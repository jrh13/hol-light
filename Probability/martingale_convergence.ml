(* ========================================================================= *)
(* Martingale convergence, conditional expectation, and Doob decomposition.  *)
(*                                                                           *)
(* Part 1: Upcrossing inequality, simple martingale convergence,             *)
(*   sigma-atom decomposition, simple conditional expectation.               *)
(* Part 2: General conditional expectation via Radon-Nikodym,                *)
(*   submartingale convergence, optional stopping for UI martingales,        *)
(*   general Doob decomposition.                                             *)
(* ========================================================================= *)

needs "Probability/martingales.ml";;

(* ========================================================================= *)
(* Upcrossing Inequality and Martingale Convergence                          *)
(* ========================================================================= *)

(* Positive part: max(x, 0) *)
let pos_part = new_definition
  `pos_part (x:real) = real_max x (&0)`;;

let POS_PART_POS = prove
 (`!x. &0 <= pos_part x`,
  REWRITE_TAC[pos_part] THEN REAL_ARITH_TAC);;

let POS_PART_NONNEG = prove
 (`!x. &0 <= x ==> pos_part x = x`,
  REWRITE_TAC[pos_part] THEN REAL_ARITH_TAC);;

let POS_PART_NEG = prove
 (`!x. x <= &0 ==> pos_part x = &0`,
  REWRITE_TAC[pos_part] THEN REAL_ARITH_TAC);;


let POS_PART_LE_IFF = prove
 (`!x y. pos_part x <= y <=> x <= y /\ &0 <= y`,
  REWRITE_TAC[pos_part] THEN REAL_ARITH_TAC);;

(* Upcrossing count for a real-valued sequence.
   We track the "phase":
     phase = 0: waiting for the sequence to go <= a
     phase = 1: waiting for the sequence to go >= b (in an upcrossing attempt)
   An upcrossing completes when phase transitions from 1 to 0 (i.e., f >= b). *)

(* Phase at each time step: 0 = below threshold not yet hit, 1 = below threshold hit *)
let upcrossing_phase = define
  `(upcrossing_phase (f:num->real) a b 0 = (if f 0 <= a then 1 else 0)) /\
   (upcrossing_phase f a b (SUC k) =
      if upcrossing_phase f a b k = 0 then
        (if f (SUC k) <= a then 1 else 0)
      else
        (if f (SUC k) >= b then 0 else 1))`;;

(* Upcrossing count: number of completed upcrossings of [a,b] *)
let upcrossing_count = define
  `(upcrossing_count (f:num->real) a b 0 = 0) /\
   (upcrossing_count f a b (SUC k) =
      upcrossing_count f a b k +
      (if upcrossing_phase f a b k = 1 /\ f (SUC k) >= b then 1 else 0))`;;

(* Downcrossing phase: dual of upcrossing phase.
   Phase 1 = above b (waiting to drop to a), Phase 0 = below b (waiting to rise to b).
   A downcrossing completes when f goes from >= b down to <= a. *)
let downcrossing_phase = define
  `(downcrossing_phase (f:num->real) a b 0 = (if f 0 >= b then 1 else 0)) /\
   (downcrossing_phase f a b (SUC k) =
      if downcrossing_phase f a b k = 0 then
        (if f (SUC k) >= b then 1 else 0)
      else
        (if f (SUC k) <= a then 0 else 1))`;;

(* Downcrossing count: number of completed downcrossings of [a,b] *)
let downcrossing_count = define
  `(downcrossing_count (f:num->real) a b 0 = 0) /\
   (downcrossing_count f a b (SUC k) =
      downcrossing_count f a b k +
      (if downcrossing_phase f a b k = 1 /\ f (SUC k) <= a then 1 else 0))`;;

(* Number of upcrossings of [a,b] by X_0(x), ..., X_n(x) *)
let num_upcrossings = new_definition
  `num_upcrossings (X:num->A->real) a b n (x:A) =
   upcrossing_count (\k. X k x) a b n`;;

(* Basic properties of upcrossing_count *)
let UPCROSSING_COUNT_MONO = prove
 (`!f a b n. upcrossing_count f a b n <= upcrossing_count f a b (SUC n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[upcrossing_count] THEN ARITH_TAC);;

let UPCROSSING_COUNT_INCREASING = prove
 (`!f a b m n. m <= n ==> upcrossing_count f a b m <= upcrossing_count f a b n`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`n:num`, `n:num`) THEN
  SPEC_TAC(`m:num`, `m:num`) THEN
  MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
  REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
  [ARITH_TAC;
   GEN_TAC THEN REWRITE_TAC[upcrossing_count] THEN ARITH_TAC]);;

let UPCROSSING_PHASE_BINARY = prove
 (`!f a b n. upcrossing_phase f a b n = 0 \/ upcrossing_phase f a b n = 1`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[upcrossing_phase] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN ARITH_TAC);;

(* Characterization of upcrossing_phase at successor step *)
let UPCROSSING_PHASE_SUC_1 = prove
 (`!f:num->real a b n.
     upcrossing_phase f a b (SUC n) = 1 <=>
     (upcrossing_phase f a b n = 0 /\ f (SUC n) <= a) \/
     (upcrossing_phase f a b n = 1 /\ f (SUC n) < b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[upcrossing_phase] THEN
  MP_TAC(SPECL [`f:num->real`; `a:real`; `b:real`; `n:num`]
    UPCROSSING_PHASE_BINARY) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
  [REWRITE_TAC[ARITH_EQ] THEN REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ];
   REWRITE_TAC[ARITH_EQ] THEN REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
   ASM_MESON_TAC[real_ge; REAL_NOT_LE; REAL_NOT_LT]]);;

let UPCROSSING_PHASE_SUC_0 = prove
 (`!f:num->real a b n.
     upcrossing_phase f a b (SUC n) = 0 <=>
     (upcrossing_phase f a b n = 0 /\ ~(f (SUC n) <= a)) \/
     (upcrossing_phase f a b n = 1 /\ f (SUC n) >= b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[upcrossing_phase] THEN
  MP_TAC(SPECL [`f:num->real`; `a:real`; `b:real`; `n:num`]
    UPCROSSING_PHASE_BINARY) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
  [REWRITE_TAC[ARITH_EQ] THEN REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ];
   REWRITE_TAC[ARITH_EQ] THEN REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ]]);;

(* The "betting strategy" for the upcrossing inequality:
   H_k = 1 when phase at time k is 1 (we're in an upcrossing attempt)
   H_k is predictable: it depends on X_0, ..., X_k *)
let upcrossing_bet = new_definition
  `upcrossing_bet (X:num->A->real) a b k (x:A) =
   if upcrossing_phase (\n. X n x) a b k = 1 then &1 else &0`;;

(* Betting gain: cumulative gain from the upcrossing betting strategy *)
let bet_gain = define
  `(bet_gain (f:num->real) a b 0 = &0) /\
   (bet_gain f a b (SUC n) = bet_gain f a b n +
    (if upcrossing_phase f a b n = 1 then &1 else &0) * (f (SUC n) - f n))`;;

(* Key deterministic lemma: pointwise upcrossing bound for non-negative sequences.
   For a non-negative sequence f and threshold b > 0:
   b * U_n <= bet_gain - f(n) * phase_indicator + correction
   More precisely, we prove the stronger invariant and then derive the bound. *)

(* Stronger invariant for the induction *)
let UPCROSSING_BOUND_INVARIANT = prove
 (`!f:num->real b n.
    &0 < b /\ (!k. &0 <= f k)
    ==> b * &(upcrossing_count f (&0) b n) <=
        bet_gain f (&0) b n -
        f n * (if upcrossing_phase f (&0) b n = 1 then &1 else &0)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [(* Base case: n = 0 *)
   REWRITE_TAC[upcrossing_count; bet_gain] THEN
   STRIP_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
   (* Goal: &0 <= &0 - f 0 * (if upcrossing_phase f (&0) b 0 = 1 then &1 else &0) *)
   MP_TAC(SPECL [`f:num->real`; `(&0):real`; `b:real`; `0`]
     UPCROSSING_PHASE_BINARY) THEN
   DISCH_THEN DISJ_CASES_TAC THENL
   [(* phase(0) = 0 *)
    ASM_REWRITE_TAC[ARITH_EQ; COND_CLAUSES] THEN REAL_ARITH_TAC;
    (* phase(0) = 1, so f 0 <= &0, combined with &0 <= f 0 gives f 0 = &0 *)
    ASM_REWRITE_TAC[ARITH_EQ; COND_CLAUSES] THEN
    SUBGOAL_THEN `(f:num->real) 0 = &0` SUBST1_TAC THENL
    [SUBGOAL_THEN `(f:num->real) 0 <= &0` MP_TAC THENL
     [UNDISCH_TAC `upcrossing_phase f (&0) b 0 = 1` THEN
      REWRITE_TAC[upcrossing_phase] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REAL_ARITH_TAC];
     REAL_ARITH_TAC]];
   (* Induction step *)
   STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
   ASM_REWRITE_TAC[] THEN
   (* IH is now an antecedent in the goal (NOT in hypotheses) *)
   (* Case split on phase(n) - IH stays in goal for joint rewriting *)
   MP_TAC(SPECL [`f:num->real`; `(&0):real`; `b:real`; `n:num`]
     UPCROSSING_PHASE_BINARY) THEN
   DISCH_THEN DISJ_CASES_TAC THENL
   [(* phase(n) = 0: not betting *)
    (* ASM_REWRITE_TAC uses phase(n)=0 to simplify both IH and main goal *)
    REWRITE_TAC[upcrossing_count; bet_gain] THEN
    ASM_REWRITE_TAC[ARITH_EQ; COND_CLAUSES] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID;
                REAL_ADD_LID; REAL_SUB_RZERO; ADD_CLAUSES] THEN
    DISCH_TAC THEN
    (* IH is now simplified: b * &U_n <= G_n *)
    MP_TAC(SPECL [`f:num->real`; `(&0):real`; `b:real`; `SUC n`]
      UPCROSSING_PHASE_BINARY) THEN
    DISCH_THEN DISJ_CASES_TAC THENL
    [(* phase(SUC n) = 0 *)
     ASM_REWRITE_TAC[ARITH_EQ; COND_CLAUSES] THEN
     REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
     ASM_REAL_ARITH_TAC;
     (* phase(SUC n) = 1: need f(SUC n) = &0 *)
     ASM_REWRITE_TAC[ARITH_EQ; COND_CLAUSES] THEN
     SUBGOAL_THEN `(f:num->real) (SUC n) = &0` SUBST1_TAC THENL
     [SUBGOAL_THEN `(f:num->real) (SUC n) <= &0` MP_TAC THENL
      [UNDISCH_TAC `upcrossing_phase f (&0) b (SUC n) = 1` THEN
       REWRITE_TAC[upcrossing_phase] THEN
       ASM_REWRITE_TAC[ARITH_EQ; COND_CLAUSES] THEN
       COND_CASES_TAC THEN REWRITE_TAC[] THEN ARITH_TAC;
       FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN REAL_ARITH_TAC];
      REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
      ASM_REAL_ARITH_TAC]];
    (* phase(n) = 1: betting *)
    (* ASM_REWRITE_TAC uses phase(n)=1 to simplify both IH and main goal *)
    REWRITE_TAC[upcrossing_count; bet_gain] THEN
    ASM_REWRITE_TAC[ARITH_EQ; COND_CLAUSES] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN
    DISCH_TAC THEN
    (* IH simplified: b * &U_n <= G_n - f n *)
    ASM_CASES_TAC `(f:num->real) (SUC n) >= b` THENL
    [(* f(SUC n) >= b: upcrossing completes *)
     ASM_REWRITE_TAC[COND_CLAUSES] THEN
     SUBGOAL_THEN `upcrossing_phase f (&0) b (SUC n) = 0` ASSUME_TAC THENL
     [REWRITE_TAC[upcrossing_phase] THEN
      ASM_REWRITE_TAC[ARITH_EQ; COND_CLAUSES]; ALL_TAC] THEN
     ASM_REWRITE_TAC[ARITH_EQ; COND_CLAUSES] THEN
     REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
     ASM_REAL_ARITH_TAC;
     (* f(SUC n) < b: still betting, phase(SUC n) = 1 *)
     ASM_REWRITE_TAC[COND_CLAUSES] THEN
     SUBGOAL_THEN `upcrossing_phase f (&0) b (SUC n) = 1` ASSUME_TAC THENL
     [REWRITE_TAC[upcrossing_phase] THEN
      ASM_REWRITE_TAC[ARITH_EQ; COND_CLAUSES]; ALL_TAC] THEN
     ASM_REWRITE_TAC[ARITH_EQ; COND_CLAUSES] THEN
     REWRITE_TAC[REAL_MUL_LID; ADD_CLAUSES] THEN
     ASM_REAL_ARITH_TAC]]]);;

(* Main pointwise upcrossing bound *)
let UPCROSSING_BOUND = prove
 (`!f:num->real b n.
    &0 < b /\ (!k. &0 <= f k)
    ==> b * &(upcrossing_count f (&0) b n) <= bet_gain f (&0) b n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:num->real`; `b:real`; `n:num`]
    UPCROSSING_BOUND_INVARIANT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= f n * (if upcrossing_phase f (&0) b n = 1
                              then &1 else &0)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN REAL_ARITH_TAC;
   REAL_ARITH_TAC]);;

(* Not-betting gain: complement of the betting strategy *)
let not_bet_gain = define
  `(not_bet_gain (f:num->real) a b 0 = &0) /\
   (not_bet_gain f a b (SUC n) = not_bet_gain f a b n +
    (if upcrossing_phase f a b n = 0 then &1 else &0) * (f (SUC n) - f n))`;;

(* Key identity: betting gain + not-betting gain = total change *)
let BET_GAIN_DECOMPOSITION = prove
 (`!f:num->real a b n.
    bet_gain f a b n + not_bet_gain f a b n = f n - f 0`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[bet_gain; not_bet_gain] THEN REAL_ARITH_TAC;
   REWRITE_TAC[bet_gain; not_bet_gain] THEN
   MP_TAC(SPECL [`f:num->real`; `a:real`; `b:real`; `n:num`]
     UPCROSSING_PHASE_BINARY) THEN
   DISCH_THEN DISJ_CASES_TAC THENL
   [ASM_REWRITE_TAC[ARITH_EQ; COND_CLAUSES] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[ARITH_EQ; COND_CLAUSES] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO] THEN
    ASM_REAL_ARITH_TAC]]);;

(* Upcrossing phase equivalence: shifting by a converts [a,b] to [0,b-a] *)
let UPCROSSING_PHASE_SHIFT = prove
 (`!f:num->real a b n. a < b ==>
    upcrossing_phase f a b n =
    upcrossing_phase (\k. pos_part (f k - a)) (&0) (b - a) n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SPEC_TAC (`n:num`, `n:num`) THEN INDUCT_TAC THENL
  [REWRITE_TAC[upcrossing_phase; pos_part] THEN
   REWRITE_TAC[REAL_ARITH `real_max (x - a) (&0) <= &0 <=> x <= a`];
   REWRITE_TAC[upcrossing_phase] THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[pos_part] THEN
   ASM_SIMP_TAC[REAL_ARITH `real_max (x - a) (&0) <= &0 <=> x <= a`;
                REAL_ARITH
     `a < b ==> (real_max (x - a) (&0) >= b - a <=> x >= b)`]]);;

(* Upcrossing count equivalence under shift *)
let UPCROSSING_COUNT_SHIFT = prove
 (`!f:num->real a b n. a < b ==>
    upcrossing_count f a b n =
    upcrossing_count (\k. pos_part (f k - a)) (&0) (b - a) n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SPEC_TAC (`n:num`, `n:num`) THEN INDUCT_TAC THENL
  [REWRITE_TAC[upcrossing_count];
   REWRITE_TAC[upcrossing_count] THEN ASM_REWRITE_TAC[] THEN
   AP_TERM_TAC THEN
   FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP UPCROSSING_PHASE_SHIFT th]) THEN
   REWRITE_TAC[pos_part] THEN
   ASM_SIMP_TAC[REAL_ARITH
     `a < b ==> (real_max (x - a) (&0) >= b - a <=> x >= b)`]]);;

(* General pointwise upcrossing inequality for arbitrary thresholds [a,b] *)
let UPCROSSING_INEQUALITY_POINTWISE = prove
 (`!f:num->real a b n. a < b ==>
    (b - a) * &(upcrossing_count f a b n) <=
    bet_gain (\k. pos_part (f k - a)) (&0) (b - a) n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `upcrossing_count (f:num->real) a b n =
    upcrossing_count (\k. pos_part (f k - a)) (&0) (b - a) n` SUBST1_TAC THENL
  [ASM_SIMP_TAC[UPCROSSING_COUNT_SHIFT]; ALL_TAC] THEN
  MP_TAC(SPECL [`\k. pos_part((f:num->real) k - a)`; `b - a:real`; `n:num`]
    UPCROSSING_BOUND) THEN
  REWRITE_TAC[POS_PART_POS] THEN
  ASM_SIMP_TAC[REAL_ARITH `a < b ==> &0 < b - a`]);;

(* ========================================================================= *)
(* Toward Probabilistic Upcrossing Inequality                                *)
(* ========================================================================= *)

(* pos_part of simple RV is simple RV *)
(* Uses pos_part(x) = (x + abs(x)) / 2 *)
let SIMPLE_RV_POS_PART = prove
 (`!p:A prob_space X.
     simple_rv p X ==> simple_rv p (\x. pos_part (X x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. pos_part ((X:A->real) x)) =
                (\x. inv(&2) * (X x + abs(X x)))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; pos_part] THEN REAL_ARITH_TAC;
   MATCH_MP_TAC SIMPLE_RV_CMUL THEN
   MATCH_MP_TAC SIMPLE_RV_ADD THEN ASM_SIMP_TAC[SIMPLE_RV_ABS]]);;

(* pos_part(X - a) is simple RV when X is *)
let SIMPLE_RV_POS_PART_SUB = prove
 (`!p:A prob_space X a.
     simple_rv p X ==> simple_rv p (\x. pos_part (X x - a))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIMPLE_RV_POS_PART THEN
  MATCH_MP_TAC SIMPLE_RV_SUB THEN ASM_SIMP_TAC[SIMPLE_RV_CONST]);;

(* Helper: simple_submartingale property extends to (X - a) * indicator *)
let SIMPLE_SUBMARTINGALE_SUB_CONST_STEP = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) (c:real).
     simple_submartingale p FF X ==>
     !(n:num) (s:A->bool). s IN FF n ==>
       simple_expectation p (\x. (X n x - c) * indicator_fn s x) <=
       simple_expectation p (\x. (X (SUC n) x - c) * indicator_fn s x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!k. simple_rv (p:A prob_space) ((X:num->A->real) k)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:A->bool) IN prob_events (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[simple_submartingale; filtration; sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x. ((X:num->A->real) n x - c) * indicator_fn (s:A->bool) x) =
     simple_expectation p
       (\x. X n x * indicator_fn s x - c * indicator_fn s x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* Rewrite RHS *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x. ((X:num->A->real) (SUC n) x - c) * indicator_fn (s:A->bool) x) =
     simple_expectation p
       (\x. X (SUC n) x * indicator_fn s x - c * indicator_fn s x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x. (X:num->A->real) n x *
    indicator_fn (s:A->bool) x)` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x. (X:num->A->real) (SUC n) x *
    indicator_fn (s:A->bool) x)` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space)
    (\x. c * indicator_fn (s:A->bool) x)` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_CMUL THEN REWRITE_TAC[ETA_AX] THEN
   MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x. (X:num->A->real) n x * indicator_fn (s:A->bool) x -
            c * indicator_fn s x) =
     simple_expectation p (\x. X n x * indicator_fn s x) -
     simple_expectation p (\x. c * indicator_fn s x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x. (X:num->A->real) (SUC n) x * indicator_fn (s:A->bool) x -
            c * indicator_fn s x) =
     simple_expectation p (\x. X (SUC n) x * indicator_fn s x) -
     simple_expectation p (\x. c * indicator_fn s x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_expectation (p:A prob_space)
    (\x. (X:num->A->real) n x * indicator_fn (s:A->bool) x) <=
    simple_expectation p (\x. X (SUC n) x * indicator_fn s x)` MP_TAC THENL
  [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* pos_part(y - a) = (y - a) * indicator of {y >= a} *)
let POS_PART_INDICATOR_FORM = prove
 (`!y a. pos_part(y - a) = (y - a) * (if a <= y then &1 else &0)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
  [REWRITE_TAC[REAL_MUL_RID] THEN
   MATCH_MP_TAC POS_PART_NONNEG THEN ASM_REAL_ARITH_TAC;
   REWRITE_TAC[REAL_MUL_RZERO] THEN
   MATCH_MP_TAC POS_PART_NEG THEN ASM_REAL_ARITH_TAC]);;

(* Submartingale pos_part step: the key conditional expectation inequality *)
let SIMPLE_SUBMARTINGALE_POS_PART_STEP = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) (a:real).
     simple_submartingale p FF X ==>
     !(n:num) (s:A->bool). s IN FF n ==>
       simple_expectation p (\x. pos_part (X n x - a) * indicator_fn s x) <=
       simple_expectation p (\x. pos_part (X (SUC n) x - a) * indicator_fn s x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  (* Extract key facts from simple_submartingale *)
  SUBGOAL_THEN `!k. simple_rv (p:A prob_space) ((X:num->A->real) k)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space) ((FF:num->(A->bool)->bool) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
  SUBGOAL_THEN `sigma_algebra ((FF:num->(A->bool)->bool) n)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:A->bool) IN prob_events (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
  (* X n is FF n-measurable *)
  SUBGOAL_THEN `measurable_wrt (p:A prob_space) ((FF:num->(A->bool)->bool) n) (X n)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[simple_submartingale; simple_adapted; adapted]; ALL_TAC] THEN
  (* Step 7: {X n >= a} IN FF n *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (X:num->A->real) n x >= a} IN
     (FF:num->(A->bool)->bool) n` ASSUME_TAC THENL
  [MATCH_MP_TAC MEASURABLE_WRT_GE THEN REWRITE_TAC[ETA_AX] THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 8: s INTER {X n >= a} IN FF n *)
  SUBGOAL_THEN
    `(s:A->bool) INTER
     {x:A | x IN prob_carrier p /\ (X:num->A->real) n x >= a} IN
     (FF:num->(A->bool)->bool) n` ASSUME_TAC THENL
  [MATCH_MP_TAC SIGMA_ALGEBRA_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 9: s_plus IN prob_events *)
  SUBGOAL_THEN
    `(s:A->bool) INTER
     {x:A | x IN prob_carrier p /\ (X:num->A->real) n x >= a} IN
     prob_events (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
  (* Step 10: simple_rv for indicators *)
  SUBGOAL_THEN `simple_rv (p:A prob_space)
    (indicator_fn ((s:A->bool) INTER
     {x:A | x IN prob_carrier p /\ (X:num->A->real) n x >= a}))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (indicator_fn (s:A->bool))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Abbreviate s_plus *)
  ABBREV_TAC `s_plus = (s:A->bool) INTER
    {x:A | x IN prob_carrier p /\ (X:num->A->real) n x >= a}` THEN
  (* Chain step 1: EXT equality *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x. pos_part ((X:num->A->real) n x - a) * indicator_fn s x) =
     simple_expectation p
       (\x. (X n x - a) * indicator_fn (s_plus:A->bool) x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[POS_PART_INDICATOR_FORM; GSYM REAL_MUL_ASSOC] THEN
   AP_TERM_TAC THEN
   EXPAND_TAC "s_plus" THEN
   REWRITE_TAC[indicator_fn; IN_INTER; IN_ELIM_THM; real_ge] THEN
   ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN
   ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO];
   ALL_TAC] THEN
  (* Establish s_plus facts *)
  SUBGOAL_THEN `(s_plus:A->bool) IN (FF:num->(A->bool)->bool) n`
    ASSUME_TAC THENL
  [EXPAND_TAC "s_plus" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s_plus:A->bool) IN prob_events (p:A prob_space)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (indicator_fn (s_plus:A->bool))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Chain step 2: transitivity *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space)
    (\x. ((X:num->A->real) (SUC n) x - a) *
         indicator_fn (s_plus:A->bool) x)` THEN
  CONJ_TAC THENL
  [(* Left: SIMPLE_SUBMARTINGALE_SUB_CONST_STEP *)
   MP_TAC(SPECL [`a:real`; `n:num`; `s_plus:A->bool`]
     (MATCH_MP SIMPLE_SUBMARTINGALE_SUB_CONST_STEP
       (ASSUME `simple_submartingale (p:A prob_space)
         (FF:num->(A->bool)->bool) (X:num->A->real)`))) THEN
   ASM_REWRITE_TAC[];
   (* Right: pointwise (X(n+1)-a)*1_{s+} <= pos_part(X(n+1)-a)*1_s *)
   MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_SUB THEN REWRITE_TAC[ETA_AX] THEN
     ASM_REWRITE_TAC[SIMPLE_RV_CONST];
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_POS_PART_SUB THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* Pointwise inequality *)
   REWRITE_TAC[] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   EXPAND_TAC "s_plus" THEN
   REWRITE_TAC[indicator_fn; IN_INTER; IN_ELIM_THM; real_ge] THEN
   ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `(x:A) IN s` THENL
   [ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO] THEN
    ASM_CASES_TAC `a <= (X:num->A->real) n x` THEN
    ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO] THEN
    REWRITE_TAC[pos_part] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO] THEN
    REWRITE_TAC[pos_part] THEN REAL_ARITH_TAC]]);;

(* {X < b} is in G when X is G-measurable *)
let MEASURABLE_WRT_LT = prove
 (`!p:A prob_space G (X:A->real) b.
     sub_sigma_algebra p G /\ measurable_wrt p G X
     ==> {x | x IN prob_carrier p /\ X x < b} IN G`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (G:(A->bool)->bool) = prob_carrier (p:A prob_space)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ X x < b} =
     UNIONS G DIFF {x | x IN prob_carrier p /\ X x >= b}`
    SUBST1_TAC THENL
  [ASM_REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; real_ge] THEN
   GEN_TAC THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier (p:A prob_space)` THEN
   ASM_REWRITE_TAC[REAL_NOT_LE];
   ALL_TAC] THEN
  MATCH_MP_TAC SIGMA_ALGEBRA_COMPL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_WRT_GE THEN ASM_REWRITE_TAC[]);;

(* Upcrossing phase set is in the filtration *)
let UPCROSSING_PHASE_SET_IN_FILTRATION = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b.
     filtration p FF /\ adapted p FF X ==>
     !n. {x | x IN prob_carrier p /\
              upcrossing_phase (\k. X k x) a b n = 1} IN FF n /\
         {x | x IN prob_carrier p /\
              upcrossing_phase (\k. X k x) a b n = 0} IN FF n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
  [(* Base case: n = 0 *)
   REWRITE_TAC[upcrossing_phase] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\
              (if (X:num->A->real) 0 x <= a then 1 else 0) = 1} =
       {x | x IN prob_carrier p /\ X 0 x <= a}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
     ALL_TAC] THEN
    MP_TAC(REWRITE_RULE[adapted]
      (ASSUME `adapted (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real)`)) THEN
    REWRITE_TAC[measurable_wrt] THEN
    DISCH_THEN(MP_TAC o SPEC `0`) THEN
    DISCH_THEN MATCH_ACCEPT_TAC;
    (* phase = 0 case: {~(X 0 <= a)} = complement of {X 0 <= a} *)
    SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space)
      ((FF:num->(A->bool)->bool) 0)` ASSUME_TAC THENL
    [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
    SUBGOAL_THEN `sigma_algebra ((FF:num->(A->bool)->bool) 0)`
      ASSUME_TAC THENL
    [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\
              (if (X:num->A->real) 0 x <= a then 1 else 0) = 0} =
       UNIONS ((FF:num->(A->bool)->bool) 0) DIFF
         {x | x IN prob_carrier p /\ X 0 x <= a}`
      SUBST1_TAC THENL
    [SUBGOAL_THEN `UNIONS ((FF:num->(A->bool)->bool) 0) =
       prob_carrier (p:A prob_space)` SUBST1_TAC THENL
     [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
     REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN GEN_TAC THEN
     ASM_CASES_TAC `(x:A) IN prob_carrier (p:A prob_space)` THEN
     ASM_REWRITE_TAC[] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
     ALL_TAC] THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_COMPL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(REWRITE_RULE[adapted]
      (ASSUME `adapted (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real)`)) THEN
    REWRITE_TAC[measurable_wrt] THEN
    DISCH_THEN(MP_TAC o SPEC `0`) THEN
    DISCH_THEN MATCH_ACCEPT_TAC];
   (* Inductive step *)
   FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC)) THEN
   SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space)
     ((FF:num->(A->bool)->bool) (SUC n))` ASSUME_TAC THENL
   [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
   SUBGOAL_THEN `sigma_algebra ((FF:num->(A->bool)->bool) (SUC n))`
     ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
   SUBGOAL_THEN `(FF:num->(A->bool)->bool) n SUBSET FF (SUC n)`
     ASSUME_TAC THENL
   [ASM_MESON_TAC[filtration; ARITH_RULE `n <= SUC n`]; ALL_TAC] THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\
             upcrossing_phase (\k. (X:num->A->real) k x) a b n = 1} IN
      FF (SUC n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\
             upcrossing_phase (\k. (X:num->A->real) k x) a b n = 0} IN
      FF (SUC n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
   SUBGOAL_THEN `measurable_wrt (p:A prob_space)
     ((FF:num->(A->bool)->bool) (SUC n)) ((X:num->A->real) (SUC n))`
     ASSUME_TAC THENL
   [ASM_MESON_TAC[adapted]; ALL_TAC] THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (X:num->A->real) (SUC n) x <= a} IN
      FF (SUC n)` ASSUME_TAC THENL
   [MP_TAC(REWRITE_RULE[measurable_wrt]
     (ASSUME `measurable_wrt (p:A prob_space) ((FF:num->(A->bool)->bool) (SUC n))
              ((X:num->A->real) (SUC n))`)) THEN
    DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (X:num->A->real) (SUC n) x >= b} IN
      FF (SUC n)` ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_WRT_GE THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (X:num->A->real) (SUC n) x < b} IN
      FF (SUC n)` ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_WRT_LT THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ ~((X:num->A->real) (SUC n) x <= a)} IN
      FF (SUC n)` ASSUME_TAC THENL
   [SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ ~((X:num->A->real) (SUC n) x <= a)} =
       UNIONS ((FF:num->(A->bool)->bool) (SUC n)) DIFF
         {x | x IN prob_carrier p /\ X (SUC n) x <= a}`
      SUBST1_TAC THENL
    [SUBGOAL_THEN `UNIONS ((FF:num->(A->bool)->bool) (SUC n)) =
       prob_carrier (p:A prob_space)` SUBST1_TAC THENL
     [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
     REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
     GEN_TAC THEN
     ASM_CASES_TAC `(x:A) IN prob_carrier (p:A prob_space)` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_COMPL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [(* {phase_{n+1} = 1} IN FF(SUC n) *)
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\
              upcrossing_phase (\k. (X:num->A->real) k x) a b (SUC n) = 1} =
       ({x | x IN prob_carrier p /\
             upcrossing_phase (\k. X k x) a b n = 0} INTER
        {x | x IN prob_carrier p /\ X (SUC n) x <= a}) UNION
       ({x | x IN prob_carrier p /\
             upcrossing_phase (\k. X k x) a b n = 1} INTER
        {x | x IN prob_carrier p /\ X (SUC n) x < b})`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM;
                 UPCROSSING_PHASE_SUC_1] THEN
     MESON_TAC[];
     ALL_TAC] THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_UNION THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC SIGMA_ALGEBRA_INTER THEN ASM_REWRITE_TAC[];
    (* {phase_{n+1} = 0} IN FF(SUC n) *)
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\
              upcrossing_phase (\k. (X:num->A->real) k x) a b (SUC n) = 0} =
       ({x | x IN prob_carrier p /\
             upcrossing_phase (\k. X k x) a b n = 0} INTER
        {x | x IN prob_carrier p /\ ~((X:num->A->real) (SUC n) x <= a)}) UNION
       ({x | x IN prob_carrier p /\
             upcrossing_phase (\k. X k x) a b n = 1} INTER
        {x | x IN prob_carrier p /\ X (SUC n) x >= b})`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM;
                 UPCROSSING_PHASE_SUC_0] THEN
     MESON_TAC[];
     ALL_TAC] THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_UNION THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC SIGMA_ALGEBRA_INTER THEN ASM_REWRITE_TAC[]]]);;



let SIMPLE_RV_NOT_BET_INDICATOR = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b n.
     filtration p FF /\ adapted p FF X
     ==> simple_rv p
           (\x. if upcrossing_phase (\k. X k x) a b n = 0 then &1 else &0)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SIMPLE_RV_EXT THEN
  EXISTS_TAC `indicator_fn
    {x:A | x IN prob_carrier p /\
           upcrossing_phase (\k. (X:num->A->real) k x) a b n = 0}` THEN
  CONJ_TAC THENL
  [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
   ASM_REWRITE_TAC[];
   MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
   MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                  `X:num->A->real`; `a:real`; `b:real`]
     UPCROSSING_PHASE_SET_IN_FILTRATION) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
   ASM_MESON_TAC[filtration; sub_sigma_algebra; SUBSET]]);;


(* Combined: simple_rv and nonneg expectation for not_bet_gain of pos_part *)
let NOT_BET_GAIN_POS_PART_NONNEG = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b.
     simple_submartingale p FF X /\ a < b ==>
     !n. simple_rv p
           (\x. not_bet_gain (\k. pos_part(X k x - a)) (&0) (b - a) n) /\
         &0 <= simple_expectation p
           (\x. not_bet_gain (\k. pos_part(X k x - a)) (&0) (b - a) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) (FF:num->(A->bool)->bool)
    (X:num->A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[simple_submartingale; simple_adapted; adapted]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. simple_rv (p:A prob_space) ((X:num->A->real) k)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  INDUCT_TAC THENL
  [(* Base case: not_bet_gain ... 0 = &0 *)
   SUBGOAL_THEN `(\x:A. not_bet_gain (\k. pos_part((X:num->A->real) k x - a))
     (&0) (b - a) 0) = (\x. &0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; not_bet_gain]; ALL_TAC] THEN
   REWRITE_TAC[SIMPLE_RV_CONST] THEN
   SIMP_TAC[SIMPLE_EXPECTATION_CONST; REAL_LE_REFL];
   (* Inductive step *)
   FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC)) THEN
   SUBGOAL_THEN
     `(\x:A. not_bet_gain (\k. pos_part((X:num->A->real) k x - a))
       (&0) (b - a) (SUC n)) =
      (\x. not_bet_gain (\k. pos_part(X k x - a)) (&0) (b - a) n +
           (if upcrossing_phase (\k. pos_part(X k x - a)) (&0) (b - a) n = 0
            then &1 else &0) *
           (pos_part(X (SUC n) x - a) - pos_part(X n x - a)))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; not_bet_gain]; ALL_TAC] THEN
   (* Use UPCROSSING_PHASE_SHIFT to replace pos_part phase with original phase *)
   SUBGOAL_THEN
     `!x:A. upcrossing_phase (\k. pos_part((X:num->A->real) k x - a))
       (&0) (b - a) n = upcrossing_phase (\k. X k x) a b n`
     (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC UPCROSSING_PHASE_SHIFT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Show simple_rv for the increment term *)
   SUBGOAL_THEN `simple_rv (p:A prob_space)
     (\x:A. (if upcrossing_phase (\k. (X:num->A->real) k x) a b n = 0
             then &1 else &0) *
            (pos_part(X (SUC n) x - a) - pos_part(X n x - a)))`
     ASSUME_TAC THENL
   [(* Step 1: pos_part(X (SUC n) - a) is simple_rv *)
    SUBGOAL_THEN `simple_rv (p:A prob_space)
      (\x:A. pos_part((X:num->A->real) (SUC n) x - a))` ASSUME_TAC THENL
    [MP_TAC(SPECL [`p:A prob_space`;
       `(X:num->A->real) (SUC n)`; `a:real`] SIMPLE_RV_POS_PART_SUB) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(ACCEPT_TAC o REWRITE_RULE[]);
     ALL_TAC] THEN
    (* Step 2: pos_part(X n - a) is simple_rv *)
    SUBGOAL_THEN `simple_rv (p:A prob_space)
      (\x:A. pos_part((X:num->A->real) n x - a))` ASSUME_TAC THENL
    [MP_TAC(SPECL [`p:A prob_space`;
       `(X:num->A->real) n`; `a:real`] SIMPLE_RV_POS_PART_SUB) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(ACCEPT_TAC o REWRITE_RULE[]);
     ALL_TAC] THEN
    (* Step 3: difference is simple_rv *)
    SUBGOAL_THEN `simple_rv (p:A prob_space)
      (\x:A. pos_part((X:num->A->real) (SUC n) x - a) -
             pos_part(X n x - a))` ASSUME_TAC THENL
    [MP_TAC(SPECL [`p:A prob_space`;
       `\x:A. pos_part((X:num->A->real) (SUC n) x - a)`;
       `\x:A. pos_part((X:num->A->real) n x - a)`]
       SIMPLE_RV_SUB) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(ACCEPT_TAC o REWRITE_RULE[])];
     ALL_TAC] THEN
    (* Step 4: not-bet indicator is simple_rv *)
    SUBGOAL_THEN `simple_rv (p:A prob_space)
      (\x:A. if upcrossing_phase (\k. (X:num->A->real) k x) a b n = 0
             then &1 else &0)` ASSUME_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_NOT_BET_INDICATOR THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
    (* Step 5: product is simple_rv *)
    MP_TAC(SPECL [`p:A prob_space`;
       `\x:A. if upcrossing_phase (\k. (X:num->A->real) k x) a b n = 0
               then &1 else &0`;
       `\x:A. pos_part((X:num->A->real) (SUC n) x - a) -
              pos_part(X n x - a)`]
       SIMPLE_RV_MUL) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[];
     DISCH_THEN(ACCEPT_TAC o REWRITE_RULE[])];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [(* simple_rv for the sum *)
    MP_TAC(SPECL
      [`p:A prob_space`;
       `\x:A. not_bet_gain (\k. pos_part((X:num->A->real) k x - a))
              (&0) (b - a) n`;
       `\x:A. (if upcrossing_phase (\k. (X:num->A->real) k x) a b n = 0
               then &1 else &0) *
              (pos_part(X (SUC n) x - a) - pos_part(X n x - a))`]
      SIMPLE_RV_ADD) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[];
     DISCH_THEN(ACCEPT_TAC o REWRITE_RULE[])];
    (* nonneg expectation *)
    SUBGOAL_THEN
      `simple_expectation (p:A prob_space)
       (\x:A. not_bet_gain (\k. pos_part((X:num->A->real) k x - a))
              (&0) (b - a) n +
              (if upcrossing_phase (\k. X k x) a b n = 0 then &1 else &0) *
              (pos_part(X (SUC n) x - a) - pos_part(X n x - a))) =
       simple_expectation p
         (\x. not_bet_gain (\k. pos_part(X k x - a)) (&0) (b - a) n) +
       simple_expectation p
         (\x. (if upcrossing_phase (\k. X k x) a b n = 0 then &1 else &0) *
              (pos_part(X (SUC n) x - a) - pos_part(X n x - a)))`
      SUBST1_TAC THENL
    [MP_TAC(SPECL
       [`p:A prob_space`;
        `\x:A. not_bet_gain (\k. pos_part((X:num->A->real) k x - a))
               (&0) (b - a) n`;
        `\x:A. (if upcrossing_phase (\k. (X:num->A->real) k x) a b n = 0
                then &1 else &0) *
               (pos_part(X (SUC n) x - a) - pos_part(X n x - a))`]
       SIMPLE_EXPECTATION_ADD) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(ACCEPT_TAC o REWRITE_RULE[])];
     ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\
              upcrossing_phase (\k. (X:num->A->real) k x) a b n = 0} IN
       (FF:num->(A->bool)->bool) n`
      ASSUME_TAC THENL
    [MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                    `X:num->A->real`; `a:real`; `b:real`]
       UPCROSSING_PHASE_SET_IN_FILTRATION) THEN
     ASM_REWRITE_TAC[] THEN MESON_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `simple_expectation (p:A prob_space)
       (\x:A. (if upcrossing_phase (\k. (X:num->A->real) k x) a b n = 0
               then &1 else &0) *
              (pos_part(X (SUC n) x - a) - pos_part(X n x - a))) =
       simple_expectation p
         (\x. pos_part(X (SUC n) x - a) *
              indicator_fn
                {y:A | y IN prob_carrier p /\
                       upcrossing_phase (\k. X k y) a b n = 0} x) -
       simple_expectation p
         (\x. pos_part(X n x - a) *
              indicator_fn
                {y:A | y IN prob_carrier p /\
                       upcrossing_phase (\k. X k y) a b n = 0} x)`
      SUBST1_TAC THENL
    [SUBGOAL_THEN
       `simple_rv (p:A prob_space)
         (\x:A. pos_part((X:num->A->real) (SUC n) x - a) *
                indicator_fn
                  {y | y IN prob_carrier p /\
                       upcrossing_phase (\k. X k y) a b n = 0} x)`
       ASSUME_TAC THENL
     [MP_TAC(SPECL
        [`p:A prob_space`;
         `\x:A. pos_part((X:num->A->real) (SUC n) x - a)`;
         `\x:A. indicator_fn
           {y:A | y IN prob_carrier p /\
                  upcrossing_phase (\k. (X:num->A->real) k y) a b n = 0} x`]
        SIMPLE_RV_MUL) THEN
      ANTS_TAC THENL
      [CONJ_TAC THENL
       [MP_TAC(SPECL [`p:A prob_space`;
          `(X:num->A->real) (SUC n)`; `a:real`] SIMPLE_RV_POS_PART_SUB) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(ACCEPT_TAC o REWRITE_RULE[]);
        REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
        ASM_MESON_TAC[filtration; sub_sigma_algebra; SUBSET]];
       DISCH_THEN(ACCEPT_TAC o REWRITE_RULE[])];
      ALL_TAC] THEN
     SUBGOAL_THEN
       `simple_rv (p:A prob_space)
         (\x:A. pos_part((X:num->A->real) n x - a) *
                indicator_fn
                  {y | y IN prob_carrier p /\
                       upcrossing_phase (\k. X k y) a b n = 0} x)`
       ASSUME_TAC THENL
     [MP_TAC(SPECL
        [`p:A prob_space`;
         `\x:A. pos_part((X:num->A->real) n x - a)`;
         `\x:A. indicator_fn
           {y:A | y IN prob_carrier p /\
                  upcrossing_phase (\k. (X:num->A->real) k y) a b n = 0} x`]
        SIMPLE_RV_MUL) THEN
      ANTS_TAC THENL
      [CONJ_TAC THENL
       [MP_TAC(SPECL [`p:A prob_space`;
          `(X:num->A->real) n`; `a:real`] SIMPLE_RV_POS_PART_SUB) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(ACCEPT_TAC o REWRITE_RULE[]);
        REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
        ASM_MESON_TAC[filtration; sub_sigma_algebra; SUBSET]];
       DISCH_THEN(ACCEPT_TAC o REWRITE_RULE[])];
      ALL_TAC] THEN
     CONV_TAC SYM_CONV THEN
     SUBGOAL_THEN
       `simple_expectation (p:A prob_space)
         (\x:A. pos_part((X:num->A->real) (SUC n) x - a) *
                indicator_fn
                  {y | y IN prob_carrier p /\
                       upcrossing_phase (\k. X k y) a b n = 0} x) -
        simple_expectation p
         (\x. pos_part(X n x - a) *
              indicator_fn
                {y | y IN prob_carrier p /\
                     upcrossing_phase (\k. X k y) a b n = 0} x) =
        simple_expectation p
         (\x. pos_part(X (SUC n) x - a) *
              indicator_fn
                {y | y IN prob_carrier p /\
                     upcrossing_phase (\k. X k y) a b n = 0} x -
              pos_part(X n x - a) *
              indicator_fn
                {y | y IN prob_carrier p /\
                     upcrossing_phase (\k. X k y) a b n = 0} x)`
       SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MP_TAC(SPECL
        [`p:A prob_space`;
         `\x:A. pos_part((X:num->A->real) (SUC n) x - a) *
                indicator_fn
                  {y:A | y IN prob_carrier p /\
                         upcrossing_phase (\k. X k y) a b n = 0} x`;
         `\x:A. pos_part((X:num->A->real) n x - a) *
                indicator_fn
                  {y:A | y IN prob_carrier p /\
                         upcrossing_phase (\k. X k y) a b n = 0} x`]
        SIMPLE_EXPECTATION_SUB) THEN
      ANTS_TAC THENL
      [ASM_REWRITE_TAC[];
       DISCH_THEN(ACCEPT_TAC o REWRITE_RULE[])];
      ALL_TAC] THEN
     MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN
    MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                   `X:num->A->real`; `a:real`]
      SIMPLE_SUBMARTINGALE_POS_PART_STEP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL
      [`n:num`;
       `{x:A | x IN prob_carrier p /\
               upcrossing_phase (\k. (X:num->A->real) k x) a b n = 0}`]) THEN
    ASM_REWRITE_TAC[]]]);;

(* Transfer simple_rv between functions agreeing on carrier *)
let SIMPLE_RV_AGREE = prove
 (`!p:A prob_space (X:A->real) (Y:A->real).
     simple_rv p X /\ (!x. x IN prob_carrier p ==> X x = Y x)
     ==> simple_rv p Y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simple_rv]) ASSUME_TAC) THEN
  REWRITE_TAC[simple_rv] THEN CONJ_TAC THENL
  [(* random_variable *)
   REWRITE_TAC[random_variable] THEN X_GEN_TAC `v:real` THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (Y:A->real) x <= v} =
      {x | x IN prob_carrier p /\ (X:A->real) x <= v}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `x:A IN prob_carrier p` THEN ASM_SIMP_TAC[];
    ASM_MESON_TAC[random_variable]];
   (* FINITE {Y x | ...} *)
   SUBGOAL_THEN
     `{(Y:A->real) x | x IN prob_carrier (p:A prob_space)} =
      {X x | x IN prob_carrier p}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    EQ_TAC THEN STRIP_TAC THEN EXISTS_TAC `x':A` THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]]]);;

(* Num-to-real of conditional: &(if P then 1 else 0) = if P then &1 else &0 *)
let REAL_OF_NUM_COND_01 = prove
 (`!P. &(if P then 1 else 0) = if P then &1 else &0`,
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* Number of upcrossings is a simple random variable *)
let SIMPLE_RV_NUM_UPCROSSINGS = prove
 (`!p:A prob_space FF (X:num->A->real) a b.
     filtration p FF /\ adapted p FF X /\ (!n. simple_rv p (X n))
     ==> !n. simple_rv p (\x. &(num_upcrossings X a b n x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
  [(* Base case: n = 0 *)
   MATCH_MP_TAC SIMPLE_RV_AGREE THEN
   EXISTS_TAC `(\x:A. &0)` THEN REWRITE_TAC[SIMPLE_RV_CONST] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[num_upcrossings; upcrossing_count];
   (* Inductive step: SUC n *)
   ABBREV_TAC
     `S = {x:A | x IN prob_carrier p /\
                  upcrossing_phase (\k. (X:num->A->real) k x) a b n = 1 /\
                  X (SUC n) x >= b}` THEN
   (* Step 1: S is in prob_events *)
   SUBGOAL_THEN `(S:A->bool) IN prob_events p` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\
              upcrossing_phase (\k. (X:num->A->real) k x) a b n = 1 /\
              X (SUC n) x >= b} =
       {x | x IN prob_carrier p /\
            upcrossing_phase (\k. X k x) a b n = 1} INTER
       {x | x IN prob_carrier p /\ X (SUC n) x >= b}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
     MESON_TAC[];
     ALL_TAC] THEN
    MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN CONJ_TAC THENL
    [MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                    `X:num->A->real`; `a:real`; `b:real`]
       UPCROSSING_PHASE_SET_IN_FILTRATION) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
     ASM_MESON_TAC[filtration; sub_sigma_algebra; SUBSET];
     MP_TAC(SPECL [`p:A prob_space`; `(X:num->A->real) (SUC n)`; `b:real`]
       RV_PREIMAGE_GE) THEN
     ANTS_TAC THENL
     [ASM_MESON_TAC[simple_rv]; SIMP_TAC[]]];
    ALL_TAC] THEN
   (* Step 2: Apply SIMPLE_RV_AGREE *)
   MATCH_MP_TAC SIMPLE_RV_AGREE THEN
   EXISTS_TAC `\x:A. &(num_upcrossings (X:num->A->real) a b n x) +
                      indicator_fn (S:A->bool) x` THEN
   CONJ_TAC THENL
   [(* simple_rv of the sum *)
    MP_TAC(SPECL [`p:A prob_space`;
                   `\x:A. &(num_upcrossings (X:num->A->real) a b n x)`;
                   `indicator_fn (S:A->bool)`]
      SIMPLE_RV_ADD) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SIMPLE_RV_INDICATOR];
    (* agreement on carrier *)
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[num_upcrossings; upcrossing_count;
                GSYM REAL_OF_NUM_ADD; REAL_OF_NUM_COND_01] THEN
    AP_TERM_TAC THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* Doob's Upcrossing Inequality                                              *)
(* ========================================================================= *)

(* Key pointwise bound: combining upcrossing inequality + decomposition *)
let UPCROSSING_POINTWISE_SUM_BOUND = prove
 (`!X:num->A->real a b n x.
     a < b ==>
     (b - a) * &(num_upcrossings X a b n x) +
     not_bet_gain (\k. pos_part(X k x - a)) (&0) (b - a) n +
     pos_part(X 0 x - a)
     <= pos_part(X n x - a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\k:num. (X:num->A->real) k x`; `a:real`; `b:real`; `n:num`]
    UPCROSSING_INEQUALITY_POINTWISE) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`\k:num. pos_part((X:num->A->real) k x - a)`;
                 `&0`; `b - a:real`; `n:num`]
    BET_GAIN_DECOMPOSITION) THEN
  REWRITE_TAC[num_upcrossings] THEN REAL_ARITH_TAC);;

(* Doob's Upcrossing Inequality *)
let SIMPLE_DOOB_UPCROSSING_INEQUALITY = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b n.
     simple_submartingale p FF X /\ a < b ==>
     (b - a) * simple_expectation p (\x. &(num_upcrossings X a b n x))
     <= simple_expectation p (\x. pos_part(X n x - a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Extract simple_submartingale components *)
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[simple_submartingale; simple_adapted]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  (* simple_rv of key terms *)
  SUBGOAL_THEN `simple_rv p (\x:A. &(num_upcrossings (X:num->A->real) a b n x))`
    ASSUME_TAC THENL
  [MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                  `X:num->A->real`; `a:real`; `b:real`]
     SIMPLE_RV_NUM_UPCROSSINGS) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(ACCEPT_TAC o SPEC `n:num`)];
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv p (\x:A. pos_part((X:num->A->real) n x - a))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_POS_PART_SUB THEN
   REWRITE_TAC[ETA_AX] THEN
   FIRST_ASSUM(ACCEPT_TAC o SPEC `n:num`);
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv p (\x:A. pos_part((X:num->A->real) 0 x - a))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_POS_PART_SUB THEN
   REWRITE_TAC[ETA_AX] THEN
   FIRST_ASSUM(ACCEPT_TAC o SPEC `0`);
   ALL_TAC] THEN
  (* not_bet_gain: simple_rv and nonneg expectation *)
  SUBGOAL_THEN
    `simple_rv p (\x:A. not_bet_gain (\k. pos_part((X:num->A->real) k x - a))
                         (&0) (b - a) n) /\
     &0 <= simple_expectation p
       (\x. not_bet_gain (\k. pos_part(X k x - a)) (&0) (b - a) n)`
    STRIP_ASSUME_TAC THENL
  [MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                  `X:num->A->real`; `a:real`; `b:real`]
     NOT_BET_GAIN_POS_PART_NONNEG) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(fun th -> ACCEPT_TAC (SPEC `n:num` th))];
   ALL_TAC] THEN
  (* E[pp_0] >= 0 *)
  SUBGOAL_THEN
    `&0 <= simple_expectation (p:A prob_space)
       (\x:A. pos_part((X:num->A->real) 0 x - a))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_POS THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[pos_part] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* E[sum] <= E[ppn] via pointwise bound and monotonicity *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
      (\x:A. (b - a) * &(num_upcrossings (X:num->A->real) a b n x) +
       not_bet_gain (\k. pos_part(X k x - a)) (&0) (b - a) n +
       pos_part(X 0 x - a))
     <= simple_expectation p (\x. pos_part(X n x - a))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
   REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SIMPLE_RV_ADD; SIMPLE_RV_CMUL];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`X:num->A->real`; `a:real`; `b:real`; `n:num`; `x:A`]
      UPCROSSING_POINTWISE_SUM_BOUND) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* E[sum] = (b-a)*E[U] + E[nbg] + E[pp0] via linearity *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
      (\x:A. (b - a) * &(num_upcrossings (X:num->A->real) a b n x) +
       not_bet_gain (\k. pos_part(X k x - a)) (&0) (b - a) n +
       pos_part(X 0 x - a)) =
     (b - a) * simple_expectation p (\x. &(num_upcrossings X a b n x)) +
     simple_expectation p
       (\x. not_bet_gain (\k. pos_part(X k x - a)) (&0) (b - a) n) +
     simple_expectation p (\x. pos_part(X 0 x - a))`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[SIMPLE_EXPECTATION_ADD; SIMPLE_EXPECTATION_CMUL;
                 SIMPLE_RV_ADD; SIMPLE_RV_CMUL];
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Martingale Convergence Theorem                                            *)
(* ========================================================================= *)

(* Bound on pos_part for bounded functions *)
let POS_PART_BOUND = prove
 (`!x a M. abs(x) <= M ==> pos_part(x - a) <= M + abs(a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pos_part; real_max] THEN
  COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* Expected upcrossings bounded for bounded simple_submartingale *)
let SIMPLE_UPCROSSING_EXPECTATION_BOUND = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b n M.
     simple_submartingale p FF X /\ a < b /\
     (!m x. x IN prob_carrier p ==> abs(X m x) <= M)
     ==> (b - a) * simple_expectation p (\x. &(num_upcrossings X a b n x))
         <= M + abs(a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                `X:num->A->real`; `a:real`; `b:real`; `n:num`]
    SIMPLE_DOOB_UPCROSSING_INEQUALITY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!m:num. simple_rv (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\x. pos_part((X:num->A->real) n x - a))
     <= M + abs(a)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`;
                   `\x:A. pos_part((X:num->A->real) n x - a)`;
                   `\x:A. M + abs(a:real)`]
     SIMPLE_EXPECTATION_MONO) THEN
   REWRITE_TAC[SIMPLE_EXPECTATION_CONST] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_POS_PART_SUB THEN REWRITE_TAC[ETA_AX] THEN
    FIRST_ASSUM(ACCEPT_TAC o SPEC `n:num`);
    REWRITE_TAC[SIMPLE_RV_CONST];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC POS_PART_BOUND THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Monotonicity of num_upcrossings *)
let NUM_UPCROSSINGS_MONO = prove
 (`!X:num->A->real a b m n x.
     m <= n ==> num_upcrossings X a b m x <= num_upcrossings X a b n x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[num_upcrossings] THEN
  MATCH_MP_TAC UPCROSSING_COUNT_INCREASING THEN ASM_REWRITE_TAC[]);;

(* The set {x | num_upcrossings >= k} is an event *)
let SIMPLE_NUM_UPCROSSINGS_GE_EVENT = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b n k.
     filtration p FF /\ adapted p FF X /\ (!m. simple_rv p (X m))
     ==> {x | x IN prob_carrier p /\
              &(num_upcrossings X a b n x) >= &k}
         IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simple_rv p (\x:A. &(num_upcrossings (X:num->A->real) a b n x))`
    ASSUME_TAC THENL
  [MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                  `X:num->A->real`; `a:real`; `b:real`]
     SIMPLE_RV_NUM_UPCROSSINGS) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(ACCEPT_TAC o SPEC `n:num`)];
   ALL_TAC] THEN
  MATCH_MP_TAC RV_PREIMAGE_GE THEN
  ASM_MESON_TAC[simple_rv]);;

(* Key MCT lemma: P(U_n >= k) <= (M + |a|) / ((b-a)*k) *)
let SIMPLE_UPCROSSING_PROB_BOUND = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b n M k.
     simple_submartingale p FF X /\ a < b /\
     (!m x. x IN prob_carrier p ==> abs(X m x) <= M) /\
     0 < k
     ==> prob p {x | x IN prob_carrier p /\
                     &(num_upcrossings X a b n x) >= &k}
         <= (M + abs(a)) / ((b - a) * &k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!m:num. simple_rv (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
    [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)`
    ASSUME_TAC THENL
    [ASM_MESON_TAC[simple_submartingale; simple_adapted]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv p (\x:A. &(num_upcrossings (X:num->A->real) a b n x))`
    ASSUME_TAC THENL
  [MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                  `X:num->A->real`; `a:real`; `b:real`]
     SIMPLE_RV_NUM_UPCROSSINGS) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(ACCEPT_TAC o SPEC `n:num`)];
   ALL_TAC] THEN
  (* Use Markov: P(U_n >= k) <= E[U_n] / k *)
  SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
    `prob p {x | x IN prob_carrier (p:A prob_space) /\
     &(num_upcrossings (X:num->A->real) a b n x) >= &k}
     <= simple_expectation p (\x. &(num_upcrossings X a b n x)) / &k`
    ASSUME_TAC THENL
  [MATCH_MP_TAC MARKOV_INEQUALITY_SIMPLE THEN
   ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_POS];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* (b-a)*E[U] <= M + |a| from upcrossing bound *)
  SUBGOAL_THEN
    `(b - a) * simple_expectation (p:A prob_space)
       (\x:A. &(num_upcrossings (X:num->A->real) a b n x)) <= M + abs(a:real)`
    ASSUME_TAC THENL
  [MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                  `X:num->A->real`; `a:real`; `b:real`; `n:num`; `M:real`]
     SIMPLE_UPCROSSING_EXPECTATION_BOUND) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* E[U] <= (M + |a|) / (b-a) *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. &(num_upcrossings (X:num->A->real) a b n x))
     <= (M + abs(a:real)) / (b - a)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
   ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* E[U]/k <= (M+|a|)/((b-a)*k) *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. &(num_upcrossings (X:num->A->real) a b n x)) / &k
     <= (M + abs(a:real)) / ((b - a) * &k)` ASSUME_TAC THENL
  [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
   MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM real_div];
    MATCH_MP_TAC REAL_LE_INV THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  ASM_MESON_TAC[REAL_LE_TRANS]);;

(* Probability bound for infinite upcrossings is zero *)
(* First, a utility: limit of bounded increasing sequence preserves bound *)
let PROB_UNIONS_INCREASING_BOUND = prove
 (`!p:A prob_space (A:num->A->bool) c.
     (!n. A n IN prob_events p) /\
     (!n. A n SUBSET A (SUC n)) /\
     (!n. prob p (A n) <= c)
     ==> prob p (UNIONS {A n | n IN (:num)}) <= c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `A:num->A->bool`]
    PROB_CONTINUITY_FROM_BELOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\n. prob (p:A prob_space) ((A:num->A->bool) n)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `0` THEN ASM_SIMP_TAC[]);;

(* Key lemma: infinite upcrossings have probability zero *)
let SIMPLE_INFINITE_UPCROSSINGS_NULL = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b M.
     simple_submartingale p FF X /\ a < b /\
     (!m x. x IN prob_carrier p ==> abs(X m x) <= M)
     ==> !k. 0 < k ==>
         prob p (UNIONS {
           {x | x IN prob_carrier p /\ &(num_upcrossings X a b n x) >= &k}
         | n IN (:num)}) <= (M + abs(a)) / ((b - a) * &k)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PROB_UNIONS_INCREASING_BOUND THEN
  SUBGOAL_THEN `!m:num. simple_rv (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
    [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)` ASSUME_TAC THENL
    [ASM_MESON_TAC[simple_submartingale; simple_adapted]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [(* A n IN events *)
   GEN_TAC THEN MATCH_MP_TAC SIMPLE_NUM_UPCROSSINGS_GE_EVENT THEN
   EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
   (* A n SUBSET A (SUC n) *)
   X_GEN_TAC `nn:num` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge;
     REAL_OF_NUM_LE] THEN
   X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[NUM_UPCROSSINGS_MONO; LE_TRANS;
     ARITH_RULE `nn <= SUC nn`];
   (* P(A n) <= c *)
   X_GEN_TAC `m:num` THEN
   MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                   `X:num->A->real`; `a:real`; `b:real`; `m:num`;
                   `M:real`; `k:num`] SIMPLE_UPCROSSING_PROB_BOUND) THEN
   DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]]);;

(* Utility: if 0 <= x and x <= c / SUC k for all k, then x = 0 *)
let REAL_EQ_0_FROM_INV_BOUND = prove
 (`!x c. &0 <= x /\ (!k. x <= c / &(SUC k)) ==> x = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `x = &0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* By Archimedean: exists n with c < n * x *)
  MP_TAC(SPEC `x:real` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` ASSUME_TAC) THEN
  (* n >= 1: if n=0 then c < 0, but x <= c/1 so c >= x > 0 *)
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
  [DISCH_TAC THEN
   UNDISCH_TAC `c < &n * x` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
   UNDISCH_TAC `!k:num. x <= c / &(SUC k)` THEN
   DISCH_THEN(MP_TAC o SPEC `0`) THEN
   REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; REAL_DIV_1] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* From hypothesis with k = n-1: x <= c/n. But c < n*x so c/n < x. *)
  UNDISCH_TAC `!k:num. x <= c / &(SUC k)` THEN
  DISCH_THEN(MP_TAC o SPEC `n - 1`) THEN
  SUBGOAL_THEN `SUC(n - 1) = n` SUBST1_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c < &n * x` THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT;
    ARITH_RULE `~(n = 0) ==> 0 < n`] THEN
  REAL_ARITH_TAC);;

(* Finite upcrossings a.s. for bounded simple_submartingale, fixed a < b *)
let SIMPLE_FINITE_UPCROSSINGS_AS = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b M.
     simple_submartingale p FF X /\ a < b /\
     (!m x. x IN prob_carrier p ==> abs(X m x) <= M)
     ==> almost_surely p
           {x | ?B:num. !n. num_upcrossings X a b n x <= B}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[almost_surely] THEN
  SUBGOAL_THEN `!m:num. simple_rv (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
    [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)` ASSUME_TAC THENL
    [ASM_MESON_TAC[simple_submartingale; simple_adapted]; ALL_TAC] THEN
  (* Take N = INTERS of UNIONS over n of {U_n >= SUC k} *)
  EXISTS_TAC
    `INTERS {UNIONS {
       {x:A | x IN prob_carrier p /\
              &(num_upcrossings (X:num->A->real) a b n x) >= &(SUC k)}
     | n IN (:num)} | k IN (:num)}` THEN
  CONJ_TAC THENL
  [(* null_event *)
   REWRITE_TAC[null_event] THEN CONJ_TAC THENL
   [(* In events: countable intersection of countable unions of events *)
    MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN
    GEN_TAC THEN MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
    GEN_TAC THEN MATCH_MP_TAC SIMPLE_NUM_UPCROSSINGS_GE_EVENT THEN
    EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
    (* P = 0 *)
    MATCH_MP_TAC REAL_EQ_0_FROM_INV_BOUND THEN
    EXISTS_TAC `(M + abs(a:real)) / (b - a)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC PROB_POSITIVE THEN
     MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN
     GEN_TAC THEN MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
     GEN_TAC THEN MATCH_MP_TAC SIMPLE_NUM_UPCROSSINGS_GE_EVENT THEN
     EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
     (* P(N) <= C/SUC k for all k *)
     X_GEN_TAC `j:num` THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `prob (p:A prob_space) (UNIONS {
       {x:A | x IN prob_carrier p /\
              &(num_upcrossings (X:num->A->real) a b n x) >= &(SUC j)}
       | n IN (:num)})` THEN
     CONJ_TAC THENL
     [(* P(INTERS) <= P(UNIONS_j) *)
      MATCH_MP_TAC PROB_MONO THEN REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN
       GEN_TAC THEN MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
       GEN_TAC THEN MATCH_MP_TAC SIMPLE_NUM_UPCROSSINGS_GE_EVENT THEN
       EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
       GEN_TAC THEN MATCH_MP_TAC SIMPLE_NUM_UPCROSSINGS_GE_EVENT THEN
       EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
       SET_TAC[]];
      (* P(UNIONS) <= C / SUC j *)
      SUBGOAL_THEN `(M + abs(a:real)) / (b - a) / &(SUC j) =
                     (M + abs a) / ((b - a) * &(SUC j))`
        SUBST1_TAC THENL
      [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC]; ALL_TAC] THEN
      MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                      `X:num->A->real`; `a:real`; `b:real`; `M:real`]
        SIMPLE_INFINITE_UPCROSSINGS_NULL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `SUC j`) THEN
      REWRITE_TAC[LT_0]]]];
   (* {bad} SUBSET N *)
   REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERS] THEN
   X_GEN_TAC `x:A` THEN STRIP_TAC THEN
   GEN_TAC THEN REWRITE_TAC[SIMPLE_IMAGE; IN_IMAGE; IN_UNIV] THEN
   DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
   REWRITE_TAC[IN_UNIONS] THEN
   REWRITE_TAC[EXISTS_IN_IMAGE; IN_UNIV; IN_ELIM_THM;
               real_ge; REAL_OF_NUM_LE] THEN
   FIRST_X_ASSUM(MP_TAC o
     GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
   DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
   REWRITE_TAC[NOT_FORALL_THM; NOT_LE] THEN
   DISCH_THEN(X_CHOOSE_THEN `nn:num` ASSUME_TAC) THEN
   EXISTS_TAC `nn:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* === Infrastructure for Martingale Convergence Theorem === *)

(* If f(m) <= a and a < b, then upcrossing_phase at m is 1 *)
let UPCROSSING_PHASE_BELOW = prove
 (`!f:num->real a b m. a < b /\ f m <= a
     ==> upcrossing_phase f a b m = 1`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[upcrossing_phase] THEN STRIP_TAC THEN
   COND_CASES_TAC THENL [REFL_TAC; ASM_MESON_TAC[]];
   REWRITE_TAC[upcrossing_phase] THEN STRIP_TAC THEN
   COND_CASES_TAC THENL
   [COND_CASES_TAC THENL [REFL_TAC; ASM_MESON_TAC[]];
    COND_CASES_TAC THENL
    [ASM_REAL_ARITH_TAC; REFL_TAC]]]);;


(* Phase transition from 1: goes to 0 iff f >= b *)
let UPCROSSING_PHASE_TRANSITION_1 = prove
 (`!f:num->real a b m.
     upcrossing_phase f a b m = 1
     ==> (upcrossing_phase f a b (SUC m) = 0 <=> f (SUC m) >= b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[upcrossing_phase] THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(1 = 0)`] THEN
  COND_CASES_TAC THEN SIMP_TAC[ARITH_RULE `~(0 = 1)`; ARITH_RULE `1 = 1`]);;

(* When phase is 1 and f >= b at next step: count increments *)
let UPCROSSING_COUNT_AT_TRANSITION = prove
 (`!f:num->real a b m.
     upcrossing_phase f a b m = 1 /\ f (SUC m) >= b
     ==> upcrossing_count f a b (SUC m) = upcrossing_count f a b m + 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[upcrossing_count] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Key stepping lemma using induction on the gap d *)
let UPCROSSING_COUNT_PHASE1_INCREMENT = prove
 (`!f:num->real a b d m.
     upcrossing_phase f a b m = 1 /\ f (m + SUC d) >= b
     ==> upcrossing_count f a b m + 1 <= upcrossing_count f a b (m + SUC d)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [(* d = 0: m + 1 = SUC m *)
   X_GEN_TAC `m:num` THEN
   REWRITE_TAC[ADD_CLAUSES] THEN
   STRIP_TAC THEN
   MP_TAC(ISPECL [`f:num->real`; `a:real`; `b:real`; `m:num`]
     UPCROSSING_COUNT_AT_TRANSITION) THEN
   ASM_REWRITE_TAC[] THEN ARITH_TAC;
   (* d = SUC d' *)
   X_GEN_TAC `m:num` THEN
   REWRITE_TAC[ADD_CLAUSES] THEN
   STRIP_TAC THEN
   (* Case split on phase at SUC m *)
   MP_TAC(ISPECL [`f:num->real`; `a:real`; `b:real`; `SUC m`]
     UPCROSSING_PHASE_BINARY) THEN
   STRIP_TAC THENL
   [(* Phase(SUC m) = 0: transition happened, f(SUC m) >= b *)
    SUBGOAL_THEN `(f:num->real) (SUC m) >= b` ASSUME_TAC THENL
    [MP_TAC(ISPECL [`f:num->real`; `a:real`; `b:real`; `m:num`]
       UPCROSSING_PHASE_TRANSITION_1) THEN
     ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `upcrossing_count f a b (SUC m) =
                   upcrossing_count (f:num->real) a b m + 1`
      (fun th -> SUBST1_TAC(SYM th)) THENL
    [MATCH_MP_TAC UPCROSSING_COUNT_AT_TRANSITION THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    (* Goal: count(SUC m) <= count(SUC(m + SUC d)) *)
    MATCH_MP_TAC UPCROSSING_COUNT_INCREASING THEN ARITH_TAC;
    (* Phase(SUC m) = 1: use IH with SUC m *)
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `upcrossing_count (f:num->real) a b (SUC m) + 1` THEN
    CONJ_TAC THENL
    [MP_TAC(ISPECL [`f:num->real`; `a:real`; `b:real`; `m:num`]
       UPCROSSING_COUNT_MONO) THEN ARITH_TAC;
     FIRST_X_ASSUM(MP_TAC o SPEC `SUC m`) THEN
     REWRITE_TAC[ADD_CLAUSES] THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]]);;

(* Combined: if f(m1) <= a and f(m2) >= b with m1 < m2 and a < b,
   then count increments *)
let UPCROSSING_COUNT_INCREMENT = prove
 (`!f:num->real a b m1 m2.
     a < b /\ f m1 <= a /\ f m2 >= b /\ m1 < m2
     ==> upcrossing_count f a b m1 + 1 <= upcrossing_count f a b m2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `upcrossing_phase (f:num->real) a b m1 = 1` ASSUME_TAC THENL
  [MATCH_MP_TAC UPCROSSING_PHASE_BELOW THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?d. m2 = m1 + SUC d` (X_CHOOSE_THEN `d:num` SUBST_ALL_TAC)
  THENL [EXISTS_TAC `m2 - m1 - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC UPCROSSING_COUNT_PHASE1_INCREMENT THEN
  ASM_REWRITE_TAC[]);;

(* Upcrossings are unbounded if we visit below a and above b infinitely often *)
let UPCROSSING_COUNT_ITERATE = prove
 (`!f:num->real a b B.
     a < b /\
     (!N. ?m. N <= m /\ f m <= a) /\
     (!N. ?m. N <= m /\ f m >= b)
     ==> ?n. B <= upcrossing_count f a b n`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [STRIP_TAC THEN EXISTS_TAC `0` THEN REWRITE_TAC[LE_0];
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "Hlow") (LABEL_TAC "Hhigh"))) THEN
   (* By IH, find n0 with B <= count(n0) *)
   SUBGOAL_THEN `?n0. B <= upcrossing_count (f:num->real) a b n0`
     (X_CHOOSE_THEN `n0:num` ASSUME_TAC) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
    [GEN_TAC THEN USE_THEN "Hlow" (MP_TAC o SPEC `N:num`) THEN MESON_TAC[];
     GEN_TAC THEN USE_THEN "Hhigh" (MP_TAC o SPEC `N:num`) THEN MESON_TAC[]];
    ALL_TAC] THEN
   (* Find m1 > n0 with f(m1) <= a *)
   USE_THEN "Hlow" (MP_TAC o SPEC `SUC n0`) THEN
   DISCH_THEN(X_CHOOSE_THEN `m1:num` STRIP_ASSUME_TAC) THEN
   (* Find m2 > m1 with f(m2) >= b *)
   USE_THEN "Hhigh" (MP_TAC o SPEC `SUC m1`) THEN
   DISCH_THEN(X_CHOOSE_THEN `m2:num` STRIP_ASSUME_TAC) THEN
   (* count(m2) >= count(m1) + 1 >= count(n0) + 1 >= B + 1 = SUC B *)
   EXISTS_TAC `m2:num` THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `upcrossing_count (f:num->real) a b m1 + 1` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `upcrossing_count (f:num->real) a b n0 + 1` THEN
    CONJ_TAC THENL
    [ASM_ARITH_TAC;
     SUBGOAL_THEN `upcrossing_count (f:num->real) a b n0 <=
                    upcrossing_count f a b m1` MP_TAC THENL
     [MATCH_MP_TAC UPCROSSING_COUNT_INCREASING THEN ASM_ARITH_TAC;
      ARITH_TAC]];
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] UPCROSSING_COUNT_INCREMENT) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

(* Bounded non-convergent sequences oscillate *)
(* If |f(n)| <= M and f doesn't converge, there exist a < b with
   infinitely many visits below a and above b *)

let BOUNDED_NOT_CONVERGENT_IMP_OSCILLATION = prove
 (`!(f:num->real) (M:real).
     &0 <= M /\ (!n. abs(f n) <= M) /\
     ~(?L. !e. &0 < e ==> ?N. !n. N <= n ==> abs(f n - L) < e)
     ==> ?a b. a < b /\
               (!N. ?n. N <= n /\ f n <= a) /\
               (!N. ?n. N <= n /\ f n >= b)`,
  REPEAT STRIP_TAC THEN
  (* Limsup exists: f is bounded above by M, not eventually below -M-1 *)
  SUBGOAL_THEN `?L:real. ((f:num->real) has_limsup L) sequentially`
    (X_CHOOSE_THEN `L:real` (LABEL_TAC "Hsup")) THENL
  [REWRITE_TAC[LIMSUP_EXISTS; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
   CONJ_TAC THENL
   [EXISTS_TAC `M:real` THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `abs(f:real) <= M ==> f <= M`) THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `--M - &1` THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; NOT_EXISTS_THM] THEN
    X_GEN_TAC `N:num` THEN REWRITE_TAC[NOT_FORALL_THM] THEN
    EXISTS_TAC `N:num` THEN REWRITE_TAC[LE_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Liminf exists: f is bounded below by -M, not eventually above M+1 *)
  SUBGOAL_THEN `?l:real. ((f:num->real) has_liminf l) sequentially`
    (X_CHOOSE_THEN `l:real` (LABEL_TAC "Hinf")) THENL
  [REWRITE_TAC[LIMINF_EXISTS; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
   CONJ_TAC THENL
   [EXISTS_TAC `--M:real` THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `abs(f:real) <= M ==> --M <= f`) THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `M + &1` THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; NOT_EXISTS_THM] THEN
    X_GEN_TAC `N:num` THEN REWRITE_TAC[NOT_FORALL_THM] THEN
    EXISTS_TAC `N:num` THEN REWRITE_TAC[LE_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* l < L (if l = L, f would converge, contradicting hypothesis) *)
  SUBGOAL_THEN `l < (L:real)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
   [(* l <= L: if l > L, pick different c values to get contradiction *)
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    (* Use c_high = (2*L + l)/3 for limsup (L < c_high) *)
    USE_THEN "Hsup" (MP_TAC o REWRITE_RULE[HAS_LIMSUP_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o SPEC `(&2 * L + l) / &3`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "Hubound")) THEN
    (* Use c_low = (L + 2*l)/3 for liminf (c_low < l) *)
    USE_THEN "Hinf" (MP_TAC o REWRITE_RULE[HAS_LIMINF_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o SPEC `(L + &2 * l) / &3`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "Hlbound")) THEN
    (* For n >= max(N1,N2): c_low <= f(n) <= c_high, but c_low > c_high *)
    SUBGOAL_THEN `(f:num->real) (N1 + N2) <= (&2 * L + l) / &3`
      ASSUME_TAC THENL
    [USE_THEN "Hubound" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(L + &2 * l) / &3 <= (f:num->real) (N1 + N2)`
      ASSUME_TAC THENL
    [USE_THEN "Hlbound" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    (* l <> L *)
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[] THEN EXISTS_TAC `L:real` THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "Hsup" (MP_TAC o REWRITE_RULE[HAS_LIMSUP_SEQUENTIALLY]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `L + e / &2`) (K ALL_TAC)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` ASSUME_TAC) THEN
    USE_THEN "Hinf" (MP_TAC o REWRITE_RULE[HAS_LIMINF_SEQUENTIALLY]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `L - e / &2`) (K ALL_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` ASSUME_TAC) THEN
    EXISTS_TAC `N1 + N2:num` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
      `&0 < e /\ f <= L + e / &2 /\ L - e / &2 <= f
       ==> abs(f - L) < e`) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
   ALL_TAC] THEN
  (* Now l < L. Extract oscillation. *)
  (* Pick a = (2l + L)/3 and b = (l + 2L)/3, so l < a < b < L *)
  EXISTS_TAC `(&2 * l + L) / &3` THEN EXISTS_TAC `(l + &2 * L) / &3` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
  [(* Infinitely many visits <= a: from liminf characterization *)
   X_GEN_TAC `N:num` THEN
   USE_THEN "Hinf" (MP_TAC o REWRITE_RULE[HAS_LIMINF_SEQUENTIALLY]) THEN
   DISCH_THEN(MP_TAC o CONJUNCT2) THEN
   DISCH_THEN(MP_TAC o SPEC `(&2 * l + L) / &3`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPEC `N:num`) THEN
   REWRITE_TAC[real_ge] THEN
   MESON_TAC[REAL_LT_IMP_LE];
   (* Infinitely many visits >= b: from limsup characterization *)
   X_GEN_TAC `N:num` THEN
   USE_THEN "Hsup" (MP_TAC o REWRITE_RULE[HAS_LIMSUP_SEQUENTIALLY]) THEN
   DISCH_THEN(MP_TAC o CONJUNCT2) THEN
   DISCH_THEN(MP_TAC o SPEC `(l + &2 * L) / &3`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPEC `N:num`) THEN
   REWRITE_TAC[real_ge] THEN
   MESON_TAC[REAL_LT_IMP_LE]]);;

(* Helper: bounded sequence with finite upcrossings for all rational pairs
   must converge. Contrapositive of oscillation + upcrossing iterate. *)
let BOUNDED_FINITE_UPCROSSINGS_IMP_CONVERGENT = prove
 (`!(f:num->real) M.
     (!n. abs(f n) <= M) /\
     (!a b. rational a /\ rational b /\ a < b
            ==> ?B. !n. upcrossing_count f a b n <= B)
     ==> ?L. (f ---> L) sequentially`,
  REPEAT STRIP_TAC THEN
  (* Proof by contradiction *)
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  (* f doesn't converge, so by BOUNDED_NOT_CONVERGENT_IMP_OSCILLATION,
     there exist a < b with infinite oscillation *)
  MP_TAC(ISPECL [`f:num->real`; `M:real`]
    BOUNDED_NOT_CONVERGENT_IMP_OSCILLATION) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((f:num->real) 0)` THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[GSYM REALLIM_SEQUENTIALLY];
   ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Hlow") (LABEL_TAC "Hhigh"))) THEN
  (* Find rationals q1, q2 with a < q1 < q2 < b *)
  MP_TAC(ISPECL [`a:real`; `(a + b) / &2`] RATIONAL_BETWEEN) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(a + b) / &2`; `b:real`] RATIONAL_BETWEEN) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real` STRIP_ASSUME_TAC) THEN
  (* f visits <= q1 infinitely often (since visits <= a and a < q1) *)
  SUBGOAL_THEN `!N. ?n. N <= n /\ (f:num->real) n <= q1` ASSUME_TAC THENL
  [X_GEN_TAC `N:num` THEN
   USE_THEN "Hlow" (MP_TAC o SPEC `N:num`) THEN
   DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* f visits >= q2 infinitely often (since visits >= b and q2 < b) *)
  SUBGOAL_THEN `!N. ?n. N <= n /\ (f:num->real) n >= q2` ASSUME_TAC THENL
  [X_GEN_TAC `N:num` THEN
   USE_THEN "Hhigh" (MP_TAC o SPEC `N:num`) THEN
   DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[real_ge] THEN
   ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* By UPCROSSING_COUNT_ITERATE, upcrossings of (q1, q2) are unbounded *)
  (* But hypothesis says they're bounded: contradiction *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`q1:real`; `q2:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:num` ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:num->real`; `q1:real`; `q2:real`; `SUC B`]
    UPCROSSING_COUNT_ITERATE) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ARITH_TAC);;

(* ALMOST_SURELY_COUNTABLE_INTER: defined in expectation.ml *)

(* ========================================================================= *)
(* SIMPLE_MARTINGALE CONVERGENCE THEOREM (bounded simple_submartingale version)            *)
(* ========================================================================= *)

(* Rational numbers can be enumerated *)
let RATIONAL_ENUMERATION = prove
 (`?g:num->real. rational = IMAGE g (:num)`,
  MATCH_MP_TAC COUNTABLE_AS_IMAGE THEN
  REWRITE_TAC[COUNTABLE_RATIONAL] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  EXISTS_TAC `&0` THEN REWRITE_TAC[IN; RATIONAL_NUM]);;

(* UNIV is almost sure *)
let ALMOST_SURELY_UNIV = prove
 (`!p:A prob_space. almost_surely p (:A)`,
  GEN_TAC THEN REWRITE_TAC[almost_surely] THEN
  EXISTS_TAC `{}:A->bool` THEN
  REWRITE_TAC[NULL_EVENT_EMPTY] THEN
  SET_TAC[]);;

(* Main theorem: bounded simple_submartingale converges almost surely *)
let SIMPLE_MARTINGALE_CONVERGENCE_BOUNDED = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) M.
     simple_submartingale p FF X /\
     (!m x. x IN prob_carrier p ==> abs(X m x) <= M)
     ==> almost_surely p
           {x | ?L. ((\n. X n x) ---> L) sequentially}`,
  REPEAT STRIP_TAC THEN
  MP_TAC RATIONAL_ENUMERATION THEN
  DISCH_THEN(X_CHOOSE_TAC `g:num->real`) THEN
  (* Step 1: For each k, the upcrossing bound property is a.s. *)
  SUBGOAL_THEN
    `!k. almost_surely (p:A prob_space)
       {x:A | (g:num->real)(NUMFST k) < g(NUMSND k) ==>
              (?B. !n. num_upcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)}`
    ASSUME_TAC THENL
  [X_GEN_TAC `k:num` THEN
   ASM_CASES_TAC `(g:num->real)(NUMFST k) < g(NUMSND k)` THENL
   [(* Case a < b: use SIMPLE_FINITE_UPCROSSINGS_AS + ALMOST_SURELY_SUBSET *)
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x:A | ?B. !n. num_upcrossings (X:num->A->real)
                  ((g:num->real)(NUMFST k)) (g(NUMSND k)) n x <= B}` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_FINITE_UPCROSSINGS_AS THEN
     MAP_EVERY EXISTS_TAC
       [`FF:num->(A->bool)->bool`; `M:real`] THEN
     ASM_REWRITE_TAC[];
     REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    (* Case a >= b: S_k = UNIV, so a.s. trivially *)
    SUBGOAL_THEN
      `{x:A | (g:num->real)(NUMFST k) < g(NUMSND k) ==>
              (?B. !n. num_upcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)} = (:A)`
      (fun th -> REWRITE_TAC[th; ALMOST_SURELY_UNIV]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
    ASM_MESON_TAC[]];
   ALL_TAC] THEN
  (* Step 2+3: a.s. of intersection => convergence *)
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
    `INTERS {{x:A | (g:num->real)(NUMFST k) < g(NUMSND k) ==>
              (?B. !n. num_upcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)}
             | k IN (:num)}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN ASM_REWRITE_TAC[];
   (* Containment: INTERS membership => convergence *)
   REWRITE_TAC[IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[IN_INTERS] THEN DISCH_TAC THEN
   (* Extract: for all k, the upcrossing bound property holds *)
   SUBGOAL_THEN
     `!k. (g:num->real)(NUMFST k) < g(NUMSND k)
          ==> ?B. !n. num_upcrossings (X:num->A->real)
                        (g(NUMFST k)) (g(NUMSND k)) n x <= B`
     ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `{x:A | (g:num->real)(NUMFST (k:num)) < g(NUMSND k) ==>
              (?B. !n. num_upcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)}`) THEN
    ANTS_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
     EXISTS_TAC `k:num` THEN REFL_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   (* Apply BOUNDED_FINITE_UPCROSSINGS_IMP_CONVERGENT *)
   MP_TAC(ISPECL [`\n:num. (X:num->A->real) n x`; `M:real`]
     BOUNDED_FINITE_UPCROSSINGS_IMP_CONVERGENT) THEN
   REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    (* Find i,j with g(i) = a, g(j) = b *)
    SUBGOAL_THEN `?i:num. (g:num->real) i = a` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o SPEC `a:real` o
       GEN_REWRITE_RULE I [EXTENSION]) THEN
     REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
     ASM_REWRITE_TAC[IN] THEN MESON_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `?j:num. (g:num->real) j = b` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o SPEC `b:real` o
       GEN_REWRITE_RULE I [EXTENSION]) THEN
     REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
     ASM_REWRITE_TAC[IN] THEN MESON_TAC[];
     ALL_TAC] THEN
    (* Use k = NUMPAIR i j *)
    FIRST_X_ASSUM(MP_TAC o SPEC `NUMPAIR i j`) THEN
    REWRITE_TAC[NUMPAIR_DEST] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `B:num`) THEN
    EXISTS_TAC `B:num` THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[num_upcrossings];
    ALL_TAC] THEN
   REWRITE_TAC[]]);;

(* ========================================================================= *)
(* ATOMS OF FINITE SIGMA-ALGEBRAS                                            *)
(* ========================================================================= *)

(* The atom containing x: intersection of all G-sets containing x *)
let sigma_atom = new_definition
  `sigma_atom (G:(A->bool)->bool) (x:A) =
   INTERS {b | b IN G /\ x IN b}`;;

(* x is always in its own atom *)
let SIGMA_ATOM_CONTAINS = prove
 (`!(G:(A->bool)->bool) (x:A). x IN UNIONS G ==> x IN sigma_atom G x`,
  REWRITE_TAC[sigma_atom; IN_INTERS; IN_ELIM_THM] THEN MESON_TAC[]);;

(* The atom is a subset of any G-set containing x *)
let SIGMA_ATOM_SUBSET = prove
 (`!(G:(A->bool)->bool) (x:A) (b:A->bool).
     b IN G /\ x IN b ==> sigma_atom G x SUBSET b`,
  REWRITE_TAC[sigma_atom; SUBSET; IN_INTERS; IN_ELIM_THM] THEN MESON_TAC[]);;

(* Atom is a subset of the carrier *)
let SIGMA_ATOM_SUBSET_CARRIER = prove
 (`!(G:(A->bool)->bool) (x:A).
     sigma_algebra G /\ x IN UNIONS G
     ==> sigma_atom G x SUBSET UNIONS G`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIGMA_ATOM_SUBSET THEN
  ASM_MESON_TAC[SIGMA_ALGEBRA_CARRIER]);;

(* For a finite sigma-algebra, the atom is in G *)
let SIGMA_ATOM_IN_G = prove
 (`!(G:(A->bool)->bool) (x:A).
     sigma_algebra G /\ FINITE G /\ x IN UNIONS G
     ==> sigma_atom G x IN G`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sigma_atom] THEN
  MATCH_MP_TAC SIGMA_ALGEBRA_INTERS_FINITE THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
   MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `G:(A->bool)->bool` THEN
   ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   EXISTS_TAC `UNIONS G:A->bool` THEN
   ASM_MESON_TAC[SIGMA_ALGEBRA_CARRIER]]);;


(* If y is in the atom of x, then their atoms are equal *)
let SIGMA_ATOM_SAME = prove
 (`!(G:(A->bool)->bool) (x:A) (y:A).
     sigma_algebra G /\ x IN UNIONS G /\ y IN sigma_atom G x
     ==> sigma_atom G y = sigma_atom G x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sigma_atom; EXTENSION; IN_INTERS; IN_ELIM_THM] THEN
  X_GEN_TAC `z:A` THEN EQ_TAC THENL
  [(* z in atom(y) ==> z in atom(x) *)
   DISCH_TAC THEN X_GEN_TAC `b:A->bool` THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `b:A->bool`) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:A) IN sigma_atom G x` THEN
    REWRITE_TAC[sigma_atom; IN_INTERS; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `b:A->bool`) THEN ASM_REWRITE_TAC[];
    SIMP_TAC[]];
   (* z in atom(x) ==> z in atom(y) *)
   DISCH_TAC THEN X_GEN_TAC `b:A->bool` THEN STRIP_TAC THEN
   (* First show x IN b by contradiction *)
   SUBGOAL_THEN `(x:A) IN b` ASSUME_TAC THENL
   [ASM_CASES_TAC `(x:A) IN b` THEN ASM_REWRITE_TAC[] THEN
    (* x not in b, so atom(x) SUBSET UNIONS G DIFF b *)
    SUBGOAL_THEN `sigma_atom G (x:A) SUBSET (UNIONS G DIFF b)` MP_TAC THENL
    [MATCH_MP_TAC SIGMA_ATOM_SUBSET THEN
     ASM_REWRITE_TAC[IN_DIFF] THEN ASM_MESON_TAC[SIGMA_ALGEBRA_COMPL];
     (* But y IN atom(x) and y IN b, contradiction *)
     REWRITE_TAC[SUBSET; IN_DIFF] THEN
     DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[]];
    (* Now x IN b, so z IN b from z IN atom(x) *)
    FIRST_X_ASSUM(MP_TAC o SPEC `b:A->bool`) THEN ASM_REWRITE_TAC[]]]);;

(* Atoms are either equal or disjoint *)
let SIGMA_ATOM_EQUAL_OR_DISJOINT = prove
 (`!(G:(A->bool)->bool) (x:A) (y:A).
     sigma_algebra G /\ FINITE G /\ x IN UNIONS G /\ y IN UNIONS G
     ==> sigma_atom G x = sigma_atom G y \/
         DISJOINT (sigma_atom G x) (sigma_atom G y)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `DISJOINT (sigma_atom G (x:A)) (sigma_atom G y)` THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISJ1_TAC THEN
  (* They intersect, so pick z in the intersection *)
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[DISJOINT; EXTENSION;
    IN_INTER; NOT_IN_EMPTY; NOT_FORALL_THM; DE_MORGAN_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `z:A`) THEN
  (* z IN sigma_atom G x, so sigma_atom G z = sigma_atom G x *)
  SUBGOAL_THEN `sigma_atom G (z:A) = sigma_atom G x` (SUBST1_TAC o GSYM) THENL
  [MATCH_MP_TAC SIGMA_ATOM_SAME THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SIGMA_ATOM_SAME THEN ASM_MESON_TAC[]);;

(* The set of atoms is finite when G is finite *)
let FINITE_SIGMA_ATOMS = prove
 (`!(G:(A->bool)->bool).
     sigma_algebra G /\ FINITE G
     ==> FINITE {sigma_atom G (x:A) | x | x IN UNIONS G}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `G:(A->bool)->bool` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SIGMA_ATOM_IN_G]);;

(* Every G-set is a union of atoms *)
let G_SET_UNION_OF_ATOMS = prove
 (`!(G:(A->bool)->bool) (s:A->bool).
     sigma_algebra G /\ s IN G
     ==> s = UNIONS {sigma_atom G (x:A) | x | x IN s}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `z:A` THEN EQ_TAC THENL
  [DISCH_TAC THEN EXISTS_TAC `sigma_atom G (z:A)` THEN
   CONJ_TAC THENL
   [EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SIGMA_ATOM_CONTAINS THEN
    REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[]];
   DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
   SUBGOAL_THEN `sigma_atom G (w:A) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SIGMA_ATOM_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[SUBSET]]);;


(* ========================================================================= *)
(* CONDITIONAL EXPECTATION FOR SIMPLE RANDOM VARIABLES                       *)
(* ========================================================================= *)

(* Constructive definition: E[X | G] using atoms of G *)
let simple_cond_exp = new_definition
  `simple_cond_exp (p:A prob_space) (G:(A->bool)->bool) (X:A->real) (x:A) =
   if prob p (sigma_atom G x) = &0 then &0
   else simple_expectation p (\y. X y * indicator_fn (sigma_atom G x) y) /
        prob p (sigma_atom G x)`;;

(* Conditional expectation is constant on atoms *)
let SIMPLE_COND_EXP_CONSTANT_ON_ATOM = prove
 (`!p:A prob_space G (X:A->real) (x:A) (y:A).
     sigma_algebra G /\ x IN UNIONS G /\ y IN sigma_atom G x
     ==> simple_cond_exp p G X y = simple_cond_exp p G X x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[simple_cond_exp] THEN
  SUBGOAL_THEN `sigma_atom G (y:A) = sigma_atom G (x:A)`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC SIGMA_ATOM_SAME THEN ASM_REWRITE_TAC[]);;

(* E[X * 1_A] = 0 when P(A) = 0 *)
let SIMPLE_EXPECTATION_MUL_INDICATOR_ZERO_PROB = prove
 (`!p:A prob_space (X:A->real) (S:A->bool).
     simple_rv p X /\ S IN prob_events p /\ prob p S = &0
     ==> simple_expectation p (\x. X x * indicator_fn S x) = &0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[simple_expectation] THEN
  MATCH_MP_TAC SUM_EQ_0 THEN
  X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `v = &0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  SUBGOAL_THEN
    `prob p {x:A | x IN prob_carrier p /\
      (X:A->real) x * indicator_fn S x = v} = &0`
    (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
  (* For v <> 0: {x | X x * 1_S x = v} = {x | X x = v} INTER S *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (X:A->real) x *
      indicator_fn (S:A->bool) x = v} =
     {x | x IN prob_carrier p /\ X x = v} INTER S`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
   X_GEN_TAC `w:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `(w:A) IN S` ASSUME_TAC THENL
    [ASM_CASES_TAC `(w:A) IN S` THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `(X:A->real) w * indicator_fn (S:A->bool) w = v` THEN
     REWRITE_TAC[indicator_fn] THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(X:A->real) w * indicator_fn (S:A->bool) w = v` THEN
    REWRITE_TAC[indicator_fn] THEN ASM_REWRITE_TAC[REAL_MUL_RID];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[indicator_fn] THEN ASM_REWRITE_TAC[REAL_MUL_RID]];
   ALL_TAC] THEN
  (* Now the set is {X=v} INTER S, both are events *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (X:A->real) x = v} INTER S
     IN prob_events p` ASSUME_TAC THENL
  [MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_LEVEL_SET THEN ASM_MESON_TAC[simple_rv];
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `prob p (S:A->bool)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC PROB_MONO THEN
   CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SET_TAC[];
   ASM_REWRITE_TAC[REAL_LE_REFL]]);;

(* The range of simple_cond_exp is finite on the carrier *)
let SIMPLE_COND_EXP_RANGE_FINITE = prove
 (`!p:A prob_space G (X:A->real).
     sub_sigma_algebra p G /\ FINITE G
     ==> FINITE {simple_cond_exp p G X x | x | x IN prob_carrier p}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS G = prob_carrier (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\(a:A->bool).
    if prob (p:A prob_space) a = &0 then &0
    else simple_expectation p (\y. (X:A->real) y * indicator_fn a y) /
         prob p a) {sigma_atom G (x:A) | x | x IN UNIONS G}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SIGMA_ATOMS THEN
   ASM_MESON_TAC[sub_sigma_algebra];
   ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `v:real` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `sigma_atom G (w:A)` THEN CONJ_TAC THENL
  [ASM_REWRITE_TAC[simple_cond_exp]; ALL_TAC] THEN
  EXISTS_TAC `w:A` THEN ASM_MESON_TAC[]);;

(* simple_cond_exp is G-measurable *)
let SIMPLE_COND_EXP_MEASURABLE_WRT_G = prove
 (`!p:A prob_space G (X:A->real).
     sub_sigma_algebra p G /\ FINITE G
     ==> measurable_wrt p G (simple_cond_exp p G X)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS G = prob_carrier (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  REWRITE_TAC[measurable_wrt] THEN X_GEN_TAC `v:real` THEN
  (* Show {x | x IN carrier /\ simple_cond_exp x <= v} =
     UNIONS {sigma_atom G x | x IN carrier /\ simple_cond_exp x <= v} *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ simple_cond_exp p G (X:A->real) x <= v} =
     UNIONS {sigma_atom G (x:A) | x |
       x IN prob_carrier p /\ simple_cond_exp p G X x <= v}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
   X_GEN_TAC `z:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `sigma_atom G (z:A)` THEN
    CONJ_TAC THENL
    [EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC SIGMA_ATOM_CONTAINS THEN ASM_MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC)
                        ASSUME_TAC)) THEN
    CONJ_TAC THENL
    [SUBGOAL_THEN `sigma_atom G (w:A) SUBSET UNIONS G` MP_TAC THENL
     [MATCH_MP_TAC SIGMA_ATOM_SUBSET_CARRIER THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[SUBSET]];
     SUBGOAL_THEN `simple_cond_exp p G (X:A->real) z =
                   simple_cond_exp p G X w` SUBST1_TAC THENL
     [MATCH_MP_TAC SIMPLE_COND_EXP_CONSTANT_ON_ATOM THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[]]]];
   ALL_TAC] THEN
  (* Show this union is in G *)
  MATCH_MP_TAC SIGMA_ALGEBRA_UNIONS_FINITE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `t:A->bool` THEN
   DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC SIGMA_ATOM_IN_G THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
   MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC `{sigma_atom G (x:A) | x | x IN UNIONS G}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SIGMA_ATOMS THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]]]);;

(* Conditioning property for individual atoms *)
let SIMPLE_COND_EXP_ATOM_COND = prove
 (`!p:A prob_space G (X:A->real) (x:A).
     sub_sigma_algebra p G /\ FINITE G /\ simple_rv p X /\
     x IN prob_carrier p
     ==> simple_expectation p
           (\y. simple_cond_exp p G X y *
                indicator_fn (sigma_atom G x) y) =
         simple_expectation p
           (\y. X y * indicator_fn (sigma_atom G x) y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS G = prob_carrier (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN UNIONS G` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sigma_atom G (x:A) IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[SIGMA_ATOM_IN_G; sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
  ASM_CASES_TAC `prob p (sigma_atom G (x:A)) = &0` THENL
  [(* Case: P(atom) = 0 -- both sides are 0 *)
   (* First establish simple_rv for simple_cond_exp *)
   SUBGOAL_THEN `measurable_wrt p G (simple_cond_exp p G (X:A->real))`
     ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`; `X:A->real`]
      SIMPLE_COND_EXP_MEASURABLE_WRT_G) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv p (simple_cond_exp p G (X:A->real))` ASSUME_TAC THENL
   [REWRITE_TAC[simple_rv] THEN CONJ_TAC THENL
    [ASM_MESON_TAC[MEASURABLE_WRT_IMP_RV];
     MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`; `X:A->real`]
        SIMPLE_COND_EXP_RANGE_FINITE) THEN
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* Now show both sides equal 0 *)
   MP_TAC(ISPECL [`p:A prob_space`; `simple_cond_exp p G (X:A->real)`;
                   `sigma_atom G (x:A)`] SIMPLE_EXPECTATION_MUL_INDICATOR_ZERO_PROB) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
                   `sigma_atom G (x:A)`] SIMPLE_EXPECTATION_MUL_INDICATOR_ZERO_PROB) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   ASM_REWRITE_TAC[];
   (* Case: P(atom) > 0 *)
   (* simple_cond_exp is constant on atom with value c *)
   ABBREV_TAC `c = simple_cond_exp p G (X:A->real) x` THEN
   (* LHS = c * P(atom) by constant-on-atom + linearity *)
   SUBGOAL_THEN
     `simple_expectation p
       (\y. simple_cond_exp p G (X:A->real) y *
            indicator_fn (sigma_atom G x) y) =
      c * prob p (sigma_atom G x)` SUBST1_TAC THENL
   [SUBGOAL_THEN
      `simple_expectation p
        (\y. simple_cond_exp p G (X:A->real) y *
             indicator_fn (sigma_atom G x) y) =
       simple_expectation p (\y. c * indicator_fn (sigma_atom G x) y)`
      SUBST1_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`;
        `\y:A. simple_cond_exp p G (X:A->real) y *
               indicator_fn (sigma_atom G (x:A)) y`;
        `\y:A. c * indicator_fn (sigma_atom G (x:A)) y`]
        SIMPLE_EXPECTATION_EXT) THEN
     ANTS_TAC THENL
     [X_GEN_TAC `z:A` THEN DISCH_TAC THEN BETA_TAC THEN
      REWRITE_TAC[indicator_fn] THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      EXPAND_TAC "c" THEN
      MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
                      `X:A->real`; `x:A`; `z:A`]
        SIMPLE_COND_EXP_CONSTANT_ON_ATOM) THEN
      ASM_REWRITE_TAC[];
      BETA_TAC THEN SIMP_TAC[]];
     ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `indicator_fn (sigma_atom G (x:A))`;
                    `c:real`] SIMPLE_EXPECTATION_CMUL) THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC SIMPLE_EXPECTATION_INDICATOR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* c = E[X * 1_atom] / P(atom), so c * P(atom) = E[X * 1_atom] *)
   EXPAND_TAC "c" THEN REWRITE_TAC[simple_cond_exp] THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REWRITE_TAC[]]);;

(* Conditioning property extended to arbitrary G-sets *)
let SIMPLE_COND_EXP_CONDITIONING = prove
 (`!p:A prob_space G (X:A->real) (a:A->bool).
     sub_sigma_algebra p G /\ FINITE G /\ simple_rv p X /\ a IN G
     ==> simple_expectation p
           (\x. simple_cond_exp p G X x * indicator_fn a x) =
         simple_expectation p (\x. X x * indicator_fn a x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS G = prob_carrier (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  (* a = UNIONS of atoms in a *)
  SUBGOAL_THEN `(a:A->bool) = UNIONS {sigma_atom G (x:A) | x | x IN a}`
    (LABEL_TAC "a_eq") THENL
  [MATCH_MP_TAC G_SET_UNION_OF_ATOMS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Key: for x in carrier, 1_a(x) = 1 iff atom(x) SUBSET a *)
  (* And if atom(x) SUBSET a, then atom(x) = atom(y) for some y IN a *)
  (* Strategy: show both expectations are equal by showing they agree
     pointwise on the carrier using the atom decomposition *)
  (* We use: on the carrier, for any function f,
     f(x) * 1_a(x) = f(x) * 1_{atom(x)}(x) if atom(x) SUBSET a, else 0 *)
  (* First, relate 1_a to atoms:
     For x IN carrier: x IN a iff sigma_atom G x SUBSET a *)
  SUBGOAL_THEN
    `!z:A. z IN prob_carrier p
           ==> (z IN a <=> sigma_atom G z SUBSET a)` (LABEL_TAC "atom_iff") THENL
  [X_GEN_TAC `z:A` THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC SIGMA_ATOM_SUBSET THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `(z:A) IN sigma_atom G z` MP_TAC THENL
    [MATCH_MP_TAC SIGMA_ATOM_CONTAINS THEN ASM_MESON_TAC[];
     ASM SET_TAC[]]];
   ALL_TAC] THEN
  (* Show: both sides decompose as sums over the (finitely many) distinct atoms
     that are subsets of a *)
  ABBREV_TAC
    `atoms = {sigma_atom G (x:A) | x | x IN prob_carrier (p:A prob_space)}` THEN
  ABBREV_TAC
    `atoms_a = {(A:A->bool) | A IN atoms /\ A SUBSET a}` THEN
  SUBGOAL_THEN `FINITE (atoms:((A->bool)->bool))` ASSUME_TAC THENL
  [EXPAND_TAC "atoms" THEN ASM_MESON_TAC[FINITE_SIGMA_ATOMS; sub_sigma_algebra];
   ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (atoms_a:((A->bool)->bool))` ASSUME_TAC THENL
  [EXPAND_TAC "atoms_a" THEN MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC `atoms:((A->bool)->bool)` THEN ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   MESON_TAC[];
   ALL_TAC] THEN
  (* The atoms in atoms_a are pairwise disjoint *)
  SUBGOAL_THEN
    `!A1 A2:A->bool. A1 IN atoms_a /\ A2 IN atoms_a /\ ~(A1 = A2)
                      ==> DISJOINT A1 A2` (LABEL_TAC "pd") THENL
  [EXPAND_TAC "atoms_a" THEN EXPAND_TAC "atoms" THEN
   REWRITE_TAC[IN_ELIM_THM] THEN
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   ASM_MESON_TAC[SIGMA_ATOM_EQUAL_OR_DISJOINT];
   ALL_TAC] THEN
  (* Each atom in atoms_a is an event *)
  SUBGOAL_THEN `!A:A->bool. A IN atoms_a ==> A IN prob_events p`
    (LABEL_TAC "ev") THENL
  [EXPAND_TAC "atoms_a" THEN EXPAND_TAC "atoms" THEN
   REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[SIGMA_ATOM_IN_G; sub_sigma_algebra; SUBSET];
   ALL_TAC] THEN
  (* a = UNIONS atoms_a *)
  SUBGOAL_THEN `(a:A->bool) = UNIONS atoms_a` (LABEL_TAC "a_union") THENL
  [REWRITE_TAC[EXTENSION; IN_UNIONS] THEN X_GEN_TAC `z:A` THEN EQ_TAC THENL
   [(* z IN a ==> z IN UNIONS atoms_a *)
    DISCH_TAC THEN
    EXISTS_TAC `sigma_atom G (z:A)` THEN CONJ_TAC THENL
    [(* sigma_atom G z IN atoms_a *)
     EXPAND_TAC "atoms_a" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [EXPAND_TAC "atoms" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      EXISTS_TAC `z:A` THEN ASM_MESON_TAC[PROB_EVENT_SUBSET; sub_sigma_algebra; SUBSET];
      USE_THEN "atom_iff" (MP_TAC o SPEC `z:A`) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[PROB_EVENT_SUBSET; sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
      ASM_MESON_TAC[]];
     (* z IN sigma_atom G z *)
     MATCH_MP_TAC SIGMA_ATOM_CONTAINS THEN
     ASM_MESON_TAC[PROB_EVENT_SUBSET; sub_sigma_algebra; SUBSET]];
    (* z IN UNIONS atoms_a ==> z IN a *)
    DISCH_THEN(X_CHOOSE_THEN `B:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(B:A->bool) SUBSET a` MP_TAC THENL
    [UNDISCH_TAC `(B:A->bool) IN atoms_a` THEN
     EXPAND_TAC "atoms_a" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
     ASM SET_TAC[]]];
   ALL_TAC] THEN
  (* Both sides equal sum over atoms_a of the per-atom expectations *)
  (* We prove: for f = simple_cond_exp or X, and for x in carrier:
     f(x) * 1_a(x) = sum over atoms_a of (f(x) * 1_A(x)) *)
  (* Key helper: z NOT IN B for B in atoms_a with B <> sigma_atom G z *)
  SUBGOAL_THEN
    `!z:A B:A->bool. z IN prob_carrier p /\ z IN a /\
     B IN atoms_a /\ ~(B = sigma_atom G z)
     ==> ~(z IN B)` (LABEL_TAC "not_in_other") THENL
  [REPEAT STRIP_TAC THEN
   REMOVE_THEN "pd" (MP_TAC o SPECL [`sigma_atom G (z:A)`; `B:A->bool`]) THEN
   SUBGOAL_THEN `sigma_atom G (z:A) IN atoms_a` ASSUME_TAC THENL
   [EXPAND_TAC "atoms_a" THEN EXPAND_TAC "atoms" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL
    [EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC SIGMA_ATOM_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
   DISCH_THEN(MP_TAC o SPEC `z:A`) THEN
   SUBGOAL_THEN `(z:A) IN sigma_atom G z` ASSUME_TAC THENL
   [MATCH_MP_TAC SIGMA_ATOM_CONTAINS THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Indicator decomposition: for z in carrier, f z * 1_a(z) = sum over atoms *)
  SUBGOAL_THEN
    `!f:A->real z. z IN prob_carrier p
     ==> f z * indicator_fn a z =
         sum atoms_a (\A. f z * indicator_fn A z)` (LABEL_TAC "decomp") THENL
  [REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `(z:A) IN a` THENL
   [(* z IN a: sigma_atom G z IN atoms_a, and z is in that atom only *)
    SUBGOAL_THEN `sigma_atom G (z:A) IN atoms_a` ASSUME_TAC THENL
    [EXPAND_TAC "atoms_a" THEN EXPAND_TAC "atoms" THEN
     REWRITE_TAC[IN_ELIM_THM] THEN
     CONJ_TAC THENL
     [EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SIGMA_ATOM_SUBSET THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
    SUBGOAL_THEN `(z:A) IN sigma_atom G z` ASSUME_TAC THENL
    [MATCH_MP_TAC SIGMA_ATOM_CONTAINS THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    (* Use SUM_DELETE to split off the sigma_atom G z term *)
    SUBGOAL_THEN
      `sum atoms_a (\A. (f:A->real) z * indicator_fn A z) =
       f z * indicator_fn (sigma_atom G z) z +
       sum (atoms_a DELETE sigma_atom G (z:A)) (\A. f z * indicator_fn A z)`
      SUBST1_TAC THENL
    [MP_TAC(ISPECL [`\(A:A->bool). (f:A->real) z * indicator_fn A z`;
                     `atoms_a:((A->bool)->bool)`; `sigma_atom G (z:A)`]
       SUM_DELETE) THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    (* indicator_fn (sigma_atom G z) z = 1 *)
    REWRITE_TAC[indicator_fn] THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
    (* sum_rest = 0 *)
    SUBGOAL_THEN
      `sum (atoms_a DELETE sigma_atom G (z:A))
           (\A. (f:A->real) z * if z IN A then &1 else &0) = &0`
      (fun th -> REWRITE_TAC[th; REAL_ADD_RID]) THEN
    MATCH_MP_TAC SUM_EQ_0 THEN
    REWRITE_TAC[IN_DELETE] THEN
    X_GEN_TAC `B:A->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((z:A) IN B)` (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
    USE_THEN "not_in_other" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* z NOT IN a: LHS = 0, sum is all zeros *)
    REWRITE_TAC[indicator_fn] THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_EQ_0 THEN
    X_GEN_TAC `B:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((z:A) IN B)`
      (fun th -> REWRITE_TAC[indicator_fn; th; REAL_MUL_RZERO]) THEN
    UNDISCH_TAC `~((z:A) IN a)` THEN
    SUBGOAL_THEN `(B:A->bool) SUBSET a` MP_TAC THENL
    [UNDISCH_TAC `(B:A->bool) IN atoms_a` THEN
     EXPAND_TAC "atoms_a" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
     SET_TAC[]]];
   ALL_TAC] THEN
  (* Now use linearity to push sum through expectation *)
  (* LHS = sum_atoms_a E[simple_cond_exp * 1_A] *)
  SUBGOAL_THEN
    `simple_expectation p (\x. simple_cond_exp p G (X:A->real) x *
       indicator_fn a x) =
     sum atoms_a (\A. simple_expectation p
       (\x. simple_cond_exp p G X x * indicator_fn A x))`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
     `simple_expectation p (\x. simple_cond_exp p G (X:A->real) x *
        indicator_fn a x) =
      simple_expectation p
        (\x. sum atoms_a (\A. simple_cond_exp p G X x * indicator_fn A x))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    REMOVE_THEN "decomp" (MP_TAC o SPECL
      [`simple_cond_exp p G (X:A->real)`; `z:A`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   MP_TAC(ISPECL
     [`p:A prob_space`;
      `\(A:A->bool) (x:A). simple_cond_exp p G (X:A->real) x *
         indicator_fn A x`;
      `atoms_a:(A->bool)->bool`]
     SIMPLE_EXPECTATION_SUM_FINITE) THEN
   BETA_TAC THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `B:A->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THENL
    [ALL_TAC; MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_MESON_TAC[]] THEN
    REWRITE_TAC[simple_rv] THEN CONJ_TAC THENL
    [MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
     EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC SIMPLE_COND_EXP_MEASURABLE_WRT_G THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC SIMPLE_COND_EXP_RANGE_FINITE THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[]];
   ALL_TAC] THEN
  (* RHS = sum_atoms_a E[X * 1_A] *)
  SUBGOAL_THEN
    `simple_expectation p (\x. (X:A->real) x * indicator_fn a x) =
     sum atoms_a (\A. simple_expectation p (\x. X x * indicator_fn A x))`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
     `simple_expectation p (\x. (X:A->real) x * indicator_fn a x) =
      simple_expectation p
        (\x. sum atoms_a (\A. X x * indicator_fn A x))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    REMOVE_THEN "decomp" (MP_TAC o SPECL [`X:A->real`; `z:A`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   MP_TAC(ISPECL
     [`p:A prob_space`;
      `\(A:A->bool) (x:A). (X:A->real) x * indicator_fn A x`;
      `atoms_a:(A->bool)->bool`]
     SIMPLE_EXPECTATION_SUM_FINITE) THEN
   BETA_TAC THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `B:A->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THENL
    [ASM_MESON_TAC[simple_rv];
     MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_MESON_TAC[]];
    SIMP_TAC[]];
   ALL_TAC] THEN
  (* Now apply per-atom conditioning *)
  MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `B:A->bool` THEN DISCH_TAC THEN BETA_TAC THEN
  (* B is an atom of some x IN carrier *)
  SUBGOAL_THEN `?w:A. w IN prob_carrier p /\ sigma_atom G w = B`
    (X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THENL
  [UNDISCH_TAC `(B:A->bool) IN atoms_a` THEN
   EXPAND_TAC "atoms_a" THEN EXPAND_TAC "atoms" THEN
   REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `B = sigma_atom G (w:A):A->bool` SUBST1_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SIMPLE_COND_EXP_ATOM_COND THEN ASM_REWRITE_TAC[]);;

(* Existence of conditional expectation for simple RVs
   NOTE: Requires FINITE G because E[X|G] is only guaranteed simple
   when G is a finite sigma-algebra *)
let SIMPLE_COND_EXP_EXISTS = prove
 (`!p:A prob_space G (X:A->real).
     sub_sigma_algebra p G /\ FINITE G /\ simple_rv p X
     ==> simple_rv_wrt p G (simple_cond_exp p G X) /\
         (!a. a IN G ==>
           simple_expectation p (\x. simple_cond_exp p G X x * indicator_fn a x) =
           simple_expectation p (\x. X x * indicator_fn a x))`,
  REPEAT STRIP_TAC THENL
  [REWRITE_TAC[simple_rv_wrt] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_COND_EXP_MEASURABLE_WRT_G THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SIMPLE_COND_EXP_RANGE_FINITE THEN ASM_REWRITE_TAC[]];
   MATCH_MP_TAC SIMPLE_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[]]);;

(* The defining property of conditional expectation *)
let SIMPLE_COND_EXP_PROPERTY = prove
 (`!p:A prob_space G (X:A->real) a.
     sub_sigma_algebra p G /\ FINITE G /\ simple_rv p X /\ a IN G
     ==> simple_expectation p (\x. simple_cond_exp p G X x * indicator_fn a x) =
         simple_expectation p (\x. X x * indicator_fn a x)`,
  MESON_TAC[SIMPLE_COND_EXP_EXISTS]);;

(* Conditional expectation is a G-measurable simple RV *)
let SIMPLE_COND_EXP_SIMPLE_RV_WRT = prove
 (`!p:A prob_space G (X:A->real).
     sub_sigma_algebra p G /\ FINITE G /\ simple_rv p X
     ==> simple_rv_wrt p G (simple_cond_exp p G X)`,
  MESON_TAC[SIMPLE_COND_EXP_EXISTS]);;

(* Conditional expectation is a simple RV *)
let SIMPLE_COND_EXP_SIMPLE_RV = prove
 (`!p:A prob_space G (X:A->real).
     sub_sigma_algebra p G /\ FINITE G /\ simple_rv p X
     ==> simple_rv p (simple_cond_exp p G X)`,
  MESON_TAC[SIMPLE_COND_EXP_SIMPLE_RV_WRT; SIMPLE_RV_WRT_IMP_SIMPLE_RV]);;


(* G-measurable functions are constant on sigma-atoms *)
let MEASURABLE_WRT_CONSTANT_ON_ATOM = prove
 (`!p:A prob_space G (X:A->real) x y.
     sub_sigma_algebra p G /\ measurable_wrt p G X /\
     x IN prob_carrier p /\ y IN sigma_atom G x
     ==> X y = X x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS G = prob_carrier (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN UNIONS G` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
  [(* X y <= X x: atom(x) SUBSET {z | X z <= X x} *)
   SUBGOAL_THEN `sigma_atom G (x:A) SUBSET
     {z | z IN prob_carrier p /\ (X:A->real) z <= X x}` MP_TAC THENL
   [MATCH_MP_TAC SIGMA_ATOM_SUBSET THEN CONJ_TAC THENL
    [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [measurable_wrt]) THEN
     DISCH_THEN(ACCEPT_TAC o SPEC `(X:A->real) x`);
     REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[]];
   (* X x <= X y: use atom(y) = atom(x), so x IN atom(y) *)
   SUBGOAL_THEN `sigma_atom G (y:A) = sigma_atom G (x:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIGMA_ATOM_SAME THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(y:A) IN prob_carrier p` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:(A->bool)->bool`; `x:A`] SIGMA_ATOM_SUBSET_CARRIER) THEN
    ASM SET_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(x:A) IN sigma_atom G y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIGMA_ATOM_CONTAINS THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `sigma_atom G (y:A) SUBSET
     {z | z IN prob_carrier p /\ (X:A->real) z <= X y}` MP_TAC THENL
   [MATCH_MP_TAC SIGMA_ATOM_SUBSET THEN CONJ_TAC THENL
    [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [measurable_wrt]) THEN
     DISCH_THEN(ACCEPT_TAC o SPEC `(X:A->real) y`);
     REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[]]]);;


(* ========================================================================= *)
(* CONDITIONAL EXPECTATION FOR FINITE SUB-SIGMA-ALGEBRAS                     *)
(* ========================================================================= *)

(* Like simple_cond_exp but uses expectation (not simple_expectation),
   so it works for integrable (not just simple) random variables. *)
let cond_exp = new_definition
  `cond_exp (p:A prob_space) (G:(A->bool)->bool) (X:A->real) (x:A) =
   if prob p (sigma_atom G x) = &0 then &0
   else expectation p (\y. X y * indicator_fn (sigma_atom G x) y) /
        prob p (sigma_atom G x)`;;

(* General conditional expectation is constant on atoms *)
let COND_EXP_CONSTANT_ON_ATOM = prove
 (`!p:A prob_space G (X:A->real) (x:A) (y:A).
     sigma_algebra G /\ x IN UNIONS G /\ y IN sigma_atom G x
     ==> cond_exp p G X y = cond_exp p G X x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cond_exp] THEN
  SUBGOAL_THEN `sigma_atom G (y:A) = sigma_atom G (x:A)`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC SIGMA_ATOM_SAME THEN ASM_REWRITE_TAC[]);;

(* The range of cond_exp is finite on the carrier *)
let COND_EXP_RANGE_FINITE = prove
 (`!p:A prob_space G (X:A->real).
     sub_sigma_algebra p G /\ FINITE G
     ==> FINITE {cond_exp p G X x | x | x IN prob_carrier p}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS G = prob_carrier (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\(a:A->bool).
    if prob (p:A prob_space) a = &0 then &0
    else expectation p (\y. (X:A->real) y * indicator_fn a y) /
         prob p a) {sigma_atom G (x:A) | x | x IN UNIONS G}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SIGMA_ATOMS THEN
   ASM_MESON_TAC[sub_sigma_algebra];
   ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `v:real` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `sigma_atom G (w:A)` THEN CONJ_TAC THENL
  [ASM_REWRITE_TAC[cond_exp]; ALL_TAC] THEN
  EXISTS_TAC `w:A` THEN ASM_MESON_TAC[]);;

(* cond_exp is G-measurable *)
let COND_EXP_MEASURABLE_WRT = prove
 (`!p:A prob_space G (X:A->real).
     sub_sigma_algebra p G /\ FINITE G
     ==> measurable_wrt p G (cond_exp p G X)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS G = prob_carrier (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  REWRITE_TAC[measurable_wrt] THEN X_GEN_TAC `v:real` THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ cond_exp p G (X:A->real) x <= v} =
     UNIONS {sigma_atom G (x:A) | x |
       x IN prob_carrier p /\ cond_exp p G X x <= v}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
   X_GEN_TAC `z:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `sigma_atom G (z:A)` THEN
    CONJ_TAC THENL
    [EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC SIGMA_ATOM_CONTAINS THEN ASM_MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC)
                        ASSUME_TAC)) THEN
    CONJ_TAC THENL
    [SUBGOAL_THEN `sigma_atom G (w:A) SUBSET UNIONS G` MP_TAC THENL
     [MATCH_MP_TAC SIGMA_ATOM_SUBSET_CARRIER THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[SUBSET]];
     SUBGOAL_THEN `cond_exp p G (X:A->real) z =
                   cond_exp p G X w` SUBST1_TAC THENL
     [MATCH_MP_TAC COND_EXP_CONSTANT_ON_ATOM THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[]]]];
   ALL_TAC] THEN
  MATCH_MP_TAC SIGMA_ALGEBRA_UNIONS_FINITE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `t:A->bool` THEN
   DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC SIGMA_ATOM_IN_G THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
   MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC `{sigma_atom G (x:A) | x | x IN UNIONS G}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SIGMA_ATOMS THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]]]);;

(* cond_exp is a simple random variable *)
let COND_EXP_SIMPLE_RV = prove
 (`!p:A prob_space G (X:A->real).
     sub_sigma_algebra p G /\ FINITE G
     ==> simple_rv p (cond_exp p G X)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simple_rv] THEN CONJ_TAC THENL
  [MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
   EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC COND_EXP_RANGE_FINITE THEN ASM_REWRITE_TAC[]]);;

(* cond_exp is integrable *)
let COND_EXP_INTEGRABLE = prove
 (`!p:A prob_space G (X:A->real).
     sub_sigma_algebra p G /\ FINITE G
     ==> integrable p (cond_exp p G X)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_SIMPLE THEN
  MATCH_MP_TAC COND_EXP_SIMPLE_RV THEN ASM_REWRITE_TAC[]);;

(* E[X * 1_S] = 0 when P(S) = 0 and X is integrable *)
let EXPECTATION_MUL_INDICATOR_ZERO_PROB = prove
 (`!p:A prob_space (X:A->real) (S:A->bool).
     integrable p X /\ S IN prob_events p /\ prob p S = &0
     ==> expectation p (\x. X x * indicator_fn S x) = &0`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SET_INTEGRAL_ZERO_ON_NULL THEN ASM_REWRITE_TAC[]);;

(* Conditioning property for individual atoms *)
let COND_EXP_ATOM_COND = prove
 (`!p:A prob_space G (X:A->real) (x:A).
     sub_sigma_algebra p G /\ FINITE G /\ integrable p X /\
     x IN prob_carrier p
     ==> expectation p
           (\y. cond_exp p G X y *
                indicator_fn (sigma_atom G x) y) =
         expectation p
           (\y. X y * indicator_fn (sigma_atom G x) y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS G = prob_carrier (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN UNIONS G` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sigma_atom G (x:A) IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[SIGMA_ATOM_IN_G; sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
  ASM_CASES_TAC `prob p (sigma_atom G (x:A)) = &0` THENL
  [(* Case: P(atom) = 0 -- both sides are 0 *)
   SUBGOAL_THEN `simple_rv p (cond_exp p G (X:A->real))` ASSUME_TAC THENL
   [MATCH_MP_TAC COND_EXP_SIMPLE_RV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC(REAL_ARITH `a = &0 /\ b = &0 ==> a = b`) THEN CONJ_TAC THENL
   [SUBGOAL_THEN `expectation p (\y:A. cond_exp p G (X:A->real) y *
      indicator_fn (sigma_atom G x) y) =
      simple_expectation p (\y. cond_exp p G X y *
        indicator_fn (sigma_atom G x) y)` SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN
     MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC[ETA_AX];
       MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]];
     MATCH_MP_TAC SIMPLE_EXPECTATION_MUL_INDICATOR_ZERO_PROB THEN
     ASM_REWRITE_TAC[ETA_AX]];
    MATCH_MP_TAC EXPECTATION_MUL_INDICATOR_ZERO_PROB THEN
    ASM_REWRITE_TAC[]];
   (* Case: P(atom) > 0 *)
   ABBREV_TAC `c = cond_exp p G (X:A->real) x` THEN
   (* LHS: cond_exp is constant c on atom *)
   SUBGOAL_THEN
     `expectation p (\y:A. cond_exp p G (X:A->real) y *
       indicator_fn (sigma_atom G x) y) =
      c * prob p (sigma_atom G x)` SUBST1_TAC THENL
   [SUBGOAL_THEN
      `expectation p (\y:A. cond_exp p G (X:A->real) y *
        indicator_fn (sigma_atom G x) y) =
       expectation p (\y. c * indicator_fn (sigma_atom G x) y)`
      SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_EXT THEN
     X_GEN_TAC `z:A` THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[indicator_fn] THEN
     COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN
     EXPAND_TAC "c" THEN
     MATCH_MP_TAC COND_EXP_CONSTANT_ON_ATOM THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `c:real`;
      `indicator_fn (sigma_atom G (x:A))`] EXPECTATION_CMUL) THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC EXPECTATION_INDICATOR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* c = E[X * 1_atom] / P(atom), so c * P(atom) = E[X * 1_atom] *)
   EXPAND_TAC "c" THEN REWRITE_TAC[cond_exp] THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REWRITE_TAC[]]);;

(* Conditioning property extended to arbitrary G-sets *)
let COND_EXP_CONDITIONING = prove
 (`!p:A prob_space G (X:A->real) (a:A->bool).
     sub_sigma_algebra p G /\ FINITE G /\ integrable p X /\ a IN G
     ==> expectation p
           (\x. cond_exp p G X x * indicator_fn a x) =
         expectation p (\x. X x * indicator_fn a x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS G = prob_carrier (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv p (cond_exp p G (X:A->real))` ASSUME_TAC THENL
  [MATCH_MP_TAC COND_EXP_SIMPLE_RV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:A->bool) IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
  (* Decompose a into atoms *)
  ABBREV_TAC
    `atoms = {sigma_atom G (x:A) | x | x IN prob_carrier (p:A prob_space)}` THEN
  ABBREV_TAC
    `atoms_a = {(A:A->bool) | A IN atoms /\ A SUBSET a}` THEN
  SUBGOAL_THEN `FINITE (atoms:((A->bool)->bool))` ASSUME_TAC THENL
  [EXPAND_TAC "atoms" THEN
   SUBGOAL_THEN `prob_carrier (p:A prob_space) = UNIONS G` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC FINITE_SIGMA_ATOMS THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (atoms_a:((A->bool)->bool))` ASSUME_TAC THENL
  [EXPAND_TAC "atoms_a" THEN MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC `atoms:((A->bool)->bool)` THEN
   ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!A1 A2:A->bool. A1 IN atoms_a /\ A2 IN atoms_a /\ ~(A1 = A2)
                      ==> DISJOINT A1 A2` (LABEL_TAC "pd") THENL
  [EXPAND_TAC "atoms_a" THEN EXPAND_TAC "atoms" THEN
   REWRITE_TAC[IN_ELIM_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   ASM_MESON_TAC[SIGMA_ATOM_EQUAL_OR_DISJOINT];
   ALL_TAC] THEN
  SUBGOAL_THEN `!A:A->bool. A IN atoms_a ==> A IN prob_events p`
    (LABEL_TAC "ev") THENL
  [EXPAND_TAC "atoms_a" THEN EXPAND_TAC "atoms" THEN
   REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[SIGMA_ATOM_IN_G; sub_sigma_algebra; SUBSET];
   ALL_TAC] THEN
  SUBGOAL_THEN `!A:A->bool. A IN atoms_a ==> A IN G`
    (LABEL_TAC "in_G") THENL
  [EXPAND_TAC "atoms_a" THEN EXPAND_TAC "atoms" THEN
   REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIGMA_ATOM_IN_G THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!B:A->bool. B IN atoms_a
     ==> ?w:A. w IN prob_carrier p /\ sigma_atom G w = B`
    (LABEL_TAC "is_atom") THENL
  [EXPAND_TAC "atoms_a" THEN EXPAND_TAC "atoms" THEN
   REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
   ALL_TAC] THEN
  (* a = UNIONS atoms_a *)
  SUBGOAL_THEN `(a:A->bool) = UNIONS atoms_a` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_UNIONS] THEN X_GEN_TAC `z:A` THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `sigma_atom G (z:A)` THEN CONJ_TAC THENL
    [EXPAND_TAC "atoms_a" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [EXPAND_TAC "atoms" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      EXISTS_TAC `z:A` THEN
      ASM_MESON_TAC[PROB_EVENT_SUBSET; sub_sigma_algebra; SUBSET];
      MATCH_MP_TAC SIGMA_ATOM_SUBSET THEN ASM_REWRITE_TAC[]];
     MATCH_MP_TAC SIGMA_ATOM_CONTAINS THEN
     ASM_MESON_TAC[PROB_EVENT_SUBSET; sub_sigma_algebra; SUBSET]];
    DISCH_THEN(X_CHOOSE_THEN `B:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(B:A->bool) SUBSET a` MP_TAC THENL
    [UNDISCH_TAC `(B:A->bool) IN atoms_a` THEN
     EXPAND_TAC "atoms_a" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
     ASM SET_TAC[]]];
   ALL_TAC] THEN
  (* Prove by finite induction on atom subsets *)
  SUBGOAL_THEN
    `!S:(A->bool)->bool. FINITE S /\ S SUBSET atoms_a
     ==> expectation p (\x. cond_exp p G (X:A->real) x *
           indicator_fn (UNIONS S) x) =
         expectation p (\x. X x * indicator_fn (UNIONS S) x)`
    (fun th -> MP_TAC(SPEC `atoms_a:((A->bool)->bool)` th) THEN
               ASM_REWRITE_TAC[SUBSET_REFL]) THEN
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
  [(* Base case: UNIONS {} = {} *)
   DISCH_TAC THEN REWRITE_TAC[UNIONS_0] THEN
   MATCH_MP_TAC(REAL_ARITH `a = &0 /\ b = &0 ==> a = b`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SET_INTEGRAL_ZERO_ON_NULL THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_SIMPLE THEN REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC COND_EXP_SIMPLE_RV THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[PROB_EMPTY_IN_EVENTS; PROB_EMPTY]];
    MATCH_MP_TAC SET_INTEGRAL_ZERO_ON_NULL THEN
    ASM_REWRITE_TAC[PROB_EMPTY_IN_EVENTS; PROB_EMPTY]];
   ALL_TAC] THEN
  (* Inductive step: INSERT B S' *)
  MAP_EVERY X_GEN_TAC [`B:A->bool`; `S':(A->bool)->bool`] THEN
  STRIP_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[UNIONS_INSERT] THEN
  (* Unpack: B IN atoms_a, S' SUBSET atoms_a *)
  SUBGOAL_THEN `(B:A->bool) IN atoms_a` ASSUME_TAC THENL
  [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(S':(A->bool)->bool) SUBSET atoms_a` ASSUME_TAC THENL
  [ASM SET_TAC[]; ALL_TAC] THEN
  (* B is an event *)
  SUBGOAL_THEN `(B:A->bool) IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* UNIONS S' is an event *)
  SUBGOAL_THEN `UNIONS S' IN prob_events (p:A prob_space)` ASSUME_TAC THENL
  [SUBGOAL_THEN `UNIONS S' IN (G:(A->bool)->bool)` MP_TAC THENL
   [MATCH_MP_TAC SIGMA_ALGEBRA_UNIONS_FINITE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `C:A->bool` THEN DISCH_TAC THEN
    USE_THEN "in_G" MATCH_MP_TAC THEN ASM SET_TAC[];
    ASM_MESON_TAC[sub_sigma_algebra; SUBSET]];
   ALL_TAC] THEN
  (* B and UNIONS S' are disjoint *)
  SUBGOAL_THEN `DISJOINT B (UNIONS S':A->bool)` ASSUME_TAC THENL
  [REWRITE_TAC[DISJOINT; EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_UNIONS] THEN
   X_GEN_TAC `z:A` THEN
   REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN
   DISCH_TAC THEN
   REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
   X_GEN_TAC `C:A->bool` THEN DISCH_TAC THEN
   SUBGOAL_THEN `DISJOINT (B:A->bool) C` MP_TAC THENL
   [USE_THEN "pd" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[]];
    REWRITE_TAC[DISJOINT; EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
    ASM_MESON_TAC[]];
   ALL_TAC] THEN
  (* Apply IH *)
  SUBGOAL_THEN
    `expectation p (\x. cond_exp p G (X:A->real) x *
       indicator_fn (UNIONS S') x) =
     expectation p (\x. X x * indicator_fn (UNIONS S') x)`
    (LABEL_TAC "ih_eq") THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Get witness for B as atom *)
  USE_THEN "is_atom" (MP_TAC o SPEC `B:A->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
  (* Per-atom: E[cond_exp * 1_B] = E[X * 1_B] *)
  SUBGOAL_THEN
    `expectation p (\x. cond_exp p G (X:A->real) x *
       indicator_fn B x) =
     expectation p (\x. X x * indicator_fn B x)`
    (LABEL_TAC "atom_eq") THENL
  [SUBGOAL_THEN `B = sigma_atom G (w:A):A->bool` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC COND_EXP_ATOM_COND THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Key: indicator decomposes additively on disjoint sets *)
  SUBGOAL_THEN `!f:A->real. integrable p f ==>
    expectation p (\x. f x * indicator_fn (B UNION UNIONS S') x) =
    expectation p (\x. f x * indicator_fn B x) +
    expectation p (\x. f x * indicator_fn (UNIONS S':A->bool) x)`
    (LABEL_TAC "decomp") THENL
  [X_GEN_TAC `f:A->real` THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `(\x:A. f x * indicator_fn (B UNION UNIONS S') x) =
      (\x. f x * indicator_fn B x +
           f x * indicator_fn (UNIONS S':A->bool) x)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:A` THEN
    REWRITE_TAC[indicator_fn; IN_UNION] THEN
    UNDISCH_TAC `DISJOINT B (UNIONS S':A->bool)` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `z:A`) THEN
    MAP_EVERY ASM_CASES_TAC [`(z:A) IN B`; `(z:A) IN UNIONS S'`] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC EXPECTATION_ADD THEN CONJ_TAC THEN
   MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Decompose both sides and combine *)
  USE_THEN "decomp" (MP_TAC o SPEC `cond_exp p G (X:A->real)`) THEN
  ANTS_TAC THENL
  [MATCH_MP_TAC COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  USE_THEN "decomp" (MP_TAC o SPEC `X:A->real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REMOVE_THEN "atom_eq" SUBST1_TAC THEN
  REMOVE_THEN "ih_eq" SUBST1_TAC THEN
  REFL_TAC);;

(* Tower property: E[E[X|G]] = E[X] *)
let COND_EXP_TOWER = prove
 (`!p:A prob_space G (X:A->real).
     sub_sigma_algebra p G /\ FINITE G /\ integrable p X
     ==> expectation p (cond_exp p G X) = expectation p X`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS G = prob_carrier (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  (* E[cond_exp] = E[cond_exp * 1_carrier] *)
  SUBGOAL_THEN
    `expectation p (cond_exp p G (X:A->real)) =
     expectation p (\x. cond_exp p G X x * indicator_fn (UNIONS G) x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `z:A` THEN
   DISCH_TAC THEN BETA_TAC THEN
   REWRITE_TAC[indicator_fn] THEN
   COND_CASES_TAC THENL [REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `expectation p (X:A->real) =
     expectation p (\x. X x * indicator_fn (UNIONS G) x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `z:A` THEN
   DISCH_TAC THEN BETA_TAC THEN
   REWRITE_TAC[indicator_fn] THEN
   COND_CASES_TAC THENL [REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC COND_EXP_CONDITIONING THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SIGMA_ALGEBRA_CARRIER]);;

(* cond_exp agrees with simple_cond_exp for simple RVs *)
let COND_EXP_AGREES_SIMPLE = prove
 (`!p:A prob_space G (X:A->real) x.
     sub_sigma_algebra p G /\ FINITE G /\ simple_rv p X /\
     x IN prob_carrier p
     ==> cond_exp p G X x = simple_cond_exp p G X x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cond_exp; simple_cond_exp] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `UNIONS G = prob_carrier (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `sigma_atom G (x:A) IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[SIGMA_ATOM_IN_G; sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN
  MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
  CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]]);;


(* Take-out property: E[Y*X|G] = Y*E[X|G] when Y is G-measurable *)
let COND_EXP_TAKE_OUT = prove
 (`!p:A prob_space G (X:A->real) Y.
     sub_sigma_algebra p G /\ FINITE G /\
     integrable p X /\ integrable p (\x. Y x * X x) /\
     measurable_wrt p G Y
     ==> !x. x IN prob_carrier p /\ ~(prob p (sigma_atom G x) = &0)
         ==> cond_exp p G (\w. Y w * X w) x = Y x * cond_exp p G X x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  REWRITE_TAC[cond_exp] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `expectation p (\y:A. ((Y:A->real) y * X y) * indicator_fn (sigma_atom G x) y) =
     Y x * expectation p (\y. X y * indicator_fn (sigma_atom G x) y)`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
     `(\y:A. ((Y:A->real) y * (X:A->real) y) * indicator_fn (sigma_atom G x) y) =
      (\y. (Y:A->real) x * (X y * indicator_fn (sigma_atom G x) y))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:A` THEN
    REWRITE_TAC[indicator_fn] THEN
    COND_CASES_TAC THENL
    [SUBGOAL_THEN `(Y:A->real) y = Y x` SUBST1_TAC THENL
     [MATCH_MP_TAC MEASURABLE_WRT_CONSTANT_ON_ATOM THEN
      ASM_MESON_TAC[];
      REAL_ARITH_TAC];
     REAL_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `sigma_atom G (x:A) IN prob_events p` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIGMA_ATOM_IN_G; sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(Y:A->real) x`;
     `\y:A. (X:A->real) y * indicator_fn (sigma_atom G x) y`]
     EXPECTATION_CMUL) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[];
    BETA_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC]];
   REWRITE_TAC[real_div; REAL_MUL_ASSOC]]);;


(* ========================================================================= *)
(* DOOB SIMPLE_MARTINGALE                                                           *)
(* ========================================================================= *)

(* The Doob simple_martingale: cond_exp applied to a filtration *)
let DOOB_MARTINGALE = prove
 (`!p:A prob_space FF (X:A->real).
     filtration p FF /\ (!n. FINITE (FF n)) /\ integrable p X
     ==> martingale p FF (\n. cond_exp p (FF n) X)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[martingale] THEN
  SUBGOAL_THEN `!n. sub_sigma_algebra p ((FF:num->(A->bool)->bool) n)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [(* filtration *)
   ASM_REWRITE_TAC[];
   (* adapted *)
   REWRITE_TAC[adapted] THEN GEN_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[];
   (* integrable *)
   GEN_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
   (* conditioning *)
   REPEAT STRIP_TAC THEN BETA_TAC THEN
   (* E[cond_exp(FF(SUC n)) * 1_a] = E[X * 1_a]
      = E[cond_exp(FF n) * 1_a] *)
   SUBGOAL_THEN
     `expectation p (\x:A. cond_exp p (FF (SUC n)) (X:A->real) x *
        indicator_fn a x) =
      expectation p (\x. X x * indicator_fn a x)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC COND_EXP_CONDITIONING THEN
    ASM_REWRITE_TAC[] THEN
    (* a IN FF n ==> a IN FF(SUC n) by filtration monotonicity *)
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [filtration]) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPECL [`n:num`; `SUC n`]) THEN
    REWRITE_TAC[LE_REFL; ARITH_RULE `n <= SUC n`] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
   CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC COND_EXP_CONDITIONING THEN
   ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* L1-BOUNDED SIMPLE_MARTINGALE CONVERGENCE THEOREM                                 *)
(* ========================================================================= *)

(* Bound on pos_part for arbitrary functions (L1 version) *)
let POS_PART_SUB_LE_ABS = prove
 (`!x a. pos_part(x - a) <= abs(x) + abs(a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pos_part; real_max] THEN
  COND_CASES_TAC THEN REAL_ARITH_TAC);;

(* Expected upcrossings bounded for L1-bounded simple_submartingale *)
let SIMPLE_UPCROSSING_EXPECTATION_BOUND_L1 = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b n C.
     simple_submartingale p FF X /\ a < b /\
     (!n. simple_expectation p (\x. abs(X n x)) <= C)
     ==> (b - a) * simple_expectation p (\x. &(num_upcrossings X a b n x))
         <= C + abs(a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                `X:num->A->real`; `a:real`; `b:real`; `n:num`]
    SIMPLE_DOOB_UPCROSSING_INEQUALITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!m:num. simple_rv (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space)
    (\x:A. pos_part((X:num->A->real) n x - a))` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space)
    (\x:A. abs((X:num->A->real) n x) + abs(a))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_POS_PART_SUB THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SIMPLE_RV_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_ABS THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[SIMPLE_RV_CONST]];
    GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[POS_PART_SUB_LE_ABS]];
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_expectation (p:A prob_space)
    (\x:A. abs((X:num->A->real) n x) + abs(a)) =
    simple_expectation p (\x. abs(X n x)) + abs(a)` SUBST1_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`;
                   `\x:A. abs((X:num->A->real) n x)`;
                   `\x:A. abs(a:real)`] SIMPLE_EXPECTATION_ADD) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_ABS THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[SIMPLE_RV_CONST]];
    REWRITE_TAC[SIMPLE_EXPECTATION_CONST] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th])];
   UNDISCH_TAC `!n. simple_expectation (p:A prob_space)
     (\x:A. abs((X:num->A->real) n x)) <= C` THEN
   DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC]);;

(* L1 Markov bound: P(U_n >= k) <= (C + |a|) / ((b-a)*k) *)
let SIMPLE_UPCROSSING_PROB_BOUND_L1 = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b n C k.
     simple_submartingale p FF X /\ a < b /\
     (!n. simple_expectation p (\x. abs(X n x)) <= C) /\
     0 < k
     ==> prob p {x | x IN prob_carrier p /\
                     &(num_upcrossings X a b n x) >= &k}
         <= (C + abs(a)) / ((b - a) * &k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!m:num. simple_rv (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
    [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)`
    ASSUME_TAC THENL
    [ASM_MESON_TAC[simple_submartingale; simple_adapted]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv p (\x:A. &(num_upcrossings (X:num->A->real) a b n x))`
    ASSUME_TAC THENL
  [MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                  `X:num->A->real`; `a:real`; `b:real`]
     SIMPLE_RV_NUM_UPCROSSINGS) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(ACCEPT_TAC o SPEC `n:num`)];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
    `prob p {x | x IN prob_carrier (p:A prob_space) /\
     &(num_upcrossings (X:num->A->real) a b n x) >= &k}
     <= simple_expectation p (\x. &(num_upcrossings X a b n x)) / &k`
    ASSUME_TAC THENL
  [MATCH_MP_TAC MARKOV_INEQUALITY_SIMPLE THEN
   ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_POS];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `(b - a) * simple_expectation (p:A prob_space)
       (\x:A. &(num_upcrossings (X:num->A->real) a b n x)) <= C + abs(a:real)`
    ASSUME_TAC THENL
  [MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                  `X:num->A->real`; `a:real`; `b:real`; `n:num`; `C:real`]
     SIMPLE_UPCROSSING_EXPECTATION_BOUND_L1) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. &(num_upcrossings (X:num->A->real) a b n x))
     <= (C + abs(a:real)) / (b - a)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
   ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. &(num_upcrossings (X:num->A->real) a b n x)) / &k
     <= (C + abs(a:real)) / ((b - a) * &k)` ASSUME_TAC THENL
  [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
   MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM real_div];
    MATCH_MP_TAC REAL_LE_INV THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  ASM_MESON_TAC[REAL_LE_TRANS]);;

(* L1 version: infinite upcrossings have probability zero *)
let SIMPLE_INFINITE_UPCROSSINGS_NULL_L1 = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b C.
     simple_submartingale p FF X /\ a < b /\
     (!n. simple_expectation p (\x. abs(X n x)) <= C)
     ==> !k. 0 < k ==>
         prob p (UNIONS {
           {x | x IN prob_carrier p /\ &(num_upcrossings X a b n x) >= &k}
         | n IN (:num)}) <= (C + abs(a)) / ((b - a) * &k)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PROB_UNIONS_INCREASING_BOUND THEN
  SUBGOAL_THEN `!m:num. simple_rv (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
    [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)` ASSUME_TAC THENL
    [ASM_MESON_TAC[simple_submartingale; simple_adapted]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC SIMPLE_NUM_UPCROSSINGS_GE_EVENT THEN
   EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
   X_GEN_TAC `nn:num` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge;
     REAL_OF_NUM_LE] THEN
   X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[NUM_UPCROSSINGS_MONO; LE_TRANS;
     ARITH_RULE `nn <= SUC nn`];
   X_GEN_TAC `m:num` THEN
   MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                   `X:num->A->real`; `a:real`; `b:real`; `m:num`;
                   `C:real`; `k:num`] SIMPLE_UPCROSSING_PROB_BOUND_L1) THEN
   DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]]);;

(* L1 version: finite upcrossings a.s. for fixed a < b *)
let SIMPLE_FINITE_UPCROSSINGS_AS_L1 = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b C.
     simple_submartingale p FF X /\ a < b /\
     (!n. simple_expectation p (\x. abs(X n x)) <= C)
     ==> almost_surely p
           {x | ?B:num. !n. num_upcrossings X a b n x <= B}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[almost_surely] THEN
  SUBGOAL_THEN `!m:num. simple_rv (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
    [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)` ASSUME_TAC THENL
    [ASM_MESON_TAC[simple_submartingale; simple_adapted]; ALL_TAC] THEN
  EXISTS_TAC
    `INTERS {UNIONS {
       {x:A | x IN prob_carrier p /\
              &(num_upcrossings (X:num->A->real) a b n x) >= &(SUC k)}
     | n IN (:num)} | k IN (:num)}` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[null_event] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN
    GEN_TAC THEN MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
    GEN_TAC THEN MATCH_MP_TAC SIMPLE_NUM_UPCROSSINGS_GE_EVENT THEN
    EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_EQ_0_FROM_INV_BOUND THEN
    EXISTS_TAC `(C + abs(a:real)) / (b - a)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC PROB_POSITIVE THEN
     MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN
     GEN_TAC THEN MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
     GEN_TAC THEN MATCH_MP_TAC SIMPLE_NUM_UPCROSSINGS_GE_EVENT THEN
     EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
     X_GEN_TAC `j:num` THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `prob (p:A prob_space) (UNIONS {
       {x:A | x IN prob_carrier p /\
              &(num_upcrossings (X:num->A->real) a b n x) >= &(SUC j)}
       | n IN (:num)})` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC PROB_MONO THEN REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN
       GEN_TAC THEN MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
       GEN_TAC THEN MATCH_MP_TAC SIMPLE_NUM_UPCROSSINGS_GE_EVENT THEN
       EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
       GEN_TAC THEN MATCH_MP_TAC SIMPLE_NUM_UPCROSSINGS_GE_EVENT THEN
       EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
       SET_TAC[]];
      SUBGOAL_THEN `(C + abs(a:real)) / (b - a) / &(SUC j) =
                     (C + abs a) / ((b - a) * &(SUC j))`
        SUBST1_TAC THENL
      [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC]; ALL_TAC] THEN
      MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                      `X:num->A->real`; `a:real`; `b:real`; `C:real`]
        SIMPLE_INFINITE_UPCROSSINGS_NULL_L1) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `SUC j`) THEN
      REWRITE_TAC[LT_0]]]];
   REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERS] THEN
   X_GEN_TAC `x:A` THEN STRIP_TAC THEN
   GEN_TAC THEN REWRITE_TAC[SIMPLE_IMAGE; IN_IMAGE; IN_UNIV] THEN
   DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
   REWRITE_TAC[IN_UNIONS] THEN
   REWRITE_TAC[EXISTS_IN_IMAGE; IN_UNIV; IN_ELIM_THM;
               real_ge; REAL_OF_NUM_LE] THEN
   FIRST_X_ASSUM(MP_TAC o
     GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
   DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
   REWRITE_TAC[NOT_FORALL_THM; NOT_LE] THEN
   DISCH_THEN(X_CHOOSE_THEN `nn:num` ASSUME_TAC) THEN
   EXISTS_TAC `nn:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* Positive part of a simple_submartingale is a simple_submartingale *)
let SIMPLE_SUBMARTINGALE_POS_PART = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real).
     simple_submartingale p FF X
     ==> simple_submartingale p FF (\n x. pos_part(X n x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_adapted (p:A prob_space) FF (X:num->A->real)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  REWRITE_TAC[simple_submartingale] THEN
  REPEAT CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   REWRITE_TAC[simple_adapted] THEN CONJ_TAC THENL
   [REWRITE_TAC[adapted] THEN GEN_TAC THEN
    REWRITE_TAC[measurable_wrt] THEN X_GEN_TAC `v:real` THEN
    REWRITE_TAC[pos_part] THEN
    ASM_CASES_TAC `v < &0` THENL
    [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ real_max ((X:num->A->real) n x) (&0) <= v} = {}`
       SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC) THEN
      REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY THEN
      ASM_MESON_TAC[filtration; sub_sigma_algebra]];
     SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ real_max ((X:num->A->real) n x) (&0) <= v} =
                   {x | x IN prob_carrier p /\ X n x <= v}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
      EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
      [POP_ASSUM MP_TAC THEN REWRITE_TAC[real_max] THEN
       COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
       REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC];
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_adapted]) THEN
      REWRITE_TAC[adapted; measurable_wrt] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
      DISCH_THEN(MP_TAC o SPEC `v:real`) THEN REWRITE_TAC[]]];
    GEN_TAC THEN
    SUBGOAL_THEN `{pos_part ((X:num->A->real) n x) | x IN prob_carrier (p:A prob_space)} =
                  IMAGE (\y. pos_part y) {X n x | x IN prob_carrier p}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
     GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `xx:A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(X:num->A->real) n xx` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `xx:A` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `y:real` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      DISCH_THEN(X_CHOOSE_THEN `xx:A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `xx:A` THEN ASM_REWRITE_TAC[]];
     MATCH_MP_TAC FINITE_IMAGE THEN
     FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_adapted]) THEN
     DISCH_THEN(MP_TAC o CONJUNCT2) THEN
     DISCH_THEN(ACCEPT_TAC o SPEC `n:num`)]];
   GEN_TAC THEN MATCH_MP_TAC SIMPLE_RV_POS_PART THEN
   REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                   `X:num->A->real`; `&0`] SIMPLE_SUBMARTINGALE_POS_PART_STEP) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`n:num`; `a:A->bool`]) THEN
   ASM_REWRITE_TAC[REAL_SUB_RZERO]]);;

(* Doob maximal inequality for positive parts of a simple_submartingale *)
let SIMPLE_DOOB_MAXIMAL_POS_PART = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) c n C.
     simple_submartingale p FF X /\ &0 < c /\
     (!n. simple_expectation p (\x. abs(X n x)) <= C)
     ==> c * prob p {x | x IN prob_carrier p /\
                         running_max (\m x. pos_part(X m x)) n x >= c}
         <= C`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                  `(\n x. pos_part((X:num->A->real) n x)):num->A->real`;
                  `c:real`; `n:num`]
    DOOB_MAXIMAL_INEQUALITY) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `c * prob (p:A prob_space)
    {x:A | x IN prob_carrier p /\
           running_max (\n x. pos_part ((X:num->A->real) n x)) n x >= c} <=
    simple_expectation p ((\n x. pos_part (X n x)) n)` ASSUME_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_SUBMARTINGALE_POS_PART THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   BETA_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[pos_part; real_max] THEN
   COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space) ((\n x. pos_part ((X:num->A->real) n x)) n)` THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space) (\x:A. abs((X:num->A->real) n x))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_POS_PART THEN REWRITE_TAC[ETA_AX] THEN
    ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_ABS THEN REWRITE_TAC[ETA_AX] THEN
    ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
   GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[pos_part; real_max] THEN
   COND_CASES_TAC THEN REAL_ARITH_TAC;
   ASM_REWRITE_TAC[]]);;

(* Helper: finite prefix of a sequence has a lower bound *)
let FINITE_PREFIX_LOWER_BOUND = prove
 (`!f:num->real. !N. ?L. !n. n < N ==> f n >= L`,
  GEN_TAC THEN INDUCT_TAC THENL
  [EXISTS_TAC `&0` THEN ARITH_TAC;
   FIRST_X_ASSUM(X_CHOOSE_TAC `L:real`) THEN
   EXISTS_TAC `min L ((f:num->real) N)` THEN
   X_GEN_TAC `n:num` THEN REWRITE_TAC[LT] THEN
   DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL
   [REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]);;

(* Bounded above + finite upcrossings => convergent or -> -infty *)
let FINITE_UPCROSSINGS_CONVERGENT_OR_MINUS_INF = prove
 (`!f M. (!n. (f:num->real) n <= M) /\
     (!a b. rational a /\ rational b /\ a < b
            ==> ?B. !n. upcrossing_count f a b n <= B)
     ==> (?L. (f ---> L) sequentially) \/
         (!K:num. ?N. !n. N <= n ==> f n <= --(&K))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `!K:num. ?N:num. !n. N <= n ==> (f:num->real) n <= --(&K)` THENL
  [ASM_REWRITE_TAC[];
   DISJ1_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
   DISCH_THEN(X_CHOOSE_TAC `K0:num`) THEN
   POP_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
   REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN DISCH_TAC THEN
   SUBGOAL_THEN `!N:num. ?n. N <= n /\ (f:num->real) n >= --(&K0)`
     ASSUME_TAC THENL
   [X_GEN_TAC `N:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
    DISCH_THEN(X_CHOOSE_THEN `nn:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `nn:num` THEN ASM_REWRITE_TAC[real_ge] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `~(!N:num. ?n. N <= n /\ (f:num->real) n <= --(&(K0 + 1)))`
     MP_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `!a b. rational a /\ rational b /\ a < b
      ==> (?B. !n. upcrossing_count (f:num->real) a b n <= B)` THEN
    DISCH_THEN(MP_TAC o SPECL [`--(&(K0 + 1))`; `--(&K0):real`]) THEN
    ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RATIONAL_NEG THEN REWRITE_TAC[RATIONAL_NUM];
      MATCH_MP_TAC RATIONAL_NEG THEN REWRITE_TAC[RATIONAL_NUM];
      REWRITE_TAC[REAL_ARITH `--a < --b <=> b < a`; REAL_OF_NUM_LT] THEN
      ARITH_TAC];
     ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `B:num`) THEN
    MP_TAC(ISPECL [`f:num->real`; `--(&(K0 + 1))`; `--(&K0):real`; `SUC B`]
      UPCROSSING_COUNT_ITERATE) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[REAL_ARITH `--a < --b <=> b < a`; REAL_OF_NUM_LT] THEN
     ARITH_TAC;
     ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `nn:num` MP_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `nn:num`) THEN ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM;
               TAUT `~(a /\ b) <=> a ==> ~b`] THEN
   DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
   MP_TAC(ISPECL [`f:num->real`; `N0:num`] FINITE_PREFIX_LOWER_BOUND) THEN
   DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN
   SUBGOAL_THEN
     `!n:num. abs((f:num->real) n) <= max (abs M) (max (&(K0 + 1)) (abs L))`
     ASSUME_TAC THENL
   [X_GEN_TAC `nn:num` THEN
    ASM_CASES_TAC `N0:num <= nn` THENL
    [REWRITE_TAC[REAL_ABS_BOUNDS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--(&(K0 + 1))` THEN
      CONJ_TAC THENL
      [REAL_ARITH_TAC;
       MATCH_MP_TAC(REAL_ARITH `~(y <= --x) ==> --x <= y`) THEN
       UNDISCH_TAC `!n. N0 <= n ==> ~((f:num->real) n <= --(&(K0 + 1)))` THEN
       DISCH_THEN(MP_TAC o SPEC `nn:num`) THEN
       ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M:real` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
     SUBGOAL_THEN `nn < N0:num` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LE] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_ABS_BOUNDS] THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L:real` THEN
       CONJ_TAC THENL
       [REAL_ARITH_TAC;
        UNDISCH_TAC `!n. n < N0 ==> (f:num->real) n >= L` THEN
        DISCH_THEN(MP_TAC o SPEC `nn:num`) THEN
        ASM_REWRITE_TAC[real_ge] THEN REAL_ARITH_TAC];
       MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M:real` THEN
       ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]];
    ALL_TAC] THEN
   MATCH_MP_TAC(ISPECL [`f:num->real`;
       `max (abs M) (max (&(K0 + 1)) (abs (L:real)))`]
       BOUNDED_FINITE_UPCROSSINGS_IMP_CONVERGENT) THEN
   ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* L1-BOUNDED SIMPLE_MARTINGALE CONVERGENCE THEOREM (main result)                   *)
(* ========================================================================= *)

(* Helper: running_max of pos_part event is in prob_events *)
let SIMPLE_RUNNING_MAX_POS_PART_EVENT = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) c n.
     simple_submartingale p FF X
     ==> {x | x IN prob_carrier p /\
              running_max (\m x. pos_part(X m x)) n x >= c}
         IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (\m x. pos_part((X:num->A->real) m x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                   `X:num->A->real`] SIMPLE_SUBMARTINGALE_POS_PART) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(fun th -> MP_TAC(REWRITE_RULE[simple_submartingale] th)) THEN
   DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
   REWRITE_TAC[simple_adapted] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
    `(\m x. pos_part((X:num->A->real) m x)):num->A->real`; `c:real`; `n:num`]
    RUNNING_MAX_EXCEEDS_IN_FILTRATION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [filtration]) THEN
  DISCH_THEN(MP_TAC o SPEC `n:num` o CONJUNCT1) THEN
  REWRITE_TAC[sub_sigma_algebra] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* Helper: running_max monotone in n *)
let RUNNING_MAX_MONO_SUC = prove
 (`!X:num->A->real. !n x.
     running_max X n x <= running_max X (SUC n) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[running_max] THEN
  REWRITE_TAC[REAL_ARITH `a <= max a b`]);;

(* Helper: running_max >= X m for m <= n *)
let RUNNING_MAX_GE = prove
 (`!X:num->A->real. !n m x. m <= n ==> X m x <= running_max X n x`,
  GEN_TAC THEN INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC[CONJUNCT1 LE; running_max] THEN
   DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
   X_GEN_TAC `m:num` THEN GEN_TAC THEN DISCH_TAC THEN
   ASM_CASES_TAC `m = SUC n` THENL
   [ASM_REWRITE_TAC[running_max] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `running_max (X:num->A->real) n x` THEN
    CONJ_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
     REWRITE_TAC[running_max] THEN REAL_ARITH_TAC]]]);;

(* Helper: X_n event in prob_events from simple_rv *)
let SIMPLE_RV_LE_EVENT = prove
 (`!p:A prob_space (X:A->real) v.
     simple_rv p X
     ==> {x | x IN prob_carrier p /\ X x <= v} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_rv]) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[random_variable] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real`) THEN REWRITE_TAC[]);;

let INTERS_UNIONS_IN_EVENTS = prove
 (`!p (A:num->num->(A->bool)).
    (!k:num n:num. A k n IN prob_events p)
    ==> INTERS {UNIONS {A k n | n IN (:num)} | k IN (:num)}
        IN prob_events p`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN GEN_TAC THEN
  MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN GEN_TAC THEN
  ASM_REWRITE_TAC[]);;

(* Helper: running_max of neg part event in prob_events *)
let SIMPLE_RUNNING_MAX_NEG_PART_EVENT = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) c n.
     simple_submartingale p FF X
     ==> {x | x IN prob_carrier p /\
              running_max (\m x. max (--X m x) (&0)) n x >= c}
         IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SPEC_TAC(`n:num`, `n:num`) THEN INDUCT_TAC THENL
  [REWRITE_TAC[running_max] THEN
   ASM_CASES_TAC `c <= &0` THENL
   [SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ max (--((X:num->A->real) 0 x)) (&0) >= c} =
       prob_carrier p`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
     EQ_TAC THENL
     [SIMP_TAC[];
      DISCH_TAC THEN ASM_REWRITE_TAC[real_ge] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
     REWRITE_TAC[PROB_CARRIER_IN_EVENTS]];
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ max (--((X:num->A->real) 0 x)) (&0) >= c} =
       {x | x IN prob_carrier p /\ X 0 x <= --c}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
     EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     POP_ASSUM MP_TAC THEN UNDISCH_TAC `~(c <= &0)` THEN REAL_ARITH_TAC;
     MATCH_MP_TAC SIMPLE_RV_LE_EVENT THEN REWRITE_TAC[ETA_AX] THEN
     ASM_MESON_TAC[simple_submartingale]]];
   REWRITE_TAC[running_max] THEN
   ASM_CASES_TAC `c <= &0` THENL
   [SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\
              max (running_max (\m x. max (--((X:num->A->real) m x)) (&0)) n x)
                  (max (--X (SUC n) x) (&0)) >= c} =
       prob_carrier p`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
     EQ_TAC THENL
     [SIMP_TAC[];
      DISCH_TAC THEN ASM_REWRITE_TAC[real_ge] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
     REWRITE_TAC[PROB_CARRIER_IN_EVENTS]];
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\
              max (running_max (\m x. max (--((X:num->A->real) m x)) (&0)) n x)
                  (max (--X (SUC n) x) (&0)) >= c} =
       {x | x IN prob_carrier p /\
            running_max (\m x. max (--X m x) (&0)) n x >= c} UNION
       {x | x IN prob_carrier p /\ X (SUC n) x <= --c}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; REAL_MAX_GE] THEN
     GEN_TAC THEN
     ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     EQ_TAC THENL
     [DISCH_THEN DISJ_CASES_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISJ2_TAC THEN POP_ASSUM MP_TAC THEN
      UNDISCH_TAC `~(c <= &0)` THEN REAL_ARITH_TAC;
      DISCH_THEN DISJ_CASES_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISJ2_TAC THEN POP_ASSUM MP_TAC THEN
      UNDISCH_TAC `~(c <= &0)` THEN REAL_ARITH_TAC];
     MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC SIMPLE_RV_LE_EVENT THEN REWRITE_TAC[ETA_AX] THEN
      ASM_MESON_TAC[simple_submartingale]]]]]);;

(* Helper: decompose expectation over carrier as sum over A and B = carrier\A *)
let SIMPLE_EXPECTATION_PARTITION = prove
 (`!p:A prob_space (X:A->real) (a:A->bool).
     simple_rv p X /\ a IN prob_events p
     ==> simple_expectation p X =
         simple_expectation p (\x. X x * indicator_fn a x) +
         simple_expectation p (\x. X x * indicator_fn (prob_carrier p DIFF a) x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (X:A->real) =
     simple_expectation p (\x. X x * indicator_fn a x +
                                X x * indicator_fn (prob_carrier p DIFF a) x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
   X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
   REWRITE_TAC[indicator_fn; IN_DIFF] THEN
   ASM_CASES_TAC `(y:A) IN a` THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC;
   MATCH_MP_TAC SIMPLE_EXPECTATION_ADD THEN
   CONJ_TAC THEN MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN
   ASM_REWRITE_TAC[PROB_CARRIER_IN_EVENTS]]);;

(* Neg part maximal inequality for submartingales *)
let SIMPLE_SUBMARTINGALE_NEG_PART_MAXIMAL = prove
 (`!p:A prob_space FF X c (n:num) C.
     simple_submartingale p FF X /\ &0 < c /\
     (!n. simple_expectation p (\x. abs(X n x)) <= C)
     ==> c * prob p {x | x IN prob_carrier p /\
                         running_max (\m x. max (--(X m x)) (&0)) n x >= c}
         <= &2 * C`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
  [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF X` ASSUME_TAC THENL
  [ASM_MESON_TAC[simple_submartingale; simple_adapted]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!n. {x:A | x IN prob_carrier p /\
               running_max (\m x. max (--((X:num->A->real) m x)) (&0)) n x >= c}
         IN (FF:num->(A->bool)->bool) n`
    ASSUME_TAC THENL
  [INDUCT_TAC THENL
   [REWRITE_TAC[running_max] THEN
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ max (--((X:num->A->real) 0 x)) (&0) >= c} =
       {x | x IN prob_carrier p /\ X 0 x <= --c}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
     EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     POP_ASSUM MP_TAC THEN UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
     FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [adapted]) THEN
     REWRITE_TAC[measurable_wrt] THEN
     DISCH_THEN(MP_TAC o SPEC `0`) THEN
     DISCH_THEN(MP_TAC o SPEC `--c:real`) THEN REWRITE_TAC[]];
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\
              running_max (\m x. max (--((X:num->A->real) m x)) (&0)) (SUC n) x >= c} =
       {x | x IN prob_carrier p /\
            running_max (\m x. max (--X m x) (&0)) n x >= c} UNION
       {x | x IN prob_carrier p /\ X (SUC n) x <= --c}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; running_max; REAL_MAX_GE] THEN
     X_GEN_TAC `z:A` THEN
     ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     EQ_TAC THENL
     [DISCH_THEN DISJ_CASES_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISJ2_TAC THEN POP_ASSUM MP_TAC THEN
      UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
      DISCH_THEN DISJ_CASES_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISJ2_TAC THEN POP_ASSUM MP_TAC THEN
      UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC];
     MATCH_MP_TAC SIGMA_ALGEBRA_UNION THEN
     CONJ_TAC THENL
     [ASM_MESON_TAC[filtration; sub_sigma_algebra]; ALL_TAC] THEN
     CONJ_TAC THENL
     [SUBGOAL_THEN `(FF:num->(A->bool)->bool) n SUBSET FF (SUC n)` MP_TAC THENL
      [ASM_MESON_TAC[filtration; LE; LE_REFL]; ALL_TAC] THEN
      ASM SET_TAC[];
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [adapted]) THEN
      REWRITE_TAC[measurable_wrt] THEN
      DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN
      DISCH_THEN(MP_TAC o SPEC `--c:real`) THEN REWRITE_TAC[]]]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!n. {x:A | x IN prob_carrier p /\
               running_max (\m x. max (--((X:num->A->real) m x)) (&0)) n x >= c}
         IN prob_events p`
    ASSUME_TAC THENL
  [GEN_TAC THEN ASM_MESON_TAC[filtration; sub_sigma_algebra; SUBSET];
   ALL_TAC] THEN
  ABBREV_TAC
    `A = \n. {x:A | x IN prob_carrier p /\
                    running_max (\m x. max (--((X:num->A->real) m x)) (&0)) n x >= c}` THEN
  ABBREV_TAC `B = \n. prob_carrier (p:A prob_space) DIFF (A:num->(A->bool)) n` THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\
            running_max (\m x. max (--((X:num->A->real) m x)) (&0)) n x >= c} =
     (A:num->(A->bool)) n`
    SUBST1_TAC THENL
  [EXPAND_TAC "A" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m. (B:num->(A->bool)) m IN prob_events p` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "B" THEN
   MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN
   ASM_REWRITE_TAC[PROB_CARRIER_IN_EVENTS] THEN
   EXPAND_TAC "A" THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m. (A:num->(A->bool)) m IN (FF:num->(A->bool)->bool) m`
    ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "A" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m. (A:num->(A->bool)) m IN prob_events p` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "A" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!m. simple_rv (p:A prob_space)
           (\x. (X:num->A->real) m x * indicator_fn ((B:num->(A->bool)) m) x)`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!m. simple_expectation (p:A prob_space)
           (\x. (X:num->A->real) m x * indicator_fn ((B:num->(A->bool)) m) x) <= C`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN
     `simple_expectation (p:A prob_space)
        (\x. (X:num->A->real) m x * indicator_fn ((B:num->(A->bool)) m) x) <=
      simple_expectation p (\x. abs(X m x))`
     MP_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_ABS THEN REWRITE_TAC[ETA_AX] THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[indicator_fn] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO] THENL
    [REAL_ARITH_TAC; REWRITE_TAC[REAL_ABS_POS]];
    MP_TAC(SPEC `m:num`
      (ASSUME `!n. simple_expectation (p:A prob_space) (\x. abs ((X:num->A->real) n x)) <= C`)) THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!m. simple_expectation (p:A prob_space)
           (\x. (X:num->A->real) m x * indicator_fn ((B:num->(A->bool)) m) x)
         >= --C + c * prob p ((A:num->(A->bool)) m)`
    ASSUME_TAC THENL
  [INDUCT_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) 0`;
                    `(A:num->(A->bool)) 0`]
      SIMPLE_EXPECTATION_PARTITION) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `prob_carrier (p:A prob_space) DIFF (A:num->(A->bool)) 0 = B 0`
      SUBST1_TAC THENL
    [EXPAND_TAC "B" THEN REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
      `simple_expectation (p:A prob_space) (\x. (X:num->A->real) 0 x * indicator_fn ((A:num->(A->bool)) 0) x)
       <= --c * prob p (A 0)`
      ASSUME_TAC THENL
    [SUBGOAL_THEN
       `simple_rv (p:A prob_space) (\x. --c * indicator_fn ((A:num->(A->bool)) 0) x)`
       ASSUME_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
      REWRITE_TAC[SIMPLE_RV_CONST] THEN MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     SUBGOAL_THEN
       `--c * prob (p:A prob_space) ((A:num->(A->bool)) 0) =
        simple_expectation p (\x. --c * indicator_fn (A 0) x)`
       SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      SUBGOAL_THEN
        `simple_expectation (p:A prob_space) (\x. --c * indicator_fn ((A:num->(A->bool)) 0) x) =
         --c * simple_expectation p (indicator_fn (A 0))`
        SUBST1_TAC THENL
      [MATCH_MP_TAC SIMPLE_EXPECTATION_CMUL THEN
       MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[];
       AP_TERM_TAC THEN MATCH_MP_TAC SIMPLE_EXPECTATION_INDICATOR THEN
       ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
     MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[indicator_fn] THEN
     COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; REAL_LE_REFL] THEN
     UNDISCH_TAC `(y:A) IN (A:num->(A->bool)) 0` THEN
     EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM; running_max] THEN
     STRIP_TAC THEN POP_ASSUM MP_TAC THEN
     UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `simple_expectation (p:A prob_space) ((X:num->A->real) 0) >= --C`
      ASSUME_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) 0`]
       SIMPLE_EXPECTATION_ABS_LE) THEN
     ASM_REWRITE_TAC[] THEN
     MP_TAC(SPEC `0` (ASSUME `!n. simple_expectation (p:A prob_space)
       (\x. abs((X:num->A->real) n x)) <= C`)) THEN
     REAL_ARITH_TAC;
     ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ABBREV_TAC
      `D = (B:num->(A->bool)) m INTER
           {x:A | x IN prob_carrier p /\ (X:num->A->real) (SUC m) x <= --c}` THEN
    SUBGOAL_THEN `(B:num->(A->bool)) (SUC m) = B m DIFF D` ASSUME_TAC THENL
    [EXPAND_TAC "D" THEN EXPAND_TAC "B" THEN EXPAND_TAC "A" THEN
     REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTER; IN_ELIM_THM;
                 running_max; REAL_MAX_GE] THEN
     X_GEN_TAC `z:A` THEN
     ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `D:A->bool IN prob_events p` ASSUME_TAC THENL
    [EXPAND_TAC "D" THEN MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC SIMPLE_RV_LE_EVENT THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT ((A:num->(A->bool)) m) D` ASSUME_TAC THENL
    [EXPAND_TAC "D" THEN EXPAND_TAC "B" THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(A:num->(A->bool)) (SUC m) = A m UNION D` ASSUME_TAC THENL
    [EXPAND_TAC "D" THEN EXPAND_TAC "B" THEN EXPAND_TAC "A" THEN
     REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_DIFF; IN_ELIM_THM;
                 running_max; REAL_MAX_GE] THEN
     X_GEN_TAC `z:A` THEN
     ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN
      `prob (p:A prob_space) ((A:num->(A->bool)) (SUC m)) =
       prob p (A m) + prob p D`
      ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PROB_ADDITIVE THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `(B:num->(A->bool)) m IN (FF:num->(A->bool)->bool) m`
      ASSUME_TAC THENL
    [EXPAND_TAC "B" THEN
     SUBGOAL_THEN `prob_carrier (p:A prob_space) DIFF (A:num->(A->bool)) m =
                    UNIONS ((FF:num->(A->bool)->bool) m) DIFF A m` SUBST1_TAC THENL
     [AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_MESON_TAC[filtration; sub_sigma_algebra];
      MATCH_MP_TAC SIGMA_ALGEBRA_COMPL THEN
      ASM_MESON_TAC[filtration; sub_sigma_algebra]];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `simple_expectation (p:A prob_space)
         (\x. (X:num->A->real) m x * indicator_fn ((B:num->(A->bool)) m) x) <=
       simple_expectation p
         (\x. X (SUC m) x * indicator_fn (B m) x)`
      ASSUME_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                     `X:num->A->real`; `m:num`; `SUC m`;
                     `(B:num->(A->bool)) m`]
       SIMPLE_SUBMARTINGALE_LOCALIZED_INCREASING) THEN
     ASM_REWRITE_TAC[ARITH_RULE `m <= SUC m`];
     ALL_TAC] THEN
    SUBGOAL_THEN `(B:num->(A->bool)) m = B (SUC m) UNION D` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN SET_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT ((B:num->(A->bool)) (SUC m)) D` ASSUME_TAC THENL
    [REWRITE_TAC[DISJOINT] THEN
     UNDISCH_TAC `(B:num->(A->bool)) (SUC m) = B m DIFF D` THEN SET_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `simple_expectation (p:A prob_space)
         (\x. (X:num->A->real) (SUC m) x * indicator_fn ((B:num->(A->bool)) m) x) =
       simple_expectation p
         (\x. X (SUC m) x * indicator_fn (B (SUC m)) x) +
       simple_expectation p
         (\x. X (SUC m) x * indicator_fn D x)`
      ASSUME_TAC THENL
    [SUBGOAL_THEN
       `simple_expectation (p:A prob_space)
          (\x. (X:num->A->real) (SUC m) x * indicator_fn ((B:num->(A->bool)) m) x) =
        simple_expectation p
          (\x. X (SUC m) x * indicator_fn (B (SUC m)) x +
               X (SUC m) x * indicator_fn D x)`
       SUBST1_TAC THENL
     [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
      REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `(B:num->(A->bool)) m = B (SUC m) UNION D` THEN
      DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC INDICATOR_FN_DISJOINT_UNION THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC SIMPLE_EXPECTATION_ADD THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
       CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]];
       MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
       CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]]]];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `simple_expectation (p:A prob_space)
         (\x. (X:num->A->real) (SUC m) x * indicator_fn D x) <=
       --c * prob p D`
      ASSUME_TAC THENL
    [SUBGOAL_THEN
       `--c * prob (p:A prob_space) D =
        simple_expectation p (\x. --c * indicator_fn D x)`
       SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      SUBGOAL_THEN
        `simple_expectation (p:A prob_space) (\x. --c * indicator_fn D x) =
         --c * simple_expectation p (indicator_fn D)`
        SUBST1_TAC THENL
      [MATCH_MP_TAC SIMPLE_EXPECTATION_CMUL THEN
       MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[];
       AP_TERM_TAC THEN MATCH_MP_TAC SIMPLE_EXPECTATION_INDICATOR THEN
       ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
     MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THENL
      [REWRITE_TAC[SIMPLE_RV_CONST];
       MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
     X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[indicator_fn] THEN
     COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; REAL_LE_REFL] THEN
     UNDISCH_TAC `(y:A) IN D` THEN EXPAND_TAC "D" THEN
     REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
     STRIP_TAC THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    POP_ASSUM MP_TAC THEN
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM MP_TAC THEN
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM(fun th ->
      REWRITE_TAC[th; REAL_ADD_LDISTRIB; REAL_MUL_LNEG]) THEN
    UNDISCH_TAC
      `simple_expectation (p:A prob_space)
         (\x. (X:num->A->real) m x * indicator_fn ((B:num->(A->bool)) m) x) >=
       --C + c * prob p ((A:num->(A->bool)) m)` THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  MP_TAC(SPEC `n:num`
    (ASSUME `!m. simple_expectation (p:A prob_space)
               (\x. (X:num->A->real) m x * indicator_fn ((B:num->(A->bool)) m) x) >=
             --C + c * prob p ((A:num->(A->bool)) m)`)) THEN
  MP_TAC(SPEC `n:num`
    (ASSUME `!m. simple_expectation (p:A prob_space)
               (\x. (X:num->A->real) m x * indicator_fn ((B:num->(A->bool)) m) x) <= C`)) THEN
  REAL_ARITH_TAC);;

(* Main theorem: L1-bounded simple_submartingale converges almost surely *)
let SIMPLE_MARTINGALE_CONVERGENCE_L1_BOUNDED = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) C.
     simple_submartingale p FF X /\
     (!n. simple_expectation p (\x. abs(X n x)) <= C)
     ==> almost_surely p
           {x | ?L. ((\n. X n x) ---> L) sequentially}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!m:num. simple_rv (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[simple_submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)`
    ASSUME_TAC THENL
    [ASM_MESON_TAC[simple_submartingale; simple_adapted]; ALL_TAC] THEN
  MP_TAC RATIONAL_ENUMERATION THEN
  DISCH_THEN(X_CHOOSE_TAC `g:num->real`) THEN
  (* Part 1: a.s. for each k, upcrossings of (g(fst k), g(snd k)) finite *)
  SUBGOAL_THEN
    `!k. almost_surely (p:A prob_space)
       {x:A | (g:num->real)(NUMFST k) < g(NUMSND k) ==>
              (?B. !n. num_upcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)}`
    ASSUME_TAC THENL
  [X_GEN_TAC `k:num` THEN
   ASM_CASES_TAC `(g:num->real)(NUMFST k) < g(NUMSND k)` THENL
   [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x:A | ?B. !n. num_upcrossings (X:num->A->real)
                  ((g:num->real)(NUMFST k)) (g(NUMSND k)) n x <= B}` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_FINITE_UPCROSSINGS_AS_L1 THEN
     MAP_EVERY EXISTS_TAC [`FF:num->(A->bool)->bool`; `C:real`] THEN
     ASM_REWRITE_TAC[];
     REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    SUBGOAL_THEN
      `{x:A | (g:num->real)(NUMFST k) < g(NUMSND k) ==>
              (?B. !n. num_upcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)} = (:A)`
      (fun th -> REWRITE_TAC[th; ALMOST_SURELY_UNIV]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
    ASM_MESON_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `almost_surely (p:A prob_space)
       (INTERS {{x:A | (g:num->real)(NUMFST k) < g(NUMSND k) ==>
              (?B. !n. num_upcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)}
             | k IN (:num)})`
    ASSUME_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Part 2: a.s. sup pos_part(X_n) is finite *)
  SUBGOAL_THEN
    `almost_surely (p:A prob_space)
       {x:A | ?M. !n. pos_part((X:num->A->real) n x) <= M}`
    ASSUME_TAC THENL
  [REWRITE_TAC[almost_surely] THEN
   EXISTS_TAC `INTERS {UNIONS {
     {x:A | x IN prob_carrier p /\
            running_max (\m x. pos_part ((X:num->A->real) m x)) n x
            >= &(SUC k)}
   | n IN (:num)} | k IN (:num)}` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[null_event] THEN CONJ_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`;
       `\k n. {x:A | x IN prob_carrier p /\
          running_max (\m x. pos_part ((X:num->A->real) m x)) n x
          >= &(SUC k)}`] INTERS_UNIONS_IN_EVENTS) THEN
     REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
     MATCH_MP_TAC SIMPLE_RUNNING_MAX_POS_PART_EVENT THEN
     EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC REAL_EQ_0_FROM_INV_BOUND THEN
     EXISTS_TAC `C:real` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PROB_POSITIVE THEN
      MP_TAC(ISPECL [`p:A prob_space`;
        `\k n. {x:A | x IN prob_carrier p /\
           running_max (\m x. pos_part ((X:num->A->real) m x)) n x
           >= &(SUC k)}`] INTERS_UNIONS_IN_EVENTS) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
      MATCH_MP_TAC SIMPLE_RUNNING_MAX_POS_PART_EVENT THEN
      EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `j:num` THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `prob (p:A prob_space) (UNIONS {
        {x:A | x IN prob_carrier p /\
               running_max (\m x. pos_part ((X:num->A->real) m x)) n x
               >= &(SUC j)} | n IN (:num)})` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC PROB_MONO THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`p:A prob_space`;
          `\k n. {x:A | x IN prob_carrier p /\
             running_max (\m x. pos_part ((X:num->A->real) m x)) n x
             >= &(SUC k)}`] INTERS_UNIONS_IN_EVENTS) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
        MATCH_MP_TAC SIMPLE_RUNNING_MAX_POS_PART_EVENT THEN
        EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN GEN_TAC THEN
        MATCH_MP_TAC SIMPLE_RUNNING_MAX_POS_PART_EVENT THEN
        EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_INTERS; SIMPLE_IMAGE;
                     FORALL_IN_IMAGE; IN_UNIV] THEN
        GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
        REWRITE_TAC[]];
       MP_TAC(ISPECL [
        `p:A prob_space`;
        `\n. {x:A | x IN prob_carrier p /\
           running_max (\m x. pos_part ((X:num->A->real) m x)) n x
           >= &(SUC j)}`;
        `C / &(SUC j)`] PROB_UNIONS_INCREASING_BOUND) THEN
       REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
       REPEAT CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC SIMPLE_RUNNING_MAX_POS_PART_EVENT THEN
        EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
        GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[real_ge] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `running_max (\m x. pos_part ((X:num->A->real) m x))
                      n (x:A)` THEN
        REWRITE_TAC[RUNNING_MAX_MONO_SUC] THEN
        FIRST_X_ASSUM(ACCEPT_TAC o REWRITE_RULE[real_ge]);
        X_GEN_TAC `nn:num` THEN
        MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                        `X:num->A->real`; `&(SUC j)`; `nn:num`; `C:real`]
          SIMPLE_DOOB_MAXIMAL_POS_PART) THEN
        ANTS_TAC THENL
        [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_TAC THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LT_0] THEN
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]]]]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERS] THEN
    X_GEN_TAC `x:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM])) THEN
    REWRITE_TAC[NOT_FORALL_THM; REAL_NOT_LE] THEN DISCH_TAC THEN
    GEN_TAC THEN REWRITE_TAC[SIMPLE_IMAGE; IN_IMAGE; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&(SUC k)`) THEN
    DISCH_THEN(X_CHOOSE_TAC `nn:num`) THEN
    EXISTS_TAC `nn:num` THEN ASM_REWRITE_TAC[real_ge] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `(\m x. pos_part ((X:num->A->real) m x)) nn x` THEN
    CONJ_TAC THENL [BETA_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC RUNNING_MAX_GE THEN REWRITE_TAC[LE_REFL]];
   ALL_TAC] THEN
  (* Part 3: a.s. X doesn't go to -infty *)
  (* Use Markov: P(X_n <= -K) <= C/K for each n *)
  SUBGOAL_THEN
    `almost_surely (p:A prob_space)
       {x:A | ?K:num. !N:num. ?n. N <= n /\
              (X:num->A->real) n x > --(&K)}`
    ASSUME_TAC THENL
  [REWRITE_TAC[almost_surely] THEN
   EXISTS_TAC `INTERS
     {UNIONS {{x:A | x IN prob_carrier p /\
                     (X:num->A->real) n x <= --(&(SUC k))}
              | n IN (:num)} | k IN (:num)}` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[null_event] THEN CONJ_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`;
       `\k n. {x:A | x IN prob_carrier p /\
          (X:num->A->real) n x <= --(&(SUC k))}`]
       INTERS_UNIONS_IN_EVENTS) THEN
     REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
     MATCH_MP_TAC SIMPLE_RV_LE_EVENT THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC REAL_EQ_0_FROM_INV_BOUND THEN
     EXISTS_TAC `&2 * C` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PROB_POSITIVE THEN
      MP_TAC(ISPECL [`p:A prob_space`;
        `\k n. {x:A | x IN prob_carrier p /\
           (X:num->A->real) n x <= --(&(SUC k))}`]
        INTERS_UNIONS_IN_EVENTS) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
      MATCH_MP_TAC SIMPLE_RV_LE_EVENT THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
        `prob (p:A prob_space) (UNIONS {
           {x:A | x IN prob_carrier p /\
                  running_max (\m x. max (--((X:num->A->real) m x)) (&0)) n x
                  >= &(SUC k)}
           | n IN (:num)})` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC PROB_MONO THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`p:A prob_space`;
          `\k n. {x:A | x IN prob_carrier p /\
             (X:num->A->real) n x <= --(&(SUC k))}`]
          INTERS_UNIONS_IN_EVENTS) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
        MATCH_MP_TAC SIMPLE_RV_LE_EVENT THEN
        REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN GEN_TAC THEN
        MATCH_MP_TAC SIMPLE_RUNNING_MAX_NEG_PART_EVENT THEN
        EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_INTERS; SIMPLE_IMAGE;
                     FORALL_IN_IMAGE; IN_UNIV] THEN
        X_GEN_TAC `x:A` THEN
        DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
        REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `nn:num` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `nn:num` THEN ASM_REWRITE_TAC[real_ge] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(\m x. max (--((X:num->A->real) m x)) (&0)) nn (x:A)` THEN
        CONJ_TAC THENL
        [BETA_TAC THEN
         MATCH_MP_TAC REAL_LE_TRANS THEN
         EXISTS_TAC `--((X:num->A->real) nn x)` THEN
         CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
         MATCH_MP_TAC RUNNING_MAX_GE THEN REWRITE_TAC[LE_REFL]]];
       MP_TAC(ISPECL [
        `p:A prob_space`;
        `\n. {x:A | x IN prob_carrier p /\
           running_max (\m x. max (--((X:num->A->real) m x)) (&0)) n x
           >= &(SUC k)}`;
        `(&2 * C) / &(SUC k)`] PROB_UNIONS_INCREASING_BOUND) THEN
       REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
       REPEAT CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC SIMPLE_RUNNING_MAX_NEG_PART_EVENT THEN
        EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
        GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[real_ge] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `running_max (\m x. max (--((X:num->A->real) m x)) (&0))
                      n (x:A)` THEN
        REWRITE_TAC[RUNNING_MAX_MONO_SUC] THEN
        FIRST_X_ASSUM(ACCEPT_TAC o REWRITE_RULE[real_ge]);
        X_GEN_TAC `nn:num` THEN
        MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                        `X:num->A->real`; `&(SUC k)`; `nn:num`; `C:real`]
          SIMPLE_SUBMARTINGALE_NEG_PART_MAXIMAL) THEN
        ANTS_TAC THENL
        [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_TAC THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LT_0] THEN
        GEN_REWRITE_TAC (LAND_CONV) [REAL_MUL_SYM] THEN
        ASM_REWRITE_TAC[]]]]];
    (* Containment *)
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERS] THEN
    X_GEN_TAC `x:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM])) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM;
                TAUT `~(a /\ b) <=> a ==> ~b`; real_gt; REAL_NOT_LT] THEN
    DISCH_TAC THEN GEN_TAC THEN
    REWRITE_TAC[SIMPLE_IMAGE; IN_IMAGE; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N0:num` (MP_TAC o SPEC `N0:num`)) THEN
    REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
    EXISTS_TAC `N0:num` THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Combine and apply analytic lemma *)
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
    `(INTERS {{x:A | (g:num->real)(NUMFST k) < g(NUMSND k) ==>
              (?B. !n. num_upcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)}
             | k IN (:num)}) INTER
     {x:A | ?M. !n. pos_part((X:num->A->real) n x) <= M} INTER
     {x:A | ?K:num. !N:num. ?n. N <= n /\ X n x > --(&K)}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_INTER THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC ALMOST_SURELY_INTER THEN ASM_REWRITE_TAC[]];
   REWRITE_TAC[IN_ELIM_THM; IN_INTER; IN_INTERS] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (X_CHOOSE_TAC `M0:real`)
                       (X_CHOOSE_TAC `K0:num`))) THEN
   SUBGOAL_THEN
     `!k. (g:num->real)(NUMFST k) < g(NUMSND k)
          ==> ?B. !n. num_upcrossings (X:num->A->real)
                        (g(NUMFST k)) (g(NUMSND k)) n x <= B`
     ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `{x:A | (g:num->real)(NUMFST (k:num)) < g(NUMSND k) ==>
              (?B. !n. num_upcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)}`) THEN
    ANTS_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
     EXISTS_TAC `k:num` THEN REFL_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `!n:num. (X:num->A->real) n x <= M0` ASSUME_TAC THENL
   [X_GEN_TAC `nn:num` THEN
    UNDISCH_TAC `!n:num. pos_part ((X:num->A->real) n x) <= M0` THEN
    DISCH_THEN(MP_TAC o SPEC `nn:num`) THEN
    REWRITE_TAC[pos_part; real_max] THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   MP_TAC(ISPECL [`\n:num. (X:num->A->real) n x`; `M0:real`]
     FINITE_UPCROSSINGS_CONVERGENT_OR_MINUS_INF) THEN
   REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?i:num. (g:num->real) i = a` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o SPEC `a:real` o
       GEN_REWRITE_RULE I [EXTENSION]) THEN
     REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
     ASM_REWRITE_TAC[IN] THEN MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?j:num. (g:num->real) j = b` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o SPEC `b:real` o
       GEN_REWRITE_RULE I [EXTENSION]) THEN
     REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
     ASM_REWRITE_TAC[IN] THEN MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `!k:num. (g:num->real)(NUMFST k) < g(NUMSND k)
                 ==> (?B. !n. num_upcrossings (X:num->A->real)
                                (g(NUMFST k)) (g(NUMSND k)) n x <= B)` THEN
    DISCH_THEN(MP_TAC o SPEC `NUMPAIR (i:num) (j:num)`) THEN
    REWRITE_TAC[NUMPAIR_DEST] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `B:num`) THEN
    EXISTS_TAC `B:num` THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[num_upcrossings]; ALL_TAC] THEN
   DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC MP_TAC) THEN
   DISCH_TAC THEN
   SUBGOAL_THEN `F` CONTR_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `K0:num`) THEN
   DISCH_THEN(X_CHOOSE_THEN `N0:num` ASSUME_TAC) THEN
   UNDISCH_TAC `!N:num. ?n:num. N <= n /\ (X:num->A->real) n x > --(&K0)` THEN
   DISCH_THEN(MP_TAC o SPEC `N0:num`) THEN
   DISCH_THEN(X_CHOOSE_THEN `n0:num` STRIP_ASSUME_TAC) THEN
   UNDISCH_TAC `!n:num. N0 <= n ==> (X:num->A->real) n x <= --(&K0)` THEN
   DISCH_THEN(MP_TAC o SPEC `n0:num`) THEN
   ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `(X:num->A->real) n0 x > --(&K0)` THEN
   REWRITE_TAC[real_gt] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* UI SIMPLE_SUBMARTINGALE CONVERGENCE                                              *)
(* Uniformly integrable submartingales converge almost surely.               *)
(* Combines UI_IMP_L1_BOUNDED with SIMPLE_MARTINGALE_CONVERGENCE_L1_BOUNDED.        *)
(* ========================================================================= *)

let SIMPLE_UI_SUBMARTINGALE_CONVERGENCE_AS = prove
 (`!p:A prob_space FF X.
    uniformly_integrable p X /\ simple_submartingale p FF X
    ==> almost_surely p {x | ?L. ((\n. X n x) ---> L) sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP UI_IMP_L1_BOUNDED) THEN
  DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN
  MATCH_MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                        `X:num->A->real`; `C:real`]
    SIMPLE_MARTINGALE_CONVERGENCE_L1_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) ((X:num->A->real) n)` ASSUME_TAC THENL
  [UNDISCH_TAC `simple_submartingale (p:A prob_space) FF (X:num->A->real)` THEN
   SIMP_TAC[simple_submartingale];
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_expectation (p:A prob_space) (\x:A. abs((X:num->A->real) n x)) =
                expectation p (\x. abs(X n x))` SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN
   MATCH_MP_TAC SIMPLE_RV_ABS THEN
   ASM_REWRITE_TAC[ETA_AX];
   ASM_REWRITE_TAC[]]);;

(* Expectation of simple_rv restricted to a null event is zero.              *)
(* Useful for bridging a.s. and L1 convergence.                              *)
let SIMPLE_EXPECTATION_NULL_EVENT = prove
 (`!p:A prob_space f a.
    simple_rv p f /\ a IN prob_events p /\ prob p a = &0
    ==> simple_expectation p (\x. f x * indicator_fn a x) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (f:A->real) x * indicator_fn a x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MUL THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. abs((f:A->real) x))`
    (fun th -> MP_TAC(MATCH_MP SIMPLE_RV_BOUNDED th)) THENL
  [MATCH_MP_TAC SIMPLE_RV_ABS THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  REWRITE_TAC[BETA_THM] THEN DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x) <= &0 ==> x = &0`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space)
    (\x:A. abs((f:A->real) x * indicator_fn a x))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_ABS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space)
    (\x:A. M * indicator_fn (a:A->bool) x)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_ABS THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_MUL THEN CONJ_TAC THENL
    [REWRITE_TAC[SIMPLE_RV_CONST];
     REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[indicator_fn; REAL_ABS_MUL] THEN
   COND_CASES_TAC THENL
   [REWRITE_TAC[REAL_ABS_1; REAL_MUL_RID] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[BETA_THM];
    REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_RZERO] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (indicator_fn (a:A->bool))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SIMPLE_EXPECTATION_CMUL; ETA_AX] THEN
  ASM_SIMP_TAC[SIMPLE_EXPECTATION_INDICATOR] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL]);;

(* ========================================================================= *)
(* BACKWARD SIMPLE_MARTINGALE CONVERGENCE                                           *)
(* Reversed (backward) martingales converge a.s. using the forward           *)
(* upcrossing inequality applied to the reversed simple_submartingale, combined     *)
(* with the combinatorial DC_LE_REV_UC inequality.                           *)
(* ========================================================================= *)

(* --- Downcrossing continuation infrastructure --- *)

let UP_PHASE_WHEN_LE_A = prove(
  `!g:num->real a b m. g m <= a /\ a < b ==> upcrossing_phase g a b m = 1`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL [
    REWRITE_TAC[upcrossing_phase] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[upcrossing_phase] THEN STRIP_TAC THEN
    COND_CASES_TAC THENL [ASM_REWRITE_TAC[];
      COND_CASES_TAC THENL [
        SUBGOAL_THEN `F` (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[]]]]);;

let UP_PHASE_1_NOT_GE_B = prove(
  `!g:num->real a b n. a < b ==> ~(upcrossing_phase g a b n = 1 /\ g n >= b)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL [
    REWRITE_TAC[upcrossing_phase] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    TRY ARITH_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[upcrossing_phase] THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN
    TRY ARITH_TAC THEN ASM_REAL_ARITH_TAC]);;

let DC_PHASE_STAYS_1 = prove(
  `!f:num->real a b k. downcrossing_phase f a b 0 = 1 /\
   (!j. j <= k ==> f j > a) ==>
   downcrossing_phase f a b k = 1 /\ downcrossing_count f a b k = 0`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL [
    REWRITE_TAC[downcrossing_phase; downcrossing_count] THEN MESON_TAC[];
    STRIP_TAC THEN
    SUBGOAL_THEN `downcrossing_phase f a b k = 1 /\ downcrossing_count f a b k = 0`
      STRIP_ASSUME_TAC THENL [
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[downcrossing_phase; downcrossing_count] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((f:num->real)(SUC k) <= a)` (fun th -> REWRITE_TAC[th]) THENL [
        FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN
        REWRITE_TAC[LE_REFL] THEN REAL_ARITH_TAC;
        ARITH_TAC]]]);;

let DC_RESTART = prove(
  `!f:num->real a b u. downcrossing_phase f a b 0 = 1 /\
   (!j. j < u ==> f j > a) /\ 1 <= u /\ f u <= a ==>
   downcrossing_phase f a b u = 0 /\ downcrossing_count f a b u = 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?v. u = SUC v` (CHOOSE_THEN SUBST_ALL_TAC) THENL [
    EXISTS_TAC `u - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `downcrossing_phase f a b v = 1 /\ downcrossing_count f a b v = 0`
    STRIP_ASSUME_TAC THENL [
    MATCH_MP_TAC DC_PHASE_STAYS_1 THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[downcrossing_phase; downcrossing_count] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(f:num->real)(SUC v) <= a` (fun th -> REWRITE_TAC[th]) THENL [
      ASM_REWRITE_TAC[]; ARITH_TAC]]);;

let DC_CONTINUATION = prove(
  `!k f:num->real a b u. downcrossing_phase f a b u = 0 /\ ~(f u >= b) ==>
   downcrossing_phase f a b (u + SUC k) =
     downcrossing_phase (\n. f(u + n)) a b (SUC k) /\
   downcrossing_count f a b (u + SUC k) =
     downcrossing_count f a b u + downcrossing_count (\n. f(u + n)) a b (SUC k)`,
  INDUCT_TAC THENL [
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `u + SUC 0 = SUC u`] THEN
    ONCE_REWRITE_TAC[downcrossing_phase] THEN
    ONCE_REWRITE_TAC[downcrossing_count] THEN
    ONCE_REWRITE_TAC[downcrossing_phase; downcrossing_count] THEN
    REWRITE_TAC[BETA_THM; ADD_0] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`f:num->real`; `a:real`; `b:real`; `u:num`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `u + SUC(SUC k) = SUC(u + SUC k)`] THEN
    ONCE_REWRITE_TAC[downcrossing_phase] THEN
    ONCE_REWRITE_TAC[downcrossing_count] THEN
    REWRITE_TAC[BETA_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `SUC(u + SUC k) = u + SUC(SUC k)`] THEN
    ARITH_TAC]);;

let DC_PHASE_SHIFT = prove(
  `!f:num->real a b k. downcrossing_phase f a b 0 = 0 ==>
   downcrossing_phase f a b (SUC k) = downcrossing_phase (\n. f(SUC n)) a b k /\
   downcrossing_count f a b (SUC k) = downcrossing_count (\n. f(SUC n)) a b k`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL [
    DISCH_TAC THEN
    ONCE_REWRITE_TAC[downcrossing_phase] THEN ONCE_REWRITE_TAC[downcrossing_count] THEN
    REWRITE_TAC[BETA_THM; downcrossing_count] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[downcrossing_phase] THEN ONCE_REWRITE_TAC[downcrossing_count] THEN
    REWRITE_TAC[BETA_THM] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let UP_PHASE_01 = prove(
  `!g:num->real a b n. upcrossing_phase g a b n = 0 \/ upcrossing_phase g a b n = 1`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL [
    REWRITE_TAC[upcrossing_phase] THEN COND_CASES_TAC THEN REWRITE_TAC[];
    ONCE_REWRITE_TAC[upcrossing_phase] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(COND_CASES_TAC THEN REWRITE_TAC[])]);;

let UC_PREFIX = prove(
  `!n f g:num->real a b. (!k. k <= n ==> f k = g k) ==>
    upcrossing_phase f a b n = upcrossing_phase g a b n /\
    upcrossing_count f a b n = upcrossing_count g a b n`,
  INDUCT_TAC THENL [
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[upcrossing_phase; upcrossing_count] THEN
    SUBGOAL_THEN `(f:num->real) 0 = g 0` (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`f:num->real`; `g:num->real`; `a:real`; `b:real`]) THEN
    ANTS_TAC THENL [
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      STRIP_TAC] THEN
    ONCE_REWRITE_TAC[upcrossing_phase] THEN
    ONCE_REWRITE_TAC[upcrossing_count] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(f:num->real)(SUC n) = g(SUC n)` (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

let UC_INCREMENT_PHASE_CHANGE = prove(
  `!n g:num->real a b m. upcrossing_phase g a b m = 1 /\
   upcrossing_phase g a b n = 0 /\ m < n ==>
   upcrossing_count g a b n >= upcrossing_count g a b m + 1`,
  INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[upcrossing_count] THEN
  MP_TAC(SPECL [`g:num->real`; `a:real`; `b:real`; `n:num`] UP_PHASE_01) THEN
  STRIP_TAC THENL [
    ASM_CASES_TAC `m < n:num` THENL [
      FIRST_X_ASSUM(MP_TAC o SPECL [`g:num->real`; `a:real`; `b:real`; `m:num`]) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      SUBGOAL_THEN `m = n:num` (fun th -> ASM_MESON_TAC[th; ARITH_RULE `~(1 = 0)`]) THEN
      ASM_ARITH_TAC];
    SUBGOAL_THEN `(g:num->real)(SUC n) >= b` ASSUME_TAC THENL [
      UNDISCH_TAC `upcrossing_phase g a b (SUC n) = 0` THEN
      ONCE_REWRITE_TAC[upcrossing_phase] THEN
      ASM_REWRITE_TAC[ARITH_RULE `~(1 = 0)`] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `upcrossing_count g a b m <= upcrossing_count g a b n` MP_TAC THENL [
        MATCH_MP_TAC UPCROSSING_COUNT_INCREASING THEN ASM_ARITH_TAC; ARITH_TAC]]]);;

let UC_COMPLETES = prove(
  `!g:num->real a b m n.
   g m <= a /\ g n >= b /\ a < b /\ m < n
   ==> upcrossing_count g a b n >= upcrossing_count g a b m + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `upcrossing_phase g a b m = 1` ASSUME_TAC THENL [
    MATCH_MP_TAC UP_PHASE_WHEN_LE_A THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`g:num->real`; `a:real`; `b:real`; `n:num`] UP_PHASE_01) THEN
  STRIP_TAC THENL [
    MP_TAC(SPECL [`n:num`; `g:num->real`; `a:real`; `b:real`; `m:num`]
      UC_INCREMENT_PHASE_CHANGE) THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`g:num->real`; `a:real`; `b:real`; `n:num`] UP_PHASE_1_NOT_GE_B) THEN
    ASM_REWRITE_TAC[]]);;

(* --- DC_LE_REV_UC: the combinatorial inequality dc(f,N) <= uc(rev f,N) + 1 --- *)

let DC_LE_REV_UC_CASE_LT = prove(
  `!N f:num->real a b.
    (!m. m < N ==> !f a b. a < b ==> downcrossing_count f a b m <=
      upcrossing_count (\k. f (m - k)) a b m + 1) ==>
    a < b ==> ~(N = 0) ==> ~(f 0 >= b) ==>
    downcrossing_count f a b N <= upcrossing_count (\k. f(N - k)) a b N + 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `downcrossing_phase (f:num->real) a b 0 = 0` ASSUME_TAC THENL [
    REWRITE_TAC[downcrossing_phase] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?M. N = SUC M` (CHOOSE_THEN SUBST_ALL_TAC) THENL [
    EXISTS_TAC `N - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`f:num->real`; `a:real`; `b:real`; `M:num`] DC_PHASE_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `M:num`) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`\n. (f:num->real)(SUC n)`; `a:real`; `b:real`]) THEN
  ASM_REWRITE_TAC[BETA_THM] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `upcrossing_count (\k. (f:num->real)(SUC(M - k))) a b M + 1` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!k:num. k <= M ==> SUC(M - k) = SUC M - k` ASSUME_TAC THENL [
    REPEAT STRIP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `a <= b ==> a + 1 <= b + 1`) THEN
  MP_TAC(SPECL [`M:num`; `\k. (f:num->real)(SUC(M - k))`;
                 `\k. (f:num->real)(SUC M - k)`; `a:real`; `b:real`] UC_PREFIX) THEN
  REWRITE_TAC[BETA_THM] THEN
  ANTS_TAC THENL [
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC UPCROSSING_COUNT_INCREASING THEN ARITH_TAC]);;

let DC_LE_REV_UC_CASE_GE = prove(
  `!N f:num->real a b.
    (!m. m < N ==> !f a b. a < b ==> downcrossing_count f a b m <=
      upcrossing_count (\k. f (m - k)) a b m + 1) ==>
    a < b ==> ~(N = 0) ==> f 0 >= b ==>
    downcrossing_count f a b N <= upcrossing_count (\k. f(N - k)) a b N + 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `downcrossing_phase (f:num->real) a b 0 = 1` ASSUME_TAC THENL [
    REWRITE_TAC[downcrossing_phase] THEN
    UNDISCH_TAC `(f:num->real) 0 >= b` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `?u:num. 1 <= u /\ u <= N /\ (f:num->real) u <= a` THENL [
    (* Crossing below a exists: find first such crossing *)
    SUBGOAL_THEN
      `?u:num. (1 <= u /\ u <= N /\ (f:num->real) u <= a) /\
               (!j:num. j < u ==> ~(1 <= j /\ j <= N /\ f j <= a))` MP_TAC THENL [
      REWRITE_TAC[GSYM num_WOP] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    (* Derive !j. j < u ==> f j > a *)
    SUBGOAL_THEN `!j:num. j < u ==> (f:num->real) j > a` ASSUME_TAC THENL [
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_CASES_TAC `j = 0` THENL [
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_gt] THEN
        UNDISCH_TAC `(f:num->real) 0 >= b` THEN UNDISCH_TAC `a < b` THEN
        REWRITE_TAC[real_ge] THEN REAL_ARITH_TAC;
        REWRITE_TAC[real_gt] THEN
        SUBGOAL_THEN `~((f:num->real) j <= a)` (fun th -> MESON_TAC[th; REAL_NOT_LE]) THEN
        FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    (* Apply DC_RESTART *)
    MP_TAC(SPECL [`f:num->real`; `a:real`; `b:real`; `u:num`] DC_RESTART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_CASES_TAC `u = N:num` THENL [
      (* u = N: dc_count = 1 <= uc + 1 *)
      SUBGOAL_THEN `downcrossing_count (f:num->real) a b N = 1` SUBST1_TAC THENL [
        ASM_MESON_TAC[];
        ARITH_TAC];
      (* u < N: use DC_CONTINUATION + IH + UC_COMPLETES *)
      SUBGOAL_THEN `u < N:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~((f:num->real) u >= b)` ASSUME_TAC THENL [
        UNDISCH_TAC `(f:num->real) u <= a` THEN UNDISCH_TAC `a < b` THEN
        REWRITE_TAC[real_ge] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`N - u - 1`; `f:num->real`; `a:real`; `b:real`; `u:num`]
        DC_CONTINUATION) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `u + SUC(N - u - 1) = N` (fun th -> REWRITE_TAC[th]) THENL [
        ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `SUC(N - u - 1) = N - u` (fun th -> REWRITE_TAC[th]) THENL [
        ASM_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      (* Now goal: 1 + dc(f', N-u) <= uc(g, N) + 1 *)
      SUBGOAL_THEN
        `downcrossing_count (\n. (f:num->real)(u + n)) a b (N - u) <=
         upcrossing_count (\k. f(u + (N - u) - k)) a b (N - u) + 1` MP_TAC THENL [
        UNDISCH_TAC `!m:num. m < N ==> (!f:num->real. !a b. a < b ==>
          downcrossing_count f a b m <= upcrossing_count (\k. f(m - k)) a b m + 1)` THEN
        DISCH_THEN(MP_TAC o SPEC `N - u:num`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`\n. (f:num->real)(u + n)`; `a:real`; `b:real`]) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[BETA_THM];
        ALL_TAC] THEN
      DISCH_TAC THEN
      (* Relate uc(\k. f(u+(N-u)-k), N-u) to uc(\k. f(N-k), N-u) via UC_PREFIX *)
      SUBGOAL_THEN
        `upcrossing_count (\k. (f:num->real)(u + (N - u) - k)) a b (N - u) =
         upcrossing_count (\k. f(N - k)) a b (N - u)` SUBST_ALL_TAC THENL [
        MP_TAC(REWRITE_RULE[BETA_THM]
          (INST [`N - u:num`, `n:num`]
            (SPECL [`\k:num. (f:num->real)(u + n - k)`;
                    `\k:num. (f:num->real)(N - k)`; `a:real`; `b:real`]
              (SPEC `n:num` UC_PREFIX)))) THEN
        ANTS_TAC THENL [
          X_GEN_TAC `k:num` THEN DISCH_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
          SIMP_TAC[]];
        ALL_TAC] THEN
      (* Now use UC_COMPLETES *)
      SUBGOAL_THEN `upcrossing_count (\k. (f:num->real)(N - k)) a b N >=
                    upcrossing_count (\k. f(N - k)) a b (N - u) + 1` MP_TAC THENL [
        MATCH_MP_TAC UC_COMPLETES THEN
        REWRITE_TAC[BETA_THM] THEN
        SUBGOAL_THEN `N - (N - u:num) = u` (fun th -> REWRITE_TAC[th]) THENL [
          ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `N - N:num = 0` (fun th -> REWRITE_TAC[th]) THENL [
          ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC]];
    (* No crossing below a: dc_count = 0 *)
    SUBGOAL_THEN `!j:num. j <= N ==> (f:num->real) j > a` ASSUME_TAC THENL [
      REPEAT STRIP_TAC THEN ASM_CASES_TAC `j = 0` THENL [
        ASM_REWRITE_TAC[real_gt] THEN
        UNDISCH_TAC `(f:num->real) 0 >= b` THEN UNDISCH_TAC `a < b` THEN
        REWRITE_TAC[real_ge] THEN REAL_ARITH_TAC;
        SUBGOAL_THEN `~((f:num->real) j <= a)` (fun th -> REWRITE_TAC[real_gt] THEN
          MESON_TAC[th; REAL_NOT_LE]) THEN
        UNDISCH_TAC `~(?u:num. 1 <= u /\ u <= N /\ (f:num->real) u <= a)` THEN
        REWRITE_TAC[NOT_EXISTS_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`f:num->real`; `a:real`; `b:real`; `N:num`] DC_PHASE_STAYS_1) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]]);;

let DC_LE_REV_UC = prove(
  `!N (f:num->real) a b. a < b ==>
    downcrossing_count f a b N <= upcrossing_count (\k. f(N - k)) a b N + 1`,
  MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `N = 0` THENL [
    ASM_REWRITE_TAC[downcrossing_count; SUB_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(f:num->real) 0 >= b` THENL [
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] DC_LE_REV_UC_CASE_GE) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] DC_LE_REV_UC_CASE_LT) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* --- Reversed simple_submartingale --- *)

let SIMPLE_REVERSED_IS_SUBMARTINGALE = prove(
  `!p FF (X:num->A->real) N. simple_backward_martingale p FF X
    ==> simple_submartingale p (\k. FF(N - k)) (\k. X(N - k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simple_backward_martingale; simple_submartingale] THEN
  STRIP_TAC THEN
  REPEAT CONJ_TAC THENL [
    REWRITE_TAC[filtration] THEN CONJ_TAC THENL [
      GEN_TAC THEN UNDISCH_TAC `decreasing_filtration (p:A prob_space) FF` THEN
      REWRITE_TAC[decreasing_filtration] THEN MESON_TAC[];
      REPEAT STRIP_TAC THEN UNDISCH_TAC `decreasing_filtration (p:A prob_space) FF` THEN
      REWRITE_TAC[decreasing_filtration] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC
    ];
    REWRITE_TAC[simple_adapted; adapted] THEN CONJ_TAC THENL [
      GEN_TAC THEN UNDISCH_TAC `simple_adapted (p:A prob_space) FF X` THEN
      REWRITE_TAC[simple_adapted; adapted] THEN MESON_TAC[];
      GEN_TAC THEN UNDISCH_TAC `simple_adapted (p:A prob_space) FF X` THEN
      REWRITE_TAC[simple_adapted] THEN MESON_TAC[]
    ];
    ASM_MESON_TAC[];
    X_GEN_TAC `k:num` THEN X_GEN_TAC `a:A->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k < N:num` THENL [
      SUBGOAL_THEN
        `simple_expectation p (\x. (X:num->A->real)(N - k) x * indicator_fn a x) =
         simple_expectation p (\x. X(N - SUC k) x * indicator_fn a x)`
        (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
      SUBGOAL_THEN `N - k = SUC(N - SUC k)` ASSUME_TAC THENL [
        ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `!n (a:A->bool). a IN FF (SUC n) ==>
        simple_expectation p (\x. (X:num->A->real) n x * indicator_fn a x) =
        simple_expectation p (\x. X (SUC n) x * indicator_fn a x)` THEN
      DISCH_THEN(MP_TAC o SPECL [`N - SUC k`; `a:A->bool`]) THEN
      SUBGOAL_THEN `SUC(N - SUC k) = N - k` (fun th -> REWRITE_TAC[th]) THENL [
        ASM_ARITH_TAC;
        UNDISCH_TAC `(a:A->bool) IN FF(N - k:num)` THEN
        SIMP_TAC[] THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `N - k = 0 /\ N - SUC k = 0`
        (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
      ASM_ARITH_TAC
    ]
  ]);;

(* --- Downcrossing-to-upcrossing negation identities --- *)

let num_downcrossings = new_definition
  `num_downcrossings (X:num->A->real) a b n x =
   downcrossing_count (\k. X k x) a b n`;;

let DOWNCROSSING_PHASE_EQ_NEG = prove(
  `!f a b n. downcrossing_phase f a b n =
             upcrossing_phase (\k. --(f k)) (--b) (--a) n`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL [
    REWRITE_TAC[downcrossing_phase; upcrossing_phase] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[downcrossing_phase; upcrossing_phase] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC]);;

let DOWNCROSSING_COUNT_EQ_NEG = prove(
  `!f a b n. downcrossing_count f a b n =
             upcrossing_count (\k. --(f k)) (--b) (--a) n`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL [
    REWRITE_TAC[downcrossing_count; upcrossing_count; DOWNCROSSING_PHASE_EQ_NEG];
    ASM_REWRITE_TAC[downcrossing_count; upcrossing_count;
                     DOWNCROSSING_PHASE_EQ_NEG] THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `(f:num->real)(SUC n) <= a <=> --(f(SUC n)) >= --a`
      (fun th -> REWRITE_TAC[th]) THEN
    REAL_ARITH_TAC]);;

let NUM_DOWNCROSSINGS_MONO = prove(
  `!X a b (m:num) n (x:A). m <= n ==>
    num_downcrossings X a b m x <= num_downcrossings X a b n x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[num_downcrossings; DOWNCROSSING_COUNT_EQ_NEG] THEN
  MATCH_ACCEPT_TAC UPCROSSING_COUNT_INCREASING);;

(* --- Auxiliary measurability lemmas --- *)

let SUB_SIGMA_ALGEBRA_SELF = prove(
  `!p:A prob_space. sub_sigma_algebra p (prob_events p)`,
  GEN_TAC THEN REWRITE_TAC[sub_sigma_algebra; SUBSET_REFL] THEN
  REWRITE_TAC[prob_carrier; PROB_SPACE_SIGMA_ALGEBRA]);;

(* --- Simple RV for downcrossing counts --- *)

let SIMPLE_RV_NUM_DOWNCROSSINGS = prove(
  `!(p:A prob_space) (X:num->A->real) a b n.
    (!n. simple_rv p (X n))
    ==> simple_rv p (\x. &(num_downcrossings X a b n x))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[num_downcrossings; DOWNCROSSING_COUNT_EQ_NEG] THEN
  SUBGOAL_THEN
    `(\x:A. &(upcrossing_count (\k. --((X:num->A->real) k x)) (--b) (--a) n)) =
     (\x. &(num_upcrossings (\k. \x. --(X k x)) (--b) (--a) n x))`
    SUBST1_TAC THENL [
    REWRITE_TAC[FUN_EQ_THM; num_upcrossings]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `\n:num. prob_events (p:A prob_space)`;
                 `\k:num. \x:A. --((X:num->A->real) k x)`;
                 `--b:real`; `--a:real`]
    SIMPLE_RV_NUM_UPCROSSINGS) THEN
  ANTS_TAC THENL [
    CONJ_TAC THENL [
      REWRITE_TAC[filtration; SUB_SIGMA_ALGEBRA_SELF; SUBSET_REFL]; ALL_TAC] THEN
    CONJ_TAC THENL [
      REWRITE_TAC[adapted] THEN X_GEN_TAC `m:num` THEN
      MP_TAC(MATCH_MP SIMPLE_RV_NEG
        (SPEC `m:num`
          (ASSUME `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`))) THEN
      REWRITE_TAC[simple_rv; random_variable; measurable_wrt] THEN MESON_TAC[];
      GEN_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SIMPLE_RV_NEG THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[]]);;

let SIMPLE_NUM_DOWNCROSSINGS_GE_EVENT = prove(
  `!(p:A prob_space) (X:num->A->real) a b n k.
    (!m. simple_rv p (X m))
    ==> {x | x IN prob_carrier p /\ &(num_downcrossings X a b n x) >= &k}
        IN prob_events p`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SIMPLE_RV_GE_EVENT THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] SIMPLE_RV_NUM_DOWNCROSSINGS) THEN
  ASM_REWRITE_TAC[]);;

(* --- Backward downcrossing bounds --- *)

let BACKWARD_DOWNCROSSING_EXPECTATION_BOUND = prove(
  `!(p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) a b N M.
    simple_backward_martingale p FF X /\ a < b /\
    (!m x. x IN prob_carrier p ==> abs(X m x) <= M)
    ==> (b - a) * simple_expectation p (\x. &(num_downcrossings X a b N x))
        <= M + abs a + (b - a)`,
  REPEAT STRIP_TAC THEN
  (* Pointwise bound: dc <= uc_rev + 1 *)
  SUBGOAL_THEN
    `!x:A. x IN prob_carrier p ==>
      &(num_downcrossings (X:num->A->real) a b N x) <=
      &(num_upcrossings (\k. X(N - k)) a b N x) + &1`
    ASSUME_TAC THENL [
    REPEAT STRIP_TAC THEN REWRITE_TAC[num_downcrossings; num_upcrossings] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC DC_LE_REV_UC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Get reversed simple_submartingale *)
  MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                  `X:num->A->real`; `N:num`] SIMPLE_REVERSED_IS_SUBMARTINGALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  (* Upcrossing expectation bound for reversed *)
  MP_TAC(ISPECL [`p:A prob_space`; `\k:num. (FF:num->(A->bool)->bool)(N - k)`;
                  `\k:num. (X:num->A->real)(N - k)`; `a:real`; `b:real`;
                  `N:num`; `M:real`]
    SIMPLE_UPCROSSING_EXPECTATION_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  (* simple_rv for dc *)
  SUBGOAL_THEN `simple_rv (p:A prob_space)
    (\x. &(num_downcrossings (X:num->A->real) a b N x))`
    ASSUME_TAC THENL [
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] SIMPLE_RV_NUM_DOWNCROSSINGS) THEN
    UNDISCH_TAC `simple_backward_martingale (p:A prob_space) FF X` THEN
    REWRITE_TAC[simple_backward_martingale] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* simple_rv for uc_rev *)
  SUBGOAL_THEN `simple_rv (p:A prob_space)
    (\x. &(num_upcrossings (\k. (X:num->A->real)(N - k)) a b N x))`
    ASSUME_TAC THENL [
    MP_TAC(ISPECL [`p:A prob_space`; `\k:num. (FF:num->(A->bool)->bool)(N - k)`;
                    `\k:num. (X:num->A->real)(N - k)`; `a:real`; `b:real`]
      SIMPLE_RV_NUM_UPCROSSINGS) THEN
    REWRITE_TAC[BETA_THM] THEN
    ANTS_TAC THENL [
      UNDISCH_TAC `simple_submartingale (p:A prob_space) (\k. FF (N - k)) (\k. X (N - k))` THEN
      REWRITE_TAC[simple_submartingale; simple_adapted] THEN MESON_TAC[];
      DISCH_THEN(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  (* simple_rv for uc_rev + 1 *)
  SUBGOAL_THEN `simple_rv (p:A prob_space)
    (\x. &(num_upcrossings (\k. (X:num->A->real)(N - k)) a b N x) + &1)`
    ASSUME_TAC THENL [
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] SIMPLE_RV_ADD) THEN
    ASM_REWRITE_TAC[SIMPLE_RV_CONST];
    ALL_TAC] THEN
  (* Main chain: (b-a)*E[dc] <= (b-a)*(E[uc_rev] + 1) <= (M+|a|) + (b-a) *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(b - a) * (simple_expectation (p:A prob_space)
    (\x. &(num_upcrossings (\k. (X:num->A->real)(N - k)) a b N x)) + &1)` THEN
  CONJ_TAC THENL [
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    (* E[dc] <= E[uc_rev] + 1 via monotonicity and linearity *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `simple_expectation (p:A prob_space)
      (\x. &(num_upcrossings (\k. (X:num->A->real)(N - k)) a b N x) + &1)` THEN
    CONJ_TAC THENL [
      (* E[dc] <= E[uc_rev + 1] by SIMPLE_EXPECTATION_MONO *)
      MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN ASM_REWRITE_TAC[];
      (* E[uc_rev + 1] = E[uc_rev] + 1 >= E[uc_rev] + 1 *)
      MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV)
        (ISPECL [`p:A prob_space`;
          `\x:A. &(num_upcrossings (\k. (X:num->A->real)(N - k)) a b N x)`;
          `\x:A. &1`] SIMPLE_EXPECTATION_ADD)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[SIMPLE_RV_CONST]; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th; SIMPLE_EXPECTATION_CONST]) THEN
      REAL_ARITH_TAC];
    (* (b-a)*(E[uc_rev] + 1) <= M + |a| + (b-a) *)
    REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC]);;

let DOWNCROSSING_PROB_BOUND = prove(
  `!(p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real)
    a b n M (k:num).
    simple_backward_martingale p FF X /\ a < b /\
    (!m x. x IN prob_carrier p ==> abs(X m x) <= M) /\ 0 < k
    ==> prob p {x | x IN prob_carrier p /\
          &(num_downcrossings X a b n x) >= &k}
        <= (M + abs a + (b - a)) / ((b - a) * &k)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space)
    (\x. &(num_downcrossings (X:num->A->real) a b n x)) / &k` THEN
  CONJ_TAC THENL [
    (* Markov inequality *)
    MATCH_MP_TAC MARKOV_INEQUALITY_SIMPLE THEN
    CONJ_TAC THENL [
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] SIMPLE_RV_NUM_DOWNCROSSINGS) THEN
      UNDISCH_TAC `simple_backward_martingale (p:A prob_space) FF X` THEN
      REWRITE_TAC[simple_backward_martingale] THEN MESON_TAC[];
      CONJ_TAC THENL [
        REWRITE_TAC[num_downcrossings] THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC[REAL_POS];
        ASM_REWRITE_TAC[REAL_OF_NUM_LT]]];
    (* E[dc]/k <= (M + |a| + (b-a)) / ((b-a) * k) *)
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [
      ALL_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_POS]] THEN
    (* E[dc] <= (M + |a| + (b-a)) * inv(b-a) *)
    MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                    `X:num->A->real`; `a:real`; `b:real`; `n:num`; `M:real`]
      BACKWARD_DOWNCROSSING_EXPECTATION_BOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC[GSYM real_div; GSYM REAL_LE_LDIV_EQ] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]]);;

let INFINITE_DOWNCROSSINGS_NULL = prove(
  `!(p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) a b M.
    simple_backward_martingale p FF X /\ a < b /\
    (!m x. x IN prob_carrier p ==> abs(X m x) <= M)
    ==> !k. 0 < k ==>
      prob p (UNIONS {
        {x | x IN prob_carrier p /\ &(num_downcrossings X a b n x) >= &k}
      | n IN (:num)}) <= (M + abs a + (b - a)) / ((b - a) * &k)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PROB_UNIONS_INCREASING_BOUND THEN
  SUBGOAL_THEN `!m:num. simple_rv (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL [
    UNDISCH_TAC `simple_backward_martingale (p:A prob_space) FF X` THEN
    REWRITE_TAC[simple_backward_martingale] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [
    (* A n IN events *)
    GEN_TAC THEN MATCH_MP_TAC SIMPLE_NUM_DOWNCROSSINGS_GE_EVENT THEN
    ASM_REWRITE_TAC[];
    (* A n SUBSET A (SUC n) *)
    X_GEN_TAC `nn:num` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge;
      REAL_OF_NUM_LE] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[NUM_DOWNCROSSINGS_MONO; LE_TRANS;
      ARITH_RULE `nn <= SUC nn`];
    (* P(A n) <= c *)
    X_GEN_TAC `nn:num` THEN
    MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                    `X:num->A->real`; `a:real`; `b:real`; `nn:num`;
                    `M:real`; `k:num`] DOWNCROSSING_PROB_BOUND) THEN
    DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* --- Backward simple_martingale convergence --- *)

let FINITE_DOWNCROSSINGS_AS = prove(
  `!(p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) a b M.
    simple_backward_martingale p FF X /\ a < b /\
    (!m x. x IN prob_carrier p ==> abs(X m x) <= M)
    ==> almost_surely p
          {x | ?B:num. !n. num_downcrossings X a b n x <= B}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[almost_surely] THEN
  SUBGOAL_THEN `!m:num. simple_rv (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL [
    UNDISCH_TAC `simple_backward_martingale (p:A prob_space) FF X` THEN
    REWRITE_TAC[simple_backward_martingale] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC
    `INTERS {UNIONS {
       {x:A | x IN prob_carrier p /\
              &(num_downcrossings (X:num->A->real) a b n x) >= &(SUC k)}
     | n IN (:num)} | k IN (:num)}` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[null_event] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN
    GEN_TAC THEN MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
    GEN_TAC THEN MATCH_MP_TAC SIMPLE_NUM_DOWNCROSSINGS_GE_EVENT THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_EQ_0_FROM_INV_BOUND THEN
    EXISTS_TAC `(M + abs(a:real) + (b - a)) / (b - a)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC PROB_POSITIVE THEN
     MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN
     GEN_TAC THEN MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
     GEN_TAC THEN MATCH_MP_TAC SIMPLE_NUM_DOWNCROSSINGS_GE_EVENT THEN
     ASM_REWRITE_TAC[];
     X_GEN_TAC `j:num` THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `prob (p:A prob_space) (UNIONS {
       {x:A | x IN prob_carrier p /\
              &(num_downcrossings (X:num->A->real) a b n x) >= &(SUC j)}
       | n IN (:num)})` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC PROB_MONO THEN REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN
       GEN_TAC THEN MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
       GEN_TAC THEN MATCH_MP_TAC SIMPLE_NUM_DOWNCROSSINGS_GE_EVENT THEN
       ASM_REWRITE_TAC[];
       MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
       GEN_TAC THEN MATCH_MP_TAC SIMPLE_NUM_DOWNCROSSINGS_GE_EVENT THEN
       ASM_REWRITE_TAC[];
       SET_TAC[]];
      SUBGOAL_THEN `(M + abs(a:real) + (b - a)) / (b - a) / &(SUC j) =
                     (M + abs a + (b - a)) / ((b - a) * &(SUC j))`
        SUBST1_TAC THENL
      [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC]; ALL_TAC] THEN
      MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                      `X:num->A->real`; `a:real`; `b:real`; `M:real`]
        INFINITE_DOWNCROSSINGS_NULL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `SUC j`) THEN
      REWRITE_TAC[LT_0]]]];
   REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERS] THEN
   X_GEN_TAC `x:A` THEN STRIP_TAC THEN
   GEN_TAC THEN REWRITE_TAC[SIMPLE_IMAGE; IN_IMAGE; IN_UNIV] THEN
   DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
   REWRITE_TAC[IN_UNIONS] THEN
   REWRITE_TAC[EXISTS_IN_IMAGE; IN_UNIV; IN_ELIM_THM;
               real_ge; REAL_OF_NUM_LE] THEN
   FIRST_X_ASSUM(MP_TAC o
     GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
   DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
   REWRITE_TAC[NOT_FORALL_THM; NOT_LE] THEN
   DISCH_THEN(X_CHOOSE_THEN `nn:num` ASSUME_TAC) THEN
   EXISTS_TAC `nn:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* Deterministic convergence from finite downcrossings *)

let BOUNDED_FINITE_DOWNCROSSINGS_IMP_CONVERGENT = prove(
  `!f M. (!n. abs(f n) <= M) /\
         (!a b. rational a /\ rational b /\ a < b
                ==> ?B. !n. downcrossing_count f a b n <= B)
         ==> ?L. (f ---> L) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n:num. --(f n:real)`; `M:real`]
    BOUNDED_FINITE_UPCROSSINGS_IMP_CONVERGENT) THEN
  ANTS_TAC THENL [
    CONJ_TAC THENL [
      GEN_TAC THEN REWRITE_TAC[REAL_ABS_NEG] THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`--b:real`; `--a:real`]) THEN
      ANTS_TAC THENL [
        ASM_SIMP_TAC[RATIONAL_NEG] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[DOWNCROSSING_COUNT_EQ_NEG; REAL_NEG_NEG]]];
    DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN
    EXISTS_TAC `--L:real` THEN
    MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV)
      (ISPECL [`sequentially`; `\n:num. --(f n:real)`; `L:real`]
        REALLIM_NEG)) THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG; ETA_AX]]);;

let SIMPLE_BACKWARD_MARTINGALE_CONVERGENCE_BOUNDED = prove(
  `!(p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) M.
    simple_backward_martingale p FF X /\
    (!m x. x IN prob_carrier p ==> abs(X m x) <= M)
    ==> almost_surely p
          {x | ?L. ((\n. X n x) ---> L) sequentially}`,
  REPEAT STRIP_TAC THEN
  MP_TAC RATIONAL_ENUMERATION THEN
  DISCH_THEN(X_CHOOSE_TAC `g:num->real`) THEN
  (* Step 1: For each k, the downcrossing bound property is a.s. *)
  SUBGOAL_THEN
    `!k. almost_surely (p:A prob_space)
       {x:A | (g:num->real)(NUMFST k) < g(NUMSND k) ==>
              (?B. !n. num_downcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)}`
    ASSUME_TAC THENL
  [X_GEN_TAC `k:num` THEN
   ASM_CASES_TAC `(g:num->real)(NUMFST k) < g(NUMSND k)` THENL
   [(* Case a < b: use FINITE_DOWNCROSSINGS_AS *)
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x:A | ?B. !n. num_downcrossings (X:num->A->real)
                  ((g:num->real)(NUMFST k)) (g(NUMSND k)) n x <= B}` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC FINITE_DOWNCROSSINGS_AS THEN
     MAP_EVERY EXISTS_TAC
       [`FF:num->(A->bool)->bool`; `M:real`] THEN
     ASM_REWRITE_TAC[];
     REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    (* Case a >= b: S_k = UNIV, trivially a.s. *)
    SUBGOAL_THEN
      `{x:A | (g:num->real)(NUMFST k) < g(NUMSND k) ==>
              (?B. !n. num_downcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)} = (:A)`
      (fun th -> REWRITE_TAC[th; ALMOST_SURELY_UNIV]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
    ASM_MESON_TAC[]];
   ALL_TAC] THEN
  (* Step 2+3: a.s. of intersection => convergence *)
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
    `INTERS {{x:A | (g:num->real)(NUMFST k) < g(NUMSND k) ==>
              (?B. !n. num_downcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)}
             | k IN (:num)}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN ASM_REWRITE_TAC[];
   (* Containment: INTERS membership => convergence *)
   REWRITE_TAC[IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[IN_INTERS] THEN DISCH_TAC THEN
   (* Extract: for all k, the downcrossing bound property holds *)
   SUBGOAL_THEN
     `!k. (g:num->real)(NUMFST k) < g(NUMSND k)
          ==> ?B. !n. num_downcrossings (X:num->A->real)
                        (g(NUMFST k)) (g(NUMSND k)) n x <= B`
     ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `{x:A | (g:num->real)(NUMFST (k:num)) < g(NUMSND k) ==>
              (?B. !n. num_downcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)}`) THEN
    ANTS_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
     EXISTS_TAC `k:num` THEN REFL_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   (* Apply BOUNDED_FINITE_DOWNCROSSINGS_IMP_CONVERGENT *)
   MP_TAC(ISPECL [`\n:num. (X:num->A->real) n x`; `M:real`]
     BOUNDED_FINITE_DOWNCROSSINGS_IMP_CONVERGENT) THEN
   REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    (* Find i,j with g(i) = a, g(j) = b *)
    SUBGOAL_THEN `?i:num. (g:num->real) i = a` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o SPEC `a:real` o
       GEN_REWRITE_RULE I [EXTENSION]) THEN
     REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
     ASM_REWRITE_TAC[IN] THEN MESON_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `?j:num. (g:num->real) j = b` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o SPEC `b:real` o
       GEN_REWRITE_RULE I [EXTENSION]) THEN
     REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
     ASM_REWRITE_TAC[IN] THEN MESON_TAC[];
     ALL_TAC] THEN
    (* Use k = NUMPAIR i j *)
    FIRST_X_ASSUM(MP_TAC o SPEC `NUMPAIR i j`) THEN
    REWRITE_TAC[NUMPAIR_DEST] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `B:num`) THEN
    EXISTS_TAC `B:num` THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[num_downcrossings];
    ALL_TAC] THEN
   REWRITE_TAC[]]);;

(* ========================================================================= *)
(* BACKWARD MARTINGALE CONVERGENCE: L^1-BOUNDED (GENERAL) CASE               *)
(* ========================================================================= *)

(* Generalize SIMPLE_REVERSED_IS_SUBMARTINGALE to backward_martingale => submartingale *)

let REVERSED_IS_SUBMARTINGALE = prove(
  `!p FF (X:num->A->real) N. backward_martingale p FF X
    ==> submartingale p (\k. FF(N - k)) (\k. X(N - k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[backward_martingale; submartingale] THEN
  STRIP_TAC THEN
  REPEAT CONJ_TAC THENL [
    REWRITE_TAC[filtration] THEN CONJ_TAC THENL [
      GEN_TAC THEN UNDISCH_TAC `decreasing_filtration (p:A prob_space) FF` THEN
      REWRITE_TAC[decreasing_filtration] THEN MESON_TAC[];
      REPEAT STRIP_TAC THEN
      UNDISCH_TAC `decreasing_filtration (p:A prob_space) FF` THEN
      REWRITE_TAC[decreasing_filtration] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    REWRITE_TAC[adapted] THEN GEN_TAC THEN
    UNDISCH_TAC `adapted (p:A prob_space) FF X` THEN
    REWRITE_TAC[adapted] THEN MESON_TAC[];
    ASM_MESON_TAC[];
    X_GEN_TAC `k:num` THEN X_GEN_TAC `a:A->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k < N:num` THENL [
      SUBGOAL_THEN `N - k = SUC(N - SUC k)` ASSUME_TAC THENL [
        ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
        `expectation p (\x. (X:num->A->real)(N - k) x * indicator_fn a x) =
         expectation p (\x. X(N - SUC k) x * indicator_fn a x)`
        (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`N - SUC k`; `a:A->bool`]) THEN
      SUBGOAL_THEN `SUC(N - SUC k) = N - k` (fun th -> REWRITE_TAC[th]) THENL [
        ASM_ARITH_TAC;
        ASM_SIMP_TAC[] THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `N - k = 0 /\ N - SUC k = 0`
        (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
      ASM_ARITH_TAC]]);;

(* Constant filtration is a filtration *)
let FILTRATION_CONST_EVENTS = prove(
  `!p:A prob_space. filtration p (\n:num. prob_events p)`,
  REWRITE_TAC[filtration; SUB_SIGMA_ALGEBRA_SELF; SUBSET_REFL]);;

(* Negation is adapted to prob_events for backward martingale *)
let ADAPTED_NEG_BACKWARD = prove(
  `!p:A prob_space FF (X:num->A->real).
    backward_martingale p FF X
    ==> adapted p (\n:num. prob_events p) (\n. \x. --(X n x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[backward_martingale] THEN STRIP_TAC THEN
  REWRITE_TAC[adapted; measurable_wrt] THEN
  X_GEN_TAC `n:num` THEN X_GEN_TAC `v:real` THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ --((X:num->A->real) n x) <= v} =
    {x | x IN prob_carrier p /\ X n x >= --v}` SUBST1_TAC THENL [
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; real_ge] THEN
    GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
  REWRITE_TAC[random_variable] THEN GEN_TAC THEN
  UNDISCH_TAC `adapted (p:A prob_space) FF X` THEN
  REWRITE_TAC[adapted; measurable_wrt] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real`) THEN
  UNDISCH_TAC `decreasing_filtration (p:A prob_space) FF` THEN
  REWRITE_TAC[decreasing_filtration; sub_sigma_algebra; SUBSET] THEN
  MESON_TAC[]);;

(* ========================================================================= *)
(* HELPER LEMMAS FOR DOOB DECOMPOSITION                                      *)
(* ========================================================================= *)


(* ========================================================================= *)
(* GENERAL CONDITIONAL EXPECTATION VIA RADON-NIKODYM                         *)
(* ========================================================================= *)

(* The current atom-based cond_exp requires FINITE G. This section defines
   gen_cond_exp for arbitrary sub-sigma-algebras using the Radon-Nikodym
   theorem applied to a restricted probability space. *)

(* --- Step 1: Restricted probability space construction --- *)

(* Verify the prob_space predicate for (G, prob p) *)
let SUB_SIGMA_ALGEBRA_PRED = prove
 (`!p:A prob_space G. sub_sigma_algebra p G ==>
    sigma_algebra G /\
    (!a. a IN G ==> &0 <= prob p a) /\
    prob p (UNIONS G) = &1 /\
    prob p {} = &0 /\
    (!A. (!n. A n IN G) /\ (!i j. ~(i = j) ==> DISJOINT (A i) (A j))
         ==> ((\n. prob p (A n)) real_sums
              prob p (UNIONS {A n | n IN (:num)})) (from 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sub_sigma_algebra] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC PROB_POSITIVE THEN ASM SET_TAC[];
   ASM_REWRITE_TAC[GSYM prob_carrier; PROB_SPACE];
   REWRITE_TAC[PROB_EMPTY];
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC PROB_COUNTABLY_ADDITIVE THEN
   CONJ_TAC THENL
   [GEN_TAC THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[]]]);;

(* Restricted probability space: replace events with sub-sigma-algebra G,
   keeping the same probability measure *)
let restrict_prob_space = new_definition
  `restrict_prob_space (p:A prob_space) (G:(A->bool)->bool) =
   prob_space(G:(A->bool)->bool, prob p)`;;

(* The type bijection gives us that prob_space_operations inverts *)
let RESTRICT_PROB_SPACE_OPS = prove
 (`!p:A prob_space G. sub_sigma_algebra p G ==>
    prob_space_operations (restrict_prob_space p G) = (G, prob p)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[restrict_prob_space] THEN
  MP_TAC(ISPEC `(G:(A->bool)->bool, prob (p:A prob_space))`
    (CONJUNCT2 prob_space_tybij)) THEN
  REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  MATCH_MP_TAC SUB_SIGMA_ALGEBRA_PRED THEN ASM_REWRITE_TAC[]);;

(* Extract individual properties *)
let RESTRICT_PROB_SPACE_EVENTS = prove
 (`!p:A prob_space G. sub_sigma_algebra p G ==>
    prob_events (restrict_prob_space p G) = G`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[prob_events] THEN
  ASM_SIMP_TAC[RESTRICT_PROB_SPACE_OPS; FST]);;

let RESTRICT_PROB_SPACE_PROB = prove
 (`!p:A prob_space G. sub_sigma_algebra p G ==>
    prob (restrict_prob_space p G) = prob p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[prob] THEN
  ASM_SIMP_TAC[RESTRICT_PROB_SPACE_OPS; SND] THEN
  REWRITE_TAC[GSYM prob]);;

let RESTRICT_PROB_SPACE_CARRIER = prove
 (`!p:A prob_space G. sub_sigma_algebra p G ==>
    prob_carrier (restrict_prob_space p G) = prob_carrier p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[prob_carrier] THEN
  ASM_SIMP_TAC[RESTRICT_PROB_SPACE_EVENTS] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [sub_sigma_algebra]) THEN
  REWRITE_TAC[prob_carrier] THEN SIMP_TAC[]);;

(* --- Step 2: Simple function transfer --- *)

(* simple_expectation depends only on prob_carrier and prob, so it agrees *)
let SIMPLE_EXPECTATION_RESTRICT = prove
 (`!p:A prob_space G (g:A->real). sub_sigma_algebra p G ==>
    simple_expectation (restrict_prob_space p G) g = simple_expectation p g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simple_expectation] THEN
  ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER; RESTRICT_PROB_SPACE_PROB]);;

(* Helper: if s IN G and G SUBSET H then s IN H *)
let IN_SUBSET_TRANSFER = MESON[SUBSET]
  `!s:A->bool G H. s IN G /\ G SUBSET H ==> s IN H`;;

(* Helper: G SUBSET prob_events p from sub_sigma_algebra *)
let SUB_SIGMA_ALGEBRA_SUBSET = prove
 (`!p:A prob_space G. sub_sigma_algebra p G ==>
    G SUBSET prob_events p`,
  REWRITE_TAC[sub_sigma_algebra] THEN MESON_TAC[]);;

(* simple_rv on restricted space implies simple_rv on original space *)
let SIMPLE_RV_RESTRICT_FORWARD = prove
 (`!p:A prob_space G (g:A->real).
    sub_sigma_algebra p G /\ simple_rv (restrict_prob_space p G) g
    ==> simple_rv p g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simple_rv; random_variable] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `prob_carrier (restrict_prob_space (p:A prob_space) G) =
                prob_carrier p` ASSUME_TAC THENL
  [ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN `prob_events (restrict_prob_space (p:A prob_space) G) = G`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[RESTRICT_PROB_SPACE_EVENTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(G:(A->bool)->bool) SUBSET prob_events p` ASSUME_TAC THENL
  [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC IN_SUBSET_TRANSFER THEN
   EXISTS_TAC `G:(A->bool)->bool` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a:real`) THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]];
   SUBGOAL_THEN `{(g:A->real) x | x IN prob_carrier p} =
                 {g x | x IN prob_carrier (restrict_prob_space (p:A prob_space) G)}`
     (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER]; ASM_REWRITE_TAC[]]]);;

(* random_variable on restricted space implies random_variable on original *)
let RANDOM_VARIABLE_RESTRICT_FORWARD = prove
 (`!p:A prob_space G (f:A->real).
    sub_sigma_algebra p G /\ random_variable (restrict_prob_space p G) f
    ==> random_variable p f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[random_variable] THEN
  STRIP_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN `prob_carrier (restrict_prob_space (p:A prob_space) G) =
                prob_carrier p` ASSUME_TAC THENL
  [ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN `prob_events (restrict_prob_space (p:A prob_space) G) = G`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[RESTRICT_PROB_SPACE_EVENTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(G:(A->bool)->bool) SUBSET prob_events p` ASSUME_TAC THENL
  [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC IN_SUBSET_TRANSFER THEN
  EXISTS_TAC `G:(A->bool)->bool` THEN CONJ_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `a:real`) THEN ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[]]);;

(* nonneg_simple_fn_approx is the same on both spaces *)
let NONNEG_SIMPLE_FN_APPROX_RESTRICT = prove
 (`!p:A prob_space G f n x. sub_sigma_algebra p G ==>
    nonneg_simple_fn_approx (restrict_prob_space p G) f n x =
    nonneg_simple_fn_approx p f n x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nonneg_simple_fn_approx] THEN
  ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER]);;

(* --- Step 3: nn_expectation transfer (bounded case) --- *)

(* Key lemma: nn_expectation agrees for bounded nonneg G-measurable functions *)
let NN_EXPECTATION_RESTRICT_BOUNDED = prove
 (`!p:A prob_space G (f:A->real) M.
    sub_sigma_algebra p G /\
    random_variable (restrict_prob_space p G) f /\
    (!x. x IN prob_carrier p ==> &0 <= f x) /\
    (!x. x IN prob_carrier p ==> f x <= M) /\
    &0 <= M
    ==> nn_expectation (restrict_prob_space p G) f = nn_expectation p f`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b /\ b <= a ==> a = b`) THEN CONJ_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_LE_FROM_SIMPLE THEN
   ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER] THEN
   X_GEN_TAC `h:A->real` THEN STRIP_TAC THEN
   ASM_SIMP_TAC[SIMPLE_EXPECTATION_RESTRICT] THEN
   MATCH_MP_TAC BOUNDED_NN_EXPECTATION_GE_SIMPLE THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_RESTRICT_FORWARD THEN
    EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER] THEN
   EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
   EXISTS_TAC
     `\n. simple_expectation p
            (nonneg_simple_fn_approx p (f:A->real) n)` THEN
   REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_MCT_NN_EXPECTATION THEN
    SUBGOAL_THEN `random_variable p (f:A->real)` ASSUME_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_RESTRICT_FORWARD THEN
     EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN
     ASM_REWRITE_TAC[];
     GEN_TAC THEN REWRITE_TAC[NONNEG_SIMPLE_FN_APPROX_NONNEG];
     REPEAT STRIP_TAC THEN MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_MONO THEN
     ASM_SIMP_TAC[ARITH_RULE `n <= SUC n`];
     ASM_SIMP_TAC[NONNEG_SIMPLE_FN_APPROX_CONVERGES];
     EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM SIMPLE_EXPECTATION_RESTRICT] THEN
    SUBGOAL_THEN
      `nonneg_simple_fn_approx p (f:A->real) n =
       nonneg_simple_fn_approx (restrict_prob_space p G) f n`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN
     GEN_TAC THEN MATCH_MP_TAC(GSYM NONNEG_SIMPLE_FN_APPROX_RESTRICT) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    MATCH_MP_TAC BOUNDED_NN_EXPECTATION_GE_SIMPLE THEN
    ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER] THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_SIMPLE_RV THEN
     ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER];
     REWRITE_TAC[NONNEG_SIMPLE_FN_APPROX_NONNEG];
     GEN_TAC THEN DISCH_TAC THEN
     MATCH_MP_TAC NONNEG_SIMPLE_FN_APPROX_LE THEN
     ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER];
     EXISTS_TAC `M:real` THEN
     ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER]]]]);;

(* --- Step 4: Integrability and expectation transfer --- *)

(* Integrability transfers from restricted to original space *)
let INTEGRABLE_RESTRICT_IMP = prove
 (`!p:A prob_space G (f:A->real).
    sub_sigma_algebra p G /\
    integrable (restrict_prob_space p G) f
    ==> integrable p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[integrable] THEN CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_RESTRICT_FORWARD THEN
   EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[integrable]) THEN
  ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER; SIMPLE_EXPECTATION_RESTRICT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `B:real` THEN
  X_GEN_TAC `g:A->real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?Bg. !x:A. x IN prob_carrier p ==> (g:A->real) x <= Bg`
    STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_BOUNDED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `nn_expectation (restrict_prob_space (p:A prob_space) G)
    (\x:A. min (abs ((f:A->real) x)) (max (Bg:real) (&0)))` THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN
     `nn_expectation (restrict_prob_space (p:A prob_space) G)
       (\x:A. min (abs ((f:A->real) x)) (max Bg (&0))) =
      nn_expectation p (\x. min (abs (f x)) (max Bg (&0)))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC NN_EXPECTATION_RESTRICT_BOUNDED THEN
    EXISTS_TAC `max Bg (&0)` THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 <= max x (&0)`] THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[RANDOM_VARIABLE_CONST]];
     GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
     GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   MATCH_MP_TAC BOUNDED_NN_EXPECTATION_GE_SIMPLE THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:A->real) y <= abs((f:A->real) y)` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(g:A->real) y <= Bg` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    EXISTS_TAC `max Bg (&0)` THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    REAL_ARITH_TAC];
   MATCH_MP_TAC(ISPEC `restrict_prob_space (p:A prob_space) G`
     NN_EXPECTATION_LE_FROM_SIMPLE) THEN
   ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    X_GEN_TAC `h:A->real` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SIMPLE_EXPECTATION_RESTRICT] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:A->real) y <= min (abs((f:A->real) y)) (max Bg (&0))`
      MP_TAC THENL
    [ASM_MESON_TAC[]; REAL_ARITH_TAC]]]);;

(* nn_expectation agrees for general nonneg G-measurable integrable functions *)
let NN_EXPECTATION_RESTRICT = prove
 (`!p:A prob_space G (f:A->real).
    sub_sigma_algebra p G /\
    random_variable (restrict_prob_space p G) f /\
    (!x. x IN prob_carrier p ==> &0 <= f x) /\
    integrable (restrict_prob_space p G) f
    ==> nn_expectation (restrict_prob_space p G) f = nn_expectation p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (f:A->real)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_RESTRICT_IMP THEN
   EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b /\ b <= a ==> a = b`) THEN CONJ_TAC THENL
  [(* Direction 1: restrict <= original *)
   MATCH_MP_TAC(ISPEC `restrict_prob_space (p:A prob_space) G`
     NN_EXPECTATION_LE_FROM_SIMPLE) THEN
   ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER] THEN
   X_GEN_TAC `h:A->real` THEN STRIP_TAC THEN
   ASM_SIMP_TAC[SIMPLE_EXPECTATION_RESTRICT] THEN
   SUBGOAL_THEN `simple_rv p (h:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_RESTRICT_FORWARD THEN
    EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `?K. !x:A. x IN prob_carrier p ==> (h:A->real) x <= K`
     STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_BOUNDED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `nn_expectation (p:A prob_space)
     (\x:A. min ((f:A->real) x) (max K (&0)))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_NN_EXPECTATION_GE_SIMPLE THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
     SUBGOAL_THEN `(h:A->real) y <= (f:A->real) y` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `(h:A->real) y <= K` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
     ASM_REAL_ARITH_TAC;
     EXISTS_TAC `max K (&0)` THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
     REAL_ARITH_TAC];
    MATCH_MP_TAC NN_EXPECTATION_MONO THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
    [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
     SUBGOAL_THEN `&0 <= (f:A->real) y` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
     X_GEN_TAC `y:A` THEN DISCH_TAC THEN REAL_ARITH_TAC]];
   (* Direction 2: original <= restrict *)
   MATCH_MP_TAC NN_EXPECTATION_LE_FROM_SIMPLE THEN
   ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `h:A->real` THEN STRIP_TAC THEN
   SUBGOAL_THEN `?K. !x:A. x IN prob_carrier p ==> (h:A->real) x <= K`
     STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_BOUNDED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `nn_expectation (p:A prob_space)
     (\x:A. min ((f:A->real) x) (max K (&0)))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_NN_EXPECTATION_GE_SIMPLE THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
     SUBGOAL_THEN `(h:A->real) y <= (f:A->real) y` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `(h:A->real) y <= K` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
     ASM_REAL_ARITH_TAC;
     EXISTS_TAC `max K (&0)` THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
     REAL_ARITH_TAC];
    SUBGOAL_THEN
      `nn_expectation (p:A prob_space) (\x:A. min ((f:A->real) x) (max K (&0))) =
       nn_expectation (restrict_prob_space p G) (\x. min (f x) (max K (&0)))`
      SUBST1_TAC THENL
    [MATCH_MP_TAC(GSYM NN_EXPECTATION_RESTRICT_BOUNDED) THEN
     EXISTS_TAC `max K (&0)` THEN
     ASM_REWRITE_TAC[REAL_ARITH `&0 <= max x (&0)`] THEN
     REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN CONJ_TAC THENL
      [ASM_REWRITE_TAC[]; REWRITE_TAC[RANDOM_VARIABLE_CONST]];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= (f:A->real) y` ASSUME_TAC THENL
      [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN REAL_ARITH_TAC];
     MATCH_MP_TAC(ISPEC `restrict_prob_space (p:A prob_space) G`
       NN_EXPECTATION_MONO) THEN
     ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER] THEN
     REPEAT CONJ_TAC THENL
     [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= (f:A->real) y` ASSUME_TAC THENL
      [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN REAL_ARITH_TAC]]]]);;

(* Expectation agrees for integrable G-measurable functions *)
let EXPECTATION_RESTRICT = prove
 (`!p:A prob_space G (f:A->real).
    sub_sigma_algebra p G /\
    integrable (restrict_prob_space p G) f
    ==> expectation (restrict_prob_space p G) f = expectation p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[expectation] THEN
  SUBGOAL_THEN
    `random_variable (restrict_prob_space (p:A prob_space) G) (f:A->real)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `nn_expectation (restrict_prob_space (p:A prob_space) G)
       (\x:A. max ((f:A->real) x) (&0)) =
     nn_expectation p (\x. max (f x) (&0))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_RESTRICT THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[]; REWRITE_TAC[RANDOM_VARIABLE_CONST]];
    ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER] THEN
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC INTEGRABLE_POS_PART THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `nn_expectation (restrict_prob_space (p:A prob_space) G)
       (\x:A. max (--((f:A->real) x)) (&0)) =
     nn_expectation p (\x. max (--f x) (&0))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC NN_EXPECTATION_RESTRICT THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[RANDOM_VARIABLE_CONST]];
    ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER] THEN
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC INTEGRABLE_NEG_PART THEN ASM_REWRITE_TAC[]];
   REWRITE_TAC[]]);;

(* --- Step 5: General conditional expectation definition --- *)

let gen_cond_exp = new_definition
  `gen_cond_exp (p:A prob_space) (G:(A->bool)->bool) (X:A->real) =
   @f. measurable_wrt p G f /\ integrable p f /\
       (!A. A IN G ==>
         expectation p (\x. f x * indicator_fn A x) =
         expectation p (\x. X x * indicator_fn A x))`;;

(* --- Step 6: Existence of gen_cond_exp --- *)

(* Helper: absolutely_continuous transfers from p to restricted space *)
let ABSOLUTELY_CONTINUOUS_RESTRICT = prove
 (`!p:A prob_space G mu.
    sub_sigma_algebra p G /\ absolutely_continuous p mu
    ==> absolutely_continuous (restrict_prob_space p G) mu`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[absolutely_continuous] THEN
  ASM_SIMP_TAC[RESTRICT_PROB_SPACE_EVENTS; RESTRICT_PROB_SPACE_PROB] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[signed_measure] THEN
   ASM_SIMP_TAC[RESTRICT_PROB_SPACE_EVENTS] THEN
   FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[absolutely_continuous]) THEN
   DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) THEN
   REWRITE_TAC[signed_measure] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `A:num->A->bool` THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `A:num->A->bool`) THEN
   SUBGOAL_THEN `(G:(A->bool)->bool) SUBSET prob_events p` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ASM_REWRITE_TAC[]];
    REWRITE_TAC[]];
   FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[absolutely_continuous]) THEN
   STRIP_TAC THEN
   REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `(G:(A->bool)->bool) SUBSET prob_events p` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_SUBSET THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[SUBSET]]]);;

(* Existence of gen_cond_exp via Radon-Nikodym on restricted space *)
let GEN_COND_EXP_EXISTS = prove
 (`!p:A prob_space G (X:A->real).
    sub_sigma_algebra p G /\ integrable p X
    ==> ?f. measurable_wrt p G f /\ integrable p f /\
            (!A. A IN G ==>
              expectation p (\x. f x * indicator_fn A x) =
              expectation p (\x. X x * indicator_fn A x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `absolutely_continuous (restrict_prob_space (p:A prob_space) G)
      (\A. expectation p (\x. (X:A->real) x * indicator_fn A x))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC ABSOLUTELY_CONTINUOUS_RESTRICT THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC ABSOLUTELY_CONTINUOUS_FROM_INTEGRAL THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL
    [`restrict_prob_space (p:A prob_space) G`;
     `\A. expectation (p:A prob_space) (\x. (X:A->real) x * indicator_fn A x)`]
    RADON_NIKODYM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:A->real` THEN
  ASM_SIMP_TAC[RESTRICT_PROB_SPACE_EVENTS] THEN
  REPEAT CONJ_TAC THENL
  [(* measurable_wrt p G f *)
   REWRITE_TAC[measurable_wrt] THEN GEN_TAC THEN
   SUBGOAL_THEN
     `random_variable (restrict_prob_space (p:A prob_space) G) (f:A->real)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[random_variable]) THEN
   DISCH_THEN(MP_TAC o SPEC `v:real`) THEN
   ASM_SIMP_TAC[RESTRICT_PROB_SPACE_CARRIER; RESTRICT_PROB_SPACE_EVENTS];
   (* integrable p f *)
   MATCH_MP_TAC INTEGRABLE_RESTRICT_IMP THEN
   EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[];
   (* conditioning property *)
   X_GEN_TAC `A:A->bool` THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space) (\x. (f:A->real) x * indicator_fn A x) =
      expectation (restrict_prob_space p G) (\x. f x * indicator_fn A x)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM EXPECTATION_RESTRICT) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPEC `restrict_prob_space (p:A prob_space) G`
      INTEGRABLE_MUL_INDICATOR_FN) THEN
    ASM_SIMP_TAC[RESTRICT_PROB_SPACE_EVENTS];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[RESTRICT_PROB_SPACE_EVENTS]]]);;

(* --- Step 7: Key properties --- *)

let GEN_COND_EXP_CONDITIONING = prove
 (`!p:A prob_space G (X:A->real) (A:A->bool).
    sub_sigma_algebra p G /\ integrable p X /\ A IN G
    ==> expectation p (\x. gen_cond_exp p G X x * indicator_fn A x) =
        expectation p (\x. X x * indicator_fn A x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?f:A->real. measurable_wrt p G f /\ integrable p f /\
       (!A. A IN G ==>
         expectation p (\x. f x * indicator_fn A x) =
         expectation p (\x. (X:A->real) x * indicator_fn A x))`
    MP_TAC THENL
  [MATCH_MP_TAC GEN_COND_EXP_EXISTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MP_TAC(REWRITE_RULE[GSYM gen_cond_exp] (SELECT_RULE th))) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

let GEN_COND_EXP_MEASURABLE_WRT = prove
 (`!p:A prob_space G (X:A->real).
    sub_sigma_algebra p G /\ integrable p X
    ==> measurable_wrt p G (gen_cond_exp p G X)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?f:A->real. measurable_wrt p G f /\ integrable p f /\
       (!A. A IN G ==>
         expectation p (\x. f x * indicator_fn A x) =
         expectation p (\x. (X:A->real) x * indicator_fn A x))`
    MP_TAC THENL
  [MATCH_MP_TAC GEN_COND_EXP_EXISTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MP_TAC(REWRITE_RULE[GSYM gen_cond_exp] (SELECT_RULE th))) THEN
  SIMP_TAC[]);;

let GEN_COND_EXP_INTEGRABLE = prove
 (`!p:A prob_space G (X:A->real).
    sub_sigma_algebra p G /\ integrable p X
    ==> integrable p (gen_cond_exp p G X)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `?f:A->real. measurable_wrt p G f /\ integrable p f /\
       (!A. A IN G ==>
         expectation p (\x. f x * indicator_fn A x) =
         expectation p (\x. (X:A->real) x * indicator_fn A x))`
    MP_TAC THENL
  [MATCH_MP_TAC GEN_COND_EXP_EXISTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MP_TAC(REWRITE_RULE[GSYM gen_cond_exp] (SELECT_RULE th))) THEN
  SIMP_TAC[]);;

let GEN_COND_EXP_TOWER = prove
 (`!p:A prob_space G (X:A->real).
    sub_sigma_algebra p G /\ integrable p X
    ==> expectation p (gen_cond_exp p G X) = expectation p X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `prob_carrier (p:A prob_space) IN G` ASSUME_TAC THENL
  [SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` MP_TAC THENL
   [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
   REWRITE_TAC[sigma_algebra] THEN STRIP_TAC THEN
   SUBGOAL_THEN `UNIONS (G:(A->bool)->bool) = prob_carrier (p:A prob_space)`
     MP_TAC THENL
   [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
   DISCH_THEN(SUBST1_TAC o GSYM) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `expectation (p:A prob_space) (gen_cond_exp p G X) =
     expectation p (\x. gen_cond_exp p G X x *
       indicator_fn (prob_carrier p) x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC(GSYM EXPECTATION_EXT) THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[indicator_fn] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `expectation (p:A prob_space) (X:A->real) =
     expectation p (\x. X x * indicator_fn (prob_carrier p) x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC(GSYM EXPECTATION_EXT) THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[indicator_fn] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[]);;


(* --- Step 8: Additional gen_cond_exp properties --- *)

(* Doob martingale: conditional expectations form a martingale *)
let GEN_DOOB_MARTINGALE = prove
 (`!p:A prob_space FF (X:A->real).
    filtration p FF /\ integrable p X
    ==> martingale p FF (\n. gen_cond_exp p (FF n) X)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[martingale; adapted] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [(* measurable_wrt *)
   GEN_TAC THEN MATCH_MP_TAC GEN_COND_EXP_MEASURABLE_WRT THEN
   ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
   REWRITE_TAC[filtration] THEN MESON_TAC[];
   (* integrable *)
   GEN_TAC THEN MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN
   ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
   REWRITE_TAC[filtration] THEN MESON_TAC[];
   (* martingale property *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `expectation p (\x:A. gen_cond_exp p (FF (SUC n)) (X:A->real) x *
        indicator_fn a x) =
      expectation p (\x. X x * indicator_fn a x)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
    [UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
     REWRITE_TAC[filtration] THEN MESON_TAC[];
     UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
     REWRITE_TAC[filtration] THEN STRIP_TAC THEN
     SUBGOAL_THEN `(FF:num->(A->bool)->bool) n SUBSET FF (SUC n)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      ASM_MESON_TAC[SUBSET]]];
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
    REWRITE_TAC[filtration] THEN MESON_TAC[]]]);;

(* {x | carrier /\ X x < v} IN G for G-measurable X *)
let MEASURABLE_WRT_STRICT_LT = prove
 (`!p:A prob_space G (X:A->real) v.
     sub_sigma_algebra p G /\ measurable_wrt p G X
     ==> {x | x IN prob_carrier p /\ X x < v} IN G`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ISPECL [`X:A->real`; `v:real`; `prob_carrier (p:A prob_space)`]
    OPEN_HALFLINE_AS_UNION] THEN
  MATCH_MP_TAC SIGMA_ALGEBRA_UNION_COUNTABLE THEN
  CONJ_TAC THENL [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `s:A->bool` THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
   ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `measurable_wrt (p:A prob_space) G X` THEN
   REWRITE_TAC[measurable_wrt] THEN
   DISCH_THEN(MP_TAC o SPEC `v - inv(&n + &1)`) THEN
   MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM];
   REWRITE_TAC[SIMPLE_IMAGE] THEN
   MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]]);;

(* A level set {X = v} of a G-measurable function is in G.                    *)
(* Relocated here (from characteristic_functions.ml) so the general take-out  *)
(* lemmas below can use it.                                                    *)
let MEASURABLE_WRT_LEVEL_SET = prove
 (`!p:A prob_space G (X:A->real) v.
     sub_sigma_algebra p G /\ measurable_wrt p G X
     ==> {x | x IN prob_carrier p /\ X x = v} IN G`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (X:A->real) x = v} =
     {x | x IN prob_carrier p /\ X x <= v} DIFF
     {x | x IN prob_carrier p /\ X x < v}`
    SUBST1_TAC THENL
  [SET_TAC[REAL_ARITH `!x v:real. x = v <=> x <= v /\ ~(x < v)`];
   ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `p:A prob_space` SUB_SIGMA_ALGEBRA_DIFF) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [ASM_MESON_TAC[measurable_wrt];
   MATCH_MP_TAC MEASURABLE_WRT_STRICT_LT THEN ASM_REWRITE_TAC[]]);;

(* Simple random variables are bounded on the carrier.  Relocated here (from   *)
(* clt.ml) so the simple-multiplier take-out below can use it.                  *)
let SIMPLE_RV_ABS_BOUNDED = prove
 (`!p:A prob_space f. simple_rv p f ==>
   ?M. !x. x IN prob_carrier p ==> abs(f x) <= M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simple_rv] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `p:A prob_space` PROB_CARRIER_NONEMPTY) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE {abs((f:A->real) x) | x IN prob_carrier (p:A prob_space)}`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `{abs((f:A->real) x) | x IN prob_carrier (p:A prob_space)} =
    IMAGE abs {f x | x IN prob_carrier p}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN
    `~({abs((f:A->real) x) | x IN prob_carrier (p:A prob_space)} = {})`
    ASSUME_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   EXISTS_TAC `abs((f:A->real) z)` THEN EXISTS_TAC `z:A` THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC
    `{abs((f:A->real) x) | x IN prob_carrier (p:A prob_space)}` SUP_FINITE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC
    `sup {abs((f:A->real) x) | x IN prob_carrier (p:A prob_space)}` THEN
  X_GEN_TAC `w:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `w:A` THEN ASM_REWRITE_TAC[]);;

(* A simple RV is its level-set expansion: X x = sum over the (finite) range of *)
(* u * indicator{X = u} x.  Used to reduce simple-multiplier take-out to the    *)
(* indicator take-out, summed over the range.                                   *)
let SIMPLE_RV_SUM_INDICATOR = prove
 (`!p:A prob_space (X:A->real) x. simple_rv p X /\ x IN prob_carrier p
   ==> X x = sum (IMAGE X (prob_carrier p))
                 (\u. u * indicator_fn {z | z IN prob_carrier p /\ X z = u} x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (IMAGE (X:A->real) (prob_carrier p))` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  SUBGOAL_THEN `(X:A->real) x IN IMAGE X (prob_carrier p)` ASSUME_TAC THENL
  [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (IMAGE (X:A->real) (prob_carrier p))
                  (\u. if u = X x then X x else &0)` THEN
  CONJ_TAC THENL
  [CONV_TAC SYM_CONV THEN REWRITE_TAC[SUM_DELTA] THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   BETA_TAC THEN REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
   ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `(X:A->real) x = u` THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `~(u = (X:A->real) x)` (fun th -> REWRITE_TAC[th]) THENL
    [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]]);;

(* Expectation/integrability of a finite SET sum (the library versions are     *)
(* numseg-indexed); used for the simple-multiplier take-out below.             *)
let INTEGRABLE_SUM_FINITE = prove
 (`!p:A prob_space (f:B->A->real) s.
     FINITE s /\ (!i. i IN s ==> integrable p (f i))
     ==> integrable p (\x. sum s (\i. f i x))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
  [REWRITE_TAC[SUM_CLAUSES; INTEGRABLE_CONST];
   MAP_EVERY X_GEN_TAC [`a:B`; `t:B->bool`] THEN STRIP_TAC THEN DISCH_TAC THEN
   ASM_SIMP_TAC[SUM_CLAUSES] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(f:B->A->real) a`;
                  `\x:A. sum t (\i. (f:B->A->real) i x)`] INTEGRABLE_ADD) THEN
   ASM_SIMP_TAC[IN_INSERT] THEN DISCH_THEN MATCH_MP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[IN_INSERT]]);;

let EXPECTATION_SUM_FINITE = prove
 (`!p:A prob_space (f:B->A->real) s.
     FINITE s /\ (!i. i IN s ==> integrable p (f i))
     ==> expectation p (\x. sum s (\i. f i x)) =
         sum s (\i. expectation p (f i))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
  [REWRITE_TAC[SUM_CLAUSES; EXPECTATION_CONST];
   MAP_EVERY X_GEN_TAC [`a:B`; `t:B->bool`] THEN STRIP_TAC THEN DISCH_TAC THEN
   ASM_SIMP_TAC[SUM_CLAUSES] THEN
   SUBGOAL_THEN `integrable p ((f:B->A->real) a)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
   SUBGOAL_THEN `!i. i IN (t:B->bool) ==> integrable p ((f:B->A->real) i)`
     ASSUME_TAC THENL [ASM_SIMP_TAC[IN_INSERT]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. sum t (\i. (f:B->A->real) i x))` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUM_FINITE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(f:B->A->real) a`;
                  `\x:A. sum t (\i. (f:B->A->real) i x)`] EXPECTATION_ADD) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]]);;

(* Pointwise level-set expansion of (Y x * Z x) * 1_A' for simple Y.          *)
let TO_POINTWISE = prove
 (`!p:A prob_space Y Z A' x.
     simple_rv p Y /\ x IN prob_carrier p
     ==> (Y x * Z x) * indicator_fn A' x =
         sum (IMAGE Y (prob_carrier p))
           (\u. u * Z x * indicator_fn
                  ({z | z IN prob_carrier p /\ Y z = u} INTER A') x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[INDICATOR_FN_INTER] THEN
  REWRITE_TAC[REAL_RING
    `!u zx iy ia:real. u * zx * iy * ia = (u * iy) * (zx * ia)`] THEN
  REWRITE_TAC[SUM_RMUL] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `Y:A->real`; `x:A`] SIMPLE_RV_SUM_INDICATOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC REAL_RING);;

(* E[Y*Z*1_A'] decomposed over the level sets of a simple Y.                   *)
let EXP_SIMPLE_MUL_DECOMP = prove
 (`!p:A prob_space Y Z A'.
     simple_rv p Y /\ integrable p Z /\
     A' IN prob_events p /\ integrable p (\w. Y w * Z w)
     ==> expectation p (\x. (Y x * Z x) * indicator_fn A' x) =
         sum (IMAGE Y (prob_carrier p))
             (\u. u * expectation p
                    (\x. Z x * indicator_fn
                           ({z | z IN prob_carrier p /\ Y z = u} INTER A') x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (IMAGE (Y:A->real) (prob_carrier p))` ASSUME_TAC THENL
  [ASM_MESON_TAC[simple_rv; SIMPLE_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!u. {z:A | z IN prob_carrier p /\ (Y:A->real) z = u} INTER A' IN prob_events p`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC RANDOM_VARIABLE_LEVEL_SET THEN ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  SUBGOAL_THEN
    `expectation p (\x. ((Y:A->real) x * Z x) * indicator_fn (A':A->bool) x) =
     expectation p (\x. sum (IMAGE Y (prob_carrier p))
        (\u. u * (Z x * indicator_fn
               ({z | z IN prob_carrier p /\ Y z = u} INTER A') x)))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `Y:A->real`; `Z:A->real`; `A':A->bool`; `x:A`]
     TO_POINTWISE) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ THEN
   X_GEN_TAC `u:real` THEN DISCH_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`p:A prob_space`;
     `\u:real. \x:A. u * (Z x * indicator_fn
        ({z | z IN prob_carrier p /\ (Y:A->real) z = u} INTER A') x)`;
     `IMAGE (Y:A->real) (prob_carrier p)`] EXPECTATION_SUM_FINITE) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   MATCH_MP_TAC INTEGRABLE_CMUL_ALT THEN
   MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_SIMP_TAC[];
   DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC EXPECTATION_CMUL THEN
  MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_SIMP_TAC[]);;

(* --- Measurability helpers for general (non-simple) functions --- *)

(* Negation preserves G-measurability *)
let MEASURABLE_WRT_NEG = prove
 (`!p:A prob_space G (f:A->real).
     sub_sigma_algebra p G /\ measurable_wrt p G f
     ==> measurable_wrt p G (\x. --f x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[measurable_wrt] THEN
  X_GEN_TAC `v:real` THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ --f x <= v} =
     prob_carrier p DIFF {x | x IN prob_carrier p /\ f x < --v}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN
   X_GEN_TAC `w:A` THEN
   ASM_CASES_TAC `(w:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC;
   MATCH_MP_TAC SUB_SIGMA_ALGEBRA_COMPL THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MEASURABLE_WRT_STRICT_LT THEN ASM_REWRITE_TAC[]]);;

(* Scalar multiplication preserves G-measurability *)
let MEASURABLE_WRT_CMUL = prove
 (`!p:A prob_space G (f:A->real) c.
     sub_sigma_algebra p G /\ measurable_wrt p G f
     ==> measurable_wrt p G (\x. c * f x)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `c = &0` THENL
  [ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
   MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_CASES_TAC `c > &0` THENL
  [REWRITE_TAC[measurable_wrt] THEN X_GEN_TAC `v:real` THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ c * f x <= v} =
      {x | x IN prob_carrier p /\ f x <= v / c}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `w:A` THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`(f:A->real) w`; `v:real`; `c:real`] REAL_LE_RDIV_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[REAL_MUL_SYM];
    UNDISCH_TAC `measurable_wrt (p:A prob_space) G f` THEN
    REWRITE_TAC[measurable_wrt] THEN MESON_TAC[]];
   (* c < 0: c * f = --(--c * f) where --c > 0 *)
   SUBGOAL_THEN `c < &0` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `!x:A. c * (f:A->real) x = --(--c * f x)`
     (fun th -> REWRITE_TAC[FUN_EQ_THM; th]) THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_MUL_LNEG; REAL_NEG_NEG]; ALL_TAC] THEN
   MATCH_MP_TAC MEASURABLE_WRT_NEG THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[measurable_wrt] THEN X_GEN_TAC `v:real` THEN
   SUBGOAL_THEN `&0 < --c` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ --c * f x <= v} =
      {x | x IN prob_carrier p /\ f x <= v / --c}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `w:A` THEN
    AP_TERM_TAC THEN
    MP_TAC(SPECL [`(f:A->real) w`; `v:real`; `--c:real`] REAL_LE_RDIV_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[REAL_MUL_SYM];
    UNDISCH_TAC `measurable_wrt (p:A prob_space) G f` THEN
    REWRITE_TAC[measurable_wrt] THEN MESON_TAC[]]]);;

(* Density of nonneg rationals: any interval (a,b) with 0 <= a contains
   a nonneg rational &n * inv(&(SUC m)) *)
let NONNEG_RATIONALS_DENSE = prove
 (`!a b. &0 <= a /\ a < b
         ==> ?n m. a < &n * inv(&(SUC m)) /\ &n * inv(&(SUC m)) < b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `b - a:real` REAL_ARCH_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?m0. K = SUC m0` (X_CHOOSE_TAC `m0:num`) THENL
  [ASM_MESON_TAC[num_CASES]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&(SUC m0))` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&(SUC m0)) < b - a` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `?n0. a < &n0 * inv(&(SUC m0)) /\
          !k. k < n0 ==> &k * inv(&(SUC m0)) <= a`
    STRIP_ASSUME_TAC THENL
  [MP_TAC(ISPEC `\n. a < &n * inv(&(SUC m0))` num_WOP) THEN
   REWRITE_TAC[] THEN
   MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN
   CONJ_TAC THENL
   [MP_TAC(SPEC `inv(&(SUC m0))` REAL_ARCH) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `nn:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `nn:num` THEN ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `?p. n0 = SUC p` (X_CHOOSE_TAC `p:num`) THENL
  [DISJ_CASES_TAC(SPEC `n0:num` num_CASES) THENL
   [UNDISCH_TAC `a < &n0 * inv(&(SUC m0))` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
    ASM_MESON_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `&p * inv(&(SUC m0)) <= a` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN
   UNDISCH_TAC `n0 = SUC p` THEN ARITH_TAC;
   ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`n0:num`; `m0:num`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `a + inv(&(SUC m0))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
   REWRITE_TAC[REAL_OF_NUM_SUC] THEN
   ASM_REAL_ARITH_TAC;
   ASM_REAL_ARITH_TAC]);;

(* Key lemma: {f - g < c} is in G when f, g are G-measurable *)
let MEASURABLE_WRT_DIFF_LT = prove
 (`!p:A prob_space G (f:A->real) (g:A->real) c.
     sub_sigma_algebra p G /\ measurable_wrt p G f /\ measurable_wrt p G g
     ==> {x | x IN prob_carrier p /\ f x - g x < c} IN G`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `!q. {x:A | x IN prob_carrier p /\ f x < q} INTER
         {x | x IN prob_carrier p /\ g x > q - c} IN G`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   MATCH_MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`]
     SUB_SIGMA_ALGEBRA_INTER) THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_WRT_STRICT_LT THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ g x > q - c} =
       prob_carrier p DIFF {x | x IN prob_carrier p /\ g x <= q - c}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN
     X_GEN_TAC `w:A` THEN
     ASM_CASES_TAC `(w:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     REAL_ARITH_TAC;
     MATCH_MP_TAC SUB_SIGMA_ALGEBRA_COMPL THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `measurable_wrt (p:A prob_space) G g` THEN
     REWRITE_TAC[measurable_wrt] THEN MESON_TAC[]]];
   ALL_TAC] THEN
  SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  ABBREV_TAC
    `S_all =
     UNIONS (IMAGE (\i.
       {x:A | x IN prob_carrier p /\
              f x < &(NUMFST i) * inv(&(SUC(NUMSND i)))} INTER
       {x | x IN prob_carrier p /\
            g x > &(NUMFST i) * inv(&(SUC(NUMSND i))) - c})
     (:num))
     UNION
     UNIONS (IMAGE (\i.
       {x:A | x IN prob_carrier p /\
              f x < --(&(NUMFST i) * inv(&(SUC(NUMSND i))))} INTER
       {x | x IN prob_carrier p /\
            g x > --(&(NUMFST i) * inv(&(SUC(NUMSND i)))) - c})
     (:num))` THEN
  SUBGOAL_THEN `S_all:A->bool IN G` ASSUME_TAC THENL
  [EXPAND_TAC "S_all" THEN
   MATCH_MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`]
     SUB_SIGMA_ALGEBRA_UNION) THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_UNION_COUNTABLE THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    GEN_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    GEN_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ f x - g x < c} = S_all`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
  [(* Forward: {f - g < c} SUBSET S_all *)
   EXPAND_TAC "S_all" THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION;
               IN_UNIONS; IN_IMAGE; IN_UNIV; IN_INTER] THEN
   X_GEN_TAC `w:A` THEN STRIP_TAC THEN
   ASM_CASES_TAC `(g:A->real) w + c > &0` THENL
   [ASM_CASES_TAC `&0 <= (f:A->real) w` THENL
    [MP_TAC(SPECL [`(f:A->real) w`; `(g:A->real) w + c`]
       NONNEG_RATIONALS_DENSE) THEN
     ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     DISCH_THEN(X_CHOOSE_THEN `n:num`
       (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC)) THEN
     DISJ1_TAC THEN
     EXISTS_TAC `{x:A | x IN prob_carrier p /\
       f x < &(NUMFST(NUMPAIR n m)) * inv(&(SUC(NUMSND(NUMPAIR n m))))}
       INTER
       {x | x IN prob_carrier p /\
       g x > &(NUMFST(NUMPAIR n m)) *
             inv(&(SUC(NUMSND(NUMPAIR n m)))) - c}` THEN
     CONJ_TAC THENL
     [EXISTS_TAC `NUMPAIR n m` THEN REFL_TAC; ALL_TAC] THEN
     REWRITE_TAC[NUMPAIR_DEST; IN_INTER; IN_ELIM_THM] THEN
     ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
     (* f(w) < 0, g(w)+c > 0: use q = 0 *)
     DISJ1_TAC THEN
     EXISTS_TAC `{x:A | x IN prob_carrier p /\
       f x < &(NUMFST(NUMPAIR 0 0)) *
             inv(&(SUC(NUMSND(NUMPAIR 0 0))))} INTER
       {x | x IN prob_carrier p /\
       g x > &(NUMFST(NUMPAIR 0 0)) *
             inv(&(SUC(NUMSND(NUMPAIR 0 0)))) - c}` THEN
     CONJ_TAC THENL
     [EXISTS_TAC `NUMPAIR 0 0` THEN REFL_TAC; ALL_TAC] THEN
     REWRITE_TAC[NUMPAIR_DEST; IN_INTER; IN_ELIM_THM] THEN
     ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC];
    (* g(w)+c <= 0: use negative family *)
    MP_TAC(SPECL [`--((g:A->real) w + c)`; `--((f:A->real) w)`]
      NONNEG_RATIONALS_DENSE) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num`
      (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC)) THEN
    DISJ2_TAC THEN
    EXISTS_TAC `{x:A | x IN prob_carrier p /\
      f x < --(&(NUMFST(NUMPAIR n m)) *
              inv(&(SUC(NUMSND(NUMPAIR n m)))))} INTER
      {x | x IN prob_carrier p /\
      g x > --(&(NUMFST(NUMPAIR n m)) *
              inv(&(SUC(NUMSND(NUMPAIR n m))))) - c}` THEN
    CONJ_TAC THENL
    [EXISTS_TAC `NUMPAIR n m` THEN REFL_TAC; ALL_TAC] THEN
    REWRITE_TAC[NUMPAIR_DEST; IN_INTER; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
   (* Backward: S_all SUBSET {f - g < c} *)
   EXPAND_TAC "S_all" THEN
   REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN
   REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
   X_GEN_TAC `w:A` THEN STRIP_TAC THEN
   UNDISCH_TAC `(w:A) IN t` THEN
   ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Difference of G-measurable functions is G-measurable *)
let MEASURABLE_WRT_SUB = prove
 (`!p:A prob_space G (f:A->real) (g:A->real).
     sub_sigma_algebra p G /\ measurable_wrt p G f /\ measurable_wrt p G g
     ==> measurable_wrt p G (\x. f x - g x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[measurable_wrt] THEN
  X_GEN_TAC `v:real` THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ f x - g x <= v} =
     prob_carrier p DIFF {x | x IN prob_carrier p /\ g x - f x < --v}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN
   X_GEN_TAC `w:A` THEN
   ASM_CASES_TAC `(w:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC;
   MATCH_MP_TAC SUB_SIGMA_ALGEBRA_COMPL THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MEASURABLE_WRT_DIFF_LT THEN ASM_REWRITE_TAC[]]);;

(* Sum of G-measurable functions is G-measurable *)
let MEASURABLE_WRT_ADD = prove
 (`!p:A prob_space G (f:A->real) (g:A->real).
     sub_sigma_algebra p G /\ measurable_wrt p G f /\ measurable_wrt p G g
     ==> measurable_wrt p G (\x. f x + g x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. (f:A->real) x + g x) = (\x. f x - --(g x))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; real_sub; REAL_NEG_NEG]; ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_WRT_SUB THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_WRT_NEG THEN ASM_REWRITE_TAC[]);;

(* --- Almost-sure uniqueness for conditional expectation --- *)

(* If f is nonneg, G-measurable, integrable, and E[f * 1_A] = 0 for all *)
(* A in G, then f = 0 a.s. *)
let NONNEG_MEASURABLE_WRT_ZERO_INTEGRALS_AE_ZERO = prove
 (`!p:A prob_space G (f:A->real).
    sub_sigma_algebra p G /\ integrable p f /\
    measurable_wrt p G f /\
    (!x. x IN prob_carrier p ==> &0 <= f x) /\
    (!A. A IN G ==> expectation p (\x. f x * indicator_fn A x) = &0)
    ==> almost_surely p {x | f x = &0}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[almost_surely] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ ~(x IN {x | f x = &0})} =
     {x | x IN prob_carrier p /\ ~(f x = &0)}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC
    `A_k = \k:num. {x:A | x IN prob_carrier p /\
                           f x >= inv(&(SUC k))}` THEN
  EXISTS_TAC
    `UNIONS {(A_k:num->A->bool) n | n IN (:num)}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC NULL_EVENT_COUNTABLE_UNION THEN X_GEN_TAC `k:num` THEN
   SUBGOAL_THEN `(A_k:num->A->bool) k IN G` ASSUME_TAC THENL
   [EXPAND_TAC "A_k" THEN BETA_TAC THEN
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ f x >= inv(&(SUC k))} =
       prob_carrier p DIFF {x | x IN prob_carrier p /\ f x < inv(&(SUC k))}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN
     X_GEN_TAC `w:A` THEN
     ASM_CASES_TAC `(w:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     REAL_ARITH_TAC;
     MATCH_MP_TAC SUB_SIGMA_ALGEBRA_COMPL THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC MEASURABLE_WRT_STRICT_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `(A_k:num->A->bool) k IN prob_events p` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
   REWRITE_TAC[null_event] THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < inv(&(SUC k))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `prob (p:A prob_space) ((A_k:num->A->bool) k) <= &0 <=>
      inv(&(SUC k)) * prob p (A_k k) <= inv(&(SUC k)) * &0`
     SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LE_LMUL_EQ THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_MUL_RZERO]] THEN
   SUBGOAL_THEN
     `inv(&(SUC k)) * prob (p:A prob_space) ((A_k:num->A->bool) k) <=
      expectation p (\x. (f:A->real) x * indicator_fn (A_k k) x)` MP_TAC THENL
   [SUBGOAL_THEN
      `inv(&(SUC k)) * prob (p:A prob_space) ((A_k:num->A->bool) k) =
       expectation p (\x:A. inv(&(SUC k)) * indicator_fn (A_k k) x)`
      SUBST1_TAC THENL
    [CONV_TAC SYM_CONV THEN
     MP_TAC(SPECL [`p:A prob_space`; `inv(&(SUC k))`;
       `indicator_fn ((A_k:num->A->bool) k):A->real`] EXPECTATION_CMUL) THEN
     BETA_TAC THEN ANTS_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[EXPECTATION_INDICATOR]];
     ALL_TAC] THEN
    MATCH_MP_TAC EXPECTATION_MONO THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
    [MP_TAC(SPECL [`p:A prob_space`; `inv(&(SUC k))`;
       `indicator_fn ((A_k:num->A->bool) k):A->real`] INTEGRABLE_CMUL_ALT) THEN
     BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
     MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[];
     X_GEN_TAC `w:A` THEN DISCH_TAC THEN
     REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THENL
     [REWRITE_TAC[REAL_MUL_RID] THEN
      SUBGOAL_THEN `(w:A) IN (A_k:num->A->bool) k` MP_TAC THENL
      [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "A_k" THEN BETA_TAC THEN
      REWRITE_TAC[IN_ELIM_THM; real_ge] THEN MESON_TAC[];
      REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL]]];
    FIRST_X_ASSUM(MP_TAC o SPEC `(A_k:num->A->bool) k`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];

   (* Subset *)
   REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN
   X_GEN_TAC `w:A` THEN STRIP_TAC THEN
   SUBGOAL_THEN `&0 < (f:A->real) w` MP_TAC THENL
   [ASM_MESON_TAC[REAL_LT_LE]; ALL_TAC] THEN
   GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
   DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `(A_k:num->A->bool) (j - 1)` THEN CONJ_TAC THENL
   [EXISTS_TAC `j - 1` THEN REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
   EXPAND_TAC "A_k" THEN BETA_TAC THEN
   REWRITE_TAC[IN_ELIM_THM; real_ge] THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `SUC (j - 1) = j` SUBST1_TAC THENL
   [UNDISCH_TAC `~(j = 0)` THEN ARITH_TAC;
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]]);;

(* A nonnegative integrable function with zero expectation is zero a.s.        *)
(* Specialize NONNEG_MEASURABLE_WRT_ZERO_INTEGRALS_AE_ZERO to the full event   *)
(* algebra: for any event A, 0 <= E[f*1_A] <= E[f] = 0.                        *)
let EXPECTATION_NONNEG_ZERO_AE_ZERO = prove
 (`!p:A prob_space f.
     integrable p f /\
     (!x. x IN prob_carrier p ==> &0 <= f x) /\
     expectation p f = &0
     ==> almost_surely p {x | f x = &0}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `prob_events (p:A prob_space)`; `f:A->real`]
    NONNEG_MEASURABLE_WRT_ZERO_INTEGRALS_AE_ZERO) THEN
  ASM_REWRITE_TAC[SUB_SIGMA_ALGEBRA_SELF] THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[MEASURABLE_WRT_EVENTS] THEN
   MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  X_GEN_TAC `A:A->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `expectation (p:A prob_space) f` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO THEN
    ASM_SIMP_TAC[INTEGRABLE_MUL_INDICATOR_FN] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO] THEN ASM_SIMP_TAC[REAL_LE_REFL];
    ASM_REWRITE_TAC[REAL_LE_REFL]];
   MATCH_MP_TAC EXPECTATION_POS THEN
   ASM_SIMP_TAC[INTEGRABLE_MUL_INDICATOR_FN] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN
   REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; REAL_LE_REFL] THEN
   ASM_SIMP_TAC[]]);;

(* If f, g are G-measurable, integrable, and have equal integrals *)
(* against all G-sets, then f = g a.s. *)
let GEN_COND_EXP_AE_UNIQUE = prove
 (`!p:A prob_space G (f:A->real) (g:A->real).
    sub_sigma_algebra p G /\
    measurable_wrt p G f /\ integrable p f /\
    measurable_wrt p G g /\ integrable p g /\
    (!A. A IN G ==>
      expectation p (\x. f x * indicator_fn A x) =
      expectation p (\x. g x * indicator_fn A x))
    ==> almost_surely p {x | f x = g x}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[almost_surely] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ ~(x IN {x | (f:A->real) x = g x})} =
     {x | x IN prob_carrier p /\ ~(f x = g x)}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC
    `A_n = \n:num. {x:A | x IN prob_carrier p /\
                           (f:A->real) x - g x >= inv(&(SUC n))}` THEN
  ABBREV_TAC
    `B_n = \n:num. {x:A | x IN prob_carrier p /\
                           (g:A->real) x - f x >= inv(&(SUC n))}` THEN
  EXISTS_TAC `UNIONS {(A_n:num->A->bool) n | n IN (:num)} UNION
              UNIONS {(B_n:num->A->bool) n | n IN (:num)}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC NULL_EVENT_UNION THEN CONJ_TAC THEN
   MATCH_MP_TAC NULL_EVENT_COUNTABLE_UNION THEN X_GEN_TAC `k:num` THEN
   (SUBGOAL_THEN `(&0 < inv(&(SUC k)))` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LT_INV THEN REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
     ALL_TAC]) THENL
   [(* A_n k *)
    SUBGOAL_THEN `(A_n:num->A->bool) k IN G` ASSUME_TAC THENL
    [EXPAND_TAC "A_n" THEN BETA_TAC THEN
     SUBGOAL_THEN
       `{x:A | x IN prob_carrier p /\ f x - g x >= inv(&(SUC k))} =
        prob_carrier p DIFF
          {x | x IN prob_carrier p /\ f x - g x < inv(&(SUC k))}`
       SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN X_GEN_TAC `w:A` THEN
      ASM_CASES_TAC `(w:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC SUB_SIGMA_ALGEBRA_COMPL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MEASURABLE_WRT_DIFF_LT THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
    SUBGOAL_THEN `(A_n:num->A->bool) k IN prob_events p` ASSUME_TAC THENL
    [ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[null_event] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
      `prob (p:A prob_space) ((A_n:num->A->bool) k) <= &0 <=>
       inv(&(SUC k)) * prob p (A_n k) <= inv(&(SUC k)) * &0`
      SUBST1_TAC THENL
    [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LE_LMUL_EQ THEN
     ASM_REWRITE_TAC[];
     REWRITE_TAC[REAL_MUL_RZERO]] THEN
    SUBGOAL_THEN
      `inv(&(SUC k)) * prob (p:A prob_space) ((A_n:num->A->bool) k) <=
       expectation p (\x. ((f:A->real) x - g x) *
                          indicator_fn (A_n k) x)` MP_TAC THENL
    [SUBGOAL_THEN
       `inv(&(SUC k)) * prob (p:A prob_space) ((A_n:num->A->bool) k) =
        expectation p (\x:A. inv(&(SUC k)) * indicator_fn (A_n k) x)`
       SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MP_TAC(SPECL [`p:A prob_space`; `inv(&(SUC k))`;
        `indicator_fn ((A_n:num->A->bool) k):A->real`] EXPECTATION_CMUL) THEN
      BETA_TAC THEN ANTS_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
       ASM_SIMP_TAC[EXPECTATION_INDICATOR]];
      ALL_TAC] THEN
     MATCH_MP_TAC EXPECTATION_MONO THEN BETA_TAC THEN
     REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`p:A prob_space`; `inv(&(SUC k))`;
        `indicator_fn ((A_n:num->A->bool) k):A->real`]
        INTEGRABLE_CMUL_ALT) THEN
      BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN
        `(\x:A. ((f:A->real) x - g x) *
                indicator_fn ((A_n:num->A->bool) k) x) =
         (\x. f x * indicator_fn (A_n k) x +
              --(g x * indicator_fn (A_n k) x))`
        SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC INTEGRABLE_NEG THEN
       MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `w:A` THEN DISCH_TAC THEN
      REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THENL
      [REWRITE_TAC[REAL_MUL_RID] THEN
       SUBGOAL_THEN `(w:A) IN (A_n:num->A->bool) k` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       EXPAND_TAC "A_n" THEN BETA_TAC THEN
       REWRITE_TAC[IN_ELIM_THM; real_ge] THEN MESON_TAC[];
       REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL]]];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `(\x:A. ((f:A->real) x - g x) *
              indicator_fn ((A_n:num->A->bool) k) x) =
       (\x. f x * indicator_fn (A_n k) x -
            g x * indicator_fn (A_n k) x)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`p:A prob_space`;
      `\x:A. (f:A->real) x * indicator_fn ((A_n:num->A->bool) k) x`;
      `\x:A. (g:A->real) x * indicator_fn ((A_n:num->A->bool) k) x`]
      EXPECTATION_SUB) THEN
    BETA_TAC THEN ANTS_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(A_n:num->A->bool) k`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;

    (* B_n k - symmetric *)
    SUBGOAL_THEN `(B_n:num->A->bool) k IN G` ASSUME_TAC THENL
    [EXPAND_TAC "B_n" THEN BETA_TAC THEN
     SUBGOAL_THEN
       `{x:A | x IN prob_carrier p /\ g x - f x >= inv(&(SUC k))} =
        prob_carrier p DIFF
          {x | x IN prob_carrier p /\ g x - f x < inv(&(SUC k))}`
       SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN X_GEN_TAC `w:A` THEN
      ASM_CASES_TAC `(w:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC SUB_SIGMA_ALGEBRA_COMPL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MEASURABLE_WRT_DIFF_LT THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
    SUBGOAL_THEN `(B_n:num->A->bool) k IN prob_events p` ASSUME_TAC THENL
    [ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[null_event] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
      `prob (p:A prob_space) ((B_n:num->A->bool) k) <= &0 <=>
       inv(&(SUC k)) * prob p (B_n k) <= inv(&(SUC k)) * &0`
      SUBST1_TAC THENL
    [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LE_LMUL_EQ THEN
     ASM_REWRITE_TAC[];
     REWRITE_TAC[REAL_MUL_RZERO]] THEN
    SUBGOAL_THEN
      `inv(&(SUC k)) * prob (p:A prob_space) ((B_n:num->A->bool) k) <=
       expectation p (\x. ((g:A->real) x - f x) *
                          indicator_fn (B_n k) x)` MP_TAC THENL
    [SUBGOAL_THEN
       `inv(&(SUC k)) * prob (p:A prob_space) ((B_n:num->A->bool) k) =
        expectation p (\x:A. inv(&(SUC k)) * indicator_fn (B_n k) x)`
       SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MP_TAC(SPECL [`p:A prob_space`; `inv(&(SUC k))`;
        `indicator_fn ((B_n:num->A->bool) k):A->real`] EXPECTATION_CMUL) THEN
      BETA_TAC THEN ANTS_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
       ASM_SIMP_TAC[EXPECTATION_INDICATOR]];
      ALL_TAC] THEN
     MATCH_MP_TAC EXPECTATION_MONO THEN BETA_TAC THEN
     REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`p:A prob_space`; `inv(&(SUC k))`;
        `indicator_fn ((B_n:num->A->bool) k):A->real`]
        INTEGRABLE_CMUL_ALT) THEN
      BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN
        `(\x:A. ((g:A->real) x - f x) *
                indicator_fn ((B_n:num->A->bool) k) x) =
         (\x. g x * indicator_fn (B_n k) x +
              --(f x * indicator_fn (B_n k) x))`
        SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC INTEGRABLE_NEG THEN
       MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `w:A` THEN DISCH_TAC THEN
      REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THENL
      [REWRITE_TAC[REAL_MUL_RID] THEN
       SUBGOAL_THEN `(w:A) IN (B_n:num->A->bool) k` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       EXPAND_TAC "B_n" THEN BETA_TAC THEN
       REWRITE_TAC[IN_ELIM_THM; real_ge] THEN MESON_TAC[];
       REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL]]];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `(\x:A. ((g:A->real) x - f x) *
              indicator_fn ((B_n:num->A->bool) k) x) =
       (\x. g x * indicator_fn (B_n k) x -
            f x * indicator_fn (B_n k) x)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`p:A prob_space`;
      `\x:A. (g:A->real) x * indicator_fn ((B_n:num->A->bool) k) x`;
      `\x:A. (f:A->real) x * indicator_fn ((B_n:num->A->bool) k) x`]
      EXPECTATION_SUB) THEN
    BETA_TAC THEN ANTS_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(B_n:num->A->bool) k`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];

   (* Subset *)
   REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; IN_UNIONS] THEN
   X_GEN_TAC `w:A` THEN STRIP_TAC THEN
   SUBGOAL_THEN `(f:A->real) w > g w \/ (g:A->real) w > f w` MP_TAC THENL
   [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    DISCH_THEN DISJ_CASES_TAC] THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `&0 < (f:A->real) w - g w` MP_TAC THENL
    [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(A_n:num->A->bool) (j - 1)` THEN CONJ_TAC THENL
    [EXISTS_TAC `j - 1` THEN REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
    EXPAND_TAC "A_n" THEN BETA_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; real_ge] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `SUC (j - 1) = j` SUBST1_TAC THENL
    [UNDISCH_TAC `~(j = 0)` THEN ARITH_TAC;
     MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]];

    DISJ2_TAC THEN
    SUBGOAL_THEN `&0 < (g:A->real) w - f w` MP_TAC THENL
    [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(B_n:num->A->bool) (j - 1)` THEN CONJ_TAC THENL
    [EXISTS_TAC `j - 1` THEN REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
    EXPAND_TAC "B_n" THEN BETA_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; real_ge] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `SUC (j - 1) = j` SUBST1_TAC THENL
    [UNDISCH_TAC `~(j = 0)` THEN ARITH_TAC;
     MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]]]);;

(* Radon-Nikodym uniqueness: if f and g are both R-N derivatives of mu, *)
(* then f = g a.s.  Corollary of GEN_COND_EXP_AE_UNIQUE with G = events. *)
let RADON_NIKODYM_UNIQUE = prove
 (`!p:A prob_space f g mu.
    integrable p f /\ integrable p g /\
    (!A. A IN prob_events p
         ==> expectation p (\x. f x * indicator_fn A x) = mu A) /\
    (!A. A IN prob_events p
         ==> expectation p (\x. g x * indicator_fn A x) = mu A)
    ==> almost_surely p {x | f x = g x}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC GEN_COND_EXP_AE_UNIQUE THEN
  EXISTS_TAC `prob_events(p:A prob_space)` THEN
  REWRITE_TAC[SUB_SIGMA_ALGEBRA_SELF] THEN
  ASM_REWRITE_TAC[MEASURABLE_WRT_EVENTS] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
   CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[]]]);;

(* Step 3: Non-negativity preservation *)
let GEN_COND_EXP_NONNEG = prove
 (`!p:A prob_space G (X:A->real).
    sub_sigma_algebra p G /\ integrable p X /\
    (!x. x IN prob_carrier p ==> &0 <= X x)
    ==> almost_surely p {x | &0 <= gen_cond_exp p G X x}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[almost_surely] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\
            ~(x IN {x | &0 <= gen_cond_exp p G (X:A->real) x})} =
     {x | x IN prob_carrier p /\ gen_cond_exp p G X x < &0}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
    `A_k = \k:num. {x:A | x IN prob_carrier p /\
                           gen_cond_exp p G (X:A->real) x <
                           --inv(&(SUC k))}` THEN
  EXISTS_TAC `UNIONS {(A_k:num->A->bool) k | k IN (:num)}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC NULL_EVENT_COUNTABLE_UNION THEN X_GEN_TAC `k:num` THEN
   SUBGOAL_THEN `(A_k:num->A->bool) k IN G` ASSUME_TAC THENL
   [SUBGOAL_THEN
      `(A_k:num->A->bool) k =
       {x:A | x IN prob_carrier p /\
              gen_cond_exp p G (X:A->real) x < --inv(&(SUC k))}`
      SUBST1_TAC THENL
    [EXPAND_TAC "A_k" THEN BETA_TAC THEN REFL_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`;
      `gen_cond_exp p G (X:A->real)`; `--inv(&(SUC k))`]
      MEASURABLE_WRT_STRICT_LT) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GEN_COND_EXP_MEASURABLE_WRT THEN
     ASM_REWRITE_TAC[];
     SIMP_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `(A_k:num->A->bool) k IN prob_events p` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
   REWRITE_TAC[null_event] THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < inv(&(SUC k))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation p (\x:A. gen_cond_exp p G (X:A->real) x *
                           indicator_fn ((A_k:num->A->bool) k) x) =
      expectation p (\x. X x * indicator_fn (A_k k) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `&0 <= expectation p (\x:A. (X:A->real) x *
                                  indicator_fn ((A_k:num->A->bool) k) x)`
     ASSUME_TAC THENL
   [MP_TAC(SPECL [`p:A prob_space`;
      `\x:A. (X:A->real) x * indicator_fn ((A_k:num->A->bool) k) x`]
      EXPECTATION_POS) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[];
     X_GEN_TAC `w:A` THEN DISCH_TAC THEN
     MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation p (\x:A. gen_cond_exp p G (X:A->real) x *
                           indicator_fn ((A_k:num->A->bool) k) x) <=
      --(inv(&(SUC k))) * prob p ((A_k:num->A->bool) k)` ASSUME_TAC THENL
   [SUBGOAL_THEN
      `--(inv(&(SUC k))) * prob (p:A prob_space) ((A_k:num->A->bool) k) =
       expectation p (\x:A. --inv(&(SUC k)) * indicator_fn (A_k k) x)`
      SUBST1_TAC THENL
    [CONV_TAC SYM_CONV THEN
     MP_TAC(SPECL [`p:A prob_space`; `--inv(&(SUC k))`;
       `indicator_fn ((A_k:num->A->bool) k):A->real`] EXPECTATION_CMUL) THEN
     BETA_TAC THEN ANTS_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[EXPECTATION_INDICATOR] THEN REAL_ARITH_TAC];
     ALL_TAC] THEN
    MATCH_MP_TAC EXPECTATION_MONO THEN BETA_TAC THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
     MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`;
       `X:A->real`] GEN_COND_EXP_INTEGRABLE) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[ETA_AX]];
     MP_TAC(SPECL [`p:A prob_space`; `--inv(&(SUC k))`;
       `indicator_fn ((A_k:num->A->bool) k):A->real`]
       INTEGRABLE_CMUL_ALT) THEN
     BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
     MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
     X_GEN_TAC `w:A` THEN DISCH_TAC THEN
     REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THENL
     [REWRITE_TAC[REAL_MUL_RID] THEN
      SUBGOAL_THEN `(w:A) IN (A_k:num->A->bool) k` MP_TAC THENL
      [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "A_k" THEN BETA_TAC THEN
      REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL]]];
    ALL_TAC] THEN
   SUBGOAL_THEN `prob (p:A prob_space) ((A_k:num->A->bool) k) <= &0 <=>
                  inv(&(SUC k)) * prob p (A_k k) <= inv(&(SUC k)) * &0`
     SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LE_LMUL_EQ THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_MUL_RZERO] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `--(expectation p (\x:A. gen_cond_exp p G (X:A->real) x *
                    indicator_fn ((A_k:num->A->bool) k) x))` THEN
    CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
   REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN
   X_GEN_TAC `w:A` THEN STRIP_TAC THEN
   SUBGOAL_THEN `&0 < --(gen_cond_exp p G (X:A->real) w)` MP_TAC THENL
   [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
   DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `(A_k:num->A->bool) (j - 1)` THEN CONJ_TAC THENL
   [EXISTS_TAC `j - 1` THEN REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
   EXPAND_TAC "A_k" THEN BETA_TAC THEN
   REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `SUC (j - 1) = j` SUBST1_TAC THENL
   [UNDISCH_TAC `~(j = 0)` THEN ARITH_TAC;
    UNDISCH_TAC `inv (&j) < --(gen_cond_exp p G (X:A->real) w)` THEN
    REAL_ARITH_TAC]]);;

(* Step 4: Scalar multiple *)
let GEN_COND_EXP_CMUL = prove
 (`!p:A prob_space G (X:A->real) c.
    sub_sigma_algebra p G /\ integrable p X
    ==> almost_surely p
      {x | gen_cond_exp p G (\w. c * X w) x = c * gen_cond_exp p G X x}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC GEN_COND_EXP_AE_UNIQUE THEN
  EXISTS_TAC `G:(A->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `(\w:A. c * (X:A->real) w)`] GEN_COND_EXP_MEASURABLE_WRT) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ETA_AX]];
   MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `(\w:A. c * (X:A->real) w)`] GEN_COND_EXP_INTEGRABLE) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ETA_AX]];
   MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `gen_cond_exp p G (X:A->real)`; `c:real`]
    MEASURABLE_WRT_CMUL) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`; `X:A->real`]
      GEN_COND_EXP_MEASURABLE_WRT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    REWRITE_TAC[]];
   MP_TAC(SPECL [`p:A prob_space`; `c:real`;
    `gen_cond_exp p G (X:A->real)`] INTEGRABLE_CMUL) THEN
   ANTS_TAC THENL
   [MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`; `X:A->real`]
     GEN_COND_EXP_INTEGRABLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    REWRITE_TAC[]];
   X_GEN_TAC `A:A->bool` THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `expectation p (\x:A. gen_cond_exp p G
        (\w. c * (X:A->real) w) x * indicator_fn A x) =
      expectation p (\x. (c * X x) * indicator_fn A x)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `(\x:A. (c * (X:A->real) x) * indicator_fn (A:A->bool) x) =
      (\x. c * (X x * indicator_fn A x))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `(\x:A. (c * gen_cond_exp p G (X:A->real) x) *
        indicator_fn (A:A->bool) x) =
      (\x. c * (gen_cond_exp p G X x * indicator_fn A x))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(A:A->bool) IN prob_events p` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation p (\x:A. c * (X:A->real) x * indicator_fn (A:A->bool) x) =
      c * expectation p (\x. X x * indicator_fn A x)` SUBST1_TAC THENL
   [MP_TAC(SPECL [`p:A prob_space`; `c:real`;
     `\x:A. (X:A->real) x * indicator_fn (A:A->bool) x`]
     EXPECTATION_CMUL) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation p (\x:A. c * gen_cond_exp p G (X:A->real) x *
        indicator_fn (A:A->bool) x) =
      c * expectation p (\x. gen_cond_exp p G X x * indicator_fn A x)`
     SUBST1_TAC THENL
   [MP_TAC(SPECL [`p:A prob_space`; `c:real`;
     `\x:A. gen_cond_exp p G (X:A->real) x *
       indicator_fn (A:A->bool) x`] EXPECTATION_CMUL) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`; `X:A->real`]
      GEN_COND_EXP_INTEGRABLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
   AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[]]);;

(* Step 5: Addition *)
let GEN_COND_EXP_ADD = prove
 (`!p:A prob_space G (X:A->real) (Y:A->real).
    sub_sigma_algebra p G /\ integrable p X /\ integrable p Y
    ==> almost_surely p
      {x | gen_cond_exp p G (\w. X w + Y w) x =
           gen_cond_exp p G X x + gen_cond_exp p G Y x}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC GEN_COND_EXP_AE_UNIQUE THEN
  EXISTS_TAC `G:(A->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `(\w:A. (X:A->real) w + (Y:A->real) w)`]
    GEN_COND_EXP_MEASURABLE_WRT) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ETA_AX]];
   MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `(\w:A. (X:A->real) w + (Y:A->real) w)`]
    GEN_COND_EXP_INTEGRABLE) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ETA_AX]];
   MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `gen_cond_exp p G (X:A->real)`;
    `gen_cond_exp p G (Y:A->real)`] MEASURABLE_WRT_ADD) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`]
      GEN_COND_EXP_MEASURABLE_WRT) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[]];
   MP_TAC(SPECL [`p:A prob_space`;
    `gen_cond_exp p G (X:A->real)`;
    `gen_cond_exp p G (Y:A->real)`] INTEGRABLE_ADD) THEN
   ANTS_TAC THENL
   [CONJ_TAC THEN
    MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`]
      GEN_COND_EXP_INTEGRABLE) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[]];
   X_GEN_TAC `A:A->bool` THEN DISCH_TAC THEN
   SUBGOAL_THEN `(A:A->bool) IN prob_events p` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation p (\x:A. gen_cond_exp p G
        (\w. (X:A->real) w + (Y:A->real) w) x *
        indicator_fn (A:A->bool) x) =
      expectation p (\x. (X x + Y x) * indicator_fn A x)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `(\x:A. ((X:A->real) x + (Y:A->real) x) *
        indicator_fn (A:A->bool) x) =
      (\x. X x * indicator_fn A x + Y x * indicator_fn A x)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `(\x:A. (gen_cond_exp p G (X:A->real) x +
        gen_cond_exp p G (Y:A->real) x) *
        indicator_fn (A:A->bool) x) =
      (\x. gen_cond_exp p G X x * indicator_fn A x +
           gen_cond_exp p G Y x * indicator_fn A x)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `integrable p (\x:A. (X:A->real) x *
        indicator_fn (A:A->bool) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `integrable p (\x:A. (Y:A->real) x *
        indicator_fn (A:A->bool) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `integrable p (\x:A. gen_cond_exp p G (X:A->real) x *
        indicator_fn (A:A->bool) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`; `X:A->real`]
      GEN_COND_EXP_INTEGRABLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `integrable p (\x:A. gen_cond_exp p G (Y:A->real) x *
        indicator_fn (A:A->bool) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`; `Y:A->real`]
      GEN_COND_EXP_INTEGRABLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
   ASM_SIMP_TAC[EXPECTATION_ADD] THEN
   BINOP_TAC THEN CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[]]);;

(* Step 5b: Subtraction *)
let GEN_COND_EXP_SUB = prove
 (`!p:A prob_space G (X:A->real) (Y:A->real).
    sub_sigma_algebra p G /\ integrable p X /\ integrable p Y
    ==> almost_surely p
      {x | gen_cond_exp p G (\w. X w - Y w) x =
           gen_cond_exp p G X x - gen_cond_exp p G Y x}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(\w:A. (X:A->real) w - (Y:A->real) w) = (\w. X w + (-- &1) * Y w)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `Y:A->real`; `-- &1`] GEN_COND_EXP_CMUL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `X:A->real`; `(\w:A. (-- &1) * (Y:A->real) w)`]
    GEN_COND_EXP_ADD) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[almost_surely] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:A->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `n1 UNION n2:A->bool` THEN CONJ_TAC THENL
  [MATCH_MP_TAC NULL_EVENT_UNION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN
  X_GEN_TAC `w:A` THEN STRIP_TAC THEN
  ASM_CASES_TAC
    `gen_cond_exp p G (\w:A. -- &1 * (Y:A->real) w) w =
     -- &1 * gen_cond_exp p G Y w` THENL
  [DISJ1_TAC THEN
   UNDISCH_TAC `{x:A | x IN prob_carrier p /\
     ~(x IN {x | gen_cond_exp p G (\w. (X:A->real) w + -- &1 * Y w) x =
                  gen_cond_exp p G X x +
                  gen_cond_exp p G (\w. -- &1 * Y w) x})} SUBSET n1` THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `~(gen_cond_exp p G (\w:A. (X:A->real) w + -- &1 * Y w) w =
     gen_cond_exp p G X w - gen_cond_exp p G Y w)` THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   DISJ2_TAC THEN
   UNDISCH_TAC `{x:A | x IN prob_carrier p /\
     ~(x IN {x | gen_cond_exp p G (\w. -- &1 * (Y:A->real) w) x =
                  -- &1 * gen_cond_exp p G Y x})} SUBSET n2` THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]]);;

(* Step 6: Monotonicity *)
let GEN_COND_EXP_MONOTONE = prove
 (`!p:A prob_space G (X:A->real) (Y:A->real).
    sub_sigma_algebra p G /\ integrable p X /\ integrable p Y /\
    (!x. x IN prob_carrier p ==> X x <= Y x)
    ==> almost_surely p {x | gen_cond_exp p G X x <= gen_cond_exp p G Y x}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[almost_surely] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\
      ~(x IN {x | gen_cond_exp p G (X:A->real) x <=
                   gen_cond_exp p G (Y:A->real) x})} =
     {x | x IN prob_carrier p /\
      gen_cond_exp p G Y x < gen_cond_exp p G X x}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
    `A_k = \k:num. {x:A | x IN prob_carrier p /\
                           gen_cond_exp p G (Y:A->real) x -
                           gen_cond_exp p G (X:A->real) x <
                           --inv(&(SUC k))}` THEN
  EXISTS_TAC `UNIONS {(A_k:num->A->bool) k | k IN (:num)}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC NULL_EVENT_COUNTABLE_UNION THEN X_GEN_TAC `k:num` THEN
   SUBGOAL_THEN `(A_k:num->A->bool) k IN G` ASSUME_TAC THENL
   [SUBGOAL_THEN
      `(A_k:num->A->bool) k =
       {x:A | x IN prob_carrier p /\
              gen_cond_exp p G (Y:A->real) x -
              gen_cond_exp p G (X:A->real) x < --inv(&(SUC k))}`
      SUBST1_TAC THENL
    [EXPAND_TAC "A_k" THEN BETA_TAC THEN REFL_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`;
      `gen_cond_exp p G (Y:A->real)`;
      `gen_cond_exp p G (X:A->real)`;
      `--inv(&(SUC k))`] MEASURABLE_WRT_DIFF_LT) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
     MATCH_MP_TAC GEN_COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[];
     SIMP_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `(A_k:num->A->bool) k IN prob_events p` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
   REWRITE_TAC[null_event] THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < inv(&(SUC k))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `prob (p:A prob_space) ((A_k:num->A->bool) k) <= &0 <=>
      inv(&(SUC k)) * prob p (A_k k) <= inv(&(SUC k)) * &0`
     SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LE_LMUL_EQ THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_MUL_RZERO]] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation p (\x:A.
     (gen_cond_exp p G (X:A->real) x -
      gen_cond_exp p G (Y:A->real) x) *
     indicator_fn ((A_k:num->A->bool) k) x)` THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN
      `inv(&(SUC k)) * prob (p:A prob_space) ((A_k:num->A->bool) k) =
       expectation p (\x:A. inv(&(SUC k)) * indicator_fn (A_k k) x)`
      SUBST1_TAC THENL
    [CONV_TAC SYM_CONV THEN
     MP_TAC(SPECL [`p:A prob_space`; `inv(&(SUC k))`;
       `indicator_fn ((A_k:num->A->bool) k):A->real`]
       EXPECTATION_CMUL) THEN
     BETA_TAC THEN ANTS_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[EXPECTATION_INDICATOR]];
     ALL_TAC] THEN
    MATCH_MP_TAC EXPECTATION_MONO THEN BETA_TAC THEN
    REPEAT CONJ_TAC THENL
    [MP_TAC(SPECL [`p:A prob_space`; `inv(&(SUC k))`;
       `indicator_fn ((A_k:num->A->bool) k):A->real`]
       INTEGRABLE_CMUL_ALT) THEN
     BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
     MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
     ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN
       `(\x:A. gen_cond_exp p G (X:A->real) x -
               gen_cond_exp p G (Y:A->real) x) =
        (\x. (\x. gen_cond_exp p G X x) x -
             (\x. gen_cond_exp p G Y x) x)` SUBST1_TAC THENL
     [REWRITE_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THEN
     REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
     X_GEN_TAC `w:A` THEN DISCH_TAC THEN
     REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THENL
     [REWRITE_TAC[REAL_MUL_RID] THEN
      SUBGOAL_THEN `(w:A) IN (A_k:num->A->bool) k` MP_TAC THENL
      [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "A_k" THEN BETA_TAC THEN
      REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL]]];
    (* E[(gen_cond_exp X - gen_cond_exp Y) * 1_A_k] <= 0 *)
    SUBGOAL_THEN
      `(\x:A. (gen_cond_exp p G (X:A->real) x -
               gen_cond_exp p G (Y:A->real) x) *
              indicator_fn ((A_k:num->A->bool) k) x) =
       (\x. gen_cond_exp p G X x * indicator_fn (A_k k) x -
            gen_cond_exp p G Y x * indicator_fn (A_k k) x)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
      `integrable p (\x:A. gen_cond_exp p G (X:A->real) x *
        indicator_fn ((A_k:num->A->bool) k) x)` ASSUME_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `integrable p (\x:A. gen_cond_exp p G (Y:A->real) x *
        indicator_fn ((A_k:num->A->bool) k) x)` ASSUME_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    ASM_SIMP_TAC[EXPECTATION_SUB] THEN
    SUBGOAL_THEN
      `expectation p (\x:A. gen_cond_exp p G (X:A->real) x *
        indicator_fn ((A_k:num->A->bool) k) x) =
       expectation p (\x. X x * indicator_fn (A_k k) x)`
      SUBST1_TAC THENL
    [MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `expectation p (\x:A. gen_cond_exp p G (Y:A->real) x *
        indicator_fn ((A_k:num->A->bool) k) x) =
       expectation p (\x. Y x * indicator_fn (A_k k) x)`
      SUBST1_TAC THENL
    [MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `integrable p (\x:A. (X:A->real) x *
        indicator_fn ((A_k:num->A->bool) k) x)` ASSUME_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `integrable p (\x:A. (Y:A->real) x *
        indicator_fn ((A_k:num->A->bool) k) x)` ASSUME_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a - b <= &0`) THEN
    MATCH_MP_TAC EXPECTATION_MONO THEN BETA_TAC THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
    [ASM_SIMP_TAC[];
     REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN
     REAL_ARITH_TAC]];
   (* Subset *)
   REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN
   X_GEN_TAC `w:A` THEN STRIP_TAC THEN
   SUBGOAL_THEN
     `&0 < gen_cond_exp p G (X:A->real) w -
           gen_cond_exp p G (Y:A->real) w` MP_TAC THENL
   [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
   DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `(A_k:num->A->bool) (j - 1)` THEN CONJ_TAC THENL
   [EXISTS_TAC `j - 1` THEN REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
   EXPAND_TAC "A_k" THEN BETA_TAC THEN
   REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `SUC (j - 1) = j` SUBST1_TAC THENL
   [UNDISCH_TAC `~(j = 0)` THEN ARITH_TAC;
    UNDISCH_TAC
      `inv (&j) < gen_cond_exp p G (X:A->real) w -
                   gen_cond_exp p G (Y:A->real) w` THEN
    REAL_ARITH_TAC]]);;

(* For a pointwise-increasing sequence of integrable random variables bounded   *)
(* by an integrable L, the conditional expectations are, off a single null set, *)
(* increasing in n and bounded by the conditional expectation of L.  Combines   *)
(* the countably-many almost-sure monotonicity facts from GEN_COND_EXP_MONOTONE *)
(* into one almost-sure statement.  (Groundwork for the conditional MCT.)       *)
let GEN_COND_EXP_SEQ_MONO_AE = prove
 (`!p:A prob_space G X L.
     sub_sigma_algebra p G /\ (!n. integrable p (X n)) /\ integrable p L /\
     (!n x. x IN prob_carrier p ==> X n x <= X (SUC n) x) /\
     (!n x. x IN prob_carrier p ==> X n x <= L x)
     ==> almost_surely p
           {x | (!n. gen_cond_exp p G (X n) x <= gen_cond_exp p G (X (SUC n)) x) /\
                (!n. gen_cond_exp p G (X n) x <= gen_cond_exp p G L x)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `!n. almost_surely p
       {x:A | gen_cond_exp p G ((X:num->A->real) n) x <= gen_cond_exp p G (X (SUC n)) x /\
              gen_cond_exp p G (X n) x <= gen_cond_exp p G (L:A->real) x}`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`; `(X:num->A->real) n`; `(X:num->A->real) (SUC n)`]
     GEN_COND_EXP_MONOTONE) THEN ASM_SIMP_TAC[] THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`; `(X:num->A->real) n`; `L:A->real`]
     GEN_COND_EXP_MONOTONE) THEN ASM_SIMP_TAC[] THEN DISCH_TAC THEN
   MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
   EXISTS_TAC `{x:A | gen_cond_exp p G ((X:num->A->real) n) x <= gen_cond_exp p G (X (SUC n)) x} INTER
               {x:A | gen_cond_exp p G ((X:num->A->real) n) x <= gen_cond_exp p G (L:A->real) x}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_INTER THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN MESON_TAC[]];
   ALL_TAC] THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
    `INTERS {{x:A | gen_cond_exp p G ((X:num->A->real) n) x <= gen_cond_exp p G (X (SUC n)) x /\
                    gen_cond_exp p G (X n) x <= gen_cond_exp p G (L:A->real) x} | n IN (:num)}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC; IN_UNIV; IN_ELIM_THM] THEN MESON_TAC[]]);;

(* For a nonnegative increasing sequence Xn converging pointwise to L (all      *)
(* integrable), the integral of (L - Xn) over any event A tends to 0.  This is  *)
(* dominated convergence: (L - Xn) times the indicator is dominated by          *)
(* (L - X0) times the indicator and tends to 0 pointwise.  (Groundwork for the  *)
(* conditional MCT: it controls the integral of the gap E[L|G] - E[Xn|G].)      *)
let INTEGRAL_GAP_TENDS_0 = prove
 (`!p:A prob_space X L A.
     (!n. integrable p (X n)) /\ integrable p L /\ A IN prob_events p /\
     (!n x. x IN prob_carrier p ==> &0 <= X n x) /\
     (!n x. x IN prob_carrier p ==> X n x <= X (SUC n) x) /\
     (!n x. x IN prob_carrier p ==> X n x <= L x) /\
     (!x. x IN prob_carrier p ==> ((\n. X n x) ---> L x) sequentially)
     ==> ((\n. expectation p (\x. (L x - X n x) * indicator_fn A x)) ---> &0)
         sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
   `\n:num. \x:A. (L x - (X:num->A->real) n x) * indicator_fn A x`;
   `\x:A. &0`;
   `\x:A. (L x - (X:num->A->real) 0 x) * indicator_fn A x`]
   DOMINATED_CONVERGENCE)) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
    MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN DISCH_TAC THEN
    REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ABS_NUM; REAL_LE_REFL] THEN
    SUBGOAL_THEN `(X:num->A->real) 0 x <= X n x /\ X n x <= L x` MP_TAC THENL
    [CONJ_TAC THENL
     [SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
      [REWRITE_TAC[REAL_LE_REFL];
       MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(X:num->A->real) n x` THEN
       ASM_SIMP_TAC[]];
      ASM_SIMP_TAC[]];
     REAL_ARITH_TAC];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `((\n. (L x - (X:num->A->real) n x) * indicator_fn A x) --->
                   (L x - L x) * indicator_fn A x) sequentially` MP_TAC THENL
    [MATCH_MP_TAC REALLIM_MUL THEN REWRITE_TAC[REALLIM_CONST] THEN
     MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
     ASM_SIMP_TAC[];
     REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO]]];
   REWRITE_TAC[EXPECTATION_CONST] THEN SIMP_TAC[]]);;

(* Pointwise limit of G-measurable functions is G-measurable.  Mirror of      *)
(* RANDOM_VARIABLE_POINTWISE_LIMIT with measurable_wrt/G in place of           *)
(* random_variable/prob_events: the level set {Y <= a} is the countable        *)
(* combination INTERS_m UNIONS_N INTERS_{n>=N} {Y_seq n < a + inv(SUC m)},     *)
(* and G is a sigma-algebra so it is closed under those countable operations.  *)
let MEASURABLE_WRT_REALLIM = prove
 (`!p:A prob_space G Y Y_seq.
     sub_sigma_algebra p G /\
     (!n. measurable_wrt p G (Y_seq n)) /\
     (!x. x IN prob_carrier p ==> ((\n. Y_seq n x) ---> Y x) sequentially)
     ==> measurable_wrt p G Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  REWRITE_TAC[measurable_wrt] THEN
  X_GEN_TAC `a:real` THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ Y x <= a} =
     INTERS (IMAGE (\m. UNIONS (IMAGE (\N.
       INTERS (IMAGE (\n. {x | x IN prob_carrier p /\
         Y_seq n x < a + inv(&(SUC m))}) {n | n >= N})) (:num))) (:num))`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; INTERS_IMAGE; UNIONS_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN X_GEN_TAC `m:num` THEN
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
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN prob_carrier p` ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
     DISCH_THEN(X_CHOOSE_THEN `N:num` ASSUME_TAC) THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
     REWRITE_TAC[GE; LE_REFL] THEN STRIP_TAC;
     ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    ABBREV_TAC `eps = (Y (x:A) - a) / &2` THEN
    SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL
    [EXPAND_TAC "eps" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `inv(eps:real)` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `mm:num`) THEN
    SUBGOAL_THEN `((\n. Y_seq n (x:A)) ---> Y x) sequentially` MP_TAC THENL
    [FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` ASSUME_TAC) THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `mm:num` th) THEN
      DISCH_THEN(X_CHOOSE_THEN `N1:num` ASSUME_TAC)) THEN
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
  MATCH_MP_TAC SIGMA_ALGEBRA_INTERS_COUNTABLE THEN
  REPEAT CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
   X_GEN_TAC `m:num` THEN BETA_TAC THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_UNION_COUNTABLE THEN
   REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `N:num` THEN BETA_TAC THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_INTERS_COUNTABLE THEN
    REPEAT CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
     X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC MEASURABLE_WRT_STRICT_LT THEN
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

(* ------------------------------------------------------------------------- *)
(* Conditional Monotone Convergence Theorem for gen_cond_exp.                *)
(* If 0 <= X_n increases to L (all integrable), then E[X_n|G] -> E[L|G] a.s. *)
(* Built in three steps: a pure dominated-convergence helper for a nonneg    *)
(* decreasing-to-0 integrable sequence; the heart, that the conditional      *)
(* expectations of such a sequence tend to 0 a.s.; and the main wrapper.     *)
(* ------------------------------------------------------------------------- *)

(* For a nonnegative decreasing-to-0 integrable sequence, the integral -> 0. *)
let DECR_INTEGRAL_TENDS_0 = prove
 (`!p:A prob_space D.
     (!n. integrable p (D n)) /\
     (!n x. x IN prob_carrier p ==> &0 <= D n x) /\
     (!n x. x IN prob_carrier p ==> D (SUC n) x <= D n x) /\
     (!x. x IN prob_carrier p ==> ((\n. D n x) ---> &0) sequentially)
     ==> ((\n. expectation p (D n)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> D n x <= D 0 x` ASSUME_TAC THENL
  [INDUCT_TAC THENL
   [REWRITE_TAC[REAL_LE_REFL];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(D:num->A->real) n x` THEN
    ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`; `D:num->A->real`;
    `\x:A. &0`; `(D:num->A->real) 0`] DOMINATED_CONVERGENCE)) THEN
  REWRITE_TAC[EXPECTATION_CONST] THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN DISCH_TAC THEN
   REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
   ASM_MESON_TAC[REAL_LE_TRANS; REAL_NOT_LE; REAL_LT_IMP_LE];
   SIMP_TAC[]]);;

(* As DECR_INTEGRAL_TENDS_0 but the pointwise convergence need hold only a.s.  *)
let DECR_INTEGRAL_TENDS_0_AE = prove
 (`!p:A prob_space D.
     (!n. integrable p (D n)) /\
     (!n x. x IN prob_carrier p ==> &0 <= D n x) /\
     (!n x. x IN prob_carrier p ==> D (SUC n) x <= D n x) /\
     almost_surely p {x | ((\n. D n x) ---> &0) sequentially}
     ==> ((\n. expectation p (D n)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> D n x <= D 0 x` ASSUME_TAC THENL
  [INDUCT_TAC THENL
   [REWRITE_TAC[REAL_LE_REFL];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(D:num->A->real) n x` THEN
    ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`; `D:num->A->real`;
    `\x:A. &0`; `(D:num->A->real) 0`] DOMINATED_CONVERGENCE_AE)) THEN
  REWRITE_TAC[EXPECTATION_CONST] THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN DISCH_TAC THEN
    REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[REAL_LE_TRANS; REAL_NOT_LE; REAL_LT_IMP_LE];
    REWRITE_TAC[RANDOM_VARIABLE_CONST];
    REWRITE_TAC[REAL_ABS_NUM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
   SIMP_TAC[]]);;

(* Multiplying by the indicator of a co-null set preserves the expectation.  *)
let EXPECTATION_MUL_INDICATOR_CONULL = prove
 (`!p:A prob_space f S.
     integrable p f /\ S IN prob_events p /\
     prob p (prob_carrier p DIFF S) = &0
     ==> expectation p (\x. f x * indicator_fn S x) = expectation p f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `prob_carrier p DIFF (S:A->bool) IN prob_events p` ASSUME_TAC THENL
  [ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `f:A->real`; `prob_carrier p DIFF (S:A->bool)`]
    EXPECTATION_MUL_INDICATOR_ZERO_PROB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\x:A. f x * indicator_fn (S:A->bool) x`;
    `\x:A. f x * indicator_fn (prob_carrier p DIFF (S:A->bool)) x`]
    EXPECTATION_ADD) THEN
  ASM_SIMP_TAC[INTEGRABLE_MUL_INDICATOR_FN; REAL_ADD_RID] THEN
  SUBGOAL_THEN
   `expectation p (\x:A. f x * indicator_fn (S:A->bool) x +
                         f x * indicator_fn (prob_carrier p DIFF S) x) =
    expectation p f` (fun th -> REWRITE_TAC[th]) THENL
  [MATCH_MP_TAC EXPECTATION_EXT THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[indicator_fn; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; REAL_ADD_LID];
   MESON_TAC[]]);;

(* The heart: for a nonneg decreasing-to-0 integrable sequence D_n, the       *)
(* conditional expectations E[D_n|G] tend to 0 almost surely.                 *)
let GEN_COND_EXP_DECR_TENDS_0 = prove
 (`!p:A prob_space G D.
     sub_sigma_algebra p G /\
     (!n. integrable p (D n)) /\
     (!n x. x IN prob_carrier p ==> &0 <= D n x) /\
     (!n x. x IN prob_carrier p ==> D (SUC n) x <= D n x) /\
     almost_surely p {x | ((\n. D n x) ---> &0) sequentially}
     ==> almost_surely p
           {x | ((\n. gen_cond_exp p G (D n) x) ---> &0) sequentially}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g = \n:num. \x:A. gen_cond_exp p G ((D:num->A->real) n) x` THEN
  SUBGOAL_THEN `!n:num. integrable p ((g:num->A->real) n)` ASSUME_TAC THENL
  [EXPAND_TAC "g" THEN GEN_TAC THEN REWRITE_TAC[ETA_AX] THEN
   MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `almost_surely p
       {x:A | (!n. &0 <= (g:num->A->real) n x) /\
              (!n. g (SUC n) x <= g n x)}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
   EXISTS_TAC
    `INTERS {{x:A | &0 <= (g:num->A->real) n x /\ g (SUC n) x <= g n x} |
             n IN (:num)}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC
     `{x:A | &0 <= (g:num->A->real) n x} INTER {x:A | g (SUC n) x <= g n x}` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC ALMOST_SURELY_INTER THEN CONJ_TAC THENL
     [EXPAND_TAC "g" THEN MATCH_MP_TAC GEN_COND_EXP_NONNEG THEN ASM_SIMP_TAC[];
      EXPAND_TAC "g" THEN MATCH_MP_TAC GEN_COND_EXP_MONOTONE THEN ASM_SIMP_TAC[]];
     REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN MESON_TAC[]];
    REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
    MESON_TAC[]];
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[almost_surely]) THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:A->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `good = prob_carrier p DIFF (N0:A->bool)` THEN
  SUBGOAL_THEN `(good:A->bool) IN prob_events p` ASSUME_TAC THENL
  [EXPAND_TAC "good" THEN MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN
   ASM_REWRITE_TAC[PROB_CARRIER_IN_EVENTS] THEN ASM_MESON_TAC[null_event];
   ALL_TAC] THEN
  SUBGOAL_THEN `prob p (prob_carrier p DIFF (good:A->bool)) = &0` ASSUME_TAC THENL
  [SUBGOAL_THEN `prob_carrier p DIFF (good:A->bool) = N0` SUBST1_TAC THENL
   [EXPAND_TAC "good" THEN
    SUBGOAL_THEN `(N0:A->bool) SUBSET prob_carrier p` MP_TAC THENL
    [ASM_MESON_TAC[null_event; SIGMA_ALGEBRA_SUBSET; prob_carrier;
                   PROB_SPACE_SIGMA_ALGEBRA]; ALL_TAC] THEN
    SET_TAC[];
    ASM_MESON_TAC[null_event]];
   ALL_TAC] THEN
  ABBREV_TAC `gc = \n:num. \x:A. (g:num->A->real) n x * indicator_fn good x` THEN
  SUBGOAL_THEN `!n:num. integrable p ((gc:num->A->real) n)` ASSUME_TAC THENL
  [EXPAND_TAC "gc" THEN GEN_TAC THEN
   MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!x:A. x IN good
       ==> (!n. &0 <= (g:num->A->real) n x) /\ (!n. g (SUC n) x <= g n x)`
    ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN EXPAND_TAC "good" THEN REWRITE_TAC[IN_DIFF] THEN
   STRIP_TAC THEN
   UNDISCH_TAC `{x:A | x IN prob_carrier p /\
     ~(x IN {x | (!n. &0 <= (g:num->A->real) n x) /\
                 (!n. g (SUC n) x <= g n x)})} SUBSET N0` THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> &0 <= (gc:num->A->real) n x`
    ASSUME_TAC THENL
  [MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN DISCH_TAC THEN
   EXPAND_TAC "gc" THEN REWRITE_TAC[indicator_fn] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_LE_REFL] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!n x:A. x IN prob_carrier p ==> (gc:num->A->real) (SUC n) x <= gc n x`
    ASSUME_TAC THENL
  [MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN DISCH_TAC THEN
   EXPAND_TAC "gc" THEN REWRITE_TAC[indicator_fn] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_LE_REFL] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n x:A. x IN prob_carrier p ==> (gc:num->A->real) n x <= gc 0 x`
    ASSUME_TAC THENL
  [INDUCT_TAC THENL
   [REWRITE_TAC[REAL_LE_REFL];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(gc:num->A->real) n x` THEN
    ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!x:A. x IN prob_carrier p
       ==> ?l. ((\n. (gc:num->A->real) n x) ---> l) sequentially`
    ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   MATCH_MP_TAC CONVERGENT_REAL_BOUNDED_MONOTONE THEN
   CONJ_TAC THENL
   [REWRITE_TAC[REAL_BOUNDED_POS] THEN
    EXISTS_TAC `abs((gc:num->A->real) 0 x) + &1` THEN
    CONJ_TAC THENL
    [REAL_ARITH_TAC;
     REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `m:num` THEN
     SUBGOAL_THEN `&0 <= (gc:num->A->real) m x /\ gc m x <= gc 0 x`
       (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
     ASM_SIMP_TAC[]];
    DISJ2_TAC THEN GEN_TAC THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  ABBREV_TAC `W = \x:A. reallim sequentially (\n. (gc:num->A->real) n x)` THEN
  SUBGOAL_THEN
    `!x:A. x IN prob_carrier p
       ==> ((\n. (gc:num->A->real) n x) ---> (W:A->real) x) sequentially`
    ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "W" THEN BETA_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(fun th -> MP_TAC(SELECT_RULE th)) THEN
   REWRITE_TAC[GSYM reallim];
   ALL_TAC] THEN
  SUBGOAL_THEN `random_variable p (W:A->real)` ASSUME_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_POINTWISE_LIMIT THEN
   EXISTS_TAC `gc:num->A->real` THEN ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> &0 <= (W:A->real) x` ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   MATCH_MP_TAC(ISPECL [`sequentially`; `\n. (gc:num->A->real) n x`;
                        `(W:A->real) x`; `&0`] REALLIM_LBOUND) THEN
   ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (W:A->real)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_POINTWISE_LIMIT_UI THEN
   EXISTS_TAC `gc:num->A->real` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC DOMINATED_IMP_UI THEN
   EXISTS_TAC `(gc:num->A->real) 0` THEN ASM_REWRITE_TAC[] THEN
   MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 <= (gc:num->A->real) n x /\ gc n x <= gc 0 x`
     (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation p (W:A->real) = &0` ASSUME_TAC THENL
  [SUBGOAL_THEN
     `((\n. expectation p ((gc:num->A->real) n)) ---> expectation p (W:A->real))
      sequentially` MP_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `gc:num->A->real`; `W:A->real`;
                   `(gc:num->A->real) 0`] DOMINATED_CONVERGENCE) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN DISCH_TAC THEN
     SUBGOAL_THEN `&0 <= (gc:num->A->real) n x /\ gc n x <= gc 0 x`
       (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN ASM_SIMP_TAC[];
     SIMP_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `!n. expectation p ((gc:num->A->real) n) = expectation p ((D:num->A->real) n)`
     ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "gc" THEN
    SUBGOAL_THEN
      `expectation p (\x:A. (g:num->A->real) n x * indicator_fn good x) =
       expectation p ((g:num->A->real) n)` SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_MUL_INDICATOR_CONULL THEN ASM_REWRITE_TAC[ETA_AX];
     EXPAND_TAC "g" THEN REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC GEN_COND_EXP_TOWER THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MATCH_MP_TAC(ISPECL [`sequentially`; `\n. expectation p ((D:num->A->real) n)`;
                        `expectation p (W:A->real)`; `&0`] REALLIM_UNIQUE) THEN
   ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
   MATCH_MP_TAC DECR_INTEGRAL_TENDS_0_AE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `almost_surely p {x:A | (W:A->real) x = &0}` ASSUME_TAC THENL
  [MATCH_MP_TAC EXPECTATION_NONNEG_ZERO_AE_ZERO THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC `good INTER {x:A | (W:A->real) x = &0}` THEN CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_INTER THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[almost_surely] THEN EXISTS_TAC `N0:A->bool` THEN
   ASM_REWRITE_TAC[] THEN EXPAND_TAC "good" THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF] THEN MESON_TAC[];
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
   SUBGOAL_THEN `!n. (gc:num->A->real) n x = gen_cond_exp p G ((D:num->A->real) n) x`
     ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "gc" THEN BETA_TAC THEN
    SUBGOAL_THEN `indicator_fn (good:A->bool) x = &1` SUBST1_TAC THENL
    [REWRITE_TAC[indicator_fn] THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[REAL_MUL_RID] THEN EXPAND_TAC "g" THEN REWRITE_TAC[]];
    ALL_TAC] THEN
   UNDISCH_TAC
     `!x:A. x IN prob_carrier p
        ==> ((\n. (gc:num->A->real) n x) ---> (W:A->real) x) sequentially` THEN
   DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[]]);;

(* Main result: conditional MCT.  If 0 <= X_n increases to L (all integrable) *)
(* then E[X_n|G] -> E[L|G] almost surely.  Apply DECR_TENDS_0 to D_n = L-X_n  *)
(* and translate back via GEN_COND_EXP_SUB.                                   *)
let GEN_COND_EXP_MCT = prove
 (`!p:A prob_space G X L.
     sub_sigma_algebra p G /\
     (!n. integrable p (X n)) /\ integrable p L /\
     (!n x. x IN prob_carrier p ==> X n x <= X (SUC n) x) /\
     (!n x. x IN prob_carrier p ==> X n x <= L x) /\
     (!x. x IN prob_carrier p ==> ((\n. X n x) ---> L x) sequentially)
     ==> almost_surely p
           {x | ((\n. gen_cond_exp p G (X n) x) ---> gen_cond_exp p G L x)
                sequentially}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = \n:num. \x:A. L x - (X:num->A->real) n x` THEN
  SUBGOAL_THEN `!n:num. integrable p ((D:num->A->real) n)` ASSUME_TAC THENL
  [EXPAND_TAC "D" THEN GEN_TAC THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `almost_surely p
       {x:A | ((\n. gen_cond_exp p G ((D:num->A->real) n) x) ---> &0)
              sequentially}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC GEN_COND_EXP_DECR_TENDS_0 THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN DISCH_TAC THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(X:num->A->real) n x <= L x` MP_TAC THENL
    [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN DISCH_TAC THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(X:num->A->real) n x <= X (SUC n) x` MP_TAC THENL
    [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
    REWRITE_TAC[ALMOST_SURELY_CARRIER] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN EXPAND_TAC "D" THEN
    SUBGOAL_THEN `((\n. L x - (X:num->A->real) n x) ---> L x - L x) sequentially`
      MP_TAC THENL
    [MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
     ASM_SIMP_TAC[];
     REWRITE_TAC[REAL_SUB_REFL]]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `almost_surely p
       {x:A | !n. gen_cond_exp p G ((D:num->A->real) n) x =
                  gen_cond_exp p G L x - gen_cond_exp p G (X n) x}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
   EXISTS_TAC
     `INTERS {{x:A | gen_cond_exp p G ((D:num->A->real) n) x =
                     gen_cond_exp p G L x - gen_cond_exp p G (X n) x} |
              n IN (:num)}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `(\w:A. L w - (X:num->A->real) n w) = (D:num->A->real) n`
      ASSUME_TAC THENL
    [EXPAND_TAC "D" THEN REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`; `L:A->real`;
                   `(X:num->A->real) n`] GEN_COND_EXP_SUB) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
    MESON_TAC[]];
   ALL_TAC] THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
    `{x:A | ((\n. gen_cond_exp p G ((D:num->A->real) n) x) ---> &0)
            sequentially} INTER
     {x:A | !n. gen_cond_exp p G ((D:num->A->real) n) x =
                gen_cond_exp p G L x - gen_cond_exp p G (X n) x}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_INTER THEN ASM_REWRITE_TAC[];
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
   SUBGOAL_THEN
     `(\n. gen_cond_exp p G ((X:num->A->real) n) x) =
      (\n. gen_cond_exp p G L x - gen_cond_exp p G ((D:num->A->real) n) x)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `((\n. gen_cond_exp p G L x - gen_cond_exp p G ((D:num->A->real) n) x)
       ---> gen_cond_exp p G L x - &0) sequentially` MP_TAC THENL
   [MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_SUB_RZERO]]]);;

(* Conditional Jensen for absolute value *)
let GEN_COND_EXP_ABS_BOUND = prove
 (`!p:A prob_space G (X:A->real).
    sub_sigma_algebra p G /\ integrable p X /\
    integrable p (\x. abs(X x))
    ==> almost_surely p
      {x | abs(gen_cond_exp p G X x) <=
           gen_cond_exp p G (\w. abs(X w)) x}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `X:A->real`; `(\w:A. abs((X:A->real) w))`]
    GEN_COND_EXP_MONOTONE) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `(\w:A. --((X:A->real) w))`; `(\w:A. abs((X:A->real) w))`]
    GEN_COND_EXP_MONOTONE) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_NEG THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `X:A->real`; `-- &1`] GEN_COND_EXP_CMUL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[almost_surely] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:A->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:A->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `n3:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `n1 UNION n2 UNION n3:A->bool` THEN CONJ_TAC THENL
  [REPEAT(MATCH_MP_TAC NULL_EVENT_UNION THEN CONJ_TAC) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN
  X_GEN_TAC `w:A` THEN STRIP_TAC THEN
  ASM_CASES_TAC
    `gen_cond_exp p G (\w:A. -- &1 * (X:A->real) w) w =
     -- &1 * gen_cond_exp p G X w` THENL
  [ASM_CASES_TAC
     `gen_cond_exp p G (\w:A. --(X:A->real) w) w <=
      gen_cond_exp p G (\w. abs(X w)) w` THENL
   [ASM_CASES_TAC
      `gen_cond_exp p G (X:A->real) w <=
       gen_cond_exp p G (\w:A. abs(X w)) w` THENL
    [UNDISCH_TAC
       `~(abs (gen_cond_exp p G (X:A->real) w) <=
          gen_cond_exp p G (\w. abs (X w)) w)` THEN
     REWRITE_TAC[] THEN
     SUBGOAL_THEN `gen_cond_exp p G (\w:A. --(X:A->real) w) w =
                   --gen_cond_exp p G X w` ASSUME_TAC THENL
     [SUBGOAL_THEN `(\w:A. --(X:A->real) w) = (\w. -- &1 * X w)`
        SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
     ASM_REAL_ARITH_TAC;
     DISJ2_TAC THEN DISJ2_TAC THEN
     UNDISCH_TAC `{x:A | x IN prob_carrier p /\
       ~(x IN {x | gen_cond_exp p G (X:A->real) x <=
                    gen_cond_exp p G (\w. abs(X w)) x})} SUBSET n3` THEN
     REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[]];
    DISJ2_TAC THEN DISJ1_TAC THEN
    UNDISCH_TAC `{x:A | x IN prob_carrier p /\
      ~(x IN {x | gen_cond_exp p G (\w. --(X:A->real) w) x <=
                   gen_cond_exp p G (\w. abs(X w)) x})} SUBSET n2` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]];
   DISJ1_TAC THEN
   UNDISCH_TAC `{x:A | x IN prob_carrier p /\
     ~(x IN {x | gen_cond_exp p G (\w. -- &1 * (X:A->real) w) x =
                  -- &1 * gen_cond_exp p G X x})} SUBSET n1` THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Conditional Dominated Convergence Theorem for gen_cond_exp.               *)
(* If X_n -> Z a.s. with |X_n| <= Y (Y integrable), then E[X_n|G] -> E[Z|G]  *)
(* a.s.  The route: the decreasing tail-sup envelope W_m = sup_{k>=m}|X_k-Z| *)
(* satisfies W_m -> 0 a.s., so E[W_m|G] -> 0 a.s. (conditional MCT); and     *)
(* |E[X_n|G] - E[Z|G]| <= E[W_n|G] a.s. (Jensen + monotonicity), giving the  *)
(* squeeze.  First three reusable supporting lemmas.                          *)
(* ------------------------------------------------------------------------- *)

(* sup over a tail equals B minus the inf of the reflected tail.             *)
let SUP_SEQ_VIA_INF = prove
 (`!X:num->real B N.
     (!k. k >= N ==> &0 <= X k /\ X k <= B)
     ==> sup {X k | k >= N} = B - inf {B - X k | k >= N}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~({B - (X:num->real) k | k >= N} = {})` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   MAP_EVERY EXISTS_TAC [`B - (X:num->real) N`; `N:num`] THEN
   REWRITE_TAC[GE; LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `?b. !y. y IN {B - (X:num->real) k | k >= N} ==> b <= y`
    ASSUME_TAC THENL
  [EXISTS_TAC `&0` THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC[REAL_SUB_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_SUP_UNIQUE THEN CONJ_TAC THENL
  [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH `i <= B - X ==> X <= B - i`) THEN
   MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`k:num`] THEN
    ASM_REWRITE_TAC[]];
   X_GEN_TAC `c:real` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`{B - (X:num->real) k | k >= N}`; `B - c:real`] INF_APPROACH) THEN
   ASM_REWRITE_TAC[REAL_ARITH `i < B - c <=> c < B - i`] THEN
   REWRITE_TAC[IN_ELIM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `(X:num->real) k` THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`k:num`] THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]]);;

(* Tail supremum of a sequence of nonnegative bounded RVs is an RV           *)
(* (function-bound version: bounded by an RV g, not a constant).            *)
let RANDOM_VARIABLE_SUP_SEQ_FN = prove
 (`!p:A prob_space (X:num->A->real) N g.
     (!n. random_variable p (X n)) /\ random_variable p g /\
     (!n x. x IN prob_carrier p ==> &0 <= X n x) /\
     (!n x. x IN prob_carrier p ==> X n x <= g x)
     ==> random_variable p (\x. sup {X k x | k >= N})`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM MEASURABLE_WRT_EVENTS] THEN
  MATCH_MP_TAC MEASURABLE_WRT_EQ_ON_CARRIER THEN
  EXISTS_TAC `\x:A. g x - inf {g x - (X:num->A->real) k x | k >= N}` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[MEASURABLE_WRT_EVENTS] THEN
   MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `\k:num. \x:A. g x - (X:num->A->real) k x`;
                  `N:num`] RANDOM_VARIABLE_INF_SEQ) THEN
   REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\x:A. (X:num->A->real) n x) = X n` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM]; ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_SUB_LE] THEN ASM_SIMP_TAC[]];
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC SUP_SEQ_VIA_INF THEN GEN_TAC THEN DISCH_TAC THEN
   ASM_SIMP_TAC[]]);;

(* If a_k -> 0 (nonnegative, bounded) then the tail suprema -> 0.            *)
let SUP_TAIL_TENDS_0 = prove
 (`!a:num->real C.
     (!k. &0 <= a k) /\ (!k. a k <= C) /\ ((\k. a k) ---> &0) sequentially
     ==> ((\m. sup {a k | k >= m}) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  UNDISCH_TAC `((\k. (a:num->real) k) ---> &0) sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (LABEL_TAC "conv")) THEN
  EXISTS_TAC `M:num` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ARITH `abs(s - &0) = abs s`] THEN
  SUBGOAL_THEN `&0 <= sup {(a:num->real) k | k >= m}` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(a:num->real) m` THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
   [EXISTS_TAC `C:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `z:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `m:num` THEN
    REWRITE_TAC[GE; LE_REFL]];
   ALL_TAC] THEN
  ASM_SIMP_TAC[real_abs] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `e / &2` THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `(a:num->real) m` THEN EXISTS_TAC `m:num` THEN
    REWRITE_TAC[GE; LE_REFL];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    REMOVE_THEN "conv" (MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL
    [UNDISCH_TAC `k:num >= m` THEN UNDISCH_TAC `M:num <= m` THEN ARITH_TAC;
     REWRITE_TAC[REAL_ARITH `abs(x - &0) = abs x`] THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x < e ==> x < e`) THEN
     ASM_REWRITE_TAC[]]];
   ASM_REAL_ARITH_TAC]);;

(* Conditional Dominated Convergence Theorem. *)
let GEN_COND_EXP_DCT = prove
 (`!p:A prob_space G X Z Y.
     sub_sigma_algebra p G /\
     (!n. integrable p (X n)) /\ integrable p Z /\ integrable p Y /\
     (!n x. x IN prob_carrier p ==> abs(X n x) <= Y x) /\
     (!x. x IN prob_carrier p ==> abs(Z x) <= Y x) /\
     almost_surely p {x | ((\n. X n x) ---> Z x) sequentially}
     ==> almost_surely p
           {x | ((\n. gen_cond_exp p G (X n) x) ---> gen_cond_exp p G Z x)
                sequentially}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `W = \m:num. \x:A. sup {abs((X:num->A->real) k x - Z x) | k >= m}` THEN
  SUBGOAL_THEN
    `!k:num. random_variable p (\x:A. abs((X:num->A->real) k x - Z x))`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
   MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
   CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
   ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!k x:A. x IN prob_carrier p ==> abs((X:num->A->real) k x - Z x) <= &2 * Y x`
    ASSUME_TAC THENL
  [MAP_EVERY X_GEN_TAC [`k:num`; `x:A`] THEN DISCH_TAC THEN
   SUBGOAL_THEN `abs((X:num->A->real) k x) <= Y x /\ abs(Z x) <= Y x` MP_TAC THENL
   [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. integrable p (\x:A. (X:num->A->real) n x - Z x)`
   ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. integrable p (\x:A. abs((X:num->A->real) n x - Z x))`
   ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
   EXISTS_TAC `\x:A. &2 * Y x` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_ABS] THEN
    SUBGOAL_THEN `abs((X:num->A->real) n x - Z x) <= &2 * Y x` MP_TAC THENL
    [ASM_SIMP_TAC[];
     MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> a <= t ==> a <= abs t`) THEN
     REWRITE_TAC[REAL_ABS_POS]]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m:num. random_variable p ((W:num->A->real) m)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "W" THEN BETA_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\k:num. \x:A. abs((X:num->A->real) k x - Z x)`; `m:num`;
     `\x:A. &2 * Y x`] RANDOM_VARIABLE_SUP_SEQ_FN) THEN
   REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN
    MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[REAL_ABS_POS]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!m x:A. x IN prob_carrier p
       ==> &0 <= (W:num->A->real) m x /\ W m x <= &2 * Y x`
    ASSUME_TAC THENL
  [MAP_EVERY X_GEN_TAC [`m:num`; `x:A`] THEN DISCH_TAC THEN
   EXPAND_TAC "W" THEN BETA_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs((X:num->A->real) m x - Z x)` THEN
    REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
    [EXISTS_TAC `&2 * (Y:A->real) x` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     X_GEN_TAC `z:real` THEN
     DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
     REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `m:num` THEN
     REWRITE_TAC[GE; LE_REFL]];
    MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
    [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
     EXISTS_TAC `abs((X:num->A->real) m x - Z x)` THEN EXISTS_TAC `m:num` THEN
     REWRITE_TAC[GE; LE_REFL];
     REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:real` THEN
     DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[]]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m:num. integrable p ((W:num->A->real) m)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
   EXISTS_TAC `\x:A. &2 * Y x` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= w /\ w <= t ==> abs w <= abs t`) THEN
    ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!m n x:A. n >= m /\ x IN prob_carrier p
       ==> abs((X:num->A->real) n x - Z x) <= (W:num->A->real) m x`
    ASSUME_TAC THENL
  [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `x:A`] THEN STRIP_TAC THEN
   EXPAND_TAC "W" THEN BETA_TAC THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN
   CONJ_TAC THENL
   [EXISTS_TAC `&2 * (Y:A->real) x` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `z:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `almost_surely p {x:A | ((\m. (W:num->A->real) m x) ---> &0) sequentially}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
   EXISTS_TAC `{x:A | ((\n. (X:num->A->real) n x) ---> Z x) sequentially}` THEN
   ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
   EXPAND_TAC "W" THEN BETA_TAC THEN
   MP_TAC(ISPECL [`\k:num. abs((X:num->A->real) k x - Z x)`; `&2 * (Y:A->real) x`]
     SUP_TAIL_TENDS_0) THEN
   REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_POS];
    GEN_TAC THEN ASM_SIMP_TAC[];
    REWRITE_TAC[REALLIM_NULL_ABS] THEN
    ONCE_REWRITE_TAC[GSYM REALLIM_NULL] THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `almost_surely p
       {x:A | ((\m. gen_cond_exp p G ((W:num->A->real) m) x) ---> &0)
              sequentially}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC GEN_COND_EXP_DECR_TENDS_0 THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `x:A`] THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`m:num`; `x:A`] THEN DISCH_TAC THEN
    EXPAND_TAC "W" THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
     EXISTS_TAC `abs((X:num->A->real) (SUC m) x - Z x)` THEN
     EXISTS_TAC `SUC m` THEN REWRITE_TAC[GE; LE_REFL];
     REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real` THEN
     DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `j:num >= SUC m` THEN ARITH_TAC;
     EXISTS_TAC `&2 * (Y:A->real) x` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     X_GEN_TAC `z:real` THEN
     DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[]]];
   ALL_TAC] THEN
  SUBGOAL_THEN
   `!n:num. almost_surely p
        {x:A | gen_cond_exp p G (\w. (X:num->A->real) n w - Z w) x =
               gen_cond_exp p G (X n) x - gen_cond_exp p G Z x}` ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`; `(X:num->A->real) n`;
                  `Z:A->real`] GEN_COND_EXP_SUB) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
   `!n:num. almost_surely p
        {x:A | abs(gen_cond_exp p G (\w. (X:num->A->real) n w - Z w) x)
               <= gen_cond_exp p G (\w. abs((X:num->A->real) n w - Z w)) x}`
   ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
                  `\w:A. (X:num->A->real) n w - Z w`] GEN_COND_EXP_ABS_BOUND) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
   `!n:num. almost_surely p
        {x:A | gen_cond_exp p G (\w. abs((X:num->A->real) n w - Z w)) x
               <= gen_cond_exp p G ((W:num->A->real) n) x}` ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
                  `\w:A. abs((X:num->A->real) n w - Z w)`; `(W:num->A->real) n`]
     GEN_COND_EXP_MONOTONE) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[GE; LE_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `almost_surely p
       {x:A | !n. gen_cond_exp p G (\w. (X:num->A->real) n w - Z w) x =
                  gen_cond_exp p G (X n) x - gen_cond_exp p G Z x}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
   EXISTS_TAC
     `INTERS {{x:A | gen_cond_exp p G (\w. (X:num->A->real) n w - Z w) x =
                     gen_cond_exp p G (X n) x - gen_cond_exp p G Z x} | n IN (:num)}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN ASM_SIMP_TAC[];
    REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC; IN_UNIV; IN_ELIM_THM] THEN MESON_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `almost_surely p
       {x:A | !n. abs(gen_cond_exp p G (\w. (X:num->A->real) n w - Z w) x)
                  <= gen_cond_exp p G (\w. abs((X:num->A->real) n w - Z w)) x}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
   EXISTS_TAC
     `INTERS {{x:A | abs(gen_cond_exp p G (\w. (X:num->A->real) n w - Z w) x)
                     <= gen_cond_exp p G (\w. abs((X:num->A->real) n w - Z w)) x} |
              n IN (:num)}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN ASM_SIMP_TAC[];
    REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC; IN_UNIV; IN_ELIM_THM] THEN MESON_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `almost_surely p
       {x:A | !n. gen_cond_exp p G (\w. abs((X:num->A->real) n w - Z w)) x
                  <= gen_cond_exp p G ((W:num->A->real) n) x}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
   EXISTS_TAC
     `INTERS {{x:A | gen_cond_exp p G (\w. abs((X:num->A->real) n w - Z w)) x
                     <= gen_cond_exp p G ((W:num->A->real) n) x} | n IN (:num)}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN ASM_SIMP_TAC[];
    REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC; IN_UNIV; IN_ELIM_THM] THEN MESON_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `almost_surely p
       {x:A | !n. abs(gen_cond_exp p G ((X:num->A->real) n) x -
                      gen_cond_exp p G Z x)
                  <= gen_cond_exp p G ((W:num->A->real) n) x}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
   EXISTS_TAC
     `{x:A | !n. gen_cond_exp p G (\w. (X:num->A->real) n w - Z w) x =
                 gen_cond_exp p G (X n) x - gen_cond_exp p G Z x} INTER
      {x:A | !n. abs(gen_cond_exp p G (\w. (X:num->A->real) n w - Z w) x)
                 <= gen_cond_exp p G (\w. abs((X:num->A->real) n w - Z w)) x} INTER
      {x:A | !n. gen_cond_exp p G (\w. abs((X:num->A->real) n w - Z w)) x
                 <= gen_cond_exp p G ((W:num->A->real) n) x}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_INTER THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     MATCH_MP_TAC ALMOST_SURELY_INTER THEN CONJ_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`)) THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
    `{x:A | !n. abs(gen_cond_exp p G ((X:num->A->real) n) x -
                    gen_cond_exp p G Z x)
                <= gen_cond_exp p G ((W:num->A->real) n) x} INTER
     {x:A | ((\m. gen_cond_exp p G ((W:num->A->real) m) x) ---> &0)
            sequentially}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_INTER THEN ASM_REWRITE_TAC[];
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
   ONCE_REWRITE_TAC[REALLIM_NULL] THEN
   MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
   EXISTS_TAC `\n. gen_cond_exp p G ((W:num->A->real) n) x` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   REPEAT STRIP_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC[]]);;

(* Step 7: Self-conditioning *)
let GEN_COND_EXP_SELF = prove
 (`!p:A prob_space G (X:A->real).
    sub_sigma_algebra p G /\ integrable p X /\ measurable_wrt p G X
    ==> almost_surely p {x | gen_cond_exp p G X x = X x}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC GEN_COND_EXP_AE_UNIQUE THEN
  EXISTS_TAC `G:(A->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [SUBGOAL_THEN
     `(\x:A. gen_cond_exp p G (X:A->real) x) = gen_cond_exp p G X`
     SUBST1_TAC THENL
   [REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   MATCH_MP_TAC GEN_COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN
     `(\x:A. gen_cond_exp p G (X:A->real) x) = gen_cond_exp p G X`
     SUBST1_TAC THENL
   [REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
   GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[]]);;

(* Step 8: Constant conditioning *)
let GEN_COND_EXP_CONST = prove
 (`!p:A prob_space G (c:real).
    sub_sigma_algebra p G
    ==> almost_surely p {x | gen_cond_exp p G (\w. c) x = c}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC GEN_COND_EXP_SELF THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[INTEGRABLE_CONST];
   MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_REWRITE_TAC[]]);;

(* Step 9: Iterated conditioning (tower property) *)
let GEN_COND_EXP_ITERATED = prove
 (`!p:A prob_space G H (X:A->real).
    sub_sigma_algebra p G /\ sub_sigma_algebra p H /\
    G SUBSET H /\ integrable p X
    ==> almost_surely p
      {x | gen_cond_exp p G (gen_cond_exp p H X) x =
           gen_cond_exp p G X x}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC GEN_COND_EXP_AE_UNIQUE THEN
  EXISTS_TAC `G:(A->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [SUBGOAL_THEN
     `(\x:A. gen_cond_exp p G (gen_cond_exp p H (X:A->real)) x) =
      gen_cond_exp p G (gen_cond_exp p H X)` SUBST1_TAC THENL
   [REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   MATCH_MP_TAC GEN_COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[ETA_AX] THEN
   MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN
     `(\x:A. gen_cond_exp p G (gen_cond_exp p H (X:A->real)) x) =
      gen_cond_exp p G (gen_cond_exp p H X)` SUBST1_TAC THENL
   [REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[ETA_AX] THEN
   MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN
     `(\x:A. gen_cond_exp p G (X:A->real) x) = gen_cond_exp p G X`
     SUBST1_TAC THENL
   [REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   MATCH_MP_TAC GEN_COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN
     `(\x:A. gen_cond_exp p G (X:A->real) x) = gen_cond_exp p G X`
     SUBST1_TAC THENL
   [REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
   GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `expectation p (\x:A. gen_cond_exp p G
        (gen_cond_exp p H (X:A->real)) x *
        indicator_fn (A:A->bool) x) =
      expectation p (\x. gen_cond_exp p H X x * indicator_fn A x)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `(A:A->bool) IN H` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation p (\x:A. gen_cond_exp p H (X:A->real) x *
        indicator_fn (A:A->bool) x) =
      expectation p (\x. X x * indicator_fn A x)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[]]);;

(* --- Additional measurability helpers --- *)

(* Indicator of a set in G is G-measurable *)
let MEASURABLE_WRT_INDICATOR = prove
 (`!p:A prob_space G (a:A->bool).
    sub_sigma_algebra p G /\ a IN G
    ==> measurable_wrt p G (indicator_fn a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[measurable_wrt; indicator_fn] THEN
  X_GEN_TAC `v:real` THEN
  ASM_CASES_TAC `v < &0` THENL
  [SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (if x IN a then &1 else &0) <= v} = {}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `sub_sigma_algebra (p:A prob_space) G` THEN
    REWRITE_TAC[sub_sigma_algebra] THEN STRIP_TAC THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY THEN ASM_REWRITE_TAC[]];
   ASM_CASES_TAC `&1 <= v` THENL
   [SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ (if x IN a then &1 else &0) <= v} =
       prob_carrier p` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
     GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
     DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
     COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
     UNDISCH_TAC `sub_sigma_algebra (p:A prob_space) G` THEN
     REWRITE_TAC[sub_sigma_algebra; sigma_algebra] THEN MESON_TAC[]];
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ (if x IN a then &1 else &0) <= v} =
       prob_carrier (p:A prob_space) DIFF a` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN
     X_GEN_TAC `x:A` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `(if (x:A) IN a then &1 else &0) <= v` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
     SUBGOAL_THEN `prob_carrier (p:A prob_space) = UNIONS G` SUBST1_TAC THENL
     [UNDISCH_TAC `sub_sigma_algebra (p:A prob_space) G` THEN
      REWRITE_TAC[sub_sigma_algebra] THEN MESON_TAC[];
      UNDISCH_TAC `sub_sigma_algebra (p:A prob_space) G` THEN
      REWRITE_TAC[sub_sigma_algebra; sigma_algebra] THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]]]]]);;

(* Finite sum of G-measurable functions is G-measurable *)
let MEASURABLE_WRT_SUM = prove
 (`!p:A prob_space G (f:num->A->real) n.
    sub_sigma_algebra p G /\ (!k. k <= n ==> measurable_wrt p G (f k))
    ==> measurable_wrt p G (\x. sum(0..n) (\k. f k x))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [STRIP_TAC THEN
   SUBGOAL_THEN `(\x:A. sum(0..0) (\k. (f:num->A->real) k x)) = f 0`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; SUM_CLAUSES_NUMSEG]; ALL_TAC] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
   STRIP_TAC THEN
   SUBGOAL_THEN
     `(\x:A. sum(0..SUC n) (\k. (f:num->A->real) k x)) =
      (\x. sum(0..n) (\k. f k x) + f (SUC n) x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; SUM_CLAUSES_NUMSEG; LE_0]; ALL_TAC] THEN
   MATCH_MP_TAC MEASURABLE_WRT_ADD THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `(\x:A. (f:num->A->real) (SUC n) x) = f(SUC n)`
      SUBST1_TAC THENL
    [REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]]);;

(* Product of indicator with G-measurable function is G-measurable *)
let MEASURABLE_WRT_MUL_INDICATOR = prove
 (`!p:A prob_space G (a:A->bool) (f:A->real).
    sub_sigma_algebra p G /\ a IN G /\ measurable_wrt p G f
    ==> measurable_wrt p G (\x. indicator_fn a x * f x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[measurable_wrt; indicator_fn] THEN
  X_GEN_TAC `v:real` THEN
  ASM_CASES_TAC `v < &0` THENL
  [SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (if x IN a then &1 else &0) * f x <= v} =
      a INTER {x | x IN prob_carrier p /\ (f:A->real) x <= v}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN EQ_TAC THENL
    [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `(if (x:A) IN a then &1 else &0) * (f:A->real) x <= v` THEN
     ASM_CASES_TAC `(x:A) IN a` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[REAL_MUL_LID];
      REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC];
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[REAL_MUL_LID]];
    SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
    [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_INTER THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `measurable_wrt (p:A prob_space) G (f:A->real)` THEN
    REWRITE_TAC[measurable_wrt] THEN DISCH_THEN(MP_TAC o SPEC `v:real`) THEN
    REWRITE_TAC[]];
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (if x IN a then &1 else &0) * f x <= v} =
      (prob_carrier p DIFF a) UNION
      (a INTER {x | x IN prob_carrier p /\ (f:A->real) x <= v})`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION; IN_DIFF; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN EQ_TAC THENL
    [STRIP_TAC THEN ASM_CASES_TAC `(x:A) IN a` THENL
     [DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(if (x:A) IN a then &1 else &0) * (f:A->real) x <= v` THEN
      ASM_REWRITE_TAC[REAL_MUL_LID];
      DISJ1_TAC THEN ASM_REWRITE_TAC[]];
     DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_MUL_LID]]];
    SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
    [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_UNION THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_COMPL THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `measurable_wrt (p:A prob_space) G (f:A->real)` THEN
     REWRITE_TAC[measurable_wrt] THEN DISCH_THEN(MP_TAC o SPEC `v:real`) THEN
     REWRITE_TAC[]]]]);;

(* Take out what is known -- indicator case:
   E[1_A * X | G] = 1_A * E[X|G] a.s. when A IN G *)
let GEN_COND_EXP_TAKE_OUT_INDICATOR = prove
 (`!p:A prob_space G (a:A->bool) (X:A->real).
    sub_sigma_algebra p G /\ a IN G /\ integrable p X
    ==> almost_surely p
      {x | gen_cond_exp p G (\w. indicator_fn a w * X w) x =
           indicator_fn a x * gen_cond_exp p G X x}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC GEN_COND_EXP_AE_UNIQUE THEN
  EXISTS_TAC `G:(A->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(a:A->bool) IN prob_events p` ASSUME_TAC THENL
  [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
   EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\w:A. indicator_fn a w * (X:A->real) w)`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `(\w:A. indicator_fn a w * (X:A->real) w) =
                  (\w. X w * indicator_fn a w)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [(* measurable_wrt gen_cond_exp LHS *)
   SUBGOAL_THEN
     `(\x:A. gen_cond_exp p G (\w. indicator_fn a w * (X:A->real) w) x) =
      gen_cond_exp p G (\w. indicator_fn a w * X w)` SUBST1_TAC THENL
   [REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   MATCH_MP_TAC GEN_COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[];
   (* integrable gen_cond_exp LHS *)
   SUBGOAL_THEN
     `(\x:A. gen_cond_exp p G (\w. indicator_fn a w * (X:A->real) w) x) =
      gen_cond_exp p G (\w. indicator_fn a w * X w)` SUBST1_TAC THENL
   [REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
   (* measurable_wrt RHS *)
   MATCH_MP_TAC MEASURABLE_WRT_MUL_INDICATOR THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `(\x:A. gen_cond_exp p G (X:A->real) x) = gen_cond_exp p G X`
     SUBST1_TAC THENL
   [REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   MATCH_MP_TAC GEN_COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[];
   (* integrable RHS *)
   SUBGOAL_THEN
     `(\x:A. indicator_fn a x * gen_cond_exp p G (X:A->real) x) =
      (\x. gen_cond_exp p G X x * indicator_fn a x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `(\x:A. gen_cond_exp p G (X:A->real) x) = gen_cond_exp p G X`
     SUBST1_TAC THENL
   [REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
   (* Conditioning property *)
   X_GEN_TAC `B:A->bool` THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `expectation p
       (\x:A. gen_cond_exp p G (\w. indicator_fn a w * (X:A->real) w) x *
              indicator_fn B x) =
      expectation p (\x. (indicator_fn a x * X x) * indicator_fn B x)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `(\x:A. (indicator_fn a x * (X:A->real) x) * indicator_fn B x) =
      (\x. X x * indicator_fn (a INTER B) x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; indicator_fn; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN a` THEN ASM_CASES_TAC `(x:A) IN B` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `(\x:A. (indicator_fn a x * gen_cond_exp p G (X:A->real) x) *
             indicator_fn B x) =
      (\x. gen_cond_exp p G X x * indicator_fn (a INTER B) x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; indicator_fn; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN a` THEN ASM_CASES_TAC `(x:A) IN B` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_INTER THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Gap 2: Martingale convergence for general (integrable) submartingales     *)
(* Lifts SIMPLE_MARTINGALE_CONVERGENCE_L1_BOUNDED etc. from                  *)
(* simple_submartingale to submartingale.                                     *)
(* ========================================================================= *)

(* {x | carrier /\ X x <= v} IN prob_events for random_variable *)
let RV_LE_EVENT = prove
 (`!p:A prob_space (X:A->real) v.
     random_variable p X
     ==> {x | x IN prob_carrier p /\ X x <= v} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
  DISCH_THEN(MP_TAC o SPEC `v:real`) THEN REWRITE_TAC[]);;

(* ---- Step 2: Multi-step submartingale inequality ---- *)

let SUBMARTINGALE_MULTI_STEP = prove
 (`!p:A prob_space FF (X:num->A->real) m n A.
     submartingale p FF X /\ m <= n /\ A IN FF m
     ==> expectation p (\x. X m x * indicator_fn A x) <=
         expectation p (\x. X n x * indicator_fn A x)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  GEN_TAC THEN INDUCT_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[LE] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
   REAL_ARITH_TAC;
   GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
   REWRITE_TAC[LE] THEN
   DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `expectation (p:A prob_space)
      (\x. (X:num->A->real) n x * indicator_fn A x)` THEN
    CONJ_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     SUBGOAL_THEN `(A:A->bool) IN (FF:num->(A->bool)->bool) n`
       ASSUME_TAC THENL
     [ASM_MESON_TAC[filtration; submartingale; SUBSET];
      ASM_MESON_TAC[submartingale]]]]]);;

(* ---- Step 3: Pos part of submartingale is submartingale ---- *)

let SUBMARTINGALE_POS_PART = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real).
     submartingale p FF X
     ==> submartingale p FF (\n x. pos_part(X n x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  REWRITE_TAC[submartingale] THEN REPEAT CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   (* adapted *)
   REWRITE_TAC[adapted; measurable_wrt] THEN X_GEN_TAC `nn:num` THEN
   X_GEN_TAC `v:real` THEN REWRITE_TAC[pos_part] THEN
   ASM_CASES_TAC `v < &0` THENL
   [SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ real_max ((X:num->A->real) nn x) (&0) <= v} =
       {}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
     GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC) THEN
     REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY THEN
     ASM_MESON_TAC[filtration; sub_sigma_algebra]];
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\ real_max ((X:num->A->real) nn x) (&0) <= v} =
       {x | x IN prob_carrier p /\ X nn x <= v}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
     ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [adapted]) THEN
     REWRITE_TAC[measurable_wrt] THEN
     DISCH_THEN(MP_TAC o SPEC `nn:num`) THEN
     DISCH_THEN(ACCEPT_TAC o SPEC `v:real`)]];
   (* integrable *)
   GEN_TAC THEN REWRITE_TAC[pos_part] THEN
   MATCH_MP_TAC INTEGRABLE_POS_PART THEN
   REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
   (* submartingale inequality: E[max(X_{n+1},0)*1_A] >= E[max(X_n,0)*1_A] *)
   MAP_EVERY X_GEN_TAC [`nn:num`; `a:A->bool`] THEN DISCH_TAC THEN
   REWRITE_TAC[pos_part] THEN
   SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space) ((FF:num->(A->bool)->bool) nn)`
     ASSUME_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
   SUBGOAL_THEN `measurable_wrt (p:A prob_space) ((FF:num->(A->bool)->bool) nn)
     ((X:num->A->real) nn)` ASSUME_TAC THENL
   [ASM_MESON_TAC[adapted]; ALL_TAC] THEN
   SUBGOAL_THEN `sigma_algebra ((FF:num->(A->bool)->bool) nn)` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
   (* Key: B = a INTER {X_n >= 0}; chain E[max(Xn,0)*1a]=E[Xn*1B]<=E[Xsn*1B]<=E[max(Xsn,0)*1a] *)
   ABBREV_TAC `B = a INTER
     {x:A | x IN prob_carrier p /\ (X:num->A->real) nn x >= &0}` THEN
   SUBGOAL_THEN `(B:A->bool) IN (FF:num->(A->bool)->bool) nn` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC SIGMA_ALGEBRA_INTER THEN
    REPEAT CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[];
     MATCH_MP_TAC MEASURABLE_WRT_GE THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* E[max(Xn,0)*1a] = E[Xn*1B]: on B, max(Xn,0)=Xn; on a\B, max(Xn,0)=0 *)
   SUBGOAL_THEN
     `expectation (p:A prob_space)
        (\x. max ((X:num->A->real) nn x) (&0) * indicator_fn a x) =
      expectation p (\x. X nn x * indicator_fn B x)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[indicator_fn] THEN EXPAND_TAC "B" THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    ASM_CASES_TAC `(x:A) IN a` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_max] THEN REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   (* E[Xn*1B] <= E[Xsn*1B] <= E[max(Xsn,0)*1a] *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space)
     (\x. (X:num->A->real) (SUC nn) x * indicator_fn B x)` THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[submartingale];
    (* E[Xsn*1B] <= E[max(Xsn,0)*1a] by EXPECTATION_MONO *)
    MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[sub_sigma_algebra; SUBSET]];
     MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_POS_PART THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[sub_sigma_algebra; SUBSET]];
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[indicator_fn] THEN
     EXPAND_TAC "B" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
     ASM_CASES_TAC `(x:A) IN a` THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[real_max] THEN REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC]]]);;

(* ---- Step 4: General Doob Upcrossing Inequality ---- *)

(* Helper: integrability transfers when functions agree on carrier *)
let INTEGRABLE_CARRIER_AGREE = prove
 (`!p:A prob_space f g.
     integrable p g /\
     (!x. x IN prob_carrier p ==> f x = g x)
     ==> integrable p f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (f:A->real)` ASSUME_TAC THENL
  [SUBGOAL_THEN `random_variable (p:A prob_space) (g:A->real)` MP_TAC THENL
   [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
   REWRITE_TAC[random_variable] THEN DISCH_TAC THEN
   X_GEN_TAC `aa:real` THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (f:A->real) x <= aa} =
      {x | x IN prob_carrier p /\ (g:A->real) x <= aa}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  REWRITE_TAC[integrable] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?B. !h:A->real.
    simple_rv (p:A prob_space) h /\
    (!x. x IN prob_carrier p ==> &0 <= h x) /\
    (!x. x IN prob_carrier p ==> h x <= abs ((g:A->real) x))
    ==> simple_expectation p h <= B` MP_TAC THENL
  [ASM_MESON_TAC[integrable]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC `B:real` THEN
  X_GEN_TAC `h:A->real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:A->real`) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `y:A` THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `abs((f:A->real) y)` THEN
   CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[REAL_ARITH `a = b ==> abs a <= abs b`];
   REWRITE_TAC[]]);;

(* Subtracting a constant preserves submartingale property *)
let SUBMARTINGALE_SUB_CONST = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) c.
     submartingale p FF X ==>
     submartingale p FF (\n x. X n x - c)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  REWRITE_TAC[submartingale] THEN
  REPEAT CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   (* adapted *)
   REWRITE_TAC[adapted; measurable_wrt] THEN REPEAT GEN_TAC THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (X:num->A->real) n x - c <= v} =
      {x | x IN prob_carrier p /\ X n x <= v + c}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[adapted; measurable_wrt]) THEN
   ASM_REWRITE_TAC[];
   (* integrable *)
   GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
   ASM_REWRITE_TAC[ETA_AX; INTEGRABLE_CONST];
   (* inequality *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(a:A->bool) IN prob_events (p:A prob_space)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
    EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[filtration];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space)
     (\x:A. (X:num->A->real) n x * indicator_fn (a:A->bool) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space)
     (\x:A. (X:num->A->real) (SUC n) x * indicator_fn (a:A->bool) x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (indicator_fn (a:A->bool))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space)
     (\x:A. c * indicator_fn (a:A->bool) x)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `c:real`; `indicator_fn (a:A->bool)`]
     INTEGRABLE_CMUL) THEN
    ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space)
       (\x:A. ((X:num->A->real) n x - c) * indicator_fn (a:A->bool) x) =
      expectation p (\x. X n x * indicator_fn a x) - c * prob p a`
     SUBST1_TAC THENL
   [SUBGOAL_THEN
      `expectation (p:A prob_space)
        (\x:A. ((X:num->A->real) n x - c) * indicator_fn (a:A->bool) x) =
       expectation p (\x. X n x * indicator_fn a x - c * indicator_fn a x)`
      SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_EXT THEN
     X_GEN_TAC `y:A` THEN DISCH_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. (X:num->A->real) n x * indicator_fn (a:A->bool) x`;
      `\x:A. c * indicator_fn (a:A->bool) x`]
      EXPECTATION_SUB) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`p:A prob_space`; `c:real`; `indicator_fn (a:A->bool)`]
      EXPECTATION_CMUL) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[EXPECTATION_INDICATOR];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space)
       (\x:A. ((X:num->A->real) (SUC n) x - c) * indicator_fn (a:A->bool) x) =
      expectation p (\x. X (SUC n) x * indicator_fn a x) - c * prob p a`
     SUBST1_TAC THENL
   [SUBGOAL_THEN
      `expectation (p:A prob_space)
        (\x:A. ((X:num->A->real) (SUC n) x - c) *
               indicator_fn (a:A->bool) x) =
       expectation p
        (\x. X (SUC n) x * indicator_fn a x - c * indicator_fn a x)`
      SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_EXT THEN
     X_GEN_TAC `y:A` THEN DISCH_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. (X:num->A->real) (SUC n) x * indicator_fn (a:A->bool) x`;
      `\x:A. c * indicator_fn (a:A->bool) x`]
      EXPECTATION_SUB) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`p:A prob_space`; `c:real`; `indicator_fn (a:A->bool)`]
      EXPECTATION_CMUL) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[EXPECTATION_INDICATOR];
    ALL_TAC] THEN
   REWRITE_TAC[REAL_ARITH `a - d <= b - d <=> a <= b`] THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [submartingale]) THEN
   STRIP_TAC THEN ASM_MESON_TAC[]]);;

(* E[not_bet_gain of pos_part] >= 0 for general submartingale *)
let NOT_BET_GAIN_NONNEG_EXPECTATION = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b.
     submartingale p FF X /\ a < b ==>
     !n. integrable p
           (\x. not_bet_gain (\k. pos_part(X k x - a)) (&0) (b - a) n) /\
         &0 <= expectation p
           (\x. not_bet_gain (\k. pos_part(X k x - a)) (&0) (b - a) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  ABBREV_TAC `pp = \k (x:A). pos_part((X:num->A->real) k x - a)` THEN
  SUBGOAL_THEN
    `submartingale (p:A prob_space) FF (pp:num->A->real)`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `(pp:num->A->real) = (\n x. pos_part((X:num->A->real) n x - a))`
    SUBST1_TAC THENL [EXPAND_TAC "pp" THEN REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC SUBMARTINGALE_POS_PART THEN
   MATCH_MP_TAC SUBMARTINGALE_SUB_CONST THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable (p:A prob_space)
    (\x. (pp:num->A->real) n x)` ASSUME_TAC THENL
  [REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!k (x:A). pos_part((X:num->A->real) k x - a) =
    (pp:num->A->real) k x` ASSUME_TAC THENL
  [EXPAND_TAC "pp" THEN REWRITE_TAC[]; ALL_TAC] THEN
  INDUCT_TAC THENL
  [(* Base case: not_bet_gain ... 0 = &0 *)
   SUBGOAL_THEN `(\x:A. not_bet_gain (\k. (pp:num->A->real) k x)
     (&0) (b - a) 0) = (\x. &0)` (fun th -> ASM_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; not_bet_gain]; ALL_TAC] THEN
   REWRITE_TAC[INTEGRABLE_CONST] THEN
   SIMP_TAC[EXPECTATION_CONST; REAL_LE_REFL];
   (* Inductive step *)
   FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC)) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `integrable (p:A prob_space)
       (\x:A. not_bet_gain (\k. (pp:num->A->real) k x) (&0) (b - a) n) /\
      &0 <= expectation (p:A prob_space)
        (\x:A. not_bet_gain (\k. (pp:num->A->real) k x) (&0) (b - a) n)`
     STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `integrable (p:A prob_space)
       (\x:A. not_bet_gain (\k. pos_part ((X:num->A->real) k x - a))
         (&0) (b - a) n)` THEN
    UNDISCH_TAC `&0 <= expectation (p:A prob_space)
       (\x:A. not_bet_gain (\k. pos_part ((X:num->A->real) k x - a))
         (&0) (b - a) n)` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `(\x:A. not_bet_gain (\k. (pp:num->A->real) k x) (&0) (b - a) (SUC n)) =
      (\x. not_bet_gain (\k. pp k x) (&0) (b - a) n +
           (if upcrossing_phase (\k. pp k x) (&0) (b - a) n = 0
            then &1 else &0) *
           (pp (SUC n) x - pp n x))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; not_bet_gain]; ALL_TAC] THEN
   SUBGOAL_THEN
     `!x:A. upcrossing_phase (\k. (pp:num->A->real) k x) (&0) (b - a) n =
            upcrossing_phase (\k. (X:num->A->real) k x) a b n`
     (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN EXPAND_TAC "pp" THEN
    MATCH_MP_TAC UPCROSSING_PHASE_SHIFT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   ABBREV_TAC `A = {x:A | x IN prob_carrier p /\
     upcrossing_phase (\k. (X:num->A->real) k x) a b n = 0}` THEN
   SUBGOAL_THEN `(A:A->bool) IN (FF:num->(A->bool)->bool) n` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN
    MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                   `X:num->A->real`; `a:real`; `b:real`]
      UPCROSSING_PHASE_SET_IN_FILTRATION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
    STRIP_TAC THEN EXPAND_TAC "A" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `(A:A->bool) IN prob_events (p:A prob_space)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
    EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[filtration];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space)
     (\x:A. (if upcrossing_phase (\k. (X:num->A->real) k x) a b n = 0
             then &1 else &0) *
            ((pp:num->A->real) (SUC n) x - pp n x))` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CARRIER_AGREE THEN
    EXISTS_TAC `\x:A. ((pp:num->A->real) (SUC n) x - pp n x) *
      indicator_fn (A:A->bool) x` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THEN
     ASM_REWRITE_TAC[ETA_AX];
     X_GEN_TAC `y:A` THEN DISCH_TAC THEN
     EXPAND_TAC "A" THEN REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
     ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space)
     (\x:A. not_bet_gain (\k. (pp:num->A->real) k x) (&0) (b - a) n +
            (if upcrossing_phase (\k. (X:num->A->real) k x) a b n = 0
             then &1 else &0) *
            (pp (SUC n) x - pp n x))` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. not_bet_gain (\k. (pp:num->A->real) k x) (&0) (b - a) n`;
     `\x:A. (if upcrossing_phase (\k. (X:num->A->real) k x) a b n = 0
             then &1 else &0) *
            ((pp:num->A->real) (SUC n) x - pp n x)`]
     EXPECTATION_ADD) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
   MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space)
       (\x:A. (if upcrossing_phase (\k. (X:num->A->real) k x) a b n = 0
               then &1 else &0) *
              ((pp:num->A->real) (SUC n) x - pp n x)) =
      expectation p (\x. pp (SUC n) x * indicator_fn (A:A->bool) x) -
      expectation p (\x. pp n x * indicator_fn A x)`
     SUBST1_TAC THENL
   [SUBGOAL_THEN
      `expectation (p:A prob_space)
        (\x:A. (if upcrossing_phase (\k. (X:num->A->real) k x) a b n = 0
                then &1 else &0) *
               ((pp:num->A->real) (SUC n) x - pp n x)) =
       expectation p
        (\x. (pp (SUC n) x - pp n x) * indicator_fn (A:A->bool) x)`
      SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_EXT THEN
     X_GEN_TAC `y:A` THEN DISCH_TAC THEN
     EXPAND_TAC "A" THEN REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
     ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN
      `(\x:A. ((pp:num->A->real) (SUC n) x - pp n x) *
              indicator_fn (A:A->bool) x) =
       (\x. pp (SUC n) x * indicator_fn A x - pp n x * indicator_fn A x)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EXPECTATION_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
   REWRITE_TAC[REAL_SUB_LE] THEN
   MP_TAC(REWRITE_RULE[submartingale]
     (ASSUME `submartingale (p:A prob_space) FF (pp:num->A->real)`)) THEN
   STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `A:A->bool`]) THEN
   ASM_REWRITE_TAC[]]);;


(* General Doob Upcrossing Inequality *)
let DOOB_UPCROSSING_INEQUALITY = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b n.
     submartingale p FF X /\ a < b ==>
     (b - a) * expectation p (\x. &(num_upcrossings X a b n x))
     <= expectation p (\x. pos_part(X n x - a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  (* random_variable for num_upcrossings by induction *)
  SUBGOAL_THEN
    `!m. random_variable (p:A prob_space)
      (\x. &(num_upcrossings (X:num->A->real) a b m x))` ASSUME_TAC THENL
  [INDUCT_TAC THENL
   [(* Base: U_0 = 0 *)
    SUBGOAL_THEN
      `(\x:A. &(num_upcrossings (X:num->A->real) a b 0 x)) = (\x. &0)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; num_upcrossings; upcrossing_count];
     REWRITE_TAC[RANDOM_VARIABLE_CONST]];
    (* Step: U_{SUC m} agrees on carrier with U_m + indicator_fn S *)
    ABBREV_TAC `S = {x:A | x IN prob_carrier p /\
      upcrossing_phase (\k. (X:num->A->real) k x) a b m = 1 /\
      X (SUC m) x >= b}` THEN
    SUBGOAL_THEN `(S:A->bool) IN prob_events p` ASSUME_TAC THENL
    [EXPAND_TAC "S" THEN
     SUBGOAL_THEN
       `{x:A | x IN prob_carrier p /\
          upcrossing_phase (\k. (X:num->A->real) k x) a b m = 1 /\
          X (SUC m) x >= b} =
        {x | x IN prob_carrier p /\
             upcrossing_phase (\k. X k x) a b m = 1} INTER
        {x | x IN prob_carrier p /\ X (SUC m) x >= b}`
       SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
     MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
        `X:num->A->real`; `a:real`; `b:real`]
        UPCROSSING_PHASE_SET_IN_FILTRATION) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `m:num`) THEN STRIP_TAC THEN
      ASM_MESON_TAC[filtration; sub_sigma_algebra; SUBSET];
      MP_TAC(SPECL [`p:A prob_space`; `(X:num->A->real) (SUC m)`; `b:real`]
        RV_PREIMAGE_GE) THEN
      ANTS_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
       SIMP_TAC[]]];
     ALL_TAC] THEN
    REWRITE_TAC[random_variable] THEN X_GEN_TAC `c:real` THEN
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\
         &(num_upcrossings (X:num->A->real) a b (SUC m) x) <= c} =
       {x | x IN prob_carrier p /\
         &(num_upcrossings X a b m x) + indicator_fn (S:A->bool) x <= c}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
     ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN
       `&(num_upcrossings (X:num->A->real) a b (SUC m) x) =
        &(num_upcrossings X a b m x) + indicator_fn (S:A->bool) x`
       (fun th -> REWRITE_TAC[th]) THEN
     REWRITE_TAC[num_upcrossings; upcrossing_count; GSYM REAL_OF_NUM_ADD] THEN
     SUBGOAL_THEN
       `&(if upcrossing_phase (\k. (X:num->A->real) k x) a b m = 1 /\
              X (SUC m) x >= b then 1 else 0) =
        indicator_fn (S:A->bool) x`
       (fun th -> REWRITE_TAC[th]) THEN
     EXPAND_TAC "S" THEN REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
     ASM_REWRITE_TAC[] THEN
     COND_CASES_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. &(num_upcrossings (X:num->A->real) a b m x)`;
      `indicator_fn (S:A->bool)`] RANDOM_VARIABLE_ADD) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[random_variable] THEN
     DISCH_THEN(MP_TAC o SPEC `c:real`) THEN REWRITE_TAC[]]];
   ALL_TAC] THEN
  (* Integrability of num_upcrossings via INTEGRABLE_BOUNDED *)
  SUBGOAL_THEN
    `integrable (p:A prob_space)
      (\x. &(num_upcrossings (X:num->A->real) a b n x))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&n` THEN
   ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[REAL_ABS_NUM; REAL_OF_NUM_LE; num_upcrossings] THEN
   SPEC_TAC(`n:num`, `k:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[upcrossing_count; LE_0];
    REWRITE_TAC[upcrossing_count] THEN COND_CASES_TAC THEN ASM_ARITH_TAC];
   ALL_TAC] THEN
  (* Integrability of pos_part(X k - a) *)
  SUBGOAL_THEN
    `!k. integrable (p:A prob_space)
      (\x. pos_part((X:num->A->real) k x - a))` ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[pos_part] THEN
   MATCH_MP_TAC INTEGRABLE_POS_PART THEN
   MATCH_MP_TAC INTEGRABLE_SUB THEN
   ASM_REWRITE_TAC[INTEGRABLE_CONST; ETA_AX];
   ALL_TAC] THEN
  (* NOT_BET_GAIN: integrable and nonneg expectation *)
  MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
    `X:num->A->real`; `a:real`; `b:real`]
    NOT_BET_GAIN_NONNEG_EXPECTATION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
  (* E[pp_0] >= 0 *)
  SUBGOAL_THEN `&0 <= expectation (p:A prob_space)
    (\x:A. pos_part((X:num->A->real) 0 x - a))` ASSUME_TAC THENL
  [MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[pos_part] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* (b-a)*E[U] = E[(b-a)*U] by EXPECTATION_CMUL *)
  SUBGOAL_THEN
    `(b - a) * expectation (p:A prob_space)
      (\x. &(num_upcrossings (X:num->A->real) a b n x)) =
     expectation p (\x. (b - a) * &(num_upcrossings X a b n x))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC(GSYM EXPECTATION_CMUL) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Abbreviate expectation values *)
  ABBREV_TAC `Eu = expectation (p:A prob_space)
    (\x. (b - a) * &(num_upcrossings (X:num->A->real) a b n x))` THEN
  ABBREV_TAC `En = expectation (p:A prob_space)
    (\x. not_bet_gain (\k. pos_part((X:num->A->real) k x - a))
      (&0) (b - a) n)` THEN
  ABBREV_TAC `E0 = expectation (p:A prob_space)
    (\x. pos_part((X:num->A->real) 0 x - a))` THEN
  (* Eu + En + E0 <= E[ppn] *)
  SUBGOAL_THEN `Eu + En + E0 <= expectation (p:A prob_space)
    (\x. pos_part((X:num->A->real) n x - a))` ASSUME_TAC THENL
  [(* Step 1: Eu + En = E[(b-a)*U + nbg] *)
   SUBGOAL_THEN `Eu + En = expectation (p:A prob_space)
     (\x:A. (b - a) * &(num_upcrossings (X:num->A->real) a b n x) +
       not_bet_gain (\k. pos_part(X k x - a)) (&0) (b - a) n)`
     ASSUME_TAC THENL
   [EXPAND_TAC "Eu" THEN EXPAND_TAC "En" THEN
    MATCH_MP_TAC(GSYM EXPECTATION_ADD) THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* Step 2: (Eu + En) + E0 = E[sum] *)
   SUBGOAL_THEN `Eu + En + E0 = expectation (p:A prob_space)
     (\x:A. (b - a) * &(num_upcrossings (X:num->A->real) a b n x) +
       not_bet_gain (\k. pos_part(X k x - a)) (&0) (b - a) n +
       pos_part(X 0 x - a))`
     SUBST1_TAC THENL
   [ASM_REWRITE_TAC[REAL_ADD_ASSOC] THEN EXPAND_TAC "E0" THEN
    MATCH_MP_TAC(GSYM EXPECTATION_ADD) THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* Step 3: E[sum] <= E[ppn] from EXPECTATION_MONO *)
   MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC) THEN
    MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`X:num->A->real`; `a:real`; `b:real`; `n:num`; `x:A`]
      UPCROSSING_POINTWISE_SUM_BOUND) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ---- Step 5: General Maximal Inequalities ---- *)

(* Doob maximal inequality for nonneg submartingales: direct first-crossing *)
let NONNEG_SUBMARTINGALE_MAXIMAL = prove
 (`!p:A prob_space FF (X:num->A->real) c n.
     submartingale p FF X /\ &0 < c /\
     (!m x. x IN prob_carrier p ==> &0 <= X m x)
     ==> c * prob p {x | x IN prob_carrier p /\ running_max X n x >= c}
         <= expectation p (X n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation (p:A prob_space)
    (\x. (X:num->A->real) n x * indicator_fn
      {y | y IN prob_carrier p /\ running_max X n y >= c} x)` THEN
  CONJ_TAC THENL
  [(* Strong maximal: c * P(max >= c) <= E[X n * 1_{max >= c}] *)
   SPEC_TAC(`n:num`, `n:num`) THEN INDUCT_TAC THENL
   [(* Base: running_max X 0 = X 0 *)
    REWRITE_TAC[running_max] THEN
    ABBREV_TAC `A0 = {y:A | y IN prob_carrier p /\
      (X:num->A->real) 0 y >= c}` THEN
    SUBGOAL_THEN `(A0:A->bool) IN prob_events (p:A prob_space)`
      ASSUME_TAC THENL
    [EXPAND_TAC "A0" THEN MATCH_MP_TAC RV_PREIMAGE_GE THEN
     REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `expectation (p:A prob_space)
      (\x:A. c * indicator_fn (A0:A->bool) x)` THEN
    CONJ_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`; `c:real`; `indicator_fn (A0:A->bool)`]
      EXPECTATION_CMUL) THEN
     ANTS_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ETA_AX] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ASM_SIMP_TAC[EXPECTATION_INDICATOR; REAL_LE_REFL]];
     MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`p:A prob_space`; `c:real`;
        `indicator_fn (A0:A->bool)`] INTEGRABLE_CMUL) THEN
      ANTS_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[ETA_AX]];
      MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
      ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
      REWRITE_TAC[indicator_fn] THEN
      COND_CASES_TAC THENL
      [REWRITE_TAC[REAL_MUL_RID] THEN
       UNDISCH_TAC `(y:A) IN (A0:A->bool)` THEN EXPAND_TAC "A0" THEN
       REWRITE_TAC[IN_ELIM_THM; real_ge] THEN REAL_ARITH_TAC;
       REAL_ARITH_TAC]]];
    (* Inductive step *)
    ABBREV_TAC
      `A_n = {x:A | x IN prob_carrier p /\
        running_max (X:num->A->real) n x >= c}` THEN
    ABBREV_TAC
      `B = {x:A | x IN prob_carrier p /\
        (X:num->A->real) (SUC n) x >= c} DIFF A_n` THEN
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\
        running_max (X:num->A->real) (SUC n) x >= c} = A_n UNION B`
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
    SUBGOAL_THEN `(A_n:A->bool) IN (FF:num->(A->bool)->bool) n`
      ASSUME_TAC THENL
    [EXPAND_TAC "A_n" THEN
     MATCH_MP_TAC RUNNING_MAX_EXCEEDS_IN_FILTRATION THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `(A_n:A->bool) IN prob_events (p:A prob_space)`
      ASSUME_TAC THENL
    [ASM_MESON_TAC[filtration; sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(B:A->bool) IN prob_events (p:A prob_space)`
      ASSUME_TAC THENL
    [EXPAND_TAC "B" THEN MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC RV_PREIMAGE_GE THEN REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `prob (p:A prob_space) (A_n UNION B) = prob p A_n + prob p B`
      SUBST1_TAC THENL
    [MATCH_MP_TAC PROB_ADDITIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
      `expectation (p:A prob_space)
        (\x. (X:num->A->real) (SUC n) x *
          indicator_fn (A_n UNION B) x) =
       expectation p (\x. X (SUC n) x * indicator_fn A_n x) +
       expectation p (\x. X (SUC n) x * indicator_fn B x)`
      SUBST1_TAC THENL
    [SUBGOAL_THEN
       `expectation (p:A prob_space)
         (\x. (X:num->A->real) (SUC n) x *
           indicator_fn (A_n UNION B) x) =
        expectation p
         (\x. X (SUC n) x * indicator_fn A_n x +
              X (SUC n) x * indicator_fn B x)`
       SUBST1_TAC THENL
     [MATCH_MP_TAC EXPECTATION_EXT THEN
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
      REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC INDICATOR_FN_DISJOINT_UNION THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC EXPECTATION_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
      ASM_REWRITE_TAC[ETA_AX]];
     ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
    [(* c * P(A_n) <= E[X(SUC n) * 1_{A_n}] via IH + submartingale *)
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `expectation (p:A prob_space)
       (\x. (X:num->A->real) n x * indicator_fn (A_n:A->bool) x)` THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MP_TAC(REWRITE_RULE[submartingale]
        (ASSUME `submartingale (p:A prob_space) FF (X:num->A->real)`)) THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `A_n:A->bool`]) THEN
      ASM_REWRITE_TAC[]];
     (* c * P(B) <= E[X(SUC n) * 1_B] *)
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `expectation (p:A prob_space)
       (\x:A. c * indicator_fn (B:A->bool) x)` THEN
     CONJ_TAC THENL
     [MP_TAC(ISPECL [`p:A prob_space`; `c:real`;
        `indicator_fn (B:A->bool)`] EXPECTATION_CMUL) THEN
      ANTS_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[ETA_AX] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
       ASM_SIMP_TAC[EXPECTATION_INDICATOR; REAL_LE_REFL]];
      MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
      [MP_TAC(ISPECL [`p:A prob_space`; `c:real`;
         `indicator_fn (B:A->bool)`] INTEGRABLE_CMUL) THEN
       ANTS_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[ETA_AX]];
       MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
       ASM_REWRITE_TAC[ETA_AX];
       X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
       REWRITE_TAC[indicator_fn] THEN
       COND_CASES_TAC THENL
       [REWRITE_TAC[REAL_MUL_RID] THEN
        UNDISCH_TAC `(y:A) IN (B:A->bool)` THEN EXPAND_TAC "B" THEN
        REWRITE_TAC[IN_DIFF; IN_ELIM_THM; real_ge] THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC]]]]];
   (* E[X n * 1_{max >= c}] <= E[X n] since X >= 0 *)
   SUBGOAL_THEN
     `{y:A | y IN prob_carrier p /\
       running_max (X:num->A->real) n y >= c} IN prob_events p`
     ASSUME_TAC THENL
   [MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                   `X:num->A->real`; `c:real`; `n:num`]
     RUNNING_MAX_EXCEEDS_IN_FILTRATION) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[filtration; sub_sigma_algebra; SUBSET];
    ALL_TAC] THEN
   MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
    ASM_REWRITE_TAC[ETA_AX];
    ASM_REWRITE_TAC[ETA_AX];
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO] THENL
    [REWRITE_TAC[REAL_LE_REFL];
     ASM_MESON_TAC[]]]]);;

(* Maximal inequality for pos part *)
let DOOB_MAXIMAL_POS_PART = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) c n C.
     submartingale p FF X /\ &0 < c /\
     (!n. expectation p (\x. abs(X n x)) <= C)
     ==> c * prob p {x | x IN prob_carrier p /\
                         running_max (\m x. pos_part(X m x)) n x >= c}
         <= C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `submartingale (p:A prob_space) FF
    (\m (x:A). pos_part((X:num->A->real) m x))` ASSUME_TAC THENL
  [MATCH_MP_TAC SUBMARTINGALE_POS_PART THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m. integrable (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL
  [REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!m. integrable (p:A prob_space)
    ((\m (x:A). pos_part((X:num->A->real) m x)) m)` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation (p:A prob_space)
    (\x:A. pos_part((X:num->A->real) n x))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC NONNEG_SUBMARTINGALE_MAXIMAL THEN
   EXISTS_TAC `FF:num->(A->bool)->bool` THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN REWRITE_TAC[POS_PART_POS];
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space) (\x:A. abs((X:num->A->real) n x))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN BETA_TAC THEN
     REWRITE_TAC[];
     MATCH_MP_TAC INTEGRABLE_ABS THEN REWRITE_TAC[ETA_AX] THEN
     ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[pos_part] THEN REAL_ARITH_TAC];
    ASM_REWRITE_TAC[]]]);;

let ADAPTED_IMP_RV = prove
 (`!p:A prob_space FF (X:num->A->real).
     filtration p FF /\ adapted p FF X
     ==> !n. random_variable p (X n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[filtration; adapted; measurable_wrt] THEN
  STRIP_TAC THEN GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[sub_sigma_algebra; random_variable] THEN
  STRIP_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real`) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(FF:num->(A->bool)->bool) n SUBSET prob_events (p:A prob_space)`
    MP_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Neg part maximal inequality *)
let SUBMARTINGALE_NEG_PART_MAXIMAL = prove
 (`!p:A prob_space FF X c (n:num) C.
     submartingale p FF X /\ &0 < c /\
     (!n. expectation p (\x. abs(X n x)) <= C)
     ==> c * prob p {x | x IN prob_carrier p /\
                         running_max (\m x. max (--(X m x)) (&0)) n x >= c}
         <= &2 * C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF X` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL
  [REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  (* Neg part process is adapted *)
  SUBGOAL_THEN
    `adapted (p:A prob_space) FF (\m x. max (--(X:num->A->real) m x) (&0))`
    ASSUME_TAC THENL
  [REWRITE_TAC[adapted; measurable_wrt] THEN REPEAT GEN_TAC THEN
   ASM_CASES_TAC `&0 <= v` THENL
   [SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\
              max (--(X:num->A->real) n x) (&0) <= v} =
       {x | x IN prob_carrier p /\ X n x >= --v}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
     EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     POP_ASSUM MP_TAC THEN UNDISCH_TAC `&0 <= v` THEN REAL_ARITH_TAC;
     MATCH_MP_TAC MEASURABLE_WRT_GE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[submartingale; filtration]; ALL_TAC] THEN
     REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[submartingale; adapted]];
    SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\
              max (--(X:num->A->real) n x) (&0) <= v} = {}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN GEN_TAC THEN
     DISCH_THEN(CONJUNCTS_THEN2 (fun _ -> ALL_TAC) MP_TAC) THEN
     UNDISCH_TAC `~(&0 <= v)` THEN REAL_ARITH_TAC;
     SUBGOAL_THEN `sigma_algebra ((FF:num->(A->bool)->bool) n)`
       MP_TAC THENL
     [ASM_MESON_TAC[submartingale; filtration; sub_sigma_algebra];
      ALL_TAC] THEN
     REWRITE_TAC[sigma_algebra] THEN STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `{}:(A->bool)->bool`) THEN
     REWRITE_TAC[EMPTY_SUBSET; COUNTABLE_EMPTY; UNIONS_0]]];
   ALL_TAC] THEN
  ABBREV_TAC
    `A = \n. {x:A | x IN prob_carrier p /\
                    running_max (\m x. max (--((X:num->A->real) m x)) (&0)) n x >= c}` THEN
  ABBREV_TAC `B = \n. prob_carrier (p:A prob_space) DIFF (A:num->(A->bool)) n` THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\
            running_max (\m x. max (--((X:num->A->real) m x)) (&0)) n x >= c} =
     (A:num->(A->bool)) n`
    SUBST1_TAC THENL
  [EXPAND_TAC "A" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m. (A:num->(A->bool)) m IN (FF:num->(A->bool)->bool) m`
    ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "A" THEN
   MATCH_MP_TAC RUNNING_MAX_EXCEEDS_IN_FILTRATION THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m. (A:num->(A->bool)) m IN prob_events p` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
   EXISTS_TAC `(FF:num->(A->bool)->bool) m` THEN
   ASM_MESON_TAC[filtration; submartingale];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m. (B:num->(A->bool)) m IN prob_events p` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "B" THEN
   MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN
   ASM_REWRITE_TAC[PROB_CARRIER_IN_EVENTS];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m. (B:num->(A->bool)) m IN (FF:num->(A->bool)->bool) m`
    ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "B" THEN
   SUBGOAL_THEN `prob_carrier (p:A prob_space) DIFF (A:num->(A->bool)) m =
                  UNIONS ((FF:num->(A->bool)->bool) m) DIFF A m` SUBST1_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_MESON_TAC[filtration; sub_sigma_algebra];
    MATCH_MP_TAC SIGMA_ALGEBRA_COMPL THEN
    ASM_MESON_TAC[filtration; sub_sigma_algebra]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!m. integrable (p:A prob_space)
    (\x. (X:num->A->real) m x * indicator_fn ((B:num->(A->bool)) m) x)`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
   ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  (* Upper bound: E[X_m * 1_{B_m}] <= C *)
  SUBGOAL_THEN
    `!m. expectation (p:A prob_space)
           (\x. (X:num->A->real) m x * indicator_fn ((B:num->(A->bool)) m) x) <= C`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space)
        (\x. (X:num->A->real) m x * indicator_fn ((B:num->(A->bool)) m) x) <=
      expectation p (\x. abs(X m x))`
     MP_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[indicator_fn] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO] THENL
    [REAL_ARITH_TAC; REWRITE_TAC[REAL_ABS_POS]];
    MP_TAC(SPEC `m:num` (ASSUME `!n. expectation (p:A prob_space)
      (\x. abs ((X:num->A->real) n x)) <= C`)) THEN
    REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Inductive claim: E[X_m * 1_{B_m}] >= -C + c * P(A_m) *)
  SUBGOAL_THEN
    `!m. expectation (p:A prob_space)
           (\x. (X:num->A->real) m x * indicator_fn ((B:num->(A->bool)) m) x)
         >= --C + c * prob p ((A:num->(A->bool)) m)`
    ASSUME_TAC THENL
  [INDUCT_TAC THENL
   [(* Base case *)
    SUBGOAL_THEN
      `expectation (p:A prob_space) ((X:num->A->real) 0) =
       expectation p (\x. X 0 x * indicator_fn ((B:num->(A->bool)) 0) x) +
       expectation p (\x. X 0 x * indicator_fn ((A:num->(A->bool)) 0) x)`
      ASSUME_TAC THENL
    [CONV_TAC SYM_CONV THEN
     SUBGOAL_THEN
       `expectation (p:A prob_space)
         (\x. (X:num->A->real) 0 x * indicator_fn ((B:num->(A->bool)) 0) x +
              X 0 x * indicator_fn ((A:num->(A->bool)) 0) x) =
        expectation p (\x. X 0 x * indicator_fn (B 0) x) +
        expectation p (\x. X 0 x * indicator_fn (A 0) x)`
       (fun th -> REWRITE_TAC[GSYM th]) THENL
     [MATCH_MP_TAC EXPECTATION_ADD THEN CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
       ASM_REWRITE_TAC[ETA_AX]];
      ALL_TAC] THEN
     MATCH_MP_TAC EXPECTATION_EXT THEN
     X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
     EXPAND_TAC "B" THEN
     REWRITE_TAC[indicator_fn; IN_DIFF] THEN
     ASM_CASES_TAC `(y:A) IN ((A:num->(A->bool)) 0)` THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN
      `expectation (p:A prob_space)
         (\x. (X:num->A->real) 0 x * indicator_fn ((A:num->(A->bool)) 0) x)
       <= --c * prob p (A 0)`
      ASSUME_TAC THENL
    [SUBGOAL_THEN
       `--c * prob (p:A prob_space) ((A:num->(A->bool)) 0) =
        expectation p (\x. --c * indicator_fn (A 0) x)`
       SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`p:A prob_space`; `--c:real`;
        `indicator_fn ((A:num->(A->bool)) 0)`] EXPECTATION_CMUL) THEN
      ANTS_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[ETA_AX] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
       ASM_SIMP_TAC[EXPECTATION_INDICATOR] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
     MATCH_MP_TAC EXPECTATION_MONO THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
      ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
     CONJ_TAC THENL
     [MP_TAC(ISPECL [`p:A prob_space`; `--c:real`;
        `indicator_fn ((A:num->(A->bool)) 0)`] INTEGRABLE_CMUL) THEN
      ANTS_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[ETA_AX]]; ALL_TAC] THEN
     X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[indicator_fn] THEN
     COND_CASES_TAC THENL
     [REWRITE_TAC[REAL_MUL_RID] THEN
      UNDISCH_TAC `(y:A) IN ((A:num->(A->bool)) 0)` THEN EXPAND_TAC "A" THEN
      REWRITE_TAC[IN_ELIM_THM; running_max; real_ge] THEN
      UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
     ALL_TAC] THEN
    SUBGOAL_THEN `expectation (p:A prob_space) ((X:num->A->real) 0) >= --C`
      ASSUME_TAC THENL
    [REWRITE_TAC[real_ge] THEN
     SUBGOAL_THEN `abs(expectation (p:A prob_space) ((X:num->A->real) 0)) <= C`
       MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `expectation (p:A prob_space)
        (\x:A. abs((X:num->A->real) 0 x))` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC EXPECTATION_ABS_LE THEN ASM_REWRITE_TAC[ETA_AX];
       MP_TAC(SPEC `0` (ASSUME `!n. expectation (p:A prob_space)
         (\x. abs ((X:num->A->real) n x)) <= C`)) THEN
       REWRITE_TAC[ETA_AX]];
      REAL_ARITH_TAC];
     ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    (* Inductive step *)
    ABBREV_TAC
      `D = (B:num->(A->bool)) m INTER
           {x:A | x IN prob_carrier p /\ (X:num->A->real) (SUC m) x <= --c}` THEN
    SUBGOAL_THEN `(B:num->(A->bool)) (SUC m) = B m DIFF D` ASSUME_TAC THENL
    [EXPAND_TAC "D" THEN EXPAND_TAC "B" THEN EXPAND_TAC "A" THEN
     REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTER; IN_ELIM_THM;
                 running_max; REAL_MAX_GE] THEN
     X_GEN_TAC `z:A` THEN
     ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `D:A->bool IN prob_events p` ASSUME_TAC THENL
    [EXPAND_TAC "D" THEN MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC RV_LE_EVENT THEN REWRITE_TAC[ETA_AX] THEN
     ASM_MESON_TAC[ADAPTED_IMP_RV];
     ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT ((A:num->(A->bool)) m) D` ASSUME_TAC THENL
    [EXPAND_TAC "D" THEN EXPAND_TAC "B" THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(A:num->(A->bool)) (SUC m) = A m UNION D` ASSUME_TAC THENL
    [EXPAND_TAC "D" THEN EXPAND_TAC "B" THEN EXPAND_TAC "A" THEN
     REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_DIFF; IN_ELIM_THM;
                 running_max; REAL_MAX_GE] THEN
     X_GEN_TAC `z:A` THEN
     ASM_CASES_TAC `(z:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN
      `prob (p:A prob_space) ((A:num->(A->bool)) (SUC m)) =
       prob p (A m) + prob p D`
      ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PROB_ADDITIVE THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `expectation (p:A prob_space)
         (\x. (X:num->A->real) m x * indicator_fn ((B:num->(A->bool)) m) x) <=
       expectation p
         (\x. X (SUC m) x * indicator_fn (B m) x)`
      ASSUME_TAC THENL
    [MP_TAC(ASSUME `submartingale (p:A prob_space) FF (X:num->A->real)`) THEN
     REWRITE_TAC[submartingale] THEN STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `(B:num->(A->bool)) m`]) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `(B:num->(A->bool)) m = B (SUC m) UNION D` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN SET_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT ((B:num->(A->bool)) (SUC m)) D` ASSUME_TAC THENL
    [REWRITE_TAC[DISJOINT] THEN
     UNDISCH_TAC `(B:num->(A->bool)) (SUC m) = B m DIFF D` THEN SET_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `expectation (p:A prob_space)
         (\x. (X:num->A->real) (SUC m) x *
              indicator_fn ((B:num->(A->bool)) m) x) =
       expectation p
         (\x. X (SUC m) x * indicator_fn (B (SUC m)) x) +
       expectation p
         (\x. X (SUC m) x * indicator_fn D x)`
      ASSUME_TAC THENL
    [SUBGOAL_THEN
       `expectation (p:A prob_space)
          (\x. (X:num->A->real) (SUC m) x *
               indicator_fn ((B:num->(A->bool)) m) x) =
        expectation p
          (\x. X (SUC m) x * indicator_fn (B (SUC m)) x +
               X (SUC m) x * indicator_fn D x)`
       SUBST1_TAC THENL
     [MATCH_MP_TAC EXPECTATION_EXT THEN
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
      REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `(B:num->(A->bool)) m = B (SUC m) UNION D` THEN
      DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC INDICATOR_FN_DISJOINT_UNION THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC EXPECTATION_ADD THEN
      CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
      ASM_REWRITE_TAC[ETA_AX]];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `expectation (p:A prob_space)
         (\x. (X:num->A->real) (SUC m) x * indicator_fn D x) <=
       --c * prob p D`
      ASSUME_TAC THENL
    [SUBGOAL_THEN
       `--c * prob (p:A prob_space) D =
        expectation p (\x. --c * indicator_fn D x)`
       SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`p:A prob_space`; `--c:real`;
        `indicator_fn (D:A->bool)`] EXPECTATION_CMUL) THEN
      ANTS_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[ETA_AX] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
       ASM_SIMP_TAC[EXPECTATION_INDICATOR] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
     MATCH_MP_TAC EXPECTATION_MONO THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
      ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
     CONJ_TAC THENL
     [MP_TAC(ISPECL [`p:A prob_space`; `--c:real`;
        `indicator_fn (D:A->bool)`] INTEGRABLE_CMUL) THEN
      ANTS_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[ETA_AX]]; ALL_TAC] THEN
     X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[indicator_fn] THEN
     COND_CASES_TAC THENL
     [REWRITE_TAC[REAL_MUL_RID] THEN
      UNDISCH_TAC `(y:A) IN D` THEN EXPAND_TAC "D" THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
     ALL_TAC] THEN
    (* Combine: abbreviate and use arithmetic *)
    ABBREV_TAC `EB = expectation (p:A prob_space)
      (\x. (X:num->A->real) (SUC m) x *
           indicator_fn ((B:num->(A->bool)) (SUC m)) x)` THEN
    ABBREV_TAC `ED = expectation (p:A prob_space)
      (\x. (X:num->A->real) (SUC m) x * indicator_fn (D:A->bool) x)` THEN
    ABBREV_TAC `EBm = expectation (p:A prob_space)
      (\x. (X:num->A->real) (SUC m) x *
           indicator_fn ((B:num->(A->bool)) m) x)` THEN
    ABBREV_TAC `Em = expectation (p:A prob_space)
      (\x. (X:num->A->real) m x *
           indicator_fn ((B:num->(A->bool)) m) x)` THEN
    ABBREV_TAC `PA = prob (p:A prob_space) ((A:num->(A->bool)) m)` THEN
    ABBREV_TAC `PD = prob (p:A prob_space) (D:A->bool)` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Final step: combine bounds *)
  MP_TAC(SPEC `n:num`
    (ASSUME `!m. expectation (p:A prob_space)
               (\x. (X:num->A->real) m x *
                    indicator_fn ((B:num->(A->bool)) m) x) >=
             --C + c * prob p ((A:num->(A->bool)) m)`)) THEN
  MP_TAC(SPEC `n:num`
    (ASSUME `!m. expectation (p:A prob_space)
               (\x. (X:num->A->real) m x *
                    indicator_fn ((B:num->(A->bool)) m) x) <= C`)) THEN
  REAL_ARITH_TAC);;

(* ---- Step 6: Event membership for general submartingales ---- *)

let RUNNING_MAX_POS_PART_EVENT = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) c n.
     submartingale p FF X
     ==> {x | x IN prob_carrier p /\
              running_max (\m x. pos_part(X m x)) n x >= c}
         IN prob_events p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `submartingale (p:A prob_space) FF
    (\n x. pos_part((X:num->A->real) n x))` ASSUME_TAC THENL
  [MATCH_MP_TAC SUBMARTINGALE_POS_PART THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
  EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN CONJ_TAC THENL
  [ASM_MESON_TAC[filtration; submartingale]; ALL_TAC] THEN
  MATCH_MP_TAC RUNNING_MAX_EXCEEDS_IN_FILTRATION THEN
  ASM_MESON_TAC[submartingale]);;

let RUNNING_MAX_NEG_PART_EVENT = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) c n.
     submartingale p FF X
     ==> {x | x IN prob_carrier p /\
              running_max (\m x. max (--X m x) (&0)) n x >= c}
         IN prob_events p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
  EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN CONJ_TAC THENL
  [ASM_MESON_TAC[filtration; submartingale]; ALL_TAC] THEN
  MATCH_MP_TAC RUNNING_MAX_EXCEEDS_IN_FILTRATION THEN CONJ_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  REWRITE_TAC[adapted; measurable_wrt] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `&0 <= v` THENL
  [SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\
              max (--(X:num->A->real) n x) (&0) <= v} =
       {x | x IN prob_carrier p /\ X n x >= --v}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
     EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     POP_ASSUM MP_TAC THEN UNDISCH_TAC `&0 <= v` THEN REAL_ARITH_TAC;
     MATCH_MP_TAC MEASURABLE_WRT_GE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[submartingale; filtration]; ALL_TAC] THEN
     REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[submartingale; adapted]];
   SUBGOAL_THEN
      `{x:A | x IN prob_carrier p /\
              max (--(X:num->A->real) n x) (&0) <= v} = {}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN GEN_TAC THEN
     DISCH_THEN(CONJUNCTS_THEN2 (fun _ -> ALL_TAC) MP_TAC) THEN
     UNDISCH_TAC `~(&0 <= v)` THEN REAL_ARITH_TAC;
     SUBGOAL_THEN `sigma_algebra ((FF:num->(A->bool)->bool) n)`
       MP_TAC THENL
     [ASM_MESON_TAC[submartingale; filtration; sub_sigma_algebra];
      ALL_TAC] THEN
     REWRITE_TAC[sigma_algebra] THEN STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `{}:(A->bool)->bool`) THEN
     REWRITE_TAC[EMPTY_SUBSET; COUNTABLE_EMPTY; UNIONS_0]]]);;

(* ---- Step 7: L1-bounded upcrossing lemmas ---- *)

let UPCROSSING_EXPECTATION_BOUND_L1 = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b n C.
     submartingale p FF X /\ a < b /\
     (!n. expectation p (\x. abs(X n x)) <= C)
     ==> (b - a) * expectation p (\x. &(num_upcrossings X a b n x))
         <= C + abs(a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m. integrable (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL
  [REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation (p:A prob_space)
    (\x:A. pos_part((X:num->A->real) n x - a))` THEN
  CONJ_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                   `X:num->A->real`; `a:real`; `b:real`; `n:num`]
    DOOB_UPCROSSING_INEQUALITY) THEN
   ASM_REWRITE_TAC[];
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space)
     (\x:A. abs((X:num->A->real) n x) + abs(a))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[pos_part] THEN MATCH_MP_TAC INTEGRABLE_POS_PART THEN
     MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ETA_AX; INTEGRABLE_CONST]];
     MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ABS THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[ETA_AX; INTEGRABLE_CONST]];
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     REWRITE_TAC[pos_part] THEN REAL_ARITH_TAC];
    SUBGOAL_THEN `expectation (p:A prob_space)
      (\x:A. abs((X:num->A->real) n x) + abs(a))
      = expectation p (\x. abs(X n x)) + abs(a)` SUBST1_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`; `\x:A. abs((X:num->A->real) n x)`;
                     `\x:A. abs(a:real)`] EXPECTATION_ADD) THEN
     ANTS_TAC THENL
     [CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_ABS THEN REWRITE_TAC[ETA_AX] THEN
       ASM_REWRITE_TAC[];
       REWRITE_TAC[INTEGRABLE_CONST]];
      REWRITE_TAC[EXPECTATION_CONST]];
     REWRITE_TAC[REAL_LE_RADD] THEN ASM_REWRITE_TAC[]]]]);;

let RV_NUM_UPCROSSINGS = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b.
     filtration p FF /\ adapted p FF X
     ==> !n. random_variable p (\x. &(num_upcrossings X a b n x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[num_upcrossings; upcrossing_count] THEN
   REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_RULE `0 = 0`] THEN
   REWRITE_TAC[RANDOM_VARIABLE_CONST];
   REWRITE_TAC[num_upcrossings; upcrossing_count] THEN
   REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM num_upcrossings] THEN
   MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ABBREV_TAC `S = {x:A | x IN prob_carrier p /\
      upcrossing_phase (\k. (X:num->A->real) k x) a b n = 1 /\
      X (SUC n) x >= b}` THEN
    SUBGOAL_THEN `(S:A->bool) IN prob_events p` ASSUME_TAC THENL
    [EXPAND_TAC "S" THEN
     SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
       upcrossing_phase (\k. (X:num->A->real) k x) a b n = 1 /\
       X (SUC n) x >= b} =
       {x | x IN prob_carrier p /\ upcrossing_phase (\k. X k x) a b n = 1}
       INTER {x | x IN prob_carrier p /\ X (SUC n) x >= b}` SUBST1_TAC THENL
     [SET_TAC[];
      MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN CONJ_TAC THENL
      [MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
         `X:num->A->real`; `a:real`; `b:real`] UPCROSSING_PHASE_SET_IN_FILTRATION) THEN
       ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
       DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun _ -> ALL_TAC)) THEN
       FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [filtration]) THEN
       DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `n:num`) (fun _ -> ALL_TAC)) THEN
       REWRITE_TAC[sub_sigma_algebra] THEN
       STRIP_TAC THEN
       FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
       MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
          `X:num->A->real`] ADAPTED_IMP_RV) THEN
       ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN
       REWRITE_TAC[ETA_AX]]];
     REWRITE_TAC[random_variable] THEN GEN_TAC THEN
     ASM_CASES_TAC `&1 <= a'` THENL
     [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
         &(if upcrossing_phase (\k. (X:num->A->real) k x) a b n = 1 /\
              X (SUC n) x >= b
           then 1 else 0) <= a'} = prob_carrier p` SUBST1_TAC THENL
      [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL
       [STRIP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
       REWRITE_TAC[PROB_CARRIER_IN_EVENTS]];
      ASM_CASES_TAC `a' < &0` THENL
      [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
          &(if upcrossing_phase (\k. (X:num->A->real) k x) a b n = 1 /\
               X (SUC n) x >= b
            then 1 else 0) <= a'} = {}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN GEN_TAC THEN
        REWRITE_TAC[DE_MORGAN_THM] THEN DISJ2_TAC THEN
        COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[PROB_EMPTY_IN_EVENTS]];
       SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
           &(if upcrossing_phase (\k. (X:num->A->real) k x) a b n = 1 /\
                X (SUC n) x >= b
             then 1 else 0) <= a'} = prob_carrier p DIFF S` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN X_GEN_TAC `x:A` THEN
        EQ_TAC THENL
        [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
         EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
         STRIP_TAC THEN
         UNDISCH_TAC `&(if upcrossing_phase (\k. (X:num->A->real) k x) a b n = 1 /\
           X (SUC n) x >= b then 1 else 0) <= a'` THEN
         ASM_REWRITE_TAC[] THEN
         UNDISCH_TAC `~(&1 <= a')` THEN REAL_ARITH_TAC;
         STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
         SUBGOAL_THEN `~(upcrossing_phase (\k. (X:num->A->real) k x) a b n = 1 /\
           X (SUC n) x >= b)` ASSUME_TAC THENL
         [UNDISCH_TAC `~((x:A) IN S)` THEN
          EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
          ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(a' < &0)` THEN REAL_ARITH_TAC]];
        MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN ASM_REWRITE_TAC[]]]]]]]);;

let NUM_UPCROSSINGS_GE_EVENT = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b n k.
     filtration p FF /\ adapted p FF X
     ==> {x | x IN prob_carrier p /\
              &(num_upcrossings X a b n x) >= &k}
         IN prob_events p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
  MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
    `X:num->A->real`; `a:real`; `b:real`] RV_NUM_UPCROSSINGS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[]);;

let UPCROSSING_COUNT_LE = prove
 (`!f a b n. upcrossing_count f a b n <= n`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[upcrossing_count; LE_REFL];
   REWRITE_TAC[upcrossing_count] THEN
   COND_CASES_TAC THEN ASM_ARITH_TAC]);;

(* BOUNDED_RV_INTEGRABLE removed: identical to INTEGRABLE_BOUNDED
   from expectation.ml. Uses below updated to INTEGRABLE_BOUNDED. *)

let INTEGRABLE_NUM_UPCROSSINGS = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b.
     filtration p FF /\ adapted p FF X
     ==> !n. integrable p (\x. &(num_upcrossings X a b n x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
  EXISTS_TAC `&n` THEN CONJ_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
    `X:num->A->real`; `a:real`; `b:real`] RV_NUM_UPCROSSINGS) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
   REWRITE_TAC[];
   GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[num_upcrossings; REAL_ABS_NUM] THEN
   REWRITE_TAC[REAL_OF_NUM_LE; UPCROSSING_COUNT_LE]]);;

let MARKOV_GE = prove
 (`!p:A prob_space f (c:real).
     integrable p f /\
     (!x. x IN prob_carrier p ==> &0 <= f x) /\
     &0 < c /\
     {x | x IN prob_carrier p /\ f x >= c} IN prob_events p
     ==> c * prob p {x | x IN prob_carrier p /\ f x >= c}
         <= expectation p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `A = {x:A | x IN prob_carrier p /\ (f:A->real) x >= c}` THEN
  SUBGOAL_THEN `c * prob (p:A prob_space) A =
    expectation p (\x:A. c * indicator_fn (A:A->bool) x)` SUBST1_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `A:A->bool`] EXPECTATION_INDICATOR) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o GSYM) THEN
   MP_TAC(ISPECL [`p:A prob_space`; `c:real`;
     `indicator_fn (A:A->bool)`] EXPECTATION_CMUL) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[]] THEN
   MESON_TAC[];
   MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `integrable (p:A prob_space) (indicator_fn (A:A->bool))`
      ASSUME_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
     MP_TAC(ISPECL [`p:A prob_space`; `c:real`;
       `indicator_fn (A:A->bool)`] INTEGRABLE_CMUL) THEN
     ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[indicator_fn] THEN
    COND_CASES_TAC THENL
    [POP_ASSUM MP_TAC THEN EXPAND_TAC "A" THEN
     REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
     STRIP_TAC THEN REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
     REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_MESON_TAC[]]]]);;


(* ========================================================================= *)
(* BACKWARD MARTINGALE CONVERGENCE: L^1-BOUNDED (continued from line ~5270)   *)
(* Moved here because it depends on MARKOV_GE, DOOB_MAXIMAL_POS_PART *)
(* and other lemmas defined in this section.                                  *)
(* ========================================================================= *)

(* Downcrossing events are measurable for backward martingale *)
let NUM_DOWNCROSSINGS_GE_EVENT = prove(
  `!(p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) a b n k.
    backward_martingale p FF X
    ==> {x | x IN prob_carrier p /\ &(num_downcrossings X a b n x) >= &k}
        IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
    &(num_downcrossings (X:num->A->real) a b n x) >= &k} =
    {x | x IN prob_carrier p /\
    &(num_upcrossings (\m:num. \x:A. --((X:num->A->real) m x)) (--b) (--a) n x) >= &k}`
    SUBST1_TAC THENL [
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; num_downcrossings; num_upcrossings;
                DOWNCROSSING_COUNT_EQ_NEG] THEN
    GEN_TAC THEN REWRITE_TAC[real_ge; REAL_OF_NUM_LE];
    MATCH_MP_TAC NUM_UPCROSSINGS_GE_EVENT THEN
    EXISTS_TAC `\n:num. prob_events (p:A prob_space)` THEN
    CONJ_TAC THENL [
      REWRITE_TAC[FILTRATION_CONST_EVENTS];
      MATCH_MP_TAC ADAPTED_NEG_BACKWARD THEN
      EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[]]]);;

(* Random variable for downcrossing counts *)
let RV_NUM_DOWNCROSSINGS = prove(
  `!(p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) a b.
    backward_martingale p FF X
    ==> !n. random_variable p (\x. &(num_downcrossings X a b n x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. &(num_downcrossings (X:num->A->real) a b n x)) =
    (\x. &(num_upcrossings (\m. \x. --(X m x)) (--b) (--a) n x))`
    SUBST1_TAC THENL [
    REWRITE_TAC[FUN_EQ_THM; num_downcrossings; num_upcrossings;
                DOWNCROSSING_COUNT_EQ_NEG];
    MP_TAC(ISPECL [`p:A prob_space`; `\n:num. prob_events (p:A prob_space)`;
                    `\m:num. \x:A. --((X:num->A->real) m x)`;
                    `--b:real`; `--a:real`] RV_NUM_UPCROSSINGS) THEN
    ANTS_TAC THENL [
      CONJ_TAC THENL [
        REWRITE_TAC[FILTRATION_CONST_EVENTS];
        MATCH_MP_TAC ADAPTED_NEG_BACKWARD THEN
        EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[]]]);;

(* Integrability of downcrossing counts *)
let INTEGRABLE_NUM_DOWNCROSSINGS = prove(
  `!(p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) a b.
    backward_martingale p FF X
    ==> !n. integrable p (\x. &(num_downcrossings X a b n x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
  EXISTS_TAC `&n` THEN CONJ_TAC THENL [
    MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
      `X:num->A->real`; `a:real`; `b:real`] RV_NUM_DOWNCROSSINGS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[num_downcrossings; DOWNCROSSING_COUNT_EQ_NEG; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_OF_NUM_LE; UPCROSSING_COUNT_LE]]);;

(* Backward downcrossing expectation bound for L^1 case *)
let BACKWARD_DOWNCROSSING_EXPECTATION_BOUND_L1 = prove(
  `!(p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) a b N C.
    backward_martingale p FF X /\ a < b /\
    (!n. expectation p (\x. abs(X n x)) <= C)
    ==> (b - a) * expectation p (\x. &(num_downcrossings X a b N x))
        <= C + abs a + (b - a)`,
  REPEAT STRIP_TAC THEN
  (* Get the reversed submartingale *)
  MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                  `X:num->A->real`; `N:num`] REVERSED_IS_SUBMARTINGALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Upcrossing bound for the reversed submartingale *)
  MP_TAC(ISPECL [`p:A prob_space`; `\k:num. (FF:num->(A->bool)->bool)(N - k)`;
                  `\k:num. (X:num->A->real)(N - k)`; `a:real`; `b:real`;
                  `N:num`; `C:real`]
    UPCROSSING_EXPECTATION_BOUND_L1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  (* Integrability of dc *)
  SUBGOAL_THEN `integrable (p:A prob_space)
    (\x. &(num_downcrossings (X:num->A->real) a b N x))` ASSUME_TAC THENL [
    MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
      `X:num->A->real`; `a:real`; `b:real`]
      INTEGRABLE_NUM_DOWNCROSSINGS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `N:num`) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  (* Integrability of uc_rev *)
  SUBGOAL_THEN `integrable (p:A prob_space)
    (\x. &(num_upcrossings (\k. (X:num->A->real)(N - k)) a b N x))`
    ASSUME_TAC THENL [
    MP_TAC(ISPECL [`p:A prob_space`; `\k:num. (FF:num->(A->bool)->bool)(N - k)`;
      `\k:num. (X:num->A->real)(N - k)`; `a:real`; `b:real`]
      INTEGRABLE_NUM_UPCROSSINGS) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [submartingale]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `N:num`) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  (* Pointwise: dc <= uc_rev + 1 *)
  SUBGOAL_THEN
    `!x:A. x IN prob_carrier p ==>
      &(num_downcrossings (X:num->A->real) a b N x) <=
      &(num_upcrossings (\k. X(N - k)) a b N x) + &1`
    ASSUME_TAC THENL [
    REPEAT STRIP_TAC THEN REWRITE_TAC[num_downcrossings; num_upcrossings] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC DC_LE_REV_UC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Main chain: (b-a)*E[dc] <= (b-a)*(E[uc_rev]+1) <= C+|a|+(b-a) *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(b - a) * (expectation (p:A prob_space)
    (\x. &(num_upcrossings (\k. (X:num->A->real)(N - k)) a b N x)) + &1)` THEN
  CONJ_TAC THENL [
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `expectation (p:A prob_space)
      (\x. &(num_upcrossings (\k. (X:num->A->real)(N - k)) a b N x) + &1)` THEN
    CONJ_TAC THENL [
      MATCH_MP_TAC EXPECTATION_MONO THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
      SUBGOAL_THEN `expectation (p:A prob_space)
        (\x. &(num_upcrossings (\k. (X:num->A->real)(N - k)) a b N x) + &1) =
        expectation p (\x. &(num_upcrossings (\k. X(N - k)) a b N x)) + &1`
        SUBST1_TAC THENL
      [MP_TAC(ISPECL [`p:A prob_space`;
        `\x:A. &(num_upcrossings (\k. (X:num->A->real)(N - k)) a b N x)`;
        `\x:A. &1`] EXPECTATION_ADD) THEN
       CONV_TAC(DEPTH_CONV BETA_CONV) THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
       DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXPECTATION_CONST];
       REAL_ARITH_TAC]];
    REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC]);;

(* Backward downcrossing probability bound for L^1 case *)
let BACKWARD_DOWNCROSSING_PROB_BOUND_L1 = prove(
  `!(p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real)
    a b n C (k:num).
    backward_martingale p FF X /\ a < b /\
    (!n. expectation p (\x. abs(X n x)) <= C) /\ 0 < k
    ==> prob p {x | x IN prob_carrier p /\
          &(num_downcrossings X a b n x) >= &k}
        <= (C + abs a + (b - a)) / ((b - a) * &k)`,
  REPEAT STRIP_TAC THEN
  (* From MARKOV_GE: &k * P(dc >= k) <= E[dc] *)
  SUBGOAL_THEN `&k * prob (p:A prob_space)
    {x | x IN prob_carrier p /\
         &(num_downcrossings (X:num->A->real) a b n x) >= &k} <=
    expectation p (\x. &(num_downcrossings X a b n x))` ASSUME_TAC THENL [
    MATCH_MP_TAC MARKOV_GE THEN REPEAT CONJ_TAC THENL [
      MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
        `X:num->A->real`; `a:real`; `b:real`]
        INTEGRABLE_NUM_DOWNCROSSINGS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
      REWRITE_TAC[];
      REWRITE_TAC[num_downcrossings] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_POS];
      ASM_REWRITE_TAC[REAL_OF_NUM_LT];
      MATCH_MP_TAC NUM_DOWNCROSSINGS_GE_EVENT THEN
      EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* From expectation bound: E[dc] <= (C + |a| + (b-a)) / (b-a) *)
  MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                  `X:num->A->real`; `a:real`; `b:real`; `n:num`; `C:real`]
    BACKWARD_DOWNCROSSING_EXPECTATION_BOUND_L1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  DISCH_TAC THEN
  (* Combine: P(dc >= k) <= (C+|a|+(b-a))/((b-a)*k) *)
  (* Via: P*((b-a)*k) <= (b-a)*(k*P) <= (b-a)*E[dc] <= C+|a|+(b-a) *)
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(b - a) * expectation (p:A prob_space)
    (\x. &(num_downcrossings (X:num->A->real) a b n x))` THEN
  CONJ_TAC THENL [
    SUBGOAL_THEN `prob (p:A prob_space)
      {x | x IN prob_carrier p /\
           &(num_downcrossings (X:num->A->real) a b n x) >= &k} *
      ((b - a) * &k) = (b - a) * (&k * prob p
      {x | x IN prob_carrier p /\
           &(num_downcrossings X a b n x) >= &k})`
      SUBST1_TAC THENL [REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[]]);;

(* a.s. finite downcrossings for L^1-bounded backward martingale *)
let FINITE_DOWNCROSSINGS_AS_L1_BACKWARD = prove(
  `!(p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) a b C.
    backward_martingale p FF X /\ a < b /\
    (!n. expectation p (\x. abs(X n x)) <= C)
    ==> almost_surely p
          {x | ?B:num. !n. num_downcrossings X a b n x <= B}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[almost_surely] THEN
  EXISTS_TAC
    `INTERS {UNIONS {
       {x:A | x IN prob_carrier p /\
              &(num_downcrossings (X:num->A->real) a b n x) >= &(SUC k)}
     | n IN (:num)} | k IN (:num)}` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[null_event] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN
    GEN_TAC THEN MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
    GEN_TAC THEN MATCH_MP_TAC NUM_DOWNCROSSINGS_GE_EVENT THEN
    EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_EQ_0_FROM_INV_BOUND THEN
    EXISTS_TAC `(C + abs(a:real) + (b - a)) / (b - a)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC PROB_POSITIVE THEN
     MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN
     GEN_TAC THEN MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
     GEN_TAC THEN MATCH_MP_TAC NUM_DOWNCROSSINGS_GE_EVENT THEN
     EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
     X_GEN_TAC `j:num` THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `prob (p:A prob_space) (UNIONS {
       {x:A | x IN prob_carrier p /\
              &(num_downcrossings (X:num->A->real) a b n x) >= &(SUC j)}
       | n IN (:num)})` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC PROB_MONO THEN REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN
       GEN_TAC THEN MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
       GEN_TAC THEN MATCH_MP_TAC NUM_DOWNCROSSINGS_GE_EVENT THEN
       EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
       GEN_TAC THEN MATCH_MP_TAC NUM_DOWNCROSSINGS_GE_EVENT THEN
       EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
       SET_TAC[]];
      SUBGOAL_THEN `(C + abs(a:real) + (b - a)) / (b - a) / &(SUC j) =
                     (C + abs a + (b - a)) / ((b - a) * &(SUC j))`
        SUBST1_TAC THENL
      [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `prob (p:A prob_space) (UNIONS {
        {x:A | x IN prob_carrier p /\
               &(num_downcrossings (X:num->A->real) a b n x) >= &(SUC j)}
        | n IN (:num)})` THEN
      CONJ_TAC THENL [REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC PROB_UNIONS_INCREASING_BOUND THEN
      REPEAT CONJ_TAC THENL
      [GEN_TAC THEN MATCH_MP_TAC NUM_DOWNCROSSINGS_GE_EVENT THEN
       EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
       X_GEN_TAC `nn:num` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge;
         REAL_OF_NUM_LE] THEN
       X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
       ASM_MESON_TAC[NUM_DOWNCROSSINGS_MONO; LE_TRANS;
         ARITH_RULE `nn <= SUC nn`];
       X_GEN_TAC `nn:num` THEN
       MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                       `X:num->A->real`; `a:real`; `b:real`; `nn:num`;
                       `C:real`; `SUC j`] BACKWARD_DOWNCROSSING_PROB_BOUND_L1) THEN
       DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LT_0]]]]];
   REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERS] THEN
   X_GEN_TAC `x:A` THEN STRIP_TAC THEN
   GEN_TAC THEN REWRITE_TAC[SIMPLE_IMAGE; IN_IMAGE; IN_UNIV] THEN
   DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
   REWRITE_TAC[IN_UNIONS] THEN
   REWRITE_TAC[EXISTS_IN_IMAGE; IN_UNIV; IN_ELIM_THM;
               real_ge; REAL_OF_NUM_LE] THEN
   FIRST_X_ASSUM(MP_TAC o
     GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
   DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
   REWRITE_TAC[NOT_FORALL_THM; NOT_LE] THEN
   DISCH_THEN(X_CHOOSE_THEN `nn:num` ASSUME_TAC) THEN
   EXISTS_TAC `nn:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* Helper: running_max is bounded if all components are bounded *)
let RUNNING_MAX_BOUNDED = prove(
  `!(f:num->A->real) N x C.
     (!m. m <= N ==> f m x <= C) ==> running_max f N x <= C`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THENL
  [REWRITE_TAC[running_max] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
   REWRITE_TAC[running_max; real_max] THEN COND_CASES_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

(* Reversal preserves running_max *)
let RUNNING_MAX_REV = prove(
  `!N (g:num->A->real) x.
     running_max (\m. g(N - m)) N x = running_max g N x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
  [MP_TAC(ISPECL [`\m:num. (g:num->A->real)(N - m)`; `N:num`; `x:A`;
                   `running_max (g:num->A->real) N x`] RUNNING_MAX_BOUNDED) THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
   MATCH_MP_TAC RUNNING_MAX_GE THEN ASM_ARITH_TAC;
   MP_TAC(ISPECL [`g:num->A->real`; `N:num`; `x:A`;
                   `running_max (\m:num. (g:num->A->real)(N - m)) N x`]
     RUNNING_MAX_BOUNDED) THEN
   DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
   SUBGOAL_THEN `(g:num->A->real) m x = (\m. g(N - m)) (N - m) x`
     SUBST1_TAC THENL
   [BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC RUNNING_MAX_GE THEN ASM_ARITH_TAC]]);;

(* Backward martingale gives random variables *)
let BACKWARD_MARTINGALE_RV = prove(
  `!p:A prob_space FF (X:num->A->real).
    backward_martingale p FF X ==> !n. random_variable p (X n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[backward_martingale] THEN STRIP_TAC THEN
  GEN_TAC THEN REWRITE_TAC[random_variable] THEN GEN_TAC THEN
  UNDISCH_TAC `adapted (p:A prob_space) FF X` THEN
  REWRITE_TAC[adapted; measurable_wrt] THEN
  DISCH_THEN(MP_TAC o SPECL [`n:num`; `a:real`]) THEN
  UNDISCH_TAC `decreasing_filtration (p:A prob_space) FF` THEN
  REWRITE_TAC[decreasing_filtration; sub_sigma_algebra; SUBSET] THEN
  MESON_TAC[]);;

(* Running max of pos_part events for backward martingale *)
let BACKWARD_SIMPLE_RUNNING_MAX_POS_PART_EVENT = prove(
  `!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) c N.
    backward_martingale p FF X
    ==> {x | x IN prob_carrier p /\
             running_max (\m x. pos_part(X m x)) N x >= c}
        IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
    running_max (\m x. pos_part((X:num->A->real) m x)) N x >= c}
    IN (\n:num. prob_events (p:A prob_space)) N`
    MP_TAC THENL
  [MATCH_MP_TAC RUNNING_MAX_EXCEEDS_IN_FILTRATION THEN CONJ_TAC THENL
   [REWRITE_TAC[FILTRATION_CONST_EVENTS]; ALL_TAC] THEN
   REWRITE_TAC[adapted; measurable_wrt] THEN
   X_GEN_TAC `n:num` THEN X_GEN_TAC `v:real` THEN
   ASM_CASES_TAC `v < &0` THENL
   [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
     pos_part((X:num->A->real) n x) <= v} = {}` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN GEN_TAC THEN
     REWRITE_TAC[DE_MORGAN_THM] THEN DISJ2_TAC THEN
     REWRITE_TAC[pos_part] THEN ASM_REAL_ARITH_TAC;
     REWRITE_TAC[PROB_EMPTY_IN_EVENTS]];
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
      pos_part((X:num->A->real) n x) <= v} =
      {x | x IN prob_carrier p /\ X n x <= v}` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
     AP_TERM_TAC THEN REWRITE_TAC[pos_part] THEN ASM_REAL_ARITH_TAC;
     MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                     `X:num->A->real`] BACKWARD_MARTINGALE_RV) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
     REWRITE_TAC[random_variable] THEN DISCH_THEN(MP_TAC o SPEC `v:real`) THEN
     REWRITE_TAC[]]];
   REWRITE_TAC[]]);;

(* Running max of neg_part events for backward martingale *)
let BACKWARD_SIMPLE_RUNNING_MAX_NEG_PART_EVENT = prove(
  `!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) c N.
    backward_martingale p FF X
    ==> {x | x IN prob_carrier p /\
             running_max (\m x. max (--(X m x)) (&0)) N x >= c}
        IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
    running_max (\m x. max (--((X:num->A->real) m x)) (&0)) N x >= c}
    IN (\n:num. prob_events (p:A prob_space)) N`
    MP_TAC THENL
  [MATCH_MP_TAC RUNNING_MAX_EXCEEDS_IN_FILTRATION THEN CONJ_TAC THENL
   [REWRITE_TAC[FILTRATION_CONST_EVENTS]; ALL_TAC] THEN
   REWRITE_TAC[adapted; measurable_wrt] THEN
   X_GEN_TAC `n:num` THEN X_GEN_TAC `v:real` THEN
   ASM_CASES_TAC `&0 <= v` THENL
   [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
      max (--((X:num->A->real) n x)) (&0) <= v} =
      {x | x IN prob_carrier p /\ X n x >= --v}` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
     EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     POP_ASSUM MP_TAC THEN UNDISCH_TAC `&0 <= v` THEN REAL_ARITH_TAC;
     MATCH_MP_TAC RV_LEVEL_GE_IN_EVENTS THEN
     MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                     `X:num->A->real`] BACKWARD_MARTINGALE_RV) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
     SIMP_TAC[ETA_AX]];
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\
      max (--((X:num->A->real) n x)) (&0) <= v} = {}` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN GEN_TAC THEN
     DISCH_THEN(CONJUNCTS_THEN2 (fun _ -> ALL_TAC) MP_TAC) THEN
     UNDISCH_TAC `~(&0 <= v)` THEN REAL_ARITH_TAC;
     REWRITE_TAC[PROB_EMPTY_IN_EVENTS]]];
   REWRITE_TAC[]]);;

(* Doob maximal inequality for pos_part of backward martingale *)
let BACKWARD_MAXIMAL_POS_PART = prove(
  `!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) c N C.
    backward_martingale p FF X /\ &0 < c /\
    (!n. expectation p (\x. abs(X n x)) <= C)
    ==> c * prob p {x | x IN prob_carrier p /\
                        running_max (\m x. pos_part(X m x)) N x >= c}
        <= C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `submartingale (p:A prob_space)
    (\k. (FF:num->(A->bool)->bool)(N - k))
    (\k. (X:num->A->real)(N - k))` ASSUME_TAC THENL
  [MATCH_MP_TAC REVERSED_IS_SUBMARTINGALE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `\k:num. (FF:num->(A->bool)->bool)(N-k)`;
                  `\k:num. (X:num->A->real)(N-k)`; `c:real`; `N:num`; `C:real`]
    DOOB_MAXIMAL_POS_PART) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN GEN_TAC THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `!y:A. running_max (\m (x:A). pos_part((X:num->A->real) m x)) N y =
           running_max (\m (x:A). pos_part(X(N - m) x)) N y`
    (fun th -> REWRITE_TAC[th] THEN FIRST_ASSUM ACCEPT_TAC) THEN
  GEN_TAC THEN
  MP_TAC(ISPECL [`N:num`; `\m (x:A). pos_part((X:num->A->real) m x)`;
                  `y:A`] RUNNING_MAX_REV) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(ACCEPT_TAC o GSYM));;

(* Doob maximal inequality for neg_part of backward martingale *)
let BACKWARD_NEG_PART_MAXIMAL = prove(
  `!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) c N C.
    backward_martingale p FF X /\ &0 < c /\
    (!n. expectation p (\x. abs(X n x)) <= C)
    ==> c * prob p {x | x IN prob_carrier p /\
                        running_max (\m x. max (--(X m x)) (&0)) N x >= c}
        <= &2 * C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `submartingale (p:A prob_space)
    (\k. (FF:num->(A->bool)->bool)(N - k))
    (\k. (X:num->A->real)(N - k))` ASSUME_TAC THENL
  [MATCH_MP_TAC REVERSED_IS_SUBMARTINGALE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `\k:num. (FF:num->(A->bool)->bool)(N-k)`;
                  `\k:num. (X:num->A->real)(N-k)`; `c:real`; `N:num`; `C:real`]
    SUBMARTINGALE_NEG_PART_MAXIMAL) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN GEN_TAC THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `!y:A. running_max (\m (x:A). max (--((X:num->A->real) m x)) (&0)) N y =
           running_max (\m (x:A). max (--(X(N - m) x)) (&0)) N y`
    (fun th -> REWRITE_TAC[th] THEN FIRST_ASSUM ACCEPT_TAC) THEN
  GEN_TAC THEN
  MP_TAC(ISPECL [`N:num`;
                  `\m (x:A). max (--((X:num->A->real) m x)) (&0)`;
                  `y:A`] RUNNING_MAX_REV) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(ACCEPT_TAC o GSYM));;

(* a.s. boundedness for L^1-bounded backward martingale *)
let BACKWARD_MARTINGALE_ALMOST_SURELY_BOUNDED = prove(
  `!(p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) C.
    backward_martingale p FF X /\
    (!n. expectation p (\x. abs(X n x)) <= C)
    ==> almost_surely p {x | ?M. !n. abs(X n x) <= M}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Reduce to pos_part and neg_part bounds *)
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
    `{x:A | ?M. !n. pos_part((X:num->A->real) n x) <= M} INTER
     {x:A | ?M. !n. max (--(X:num->A->real) n x) (&0) <= M}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_INTER THEN CONJ_TAC THENL
   [(* a.s. pos_part bounded *)
    REWRITE_TAC[almost_surely] THEN
    EXISTS_TAC `INTERS {UNIONS {
      {x:A | x IN prob_carrier p /\
             running_max (\m x. pos_part ((X:num->A->real) m x)) n x
             >= &(SUC k)}
    | n IN (:num)} | k IN (:num)}` THEN
    CONJ_TAC THENL
    [REWRITE_TAC[null_event] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`p:A prob_space`;
        `\k n. {x:A | x IN prob_carrier p /\
           running_max (\m x. pos_part ((X:num->A->real) m x)) n x
           >= &(SUC k)}`] INTERS_UNIONS_IN_EVENTS) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
      MATCH_MP_TAC BACKWARD_SIMPLE_RUNNING_MAX_POS_PART_EVENT THEN
      EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_0_FROM_INV_BOUND THEN
      EXISTS_TAC `C:real` THEN CONJ_TAC THENL
      [MATCH_MP_TAC PROB_POSITIVE THEN
       MP_TAC(ISPECL [`p:A prob_space`;
         `\k n. {x:A | x IN prob_carrier p /\
            running_max (\m x. pos_part ((X:num->A->real) m x)) n x
            >= &(SUC k)}`] INTERS_UNIONS_IN_EVENTS) THEN
       REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
       MATCH_MP_TAC BACKWARD_SIMPLE_RUNNING_MAX_POS_PART_EVENT THEN
       EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
       X_GEN_TAC `j:num` THEN
       MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `prob (p:A prob_space) (UNIONS {
         {x:A | x IN prob_carrier p /\
                running_max (\m x. pos_part ((X:num->A->real) m x)) n x
                >= &(SUC j)} | n IN (:num)})` THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC PROB_MONO THEN REPEAT CONJ_TAC THENL
        [MP_TAC(ISPECL [`p:A prob_space`;
           `\k n. {x:A | x IN prob_carrier p /\
              running_max (\m x. pos_part ((X:num->A->real) m x)) n x
              >= &(SUC k)}`] INTERS_UNIONS_IN_EVENTS) THEN
         REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
         MATCH_MP_TAC BACKWARD_SIMPLE_RUNNING_MAX_POS_PART_EVENT THEN
         EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
         MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN GEN_TAC THEN
         MATCH_MP_TAC BACKWARD_SIMPLE_RUNNING_MAX_POS_PART_EVENT THEN
         EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
         REWRITE_TAC[SUBSET; IN_INTERS; SIMPLE_IMAGE;
                      FORALL_IN_IMAGE; IN_UNIV] THEN
         GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
         REWRITE_TAC[]];
        MP_TAC(ISPECL [
         `p:A prob_space`;
         `\n. {x:A | x IN prob_carrier p /\
            running_max (\m x. pos_part ((X:num->A->real) m x)) n x
            >= &(SUC j)}`;
         `C / &(SUC j)`] PROB_UNIONS_INCREASING_BOUND) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        REPEAT CONJ_TAC THENL
        [GEN_TAC THEN MATCH_MP_TAC BACKWARD_SIMPLE_RUNNING_MAX_POS_PART_EVENT THEN
         EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
         GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
         X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
         REWRITE_TAC[real_ge] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
         EXISTS_TAC `running_max (\m x. pos_part ((X:num->A->real) m x))
                       n (x:A)` THEN
         REWRITE_TAC[RUNNING_MAX_MONO_SUC] THEN
         FIRST_X_ASSUM(ACCEPT_TAC o REWRITE_RULE[real_ge]);
         X_GEN_TAC `nn:num` THEN
         MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                         `X:num->A->real`; `&(SUC j)`; `nn:num`; `C:real`]
           BACKWARD_MAXIMAL_POS_PART) THEN
         ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
         DISCH_TAC THEN
         ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LT_0] THEN
         ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]]]]];
     REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERS] THEN
     X_GEN_TAC `x:A` THEN
     DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM])) THEN
     REWRITE_TAC[NOT_FORALL_THM; REAL_NOT_LE] THEN DISCH_TAC THEN
     GEN_TAC THEN REWRITE_TAC[SIMPLE_IMAGE; IN_IMAGE; IN_UNIV] THEN
     DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
     REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `&(SUC k)`) THEN
     DISCH_THEN(X_CHOOSE_TAC `nn:num`) THEN
     EXISTS_TAC `nn:num` THEN ASM_REWRITE_TAC[real_ge] THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN
     MATCH_MP_TAC REAL_LTE_TRANS THEN
     EXISTS_TAC `(\m x. pos_part ((X:num->A->real) m x)) nn x` THEN
     CONJ_TAC THENL [BETA_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC RUNNING_MAX_GE THEN REWRITE_TAC[LE_REFL]];
    (* a.s. neg_part bounded *)
    REWRITE_TAC[almost_surely] THEN
    EXISTS_TAC `INTERS {UNIONS {
      {x:A | x IN prob_carrier p /\
             running_max (\m x. max (--(X:num->A->real) m x) (&0)) n x
             >= &(SUC k)}
    | n IN (:num)} | k IN (:num)}` THEN
    CONJ_TAC THENL
    [REWRITE_TAC[null_event] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`p:A prob_space`;
        `\k n. {x:A | x IN prob_carrier p /\
           running_max (\m x. max (--(X:num->A->real) m x) (&0)) n x
           >= &(SUC k)}`] INTERS_UNIONS_IN_EVENTS) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
      MATCH_MP_TAC BACKWARD_SIMPLE_RUNNING_MAX_NEG_PART_EVENT THEN
      EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_0_FROM_INV_BOUND THEN
      EXISTS_TAC `&2 * C` THEN CONJ_TAC THENL
      [MATCH_MP_TAC PROB_POSITIVE THEN
       MP_TAC(ISPECL [`p:A prob_space`;
         `\k n. {x:A | x IN prob_carrier p /\
            running_max (\m x. max (--(X:num->A->real) m x) (&0)) n x
            >= &(SUC k)}`] INTERS_UNIONS_IN_EVENTS) THEN
       REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
       MATCH_MP_TAC BACKWARD_SIMPLE_RUNNING_MAX_NEG_PART_EVENT THEN
       EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
       X_GEN_TAC `j:num` THEN
       MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `prob (p:A prob_space) (UNIONS {
         {x:A | x IN prob_carrier p /\
                running_max (\m x. max (--(X:num->A->real) m x) (&0)) n x
                >= &(SUC j)} | n IN (:num)})` THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC PROB_MONO THEN REPEAT CONJ_TAC THENL
        [MP_TAC(ISPECL [`p:A prob_space`;
           `\k n. {x:A | x IN prob_carrier p /\
              running_max (\m x. max (--(X:num->A->real) m x) (&0)) n x
              >= &(SUC k)}`] INTERS_UNIONS_IN_EVENTS) THEN
         REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
         MATCH_MP_TAC BACKWARD_SIMPLE_RUNNING_MAX_NEG_PART_EVENT THEN
         EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
         MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN GEN_TAC THEN
         MATCH_MP_TAC BACKWARD_SIMPLE_RUNNING_MAX_NEG_PART_EVENT THEN
         EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
         REWRITE_TAC[SUBSET; IN_INTERS; SIMPLE_IMAGE;
                      FORALL_IN_IMAGE; IN_UNIV] THEN
         GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
         REWRITE_TAC[]];
        MP_TAC(ISPECL [
         `p:A prob_space`;
         `\n. {x:A | x IN prob_carrier p /\
            running_max (\m x. max (--(X:num->A->real) m x) (&0)) n x
            >= &(SUC j)}`;
         `(&2 * C) / &(SUC j)`] PROB_UNIONS_INCREASING_BOUND) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        REPEAT CONJ_TAC THENL
        [GEN_TAC THEN MATCH_MP_TAC BACKWARD_SIMPLE_RUNNING_MAX_NEG_PART_EVENT THEN
         EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
         GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
         X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
         REWRITE_TAC[real_ge] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
         EXISTS_TAC `running_max (\m x. max (--(X:num->A->real) m x) (&0))
                       n (x:A)` THEN
         REWRITE_TAC[RUNNING_MAX_MONO_SUC] THEN
         FIRST_X_ASSUM(ACCEPT_TAC o REWRITE_RULE[real_ge]);
         X_GEN_TAC `nn:num` THEN
         MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                         `X:num->A->real`; `&(SUC j)`; `nn:num`; `C:real`]
           BACKWARD_NEG_PART_MAXIMAL) THEN
         ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
         DISCH_TAC THEN
         ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LT_0] THEN
         GEN_REWRITE_TAC (LAND_CONV) [REAL_MUL_SYM] THEN
         ASM_REWRITE_TAC[]]]]];
     REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERS] THEN
     X_GEN_TAC `x:A` THEN
     DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM])) THEN
     REWRITE_TAC[NOT_FORALL_THM; REAL_NOT_LE] THEN DISCH_TAC THEN
     GEN_TAC THEN REWRITE_TAC[SIMPLE_IMAGE; IN_IMAGE; IN_UNIV] THEN
     DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
     REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `&(SUC k)`) THEN
     DISCH_THEN(X_CHOOSE_TAC `nn:num`) THEN
     EXISTS_TAC `nn:num` THEN ASM_REWRITE_TAC[real_ge] THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN
     MATCH_MP_TAC REAL_LTE_TRANS THEN
     EXISTS_TAC `(\m x. max (--(X:num->A->real) m x) (&0)) nn x` THEN
     CONJ_TAC THENL [BETA_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC RUNNING_MAX_GE THEN REWRITE_TAC[LE_REFL]]];
   (* Subset: pos_part bounded + neg_part bounded ==> abs bounded *)
   REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `M1:real`) (X_CHOOSE_TAC `M2:real`)) THEN
   EXISTS_TAC `M1 + M2:real` THEN GEN_TAC THEN
   MP_TAC(SPEC `n:num`
     (ASSUME `!n. pos_part ((X:num->A->real) n x) <= M1`)) THEN
   MP_TAC(SPEC `n:num`
     (ASSUME `!n. max (--(X:num->A->real) n x) (&0) <= M2`)) THEN
   REWRITE_TAC[pos_part] THEN REAL_ARITH_TAC]);;

(* Main convergence theorem for L^1-bounded backward martingale *)
let BACKWARD_MARTINGALE_CONVERGENCE_L1_BOUNDED = prove(
  `!(p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real) C.
    backward_martingale p FF X /\
    (!n. expectation p (\x. abs(X n x)) <= C)
    ==> almost_surely p
          {x | ?L. ((\n. X n x) ---> L) sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC RATIONAL_ENUMERATION THEN
  DISCH_THEN(X_CHOOSE_TAC `g:num->real`) THEN
  (* Step 1: For each k, the downcrossing bound property is a.s. *)
  SUBGOAL_THEN
    `!k. almost_surely (p:A prob_space)
       {x:A | (g:num->real)(NUMFST k) < g(NUMSND k) ==>
              (?B. !n. num_downcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)}`
    ASSUME_TAC THENL
  [X_GEN_TAC `k:num` THEN
   ASM_CASES_TAC `(g:num->real)(NUMFST k) < g(NUMSND k)` THENL
   [(* Case a < b: use FINITE_DOWNCROSSINGS_AS_L1_BACKWARD *)
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x:A | ?B. !n. num_downcrossings (X:num->A->real)
                  ((g:num->real)(NUMFST k)) (g(NUMSND k)) n x <= B}` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                           `X:num->A->real`;
                           `(g:num->real)(NUMFST (k:num))`;
                           `(g:num->real)(NUMSND (k:num))`;
                           `C:real`] FINITE_DOWNCROSSINGS_AS_L1_BACKWARD) THEN
     ASM_REWRITE_TAC[];
     REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    (* Case a >= b: S_k = UNIV, trivially a.s. *)
    SUBGOAL_THEN
      `{x:A | (g:num->real)(NUMFST k) < g(NUMSND k) ==>
              (?B. !n. num_downcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)} = (:A)`
      (fun th -> REWRITE_TAC[th; ALMOST_SURELY_UNIV]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
    ASM_MESON_TAC[]];
   ALL_TAC] THEN
  (* Step 2: a.s. bounded *)
  SUBGOAL_THEN
    `almost_surely (p:A prob_space)
       {x:A | ?M. !n. abs((X:num->A->real) n x) <= M}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                         `X:num->A->real`; `C:real`]
    BACKWARD_MARTINGALE_ALMOST_SURELY_BOUNDED) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: Combine a.s. bounded with a.s. finite rational downcrossings *)
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
    `{x:A | ?M. !n. abs((X:num->A->real) n x) <= M} INTER
     INTERS {{x:A | (g:num->real)(NUMFST k) < g(NUMSND k) ==>
              (?B. !n. num_downcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)}
             | k IN (:num)}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_INTER THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN ASM_REWRITE_TAC[]];
   (* Step 4: Pointwise implication *)
   REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[IN_INTERS] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `M:real`) ASSUME_TAC) THEN
   (* Extract: for all k, the downcrossing bound property holds *)
   SUBGOAL_THEN
     `!k. (g:num->real)(NUMFST k) < g(NUMSND k)
          ==> ?B. !n. num_downcrossings (X:num->A->real)
                        (g(NUMFST k)) (g(NUMSND k)) n x <= B`
     ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `{x:A | (g:num->real)(NUMFST (k:num)) < g(NUMSND k) ==>
              (?B. !n. num_downcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)}`) THEN
    ANTS_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
     EXISTS_TAC `k:num` THEN REFL_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   (* Apply BOUNDED_FINITE_DOWNCROSSINGS_IMP_CONVERGENT *)
   MP_TAC(ISPECL [`\n:num. (X:num->A->real) n x`; `M:real`]
     BOUNDED_FINITE_DOWNCROSSINGS_IMP_CONVERGENT) THEN
   REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    (* Find i,j with g(i) = a, g(j) = b *)
    SUBGOAL_THEN `?i:num. (g:num->real) i = a` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o SPEC `a:real` o
       GEN_REWRITE_RULE I [EXTENSION]) THEN
     REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
     ASM_REWRITE_TAC[IN] THEN MESON_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `?j:num. (g:num->real) j = b` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o SPEC `b:real` o
       GEN_REWRITE_RULE I [EXTENSION]) THEN
     REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
     ASM_REWRITE_TAC[IN] THEN MESON_TAC[];
     ALL_TAC] THEN
    (* Use k = NUMPAIR i j *)
    FIRST_X_ASSUM(MP_TAC o SPEC `NUMPAIR i j`) THEN
    REWRITE_TAC[NUMPAIR_DEST] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `B:num`) THEN
    EXISTS_TAC `B:num` THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[num_downcrossings];
    REWRITE_TAC[]]]);;

let UPCROSSING_PROB_BOUND_L1 = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b n C k.
     submartingale p FF X /\ a < b /\
     (!n. expectation p (\x. abs(X n x)) <= C) /\
     0 < k
     ==> prob p {x | x IN prob_carrier p /\
                     &(num_upcrossings X a b n x) >= &k}
         <= (C + abs(a)) / ((b - a) * &k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF /\ adapted p FF X`
    STRIP_ASSUME_TAC THENL
  [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [submartingale]) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (b - a) * &k` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `0 < k` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(b - a) * expectation (p:A prob_space)
    (\x:A. &(num_upcrossings (X:num->A->real) a b n x))` THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL
   [UNDISCH_TAC `0 < k` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&k * prob (p:A prob_space) {x:A | x IN prob_carrier p /\
     &(num_upcrossings (X:num->A->real) a b n x) >= &k}
     <= expectation p (\x. &(num_upcrossings X a b n x))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`;
       `\x:A. &(num_upcrossings (X:num->A->real) a b n x)`;
       `&k`] MARKOV_GE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
        `X:num->A->real`; `a:real`; `b:real`] INTEGRABLE_NUM_UPCROSSINGS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
      REWRITE_TAC[];
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_POS];
      MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
        `X:num->A->real`; `a:real`; `b:real`; `n:num`; `k:num`]
        NUM_UPCROSSINGS_GE_EVENT) THEN
      ASM_REWRITE_TAC[]];
     REWRITE_TAC[]];
    ABBREV_TAC `PP = prob (p:A prob_space) {x:A | x IN prob_carrier p /\
      &(num_upcrossings (X:num->A->real) a b n x) >= &k}` THEN
    ABBREV_TAC `EE = expectation (p:A prob_space)
      (\x:A. &(num_upcrossings (X:num->A->real) a b n x))` THEN
    SUBGOAL_THEN `PP * (b - a) * &k = (b - a) * (&k * PP)` SUBST1_TAC THENL
    [REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC];
   MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
     `X:num->A->real`; `a:real`; `b:real`; `n:num`; `C:real`]
     UPCROSSING_EXPECTATION_BOUND_L1) THEN
   ASM_REWRITE_TAC[]]);;

let PROB_INCREASING_UNION_BOUND = prove
 (`!p:A prob_space (A:num->A->bool) c.
     (!n. A n IN prob_events p) /\
     (!m n. m <= n ==> A m SUBSET A n) /\
     (!n. prob p (A n) <= c)
     ==> prob p (UNIONS {A n | n IN (:num)}) <= c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_liminf (\n. prob (p:A prob_space) ((A:num->A->bool) n))` THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN `UNIONS {(A:num->A->bool) n | n IN (:num)} = liminf_events A`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `!m. INTERS {(A:num->A->bool) n | n >= m} = A m`
      ASSUME_TAC THENL
    [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INTERS; IN_ELIM_THM] THEN
     X_GEN_TAC `x:A` THEN EQ_TAC THENL
     [DISCH_THEN(MP_TAC o SPEC `(A:num->A->bool) m`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      ANTS_TAC THENL [EXISTS_TAC `m:num` THEN ARITH_TAC; REWRITE_TAC[]];
      DISCH_TAC THEN X_GEN_TAC `t:A->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 ASSUME_TAC
        (fun th -> REWRITE_TAC[th]))) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `n:num >= m` THEN REWRITE_TAC[GE] THEN
      STRIP_TAC THEN ASM SET_TAC[]];
     REWRITE_TAC[liminf_events] THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC FATOU_EVENTS_LIMINF THEN ASM_REWRITE_TAC[]];
   MATCH_MP_TAC REAL_LIMINF_UBOUND THEN
   EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]]);;

let INFINITE_UPCROSSINGS_NULL_L1 = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b C.
     submartingale p FF X /\ a < b /\
     (!n. expectation p (\x. abs(X n x)) <= C)
     ==> !k. 0 < k ==>
         prob p (UNIONS {
           {x | x IN prob_carrier p /\ &(num_upcrossings X a b n x) >= &k}
         | n IN (:num)}) <= (C + abs(a)) / ((b - a) * &k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC PROB_INCREASING_UNION_BOUND THEN
  REPEAT CONJ_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC NUM_UPCROSSINGS_GE_EVENT THEN
   EXISTS_TAC `FF:num->(A->bool)->bool` THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [submartingale]) THEN
   ASM_REWRITE_TAC[];
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_ge]) THEN
   DISCH_TAC THEN REWRITE_TAC[real_ge] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `&(num_upcrossings (X:num->A->real) a b m x)` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[REAL_OF_NUM_LE; num_upcrossings] THEN
   MATCH_MP_TAC UPCROSSING_COUNT_INCREASING THEN ASM_REWRITE_TAC[];
   GEN_TAC THEN MATCH_MP_TAC UPCROSSING_PROB_BOUND_L1 THEN
   EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

let REAL_LE_ZERO_FROM_BOUND = prove
 (`!x c d. &0 < d /\ (!k. 0 < k ==> x <= c / (d * &k)) ==> x <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPEC `c / (d * x):real` REAL_ARCH_LT) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC N`) THEN
  REWRITE_TAC[ARITH_RULE `0 < SUC N`] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN
  SUBGOAL_THEN `&0 < d * &(SUC N)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
   ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d * x` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `c / (d * x) < &N` THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&N * (d * x)` THEN
  CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   SUBGOAL_THEN `&N * d * x = &N * (d * x) /\
     x * d * &(SUC N) = &(SUC N) * (d * x)`
     (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]]);;

let FINITE_UPCROSSINGS_AS_L1 = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b C.
     submartingale p FF X /\ a < b /\
     (!n. expectation p (\x. abs(X n x)) <= C)
     ==> almost_surely p
           {x | ?B:num. !n. num_upcrossings X a b n x <= B}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[almost_surely; null_event; IN_ELIM_THM;
              NOT_EXISTS_THM; NOT_FORALL_THM; NOT_LE] THEN
  EXISTS_TAC `INTERS {UNIONS {
    {x:A | x IN prob_carrier p /\ &(num_upcrossings X a b n x) >= &k}
  | n IN (:num)} | k | 0 < k}` THEN
  MATCH_MP_TAC(TAUT `c /\ (c ==> a /\ b) ==> (a /\ b) /\ c`) THEN
  CONJ_TAC THENL
  [(* Subset part *)
   REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERS; IN_UNIONS; IN_UNIV] THEN
   X_GEN_TAC `x:A` THEN STRIP_TAC THEN
   X_GEN_TAC `t:A->bool` THEN
   DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC
     (fun th -> REWRITE_TAC[th]))) THEN
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
   DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
   EXISTS_TAC `{x:A | x IN prob_carrier p /\
     &(num_upcrossings X a b n x) >= &k}` THEN
   CONJ_TAC THENL
   [EXISTS_TAC `n:num` THEN REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[real_ge; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC];
   DISCH_TAC] THEN
  (* Each Uk is in events *)
  SUBGOAL_THEN `!k. 0 < k ==> UNIONS {{x:A | x IN prob_carrier p /\
    &(num_upcrossings X a b n x) >= &k} | n IN (:num)} IN prob_events p`
    ASSUME_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `s:A->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `nn:num` ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NUM_UPCROSSINGS_GE_EVENT THEN
    EXISTS_TAC `FF:num->(A->bool)->bool` THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [submartingale]) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC `IMAGE (\n. {x:A | x IN prob_carrier p /\
      &(num_upcrossings X a b n x) >= &k}) (:num)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE];
     REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN
     X_GEN_TAC `s:A->bool` THEN
     DISCH_THEN(X_CHOOSE_THEN `nn:num` ASSUME_TAC) THEN
     EXISTS_TAC `nn:num` THEN ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  (* INTERS is in events *)
  SUBGOAL_THEN `INTERS {UNIONS {{x:A | x IN prob_carrier p /\
    &(num_upcrossings X a b n x) >= &k} | n IN (:num)} | 0 < k}
    IN prob_events p` ASSUME_TAC THENL
  [MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `s:A->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `kk:num` (CONJUNCTS_THEN2 ASSUME_TAC
      (fun th -> REWRITE_TAC[th]))) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC `IMAGE (\k. UNIONS {{x:A | x IN prob_carrier p /\
      &(num_upcrossings X a b n x) >= &k} | n IN (:num)}) (:num)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE];
     REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN
     X_GEN_TAC `s:A->bool` THEN
     DISCH_THEN(X_CHOOSE_THEN `kk:num` (CONJUNCTS_THEN2 ASSUME_TAC
       (fun th -> REWRITE_TAC[th]))) THEN
     EXISTS_TAC `kk:num` THEN REWRITE_TAC[]];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `UNIONS {{x:A | x IN prob_carrier p /\
      &(num_upcrossings X a b n x) >= &1} | n IN (:num)}` THEN
    EXISTS_TAC `1` THEN ARITH_TAC];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* Prob = 0 *)
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC REAL_LE_ZERO_FROM_BOUND THEN
   MAP_EVERY EXISTS_TAC [`C + abs(a:real)`; `b - a:real`] THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `prob (p:A prob_space) (UNIONS {{x:A | x IN prob_carrier p /\
     &(num_upcrossings X a b n x) >= &k} | n IN (:num)})` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_MONO THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTERS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `UNIONS {{x:A | x IN prob_carrier p /\
      &(num_upcrossings X a b n x) >= &k} | n IN (:num)}`) THEN
    ANTS_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `k:num` THEN
     ASM_REWRITE_TAC[];
     REWRITE_TAC[]];
    MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
      `X:num->A->real`; `a:real`; `b:real`; `C:real`]
      INFINITE_UPCROSSINGS_NULL_L1) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[]]]);;

(* ---- Step 8: A.s. boundedness for L1-bounded submartingales ---- *)

(* This follows from DOOB_MAXIMAL_POS_PART and
   SUBMARTINGALE_NEG_PART_MAXIMAL via Borel-Cantelli type argument:
   P(exists n. |X_n| >= c) <= C/c + 2C/c = 3C/c -> 0 as c -> inf *)
let SUBMARTINGALE_ALMOST_SURELY_BOUNDED = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) C.
     submartingale p FF X /\
     (!n. expectation p (\x. abs(X n x)) <= C)
     ==> almost_surely p {x | ?M. !n. abs(X n x) <= M}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Reduce to pos_part and neg_part bounds *)
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
    `{x:A | ?M. !n. pos_part((X:num->A->real) n x) <= M} INTER
     {x:A | ?M. !n. max (--(X:num->A->real) n x) (&0) <= M}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_INTER THEN CONJ_TAC THENL
   [(* a.s. pos_part bounded *)
    REWRITE_TAC[almost_surely] THEN
    EXISTS_TAC `INTERS {UNIONS {
      {x:A | x IN prob_carrier p /\
             running_max (\m x. pos_part ((X:num->A->real) m x)) n x
             >= &(SUC k)}
    | n IN (:num)} | k IN (:num)}` THEN
    CONJ_TAC THENL
    [REWRITE_TAC[null_event] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`p:A prob_space`;
        `\k n. {x:A | x IN prob_carrier p /\
           running_max (\m x. pos_part ((X:num->A->real) m x)) n x
           >= &(SUC k)}`] INTERS_UNIONS_IN_EVENTS) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
      MATCH_MP_TAC RUNNING_MAX_POS_PART_EVENT THEN
      EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_0_FROM_INV_BOUND THEN
      EXISTS_TAC `C:real` THEN CONJ_TAC THENL
      [MATCH_MP_TAC PROB_POSITIVE THEN
       MP_TAC(ISPECL [`p:A prob_space`;
         `\k n. {x:A | x IN prob_carrier p /\
            running_max (\m x. pos_part ((X:num->A->real) m x)) n x
            >= &(SUC k)}`] INTERS_UNIONS_IN_EVENTS) THEN
       REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
       MATCH_MP_TAC RUNNING_MAX_POS_PART_EVENT THEN
       EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
       X_GEN_TAC `j:num` THEN
       MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `prob (p:A prob_space) (UNIONS {
         {x:A | x IN prob_carrier p /\
                running_max (\m x. pos_part ((X:num->A->real) m x)) n x
                >= &(SUC j)} | n IN (:num)})` THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC PROB_MONO THEN REPEAT CONJ_TAC THENL
        [MP_TAC(ISPECL [`p:A prob_space`;
           `\k n. {x:A | x IN prob_carrier p /\
              running_max (\m x. pos_part ((X:num->A->real) m x)) n x
              >= &(SUC k)}`] INTERS_UNIONS_IN_EVENTS) THEN
         REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
         MATCH_MP_TAC RUNNING_MAX_POS_PART_EVENT THEN
         EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
         MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN GEN_TAC THEN
         MATCH_MP_TAC RUNNING_MAX_POS_PART_EVENT THEN
         EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
         REWRITE_TAC[SUBSET; IN_INTERS; SIMPLE_IMAGE;
                      FORALL_IN_IMAGE; IN_UNIV] THEN
         GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
         REWRITE_TAC[]];
        MP_TAC(ISPECL [
         `p:A prob_space`;
         `\n. {x:A | x IN prob_carrier p /\
            running_max (\m x. pos_part ((X:num->A->real) m x)) n x
            >= &(SUC j)}`;
         `C / &(SUC j)`] PROB_UNIONS_INCREASING_BOUND) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        REPEAT CONJ_TAC THENL
        [GEN_TAC THEN MATCH_MP_TAC RUNNING_MAX_POS_PART_EVENT THEN
         EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
         GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
         X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
         REWRITE_TAC[real_ge] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
         EXISTS_TAC `running_max (\m x. pos_part ((X:num->A->real) m x))
                       n (x:A)` THEN
         REWRITE_TAC[RUNNING_MAX_MONO_SUC] THEN
         FIRST_X_ASSUM(ACCEPT_TAC o REWRITE_RULE[real_ge]);
         X_GEN_TAC `nn:num` THEN
         MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                         `X:num->A->real`; `&(SUC j)`; `nn:num`; `C:real`]
           DOOB_MAXIMAL_POS_PART) THEN
         ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
         DISCH_TAC THEN
         ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LT_0] THEN
         ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]]]]];
     REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERS] THEN
     X_GEN_TAC `x:A` THEN
     DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM])) THEN
     REWRITE_TAC[NOT_FORALL_THM; REAL_NOT_LE] THEN DISCH_TAC THEN
     GEN_TAC THEN REWRITE_TAC[SIMPLE_IMAGE; IN_IMAGE; IN_UNIV] THEN
     DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
     REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `&(SUC k)`) THEN
     DISCH_THEN(X_CHOOSE_TAC `nn:num`) THEN
     EXISTS_TAC `nn:num` THEN ASM_REWRITE_TAC[real_ge] THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN
     MATCH_MP_TAC REAL_LTE_TRANS THEN
     EXISTS_TAC `(\m x. pos_part ((X:num->A->real) m x)) nn x` THEN
     CONJ_TAC THENL [BETA_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC RUNNING_MAX_GE THEN REWRITE_TAC[LE_REFL]];
    (* a.s. neg_part bounded *)
    REWRITE_TAC[almost_surely] THEN
    EXISTS_TAC `INTERS {UNIONS {
      {x:A | x IN prob_carrier p /\
             running_max (\m x. max (--(X:num->A->real) m x) (&0)) n x
             >= &(SUC k)}
    | n IN (:num)} | k IN (:num)}` THEN
    CONJ_TAC THENL
    [REWRITE_TAC[null_event] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`p:A prob_space`;
        `\k n. {x:A | x IN prob_carrier p /\
           running_max (\m x. max (--(X:num->A->real) m x) (&0)) n x
           >= &(SUC k)}`] INTERS_UNIONS_IN_EVENTS) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
      MATCH_MP_TAC RUNNING_MAX_NEG_PART_EVENT THEN
      EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_0_FROM_INV_BOUND THEN
      EXISTS_TAC `&2 * C` THEN CONJ_TAC THENL
      [MATCH_MP_TAC PROB_POSITIVE THEN
       MP_TAC(ISPECL [`p:A prob_space`;
         `\k n. {x:A | x IN prob_carrier p /\
            running_max (\m x. max (--(X:num->A->real) m x) (&0)) n x
            >= &(SUC k)}`] INTERS_UNIONS_IN_EVENTS) THEN
       REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
       MATCH_MP_TAC RUNNING_MAX_NEG_PART_EVENT THEN
       EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
       X_GEN_TAC `j:num` THEN
       MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `prob (p:A prob_space) (UNIONS {
         {x:A | x IN prob_carrier p /\
                running_max (\m x. max (--(X:num->A->real) m x) (&0)) n x
                >= &(SUC j)} | n IN (:num)})` THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC PROB_MONO THEN REPEAT CONJ_TAC THENL
        [MP_TAC(ISPECL [`p:A prob_space`;
           `\k n. {x:A | x IN prob_carrier p /\
              running_max (\m x. max (--(X:num->A->real) m x) (&0)) n x
              >= &(SUC k)}`] INTERS_UNIONS_IN_EVENTS) THEN
         REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT GEN_TAC THEN
         MATCH_MP_TAC RUNNING_MAX_NEG_PART_EVENT THEN
         EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
         MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN GEN_TAC THEN
         MATCH_MP_TAC RUNNING_MAX_NEG_PART_EVENT THEN
         EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
         REWRITE_TAC[SUBSET; IN_INTERS; SIMPLE_IMAGE;
                      FORALL_IN_IMAGE; IN_UNIV] THEN
         GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
         REWRITE_TAC[]];
        MP_TAC(ISPECL [
         `p:A prob_space`;
         `\n. {x:A | x IN prob_carrier p /\
            running_max (\m x. max (--(X:num->A->real) m x) (&0)) n x
            >= &(SUC j)}`;
         `(&2 * C) / &(SUC j)`] PROB_UNIONS_INCREASING_BOUND) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        REPEAT CONJ_TAC THENL
        [GEN_TAC THEN MATCH_MP_TAC RUNNING_MAX_NEG_PART_EVENT THEN
         EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
         GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
         X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
         REWRITE_TAC[real_ge] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
         EXISTS_TAC `running_max (\m x. max (--(X:num->A->real) m x) (&0))
                       n (x:A)` THEN
         REWRITE_TAC[RUNNING_MAX_MONO_SUC] THEN
         FIRST_X_ASSUM(ACCEPT_TAC o REWRITE_RULE[real_ge]);
         X_GEN_TAC `nn:num` THEN
         MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                         `X:num->A->real`; `&(SUC j)`; `nn:num`; `C:real`]
           SUBMARTINGALE_NEG_PART_MAXIMAL) THEN
         ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
         DISCH_TAC THEN
         ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LT_0] THEN
         GEN_REWRITE_TAC (LAND_CONV) [REAL_MUL_SYM] THEN
         ASM_REWRITE_TAC[]]]]];
     REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERS] THEN
     X_GEN_TAC `x:A` THEN
     DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM])) THEN
     REWRITE_TAC[NOT_FORALL_THM; REAL_NOT_LE] THEN DISCH_TAC THEN
     GEN_TAC THEN REWRITE_TAC[SIMPLE_IMAGE; IN_IMAGE; IN_UNIV] THEN
     DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
     REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `&(SUC k)`) THEN
     DISCH_THEN(X_CHOOSE_TAC `nn:num`) THEN
     EXISTS_TAC `nn:num` THEN ASM_REWRITE_TAC[real_ge] THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN
     MATCH_MP_TAC REAL_LTE_TRANS THEN
     EXISTS_TAC `(\m x. max (--(X:num->A->real) m x) (&0)) nn x` THEN
     CONJ_TAC THENL [BETA_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC RUNNING_MAX_GE THEN REWRITE_TAC[LE_REFL]]];
   (* Subset: pos_part bounded + neg_part bounded ==> abs bounded *)
   REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `M1:real`) (X_CHOOSE_TAC `M2:real`)) THEN
   EXISTS_TAC `M1 + M2:real` THEN GEN_TAC THEN
   MP_TAC(SPEC `n:num`
     (ASSUME `!n. pos_part ((X:num->A->real) n x) <= M1`)) THEN
   MP_TAC(SPEC `n:num`
     (ASSUME `!n. max (--(X:num->A->real) n x) (&0) <= M2`)) THEN
   REWRITE_TAC[pos_part] THEN REAL_ARITH_TAC]);;

(* ---- Step 9: Main convergence theorem ---- *)

let SUBMARTINGALE_CONVERGENCE_L1_BOUNDED = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) C.
     submartingale p FF X /\
     (!n. expectation p (\x. abs(X n x)) <= C)
     ==> almost_surely p
           {x | ?L. ((\n. X n x) ---> L) sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC RATIONAL_ENUMERATION THEN
  DISCH_THEN(X_CHOOSE_TAC `g:num->real`) THEN
  (* Step 1: For each k, the upcrossing bound property is a.s. *)
  SUBGOAL_THEN
    `!k. almost_surely (p:A prob_space)
       {x:A | (g:num->real)(NUMFST k) < g(NUMSND k) ==>
              (?B. !n. num_upcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)}`
    ASSUME_TAC THENL
  [X_GEN_TAC `k:num` THEN
   ASM_CASES_TAC `(g:num->real)(NUMFST k) < g(NUMSND k)` THENL
   [(* Case a < b: use FINITE_UPCROSSINGS_AS_L1 *)
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x:A | ?B. !n. num_upcrossings (X:num->A->real)
                  ((g:num->real)(NUMFST k)) (g(NUMSND k)) n x <= B}` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                           `X:num->A->real`;
                           `(g:num->real)(NUMFST (k:num))`;
                           `(g:num->real)(NUMSND (k:num))`;
                           `C:real`] FINITE_UPCROSSINGS_AS_L1) THEN
     ASM_REWRITE_TAC[];
     REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    (* Case a >= b: S_k = UNIV, so a.s. trivially *)
    SUBGOAL_THEN
      `{x:A | (g:num->real)(NUMFST k) < g(NUMSND k) ==>
              (?B. !n. num_upcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)} = (:A)`
      (fun th -> REWRITE_TAC[th; ALMOST_SURELY_UNIV]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
    ASM_MESON_TAC[]];
   ALL_TAC] THEN
  (* Step 2: a.s. bounded *)
  SUBGOAL_THEN
    `almost_surely (p:A prob_space)
       {x:A | ?M. !n. abs((X:num->A->real) n x) <= M}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                         `X:num->A->real`; `C:real`]
    SUBMARTINGALE_ALMOST_SURELY_BOUNDED) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: Combine a.s. bounded with a.s. finite rational upcrossings *)
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
    `{x:A | ?M. !n. abs((X:num->A->real) n x) <= M} INTER
     INTERS {{x:A | (g:num->real)(NUMFST k) < g(NUMSND k) ==>
              (?B. !n. num_upcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)}
             | k IN (:num)}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_INTER THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN ASM_REWRITE_TAC[]];
   (* Step 4: Pointwise implication *)
   REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[IN_INTERS] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `M:real`) ASSUME_TAC) THEN
   (* Extract: for all k, the upcrossing bound property holds *)
   SUBGOAL_THEN
     `!k. (g:num->real)(NUMFST k) < g(NUMSND k)
          ==> ?B. !n. num_upcrossings (X:num->A->real)
                        (g(NUMFST k)) (g(NUMSND k)) n x <= B`
     ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `{x:A | (g:num->real)(NUMFST (k:num)) < g(NUMSND k) ==>
              (?B. !n. num_upcrossings (X:num->A->real)
                         (g(NUMFST k)) (g(NUMSND k)) n x <= B)}`) THEN
    ANTS_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
     EXISTS_TAC `k:num` THEN REFL_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   (* Apply BOUNDED_FINITE_UPCROSSINGS_IMP_CONVERGENT *)
   MP_TAC(ISPECL [`\n:num. (X:num->A->real) n x`; `M:real`]
     BOUNDED_FINITE_UPCROSSINGS_IMP_CONVERGENT) THEN
   REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    (* Find i,j with g(i) = a, g(j) = b *)
    SUBGOAL_THEN `?i:num. (g:num->real) i = a` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o SPEC `a:real` o
       GEN_REWRITE_RULE I [EXTENSION]) THEN
     REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
     ASM_REWRITE_TAC[IN] THEN MESON_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `?j:num. (g:num->real) j = b` STRIP_ASSUME_TAC THENL
    [FIRST_ASSUM(MP_TAC o SPEC `b:real` o
       GEN_REWRITE_RULE I [EXTENSION]) THEN
     REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
     ASM_REWRITE_TAC[IN] THEN MESON_TAC[];
     ALL_TAC] THEN
    (* Use k = NUMPAIR i j *)
    FIRST_X_ASSUM(MP_TAC o SPEC `NUMPAIR i j`) THEN
    REWRITE_TAC[NUMPAIR_DEST] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `B:num`) THEN
    EXISTS_TAC `B:num` THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[num_upcrossings];
    REWRITE_TAC[]]]);;

(* ---- Step 10: UI submartingale convergence ---- *)

let UI_SUBMARTINGALE_CONVERGENCE_AS = prove
 (`!p:A prob_space FF X.
    uniformly_integrable p X /\ submartingale p FF X
    ==> almost_surely p {x | ?L. ((\n. X n x) ---> L) sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP UI_IMP_L1_BOUNDED) THEN
  DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN
  MATCH_MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                        `X:num->A->real`; `C:real`]
    SUBMARTINGALE_CONVERGENCE_L1_BOUNDED) THEN
  ASM_REWRITE_TAC[]);;

let UI_BACKWARD_MARTINGALE_CONVERGENCE_AS = prove
 (`!p:A prob_space FF X.
    uniformly_integrable p X /\ backward_martingale p FF X
    ==> almost_surely p {x | ?L. ((\n. X n x) ---> L) sequentially}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP UI_IMP_L1_BOUNDED) THEN
  DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN
  MATCH_MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                        `X:num->A->real`; `C:real`]
    BACKWARD_MARTINGALE_CONVERGENCE_L1_BOUNDED) THEN
  ASM_REWRITE_TAC[]);;

(* ==================================================================== *)
(* Unbounded optional stopping under uniform integrability (Gap 3)      *)
(* Williams Ch 10, Theorem 10.10                                        *)
(* ==================================================================== *)

(* Arithmetic helpers for MIN on natural numbers *)

let MIN_LE_RIGHT = prove
 (`!t N n:num. N <= n ==> MIN t N <= n`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `MIN t N <= N ==> N <= n ==> MIN t N <= n`) THEN
  ARITH_TAC);;

let MIN_LE_IFF = prove
 (`!t N n:num. ~(N <= n) ==> (MIN t N <= n <=> t <= n)`,
  REPEAT GEN_TAC THEN SIMP_TAC[MIN] THEN ARITH_TAC);;

(* Truncation of stopping time: MIN(tau, N) is a bounded stopping time *)

let STOPPING_TIME_MIN = prove
 (`!p FF (tau:A->num) N.
    stopping_time p FF tau /\ filtration p FF
    ==> bounded_stopping_time p FF (\x. MIN (tau x) N) N`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[bounded_stopping_time] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[stopping_time] THEN X_GEN_TAC `n:num` THEN
   ASM_CASES_TAC `N:num <= n` THENL
   [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ MIN (tau x) N <= n} =
      prob_carrier p` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN
     EQ_TAC THENL
     [SIMP_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `N:num <= n`
        (fun th -> SIMP_TAC[th; MIN_LE_RIGHT]) THEN
      ASM_REWRITE_TAC[]];
     ASM_MESON_TAC[filtration; SUB_SIGMA_ALGEBRA_CARRIER_IN]];
    SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ MIN (tau x) N <= n} =
      {x | x IN prob_carrier p /\ tau x <= n}` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN
     AP_TERM_TAC THEN
     SUBGOAL_THEN `~(N:num <= n)`
       (fun th -> SIMP_TAC[th; MIN_LE_IFF]) THEN
     ASM_REWRITE_TAC[];
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [stopping_time]) THEN
     DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[]]];
   GEN_TAC THEN DISCH_TAC THEN ARITH_TAC]);;

(* Stopped process with truncated tau at N agrees with original *)

let STOPPED_PROCESS_TRUNCATION_AGREE = prove
 (`!X (tau:A->num) N x.
    stopped_process X (\x. MIN (tau x) N) N x = stopped_process X tau N x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stopped_process] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* Pointwise convergence of stopped process to X(tau(x), x) *)

let STOPPED_PROCESS_POINTWISE_LIMIT = prove
 (`!X (tau:A->num) x.
    ((\n. stopped_process X tau n x) ---> X (tau x) x) sequentially`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REALLIM_EVENTUALLY THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `(tau:A->num) x` THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[stopped_process] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* Main theorem: unbounded optional stopping for martingales *)

let OPTIONAL_STOPPING_UI = prove
 (`!p FF X (tau:A->num).
    martingale p FF X /\ stopping_time p FF tau /\
    uniformly_integrable p (\n. stopped_process X tau n)
    ==> integrable p (\x. X (tau x) x) /\
        expectation p (\x. X (tau x) x) = expectation p (X 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `integrable p (\x:A. X (tau x) x) /\
    ((\n. expectation p (\x. abs(stopped_process X tau n x - X (tau x) x)))
     ---> &0) sequentially`
   STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC UI_POINTWISE_L1 THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `(\n x:A. stopped_process X tau n x) = (\n. stopped_process X tau n)`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; ETA_AX]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[STOPPED_PROCESS_POINTWISE_LIMIT];
   ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. expectation p (stopped_process (X:num->A->real) tau n) =
        expectation p (X 0)`
   ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(SPECL [`p:(A)prob_space`; `FF:num->(A->bool)->bool`;
                 `X:num->A->real`; `\x:A. MIN (tau x) n`; `n:num`]
     DOOB_OPTIONAL_STOPPING) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC STOPPING_TIME_MIN THEN
    ASM_MESON_TAC[martingale];
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
    SUBGOAL_THEN
      `stopped_process X (\x:A. MIN (tau x) n) n = stopped_process X tau n`
      (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[FUN_EQ_THM; STOPPED_PROCESS_TRUNCATION_AGREE]];
   ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC
    `\n. expectation p (stopped_process (X:num->A->real) tau n)` THEN
  CONJ_TAC THENL [REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY]; ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN
   DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
   DISCH_THEN(fun th ->
     MP_TAC(MATCH_MP (SPEC `e:real` th) (ASSUME `&0 < e`))) THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
   MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
   MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC
     `expectation p
       (\x:A. abs(stopped_process X tau n x - X (tau x) x))` THEN
   CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
   SUBGOAL_THEN
     `expectation p (stopped_process (X:num->A->real) tau n) -
      expectation p (\x. X (tau x) x) =
      expectation p (\x. stopped_process X tau n x - X (tau x) x)`
     SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MP_TAC(SPECL [`p:(A)prob_space`;
                  `stopped_process (X:num->A->real) tau n`;
                  `\x:A. (X:num->A->real) (tau x) x`] EXPECTATION_SUB) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [uniformly_integrable]) THEN
     SIMP_TAC[];
     REWRITE_TAC[]];
    MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [uniformly_integrable]) THEN
    SIMP_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ETA_AX]];
   ASM_REWRITE_TAC[REALLIM_CONST]]);;

(* Submartingale variant *)

let SUBMARTINGALE_OPTIONAL_STOPPING_UI = prove
 (`!p FF X (tau:A->num).
    submartingale p FF X /\ stopping_time p FF tau /\
    uniformly_integrable p (\n. stopped_process X tau n)
    ==> integrable p (\x. X (tau x) x) /\
        expectation p (X 0) <= expectation p (\x. X (tau x) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `integrable p (\x:A. X (tau x) x) /\
    ((\n. expectation p (\x. abs(stopped_process X tau n x - X (tau x) x)))
     ---> &0) sequentially`
   STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC UI_POINTWISE_L1 THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `(\n x:A. stopped_process X tau n x) = (\n. stopped_process X tau n)`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; ETA_AX]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[STOPPED_PROCESS_POINTWISE_LIMIT];
   ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. expectation p ((X:num->A->real) 0) <=
        expectation p (stopped_process X tau n)`
   ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(SPECL [`p:(A)prob_space`; `FF:num->(A->bool)->bool`;
                 `X:num->A->real`; `\x:A. MIN (tau x) n`; `n:num`]
     SUBMARTINGALE_OPTIONAL_STOPPING_GE) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC STOPPING_TIME_MIN THEN
    ASM_MESON_TAC[submartingale; martingale];
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
    SUBGOAL_THEN
      `stopped_process X (\x:A. MIN (tau x) n) n = stopped_process X tau n`
      (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[FUN_EQ_THM; STOPPED_PROCESS_TRUNCATION_AGREE]];
   ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  EXISTS_TAC `\n:num. expectation p ((X:num->A->real) 0)` THEN
  EXISTS_TAC
    `\n:num. expectation p (stopped_process (X:num->A->real) tau n)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; REALLIM_CONST] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN
   DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
   DISCH_THEN(fun th ->
     MP_TAC(MATCH_MP (SPEC `e:real` th) (ASSUME `&0 < e`))) THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
   MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
   MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC
     `expectation p
       (\x:A. abs(stopped_process X tau n x - X (tau x) x))` THEN
   CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
   SUBGOAL_THEN
     `expectation p (stopped_process (X:num->A->real) tau n) -
      expectation p (\x. X (tau x) x) =
      expectation p (\x. stopped_process X tau n x - X (tau x) x)`
     SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MP_TAC(SPECL [`p:(A)prob_space`;
                  `stopped_process (X:num->A->real) tau n`;
                  `\x:A. (X:num->A->real) (tau x) x`] EXPECTATION_SUB) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [uniformly_integrable]) THEN
     SIMP_TAC[];
     REWRITE_TAC[]];
    MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [uniformly_integrable]) THEN
    SIMP_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ETA_AX]];
   ASM_REWRITE_TAC[EVENTUALLY_TRUE]]);;

(* Supermartingale variant *)

let SUPERMARTINGALE_OPTIONAL_STOPPING_UI = prove
 (`!p FF X (tau:A->num).
    supermartingale p FF X /\ stopping_time p FF tau /\
    uniformly_integrable p (\n. stopped_process X tau n)
    ==> integrable p (\x. X (tau x) x) /\
        expectation p (\x. X (tau x) x) <= expectation p (X 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `integrable p (\x:A. X (tau x) x) /\
    ((\n. expectation p (\x. abs(stopped_process X tau n x - X (tau x) x)))
     ---> &0) sequentially`
   STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC UI_POINTWISE_L1 THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `(\n x:A. stopped_process X tau n x) = (\n. stopped_process X tau n)`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; ETA_AX]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[STOPPED_PROCESS_POINTWISE_LIMIT];
   ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. expectation p (stopped_process (X:num->A->real) tau n) <=
        expectation p (X 0)`
   ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(SPECL [`p:(A)prob_space`; `FF:num->(A->bool)->bool`;
                 `X:num->A->real`; `\x:A. MIN (tau x) n`; `n:num`]
     SUPERMARTINGALE_OPTIONAL_STOPPING_LE) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC STOPPING_TIME_MIN THEN
    ASM_MESON_TAC[supermartingale; martingale];
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
    SUBGOAL_THEN
      `stopped_process X (\x:A. MIN (tau x) n) n = stopped_process X tau n`
      (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[FUN_EQ_THM; STOPPED_PROCESS_TRUNCATION_AGREE]];
   ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  EXISTS_TAC
    `\n:num. expectation p (stopped_process (X:num->A->real) tau n)` THEN
  EXISTS_TAC `\n:num. expectation p ((X:num->A->real) 0)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; REALLIM_CONST] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN
   DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
   DISCH_THEN(fun th ->
     MP_TAC(MATCH_MP (SPEC `e:real` th) (ASSUME `&0 < e`))) THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
   MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
   MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC
     `expectation p
       (\x:A. abs(stopped_process X tau n x - X (tau x) x))` THEN
   CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
   SUBGOAL_THEN
     `expectation p (stopped_process (X:num->A->real) tau n) -
      expectation p (\x. X (tau x) x) =
      expectation p (\x. stopped_process X tau n x - X (tau x) x)`
     SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MP_TAC(SPECL [`p:(A)prob_space`;
                  `stopped_process (X:num->A->real) tau n`;
                  `\x:A. (X:num->A->real) (tau x) x`] EXPECTATION_SUB) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [uniformly_integrable]) THEN
     SIMP_TAC[];
     REWRITE_TAC[]];
    MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [uniformly_integrable]) THEN
    SIMP_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ETA_AX]];
   ASM_REWRITE_TAC[EVENTUALLY_TRUE]]);;


(* ========================================================================= *)
(* GENERAL DOOB DECOMPOSITION                                                *)
(* Removes FINITE(FF n) and simple_rv restrictions from DOOB_DECOMPOSITION.  *)
(* Uses gen_cond_exp instead of simple_cond_exp. Williams Ch 12, Thm 12.14.  *)
(* ========================================================================= *)

(* General predictable: H_{n+1} is FF_n-measurable (no simple_rv requirement) *)
let gen_predictable = new_definition
  `gen_predictable (p:A prob_space) (FF:num->(A->bool)->bool) (H:num->A->real) <=>
   measurable_wrt p (FF 0) (H 0) /\
   (!n. measurable_wrt p (FF n) (H (SUC n)))`;;

(* General Doob compensator: A_0 = 0, A_{n+1} = A_n + E[X_{n+1}|FF_n] - X_n *)
let gen_doob_compensator = define
  `(gen_doob_compensator (p:A prob_space) (FF:num->(A->bool)->bool)
     (X:num->A->real) 0 (x:A) = &0) /\
   (gen_doob_compensator p FF X (SUC n) x =
     gen_doob_compensator p FF X n x +
     gen_cond_exp p (FF n) (X (SUC n)) x - X n x)`;;

(* Submartingale property via gen_cond_exp: E[X_{n+1}|FF_n] >= X_n a.s. *)
let SUBMARTINGALE_GEN_COND_EXP_GE = prove
 (`!p:A prob_space FF (X:num->A->real) n.
    submartingale p FF X
    ==> almost_surely p
          {x | X n x <= gen_cond_exp p (FF n) (X (SUC n)) x}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[almost_surely] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\
            ~(x IN {x | (X:num->A->real) n x <=
                        gen_cond_exp p ((FF:num->(A->bool)->bool) n) (X (SUC n)) x})} =
     {x | x IN prob_carrier p /\
          gen_cond_exp p (FF n) (X (SUC n)) x - X n x < &0}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space) ((FF:num->(A->bool)->bool) n)` ASSUME_TAC THENL
  [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) ((X:num->A->real) (SUC n))` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) ((X:num->A->real) n)` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `measurable_wrt (p:A prob_space) ((FF:num->(A->bool)->bool) n) ((X:num->A->real) n)` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale; adapted]; ALL_TAC] THEN
  ABBREV_TAC
    `A_k = \k:num. {x:A | x IN prob_carrier p /\
                           gen_cond_exp p ((FF:num->(A->bool)->bool) n)
                             ((X:num->A->real) (SUC n)) x - X n x <
                           --inv(&(SUC k))}` THEN
  EXISTS_TAC `UNIONS {(A_k:num->A->bool) k | k IN (:num)}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC NULL_EVENT_COUNTABLE_UNION THEN X_GEN_TAC `k:num` THEN
   SUBGOAL_THEN
     `(A_k:num->A->bool) k =
      {x:A | x IN prob_carrier p /\
             gen_cond_exp p ((FF:num->(A->bool)->bool) n)
               ((X:num->A->real) (SUC n)) x - X n x < --inv(&(SUC k))}`
     SUBST1_TAC THENL
   [EXPAND_TAC "A_k" THEN BETA_TAC THEN REFL_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\
             gen_cond_exp p ((FF:num->(A->bool)->bool) n)
               ((X:num->A->real) (SUC n)) x - X n x < --inv (&(SUC k))} IN
      FF n`
     ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `(FF:num->(A->bool)->bool) n`;
      `gen_cond_exp p ((FF:num->(A->bool)->bool) n)
               ((X:num->A->real) (SUC n))`;
      `(X:num->A->real) n`;
      `--inv(&(SUC k))`] MEASURABLE_WRT_DIFF_LT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC GEN_COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\
             gen_cond_exp p ((FF:num->(A->bool)->bool) n)
               ((X:num->A->real) (SUC n)) x - X n x < --inv(&(SUC k))} IN
      prob_events p`
     ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
   REWRITE_TAC[null_event] THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < inv(&(SUC k))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `prob (p:A prob_space)
       {x:A | x IN prob_carrier p /\
              gen_cond_exp p ((FF:num->(A->bool)->bool) n)
                ((X:num->A->real) (SUC n)) x - X n x < --inv(&(SUC k))} <= &0 <=>
      inv(&(SUC k)) * prob p
       {x | x IN prob_carrier p /\
            gen_cond_exp p (FF n) (X (SUC n)) x - X n x < --inv(&(SUC k))} <=
      inv(&(SUC k)) * &0`
     SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LE_LMUL_EQ THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_MUL_RZERO]] THEN
   (* conditioning: E[gen_cond_exp * 1_A] = E[X_{n+1} * 1_A] *)
   SUBGOAL_THEN
     `expectation p (\x:A. gen_cond_exp p ((FF:num->(A->bool)->bool) n)
        ((X:num->A->real) (SUC n)) x *
        indicator_fn
          {x | x IN prob_carrier p /\
               gen_cond_exp p (FF n) (X (SUC n)) x - X n x < --inv(&(SUC k))} x) =
      expectation p (\x. X (SUC n) x *
        indicator_fn
          {x | x IN prob_carrier p /\
               gen_cond_exp p (FF n) (X (SUC n)) x - X n x < --inv(&(SUC k))} x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* submartingale inequality *)
   SUBGOAL_THEN
     `expectation p (\x:A. (X:num->A->real) n x *
        indicator_fn
          {x | x IN prob_carrier p /\
               gen_cond_exp p ((FF:num->(A->bool)->bool) n) (X (SUC n)) x - X n x <
               --inv(&(SUC k))} x) <=
      expectation p (\x. X (SUC n) x *
        indicator_fn
          {x | x IN prob_carrier p /\
               gen_cond_exp p (FF n) (X (SUC n)) x - X n x < --inv(&(SUC k))} x)`
     ASSUME_TAC THENL
   [UNDISCH_TAC `submartingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real)` THEN
    REWRITE_TAC[submartingale] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* integrabilities *)
   ABBREV_TAC `B = {x:A | x IN prob_carrier p /\
     gen_cond_exp p ((FF:num->(A->bool)->bool) n)
       ((X:num->A->real) (SUC n)) x - X n x < --inv(&(SUC k))}` THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (X:num->A->real) n x * indicator_fn (B:A->bool) x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. gen_cond_exp p ((FF:num->(A->bool)->bool) n)
     ((X:num->A->real) (SUC n)) x * indicator_fn (B:A->bool) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* inv(k+1)*P(B) = E[inv(k+1)*1_B] *)
   SUBGOAL_THEN
     `inv(&(SUC k)) * prob (p:A prob_space) (B:A->bool) =
      expectation p (\x:A. inv(&(SUC k)) * indicator_fn B x)`
     SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`p:A prob_space`; `inv(&(SUC k))`;
      `indicator_fn (B:A->bool):A->real`] EXPECTATION_CMUL) THEN
    BETA_TAC THEN ANTS_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[EXPECTATION_INDICATOR]]; ALL_TAC] THEN
   (* E[(X_n - gen_cond_exp) * 1_B] = E[X_n*1_B] - E[gen_cond_exp*1_B] *)
   SUBGOAL_THEN
     `expectation (p:A prob_space)
       (\x:A. (X:num->A->real) n x * indicator_fn (B:A->bool) x) -
      expectation p (\x. gen_cond_exp p ((FF:num->(A->bool)->bool) n) (X (SUC n)) x *
                          indicator_fn B x) =
      expectation p (\x. X n x * indicator_fn B x -
                          gen_cond_exp p (FF n) (X (SUC n)) x *
                          indicator_fn B x)`
     SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXPECTATION_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Main: E[inv(k+1)*1_B] <= E[(X_n - gen_cond_exp)*1_B] <= 0 *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC
     `expectation (p:A prob_space)
       (\x:A. (X:num->A->real) n x * indicator_fn (B:A->bool) x -
              gen_cond_exp p ((FF:num->(A->bool)->bool) n) (X (SUC n)) x *
              indicator_fn B x)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`; `inv(&(SUC k))`;
       `indicator_fn (B:A->bool):A->real`] INTEGRABLE_CMUL_ALT) THEN
     BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
     MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[];
     X_GEN_TAC `w:A` THEN DISCH_TAC THEN
     REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THENL
     [REWRITE_TAC[REAL_MUL_RID] THEN
      SUBGOAL_THEN `(w:A) IN (B:A->bool)` MP_TAC THENL
      [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      UNDISCH_TAC `gen_cond_exp p ((FF:num->(A->bool)->bool) n)
        ((X:num->A->real) (SUC n)) (w:A) - X n w < --inv (&(SUC k))` THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC]];
    SUBGOAL_THEN
      `expectation (p:A prob_space)
         (\x:A. (X:num->A->real) n x * indicator_fn (B:A->bool) x -
                gen_cond_exp p ((FF:num->(A->bool)->bool) n) (X (SUC n)) x *
                indicator_fn B x) =
       expectation p (\x. X n x * indicator_fn B x) -
       expectation p (\x. gen_cond_exp p (FF n) (X (SUC n)) x *
                            indicator_fn B x)`
      SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_SUB THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    UNDISCH_TAC `expectation (p:A prob_space)
      (\x:A. gen_cond_exp p ((FF:num->(A->bool)->bool) n)
        ((X:num->A->real) (SUC n)) x * indicator_fn (B:A->bool) x) =
      expectation p (\x. X (SUC n) x * indicator_fn B x)` THEN
    UNDISCH_TAC `expectation (p:A prob_space)
      (\x:A. (X:num->A->real) n x * indicator_fn (B:A->bool) x) <=
      expectation p (\x. X (SUC n) x * indicator_fn B x)` THEN
    REAL_ARITH_TAC];
   (* Subset: {f < 0} SUBSET UNIONS {A_k k | k IN UNIV} *)
   REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN
   X_GEN_TAC `w:A` THEN STRIP_TAC THEN
   SUBGOAL_THEN `&0 < (X:num->A->real) n w -
     gen_cond_exp p ((FF:num->(A->bool)->bool) n) (X (SUC n)) w` MP_TAC THENL
   [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
   DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `(A_k:num->A->bool) (j - 1)` THEN CONJ_TAC THENL
   [EXISTS_TAC `j - 1` THEN REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
   EXPAND_TAC "A_k" THEN BETA_TAC THEN
   REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `SUC (j - 1) = j` SUBST1_TAC THENL
   [UNDISCH_TAC `~(j = 0)` THEN ARITH_TAC;
    UNDISCH_TAC `inv (&j) < (X:num->A->real) n w -
      gen_cond_exp p ((FF:num->(A->bool)->bool) n) (X (SUC n)) w` THEN
    REAL_ARITH_TAC]]);;

(* Lemma A: gen_doob_compensator is integrable *)
let GEN_DOOB_COMPENSATOR_INTEGRABLE = prove
 (`!p:A prob_space FF (X:num->A->real) n.
    submartingale p FF X
    ==> integrable p (gen_doob_compensator p FF X n)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN STRIP_TAC THENL
  [(* Base case *)
   SUBGOAL_THEN `gen_doob_compensator (p:A prob_space) FF X 0 = (\x:A. &0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; gen_doob_compensator]; ALL_TAC] THEN
   REWRITE_TAC[INTEGRABLE_CONST];
   (* Step case *)
   SUBGOAL_THEN `integrable (p:A prob_space) (gen_doob_compensator p FF X n)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `gen_doob_compensator (p:A prob_space) FF X (SUC n) =
       (\x:A. gen_doob_compensator p FF X n x +
              gen_cond_exp p (FF n) (X (SUC n)) x - X n x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; gen_doob_compensator]; ALL_TAC] THEN
   SUBGOAL_THEN `(\x:A. gen_doob_compensator (p:A prob_space) FF X n x +
       gen_cond_exp p (FF n) (X (SUC n)) x - X n x) =
     (\x. (gen_doob_compensator p FF X n x + gen_cond_exp p (FF n) (X (SUC n)) x) - X n x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`;
                    `gen_doob_compensator (p:A prob_space) FF X n`;
                    `gen_cond_exp (p:A prob_space) (FF (n:num)) ((X:num->A->real) (SUC n))`]
                   INTEGRABLE_ADD) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN
    ASM_MESON_TAC[submartingale; filtration];
    REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[submartingale]]]);;

(* Helper: gen_doob_compensator is measurable_wrt FF n at step n *)
let GEN_DOOB_COMPENSATOR_MEASURABLE_WRT = prove
 (`!p:A prob_space FF (X:num->A->real) n.
    submartingale p FF X
    ==> measurable_wrt p (FF n) (gen_doob_compensator p FF X n)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN STRIP_TAC THENL
  [(* Base case *)
   SUBGOAL_THEN `gen_doob_compensator (p:A prob_space) FF X 0 = (\x:A. &0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; gen_doob_compensator]; ALL_TAC] THEN
   MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_MESON_TAC[submartingale; filtration];
   (* Step case *)
   SUBGOAL_THEN `measurable_wrt (p:A prob_space) (FF n) (gen_doob_compensator p FF X n)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
   [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
   SUBGOAL_THEN `(FF:num->(A->bool)->bool) n SUBSET FF (SUC n)` ASSUME_TAC THENL
   [MATCH_MP_TAC FILTRATION_MONO THEN EXISTS_TAC `p:A prob_space` THEN
    ASM_REWRITE_TAC[LE; LE_REFL]; ALL_TAC] THEN
   SUBGOAL_THEN `measurable_wrt (p:A prob_space) (FF (SUC n)) (gen_doob_compensator p FF X n)` ASSUME_TAC THENL
   [UNDISCH_TAC `measurable_wrt (p:A prob_space) (FF n) (gen_doob_compensator p FF X n)` THEN
    UNDISCH_TAC `(FF:num->(A->bool)->bool) n SUBSET FF (SUC n)` THEN
    REWRITE_TAC[measurable_wrt; SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
   GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
   REWRITE_TAC[gen_doob_compensator] THEN
   SUBGOAL_THEN `(\x:A. gen_doob_compensator (p:A prob_space) FF X n x +
       gen_cond_exp p (FF n) (X (SUC n)) x - X n x) =
     (\x. (gen_doob_compensator p FF X n x + gen_cond_exp p (FF n) (X (SUC n)) x) - X n x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space) ((FF:num->(A->bool)->bool) (SUC n))` ASSUME_TAC THENL
   [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
   SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space) ((FF:num->(A->bool)->bool) n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) ((X:num->A->real) (SUC n))` ASSUME_TAC THENL
   [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
   SUBGOAL_THEN `measurable_wrt (p:A prob_space) (FF (SUC n)) (gen_cond_exp p (FF n) (X (SUC n)))` ASSUME_TAC THENL
   [SUBGOAL_THEN `measurable_wrt (p:A prob_space) ((FF:num->(A->bool)->bool) n)
       (gen_cond_exp p (FF n) ((X:num->A->real) (SUC n)))` MP_TAC THENL
    [MATCH_MP_TAC GEN_COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[];
     UNDISCH_TAC `(FF:num->(A->bool)->bool) n SUBSET FF (SUC n)` THEN
     REWRITE_TAC[measurable_wrt; SUBSET] THEN MESON_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `measurable_wrt (p:A prob_space) (FF (SUC n)) ((X:num->A->real) n)` ASSUME_TAC THENL
   [SUBGOAL_THEN `measurable_wrt (p:A prob_space) ((FF:num->(A->bool)->bool) n) ((X:num->A->real) n)` MP_TAC THENL
    [ASM_MESON_TAC[submartingale; adapted]; ALL_TAC] THEN
    UNDISCH_TAC `(FF:num->(A->bool)->bool) n SUBSET FF (SUC n)` THEN
    REWRITE_TAC[measurable_wrt; SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(FF:num->(A->bool)->bool) (SUC n)`;
                   `\x:A. gen_doob_compensator (p:A prob_space) FF X n x + gen_cond_exp p (FF n) (X (SUC n)) x`;
                   `(X:num->A->real) n`] MEASURABLE_WRT_SUB) THEN
   REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(FF:num->(A->bool)->bool) (SUC n)`;
                   `gen_doob_compensator (p:A prob_space) FF X n`;
                   `gen_cond_exp (p:A prob_space) ((FF:num->(A->bool)->bool) n) ((X:num->A->real) (SUC n))`]
                  MEASURABLE_WRT_ADD) THEN
   REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]]);;

(* Lemma B: gen_doob_compensator is gen_predictable *)
let GEN_DOOB_COMPENSATOR_GEN_PREDICTABLE = prove
 (`!p:A prob_space FF (X:num->A->real).
    submartingale p FF X
    ==> gen_predictable p FF (gen_doob_compensator p FF X)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[gen_predictable] THEN CONJ_TAC THENL
  [(* Base: measurable_wrt p (FF 0) (compensator 0) *)
   SUBGOAL_THEN `gen_doob_compensator (p:A prob_space) FF X 0 = (\x:A. &0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; gen_doob_compensator]; ALL_TAC] THEN
   MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_MESON_TAC[submartingale; filtration];
   (* Step: measurable_wrt p (FF n) (compensator (SUC n)) *)
   GEN_TAC THEN
   GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
   REWRITE_TAC[gen_doob_compensator] THEN
   SUBGOAL_THEN `(\x:A. gen_doob_compensator (p:A prob_space) FF X n x +
       gen_cond_exp p (FF n) (X (SUC n)) x - X n x) =
     (\x. (gen_doob_compensator p FF X n x + gen_cond_exp p (FF n) (X (SUC n)) x) - X n x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space) ((FF:num->(A->bool)->bool) n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[submartingale; filtration]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(FF:num->(A->bool)->bool) n`;
                   `\x:A. gen_doob_compensator (p:A prob_space) FF X n x + gen_cond_exp p (FF n) (X (SUC n)) x`;
                   `(X:num->A->real) n`] MEASURABLE_WRT_SUB) THEN
   REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `(FF:num->(A->bool)->bool) n`;
                    `gen_doob_compensator (p:A prob_space) FF X n`;
                    `gen_cond_exp (p:A prob_space) ((FF:num->(A->bool)->bool) n) ((X:num->A->real) (SUC n))`]
                   MEASURABLE_WRT_ADD) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [ASM_SIMP_TAC[GEN_DOOB_COMPENSATOR_MEASURABLE_WRT];
     MATCH_MP_TAC GEN_COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[submartingale]];
    ASM_MESON_TAC[submartingale; adapted]]]);;

(* Lemma C: gen_doob_compensator is a.e. increasing *)
let GEN_DOOB_COMPENSATOR_AE_INCREASING = prove
 (`!p:A prob_space FF (X:num->A->real) n.
    submartingale p FF X
    ==> almost_surely p
          {x | gen_doob_compensator p FF X n x <=
               gen_doob_compensator p FF X (SUC n) x}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[gen_doob_compensator] THEN
  SUBGOAL_THEN
    `{x:A | gen_doob_compensator (p:A prob_space) FF X n x <=
            gen_doob_compensator p FF X n x +
            gen_cond_exp p (FF n) (X (SUC n)) x - X n x} =
     {x | (X:num->A->real) n x <= gen_cond_exp p (FF n) (X (SUC n)) x}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
   ASM_SIMP_TAC[SUBMARTINGALE_GEN_COND_EXP_GE]]);;

(* Lemma D: X - gen_doob_compensator is a martingale *)
let GEN_DOOB_COMPENSATOR_MARTINGALE = prove
 (`!p:A prob_space FF (X:num->A->real).
    submartingale p FF X
    ==> martingale p FF (\n x. X n x - gen_doob_compensator p FF X n x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[martingale] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF X` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable (p:A prob_space) ((X:num->A->real) n)` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [(* adapted *)
   REWRITE_TAC[adapted] THEN GEN_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space) ((FF:num->(A->bool)->bool) n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(FF:num->(A->bool)->bool) n`;
                   `(X:num->A->real) n`;
                   `gen_doob_compensator (p:A prob_space) FF X n`] MEASURABLE_WRT_SUB) THEN
   REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[adapted]; ASM_SIMP_TAC[GEN_DOOB_COMPENSATOR_MEASURABLE_WRT]];
   (* integrable *)
   GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`;
                   `gen_doob_compensator (p:A prob_space) FF X n`] INTEGRABLE_SUB) THEN
   REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[GEN_DOOB_COMPENSATOR_INTEGRABLE];
   (* martingale condition *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `!x:A. x IN prob_carrier p ==>
     (X (SUC n) x - gen_doob_compensator (p:A prob_space) FF X (SUC n) x) * indicator_fn a x =
     (X n x - gen_doob_compensator p FF X n x) * indicator_fn (a:A->bool) x +
     (X (SUC n) x - gen_cond_exp p ((FF:num->(A->bool)->bool) n) (X (SUC n)) x) * indicator_fn a x`
     ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[gen_doob_compensator] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `(a:A->bool) IN prob_events p` ASSUME_TAC THENL
   [ASM_MESON_TAC[filtration; sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
   SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space) ((FF:num->(A->bool)->bool) n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. ((X:num->A->real) n x - gen_doob_compensator p FF X n x) * indicator_fn (a:A->bool) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`;
                    `gen_doob_compensator (p:A prob_space) FF X n`] INTEGRABLE_SUB) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[GEN_DOOB_COMPENSATOR_INTEGRABLE];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. ((X:num->A->real) (SUC n) x - gen_cond_exp p ((FF:num->(A->bool)->bool) n) (X (SUC n)) x) * indicator_fn (a:A->bool) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) (SUC n)`;
                    `gen_cond_exp (p:A prob_space) ((FF:num->(A->bool)->bool) n) ((X:num->A->real) (SUC n))`] INTEGRABLE_SUB) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space)
       (\x. (X (SUC n) x - gen_doob_compensator p FF X (SUC n) x) * indicator_fn (a:A->bool) x) =
      expectation p
       (\x. (X n x - gen_doob_compensator p FF X n x) * indicator_fn a x +
            (X (SUC n) x - gen_cond_exp p (FF n) (X (SUC n)) x) * indicator_fn a x)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_EXT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
                   `\x:A. ((X:num->A->real) n x - gen_doob_compensator (p:A prob_space) FF X n x) * indicator_fn (a:A->bool) x`;
                   `\x:A. ((X:num->A->real) (SUC n) x - gen_cond_exp (p:A prob_space) ((FF:num->(A->bool)->bool) n) (X (SUC n)) x) * indicator_fn (a:A->bool) x`]
                  EXPECTATION_ADD) THEN
   REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space)
       (\x:A. ((X:num->A->real) (SUC n) x - gen_cond_exp p ((FF:num->(A->bool)->bool) n) (X (SUC n)) x) *
              indicator_fn (a:A->bool) x) = &0`
     (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
   SUBGOAL_THEN
     `(\x:A. ((X:num->A->real) (SUC n) x - gen_cond_exp (p:A prob_space) ((FF:num->(A->bool)->bool) n) (X (SUC n)) x) *
             indicator_fn (a:A->bool) x) =
      (\x. X (SUC n) x * indicator_fn a x - gen_cond_exp p (FF n) (X (SUC n)) x * indicator_fn a x)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. (X:num->A->real) (SUC n) x * indicator_fn (a:A->bool) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   SUBGOAL_THEN `integrable (p:A prob_space) (\x:A. gen_cond_exp p ((FF:num->(A->bool)->bool) n) ((X:num->A->real) (SUC n)) x * indicator_fn (a:A->bool) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
                   `\x:A. (X:num->A->real) (SUC n) x * indicator_fn (a:A->bool) x`;
                   `\x:A. gen_cond_exp (p:A prob_space) ((FF:num->(A->bool)->bool) n) ((X:num->A->real) (SUC n)) x * indicator_fn (a:A->bool) x`]
                  EXPECTATION_SUB) THEN
   REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC(SPECL [`p:A prob_space`; `(FF:num->(A->bool)->bool) n`;
                  `(X:num->A->real) (SUC n)`; `a:A->bool`] GEN_COND_EXP_CONDITIONING) THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* General Doob decomposition: X = M + A where M is a martingale,
   A is gen_predictable, a.e. increasing, and A_0 = 0. *)
let GEN_DOOB_DECOMPOSITION = prove
 (`!p:A prob_space FF (X:num->A->real).
    submartingale p FF X
    ==> ?M A. martingale p FF M /\
              gen_predictable p FF A /\
              (!x:A. A 0 x = &0) /\
              (!n. almost_surely p {x | A n x <= A (SUC n) x}) /\
              (!n x. X n x = M n x + A n x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `\n (x:A). X n x - gen_doob_compensator (p:A prob_space) FF X n x` THEN
  EXISTS_TAC `gen_doob_compensator (p:A prob_space) FF X` THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REPEAT CONJ_TAC THENL
  [ASM_SIMP_TAC[GEN_DOOB_COMPENSATOR_MARTINGALE];
   ASM_SIMP_TAC[GEN_DOOB_COMPENSATOR_GEN_PREDICTABLE];
   REWRITE_TAC[gen_doob_compensator];
   ASM_SIMP_TAC[GEN_DOOB_COMPENSATOR_AE_INCREASING];
   REPEAT GEN_TAC THEN REAL_ARITH_TAC]);;

(* Helper: supermartingale negation gives submartingale *)
let SUPERMARTINGALE_NEG_SUBMARTINGALE = prove
 (`!p:A prob_space FF X.
     supermartingale p FF X
     ==> submartingale p FF (\n x. --((X:num->A->real) n x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[supermartingale; submartingale] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC[adapted] THEN GEN_TAC THEN
   MATCH_MP_TAC MEASURABLE_WRT_NEG THEN CONJ_TAC THENL
   [UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
    REWRITE_TAC[filtration] THEN SIMP_TAC[];
    UNDISCH_TAC `adapted (p:A prob_space) FF X` THEN
    REWRITE_TAC[adapted] THEN SIMP_TAC[ETA_AX]];
   GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_NEG THEN ASM_REWRITE_TAC[ETA_AX];
   REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MUL_LNEG] THEN
   SUBGOAL_THEN `(a:A->bool) IN prob_events (p:A prob_space)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
    EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
    REWRITE_TAC[filtration] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `!k. integrable (p:A prob_space) (\x:A. (X:num->A->real) k x * indicator_fn (a:A->bool) x)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
    ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   ASM_SIMP_TAC[EXPECTATION_NEG_INTEGRABLE] THEN
   REWRITE_TAC[REAL_LE_NEG2] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Helper: negation of martingale is martingale *)
let MARTINGALE_NEG = prove
 (`!p:A prob_space FF X.
     martingale p FF X
     ==> martingale p FF (\n x. --((X:num->A->real) n x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[martingale] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC[adapted] THEN GEN_TAC THEN
   MATCH_MP_TAC MEASURABLE_WRT_NEG THEN CONJ_TAC THENL
   [UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
    REWRITE_TAC[filtration] THEN SIMP_TAC[];
    UNDISCH_TAC `adapted (p:A prob_space) FF X` THEN
    REWRITE_TAC[adapted] THEN SIMP_TAC[ETA_AX]];
   GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_NEG THEN ASM_REWRITE_TAC[ETA_AX];
   REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MUL_LNEG] THEN
   SUBGOAL_THEN `(a:A->bool) IN prob_events (p:A prob_space)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
    EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
    REWRITE_TAC[filtration] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `!k. integrable (p:A prob_space) (\x:A. (X:num->A->real) k x * indicator_fn (a:A->bool) x)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
    ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   ASM_SIMP_TAC[EXPECTATION_NEG_INTEGRABLE] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Supermartingale variant: X = M + A where A is a.e. decreasing *)
let GEN_DOOB_DECOMPOSITION_SUPER = prove
 (`!p:A prob_space FF (X:num->A->real).
    supermartingale p FF X
    ==> ?M A. martingale p FF M /\
              gen_predictable p FF A /\
              (!x:A. A 0 x = &0) /\
              (!n. almost_surely p {x | A (SUC n) x <= A n x}) /\
              (!n x. X n x = M n x + A n x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `submartingale (p:A prob_space) FF (\n x. --((X:num->A->real) n x))`
    (MP_TAC o MATCH_MP GEN_DOOB_DECOMPOSITION) THENL
  [MATCH_MP_TAC SUPERMARTINGALE_NEG_SUBMARTINGALE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `M':num->A->real`
    (X_CHOOSE_THEN `A':num->A->real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\n (x:A). --((M':num->A->real) n x)` THEN
  EXISTS_TAC `\n (x:A). --((A':num->A->real) n x)` THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC MARTINGALE_NEG THEN ASM_REWRITE_TAC[];
   (* gen_predictable *)
   UNDISCH_TAC `gen_predictable (p:A prob_space) FF (A':num->A->real)` THEN
   REWRITE_TAC[gen_predictable] THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
   SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
   [ASM_MESON_TAC[supermartingale]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_WRT_NEG THEN
    CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ASM_REWRITE_TAC[ETA_AX]];
    GEN_TAC THEN MATCH_MP_TAC MEASURABLE_WRT_NEG THEN
    CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ASM_REWRITE_TAC[ETA_AX]]];
   (* A' 0 = 0 so --A' 0 = 0 *)
   ASM_REWRITE_TAC[REAL_NEG_0];
   (* a.e. decreasing *)
   GEN_TAC THEN
   SUBGOAL_THEN `{x:A | --(A':num->A->real) (SUC n) x <= --A' n x} =
     {x | A' n x <= A' (SUC n) x}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]];
   (* X = -M' + -A' *)
   REPEAT GEN_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:A`]) THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Levy's Conditional Borel-Cantelli Lemma                                   *)
(* ========================================================================= *)

(* Partial sum of indicators forms a submartingale for adapted events *)
let INDICATOR_SUM_SUBMARTINGALE = prove
 (`!p:A prob_space FF (B:num->A->bool).
     filtration p FF /\
     (!n. B n IN prob_events p) /\
     (!n. B n SUBSET prob_carrier p) /\
     (!n. B n IN FF n)
     ==> submartingale p FF (\n x. sum(0..n) (\k. indicator_fn (B k) x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[submartingale] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [(* adapted *)
   REWRITE_TAC[adapted] THEN X_GEN_TAC `n:num` THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(FF:num->(A->bool)->bool) n`;
                   `\k (x:A). indicator_fn ((B:num->A->bool) k) x`; `n:num`]
                  MEASURABLE_WRT_SUM) THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[filtration];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\x:A. indicator_fn ((B:num->A->bool) k) x) =
                   indicator_fn (B k)` SUBST1_TAC THENL
    [REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    MATCH_MP_TAC MEASURABLE_WRT_INDICATOR THEN CONJ_TAC THENL
    [ASM_MESON_TAC[filtration];
     UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
     REWRITE_TAC[filtration] THEN STRIP_TAC THEN
     SUBGOAL_THEN `(FF:num->(A->bool)->bool) k SUBSET FF n` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[SUBSET] THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]];
   (* integrable *)
   X_GEN_TAC `n:num` THEN
   MP_TAC(ISPECL [`p:A prob_space`; `\k. indicator_fn ((B:num->A->bool) k)`;
                   `n:num`] INTEGRABLE_SUM) THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN
   GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
   (* submartingale property: E[S_n * 1_a] <= E[S_{n+1} * 1_a] *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(a:A->bool) IN prob_events p` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
    EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[filtration]; ALL_TAC] THEN
   SUBGOAL_THEN
     `!x:A. sum(0..SUC n) (\k. indicator_fn ((B:num->A->bool) k) x) =
            sum(0..n) (\k. indicator_fn (B k) x) + indicator_fn (B (SUC n)) x`
     (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0]; ALL_TAC] THEN
   REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
   MATCH_MP_TAC EXPECTATION_MONO THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `\k. indicator_fn ((B:num->A->bool) k)`;
                    `n:num`] INTEGRABLE_SUM) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC INTEGRABLE_INDICATOR THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
     MP_TAC(ISPECL [`p:A prob_space`; `\k. indicator_fn ((B:num->A->bool) k)`;
                     `n:num`] INTEGRABLE_SUM) THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN
     GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC INTEGRABLE_INDICATOR THEN
     ASM_REWRITE_TAC[];
     MP_TAC(ISPECL [`p:A prob_space`;
       `indicator_fn ((B:num->A->bool) (SUC n))`; `a:A->bool`]
       INTEGRABLE_MUL_INDICATOR_FN) THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN
    REWRITE_TAC[indicator_fn] THEN REPEAT COND_CASES_TAC THEN
    REAL_ARITH_TAC]]);;

(* Key pointwise inequality for the telescoping bound:
   h / (1+c+h)^2 <= inv(1+c) - inv(1+c+h) for h,c >= 0 *)
let TELESCOPING_STEP = prove
 (`!h c:real. &0 <= h /\ &0 <= c
    ==> h / (&1 + c + h) pow 2 <= inv(&1 + c) - inv(&1 + c + h)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + c /\ &0 < &1 + c + h` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&1 + c = &0) /\ ~(&1 + c + h = &0)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&1 + c) - inv(&1 + c + h) =
                 h / ((&1 + c) * (&1 + c + h))`
    SUBST1_TAC THENL
  [ASM_SIMP_TAC[REAL_FIELD
     `~(a = &0) /\ ~(b = &0) ==> inv a - inv b = (b - a) / (a * b)`] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[REAL_POW_2] THEN
   MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

(* Telescoping bound: sum of h_k / (1+c_{k+1})^2 <= 1 - inv(1+c_{n+1})
   where c is non-decreasing, c(0) = 0, h_k = c_{k+1} - c_k *)
let TELESCOPING_SUM_BOUND = prove
 (`!c:num->real n.
     c(0) = &0 /\ (!k. k <= n ==> &0 <= c(SUC k) - c(k))
     ==> sum(0..n) (\k. (c(SUC k) - c(k)) / (&1 + c(SUC k)) pow 2)
         <= &1 - inv(&1 + c(SUC n))`,
  GEN_TAC THEN INDUCT_TAC THENL
  [STRIP_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
   SUBGOAL_THEN `&0 <= (c:num->real) 1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_REFL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MP_TAC TELESCOPING_STEP THEN
   DISCH_THEN(MP_TAC o SPECL [`(c:num->real) 1`; `&0`]) THEN
   ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ADD_RID; REAL_ADD_LID; REAL_INV_1];
   STRIP_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
   SUBGOAL_THEN `!j:num. j <= SUC n ==> &0 <= (c:num->real) j`
     ASSUME_TAC THENL
   [INDUCT_TAC THENL
    [DISCH_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
     DISCH_TAC THEN
     SUBGOAL_THEN `&0 <= (c:num->real)(SUC j) - c j` MP_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `j:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      SUBGOAL_THEN `&0 <= (c:num->real) j` MP_TAC THENL
      [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
       REAL_ARITH_TAC]]]; ALL_TAC] THEN
   SUBGOAL_THEN `sum (0..n) (\k. ((c:num->real) (SUC k) - c k) /
                  (&1 + c (SUC k)) pow 2) <= &1 - inv(&1 + c(SUC n))`
     ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_MESON_TAC[ARITH_RULE `k <= n ==> k <= SUC n`]; ALL_TAC] THEN
   SUBGOAL_THEN `((c:num->real) (SUC (SUC n)) - c (SUC n)) /
                  (&1 + c (SUC (SUC n))) pow 2 <=
                  inv(&1 + c(SUC n)) - inv(&1 + c(SUC(SUC n)))`
     ASSUME_TAC THENL
   [MP_TAC TELESCOPING_STEP THEN
    DISCH_THEN(MP_TAC o SPECL [`(c:num->real)(SUC(SUC n)) - c(SUC n)`;
                                 `(c:num->real)(SUC n)`]) THEN
    ANTS_TAC THENL
    [ASM_MESON_TAC[LE_REFL];
     SUBGOAL_THEN `&1 + (c:num->real)(SUC n) + (c(SUC(SUC n)) - c(SUC n)) =
                    &1 + c(SUC(SUC n))` (fun th -> REWRITE_TAC[th]) THEN
     REAL_ARITH_TAC]; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC]);;

(* Simplified version: sum <= 1 *)
let TELESCOPING_SUM_BOUND_SIMPLE = prove
 (`!c:num->real n.
     c(0) = &0 /\ (!k. k <= n ==> &0 <= c(SUC k) - c(k))
     ==> sum(0..n) (\k. (c(SUC k) - c(k)) / (&1 + c(SUC k)) pow 2) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 - inv(&1 + (c:num->real)(SUC n))` THEN CONJ_TAC THENL
  [MATCH_MP_TAC TELESCOPING_SUM_BOUND THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 - x <= &1`) THEN
   MATCH_MP_TAC REAL_LE_INV THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= c ==> &0 <= &1 + c`) THEN
   SUBGOAL_THEN `!j:num. j <= SUC n ==> &0 <= (c:num->real) j` MP_TAC THENL
   [INDUCT_TAC THENL
    [DISCH_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
     DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `(c:num->real) j` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC]]];
    DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN REWRITE_TAC[LE_REFL]]]);;

(* Abel summation / summation by parts identity *)
let SUMMATION_BY_PARTS = prove
 (`!a b n. sum (0..SUC n) (\k. a k * b k) =
           sum (0..SUC n) a * b (SUC n) +
           sum (0..n) (\k. sum (0..k) a * (b k - b (SUC k)))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= SUC 0`; LE_0] THEN
   REAL_ARITH_TAC;
   REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; ARITH_RULE `0 <= SUC(SUC n)`] THEN
   FIRST_X_ASSUM(MP_TAC) THEN
   REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; ARITH_RULE `0 <= SUC n`] THEN
   ABBREV_TAC `s1 = sum (0..n) (\k. (a:num->real) k * (b:num->real) k)` THEN
   ABBREV_TAC `s2 = sum (0..n) (a:num->real)` THEN
   ABBREV_TAC `t1 = sum (0..n) (\k. sum (0..k) (a:num->real) *
                    ((b:num->real) k - b (SUC k)))` THEN
   REAL_ARITH_TAC]);;

(* Each indicator is in [0,1], so sum of n+1 indicators is at most n+1 *)
let INDICATOR_SUM_BOUNDED = prove
 (`!(B:num->A->bool) x n. sum (0..n) (\k. indicator_fn (B k) x) <= &n + &1`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (0..n) (\k. &1)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
   REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
   REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; ADD_CLAUSES] THEN
   REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC]);;

(* x in limsup B iff the sum of indicators is unbounded *)
let LIMSUP_EVENTS_IFF_SUM_UNBOUNDED = prove
 (`!(B:num->A->bool) (x:A). x IN limsup_events B <=>
     (!M. ?N. &M <= sum (0..N) (\k. indicator_fn (B k) x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIMSUP_EVENTS_ALT; IN_ELIM_THM] THEN
  EQ_TAC THENL
  [(* Forward: i.o. ==> sum unbounded *)
   DISCH_TAC THEN INDUCT_TAC THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[SUM_SING_NUMSEG; indicator_fn] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(X_CHOOSE_TAC `N0:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N0 + 1`) THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `n:num` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (0..N0) (\k. indicator_fn ((B:num->A->bool) k) (x:A)) +
                indicator_fn (B n) x` THEN
    CONJ_TAC THENL
    [SUBGOAL_THEN `indicator_fn ((B:num->A->bool) n) (x:A) = &1` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[indicator_fn; COND_ID]; ALL_TAC] THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN ASM_REAL_ARITH_TAC;
     SUBGOAL_THEN `sum (0..N0) (\k. indicator_fn ((B:num->A->bool) k) (x:A)) +
                   indicator_fn (B n) x =
                   sum (0..N0) (\k. indicator_fn (B k) x) +
                   sum (n..n) (\k. indicator_fn (B k) x)` SUBST1_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[SUM_SING_NUMSEG]; ALL_TAC] THEN
     SUBGOAL_THEN `DISJOINT (0..N0) (n..n:num)` ASSUME_TAC THENL
     [REWRITE_TAC[DISJOINT; EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_NUMSEG] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN
      `sum (0..N0) (\k. indicator_fn ((B:num->A->bool) k) (x:A)) +
       sum (n..n) (\k. indicator_fn (B k) x) =
       sum ((0..N0) UNION (n..n)) (\k. indicator_fn (B k) x)` SUBST1_TAC THENL
     [MATCH_MP_TAC(GSYM SUM_UNION) THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG]; ALL_TAC] THEN
     MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
     REWRITE_TAC[FINITE_NUMSEG] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNION; IN_NUMSEG] THEN ASM_ARITH_TAC;
      X_GEN_TAC `k:num` THEN
      REWRITE_TAC[IN_DIFF; IN_NUMSEG; IN_UNION] THEN
      STRIP_TAC THEN REWRITE_TAC[indicator_fn] THEN
      COND_CASES_TAC THEN REAL_ARITH_TAC]]];
   (* Backward: sum unbounded ==> i.o. *)
   DISCH_TAC THEN X_GEN_TAC `m:num` THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `SUC m`) THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
   REWRITE_TAC[GE] THEN
   ASM_CASES_TAC `?n:num. m <= n /\ x IN (B:num->A->bool) n` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `!k. m <= k ==> indicator_fn ((B:num->A->bool) k) (x:A) = &0`
   ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[indicator_fn] THEN
    COND_CASES_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (fun th ->
       fst(dest_const(fst(strip_comb(concl th)))) = "~")) THEN
     REWRITE_TAC[] THEN ASM_MESON_TAC[];
     REFL_TAC]; ALL_TAC] THEN
   SUBGOAL_THEN
    `sum (0..N) (\k. indicator_fn ((B:num->A->bool) k) (x:A)) <= &m` MP_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC
     `&(SUC m) <= sum (0..N) (\k. indicator_fn ((B:num->A->bool) k) (x:A))` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC] THEN
   ASM_CASES_TAC `N < m:num` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N + &1` THEN
    REWRITE_TAC[INDICATOR_SUM_BOUNDED] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_LE] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_ADD] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
   ASM_CASES_TAC `m = 0` THENL
   [SUBGOAL_THEN
     `sum (0..N) (\k. indicator_fn ((B:num->A->bool) k) (x:A)) = &0`
    SUBST1_TAC THENL
    [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_ARITH_TAC;
     REAL_ARITH_TAC]; ALL_TAC] THEN
   SUBGOAL_THEN `?p. N = (m - 1) + p:num` MP_TAC THENL
   [EXISTS_TAC `N - (m - 1):num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST_ALL_TAC) THEN
   SUBGOAL_THEN
    `sum (0..m - 1 + p) (\k. indicator_fn ((B:num->A->bool) k) (x:A)) =
     sum (0..m - 1) (\k. indicator_fn (B k) x) +
     sum (m..m - 1 + p) (\k. indicator_fn (B k) x)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\k. indicator_fn ((B:num->A->bool) k) (x:A)`;
                    `0`; `m - 1`; `p:num`] SUM_ADD_SPLIT) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `m - 1 + 1 = m` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `sum (m..m - 1 + p) (\k. indicator_fn ((B:num->A->bool) k) (x:A)) = &0`
   SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    BETA_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[REAL_ADD_RID] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(m - 1) + &1` THEN
   REWRITE_TAC[INDICATOR_SUM_BOUNDED] THEN
   SUBGOAL_THEN `1 <= m` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN REAL_ARITH_TAC]);;

(* ---- Telescoping variance bound for Levy CBC ---- *)
(* Key bound: sum v_k/(1+V_k)^2 <= 1 - inv(1+V_n) < 1 *)
(* where V_k = sum(0..k) v is the partial sum. *)

let TELESCOPING_VARIANCE_BOUND = prove
 (`!v n. (!k. &0 <= v k) ==>
         sum (0..n) (\k. v k / (&1 + sum (0..k) v) pow 2)
         <= &1 - inv(&1 + sum (0..n) v)`,
  GEN_TAC THEN INDUCT_TAC THENL
  [DISCH_TAC THEN REWRITE_TAC[SUM_SING_NUMSEG] THEN
   FIRST_ASSUM(MP_TAC o SPEC `0`) THEN
   SPEC_TAC (`(v:num->real) 0`, `a:real`) THEN
   GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `~(&1 + a = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a / (&1 + a)` THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_2; REAL_INV_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC];
    UNDISCH_TAC `~(&1 + a = &0)` THEN CONV_TAC REAL_FIELD];
   DISCH_TAC THEN
   REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= SUC n`] THEN
   FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   ABBREV_TAC `V = sum (0..n) (v:num->real)` THEN
   ABBREV_TAC `u = (v:num->real) (SUC n)` THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `(&1 - inv(&1 + V)) + u / (&1 + V + u) pow 2` THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= u` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `~(&1 + V = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `~(&1 + V + u = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_ARITH `a - b + c <= a - d <=> c <= b - d`] THEN
   SUBGOAL_THEN
    `inv(&1 + V) - inv(&1 + V + u) = u / ((&1 + V) * (&1 + V + u))`
   SUBST1_TAC THENL
   [UNDISCH_TAC `~(&1 + V = &0)` THEN UNDISCH_TAC `~(&1 + V + u = &0)` THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
   REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]]);;

let TELESCOPING_VARIANCE_BOUND_SIMPLE = prove
 (`!v n. (!k. &0 <= v k) ==>
         sum (0..n) (\k. v k / (&1 + sum (0..k) v) pow 2) <= &1`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 - inv(&1 + sum (0..n) (v:num->real))` THEN
  ASM_SIMP_TAC[TELESCOPING_VARIANCE_BOUND] THEN
  SUBGOAL_THEN `&0 <= sum (0..n) (v:num->real)` MP_TAC THENL
  [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 - x <= &1`) THEN
  MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC);;

(* Step identity: E[S_{n+1}|F_n] - S_n = E[1_{B_{n+1}}|F_n] a.s. *)
let INDICATOR_SUM_COND_EXP_STEP = prove
 (`!p FF (B:num->A->bool) n.
       filtration p FF /\ (!n. B n IN prob_events p) /\
       (!n. B n SUBSET prob_carrier p) /\ (!n. B n IN FF n)
       ==> almost_surely p
           {x | gen_cond_exp p (FF n)
                  (\y. sum (0..SUC n) (\k. indicator_fn (B k) y)) x -
                sum (0..n) (\k. indicator_fn (B k) x) =
                gen_cond_exp p (FF n)
                  (\y. indicator_fn (B (SUC n)) y) x}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y:A. sum (0..SUC n) (\k. indicator_fn (B k) y)) =
    (\y. sum (0..n) (\k. indicator_fn ((B:num->A->bool) k) y) +
         indicator_fn (B (SUC n)) y)`
  SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; SUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= SUC n`] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sub_sigma_algebra p ((FF:num->(A->bool)->bool) n)`
  ASSUME_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k:num. integrable p (\y:A. indicator_fn ((B:num->A->bool) k) y)`
  ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[ETA_AX] THEN
   MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `integrable p
      (\y:A. sum (0..n) (\k. indicator_fn ((B:num->A->bool) k) y))`
  ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SUM THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
   `almost_surely p
      {x:A | gen_cond_exp p ((FF:num->(A->bool)->bool) n)
           (\y. sum (0..n) (\k. indicator_fn ((B:num->A->bool) k) y) +
                indicator_fn (B (SUC n)) y) x =
           gen_cond_exp p (FF n)
             (\y. sum (0..n) (\k. indicator_fn (B k) y)) x +
           gen_cond_exp p (FF n)
             (\y. indicator_fn (B (SUC n)) y) x}`
  ASSUME_TAC THENL
  [MP_TAC(ISPECL
     [`p:A prob_space`; `(FF:num->(A->bool)->bool) n`;
      `\y:A. sum (0..n) (\k. indicator_fn ((B:num->A->bool) k) y)`;
      `\y:A. indicator_fn ((B:num->A->bool) (SUC n)) y`]
     GEN_COND_EXP_ADD) THEN
   REWRITE_TAC[BETA_THM] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `measurable_wrt p ((FF:num->(A->bool)->bool) n)
     (\y:A. sum (0..n) (\k. indicator_fn ((B:num->A->bool) k) y))`
  ASSUME_TAC THENL
  [MATCH_MP_TAC MEASURABLE_WRT_SUM THEN ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC MEASURABLE_WRT_INDICATOR THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `(B:num->A->bool) k IN FF k` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(FF:num->(A->bool)->bool) k SUBSET FF n` MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [filtration]) THEN
    SIMP_TAC[SUBSET; IN] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPECL [`k:num`; `n:num`]) THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[SUBSET; IN]]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`p:A prob_space`; `(FF:num->(A->bool)->bool) n`;
    `\y:A. sum (0..n) (\k. indicator_fn ((B:num->A->bool) k) y)`]
   GEN_COND_EXP_SELF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `p:A prob_space` ALMOST_SURELY_SUBSET) THEN
  EXISTS_TAC `{x:A | gen_cond_exp p ((FF:num->(A->bool)->bool) n)
    (\y. sum (0..n) (\k. indicator_fn ((B:num->A->bool) k) y) +
         indicator_fn (B (SUC n)) y) x =
    gen_cond_exp p (FF n)
      (\y. sum (0..n) (\k. indicator_fn (B k) y)) x +
    gen_cond_exp p (FF n) (\y. indicator_fn (B (SUC n)) y) x} INTER
   {x:A | gen_cond_exp p (FF n)
      (\y. sum (0..n) (\k. indicator_fn (B k) y)) x =
    sum (0..n) (\k. indicator_fn (B k) x)}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC(ISPEC `p:A prob_space` ALMOST_SURELY_INTER) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Compensator identity: A_{n+1} = sum_0^n E[1_{B_{k+1}}|F_k] a.s. *)
let INDICATOR_SUM_COMPENSATOR_IDENTITY = prove
 (`!p FF (B:num->A->bool).
     filtration p FF /\ (!n. B n IN prob_events p) /\
     (!n. B n SUBSET prob_carrier p) /\ (!n. B n IN FF n)
     ==> almost_surely p
       {x | !n. gen_doob_compensator p FF
             (\n x. sum (0..n) (\k. indicator_fn (B k) x)) (SUC n) x =
            sum (0..n) (\k. gen_cond_exp p (FF k)
                             (\y. indicator_fn (B (SUC k)) y) x)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `p:A prob_space` ALMOST_SURELY_SUBSET) THEN
  EXISTS_TAC `INTERS
    {({x:A | gen_cond_exp p ((FF:num->(A->bool)->bool) n)
        (\y. sum (0..SUC n) (\k. indicator_fn ((B:num->A->bool) k) y))
        x - sum (0..n) (\k. indicator_fn (B k) x) =
        gen_cond_exp p (FF n) (\y. indicator_fn (B (SUC n)) y) x})
     | n IN (:num)}` THEN
  CONJ_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`;
    `\n. {x:A | gen_cond_exp p ((FF:num->(A->bool)->bool) n)
        (\y. sum (0..SUC n) (\k. indicator_fn ((B:num->A->bool) k) y))
        x - sum (0..n) (\k. indicator_fn (B k) x) =
        gen_cond_exp p (FF n) (\y. indicator_fn (B (SUC n)) y) x}`]
    ALMOST_SURELY_COUNTABLE_INTER) THEN
   REWRITE_TAC[BETA_THM] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   GEN_TAC THEN MATCH_MP_TAC INDICATOR_SUM_COND_EXP_STEP THEN
   ASM_REWRITE_TAC[];
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[IN_INTERS; IN_ELIM_THM; IN_UNIV] THEN
   DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
   SUBGOAL_THEN
    `!m. gen_cond_exp p ((FF:num->(A->bool)->bool) m)
        (\y. sum (0..SUC m) (\k. indicator_fn ((B:num->A->bool) k) y))
        (x:A) - sum (0..m) (\k. indicator_fn (B k) x) =
        gen_cond_exp p (FF m) (\y. indicator_fn (B (SUC m)) y) x`
   ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN
    FIRST_ASSUM(MP_TAC o SPEC
     `{x:A | gen_cond_exp p ((FF:num->(A->bool)->bool) m)
         (\y. sum (0..SUC m)
           (\k. indicator_fn ((B:num->A->bool) k) y))
         x - sum (0..m) (\k. indicator_fn (B k) x) =
         gen_cond_exp p (FF m)
           (\y. indicator_fn (B (SUC m)) y) x}`) THEN
    ANTS_TAC THENL
    [EXISTS_TAC `m:num` THEN REWRITE_TAC[];
     REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
   INDUCT_TAC THENL
   [REWRITE_TAC[gen_doob_compensator; SUM_SING_NUMSEG; REAL_ADD_LID] THEN
    FIRST_ASSUM(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= SUC 0`; LE_0;
                SUM_SING_NUMSEG] THEN
    REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[gen_doob_compensator] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= SUC n`] THEN
    FIRST_ASSUM(MP_TAC o SPEC `SUC n`) THEN
    ABBREV_TAC `E1 = gen_cond_exp p ((FF:num->(A->bool)->bool) (SUC n))
      (\y. sum (0..SUC(SUC n))
        (\k. indicator_fn ((B:num->A->bool) k) y)) (x:A)` THEN
    ABBREV_TAC `S1 = sum (0..SUC n)
      (\k. indicator_fn ((B:num->A->bool) k) (x:A))` THEN
    ABBREV_TAC `C1 = gen_cond_exp p ((FF:num->(A->bool)->bool) (SUC n))
      (\y. indicator_fn ((B:num->A->bool) (SUC(SUC n))) y) (x:A)` THEN
    ABBREV_TAC `D1 = sum (0..n)
      (\k. gen_cond_exp p ((FF:num->(A->bool)->bool) k)
        (\y. indicator_fn ((B:num->A->bool) (SUC k)) y) (x:A))` THEN
    DISCH_TAC THEN ASM_REAL_ARITH_TAC]]);;

(* Kronecker rescaled: if sum(a_k) converges and 1+V_k -> infinity,
   then inv(1+V_n) * sum(a_k * (1+V_k)) -> 0 *)
let KRONECKER_RESCALED = prove
 (`!a v. (!k. &0 <= v k) /\
         real_summable (from 0) a /\
         (!M. ?N. !n. N <= n ==> M <= &1 + sum(0..n) v)
         ==> ((\n. inv(&1 + sum(0..n) v) *
                   sum(0..n) (\k. a k * (&1 + sum(0..k) v)))
              ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!n. &0 < &1 + sum(0..n) (v:num->real)` ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `&0 <= sum(0..n) (v:num->real)` MP_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~(&1 + sum(0..n) (v:num->real) = &0)` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\k. (a:num->real) k * (&1 + sum(0..k) (v:num->real))`;
    `\n. &1 + sum(0..n) (v:num->real)`]
   KRONECKER_LEMMA) THEN
  REWRITE_TAC[BETA_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[ARITH_RULE `n + 1 = SUC n`;
     SUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= SUC n`] THEN
   MP_TAC(SPEC `SUC n` (ASSUME `!k. &0 <= (v:num->real) k`)) THEN
   REAL_ARITH_TAC;
   SUBGOAL_THEN
    `(\k. (a k * (&1 + sum (0..k) (v:num->real))) /
          (&1 + sum (0..k) v)) = a`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    SUBGOAL_THEN `~(&1 + sum(0..x) (v:num->real) = &0)` MP_TAC THENL
    [ASM_REWRITE_TAC[]; CONV_TAC REAL_FIELD];
    ASM_REWRITE_TAC[]]]);;

(* Abel convergence: if sum(a_k) converges and b_k positive increasing
   converges, then sum(a_k * b_k) converges *)
let ABEL_SUMMATION_CONVERGENCE = prove
 (`!a v. (!k. &0 <= v k) /\
         (?L. ((\n. sum(0..n) a) ---> L) sequentially) /\
         (?V_inf. ((\n. sum(0..n) v) ---> V_inf) sequentially)
         ==> ?M_inf.
           ((\n. sum(0..n) (\k. a k * (&1 + sum(0..k) v))) ---> M_inf)
           sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Helper: f(SUC n) --> l implies f(n) --> l *)
  SUBGOAL_THEN
    `!f:num->real l. ((\n. f(SUC n)) ---> l) sequentially
                     ==> (f ---> l) sequentially`
    (LABEL_TAC "SUC_LIM") THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `SUC N` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
   SUBGOAL_THEN `SUC(n - 1) = n` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  (* Helper: f(n) --> l implies f(SUC n) --> l *)
  SUBGOAL_THEN
    `!f:num->real l. (f ---> l) sequentially
                     ==> ((\n. f(SUC n)) ---> l) sequentially`
    (LABEL_TAC "LIM_SUC") THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
   REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  (* Partial sums of a are bounded *)
  SUBGOAL_THEN
    `?C. &0 < C /\ !n. abs(sum(0..n) (a:num->real)) <= C`
    STRIP_ASSUME_TAC THENL
  [MP_TAC(ISPECL [`\n. sum(0..n) (a:num->real)`; `L:real`]
    REAL_CONVERGENT_IMP_BOUNDED) THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE; IN_UNIV]; ALL_TAC] THEN
  (* sum(S_k * v(SUC k)) converges by comparison with C * v(SUC k) *)
  SUBGOAL_THEN
    `?T_inf. ((\n. sum(0..n) (\k. sum(0..k) (a:num->real) * v(SUC k)))
              ---> T_inf) sequentially`
    (X_CHOOSE_TAC `T_inf:real`) THENL
  [SUBGOAL_THEN
     `real_summable (from 0) (\k. sum(0..k) (a:num->real) * v(SUC k))`
     MP_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC `\k. C * (v:num->real)(SUC k)` THEN CONJ_TAC THENL
    [REWRITE_TAC[real_summable; real_sums; FROM_INTER_NUMSEG; SUM_LMUL] THEN
     EXISTS_TAC `C * (V_inf - (v:num->real) 0)` THEN
     MATCH_MP_TAC REALLIM_LMUL THEN
     SUBGOAL_THEN `!n. sum(0..n) (\k. (v:num->real)(SUC k)) =
                       sum(0..SUC n) v - v 0`
       (fun th -> REWRITE_TAC[th]) THENL
     [INDUCT_TAC THENL
      [REWRITE_TAC[SUM_SING_NUMSEG; SUM_CLAUSES_NUMSEG; LE_0] THEN
       REAL_ARITH_TAC;
       ONCE_REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN REWRITE_TAC[LE_0] THEN
       ASM_REWRITE_TAC[] THEN
       ONCE_REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN REWRITE_TAC[LE_0] THEN
       REAL_ARITH_TAC]; ALL_TAC] THEN
     MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
     REMOVE_THEN "LIM_SUC"
       (MP_TAC o SPECL [`\n. sum(0..n) (v:num->real)`; `V_inf:real`]) THEN
     ASM_REWRITE_TAC[];
     EXISTS_TAC `0` THEN REWRITE_TAC[GE; LE_0; IN_FROM] THEN
     REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
     MATCH_MP_TAC REAL_LE_MUL2 THEN
     ASM_SIMP_TAC[REAL_ABS_POS; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
     REAL_ARITH_TAC];
    REWRITE_TAC[real_summable; real_sums; FROM_INTER_NUMSEG] THEN
    MESON_TAC[]]; ALL_TAC] THEN
  (* Main: sum(0..SUC n)(a_k*b_k) = product - sum, both converge *)
  EXISTS_TAC `L * (&1 + V_inf) - T_inf` THEN
  REMOVE_THEN "SUC_LIM" (fun th -> MATCH_MP_TAC th) THEN
  SUBGOAL_THEN
    `!n. sum(0..SUC n) (\k. (a:num->real) k * (&1 + sum(0..k) v)) =
         sum(0..SUC n) a * (&1 + sum(0..SUC n) v) -
         sum(0..n) (\k. sum(0..k) a * v(SUC k))`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN REWRITE_TAC[SUMMATION_BY_PARTS] THEN
   SUBGOAL_THEN
     `sum (0..n) (\k. sum(0..k) (a:num->real) *
        ((&1 + sum(0..k) v) - (&1 + sum(0..SUC k) v))) =
      --(sum(0..n) (\k. sum(0..k) a * v(SUC k)))`
     (fun th -> REWRITE_TAC[th] THEN CONV_TAC REAL_RING) THEN
   REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
   REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
   ONCE_REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN REWRITE_TAC[LE_0] THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_SUB THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
  [REMOVE_THEN "LIM_SUC"
     (MP_TAC o SPECL [`\n. sum(0..n) (a:num->real)`; `L:real`]) THEN
   ASM_REWRITE_TAC[];
   MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
   REMOVE_THEN "LIM_SUC"
     (MP_TAC o SPECL [`\n. sum(0..n) (v:num->real)`; `V_inf:real`]) THEN
   ASM_REWRITE_TAC[]]);;

(* Decomposition unbounded iff: c + V + M unbounded <=> V unbounded *)
(* Under: v_k >= 0, sum(a_k) converges, c >= 0, M_n = sum a_k*(1+V_k) *)
let DECOMPOSITION_UNBOUNDED_IFF = prove
 (`!v a c.
   (!k. &0 <= v k) /\
   (?L. ((\n. sum(0..n) a) ---> L) sequentially) /\
   &0 <= c
   ==> ((!M. ?N. &M <= c + sum(0..N) v +
              sum(0..N) (\k. a k * (&1 + sum(0..k) v)))
        <=> (!M. ?N. &M <= sum(0..N) v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
  [(* Backward: c+V+M unbounded => V unbounded (contrapositive) *)
   ONCE_REWRITE_TAC[TAUT `(p ==> q) <=> (~q ==> ~p)`] THEN
   REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM; REAL_NOT_LE] THEN
   DISCH_THEN(X_CHOOSE_TAC `M0:num`) THEN
   (* V bounded => V converges *)
   SUBGOAL_THEN
     `?V_inf. ((\n. sum(0..n) (v:num->real)) ---> V_inf) sequentially`
     (X_CHOOSE_TAC `V_inf:real`) THENL
   [MATCH_MP_TAC CONVERGENT_REAL_BOUNDED_MONOTONE THEN CONJ_TAC THENL
    [REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
     EXISTS_TAC `&M0` THEN GEN_TAC THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x < M ==> abs x <= M`) THEN
     ASM_SIMP_TAC[SUM_POS_LE_NUMSEG];
     DISJ1_TAC THEN GEN_TAC THEN
     REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
     UNDISCH_TAC `!k. &0 <= (v:num->real) k` THEN
     DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN REAL_ARITH_TAC]; ALL_TAC] THEN
   (* Abel: sum(a_k*(1+V_k)) converges *)
   SUBGOAL_THEN
     `?M_inf. ((\n. sum(0..n) (\k. (a:num->real) k * (&1 + sum(0..k) v)))
                ---> M_inf) sequentially`
     (X_CHOOSE_TAC `M_inf:real`) THENL
   [MATCH_MP_TAC ABEL_SUMMATION_CONVERGENCE THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
   (* c + V + M bounded *)
   MP_TAC(ISPECL [`\n:num. sum(0..n) (v:num->real)`; `V_inf:real`]
     REAL_CONVERGENT_IMP_BOUNDED) THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE; IN_UNIV] THEN
   DISCH_THEN(X_CHOOSE_THEN `Cv:real` STRIP_ASSUME_TAC) THEN
   MP_TAC(ISPECL [`\n:num. sum(0..n)
     (\k. (a:num->real) k * (&1 + sum(0..k) v))`; `M_inf:real`]
     REAL_CONVERGENT_IMP_BOUNDED) THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE; IN_UNIV] THEN
   DISCH_THEN(X_CHOOSE_THEN `Cm:real` STRIP_ASSUME_TAC) THEN
   MP_TAC(SPEC `c + Cv + Cm + &1` REAL_ARCH_SIMPLE) THEN
   DISCH_THEN(X_CHOOSE_TAC `M1:num`) THEN
   EXISTS_TAC `M1:num` THEN GEN_TAC THEN
   MATCH_MP_TAC(REAL_ARITH
     `abs(v) <= Cv /\ abs(m) <= Cm /\ c + Cv + Cm + &1 <= &M1
      ==> c + v + m < &M1`) THEN
   ASM_REWRITE_TAC[];
   (* Forward: V unbounded => c+V+M unbounded (using Kronecker) *)
   DISCH_TAC THEN
   SUBGOAL_THEN `real_summable (from 0) (a:num->real)` ASSUME_TAC THENL
   [REWRITE_TAC[real_summable; real_sums; FROM_INTER_NUMSEG; LE_0] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `!m n. m <= n ==> sum(0..m) (v:num->real) <= sum(0..n) v`
     (LABEL_TAC "V_MONO2") THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN CONJ_TAC THENL
    [REWRITE_TAC[REAL_LE_REFL]; CONJ_TAC THENL
     [MESON_TAC[REAL_LE_TRANS]; ALL_TAC]] THEN
    GEN_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
    UNDISCH_TAC `!k. &0 <= (v:num->real) k` THEN
    DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `!n. &0 < &1 + sum(0..n) (v:num->real)` (LABEL_TAC "VP") THENL
   [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> &0 < &1 + s`) THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* Apply KRONECKER_RESCALED *)
   MP_TAC(ISPECL [`a:num->real`; `v:num->real`] KRONECKER_RESCALED) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:real` THEN
    MP_TAC(SPEC `r:real` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `M1:num`) THEN
    UNDISCH_TAC `!M:num. ?N:num. &M <= sum(0..N) (v:num->real)` THEN
    DISCH_THEN(MP_TAC o SPEC `M1:num`) THEN
    DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
    EXISTS_TAC `N1:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..N1) (v:num->real)` THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `sum(0..n) (v:num->real)` THEN CONJ_TAC THENL
     [USE_THEN "V_MONO2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> s <= &1 + s`) THEN
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
   (* Kronecker: inv(1+V)*M -> 0 *)
   REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
   DISCH_THEN(MP_TAC o SPEC `inv(&2)`) THEN
   ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
   X_GEN_TAC `M2:num` THEN
   UNDISCH_TAC `!M:num. ?N. &M <= sum(0..N) (v:num->real)` THEN
   DISCH_THEN(MP_TAC o SPEC `2 * M2 + 1`) THEN
   DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
   ABBREV_TAC `N = N1 + N2:num` THEN EXISTS_TAC `N:num` THEN
   SUBGOAL_THEN `&(2 * M2 + 1) <= sum(0..N) (v:num->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..N2) (v:num->real)` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "V_MONO2" MATCH_MP_TAC THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `N1 <= N:num` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME `N1 <= N:num`))) THEN
   USE_THEN "VP" (MP_TAC o SPEC `N:num`) THEN
   ABBREV_TAC `W = &1 + sum(0..N) (v:num->real)` THEN
   ABBREV_TAC `Mn = sum(0..N)
     (\k. (a:num->real) k * (&1 + sum(0..k) v))` THEN
   REPEAT STRIP_TAC THEN
   (* Key: |inv(W)*Mn| < 1/2 ==> --(W/2) < Mn *)
   SUBGOAL_THEN `--(W / &2) < Mn` ASSUME_TAC THENL
   [SUBGOAL_THEN `--inv(&2) < inv(W) * Mn` ASSUME_TAC THENL
    [UNDISCH_TAC `abs(inv W * Mn) < inv(&2)` THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `~(W = &0)` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `W * --inv(&2) < W * inv W * Mn` MP_TAC THENL
    [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `W * inv W = &1` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[REAL_MUL_LID] THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   (* c + V + Mn >= V/2 - 1/2 >= M2 *)
   UNDISCH_TAC `--(W / &2) < Mn` THEN
   UNDISCH_TAC `&1 + sum(0..N) (v:num->real) = W` THEN
   UNDISCH_TAC `&(2 * M2 + 1) <= sum(0..N) (v:num->real)` THEN
   UNDISCH_TAC `&0 <= c` THEN
   REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
   REAL_ARITH_TAC]);;


(* ================================================================== *)
(* Infrastructure lemmas for RESCALED_INDICATOR_CONVERGENCE            *)
(* ================================================================== *)

(* Squaring preserves measurability *)
let MEASURABLE_WRT_POW2 = prove
 (`!p:A prob_space G (f:A->real).
    sub_sigma_algebra p G /\ measurable_wrt p G f
    ==> measurable_wrt p G (\x. f x pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[measurable_wrt] THEN
  X_GEN_TAC `v:real` THEN ASM_CASES_TAC `v < &0` THENL
  [SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ f x pow 2 <= v} = {}`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:A` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(SPEC `(f:A->real) x` REAL_LE_POW_2) THEN
    UNDISCH_TAC `v < &0` THEN REAL_ARITH_TAC;
    ASM_MESON_TAC[sub_sigma_algebra; SIGMA_ALGEBRA_EMPTY]];
   SUBGOAL_THEN `&0 <= v` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ f x pow 2 <= v} =
     {x | x IN prob_carrier p /\ f x <= sqrt v} INTER
     {x | x IN prob_carrier p /\ f x >= --(sqrt v)}`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN EQ_TAC THENL
    [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(--(f:A->real) x) pow 2 <= v` MP_TAC THENL
      [REWRITE_TAC[REAL_POW_NEG; ARITH] THEN ASM_REWRITE_TAC[];
       DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_RSQRT) THEN REAL_ARITH_TAC]];
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `abs((f:A->real) x) <= sqrt v` MP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN
      SUBGOAL_THEN `abs((f:A->real) x) pow 2 <= v` MP_TAC THENL
      [MATCH_MP_TAC REAL_RSQRT_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS];
       REWRITE_TAC[REAL_POW2_ABS]]]];
    SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
    [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_INTER THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
    [UNDISCH_TAC `measurable_wrt (p:A prob_space) G (f:A->real)` THEN
     REWRITE_TAC[measurable_wrt] THEN DISCH_THEN(MP_TAC o SPEC `sqrt v`) THEN
     REWRITE_TAC[];
     MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`; `f:A->real`;
                    `--(sqrt v)`] MEASURABLE_WRT_GE) THEN
     ASM_REWRITE_TAC[]]]]);;

(* Product of measurable_wrt functions is measurable_wrt -- via polarization *)
let MEASURABLE_WRT_MUL = prove
 (`!p:A prob_space G (f:A->real) (g:A->real).
    sub_sigma_algebra p G /\ measurable_wrt p G f /\ measurable_wrt p G g
    ==> measurable_wrt p G (\x. f x * g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(\x:A. f x * g x) =
     (\x. inv(&2) * ((f x + g x) pow 2 - f x pow 2 - g x pow 2))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; REAL_POW_2] THEN GEN_TAC THEN REAL_ARITH_TAC;
   MATCH_MP_TAC MEASURABLE_WRT_CMUL THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MEASURABLE_WRT_SUB THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_WRT_SUB THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC MEASURABLE_WRT_POW2 THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC MEASURABLE_WRT_ADD THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC MEASURABLE_WRT_POW2 THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MEASURABLE_WRT_POW2 THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Taking out what is known: an affine G-measurable factor can be pulled out  *)
(* of a conditional expectation.  This extends the indicator-multiplier case  *)
(* above to multipliers of the form c times an indicator plus a constant.     *)
(* Three helper lemmas precede the main result.                               *)
(* ------------------------------------------------------------------------- *)

(* An affine function of a G-indicator is G-measurable. *)
let MWRT_AFFINE = prove
 (`!p:A prob_space G A c d.
     sub_sigma_algebra p G /\ A IN G
     ==> measurable_wrt p G (\x. c * indicator_fn A x + d)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `measurable_wrt (p:A prob_space) G (indicator_fn (A:A->bool))` ASSUME_TAC THENL
  [ASM_SIMP_TAC[MEASURABLE_WRT_INDICATOR]; ALL_TAC] THEN
  SUBGOAL_THEN `measurable_wrt (p:A prob_space) G (\x:A. c * indicator_fn A x)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`; `indicator_fn (A:A->bool)`; `c:real`]
     MEASURABLE_WRT_CMUL) THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `\x:A. c * indicator_fn A x`; `\x:A. d:real`] MEASURABLE_WRT_ADD)) THEN
  ASM_SIMP_TAC[MEASURABLE_WRT_CONST]);;

(* An affine multiple of an indicator times an integrable X is integrable.    *)
let INTEGRABLE_AFFINE_IND_MUL = prove
 (`!p:A prob_space A X c d.
     integrable p X /\ A IN prob_events p
     ==> integrable p (\w. (c * indicator_fn A w + d) * X w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\w:A. (c * indicator_fn A w + d) * X w) =
                (\w. c * (X w * indicator_fn A w) + d * X w)` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
  ASM_SIMP_TAC[INTEGRABLE_MUL_INDICATOR_FN]);;

(* The expectation of the affine multiplier times Z times an indicator splits  *)
(* into the two pieces over the intersection and over the test set.           *)
let EXP_AFFINE_DECOMP = prove
 (`!p:A prob_space Z A A' c d.
     integrable p Z /\ A IN prob_events p /\ A' IN prob_events p
     ==> expectation p (\x. ((c * indicator_fn A x + d) * Z x) * indicator_fn A' x) =
         c * expectation p (\x. Z x * indicator_fn (A INTER A') x) +
         d * expectation p (\x. Z x * indicator_fn A' x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (\x:A. Z x * indicator_fn (A INTER A') x) /\
                integrable p (\x:A. Z x * indicator_fn A' x)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
   ASM_SIMP_TAC[PROB_INTER_IN_EVENTS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:A. ((c * indicator_fn A x + d) * Z x) * indicator_fn A' x) =
    (\x. c * (Z x * indicator_fn (A INTER A') x) + d * (Z x * indicator_fn A' x))`
   SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; INDICATOR_FN_INTER] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\x:A. c * (Z x * indicator_fn (A INTER A') x)`;
    `\x:A. d * (Z x * indicator_fn A' x)`] EXPECTATION_ADD) THEN
  ASM_SIMP_TAC[INTEGRABLE_CMUL] THEN BETA_TAC THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[EXPECTATION_CMUL]);;

(* Take-out of an affine G-measurable factor. *)
let GEN_COND_EXP_TAKE_OUT_AFFINE = prove
 (`!p:A prob_space G X A c d.
     sub_sigma_algebra p G /\ A IN G /\ integrable p X
     ==> almost_surely p
       {x | gen_cond_exp p G (\w. (c * indicator_fn A w + d) * X w) x =
            (c * indicator_fn A x + d) * gen_cond_exp p G X x}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(A:A->bool) IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[SUB_SIGMA_ALGEBRA_IN_EVENTS]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\w:A. (c * indicator_fn A w + d) * X w)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[INTEGRABLE_AFFINE_IND_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN
    `measurable_wrt p G (\x:A. (c * indicator_fn A x + d) * gen_cond_exp p G X x)`
    ASSUME_TAC THENL
  [MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
     `\x:A. c * indicator_fn A x + d`; `gen_cond_exp p G (X:A->real)`]
     MEASURABLE_WRT_MUL)) THEN
   ASM_SIMP_TAC[MWRT_AFFINE; GEN_COND_EXP_MEASURABLE_WRT]; ALL_TAC] THEN
  SUBGOAL_THEN
    `integrable p (\x:A. (c * indicator_fn A x + d) * gen_cond_exp p G X x)`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `A:A->bool`; `gen_cond_exp p G (X:A->real)`;
     `c:real`; `d:real`] INTEGRABLE_AFFINE_IND_MUL) THEN
   ASM_SIMP_TAC[GEN_COND_EXP_INTEGRABLE]; ALL_TAC] THEN
  MATCH_MP_TAC GEN_COND_EXP_AE_UNIQUE THEN EXISTS_TAC `G:(A->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[GEN_COND_EXP_MEASURABLE_WRT];
   REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[GEN_COND_EXP_INTEGRABLE];
   ALL_TAC] THEN
  X_GEN_TAC `A':A->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(A':A->bool) IN prob_events p /\ A INTER A' IN G /\ A INTER A' IN prob_events p`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC[SUB_SIGMA_ALGEBRA_IN_EVENTS; SIGMA_ALGEBRA_INTER;
                 sub_sigma_algebra]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `\w:A. (c * indicator_fn A w + d) * X w`; `A':A->bool`] GEN_COND_EXP_CONDITIONING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[EXP_AFFINE_DECOMP; GEN_COND_EXP_INTEGRABLE] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `gen_cond_exp p G (X:A->real)`;
    `A:A->bool`; `A':A->bool`; `c:real`; `d:real`] EXP_AFFINE_DECOMP) THEN
  ASM_SIMP_TAC[GEN_COND_EXP_INTEGRABLE] THEN DISCH_THEN SUBST1_TAC THEN
  BINOP_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[]);;

(* Integrability of h*g when h is integrable and g is bounded *)
let INTEGRABLE_MUL_BOUNDED = prove
 (`!p:A prob_space (h:A->real) (g:A->real) K.
    integrable p h /\ random_variable p g /\ &0 <= K /\
    (!x. x IN prob_carrier p ==> abs(g x) <= K)
    ==> integrable p (\x. h x * g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
  EXISTS_TAC `\x:A. K * abs(h x)` THEN BETA_TAC THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN `(\x:A. K * abs(h x)) = (\x. K * (\y. abs(h y)) x)`
     SUBST1_TAC THENL
   [REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_CMUL_ALT THEN
   MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[];
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_ABS] THEN
   SUBGOAL_THEN `abs K = K` SUBST1_TAC THENL
   [REWRITE_TAC[real_abs] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `K * abs((h:A->real) x) = abs(h x) * K` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
   ASM_SIMP_TAC[]]);;

(* Taking out a SIMPLE G-measurable multiplier from gen_cond_exp:             *)
(*   E[Y*X | G] = Y * E[X|G] a.s., for Y simple and G-measurable.             *)
(* Decompose Y over its finite range (SIMPLE_RV_SUM_INDICATOR) and verify the *)
(* defining integral test level-set by level-set (EXP_SIMPLE_MUL_DECOMP +     *)
(* GEN_COND_EXP_CONDITIONING).                                                 *)
let GEN_COND_EXP_TAKE_OUT_SIMPLE = prove
 (`!p:A prob_space G Y X.
     sub_sigma_algebra p G /\ integrable p X /\
     measurable_wrt p G Y /\ simple_rv p Y /\
     integrable p (\w. Y w * X w)
     ==> almost_surely p
           {x | gen_cond_exp p G (\w. Y w * X w) x =
                Y x * gen_cond_exp p G X x}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `Y:A->real`] SIMPLE_RV_ABS_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN
  SUBGOAL_THEN
    `measurable_wrt p G (\x:A. Y x * gen_cond_exp p G (X:A->real) x)`
    ASSUME_TAC THENL
  [MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
     `Y:A->real`; `gen_cond_exp p G (X:A->real)`] MEASURABLE_WRT_MUL)) THEN
   ASM_SIMP_TAC[GEN_COND_EXP_MEASURABLE_WRT]; ALL_TAC] THEN
  SUBGOAL_THEN
    `integrable p (\x:A. Y x * gen_cond_exp p G (X:A->real) x)`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [MP_TAC(ISPEC `p:A prob_space` PROB_CARRIER_NONEMPTY) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(\x:A. Y x * gen_cond_exp p G (X:A->real) x) =
                 (\x:A. gen_cond_exp p G (X:A->real) x * Y x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `gen_cond_exp p G (X:A->real)`; `Y:A->real`;
                  `M:real`] INTEGRABLE_MUL_BOUNDED) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
     ASM_MESON_TAC[simple_rv]];
    REWRITE_TAC[]]; ALL_TAC] THEN
  MATCH_MP_TAC GEN_COND_EXP_AE_UNIQUE THEN EXISTS_TAC `G:(A->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[GEN_COND_EXP_MEASURABLE_WRT];
   REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[GEN_COND_EXP_INTEGRABLE];
   ALL_TAC] THEN
  X_GEN_TAC `A':A->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(A':A->bool) IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[SUB_SIGMA_ALGEBRA_IN_EVENTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `(\w. Y w * X w):A->real`; `A':A->bool`] GEN_COND_EXP_CONDITIONING) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `Y:A->real`; `X:A->real`; `A':A->bool`]
    EXP_SIMPLE_MUL_DECOMP) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `Y:A->real`; `gen_cond_exp p G (X:A->real)`;
    `A':A->bool`] EXP_SIMPLE_MUL_DECOMP) THEN
  ASM_SIMP_TAC[GEN_COND_EXP_INTEGRABLE] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `{z:A | z IN prob_carrier p /\ (Y:A->real) z = u} INTER A' IN G`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIGMA_ALGEBRA_INTER THEN
   CONJ_TAC THENL [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_WRT_LEVEL_SET THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`; `X:A->real`;
    `{z:A | z IN prob_carrier p /\ (Y:A->real) z = u} INTER A'`]
    GEN_COND_EXP_CONDITIONING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(* ------------------------------------------------------------------ *)
(* Dyadic approximation of a bounded measurable function.  These give  *)
(* a sequence of simple, G-measurable functions Yn converging to Y     *)
(* everywhere with abs(Yn) bounded by abs(Y)+1, used to lift the       *)
(* simple-multiplier take-out to bounded measurable multipliers.       *)
(* ------------------------------------------------------------------ *)

let DYADIC_APPROX_BOUND = prove
 (`!n y:real. abs(floor(&2 pow n * y) / &2 pow n - y) <= inv(&2 pow n)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&0 < &2 pow n` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `&2 pow n * y` FLOOR) THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `floor(&2 pow n * y) / &2 pow n - y =
     (floor(&2 pow n * y) - &2 pow n * y) * inv(&2 pow n)` SUBST1_TAC THENL
  [ASM_SIMP_TAC[REAL_FIELD `&0 < a ==> (f/a - y = (f - a*y)*inv a)`]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
  ASM_REAL_ARITH_TAC);;

let DYADIC_LEVEL = prove
 (`!n y v:real. floor(&2 pow n * y) / &2 pow n <= v <=>
                y < (floor(&2 pow n * v) + &1) / &2 pow n`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&0 < &2 pow n` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `integer(floor(&2 pow n * v))` ASSUME_TAC THENL
  [MESON_TAC[FLOOR]; ALL_TAC] THEN
  SUBGOAL_THEN `integer(floor(&2 pow n * y))` ASSUME_TAC THENL
  [MESON_TAC[FLOOR]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ] THEN
  SUBGOAL_THEN `v * &2 pow n = &2 pow n * v` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `y * &2 pow n = &2 pow n * y` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`&2 pow n * v`; `floor(&2 pow n * y)`] REAL_LE_FLOOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`&2 pow n * y`; `floor(&2 pow n * v)`] REAL_FLOOR_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let DYADIC_MEASURABLE = prove
 (`!p:A prob_space G Y n.
     sub_sigma_algebra p G /\ measurable_wrt p G Y
     ==> measurable_wrt p G (\x. floor(&2 pow n * Y x) / &2 pow n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[measurable_wrt] THEN X_GEN_TAC `v:real` THEN
  BETA_TAC THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ floor(&2 pow n * Y x) / &2 pow n <= v} =
     {x | x IN prob_carrier p /\ Y x < (floor(&2 pow n * v) + &1) / &2 pow n}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   REWRITE_TAC[DYADIC_LEVEL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`; `Y:A->real`;
    `(floor(&2 pow n * v) + &1) / &2 pow n`] MEASURABLE_WRT_STRICT_LT) THEN
  ASM_REWRITE_TAC[]);;

let DYADIC_SIMPLE = prove
 (`!p:A prob_space G Y n K.
     sub_sigma_algebra p G /\ measurable_wrt p G Y /\
     (!x. x IN prob_carrier p ==> abs(Y x) <= K)
     ==> simple_rv p (\x. floor(&2 pow n * Y x) / &2 pow n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simple_rv] THEN CONJ_TAC THENL
  [MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
   EXISTS_TAC `G:(A->bool)->bool` THEN ASM_SIMP_TAC[DYADIC_MEASURABLE];
   ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\m:real. m / &2 pow n)
                {m | integer m /\ --(&2 pow n * K + &1) <= m /\ m <= &2 pow n * K + &1}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_INTSEG]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `r:real` THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `floor(&2 pow n * (Y:A->real) x)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &2 pow n` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CONJUNCT1(SPEC_ALL FLOOR)] THEN
  MP_TAC(SPEC `&2 pow n * (Y:A->real) x` FLOOR) THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(&2 pow n * (Y:A->real) x) <= &2 pow n * K` MP_TAC THENL
  [REWRITE_TAC[REAL_ABS_MUL] THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
   ASM_REAL_ARITH_TAC]);;

let DYADIC_CONV = prove
 (`!Y:A->real x. ((\n. floor(&2 pow n * Y x) / &2 pow n) ---> Y x) sequentially`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REALLIM_NULL] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. inv(&2 pow n)` THEN CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[DYADIC_APPROX_BOUND];
   REWRITE_TAC[REAL_INV_POW] THEN MATCH_MP_TAC REALLIM_POWN THEN
   REWRITE_TAC[REAL_ABS_INV] THEN REAL_ARITH_TAC]);;

let DYADIC_BOUND = prove
 (`!Y:A->real x K n. abs(Y x) <= K
     ==> abs(floor(&2 pow n * Y x) / &2 pow n) <= K + &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `(Y:A->real) x`] DYADIC_APPROX_BOUND) THEN
  SUBGOAL_THEN `inv(&2 pow n) <= &1` MP_TAC THENL
  [MATCH_MP_TAC REAL_INV_LE_1 THEN
   MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC;
   ASM_REAL_ARITH_TAC]);;

(* Take-out of a bounded G-measurable multiplier: for measurable_wrt p G Y    *)
(* with abs(Y) bounded, E[Y * X | G] = Y * E[X | G] a.s.  Proved by dyadic    *)
(* approximation, the simple-multiplier take-out per level, and conditional   *)
(* dominated convergence (the dominator is (K+1)*abs(X)).                      *)
let GEN_COND_EXP_TAKE_OUT_BOUNDED = prove
 (`!p:A prob_space G Y X K.
     sub_sigma_algebra p G /\ integrable p X /\
     measurable_wrt p G Y /\ (!x. x IN prob_carrier p ==> abs(Y x) <= K)
     ==> almost_surely p
           {x | gen_cond_exp p G (\w. Y w * X w) x =
                Y x * gen_cond_exp p G X x}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Yn = \n:num. \x:A. floor(&2 pow n * Y x) / &2 pow n` THEN
  SUBGOAL_THEN `integrable p (\x:A. (K + &1) * abs(X x))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_CMUL_ALT THEN MATCH_MP_TAC INTEGRABLE_ABS THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
  [MP_TAC(ISPEC `p:A prob_space` PROB_CARRIER_NONEMPTY) THEN
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\w:A. Y w * X w)` ASSUME_TAC THENL
  [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Y:A->real`; `K:real`]
     INTEGRABLE_MUL_BOUNDED) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
    EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[]; REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable p (\w:A. (Yn:num->A->real) n w * X w)`
    ASSUME_TAC THENL
  [GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `(Yn:num->A->real) n`; `K + &1`]
     INTEGRABLE_MUL_BOUNDED) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN EXISTS_TAC `G:(A->bool)->bool` THEN
     EXPAND_TAC "Yn" THEN BETA_TAC THEN ASM_SIMP_TAC[DYADIC_MEASURABLE];
     ASM_REAL_ARITH_TAC;
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "Yn" THEN BETA_TAC THEN
     MATCH_MP_TAC DYADIC_BOUND THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!n. almost_surely p
       {x:A | gen_cond_exp p G (\w. (Yn:num->A->real) n w * X w) x =
              Yn n x * gen_cond_exp p G X x}`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC GEN_COND_EXP_TAKE_OUT_SIMPLE THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "Yn" THEN BETA_TAC THEN ASM_SIMP_TAC[DYADIC_MEASURABLE];
    EXPAND_TAC "Yn" THEN BETA_TAC THEN MATCH_MP_TAC DYADIC_SIMPLE THEN
    MAP_EVERY EXISTS_TAC [`G:(A->bool)->bool`; `K:real`] THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `almost_surely p
       {x:A | ((\n. gen_cond_exp p G (\w. (Yn:num->A->real) n w * X w) x) --->
               gen_cond_exp p G (\w. Y w * X w) x) sequentially}`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
      `(\n:num. \w:A. (Yn:num->A->real) n w * X w)`;
      `(\w:A. (Y:A->real) w * X w)`; `(\x:A. (K + &1) * abs((X:A->real) x))`]
      GEN_COND_EXP_DCT) THEN
   BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`;`x:A`] THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    EXPAND_TAC "Yn" THEN BETA_TAC THEN
    MATCH_MP_TAC DYADIC_BOUND THEN ASM_SIMP_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
    REWRITE_TAC[ALMOST_SURELY_CARRIER] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC REALLIM_MUL THEN REWRITE_TAC[REALLIM_CONST] THEN
    EXPAND_TAC "Yn" THEN BETA_TAC THEN REWRITE_TAC[DYADIC_CONV]];
   ALL_TAC] THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
    `(prob_carrier (p:A prob_space)) INTER
     (INTERS {{x:A | gen_cond_exp p G (\w. (Yn:num->A->real) n w * X w) x =
                     Yn n x * gen_cond_exp p G X x} | n IN (:num)}) INTER
     {x:A | ((\n. gen_cond_exp p G (\w. (Yn:num->A->real) n w * X w) x) --->
             gen_cond_exp p G (\w. Y w * X w) x) sequentially}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_INTER THEN CONJ_TAC THENL
   [REWRITE_TAC[ALMOST_SURELY_CARRIER];
    MATCH_MP_TAC ALMOST_SURELY_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_INTER; IN_INTERS; IN_ELIM_THM; FORALL_IN_GSPEC; IN_UNIV] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC (ISPECL [`sequentially`;
    `\n:num. (Yn:num->A->real) n x * gen_cond_exp p G X x`;
    `gen_cond_exp p G (\w. (Y:A->real) w * X w) x`;
    `(Y:A->real) x * gen_cond_exp p G X x`] REALLIM_UNIQUE) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
  [SUBGOAL_THEN
     `(\n. (Yn:num->A->real) n x * gen_cond_exp p G X x) =
      (\n. gen_cond_exp p G (\w. Yn n w * X w) x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[];
   MATCH_MP_TAC REALLIM_MUL THEN REWRITE_TAC[REALLIM_CONST] THEN
   EXPAND_TAC "Yn" THEN BETA_TAC THEN REWRITE_TAC[DYADIC_CONV]]);;

(* ------------------------------------------------------------------ *)
(* Conditional Cauchy-Schwarz inequality.                              *)
(*                                                                      *)
(* The proof is the discriminant argument done conditionally: for each  *)
(* rational q, E[(X - qY)^2|G] >= 0 a.s., which expands by linearity to  *)
(* a nonneg quadratic in q.  On the conull set where this holds for all  *)
(* rationals (a countable intersection), density and the discriminant    *)
(* test give E[XY|G]^2 <= E[X^2|G]*E[Y^2|G].                             *)
(* ------------------------------------------------------------------ *)

(* Nonneg quadratic (all real t) ==> discriminant <= 0. *)
let DISCRIMINANT_NONNEG = prove
 (`!a b c:real. &0 <= a /\ (!t. &0 <= a * t pow 2 - &2 * b * t + c)
                ==> b pow 2 <= a * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `a = &0` THENL
  [FIRST_X_ASSUM SUBST_ALL_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_LZERO; REAL_ADD_LID]) THEN
   SUBGOAL_THEN `b = &0` SUBST_ALL_TAC THENL
   [ASM_CASES_TAC `b = &0` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(c + &1) / (&2 * b)`) THEN
    ASM_SIMP_TAC[REAL_FIELD `~(b = &0) ==> &2 * b * (c + &1)/(&2 * b) = c + &1`] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[] THEN REAL_ARITH_TAC];
   SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `b / a:real`) THEN
   ASM_SIMP_TAC[REAL_FIELD
     `&0 < a ==> a * (b/a) pow 2 - &2 * b * (b/a) + c = c - b pow 2 / a`] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN `b pow 2 / a <= c` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC]);;

(* Nonneg quadratic on the rationals ==> nonneg everywhere (density). *)
let RATIONAL_DISCRIMINANT_DENSITY = prove
 (`!A B C:real. (!q. rational q ==> &0 <= A * q pow 2 - &2 * B * q + C)
                ==> (!t. &0 <= A * t pow 2 - &2 * B * t + C)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?r:num->real. !n. rational(r n) /\ abs(r n - t) < inv(&n + &1)`
    (X_CHOOSE_THEN `r:num->real` STRIP_ASSUME_TAC) THENL
  [REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN
   MATCH_MP_TAC RATIONAL_APPROXIMATION THEN
   MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((r:num->real) ---> t) sequentially` ASSUME_TAC THENL
  [REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
   MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `inv(&N)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
    [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
     REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `((\n. A * (r:num->real) n pow 2 - &2 * B * r n + C) --->
      (A * t pow 2 - &2 * B * t + C)) sequentially` ASSUME_TAC THENL
  [MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
   MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REALLIM_LMUL THEN
    MATCH_MP_TAC REALLIM_MUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REALLIM_LMUL THEN
    MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  MP_TAC(ISPECL
    [`sequentially`;
     `\n. A * (r:num->real) n pow 2 - &2 * B * r n + C`;
     `A * t pow 2 - &2 * B * t + C`; `&0:real`] REALLIM_LBOUND) THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* Combined: nonneg on rationals + a >= 0 ==> discriminant <= 0. *)
let RATIONAL_DISCRIMINANT = prove
 (`!A B C:real. &0 <= A /\
                (!q. rational q ==> &0 <= A * q pow 2 - &2 * B * q + C)
                ==> B pow 2 <= A * C`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DISCRIMINANT_NONNEG THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RATIONAL_DISCRIMINANT_DENSITY THEN
  ASM_REWRITE_TAC[]);;

(* Conditional expectation of an affine combination f - c*g + d*h. *)
let GEN_COND_EXP_LINEAR3 = prove
 (`!p:A prob_space G f g h c d.
     sub_sigma_algebra p G /\ integrable p f /\ integrable p g /\ integrable p h
     ==> almost_surely p
           {x | gen_cond_exp p G (\w. f w - c * g w + d * h w) x =
                gen_cond_exp p G f x - c * gen_cond_exp p G g x +
                d * gen_cond_exp p G h x}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (\w:A. c * g w)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\w:A. d * h w)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\w:A. f w - c * g w)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `(\u:A. (f:A->real) u - (c:real) * (g:A->real) u)`;
    `(\u:A. (d:real) * (h:A->real) u)`] GEN_COND_EXP_ADD)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `f:A->real`; `(\u:A. (c:real) * (g:A->real) u)`] GEN_COND_EXP_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `g:A->real`; `c:real`] GEN_COND_EXP_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `h:A->real`; `d:real`] GEN_COND_EXP_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `{x:A | gen_cond_exp p G (\w. f w - c * g w + d * h w) x =
            gen_cond_exp p G (\u:A. f u - c * g u) x +
            gen_cond_exp p G (\u:A. d * h u) x}`;
    `{x:A | gen_cond_exp p G (\w. f w - c * g w) x =
            gen_cond_exp p G f x - gen_cond_exp p G (\u:A. c * g u) x}`]
    ALMOST_SURELY_INTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `{x:A | gen_cond_exp p G (\w. c * g w) x = c * gen_cond_exp p G g x}`;
    `{x:A | gen_cond_exp p G (\w. d * h w) x = d * gen_cond_exp p G h x}`]
    ALMOST_SURELY_INTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
    `({x:A | gen_cond_exp p G (\w. f w - c * g w + d * h w) x =
            gen_cond_exp p G (\u:A. f u - c * g u) x +
            gen_cond_exp p G (\u:A. d * h u) x} INTER
      {x:A | gen_cond_exp p G (\w. f w - c * g w) x =
            gen_cond_exp p G f x - gen_cond_exp p G (\u:A. c * g u) x}) INTER
     ({x:A | gen_cond_exp p G (\w. c * g w) x = c * gen_cond_exp p G g x} INTER
      {x:A | gen_cond_exp p G (\w. d * h w) x = d * gen_cond_exp p G h x})` THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_INTER THEN ASM_REWRITE_TAC[];
   GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC]);;

let GEN_COND_EXP_CAUCHY_SCHWARZ = prove
 (`!p:A prob_space G X Y.
     sub_sigma_algebra p G /\
     integrable p (\x. X x pow 2) /\ integrable p (\x. Y x pow 2) /\
     integrable p (\x. X x * Y x)
     ==> almost_surely p
           {x | gen_cond_exp p G (\w. X w * Y w) x pow 2 <=
                gen_cond_exp p G (\w. X w pow 2) x *
                gen_cond_exp p G (\w. Y w pow 2) x}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `!q. almost_surely p
       {x:A | &0 <= gen_cond_exp p G (\w. X w pow 2) x -
                    &2 * q * gen_cond_exp p G (\w. X w * Y w) x +
                    q pow 2 * gen_cond_exp p G (\w. Y w pow 2) x}`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `integrable p (\w:A. (X w - q * Y w) pow 2)` ASSUME_TAC THENL
   [SUBGOAL_THEN
      `(\w:A. (X w - q * Y w) pow 2) =
       (\w. (\w. X w pow 2) w - (\w. (&2 * q) * (\w. X w * Y w) w) w
            + (\w. (q pow 2) * (\w. Y w pow 2) w) w)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN CONV_TAC REAL_RING;
     ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_SUB THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
     BETA_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
     `(\w:A. ((X:A->real) w - q * (Y:A->real) w) pow 2)`]
     GEN_COND_EXP_NONNEG) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
   DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
     `(\w:A. (X:A->real) w pow 2)`; `(\w:A. (X:A->real) w * (Y:A->real) w)`;
     `(\w:A. (Y:A->real) w pow 2)`; `(&2 * q)`; `(q:real) pow 2`]
     GEN_COND_EXP_LINEAR3) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `(\w:A. ((X:A->real) w - q * (Y:A->real) w) pow 2) =
      (\w. X w pow 2 - (&2 * q) * X w * Y w + q pow 2 * Y w pow 2)`
     ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
     `(\w:A. ((X:A->real) w - q * (Y:A->real) w) pow 2) =
      (\w. X w pow 2 - (&2 * q) * X w * Y w + q pow 2 * Y w pow 2)`]) THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `{x:A | &0 <= gen_cond_exp p G
            (\w. (X:A->real) w pow 2 - (&2 * q) * X w * Y w + q pow 2 * Y w pow 2) x}`;
     `{x:A | gen_cond_exp p G
            (\w. (X:A->real) w pow 2 - (&2 * q) * X w * Y w + q pow 2 * Y w pow 2) x =
            gen_cond_exp p G (\w. X w pow 2) x -
            (&2 * q) * gen_cond_exp p G (\w. X w * Y w) x +
            q pow 2 * gen_cond_exp p G (\w. Y w pow 2) x}`]
     ALMOST_SURELY_INTER) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
   FIRST_X_ASSUM(fun th -> EXISTS_TAC (rand(concl th)) THEN
      CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
   REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
   GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `almost_surely p {x:A | &0 <= gen_cond_exp p G (\w. Y w pow 2) x}`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
     `(\w:A. (Y:A->real) w pow 2)`] GEN_COND_EXP_NONNEG) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  MP_TAC(ISPEC `rational` COUNTABLE_AS_IMAGE) THEN
  REWRITE_TAC[COUNTABLE_RATIONAL] THEN ANTS_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `&0:real` THEN
   REWRITE_TAC[IN] THEN MESON_TAC[RATIONAL_NUM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `enum:num->real`) THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\n. {x:A | &0 <= gen_cond_exp p G (\w. X w pow 2) x -
                      &2 * ((enum:num->real) n) * gen_cond_exp p G (\w. X w * Y w) x +
                      ((enum:num->real) n) pow 2 * gen_cond_exp p G (\w. Y w pow 2) x}`]
    ALMOST_SURELY_COUNTABLE_INTER) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `{x:A | &0 <= gen_cond_exp p G (\w. Y w pow 2) x}`;
    `INTERS {{x:A | &0 <= gen_cond_exp p G (\w. X w pow 2) x -
                      &2 * ((enum:num->real) n) * gen_cond_exp p G (\w. X w * Y w) x +
                      ((enum:num->real) n) pow 2 * gen_cond_exp p G (\w. Y w pow 2) x} |
             n IN (:num)}`]
    ALMOST_SURELY_INTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
    `{x:A | &0 <= gen_cond_exp p G (\w. Y w pow 2) x} INTER
     INTERS {{x:A | &0 <= gen_cond_exp p G (\w. X w pow 2) x -
                      &2 * ((enum:num->real) n) * gen_cond_exp p G (\w. X w * Y w) x +
                      ((enum:num->real) n) pow 2 * gen_cond_exp p G (\w. Y w pow 2) x} |
             n IN (:num)}` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_INTER; IN_INTERS; IN_ELIM_THM; FORALL_IN_GSPEC; IN_UNIV] THEN
  STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC RATIONAL_DISCRIMINANT THEN CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   X_GEN_TAC `q:real` THEN DISCH_TAC THEN
   SUBGOAL_THEN `?n. q = (enum:num->real) n` (X_CHOOSE_THEN `n:num` SUBST1_TAC) THENL
   [SUBGOAL_THEN `(q:real) IN rational` MP_TAC THENL
    [ASM_REWRITE_TAC[IN]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------ *)
(* Conditional Jensen's inequality: f(E[X|G]) <= E[f(X)|G] a.s. for     *)
(* convex f.  Built from the supporting-line / affine-minorant          *)
(* representation of a convex function on R.                            *)
(* ------------------------------------------------------------------ *)

(* Three-slopes (secant monotonicity), multiplicative form. *)
let THREE_SLOPES = prove
 (`!f:real->real.
     (!a b x. a IN (:real) /\ b IN (:real) /\ x IN real_segment[a,b]
              ==> (f x - f a) * abs(b - a) <= (f b - f a) * abs(x - a))
     ==> !u m v. u < m /\ m < v
                 ==> (f m - f u) * (v - m) <= (f v - f m) * (m - u)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real`; `v:real`; `m:real`]) THEN
  REWRITE_TAC[IN_UNIV; REAL_SEGMENT_INTERVAL] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(v - u) = v - u /\ abs(m - u) = m - u`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
    `(fv - fu) * (m - u) - (fm - fu) * (v - u) =
     (fv - fm) * (m - u) - (fm - fu) * (v - m)
     ==> (fm - fu) * (v - u) <= (fv - fu) * (m - u)
         ==> (fm - fu) * (v - m) <= (fv - fm) * (m - u)`) THEN
  REAL_ARITH_TAC);;

(* Supporting line for a convex function on R: at every point m there is a
   slope s with f(m) + s*(y-m) <= f(y) for all y.  Slope = right derivative,
   built as the infimum of right-secant slopes. *)
let REAL_CONVEX_SUPPORTING_LINE = prove
 (`!f:real->real. f real_convex_on (:real)
     ==> !m. ?s. !y. f m + s * (y - m) <= f y`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `!u m v. u < m /\ m < v
             ==> (f m - f u) * (v - m) <= (f v - f m) * (m - u)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC THREE_SLOPES THEN
   ASM_REWRITE_TAC[GSYM REAL_CONVEX_ON_LEFT_SECANT_MUL]; ALL_TAC] THEN
  GEN_TAC THEN
  EXISTS_TAC `inf {((f:real->real) v - f m) / (v - m) | v | (m:real) < v}` THEN
  SUBGOAL_THEN
    `~({((f:real->real) v - f m) / (v - m) | v | (m:real) < v} = {})`
    ASSUME_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   MAP_EVERY EXISTS_TAC
     [`((f:real->real)(m + &1) - f m) / ((m + &1) - m)`; `(m:real) + &1`] THEN
   REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `!z. z IN {((f:real->real) v - f m) / (v - m) | v | (m:real) < v}
         ==> f m - f(m - &1) <= z`
    ASSUME_TAC THENL
  [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `&0 < v - m` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`m - &1:real`; `m:real`; `v:real`]) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_ARITH `m - (m - &1) = &1`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `{((f:real->real) v - f m) / (v - m) | v | (m:real) < v}` INF) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
  [EXISTS_TAC `(f:real->real) m - f(m - &1)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `s = inf {((f:real->real) v - f m) / (v - m) | v | (m:real) < v}` THEN
  STRIP_TAC THEN
  X_GEN_TAC `y:real` THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH `y < m \/ y = m \/ m < y`) THENL
  [SUBGOAL_THEN `(f m - f y) / (m - y) <= s` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `z:real` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < v - m /\ &0 < m - y` STRIP_ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(f m - f y) * (v - m) <= (f v - f m) * (m - y)` MP_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPECL [`y:real`; `m:real`; `v:real`]) THEN
     ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < a ==> (x / a * b = x * b / a)`;
                 REAL_FIELD `&0 < a ==> (b * x / a = (b * x) / a)`] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 < m - y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `f m - f y <= s * (m - y)` MP_TAC THENL
    [ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ]; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB] THEN REAL_ARITH_TAC];
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   SUBGOAL_THEN `s <= (f y - f m) / (y - m)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `y:real` THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `&0 < y - m` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `s * (y - m) <= f y - f m` MP_TAC THENL
    [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ]; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB] THEN REAL_ARITH_TAC]]);;

(* Slope function with both secant bounds (SKOLEMized supporting line). *)
let SUPPORTING_SLOPE = prove
 (`!f:real->real. f real_convex_on (:real)
     ==> ?sl. (!m y. f m + sl m * (y - m) <= f y) /\
              (!m. sl m <= f(m + &1) - f m) /\
              (!m. f m - f(m - &1) <= sl m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP REAL_CONVEX_SUPPORTING_LINE (ASSUME `f real_convex_on (:real)`)) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `sl:real->real` ASSUME_TAC) THEN
  EXISTS_TAC `sl:real->real` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN GEN_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPECL [`m:real`; `m + &1:real`]) THEN REAL_ARITH_TAC;
   FIRST_X_ASSUM(MP_TAC o SPECL [`m:real`; `m - &1:real`]) THEN REAL_ARITH_TAC]);;

(* Continuity of a convex function at every real point. *)
let CONVEX_CONT_AT = prove
 (`!f:real->real. f real_convex_on (:real) ==> !w. f real_continuous atreal w`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `(:real)`]
    REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT) THEN
  REWRITE_TAC[REAL_OPEN_UNIV; IN_UNIV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_CONVEX_ON_CONTINUOUS THEN ASM_REWRITE_TAC[REAL_OPEN_UNIV]);;

(* Continuous function applied to a convergent sequence. *)
let CONTINUOUS_COMPOSE_SEQ = prove
 (`!f z q:num->real. f real_continuous atreal z /\ (q ---> z) sequentially
     ==> ((\n. f(q n)) ---> f z) sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN ASM_REWRITE_TAC[]);;

(* abs is continuous; abs of a convergent sequence converges. *)
let ABS_CONT = prove
 (`!L:real. abs real_continuous atreal L`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`atreal L`; `\x:real. x`] REAL_CONTINUOUS_ABS) THEN
  REWRITE_TAC[REAL_CONTINUOUS_AT_ID; ETA_AX]);;

let ABS_LIM = prove
 (`!a L. (a ---> L) sequentially ==> ((\n. abs(a n)) ---> abs L) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`abs`; `sequentially`; `a:num->real`; `L:real`]
    REALLIM_REAL_CONTINUOUS_FUNCTION) THEN
  REWRITE_TAC[ABS_CONT] THEN ASM_REWRITE_TAC[]);;

(* Affine-minorant representation: if every supporting-line value at rational
   base points is <= C, then f z <= C.  (Density of rationals + continuity.) *)
let CONVEX_AFFINE_MINORANT_SUP = prove
 (`!f sl:real->real. f real_convex_on (:real) /\
     (!m. sl m <= f(m + &1) - f m) /\ (!m. f m - f(m - &1) <= sl m)
     ==> !z C. (!q. rational q ==> f q + sl q * (z - q) <= C) ==> f z <= C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!w:real. f real_continuous atreal w` ASSUME_TAC THENL
  [MATCH_MP_TAC CONVEX_CONT_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?q:num->real. !n. rational(q n) /\ abs(q n - z) < inv(&n + &1)`
    (X_CHOOSE_THEN `q:num->real` STRIP_ASSUME_TAC) THENL
  [REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN
   MATCH_MP_TAC RATIONAL_APPROXIMATION THEN
   MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((q:num->real) ---> z) sequentially` ASSUME_TAC THENL
  [REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
   MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `inv(&N)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
    [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
     REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `((\n. f((q:num->real) n)) ---> f z) sequentially` ASSUME_TAC THENL
  [MATCH_MP_TAC CONTINUOUS_COMPOSE_SEQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((\n. f((q:num->real) n + &1)) ---> f(z + &1)) sequentially`
    ASSUME_TAC THENL
  [MATCH_MP_TAC CONTINUOUS_COMPOSE_SEQ THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REALLIM_ADD THEN ASM_REWRITE_TAC[REALLIM_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN `((\n. f((q:num->real) n - &1)) ---> f(z - &1)) sequentially`
    ASSUME_TAC THENL
  [MATCH_MP_TAC CONTINUOUS_COMPOSE_SEQ THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REALLIM_SUB THEN ASM_REWRITE_TAC[REALLIM_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN `((\n. sl((q:num->real) n) * (z - q n)) ---> &0) sequentially`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
   EXISTS_TAC
     `\n. (abs(f((q:num->real) n + &1) - f(q n)) +
           abs(f(q n - &1) - f(q n))) * abs(z - q n)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    UNDISCH_TAC `!m. (sl:real->real) m <= f(m + &1) - f m` THEN
    DISCH_THEN(MP_TAC o SPEC `(q:num->real) n`) THEN
    UNDISCH_TAC `!m. f m - f(m - &1) <= (sl:real->real) m` THEN
    DISCH_THEN(MP_TAC o SPEC `(q:num->real) n`) THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN
      `&0 = (abs(f(z + &1) - f z) + abs(f(z - &1) - f z)) * abs(z - z)`
      SUBST1_TAC THENL
    [REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THEN MATCH_MP_TAC ABS_LIM THEN
     MATCH_MP_TAC REALLIM_SUB THEN ASM_REWRITE_TAC[REALLIM_CONST];
     MATCH_MP_TAC ABS_LIM THEN MATCH_MP_TAC REALLIM_SUB THEN
     ASM_REWRITE_TAC[REALLIM_CONST]]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `((\n. f((q:num->real) n) + sl(q n) * (z - q n)) ---> f z) sequentially`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `(f:real->real) z = f z + &0` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_ADD THEN ASM_REWRITE_TAC[REAL_ADD_RID]; ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
    [`sequentially`; `\n. f((q:num->real) n) + sl(q n) * (z - q n)`;
     `(f:real->real) z`; `C:real`] REALLIM_UBOUND) THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* E[a*X + b | G] = a*E[X|G] + b a.s. *)
let GEN_COND_EXP_AFFINE = prove
 (`!p:A prob_space G X a b.
     sub_sigma_algebra p G /\ integrable p X
     ==> almost_surely p
           {x | gen_cond_exp p G (\w. a * X w + b) x =
                a * gen_cond_exp p G X x + b}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (\w:A. a * X w)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\w:A. b:real)` ASSUME_TAC THENL
  [REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `(\w:A. a * (X:A->real) w)`; `(\w:A. b:real)`] GEN_COND_EXP_ADD)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`; `X:A->real`; `a:real`]
    GEN_COND_EXP_CMUL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`; `b:real`]
    GEN_COND_EXP_CONST) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `{x:A | gen_cond_exp p G (\w. a * X w + b) x =
            gen_cond_exp p G (\w. a * X w) x + gen_cond_exp p G (\w. b) x}`;
    `{x:A | gen_cond_exp p G (\w. a * X w) x = a * gen_cond_exp p G X x}`]
    ALMOST_SURELY_INTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `({x:A | gen_cond_exp p G (\w. a * X w + b) x =
            gen_cond_exp p G (\w. a * X w) x + gen_cond_exp p G (\w. b) x} INTER
      {x:A | gen_cond_exp p G (\w. a * X w) x = a * gen_cond_exp p G X x})`;
    `{x:A | gen_cond_exp p G (\w. b) x = b}`]
    ALMOST_SURELY_INTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  FIRST_X_ASSUM(fun th -> EXISTS_TAC (rand(concl th)) THEN
     CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* Conditional Jensen's inequality. *)
let GEN_COND_EXP_JENSEN = prove
 (`!p:A prob_space G X f.
     sub_sigma_algebra p G /\ integrable p X /\
     integrable p (\x. f(X x)) /\ f real_convex_on (:real)
     ==> almost_surely p
           {x | f(gen_cond_exp p G X x) <= gen_cond_exp p G (\w. f(X w)) x}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `sl:real->real` STRIP_ASSUME_TAC o
    MATCH_MP SUPPORTING_SLOPE) THEN
  SUBGOAL_THEN
    `!q. almost_surely p
       {x:A | sl q * gen_cond_exp p G X x + (f q - sl q * q) <=
              gen_cond_exp p G (\w. f(X w)) x}`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`; `X:A->real`;
     `(sl:real->real) q`; `(f:real->real) q - sl q * q`] GEN_COND_EXP_AFFINE) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
     `(\w:A. (sl:real->real) q * (X:A->real) w + ((f:real->real) q - sl q * q))`;
     `(\w:A. (f:real->real)((X:A->real) w))`] GEN_COND_EXP_MONOTONE) THEN
   ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[INTEGRABLE_CONST]];
     X_GEN_TAC `w:A` THEN DISCH_TAC THEN
     MP_TAC(SPECL [`q:real`; `(X:A->real) w`]
       (ASSUME `!m y. f m + sl m * (y - m) <= f y`)) THEN
     REAL_ARITH_TAC];
    ALL_TAC] THEN
   DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `{x:A | gen_cond_exp p G (\w. sl q * X w + (f q - sl q * q)) x =
             sl q * gen_cond_exp p G X x + (f q - sl q * q)}`;
     `{x:A | gen_cond_exp p G (\w. sl q * X w + (f q - sl q * q)) x <=
             gen_cond_exp p G (\w. f(X w)) x}`]
     ALMOST_SURELY_INTER) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
   FIRST_X_ASSUM(fun th -> EXISTS_TAC (rand(concl th)) THEN
      CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
   REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
   GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(ISPEC `rational` COUNTABLE_AS_IMAGE) THEN
  REWRITE_TAC[COUNTABLE_RATIONAL] THEN ANTS_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `&0:real` THEN
   REWRITE_TAC[IN] THEN MESON_TAC[RATIONAL_NUM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `enum:num->real`) THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\n. {x:A | (sl:real->real)((enum:num->real) n) * gen_cond_exp p G X x +
                (f(enum n) - sl(enum n) * (enum n)) <=
                gen_cond_exp p G (\w. f(X w)) x}`]
    ALMOST_SURELY_COUNTABLE_INTER) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  FIRST_X_ASSUM(fun th -> EXISTS_TAC (rand(concl th)) THEN
     CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_INTERS; IN_ELIM_THM; FORALL_IN_GSPEC; IN_UNIV] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `sl:real->real`] CONVEX_AFFINE_MINORANT_SUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`gen_cond_exp p G (X:A->real) x`;
     `gen_cond_exp p G (\w. f((X:A->real) w)) x`]) THEN
  ANTS_TAC THENL
  [X_GEN_TAC `q:real` THEN DISCH_TAC THEN
   SUBGOAL_THEN `?n. q = (enum:num->real) n` (X_CHOOSE_THEN `n:num` SUBST1_TAC) THENL
   [SUBGOAL_THEN `(q:real) IN rational` MP_TAC THENL
    [ASM_REWRITE_TAC[IN]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC;
   REWRITE_TAC[]]);;

(* ------------------------------------------------------------------ *)
(* Corollaries of conditional Jensen.                                  *)
(* ------------------------------------------------------------------ *)

(* x^2 is convex on the whole line (second-derivative test). *)
let X2_CONVEX = prove
 (`(\x:real. x pow 2) real_convex_on (:real)`,
  MP_TAC(ISPECL [`\x:real. x pow 2`; `\x:real. &2 * x`; `\x:real. &2`; `(:real)`]
    REAL_CONVEX_ON_SECOND_DERIVATIVE) THEN
  REWRITE_TAC[IS_REALINTERVAL_UNIV; IN_UNIV] THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIV; IN_SING] THEN MESON_TAC[REAL_ARITH `~(&0 = &1)`];
    CONJ_TAC THEN GEN_TAC THEN REAL_DIFF_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN REAL_ARITH_TAC];
   DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

(* Conditional L2 contraction: E[X|G]^2 <= E[X^2|G] a.s.  (Jensen, f = x^2.) *)
let GEN_COND_EXP_L2_CONTRACTION = prove
 (`!p:A prob_space G X.
     sub_sigma_algebra p G /\ integrable p X /\ integrable p (\x. X x pow 2)
     ==> almost_surely p
           {x | gen_cond_exp p G X x pow 2 <= gen_cond_exp p G (\w. X w pow 2) x}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`; `X:A->real`;
    `\x:real. x pow 2`] GEN_COND_EXP_JENSEN) THEN
  ASM_REWRITE_TAC[X2_CONVEX] THEN BETA_TAC THEN REWRITE_TAC[]);;

(* Conditional Jensen for exp: exp(E[X|G]) <= E[exp X|G] a.s. *)
let GEN_COND_EXP_JENSEN_EXP = prove
 (`!p:A prob_space G X.
     sub_sigma_algebra p G /\ integrable p X /\ integrable p (\x. exp(X x))
     ==> almost_surely p
           {x | exp(gen_cond_exp p G X x) <= gen_cond_exp p G (\w. exp(X w)) x}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`; `X:A->real`;
    `exp`] GEN_COND_EXP_JENSEN) THEN
  ASM_REWRITE_TAC[REAL_CONVEX_ON_EXP; ETA_AX]);;

(* Conditional triangle inequality: E[|X+Y| |G] <= E[|X| |G] + E[|Y| |G] a.s. *)
let GEN_COND_EXP_TRIANGLE = prove
 (`!p:A prob_space G X Y.
     sub_sigma_algebra p G /\ integrable p X /\ integrable p Y
     ==> almost_surely p
           {x | gen_cond_exp p G (\w. abs(X w + Y w)) x <=
                gen_cond_exp p G (\w. abs(X w)) x +
                gen_cond_exp p G (\w. abs(Y w)) x}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (\w:A. abs(X w))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\w:A. abs(Y w))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\w:A. abs(X w + Y w))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `(\w:A. abs((X:A->real) w))`; `(\w:A. abs((Y:A->real) w))`]
    GEN_COND_EXP_ADD)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `(\w:A. abs((X:A->real) w + Y w))`;
    `(\w:A. abs((X:A->real) w) + abs(Y w))`] GEN_COND_EXP_MONOTONE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `{x:A | gen_cond_exp p G (\w. abs(X w + Y w)) x <=
            gen_cond_exp p G (\w. abs(X w) + abs(Y w)) x}`;
    `{x:A | gen_cond_exp p G (\w. abs(X w) + abs(Y w)) x =
            gen_cond_exp p G (\w. abs(X w)) x + gen_cond_exp p G (\w. abs(Y w)) x}`]
    ALMOST_SURELY_INTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  FIRST_X_ASSUM(fun th -> EXISTS_TAC (rand(concl th)) THEN
     CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Integrability of h * phi * indicator_fn A when phi bounded on A *)
let INTEGRABLE_PRODUCT_INDICATOR = prove
 (`!p:A prob_space G (h:A->real) (phi:A->real) (A:A->bool) K.
    sub_sigma_algebra p G /\ integrable p h /\
    measurable_wrt p G phi /\ A IN G /\ &0 <= K /\
    (!x. x IN prob_carrier p /\ x IN A ==> abs(phi x) <= K)
    ==> integrable p (\x. h x * phi x * indicator_fn A x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. h x * phi x * indicator_fn A x) =
                 (\x. h x * (phi x * indicator_fn A x))` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; REAL_MUL_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN
  EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [SUBGOAL_THEN `(\x:A. phi x * indicator_fn A x) =
                  (\x. indicator_fn A x * phi x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
   EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MEASURABLE_WRT_MUL_INDICATOR THEN ASM_REWRITE_TAC[];
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[indicator_fn] THEN
   COND_CASES_TAC THENL
   [REWRITE_TAC[REAL_MUL_RID] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ABS_NUM] THEN ASM_REAL_ARITH_TAC]]);;

(* Integrability of |h| * indicator *)
let INTEGRABLE_ABS_INDICATOR = prove
 (`!p:A prob_space (h:A->real) (A:A->bool).
    integrable p h /\ A IN prob_events p
    ==> integrable p (\x. abs(h x) * indicator_fn A x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. abs(h x) * indicator_fn A x) =
                 (\x. (\y. abs(h y)) x * indicator_fn A x)` SUBST1_TAC THENL
  [REWRITE_TAC[];
   MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[]]);;

(* Binary halving: quantitative bound for zero-integral bounded measurable *)
let EXPECTATION_ZERO_HALVING = prove
 (`!p G (h:A->real).
    sub_sigma_algebra p G /\ integrable p h /\
    (!B. B IN G ==>
       expectation p (\x. h x * indicator_fn B x) = &0)
    ==> !n K phi A.
          measurable_wrt p G phi /\ A IN G /\ &0 <= K /\
          (!x. x IN prob_carrier p /\ x IN A ==> abs(phi x) <= K)
          ==> abs(expectation p (\x. h x * phi x * indicator_fn A x))
              <= K / &2 pow n *
                 expectation p (\x. abs(h x) * indicator_fn A x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
  [(* Base case: n = 0. Goal: |E[h*phi*1_A]| <= K * E[|h|*1_A] *)
   REWRITE_TAC[real_pow; REAL_DIV_1] THEN
   SUBGOAL_THEN `(A:A->bool) IN prob_events p` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
    EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. h x * phi x * indicator_fn A x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_PRODUCT_INDICATOR THEN
    EXISTS_TAC `G:(A->bool)->bool` THEN EXISTS_TAC `K:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. abs(h x) * indicator_fn A x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ABS_INDICATOR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation p (\x:A. abs(h x * phi x * indicator_fn A x))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_ABS_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `K * expectation p (\x:A. abs(h x) * indicator_fn A x) =
      expectation p (\x. K * (abs(h x) * indicator_fn A x))`
     SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    MATCH_MP_TAC EXPECTATION_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   MATCH_MP_TAC EXPECTATION_MONO THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:A. K * (abs(h x) * indicator_fn A x)) =
                   (\x. K * (\y. abs(h y) * indicator_fn A y) x)`
      SUBST1_TAC THENL
    [REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_CMUL_ALT THEN ASM_REWRITE_TAC[];
    BETA_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(indicator_fn A (x:A)) = indicator_fn A x`
      SUBST1_TAC THENL
    [REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN
     REWRITE_TAC[REAL_ABS_NUM]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THENL
    [REWRITE_TAC[REAL_MUL_RID] THEN
     SUBGOAL_THEN `K * abs((h:A->real) x) = abs(h x) * K` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
     REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL]]];

   (* Induction step: n -> SUC n *)
   (* Define Apos = A INTER {phi >= 0}, Aneg = A INTER {phi < 0} *)
   ABBREV_TAC
     `Apos = (A:A->bool) INTER {x | x IN prob_carrier p /\ phi x >= &0}` THEN
   ABBREV_TAC
     `Aneg = (A:A->bool) INTER {x:A | x IN prob_carrier p /\ phi x < &0}` THEN
   SUBGOAL_THEN `(Apos:A->bool) IN G` ASSUME_TAC THENL
   [EXPAND_TAC "Apos" THEN MATCH_MP_TAC SIGMA_ALGEBRA_INTER THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURABLE_WRT_GE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `(Aneg:A->bool) IN G` ASSUME_TAC THENL
   [EXPAND_TAC "Aneg" THEN MATCH_MP_TAC SIGMA_ALGEBRA_INTER THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURABLE_WRT_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `(A:A->bool) IN prob_events p` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
    EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `(A:A->bool) SUBSET prob_carrier p` ASSUME_TAC THENL
   [REWRITE_TAC[prob_carrier; SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `(Apos:A->bool) IN prob_events p` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
    EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `(Aneg:A->bool) IN prob_events p` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
    EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Bounds on shifted functions *)
   SUBGOAL_THEN `!x:A. x IN prob_carrier p /\ x IN Apos
     ==> abs(phi x - K / &2) <= K / &2` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN A /\ phi x >= &0` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `(x:A) IN Apos` THEN EXPAND_TAC "Apos" THEN
     REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `abs((phi:A->real) x) <= K` ASSUME_TAC THENL
    [UNDISCH_TAC `!x:A. x IN prob_carrier p /\ x IN A ==> abs(phi x) <= K` THEN
     DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
     UNDISCH_TAC `(phi:A->real) x >= &0` THEN
     UNDISCH_TAC `abs((phi:A->real) x) <= K` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `!x:A. x IN prob_carrier p /\ x IN Aneg
     ==> abs(phi x + K / &2) <= K / &2` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN A /\ phi x < &0` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `(x:A) IN Aneg` THEN EXPAND_TAC "Aneg" THEN
     REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `abs((phi:A->real) x) <= K` ASSUME_TAC THENL
    [UNDISCH_TAC `!x:A. x IN prob_carrier p /\ x IN A ==> abs(phi x) <= K` THEN
     DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
     UNDISCH_TAC `(phi:A->real) x < &0` THEN
     UNDISCH_TAC `abs((phi:A->real) x) <= K` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   (* Measurability of shifted functions *)
   SUBGOAL_THEN `measurable_wrt p G (\x:A. phi x - K / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_WRT_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `measurable_wrt p G (\x:A. phi x + K / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_WRT_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Integrability of the key terms *)
   SUBGOAL_THEN `integrable p (\x:A. h x * phi x * indicator_fn A x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_PRODUCT_INDICATOR THEN
    EXISTS_TAC `G:(A->bool)->bool` THEN EXISTS_TAC `K:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. h x * (phi x - K / &2) * indicator_fn Apos x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_PRODUCT_INDICATOR THEN
    EXISTS_TAC `G:(A->bool)->bool` THEN EXISTS_TAC `K / &2` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. h x * (phi x + K / &2) * indicator_fn Aneg x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_PRODUCT_INDICATOR THEN
    EXISTS_TAC `G:(A->bool)->bool` THEN EXISTS_TAC `K / &2` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. abs(h x) * indicator_fn A x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ABS_INDICATOR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. abs(h x) * indicator_fn Apos x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ABS_INDICATOR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `integrable p (\x:A. abs(h x) * indicator_fn Aneg x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ABS_INDICATOR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* E[h * 1_Apos] = 0, E[h * 1_Aneg] = 0 *)
   SUBGOAL_THEN `expectation p (\x:A. h x * indicator_fn Apos x) = &0`
     ASSUME_TAC THENL
   [UNDISCH_TAC `!B:A->bool. B IN G ==>
      expectation p (\x. h x * indicator_fn B x) = &0` THEN
    DISCH_THEN(MP_TAC o SPEC `Apos:A->bool`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `expectation p (\x:A. h x * indicator_fn Aneg x) = &0`
     ASSUME_TAC THENL
   [UNDISCH_TAC `!B:A->bool. B IN G ==>
      expectation p (\x. h x * indicator_fn B x) = &0` THEN
    DISCH_THEN(MP_TAC o SPEC `Aneg:A->bool`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Key identity: E[h*phi*1_A] = E[h*(phi-K/2)*1_Apos] + E[h*(phi+K/2)*1_Aneg]
      because E[h*1_Apos] = E[h*1_Aneg] = 0 *)
   SUBGOAL_THEN
     `expectation p (\x:A. h x * phi x * indicator_fn A x) =
      expectation p (\x. h x * (phi x - K / &2) * indicator_fn Apos x) +
      expectation p (\x. h x * (phi x + K / &2) * indicator_fn Aneg x)`
     SUBST1_TAC THENL
   [SUBGOAL_THEN `integrable p (\x:A. h x * indicator_fn Apos x)`
      ASSUME_TAC THENL
    [SUBGOAL_THEN `(\x:A. h x * indicator_fn Apos x) =
                    (\x. h x * indicator_fn Apos x)` SUBST1_TAC THENL
     [REWRITE_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `integrable p (\x:A. h x * indicator_fn Aneg x)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    (* E[h*phi*1_A] = E[h*phi*1_Apos] + E[h*phi*1_Aneg]
       since 1_A = 1_Apos + 1_Aneg on prob_carrier *)
    SUBGOAL_THEN `!x:A. x IN prob_carrier p /\ x IN Apos ==> abs(phi x) <= K`
      ASSUME_TAC THENL
    [X_GEN_TAC `x:A` THEN STRIP_TAC THEN
     UNDISCH_TAC `!x:A. x IN prob_carrier p /\ x IN A ==> abs(phi x) <= K` THEN
     DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN MATCH_MP_TAC THEN
     UNDISCH_TAC `(x:A) IN Apos` THEN EXPAND_TAC "Apos" THEN
     REWRITE_TAC[IN_INTER] THEN MESON_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `!x:A. x IN prob_carrier p /\ x IN Aneg ==> abs(phi x) <= K`
      ASSUME_TAC THENL
    [X_GEN_TAC `x:A` THEN STRIP_TAC THEN
     UNDISCH_TAC `!x:A. x IN prob_carrier p /\ x IN A ==> abs(phi x) <= K` THEN
     DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN MATCH_MP_TAC THEN
     UNDISCH_TAC `(x:A) IN Aneg` THEN EXPAND_TAC "Aneg" THEN
     REWRITE_TAC[IN_INTER] THEN MESON_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `integrable p (\x:A. h x * phi x * indicator_fn Apos x)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_PRODUCT_INDICATOR THEN
     EXISTS_TAC `G:(A->bool)->bool` THEN EXISTS_TAC `K:real` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `integrable p (\x:A. h x * phi x * indicator_fn Aneg x)`
      ASSUME_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_PRODUCT_INDICATOR THEN
     EXISTS_TAC `G:(A->bool)->bool` THEN EXISTS_TAC `K:real` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    (* Now the identity via expectation algebra *)
    (* E[h*phi*1_A] = E[h*phi*1_Apos] + E[h*phi*1_Aneg] *)
    SUBGOAL_THEN
      `expectation p (\x:A. h x * phi x * indicator_fn A x) =
       expectation p (\x. h x * phi x * indicator_fn Apos x) +
       expectation p (\x. h x * phi x * indicator_fn Aneg x)`
      SUBST1_TAC THENL
    [SUBGOAL_THEN
       `(\x:A. h x * phi x * indicator_fn A x) =
        (\x. h x * phi x * indicator_fn Apos x +
             h x * phi x * indicator_fn Aneg x)`
       SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN
      REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      EXPAND_TAC "Apos" THEN EXPAND_TAC "Aneg" THEN
      REWRITE_TAC[indicator_fn; IN_INTER; IN_ELIM_THM] THEN
      ASM_CASES_TAC `(x:A) IN A` THEN ASM_REWRITE_TAC[] THENL
      [ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THENL
       [ASM_CASES_TAC `(phi:A->real) x >= &0` THEN ASM_REWRITE_TAC[] THENL
        [SUBGOAL_THEN `~((phi:A->real) x < &0)` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
         SUBGOAL_THEN `(phi:A->real) x < &0` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
        ASM_MESON_TAC[SUBSET]];
       REAL_ARITH_TAC];
      MATCH_MP_TAC EXPECTATION_ADD THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
    (* Prove E[h*phi*1_Apos] = E[h*(phi-K/2)*1_Apos] using E[h*1_Apos]=0 *)
    SUBGOAL_THEN
      `expectation p (\x:A. h x * phi x * indicator_fn Apos x) =
       expectation p (\x. h x * (phi x - K / &2) * indicator_fn Apos x)`
      SUBST1_TAC THENL
    [SUBGOAL_THEN
       `(\x:A. h x * phi x * indicator_fn Apos x) =
        (\x. h x * (phi x - K / &2) * indicator_fn Apos x +
             K / &2 * (h x * indicator_fn Apos x))`
       SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
     MP_TAC(ISPECL [`p:A prob_space`;
                     `\x:A. h x * (phi x - K / &2) * indicator_fn Apos x`;
                     `\x:A. K / &2 * (h:A->real) x * indicator_fn (Apos:A->bool) x`]
       EXPECTATION_ADD) THEN
     CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_CMUL_ALT THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     MP_TAC(ISPECL [`p:A prob_space`; `K / &2`;
                     `\x:A. (h:A->real) x * indicator_fn (Apos:A->bool) x`]
       EXPECTATION_CMUL) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
     DISCH_THEN SUBST1_TAC THEN
     ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID]; ALL_TAC] THEN
    (* Prove E[h*phi*1_Aneg] = E[h*(phi+K/2)*1_Aneg] using E[h*1_Aneg]=0 *)
    SUBGOAL_THEN
      `expectation p (\x:A. h x * phi x * indicator_fn Aneg x) =
       expectation p (\x. h x * (phi x + K / &2) * indicator_fn Aneg x)`
      SUBST1_TAC THENL
    [SUBGOAL_THEN
       `(\x:A. h x * phi x * indicator_fn Aneg x) =
        (\x. h x * (phi x + K / &2) * indicator_fn Aneg x +
             --(K / &2) * (h x * indicator_fn Aneg x))`
       SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
     MP_TAC(ISPECL [`p:A prob_space`;
                     `\x:A. h x * (phi x + K / &2) * indicator_fn Aneg x`;
                     `\x:A. --(K / &2) * (h:A->real) x * indicator_fn (Aneg:A->bool) x`]
       EXPECTATION_ADD) THEN
     CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_CMUL_ALT THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     MP_TAC(ISPECL [`p:A prob_space`; `--(K / &2)`;
                     `\x:A. (h:A->real) x * indicator_fn (Aneg:A->bool) x`]
       EXPECTATION_CMUL) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
     DISCH_THEN SUBST1_TAC THEN
     ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   (* Now apply triangle inequality, then IH *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC
     `abs(expectation p (\x:A. h x * (phi x - K / &2) * indicator_fn Apos x)) +
      abs(expectation p (\x. h x * (phi x + K / &2) * indicator_fn Aneg x))` THEN
   CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   (* Apply IH to each term *)
   SUBGOAL_THEN
     `abs(expectation p (\x:A. h x * (phi x - K / &2) * indicator_fn Apos x)) <=
      (K / &2) / &2 pow n *
      expectation p (\x. abs(h x) * indicator_fn Apos x)`
     ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`K / &2`; `\x:A. phi x - K / &2`;
                                   `Apos:A->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `abs(expectation p (\x:A. h x * (phi x + K / &2) * indicator_fn Aneg x)) <=
      (K / &2) / &2 pow n *
      expectation p (\x. abs(h x) * indicator_fn Aneg x)`
     ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`K / &2`; `\x:A. phi x + K / &2`;
                                   `Aneg:A->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC
     `(K / &2) / &2 pow n *
      expectation p (\x:A. abs(h x) * indicator_fn Apos x) +
      (K / &2) / &2 pow n *
      expectation p (\x. abs(h x) * indicator_fn Aneg x)` THEN
   CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
   (* E[|h|*1_Apos] + E[|h|*1_Aneg] = E[|h|*1_A] *)
   SUBGOAL_THEN
     `expectation p (\x:A. abs(h x) * indicator_fn Apos x) +
      expectation p (\x. abs(h x) * indicator_fn Aneg x) =
      expectation p (\x. abs(h x) * indicator_fn A x)` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    SUBGOAL_THEN
      `(\x:A. abs(h x) * indicator_fn A x) =
       (\x. abs(h x) * indicator_fn Apos x +
            abs(h x) * indicator_fn Aneg x)` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN
     REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN AP_TERM_TAC THEN
     EXPAND_TAC "Apos" THEN EXPAND_TAC "Aneg" THEN
     REWRITE_TAC[indicator_fn; IN_INTER; IN_ELIM_THM] THEN
     ASM_CASES_TAC `(x:A) IN A` THEN ASM_REWRITE_TAC[] THENL
     [ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THENL
      [ASM_CASES_TAC `(phi:A->real) x >= &0` THEN ASM_REWRITE_TAC[] THENL
       [SUBGOAL_THEN `~((phi:A->real) x < &0)` (fun th -> REWRITE_TAC[th]) THENL
        [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        SUBGOAL_THEN `(phi:A->real) x < &0` (fun th -> REWRITE_TAC[th]) THENL
        [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
       ASM_MESON_TAC[SUBSET]];
      REAL_ARITH_TAC];
     MATCH_MP_TAC EXPECTATION_ADD THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* (K/2)/2^n * E[|h|*1_A] <= K/2^{SUC n} * E[|h|*1_A] *)
   SUBGOAL_THEN `(K / &2) / &2 pow n = K / &2 pow (SUC n)`
     SUBST1_TAC THENL
   [REWRITE_TAC[real_pow; real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]]);;

(* Archimedean shrinking: if abs x <= K/2^n * C for all n and C >= 0, then x = 0 *)
let POW2_SHRINK_ZERO = prove
 (`(!n. abs x <= K / &2 pow n * C) /\ &0 <= C ==> x = &0`,
  STRIP_TAC THEN
  ASM_CASES_TAC `abs(x:real) = &0` THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs(x:real)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K * C` ASSUME_TAC THENL
  [FIRST_ASSUM(MP_TAC o SPEC `0`) THEN
   REWRITE_TAC[real_pow; REAL_DIV_1] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(ISPEC `K * C * inv(abs(x:real))` REAL_ARCH_POW2) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `N:num`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(&2 pow N = &0)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_POW_NZ THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `K / &2 pow N * &2 pow N = K` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 pow N` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(x:real) * &2 pow N <= (K / &2 pow N * C) * &2 pow N`
    MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(K / &2 pow N * C) * &2 pow N = K * C`
    SUBST1_TAC THENL
  [ONCE_REWRITE_TAC[REAL_ARITH `(a * c) * b = (a * b) * c:real`] THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(K * C * inv(abs(x:real))) * abs x < &2 pow N * abs x`
    MP_TAC THENL
  [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(K * C * inv(abs(x:real))) * abs x = K * C`
    SUBST1_TAC THENL
  [ONCE_REWRITE_TAC[REAL_ARITH `(a * (b * c)) * d = (a * b) * (c * d):real`] THEN
   SUBGOAL_THEN `inv(abs(x:real)) * abs x = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_MUL_RID]]; ALL_TAC] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `abs(x:real) * &2 pow N <= K * C` THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REAL_ARITH_TAC);;

(* Corollary: if E[h*1_B] = 0 for all B in G, then E[h*phi] = 0
   for bounded G-measurable phi *)
let EXPECTATION_ZERO_BOUNDED_MEASURABLE = prove
 (`!p:A prob_space G (h:A->real) (phi:A->real) K.
    sub_sigma_algebra p G /\ integrable p h /\
    (!B. B IN G ==> expectation p (\x. h x * indicator_fn B x) = &0) /\
    measurable_wrt p G phi /\ &0 <= K /\
    (!x. x IN prob_carrier p ==> abs(phi x) <= K)
    ==> expectation p (\x. h x * phi x) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(INST [`expectation p (\x:A. (h:A->real) x * (phi:A->real) x)`,
               `x:real`;
               `expectation p (\x:A. abs((h:A->real) x))`, `C:real`]
    POW2_SHRINK_ZERO) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [GEN_TAC THEN
    MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`; `h:A->real`]
      EXPECTATION_ZERO_HALVING) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`n:num`; `K:real`; `phi:A->real`;
                                 `prob_carrier(p:A prob_space)`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `prob_carrier(p:A prob_space) IN G` ASSUME_TAC THENL
    [MATCH_MP_TAC SUB_SIGMA_ALGEBRA_CARRIER_IN THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN
      `expectation p (\x:A. h x * phi x * indicator_fn (prob_carrier p) x) =
       expectation p (\x. h x * phi x)`
      (fun th -> REWRITE_TAC[th]) THENL
    [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     REWRITE_TAC[indicator_fn] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN
      `expectation p (\x:A. abs(h x) * indicator_fn (prob_carrier p) x) =
       expectation p (\x. abs(h x))`
      (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[indicator_fn] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POS]]];
   SIMP_TAC[]]);;


(* ================================================================== *)
(* L2 CONTRACTION AND CONDITIONAL VARIANCE                             *)
(* ================================================================== *)

(* L2 contraction: E[(cond_exp X)^2] <= E[X^2] *)
let COND_EXP_L2_CONTRACTION = prove
 (`!p:A prob_space G (X:A->real).
     sub_sigma_algebra p G /\ FINITE G /\
     integrable p X /\ integrable p (\x. X x pow 2)
     ==> expectation p (\x. cond_exp p G X x pow 2) <=
         expectation p (\x. X x pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simple_rv p (cond_exp p G (X:A->real))` ASSUME_TAC THENL
  [MATCH_MP_TAC COND_EXP_SIMPLE_RV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (cond_exp p G (X:A->real))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SIMPLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `measurable_wrt p G (cond_exp p G (X:A->real))` ASSUME_TAC THENL
  [MATCH_MP_TAC COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Get abs bound for cond_exp *)
  SUBGOAL_THEN
    `?K. &0 <= K /\ !z:A. z IN prob_carrier p
         ==> abs(cond_exp p G (X:A->real) z) <= K`
    (X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC) THENL
  [MP_TAC(SPECL [`p:A prob_space`;
     `\x:A. abs(cond_exp p G (X:A->real) x)`] SIMPLE_RV_BOUNDED) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_ABS THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   BETA_TAC THEN DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN
   EXISTS_TAC `max M (&0)` THEN CONJ_TAC THENL
   [REAL_ARITH_TAC;
    ASM_MESON_TAC[REAL_ARITH `x <= M ==> x <= max M (&0)`]];
   ALL_TAC] THEN
  (* Orthogonality: E[(X - cond_exp X) * cond_exp X] = 0 *)
  SUBGOAL_THEN
    `expectation p
      (\x:A. ((X:A->real) x - cond_exp p G X x) * cond_exp p G X x) = &0`
    (LABEL_TAC "orth") THENL
  [MATCH_MP_TAC EXPECTATION_ZERO_BOUNDED_MEASURABLE THEN
   EXISTS_TAC `G:(A->bool)->bool` THEN EXISTS_TAC `K:real` THEN
   ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   X_GEN_TAC `B:A->bool` THEN DISCH_TAC THEN
   SUBGOAL_THEN `B IN prob_events (p:A prob_space)` ASSUME_TAC THENL
   [ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
   SUBGOAL_THEN
     `(\x:A. ((X:A->real) x - cond_exp p G X x) * indicator_fn B x) =
      (\x. X x * indicator_fn B x - cond_exp p G X x * indicator_fn B x)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. (X:A->real) x * indicator_fn (B:A->bool) x`;
     `\x:A. cond_exp p G (X:A->real) x * indicator_fn (B:A->bool) x`]
     EXPECTATION_SUB) THEN
   ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
    ASM_REWRITE_TAC[ETA_AX];
    BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`;
      `X:A->real`; `B:A->bool`] COND_EXP_CONDITIONING) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Main inequality via non-negativity of squared difference *)
  MATCH_MP_TAC(REAL_ARITH `&0 <= a - b ==> b <= a`) THEN
  SUBGOAL_THEN `integrable p (\x:A. cond_exp p G (X:A->real) x pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SIMPLE THEN MATCH_MP_TAC SIMPLE_RV_SQUARE THEN
   ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\x:A. (X:A->real) x pow 2`;
    `\x:A. cond_exp p G (X:A->real) x pow 2`] EXPECTATION_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN(SUBST1_TAC o GSYM) THEN
  SUBGOAL_THEN
    `(\x:A. (X:A->real) x pow 2 - cond_exp p G X x pow 2) =
     (\x. (X x - cond_exp p G X x) pow 2 +
          &2 * (X x - cond_exp p G X x) * cond_exp p G X x)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:A` THEN
   REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `integrable p (\x:A. ((X:A->real) x - cond_exp p G X x) pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
   EXISTS_TAC `\x:A. &2 * ((X:A->real) x pow 2 +
     cond_exp p G X x pow 2)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_SQUARE THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
    [ASM_MESON_TAC[integrable];
     MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
     EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `w:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
      `&0 <= a /\ a <= b /\ &0 <= b ==> abs a <= abs b`) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN CONJ_TAC THENL
    [REWRITE_TAC[REAL_POW_2] THEN
     MATCH_MP_TAC(REAL_ARITH
       `&0 <= (x + c) * (x + c) /\ &0 <= (x - c) * (x - c)
        ==> (x - c) * (x - c) <= &2 * (x * x + c * c)`) THEN
     REWRITE_TAC[REAL_LE_SQUARE];
     MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2]]]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `integrable p (\x:A. ((X:A->real) x - cond_exp p G X x) *
      cond_exp p G X x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN
   EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
   EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[ETA_AX];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\x:A. ((X:A->real) x - cond_exp p G X x) pow 2`;
    `\x:A. &2 * ((X:A->real) x - cond_exp p G X x) * cond_exp p G X x`]
    EXPECTATION_ADD) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `&2`;
    `\x:A. ((X:A->real) x - cond_exp p G X x) * cond_exp p G X x`]
    EXPECTATION_CMUL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
  MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2]);;

(* Conditional variance definition *)
let cond_variance = new_definition
  `cond_variance (p:A prob_space) (G:(A->bool)->bool) (X:A->real) =
   cond_exp p G (\x. (X x - cond_exp p G X x) pow 2)`;;

(* Law of total variance: Var(X) = E[Var(X|G)] + Var(E[X|G]) *)
let LAW_OF_TOTAL_VARIANCE = prove
 (`!p:A prob_space G (X:A->real).
     sub_sigma_algebra p G /\ FINITE G /\
     integrable p X /\ integrable p (\x. X x pow 2)
     ==> variance p X =
         expectation p (cond_variance p G X) +
         variance p (cond_exp p G X)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simple_rv p (cond_exp p G (X:A->real))` ASSUME_TAC THENL
  [MATCH_MP_TAC COND_EXP_SIMPLE_RV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (cond_exp p G (X:A->real))` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SIMPLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x:A. cond_exp p G (X:A->real) x pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SIMPLE THEN MATCH_MP_TAC SIMPLE_RV_SQUARE THEN
   ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  (* E[cond_exp X] = E[X] by tower property *)
  SUBGOAL_THEN
    `expectation p (cond_exp p G (X:A->real)) = expectation p X`
    (LABEL_TAC "tower") THENL
  [MATCH_MP_TAC COND_EXP_TOWER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* E[Var(X|G)] = E[(X - cond_exp X)^2] by cond_exp tower *)
  SUBGOAL_THEN
    `integrable p (\x:A. ((X:A->real) x - cond_exp p G X x) pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
   EXISTS_TAC `\x:A. &2 * ((X:A->real) x pow 2 +
     cond_exp p G X x pow 2)` THEN
   SUBGOAL_THEN `measurable_wrt p G (cond_exp p G (X:A->real))` ASSUME_TAC
   THENL
   [MATCH_MP_TAC COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_SQUARE THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
    [ASM_MESON_TAC[integrable];
     MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
     EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[ETA_AX]];
    MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `w:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
      `&0 <= a /\ a <= b /\ &0 <= b ==> abs a <= abs b`) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN CONJ_TAC THENL
    [REWRITE_TAC[REAL_POW_2] THEN
     MATCH_MP_TAC(REAL_ARITH
       `&0 <= (x + c) * (x + c) /\ &0 <= (x - c) * (x - c)
        ==> (x - c) * (x - c) <= &2 * (x * x + c * c)`) THEN
     REWRITE_TAC[REAL_LE_SQUARE];
     MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2]]]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `expectation p (cond_variance p G (X:A->real)) =
     expectation p (\x. (X x - cond_exp p G X x) pow 2)`
    SUBST1_TAC THENL
  [REWRITE_TAC[cond_variance] THEN
   MATCH_MP_TAC COND_EXP_TOWER THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* E[(X - ce)^2] = E[X^2] - E[ce^2] by orthogonality *)
  SUBGOAL_THEN
    `expectation p (\x:A. ((X:A->real) x - cond_exp p G X x) pow 2) =
     expectation p (\x. X x pow 2) -
     expectation p (\x. cond_exp p G X x pow 2)`
    SUBST1_TAC THENL
  [MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`; `X:A->real`]
     COND_EXP_L2_CONTRACTION) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   (* This follows from orthogonality, same as L2 contraction proof *)
   SUBGOAL_THEN `measurable_wrt p G (cond_exp p G (X:A->real))` ASSUME_TAC
   THENL
   [MATCH_MP_TAC COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?K. &0 <= K /\ !z:A. z IN prob_carrier p
          ==> abs(cond_exp p G (X:A->real) z) <= K`
     (X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC) THENL
   [MP_TAC(SPECL [`p:A prob_space`;
      `\x:A. abs(cond_exp p G (X:A->real) x)`] SIMPLE_RV_BOUNDED) THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_ABS THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    BETA_TAC THEN DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN
    EXISTS_TAC `max M (&0)` THEN CONJ_TAC THENL
    [REAL_ARITH_TAC;
     ASM_MESON_TAC[REAL_ARITH `x <= M ==> x <= max M (&0)`]];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `expectation p
       (\x:A. ((X:A->real) x - cond_exp p G X x) * cond_exp p G X x) = &0`
     (LABEL_TAC "orth") THENL
   [MATCH_MP_TAC EXPECTATION_ZERO_BOUNDED_MEASURABLE THEN
    EXISTS_TAC `G:(A->bool)->bool` THEN EXISTS_TAC `K:real` THEN
    ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    X_GEN_TAC `B:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `B IN prob_events (p:A prob_space)` ASSUME_TAC THENL
    [ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
      `(\x:A. ((X:A->real) x - cond_exp p G X x) * indicator_fn B x) =
       (\x. X x * indicator_fn B x - cond_exp p G X x * indicator_fn B x)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. (X:A->real) x * indicator_fn (B:A->bool) x`;
      `\x:A. cond_exp p G (X:A->real) x * indicator_fn (B:A->bool) x`]
      EXPECTATION_SUB) THEN
    ANTS_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
     ASM_REWRITE_TAC[ETA_AX];
     BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
     MP_TAC(SPECL [`p:A prob_space`; `G:(A->bool)->bool`;
       `X:A->real`; `B:A->bool`] COND_EXP_CONDITIONING) THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   (* E[(X - ce)^2] = E[X^2 - 2*X*ce + ce^2] = E[X^2] - 2*E[X*ce] + E[ce^2]
      E[(X - ce)*ce] = 0 means E[X*ce] = E[ce^2]
      So E[(X - ce)^2] = E[X^2] - 2*E[ce^2] + E[ce^2] = E[X^2] - E[ce^2] *)
   SUBGOAL_THEN
     `integrable p (\x:A. ((X:A->real) x - cond_exp p G X x) *
       cond_exp p G X x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN
    EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
    EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `(\x:A. ((X:A->real) x - cond_exp p G X x) pow 2) =
      (\x. X x pow 2 - &2 * (X x - cond_exp p G X x) * cond_exp p G X x -
           cond_exp p G X x pow 2)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:A` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. (X:A->real) x pow 2 -
       &2 * (X x - cond_exp p G X x) * cond_exp p G X x`;
     `\x:A. cond_exp p G (X:A->real) x pow 2`] EXPECTATION_SUB) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[]];
    BETA_TAC THEN DISCH_THEN SUBST1_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. (X:A->real) x pow 2`;
     `\x:A. &2 * ((X:A->real) x - cond_exp p G X x) * cond_exp p G X x`]
     EXPECTATION_SUB) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    ASM_REWRITE_TAC[];
    BETA_TAC THEN DISCH_THEN SUBST1_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `&2`;
     `\x:A. ((X:A->real) x - cond_exp p G X x) * cond_exp p G X x`]
     EXPECTATION_CMUL) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Use VARIANCE_ALT: Var(Z) = E[Z^2] - (E[Z])^2, then tower + arith *)
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`] VARIANCE_ALT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `cond_exp p G (X:A->real)`]
    VARIANCE_ALT) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  USE_THEN "tower" (fun th -> REWRITE_TAC[th]) THEN
  REAL_ARITH_TAC);;


(* ================================================================== *)
(* Helper lemmas for RESCALED_INDICATOR_CONVERGENCE                    *)
(* ================================================================== *)

(* Shifting a filtration by one step preserves the filtration property *)
let SHIFTED_FILTRATION = prove
 (`!p:A prob_space FF.
     filtration p FF ==> filtration p (\n. FF(SUC n))`,
  REWRITE_TAC[filtration] THEN REPEAT STRIP_TAC THENL
  [ASM_SIMP_TAC[];
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* max of a measurable function and a constant is measurable *)
let MEASURABLE_WRT_MAX_CONST = prove
 (`!p:A prob_space G f c.
     sub_sigma_algebra p G /\ measurable_wrt p G f
     ==> measurable_wrt p G (\x. max (f x) c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[measurable_wrt] THEN
  X_GEN_TAC `v:real` THEN ASM_CASES_TAC `v < c` THENL
  [SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ max (f x) c <= v} = {}`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; REAL_MAX_LE] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ASM_MESON_TAC[sub_sigma_algebra; SIGMA_ALGEBRA_EMPTY]];
   SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ max (f x) c <= v} =
     {x | x IN prob_carrier p /\ f x <= v}`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; REAL_MAX_LE] THEN
    GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `measurable_wrt (p:A prob_space) G (f:A->real)` THEN
    REWRITE_TAC[measurable_wrt] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real`) THEN REWRITE_TAC[]]]);;

(* Inverse of a measurable function that is >= 1 on the carrier is measurable *)
let MEASURABLE_WRT_INV_GE_ONE = prove
 (`!p:A prob_space G f.
     sub_sigma_algebra p G /\ measurable_wrt p G f /\
     (!x. x IN prob_carrier p ==> &1 <= f x)
     ==> measurable_wrt p G (\x. inv(f x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[measurable_wrt] THEN
  X_GEN_TAC `v:real` THEN ASM_CASES_TAC `v <= &0` THENL
  [SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ inv(f x) <= v} = {}`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < inv((f:A->real) x)` MP_TAC THENL
    [MATCH_MP_TAC REAL_LT_INV THEN
     MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1` THEN
     CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[]];
     ASM_REAL_ARITH_TAC];
    ASM_MESON_TAC[sub_sigma_algebra; SIGMA_ALGEBRA_EMPTY]];
   SUBGOAL_THEN `&0 < v` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_CASES_TAC `&1 <= v` THENL
   [SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ inv(f x) <= v} =
      prob_carrier p`
     SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
     X_GEN_TAC `x:A` THEN EQ_TAC THENL
     [SIMP_TAC[];
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
      ASM_SIMP_TAC[]];
     ASM_MESON_TAC[SUB_SIGMA_ALGEBRA_CARRIER_IN]];
    (* 0 < v < 1: {x | inv(f x) <= v} = {x | f x >= inv v} *)
    SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ inv(f x) <= v} =
      {x | x IN prob_carrier p /\ f x >= inv v}`
     SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; real_ge] THEN
     X_GEN_TAC `x:A` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LINV THEN
      CONJ_TAC THENL
      [ASM_MESON_TAC[REAL_LTE_TRANS; REAL_LT_01];
       ASM_REWRITE_TAC[]];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LINV THEN ASM_REWRITE_TAC[]];
     MATCH_MP_TAC MEASURABLE_WRT_GE THEN ASM_REWRITE_TAC[]]]]);;

(* L1 bound from L2 bound: E[|f|] <= (E[f^2] + 1) / 2 *)
(* This uses the elementary inequality |x| <= (x^2 + 1)/2 *)
let EXPECTATION_ABS_FROM_SQUARE = prove
 (`!p:A prob_space f.
     integrable p f /\ integrable p (\x. f x pow 2)
     ==> expectation p (\x. abs(f x)) <=
         (expectation p (\x. f x pow 2) + &1) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `expectation (p:A prob_space) (\x:A. ((f:A->real) x pow 2 + &1) / &2)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC EXPECTATION_MONO THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ABS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\x:A. ((f:A->real) x pow 2 + &1) / &2) =
      (\x. inv(&2) * (f x pow 2 + &1))` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
     MATCH_MP_TAC INTEGRABLE_CMUL THEN
     MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[INTEGRABLE_CONST]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(SPEC `abs((f:A->real) x) - &1` REAL_LE_POW_2) THEN
    REWRITE_TAC[REAL_POW2_ABS] THEN REAL_ARITH_TAC];
   SUBGOAL_THEN
    `(\x:A. ((f:A->real) x pow 2 + &1) / &2) =
     (\x. inv(&2) * (f x pow 2 + &1))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `expectation (p:A prob_space) (\x. inv(&2) * ((f:A->real) x pow 2 + &1)) =
     inv(&2) * expectation p (\x. f x pow 2 + &1)` SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_CMUL THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INTEGRABLE_CONST]; ALL_TAC] THEN
   SUBGOAL_THEN
    `expectation (p:A prob_space) (\x. (f:A->real) x pow 2 + &1) =
     expectation p (\x. f x pow 2) + &1` SUBST1_TAC THENL
   [SUBGOAL_THEN
     `expectation (p:A prob_space) (\x. (f:A->real) x pow 2 + &1) =
      expectation p (\x. f x pow 2) + expectation p (\x:A. &1)`
     SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_ADD THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[INTEGRABLE_CONST];
     REWRITE_TAC[EXPECTATION_CONST]];
    REAL_ARITH_TAC]]);;

(* If f = 0 a.e. and is integrable, then E[f] = 0 *)
let EXPECTATION_AE_ZERO = prove
 (`!p:A prob_space f.
    integrable p f /\ almost_surely p {x | f x = &0}
    ==> expectation p f = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [almost_surely]) THEN
  REWRITE_TAC[null_event; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `expectation (p:A prob_space) (f:A->real) =
     expectation p (\x. f x * indicator_fn (n:A->bool) x)` SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[indicator_fn] THEN
   ASM_CASES_TAC `(f:A->real) x = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO]; ALL_TAC] THEN
   SUBGOAL_THEN `(x:A) IN n` ASSUME_TAC THENL
   [UNDISCH_TAC `{x:A | x IN prob_carrier p /\ ~(f x = &0)} SUBSET n` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[REAL_MUL_RID]];
   MATCH_MP_TAC EXPECTATION_MUL_INDICATOR_ZERO_PROB THEN
   ASM_REWRITE_TAC[]]);;

(* a.e. version of EXPECTATION_ZERO_BOUNDED_MEASURABLE:                     *)
(* E[h * phi] = 0 when phi is G-measurable and a.e. bounded                *)
let EXPECTATION_ZERO_AE_BOUNDED_MEASURABLE = prove
 (`!p:A prob_space G (h:A->real) (phi:A->real) K.
    sub_sigma_algebra p G /\ integrable p h /\
    (!B. B IN G ==> expectation p (\x. h x * indicator_fn B x) = &0) /\
    measurable_wrt p G phi /\
    integrable p (\x. h x * phi x) /\
    &0 <= K /\ almost_surely p {x | abs(phi x) <= K}
    ==> expectation p (\x. h x * phi x) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `phi_K = \x:A. max (min ((phi:A->real) x) K) (--K)` THEN
  SUBGOAL_THEN `measurable_wrt (p:A prob_space) G (phi_K:A->real)` ASSUME_TAC THENL
  [EXPAND_TAC "phi_K" THEN MATCH_MP_TAC MEASURABLE_WRT_MAX_CONST THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `(\x:A. min ((phi:A->real) x) K) = (\x. --(max (--phi x) (--K)))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC MEASURABLE_WRT_NEG THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MEASURABLE_WRT_MAX_CONST THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MEASURABLE_WRT_NEG THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> abs((phi_K:A->real) x) <= K`
    ASSUME_TAC THENL
  [EXPAND_TAC "phi_K" THEN GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC(REAL_ARITH
     `--K <= max (min (phi:real) K) (--K) /\
      max (min phi K) (--K) <= K
      ==> abs(max (min phi K) (--K)) <= K`) THEN
   CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `a <= K /\ --K <= K ==> max a (--K) <= K`) THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `expectation (p:A prob_space) (\x. (h:A->real) x * (phi_K:A->real) x) = &0`
    ASSUME_TAC THENL
  [MATCH_MP_TAC EXPECTATION_ZERO_BOUNDED_MEASURABLE THEN
   EXISTS_TAC `G:(A->bool)->bool` THEN EXISTS_TAC `K:real` THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `expectation (p:A prob_space)
       (\x. (h:A->real) x * (phi:A->real) x - h x * (phi_K:A->real) x) = &0`
    MP_TAC THENL
  [MATCH_MP_TAC EXPECTATION_AE_ZERO THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN
    EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
    EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x:A | abs((phi:A->real) x) <= K}` THEN
    CONJ_TAC THENL
    [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    REPEAT DISCH_TAC THEN EXPAND_TAC "phi_K" THEN
    UNDISCH_TAC `abs((phi:A->real) x) <= K` THEN
    REWRITE_TAC[REAL_ABS_BOUNDS] THEN STRIP_TAC THEN
    SUBGOAL_THEN `min ((phi:A->real) x) K = phi x` SUBST1_TAC THENL
    [REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `max ((phi:A->real) x) (--K) = phi x` SUBST1_TAC THENL
    [REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
     REAL_ARITH_TAC]];
   DISCH_TAC THEN
   SUBGOAL_THEN
     `expectation (p:A prob_space) (\x. (h:A->real) x * (phi:A->real) x) =
      expectation p (\x. h x * (phi_K:A->real) x) +
      expectation p (\x. h x * phi x - h x * phi_K x)` SUBST1_TAC THENL
   [SUBGOAL_THEN
     `expectation (p:A prob_space) (\x. (h:A->real) x * (phi:A->real) x) =
      expectation p (\x. h x * (phi_K:A->real) x +
                         (h x * phi x - h x * phi_K x))`
     SUBST1_TAC THENL
    [MATCH_MP_TAC EXPECTATION_EXT THEN GEN_TAC THEN DISCH_TAC THEN
     REAL_ARITH_TAC;
     MATCH_MP_TAC EXPECTATION_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN
      EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
      EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN
      EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
      EXISTS_TAC `G:(A->bool)->bool` THEN ASM_REWRITE_TAC[]]];
    ASM_REAL_ARITH_TAC]]);;

(* a.e. monotonicity of expectation *)
let EXPECTATION_MONO_AE = prove
 (`!p:A prob_space f g.
    integrable p f /\ integrable p g /\
    almost_surely p {x | f x <= g x}
    ==> expectation p f <= expectation p g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `&0 <= expectation (p:A prob_space) (\x. (g:A->real) x - (f:A->real) x)`
    MP_TAC THENL
  [ALL_TAC;
   MP_TAC(ISPECL [`p:A prob_space`; `g:A->real`; `f:A->real`] EXPECTATION_SUB) THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. (g:A->real) x - (f:A->real) x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `h = \x:A. (g:A->real) x - (f:A->real) x` THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. max (--(h:A->real) x) (&0))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MAX THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_NEG THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INTEGRABLE_CONST]]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. max ((h:A->real) x) (&0))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MAX THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[INTEGRABLE_CONST]]; ALL_TAC] THEN
  SUBGOAL_THEN
    `expectation (p:A prob_space) (h:A->real) =
     expectation p (\x. max (h x) (&0)) -
     expectation p (\x. max (--h x) (&0))`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
    `expectation (p:A prob_space) (h:A->real) =
     expectation p (\x. max (h x) (&0) - max (--h x) (&0))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_EXT THEN GEN_TAC THEN DISCH_TAC THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC EXPECTATION_SUB THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `expectation (p:A prob_space) (\x. max (--(h:A->real) x) (&0)) = &0`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_AE_ZERO THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
   EXISTS_TAC `{x:A | (f:A->real) x <= (g:A->real) x}` THEN
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   GEN_TAC THEN EXPAND_TAC "h" THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC);;

(* gen_cond_exp of indicator is in [0,1] a.e.                               *)
let COND_EXP_INDICATOR_BOUNDED_AE = prove
 (`!p FF (B:num->A->bool).
    filtration p FF /\ (!n. B n IN prob_events p) /\
    (!n. B n SUBSET prob_carrier p) /\ (!n. B n IN FF n)
    ==> !k. almost_surely p
      {x | &0 <= gen_cond_exp p (FF k) (\y. indicator_fn (B (SUC k)) y) x /\
           gen_cond_exp p (FF k) (\y. indicator_fn (B (SUC k)) y) x <= &1}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sub_sigma_algebra p ((FF:num->(A->bool)->bool) k)` ASSUME_TAC THENL
  [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\y:A. indicator_fn ((B:num->A->bool) (SUC k)) y)`
    ASSUME_TAC THENL
  [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC INTEGRABLE_INDICATOR THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC `{x:A | &0 <= gen_cond_exp p ((FF:num->(A->bool)->bool) k)
    (\y. indicator_fn (B (SUC k)) y) x} INTER
   ({x | gen_cond_exp p (FF k) (\y. indicator_fn (B (SUC k)) y) x <=
         gen_cond_exp p (FF k) (\w:A. &1) x} INTER
    {x | gen_cond_exp p (FF k) (\w. &1) x = &1})` THEN
  CONJ_TAC THENL
  [REPEAT(MATCH_MP_TAC ALMOST_SURELY_INTER THEN CONJ_TAC) THENL
   [MATCH_MP_TAC GEN_COND_EXP_NONNEG THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[indicator_fn] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC GEN_COND_EXP_MONOTONE THEN
    ASM_REWRITE_TAC[INTEGRABLE_CONST] THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[indicator_fn] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC GEN_COND_EXP_CONST THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

(* min preserves measurability *)
let MEASURABLE_WRT_MIN_CONST = prove
 (`!p G (f:A->real) c.
    sub_sigma_algebra p G /\ measurable_wrt p G f
    ==> measurable_wrt p G (\x. min (f x) c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. min ((f:A->real) x) c) =
    (\x. --(max (--f x) (--c)))` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\x:A. --(max (--(f:A->real) x) (--c))) =
    (\x. &0 - max (&0 - f x) (--c))` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_WRT_SUB THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_WRT_MAX_CONST THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_WRT_SUB THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_REWRITE_TAC[]);;

(* The rescaled martingale T_n = sum(d_k/(1+V_k)) converges a.e.           *)
(* Strategy: T' with max(1+V_k,1) denominator is a martingale with         *)
(* bounded L1 norm; apply SUBMARTINGALE_CONVERGENCE_L1_BOUNDED. Since       *)
(* v_k >= 0 a.e., max(1+V_k,1) = 1+V_k a.e., so T' = T a.e.              *)

(* Martingale difference d_k = f - E[f|G] is orthogonal to G              *)
let MARTINGALE_DIFF_ORTHOGONAL = prove
 (`!p:A prob_space G f.
    sub_sigma_algebra p G /\ integrable p f
    ==> !A. A IN G ==>
      expectation p (\x. (f x - gen_cond_exp p G f x) *
        indicator_fn A x) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(A:A->bool) IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[SUB_SIGMA_ALGEBRA_IN_EVENTS]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (gen_cond_exp p G (f:A->real))`
  ASSUME_TAC THENL
  [MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:A. ((f:A->real) x - gen_cond_exp p G f x) * indicator_fn A x) =
    (\x. f x * indicator_fn A x -
         gen_cond_exp p G f x * indicator_fn A x)`
   SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `expectation (p:A prob_space) (\x. (f:A->real) x * indicator_fn A x -
      gen_cond_exp p G f x * indicator_fn A x) =
    expectation p (\x. f x * indicator_fn A x) -
    expectation p (\x. gen_cond_exp p G f x * indicator_fn A x)`
   SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_SUB THEN CONJ_TAC THEN
   MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
   ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
    `f:A->real`; `A:A->bool`] GEN_COND_EXP_CONDITIONING) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Helper: T' is a martingale w.r.t. shifted filtration                    *)
let RESCALED_MAX_MARTINGALE = prove
 (`!p FF (B:num->A->bool).
     filtration p FF /\ (!n. B n IN prob_events p) /\
     (!n. B n SUBSET prob_carrier p) /\ (!n. B n IN FF n)
     ==> martingale p (\n. FF(SUC n))
       (\n x. sum(0..n)
         (\k. (indicator_fn (B (SUC k)) x -
               gen_cond_exp p (FF k)
                 (\y. indicator_fn (B (SUC k)) y) x) /
              max (&1 + sum(0..k)
                (\j. gen_cond_exp p (FF j)
                  (\y. indicator_fn (B (SUC j)) y) x)) (&1)))`,
  REWRITE_TAC[martingale] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Establish useful facts *)
  SUBGOAL_THEN `!k. sub_sigma_algebra p ((FF:num->(A->bool)->bool) k)`
  ASSUME_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
  SUBGOAL_THEN `!k:num. integrable p (indicator_fn ((B:num->A->bool) (SUC k)))`
  ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. measurable_wrt p ((FF:num->(A->bool)->bool) k)
     (gen_cond_exp p (FF k) (indicator_fn ((B:num->A->bool) (SUC k))))`
  ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC GEN_COND_EXP_MEASURABLE_WRT THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. integrable p
     (gen_cond_exp p ((FF:num->(A->bool)->bool) k)
       (indicator_fn ((B:num->A->bool) (SUC k))))`
  ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [(* 1. Shifted filtration *)
   MATCH_MP_TAC SHIFTED_FILTRATION THEN ASM_REWRITE_TAC[];
   (* 2. Adapted: T'_n is FF(SUC n)-measurable *)
   REWRITE_TAC[adapted] THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC MEASURABLE_WRT_SUM THEN
   CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
   X_GEN_TAC `k:num` THEN DISCH_TAC THEN
   REWRITE_TAC[real_div] THEN
   MATCH_MP_TAC MEASURABLE_WRT_MUL THEN
   CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_WRT_SUB THEN
    CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
    CONJ_TAC THENL
    [REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
     EXISTS_TAC `(FF:num->(A->bool)->bool) (SUC k)` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_WRT_INDICATOR THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [filtration]) THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
     REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
     EXISTS_TAC `(FF:num->(A->bool)->bool) k` THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [filtration]) THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    MATCH_MP_TAC MEASURABLE_WRT_INV_GE_ONE THEN
    CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC MEASURABLE_WRT_MAX_CONST THEN
     CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
     MATCH_MP_TAC MEASURABLE_WRT_ADD THEN
     CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MEASURABLE_WRT_SUM THEN
      CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
      EXISTS_TAC `(FF:num->(A->bool)->bool) j` THEN
      CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [filtration]) THEN
       STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN REAL_ARITH_TAC]];
   (* 3. Integrable *)
   X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC INTEGRABLE_SUM THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
   REWRITE_TAC[real_div] THEN
   MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN EXISTS_TAC `&1` THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUB THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
    EXISTS_TAC `(FF:num->(A->bool)->bool) (SUC n)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
    REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC MEASURABLE_WRT_INV_GE_ONE THEN
    CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC MEASURABLE_WRT_MAX_CONST THEN
     CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
     MATCH_MP_TAC MEASURABLE_WRT_ADD THEN
     CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MEASURABLE_WRT_SUM THEN
      CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
      EXISTS_TAC `(FF:num->(A->bool)->bool) j` THEN
      CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [filtration]) THEN
       STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN REAL_ARITH_TAC];
    REAL_ARITH_TAC;
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_INV] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_INV2 THEN
     CONJ_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[real_abs] THEN
     REAL_ARITH_TAC];
     REWRITE_TAC[REAL_INV_1] THEN REAL_ARITH_TAC]];
   (* 4. Increment property: E[T'(SUC n)*1_a] = E[T'(n)*1_a] *)
   X_GEN_TAC `n:num` THEN X_GEN_TAC `a:A->bool` THEN DISCH_TAC THEN
   SUBGOAL_THEN `(a:A->bool) IN prob_events p` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUB_SIGMA_ALGEBRA_IN_EVENTS; filtration]; ALL_TAC] THEN
   (* Rewrite sum(0..SUC n) as sum(0..n) + last term *)
   REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
   REWRITE_TAC[ETA_AX] THEN
   (* Distribute multiplication over addition *)
   SUBGOAL_THEN
    `!x:A. (sum (0..n)
       (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
             gen_cond_exp p (FF k) (indicator_fn (B (SUC k))) x) /
            max (&1 + sum (0..k)
              (\j. gen_cond_exp p (FF j) (indicator_fn (B (SUC j))) x))
            (&1)) +
      (indicator_fn (B (SUC (SUC n))) x -
       gen_cond_exp p (FF (SUC n)) (indicator_fn (B (SUC (SUC n)))) x) /
      max (&1 + sum (0..n)
        (\j. gen_cond_exp p (FF j) (indicator_fn (B (SUC j))) x) +
        gen_cond_exp p (FF (SUC n)) (indicator_fn (B (SUC (SUC n)))) x)
      (&1)) * indicator_fn a x =
     sum (0..n)
       (\k. (indicator_fn (B (SUC k)) x -
             gen_cond_exp p (FF k) (indicator_fn (B (SUC k))) x) /
            max (&1 + sum (0..k)
              (\j. gen_cond_exp p (FF j) (indicator_fn (B (SUC j))) x))
            (&1)) * indicator_fn a x +
     (indicator_fn (B (SUC (SUC n))) x -
       gen_cond_exp p (FF (SUC n)) (indicator_fn (B (SUC (SUC n)))) x) /
      max (&1 + sum (0..n)
        (\j. gen_cond_exp p (FF j) (indicator_fn (B (SUC j))) x) +
        gen_cond_exp p (FF (SUC n)) (indicator_fn (B (SUC (SUC n)))) x)
      (&1) * indicator_fn a x`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   (* d_{SUC n} is integrable *)
   SUBGOAL_THEN
    `integrable p (\x:A. indicator_fn ((B:num->A->bool) (SUC (SUC n))) x -
       gen_cond_exp p (FF (SUC n)) (indicator_fn (B (SUC (SUC n)))) x)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUB THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* E[inc * 1_a] = 0 via EXPECTATION_ZERO_BOUNDED_MEASURABLE *)
   SUBGOAL_THEN
    `expectation p (\x:A.
       (indicator_fn ((B:num->A->bool) (SUC (SUC n))) x -
        gen_cond_exp p (FF (SUC n)) (indicator_fn (B (SUC (SUC n)))) x) /
       max (&1 + sum (0..n)
         (\j. gen_cond_exp p (FF j) (indicator_fn (B (SUC j))) x) +
         gen_cond_exp p (FF (SUC n)) (indicator_fn (B (SUC (SUC n)))) x)
       (&1) * indicator_fn a x) = &0`
   ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MP_TAC(ISPECL
     [`p:A prob_space`;
      `(FF:num->(A->bool)->bool) (SUC n)`;
      `\x:A. indicator_fn ((B:num->A->bool) (SUC (SUC n))) x -
         gen_cond_exp p ((FF:num->(A->bool)->bool) (SUC n))
           (indicator_fn (B (SUC (SUC n)))) x`;
      `\x:A. inv(max (&1 + sum (0..n)
         (\j. gen_cond_exp p ((FF:num->(A->bool)->bool) j)
           (indicator_fn ((B:num->A->bool) (SUC j))) x) +
         gen_cond_exp p (FF (SUC n)) (indicator_fn (B (SUC (SUC n)))) x)
        (&1)) * indicator_fn (a:A->bool) x`;
      `&1`]
     EXPECTATION_ZERO_BOUNDED_MEASURABLE) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
     [(* sub_sigma_algebra p (FF (SUC n)) *)
      ASM_MESON_TAC[filtration];
      (* integrable p d *)
      ASM_REWRITE_TAC[];
      (* E[d * 1_B'] = 0 for B' in FF(SUC n) *)
      X_GEN_TAC `B':A->bool` THEN DISCH_TAC THEN
      MP_TAC(ISPECL
       [`p:A prob_space`;
        `(FF:num->(A->bool)->bool) (SUC n)`;
        `indicator_fn ((B:num->A->bool) (SUC (SUC n)))`]
       MARTINGALE_DIFF_ORTHOGONAL) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `B':A->bool`) THEN
      ASM_REWRITE_TAC[];
      (* measurable_wrt phi *)
      MATCH_MP_TAC MEASURABLE_WRT_MUL THEN
      CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC MEASURABLE_WRT_INV_GE_ONE THEN
       CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_WRT_MAX_CONST THEN
        CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
        MATCH_MP_TAC MEASURABLE_WRT_ADD THEN
        CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_REWRITE_TAC[];
         MATCH_MP_TAC MEASURABLE_WRT_ADD THEN
         CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
         CONJ_TAC THENL
         [MATCH_MP_TAC MEASURABLE_WRT_SUM THEN
          CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
          X_GEN_TAC `j:num` THEN DISCH_TAC THEN
          REWRITE_TAC[ETA_AX] THEN
          MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
          EXISTS_TAC `(FF:num->(A->bool)->bool) j` THEN
          CONJ_TAC THENL
          [ASM_REWRITE_TAC[];
           FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [filtration]) THEN
           STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
          REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]]];
        X_GEN_TAC `x:A` THEN DISCH_TAC THEN REAL_ARITH_TAC];
       REWRITE_TAC[ETA_AX] THEN
       MATCH_MP_TAC MEASURABLE_WRT_INDICATOR THEN ASM_REWRITE_TAC[]];
      (* &0 <= K *)
      REAL_ARITH_TAC;
      (* |phi| <= 1 *)
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &1` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
       CONJ_TAC THENL
       [REWRITE_TAC[REAL_ABS_INV] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1)` THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LE_INV2 THEN
         CONJ_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[real_abs] THEN
         REAL_ARITH_TAC];
         REWRITE_TAC[REAL_INV_1] THEN REAL_ARITH_TAC];
        REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN REAL_ARITH_TAC];
       REAL_ARITH_TAC]];
    REWRITE_TAC[]];
   ALL_TAC] THEN
   (* Integrability of sum * 1_a *)
   SUBGOAL_THEN
    `integrable p (\x:A.
       sum (0..n)
         (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
               gen_cond_exp p (FF k) (indicator_fn (B (SUC k))) x) /
              max (&1 + sum (0..k)
                (\j. gen_cond_exp p (FF j) (indicator_fn (B (SUC j))) x))
              (&1)) * indicator_fn a x)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN EXISTS_TAC `&1` THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_SUM THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
     REWRITE_TAC[real_div] THEN
     MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN EXISTS_TAC `&1` THEN
     REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SUB THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
      EXISTS_TAC `(FF:num->(A->bool)->bool) (SUC n)` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
      REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC MEASURABLE_WRT_INV_GE_ONE THEN
      CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC MEASURABLE_WRT_MAX_CONST THEN
       CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
       MATCH_MP_TAC MEASURABLE_WRT_ADD THEN
       CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC MEASURABLE_WRT_SUM THEN
        CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
        X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
        EXISTS_TAC `(FF:num->(A->bool)->bool) j` THEN
        CONJ_TAC THENL
        [ASM_REWRITE_TAC[];
         FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [filtration]) THEN
         STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
       X_GEN_TAC `x:A` THEN DISCH_TAC THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC;
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_ABS_INV] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1)` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_INV2 THEN
       CONJ_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[real_abs] THEN
       REAL_ARITH_TAC];
       REWRITE_TAC[REAL_INV_1] THEN REAL_ARITH_TAC]];
     REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
     REAL_ARITH_TAC;
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   (* Integrability of inc * 1_a *)
   SUBGOAL_THEN
    `integrable p (\x:A.
       (indicator_fn ((B:num->A->bool) (SUC (SUC n))) x -
        gen_cond_exp p (FF (SUC n)) (indicator_fn (B (SUC (SUC n)))) x) /
       max (&1 + sum (0..n)
         (\j. gen_cond_exp p (FF j) (indicator_fn (B (SUC j))) x) +
         gen_cond_exp p (FF (SUC n)) (indicator_fn (B (SUC (SUC n)))) x)
       (&1) * indicator_fn a x)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN EXISTS_TAC `&1` THEN
    REPEAT CONJ_TAC THENL
    [REWRITE_TAC[real_div] THEN
     MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN EXISTS_TAC `&1` THEN
     REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
      EXISTS_TAC `(FF:num->(A->bool)->bool) (SUC n)` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
      MATCH_MP_TAC MEASURABLE_WRT_INV_GE_ONE THEN
      CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC MEASURABLE_WRT_MAX_CONST THEN
       CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
       MATCH_MP_TAC MEASURABLE_WRT_ADD THEN
       CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC MEASURABLE_WRT_ADD THEN
        CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC MEASURABLE_WRT_SUM THEN
         CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
         X_GEN_TAC `j:num` THEN DISCH_TAC THEN
         REWRITE_TAC[ETA_AX] THEN
         MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
         EXISTS_TAC `(FF:num->(A->bool)->bool) j` THEN
         CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [filtration]) THEN
          STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
         REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]]];
       X_GEN_TAC `x:A` THEN DISCH_TAC THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC;
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_ABS_INV] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1)` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_INV2 THEN
       CONJ_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[real_abs] THEN
       REAL_ARITH_TAC];
       REWRITE_TAC[REAL_INV_1] THEN REAL_ARITH_TAC]];
     REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
     REAL_ARITH_TAC;
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   (* Combine: E[f + g] = E[f] + E[g] = E[f] + 0 = E[f] *)
   SUBGOAL_THEN
    `expectation (p:A prob_space)
      (\x. sum (0..n)
        (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
              gen_cond_exp p (FF k) (indicator_fn (B (SUC k))) x) /
             max (&1 + sum (0..k)
               (\j. gen_cond_exp p (FF j) (indicator_fn (B (SUC j))) x))
             (&1)) * indicator_fn a x +
       (indicator_fn (B (SUC (SUC n))) x -
        gen_cond_exp p (FF (SUC n)) (indicator_fn (B (SUC (SUC n)))) x) /
       max (&1 + sum (0..n)
         (\j. gen_cond_exp p (FF j) (indicator_fn (B (SUC j))) x) +
         gen_cond_exp p (FF (SUC n)) (indicator_fn (B (SUC (SUC n)))) x)
       (&1) * indicator_fn a x) =
     expectation p
      (\x. sum (0..n)
        (\k. (indicator_fn (B (SUC k)) x -
              gen_cond_exp p (FF k) (indicator_fn (B (SUC k))) x) /
             max (&1 + sum (0..k)
               (\j. gen_cond_exp p (FF j) (indicator_fn (B (SUC j))) x))
             (&1)) * indicator_fn a x) +
     expectation p
      (\x. (indicator_fn (B (SUC (SUC n))) x -
        gen_cond_exp p (FF (SUC n)) (indicator_fn (B (SUC (SUC n)))) x) /
       max (&1 + sum (0..n)
         (\j. gen_cond_exp p (FF j) (indicator_fn (B (SUC j))) x) +
         gen_cond_exp p (FF (SUC n)) (indicator_fn (B (SUC (SUC n)))) x)
       (&1) * indicator_fn a x)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Truncated martingale difference has zero expectation against bounded     *)
(* measurable functions                                                     *)
let TRUNCATED_DIFF_EXPECTATION_ZERO = prove
 (`!p FF (B:num->A->bool) k phi K.
    filtration p FF /\ (!n. B n IN prob_events p) /\
    (!n. B n SUBSET prob_carrier p) /\ (!n. B n IN FF n) /\
    integrable p phi /\
    measurable_wrt p (FF k) phi /\
    &0 <= K /\
    (!x. x IN prob_carrier p ==> abs(phi x) <= K)
    ==> expectation p
      (\x. (indicator_fn (B (SUC k)) x -
            max (min (gen_cond_exp p (FF k)
              (\y. indicator_fn (B (SUC k)) y) x) (&1)) (&0)) *
           phi x) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `v = gen_cond_exp p ((FF:num->(A->bool)->bool) k)
    (\y. indicator_fn ((B:num->A->bool) (SUC k)) y)` THEN
  SUBGOAL_THEN `sub_sigma_algebra p ((FF:num->(A->bool)->bool) k)` ASSUME_TAC THENL
  [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\y:A. indicator_fn ((B:num->A->bool) (SUC k)) y)`
    ASSUME_TAC THENL
  [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC INTEGRABLE_INDICATOR THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EXPECTATION_ZERO_BOUNDED_MEASURABLE THEN
  EXISTS_TAC `(FF:num->(A->bool)->bool) k` THEN
  EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [(* Integrability of h = 1_B - max(min(v,1),0) *)
   MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC INTEGRABLE_INDICATOR THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
    EXISTS_TAC `(FF:num->(A->bool)->bool) k` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURABLE_WRT_MAX_CONST THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURABLE_WRT_MIN_CONST THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[GEN_COND_EXP_MEASURABLE_WRT];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* E[h * 1_A] = 0 for A in FF k *)
  X_GEN_TAC `A:A->bool` THEN DISCH_TAC THEN
  (* Split: h = (1_B - v) + (v - max(min(v,1),0)) *)
  SUBGOAL_THEN
   `(\x:A. (indicator_fn ((B:num->A->bool) (SUC k)) x -
     max (min (v x) (&1)) (&0)) * indicator_fn (A:A->bool) x) =
    (\x. (indicator_fn (B (SUC k)) x - v x) * indicator_fn A x +
         (v x - max (min (v x) (&1)) (&0)) * indicator_fn A x)`
   (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(A:A->bool) IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[SUB_SIGMA_ALGEBRA_IN_EVENTS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `expectation p
     (\x:A. (indicator_fn ((B:num->A->bool) (SUC k)) x - v x) *
       indicator_fn (A:A->bool) x +
       (v x - max (min (v x) (&1)) (&0)) * indicator_fn A x) =
    expectation p (\x. (indicator_fn (B (SUC k)) x - v x) *
      indicator_fn A x) +
    expectation p (\x. (v x - max (min (v x) (&1)) (&0)) *
      indicator_fn A x)`
   SUBST1_TAC THENL
  [MATCH_MP_TAC EXPECTATION_ADD THEN CONJ_TAC THEN
   MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
   ASM_REWRITE_TAC[ETA_AX] THENL
   [MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
    [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC INTEGRABLE_INDICATOR THEN
     ASM_REWRITE_TAC[];
     EXPAND_TAC "v" THEN MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN
     ASM_REWRITE_TAC[]];
    MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
    [EXPAND_TAC "v" THEN MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN
     ASM_REWRITE_TAC[];
     MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
      EXISTS_TAC `(FF:num->(A->bool)->bool) k` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MEASURABLE_WRT_MAX_CONST THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MEASURABLE_WRT_MIN_CONST THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[GEN_COND_EXP_MEASURABLE_WRT];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN REAL_ARITH_TAC]]];
   ALL_TAC] THEN
  (* First term: E[(1_B - v) * 1_A] = 0 by MARTINGALE_DIFF_ORTHOGONAL *)
  SUBGOAL_THEN
   `expectation p (\x:A. (indicator_fn ((B:num->A->bool) (SUC k)) x - v x) *
     indicator_fn (A:A->bool) x) = &0` SUBST1_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `(FF:num->(A->bool)->bool) k`;
     `\y:A. indicator_fn ((B:num->A->bool) (SUC k)) y`]
     MARTINGALE_DIFF_ORTHOGONAL) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPEC `A:A->bool`) THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
   AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
   X_GEN_TAC `x:A` THEN EXPAND_TAC "v" THEN REFL_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LID] THEN
  (* Second term: E[(v - max(min(v,1),0)) * 1_A] = 0 since v = v' a.e. *)
  MATCH_MP_TAC EXPECTATION_AE_ZERO THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[ETA_AX] THEN
   MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
   [EXPAND_TAC "v" THEN MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
     EXISTS_TAC `(FF:num->(A->bool)->bool) k` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC MEASURABLE_WRT_MAX_CONST THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC MEASURABLE_WRT_MIN_CONST THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[GEN_COND_EXP_MEASURABLE_WRT];
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* v = max(min(v,1),0) a.e. by COND_EXP_INDICATOR_BOUNDED_AE *)
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC `{x:A | &0 <= v x /\ v x <= &1}` THEN
  CONJ_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
     `B:num->A->bool`] COND_EXP_INDICATOR_BOUNDED_AE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
   ASM_REWRITE_TAC[];
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
   STRIP_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `max (min (v (x:A)) (&1)) (&0) = v x` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ x <= &1 ==> max (min x (&1)) (&0) = x`) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO]]);;

(* E[(1_B - v')^2 * phi] <= E[v' * phi] for non-negative F_k-meas phi     *)
let TRUNCATED_DIFF_SQ_BOUND = prove
 (`!p FF (B:num->A->bool) k phi (K:real).
     filtration p FF /\ (!n. B n IN prob_events p) /\
     (!n. B n SUBSET prob_carrier p) /\ (!n. B n IN FF n) /\
     integrable p phi /\ measurable_wrt p (FF k) phi /\
     &0 <= K /\ (!x:A. x IN prob_carrier p ==> abs(phi x) <= K) /\
     (!x:A. x IN prob_carrier p ==> &0 <= phi x)
     ==> expectation p
       (\x. (indicator_fn (B (SUC k)) x -
             max (min (gen_cond_exp p (FF k)
               (\y. indicator_fn (B (SUC k)) y) x) (&1)) (&0)) pow 2 *
             phi x) <=
     expectation p
       (\x. max (min (gen_cond_exp p (FF k)
               (\y. indicator_fn (B (SUC k)) y) x) (&1)) (&0) *
             phi x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `v' = \x:A. max (min (gen_cond_exp p ((FF:num->(A->bool)->bool) k)
    (\y. indicator_fn ((B:num->A->bool) (SUC k)) y) x) (&1)) (&0)` THEN
  SUBGOAL_THEN `!x:A. max (min (gen_cond_exp p ((FF:num->(A->bool)->bool) k)
    (\y. indicator_fn ((B:num->A->bool) (SUC k)) y) x) (&1)) (&0) =
    (v':A->real) x` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x:A. &0 <= (v':A->real) x /\ v' x <= &1` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "v'" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sub_sigma_algebra p ((FF:num->(A->bool)->bool) k)` ASSUME_TAC
    THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
  SUBGOAL_THEN `random_variable p (v':A->real)` ASSUME_TAC THENL
  [SUBGOAL_THEN `(v':A->real) =
    (\x. max (min (gen_cond_exp p ((FF:num->(A->bool)->bool) k)
      (\y. indicator_fn ((B:num->A->bool) (SUC k)) y) x) (&1)) (&0))`
      SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN CONJ_TAC THENL
    [REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[RANDOM_VARIABLE_CONST]];
    REWRITE_TAC[RANDOM_VARIABLE_CONST]]; ALL_TAC] THEN
  SUBGOAL_THEN `measurable_wrt p ((FF:num->(A->bool)->bool) k) (v':A->real)`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `(v':A->real) =
    (\x. max (min (gen_cond_exp p ((FF:num->(A->bool)->bool) k)
      (\y. indicator_fn ((B:num->A->bool) (SUC k)) y) x) (&1)) (&0))`
      SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC MEASURABLE_WRT_MAX_CONST THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MEASURABLE_WRT_MIN_CONST THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[ETA_AX] THEN
   MATCH_MP_TAC GEN_COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Algebraic identity: (1_B-v')^2*phi = (1_B-v')*(1-2v')*phi + v'*(1-v')*phi *)
  SUBGOAL_THEN `!x:A. (indicator_fn ((B:num->A->bool) (SUC k)) x -
    (v':A->real) x) pow 2 * phi x =
    (indicator_fn (B (SUC k)) x - v' x) * (&1 - &2 * v' x) * phi x +
    v' x * (&1 - v' x) * phi x`
    (fun th -> REWRITE_TAC[th]) THENL
  [X_GEN_TAC `x:A` THEN
   REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* By TRUNCATED_DIFF: E[(1_B-v')*(1-2v')*phi] = 0 *)
  SUBGOAL_THEN `expectation p (\x:A. (indicator_fn ((B:num->A->bool) (SUC k)) x -
    (v':A->real) x) * (&1 - &2 * v' x) * (phi:A->real) x) = &0`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
    `B:num->A->bool`; `k:num`;
    `\x:A. (&1 - &2 * (v':A->real) x) * (phi:A->real) x`;
    `K:real`] TRUNCATED_DIFF_EXPECTATION_ZERO) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN
    EXISTS_TAC `K:real` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
      [REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN
      MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= v /\ v <= &1 ==> abs(&1 - &2 * v) <= &1`) THEN
      ASM_MESON_TAC[]];
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MEASURABLE_WRT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURABLE_WRT_SUB THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    MATCH_MP_TAC MEASURABLE_WRT_CMUL THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * K` THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= v /\ v <= &1 ==> abs(&1 - &2 * v) <= &1`) THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
     ASM_REAL_ARITH_TAC]]; ALL_TAC] THEN
  (* Integrability of both parts *)
  SUBGOAL_THEN `integrable p (\x:A. (indicator_fn ((B:num->A->bool) (SUC k)) x -
    (v':A->real) x) * (&1 - &2 * v' x) * (phi:A->real) x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `K:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
      MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
     MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
      [REWRITE_TAC[RANDOM_VARIABLE_CONST];
       MATCH_MP_TAC RANDOM_VARIABLE_CMUL THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[]]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs((indicator_fn ((B:num->A->bool) (SUC k)) (x:A) -
      (v':A->real) x) * (&1 - &2 * v' x) * (phi:A->real) x)` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(indicator_fn ((B:num->A->bool) (SUC k)) (x:A) -
      (v':A->real) x) * abs(&1 - &2 * v' x) <= &1` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
      [REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= v /\ v <= &1 ==> abs(&1 - v) <= &1`) THEN
        ASM_MESON_TAC[];
        MATCH_MP_TAC(REAL_ARITH `&0 <= v /\ v <= &1 ==> abs(&0 - v) <= &1`) THEN
        ASM_MESON_TAC[]];
       MATCH_MP_TAC(REAL_ARITH `&0 <= v /\ v <= &1 ==> abs(&1 - &2 * v) <= &1`) THEN
       ASM_MESON_TAC[]];
      REAL_ARITH_TAC]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * K` THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS];
      ASM_MESON_TAC[]];
     ASM_REAL_ARITH_TAC]]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x:A. (v':A->real) x * (&1 - v' x) *
    (phi:A->real) x)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `K:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
      [REWRITE_TAC[RANDOM_VARIABLE_CONST];
       ASM_REWRITE_TAC[]];
      MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[]]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs((v':A->real) x * (&1 - v' x) * (phi:A->real) x)` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs((v':A->real) x) * abs(&1 - v' x) <= &1` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
      [MATCH_MP_TAC(REAL_ARITH `&0 <= v /\ v <= &1 ==> abs v <= &1`) THEN
       ASM_MESON_TAC[];
       MATCH_MP_TAC(REAL_ARITH `&0 <= v /\ v <= &1 ==> abs(&1 - v) <= &1`) THEN
       ASM_MESON_TAC[]];
      REAL_ARITH_TAC]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * K` THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS];
      ASM_MESON_TAC[]];
     ASM_REAL_ARITH_TAC]]; ALL_TAC] THEN
  (* Use EXPECTATION_ADD to split *)
  MP_TAC(ISPECL [`p:A prob_space`;
    `\x:A. (indicator_fn ((B:num->A->bool) (SUC k)) x - (v':A->real) x) *
      (&1 - &2 * v' x) * (phi:A->real) x`;
    `\x:A. (v':A->real) x * (&1 - v' x) * (phi:A->real) x`]
    EXPECTATION_ADD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[REAL_ADD_LID] THEN
  (* Now: E[v'*(1-v')*phi] <= E[v'*phi] *)
  MATCH_MP_TAC EXPECTATION_MONO THEN CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN
    EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN
     ASM_REWRITE_TAC[] THEN
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= v /\ v <= &1 ==> abs(v) <= &1`) THEN
     ASM_MESON_TAC[];
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `&0 <= (v':A->real) x /\ v' x <= &1` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (phi:A->real) x` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]]);;

(* Division by a positive random variable preserves measurability           *)
let RANDOM_VARIABLE_DIV_POS = prove
 (`!p (f:A->real) g. random_variable p f /\ random_variable p g /\
   (!x:A. x IN prob_carrier p ==> &0 < g x) ==>
   random_variable p (\x. f x / g x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[random_variable] THEN X_GEN_TAC `a:real` THEN
  ASM_CASES_TAC `a <= &0` THENL
  [SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ inv(g x) <= a} =
    {x | x IN prob_carrier p /\ (g:A->real) x <= &0}`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    EQ_TAC THEN STRIP_TAC THENL
    [SUBGOAL_THEN `&0 < inv((g:A->real) x)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV]; ASM_REAL_ARITH_TAC];
     SUBGOAL_THEN `&0 < (g:A->real) x` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [random_variable]) THEN
    DISCH_THEN(MP_TAC o SPEC `&0`) THEN REWRITE_TAC[]];
   SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ inv(g x) <= a} =
    {x | x IN prob_carrier p /\ (g:A->real) x >= inv a}`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < (g:A->real) x` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[real_ge] THEN
    EQ_TAC THEN STRIP_TAC THENL
    [MP_TAC(SPECL [`inv((g:A->real) x)`; `a:real`] REAL_LE_INV2) THEN
     ASM_SIMP_TAC[REAL_LT_INV; REAL_INV_INV];
     MP_TAC(SPECL [`inv(a:real)`; `(g:A->real) x`] REAL_LE_INV2) THEN
     ASM_SIMP_TAC[REAL_LT_INV; REAL_INV_INV]];
    MP_TAC(ISPECL [`p:A prob_space`; `g:A->real`; `inv(a:real)`]
     RV_PREIMAGE_GE) THEN
    ASM_REWRITE_TAC[]]]);;

let REAL_DIV_ABS_LE_1 = prove(
  `!a b. abs a <= &1 /\ &1 <= b ==> abs a / abs b <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < abs b` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

let REAL_ABS_DIV_LE = prove(
  `abs s <= t /\ &1 <= abs d ==> abs s / abs d <= t`,
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < abs d` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `t * &1` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[REAL_MUL_RID] THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC REAL_LE_LMUL THEN
   ASM_REAL_ARITH_TAC]);;

(* E[(f+g)^2] = E[f^2] + E[g^2] when E[f*g] = 0                           *)
let EXPECTATION_SQ_ORTHOGONAL = prove
 (`!p (f:A->real) g.
    integrable p f /\ integrable p g /\
    integrable p (\x. f x pow 2) /\ integrable p (\x. g x pow 2) /\
    integrable p (\x. f x * g x) /\
    expectation p (\x. f x * g x) = &0
    ==> expectation p (\x. (f x + g x) pow 2) =
        expectation p (\x. f x pow 2) + expectation p (\x. g x pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. ((f:A->real) x + g x) pow 2) =
    (\x. f x pow 2 + g x pow 2 + &2 * f x * g x)` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x:A. (f:A->real) x pow 2 + g x pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x:A. &2 * (f:A->real) x * g x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\x:A. (f:A->real) x pow 2`;
    `\x:A. (g:A->real) x pow 2 + &2 * f x * g x`] EXPECTATION_ADD) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\x:A. (g:A->real) x pow 2`;
    `\x:A. &2 * (f:A->real) x * g x`] EXPECTATION_ADD) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `&2`;
    `\x:A. (f:A->real) x * (g:A->real) x`] EXPECTATION_CMUL) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* L2 bound for truncated rescaled sum: E[T''^2] <= 1                      *)
(* Uses cross term orthogonality + diagonal bound + telescoping             *)
let RESCALED_TRUNCATED_L2 = prove
 (`!p FF (B:num->A->bool).
     filtration p FF /\ (!n. B n IN prob_events p) /\
     (!n. B n SUBSET prob_carrier p) /\ (!n. B n IN FF n)
     ==> !n. expectation p
       (\x. (sum(0..n)
         (\k. (indicator_fn (B (SUC k)) x -
               max (min (gen_cond_exp p (FF k)
                 (\y. indicator_fn (B (SUC k)) y) x) (&1)) (&0)) /
              (&1 + sum(0..k)
                (\j. max (min (gen_cond_exp p (FF j)
                  (\y. indicator_fn (B (SUC j)) y) x) (&1)) (&0))))) pow 2)
       <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `v = \k x:A. gen_cond_exp p (FF k)
    (\y. indicator_fn (B (SUC k)) y) x` THEN
  SUBGOAL_THEN `!k (x:A). gen_cond_exp p (FF k)
    (\y. indicator_fn (B (SUC k)) y) x = (v:num->A->real) k x`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `v' = \k (x:A). max (min ((v:num->A->real) k x) (&1)) (&0)` THEN
  SUBGOAL_THEN `!k (x:A). max (min ((v:num->A->real) k x) (&1)) (&0) =
    (v':num->A->real) k x` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!k (x:A). &0 <= (v':num->A->real) k x /\ v' k x <= &1`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN EXPAND_TAC "v'" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!n. sub_sigma_algebra p ((FF:num->(A->bool)->bool) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. integrable p (\y:A. indicator_fn
    ((B:num->A->bool) (SUC k)) y)` ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[ETA_AX] THEN
   MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!k:num. random_variable p ((v':num->A->real) k)` ASSUME_TAC
    THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `(v':num->A->real) k =
     (\x. max (min ((v:num->A->real) k x) (&1)) (&0))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN CONJ_TAC THENL
    [SUBGOAL_THEN `(\x:A. (v:num->A->real) k x) =
      gen_cond_exp p ((FF:num->(A->bool)->bool) k)
        (\y. indicator_fn ((B:num->A->bool) (SUC k)) y)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
     MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[RANDOM_VARIABLE_CONST]];
    REWRITE_TAC[RANDOM_VARIABLE_CONST]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!k:num. measurable_wrt p ((FF:num->(A->bool)->bool) k)
    ((v':num->A->real) k)` ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `(v':num->A->real) k =
     (\x. max (min ((v:num->A->real) k x) (&1)) (&0))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC MEASURABLE_WRT_MAX_CONST THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MEASURABLE_WRT_MIN_CONST THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `(\x:A. (v:num->A->real) k x) =
     gen_cond_exp p ((FF:num->(A->bool)->bool) k)
       (\y. indicator_fn ((B:num->A->bool) (SUC k)) y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC GEN_COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Stronger invariant: E[S_n^2] <= E[sum v'_k/(1+V'_k)^2] *)
  SUBGOAL_THEN `!n:num. expectation p
    (\x:A. (sum (0..n) (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
      (v':num->A->real) k x) /
      (&1 + sum (0..k) (\j. v' j x)))) pow 2) <=
    expectation p
      (\x. sum (0..n) (\k. v' k x /
        (&1 + sum (0..k) (\j. v' j x)) pow 2))`
    ASSUME_TAC THENL
  [INDUCT_TAC THENL
   [(* Base case: n = 0 *)
    REWRITE_TAC[SUM_SING_NUMSEG; REAL_POW_DIV; real_div;
                REAL_POW_MUL; REAL_POW_INV] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
      `B:num->A->bool`; `0`;
      `\x:A. inv((&1 + (v':num->A->real) 0 x) pow 2)`;
      `&1`] TRUNCATED_DIFF_SQ_BOUND) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> MATCH_MP_TAC(BETA_RULE th)) THEN
    REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
    [(* integrable phi *)
     MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\x:A. inv((&1 + (v':num->A->real) 0 x) pow 2)) =
        (\x. &1 / (&1 + v' 0 x) pow 2)` SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_LID]; ALL_TAC] THEN
      MATCH_MP_TAC RANDOM_VARIABLE_DIV_POS THEN CONJ_TAC THENL
      [REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN CONJ_TAC THENL
      [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
       MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
       [REWRITE_TAC[RANDOM_VARIABLE_CONST];
        REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
       X_GEN_TAC `x:A` THEN DISCH_TAC THEN
       MATCH_MP_TAC REAL_POW_LT THEN
       MATCH_MP_TAC(REAL_ARITH `&0 <= v ==> &0 < &1 + v`) THEN
       ASM_MESON_TAC[]];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
      REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 pow 2` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= v ==> &1 <= abs(&1 + v)`) THEN
      ASM_MESON_TAC[]];
     (* measurable_wrt phi *)
     MATCH_MP_TAC MEASURABLE_WRT_INV_GE_ONE THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_WRT_POW2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MEASURABLE_WRT_ADD THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
      [MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[]];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 pow 2` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= v ==> &1 <= &1 + v`) THEN
      ASM_MESON_TAC[]];
     (* abs bound *)
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW] THEN
     MATCH_MP_TAC REAL_INV_LE_1 THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 pow 2` THEN
     CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC REAL_POW_LE2 THEN
     CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= v ==> &1 <= abs(&1 + v)`) THEN
     ASM_MESON_TAC[];
     (* nonneg *)
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= v ==> &0 <= &1 + v`) THEN
     ASM_MESON_TAC[]];
    (* Inductive step *)
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
    (* Shared: inner denominators positive *)
    SUBGOAL_THEN `!k (x:A). x IN prob_carrier p
      ==> &0 < &1 + sum(0..k) (\j. (v':num->A->real) j x)`
      ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> &0 < &1 + s`) THEN
     MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
    (* Shared: outer denominator positive *)
    SUBGOAL_THEN `!(x:A). x IN prob_carrier p
      ==> &0 < &1 + sum(0..n) (\j. (v':num->A->real) j x) +
          v' (SUC n) x` ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN
     MATCH_MP_TAC(REAL_ARITH
       `&0 <= s /\ &0 <= t ==> &0 < &1 + s + t`) THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
     ALL_TAC] THEN
    (* Shared: integrable v' k *)
    SUBGOAL_THEN `!k:num. integrable p ((v':num->A->real) k)`
      ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
     EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     MATCH_MP_TAC(REAL_ARITH
       `&0 <= y /\ y <= &1 ==> abs(y) <= &1`) THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
    (* Shared: |1_B - v'| <= 1 *)
    SUBGOAL_THEN `!k (x:A). x IN prob_carrier p
      ==> abs(indicator_fn ((B:num->A->bool) (SUC k)) x -
              (v':num->A->real) k x) <= &1` ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN
     MATCH_MP_TAC(REAL_ARITH
       `&0 <= i /\ i <= &1 /\ &0 <= v /\ v <= &1
        ==> abs(i - v) <= &1`) THEN
     REWRITE_TAC[indicator_fn] THEN
     CONJ_TAC THENL [COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
     CONJ_TAC THENL [COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
    (* Step 1: Cross-term E[(1_B - v') * Sn / Dn] = 0 *)
    SUBGOAL_THEN `expectation p
      (\x:A. (indicator_fn ((B:num->A->bool) (SUC (SUC n))) x -
              (v':num->A->real) (SUC n) x) *
       (sum (0..n)
         (\k. (indicator_fn (B (SUC k)) x - v' k x) /
              (&1 + sum (0..k) (\j. v' j x))) /
        (&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x))) = &0`
      ASSUME_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
        `B:num->A->bool`; `SUC n`;
        `\x:A. sum (0..n)
          (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
                (v':num->A->real) k x) /
               (&1 + sum (0..k) (\j. v' j x))) /
          (&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x)`;
        `&(SUC n)`] TRUNCATED_DIFF_EXPECTATION_ZERO) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(fun th ->
       MATCH_MP_TAC(BETA_RULE(REWRITE_RULE[IMP_IMP] th))) THEN
     REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
     [(* integrable Sn/Dn *)
      MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&(SUC n)` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC RANDOM_VARIABLE_DIV_POS THEN CONJ_TAC THENL
       [MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
        MATCH_MP_TAC RANDOM_VARIABLE_DIV_POS THEN CONJ_TAC THENL
        [MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
         [SUBGOAL_THEN `(\x:A. indicator_fn ((B:num->A->bool) (SUC i)) x) =
           indicator_fn (B (SUC i))` SUBST1_TAC THENL
          [REWRITE_TAC[FUN_EQ_THM; ETA_AX]; ALL_TAC] THEN
          MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
          MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
         ALL_TAC] THEN CONJ_TAC THENL
        [MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
         [REWRITE_TAC[RANDOM_VARIABLE_CONST];
          MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN GEN_TAC THEN DISCH_TAC THEN
          BETA_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
         X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_MESON_TAC[]];
        ALL_TAC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
        [REWRITE_TAC[RANDOM_VARIABLE_CONST];
         MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
         [MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN GEN_TAC THEN DISCH_TAC THEN
          BETA_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]]];
        X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_MESON_TAC[]];
       (* bound: |Sn/Dn| <= SUC n *)
       X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
       REWRITE_TAC[REAL_ABS_DIV] THEN
       MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `sum(0..n) (\k:num. &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_ABS_DIV_LE THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LE_TRANS THEN
         EXISTS_TAC `sum(0..n)
           (\k. abs((indicator_fn ((B:num->A->bool) (SUC k)) x -
                     (v':num->A->real) k x) /
                    (&1 + sum (0..k) (\j. v' j x))))` THEN
         CONJ_TAC THENL
         [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
          SIMP_TAC[IN_NUMSEG; REAL_LE_REFL]; ALL_TAC] THEN
         MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN
         STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_DIV] THEN
         MATCH_MP_TAC REAL_DIV_ABS_LE_1 THEN
         CONJ_TAC THENL [ASM_MESON_TAC[];
         MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> &1 <= &1 + s`) THEN
         MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
         ASM_MESON_TAC[]];
         MATCH_MP_TAC(REAL_ARITH
           `&0 <= s /\ &0 <= t ==> &1 <= abs(&1 + s + t)`) THEN
         CONJ_TAC THENL
         [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
          ASM_MESON_TAC[];
          ASM_MESON_TAC[]]];
        REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
        REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_MUL; MULT_CLAUSES] THEN
        ARITH_TAC]];
      (* measurable_wrt Sn/Dn wrt FF(SUC n) *)
      REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC MEASURABLE_WRT_MUL THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC MEASURABLE_WRT_SUM THEN ASM_REWRITE_TAC[] THEN
       X_GEN_TAC `k:num` THEN DISCH_TAC THEN
       REWRITE_TAC[real_div] THEN BETA_TAC THEN
       MATCH_MP_TAC MEASURABLE_WRT_MUL THEN ASM_REWRITE_TAC[] THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_WRT_SUB THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
        [MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
         EXISTS_TAC `(FF:num->(A->bool)->bool) (SUC k)` THEN
         CONJ_TAC THENL
         [MATCH_MP_TAC MEASURABLE_WRT_INDICATOR THEN ASM_REWRITE_TAC[];
          SUBGOAL_THEN `SUC k <= SUC (n:num)` ASSUME_TAC THENL
          [UNDISCH_TAC `k:num <= n` THEN ARITH_TAC; ALL_TAC] THEN
          ASM_MESON_TAC[filtration]];
         MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
         EXISTS_TAC `(FF:num->(A->bool)->bool) k` THEN
         ASM_REWRITE_TAC[] THEN
         SUBGOAL_THEN `k:num <= SUC n` ASSUME_TAC THENL
         [UNDISCH_TAC `k:num <= n` THEN ARITH_TAC; ALL_TAC] THEN
         ASM_MESON_TAC[filtration]];
        MATCH_MP_TAC MEASURABLE_WRT_INV_GE_ONE THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC MEASURABLE_WRT_ADD THEN ASM_REWRITE_TAC[] THEN
         CONJ_TAC THENL
         [MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC MEASURABLE_WRT_SUM THEN ASM_REWRITE_TAC[] THEN
          X_GEN_TAC `j:num` THEN DISCH_TAC THEN
          REWRITE_TAC[ETA_AX] THEN
          MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
          EXISTS_TAC `(FF:num->(A->bool)->bool) j` THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `j:num <= SUC n` ASSUME_TAC THENL
          [UNDISCH_TAC `j:num <= k` THEN UNDISCH_TAC `k:num <= n` THEN
           ARITH_TAC; ALL_TAC] THEN
          ASM_MESON_TAC[filtration]];
         X_GEN_TAC `x:A` THEN DISCH_TAC THEN
         MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> &1 <= &1 + s`) THEN
         MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
         ASM_MESON_TAC[]]];
       MATCH_MP_TAC MEASURABLE_WRT_INV_GE_ONE THEN ASM_REWRITE_TAC[] THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_WRT_ADD THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_REWRITE_TAC[];
         MATCH_MP_TAC MEASURABLE_WRT_ADD THEN ASM_REWRITE_TAC[] THEN
         CONJ_TAC THENL
         [MATCH_MP_TAC MEASURABLE_WRT_SUM THEN ASM_REWRITE_TAC[] THEN
          X_GEN_TAC `j:num` THEN DISCH_TAC THEN
          REWRITE_TAC[ETA_AX] THEN
          MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
          EXISTS_TAC `(FF:num->(A->bool)->bool) j` THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `j:num <= SUC n` ASSUME_TAC THENL
          [UNDISCH_TAC `j:num <= n` THEN ARITH_TAC; ALL_TAC] THEN
          ASM_MESON_TAC[filtration];
          REWRITE_TAC[ETA_AX] THEN
          MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
          EXISTS_TAC `(FF:num->(A->bool)->bool) (SUC n)` THEN
          ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[filtration; LE_REFL]]];
        X_GEN_TAC `x:A` THEN DISCH_TAC THEN
        MATCH_MP_TAC(REAL_ARITH
          `&0 <= s /\ &0 <= t ==> &1 <= &1 + s + t`) THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
         ASM_MESON_TAC[];
         ASM_MESON_TAC[]]]];
      (* |Sn/Dn| <= SUC n *)
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
      REWRITE_TAC[REAL_ABS_DIV] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(0..n) (\k:num. &1)` THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_ABS_DIV_LE THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `sum(0..n)
          (\k. abs((indicator_fn ((B:num->A->bool) (SUC k)) x -
                    (v':num->A->real) k x) /
                   (&1 + sum (0..k) (\j. v' j x))))` THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
         SIMP_TAC[IN_NUMSEG; REAL_LE_REFL]; ALL_TAC] THEN
        MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN
        STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_DIV] THEN
        MATCH_MP_TAC REAL_DIV_ABS_LE_1 THEN
        CONJ_TAC THENL [ASM_MESON_TAC[];
        MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> &1 <= &1 + s`) THEN
        MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
        ASM_MESON_TAC[]];
        MATCH_MP_TAC(REAL_ARITH
          `&0 <= s /\ &0 <= t ==> &1 <= abs(&1 + s + t)`) THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
         ASM_MESON_TAC[];
         ASM_MESON_TAC[]]];
       REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
       REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_MUL; MULT_CLAUSES] THEN
       ARITH_TAC]];
     ALL_TAC] THEN
    (* Step 2: Main inequality via REAL_LE_TRANS *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `expectation p
      (\x:A. sum (0..n)
         (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
              (v':num->A->real) k x) /
              (&1 + sum (0..k) (\j. v' j x))) pow 2) +
      expectation p
      (\x. (indicator_fn (B (SUC (SUC n))) x - v' (SUC n) x) pow 2 *
           inv ((&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x) pow 2))` THEN
    CONJ_TAC THENL
    [(* E[(S+d)^2] <= E[S^2] + E[d^2] using cross-term = 0 *)
     MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= b`) THEN
     (* Algebraic identity: (S + d/D)^2 = S^2 + d^2/D^2 + 2*(d*(S/D)) *)
     SUBGOAL_THEN
       `(\x:A. (sum (0..n)
         (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
              (v':num->A->real) k x) /
              (&1 + sum (0..k) (\j. v' j x))) +
        (indicator_fn (B (SUC (SUC n))) x - v' (SUC n) x) /
        (&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x)) pow 2) =
       (\x. sum (0..n)
         (\k. (indicator_fn (B (SUC k)) x - v' k x) /
              (&1 + sum (0..k) (\j. v' j x))) pow 2 +
        (indicator_fn (B (SUC (SUC n))) x - v' (SUC n) x) pow 2 *
        inv ((&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x) pow 2) +
        &2 * ((indicator_fn (B (SUC (SUC n))) x - v' (SUC n) x) *
         (sum (0..n)
           (\k. (indicator_fn (B (SUC k)) x - v' k x) /
                (&1 + sum (0..k) (\j. v' j x))) /
          (&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x))))`
       SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN BETA_TAC THEN
      SPEC_TAC(`sum (0..n)
        (\k. (indicator_fn ((B:num->A->bool) (SUC k)) (x:A) -
              (v':num->A->real) k x) /
             (&1 + sum (0..k) (\j. v' j x)))`, `s:real`) THEN
      SPEC_TAC(`indicator_fn ((B:num->A->bool) (SUC (SUC n))) (x:A) -
                (v':num->A->real) (SUC n) x`, `dd:real`) THEN
      SPEC_TAC(`&1 + sum (0..n) (\j. (v':num->A->real) j (x:A)) +
                v' (SUC n) x`, `cc:real`) THEN
      REPEAT GEN_TAC THEN
      REWRITE_TAC[real_div; REAL_POW_MUL; GSYM REAL_POW_INV] THEN
      CONV_TAC REAL_RING;
      ALL_TAC] THEN
     (* Integrable: each term (ind-v')/(1+V_k) *)
     SUBGOAL_THEN `!i:num. i <= n
       ==> integrable p (\x:A. (indicator_fn ((B:num->A->bool) (SUC i)) x -
           (v':num->A->real) i x) /
           (&1 + sum (0..i) (\j. v' j x)))` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN EXISTS_TAC `&1` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
       ALL_TAC] THEN CONJ_TAC THENL
      [SUBGOAL_THEN `(\x:A. inv(&1 + sum (0..i)
          (\j. (v':num->A->real) j x))) =
         (\x. &1 / (&1 + sum (0..i) (\j. v' j x)))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_LID]; ALL_TAC] THEN
       MATCH_MP_TAC RANDOM_VARIABLE_DIV_POS THEN CONJ_TAC THENL
       [REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
        [REWRITE_TAC[RANDOM_VARIABLE_CONST];
         MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN GEN_TAC THEN DISCH_TAC THEN
         BETA_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
        X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_MESON_TAC[]];
       ALL_TAC] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
      REWRITE_TAC[REAL_ABS_INV] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> &1 <= abs(&1 + s)`) THEN
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
     (* Integrable S_n *)
     SUBGOAL_THEN `integrable p
       (\x:A. sum (0..n) (\k.
         (indicator_fn ((B:num->A->bool) (SUC k)) x -
          (v':num->A->real) k x) /
         (&1 + sum (0..k) (\j. v' j x))))` ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SUM THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     (* |S_n| <= SUC n *)
     SUBGOAL_THEN `!x:A. x IN prob_carrier p
       ==> abs(sum (0..n) (\k.
         (indicator_fn ((B:num->A->bool) (SUC k)) x -
          (v':num->A->real) k x) /
         (&1 + sum (0..k) (\j. v' j x)))) <= &(SUC n)` ASSUME_TAC THENL
     [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(0..n) (\k:num. &1)` THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `sum(0..n)
         (\k. abs((indicator_fn ((B:num->A->bool) (SUC k)) x -
                   (v':num->A->real) k x) /
                  (&1 + sum (0..k) (\j. v' j x))))` THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
        SIMP_TAC[IN_NUMSEG; REAL_LE_REFL]; ALL_TAC] THEN
       MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN
       STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_DIV] THEN
       MATCH_MP_TAC REAL_DIV_ABS_LE_1 THEN
       CONJ_TAC THENL [ASM_MESON_TAC[];
       MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> &1 <= &1 + s`) THEN
       MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
       ASM_MESON_TAC[]];
       REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
       REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_MUL; MULT_CLAUSES] THEN
       ARITH_TAC];
      ALL_TAC] THEN
     (* Integrable S_n^2 *)
     SUBGOAL_THEN `integrable p
       (\x:A. sum (0..n) (\k.
         (indicator_fn ((B:num->A->bool) (SUC k)) x -
          (v':num->A->real) k x) /
         (&1 + sum (0..k) (\j. v' j x))) pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
      EXISTS_TAC `(&(SUC n)) pow 2` THEN CONJ_TAC THENL
      [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
       MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN ASM_REWRITE_TAC[];
       X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
       REWRITE_TAC[REAL_ABS_POW] THEN
       MATCH_MP_TAC REAL_POW_LE2 THEN
       REWRITE_TAC[REAL_ABS_POS] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
     (* Integrable d^2 * inv(D^2) *)
     SUBGOAL_THEN `integrable p
       (\x:A. (indicator_fn ((B:num->A->bool) (SUC (SUC n))) x -
        (v':num->A->real) (SUC n) x) pow 2 *
        inv ((&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x) pow 2))`
       ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
        MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
        [SUBGOAL_THEN `(\x:A. indicator_fn
           ((B:num->A->bool) (SUC (SUC n))) x) =
           indicator_fn (B (SUC (SUC n)))` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; ETA_AX]; ALL_TAC] THEN
         MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
         MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
         REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `(\x:A. inv((&1 + sum (0..n)
          (\j. (v':num->A->real) j x) + v' (SUC n) x) pow 2)) =
          (\x. &1 / (&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x) pow 2)`
          SUBST1_TAC THENL
        [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_LID]; ALL_TAC] THEN
        MATCH_MP_TAC RANDOM_VARIABLE_DIV_POS THEN CONJ_TAC THENL
        [REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN CONJ_TAC THENL
        [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
         MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
         [REWRITE_TAC[RANDOM_VARIABLE_CONST];
          MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
          [MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN GEN_TAC THEN DISCH_TAC THEN
           BETA_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
           REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]]];
         X_GEN_TAC `x:A` THEN DISCH_TAC THEN
         MATCH_MP_TAC REAL_POW_LT THEN ASM_MESON_TAC[]]];
       X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
       REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_INV] THEN
       MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &1` THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN
        REPEAT CONJ_TAC THENL
        [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
         MATCH_MP_TAC REAL_POW_1_LE THEN REWRITE_TAC[REAL_ABS_POS] THEN
         ASM_MESON_TAC[];
         MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
         REWRITE_TAC[REAL_ABS_POS];
         MATCH_MP_TAC REAL_INV_LE_1 THEN
         MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 pow 2` THEN
         CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
         MATCH_MP_TAC REAL_POW_LE2 THEN
         CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
         MATCH_MP_TAC(REAL_ARITH
           `&0 <= s /\ &0 <= t ==> &1 <= abs(&1 + s + t)`) THEN
         CONJ_TAC THENL
         [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
          ASM_MESON_TAC[];
          ASM_MESON_TAC[]]];
        REAL_ARITH_TAC]];
      ALL_TAC] THEN
     (* Integrable cross-term d * (S/D) *)
     SUBGOAL_THEN `integrable p
       (\x:A. (indicator_fn ((B:num->A->bool) (SUC (SUC n))) x -
        (v':num->A->real) (SUC n) x) *
        (sum (0..n) (\k. (indicator_fn (B (SUC k)) x - v' k x) /
              (&1 + sum (0..k) (\j. v' j x))) /
         (&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x)))`
       ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN
      EXISTS_TAC `&(SUC n)` THEN CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
       ALL_TAC] THEN CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
       ONCE_REWRITE_TAC[real_div] THEN
       MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN
       EXISTS_TAC `&1` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(\x:A. inv(&1 + sum (0..n)
          (\j. (v':num->A->real) j x) + v' (SUC n) x)) =
          (\x. &1 / (&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x))`
          SUBST1_TAC THENL
        [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_LID]; ALL_TAC] THEN
        MATCH_MP_TAC RANDOM_VARIABLE_DIV_POS THEN CONJ_TAC THENL
        [REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN CONJ_TAC THENL
        [MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
         [REWRITE_TAC[RANDOM_VARIABLE_CONST];
          MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
          [MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN GEN_TAC THEN DISCH_TAC THEN
           BETA_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
           REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]]];
         X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_MESON_TAC[]];
        ALL_TAC] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
       X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
       REWRITE_TAC[REAL_ABS_INV] THEN
       MATCH_MP_TAC REAL_INV_LE_1 THEN
       MATCH_MP_TAC(REAL_ARITH
         `&0 <= s /\ &0 <= t ==> &1 <= abs(&1 + s + t)`) THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
        ASM_MESON_TAC[];
        ASM_MESON_TAC[]];
       ALL_TAC] THEN CONJ_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
      REWRITE_TAC[REAL_ABS_DIV] THEN
      MATCH_MP_TAC REAL_ABS_DIV_LE THEN
      CONJ_TAC THENL
      [ASM_MESON_TAC[];
       MATCH_MP_TAC(REAL_ARITH
         `&0 <= s /\ &0 <= t ==> &1 <= abs(&1 + s + t)`) THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
        ASM_MESON_TAC[];
        ASM_MESON_TAC[]]];
      ALL_TAC] THEN
     (* First EXPECTATION_ADD: split E[S^2 + (d^2/D^2 + 2*cross)] *)
     MP_TAC(ISPECL [`p:A prob_space`;
       `\x:A. sum (0..n)
         (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
              (v':num->A->real) k x) /
              (&1 + sum (0..k) (\j. v' j x))) pow 2`;
       `\x:A. (indicator_fn ((B:num->A->bool) (SUC (SUC n))) x -
        (v':num->A->real) (SUC n) x) pow 2 *
        inv ((&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x) pow 2) +
        &2 * ((indicator_fn (B (SUC (SUC n))) x - v' (SUC n) x) *
         (sum (0..n) (\k. (indicator_fn (B (SUC k)) x - v' k x) /
               (&1 + sum (0..k) (\j. v' j x))) /
          (&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x)))`]
       EXPECTATION_ADD) THEN
     BETA_TAC THEN ANTS_TAC THENL
     [CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     AP_TERM_TAC THEN
     (* Second EXPECTATION_ADD: split E[d^2/D^2 + 2*cross] *)
     MP_TAC(ISPECL [`p:A prob_space`;
       `\x:A. (indicator_fn ((B:num->A->bool) (SUC (SUC n))) x -
        (v':num->A->real) (SUC n) x) pow 2 *
        inv ((&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x) pow 2)`;
       `\x:A. &2 * ((indicator_fn ((B:num->A->bool) (SUC (SUC n))) x -
        (v':num->A->real) (SUC n) x) *
        (sum (0..n) (\k. (indicator_fn (B (SUC k)) x - v' k x) /
              (&1 + sum (0..k) (\j. v' j x))) /
         (&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x)))`]
       EXPECTATION_ADD) THEN
     BETA_TAC THEN ANTS_TAC THENL
     [CONJ_TAC THENL
      [ASM_REWRITE_TAC[];
       MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     (* E[2 * cross] = 2 * E[cross] = 0 *)
     MP_TAC(ISPECL [`p:A prob_space`; `&2`;
       `\x:A. (indicator_fn ((B:num->A->bool) (SUC (SUC n))) x -
        (v':num->A->real) (SUC n) x) *
        (sum (0..n) (\k. (indicator_fn (B (SUC k)) x - v' k x) /
              (&1 + sum (0..k) (\j. v' j x))) /
         (&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x))`]
       EXPECTATION_CMUL) THEN
     BETA_TAC THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    (* Step 3: E[S^2] + E[d^2] <= E[sum + v'/D^2] *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `expectation p
      (\x:A. sum (0..n) (\k. (v':num->A->real) k x /
        (&1 + sum (0..k) (\j. v' j x)) pow 2)) +
      expectation p
      (\x. v' (SUC n) x *
           inv ((&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x) pow 2))` THEN
    CONJ_TAC THENL
    [(* IH + TRUNCATED_DIFF_SQ_BOUND *)
     MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
        `B:num->A->bool`; `SUC n`;
        `\x:A. inv((&1 + sum (0..n) (\j. (v':num->A->real) j x) +
                     v' (SUC n) x) pow 2)`;
        `&1`] TRUNCATED_DIFF_SQ_BOUND) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th ->
        MATCH_MP_TAC(BETA_RULE(REWRITE_RULE[IMP_IMP] th))) THEN
      REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
      [(* integrable inv(D^2) *)
       MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN
       CONJ_TAC THENL
       [SUBGOAL_THEN `(\x:A. inv((&1 + sum (0..n)
           (\j. (v':num->A->real) j x) + v' (SUC n) x) pow 2)) =
         (\x. &1 / (&1 + sum (0..n) (\j. v' j x) + v' (SUC n) x) pow 2)`
         SUBST1_TAC THENL
        [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_LID]; ALL_TAC] THEN
        MATCH_MP_TAC RANDOM_VARIABLE_DIV_POS THEN CONJ_TAC THENL
        [REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN CONJ_TAC THENL
        [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
         MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
         [REWRITE_TAC[RANDOM_VARIABLE_CONST];
          MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
          [MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN GEN_TAC THEN
           DISCH_TAC THEN BETA_TAC THEN
           REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
           REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]]];
         X_GEN_TAC `x:A` THEN DISCH_TAC THEN
         MATCH_MP_TAC REAL_POW_LT THEN ASM_MESON_TAC[]];
        X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
        REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW] THEN
        MATCH_MP_TAC REAL_INV_LE_1 THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 pow 2` THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH
          `&0 <= s /\ &0 <= t ==> &1 <= abs(&1 + s + t)`) THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
         ASM_MESON_TAC[];
         ASM_MESON_TAC[]]];
       (* measurable_wrt inv(D^2) *)
       MATCH_MP_TAC MEASURABLE_WRT_INV_GE_ONE THEN ASM_REWRITE_TAC[] THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_WRT_POW2 THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MEASURABLE_WRT_ADD THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC MEASURABLE_WRT_CONST THEN ASM_REWRITE_TAC[];
         MATCH_MP_TAC MEASURABLE_WRT_ADD THEN ASM_REWRITE_TAC[] THEN
         CONJ_TAC THENL
         [MATCH_MP_TAC MEASURABLE_WRT_SUM THEN ASM_REWRITE_TAC[] THEN
          X_GEN_TAC `j:num` THEN DISCH_TAC THEN
          REWRITE_TAC[ETA_AX] THEN
          MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
          EXISTS_TAC `(FF:num->(A->bool)->bool) j` THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `j:num <= SUC n` ASSUME_TAC THENL
          [UNDISCH_TAC `j:num <= n` THEN ARITH_TAC; ALL_TAC] THEN
          ASM_MESON_TAC[filtration];
          REWRITE_TAC[ETA_AX] THEN
          MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
          EXISTS_TAC `(FF:num->(A->bool)->bool) (SUC n)` THEN
          ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[filtration; LE_REFL]]];
        X_GEN_TAC `x:A` THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 pow 2` THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH
          `&0 <= s /\ &0 <= t ==> &1 <= &1 + s + t`) THEN
        CONJ_TAC THENL
        [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
         ASM_MESON_TAC[];
         ASM_MESON_TAC[]]];
       (* |inv(D^2)| <= 1 *)
       X_GEN_TAC `x:A` THEN DISCH_TAC THEN
       REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW] THEN
       MATCH_MP_TAC REAL_INV_LE_1 THEN
       MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 pow 2` THEN
       CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC REAL_POW_LE2 THEN
       CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC(REAL_ARITH
         `&0 <= s /\ &0 <= t ==> &1 <= abs(&1 + s + t)`) THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
        ASM_MESON_TAC[];
        ASM_MESON_TAC[]];
       (* nonneg: 0 <= inv(D^2) *)
       X_GEN_TAC `x:A` THEN DISCH_TAC THEN
       MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
       MATCH_MP_TAC(REAL_ARITH
         `&0 <= s /\ &0 <= t ==> &0 <= &1 + s + t`) THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
        ASM_MESON_TAC[];
        ASM_MESON_TAC[]]]];
     (* E[sum] + E[v'*inv(D^2)] = E[sum + v'/D^2] *)
     REWRITE_TAC[real_div] THEN
     MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= b`) THEN
     MATCH_MP_TAC(GSYM EXPECTATION_ADD) THEN
     CONJ_TAC THENL
     [(* integrable sum v'_k * inv(D_k^2) *)
      MATCH_MP_TAC INTEGRABLE_SUM THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN
      EXISTS_TAC `&1` THEN CONJ_TAC THENL
      [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
      [SUBGOAL_THEN `(\x:A. inv((&1 + sum (0..i)
          (\j. (v':num->A->real) j x)) pow 2)) =
        (\x. &1 / (&1 + sum (0..i) (\j. v' j x)) pow 2)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_LID]; ALL_TAC] THEN
       MATCH_MP_TAC RANDOM_VARIABLE_DIV_POS THEN CONJ_TAC THENL
       [REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
        MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
        [REWRITE_TAC[RANDOM_VARIABLE_CONST];
         MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN GEN_TAC THEN DISCH_TAC THEN
         BETA_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
        X_GEN_TAC `x:A` THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_POW_LT THEN ASM_MESON_TAC[]];
       CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
       X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
       REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW] THEN
       MATCH_MP_TAC REAL_INV_LE_1 THEN
       MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 pow 2` THEN
       CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC REAL_POW_LE2 THEN
       CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> &1 <= abs(&1 + s)`) THEN
       MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
       ASM_MESON_TAC[]];
      (* integrable v'(SUC n) * inv(D^2) *)
      MATCH_MP_TAC INTEGRABLE_MUL_BOUNDED THEN
      EXISTS_TAC `&1` THEN CONJ_TAC THENL
      [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
      [SUBGOAL_THEN `(\x:A. inv((&1 + sum (0..n)
          (\j. (v':num->A->real) j x) + v' (SUC n) x) pow 2)) =
        (\x. &1 / (&1 + sum (0..n) (\j. v' j x) +
             v' (SUC n) x) pow 2)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; real_div; REAL_MUL_LID]; ALL_TAC] THEN
       MATCH_MP_TAC RANDOM_VARIABLE_DIV_POS THEN CONJ_TAC THENL
       [REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
        MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
        [REWRITE_TAC[RANDOM_VARIABLE_CONST];
         MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
         [MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN GEN_TAC THEN DISCH_TAC THEN
          BETA_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]]];
        X_GEN_TAC `x:A` THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_POW_LT THEN ASM_MESON_TAC[]];
       CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
       X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
       REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW] THEN
       MATCH_MP_TAC REAL_INV_LE_1 THEN
       MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 pow 2` THEN
       CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC REAL_POW_LE2 THEN
       CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC(REAL_ARITH
         `&0 <= s /\ &0 <= t ==> &1 <= abs(&1 + s + t)`) THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
        ASM_MESON_TAC[];
        ASM_MESON_TAC[]]]]]];
   ALL_TAC] THEN
  (* Final: E[sum v'/(1+V')^2] <= 1 by telescoping *)
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation p
    (\x:A. sum (0..n) (\k. (v':num->A->real) k x /
      (&1 + sum (0..k) (\j. v' j x)) pow 2))` THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation p (\x:A. &1)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC EXPECTATION_MONO THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN GEN_TAC THEN DISCH_TAC THEN
     BETA_TAC THEN
     MATCH_MP_TAC RANDOM_VARIABLE_DIV_POS THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      CONJ_TAC THENL
      [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
       MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN
       REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
       MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN GEN_TAC THEN DISCH_TAC THEN
       REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
       GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
       MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> &0 < &1 + s`) THEN
       MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
       ASM_MESON_TAC[]]];
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= t /\ t <= &1 ==> abs t <= &1`) THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN GEN_TAC THEN STRIP_TAC THEN
      BETA_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
      [ASM_MESON_TAC[]; REWRITE_TAC[REAL_LE_POW_2]];
      MP_TAC(ISPECL [`\k:num. (v':num->A->real) k (x:A)`; `n:num`]
        TELESCOPING_VARIANCE_BOUND_SIMPLE) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      GEN_TAC THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_BOUNDED THEN EXISTS_TAC `&1` THEN
    CONJ_TAC THENL [REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_ABS_NUM] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC TELESCOPING_VARIANCE_BOUND_SIMPLE THEN
    GEN_TAC THEN ASM_MESON_TAC[]];
   REWRITE_TAC[EXPECTATION_CONST; REAL_LE_REFL]]);;

(* Helper: T' has bounded L1 norm                                          *)
let RESCALED_MAX_L2_BOUNDED = prove
 (`!p FF (B:num->A->bool).
     filtration p FF /\ (!n. B n IN prob_events p) /\
     (!n. B n SUBSET prob_carrier p) /\ (!n. B n IN FF n)
     ==> !n. expectation p
       (\x. abs(sum(0..n)
         (\k. (indicator_fn (B (SUC k)) x -
               gen_cond_exp p (FF k)
                 (\y. indicator_fn (B (SUC k)) y) x) /
              max (&1 + sum(0..k)
                (\j. gen_cond_exp p (FF j)
                  (\y. indicator_fn (B (SUC j)) y) x)) (&1)))) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `v = \k x:A. gen_cond_exp p (FF k)
    (\y. indicator_fn (B (SUC k)) y) x` THEN
  SUBGOAL_THEN `!k (x:A). gen_cond_exp p (FF k)
    (\y. indicator_fn (B (SUC k)) y) x = (v:num->A->real) k x`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!n. sub_sigma_algebra p ((FF:num->(A->bool)->bool) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. integrable p (\y:A. indicator_fn
    ((B:num->A->bool) (SUC k)) y)` ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[ETA_AX] THEN
   MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `v' = \k (x:A). max (min ((v:num->A->real) k x) (&1)) (&0)` THEN
  SUBGOAL_THEN `!k (x:A). &0 <= (v':num->A->real) k x /\ v' k x <= &1`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN EXPAND_TAC "v'" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!k. random_variable p (\x:A. (v:num->A->real) k x)`
    (LABEL_TAC "RV_V") THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `(\x:A. (v:num->A->real) k x) =
     gen_cond_exp p ((FF:num->(A->bool)->bool) k)
       (\y. indicator_fn ((B:num->A->bool) (SUC k)) y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
   EXISTS_TAC `(FF:num->(A->bool)->bool) k` THEN
   ASM_MESON_TAC[GEN_COND_EXP_MEASURABLE_WRT];
   ALL_TAC] THEN
  (* v = v' a.e. for all k simultaneously *)
  SUBGOAL_THEN `almost_surely p
    {x:A | !k. (v:num->A->real) k x = (v':num->A->real) k x}`
    (LABEL_TAC "VV") THENL
  [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
   EXISTS_TAC `INTERS {(\k. {x:A | &0 <= (v:num->A->real) k x /\
     v k x <= &1}) n | n IN (:num)}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN GEN_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `{x:A | &0 <= (v:num->A->real) n x /\ v n x <= &1} =
      {x | &0 <= gen_cond_exp p (FF n) (\y. indicator_fn (B (SUC n)) y) x /\
       gen_cond_exp p (FF n) (\y. indicator_fn (B (SUC n)) y) x <= &1}`
      SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
      `B:num->A->bool`] COND_EXP_INDICATOR_BOUNDED_AE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[];
    REWRITE_TAC[IN_INTERS; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    DISCH_TAC THEN X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN `&0 <= (v:num->A->real) k x /\ v k x <= &1` MP_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC
      `{x:A | &0 <= (v:num->A->real) k x /\ v k x <= &1}`) THEN
     REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
     [EXISTS_TAC `k:num` THEN REWRITE_TAC[]; SIMP_TAC[]]; ALL_TAC] THEN
    EXPAND_TAC "v'" THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  (* On the a.e. set, v = v' implies T' = T'' *)
  SUBGOAL_THEN `!n:num. almost_surely p
    {x:A | sum (0..n) (\k. (indicator_fn (B (SUC k)) x - (v:num->A->real) k x) /
      max (&1 + sum (0..k) (\j. v j x)) (&1)) =
     sum (0..n) (\k. (indicator_fn (B (SUC k)) x - (v':num->A->real) k x) /
      (&1 + sum (0..k) (\j. v' j x)))}`
    (LABEL_TAC "EQ") THENL
  [GEN_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
   EXISTS_TAC `{x:A | !k. (v:num->A->real) k x = (v':num->A->real) k x}` THEN
   CONJ_TAC THENL [REMOVE_THEN "VV" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
   REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   DISCH_TAC THEN
   MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
   SUBGOAL_THEN `(v:num->A->real) k x = (v':num->A->real) k x` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `sum (0..k) (\j. (v:num->A->real) j x) =
     sum (0..k) (\j. (v':num->A->real) j x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= sum (0..k) (\j. (v':num->A->real) j x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `&0 <= s ==> max (&1 + s) (&1) = &1 + s`) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* The original |T'| is integrable (from martingale property) *)
  SUBGOAL_THEN `!n:num. integrable p (\x:A. abs(sum (0..n)
    (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
      (v:num->A->real) k x) /
      max (&1 + sum (0..k) (\j. v j x)) (&1))))` (LABEL_TAC "INT") THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_ABS THEN
   MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
     `B:num->A->bool`] RESCALED_MAX_MARTINGALE) THEN
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[martingale; submartingale] THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* L2 bound for truncated version *)
  SUBGOAL_THEN `!n:num. expectation p
    (\x:A. (sum (0..n) (\k. (indicator_fn (B (SUC k)) x -
      (v':num->A->real) k x) /
      (&1 + sum (0..k) (\j. v' j x)))) pow 2) <= &1`
    (LABEL_TAC "L2") THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
     `B:num->A->bool`] RESCALED_TRUNCATED_L2) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `!k (x:A). max (min (gen_cond_exp p ((FF:num->(A->bool)->bool) k)
     (\y. indicator_fn ((B:num->A->bool) (SUC k)) y) x) (&1)) (&0) =
     (v':num->A->real) k x` (fun th -> REWRITE_TAC[th]) THEN
   REPEAT GEN_TAC THEN EXPAND_TAC "v'" THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* T'' is bounded everywhere *)
  SUBGOAL_THEN `!n (x:A). abs(sum (0..n) (\k. (indicator_fn
    ((B:num->A->bool) (SUC k)) x - (v':num->A->real) k x) /
    (&1 + sum (0..k) (\j. v' j x)))) <= &(SUC n)` (LABEL_TAC "BD") THENL
  [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `sum (0..n) (\k:num. abs((indicator_fn
     ((B:num->A->bool) (SUC k)) x - (v':num->A->real) k x) /
     (&1 + sum (0..k) (\j. v' j x))))` THEN
   REWRITE_TAC[SUM_ABS_NUMSEG] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `sum (0..n) (\k:num. &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_DIV] THEN
    SUBGOAL_THEN `&0 < abs(&1 + sum(0..k) (\j. (v':num->A->real) j x))`
      ASSUME_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> &0 < abs(&1 + s)`) THEN
     MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN CONJ_TAC THENL
    [REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN ASM_MESON_TAC[REAL_ARITH
      `&0 <= v /\ v <= &1 ==> abs(&1 - v) <= &1 /\ abs(&0 - v) <= &1`];
     MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> &1 <= abs(&1 + s)`) THEN
     MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[]];
    REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; ADD1; REAL_MUL_RID] THEN
    REAL_ARITH_TAC]; ALL_TAC] THEN
  (* T'' pow 2 is integrable *)
  SUBGOAL_THEN `!n:num. integrable p (\x:A. (sum (0..n)
    (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
      (v':num->A->real) k x) /
      (&1 + sum (0..k) (\j. v' j x)))) pow 2)` (LABEL_TAC "I2") THENL
  [X_GEN_TAC `m:num` THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `(&(SUC m)) pow 2` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `random_variable p (\x:A. sum (0..m)
     (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
       (v':num->A->real) k x) /
       (&1 + sum (0..k) (\j. v' j x))))` (fun rv_th ->
     MP_TAC(SPEC `2` (MATCH_MP RANDOM_VARIABLE_POW rv_th)) THEN
     REWRITE_TAC[]) THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN REPEAT STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_DIV_POS THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
      MATCH_MP_TAC INTEGRABLE_INDICATOR THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN EXPAND_TAC "v'" THEN
     MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN CONJ_TAC THENL
      [USE_THEN "RV_V" MATCH_ACCEPT_TAC;
       REWRITE_TAC[RANDOM_VARIABLE_CONST]];
      REWRITE_TAC[RANDOM_VARIABLE_CONST]]; ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN REPEAT STRIP_TAC THEN
     BETA_TAC THEN
     EXPAND_TAC "v'" THEN MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN CONJ_TAC THENL
      [USE_THEN "RV_V" MATCH_ACCEPT_TAC;
       REWRITE_TAC[RANDOM_VARIABLE_CONST]];
      REWRITE_TAC[RANDOM_VARIABLE_CONST]]; ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> &0 < &1 + s`) THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    USE_THEN "BD" (MP_TAC o SPECL [`m:num`; `x:A`]) THEN
    ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  (* T'' is integrable *)
  SUBGOAL_THEN `!n:num. integrable p (\x:A. sum (0..n)
    (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
      (v':num->A->real) k x) /
      (&1 + sum (0..k) (\j. v' j x))))` (LABEL_TAC "IT") THENL
  [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED THEN
   EXISTS_TAC `&(SUC n)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN REPEAT STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_DIV_POS THEN CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
      MATCH_MP_TAC INTEGRABLE_INDICATOR THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN EXPAND_TAC "v'" THEN
     MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN CONJ_TAC THENL
      [USE_THEN "RV_V" MATCH_ACCEPT_TAC;
       REWRITE_TAC[RANDOM_VARIABLE_CONST]];
      REWRITE_TAC[RANDOM_VARIABLE_CONST]]; ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN
     MATCH_MP_TAC RANDOM_VARIABLE_SUM THEN REPEAT STRIP_TAC THEN
     BETA_TAC THEN
     EXPAND_TAC "v'" THEN MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN CONJ_TAC THENL
      [USE_THEN "RV_V" MATCH_ACCEPT_TAC;
       REWRITE_TAC[RANDOM_VARIABLE_CONST]];
      REWRITE_TAC[RANDOM_VARIABLE_CONST]]; ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> &0 < &1 + s`) THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "BD" (MP_TAC o SPECL [`n:num`; `x:A`]) THEN
    ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  (* E[|T''|] <= 1 from L2 bound *)
  SUBGOAL_THEN `!n:num. expectation p
    (\x:A. abs(sum (0..n) (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
      (v':num->A->real) k x) /
      (&1 + sum (0..k) (\j. v' j x))))) <= &1` (LABEL_TAC "L1T") THENL
  [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `(expectation p (\x:A. (sum (0..n)
     (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
       (v':num->A->real) k x) /
       (&1 + sum (0..k) (\j. v' j x)))) pow 2) + &1) / &2` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_ABS_FROM_SQUARE THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    MATCH_MP_TAC(REAL_ARITH `e <= &1 ==> (e + &1) / &2 <= &1`) THEN
    ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  (* Conclusion: E[|T'|] <= E[|T''|] via a.e. equality *)
  X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation p (\x:A. abs(sum (0..n)
    (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
      (v':num->A->real) k x) /
      (&1 + sum (0..k) (\j. v' j x)))))` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC EXPECTATION_MONO_AE THEN CONJ_TAC THENL
  [USE_THEN "INT" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_ABS THEN
   USE_THEN "IT" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC `{x:A | sum (0..n) (\k. (indicator_fn
    ((B:num->A->bool) (SUC k)) x - (v:num->A->real) k x) /
    max (&1 + sum (0..k) (\j. v j x)) (&1)) =
    sum (0..n) (\k. (indicator_fn (B (SUC k)) x - (v':num->A->real) k x) /
    (&1 + sum (0..k) (\j. v' j x)))}` THEN
  CONJ_TAC THENL [USE_THEN "EQ" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* Helper: T' with max denominator converges a.e.                          *)
let RESCALED_INDICATOR_CONVERGENCE_MAX = prove
 (`!p FF (B:num->A->bool).
     filtration p FF /\ (!n. B n IN prob_events p) /\
     (!n. B n SUBSET prob_carrier p) /\ (!n. B n IN FF n)
     ==> almost_surely p
         {x | ?L. ((\n. sum(0..n)
           (\k. (indicator_fn (B (SUC k)) x -
                 gen_cond_exp p (FF k)
                   (\y. indicator_fn (B (SUC k)) y) x) /
                max (&1 + sum(0..k)
                  (\j. gen_cond_exp p (FF j)
                    (\y. indicator_fn (B (SUC j)) y) x)) (&1)))
              ---> L) sequentially}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `martingale p (\n. (FF:num->(A->bool)->bool)(SUC n))
     (\n (x:A). sum(0..n)
       (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
             gen_cond_exp p (FF k)
               (\y. indicator_fn (B (SUC k)) y) x) /
            max (&1 + sum(0..k)
              (\j. gen_cond_exp p (FF j)
                (\y. indicator_fn (B (SUC j)) y) x)) (&1)))`
  (LABEL_TAC "MART") THENL
  [MATCH_MP_TAC RESCALED_MAX_MARTINGALE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. expectation (p:A prob_space)
     (\x. abs(sum(0..n)
       (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
             gen_cond_exp p (FF k)
               (\y. indicator_fn (B (SUC k)) y) x) /
            max (&1 + sum(0..k)
              (\j. gen_cond_exp p (FF j)
                (\y. indicator_fn (B (SUC j)) y) x)) (&1)))) <= &1`
  (LABEL_TAC "L1") THENL
  [MATCH_MP_TAC RESCALED_MAX_L2_BOUNDED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`p:A prob_space`; `\n:num. (FF:num->(A->bool)->bool)(SUC n)`;
    `\n (x:A). sum(0..n)
      (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
            gen_cond_exp p (FF k)
              (\y. indicator_fn (B (SUC k)) y) x) /
           max (&1 + sum(0..k)
             (\j. gen_cond_exp p (FF j)
               (\y. indicator_fn (B (SUC j)) y) x)) (&1))`;
    `&1`]
   SUBMARTINGALE_CONVERGENCE_L1_BOUNDED) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC th) THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC MARTINGALE_IMP_SUBMARTINGALE THEN ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC[]]);;

let RESCALED_INDICATOR_CONVERGENCE = prove
 (`!p FF (B:num->A->bool).
     filtration p FF /\ (!n. B n IN prob_events p) /\
     (!n. B n SUBSET prob_carrier p) /\ (!n. B n IN FF n)
     ==> almost_surely p
         {x | ?L. ((\n. sum(0..n)
           (\k. (indicator_fn (B (SUC k)) x -
                 gen_cond_exp p (FF k)
                   (\y. indicator_fn (B (SUC k)) y) x) /
                (&1 + sum(0..k)
                  (\j. gen_cond_exp p (FF j)
                    (\y. indicator_fn (B (SUC j)) y) x))))
              ---> L) sequentially}`,
  REPEAT STRIP_TAC THEN
  (* Step 1: v_k >= 0 a.e. *)
  SUBGOAL_THEN
   `almost_surely p
     (INTERS {{x:A | &0 <=
       gen_cond_exp p (FF k)
         (\y. indicator_fn ((B:num->A->bool) (SUC k)) y) x} |
       k IN (:num)})`
  (LABEL_TAC "NONNEG_AS") THENL
  [MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN
   GEN_TAC THEN MATCH_MP_TAC GEN_COND_EXP_NONNEG THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[filtration];
    REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  (* Step 2: T' with max denominator converges a.e. *)
  SUBGOAL_THEN
   `almost_surely p
     {x:A | ?L. ((\n. sum(0..n)
       (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
             gen_cond_exp p (FF k)
               (\y. indicator_fn (B (SUC k)) y) x) /
            max (&1 + sum(0..k)
              (\j. gen_cond_exp p (FF j)
                (\y. indicator_fn (B (SUC j)) y) x)) (&1)))
       ---> L) sequentially}`
  (LABEL_TAC "CONV_MAX") THENL
  [MATCH_MP_TAC RESCALED_INDICATOR_CONVERGENCE_MAX THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 3: Intersect the two a.e. sets *)
  SUBGOAL_THEN
   `almost_surely p
     ((INTERS {{x:A | &0 <=
       gen_cond_exp p (FF k)
         (\y. indicator_fn ((B:num->A->bool) (SUC k)) y) x} |
       k IN (:num)}) INTER
      {x | ?L. ((\n. sum(0..n)
        (\k. (indicator_fn (B (SUC k)) x -
              gen_cond_exp p (FF k)
                (\y. indicator_fn (B (SUC k)) y) x) /
             max (&1 + sum(0..k)
               (\j. gen_cond_exp p (FF j)
                 (\y. indicator_fn (B (SUC j)) y) x)) (&1)))
        ---> L) sequentially})`
  MP_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  (* Step 4: Use ALMOST_SURELY_SUBSET: on intersection T' = T *)
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
   `(INTERS {{x:A | &0 <=
      gen_cond_exp p (FF k)
        (\y. indicator_fn ((B:num->A->bool) (SUC k)) y) x} |
      k IN (:num)}) INTER
    {x | ?L. ((\n. sum(0..n)
      (\k. (indicator_fn (B (SUC k)) x -
            gen_cond_exp p (FF k)
              (\y. indicator_fn (B (SUC k)) y) x) /
           max (&1 + sum(0..k)
             (\j. gen_cond_exp p (FF j)
               (\y. indicator_fn (B (SUC j)) y) x)) (&1)))
      ---> L) sequentially}` THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_INTER; IN_INTERS; IN_ELIM_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. &0 <= gen_cond_exp p (FF k)
     (\y. indicator_fn ((B:num->A->bool) (SUC k)) y) (x:A)` ASSUME_TAC THENL
  [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC
    `{x:A | &0 <= gen_cond_exp p (FF k)
      (\y. indicator_fn ((B:num->A->bool) (SUC k)) y) x}`) THEN
   REWRITE_TAC[IN_ELIM_THM] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   EXISTS_TAC `k:num` THEN REFL_TAC; ALL_TAC] THEN
  EXISTS_TAC `L:real` THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_TRANSFORM_EVENTUALLY) THEN
  EXISTS_TAC `\n. sum(0..n)
    (\k. (indicator_fn ((B:num->A->bool) (SUC k)) (x:A) -
          gen_cond_exp p (FF k)
            (\y. indicator_fn (B (SUC k)) y) x) /
         max (&1 + sum(0..k)
           (\j. gen_cond_exp p (FF j)
             (\y. indicator_fn (B (SUC j)) y) x)) (&1))` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `max (&1 + sum(0..k)
     (\j. gen_cond_exp p (FF j)
       (\y. indicator_fn ((B:num->A->bool) (SUC j)) y) (x:A))) (&1) =
    &1 + sum(0..k)
     (\j. gen_cond_exp p (FF j)
       (\y. indicator_fn (B (SUC j)) y) x)`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[REAL_ARITH `max a b = a <=> b <= a`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> &1 <= &1 + s`) THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]);;

(* ======================================================================== *)
(* Levy Conditional Borel-Cantelli Lemma:                                   *)
(* For adapted events B_n in F_n, {B_n i.o.} iff sum E[1_{B_{n+1}}|F_n]=oo *)
(* ======================================================================== *)

let LEVY_CONDITIONAL_BOREL_CANTELLI = prove
 (`!p FF (B:num->A->bool).
     filtration p FF /\ (!n. B n IN prob_events p) /\
     (!n. B n SUBSET prob_carrier p) /\ (!n. B n IN FF n)
     ==> almost_surely p
         {x | x IN limsup_events B <=>
              (!M. ?N. &M <= sum(0..N)
                (\k. gen_cond_exp p (FF k)
                  (\y. indicator_fn (B (SUC k)) y) x))}`,
  REPEAT STRIP_TAC THEN
  (* Step 1: v_k >= 0 a.e. *)
  SUBGOAL_THEN
   `almost_surely p
     (INTERS {{x:A | &0 <= gen_cond_exp p (FF k)
       (\y. indicator_fn ((B:num->A->bool) (SUC k)) y) x} | k IN (:num)})`
  (LABEL_TAC "NONNEG_AS") THENL
  [MATCH_MP_TAC ALMOST_SURELY_COUNTABLE_INTER THEN
   GEN_TAC THEN MATCH_MP_TAC GEN_COND_EXP_NONNEG THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[filtration];
    REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC INTEGRABLE_INDICATOR THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  (* Step 2: rescaled sum converges a.e. *)
  SUBGOAL_THEN
   `almost_surely p
     {x:A | ?L. ((\n. sum(0..n)
       (\k. (indicator_fn ((B:num->A->bool) (SUC k)) x -
             gen_cond_exp p (FF k)
               (\y. indicator_fn (B (SUC k)) y) x) /
            (&1 + sum(0..k)
              (\j. gen_cond_exp p (FF j)
                (\y. indicator_fn (B (SUC j)) y) x))))
       ---> L) sequentially}`
  (LABEL_TAC "CONV_AS") THENL
  [MATCH_MP_TAC RESCALED_INDICATOR_CONVERGENCE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: intersect the a.e. sets *)
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC
   `(INTERS {{x:A | &0 <= gen_cond_exp p (FF k)
     (\y. indicator_fn ((B:num->A->bool) (SUC k)) y) x} | k IN (:num)})
    INTER
    {x | ?L. ((\n. sum(0..n)
      (\k. (indicator_fn (B (SUC k)) x -
            gen_cond_exp p (FF k)
              (\y. indicator_fn (B (SUC k)) y) x) /
           (&1 + sum(0..k)
             (\j. gen_cond_exp p (FF j)
               (\y. indicator_fn (B (SUC j)) y) x))))
      ---> L) sequentially}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALMOST_SURELY_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_INTERS] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `L:real` ASSUME_TAC)) THEN
  (* Step 4: extract pointwise nonnegativity *)
  SUBGOAL_THEN
   `!k. &0 <= gen_cond_exp p (FF k)
     (\y:A. indicator_fn ((B:num->A->bool) (SUC k)) y) x`
  (LABEL_TAC "NONNEG") THENL
  [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC
    `{x:A | &0 <= gen_cond_exp p (FF k)
      (\y. indicator_fn ((B:num->A->bool) (SUC k)) y) x}`) THEN
   REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]; ALL_TAC] THEN
  (* Step 5: abbreviate v, establish CONV2, then abbreviate a *)
  ABBREV_TAC
   `v = \k. gen_cond_exp p (FF k)
     (\y:A. indicator_fn ((B:num->A->bool) (SUC k)) y) x` THEN
  SUBGOAL_THEN
   `((\n. sum(0..n) (\k:num. (indicator_fn ((B:num->A->bool) (SUC k)) x -
      (v:num->real) k) / (&1 + sum(0..k) v))) ---> L) sequentially`
  (LABEL_TAC "CONV2") THENL
  [FIRST_X_ASSUM(fun th ->
     if free_in `sequentially` (concl th)
     then MP_TAC th else failwith "") THEN
   EXPAND_TAC "v" THEN REWRITE_TAC[];
   ALL_TAC] THEN
  ABBREV_TAC
   `a = \k:num. (indicator_fn ((B:num->A->bool) (SUC k)) x -
     (v:num->real) k) /
     (&1 + sum(0..k) v)` THEN
  (* Step 6: rewrite limsup with LIMSUP_EVENTS_IFF_SUM_UNBOUNDED *)
  REWRITE_TAC[LIMSUP_EVENTS_IFF_SUM_UNBOUNDED] THEN
  (* Step 7: reindex sum(0..N) to sum(0..SUC N) *)
  SUBGOAL_THEN
   `(!M:num. ?N. &M <= sum(0..N) (\k. indicator_fn ((B:num->A->bool) k) x))
    <=> (!M:num. ?N. &M <= sum(0..SUC N)
      (\k. indicator_fn (B k) x))`
  SUBST1_TAC THENL
  [EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `M:num` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `M:num`) THEN
    DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
    EXISTS_TAC `N0:num` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..N0) (\k. indicator_fn ((B:num->A->bool) k) x)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG] THEN CONJ_TAC THENL
    [ARITH_TAC;
     GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
     COND_CASES_TAC THEN REAL_ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o SPEC `M:num`) THEN
    DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
    EXISTS_TAC `SUC N0` THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  (* Step 8: v k >= 0 and 1 + V_k > 0 *)
  SUBGOAL_THEN `!k. &0 <= (v:num->real) k` ASSUME_TAC THENL
  [GEN_TAC THEN USE_THEN "NONNEG" (MP_TAC o SPEC `k:num`) THEN
   EXPAND_TAC "v" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. &0 < &1 + sum(0..k) (v:num->real)`
  (LABEL_TAC "VP") THENL
  [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> &0 < &1 + s`) THEN
   MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 9: Algebraic identity *)
  SUBGOAL_THEN
   `!k. (a:num->real) k * (&1 + sum(0..k) v) =
     indicator_fn ((B:num->A->bool) (SUC k)) x - v k`
  ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `(a:num->real) k =
     (indicator_fn ((B:num->A->bool) (SUC k)) x - v k) /
     (&1 + sum(0..k) v)` SUBST1_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_DIV_RMUL THEN
   USE_THEN "VP" (MP_TAC o SPEC `k:num`) THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
   `!N. sum(0..SUC N) (\k. indicator_fn ((B:num->A->bool) k) x) =
     indicator_fn (B 0) x + sum(0..N) (v:num->real) +
     sum(0..N) (\k. a k * (&1 + sum(0..k) v))`
  (LABEL_TAC "IDENT") THENL
  [ASM_REWRITE_TAC[] THEN GEN_TAC THEN
   REWRITE_TAC[SUM_SUB_NUMSEG] THEN
   MP_TAC(ISPECL [`\k:num. indicator_fn ((B:num->A->bool) k) x`;
     `0`; `SUC N`] SUM_CLAUSES_LEFT) THEN
   REWRITE_TAC[LE_0] THEN
   DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
   REWRITE_TAC[ARITH_RULE `0 + 1 = 1`] THEN
   SUBGOAL_THEN
    `sum(1..SUC N) (\k:num. indicator_fn ((B:num->A->bool) k) x) =
     sum(0..N) (\k. indicator_fn (B (SUC k)) x)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`1`;
      `\k:num. indicator_fn ((B:num->A->bool) k) x`;
      `0`; `N:num`] SUM_OFFSET) THEN
    REWRITE_TAC[ADD1; ADD_CLAUSES]; ALL_TAC] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  (* Step 10: Apply DECOMPOSITION_UNBOUNDED_IFF *)
  USE_THEN "IDENT" (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`v:num->real`; `a:num->real`;
    `indicator_fn ((B:num->A->bool) 0) x`]
    DECOMPOSITION_UNBOUNDED_IFF) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  SIMP_TAC[]);;

(* ==================================================================== *)
(* UI MARTINGALE CLOSURE THEOREM (Williams Ch 12-13)                    *)
(* ==================================================================== *)

(* Key helper: pointwise truncation identity *)
let TRUNCATION_ABS_DIFF = prove
 (`!x M. &0 <= M ==> abs(x - max (min x M) (--M)) = max (abs x - M) (&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_max; real_min] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC);;

(* Truncation preserves convergence: if X_n -> f then trunc(X_n) -> trunc(f) *)
let TRUNCATION_PRESERVES_LIMIT = prove
 (`!f:num->real g M.
     (f ---> g) sequentially /\ &0 <= M
     ==> ((\n. max (min (f n) M) (--M)) ---> max (min g M) (--M)) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  REWRITE_TAC[real_max; real_min] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC);;

(* Truncation is a random variable *)
let RANDOM_VARIABLE_TRUNCATION = prove
 (`!p:A prob_space f M.
     random_variable p f
     ==> random_variable p (\x. max (min (f x) M) (--M))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_MAX THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_MIN THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[RANDOM_VARIABLE_CONST];
   REWRITE_TAC[RANDOM_VARIABLE_CONST]]);;

(* Truncation is integrable *)
let INTEGRABLE_TRUNCATION = prove
 (`!p:A prob_space f M.
     integrable p f
     ==> integrable p (\x. max (min (f x) M) (--M))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_MAX THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_MIN THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
   REWRITE_TAC[INTEGRABLE_CONST]]);;

(* INTEGRABLE_TAIL_VANISHES already in expectation.ml *)

(* ---- Main theorem: Vitali convergence with a.e. convergence ---- *)

let UI_POINTWISE_L1_AE = prove
 (`!p:A prob_space (X:num->A->real) f.
    uniformly_integrable p X /\ integrable p f /\
    almost_surely p {x | ((\n. X n x) ---> f x) sequentially}
    ==> ((\n. expectation p (\x. abs(X n x - f x))) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. integrable (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL
  [UNDISCH_TAC `uniformly_integrable (p:A prob_space) (X:num->A->real)` THEN
   REWRITE_TAC[uniformly_integrable] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. random_variable (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   UNDISCH_TAC `!n. integrable (p:A prob_space) ((X:num->A->real) n)` THEN
   DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
   REWRITE_TAC[integrable] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (f:A->real)` ASSUME_TAC THENL
  [UNDISCH_TAC `integrable (p:A prob_space) (f:A->real)` THEN
   REWRITE_TAC[integrable] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < e / &3` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  SUBGOAL_THEN `!n:num. &0 <= expectation (p:A prob_space)
    (\x:A. abs((X:num->A->real) n x - (f:A->real) x))` ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. abs(expectation (p:A prob_space)
    (\x:A. abs((X:num->A->real) n x - (f:A->real) x))) =
    expectation p (\x. abs(X n x - f x))`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Get K from UI and tail vanishes for f *)
  UNDISCH_TAC `uniformly_integrable (p:A prob_space) (X:num->A->real)` THEN
  REWRITE_TAC[uniformly_integrable] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `K1:real`) THEN
  MP_TAC(ISPECL [`p:A prob_space`; `f:A->real`] INTEGRABLE_TAIL_VANISHES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  ABBREV_TAC `K = max K1 (&N1)` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
  [EXPAND_TAC "K" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* Tail bounds with K *)
  SUBGOAL_THEN `!n:num. expectation (p:A prob_space)
    (\x:A. max (abs((X:num->A->real) n x) - K) (&0)) < e / &3`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space)
     (\x:A. max (abs((X:num->A->real) n x) - K1) (&0))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_MAX_SUB_CONST THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC INTEGRABLE_MAX_SUB_CONST THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     SUBGOAL_THEN `K1 <= K` (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
     EXPAND_TAC "K" THEN REAL_ARITH_TAC];
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space)
    (\x:A. max (abs((f:A->real) x) - &N1) (&0)) < e / &3`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= expectation (p:A prob_space)
     (\x:A. max (abs((f:A->real) x) - &N1) (&0))` MP_TAC THENL
   [MATCH_MP_TAC EXPECTATION_TAIL_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   UNDISCH_TAC `!n:num. N1 <= n ==>
     abs(expectation (p:A prob_space)
       (\x:A. max (abs((f:A->real) x) - &n) (&0)) - &0) < e / &3` THEN
   DISCH_THEN(MP_TAC o SPEC `N1:num`) THEN
   REWRITE_TAC[LE_REFL; REAL_SUB_RZERO] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `expectation (p:A prob_space)
    (\x:A. max (abs((f:A->real) x) - K) (&0)) < e / &3`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space)
     (\x:A. max (abs((f:A->real) x) - &N1) (&0))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_MAX_SUB_CONST THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC INTEGRABLE_MAX_SUB_CONST THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     SUBGOAL_THEN `&N1 <= K` (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
     EXPAND_TAC "K" THEN REAL_ARITH_TAC];
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Bounded convergence via DOMINATED_CONVERGENCE_AE *)
  SUBGOAL_THEN
    `((\n. expectation (p:A prob_space) (\x:A. min (abs((X:num->A->real) n x -
       (f:A->real) x)) (&2 * K))) ---> &0) sequentially` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 = expectation (p:A prob_space) (\x:A. &0)`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXPECTATION_CONST]; ALL_TAC] THEN
   SUBGOAL_THEN
     `integrable (p:A prob_space) (\x:A. &0) /\
      ((\n. expectation (p:A prob_space) (\x:A. min (abs((X:num->A->real) n x -
       (f:A->real) x)) (&2 * K))) --->
      expectation p (\x:A. &0)) sequentially` MP_TAC THENL
   [ALL_TAC; SIMP_TAC[]] THEN
   MATCH_MP_TAC DOMINATED_CONVERGENCE_AE THEN
   EXISTS_TAC `\x:A. &2 * K` THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_MIN THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[INTEGRABLE_CONST]];
    REWRITE_TAC[INTEGRABLE_CONST];
    GEN_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= M ==> abs(min a M) <= M`) THEN
    ASM_SIMP_TAC[REAL_ABS_POS; REAL_LE_MUL; REAL_POS];
    REWRITE_TAC[RANDOM_VARIABLE_CONST];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= M ==> abs(&0) <= M`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REWRITE_TAC[];
    (* a.e. convergence of min(|X_n-f|, 2K) to 0 *)
    BETA_TAC THEN
    UNDISCH_TAC `almost_surely (p:A prob_space)
      {x:A | ((\n. (X:num->A->real) n x) ---> (f:A->real) x) sequentially}` THEN
    REWRITE_TAC[almost_surely] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{x:A | x IN prob_carrier p /\
      ~(x IN {x | ((\n. (X:num->A->real) n x) ---> (f:A->real) x)
        sequentially})}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `((\n. (X:num->A->real) n x - (f:A->real) x) ---> &0)
      sequentially` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM REALLIM_NULL] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `((\n:num. abs((X:num->A->real) n x - (f:A->real) x)) ---> &0)
      sequentially` ASSUME_TAC THENL
    [MP_TAC(ISPEC `sequentially` REALLIM_ABS) THEN
     DISCH_THEN(MP_TAC o SPECL
       [`\n:num. (X:num->A->real) n x - (f:A->real) x`; `&0`]) THEN
     REWRITE_TAC[REAL_ABS_NUM] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `&0 = min (&0) (&2 * K)` SUBST1_TAC THENL
    [CONV_TAC SYM_CONV THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= M ==> min (&0) M = &0`) THEN
     MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
     ASM_REWRITE_TAC[];
     MATCH_MP_TAC REALLIM_MIN THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; REWRITE_TAC[REALLIM_CONST]]]];
   ALL_TAC] THEN
  (* Combine: E[|X_n-f|] = E[min] + E[max], and bound both parts *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `expectation (p:A prob_space)
    (\x:A. min (abs((X:num->A->real) n x - (f:A->real) x)) (&2 * K)) <
    e / &3` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
   SUBGOAL_THEN `&0 <= expectation (p:A prob_space)
     (\x:A. min (abs((X:num->A->real) n x - (f:A->real) x)) (&2 * K))`
     MP_TAC THENL
   [MATCH_MP_TAC EXPECTATION_POS THEN CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_MIN THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[INTEGRABLE_CONST]];
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= M ==> &0 <= min a M`) THEN
     ASM_SIMP_TAC[REAL_ABS_POS; REAL_LE_MUL; REAL_POS]];
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Split E[|X_n-f|] = E[min] + E[max] *)
  SUBGOAL_THEN `expectation (p:A prob_space)
    (\x:A. abs((X:num->A->real) n x - (f:A->real) x)) =
    expectation p (\x. min (abs(X n x - f x)) (&2 * K)) +
    expectation p (\x. max (abs(X n x - f x) - &2 * K) (&0))`
    SUBST1_TAC THENL
  [MP_TAC(BETA_RULE(ISPECL
    [`p:A prob_space`;
     `\x:A. min (abs((X:num->A->real) n x - (f:A->real) x)) (&2 * K)`;
     `\x:A. max (abs((X:num->A->real) n x - (f:A->real) x) - &2 * K) (&0)`]
    EXPECTATION_ADD)) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_MIN THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ABS THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[INTEGRABLE_CONST]];
     MP_TAC(ISPECL [`p:A prob_space`;
       `\x:A. (X:num->A->real) n x - (f:A->real) x`; `&2 * K`]
       INTEGRABLE_MAX_SUB_CONST) THEN
     ANTS_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SUB THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[]]];
    DISCH_THEN(SUBST1_TAC o GSYM) THEN
    MATCH_MP_TAC EXPECTATION_EXT THEN
    GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Bound the tail via MAX_ABS_SUB_TRIANGLE *)
  SUBGOAL_THEN `expectation (p:A prob_space)
    (\x:A. max (abs((X:num->A->real) n x - (f:A->real) x) - &2 * K) (&0)) <
    &2 * e / &3` MP_TAC THENL
  [MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space)
     (\x:A. max (abs((X:num->A->real) n x) - K) (&0) +
            max (abs((f:A->real) x) - K) (&0))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`;
       `\x:A. (X:num->A->real) n x - (f:A->real) x`; `&2 * K`]
       INTEGRABLE_MAX_SUB_CONST) THEN
     ANTS_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SUB THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[]];
     MP_TAC(BETA_RULE(ISPECL
       [`p:A prob_space`;
        `\x:A. max (abs((X:num->A->real) n x) - K) (&0)`;
        `\x:A. max (abs((f:A->real) x) - K) (&0)`]
       INTEGRABLE_ADD)) THEN
     ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_MAX_SUB_CONST THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[]];
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
     MP_TAC(SPECL [`(X:num->A->real) n x`; `(f:A->real) x`; `K:real`]
       MAX_ABS_SUB_TRIANGLE) THEN REAL_ARITH_TAC];
    SUBGOAL_THEN `expectation (p:A prob_space)
      (\x:A. max (abs((X:num->A->real) n x) - K) (&0) +
             max (abs((f:A->real) x) - K) (&0)) =
      expectation p (\x. max (abs(X n x) - K) (&0)) +
      expectation p (\x. max (abs(f x) - K) (&0))` SUBST1_TAC THENL
    [MP_TAC(BETA_RULE(ISPECL
       [`p:A prob_space`;
        `\x:A. max (abs((X:num->A->real) n x) - K) (&0)`;
        `\x:A. max (abs((f:A->real) x) - K) (&0)`]
       EXPECTATION_ADD)) THEN
     ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_MAX_SUB_CONST THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[th])];
     UNDISCH_TAC `!n:num. expectation (p:A prob_space)
       (\x:A. max (abs((X:num->A->real) n x) - K) (&0)) < e / &3` THEN
     DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
     UNDISCH_TAC `expectation (p:A prob_space)
       (\x:A. max (abs((f:A->real) x) - K) (&0)) < e / &3` THEN
     REAL_ARITH_TAC]];
   UNDISCH_TAC `expectation (p:A prob_space)
     (\x:A. min (abs((X:num->A->real) n x - (f:A->real) x)) (&2 * K)) <
     e / &3` THEN
   REAL_ARITH_TAC]);;

(* Helper: equality from vanishing absolute difference *)
let REAL_EQ_EPSILON = prove
 (`!x y:real. (!e. &0 < e ==> abs(x - y) <= e) ==> x = y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
    `~(&0 < abs(x - y)) ==> x = y`) THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `abs(x - y) / &2`) THEN
  ASM_REAL_ARITH_TAC);;

(* ---- UI Martingale Closure: representation X_n = E[X_inf | F_n] ---- *)

let UI_MARTINGALE_CLOSURE = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real).
    martingale p FF X /\ uniformly_integrable p X
    ==> ?f. integrable p f /\
            almost_surely p {x | ((\n. X n x) ---> f x) sequentially} /\
            ((\n. expectation p (\x. abs(X n x - f x))) ---> &0)
              sequentially /\
            (!n. almost_surely p
              {x | X n x = gen_cond_exp p (FF n) f x})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Extract martingale components *)
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL
  [UNDISCH_TAC `martingale (p:A prob_space) FF (X:num->A->real)` THEN
   REWRITE_TAC[martingale] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) (FF:num->(A->bool)->bool)
    (X:num->A->real)` ASSUME_TAC THENL
  [UNDISCH_TAC `martingale (p:A prob_space) FF (X:num->A->real)` THEN
   REWRITE_TAC[martingale] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. integrable (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL
  [UNDISCH_TAC `martingale (p:A prob_space) FF (X:num->A->real)` THEN
   REWRITE_TAC[martingale] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. sub_sigma_algebra (p:A prob_space)
    ((FF:num->(A->bool)->bool) n)` ASSUME_TAC THENL
  [UNDISCH_TAC `filtration (p:A prob_space) FF` THEN
   REWRITE_TAC[filtration] THEN MESON_TAC[]; ALL_TAC] THEN
  (* Step 1: a.s. convergence via UI_SUBMARTINGALE_CONVERGENCE_AS *)
  SUBGOAL_THEN `submartingale (p:A prob_space) FF (X:num->A->real)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC MARTINGALE_IMP_SUBMARTINGALE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
    `X:num->A->real`] UI_SUBMARTINGALE_CONVERGENCE_AS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Step 2: Extract null set and construct measurable limit function *)
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[almost_surely]) THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `prob_carrier (p:A prob_space) DIFF (N0:A->bool)
    IN prob_events p` ASSUME_TAC THENL
  [MATCH_MP_TAC SIGMA_ALGEBRA_DIFF THEN
   REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `p:A prob_space` PROB_SPACE_SIGMA_ALGEBRA) THEN
    REWRITE_TAC[sigma_algebra] THEN
    REWRITE_TAC[GSYM prob_carrier] THEN MESON_TAC[];
    UNDISCH_TAC `null_event (p:A prob_space) (N0:A->bool)` THEN
    REWRITE_TAC[null_event] THEN MESON_TAC[]];
   ALL_TAC] THEN
  EXISTS_TAC `\x:A. if x IN prob_carrier p DIFF N0
    then reallim sequentially (\n. (X:num->A->real) n x) else &0` THEN
  ABBREV_TAC `f = \x:A. if x IN prob_carrier p DIFF N0
    then reallim sequentially (\n. (X:num->A->real) n x) else &0` THEN
  (* Step 3: Integrability via pointwise limit of UI-dominated sequence *)
  SUBGOAL_THEN `integrable (p:A prob_space) (f:A->real)` ASSUME_TAC THENL
  [MATCH_MP_TAC INTEGRABLE_POINTWISE_LIMIT_UI THEN
   EXISTS_TAC `\n (x:A). (X:num->A->real) n x *
     indicator_fn (prob_carrier (p:A prob_space) DIFF N0) x` THEN
   CONJ_TAC THENL
   [(* Uniform integrability of X_n * 1_{carrier\N0} *)
    REWRITE_TAC[uniformly_integrable] THEN CONJ_TAC THENL
    [GEN_TAC THEN REWRITE_TAC[GSYM ETA_AX] THEN
     MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
     ASM_REWRITE_TAC[ETA_AX];
     ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `uniformly_integrable (p:A prob_space) (X:num->A->real)` THEN
    REWRITE_TAC[uniformly_integrable] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `e:real`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `K:real`) THEN
    EXISTS_TAC `K:real` THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `expectation (p:A prob_space)
      (\x. max (abs((X:num->A->real) n x) - K) (&0))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_MAX_SUB_CONST THEN
      REWRITE_TAC[GSYM ETA_AX] THEN
      MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
      ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC INTEGRABLE_MAX_SUB_CONST THEN ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
      REWRITE_TAC[indicator_fn; REAL_ABS_MUL] THEN
      COND_CASES_TAC THENL
      [REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_RID; REAL_LE_REFL];
       REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_RZERO; REAL_ABS_NUM] THEN
       REAL_ARITH_TAC]];
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* Pointwise convergence: X_n * 1_S -> f on carrier *)
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
   FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN BETA_TAC THEN
   REWRITE_TAC[indicator_fn] THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p DIFF N0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_RID] THEN
    SUBGOAL_THEN `?L. ((\n. (X:num->A->real) n x) ---> L) sequentially`
      MP_TAC THENL
    [UNDISCH_TAC `{x:A | x IN prob_carrier p /\
      ~(x IN {x | ?L. ((\n. (X:num->A->real) n x) ---> L) sequentially})}
      SUBSET N0` THEN
     REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
     UNDISCH_TAC `(x:A) IN prob_carrier p DIFF N0` THEN
     REWRITE_TAC[IN_DIFF] THEN MESON_TAC[];
     ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(SELECT_RULE th)) THEN
    REWRITE_TAC[GSYM reallim];
    ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN REWRITE_TAC[REALLIM_CONST]];
   ALL_TAC] THEN
  (* Step 4: a.s. convergence to f *)
  SUBGOAL_THEN
    `almost_surely (p:A prob_space)
      {x:A | ((\n. (X:num->A->real) n x) ---> (f:A->real) x) sequentially}`
    ASSUME_TAC THENL
  [REWRITE_TAC[almost_surely] THEN
   EXISTS_TAC `N0:A->bool` THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   REWRITE_TAC[] THEN DISCH_TAC THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p DIFF N0` THENL
   [UNDISCH_TAC `~((\n. (X:num->A->real) n x) ---> (f:A->real) x)
      sequentially` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN BETA_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `?L. ((\n. (X:num->A->real) n x) ---> L) sequentially`
      MP_TAC THENL
    [UNDISCH_TAC `{x:A | x IN prob_carrier p /\
      ~(x IN {x | ?L. ((\n. (X:num->A->real) n x) ---> L) sequentially})}
      SUBSET N0` THEN
     REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
     UNDISCH_TAC `(x:A) IN prob_carrier p DIFF N0` THEN
     REWRITE_TAC[IN_DIFF] THEN MESON_TAC[];
     ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(SELECT_RULE th)) THEN
    REWRITE_TAC[GSYM reallim] THEN MESON_TAC[];
    UNDISCH_TAC `(x:A) IN prob_carrier p` THEN
    UNDISCH_TAC `~((x:A) IN prob_carrier p DIFF N0)` THEN
    REWRITE_TAC[IN_DIFF] THEN MESON_TAC[]];
   ALL_TAC] THEN
  (* Step 5: L1 convergence *)
  SUBGOAL_THEN
    `((\n. expectation (p:A prob_space)
        (\x. abs((X:num->A->real) n x - (f:A->real) x))) ---> &0)
      sequentially` ASSUME_TAC THENL
  [MATCH_MP_TAC UI_POINTWISE_L1_AE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 6: Conditional expectation representation *)
  SUBGOAL_THEN
    `!n (a:A->bool). a IN (FF:num->(A->bool)->bool) n ==>
      expectation (p:A prob_space)
        (\x. (X:num->A->real) n x * indicator_fn a x) =
      expectation p (\x. (f:A->real) x * indicator_fn a x)`
    (LABEL_TAC "EQ_COND") THENL
  [(* Key equality: E[X_n * 1_A] = E[f * 1_A] for A in FF_n *)
   (* Proof: martingale property gives E[X_m * 1_A] = E[X_n * 1_A] for m>=n,
      and L1 convergence gives |E[X_m * 1_A] - E[f * 1_A]| -> 0 *)
   REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_EQ_EPSILON THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   (* From L1 convergence, get N with E[|X_m - f|] < e for m >= N *)
   FIRST_X_ASSUM(MP_TAC o
     GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
   REWRITE_TAC[REAL_SUB_RZERO] THEN SIMP_TAC[] THEN
   DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `N:num` ASSUME_TAC) THEN
   (* Choose m = n + N (so m >= n and m >= N) *)
   ABBREV_TAC `m = n + N:num` THEN
   SUBGOAL_THEN `n <= (m:num) /\ N <= m` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ARITH_TAC; ALL_TAC] THEN
   (* From MARTINGALE_TOWER: E[X_m * 1_a] = E[X_n * 1_a] *)
   SUBGOAL_THEN
     `expectation (p:A prob_space)
       (\x. (X:num->A->real) m x * indicator_fn (a:A->bool) x) =
      expectation p (\x. X n x * indicator_fn a x)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`n:num`; `m:num`; `a:A->bool`]
     (REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
       (ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                `X:num->A->real`] MARTINGALE_TOWER))) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* a IN prob_events p *)
   SUBGOAL_THEN `(a:A->bool) IN prob_events (p:A prob_space)` ASSUME_TAC THENL
   [SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space)
      ((FF:num->(A->bool)->bool) n)` MP_TAC THENL
    [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[sub_sigma_algebra] THEN
    ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
   (* Key chain: |E[X_n*1_a] - E[f*1_a]| = |E[X_m*1_a] - E[f*1_a]|
                 <= E[|X_m - f|] < e *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `expectation (p:A prob_space)
     (\x. abs((X:num->A->real) m x - (f:A->real) x))` THEN
   CONJ_TAC THENL
   [(* |E[X_n * 1_a] - E[f * 1_a]| <= E[|X_m - f|] *)
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
      `expectation (p:A prob_space)
        (\x. (X:num->A->real) m x * indicator_fn (a:A->bool) x) -
       expectation p (\x. (f:A->real) x * indicator_fn a x) =
       expectation p (\x. (X m x - f x) * indicator_fn a x)`
      SUBST1_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`;
       `\x:A. (X:num->A->real) m x * indicator_fn (a:A->bool) x`;
       `\x:A. (f:A->real) x * indicator_fn (a:A->bool) x`]
       EXPECTATION_SUB) THEN
     ASM_SIMP_TAC[INTEGRABLE_MUL_INDICATOR_FN; ETA_AX] THEN
     DISCH_THEN(SUBST1_TAC o GSYM) THEN
     AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `expectation (p:A prob_space)
      (\x. abs(((X:num->A->real) m x - (f:A->real) x) *
        indicator_fn (a:A->bool) x))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC EXPECTATION_ABS_LE THEN
     SUBGOAL_THEN
       `(\x:A. ((X:num->A->real) m x - (f:A->real) x) *
         indicator_fn (a:A->bool) x) =
        (\x. X m x * indicator_fn a x - f x * indicator_fn a x)`
       SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC INTEGRABLE_SUB THEN
     ASM_SIMP_TAC[INTEGRABLE_MUL_INDICATOR_FN; ETA_AX];
     ALL_TAC] THEN
    MATCH_MP_TAC EXPECTATION_MONO THEN REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRABLE_ABS THEN
     SUBGOAL_THEN
       `(\x:A. ((X:num->A->real) m x - (f:A->real) x) *
         indicator_fn (a:A->bool) x) =
        (\x. X m x * indicator_fn a x - f x * indicator_fn a x)`
       SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC INTEGRABLE_SUB THEN
     ASM_SIMP_TAC[INTEGRABLE_MUL_INDICATOR_FN; ETA_AX];
     MATCH_MP_TAC INTEGRABLE_ABS THEN
     MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     REWRITE_TAC[indicator_fn; REAL_ABS_MUL] THEN
     COND_CASES_TAC THENL
     [REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_RID; REAL_LE_REFL];
      REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_RZERO; REAL_ABS_POS]]];
    (* E[|X_m - f|] <= e from L1 convergence bound *)
    MATCH_MP_TAC(REAL_ARITH `abs(x:real) < e ==> x <= e`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Now prove the four conclusions *)
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Representation: X_n = E[f | F_n] a.s. *)
  X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC GEN_COND_EXP_AE_UNIQUE THEN
  EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN
  REPEAT CONJ_TAC THENL
  [(* sub_sigma_algebra p (FF n) *)
   ASM_REWRITE_TAC[];
   (* measurable_wrt p (FF n) (X n) -- from adapted *)
   REWRITE_TAC[ETA_AX] THEN
   UNDISCH_TAC `adapted (p:A prob_space) FF (X:num->A->real)` THEN
   REWRITE_TAC[adapted] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
   REWRITE_TAC[];
   (* integrable p (X n) *)
   REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
   (* measurable_wrt p (FF n) (gen_cond_exp p (FF n) f) *)
   REWRITE_TAC[ETA_AX] THEN
   MATCH_MP_TAC GEN_COND_EXP_MEASURABLE_WRT THEN ASM_REWRITE_TAC[];
   (* integrable p (gen_cond_exp p (FF n) f) *)
   REWRITE_TAC[ETA_AX] THEN
   MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
   (* !A. A IN FF n ==> E[X_n * 1_A] = E[gen_cond_exp * 1_A] *)
   X_GEN_TAC `a:A->bool` THEN DISCH_TAC THEN
   (* E[gen_cond_exp p (FF n) f * 1_a] = E[f * 1_a] by conditioning *)
   SUBGOAL_THEN
     `expectation (p:A prob_space)
       (\x. gen_cond_exp p ((FF:num->(A->bool)->bool) n) (f:A->real) x *
            indicator_fn (a:A->bool) x) =
      expectation p (\x. f x * indicator_fn a x)` SUBST1_TAC THENL
   [MATCH_MP_TAC GEN_COND_EXP_CONDITIONING THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Now use our established equality *)
   REMOVE_THEN "EQ_COND" (MP_TAC o SPECL [`n:num`; `a:A->bool`]) THEN
   ASM_REWRITE_TAC[]]);;
