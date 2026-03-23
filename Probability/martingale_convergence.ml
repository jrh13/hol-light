(* ========================================================================= *)
(* Martingale convergence: upcrossing inequality, convergence theorem,       *)
(* sigma-atoms, and conditional expectation.                                 *)
(*                                                                           *)
(* Follows Williams "Probability with Martingales" Chapters 11-12.           *)
(* Includes Doob's upcrossing inequality, martingale convergence theorem,    *)
(* sigma-atom decomposition, and simple conditional expectation.             *)
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

(* Helper: submartingale property extends to (X - a) * indicator *)
let SUBMARTINGALE_SUB_CONST_STEP = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) (c:real).
     submartingale p FF X ==>
     !(n:num) (s:A->bool). s IN FF n ==>
       simple_expectation p (\x. (X n x - c) * indicator_fn s x) <=
       simple_expectation p (\x. (X (SUC n) x - c) * indicator_fn s x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!k. simple_rv (p:A prob_space) ((X:num->A->real) k)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:A->bool) IN prob_events (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale; filtration; sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
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
  [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
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
let SUBMARTINGALE_POS_PART_STEP = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) (a:real).
     submartingale p FF X ==>
     !(n:num) (s:A->bool). s IN FF n ==>
       simple_expectation p (\x. pos_part (X n x - a) * indicator_fn s x) <=
       simple_expectation p (\x. pos_part (X (SUC n) x - a) * indicator_fn s x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  (* Extract key facts from submartingale *)
  SUBGOAL_THEN `!k. simple_rv (p:A prob_space) ((X:num->A->real) k)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space) ((FF:num->(A->bool)->bool) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
  SUBGOAL_THEN `sigma_algebra ((FF:num->(A->bool)->bool) n)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:A->bool) IN prob_events (p:A prob_space)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
  (* X n is FF n-measurable *)
  SUBGOAL_THEN `measurable_wrt (p:A prob_space) ((FF:num->(A->bool)->bool) n) (X n)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale; simple_adapted; adapted]; ALL_TAC] THEN
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
  [(* Left: SUBMARTINGALE_SUB_CONST_STEP *)
   MP_TAC(SPECL [`a:real`; `n:num`; `s_plus:A->bool`]
     (MATCH_MP SUBMARTINGALE_SUB_CONST_STEP
       (ASSUME `submartingale (p:A prob_space)
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
     submartingale p FF X /\ a < b ==>
     !n. simple_rv p
           (\x. not_bet_gain (\k. pos_part(X k x - a)) (&0) (b - a) n) /\
         &0 <= simple_expectation p
           (\x. not_bet_gain (\k. pos_part(X k x - a)) (&0) (b - a) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) (FF:num->(A->bool)->bool)
    (X:num->A->real)` ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale; simple_adapted; adapted]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. simple_rv (p:A prob_space) ((X:num->A->real) k)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
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
      SUBMARTINGALE_POS_PART_STEP) THEN
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
       RANDOM_VARIABLE_GE) THEN
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
let DOOB_UPCROSSING_INEQUALITY = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b n.
     submartingale p FF X /\ a < b ==>
     (b - a) * simple_expectation p (\x. &(num_upcrossings X a b n x))
     <= simple_expectation p (\x. pos_part(X n x - a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Extract submartingale components *)
  SUBGOAL_THEN `filtration (p:A prob_space) (FF:num->(A->bool)->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[submartingale; simple_adapted]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. simple_rv (p:A prob_space) ((X:num->A->real) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
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

(* Expected upcrossings bounded for bounded submartingale *)
let UPCROSSING_EXPECTATION_BOUND = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b n M.
     submartingale p FF X /\ a < b /\
     (!m x. x IN prob_carrier p ==> abs(X m x) <= M)
     ==> (b - a) * simple_expectation p (\x. &(num_upcrossings X a b n x))
         <= M + abs(a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                `X:num->A->real`; `a:real`; `b:real`; `n:num`]
    DOOB_UPCROSSING_INEQUALITY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!m:num. simple_rv (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
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
let NUM_UPCROSSINGS_GE_EVENT = prove
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
  MATCH_MP_TAC RANDOM_VARIABLE_GE THEN
  ASM_MESON_TAC[simple_rv]);;

(* Key MCT lemma: P(U_n >= k) <= (M + |a|) / ((b-a)*k) *)
let UPCROSSING_PROB_BOUND = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b n M k.
     submartingale p FF X /\ a < b /\
     (!m x. x IN prob_carrier p ==> abs(X m x) <= M) /\
     0 < k
     ==> prob p {x | x IN prob_carrier p /\
                     &(num_upcrossings X a b n x) >= &k}
         <= (M + abs(a)) / ((b - a) * &k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!m:num. simple_rv (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
    [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)`
    ASSUME_TAC THENL
    [ASM_MESON_TAC[submartingale; simple_adapted]; ALL_TAC] THEN
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
     UPCROSSING_EXPECTATION_BOUND) THEN
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
let INFINITE_UPCROSSINGS_NULL = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b M.
     submartingale p FF X /\ a < b /\
     (!m x. x IN prob_carrier p ==> abs(X m x) <= M)
     ==> !k. 0 < k ==>
         prob p (UNIONS {
           {x | x IN prob_carrier p /\ &(num_upcrossings X a b n x) >= &k}
         | n IN (:num)}) <= (M + abs(a)) / ((b - a) * &k)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PROB_UNIONS_INCREASING_BOUND THEN
  SUBGOAL_THEN `!m:num. simple_rv (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
    [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)` ASSUME_TAC THENL
    [ASM_MESON_TAC[submartingale; simple_adapted]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [(* A n IN events *)
   GEN_TAC THEN MATCH_MP_TAC NUM_UPCROSSINGS_GE_EVENT THEN
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
                   `M:real`; `k:num`] UPCROSSING_PROB_BOUND) THEN
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

(* Finite upcrossings a.s. for bounded submartingale, fixed a < b *)
let FINITE_UPCROSSINGS_AS = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) a b M.
     submartingale p FF X /\ a < b /\
     (!m x. x IN prob_carrier p ==> abs(X m x) <= M)
     ==> almost_surely p
           {x | ?B:num. !n. num_upcrossings X a b n x <= B}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[almost_surely] THEN
  SUBGOAL_THEN `!m:num. simple_rv (p:A prob_space) ((X:num->A->real) m)`
    ASSUME_TAC THENL [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `filtration (p:A prob_space) FF` ASSUME_TAC THENL
    [ASM_MESON_TAC[submartingale]; ALL_TAC] THEN
  SUBGOAL_THEN `adapted (p:A prob_space) FF (X:num->A->real)` ASSUME_TAC THENL
    [ASM_MESON_TAC[submartingale; simple_adapted]; ALL_TAC] THEN
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
    GEN_TAC THEN MATCH_MP_TAC NUM_UPCROSSINGS_GE_EVENT THEN
    EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
    (* P = 0 *)
    MATCH_MP_TAC REAL_EQ_0_FROM_INV_BOUND THEN
    EXISTS_TAC `(M + abs(a:real)) / (b - a)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC PROB_POSITIVE THEN
     MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN
     GEN_TAC THEN MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
     GEN_TAC THEN MATCH_MP_TAC NUM_UPCROSSINGS_GE_EVENT THEN
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
       GEN_TAC THEN MATCH_MP_TAC NUM_UPCROSSINGS_GE_EVENT THEN
       EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
       GEN_TAC THEN MATCH_MP_TAC NUM_UPCROSSINGS_GE_EVENT THEN
       EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
       SET_TAC[]];
      (* P(UNIONS) <= C / SUC j *)
      SUBGOAL_THEN `(M + abs(a:real)) / (b - a) / &(SUC j) =
                     (M + abs a) / ((b - a) * &(SUC j))`
        SUBST1_TAC THENL
      [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC]; ALL_TAC] THEN
      MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                      `X:num->A->real`; `a:real`; `b:real`; `M:real`]
        INFINITE_UPCROSSINGS_NULL) THEN
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

(* ========================================================================= *)
(* MARTINGALE CONVERGENCE THEOREM (bounded submartingale version)            *)
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

(* Main theorem: bounded submartingale converges almost surely *)
let MARTINGALE_CONVERGENCE_BOUNDED = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) M.
     submartingale p FF X /\
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
   [(* Case a < b: use FINITE_UPCROSSINGS_AS + ALMOST_SURELY_SUBSET *)
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x:A | ?B. !n. num_upcrossings (X:num->A->real)
                  ((g:num->real)(NUMFST k)) (g(NUMSND k)) n x <= B}` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC FINITE_UPCROSSINGS_AS THEN
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
let EXPECTATION_MUL_INDICATOR_ZERO_PROB = prove
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
                   `sigma_atom G (x:A)`] EXPECTATION_MUL_INDICATOR_ZERO_PROB) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
                   `sigma_atom G (x:A)`] EXPECTATION_MUL_INDICATOR_ZERO_PROB) THEN
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
(* HELPER LEMMAS FOR DOOB DECOMPOSITION                                      *)
(* ========================================================================= *)

