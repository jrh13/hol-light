(* ========================================================================= *)
(* Probability measure spaces: sigma-algebras and probability measures.      *)
(*                                                                           *)
(* Follows Williams "Probability with Martingales" Chapters 1-2.             *)
(* Uses real_sums / ---> / sequentially from Multivariate/realanalysis.ml    *)
(* ========================================================================= *)

needs "100/inclusion_exclusion.ml";;
needs "Library/card.ml";;
needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* Chapter 1: Sigma-algebras and Measure Spaces                              *)
(* ------------------------------------------------------------------------- *)

let sigma_algebra = new_definition
  `sigma_algebra (f:(A->bool)->bool) <=>
   UNIONS f IN f /\
   (!a. a IN f ==> (UNIONS f DIFF a) IN f) /\
   (!s. s SUBSET f /\ COUNTABLE s ==> UNIONS s IN f)`;;

(* Basic properties of sigma-algebras *)

let SIGMA_ALGEBRA_SUBSET = prove
  (`!(f:(A->bool)->bool) a. a IN f ==> a SUBSET UNIONS f`,
   REWRITE_TAC[SUBSET; IN_UNIONS] THEN MESON_TAC[]);;

let SIGMA_ALGEBRA_CARRIER = prove
  (`!(f:(A->bool)->bool). sigma_algebra f ==> UNIONS f IN f`,
   SIMP_TAC[sigma_algebra]);;

let SIGMA_ALGEBRA_EMPTY = prove
  (`!(f:(A->bool)->bool). sigma_algebra f ==> {} IN f`,
   GEN_TAC THEN REWRITE_TAC[sigma_algebra] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `{}:A->bool = UNIONS f DIFF UNIONS f` SUBST1_TAC THENL
   [SET_TAC[]; ASM_MESON_TAC[]]);;

let SIGMA_ALGEBRA_COMPL = prove
  (`!(f:(A->bool)->bool) a.
      sigma_algebra f /\ a IN f ==> (UNIONS f DIFF a) IN f`,
   REWRITE_TAC[sigma_algebra] THEN MESON_TAC[]);;

let SIGMA_ALGEBRA_UNION_COUNTABLE = prove
  (`!(f:(A->bool)->bool) s.
      sigma_algebra f /\ s SUBSET f /\ COUNTABLE s ==> UNIONS s IN f`,
   REWRITE_TAC[sigma_algebra] THEN MESON_TAC[]);;

let SIGMA_ALGEBRA_UNION = prove
  (`!(f:(A->bool)->bool) a b.
      sigma_algebra f /\ a IN f /\ b IN f ==> (a UNION b) IN f`,
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `(a:A->bool) UNION b = UNIONS {a, b}` SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_2]; ALL_TAC] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_UNION_COUNTABLE THEN
   ASM_REWRITE_TAC[COUNTABLE_INSERT; COUNTABLE_EMPTY] THEN
   ASM SET_TAC[]);;

let SIGMA_ALGEBRA_INTER = prove
  (`!(f:(A->bool)->bool) a b.
      sigma_algebra f /\ a IN f /\ b IN f ==> (a INTER b) IN f`,
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `(a:A->bool) INTER b =
     UNIONS f DIFF ((UNIONS f DIFF a) UNION (UNIONS f DIFF b))`
     SUBST1_TAC THENL
   [MP_TAC(ISPECL [`f:(A->bool)->bool`; `a:A->bool`] SIGMA_ALGEBRA_SUBSET) THEN
    MP_TAC(ISPECL [`f:(A->bool)->bool`; `b:A->bool`] SIGMA_ALGEBRA_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC SIGMA_ALGEBRA_COMPL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_UNION THEN
    ASM_SIMP_TAC[SIGMA_ALGEBRA_COMPL]]);;

let SIGMA_ALGEBRA_DIFF = prove
  (`!(f:(A->bool)->bool) a b.
      sigma_algebra f /\ a IN f /\ b IN f ==> (a DIFF b) IN f`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(a:A->bool) DIFF b = a INTER (UNIONS f DIFF b)`
     SUBST1_TAC THENL
   [MP_TAC(ISPECL [`f:(A->bool)->bool`; `a:A->bool`] SIGMA_ALGEBRA_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC SIGMA_ALGEBRA_INTER THEN
    ASM_SIMP_TAC[SIGMA_ALGEBRA_COMPL]]);;

let SIGMA_ALGEBRA_UNIONS_FINITE = prove
  (`!(f:(A->bool)->bool) s.
      sigma_algebra f /\ s SUBSET f /\ FINITE s ==> UNIONS s IN f`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_UNION_COUNTABLE THEN
   ASM_SIMP_TAC[FINITE_IMP_COUNTABLE]);;

let INTERS_COMPL_UNIONS = prove
  (`!(u:A->bool) s.
      ~(s = {}) /\ (!a. a IN s ==> a SUBSET u)
      ==> INTERS s = u DIFF UNIONS (IMAGE (\a. u DIFF a) s)`,
   REPEAT STRIP_TAC THEN
   GEN_REWRITE_TAC I [EXTENSION] THEN
   X_GEN_TAC `x:A` THEN
   REWRITE_TAC[IN_INTERS; IN_DIFF; IN_UNIONS; EXISTS_IN_IMAGE] THEN
   TRY BETA_TAC THEN
   REWRITE_TAC[IN_DIFF] THEN
   ASM_MESON_TAC[MEMBER_NOT_EMPTY; SUBSET]);;

let SIGMA_ALGEBRA_INTERS_FINITE = prove
  (`!(f:(A->bool)->bool) s.
      sigma_algebra f /\ s SUBSET f /\ FINITE s /\ ~(s = {})
      ==> INTERS s IN f`,
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN
     `INTERS s :A->bool = UNIONS f DIFF UNIONS (IMAGE (\a. UNIONS f DIFF a) s)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC INTERS_COMPL_UNIONS THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SIGMA_ALGEBRA_SUBSET THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_COMPL THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_UNIONS_FINITE THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SIGMA_ALGEBRA_COMPL THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM_SIMP_TAC[FINITE_IMAGE]]);;


(* ------------------------------------------------------------------------- *)
(* Probability Spaces as a new type                                          *)
(* Following the pattern of grouptheory.ml / metric.ml                       *)
(* Countable additivity uses N-indexed real_sums from realanalysis.ml        *)
(* ------------------------------------------------------------------------- *)

let prob_space_tybij =
  let eth = prove
   (`?ev:((A->bool)->bool) p:((A->bool)->real).
          sigma_algebra ev /\
          (!a. a IN ev ==> &0 <= p a) /\
          p (UNIONS ev) = &1 /\
          p {} = &0 /\
          (!A:num->A->bool.
             (!n. A n IN ev) /\
             (!i j. ~(i = j) ==> DISJOINT (A i) (A j))
             ==> ((\n. p(A n)) real_sums
                  p(UNIONS {A n | n IN (:num)})) (from 0))`,
    MAP_EVERY EXISTS_TAC
     [`{({ARB:A}):A->bool, ({}:A->bool)}`;
      `(\a:A->bool. if a = {ARB:A} then &1 else &0)`] THEN
    BETA_TAC THEN REWRITE_TAC[sigma_algebra; UNIONS_2; UNION_EMPTY] THEN
    REPEAT CONJ_TAC THENL
    [(* {ARB} IN {{ARB}, {}} *)
     REWRITE_TAC[IN_INSERT];
     (* complement closure *)
     REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
     CONJ_TAC THENL
     [SUBGOAL_THEN `{ARB:A} DIFF {ARB:A} = {}` (fun th -> REWRITE_TAC[th]) THENL
      [SET_TAC[]; REWRITE_TAC[IN_INSERT]];
      REWRITE_TAC[DIFF_EMPTY; IN_INSERT]];
     (* countable union closure *)
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `(UNIONS s:A->bool) SUBSET {ARB:A}` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS {({ARB:A}):A->bool, ({}:A->bool)}` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC SUBSET_UNIONS THEN ASM_REWRITE_TAC[];
       REWRITE_TAC[UNIONS_2; UNION_EMPTY; SUBSET_REFL]];
      ALL_TAC] THEN
     SUBGOAL_THEN `(UNIONS s:A->bool) = {} \/ UNIONS s = {ARB:A}`
       STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[];
      ASM_REWRITE_TAC[IN_INSERT]; ASM_REWRITE_TAC[IN_INSERT]];
     (* positivity *)
     REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN REAL_ARITH_TAC;
     (* p(UNIONS ev) = 1 was simplified away by REWRITE_TAC above *)
     (* p {} = 0 *)
     SUBGOAL_THEN `~({}:A->bool = {ARB:A})` (fun th -> REWRITE_TAC[th]) THEN
     ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[NOT_INSERT_EMPTY];
     (* countable additivity *)
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `!n:num. (A:num->A->bool) n = {} \/ A n = {ARB:A}`
       ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_INSERT; NOT_IN_EMPTY]; ALL_TAC] THEN
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `!n:num. (A:num->A->bool) n = {} \/ A n = {ARB:A}`
       ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_INSERT; NOT_IN_EMPTY]; ALL_TAC] THEN
     ASM_CASES_TAC `?k:num. (A:num->A->bool) k = {ARB:A}` THENL
     [(* Case: some A k = {ARB} *)
      FIRST_X_ASSUM(X_CHOOSE_TAC `k:num`) THEN
      SUBGOAL_THEN `!n:num. ~(n = k) ==> (A:num->A->bool) n = {}`
        ASSUME_TAC THENL
      [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
       FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `k:num`]) THEN
       ASM_REWRITE_TAC[DISJOINT] THEN SET_TAC[];
       ALL_TAC] THEN
      SUBGOAL_THEN
        `UNIONS {(A:num->A->bool) n | n IN (:num)} = {ARB:A}`
        SUBST1_TAC THENL
      [REWRITE_TAC[UNIONS_GSPEC; IN_UNIV; EXTENSION; IN_ELIM_THM;
                   IN_SING] THEN
       GEN_TAC THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
        ASM_CASES_TAC `n:num = k` THENL
        [ASM_REWRITE_TAC[IN_SING];
         FIRST_X_ASSUM(fun th ->
           MP_TAC(MATCH_MP th (ASSUME `~(n:num = k)`))) THEN
         DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NOT_IN_EMPTY]];
        DISCH_TAC THEN EXISTS_TAC `k:num` THEN
        ASM_REWRITE_TAC[IN_SING]];
       ALL_TAC] THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_SERIES_SUM THEN
      EXISTS_TAC `{k:num}` THEN REPEAT CONJ_TAC THENL
      [REWRITE_TAC[FINITE_SING];
       REWRITE_TAC[FROM_0; SUBSET_UNIV];
       X_GEN_TAC `x:num` THEN REWRITE_TAC[IN_SING] THEN DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
       DISCH_THEN SUBST1_TAC THEN
       SUBGOAL_THEN `~({}:A->bool = {ARB:A})` (fun th -> REWRITE_TAC[th]) THEN
       ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[NOT_INSERT_EMPTY];
       REWRITE_TAC[SUM_SING] THEN ASM_REWRITE_TAC[]];
      (* Case: all A n = {} *)
      SUBGOAL_THEN `!n:num. (A:num->A->bool) n = {}` ASSUME_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `UNIONS {(A:num->A->bool) n | n IN (:num)} = {}`
        SUBST1_TAC THENL
      [REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_UNIV; IN_ELIM_THM;
                   NOT_IN_EMPTY] THEN
       ASM_REWRITE_TAC[NOT_IN_EMPTY];
       ALL_TAC] THEN
      SUBGOAL_THEN `~({}:A->bool = {ARB:A})` ASSUME_TAC THENL
      [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[NOT_INSERT_EMPTY];
       ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MESON_TAC[REAL_SERIES_0]]]) in
  new_type_definition "prob_space" ("prob_space","prob_space_operations")
   (GEN_REWRITE_RULE DEPTH_CONV [EXISTS_UNPAIR_THM] eth);;

let prob_events = new_definition
  `prob_events (p:(A)prob_space) = FST(prob_space_operations p)`;;

let prob = new_definition
  `prob (p:(A)prob_space) = SND(prob_space_operations p)`;;

let prob_carrier = new_definition
  `prob_carrier (p:(A)prob_space) = UNIONS(prob_events p)`;;

(* Extract the fundamental properties via the type bijection *)
let PROB_SPACE_EXTRACT = MATCH_MP(MESON[]
  `(!a. mk(dest a) = a) /\ (!r. P r <=> dest(mk r) = r)
   ==> !a. P(dest a)`) prob_space_tybij;;

let PROB_SPACE_SIGMA_ALGEBRA = prove
  (`!p:A prob_space. sigma_algebra (prob_events p)`,
   GEN_TAC THEN
   MP_TAC(SPEC `p:A prob_space` PROB_SPACE_EXTRACT) THEN
   REWRITE_TAC[prob_events; prob] THEN
   SIMP_TAC[]);;

let PROB_POSITIVE = prove
  (`!p:A prob_space a. a IN prob_events p ==> &0 <= prob p a`,
   GEN_TAC THEN
   MP_TAC(SPEC `p:A prob_space` PROB_SPACE_EXTRACT) THEN
   REWRITE_TAC[prob_events; prob] THEN
   SIMP_TAC[]);;

let PROB_SPACE = prove
  (`!p:A prob_space. prob p (prob_carrier p) = &1`,
   GEN_TAC THEN
   MP_TAC(SPEC `p:A prob_space` PROB_SPACE_EXTRACT) THEN
   REWRITE_TAC[prob_carrier; prob_events; prob] THEN
   SIMP_TAC[]);;

let PROB_EMPTY = prove
  (`!p:A prob_space. prob p {} = &0`,
   GEN_TAC THEN
   MP_TAC(SPEC `p:A prob_space` PROB_SPACE_EXTRACT) THEN
   REWRITE_TAC[prob_events; prob] THEN
   SIMP_TAC[]);;

let PROB_COUNTABLY_ADDITIVE = prove
  (`!p:A prob_space A.
      (!n. A n IN prob_events p) /\
      (!i j. ~(i = j) ==> DISJOINT (A i) (A j))
      ==> ((\n. prob p (A n)) real_sums
           prob p (UNIONS {A n | n IN (:num)})) (from 0)`,
   GEN_TAC THEN
   MP_TAC(SPEC `p:A prob_space` PROB_SPACE_EXTRACT) THEN
   REWRITE_TAC[prob_events; prob] THEN
   SIMP_TAC[]);;

(* The sample space is an event *)
let PROB_CARRIER_IN_EVENTS = prove
  (`!p:A prob_space. prob_carrier p IN prob_events p`,
   GEN_TAC THEN REWRITE_TAC[prob_carrier] THEN
   MP_TAC(SPEC `p:A prob_space` PROB_SPACE_SIGMA_ALGEBRA) THEN
   REWRITE_TAC[sigma_algebra] THEN MESON_TAC[]);;

(* The empty set is an event *)
let PROB_EMPTY_IN_EVENTS = prove
  (`!p:A prob_space. {} IN prob_events p`,
   GEN_TAC THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY THEN
   REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA]);;

(* Complements are events *)
let PROB_COMPL_IN_EVENTS = prove
  (`!p:A prob_space a. a IN prob_events p
      ==> (prob_carrier p DIFF a) IN prob_events p`,
   REWRITE_TAC[prob_carrier] THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_COMPL THEN
   ASM_REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA]);;

(* Unions of events are events *)
let PROB_UNION_IN_EVENTS = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p
      ==> (a UNION b) IN prob_events p`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_UNION THEN
   ASM_REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA]);;

(* Intersections of events are events *)
let PROB_INTER_IN_EVENTS = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p
      ==> (a INTER b) IN prob_events p`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_INTER THEN
   ASM_REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA]);;

(* Differences of events are events *)
let PROB_DIFF_IN_EVENTS = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p
      ==> (a DIFF b) IN prob_events p`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SIGMA_ALGEBRA_DIFF THEN
   ASM_REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA]);;

(* Events are subsets of the sample space *)
let PROB_EVENT_SUBSET = prove
  (`!p:A prob_space a. a IN prob_events p ==> a SUBSET prob_carrier p`,
   REWRITE_TAC[prob_carrier; SUBSET; IN_UNIONS] THEN MESON_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Finite additivity - derived from countable additivity                     *)
(* ------------------------------------------------------------------------- *)

let PROB_ADDITIVE = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p /\ DISJOINT a b
      ==> prob p (a UNION b) = prob p a + prob p b`,
   REPEAT STRIP_TAC THEN
   (* Use countable additivity with A 0 = a, A 1 = b, A n = {} for n >= 2 *)
   MP_TAC(SPECL [`p:A prob_space`;
                 `(\n. if n = 0 then a
                       else if n = 1 then b
                       else ({}:A->bool)):num->A->bool`]
          PROB_COUNTABLY_ADDITIVE) THEN
   TRY BETA_TAC THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [X_GEN_TAC `n:num` THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[PROB_EMPTY_IN_EVENTS];
     (* Pairwise disjointness *)
     MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN
     ASM_CASES_TAC `i = 0` THEN ASM_CASES_TAC `j = 0` THENL
     [ASM_MESON_TAC[];
      ASM_CASES_TAC `j = 1` THEN ASM_REWRITE_TAC[DISJOINT_EMPTY] THEN
      ASM_REWRITE_TAC[];
      ASM_CASES_TAC `i = 1` THEN ASM_REWRITE_TAC[DISJOINT_EMPTY] THEN
      ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[];
      ASM_CASES_TAC `i = 1` THENL
      [ASM_CASES_TAC `j = 1` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
       ASM_REWRITE_TAC[DISJOINT_EMPTY];
       ASM_CASES_TAC `j = 1` THENL
       [ASM_REWRITE_TAC[DISJOINT_EMPTY]; ASM_REWRITE_TAC[DISJOINT_EMPTY]]]]];
    ALL_TAC] THEN
   (* Simplify UNIONS *)
   SUBGOAL_THEN
     `UNIONS {(if n = 0 then a
               else if n = 1 then b
               else ({}:A->bool)) | n IN (:num)} = a UNION b`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[UNIONS_GSPEC; IN_UNIV; EXTENSION; IN_ELIM_THM; IN_UNION;
                NOT_IN_EMPTY] THEN
    GEN_TAC THEN EQ_TAC THENL
    [DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
     COND_CASES_TAC THENL
     [MESON_TAC[];
      COND_CASES_TAC THENL
      [MESON_TAC[];
       REWRITE_TAC[NOT_IN_EMPTY]]];
     STRIP_TAC THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `1` THEN ASM_REWRITE_TAC[ARITH_EQ]]];
    ALL_TAC] THEN
   DISCH_TAC THEN
   (* Also show the series sums to prob a + prob b via REAL_SERIES_SUM *)
   SUBGOAL_THEN
     `((\n. prob p (if n = 0 then a
                    else if n = 1 then b
                    else ({}:A->bool))) real_sums
      (prob p a + prob p b)) (from 0)`
     (fun h2 -> FIRST_X_ASSUM(fun h1 ->
        ACCEPT_TAC(MATCH_MP REAL_SERIES_UNIQUE (CONJ h1 h2)))) THEN
   (* Prove via eventually constant partial sums *)
   REWRITE_TAC[real_sums; FROM_0; INTER_UNIV] THEN
   MATCH_MP_TAC REALLIM_EVENTUALLY THEN
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
   EXISTS_TAC `1` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
   MP_TAC(SPECL [`\n. prob (p:A prob_space) (if n = 0 then a
                   else if n = 1 then b else ({}:A->bool))`;
                  `0`; `N:num`] SUM_CLAUSES_LEFT) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   TRY BETA_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[] THEN
   MP_TAC(SPECL [`\n. prob (p:A prob_space) (if n = 0 then a
                   else if n = 1 then b else ({}:A->bool))`;
                  `1`; `N:num`] SUM_CLAUSES_LEFT) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   TRY BETA_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[] THEN
   SUBGOAL_THEN `sum (2..N) (\n. prob (p:A prob_space)
     (if n = 0 then a else if n = 1 then b else ({}:A->bool))) = &0`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(i = 0) /\ ~(i = 1)` (fun th -> REWRITE_TAC[th]) THENL
    [ASM_ARITH_TAC; REWRITE_TAC[PROB_EMPTY]];
    REAL_ARITH_TAC]);;


(* Probability of complement *)
let PROB_COMPL = prove
  (`!p:A prob_space a.
      a IN prob_events p ==> prob p (prob_carrier p DIFF a) = &1 - prob p a`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `a:A->bool SUBSET prob_carrier p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PROB_EVENT_SUBSET]; ALL_TAC] THEN
   SUBGOAL_THEN
     `prob p (prob_carrier p:A->bool) =
      prob p a + prob p (prob_carrier p DIFF a)`
     MP_TAC THENL
   [SUBGOAL_THEN `prob_carrier p = a UNION (prob_carrier p DIFF a:A->bool)`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
    [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC PROB_ADDITIVE THEN
    ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS] THEN
    REWRITE_TAC[DISJOINT] THEN ASM SET_TAC[];
    REWRITE_TAC[PROB_SPACE] THEN REAL_ARITH_TAC]);;

(* Probability is at most 1 *)
let PROB_LE_1 = prove
  (`!p:A prob_space a. a IN prob_events p ==> prob p a <= &1`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `&1 = prob p a + prob p (prob_carrier p DIFF a:A->bool)`
     MP_TAC THENL
   [ASM_SIMP_TAC[PROB_COMPL] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> &1 = x + y ==> x <= &1`) THEN
    MATCH_MP_TAC PROB_POSITIVE THEN
    ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS]]);;

(* Monotonicity of probability *)
let PROB_MONO = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p /\ a SUBSET b
      ==> prob p a <= prob p b`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `b = a UNION (b DIFF a:A->bool)` SUBST1_TAC THENL
   [ASM SET_TAC[];
    SUBGOAL_THEN
      `prob p (a UNION (b DIFF a):A->bool) = prob p a + prob p (b DIFF a)`
      SUBST1_TAC THENL
    [MATCH_MP_TAC PROB_ADDITIVE THEN
     ASM_SIMP_TAC[PROB_DIFF_IN_EVENTS] THEN SET_TAC[];
     MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN
     MATCH_MP_TAC PROB_POSITIVE THEN
     ASM_SIMP_TAC[PROB_DIFF_IN_EVENTS]]]);;


(* ------------------------------------------------------------------------- *)
(* Inclusion-exclusion for two events                                        *)
(* ------------------------------------------------------------------------- *)

let PROB_UNION = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p
      ==> prob p (a UNION b) = prob p a + prob p b - prob p (a INTER b)`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `a UNION b = a UNION (b DIFF a):A->bool`
     SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `prob p (a UNION (b DIFF a):A->bool) = prob p a + prob p (b DIFF a)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC PROB_ADDITIVE THEN
    ASM_SIMP_TAC[PROB_DIFF_IN_EVENTS] THEN SET_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `prob p (b:A->bool) = prob p (a INTER b) + prob p (b DIFF a)`
     MP_TAC THENL
   [SUBGOAL_THEN `b = (a INTER b) UNION (b DIFF a):A->bool`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
    [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC PROB_ADDITIVE THEN
    ASM_SIMP_TAC[PROB_INTER_IN_EVENTS; PROB_DIFF_IN_EVENTS] THEN SET_TAC[];
    REAL_ARITH_TAC]);;

(* Inclusion-exclusion for three events *)

let PROB_UNION_3 = prove
  (`!p:A prob_space a b c.
      a IN prob_events p /\ b IN prob_events p /\ c IN prob_events p
      ==> prob p (a UNION b UNION c) =
          prob p a + prob p b + prob p c -
          prob p (a INTER b) - prob p (a INTER c) - prob p (b INTER c) +
          prob p (a INTER b INTER c)`,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `a:A->bool`; `b UNION c:A->bool`]
     PROB_UNION) THEN
   ASM_SIMP_TAC[PROB_UNION_IN_EVENTS] THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `b:A->bool`; `c:A->bool`]
     PROB_UNION) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `(a:A->bool) INTER (b UNION c) = (a INTER b) UNION (a INTER c)`
     SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `a INTER b:A->bool`; `a INTER c:A->bool`]
     PROB_UNION) THEN
   ASM_SIMP_TAC[PROB_INTER_IN_EVENTS] THEN
   SUBGOAL_THEN `((a:A->bool) INTER b) INTER (a INTER c) = a INTER (b INTER c)`
     (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
   REAL_ARITH_TAC);;

let PROB_SUBADDITIVE = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p
      ==> prob p (a UNION b) <= prob p a + prob p b`,
   REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC[PROB_UNION] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= z ==> x + y - z <= x + y`) THEN
   MATCH_MP_TAC PROB_POSITIVE THEN
   ASM_SIMP_TAC[PROB_INTER_IN_EVENTS]);;

let PROB_SUBADDITIVE_3 = prove
  (`!p:A prob_space a b c.
      a IN prob_events p /\ b IN prob_events p /\ c IN prob_events p
      ==> prob p (a UNION b UNION c) <= prob p a + prob p b + prob p c`,
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PROB_UNION_3] THEN
   MATCH_MP_TAC(REAL_ARITH
     `&0 <= ac /\ &0 <= bc /\ abc <= ab
      ==> a + b + c - ab - ac - bc + abc <= a + b + c`) THEN
   ASM_SIMP_TAC[PROB_POSITIVE; PROB_INTER_IN_EVENTS] THEN
   MATCH_MP_TAC PROB_MONO THEN
   ASM_SIMP_TAC[PROB_INTER_IN_EVENTS] THEN SET_TAC[]);;

(* General inclusion-exclusion for finite families of events *)

let PROB_INCLUSION_EXCLUSION = prove
  (`!p:A prob_space A.
      FINITE A /\ A SUBSET prob_events p
      ==> prob p (UNIONS A) =
          sum {B | B SUBSET A /\ ~(B = {})}
              (\B. (-- &1) pow (CARD B + 1) * prob p (INTERS B))`,
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC INCLUSION_EXCLUSION_REAL_RESTRICTED THEN
   EXISTS_TAC `\s:A->bool. s IN prob_events p` THEN
   ASM_REWRITE_TAC[PROB_EMPTY_IN_EVENTS] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PROB_ADDITIVE THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THENL
    [MATCH_MP_TAC PROB_INTER_IN_EVENTS;
     MATCH_MP_TAC PROB_UNION_IN_EVENTS;
     MATCH_MP_TAC PROB_DIFF_IN_EVENTS] THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

(* Boole's inequality for finite families of events *)

let PROB_SUBADDITIVE_FINITE = prove
  (`!p:A prob_space A.
      FINITE A /\ A SUBSET prob_events p
      ==> prob p (UNIONS A) <= sum A (prob p)`,
   GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
   MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_0; SUM_CLAUSES; PROB_EMPTY; REAL_LE_REFL];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[UNIONS_INSERT; SUM_CLAUSES] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `prob p (x:A->bool) + prob p (UNIONS A)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC PROB_SUBADDITIVE THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC SIGMA_ALGEBRA_UNIONS_FINITE THEN
     ASM_REWRITE_TAC[PROB_SPACE_SIGMA_ALGEBRA] THEN ASM SET_TAC[];
     MATCH_MP_TAC REAL_LE_LADD_IMP THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]]);;

let PROB_DIFF = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p
      ==> prob p (a DIFF b) = prob p a - prob p (a INTER b)`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `a:A->bool = (a INTER b) UNION (a DIFF b)` MP_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
   DISCH_THEN(fun th ->
     MP_TAC(AP_TERM `prob (p:A prob_space)` th)) THEN
   SUBGOAL_THEN
     `prob p ((a INTER b) UNION (a DIFF b):A->bool) =
      prob p (a INTER b) + prob p (a DIFF b)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC PROB_ADDITIVE THEN
    ASM_SIMP_TAC[PROB_INTER_IN_EVENTS; PROB_DIFF_IN_EVENTS] THEN SET_TAC[];
    REAL_ARITH_TAC]);;

let PROB_DIFF_SUBSET = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p /\ a SUBSET b
      ==> prob p (b DIFF a) = prob p b - prob p a`,
   REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC[PROB_DIFF] THEN
   AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

(* Countable unions of events are events *)
let PROB_COUNTABLE_UNION_IN_EVENTS = prove
  (`!p:A prob_space s.
      s SUBSET prob_events p /\ COUNTABLE s
      ==> UNIONS s IN prob_events p`,
   REPEAT STRIP_TAC THEN
   MP_TAC(SPEC `p:A prob_space` PROB_SPACE_SIGMA_ALGEBRA) THEN
   REWRITE_TAC[sigma_algebra] THEN
   STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]);;

let PROB_FINITE_UNION_IN_EVENTS = prove
  (`!p:A prob_space s.
      s SUBSET prob_events p /\ FINITE s
      ==> UNIONS s IN prob_events p`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN
   ASM_SIMP_TAC[FINITE_IMP_COUNTABLE]);;

let PROB_COUNTABLE_INTERS_IN_EVENTS = prove
  (`!p:A prob_space s.
      s SUBSET prob_events p /\ COUNTABLE s /\ ~(s = {})
      ==> INTERS s IN prob_events p`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `INTERS s:A->bool =
      prob_carrier p DIFF UNIONS (IMAGE (\a. prob_carrier p DIFF a) s)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC INTERS_COMPL_UNIONS THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PROB_EVENT_SUBSET; SUBSET];
    ALL_TAC] THEN
   MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
   MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN
   ASM_SIMP_TAC[COUNTABLE_IMAGE] THEN
   REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
   ASM_MESON_TAC[SUBSET]);;


(* ------------------------------------------------------------------------- *)
(* Conditional Probability                                                   *)
(* ------------------------------------------------------------------------- *)

let cond_prob = new_definition
  `cond_prob (p:(A)prob_space) a b = prob p (a INTER b) / prob p b`;;

let BAYES_THEOREM = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p /\
      ~(prob p a = &0) /\ ~(prob p b = &0)
      ==> cond_prob p a b * prob p b = cond_prob p b a * prob p a`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[cond_prob] THEN
   SUBGOAL_THEN
     `prob p ((a:A->bool) INTER b) / prob p b * prob p b =
      prob p (a INTER b)` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `prob p ((b:A->bool) INTER a) / prob p a * prob p a =
      prob p (b INTER a)` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[INTER_COMM]);;

let COND_PROB_BOUNDS = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p /\ &0 < prob p b
      ==> &0 <= cond_prob p a b /\ cond_prob p a b <= &1`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[cond_prob] THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[PROB_POSITIVE; PROB_INTER_IN_EVENTS; REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN
    MATCH_MP_TAC PROB_MONO THEN
    ASM_SIMP_TAC[PROB_INTER_IN_EVENTS] THEN SET_TAC[]]);;

let PROB_TOTAL_TWO = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p /\
      a UNION b = prob_carrier p /\ DISJOINT a b
      ==> !c. c IN prob_events p
              ==> prob p c = prob p (c INTER a) + prob p (c INTER b)`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `c:A->bool = (c INTER a) UNION (c INTER b)` MP_TAC THENL
   [SUBGOAL_THEN `c SUBSET prob_carrier (p:A prob_space)` MP_TAC THENL
    [MATCH_MP_TAC PROB_EVENT_SUBSET THEN ASM_REWRITE_TAC[];
     ASM SET_TAC[]];
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    MATCH_MP_TAC PROB_ADDITIVE THEN
    ASM_SIMP_TAC[PROB_INTER_IN_EVENTS] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DISJOINT]) THEN
    SET_TAC[]]);;

(* Probability-zero closure under union *)
let PROB_ZERO_UNION = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p /\
      prob p a = &0 /\ prob p b = &0
      ==> prob p (a UNION b) = &0`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `a:A->bool`; `b:A->bool`]
      PROB_SUBADDITIVE) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC PROB_POSITIVE THEN
    ASM_SIMP_TAC[PROB_UNION_IN_EVENTS]]);;

(* Probability-one closure under intersection *)
let PROB_ONE_INTER = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p /\
      prob p a = &1 /\ prob p b = &1
      ==> prob p (a INTER b) = &1`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PROB_LE_1 THEN
    ASM_SIMP_TAC[PROB_INTER_IN_EVENTS];
    MP_TAC(ISPECL [`p:A prob_space`; `a:A->bool`; `b:A->bool`]
      PROB_UNION) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `a UNION b:A->bool`]
      PROB_LE_1) THEN
    ASM_SIMP_TAC[PROB_UNION_IN_EVENTS] THEN REAL_ARITH_TAC]);;

(* P(A)=0 implies P(A INTER B) = 0 *)
let PROB_ZERO_INTER = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p /\ prob p a = &0
      ==> prob p (a INTER b) = &0`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `a INTER b:A->bool`; `a:A->bool`]
      PROB_MONO) THEN
    ASM_SIMP_TAC[PROB_INTER_IN_EVENTS; INTER_SUBSET];
    MATCH_MP_TAC PROB_POSITIVE THEN
    ASM_SIMP_TAC[PROB_INTER_IN_EVENTS]]);;

(* P(A)=1 implies P(A UNION B) = 1 *)
let PROB_ONE_UNION = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p /\ prob p a = &1
      ==> prob p (a UNION b) = &1`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PROB_LE_1 THEN ASM_SIMP_TAC[PROB_UNION_IN_EVENTS];
    MP_TAC(ISPECL [`p:A prob_space`; `a:A->bool`; `a UNION b:A->bool`]
      PROB_MONO) THEN
    ASM_SIMP_TAC[PROB_UNION_IN_EVENTS; SUBSET_UNION]]);;

(* Bonferroni inequality: P(A INTER B) >= P(A) + P(B) - 1 *)
let PROB_INTER_LOWER_BOUND = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p
      ==> prob p a + prob p b - &1 <= prob p (a INTER b)`,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `a:A->bool`; `b:A->bool`]
     PROB_UNION) THEN
   MP_TAC(ISPECL [`p:A prob_space`; `a UNION b:A->bool`]
     PROB_LE_1) THEN
   ASM_SIMP_TAC[PROB_UNION_IN_EVENTS] THEN REAL_ARITH_TAC);;

(* Symmetric difference: P(A Delta B) = P(A) + P(B) - 2*P(A INTER B) *)
let PROB_SYMMETRIC_DIFFERENCE = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p
      ==> prob p ((a DIFF b) UNION (b DIFF a)) =
          prob p a + prob p b - &2 * prob p (a INTER b)`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `DISJOINT (a DIFF b) (b DIFF a:A->bool)` ASSUME_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `a DIFF b:A->bool`; `b DIFF a:A->bool`]
     PROB_ADDITIVE) THEN
   ASM_SIMP_TAC[PROB_DIFF_IN_EVENTS] THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `a:A->bool`; `b:A->bool`] PROB_DIFF) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `b:A->bool`; `a:A->bool`] PROB_DIFF) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `b INTER a = a INTER b:A->bool` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;


