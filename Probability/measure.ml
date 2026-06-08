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

(* Closure under countable (non-empty) intersection: the De Morgan dual of     *)
(* SIGMA_ALGEBRA_UNION_COUNTABLE, mirroring SIGMA_ALGEBRA_INTERS_FINITE.        *)
let SIGMA_ALGEBRA_INTERS_COUNTABLE = prove
  (`!(f:(A->bool)->bool) s.
      sigma_algebra f /\ s SUBSET f /\ COUNTABLE s /\ ~(s = {})
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
   MATCH_MP_TAC SIGMA_ALGEBRA_UNION_COUNTABLE THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SIGMA_ALGEBRA_COMPL THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM_SIMP_TAC[COUNTABLE_IMAGE]]);;

(* Closure under symmetric difference. *)
let SIGMA_ALGEBRA_SYM_DIFF = prove
  (`!(f:(A->bool)->bool) a b.
      sigma_algebra f /\ a IN f /\ b IN f
      ==> ((a DIFF b) UNION (b DIFF a)) IN f`,
   REPEAT STRIP_TAC THEN MATCH_MP_TAC SIGMA_ALGEBRA_UNION THEN
   ASM_SIMP_TAC[SIGMA_ALGEBRA_DIFF]);;

(* The Borel sets of any topology form a sigma-algebra (in the sense of this  *)
(* development).  borel_in and its theory now live in Multivariate/metric.ml; *)
(* this connection to our sigma_algebra predicate stays here since            *)
(* sigma_algebra is defined above.                                            *)

let BOREL_IN_SIGMA_ALGEBRA = prove
 (`!top:A topology. sigma_algebra {s | borel_in top s}`,
  GEN_TAC THEN REWRITE_TAC[sigma_algebra; IN_ELIM_THM] THEN
  SUBGOAL_THEN `UNIONS {s:A->bool | borel_in top s} = topspace top`
    (fun th -> REWRITE_TAC[th]) THENL
  [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM; BOREL_IN_SUBSET_TOPSPACE];
    MATCH_MP_TAC(SET_RULE `(x:A->bool) IN s ==> x SUBSET UNIONS s`) THEN
    REWRITE_TAC[IN_ELIM_THM; BOREL_IN_TOPSPACE]];
   REWRITE_TAC[BOREL_IN_TOPSPACE; borel_in_RULES] THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC BOREL_IN_UNIONS THEN
   ASM_REWRITE_TAC[] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
   ASM_MESON_TAC[]]);;

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


(* ========================================================================= *)
(* Signed measures and positive/negative sets                                *)
(* ========================================================================= *)

(* A signed measure is a countably additive real-valued set function with    *)
(* mu({}) = 0. Unlike a probability measure, it can take negative values.    *)

let signed_measure = new_definition
  `signed_measure (p:A prob_space) (mu:(A->bool)->real) <=>
   mu {} = &0 /\
   (!A. (!n. A n IN prob_events p) /\
        (!i j. ~(i = j) ==> DISJOINT (A i) (A j))
        ==> ((\n. mu(A n)) real_sums mu(UNIONS {A n | n IN (:num)})) (from 0))`;;

(* A positive set for mu: every measurable subset has nonneg mu-measure *)
let positive_set = new_definition
  `positive_set (p:A prob_space) (mu:(A->bool)->real) (A:A->bool) <=>
   A IN prob_events p /\
   (!B. B IN prob_events p /\ B SUBSET A ==> &0 <= mu B)`;;

(* A negative set for mu: every measurable subset has nonpos mu-measure *)
let negative_set = new_definition
  `negative_set (p:A prob_space) (mu:(A->bool)->real) (A:A->bool) <=>
   A IN prob_events p /\
   (!B. B IN prob_events p /\ B SUBSET A ==> mu B <= &0)`;;

let SIGNED_MEASURE_EMPTY = prove
 (`!p:A prob_space mu. signed_measure p mu ==> mu {} = &0`,
  SIMP_TAC[signed_measure]);;

(* Finite additivity for signed measures - follows PROB_ADDITIVE pattern *)
let SIGNED_MEASURE_FINITELY_ADDITIVE = prove
 (`!p:A prob_space mu a b.
     signed_measure p mu /\
     a IN prob_events p /\ b IN prob_events p /\ DISJOINT a b
     ==> mu(a UNION b) = mu a + mu b`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [signed_measure]) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `(\n. if n = 0 then a
          else if n = 1 then b
          else ({}:A->bool)):num->A->bool`) THEN
  TRY BETA_TAC THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[PROB_EMPTY_IN_EVENTS];
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
  SUBGOAL_THEN
    `((\n. (mu:(A->bool)->real) (if n = 0 then a
                   else if n = 1 then b
                   else ({}:A->bool))) real_sums
     (mu a + mu b)) (from 0)`
    (fun h2 -> FIRST_X_ASSUM(fun h1 ->
       ACCEPT_TAC(MATCH_MP REAL_SERIES_UNIQUE (CONJ h1 h2)))) THEN
  REWRITE_TAC[real_sums; FROM_0; INTER_UNIV] THEN
  MATCH_MP_TAC REALLIM_EVENTUALLY THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `1` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`\n. (mu:(A->bool)->real) (if n = 0 then a
                  else if n = 1 then b else ({}:A->bool))`;
                 `0`; `N:num`] SUM_CLAUSES_LEFT) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  TRY BETA_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN
  MP_TAC(SPECL [`\n. (mu:(A->bool)->real) (if n = 0 then a
                  else if n = 1 then b else ({}:A->bool))`;
                 `1`; `N:num`] SUM_CLAUSES_LEFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  TRY BETA_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `sum (2..N) (\n. (mu:(A->bool)->real)
    (if n = 0 then a else if n = 1 then b else ({}:A->bool))) = &0`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
   X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   SUBGOAL_THEN `~(i = 0) /\ ~(i = 1)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
   REAL_ARITH_TAC]);;

(* Difference formula for signed measures *)
let SIGNED_MEASURE_DIFF = prove
 (`!p:A prob_space mu a b.
     signed_measure p mu /\
     a IN prob_events p /\ b IN prob_events p /\ b SUBSET a
     ==> mu(a DIFF b) = mu a - mu b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `mu:(A->bool)->real`;
                 `b:A->bool`; `a DIFF b:A->bool`]
         SIGNED_MEASURE_FINITELY_ADDITIVE) THEN
  SUBGOAL_THEN `b UNION (a DIFF b) = a:A->bool` SUBST1_TAC THENL
  [ASM SET_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
  [ASM_SIMP_TAC[PROB_DIFF_IN_EVENTS] THEN SET_TAC[];
   DISCH_THEN(fun th -> MP_TAC th) THEN REAL_ARITH_TAC]);;

(* Every probability measure is a signed measure *)
let PROB_IS_SIGNED_MEASURE = prove
 (`!p:A prob_space. signed_measure p (prob p)`,
  GEN_TAC THEN REWRITE_TAC[signed_measure; PROB_EMPTY] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[]
    (ISPEC `p:A prob_space` PROB_COUNTABLY_ADDITIVE)) THEN
  ASM_REWRITE_TAC[]);;

let POSITIVE_SET_EMPTY = prove
 (`!p:A prob_space mu. signed_measure p mu ==> positive_set p mu {}`,
  REWRITE_TAC[positive_set; PROB_EMPTY_IN_EVENTS] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `B = {}:A->bool` SUBST1_TAC THENL
  [ASM SET_TAC[]; ASM_MESON_TAC[signed_measure; REAL_LE_REFL]]);;

let NEGATIVE_SET_EMPTY = prove
 (`!p:A prob_space mu. signed_measure p mu ==> negative_set p mu {}`,
  REWRITE_TAC[negative_set; PROB_EMPTY_IN_EVENTS] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `B = {}:A->bool` SUBST1_TAC THENL
  [ASM SET_TAC[]; ASM_MESON_TAC[signed_measure; REAL_LE_REFL]]);;

let POSITIVE_SET_SUBSET = prove
 (`!p:A prob_space mu A B.
     positive_set p mu A /\ B IN prob_events p /\ B SUBSET A
     ==> positive_set p mu B`,
  REWRITE_TAC[positive_set] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let NEGATIVE_SET_SUBSET = prove
 (`!p:A prob_space mu A B.
     negative_set p mu A /\ B IN prob_events p /\ B SUBSET A
     ==> negative_set p mu B`,
  REWRITE_TAC[negative_set] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Union of two positive sets is positive *)
let POSITIVE_SET_UNION = prove
 (`!p:A prob_space mu A B.
     signed_measure p mu /\ positive_set p mu A /\ positive_set p mu B
     ==> positive_set p mu (A UNION B)`,
  REWRITE_TAC[positive_set] THEN REPEAT STRIP_TAC THENL
  [ASM_SIMP_TAC[PROB_UNION_IN_EVENTS]; ALL_TAC] THEN
  SUBGOAL_THEN
    `B' = (B' INTER A) UNION (B' INTER (B DIFF A)):A->bool` SUBST1_TAC THENL
  [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `B' INTER A IN prob_events (p:A prob_space)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[PROB_INTER_IN_EVENTS]; ALL_TAC] THEN
  SUBGOAL_THEN `B' INTER (B DIFF A) IN prob_events (p:A prob_space)`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[PROB_INTER_IN_EVENTS; PROB_DIFF_IN_EVENTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `mu:(A->bool)->real`;
                 `B' INTER A:A->bool`; `B' INTER (B DIFF A):A->bool`]
         SIGNED_MEASURE_FINITELY_ADDITIVE) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
  [SUBGOAL_THEN `B' INTER A SUBSET A:A->bool`
     (fun th -> ASM_MESON_TAC[th]) THEN SET_TAC[];
   SUBGOAL_THEN `B' INTER (B DIFF A) SUBSET B:A->bool`
     (fun th -> ASM_MESON_TAC[th]) THEN SET_TAC[]]);;

(* Union of two negative sets is negative *)
let NEGATIVE_SET_UNION = prove
 (`!p:A prob_space mu A B.
     signed_measure p mu /\ negative_set p mu A /\ negative_set p mu B
     ==> negative_set p mu (A UNION B)`,
  REWRITE_TAC[negative_set] THEN REPEAT STRIP_TAC THENL
  [ASM_SIMP_TAC[PROB_UNION_IN_EVENTS]; ALL_TAC] THEN
  SUBGOAL_THEN
    `B' = (B' INTER A) UNION (B' INTER (B DIFF A)):A->bool` SUBST1_TAC THENL
  [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `B' INTER A IN prob_events (p:A prob_space)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[PROB_INTER_IN_EVENTS]; ALL_TAC] THEN
  SUBGOAL_THEN `B' INTER (B DIFF A) IN prob_events (p:A prob_space)`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[PROB_INTER_IN_EVENTS; PROB_DIFF_IN_EVENTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `mu:(A->bool)->real`;
                 `B' INTER A:A->bool`; `B' INTER (B DIFF A):A->bool`]
         SIGNED_MEASURE_FINITELY_ADDITIVE) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a <= &0 /\ b <= &0 ==> a + b <= &0`) THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN `B' INTER A SUBSET A:A->bool`
     (fun th -> ASM_MESON_TAC[th]) THEN SET_TAC[];
   SUBGOAL_THEN `B' INTER (B DIFF A) SUBSET B:A->bool`
     (fun th -> ASM_MESON_TAC[th]) THEN SET_TAC[]]);;

(* ---------------------------------------------------------------------- *)
(*  Phase 2: Countable union of positive sets, monotonicity, extraction    *)
(* ---------------------------------------------------------------------- *)

let IMAGE_NUMSEG_IN_EVENTS = prove
 (`!p:A prob_space A n.
     (!m. A m IN prob_events p)
     ==> UNIONS(IMAGE A (0..n)) IN prob_events p`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
  CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
   SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG]]);;

let POSITIVE_SET_COUNTABLE_UNION = prove
 (`!p:A prob_space mu A.
     signed_measure p mu /\ (!n. positive_set p mu (A n))
     ==> positive_set p mu (UNIONS {A n | n IN (:num)})`,
  REWRITE_TAC[positive_set] THEN REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN
   CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SIMPLE_IMAGE] THEN
    MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. (A:num->A->bool) n IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
    `D = \n:num. B INTER ((A:num->A->bool) n DIFF
                  UNIONS {A j | j:num < n}):A->bool` THEN
  SUBGOAL_THEN `!n:num. (D:num->A->bool) n IN prob_events p` ASSUME_TAC THENL
  [X_GEN_TAC `n:num` THEN EXPAND_TAC "D" THEN
   MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
   CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (A:num->A->bool) {j:num | j < n}` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG_LT];
     REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_IMAGE; IN_ELIM_THM] THEN
     MESON_TAC[]]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i j. ~(i = j) ==> DISJOINT ((D:num->A->bool) i) (D j)` ASSUME_TAC THENL
  [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN
   EXPAND_TAC "D" THEN
   REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_DIFF;
               UNIONS_GSPEC; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN
   REWRITE_TAC[TAUT `~((a /\ b /\ ~c) /\ d /\ e /\ ~f) <=>
     a /\ b /\ d /\ e ==> c \/ f`] THEN
   STRIP_TAC THEN
   DISJ_CASES_TAC(SPECL [`i:num`; `j:num`] LT_CASES) THENL
   [DISJ2_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
    [DISJ1_TAC THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
     ASM_MESON_TAC[]]];
   ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {(D:num->A->bool) n | n IN (:num)} = B` ASSUME_TAC THENL
  [EXPAND_TAC "D" THEN
   REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV;
               IN_INTER; IN_DIFF] THEN
   X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [MESON_TAC[]; ALL_TAC] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN `?m:num. (x:A) IN A m` MP_TAC THENL
   [UNDISCH_TAC `B SUBSET UNIONS {(A:num->A->bool) n | n IN (:num)}` THEN
    UNDISCH_TAC `(x:A) IN B` THEN
    REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
   DISCH_TAC THEN
   MP_TAC(SPEC `\n:num. (x:A) IN A n` MINIMAL) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(fun th ->
     EXISTS_TAC `(minimal) (\n:num. (x:A) IN A n)` THEN MP_TAC th) THEN
   REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN
   ASM_MESON_TAC[NOT_LT];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. (D:num->A->bool) n SUBSET A n` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "D" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. &0 <= mu((D:num->A->bool) n)` ASSUME_TAC THENL
  [GEN_TAC THEN
   FIRST_ASSUM(MP_TAC o CONJUNCT2 o SPEC `n:num`) THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [signed_measure]) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `D:num->A->bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\n:num. &0:real`; `\n:num. mu((D:num->A->bool) n):real`;
                 `from 0`; `&0:real`; `mu(B:A->bool):real`]
         REAL_SERIES_LE) THEN
  ASM_REWRITE_TAC[REAL_SERIES_0] THEN
  ANTS_TAC THENL
  [REWRITE_TAC[IN_FROM] THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
   REAL_ARITH_TAC]);;

let POSITIVE_SET_MONOTONE = prove
 (`!p:A prob_space mu A B.
     signed_measure p mu /\ positive_set p mu A /\
     B IN prob_events p /\ B SUBSET A
     ==> &0 <= mu B /\ mu B <= mu A`,
  REWRITE_TAC[positive_set] THEN REPEAT STRIP_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `mu:(A->bool)->real`;
                 `A:A->bool`; `B:A->bool`] SIGNED_MEASURE_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= mu(A DIFF B:A->bool)` MP_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_SIMP_TAC[PROB_DIFF_IN_EVENTS] THEN SET_TAC[];
   ASM_REAL_ARITH_TAC]);;

(* If S is not a positive set, there exists a measurable subset with measure
   bounded below by -inv(&(k+1)) for some k. *)
let NOT_POSITIVE_HAS_NEG_INV = prove
 (`!p:A prob_space mu S.
     S IN prob_events p /\ ~(positive_set p mu S)
     ==> ?k D:A->bool. D IN prob_events p /\ D SUBSET S /\
         (mu:(A->bool)->real) D <= --inv(&(k + 1))`,
  REWRITE_TAC[positive_set] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
    REWRITE_RULE[DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < --((mu:(A->bool)->real) B)` MP_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `n - 1` THEN EXISTS_TAC `B:A->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&(n - 1 + 1) = &n` SUBST1_TAC THENL
  [ASM_SIMP_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_SUB;
                ARITH_RULE `~(n = 0) ==> 1 <= n`] THEN
   REAL_ARITH_TAC;
   ASM_REAL_ARITH_TAC]);;

(* Key extraction lemma: from any set A with mu(A) > 0, we can extract a
   positive subset B with mu(B) > 0. Uses recursive construction with
   the "minimal k" trick to ensure the extracted subsets are bounded. *)
let EXTRACT_POSITIVE_SUBSET = prove
 (`!p:A prob_space mu A.
     signed_measure p mu /\ A IN prob_events p /\ &0 < mu A
     ==> ?B. B IN prob_events p /\ B SUBSET A /\
             positive_set p mu B /\ &0 < mu B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `positive_set (p:A prob_space) mu (A:A->bool)` THENL
  [EXISTS_TAC `A:A->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
   ASM_MESON_TAC[positive_set];
   ALL_TAC] THEN
  (* Build recursive sequence R(0)=A, R(n+1) = R(n) minus extracted neg set *)
  MP_TAC(ISPECL
    [`A:A->bool`;
     `\(S:A->bool) (n:num).
       if (?k:num. ?C:A->bool. C IN prob_events (p:A prob_space) /\
           C SUBSET S /\ (mu:(A->bool)->real) C <= --inv(&(k + 1)))
       then S DIFF (@D:A->bool. D IN prob_events p /\ D SUBSET S /\
                    mu D <= --inv(&((minimal)
                      (\k:num. ?E:A->bool. E IN prob_events p /\
                               E SUBSET S /\ mu E <= --inv(&(k + 1))) + 1)))
       else S`]
    num_RECURSION) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:num->A->bool` STRIP_ASSUME_TAC) THEN
  (* Abbreviate the "bad predicate" for set S *)
  ABBREV_TAC
    `hasneg = \S:A->bool.
       ?k:num. ?C:A->bool. C IN prob_events (p:A prob_space) /\
       C SUBSET S /\ (mu:(A->bool)->real) C <= --inv(&(k + 1))` THEN
  (* Key property: when hasneg(R n), the @-selected set satisfies specs *)
  SUBGOAL_THEN
    `!n:num. (hasneg:(A->bool)->bool)((R:num->A->bool) n)
     ==> (@D:A->bool. D IN prob_events p /\ D SUBSET R n /\
           (mu:(A->bool)->real) D <= --inv(&((minimal)
             (\k. ?E:A->bool. E IN prob_events p /\ E SUBSET R n /\
                   mu E <= --inv(&(k + 1))) + 1)))
         IN prob_events p /\
         (@D:A->bool. D IN prob_events p /\ D SUBSET R n /\
           mu D <= --inv(&((minimal)
             (\k. ?E:A->bool. E IN prob_events p /\ E SUBSET R n /\
                   mu E <= --inv(&(k + 1))) + 1)))
         SUBSET R n /\
         mu(@D:A->bool. D IN prob_events p /\ D SUBSET R n /\
              mu D <= --inv(&((minimal)
                (\k. ?E:A->bool. E IN prob_events p /\ E SUBSET R n /\
                      mu E <= --inv(&(k + 1))) + 1)))
         <= --inv(&((minimal)
              (\k. ?E:A->bool. E IN prob_events p /\ E SUBSET R n /\
                    mu E <= --inv(&(k + 1))) + 1))`
    ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "hasneg" THEN REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC(fst(EQ_IMP_RULE(REWRITE_RULE[]
     (SPEC `\k:num. ?E:A->bool. E IN prob_events (p:A prob_space) /\
       E SUBSET (R:num->A->bool) n /\
       (mu:(A->bool)->real) E <= --inv(&(k + 1))` MINIMAL)))) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   STRIP_TAC THEN
   MP_TAC(ISPECL
     [`\D:A->bool. D IN prob_events (p:A prob_space) /\
       D SUBSET (R:num->A->bool) n /\
       (mu:(A->bool)->real) D <= --inv(&((minimal)
         (\k:num. ?E:A->bool. E IN prob_events p /\ E SUBSET R n /\
               mu E <= --inv(&(k + 1))) + 1))`;
      `E:A->bool`] SELECT_AX) THEN
   REWRITE_TAC[] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* R(n) in events and R(n) SUBSET A *)
  SUBGOAL_THEN
    `!n:num. (R:num->A->bool) n IN prob_events p /\ R n SUBSET A`
    ASSUME_TAC THENL
  [INDUCT_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL];
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
    [SUBGOAL_THEN `hasneg((R:num->A->bool) n):bool` ASSUME_TAC THENL
     [EXPAND_TAC "hasneg" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN ASM_MESON_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `(R:num->A->bool) n` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
     ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  (* R(SUC n) SUBSET R n *)
  SUBGOAL_THEN `!n:num. (R:num->A->bool)(SUC n) SUBSET R n`
    ASSUME_TAC THENL
  [GEN_TAC THEN ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN REWRITE_TAC[SUBSET_REFL] THEN SET_TAC[];
   ALL_TAC] THEN
  (* Monotonicity: m <= n ==> R n SUBSET R m *)
  SUBGOAL_THEN `!m n:num. m <= n ==> (R:num->A->bool) n SUBSET R m`
    ASSUME_TAC THENL
  [GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LE] THEN DISCH_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL];
    REWRITE_TAC[LE] THEN STRIP_TAC THENL
    [ASM_REWRITE_TAC[SUBSET_REFL];
     MATCH_MP_TAC SUBSET_TRANS THEN
     EXISTS_TAC `(R:num->A->bool) n` THEN ASM_SIMP_TAC[]]];
   ALL_TAC] THEN
  (* Define C(n) = R(n) \ R(n+1) *)
  ABBREV_TAC `C = \n:num. (R:num->A->bool) n DIFF R(SUC n)` THEN
  (* C(n) in events *)
  SUBGOAL_THEN `!n:num. (C:num->A->bool) n IN prob_events p`
    ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "C" THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* C(i), C(j) pairwise disjoint *)
  SUBGOAL_THEN
    `!i j:num. ~(i = j) ==> DISJOINT ((C:num->A->bool) i) (C j)`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "C" THEN REWRITE_TAC[] THEN
   REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_DIFF; NOT_IN_EMPTY] THEN
   X_GEN_TAC `x:A` THEN
   REWRITE_TAC[TAUT `~((a /\ ~b) /\ c /\ ~d) <=> a /\ c ==> b \/ d`] THEN
   STRIP_TAC THEN
   DISJ_CASES_TAC(SPECL [`i:num`; `j:num`] LT_CASES) THENL
   [DISJ1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`SUC i`; `j:num`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
    [DISJ2_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`SUC j`; `i:num`]) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
     ASM_MESON_TAC[]]];
   ALL_TAC] THEN
  (* C(n) SUBSET A *)
  SUBGOAL_THEN `!n:num. (C:num->A->bool) n SUBSET A` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "C" THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(R:num->A->bool) n` THEN
   ASM_REWRITE_TAC[] THEN SET_TAC[];
   ALL_TAC] THEN
  (* Series convergence: sum(mu(C n)) = mu(UNIONS{C n}) *)
  SUBGOAL_THEN
    `((\n. (mu:(A->bool)->real)((C:num->A->bool) n))
      real_sums mu(UNIONS {C n | n IN (:num)})) (from 0)`
    ASSUME_TAC THENL
  [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [signed_measure]) THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `C:num->A->bool`) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* UNIONS{C n} in events *)
  ABBREV_TAC `UC = UNIONS {(C:num->A->bool) n | n IN (:num)}` THEN
  SUBGOAL_THEN `(UC:A->bool) IN prob_events p` ASSUME_TAC THENL
  [EXPAND_TAC "UC" THEN
   MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN
   CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SIMPLE_IMAGE] THEN
    MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]];
   ALL_TAC] THEN
  SUBGOAL_THEN `UC SUBSET A:A->bool` ASSUME_TAC THENL
  [EXPAND_TAC "UC" THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* A DIFF UC is in events *)
  SUBGOAL_THEN `A DIFF UC IN prob_events (p:A prob_space)` ASSUME_TAC THENL
  [MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* A DIFF UC SUBSET R(n) for all n *)
  SUBGOAL_THEN `!n:num. A DIFF UC SUBSET (R:num->A->bool) n`
    ASSUME_TAC THENL
  [INDUCT_TAC THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN R(n:num)` ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF];
     ALL_TAC] THEN
    ASM_CASES_TAC `(x:A) IN R(SUC n):A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((x:A) IN UC:A->bool)` THEN REWRITE_TAC[] THEN
    EXPAND_TAC "UC" THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `n:num` THEN
    SUBGOAL_THEN `(C:num->A->bool) n = R n DIFF R(SUC n)`
      SUBST1_TAC THENL
    [EXPAND_TAC "C" THEN REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_DIFF]];
   ALL_TAC] THEN
  (* mu(C n) <= 0 for all n *)
  SUBGOAL_THEN `!n:num. (mu:(A->bool)->real)((C:num->A->bool) n) <= &0`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `(C:num->A->bool) n = R n DIFF R(SUC n)` SUBST1_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o
     check(fun th -> is_forall(concl th) && is_eq(snd(dest_forall(concl th))))) THEN
   REWRITE_TAC[] THEN
   COND_CASES_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC) THEN
    SUBGOAL_THEN `hasneg((R:num->A->bool) n):bool` ASSUME_TAC THENL
    [EXPAND_TAC "hasneg" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
      `(R:num->A->bool) n DIFF (R n DIFF (@D:A->bool. D IN prob_events p /\ D SUBSET R n /\
        (mu:(A->bool)->real) D <= --inv(&((minimal)
          (\k. ?E:A->bool. E IN prob_events p /\ E SUBSET R n /\
                mu E <= --inv(&(k + 1))) + 1)))) =
       R n INTER (@D:A->bool. D IN prob_events p /\ D SUBSET R n /\
        mu D <= --inv(&((minimal)
          (\k. ?E:A->bool. E IN prob_events p /\ E SUBSET R n /\
                mu E <= --inv(&(k + 1))) + 1)))`
      SUBST1_TAC THENL
    [SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o
      check(fun th -> can (find_term
        (fun t -> is_var t && fst(dest_var t) = "hasneg")) (concl th) &&
        is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
      `(R:num->A->bool) n INTER (@D:A->bool. D IN prob_events p /\ D SUBSET R n /\
        (mu:(A->bool)->real) D <= --inv(&((minimal)
          (\k. ?E:A->bool. E IN prob_events p /\ E SUBSET R n /\
                mu E <= --inv(&(k + 1))) + 1))) =
       (@D:A->bool. D IN prob_events p /\ D SUBSET R n /\
        mu D <= --inv(&((minimal)
          (\k. ?E:A->bool. E IN prob_events p /\ E SUBSET R n /\
                mu E <= --inv(&(k + 1))) + 1)))`
      SUBST1_TAC THENL
    [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < y ==> x <= --y ==> x <= &0`) THEN
    MATCH_MP_TAC REAL_LT_INV THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC) THEN
    SUBGOAL_THEN `(R:num->A->bool) n DIFF R n = {}:A->bool`
      SUBST1_TAC THENL
    [SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [signed_measure]) THEN
    SIMP_TAC[] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* mu(UC) <= 0 *)
  SUBGOAL_THEN `(mu:(A->bool)->real) UC <= &0` ASSUME_TAC THENL
  [MP_TAC(ISPECL
    [`\n:num. (mu:(A->bool)->real)((C:num->A->bool) n)`;
     `\n:num. &0:real`;
     `from 0`; `(mu:(A->bool)->real)(UC:A->bool)`; `&0:real`]
    REAL_SERIES_LE) THEN
   ASM_REWRITE_TAC[REAL_SERIES_0] THEN
   ANTS_TAC THENL
   [REWRITE_TAC[IN_FROM] THEN GEN_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[];
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* mu(A DIFF UC) = mu(A) - mu(UC) *)
  SUBGOAL_THEN `(mu:(A->bool)->real)(A DIFF UC:A->bool) = mu(A:A->bool) - mu(UC:A->bool)`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `mu:(A->bool)->real`;
                  `A:A->bool`; `UC:A->bool`] SIGNED_MEASURE_DIFF) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Now prove B = A DIFF UC satisfies all conditions *)
  EXISTS_TAC `A DIFF UC:A->bool` THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  (* mu(B) > 0 *)
  CONJ_TAC THENL
  [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  (* B is positive: proof by contradiction *)
  REWRITE_TAC[positive_set] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `E:A->bool` THEN STRIP_TAC THEN
  (* Assume mu(E) < 0 and derive contradiction *)
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  (* E SUBSET R(n) for all n *)
  SUBGOAL_THEN `!n:num. (E:A->bool) SUBSET (R:num->A->bool) n`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `A DIFF UC:A->bool` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Find m with mu(E) <= -inv(&(m+1)) *)
  SUBGOAL_THEN `&0 < --((mu:(A->bool)->real) E)` MP_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(mu:(A->bool)->real) E <= --inv(&m)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* For all n: hasneg(R n) because E SUBSET R(n) and mu(E) < 0 *)
  SUBGOAL_THEN `!n:num. hasneg((R:num->A->bool) n):bool` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "hasneg" THEN REWRITE_TAC[] THEN
   EXISTS_TAC `m - 1` THEN EXISTS_TAC `E:A->bool` THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `&(m - 1 + 1) = &m` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_SUB;
                 ARITH_RULE `~(m = 0) ==> 1 <= m`] THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* For all n: the minimal k for R(n) is <= m-1 *)
  SUBGOAL_THEN
    `!n:num. (minimal)(\k. ?D:A->bool. D IN prob_events (p:A prob_space) /\
       D SUBSET (R:num->A->bool) n /\
       (mu:(A->bool)->real) D <= --inv(&(k + 1))) <= m - 1`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(fst(EQ_IMP_RULE(REWRITE_RULE[]
     (SPEC `\k:num. ?D:A->bool. D IN prob_events (p:A prob_space) /\
       D SUBSET (R:num->A->bool) n /\
       (mu:(A->bool)->real) D <= --inv(&(k + 1))` MINIMAL)))) THEN
   ANTS_TAC THENL
   [EXISTS_TAC `m - 1` THEN EXISTS_TAC `E:A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&(m - 1 + 1) = &m` SUBST1_TAC THENL
    [ASM_SIMP_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_SUB;
                  ARITH_RULE `~(m = 0) ==> 1 <= m`] THEN
     REAL_ARITH_TAC;
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   STRIP_TAC THEN
   REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `m - 1`) THEN
   ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `E:A->bool` THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `&(m - 1 + 1) = &m` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_SUB;
                 ARITH_RULE `~(m = 0) ==> 1 <= m`] THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* So mu(C n) <= -inv(&m) for all n *)
  SUBGOAL_THEN
    `!n:num. (mu:(A->bool)->real)((C:num->A->bool) n) <= --inv(&m)`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `(C:num->A->bool) n = R n DIFF R(SUC n)` SUBST1_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o
     check(fun th -> is_forall(concl th) && is_eq(snd(dest_forall(concl th))))) THEN
   REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `?k:num. ?C:A->bool. C IN prob_events (p:A prob_space) /\
      C SUBSET (R:num->A->bool) n /\
      (mu:(A->bool)->real) C <= --inv(&(k + 1))`
     (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o
     check(fun th -> can (find_term
       (fun t -> is_var t && fst(dest_var t) = "hasneg")) (concl th))) THEN
    EXPAND_TAC "hasneg" THEN REWRITE_TAC[];
    ALL_TAC] THEN
   DISCH_TAC THEN
   FIRST_X_ASSUM(SUBST1_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o
     check(fun th ->
       can (find_term
         (fun t -> is_var t && fst(dest_var t) = "hasneg")) (concl th) &&
       is_forall(concl th))) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   SUBGOAL_THEN
     `(R:num->A->bool) n DIFF (R n DIFF (@D:A->bool. D IN prob_events p /\ D SUBSET R n /\
       (mu:(A->bool)->real) D <= --inv(&((minimal)
         (\k. ?E:A->bool. E IN prob_events p /\ E SUBSET R n /\
               mu E <= --inv(&(k + 1))) + 1)))) =
      (@D:A->bool. D IN prob_events p /\ D SUBSET R n /\
       mu D <= --inv(&((minimal)
         (\k. ?E:A->bool. E IN prob_events p /\ E SUBSET R n /\
               mu E <= --inv(&(k + 1))) + 1)))`
     SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `--inv(&((minimal)
     (\k. ?E:A->bool. E IN prob_events (p:A prob_space) /\ E SUBSET
       (R:num->A->bool) n /\
       (mu:(A->bool)->real) E <= --inv(&(k + 1))) + 1))` THEN
   ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [(* First conjunct: mu(@D...) <= --inv(minimal_k + 1) *)
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o
      check(fun th ->
        can (find_term
          (fun t -> is_var t && fst(dest_var t) = "hasneg")) (concl th) &&
        is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    (* Second conjunct: --inv(minimal_k + 1) <= --inv(&m) *)
    REWRITE_TAC[REAL_LE_NEG2] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    CONJ_TAC THENL [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o
      check(fun th -> can (find_term
        (fun t -> is_const t && fst(dest_const t) = "minimal")) (concl th))) THEN
    UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC];
   ALL_TAC] THEN
  (* But the series converges, and terms -> 0 *)
  SUBGOAL_THEN `((\n:num. (mu:(A->bool)->real)((C:num->A->bool) n)) ---> &0)
                sequentially` MP_TAC THENL
  [MATCH_MP_TAC REAL_SERIES_TERMS_TOZERO THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&m)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
  REWRITE_TAC[LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num` o
    check(fun th -> can (find_term
      (fun t -> is_var t && fst(dest_var t) = "m")) (concl th))) THEN
  REAL_ARITH_TAC);;

(* ---------------------------------------------------------------------- *)
(*  Phase 3: Hahn decomposition theorem                                    *)
(* ---------------------------------------------------------------------- *)

(* The measure of any positive set is bounded above *)
let SUP_POSITIVE_MEASURE_BOUNDED = prove
 (`!p:A prob_space mu. signed_measure p mu
     ==> ?B. !E:A->bool. positive_set p mu E ==> mu E <= B`,
  REPEAT STRIP_TAC THEN
  (* By contradiction: suppose no bound *)
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM;
    NOT_IMP; REAL_NOT_LE]) THEN
  DISCH_TAC THEN
  (* For each n, get E_n positive with mu(E_n) > n *)
  SUBGOAL_THEN `!n:num. ?E:A->bool. positive_set (p:A prob_space) mu E /\
    &n < mu E` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `E:num->A->bool`) THEN
  (* P = UNIONS{E_n | n} is positive *)
  ABBREV_TAC `P = UNIONS {(E:num->A->bool) n | n IN (:num)}` THEN
  SUBGOAL_THEN `positive_set (p:A prob_space) mu P` ASSUME_TAC THENL
  [EXPAND_TAC "P" THEN MATCH_MP_TAC POSITIVE_SET_COUNTABLE_UNION THEN
   ASM_MESON_TAC[]; ALL_TAC] THEN
  (* mu(E_n) <= mu(P) for all n *)
  SUBGOAL_THEN `!n:num. (mu:(A->bool)->real)((E:num->A->bool) n) <=
    mu(P:A->bool)` ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `mu:(A->bool)->real`;
     `P:A->bool`; `(E:num->A->bool) n`] POSITIVE_SET_MONOTONE) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [ASM_MESON_TAC[positive_set];
     EXPAND_TAC "P" THEN
     REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
     MESON_TAC[]];
    REAL_ARITH_TAC]; ALL_TAC] THEN
  (* &n < mu(P) for all n *)
  SUBGOAL_THEN `!n:num. &n < (mu:(A->bool)->real)(P:A->bool)`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
   EXISTS_TAC `(mu:(A->bool)->real)((E:num->A->bool) n)` THEN
   CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]]; ALL_TAC] THEN
  (* Contradiction: mu(P) is a fixed real but > n for all n *)
  MP_TAC(SPEC `(mu:(A->bool)->real)(P:A->bool)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  UNDISCH_TAC `(mu:(A->bool)->real)(P:A->bool) <= &N` THEN
  REAL_ARITH_TAC);;

(* ---------------------------------------------------------------------- *)
(*  Hahn decomposition: prob_carrier = P UNION N, P positive, N negative   *)
(* ---------------------------------------------------------------------- *)

let HAHN_DECOMPOSITION = prove
 (`!p:A prob_space mu.
     signed_measure p mu
     ==> ?P N. positive_set p mu P /\ negative_set p mu N /\
               DISJOINT P N /\ P UNION N = prob_carrier p`,
  REPEAT STRIP_TAC THEN
  (* s = sup{mu(E) | E | positive_set p mu E} -- two-bar syntax keeps mu free *)
  ABBREV_TAC `s = sup {mu(E:A->bool) | E | positive_set (p:A prob_space) mu E}` THEN
  (* s is well-defined: set is nonempty (empty set) and bounded above *)
  SUBGOAL_THEN `~({mu(E:A->bool) | E | positive_set (p:A prob_space) mu E} = {})`
    ASSUME_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   EXISTS_TAC `&0` THEN EXISTS_TAC `{}:A->bool` THEN
   ASM_MESON_TAC[POSITIVE_SET_EMPTY; SIGNED_MEASURE_EMPTY];
   ALL_TAC] THEN
  SUBGOAL_THEN `?B. !x:real. x IN {mu(E:A->bool) | E | positive_set (p:A prob_space) mu E}
    ==> x <= B` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `mu:(A->bool)->real`]
    SUP_POSITIVE_MEASURE_BOUNDED) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
   EXISTS_TAC `B:real` THEN
   REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Properties of s *)
  SUBGOAL_THEN `!E:A->bool. positive_set (p:A prob_space) mu E ==> mu E <= s`
    ASSUME_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "s" THEN
   MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] ELEMENT_LE_SUP) THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[IN_ELIM_THM]; REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL
  [ASM_MESON_TAC[POSITIVE_SET_EMPTY; SIGNED_MEASURE_EMPTY; REAL_LE_TRANS;
                  REAL_LE_REFL];
   ALL_TAC] THEN
  (* Approximating sequence: positive E_n with mu(E_n) > s - inv(n+1) *)
  SUBGOAL_THEN
    `!n:num. ?E:A->bool. positive_set (p:A prob_space) mu E /\
      s - inv(&(n + 1)) < mu E`
    MP_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`{mu(E:A->bool) | E | positive_set (p:A prob_space) mu E}`;
                   `s - inv(&(n + 1))`] SUP_APPROACH) THEN
   ASM_REWRITE_TAC[] THEN
   ANTS_TAC THENL
   [SUBGOAL_THEN `s - inv(&(n + 1)) < s` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_ARITH `s - x < s <=> &0 < x`] THEN
    MATCH_MP_TAC REAL_LT_INV THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `E:num->A->bool` THEN DISCH_TAC THEN
  (* Build cumulative unions P_n = UNIONS(IMAGE E (0..n)) *)
  ABBREV_TAC `Pn = \n:num. UNIONS(IMAGE (E:num->A->bool) (0..n))` THEN
  (* Each P_n is positive (by induction, using POSITIVE_SET_UNION) *)
  SUBGOAL_THEN `!n:num. positive_set (p:A prob_space) mu ((Pn:num->A->bool) n)`
    ASSUME_TAC THENL
  [INDUCT_TAC THENL
   [EXPAND_TAC "Pn" THEN REWRITE_TAC[NUMSEG_SING; IMAGE_CLAUSES] THEN
    REWRITE_TAC[UNIONS_1] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   EXPAND_TAC "Pn" THEN
   SIMP_TAC[NUMSEG_CLAUSES; LE_0] THEN
   REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT] THEN
   MATCH_MP_TAC POSITIVE_SET_UNION THEN
   SUBGOAL_THEN `UNIONS(IMAGE (E:num->A->bool) (0..n)) = (Pn:num->A->bool) n`
     SUBST1_TAC THENL
   [EXPAND_TAC "Pn" THEN REWRITE_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* P = UNIONS{P_n | n} is positive *)
  SUBGOAL_THEN
    `UNIONS {(Pn:num->A->bool) n | n IN (:num)} =
     UNIONS {(E:num->A->bool) n | n IN (:num)}`
    ASSUME_TAC THENL
  [EXPAND_TAC "Pn" THEN
   REWRITE_TAC[UNIONS_GSPEC; IN_UNIV] THEN
   GEN_REWRITE_TAC I [EXTENSION] THEN
   X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN
   REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_NUMSEG] THEN
   MESON_TAC[LE_REFL; LE_0];
   ALL_TAC] THEN
  ABBREV_TAC `P = UNIONS {(E:num->A->bool) n | n IN (:num)}` THEN
  SUBGOAL_THEN `positive_set (p:A prob_space) mu P` ASSUME_TAC THENL
  [EXPAND_TAC "P" THEN
   SUBGOAL_THEN `UNIONS {(E:num->A->bool) n | n IN (:num)} =
     UNIONS {(Pn:num->A->bool) n | n IN (:num)}` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC POSITIVE_SET_COUNTABLE_UNION THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* mu(P) = s *)
  SUBGOAL_THEN `(mu:(A->bool)->real) P = s` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `a <= b /\ b <= a ==> a = b`) THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* s <= mu(P): by contradiction via approximating sequence *)
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   (* mu(E_N) <= mu(P) by monotonicity in positive set P *)
   SUBGOAL_THEN `!n:num. (mu:(A->bool)->real)((E:num->A->bool) n) <= mu(P:A->bool)`
     ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `mu:(A->bool)->real`;
      `P:A->bool`; `(E:num->A->bool) n`] POSITIVE_SET_MONOTONE) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[positive_set];
      EXPAND_TAC "P" THEN
      REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
      MESON_TAC[]];
     REAL_ARITH_TAC];
    ALL_TAC] THEN
   (* s - mu(P) > 0, find N with inv(N) < s - mu(P) *)
   MP_TAC(fst(EQ_IMP_RULE(SPEC `s - (mu:(A->bool)->real)(P:A->bool)`
     REAL_ARCH_INV))) THEN
   ANTS_TAC THENL
   [UNDISCH_TAC `(mu:(A->bool)->real)(P:A->bool) < s` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
   (* inv(N+1) <= inv(N) *)
   SUBGOAL_THEN `inv(&(N + 1)) <= inv(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `~(N = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
   (* s - inv(N+1) < mu(E_N) from approximating sequence *)
   SUBGOAL_THEN `s - inv(&(N + 1)) < (mu:(A->bool)->real)((E:num->A->bool) N)`
     ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   (* Contradiction: inv(N+1) <= inv(N) < s - mu(P), so *)
   (* s - inv(N+1) >= mu(P), but s - inv(N+1) < mu(E_N) <= mu(P) *)
   FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
   UNDISCH_TAC `s - inv(&(N + 1)) < (mu:(A->bool)->real)((E:num->A->bool) N)` THEN
   UNDISCH_TAC `inv(&(N + 1)) <= inv(&N)` THEN
   UNDISCH_TAC `inv(&N) < s - (mu:(A->bool)->real)(P:A->bool)` THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* N = prob_carrier p DIFF P *)
  EXISTS_TAC `P:A->bool` THEN
  EXISTS_TAC `prob_carrier (p:A prob_space) DIFF P` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `P:A->bool IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[positive_set]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [(* negative_set p mu N *)
   REWRITE_TAC[negative_set] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS]; ALL_TAC] THEN
   X_GEN_TAC `B:A->bool` THEN STRIP_TAC THEN
   (* Suppose for contradiction mu(B) > 0 *)
   REWRITE_TAC[REAL_ARITH `x <= &0 <=> ~(&0 < x)`] THEN DISCH_TAC THEN
   (* By EXTRACT_POSITIVE_SUBSET, get Q subset B positive with mu(Q) > 0 *)
   MP_TAC(ISPECL [`p:A prob_space`; `mu:(A->bool)->real`; `B:A->bool`]
     EXTRACT_POSITIVE_SUBSET) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `Q:A->bool` STRIP_ASSUME_TAC) THEN
   (* P UNION Q is positive *)
   SUBGOAL_THEN `positive_set (p:A prob_space) mu (P UNION Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC POSITIVE_SET_UNION THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* mu(P UNION Q) = mu(P) + mu(Q) since DISJOINT *)
   SUBGOAL_THEN `DISJOINT P (Q:A->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `(mu:(A->bool)->real)(P UNION Q) = mu P + mu Q`
     ASSUME_TAC THENL
   [MATCH_MP_TAC SIGNED_MEASURE_FINITELY_ADDITIVE THEN
    ASM_MESON_TAC[positive_set];
    ALL_TAC] THEN
   (* mu(P UNION Q) = s + mu(Q) > s, but mu(P UNION Q) <= s *)
   SUBGOAL_THEN `(mu:(A->bool)->real)(P UNION Q) <= s` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check(fun th ->
     can (find_term (fun t -> is_var t && fst(dest_var t) = "s")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `(mu:(A->bool)->real)(P UNION Q:A->bool) = mu P + mu Q` THEN
    UNDISCH_TAC `(mu:(A->bool)->real)(P:A->bool) = s` THEN
    UNDISCH_TAC `&0 < (mu:(A->bool)->real)(Q:A->bool)` THEN
    REAL_ARITH_TAC];
   (* DISJOINT P N *)
   REWRITE_TAC[DISJOINT] THEN SET_TAC[];
   (* P UNION N = carrier *)
   SUBGOAL_THEN `(P:A->bool) SUBSET prob_carrier p` MP_TAC THENL
   [ASM_MESON_TAC[PROB_EVENT_SUBSET]; SET_TAC[]]]
  );;

(* ---------------------------------------------------------------------- *)
(*  Phase 4: Jordan decomposition and absolute continuity                  *)
(* ---------------------------------------------------------------------- *)

(* Hahn positive set: a canonical choice of P from Hahn decomposition *)
let hahn_pos_set = new_definition
  `hahn_pos_set (p:A prob_space) (mu:(A->bool)->real) =
   @P. positive_set p mu P /\
       negative_set p mu (prob_carrier p DIFF P) /\
       P SUBSET prob_carrier p`;;

let HAHN_POS_SET_WORKS = prove
 (`!p:A prob_space mu. signed_measure p mu
     ==> positive_set p mu (hahn_pos_set p mu) /\
         negative_set p mu (prob_carrier p DIFF hahn_pos_set p mu) /\
         hahn_pos_set p mu SUBSET prob_carrier p`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[hahn_pos_set] THEN
  CONV_TAC SELECT_CONV THEN
  MP_TAC(ISPECL [`p:A prob_space`; `mu:(A->bool)->real`]
    HAHN_DECOMPOSITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:A->bool`
    (X_CHOOSE_THEN `N:A->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `P:A->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [SUBGOAL_THEN `prob_carrier (p:A prob_space) DIFF P = N:A->bool`
     SUBST1_TAC THENL
   [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
   ASM_MESON_TAC[positive_set; PROB_EVENT_SUBSET]]);;

(* Jordan decomposition: positive and negative variation *)
let jordan_pos = new_definition
  `jordan_pos (p:A prob_space) (mu:(A->bool)->real) (A:A->bool) =
   mu(A INTER hahn_pos_set p mu)`;;

let jordan_neg = new_definition
  `jordan_neg (p:A prob_space) (mu:(A->bool)->real) (A:A->bool) =
   --(mu(A INTER (prob_carrier p DIFF hahn_pos_set p mu)))`;;

let JORDAN_POS_NONNEG = prove
 (`!p:A prob_space mu A.
     signed_measure p mu /\ A IN prob_events p
     ==> &0 <= jordan_pos p mu A`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jordan_pos] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `mu:(A->bool)->real`]
    HAHN_POS_SET_WORKS) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[positive_set] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[PROB_INTER_IN_EVENTS] THEN SET_TAC[]);;

let JORDAN_NEG_NONNEG = prove
 (`!p:A prob_space mu A.
     signed_measure p mu /\ A IN prob_events p
     ==> &0 <= jordan_neg p mu A`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jordan_neg] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= --x <=> x <= &0`] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `mu:(A->bool)->real`]
    HAHN_POS_SET_WORKS) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[negative_set] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[PROB_INTER_IN_EVENTS; PROB_COMPL_IN_EVENTS] THEN
  SET_TAC[]);;

let JORDAN_DECOMPOSITION = prove
 (`!p:A prob_space mu A.
     signed_measure p mu /\ A IN prob_events p
     ==> mu A = jordan_pos p mu A - jordan_neg p mu A`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[jordan_pos; jordan_neg; REAL_SUB_RNEG] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `mu:(A->bool)->real`]
    HAHN_POS_SET_WORKS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `P = hahn_pos_set (p:A prob_space) mu` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(P:A->bool) IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[positive_set]; ALL_TAC] THEN
  SUBGOAL_THEN `prob_carrier (p:A prob_space) DIFF P IN prob_events p`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[negative_set]; ALL_TAC] THEN
  SUBGOAL_THEN `(A:A->bool) = (A INTER P) UNION (A INTER (prob_carrier p DIFF P))`
    (fun th -> CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[th]))) THENL
  [SUBGOAL_THEN `(A:A->bool) SUBSET prob_carrier p` MP_TAC THENL
   [ASM_MESON_TAC[PROB_EVENT_SUBSET]; SET_TAC[]];
   ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL [`p:A prob_space`] SIGNED_MEASURE_FINITELY_ADDITIVE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[DISJOINT] THEN SET_TAC[]]);;

(* Absolute continuity *)
let absolutely_continuous = new_definition
  `absolutely_continuous (p:A prob_space) (mu:(A->bool)->real) <=>
   signed_measure p mu /\
   (!A. A IN prob_events p /\ prob p A = &0 ==> mu A = &0)`;;

let ABSOLUTELY_CONTINUOUS_SUBSET = prove
 (`!p:A prob_space mu A.
     absolutely_continuous p mu /\ A IN prob_events p /\ prob p A = &0
     ==> !B. B IN prob_events p /\ B SUBSET A ==> mu B = &0`,
  REWRITE_TAC[absolutely_continuous] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= prob (p:A prob_space) B` MP_TAC THENL
  [ASM_MESON_TAC[PROB_POSITIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `prob (p:A prob_space) B <= prob p A` MP_TAC THENL
  [MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `prob (p:A prob_space) A = &0` THEN REAL_ARITH_TAC);;

let ABSOLUTELY_CONTINUOUS_JORDAN = prove
 (`!p:A prob_space mu A.
     absolutely_continuous p mu /\ A IN prob_events p /\ prob p A = &0
     ==> jordan_pos p mu A = &0 /\ jordan_neg p mu A = &0`,
  REWRITE_TAC[absolutely_continuous] THEN REPEAT STRIP_TAC THENL
  [REWRITE_TAC[jordan_pos] THEN
   SUBGOAL_THEN `(mu:(A->bool)->real)(A INTER hahn_pos_set p mu) = &0`
     (fun th -> REWRITE_TAC[th]) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `mu:(A->bool)->real`]
     HAHN_POS_SET_WORKS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   SUBGOAL_THEN `(A:A->bool) INTER hahn_pos_set p mu IN prob_events p`
     ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
    ASM_MESON_TAC[positive_set]; ALL_TAC] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= prob (p:A prob_space) (A INTER hahn_pos_set p mu)`
     MP_TAC THENL
   [ASM_MESON_TAC[PROB_POSITIVE]; ALL_TAC] THEN
   SUBGOAL_THEN
     `prob (p:A prob_space) (A INTER hahn_pos_set p mu) <= prob p A`
     MP_TAC THENL
   [MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
   UNDISCH_TAC `prob (p:A prob_space) A = &0` THEN REAL_ARITH_TAC;
   REWRITE_TAC[jordan_neg] THEN
   REWRITE_TAC[REAL_ARITH `--x = &0 <=> x = &0`] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `mu:(A->bool)->real`]
     HAHN_POS_SET_WORKS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   SUBGOAL_THEN
     `(A:A->bool) INTER (prob_carrier p DIFF hahn_pos_set p mu)
      IN prob_events p` ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
    ASM_MESON_TAC[negative_set]; ALL_TAC] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `&0 <= prob (p:A prob_space)
       (A INTER (prob_carrier p DIFF hahn_pos_set p mu))` MP_TAC THENL
   [ASM_MESON_TAC[PROB_POSITIVE]; ALL_TAC] THEN
   SUBGOAL_THEN
     `prob (p:A prob_space)
       (A INTER (prob_carrier p DIFF hahn_pos_set p mu)) <= prob p A`
     MP_TAC THENL
   [MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
   UNDISCH_TAC `prob (p:A prob_space) A = &0` THEN REAL_ARITH_TAC]);;

(* ---------------------------------------------------------------------- *)
(*  Phase 5: Jordan variations as signed measures + absolute continuity    *)
(* ---------------------------------------------------------------------- *)

let JORDAN_POS_SIGNED_MEASURE = prove
 (`!p:A prob_space mu. signed_measure p mu
     ==> signed_measure p (jordan_pos p mu)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[signed_measure; jordan_pos] THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN `{} INTER hahn_pos_set (p:A prob_space) mu = {}:A->bool`
     SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[signed_measure];
   ALL_TAC] THEN
  X_GEN_TAC `A:num->A->bool` THEN STRIP_TAC THEN
  ABBREV_TAC `H = hahn_pos_set (p:A prob_space) mu` THEN
  SUBGOAL_THEN `H:A->bool IN prob_events p` ASSUME_TAC THENL
  [EXPAND_TAC "H" THEN ASM_MESON_TAC[HAHN_POS_SET_WORKS; positive_set];
   ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {(A:num->A->bool) n | n IN (:num)} INTER H =
    UNIONS {A n INTER H | n IN (:num)}:A->bool` SUBST1_TAC THENL
  [REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER; IN_UNIV] THEN
   SET_TAC[];
   ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [signed_measure]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `\n:num. (A:num->A->bool) n INTER H`)) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ASM_REWRITE_TAC[DISJOINT] THEN SET_TAC[]];
   REWRITE_TAC[]]);;

let JORDAN_NEG_SIGNED_MEASURE = prove
 (`!p:A prob_space mu. signed_measure p mu
     ==> signed_measure p (jordan_neg p mu)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[signed_measure; jordan_neg] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[INTER_EMPTY; REAL_NEG_0] THEN
   SUBGOAL_THEN `(mu:(A->bool)->real) {} = &0` SUBST1_TAC THENL
   [ASM_MESON_TAC[signed_measure]; REWRITE_TAC[REAL_NEG_0]];
   ALL_TAC] THEN
  X_GEN_TAC `A:num->A->bool` THEN STRIP_TAC THEN
  ABBREV_TAC `N = prob_carrier (p:A prob_space) DIFF hahn_pos_set p mu` THEN
  SUBGOAL_THEN `N:A->bool IN prob_events p` ASSUME_TAC THENL
  [EXPAND_TAC "N" THEN ASM_MESON_TAC[HAHN_POS_SET_WORKS; negative_set];
   ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {(A:num->A->bool) n | n IN (:num)} INTER N =
    UNIONS {A n INTER N | n IN (:num)}:A->bool` SUBST1_TAC THENL
  [REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER; IN_UNIV] THEN
   SET_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[real_sums; SUM_NEG] THEN
  MATCH_MP_TAC REALLIM_NEG THEN
  REWRITE_TAC[GSYM real_sums] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [signed_measure]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `\n:num. (A:num->A->bool) n INTER N`)) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ASM_REWRITE_TAC[DISJOINT] THEN SET_TAC[]];
   REWRITE_TAC[]]);;

let JORDAN_POS_ABSOLUTELY_CONTINUOUS = prove
 (`!p:A prob_space mu.
     absolutely_continuous p mu
     ==> absolutely_continuous p (jordan_pos p mu)`,
  REWRITE_TAC[absolutely_continuous] THEN REPEAT STRIP_TAC THENL
  [ASM_MESON_TAC[JORDAN_POS_SIGNED_MEASURE];
   REWRITE_TAC[jordan_pos] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   SUBGOAL_THEN `(A:A->bool) INTER hahn_pos_set p mu IN prob_events p`
     ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
    ASM_MESON_TAC[HAHN_POS_SET_WORKS; positive_set];
    ALL_TAC] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= prob (p:A prob_space)
     (A INTER hahn_pos_set p mu)` MP_TAC THENL
   [ASM_MESON_TAC[PROB_POSITIVE]; ALL_TAC] THEN
   SUBGOAL_THEN `prob (p:A prob_space) (A INTER hahn_pos_set p mu)
     <= prob p A` MP_TAC THENL
   [MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
   UNDISCH_TAC `prob (p:A prob_space) A = &0` THEN REAL_ARITH_TAC]);;

let JORDAN_NEG_ABSOLUTELY_CONTINUOUS = prove
 (`!p:A prob_space mu.
     absolutely_continuous p mu
     ==> absolutely_continuous p (jordan_neg p mu)`,
  REWRITE_TAC[absolutely_continuous] THEN REPEAT STRIP_TAC THENL
  [ASM_MESON_TAC[JORDAN_NEG_SIGNED_MEASURE];
   REWRITE_TAC[jordan_neg; REAL_ARITH `--x = &0 <=> x = &0`] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   SUBGOAL_THEN `(A:A->bool) INTER (prob_carrier p DIFF hahn_pos_set p mu)
     IN prob_events p` ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
    ASM_MESON_TAC[HAHN_POS_SET_WORKS; negative_set];
    ALL_TAC] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= prob (p:A prob_space)
     (A INTER (prob_carrier p DIFF hahn_pos_set p mu))` MP_TAC THENL
   [ASM_MESON_TAC[PROB_POSITIVE]; ALL_TAC] THEN
   SUBGOAL_THEN `prob (p:A prob_space)
     (A INTER (prob_carrier p DIFF hahn_pos_set p mu)) <= prob p A`
     MP_TAC THENL
   [MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
   UNDISCH_TAC `prob (p:A prob_space) A = &0` THEN REAL_ARITH_TAC]);;
