(* ========================================================================= *)
(* Independence of events and random variables; Borel-Cantelli lemmas.       *)
(*                                                                           *)
(* Follows Williams "Probability with Martingales" Chapter 4.                *)
(* ========================================================================= *)

needs "Probability/random_variables.ml";;

let indep_events = new_definition
  `indep_events (p:(A)prob_space) a b <=>
   a IN prob_events p /\ b IN prob_events p /\
   prob p (a INTER b) = prob p a * prob p b`;;

let INDEP_EVENTS_SYM = prove
  (`!p:A prob_space a b. indep_events p a b <=> indep_events p b a`,
   REPEAT GEN_TAC THEN REWRITE_TAC[indep_events; INTER_COMM] THEN
   REWRITE_TAC[REAL_MUL_SYM] THEN MESON_TAC[]);;

let INDEP_EVENTS_EMPTY = prove
  (`!p:A prob_space a. a IN prob_events p ==> indep_events p a {}`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[indep_events] THEN
   ASM_REWRITE_TAC[PROB_EMPTY_IN_EVENTS; INTER_EMPTY; PROB_EMPTY] THEN
   REAL_ARITH_TAC);;

let INDEP_EVENTS_SPACE = prove
  (`!p:A prob_space a. a IN prob_events p ==> indep_events p a (prob_carrier p)`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[indep_events] THEN
   ASM_REWRITE_TAC[PROB_CARRIER_IN_EVENTS; PROB_SPACE; REAL_MUL_RID] THEN
   AP_TERM_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `a:A->bool`] PROB_EVENT_SUBSET) THEN
   ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let INDEP_EVENTS_COMPL = prove
  (`!p:A prob_space a b.
      indep_events p a b
      ==> indep_events p a (prob_carrier p DIFF b)`,
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [indep_events]) THEN
   STRIP_TAC THEN REWRITE_TAC[indep_events] THEN
   ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS; PROB_COMPL] THEN
   SUBGOAL_THEN
     `a INTER (prob_carrier p DIFF b) = a DIFF b:A->bool`
     SUBST1_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `a:A->bool`] PROB_EVENT_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
   ASM_SIMP_TAC[PROB_DIFF] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Complement of both independent events *)
let INDEP_EVENTS_COMPL_BOTH = prove
  (`!p:A prob_space a b.
      indep_events p a b
      ==> indep_events p (prob_carrier p DIFF a) (prob_carrier p DIFF b)`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC INDEP_EVENTS_COMPL THEN
   ONCE_REWRITE_TAC[INDEP_EVENTS_SYM] THEN
   MATCH_MP_TAC INDEP_EVENTS_COMPL THEN
   ONCE_REWRITE_TAC[INDEP_EVENTS_SYM] THEN
   ASM_REWRITE_TAC[]);;

(* Probability-zero events are independent of everything *)
let INDEP_EVENTS_PROB_ZERO = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p /\ prob p a = &0
      ==> indep_events p a b`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[indep_events] THEN
   ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
   REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `a INTER b:A->bool`; `a:A->bool`]
      PROB_MONO) THEN
    ASM_SIMP_TAC[PROB_INTER_IN_EVENTS; INTER_SUBSET];
    MATCH_MP_TAC PROB_POSITIVE THEN
    ASM_SIMP_TAC[PROB_INTER_IN_EVENTS]]);;

(* Probability-one events are independent of everything *)
let INDEP_EVENTS_PROB_ONE = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p /\ prob p a = &1
      ==> indep_events p a b`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[indep_events] THEN
   ASM_REWRITE_TAC[REAL_MUL_LID] THEN
   SUBGOAL_THEN `prob p (b DIFF a:A->bool) = &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`; `b DIFF a:A->bool`;
                     `prob_carrier p DIFF a:A->bool`] PROB_MONO) THEN
     ASM_SIMP_TAC[PROB_DIFF_IN_EVENTS; PROB_COMPL_IN_EVENTS; PROB_COMPL] THEN
     ANTS_TAC THENL
     [MP_TAC(ISPECL [`p:A prob_space`; `b:A->bool`] PROB_EVENT_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REAL_ARITH_TAC];
     MATCH_MP_TAC PROB_POSITIVE THEN ASM_SIMP_TAC[PROB_DIFF_IN_EVENTS]];
    ALL_TAC] THEN
   SUBGOAL_THEN `prob p (b:A->bool) =
     prob p (a INTER b) + prob p (b DIFF a)` MP_TAC THENL
   [SUBGOAL_THEN `b = (a INTER b) UNION (b DIFF a):A->bool`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
    [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC PROB_ADDITIVE THEN
    ASM_SIMP_TAC[PROB_INTER_IN_EVENTS; PROB_DIFF_IN_EVENTS] THEN SET_TAC[];
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Borel-Cantelli Lemma (first part) - limsup definition                     *)
(* ------------------------------------------------------------------------- *)

let limsup_events = new_definition
  `limsup_events (A:num->A->bool) =
   INTERS {UNIONS {A n | n >= m} | m IN (:num)}`;;

let LIMSUP_EVENTS_ALT = prove
  (`!A:num->A->bool. limsup_events A =
     {x | !m. ?n. n >= m /\ x IN A n}`,
   GEN_TAC THEN REWRITE_TAC[limsup_events; EXTENSION; IN_INTERS] THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV; IN_UNIONS] THEN
   GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `m:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `UNIONS {(A:num->A->bool) n | n >= m}`) THEN
    ANTS_TAC THENL [MESON_TAC[]; REWRITE_TAC[IN_UNIONS; IN_ELIM_THM]] THEN
    MESON_TAC[];
    DISCH_TAC THEN X_GEN_TAC `t:A->bool` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* More conditional probability results                                      *)
(* ------------------------------------------------------------------------- *)

let COND_PROB_SELF = prove
  (`!p:A prob_space a.
      a IN prob_events p /\ &0 < prob p a
      ==> cond_prob p a a = &1`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[cond_prob] THEN
   SUBGOAL_THEN `(a:A->bool) INTER a = a` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_DIV_REFL THEN
   ASM_SIMP_TAC[REAL_LT_IMP_NZ]);;

let COND_PROB_INTER = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p /\ ~(prob p b = &0)
      ==> prob p (a INTER b) = cond_prob p a b * prob p b`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[cond_prob] THEN
   ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
   MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REWRITE_TAC[]);;

let INDEP_EVENTS_COND_PROB = prove
  (`!p:A prob_space a b.
      a IN prob_events p /\ b IN prob_events p /\ &0 < prob p b
      ==> (indep_events p a b <=> cond_prob p a b = prob p a)`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[indep_events; cond_prob] THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `~(prob p (b:A->bool) = &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
   EQ_TAC THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID];
    DISCH_TAC THEN
    SUBGOAL_THEN
      `prob p ((a:A->bool) INTER b) / prob p b * prob p b =
       prob p a * prob p b` MP_TAC THENL
    [AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[REAL_DIV_RMUL]]]);;


(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Borel-Cantelli infrastructure                                             *)
(* ------------------------------------------------------------------------- *)

let LIMSUP_EVENTS_IN_EVENTS = prove
  (`!p:A prob_space A.
      (!n. A n IN prob_events p)
      ==> limsup_events A IN prob_events p`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[limsup_events] THEN
   MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
   REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIV] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN
    CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
     MATCH_MP_TAC COUNTABLE_SUBSET THEN
     EXISTS_TAC `IMAGE (A:num->A->bool) (:num)` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE];
      REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
      MESON_TAC[]]];
    REWRITE_TAC[SIMPLE_IMAGE] THEN
    MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
    MAP_EVERY EXISTS_TAC
      [`UNIONS {(A:num->A->bool) n | n >= 0}`; `0`] THEN
    REWRITE_TAC[]]);;

let LIMSUP_SUBSET_TAIL = prove
  (`!A:num->A->bool m.
      limsup_events A SUBSET UNIONS {A n | n >= m}`,
   REPEAT GEN_TAC THEN REWRITE_TAC[limsup_events] THEN
   REWRITE_TAC[SUBSET; IN_INTERS; IN_ELIM_THM; IN_UNIV] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `m:num` THEN REWRITE_TAC[]);;

let TAIL_UNION_DECREASING = prove
  (`!A:num->A->bool m.
      UNIONS {A n | n >= SUC m} SUBSET UNIONS {A n | n >= m}`,
   REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
   X_GEN_TAC `S:A->bool` THEN STRIP_TAC THEN
   EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let COUNTABLE_GSPEC_NUM = prove
  (`!(f:num->B) (P:num->bool). COUNTABLE {f n | P n}`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
   MATCH_MP_TAC COUNTABLE_IMAGE THEN
   REWRITE_TAC[COUNTABLE_SUBSET_NUM]);;

let TAIL_UNION_IN_EVENTS = prove
  (`!p:A prob_space (B:num->A->bool) m.
      (!n. B n IN prob_events p)
      ==> UNIONS {B n | n >= m} IN prob_events p`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN
   CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN ASM_SIMP_TAC[];
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    TRY BETA_TAC THEN
    MATCH_MP_TAC COUNTABLE_IMAGE THEN
    REWRITE_TAC[COUNTABLE_SUBSET_NUM]]);;


(* --- Toward First Borel-Cantelli Lemma --- *)

(* Helper: union of finite approximations equals the full union *)
let UNIONS_IMAGE_NUMSEG_FULL = prove
  (`!(B:num->A->bool).
      UNIONS {UNIONS (IMAGE B (0..n)) | n IN (:num)} =
      UNIONS {B n | n IN (:num)}`,
   GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
   X_GEN_TAC `x:A` THEN
   REWRITE_TAC[UNIONS_GSPEC; UNIONS_IMAGE; IN_ELIM_THM;
               IN_NUMSEG; IN_UNIV; LE_0] THEN
   MESON_TAC[LE_REFL]);;

(* Renamed version of PROB_FINITE_SUBADDITIVE to avoid type variable clash *)
let PROB_FINITE_SUBADDITIVE' = prove
  (`!p:A prob_space (B:num->A->bool) k.
      (!i. i <= k ==> B i IN prob_events p)
      ==> prob p (UNIONS (IMAGE B (0..k))) <= sum (0..k) (\i. prob p (B i))`,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `B:num->A->bool`; `k:num`]
     PROB_FINITE_SUBADDITIVE) THEN
   ASM_REWRITE_TAC[]);;

(* Helper: finite partial unions converge to full union *)
let PROB_CONTINUITY_FROM_BELOW' = prove
  (`!p:A prob_space (B:num->A->bool).
      (!n. B n IN prob_events p) /\ (!n. B n SUBSET B (SUC n))
      ==> ((\n. prob p (B n)) --->
           prob p (UNIONS {B n | n IN (:num)})) sequentially`,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `B:num->A->bool`]
     PROB_CONTINUITY_FROM_BELOW) THEN
   ASM_REWRITE_TAC[]);;

let FINITE_UNION_CONVERGENCE = prove
  (`!p:A prob_space (B:num->A->bool).
      (!n. B n IN prob_events p)
      ==> ((\n. prob p (UNIONS (IMAGE B (0..n)))) --->
           prob p (UNIONS {B n | n IN (:num)})) sequentially`,
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC[GSYM UNIONS_IMAGE_NUMSEG_FULL] THEN
   MP_TAC(CONV_RULE (DEPTH_CONV BETA_CONV)
     (ISPECL [`p:A prob_space`;
              `\n:num. UNIONS (IMAGE (B:num->A->bool) (0..n))`]
       PROB_CONTINUITY_FROM_BELOW')) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [GEN_TAC THEN
     MP_TAC(ISPECL [`p:A prob_space`; `B:num->A->bool`; `n:num`]
       PROB_FINITE_INDEXED_UNION_IN_EVENTS) THEN
     ASM_REWRITE_TAC[];
     GEN_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THEN
     MATCH_MP_TAC IMAGE_SUBSET THEN
     REWRITE_TAC[SUBSET_NUMSEG] THEN ARITH_TAC];
    SIMP_TAC[]]);;

(* Helper: each finite partial union prob bounded by infsum *)
let FINITE_UNION_BOUNDED_BY_INFSUM = prove
  (`!p:A prob_space (B:num->A->bool) n.
      (!n. B n IN prob_events p) /\
      real_summable (from 0) (\i. prob p (B i))
      ==> prob p (UNIONS (IMAGE B (0..n))) <=
          real_infsum (from 0) (\i. prob p (B i))`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `sum (0..n) (\i:num. prob (p:A prob_space) ((B:num->A->bool) i))` THEN
   CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `B:num->A->bool`; `n:num`]
      PROB_FINITE_SUBADDITIVE') THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
    MP_TAC(CONV_RULE (DEPTH_CONV BETA_CONV)
      (REWRITE_RULE[FROM_INTER_NUMSEG]
        (ISPECL [`\i:num. prob (p:A prob_space) ((B:num->A->bool) i)`;
                 `from 0`; `n:num`]
          REAL_PARTIAL_SUMS_LE_INFSUM))) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL
     [REWRITE_TAC[IN_FROM; LE_0] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
     SIMP_TAC[]]]);;

(* Countable subadditivity for indexed events:
   P(UNION_n B_n) <= sum_n P(B_n) *)
let PROB_COUNTABLE_SUBADDITIVE_INDEXED = prove
  (`!p:A prob_space (B:num->A->bool).
      (!n. B n IN prob_events p) /\
      real_summable (from 0) (\i. prob p (B i))
      ==> prob p (UNIONS {B n | n IN (:num)}) <=
          real_infsum (from 0) (\i. prob p (B i))`,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL
     [`sequentially`;
      `\n:num. prob (p:A prob_space) (UNIONS (IMAGE (B:num->A->bool) (0..n)))`;
      `prob (p:A prob_space) (UNIONS {(B:num->A->bool) n | n IN (:num)})`;
      `real_infsum (from 0) (\i:num. prob (p:A prob_space) ((B:num->A->bool) i))`]
     REALLIM_UBOUND) THEN
   REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
   DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `B:num->A->bool`]
      FINITE_UNION_CONVERGENCE) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `B:num->A->bool`; `n:num`]
      FINITE_UNION_BOUNDED_BY_INFSUM) THEN
    ASM_REWRITE_TAC[]]);;

(* Countable union of probability-zero events has probability zero *)
let PROB_COUNTABLE_UNION_ZERO = prove
  (`!p:A prob_space (B:num->A->bool).
      (!n. B n IN prob_events p) /\ (!n. prob p (B n) = &0)
      ==> prob p (UNIONS {B n | n IN (:num)}) = &0`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `B:num->A->bool`]
      PROB_COUNTABLE_SUBADDITIVE_INDEXED) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `(\i. prob (p:A prob_space) ((B:num->A->bool) i)) = (\i. &0)`
       SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_SUMMABLE_0]];
     SUBGOAL_THEN `(\i. prob (p:A prob_space) ((B:num->A->bool) i)) = (\i. &0)`
       SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_INFSUM_0] THEN REAL_ARITH_TAC]];
    MATCH_MP_TAC PROB_POSITIVE THEN
    MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
    ASM_REWRITE_TAC[]]);;

(* Countable intersection of probability-one events has probability one *)
let PROB_COUNTABLE_INTER_ONE = prove
  (`!p:A prob_space (B:num->A->bool).
      (!n. B n IN prob_events p) /\ (!n. prob p (B n) = &1)
      ==> prob p (INTERS {B n | n IN (:num)}) = &1`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `INTERS {(B:num->A->bool) n | n IN (:num)} IN prob_events p`
     ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
    REWRITE_TAC[SIMPLE_IMAGE; IMAGE_EQ_EMPTY; UNIV_NOT_EMPTY] THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    MESON_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `prob p (INTERS {(B:num->A->bool) n | n IN (:num)}) =
      &1 - prob p (prob_carrier p DIFF INTERS {B n | n IN (:num)})`
     SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `b = &1 - a ==> a = &1 - b`) THEN
    MATCH_MP_TAC PROB_COMPL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `prob p (prob_carrier p DIFF INTERS {(B:num->A->bool) n | n IN (:num)}) = &0`
     SUBST1_TAC THENL
   [SUBGOAL_THEN
      `prob_carrier p DIFF INTERS {(B:num->A->bool) n | n IN (:num)} SUBSET
       UNIONS {prob_carrier p DIFF B n | n IN (:num)}`
      ASSUME_TAC THENL
    [REWRITE_TAC[SUBSET; IN_DIFF; IN_INTERS; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
     MESON_TAC[IN_DIFF];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `prob p (UNIONS {prob_carrier p DIFF (B:num->A->bool) n | n IN (:num)}) = &0`
      ASSUME_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`;
                     `\n:num. prob_carrier p DIFF (B:num->A->bool) n`]
       PROB_COUNTABLE_UNION_ZERO) THEN
     BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS; PROB_COMPL] THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`;
       `prob_carrier p DIFF INTERS {(B:num->A->bool) n | n IN (:num)}`;
       `UNIONS {prob_carrier p DIFF (B:num->A->bool) n | n IN (:num)}`]
       PROB_MONO) THEN
     ANTS_TAC THENL
     [ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS] THEN
      MATCH_MP_TAC PROB_INDEXED_UNION_IN_EVENTS THEN
      ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS];
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
     MATCH_MP_TAC PROB_POSITIVE THEN ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS]];
    REAL_ARITH_TAC]);;


(* A constant bounded by a sequence tending to 0 is <= 0 *)
let REAL_LE_SEQUENTIALLY = prove
  (`!c f. (!n. c <= f n) /\ (f ---> &0) sequentially ==> c <= &0`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
   DISCH_THEN(MP_TAC o SPEC `c:real`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN
   DISCH_THEN(MP_TAC o SPEC `N:num`) THEN
   REWRITE_TAC[LE_REFL] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
   REAL_ARITH_TAC);;

(* Set identity for shifting indexed unions *)
let UNIONS_GEQ_SHIFT = prove
  (`!(B:num->A->bool) m.
      {B n | n >= m} = {B(n + m) | n IN (:num)}`,
   REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC I [EXTENSION] THEN
   X_GEN_TAC `s:A->bool` THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV; GE] THEN
   EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `k:num`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    EXISTS_TAC `k - m:num` THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
    EXISTS_TAC `k + m:num` THEN ARITH_TAC]);;

(* Tail countable subadditivity *)
let PROB_TAIL_SUBADDITIVE = prove
  (`!p:A prob_space (B:num->A->bool) m.
      (!n. B n IN prob_events p) /\
      real_summable (from 0) (\i. prob p (B i))
      ==> prob p (UNIONS {B n | n >= m}) <=
          real_infsum (from m) (\i. prob p (B i))`,
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC[UNIONS_GEQ_SHIFT] THEN
   (* Rewrite real_infsum(from m) = real_infsum(from 0) of shifted function *)
   SUBGOAL_THEN
     `real_infsum (from m) (\i:num. prob (p:A prob_space) ((B:num->A->bool) i)) =
      real_infsum (from 0) (\i. prob p (B(i + m)))`
     SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN
    MP_TAC(CONV_RULE (DEPTH_CONV BETA_CONV)
      (REWRITE_RULE[ADD_CLAUSES]
        (ISPECL [`m:num`;
                 `\i:num. prob (p:A prob_space) ((B:num->A->bool) i)`;
                 `real_infsum (from m)
                    (\i:num. prob (p:A prob_space) ((B:num->A->bool) i))`;
                 `0`]
          REAL_SUMS_REINDEX))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_SUMS_INFSUM] THEN
    MATCH_MP_TAC REAL_SUMMABLE_FROM_ELSEWHERE THEN
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Apply PROB_COUNTABLE_SUBADDITIVE_INDEXED to shifted sequence *)
   MP_TAC(CONV_RULE (DEPTH_CONV BETA_CONV)
     (ISPECL [`p:A prob_space`;
              `\n:num. (B:num->A->bool)(n + m)`]
       PROB_COUNTABLE_SUBADDITIVE_INDEXED)) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [GEN_TAC THEN ASM_REWRITE_TAC[];
     (* real_summable (from 0) (\i. prob p (B(i + m))) *)
     REWRITE_TAC[real_summable] THEN
     SUBGOAL_THEN
       `real_summable (from m)
          (\i:num. prob (p:A prob_space) ((B:num->A->bool) i))` MP_TAC THENL
     [MATCH_MP_TAC REAL_SUMMABLE_FROM_ELSEWHERE THEN
      EXISTS_TAC `0` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     REWRITE_TAC[real_summable] THEN
     DISCH_THEN(X_CHOOSE_TAC `l:real`) THEN
     EXISTS_TAC `l:real` THEN
     MP_TAC(CONV_RULE (DEPTH_CONV BETA_CONV)
       (REWRITE_RULE[ADD_CLAUSES]
         (ISPECL [`m:num`;
                  `\i:num. prob (p:A prob_space) ((B:num->A->bool) i)`;
                  `l:real`; `0`]
           REAL_SUMS_REINDEX))) THEN
     ASM_MESON_TAC[]];
    SIMP_TAC[]]);;

(* Tail of convergent non-negative series -> 0 *)
let TAIL_INFSUM_TENDS_TO_ZERO = prove
  (`!f. (!i. &0 <= f i) /\ real_summable (from 0) f
       ==> ((\n. real_infsum (from (SUC n)) f) ---> &0) sequentially`,
   REPEAT STRIP_TAC THEN
   ABBREV_TAC `L = real_infsum (from 0) f` THEN
   SUBGOAL_THEN `(f real_sums L) (from 0)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[REAL_SUMS_INFSUM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `!n. real_infsum (from (SUC n)) f = L - sum (0..n) f`
     (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN
    MP_TAC(ISPECL [`f:num->real`; `L:real`; `0`; `SUC n`]
      REAL_SUMS_OFFSET) THEN
    ASM_REWRITE_TAC[LT_0; SUC_SUB1];
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 = L - L` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THENL
   [REWRITE_TAC[REALLIM_CONST];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [REAL_SERIES_FROM]) THEN
    SIMP_TAC[]]);;

(* First Borel-Cantelli Lemma *)
let FIRST_BOREL_CANTELLI = prove
  (`!p:A prob_space (B:num->A->bool).
      (!n. B n IN prob_events p) /\
      real_summable (from 0) (\i. prob p (B i))
      ==> prob p (limsup_events B) = &0`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_POSITIVE THEN
    MATCH_MP_TAC LIMSUP_EVENTS_IN_EVENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* prob(limsup B) <= 0: use REAL_LE_SEQUENTIALLY *)
   MP_TAC(CONV_RULE (DEPTH_CONV BETA_CONV)
     (ISPECL
       [`prob (p:A prob_space) (limsup_events (B:num->A->bool))`;
        `\n:num. real_infsum (from (SUC n))
           (\i:num. prob (p:A prob_space) ((B:num->A->bool) i))`]
       REAL_LE_SEQUENTIALLY)) THEN
   DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [(* For each n: prob(limsup B) <= tail infsum from SUC n *)
    X_GEN_TAC `N:num` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `prob (p:A prob_space)
      (UNIONS {(B:num->A->bool) n | n >= SUC N})` THEN
    CONJ_TAC THENL
    [(* prob(limsup B) <= prob(tail union) *)
     MATCH_MP_TAC PROB_MONO THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LIMSUP_EVENTS_IN_EVENTS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC TAIL_UNION_IN_EVENTS THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LIMSUP_SUBSET_TAIL]];
     (* prob(tail union) <= tail infsum *)
     MP_TAC(ISPECL [`p:A prob_space`; `B:num->A->bool`; `SUC N`]
       PROB_TAIL_SUBADDITIVE) THEN
     ASM_REWRITE_TAC[]];
    (* Tail infsum -> 0 *)
    MP_TAC(CONV_RULE (DEPTH_CONV BETA_CONV)
      (ISPEC `\i:num. prob (p:A prob_space) ((B:num->A->bool) i)`
        TAIL_INFSUM_TENDS_TO_ZERO)) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
     SIMP_TAC[]]]);;

(* ===== Second Borel-Cantelli Lemma ===== *)


(* Mutual independence of a sequence of events *)
let indep_events_seq = new_definition
  `indep_events_seq (p:A prob_space) (B:num->A->bool) <=>
   (!n. B n IN prob_events p) /\
   (!S. FINITE S /\ ~(S = {}) ==>
        prob p (INTERS (IMAGE B S)) = product S (\i. prob p (B i)))`;;

(* Helper: INTERS over IMAGE of numseg can be split at SUC n *)
let INTERS_IMAGE_NUMSEG_SUC = prove
  (`!(f:num->A->bool) m n.
      m <= SUC n
      ==> INTERS(IMAGE f (m..SUC n)) = f(SUC n) INTER INTERS(IMAGE f (m..n))`,
   REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC[NUMSEG_CLAUSES; ARITH_RULE `m <= SUC n ==> m <= SUC n`] THEN
   ASM_REWRITE_TAC[IMAGE_CLAUSES; INTERS_INSERT]);;

(* Helper: single complement intersected with originals *)
let INDEP_COMPL_SINGLE_INTER = prove
  (`!p:A prob_space (B:num->A->bool) m (idx:num->bool).
      indep_events_seq p B /\ FINITE idx /\ ~(idx = {}) /\ ~(m IN idx)
      ==> prob p ((prob_carrier p DIFF B m) INTER INTERS(IMAGE B idx)) =
          (&1 - prob p (B m)) * product idx (\j. prob p (B j))`,
   REPEAT STRIP_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [indep_events_seq]) THEN
   (* Step 1: INTERS(IMAGE B idx) IN prob_events p *)
   SUBGOAL_THEN `INTERS(IMAGE (B:num->A->bool) idx) IN prob_events p`
     ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
    CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; IN_IMAGE] THEN ASM_MESON_TAC[];
     ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; FINITE_IMAGE; IMAGE_EQ_EMPTY]];
    ALL_TAC] THEN
   (* Step 2: (Omega \ B m) INTER D = D \ B m *)
   SUBGOAL_THEN
     `(prob_carrier p DIFF B m) INTER INTERS(IMAGE (B:num->A->bool) idx) =
      INTERS(IMAGE B idx) DIFF B m`
     SUBST1_TAC THENL
   [SUBGOAL_THEN
      `INTERS(IMAGE (B:num->A->bool) idx) SUBSET prob_carrier (p:A prob_space)`
      MP_TAC THENL
    [ASM_MESON_TAC[PROB_EVENT_SUBSET]; SET_TAC[]];
    ALL_TAC] THEN
   (* Step 3: apply PROB_DIFF *)
   ASM_SIMP_TAC[PROB_DIFF] THEN
   (* Step 4: D INTER B m = INTERS(IMAGE B (m INSERT idx)) *)
   SUBGOAL_THEN
     `INTERS(IMAGE (B:num->A->bool) idx) INTER B m =
      INTERS(IMAGE B (m INSERT idx))`
     SUBST1_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES; INTERS_INSERT] THEN SET_TAC[];
    ALL_TAC] THEN
   (* Step 5: apply independence *)
   SUBGOAL_THEN
     `prob p (INTERS(IMAGE (B:num->A->bool) idx)) =
      product idx (\j. prob p (B j))`
     SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `idx:num->bool`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `prob p (INTERS(IMAGE (B:num->A->bool) (m INSERT idx))) =
      product (m INSERT idx) (\j. prob p (B j))`
     SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `m INSERT (idx:num->bool)`) THEN
    ASM_SIMP_TAC[FINITE_INSERT; NOT_INSERT_EMPTY];
    ALL_TAC] THEN
   ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
   REWRITE_TAC[REAL_SUB_RDISTRIB; REAL_MUL_LID]);;

(* Simultaneous induction: main + helper with extra original events *)
let INDEP_COMPL_INTERS_NUMSEG_BOTH = prove
  (`!n.
     (!p:A prob_space (B:num->A->bool) m.
        indep_events_seq p B /\ m <= n
        ==> prob p (INTERS(IMAGE (\i. prob_carrier p DIFF B i) (m..n))) =
            product(m..n) (\i. &1 - prob p (B i))) /\
     (!p:A prob_space (B:num->A->bool) m (extra:num->bool).
        indep_events_seq p B /\ m <= n /\
        FINITE extra /\ ~(extra = {}) /\ (!j. j IN extra ==> n < j)
        ==> prob p (INTERS(IMAGE (\i. prob_carrier p DIFF B i) (m..n)) INTER
                     INTERS(IMAGE B extra)) =
            product(m..n) (\i. &1 - prob p (B i)) *
            product extra (\j. prob p (B j)))`,
   INDUCT_TAC THENL
   [(* Base: n = 0 *)
    CONJ_TAC THENL
    [(* Part 1: singleton, no extra events *)
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[NUMSEG_SING; IMAGE_CLAUSES; INTERS_1;
                  PRODUCT_SING_NUMSEG; PRODUCT_SING] THEN
     FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [indep_events_seq]) THEN
     ASM_SIMP_TAC[PROB_COMPL];
     (* Part 2: singleton, with extra events *)
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `m = 0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[NUMSEG_SING; IMAGE_CLAUSES; INTERS_1] THEN
     REWRITE_TAC[PRODUCT_SING_NUMSEG; PRODUCT_SING] THEN
     MATCH_MP_TAC INDEP_COMPL_SINGLE_INTER THEN
     ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `~(0 IN extra)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REWRITE_TAC[]]];
    (* Step: n -> SUC n *)
    FIRST_X_ASSUM(CONJUNCTS_THEN2
      (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
    CONJ_TAC THENL
    [(* Part 1: no extra events *)
     REPEAT STRIP_TAC THEN
     ASM_CASES_TAC `m = SUC n` THENL
     [(* Singleton case: m = SUC n *)
      ASM_REWRITE_TAC[NUMSEG_SING; IMAGE_CLAUSES; INTERS_1;
                       PRODUCT_SING_NUMSEG; PRODUCT_SING] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [indep_events_seq]) THEN
      ASM_SIMP_TAC[PROB_COMPL];
      (* m <= n case *)
      SUBGOAL_THEN `m <= n:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [indep_events_seq]) THEN
      (* Rewrite INTERS over m..SUC n *)
      ASM_SIMP_TAC[INTERS_IMAGE_NUMSEG_SUC] THEN
      (* Let D_n = INTERS(IMAGE (\i. Omega \ B i) (m..n)) *)
      ABBREV_TAC
        `D_n = INTERS(IMAGE (\i. prob_carrier (p:A prob_space) DIFF B i) (m..n))` THEN
      (* D_n IN prob_events p *)
      SUBGOAL_THEN `D_n IN prob_events (p:A prob_space)` ASSUME_TAC THENL
      [EXPAND_TAC "D_n" THEN
       MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
       CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_IMAGE; IN_NUMSEG] THEN
        ASM_MESON_TAC[PROB_COMPL_IN_EVENTS];
        ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IMAGE_EQ_EMPTY;
                      FINITE_IMP_COUNTABLE; NUMSEG_EMPTY; NOT_LT; LE_REFL]];
       ALL_TAC] THEN
      (* D_n SUBSET prob_carrier p *)
      SUBGOAL_THEN `D_n SUBSET prob_carrier (p:A prob_space)` ASSUME_TAC THENL
      [ASM_MESON_TAC[PROB_EVENT_SUBSET]; ALL_TAC] THEN
      (* (Omega \ B(SUC n)) INTER D_n = D_n \ B(SUC n) *)
      SUBGOAL_THEN
        `(prob_carrier (p:A prob_space) DIFF B(SUC n)) INTER D_n =
         D_n DIFF B(SUC n)` SUBST1_TAC THENL
      [ASM SET_TAC[]; ALL_TAC] THEN
      (* Apply PROB_DIFF *)
      ASM_SIMP_TAC[PROB_DIFF] THEN
      (* P(D_n) by IH1 *)
      SUBGOAL_THEN
        `prob (p:A prob_space) D_n =
         product(m..n) (\i. &1 - prob p (B i))`
        SUBST1_TAC THENL
      [EXPAND_TAC "D_n" THEN
       REMOVE_THEN "IH1" (MP_TAC o SPECL
         [`p:A prob_space`; `B:num->A->bool`; `m:num`]) THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      (* D_n INTER B(SUC n) by IH2 with extra = {SUC n} *)
      SUBGOAL_THEN
        `prob (p:A prob_space) (D_n INTER B(SUC n)) =
         product(m..n) (\i. &1 - prob p (B i)) * prob p (B(SUC n))`
        SUBST1_TAC THENL
      [SUBGOAL_THEN
         `D_n INTER (B:num->A->bool)(SUC n) =
          INTERS(IMAGE (\i. prob_carrier (p:A prob_space) DIFF B i) (m..n)) INTER
          INTERS(IMAGE B {SUC n})`
         SUBST1_TAC THENL
       [EXPAND_TAC "D_n" THEN
        REWRITE_TAC[IMAGE_CLAUSES; INTERS_1]; ALL_TAC] THEN
       REMOVE_THEN "IH2" (MP_TAC o SPECL
         [`p:A prob_space`; `B:num->A->bool`; `m:num`; `{SUC n}`]) THEN
       ASM_REWRITE_TAC[FINITE_SING; NOT_INSERT_EMPTY; IN_SING] THEN
       ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
       DISCH_THEN(fun th -> REWRITE_TAC[th; PRODUCT_SING]);
       ALL_TAC] THEN
      (* Algebra: P - P*q = (1-q)*P = product(m..SUC n) *)
      SUBGOAL_THEN `m <= SUC n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[PRODUCT_CLAUSES_NUMSEG] THEN
      CONV_TAC REAL_RING];
     (* Part 2: with extra events *)
     REPEAT STRIP_TAC THEN
     ASM_CASES_TAC `m = SUC n` THENL
     [(* Singleton case *)
      ASM_REWRITE_TAC[NUMSEG_SING; IMAGE_CLAUSES; INTERS_1;
                       PRODUCT_SING_NUMSEG; PRODUCT_SING] THEN
      MATCH_MP_TAC INDEP_COMPL_SINGLE_INTER THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(SUC n IN extra)` ASSUME_TAC THENL
      [DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN ASM_REWRITE_TAC[] THEN
       ARITH_TAC;
       ASM_REWRITE_TAC[]];
      (* m <= n case *)
      SUBGOAL_THEN `m <= n:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [indep_events_seq]) THEN
      ASM_SIMP_TAC[INTERS_IMAGE_NUMSEG_SUC] THEN
      ABBREV_TAC
        `D_n = INTERS(IMAGE (\i. prob_carrier (p:A prob_space) DIFF B i) (m..n))` THEN
      (* D_n IN prob_events p *)
      SUBGOAL_THEN `D_n IN prob_events (p:A prob_space)` ASSUME_TAC THENL
      [EXPAND_TAC "D_n" THEN
       MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
       CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_IMAGE; IN_NUMSEG] THEN
        ASM_MESON_TAC[PROB_COMPL_IN_EVENTS];
        ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IMAGE_EQ_EMPTY;
                      FINITE_IMP_COUNTABLE; NUMSEG_EMPTY; NOT_LT; LE_REFL]];
       ALL_TAC] THEN
      SUBGOAL_THEN `D_n SUBSET prob_carrier (p:A prob_space)` ASSUME_TAC THENL
      [ASM_MESON_TAC[PROB_EVENT_SUBSET]; ALL_TAC] THEN
      (* INTERS(IMAGE B extra) IN prob_events p *)
      SUBGOAL_THEN `INTERS(IMAGE (B:num->A->bool) extra) IN prob_events p`
        ASSUME_TAC THENL
      [MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
       CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_IMAGE] THEN ASM_MESON_TAC[];
        ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; FINITE_IMAGE; IMAGE_EQ_EMPTY]];
       ALL_TAC] THEN
      (* Let E = D_n INTER INTERS(IMAGE B extra) *)
      ABBREV_TAC
        `E = D_n INTER INTERS(IMAGE (B:num->A->bool) extra)` THEN
      (* E IN prob_events p *)
      SUBGOAL_THEN `E IN prob_events (p:A prob_space)` ASSUME_TAC THENL
      [EXPAND_TAC "E" THEN
       ASM_SIMP_TAC[PROB_INTER_IN_EVENTS]; ALL_TAC] THEN
      SUBGOAL_THEN `E SUBSET prob_carrier (p:A prob_space)` ASSUME_TAC THENL
      [ASM_MESON_TAC[PROB_EVENT_SUBSET]; ALL_TAC] THEN
      (* Prove set equation and rewrite *)
      SUBGOAL_THEN
        `((prob_carrier (p:A prob_space) DIFF B(SUC n)) INTER D_n) INTER
          INTERS(IMAGE (B:num->A->bool) extra) =
         E DIFF B(SUC n)` ASSUME_TAC THENL
      [EXPAND_TAC "E" THEN ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[PROB_DIFF] THEN
      (* P(E) by IH2 *)
      SUBGOAL_THEN
        `prob (p:A prob_space) E =
         product(m..n) (\i. &1 - prob p (B i)) *
         product extra (\j. prob p (B j))`
        SUBST1_TAC THENL
      [EXPAND_TAC "E" THEN EXPAND_TAC "D_n" THEN
       REMOVE_THEN "IH2" (MP_TAC o SPECL
         [`p:A prob_space`; `B:num->A->bool`; `m:num`; `extra:num->bool`]) THEN
       ASM_REWRITE_TAC[] THEN
       ANTS_TAC THENL
       [ASM_MESON_TAC[ARITH_RULE `SUC n < j ==> n < j`];
        SIMP_TAC[]];
       ALL_TAC] THEN
      (* P(E INTER B(SUC n)) by IH2 with (SUC n INSERT extra) *)
      SUBGOAL_THEN
        `prob (p:A prob_space) (E INTER B(SUC n)) =
         product(m..n) (\i. &1 - prob p (B i)) *
         product (SUC n INSERT extra) (\j. prob p (B j))`
        SUBST1_TAC THENL
      [SUBGOAL_THEN
         `E INTER (B:num->A->bool)(SUC n) =
          INTERS(IMAGE (\i. prob_carrier (p:A prob_space) DIFF B i) (m..n)) INTER
          INTERS(IMAGE B (SUC n INSERT extra))`
         ASSUME_TAC THENL
       [EXPAND_TAC "E" THEN EXPAND_TAC "D_n" THEN
        REWRITE_TAC[IMAGE_CLAUSES; INTERS_INSERT] THEN SET_TAC[];
        ALL_TAC] THEN
       ASM_REWRITE_TAC[] THEN
       REMOVE_THEN "IH2" (MP_TAC o SPECL
         [`p:A prob_space`; `B:num->A->bool`; `m:num`;
          `SUC n INSERT (extra:num->bool)`]) THEN
       ASM_SIMP_TAC[FINITE_INSERT; NOT_INSERT_EMPTY] THEN
       ANTS_TAC THENL
       [REWRITE_TAC[IN_INSERT] THEN
        ASM_MESON_TAC[ARITH_RULE `SUC n < j ==> n < j`;
                       ARITH_RULE `n < SUC n`];
        SIMP_TAC[]];
       ALL_TAC] THEN
      (* Expand product(SUC n INSERT extra) using PRODUCT_CLAUSES *)
      SUBGOAL_THEN `~(SUC n IN extra)` ASSUME_TAC THENL
      [ASM_MESON_TAC[ARITH_RULE `~(SUC n < SUC n)`]; ALL_TAC] THEN
      ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
      (* Algebra *)
      SUBGOAL_THEN `m <= SUC n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[PRODUCT_CLAUSES_NUMSEG] THEN
      CONV_TAC REAL_RING]]]);;


let INDEP_COMPL_INTERS_NUMSEG = prove
  (`!p:A prob_space (B:num->A->bool) m n.
      indep_events_seq p B /\ m <= n
      ==> prob p (INTERS (IMAGE (\i. prob_carrier p DIFF B i) (m..n))) =
          product(m..n) (\i. &1 - prob p (B i))`,
   MESON_TAC[INDEP_COMPL_INTERS_NUMSEG_BOTH]);;

(* Product of (1 - f(i)) bounded by exp(-sum f) for 0 <= f <= 1 *)
let PRODUCT_ONE_MINUS_LE_EXP_NEG = prove
  (`!f m n. (!i. m <= i /\ i <= n ==> &0 <= f i /\ f i <= &1)
            ==> product(m..n) (\i. &1 - f i) <= exp(--(sum(m..n) f))`,
   REPEAT STRIP_TAC THEN
   (* Step 1: product(1-f) <= product(exp(-f)) *)
   SUBGOAL_THEN
     `product(m..n) (\i:num. &1 - (f:num->real) i) <=
      product(m..n) (\i. exp(--f i))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC;
     MP_TAC(SPEC `--((f:num->real) i)` REAL_EXP_LE_X) THEN
     REAL_ARITH_TAC];
    ALL_TAC] THEN
   (* Step 2: product(exp(-f)) = exp(-sum(f)) *)
   SUBGOAL_THEN
     `product(m..n) (\i:num. exp(--(f i:real))) = exp(--(sum(m..n) f))`
     ASSUME_TAC THENL
   [MP_TAC(CONV_RULE (DEPTH_CONV BETA_CONV)
     (ISPECL [`\i:num. --((f:num->real) i)`; `(m:num)..(n:num)`]
       REAL_EXP_SUM)) THEN
    REWRITE_TAC[FINITE_NUMSEG; SUM_NEG] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]);
    ASM_REAL_ARITH_TAC]);;

(* Nonneg partial sums of non-summable series are unbounded *)
let NONNEG_PARTIAL_SUMS_UNBOUNDED = prove
  (`!f. (!i. &0 <= f i) /\ ~real_summable (from 0) f
       ==> !M. ?N. M <= sum(0..N) f`,
   REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `M:real` THEN
   (* By contradiction: assume all partial sums < M *)
   ASM_CASES_TAC `?N:num. M <= sum(0..N) (f:num->real)` THENL
   [ASM_MESON_TAC[];
    (* All partial sums < M, so they're bounded + monotone => convergent *)
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~real_summable (from 0) (f:num->real)` THEN
    REWRITE_TAC[real_summable; real_sums; FROM_INTER_NUMSEG] THEN
    MP_TAC(SPEC `\n:num. sum(0..n) (f:num->real)`
      CONVERGENT_REAL_BOUNDED_MONOTONE) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL
     [(* bounded *)
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
      EXISTS_TAC `abs M` THEN GEN_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x < M ==> abs x <= abs M`) THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[]];
      (* monotone increasing *)
      DISJ1_TAC THEN GEN_TAC THEN
      REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> a <= a + x`) THEN
      ASM_REWRITE_TAC[]];
     MESON_TAC[]]]);;

(* Helper: product(m..n)(1-f) -> 0 when sum f diverges and 0<=f<=1 *)
let PRODUCT_ONE_MINUS_TENDS_TO_ZERO = prove
  (`!f m. (!i. &0 <= f i /\ f i <= &1) /\
          ~real_summable (from 0) f
          ==> ((\n. product(m..n) (\i. &1 - f i)) ---> &0) sequentially`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   (* Get N with sum(0..N) f large enough *)
   MP_TAC(SPEC `f:num->real` NONNEG_PARTIAL_SUMS_UNBOUNDED) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPEC `-- log e + sum(0..m) (f:num->real) + &1`) THEN
   DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
   EXISTS_TAC `N0 + m:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   SUBGOAL_THEN `m:num <= n` ASSUME_TAC THENL
   [UNDISCH_TAC `N0 + m:num <= n` THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `N0:num <= n` ASSUME_TAC THENL
   [UNDISCH_TAC `N0 + m:num <= n` THEN ARITH_TAC; ALL_TAC] THEN
   (* |product - 0| = product since product >= 0 *)
   REWRITE_TAC[REAL_SUB_RZERO; real_abs] THEN
   SUBGOAL_THEN `&0 <= product(m..n) (\i. &1 - (f:num->real) i)` ASSUME_TAC
     THENL
   [MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN BETA_TAC THEN
    ASM_MESON_TAC[REAL_ARITH `x <= &1 ==> &0 <= &1 - x`]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   (* product(m..n)(1-f) <= exp(-sum(m..n) f) *)
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `exp(--sum(m..n) (f:num->real))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_ONE_MINUS_LE_EXP_NEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Show sum(m..n) f > -log e, so exp(-sum(m..n) f) < e *)
   SUBGOAL_THEN `-- log e < sum(m..n) (f:num->real)` ASSUME_TAC THENL
   [(* Chain: sum(0..N0) f <= sum(0..n) f, and
      sum(0..n) f <= sum(0..m) f + sum(m..n) f (double-counting at m),
      plus our bound -log e + sum(0..m) f + 1 <= sum(0..N0) f *)
    SUBGOAL_THEN `sum(0..N0) (f:num->real) <= sum(0..n) f` ASSUME_TAC THENL
    [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
     CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_NUMSEG] THEN
      UNDISCH_TAC `N0:num <= n` THEN ARITH_TAC;
      REWRITE_TAC[IN_DIFF; IN_NUMSEG] THEN ASM_MESON_TAC[]];
     ALL_TAC] THEN
    (* sum(0..n) f <= sum(0..m) f + sum(m..n) f via SUM_COMBINE_R *)
    SUBGOAL_THEN `sum(0..n) (f:num->real) <= sum(0..m) f + sum(m..n) f`
      ASSUME_TAC THENL
    [MP_TAC(ISPECL [`f:num->real`; `0`; `m:num`; `n:num`] SUM_COMBINE_R) THEN
     ANTS_TAC THENL
     [UNDISCH_TAC `m:num <= n` THEN ARITH_TAC; ALL_TAC] THEN
     DISCH_TAC THEN
     SUBGOAL_THEN `sum(m + 1..n) (f:num->real) <= sum(m..n) f`
       ASSUME_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      CONJ_TAC THENL
      [REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ARITH_TAC;
       REWRITE_TAC[IN_DIFF; IN_NUMSEG] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
     ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `exp(--sum(m..n) (f:num->real)) < exp(log e)` MP_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[EXP_LOG] THEN REAL_ARITH_TAC);;

(* Helper: tail union has prob 1 under Second BC hypotheses *)
let TAIL_UNION_PROB_ONE = prove
  (`!p:A prob_space (B:num->A->bool) m.
      indep_events_seq p B /\
      ~real_summable (from 0) (\i. prob p (B i))
      ==> prob p (UNIONS {B n | n >= m}) = &1`,
   REPEAT STRIP_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [indep_events_seq]) THEN
   SUBGOAL_THEN
     `UNIONS {(B:num->A->bool) n | n >= m} IN prob_events (p:A prob_space)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC TAIL_UNION_IN_EVENTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* Suffice: prob(complement) = 0, then PROB_COMPL gives prob = 1 *)
   SUBGOAL_THEN
     `prob (p:A prob_space)
       (prob_carrier p DIFF UNIONS {(B:num->A->bool) n | n >= m}) = &0`
     ASSUME_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(fun th ->
      MP_TAC th THEN ASM_SIMP_TAC[PROB_COMPL]) THEN
    REWRITE_TAC[REAL_ARITH `&1 - x = &0 <=> x = &1`]] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC PROB_POSITIVE THEN
    MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Bound by product(m..n)(1-prob(B i)) -> 0 via REAL_LE_SEQUENTIALLY *)
   MP_TAC(ISPECL
     [`prob (p:A prob_space)
        (prob_carrier p DIFF UNIONS {(B:num->A->bool) n | n >= m})`;
      `\n:num. product(m..n)
        (\i:num. &1 - prob (p:A prob_space) ((B:num->A->bool) i))`]
     REAL_LE_SEQUENTIALLY) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [(* For all n: prob(compl) <= product(m..n)(1-prob(B i)) *)
     BETA_TAC THEN X_GEN_TAC `n:num` THEN
     ASM_CASES_TAC `m:num <= n` THENL
     [(* Case m <= n: subset gives prob bound *)
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
        `prob (p:A prob_space)
          (INTERS (IMAGE (\i. prob_carrier p DIFF B i) ((m:num)..n)))` THEN
      CONJ_TAC THENL
      [(* prob(compl of union) <= prob(finite inters of compls) *)
       MATCH_MP_TAC PROB_MONO THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN ASM_REWRITE_TAC[];
        (* INTERS in events *)
        MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
        REWRITE_TAC[IMAGE_EQ_EMPTY; NUMSEG_EMPTY; NOT_LT] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
        [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
         REPEAT STRIP_TAC THEN MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
         ASM_REWRITE_TAC[];
         MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN
         MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG]];
        (* subset *)
        REWRITE_TAC[SUBSET; IN_DIFF; IN_INTERS; FORALL_IN_IMAGE;
                     IN_NUMSEG; IN_UNIONS; IN_ELIM_THM; GE] THEN
        MESON_TAC[LE_TRANS]];
       (* prob(finite inters) = product by independence *)
       ASM_SIMP_TAC[INDEP_COMPL_INTERS_NUMSEG] THEN REAL_ARITH_TAC];
      (* Case ~(m <= n): product over empty numseg = 1, prob <= 1 *)
      SUBGOAL_THEN `(m:num)..n = {}` SUBST1_TAC THENL
      [REWRITE_TAC[NUMSEG_EMPTY] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[PRODUCT_CLAUSES] THEN
      MATCH_MP_TAC PROB_LE_1 THEN
      MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN ASM_REWRITE_TAC[]];
     (* product(m..n)(1-prob(B i)) -> 0 *)
     MATCH_MP_TAC PRODUCT_ONE_MINUS_TENDS_TO_ZERO THEN
     CONJ_TAC THENL
     [GEN_TAC THEN CONJ_TAC THENL
      [MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC PROB_LE_1 THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[]]];
    REAL_ARITH_TAC]);;

(* Second Borel-Cantelli Lemma *)
let SECOND_BOREL_CANTELLI = prove
  (`!p:A prob_space (B:num->A->bool).
      indep_events_seq p B /\
      ~real_summable (from 0) (\i. prob p (B i))
      ==> prob p (limsup_events B) = &1`,
   REPEAT STRIP_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [indep_events_seq]) THEN
   (* Apply PROB_CONTINUITY_FROM_ABOVE to T(m) = UNIONS{B n | n >= m} *)
   MP_TAC(CONV_RULE (DEPTH_CONV BETA_CONV)
     (ISPECL [`p:A prob_space`;
              `\m:num. UNIONS {(B:num->A->bool) n | n >= m}`]
       PROB_CONTINUITY_FROM_ABOVE)) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC TAIL_UNION_IN_EVENTS THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[TAIL_UNION_DECREASING]];
    ALL_TAC] THEN
   (* Rewrite INTERS{T m | m} to limsup_events B *)
   REWRITE_TAC[GSYM limsup_events] THEN
   (* Rewrite (\m. prob(T m)) to (\m. &1) *)
   SUBGOAL_THEN
     `(\m:num. prob (p:A prob_space) (UNIONS {(B:num->A->bool) n | n >= m})) =
      (\m. &1)`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC TAIL_UNION_PROB_ONE THEN
    ASM_REWRITE_TAC[indep_events_seq];
    ALL_TAC] THEN
   (* Goal: ((\m. &1) ---> prob(limsup B)) seq ==> prob(limsup B) = &1 *)
   DISCH_TAC THEN
   MP_TAC(ISPECL [`sequentially`; `\m:num. &1`; `&1`;
     `prob (p:A prob_space) (limsup_events (B:num->A->bool))`]
     REALLIM_UNIQUE) THEN
   ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; REALLIM_CONST] THEN
   DISCH_THEN(ACCEPT_TAC o GSYM));;

