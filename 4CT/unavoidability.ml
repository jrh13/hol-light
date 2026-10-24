(* ========================================================================= *)
(* 4CT/unavoidability.ml                                                     *)
(*                                                                           *)
(* unavoidability.v: reducibility implies that there is no minimal           *)
(* counter-example (UNAVOIDABILITY_CHECK, Coq unavoidability), collating the *)
(* seven presentation lemmas of presentations.ml (present5.v to present11.v) *)
(* with POSZ_DSCORE, DSCORE_CAP1 and the four discharge bound checks         *)
(* THE_DBOUND1_CHECK for the hub sizes 5 to 8.  Coq's reducibility is the    *)
(* computational check check_reducibility of present.ml.                     *)
(* ========================================================================= *)

needs "4CT/present.ml";;
needs "4CT/redpart_eval.ml";;

(* ------------------------------------------------------------------------- *)
(* exclude5 .. exclude11 (Coq present5.v .. present11.v) come from           *)
(* presentations.ml: Gonthier's scripts run through the present_eval.ml      *)
(* interpreter.                                                              *)
(* ------------------------------------------------------------------------- *)

needs "4CT/presentations.ml";;

(* ------------------------------------------------------------------------- *)
(* The collating argument (Coq unavoidability.v:20-34).                      *)
(* ------------------------------------------------------------------------- *)

let DRULE_FORK_VALUES_THE = prove
 (`!n. drule_fork_values n (FST (the_drule_fork n)) (SND (the_drule_fork n))`,
  REWRITE_TAC[the_drule_fork; drule_fork_values]);;

let FOUR_COLORABLE_EMPTY = prove
 (`!(H:(A)hypermap). dart H = {} ==> four_colorable H`,
  REWRITE_TAC[four_colorable; coloring] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `\x:A. Color0` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY]);;

let MCE_DART_NONEMPTY = prove
 (`!(G:(A)hypermap). minimal_counter_example G ==> ~(dart G = {})`,
  GEN_TAC THEN REWRITE_TAC[minimal_counter_example] THEN STRIP_TAC THEN
  ASM_MESON_TAC[FOUR_COLORABLE_EMPTY]);;

let MCE_PLAIN_CUBIC_CONNECTED = prove
 (`!(G:(A)hypermap). minimal_counter_example G ==> plain_cubic_connected G`,
  REWRITE_TAC[plain_cubic_connected] THEN
  MESON_TAC[MCE_PLAIN_CUBIC; MCE_CONNECTED]);;

(* Every dart's dscore1 is at most 5: dscore1 y = dbound1 (the_drule_fork n) *)
(* x where y = f (f x), n = arity x; for n in 5..8 the dbound1 check bounds  *)
(* it by 5, otherwise the source rule list is empty.                         *)
let DSCORE1_LE5 = prove
 (`!(G:(A)hypermap). check_reducibility /\ minimal_counter_example G
                     ==> !y. y IN dart G ==> dscore1 G y <= &5`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MCE_PLAIN_CUBIC_PENTAGONAL) THEN
  SUBST1_TAC(SYM(ISPECL [`G:(A)hypermap`; `y:A`] FF_INV_FACE2)) THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `y:A`] INV_FACE2_IN_DART) THEN
  ASM_REWRITE_TAC[] THEN SPEC_TAC(`inv_face2 G (y:A)`, `x:A`) THEN
  REPEAT STRIP_TAC THEN ABBREV_TAC `n = arity G (x:A)` THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `n:num`; `FST (the_drule_fork n)`;
                 `SND (the_drule_fork n)`; `x:A`] DBOUND1_EQ) THEN
  ASM_REWRITE_TAC[DRULE_FORK_VALUES_THE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_CASES_TAC `mem_range Pr58 n` THENL
   [MATCH_MP_TAC CHECK_DBOUND1P THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `redpart the_quiz_tree`; `pcons_ n`] THEN
    ASM_REWRITE_TAC[DRULE_FORK_VALUES_THE] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[NO_FIT_THE_REDPART];
      EXPAND_TAC "n" THEN MATCH_MP_TAC EXACT_FITP_PCONS_ THEN
      ASM_MESON_TAC[plain_cubic_pentagonal];
      MATCH_MP_TAC THE_DBOUND1_CHECK THEN
      UNDISCH_TAC `mem_range Pr58 n` THEN REWRITE_TAC[mem_range] THEN
      ARITH_TAC];
    MP_TAC(ISPECL [`n:num`; `FST (the_drule_fork n)`;
                   `SND (the_drule_fork n)`] SOURCE_DRULES_RANGE) THEN
    ASM_REWRITE_TAC[DRULE_FORK_VALUES_THE] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DBOUND1_NIL] THEN ARITH_TAC]);;

(* Coq unavoidability.                                                       *)
let UNAVOIDABILITY_CHECK = prove
 (`check_reducibility ==> !G:(A)hypermap. ~(minimal_counter_example G)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `G:(A)hypermap` POSZ_DSCORE) THEN
  ASM_SIMP_TAC[MCE_PLAIN_CUBIC_CONNECTED; MCE_PLANAR; MCE_DART_NONEMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `valid_hub (G:(A)hypermap) x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[valid_hub]; ALL_TAC] THEN
  SUBGOAL_THEN `5 <= arity G (x:A) /\ arity G x < 12` MP_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`G:(A)hypermap`; `x:A`] PENTA_PR59) THEN
      ASM_SIMP_TAC[MCE_PENTAGONAL; mem_range];
      MP_TAC(ISPECL [`G:(A)hypermap`; `5`] DSCORE_CAP1) THEN
      ASM_SIMP_TAC[DSCORE1_LE5] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o SPEC `12`) THEN
      ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY (fun th ->
    MP_TAC(SPECL [`G:(A)hypermap`; `x:A`]
           (MATCH_MP (REWRITE_RULE[excluded_arity] th)
                     (ASSUME `check_reducibility`))))
  [exclude5; exclude6; exclude7; exclude8; exclude9; exclude10; exclude11] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;
