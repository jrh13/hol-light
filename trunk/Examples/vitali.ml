(* ========================================================================= *)
(* Existence of a (bounded) non-measurable set of reals.                     *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* Classic Vitali proof (positive case simplified via Steinhaus's theorem).  *)
(* ------------------------------------------------------------------------- *)

let NON_MEASURABLE_SET = prove
 (`?s. real_bounded s /\ ~real_measurable s`,
  MAP_EVERY ABBREV_TAC
   [`equiv = \x y. &0 <= x /\ x < &1 /\ &0 <= y /\ y < &1 /\ rational(x - y)`;
    `(canonize:real->real) = \x. @y. equiv x y`;
    `V = IMAGE (canonize:real->real) {x | &0 <= x /\ x < &1}`] THEN
  SUBGOAL_THEN `!x. equiv x x <=> &0 <= x /\ x < &1` ASSUME_TAC THENL
   [EXPAND_TAC "equiv" THEN REWRITE_TAC[REAL_SUB_REFL; RATIONAL_NUM; CONJ_ACI];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real. equiv x y ==> equiv y x` ASSUME_TAC THENL
   [EXPAND_TAC "equiv" THEN MESON_TAC[RATIONAL_NEG; REAL_NEG_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y z:real. equiv x y /\ equiv y z ==> equiv x z`
  ASSUME_TAC THENL
   [EXPAND_TAC "equiv" THEN MESON_TAC[RATIONAL_ADD;
        REAL_ARITH `x - z:real = (x - y) + (y - z)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. &0 <= x /\ x < &1 ==> (equiv:real->real->bool) x (canonize x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "canonize" THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN V /\ y IN V /\ rational(x - y) ==> x = y`
  ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    X_GEN_TAC `y:real` THEN STRIP_TAC THEN STRIP_TAC THEN
    EXPAND_TAC "canonize" THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real` THEN
    SUBGOAL_THEN `equiv ((canonize:real->real) x) (canonize y) :bool`
     (fun th -> MP_TAC th THEN ASM_MESON_TAC[]) THEN
    EXPAND_TAC "equiv" THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `V:real->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_BOUNDED_SUBSET THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN
    REWRITE_TAC[REAL_BOUNDED_REAL_INTERVAL; SUBSET; IN_REAL_INTERVAL] THEN
    ASM SET_TAC[REAL_LT_IMP_LE];
    DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_REAL_MEASURE_MEASURE]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_MEASURE_POS_LE) THEN
  REWRITE_TAC[REAL_ARITH `&0 <= x <=> &0 < x \/ x = &0`] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC) THENL
   [MP_TAC(ISPEC `V:real->bool` REAL_STEINHAUS) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MP_TAC(ISPECL [`d / &2`; `d / &2`] RATIONAL_APPROXIMATION) THEN
    ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `q:real` THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `q:real`) THEN REWRITE_TAC[NOT_IMP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `q = &0` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[REAL_SUB_0];
    REWRITE_TAC[HAS_REAL_MEASURE_0] THEN DISCH_TAC THEN
    SUBGOAL_THEN `?r. rational = IMAGE r (:num)` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC COUNTABLE_AS_IMAGE THEN REWRITE_TAC[COUNTABLE_RATIONAL] THEN
      REWRITE_TAC[FUN_EQ_THM; EMPTY] THEN MESON_TAC[RATIONAL_NUM];
      ALL_TAC] THEN
    MP_TAC(ISPEC `\n. IMAGE (\x. (r:num->real) n + x) V`
      REAL_NEGLIGIBLE_COUNTABLE_UNIONS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_NEGLIGIBLE_TRANSLATION]; ALL_TAC] THEN
    SUBGOAL_THEN `~(real_negligible(real_interval(&0,&1)))` MP_TAC THENL
     [SIMP_TAC[GSYM REAL_MEASURABLE_REAL_MEASURE_EQ_0;
               REAL_MEASURABLE_REAL_INTERVAL; REAL_MEASURE_REAL_INTERVAL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_NEGLIGIBLE_SUBSET) THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(equiv:real->real->bool) x (canonize x)` MP_TAC THENL
     [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    EXPAND_TAC "equiv" THEN ASM_REWRITE_TAC[] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM IN] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (ASSUME_TAC o SYM)) THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[UNIONS_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `(canonize:real->real) x`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "V" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]);;
