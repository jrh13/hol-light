(* ========================================================================= *)
(* Dickson's lemma. This is a direct application of the minimal bad sequence *)
(* argument a la Nash-Williams (MINIMAL_BAD_SEQUENCE). There is also a proof *)
(* of the same result in "Library/wo.ml" as part of a more systematic theory *)
(* of well quasi-orderings.                                                  *)
(* ========================================================================= *)

let DICKSON = prove
 (`!n x:num->num->num. ?i j. i < j /\ (!k. k < n ==> x i k <= x j k)`,
  ABBREV_TAC
   `bad = \n x:num->num->num. !i j. i < j ==> ?k. k < n /\ x j k < x i k` THEN
  SUBGOAL_THEN `!n:num x:num->num->num. ~(bad n x)` MP_TAC THENL
   [ALL_TAC; EXPAND_TAC "bad" THEN MESON_TAC[NOT_LT]] THEN
  INDUCT_TAC THENL [EXPAND_TAC "bad" THEN MESON_TAC[LT]; ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_EXISTS_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?x. bad (SUC n) (x:num->num->num) /\
        !y j. bad (SUC n) y /\ (!i. i < j ==> y i = x i)
              ==> x j n <= y j n`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN
    MATCH_MP_TAC MINIMAL_BAD_SEQUENCE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC
    THENL [MATCH_ACCEPT_TAC(MATCH_MP WF_MEASURE_GEN WF_num); ALL_TAC] THEN
    X_GEN_TAC `x:num->num->num` THEN EXPAND_TAC "bad" THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    EXISTS_TAC `SUC j` THEN X_GEN_TAC `y:num->num->num` THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [LT_SUC_LE] THEN
    REWRITE_TAC[LE_LT] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `~(bad (n:num) (x:num->num->num))` MP_TAC THENL
     [ASM_MESON_TAC[]; EXPAND_TAC "bad" THEN REWRITE_TAC[]] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN
    MP_TAC(ASSUME `bad (SUC n) (x:num->num->num):bool`) THEN
    EXPAND_TAC "bad" THEN REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ASM_REWRITE_TAC[LT] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[LT_REFL] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC
     `\k. if k < i then (x:num->num->num) k else x (j + k - i)`) THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[LT_REFL; SUB_REFL; ADD_CLAUSES; NOT_IMP; NOT_LE] THEN
    SIMP_TAC[] THEN UNDISCH_TAC `bad (SUC n) (x:num->num->num):bool` THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN EXPAND_TAC "bad" THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
    REPEAT GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_MESON_TAC[LT_TRANS; ARITH_RULE
      `(a:num < i /\ ~(b < i) /\ i < j ==> a < j + b - i) /\
       (~(a < i) /\ a < b /\ i < j ==> j + a - i < j + b - i)`]]);;
