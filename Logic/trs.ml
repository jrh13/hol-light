(* ========================================================================= *)
(* Basic definitions for and theorems about term rewriting.                  *)
(* ========================================================================= *)

let TRS_RULES,TRS_INDUCT,TRS_CASES = new_inductive_definition
  `(!i l r.
         (l,r) IN rws ==> TRS rws (termsubst i l) (termsubst i r)) /\
   (!s t f largs rargs.
         TRS rws s t ==> TRS rws (Fn f (APPEND largs (CONS s rargs)))
                                 (Fn f (APPEND largs (CONS t rargs))))`;;

(* ------------------------------------------------------------------------- *)
(* Nice general result justfying both deletion and right-simplification.     *)
(* ------------------------------------------------------------------------- *)

let CONVERGENT_MODIFY_LEMMA = prove
 (`!R S. SN R /\
         CR(RTC R) /\
         (!x y. S x y ==> TC R x y) /\
         (!x y. R x y ==> ?y'. S x y')
         ==> !y:A. NORMAL(R) y ==> !x. RTC R x y ==> RTC S x y`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM SN_TC] THEN
  REWRITE_TAC[SN_NOETHERIAN] THEN STRIP_TAC THEN
  GEN_TAC THEN REWRITE_TAC[NORMAL; NOT_EXISTS_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [RTC_CASES_R] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THEN
  REWRITE_TAC[RTC_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `!x:A y:A. R x y ==> (?y':A. S x y')` THEN
  DISCH_THEN(MP_TAC o SPECL [`x:A`; `u:A`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:A`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `v:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CR]) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:A`; `y:A`; `v:A`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[RTC_CASES_R; TC_RTC_CASES_R]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `z:A = y` SUBST_ALL_TAC THEN ASM_MESON_TAC[RTC_CASES_R]);;

let CONVERGENT_MODIFY = prove
 (`!R S. SN R /\
         CR(RTC R) /\
         (!x:A y. S x y ==> TC R x y) /\
         (!x:A y. R x y ==> ?y'. S x y')
         ==> SN(S) /\ CR(RTC S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SN_WF] THEN MATCH_MP_TAC WF_SUBSET THEN
    EXISTS_TAC `INV(TC(R:A->A->bool))` THEN ASM_REWRITE_TAC[INV] THEN
    REWRITE_TAC[GSYM TC_INV; WF_TC] THEN ASM_REWRITE_TAC[GSYM SN_WF];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC NEWMAN_LEMMA THEN ASM_REWRITE_TAC[WCR] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y1:A`; `y2:A`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CR]) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:A`; `y1:A`; `y2:A`]) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[RTC_INC_TC]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(MATCH_MP SN_WN (ASSUME `SN(R:A->A->bool)`)) THEN
  REWRITE_TAC[WN] THEN DISCH_THEN(MP_TAC o SPEC `z0:A`) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`R:A->A->bool`; `S:A->A->bool`] CONVERGENT_MODIFY_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[RTC_TRANS]);;

let EQUIVALENT_JOINABLE_MODIFY = prove
 (`!R S. SN R /\
         CR(RTC R) /\
         (!x y. S x y ==> TC R x y) /\
         (!x y. R x y ==> ?y'. S x y')
         ==> (!x:A y. JOINABLE S x y = JOINABLE R x y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[JOINABLE] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `!x:A y. RTC S x y ==> RTC R x y`
     (fun th -> ASM_MESON_TAC[th]) THEN
    REWRITE_TAC[RTC; RC_CASES] THEN
    SUBGOAL_THEN `!x:A y. TC S x y ==> TC R x y`
     (fun th -> ASM_MESON_TAC[th]) THEN
    GEN_REWRITE_TAC (funpow 2 BINDER_CONV o RAND_CONV o ONCE_DEPTH_CONV)
     [GSYM TC_IDEMP] THEN
    MATCH_MP_TAC TC_MONO THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP SN_WN) THEN REWRITE_TAC[WN] THEN
    DISCH_THEN(MP_TAC o SPEC `z:A`) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`R:A->A->bool`; `S:A->A->bool`] CONVERGENT_MODIFY_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `w:A`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RTC_TRANS]]);;

let EQUIVALENT_RSTC_MODIFY = prove
 (`!R S. SN R /\
         CR(RTC R) /\
         (!x y. S x y ==> TC R x y) /\
         (!x y. R x y ==> ?y'. S x y')
         ==> (!x:A y. RSTC S x y = RSTC R x y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`R:A->A->bool`; `S:A->A->bool`] CONVERGENT_MODIFY) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`R:A->A->bool`; `S:A->A->bool`]
               EQUIVALENT_JOINABLE_MODIFY) THEN
  ASM_SIMP_TAC[CR_RSTC_JOINABLE] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]);;

let EQUIVALENT_MODIFY = prove
 (`!R S. SN R /\
         CR(RTC R) /\
         (!x y. S x y ==> TC R x y) /\
         (!x y. R x y ==> ?y'. S x y')
         ==> SN(S) /\ CR(RTC S) /\ (!x:A y. RSTC S x y = RSTC R x y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONVERGENT_MODIFY THEN EXISTS_TAC `R:A->A->bool`;
    MATCH_MP_TAC EQUIVALENT_RSTC_MODIFY] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Special case of right simplification of rules.                            *)
(* ------------------------------------------------------------------------- *)

let EQUIVALENT_MODIFY_RIGHT = prove
 (`!R S S'.
        SN(\x y. R x y \/ S x y) /\
        CR(RTC(\x y. R x y \/ S x y)) /\
        (!s:A t. S s t ==> ?t'. S' s t') /\
        (!s t. S' s t ==> ?u. S s u /\ RTC (\x y. R x y \/ S x y) u t)
        ==> SN(\x y. R x y \/ S' x y) /\
            CR(RTC(\x y. R x y \/ S' x y)) /\
            (!x y. RSTC(\x y. R x y \/ S' x y) x y =
                   RSTC(\x y. R x y \/ S x y) x y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC EQUIVALENT_MODIFY THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THENL
   [MATCH_MP_TAC TC_INC THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(S':A->A->bool) x y`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
    GEN_REWRITE_TAC I [TC_RTC_CASES_R] THEN
    EXISTS_TAC `u:A` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* And of deletion of joinable ones.                                         *)
(* ------------------------------------------------------------------------- *)

let CONVERGENT_DELETE_LEFT = prove
 (`!R S. SN(\x y. R x y \/ S x y) /\
         CR(RTC(\x y. R x y \/ S x y)) /\
         (!x:A y. S x y ==> ?z. R x z)
         ==> SN(R) /\ CR(RTC R) /\
             (!x y. RSTC(R) x y = RSTC(\x y. R x y \/ S x y) x y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC EQUIVALENT_MODIFY THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[TC_INC] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The case of left-simplification is harder; this lemma isn't enough.       *)
(* But given the deletion result above, we don't need this anyway!           *)
(* ------------------------------------------------------------------------- *)

let CONVERGENT_MODIFY_LEMMA = prove
 (`!R S S' t.
        SN(\x y. R x y \/ S x y \/ S' x y) /\
        CR(RTC(\x y. R x y \/ S x y)) /\
        (!s t. S s t
               ==> ?s' t'. RTC R s s' /\ RTC R t t' /\
                           (S' s' t' \/ S' t' s')) /\
        NORMAL(\x y. R x y \/ S x y) t
        ==> !s:A. RTC (\x y. R x y \/ S x y) s t
                  ==> RTC (\x y. R x y \/ S' x y) s t`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM SN_TC] THEN
  REWRITE_TAC[SN_NOETHERIAN] THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  X_GEN_TAC `s:A` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [RTC_CASES_R] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THEN
  REWRITE_TAC[RTC_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THENL
   [FIRST_ASSUM(fun th -> MP_TAC(SPEC `u:A` th) THEN ANTS_TAC) THENL
     [ONCE_REWRITE_TAC[TC_CASES_R] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ONCE_REWRITE_TAC[RTC_CASES_R] THEN
    DISJ2_TAC THEN EXISTS_TAC `u:A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:A`; `u:A`]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s':A`; `u':A`] THEN STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `u':A`) THEN ANTS_TAC THENL
     [ONCE_REWRITE_TAC[TC_RTC_CASES_R] THEN EXISTS_TAC `u:A` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `RTC R (u:A) u'` THEN
      MAP_EVERY (fun s -> SPEC_TAC(s,s)) [`u':A`; `u:A`] THEN
      MATCH_MP_TAC RTC_MONO THEN SIMP_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CR]) THEN
    DISCH_THEN(MP_TAC o SPECL [`s:A`; `u':A`; `t:A`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ONCE_REWRITE_TAC[RTC_CASES_R] THEN DISJ2_TAC THEN EXISTS_TAC `u:A` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `RTC R (u:A) u'` THEN
        MAP_EVERY (fun s -> SPEC_TAC(s,s)) [`u':A`; `u:A`] THEN
        MATCH_MP_TAC RTC_MONO THEN SIMP_TAC[];
        ALL_TAC] THEN
      ONCE_REWRITE_TAC[RTC_CASES_R] THEN DISJ2_TAC THEN EXISTS_TAC `u:A` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `z:A = t` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `RTC (\x y. R x y \/ S x y) t (z:A)` THEN
      ONCE_REWRITE_TAC[RTC_CASES_R] THEN
      ASM_CASES_TAC `z:A = t` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NORMAL]) THEN
      REWRITE_TAC[] THEN MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[RTC_CASES] THEN DISJ2_TAC THEN
    EXISTS_TAC `u':A` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[RTC_CASES_L] THEN DISJ2_TAC THEN
    EXISTS_TAC `s':A` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `RTC R (s:A) s'` THEN
    MAP_EVERY (fun s -> SPEC_TAC(s,s)) [`s':A`; `s:A`] THEN
    MATCH_MP_TAC RTC_MONO THEN SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `s':A = s` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[GSYM SN_NOETHERIAN; SN_WF]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP WF_REFL) THEN
    DISCH_THEN(MP_TAC o SPEC `s:A`) THEN REWRITE_TAC[INV] THEN
    MATCH_MP_TAC(TAUT `a ==> ~a ==> b`) THEN
    ONCE_REWRITE_TAC[TC_RTC_CASES_R] THEN EXISTS_TAC `u:A` THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[RTC_CASES_L] THEN DISJ2_TAC THEN EXISTS_TAC `u':A` THEN
    UNDISCH_THEN `s':A = s` SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `RTC R (u:A) u'` THEN
    MAP_EVERY (fun s -> SPEC_TAC(s,s)) [`u':A`; `u:A`] THEN
    MATCH_MP_TAC RTC_MONO THEN SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `s':A`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC RTC_NE_IMP_TC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `RTC R (s:A) s'` THEN
    MAP_EVERY (fun s -> SPEC_TAC(s,s)) [`s':A`; `s:A`] THEN
    MATCH_MP_TAC RTC_MONO THEN SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CR]) THEN
  DISCH_THEN(MP_TAC o SPECL [`s:A`; `s':A`; `t:A`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `RTC R (s:A) s'` THEN
      MAP_EVERY (fun s -> SPEC_TAC(s,s)) [`s':A`; `s:A`] THEN
      MATCH_MP_TAC RTC_MONO THEN SIMP_TAC[];
      ONCE_REWRITE_TAC[RTC_CASES_R] THEN DISJ2_TAC THEN EXISTS_TAC `u:A` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `z:A = t` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `RTC (\x y. R x y \/ S x y) t (z:A)` THEN
    ONCE_REWRITE_TAC[RTC_CASES_R] THEN
    ASM_CASES_TAC `z:A = t` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NORMAL]) THEN
    REWRITE_TAC[] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[RTC_CASES] THEN DISJ2_TAC THEN
  EXISTS_TAC `s':A` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `RTC R (s:A) s'` THEN
  MAP_EVERY (fun s -> SPEC_TAC(s,s)) [`s':A`; `s:A`] THEN
  MATCH_MP_TAC RTC_MONO THEN SIMP_TAC[]);;
