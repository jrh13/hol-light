(* ========================================================================= *)
(* Dickson's lemma.                                                          *)
(* ========================================================================= *)

let MINIMIZING_CHOICE = prove
 (`!(m:A->num) s. (?x. P x) ==> ?a. P a /\ !b. P b ==> m(a) <= m(b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN
  MP_TAC(ISPEC `\n. ?x. P x /\ (m:A->num) x = n` num_WOP) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Nash-Williams minimal bad sequence argument for some predicate `bad`  *)
(* that is a "safety property" in the Lamport/Alpern/Schneider sense.        *)
(* ------------------------------------------------------------------------- *)

let MINIMAL_BAD_SEQUENCE = prove
 (`!(bad:(num->A)->bool) (m:A->num).
     (!x. ~bad x ==> ?n. !y. (!k. k < n ==> y k = x k) ==> ~bad y) /\
     (?x. bad x)
      ==> ?y. bad y /\
              !z n. bad z /\ (!k. k < n ==> z k = y k) ==> m(y n) <= m(z n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN
   `?x. !n. (x:num->A) n =
             @a. (?y. bad y /\ (!k. k < n ==> y k = x k) /\ y n = a) /\
                 !z. bad z /\ (!k. k < n ==> z k = x k)
                     ==> (m:A->num)(a) <= m(z n)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(MATCH_MP WF_REC WF_num) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (?y:num->A. bad y /\ (!k. k < n ==> y k = x k) /\ y n = x n) /\
        !z. bad z /\ (!k. k < n ==> z k = x k) ==> m(x n):num <= m(z n)`
  ASSUME_TAC THENL [ALL_TAC; EXISTS_TAC `x:num->A` THEN ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  FIRST_X_ASSUM(fun th -> DISCH_TAC THEN SUBST1_TAC(SPEC `n:num` th)) THEN
  CONV_TAC SELECT_CONV THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `(p /\ q /\ r) /\ s <=> r /\ p /\ q /\ s`] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM1] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN MATCH_MP_TAC MINIMIZING_CHOICE THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN SPEC_TAC(`n:num`,`n:num`) THEN 
  INDUCT_TAC THEN SIMP_TAC[LT] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Dickson's Lemma itself.                                                   *)
(* ------------------------------------------------------------------------- *)

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
   [MATCH_MP_TAC MINIMAL_BAD_SEQUENCE THEN ASM_REWRITE_TAC[] THEN
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
