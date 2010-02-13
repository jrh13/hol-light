(* ========================================================================= *)
(* #73: Erdos-Szekeres theorem on ascending / descending subsequences.       *)
(* ========================================================================= *)

let lemma = prove
 (`!f s. s = UNIONS (IMAGE (\a. {x | x IN s /\ f(x) = a}) (IMAGE f s))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN GEN_TAC THEN 
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_IMAGE] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
  REWRITE_TAC[UNWIND_THM2; GSYM CONJ_ASSOC; IN_ELIM_THM] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Pigeonhole lemma.                                                         *)
(* ------------------------------------------------------------------------- *)

let PIGEONHOLE_LEMMA = prove
 (`!f:A->B s n. 
        FINITE s /\ (n - 1) * CARD(IMAGE f s) < CARD s
        ==> ?t a. t SUBSET s /\ t HAS_SIZE n /\ (!x. x IN t ==> f(x) = a)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPECL [`f:A->B`; `s:A->bool`] lemma) THEN DISCH_THEN(fun th -> 
    GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV) [th]) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[NOT_LT] THEN
  STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN MATCH_MP_TAC
   (REWRITE_RULE[SET_RULE `{t x | x IN s} = IMAGE t s`] CARD_UNIONS_LE) THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_IMAGE] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:A->bool` THEN
    ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC(ARITH_RULE `~(n <= x) ==> x <= n - 1`) THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPEC `{y | y IN s /\ (f:A->B) y = f x}` CHOOSE_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Abbreviation for "monotonicity of f on s w.r.t. ordering r".              *)
(* ------------------------------------------------------------------------- *)

let mono_on = define
 `mono_on (f:num->real) r s <=> 
    !i j. i IN s /\ j IN s /\ i <= j ==> r (f i) (f j)`;;

let MONO_ON_SUBSET = prove
 (`!s t. t SUBSET s /\ mono_on f r s ==> mono_on f r t`,
  REWRITE_TAC[mono_on; SUBSET] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The main result.                                                          *)
(* ------------------------------------------------------------------------- *)

let ERDOS_SZEKERES = prove
 (`!f:num->real m n.
        (?s. s SUBSET (1..m*n+1) /\ s HAS_SIZE (m + 1) /\ mono_on f (<=) s) \/
        (?s. s SUBSET (1..m*n+1) /\ s HAS_SIZE (n + 1) /\ mono_on f (>=) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i IN (1..m*n+1)
        ==> ?k. (?s. s SUBSET (1..m*n+1) /\ s HAS_SIZE k /\ 
                     mono_on f (<=) s /\ i IN s /\ (!j. j IN s ==> i <= j)) /\
                (!l. (?s. s SUBSET (1..m*n+1) /\ s HAS_SIZE l /\
                     mono_on f (<=) s /\ i IN s /\ (!j. j IN s ==> i <= j))
                     ==> l <= k)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM num_MAX] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`1`; `{i:num}`] THEN
      ASM_SIMP_TAC[SUBSET; IN_SING; LE_REFL; HAS_SIZE; FINITE_INSERT] THEN
      SIMP_TAC[FINITE_RULES; CARD_CLAUSES; NOT_IN_EMPTY; ARITH] THEN
      SIMP_TAC[mono_on; IN_SING; REAL_LE_REFL];
      EXISTS_TAC `CARD(1..m*n+1)` THEN
      ASM_MESON_TAC[CARD_SUBSET; FINITE_NUMSEG; HAS_SIZE]];
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:num->num` (LABEL_TAC "*" ))] THEN
  ASM_CASES_TAC `?i. i IN (1..m*n+1) /\ m + 1 <= t(i)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:num->bool` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    MP_TAC(ISPEC `s:num->bool` CHOOSE_SUBSET) THEN
    ASM_MESON_TAC[HAS_SIZE; MONO_ON_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN (1..m*n+1) ==> 1 <= t i /\ t i <= m` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC MONO_FORALL) THEN
    X_GEN_TAC `i:num` THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `1` o CONJUNCT2) THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[ARITH_RULE `~(m + 1 <= n) ==> n <= m`]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `{i:num}` THEN
    ASM_SIMP_TAC[SUBSET; IN_SING; LE_REFL; HAS_SIZE; FINITE_INSERT] THEN
    SIMP_TAC[FINITE_RULES; CARD_CLAUSES; NOT_IN_EMPTY; ARITH] THEN
    SIMP_TAC[mono_on; IN_SING; REAL_LE_REFL];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  SUBGOAL_THEN
   `?s k:num. s SUBSET (1..m*n+1) /\ s HAS_SIZE (n + 1) /\
              !i. i IN s ==> t(i) = k`
  MP_TAC THENL
   [MATCH_MP_TAC PIGEONHOLE_LEMMA THEN
    REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1; ADD_SUB] THEN
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n * CARD(1..m)` THEN 
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[CARD_NUMSEG_1] THEN ARITH_TAC] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN 
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:num->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN 
  ASM_REWRITE_TAC[mono_on] THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  REWRITE_TAC[LE_LT; real_ge] THEN STRIP_TAC THEN 
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  REMOVE_THEN "*" (fun th -> 
    MP_TAC(SPEC `i:num` th) THEN MP_TAC(SPEC `j:num` th)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->bool` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `k + 1` o CONJUNCT2) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k + 1 <= k)`; GSYM REAL_NOT_LT] THEN
  REWRITE_TAC[CONTRAPOS_THM] THEN 
  DISCH_TAC THEN EXISTS_TAC `(i:num) INSERT s` THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    REWRITE_TAC[HAS_SIZE_CLAUSES; GSYM ADD1] THEN ASM_MESON_TAC[NOT_LT];
    ALL_TAC;
    REWRITE_TAC[IN_INSERT];
    ASM_MESON_TAC[IN_INSERT; LE_REFL; LT_IMP_LE; LE_TRANS]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mono_on]) THEN
  REWRITE_TAC[mono_on; IN_INSERT] THEN
  ASM_MESON_TAC[REAL_LE_REFL; REAL_LE_TRANS; REAL_LT_IMP_LE; NOT_LE;
                LT_REFL; LE_TRANS]);;
