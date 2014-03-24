(* ========================================================================= *)
(* Nice little result that harmonic sum never gives an integer.              *)
(* ========================================================================= *)

needs "Library/prime.ml";;
needs "Library/products.ml";;
needs "Library/floor.ml";;

(* ------------------------------------------------------------------------- *)
(* In any contiguous range, index (order) of 2 has a strict maximum.         *)
(* ------------------------------------------------------------------------- *)

let NUMSEG_MAXIMAL_INDEX_2 = prove
 (`!m n. 1 <= m /\ m <= n
         ==> ?k. k IN m..n /\
                 !l. l IN m..n /\ ~(l = k) ==> index 2 l < index 2 k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\x. x IN IMAGE (index 2) (m..n)` num_MAX) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_NUMSEG] THEN
  ASM_REWRITE_TAC[MEMBER_NOT_EMPTY; IMAGE_EQ_EMPTY; NUMSEG_EMPTY; NOT_LT] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL [MESON_TAC[INDEX_TRIVIAL_BOUND; LE_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[LT_LE] THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:num`; `2`] INDEX_DECOMPOSITION_PRIME) THEN
  MP_TAC(SPECL [`k:num`; `2`] INDEX_DECOMPOSITION_PRIME) THEN
  REWRITE_TAC[PRIME_2; LEFT_IMP_EXISTS_THM; COPRIME_2] THEN
  ASM_CASES_TAC `k = 0` THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `l = 0` THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ARITH_RULE `~(l:num = k) ==> l < k \/ k < l`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN
  MAP_EVERY EXPAND_TAC ["k"; "l"] THEN
  REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `2 EXP index 2 k * (q + 1)`);
    FIRST_X_ASSUM(MP_TAC o SPEC `2 EXP index 2 k * (p + 1)`)] THEN
  ASM_SIMP_TAC[INDEX_MUL; PRIME_2; EXP_EQ_0; ADD_EQ_0; ARITH; NOT_IMP;
               INDEX_EXP; INDEX_REFL] THEN
  REWRITE_TAC[ARITH_RULE `n * 1 + k <= n <=> k = 0`; INDEX_EQ_0] THEN
  ASM_REWRITE_TAC[ADD_EQ_0; ARITH; DIVIDES_2; EVEN_ADD; NOT_EVEN] THEN
  MATCH_MP_TAC(ARITH_RULE
   `!p. m <= e * q /\ e * (q + 1) <= e * p /\ e * p <= n
         ==> m <= e * (q + 1) /\ e * (q + 1) <= n`)
  THENL [EXISTS_TAC `p:num`; EXISTS_TAC `q:num`] THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hence the result.                                                         *)
(* ------------------------------------------------------------------------- *)

let NONINTEGER_HARMONIC = prove
 (`!m n. 1 <= m /\ 1 < n /\ m <= n ==> ~(integer (sum(m..n) (\k. inv(&k))))`,
  let lemma = prove
   (`!m n. 1 <= m
           ==> sum(m..n) (\k. inv(&k)) =
               (sum(m..n) (\k. product ((m..n) DELETE k) (\i. &i))) /
               product(m..n) (\i. &i)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_FIELD
     `~(x = &0) /\ ~(z = &0) /\ x * y = z
      ==> inv x = y * inv z`) THEN
    ASM_SIMP_TAC[PRODUCT_EQ_0; FINITE_NUMSEG; IN_NUMSEG; REAL_OF_NUM_EQ] THEN
    REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    MP_TAC(ISPECL [`\i. &i`; `m..n`; `k:num`] PRODUCT_DELETE) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `n:num = m` THENL
   [ASM_REWRITE_TAC[SUM_SING_NUMSEG] THEN
    REWRITE_TAC[REAL_ARITH `inv x = &1 / x`; INTEGER_DIV; DIVIDES_ONE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[lemma] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_NPRODUCT; FINITE_NUMSEG; GSYM REAL_OF_NUM_SUM;
           FINITE_DELETE; INTEGER_DIV] THEN
  SIMP_TAC[NPRODUCT_EQ_0; FINITE_NUMSEG; IN_NUMSEG; DE_MORGAN_THM] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`m:num`; `n:num`] NUMSEG_MAXIMAL_INDEX_2) THEN
  ASM_REWRITE_TAC[IN_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\i. nproduct((m..n) DELETE i) (\j. j)`; `m..n`; `k:num`]
     NSUM_DELETE) THEN
  ASM_REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC `i = index 2 (nproduct ((m..n) DELETE k) (\j. j))` THEN
  MATCH_MP_TAC(EQT_ELIM(
   (REWRITE_CONV[IMP_CONJ; CONTRAPOS_THM] THENC (EQT_INTRO o NUMBER_RULE))
   `!p. p divides r /\ p divides n /\ ~(p divides m)
       ==> ~(r divides (m + n))`)) THEN
  EXISTS_TAC `2 EXP (i + 1)` THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC DIVIDES_NSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; FINITE_DELETE; IN_NUMSEG; IN_DELETE] THEN
    X_GEN_TAC `l:num` THEN STRIP_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX] THEN
  SIMP_TAC[ARITH; DE_MORGAN_THM; NPRODUCT_EQ_0; FINITE_NUMSEG; FINITE_DELETE;
           IN_NUMSEG; IN_DELETE]
  THENL
   [DISJ2_TAC THEN
    MP_TAC(ISPECL [`\i:num. i`; `m..n`; `k:num`] NPRODUCT_DELETE) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    DISCH_THEN(MP_TAC o AP_TERM `index 2`) THEN IMP_REWRITE_TAC[INDEX_MUL] THEN
    SIMP_TAC[NPRODUCT_EQ_0; FINITE_NUMSEG; FINITE_DELETE; PRIME_2] THEN
    REWRITE_TAC[IN_DELETE; IN_NUMSEG] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    FIRST_X_ASSUM(fun th ->
     MP_TAC(SPEC `m:num` th) THEN MP_TAC(SPEC `n:num` th)) THEN
    ASM_ARITH_TAC;
    DISJ2_TAC THEN
    MP_TAC(ISPECL [`\i:num. i`; `m..n`; `l:num`] NPRODUCT_DELETE) THEN
    MP_TAC(ISPECL [`\i:num. i`; `m..n`; `k:num`] NPRODUCT_DELETE) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; IMP_IMP] THEN
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o AP_TERM `index 2`)) THEN
    IMP_REWRITE_TAC[INDEX_MUL] THEN
    SIMP_TAC[NPRODUCT_EQ_0; FINITE_NUMSEG; FINITE_DELETE; PRIME_2] THEN
    REWRITE_TAC[IN_DELETE; IN_NUMSEG] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `l:num`) THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;
