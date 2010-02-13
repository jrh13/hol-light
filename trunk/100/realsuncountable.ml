(* ========================================================================= *)
(* #22: non-denumerability of continuum (= uncountability of the reals).     *)
(* ========================================================================= *)

needs "Library/card.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Definition of countability.                                               *)
(* ------------------------------------------------------------------------- *)

let countable = new_definition
  `countable s <=> s <=_c (UNIV:num->bool)`;;

(* ------------------------------------------------------------------------- *)
(* Set of repeating digits and its countability.                             *)
(* ------------------------------------------------------------------------- *)

let repeating = new_definition
 `repeating = {s:num->bool | ?n. !m. m >= n ==> s m}`;;

let BINARY_BOUND = prove
(`!n. nsum(0..n) (\i. if b(i) then 2 EXP i else 0) < 2 EXP (n + 1)`,
  INDUCT_TAC THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[ARITH]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[LE_0; EXP_ADD; EXP_1; EXP] THEN
  ARITH_TAC);;

let BINARY_DIV_POW2 = prove
 (`!n. (nsum(0..n) (\i. if b(i) then 2 EXP i else 0)) DIV (2 EXP (SUC n)) = 0`,
  SIMP_TAC[ADD1; DIV_LT; BINARY_BOUND]);;

let PLUS_MOD_REFL = prove
 (`!a b. ~(b = 0) ==> (a + b) MOD b = a MOD b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_EQ THEN MESON_TAC[MULT_CLAUSES]);;

let BINARY_PLUS_DIV_POW2 = prove
 (`!n. (nsum(0..n) (\i. if b(i) then 2 EXP i else 0) + 2 EXP (SUC n))
       DIV (2 EXP (SUC n)) = 1`,
  GEN_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `nsum(0..n) (\i. if b(i) then 2 EXP i else 0)` THEN
  ASM_REWRITE_TAC[BINARY_BOUND; ADD1] THEN
  REWRITE_TAC[ADD_AC; MULT_CLAUSES]);;

let BINARY_UNIQUE_LEMMA = prove
 (`!n. nsum(0..n) (\i. if b(i) then 2 EXP i else 0) =
       nsum(0..n) (\i. if c(i) then 2 EXP i else 0)
       ==> !i. i <= n ==> (b(i) <=> c(i))`,
  INDUCT_TAC THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THENL
   [SIMP_TAC[LE] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH]);
    REWRITE_TAC[LE_0]] THEN
  REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THENL
   [UNDISCH_THEN `i = SUC n` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x DIV (2 EXP (SUC n))`) THEN
    REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; BINARY_DIV_POW2; BINARY_PLUS_DIV_POW2] THEN
    REWRITE_TAC[ARITH_EQ];
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD (2 EXP (SUC n))`) THEN
    REPEAT COND_CASES_TAC THEN
    SIMP_TAC[ADD_CLAUSES; BINARY_BOUND; MOD_LT; PLUS_MOD_REFL; EXP_EQ_0; ARITH;
             ADD1] THEN
    ASM_MESON_TAC[LE_REFL]]);;

let COUNTABLE_REPEATING = prove
 (`countable repeating`,
  REWRITE_TAC[countable] THEN
  TRANS_TAC CARD_LE_TRANS `(UNIV:num->bool) *_c (UNIV:num->bool)` THEN
  CONJ_TAC THENL
    [ALL_TAC;
     MATCH_MP_TAC CARD_EQ_IMP_LE THEN REWRITE_TAC[CARD_SQUARE_NUM]] THEN
  REWRITE_TAC[le_c] THEN EXISTS_TAC
   `\s:num->bool. let n = minimal n. !m. m >= n ==> s m in
                  n,nsum(0..n) (\i. if s(i) then 2 EXP i else 0)` THEN
  REWRITE_TAC[repeating; IN_ELIM_THM] THEN CONJ_TAC THENL
   [GEN_TAC THEN LET_TAC THEN REWRITE_TAC[mul_c; IN_ELIM_THM; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:num->bool`; `t:num->bool`] THEN
  ONCE_REWRITE_TAC[MINIMAL] THEN
  ABBREV_TAC `k = minimal n. !m. m >= n ==> s m` THEN
  ABBREV_TAC `l = minimal n. !m. m >= n ==> t m` THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN
  ASM_CASES_TAC `l:num = k` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[FUN_EQ_THM; GE] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP BINARY_UNIQUE_LEMMA) THEN
  ASM_MESON_TAC[LE_CASES]);;

(* ------------------------------------------------------------------------- *)
(* Canonical digits and their uncountability.                                *)
(* ------------------------------------------------------------------------- *)

let canonical = new_definition
 `canonical = {s:num->bool | !n. ?m. m >= n /\ ~(s m)}`;;

let UNCOUNTABLE_CANONICAL = prove
 (`~countable canonical`,
  REWRITE_TAC[countable] THEN STRIP_TAC THEN
  MP_TAC (INST_TYPE [`:num`,`:A`] CANTOR_THM_UNIV) THEN
  REWRITE_TAC[CARD_NOT_LT] THEN
  MP_TAC(ISPECL [`canonical`; `repeating`] CARD_DISJOINT_UNION) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM;
                canonical; repeating; GE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `canonical UNION repeating = UNIV` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM;
                canonical; repeating; GE; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN TRANS_TAC CARD_LE_TRANS `canonical +_c repeating` THEN
  ASM_SIMP_TAC[CARD_EQ_IMP_LE] THEN
  TRANS_TAC CARD_LE_TRANS `(UNIV:num->bool) +_c (UNIV:num->bool)` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[countable; COUNTABLE_REPEATING; CARD_LE_ADD];
    MATCH_MP_TAC CARD_ADD_ABSORB_LE THEN
    REWRITE_TAC[num_INFINITE; CARD_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Injection of canonical digits into the reals.                             *)
(* ------------------------------------------------------------------------- *)

needs "Library/analysis.ml";;

prioritize_real();;

let SUM_BINSEQUENCE_LBOUND = prove
 (`!m n. &0 <= sum(m,n) (\i. if s(i) then inv(&2 pow i) else &0)`,
  MATCH_MP_TAC SUM_POS THEN GEN_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_LE_INV_EQ] THEN
  SIMP_TAC[REAL_POW_LE; REAL_POS]);;

let SUM_BINSEQUENCE_UBOUND_SHARP = prove
 (`!s m n. sum(m,n) (\i. if s(i) then inv(&2 pow i) else &0)
             <= &2 / &2 pow m - &2 / &2 pow (m + n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[sum] THEN
  REWRITE_TAC[ADD_CLAUSES; REAL_SUB_REFL; REAL_LE_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= y /\ x + y <= a ==> x + (if b then y else &0) <= a`) THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `x <= a ==> a + y <= b ==> x + y <= b`)) THEN
  REWRITE_TAC[real_pow; real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC);;

let SUMMABLE_BINSEQUENCE = prove
 (`!s. summable (\i. if s(i) then inv(&2 pow i) else &0)`,
  GEN_TAC THEN REWRITE_TAC[summable; sums; GSYM convergent] THEN
  MATCH_MP_TAC SEQ_ICONV THEN REWRITE_TAC[MR1_BOUNDED] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`&2`; `0`] THEN
    REWRITE_TAC[GE; LE_0; LE_REFL] THEN X_GEN_TAC `n:num` THEN
    MP_TAC(SPECL [`s:num->bool`; `0`; `n:num`]
         SUM_BINSEQUENCE_UBOUND_SHARP) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ a < b ==> x <= a ==> abs x < b`) THEN
    REWRITE_TAC[SUM_BINSEQUENCE_LBOUND; real_pow; REAL_DIV_1; ADD_CLAUSES] THEN
    REWRITE_TAC[REAL_ARITH `a - x < a <=> &0 < x`] THEN
    SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT; ARITH];
    GEN_TAC THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[GE; LE_EXISTS] THEN
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC[GSYM SUM_SPLIT] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> a + x >= a`) THEN
    REWRITE_TAC[SUM_BINSEQUENCE_LBOUND]]);;

let SUMS_BINSEQUENCE = prove
 (`!s. (\i. if s(i) then inv(&2 pow i) else &0) sums
       (suminf (\i. if s(i) then inv(&2 pow i) else &0))`,
  SIMP_TAC[SUMMABLE_SUM; SUMMABLE_BINSEQUENCE]);;

let SUM_BINSEQUENCE_UBOUND_LE = prove
 (`!s m n. sum(m,n) (\i. if s(i) then inv(&2 pow i) else &0) <= &2 / &2 pow m`,
  MP_TAC SUM_BINSEQUENCE_UBOUND_SHARP THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> x <= a - b ==> x <= a`) THEN
  SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_POS]);;

(* ------------------------------------------------------------------------- *)
(* The main injection and hence main theorem.                                *)
(* ------------------------------------------------------------------------- *)

let SUMINF_INJ_LEMMA = prove
 (`!s t n. ~(s n) /\ t n /\
           (!m. m < n ==> (s(m) <=> t(m))) /\
           (!n. ?m. m >= n /\ ~(s m))
           ==> suminf(\n. if s n then inv (&2 pow n) else &0)
                < suminf(\n. if t n then inv (&2 pow n) else &0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `sum(0,n+1) (\n. if t n then inv (&2 pow n) else &0)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SEQ_LE THEN MAP_EVERY EXISTS_TAC
     [`\k:num. sum(0,n+1) (\n. if t n then inv (&2 pow n) else &0)`;
      `\n:num. sum(0,n) (\n. if t n then inv (&2 pow n) else &0)`] THEN
    REWRITE_TAC[SEQ_CONST; GSYM sums; SUMS_BINSEQUENCE] THEN
    EXISTS_TAC `n + 1` THEN X_GEN_TAC `m:num` THEN
    REWRITE_TAC[GE; LE_EXISTS] THEN DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC[GSYM ADD1] THEN
    REWRITE_TAC[GSYM SUM_SPLIT; REAL_LE_ADDR; SUM_BINSEQUENCE_LBOUND]] THEN
  ASM_REWRITE_TAC[GSYM SUM_SPLIT; SUM_1; ADD_CLAUSES] THEN
  UNDISCH_THEN `!n:num. ?m. m >= n /\ ~s m` (MP_TAC o SPEC `n + 1`) THEN
  REWRITE_TAC[GE] THEN DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
    `sum(0,m) (\n. if s n then inv (&2 pow n) else &0) + inv(&2 pow m)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SEQ_LE THEN MAP_EVERY EXISTS_TAC
     [`\n:num. sum(0,n) (\n. if s n then inv (&2 pow n) else &0)`;
      `\k:num. sum(0,m) (\n. if s n then inv(&2 pow n) else &0) +
               inv(&2 pow m)`] THEN
    REWRITE_TAC[SEQ_CONST; GSYM sums; SUMS_BINSEQUENCE] THEN
    EXISTS_TAC `m:num` THEN REWRITE_TAC[GE; LE_REFL] THEN
    X_GEN_TAC `r:num` THEN REWRITE_TAC[LE_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST_ALL_TAC) THEN
    REWRITE_TAC[GSYM SUM_SPLIT; REAL_LE_LADD; ADD_CLAUSES] THEN
    DISJ_CASES_THEN SUBST_ALL_TAC (ARITH_RULE `p = 0 \/ p = 1 + PRE p`) THEN
    SIMP_TAC[sum; REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
    ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN
    ASM_REWRITE_TAC[SUM_1; REAL_ADD_LID] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 / &2 pow (m + 1)` THEN
    REWRITE_TAC[SUM_BINSEQUENCE_UBOUND_LE] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[GSYM SUM_SPLIT] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; SUM_1; REAL_ADD_RID] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b /\ c < e - d ==> (a + c) + d < b + e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[LE_0; ADD_CLAUSES]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&2 / &2 pow (n + 1) - &2 / &2 pow ((n + 1) + r)` THEN
  REWRITE_TAC[SUM_BINSEQUENCE_UBOUND_SHARP] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b /\ d < c ==> a - c < b - d`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC(REAL_FIELD `&0 < inv(x) ==> inv(x) < &2 / x`) THEN
    SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH]]);;

let UNCOUNTABLE_REALS = prove
 (`~countable(UNIV:real->bool)`,
  MP_TAC UNCOUNTABLE_CANONICAL THEN REWRITE_TAC[CONTRAPOS_THM] THEN
  REWRITE_TAC[countable] THEN DISCH_TAC THEN
  TRANS_TAC CARD_LE_TRANS `UNIV:real->bool` THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM(K ALL_TAC) THEN REWRITE_TAC[le_c] THEN
  EXISTS_TAC `\s. suminf(\n. if s(n) then inv(&2 pow n) else &0)` THEN
  REWRITE_TAC[IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`s:num->bool`; `t:num->bool`] THEN
  REWRITE_TAC[canonical; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_REWRITE_TAC I [MESON[] `(!x. P x) <=> ~(?x. ~P x)`] THEN
  ONCE_REWRITE_TAC[MINIMAL] THEN
  ABBREV_TAC `n = minimal x. ~(s x <=> t x)` THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_var o rhs o concl)) THEN
  ASM_CASES_TAC `(t:num->bool) n` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SYM) THENL
   [MATCH_MP_TAC(REAL_ARITH `b < a ==> a = b ==> F`);
    MATCH_MP_TAC(REAL_ARITH `a < b ==> a = b ==> F`)] THEN
  MATCH_MP_TAC SUMINF_INJ_LEMMA THEN ASM_MESON_TAC[]);;
