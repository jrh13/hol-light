(* ========================================================================= *)
(* Arithmetic-geometric mean inequality.                                     *)
(* ========================================================================= *)

needs "Library/products.ml";;
prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* There's already one proof of this in "Library/agm.ml". This one is from  *)
(* an article by Michael Hirschhorn, Math. Intelligencer vol. 29, p7.        *)
(* ------------------------------------------------------------------------- *)

let LEMMA_1 = prove
 (`!x n. x pow (n + 1) - (&n + &1) * x + &n =
         (x - &1) pow 2 * sum(1..n) (\k. &k * x pow (n - k))`,
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ADD_CLAUSES] THENL
   [REAL_ARITH_TAC; REWRITE_TAC[ARITH_RULE `1 <= SUC n`]] THEN
  SIMP_TAC[ARITH_RULE `k <= n ==> SUC n - k = SUC(n - k)`; SUB_REFL] THEN
  REWRITE_TAC[real_pow; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ARITH `k * x * x pow n = (k * x pow n) * x`] THEN
  ASM_REWRITE_TAC[SUM_RMUL; REAL_MUL_ASSOC; REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_POW_ADD] THEN REAL_ARITH_TAC);;

let LEMMA_2 = prove
 (`!n x. &0 <= x ==> &0 <= x pow (n + 1) - (&n + &1) * x + &n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LEMMA_1] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_POW_LE]);;

let LEMMA_3 = prove
 (`!n x. 1 <= n /\ (!i. 1 <= i /\ i <= n + 1 ==> &0 <= x i)
         ==> x(n + 1) * (sum(1..n) x / &n) pow n
                <= (sum(1..n+1) x / (&n + &1)) pow (n + 1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `a = sum(1..n+1) x / (&n + &1)` THEN
  ABBREV_TAC `b = sum(1..n) x / &n` THEN
  SUBGOAL_THEN `x(n + 1) = (&n + &1) * a - &n * b` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; LE_1;
                 REAL_ARITH `~(&n + &1 = &0)`] THEN
    SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`; SUM_SING_NUMSEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a /\ &0 <= b` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_DIV THEN
    (CONJ_TAC THENL [MATCH_MP_TAC SUM_POS_LE_NUMSEG; REAL_ARITH_TAC]) THEN
    ASM_SIMP_TAC[ARITH_RULE `p <= n ==> p <= n + 1`];
    ALL_TAC] THEN
  ASM_CASES_TAC `b = &0` THEN
  ASM_SIMP_TAC[REAL_POW_ZERO; LE_1; REAL_MUL_RZERO; REAL_POW_LE] THEN
  MP_TAC(ISPECL [`n:num`; `a / b`] LEMMA_2) THEN ASM_SIMP_TAC[REAL_LE_DIV] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= x - a + b <=> a - b <= x`; REAL_POW_DIV] THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_POW_ADD] THEN UNDISCH_TAC `~(b = &0)` THEN
  CONV_TAC REAL_FIELD);;

let AGM = prove
 (`!n a. 1 <= n /\ (!i. 1 <= i /\ i <= n ==> &0 <= a(i))
         ==> product(1..n) a <= (sum(1..n) a / &n) pow n`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH; PRODUCT_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `1 <= SUC n`] THEN X_GEN_TAC `x:num->real` THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; ARITH; SUM_SING_NUMSEG] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[ADD1] THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN     
    EXISTS_TAC `x(n + 1) * (sum(1..n) x / &n) pow n` THEN
    ASM_SIMP_TAC[LEMMA_3; GSYM REAL_OF_NUM_ADD; LE_1;
                 ARITH_RULE `i <= n ==> i <= n + 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[LE_REFL; LE_1; ARITH_RULE `i <= n ==> i <= n + 1`]]);;

(* ------------------------------------------------------------------------- *)
(* Finally, reformulate in the usual way using roots.                        *)
(* ------------------------------------------------------------------------- *)

needs "Library/transc.ml";;

let AGM_ROOT = prove
 (`!n a. 1 <= n /\ (!i. 1 <= i /\ i <= n ==> &0 <= a(i))
         ==> root n (product(1..n) a) <= sum(1..n) a / &n`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH; ARITH_RULE `1 <= SUC n`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `root(SUC n) ((sum(1..SUC n) a / &(SUC n)) pow (SUC n))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ROOT_MONO_LE THEN
    ASM_SIMP_TAC[AGM; ARITH_RULE `1 <= SUC n`] THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN
    ASM_REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC POW_ROOT_POS THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; SUM_POS_LE_NUMSEG]]);;
