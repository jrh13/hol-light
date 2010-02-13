(* ========================================================================= *)
(* Arithmetic-geometric mean inequality.                                     *)
(* ========================================================================= *)

needs "Library/products.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Various trivial lemmas.                                                   *)
(* ------------------------------------------------------------------------- *)

let FORALL_2 = prove
 (`!P. (!i. 1 <= i /\ i <= 2 ==> P i) <=> P 1 /\ P 2`,
  MESON_TAC[ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`]);;

let NUMSEG_2 = prove
 (`1..2 = {1,2}`,
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY; IN_NUMSEG] THEN ARITH_TAC);;

let AGM_2 = prove
 (`!x y. x * y <= ((x + y) / &2) pow 2`,
  REWRITE_TAC[REAL_LE_SQUARE; REAL_ARITH
   `x * y <= ((x + y) / &2) pow 2 <=> &0 <= (x - y) * (x - y)`]);;

let SUM_SPLIT_2 = prove
 (`sum(1..2*n) f = sum(1..n) f + sum(n+1..2*n) f`,
  SIMP_TAC[MULT_2; ARITH_RULE `1 <= n + 1`; SUM_ADD_SPLIT]);;

let PRODUCT_SPLIT_2 = prove
 (`product(1..2*n) f = product(1..n) f * product(n+1..2*n) f`,
  SIMP_TAC[MULT_2; ARITH_RULE `1 <= n + 1`; PRODUCT_ADD_SPLIT]);;

(* ------------------------------------------------------------------------- *)
(* Specialized induction principle.                                          *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_INDUCT = prove
 (`!P. P 2 /\ (!n. P n ==> P(2 * n)) /\ (!n. P(n + 1) ==> P n) ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `P(0) /\ P(1)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `1 = 0 + 1 /\ 2 = 1 + 1`]; ALL_TAC] THEN
  ASM_CASES_TAC `EVEN n` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
    ASM_MESON_TAC[ARITH_RULE `2 * n = 0 \/ n < 2 * n`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EVEN]) THEN
  SIMP_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  ASM_MESON_TAC[ARITH_RULE `SUC(2 * m) = 1 \/ m + 1 < SUC(2 * m)`;
                ARITH_RULE `SUC(2 * m) + 1 = 2 * (m + 1)`]);;

(* ------------------------------------------------------------------------- *)
(* The main result.                                                          *)
(* ------------------------------------------------------------------------- *)

let AGM = prove
 (`!n a. 1 <= n /\ (!i. 1 <= i /\ i <= n ==> &0 <= a(i))
         ==> product(1..n) a <= (sum(1..n) a / &n) pow n`,
  MATCH_MP_TAC CAUCHY_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FORALL_2; NUMSEG_2] THEN
    SIMP_TAC[SUM_CLAUSES; PRODUCT_CLAUSES; FINITE_RULES; IN_INSERT;
             NOT_IN_EMPTY; ARITH; REAL_MUL_RID; REAL_ADD_RID] THEN
    REWRITE_TAC[AGM_2];
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `a:num->real` THEN
    STRIP_TAC THEN REWRITE_TAC[SUM_SPLIT_2; PRODUCT_SPLIT_2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(sum(1..n) a / &n) pow n * (sum(n+1..2*n) a / &n) pow n` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC PRODUCT_POS_LE THEN
        REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        ASM_MESON_TAC[ARITH_RULE `i <= n ==> i <= 2 * n`];
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC[ARITH_RULE `i <= n ==> i <= 2 * n`;
                      ARITH_RULE `1 <= 2 * n ==> 1 <= n`];
        MATCH_MP_TAC PRODUCT_POS_LE THEN
        REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        ASM_MESON_TAC[ARITH_RULE `n + 1 <= i ==> 1 <= i`];
        ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[MULT_2] THEN
        REWRITE_TAC[PRODUCT_OFFSET; SUM_OFFSET] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC[ARITH_RULE
          `1 <= i /\ i <= n ==> 1 <= i + n /\ i + n <= 2 * n`;
                      ARITH_RULE `1 <= 2 * n ==> 1 <= n`]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_POW_MUL; GSYM REAL_POW_POW] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    SUBST1_TAC(REAL_ARITH `&2 * &n = &n * &2`) THEN
    REWRITE_TAC[real_div; REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_ARITH `(x + y) * (a * b) = (x * a + y * a) * b`] THEN
    REWRITE_TAC[GSYM real_div; AGM_2] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC SUM_POS_LE THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC;
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `a:num->real` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC
     `\i. if i <= n then a(i) else sum(1..n) a / &n`) THEN
    REWRITE_TAC[ARITH_RULE `1 <= n + 1`] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      ASM_SIMP_TAC[SUM_POS_LE; FINITE_NUMSEG; IN_NUMSEG];
      ALL_TAC] THEN
    ABBREV_TAC `A = sum(1..n) a / &n` THEN
    SIMP_TAC[GSYM ADD1; PRODUCT_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG] THEN
    SIMP_TAC[ARITH_RULE `1 <= SUC n /\ ~(SUC n <= n)`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN EXPAND_TAC "A" THEN
    SIMP_TAC[REAL_OF_NUM_LE; ASSUME `1 <= n`; REAL_FIELD
     `&1 <= &n ==> (s + s / &n) / (&n + &1) = s / &n`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[real_pow] THEN
    ASM_CASES_TAC `&0 < A` THEN ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
    SUBGOAL_THEN `A = &0` MP_TAC THENL
     [ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM; GSYM REAL_NOT_LT] THEN
      REWRITE_TAC[REAL_NOT_LT] THEN EXPAND_TAC "A" THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      ASM_SIMP_TAC[SUM_POS_LE; FINITE_NUMSEG; IN_NUMSEG];
      ALL_TAC] THEN
    EXPAND_TAC "A" THEN
    REWRITE_TAC[real_div; REAL_ENTIRE; REAL_INV_EQ_0; REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> ~(n = 0)`] THEN DISCH_TAC THEN
    DISCH_THEN(K ALL_TAC) THEN
    MP_TAC(SPECL [`a:num->real`; `1`; `n:num`] SUM_POS_EQ_0_NUMSEG) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
    REWRITE_TAC[ARITH_RULE `1 + n = SUC n`] THEN
    DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC[real_pow; REAL_MUL_LZERO; PRODUCT_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `1 <= SUC n`; REAL_MUL_RZERO; REAL_LE_REFL]]);;
