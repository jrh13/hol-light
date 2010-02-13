(* ========================================================================= *)
(* Binary expansions as a bijection between numbers and finite sets.         *)
(* ========================================================================= *)

let LT_POW2_REFL = prove
 (`!n. n < 2 EXP n`,
  INDUCT_TAC THEN REWRITE_TAC[EXP] THEN TRY(POP_ASSUM MP_TAC) THEN ARITH_TAC);;

let BINARY_INDUCT = prove
 (`!P. P 0 /\ (!n. P n ==> P(2 * n) /\ P(2 * n + 1)) ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF THEN GEN_TAC THEN
  STRIP_ASSUME_TAC(ARITH_RULE
   `n = 0 \/ n DIV 2 < n /\ (n = 2 * n DIV 2 \/ n = 2 * n DIV 2 + 1)`) THEN
  ASM_MESON_TAC[]);;

let BOUNDED_FINITE = prove
 (`!s. (!x:num. x IN s ==> x <= n) ==> FINITE s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..n` THEN
  ASM_SIMP_TAC[SUBSET; IN_NUMSEG; FINITE_NUMSEG; LE_0]);;

let EVEN_NSUM = prove
 (`!s. FINITE s /\ (!i. i IN s ==> EVEN(f i)) ==> EVEN(nsum s f)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[NSUM_CLAUSES; ARITH; EVEN_ADD; IN_INSERT]);;

(* ------------------------------------------------------------------------- *)
(* The basic bijections.                                                     *)
(* ------------------------------------------------------------------------- *)

let bitset = new_definition
 `bitset n = {i | ODD(n DIV (2 EXP i))}`;;

let binarysum = new_definition
 `binarysum s = nsum s (\i. 2 EXP i)`;;

(* ------------------------------------------------------------------------- *)
(* Inverse property in one direction.                                        *)
(* ------------------------------------------------------------------------- *)

let BITSET_BOUND_LEMMA = prove
 (`!n i. i IN (bitset n) ==> 2 EXP i <= n`,
  REWRITE_TAC[bitset; IN_ELIM_THM] THEN MESON_TAC[DIV_LT; ODD; NOT_LE]);;

let BITSET_BOUND_WEAK = prove
 (`!n i. i IN (bitset n) ==> i < n`,
  MESON_TAC[BITSET_BOUND_LEMMA; LT_POW2_REFL; LTE_TRANS]);;

let FINITE_BITSET = prove
 (`!n. FINITE(bitset n)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..n` THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0; SUBSET] THEN
  MESON_TAC[LT_IMP_LE; BITSET_BOUND_WEAK]);;

let BITSET_0 = prove
 (`bitset 0 = {}`,
  REWRITE_TAC[bitset; EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  SIMP_TAC[DIV_0; EXP_EQ_0; ARITH]);;

let BITSET_STEP = prove
 (`(!n. bitset(2 * n) = IMAGE SUC (bitset n)) /\
   (!n. bitset(2 * n + 1) = 0 INSERT (IMAGE SUC (bitset n)))`,
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ALL_TAC; DISCH_THEN(fun th -> REWRITE_TAC[GSYM th])] THEN
  REWRITE_TAC[bitset; EXTENSION; IN_INSERT; IN_ELIM_THM; IN_IMAGE] THEN
  GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[ARITH; ODD_MULT; DIV_1; NOT_SUC; ODD_ADD] THEN
  GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[EQ_SUC; UNWIND_THM1; EXP] THEN
  SIMP_TAC[CONV_RULE(RAND_CONV SYM_CONV) (SPEC_ALL DIV_DIV);
           MULT_EQ_0; EXP_EQ_0; ARITH] THEN
  REWRITE_TAC[ARITH_RULE `(2 * n + 1) DIV 2 = n /\ (2 * n) DIV 2 = n`]);;

let BINARYSUM_BITSET = prove
 (`!n. binarysum (bitset n) = n`,
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN REWRITE_TAC[binarysum] THEN
  MATCH_MP_TAC BINARY_INDUCT THEN REWRITE_TAC[BITSET_0; NSUM_CLAUSES] THEN
  SIMP_TAC[BITSET_STEP; NSUM_IMAGE; EQ_SUC; ADD1; FINITE_BITSET; ARITH;
  NSUM_CLAUSES; FINITE_IMAGE; IN_IMAGE; ARITH_RULE `~(0 = x + 1)`] THEN
  REWRITE_TAC[o_DEF; EXP; NSUM_LMUL] THEN
  ASM_MESON_TAC[ADD_SYM; ARITH_RULE `~(2 * m = 0) ==> m < 2 * m`;
                ARITH_RULE `m < SUC(2 * m)`]);;

let BITSET_EQ = prove
 (`!m n. bitset m = bitset n <=> m = n`,
  MESON_TAC[BINARYSUM_BITSET]);;

let BITSET_EQ_EMPTY = prove
 (`!n. bitset n = {} <=> n = 0`,
  MESON_TAC[BITSET_EQ; BITSET_0]);;

(* ------------------------------------------------------------------------- *)
(* Inverse property in the other direction.                                  *)
(* ------------------------------------------------------------------------- *)

let BINARYSUM_BOUND_LEMMA = prove
 (`!k s. (!i. i IN s ==> i < k) ==> nsum s (\i. 2 EXP i) < 2 EXP k`,
  INDUCT_TAC THEN
  SIMP_TAC[LT; GSYM NOT_EXISTS_THM; MEMBER_NOT_EMPTY; NSUM_CLAUSES; ARITH] THEN
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `FINITE(s:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[BOUNDED_FINITE; LE_LT]; ALL_TAC] THEN
  MATCH_MP_TAC LET_TRANS THEN
  EXISTS_TAC `nsum (k INSERT (s DELETE k)) (\i. 2 EXP i)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_SUBSET THEN SIMP_TAC[FINITE_INSERT; FINITE_DELETE];
    ASM_SIMP_TAC[NSUM_CLAUSES; FINITE_DELETE; IN_DELETE] THEN
    REWRITE_TAC[EXP; ARITH_RULE `a + b < 2 * a <=> b < a `] THEN
    FIRST_X_ASSUM MATCH_MP_TAC] THEN
  ASM SET_TAC[]);;

let BINARYSUM_DIV_DIVISIBLE = prove
 (`!s k. FINITE s /\ (!i. i IN s ==> k <= i)
         ==> nsum s (\i. 2 EXP i) = 2 EXP k * nsum s (\i. 2 EXP (i - k))`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NSUM_CLAUSES; DIV_0; EXP_EQ_0; ARITH_EQ; MULT_CLAUSES] THEN
  SIMP_TAC[IN_INSERT; ADD_ASSOC; EQ_ADD_RCANCEL; LEFT_ADD_DISTRIB] THEN
  SIMP_TAC[GSYM EXP_ADD; ARITH_RULE `i <= k:num ==> i + k - i = k`]);;

let BINARYSUM_DIV = prove
 (`!k s. FINITE s
         ==> (nsum s (\j. 2 EXP j)) DIV (2 EXP k) =
             nsum s (\j. if j < k then 0 else 2 EXP (j - k))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(nsum {i | i < k /\ i IN s} (\j. 2 EXP j) +
               nsum {i | k <= i /\ i IN s} (\j. 2 EXP j)) DIV (2 EXP k)` THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC NSUM_UNION_EQ THEN
    ASM_SIMP_TAC[EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    CONJ_TAC THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `(i:num) IN s` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `nsum {i | i < k /\ i IN s} (\j. 2 EXP j)` THEN
  SIMP_TAC[BINARYSUM_BOUND_LEMMA; IN_ELIM_THM] THEN
  REWRITE_TAC[ARITH_RULE `a + x:num = y + a <=> x = y`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `2 EXP k * nsum {i | k <= i /\ i IN s} (\i. 2 EXP (i - k))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC BINARYSUM_DIV_DIVISIBLE THEN SIMP_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:num->bool` THEN
    ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
  REWRITE_TAC[EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
  ONCE_REWRITE_TAC[GSYM NSUM_SUPPORT] THEN
  REWRITE_TAC[support; NEUTRAL_ADD; EXP_EQ_0; ARITH; IN_ELIM_THM] THEN
  REWRITE_TAC[ARITH_RULE `(if p then 0 else q) = 0 <=> ~p ==> q = 0`] THEN
  REWRITE_TAC[EXP_EQ_0; ARITH; NOT_LT; CONJ_ACI] THEN
  MATCH_MP_TAC NSUM_EQ THEN
  SIMP_TAC[IN_ELIM_THM; ARITH_RULE `k <= j:num ==> ~(j < k)`]);;

let BITSET_BINARYSUM = prove
 (`!s. FINITE s ==> bitset (binarysum s) = s`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[bitset; binarysum; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN ASM_SIMP_TAC[BINARYSUM_DIV] THEN
  ASM_CASES_TAC `(i:num) IN s` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
     `i IN s ==> s = i INSERT (s DELETE i)`)) THEN
    ASM_SIMP_TAC[NSUM_CLAUSES; FINITE_DELETE; IN_DELETE] THEN
    REWRITE_TAC[LT_REFL; SUB_REFL; ARITH; ODD_ADD];
    ALL_TAC] THEN
  REWRITE_TAC[NOT_ODD] THEN MATCH_MP_TAC EVEN_NSUM THEN
  ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN SIMP_TAC[ARITH; EVEN_EXP; SUB_EQ_0] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[LE_LT]);;

(* ------------------------------------------------------------------------- *)
(* Also, bijections between restricted segments.                             *)
(* ------------------------------------------------------------------------- *)

let BINARYSUM_BOUND = prove
 (`!k s. (!i. i IN s ==> i < k) ==> binarysum s < 2 EXP k`,
  REWRITE_TAC[BINARYSUM_BOUND_LEMMA; binarysum]);;

let BITSET_BOUND = prove
 (`!n i k. n < 2 EXP k /\ i IN bitset n ==> i < k`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `2 EXP i < 2 EXP k` MP_TAC THENL
   [ASM_MESON_TAC[BITSET_BOUND_LEMMA; LET_TRANS];
    REWRITE_TAC[LT_EXP; ARITH]]);;

let BITSET_BOUND_EQ = prove
 (`!n k. n < 2 EXP k <=> (!i. i IN bitset n ==> i < k)`,
  MESON_TAC[BINARYSUM_BOUND; BITSET_BOUND; BINARYSUM_BITSET]);;

let BINARYSUM_BOUND_EQ = prove
 (`!s k. FINITE s ==> (binarysum s < 2 EXP k <=> (!i. i IN s ==> i < k))`,
  MESON_TAC[BINARYSUM_BOUND; BITSET_BOUND; BITSET_BINARYSUM]);;
