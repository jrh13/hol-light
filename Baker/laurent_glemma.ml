(* ========================================================================= *)
(* Two logarithms, the Laurent bound: the g-lemma.                           *)
(*                                                                           *)
(* Purpose: the centring lemma of M. Laurent, Linear forms in two logarithms *)
(* and interpolation determinants, Acta Arith. 66 (1994), Lemma 3, which     *)
(* gives the factor g = 1/4 - N / (12 R S) of Laurent, Acta Arith. 133       *)
(* (2008), Theorem 1, with the layer-cake argument of D. Lombardo,           *)
(* Interpolation determinants and the Lebesgue-Nagell equation, arXiv        *)
(* 2609.23899 (2026), Lemma 3.8:                                             *)
(*   GRID_TOP_MINUS_BOTTOM: for disjoint A, B of size q in the grid R x S,   *)
(*     sum_A r - sum_B r <= q (R S - q) / S   (layer cake over the rows);    *)
(*   TWOLOG_G_LEMMA: for N = K L distinct grid points and any permutation p, *)
(*     |sum_i ((i-1) DIV K - (L-1)/2) r_(p i)| <= (L R N / 2) g,             *)
(*     g = 1/4 - N/(12 R S)                                                  *)
(* (threshold decomposition of the centred row index into disjoint pairs of  *)
(* index sets of equal size, GRID_TOP_MINUS_BOTTOM for each pair, and the    *)
(* closed forms of the resulting sums).                                      *)
(*                                                                           *)
(* Main results: GRID_TOP_MINUS_BOTTOM, TWOLOG_G_LEMMA (the form with rr, R  *)
(* and ss, S exchanged is the same theorem); helper names GLEMMA_*.          *)
(*                                                                           *)
(* Uses: Library/permutations.ml (PERMUTES_INJECTIVE, PERMUTES_IN_IMAGE).    *)
(* ========================================================================= *)

needs "Library/permutations.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Elementary sums.                                                          *)
(* ------------------------------------------------------------------------- *)

let GLEMMA_SUM_ID = prove
 (`!n. sum(1..n) (\i. &i) = &n * (&n + &1) / &2`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC);;

let GLEMMA_SUM_SQ = prove
 (`!n. sum(1..n) (\i. &i pow 2) = &n * (&n + &1) * (&2 * &n + &1) / &6`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC);;

let GLEMMA_SUM_INDICATOR = prove
 (`!(s:A->bool) P.
     FINITE s
     ==> sum s (\x. if P x then &1 else &0) = &(CARD {x | x IN s /\ P x})`,
  SIMP_TAC[CARD_EQ_SUM; FINITE_RESTRICT; SUM_RESTRICT_SET]);;

let GLEMMA_NSUM_INDICATOR = prove
 (`!(s:A->bool) P.
     FINITE s
     ==> nsum s (\x. if P x then 1 else 0) = CARD {x | x IN s /\ P x}`,
  SIMP_TAC[CARD_EQ_NSUM; FINITE_RESTRICT; NSUM_RESTRICT_SET]);;

let GLEMMA_SUM_REFLECT = prove
 (`!f n. sum(1..n) (\i. f((n + 1) - i)) = sum(1..n) f`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_REFLECT] THEN
  ASM_REWRITE_TAC[ARITH_RULE `n < 1 <=> n = 0`] THEN
  MP_TAC(ISPECL [`1`; `f:num->real`; `0`; `n - 1`] SUM_OFFSET) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - 1 + 1 = n`; ADD_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  UNDISCH_TAC `i <= n - 1` THEN UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC);;

let GLEMMA_NSUM_REFLECT = prove
 (`!f n. nsum(1..n) (\i. f((n + 1) - i)) = nsum(1..n) f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
  SIMP_TAC[REAL_OF_NUM_SUM; FINITE_NUMSEG] THEN
  MP_TAC(ISPECL [`\i. &((f:num->num) i):real`; `n:num`] GLEMMA_SUM_REFLECT) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Folding a sum over t = 1..L-1 of f(MIN t (L-t)), L = 2n+1 or 2n+2.        *)
(* ------------------------------------------------------------------------- *)

let GLEMMA_FOLD_ODD = prove
 (`!f n. sum(1..2 * n) (\t. f(MIN t ((2 * n + 1) - t))) = &2 * sum(1..n) f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `2 * n = n + n`] THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`] THEN
  MATCH_MP_TAC(REAL_ARITH `a = c /\ b = c ==> a + b = &2 * c`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN UNDISCH_TAC `i <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `\t. (f:num->real)(MIN t (((n + n) + 1) - t))`;
                 `1`; `n:num`] SUM_OFFSET) THEN
  REWRITE_TAC[ARITH_RULE `1 + n = n + 1`] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM GLEMMA_SUM_REFLECT] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN UNDISCH_TAC `1 <= i` THEN UNDISCH_TAC `i <= n` THEN
  ARITH_TAC);;

let GLEMMA_FOLD_EVEN = prove
 (`!f n. sum(1..2 * n + 1) (\t. f(MIN t ((2 * n + 2) - t))) =
         &2 * sum(1..n) f + f(n + 1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * n + 1 = (n + 1) + n`] THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= (n + 1) + 1`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a = c + d /\ b = c ==> a + b = &2 * c + d`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    BINOP_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      AP_TERM_TAC THEN UNDISCH_TAC `i <= n` THEN ARITH_TAC;
      AP_TERM_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n + 1`; `\t. (f:num->real)(MIN t ((2 * n + 2) - t))`;
                 `1`; `n:num`] SUM_OFFSET) THEN
  REWRITE_TAC[ARITH_RULE `1 + n + 1 = (n + 1) + 1`;
              ARITH_RULE `n + n + 1 = (n + 1) + n`] THEN
  DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM GLEMMA_SUM_REFLECT] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN UNDISCH_TAC `1 <= i` THEN UNDISCH_TAC `i <= n` THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Step IV: closed form of (1/2) sum_t q_t (R S - q_t) / S, q_t = K m_t.     *)
(* ------------------------------------------------------------------------- *)

let GLEMMA_SUM_QUAD = prove
 (`!K R S n.
     ~(S = 0)
     ==> sum(1..n) (\m. &(K * m) * (&R * &S - &(K * m)) / &S) =
         &K * &R * &n * (&n + &1) / &2 -
         &K pow 2 * &n * (&n + &1) * (&2 * &n + &1) / (&6 * &S)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!m. &(K * m) * (&R * &S - &(K * m)) / &S =
        (&K * &R) * &m - (&K pow 2 / &S) * &m pow 2`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    UNDISCH_TAC `~(S = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; SUM_LMUL; GLEMMA_SUM_SQ;
              REWRITE_RULE[ETA_AX] GLEMMA_SUM_ID] THEN
  UNDISCH_TAC `~(S = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
  CONV_TAC REAL_FIELD);;

let GLEMMA_ODD_REAL = prove
 (`!k r s x.
     &0 < r /\ &0 < s /\ &0 <= k /\ k * (&2 * x + &1) <= r * s
     ==> (&2 * (k * r * x * (x + &1) / &2 -
                k pow 2 * x * (x + &1) * (&2 * x + &1) / (&6 * s))) / &2 <=
         (&2 * x + &1) * r * (k * (&2 * x + &1)) / &2 *
         (&1 / &4 - (k * (&2 * x + &1)) / (&12 * r * s))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  SUBGOAL_THEN
   `(&2 * x + &1) * r * (k * (&2 * x + &1)) / &2 *
    (&1 / &4 - (k * (&2 * x + &1)) / (&12 * r * s)) -
    (&2 * (k * r * x * (x + &1) / &2 -
           k pow 2 * x * (x + &1) * (&2 * x + &1) / (&6 * s))) / &2 =
    (k * (&3 * r * s - k * (&2 * x + &1))) / (&24 * s)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < s` THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= r * s` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      UNDISCH_TAC `&0 < s` THEN UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `k * (&2 * x + &1) <= r * s` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&0 < s` THEN REAL_ARITH_TAC]);;

let GLEMMA_EVEN_REAL = prove
 (`!k r s x.
     &0 < r /\ &0 < s /\ &0 <= x
     ==> (&2 * (k * r * x * (x + &1) / &2 -
                k pow 2 * x * (x + &1) * (&2 * x + &1) / (&6 * s)) +
          (k * (x + &1)) * (r * s - k * (x + &1)) / s) / &2 <=
         (&2 * x + &2) * r * (k * (&2 * x + &2)) / &2 *
         (&1 / &4 - (k * (&2 * x + &2)) / (&12 * r * s))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  SUBGOAL_THEN
   `(&2 * x + &2) * r * (k * (&2 * x + &2)) / &2 *
    (&1 / &4 - (k * (&2 * x + &2)) / (&12 * r * s)) -
    (&2 * (k * r * x * (x + &1) / &2 -
           k pow 2 * x * (x + &1) * (&2 * x + &1) / (&6 * s)) +
     (k * (x + &1)) * (r * s - k * (x + &1)) / s) / &2 =
    (k pow 2 * (&2 * x + &2)) / (&12 * s)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < s` THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    UNDISCH_TAC `&0 <= x` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&0 < s` THEN REAL_ARITH_TAC]);;

let GLEMMA_CLOSED_FORM = prove
 (`!K L R S.
     1 <= L /\ 1 <= R /\ 1 <= S /\ K * L <= R * S
     ==> sum(1..L - 1)
           (\t. &(K * MIN t (L - t)) *
                (&R * &S - &(K * MIN t (L - t))) / &S) / &2 <=
         &L * &R * &(K * L) / &2 * (&1 / &4 - &(K * L) / (&12 * &R * &S))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(S = 0) /\ &0 < &S /\ &0 < &R` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_binary "<=" o concl))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. L = 2 * n + 1 \/ L = 2 * n + 2`
   (X_CHOOSE_THEN `n:num` DISJ_CASES_TAC)
  THENL
   [MP_TAC(SPEC `L:num` EVEN_OR_ODD) THEN
    REWRITE_TAC[EVEN_EXISTS; ODD_EXISTS] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `m - 1` THEN UNDISCH_TAC `1 <= L` THEN
      UNDISCH_TAC `L = 2 * m` THEN ARITH_TAC;
      EXISTS_TAC `m:num` THEN UNDISCH_TAC `L = SUC(2 * m)` THEN ARITH_TAC];
    MP_TAC(BETA_RULE(ISPECL
      [`\m. &(K * m) * (&R * &S - &(K * m)) / &S`; `n:num`]
      GLEMMA_FOLD_ODD)) THEN
    ASM_REWRITE_TAC[ARITH_RULE `(2 * n + 1) - 1 = 2 * n`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[GLEMMA_SUM_QUAD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC GLEMMA_ODD_REAL THEN ASM_REWRITE_TAC[REAL_POS] THEN
    UNDISCH_TAC `K * L <= R * S` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL;
                GSYM REAL_OF_NUM_ADD];
    MP_TAC(BETA_RULE(ISPECL
      [`\m. &(K * m) * (&R * &S - &(K * m)) / &S`; `n:num`]
      GLEMMA_FOLD_EVEN)) THEN
    ASM_REWRITE_TAC[ARITH_RULE `(2 * n + 2) - 1 = 2 * n + 1`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[GLEMMA_SUM_QUAD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC GLEMMA_EVEN_REAL THEN ASM_REWRITE_TAC[REAL_POS]]);;

(* ------------------------------------------------------------------------- *)
(* Layer cake and the grid arithmetic (Lombardo Lemma 3.8).                  *)
(* ------------------------------------------------------------------------- *)

let GLEMMA_GRID_CROSS = prove
 (`!R S. {(r,s) | r < R /\ s < S} = {r:num | r < R} CROSS {s:num | s < S}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_CROSS; IN_ELIM_PAIR_THM;
              IN_ELIM_THM]);;

let GLEMMA_LAYER_CAKE = prove
 (`!(A:A->bool) f n.
     FINITE A /\ (!a. a IN A ==> f a <= n)
     ==> nsum A f = nsum(1..n) (\u. CARD {a | a IN A /\ u <= f a})`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `nsum A (\a. nsum(1..n) (\u. if u <= (f:A->num) a then 1 else 0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `a:A` THEN DISCH_TAC THEN
    SIMP_TAC[GLEMMA_NSUM_INDICATOR; FINITE_NUMSEG] THEN
    SUBGOAL_THEN `{u | u IN 1..n /\ u <= (f:A->num) a} = 1..f a`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      REWRITE_TAC[CARD_NUMSEG] THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\a u. if u <= (f:A->num) a then 1 else 0`;
                 `A:A->bool`; `1..n`] NSUM_SWAP) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC NSUM_EQ_NUMSEG THEN X_GEN_TAC `u:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GLEMMA_NSUM_INDICATOR]);;

let GLEMMA_GAUSS_CUTOFF = prove
 (`!R S q.
     q <= R * S
     ==> &q * &q <= &S * &q + &2 * &S * sum(1..R - 1) (\u. &(q - S * u))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `q = 0` THENL
   [ASM_REWRITE_TAC[SUB_0; SUM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(S = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `q <= R * S` THEN
    UNDISCH_TAC `~(q = 0)` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c = (q - 1) DIV S` THEN
  ABBREV_TAC `d = (q - 1) MOD S + 1` THEN
  SUBGOAL_THEN `q = S * c + d /\ d <= S /\ c <= R - 1` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`q - 1`; `S:num`] DIVISION) THEN
    MP_TAC(SPECL [`S:num`; `q - 1`; `R:num`] RDIV_LT_EQ) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `q - 1 < S * R` (fun th -> REWRITE_TAC[th]) THENL
     [ONCE_REWRITE_TAC[MULT_SYM] THEN UNDISCH_TAC `q <= R * S` THEN
      UNDISCH_TAC `~(q = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT STRIP_TAC THENL
     [UNDISCH_TAC `(q - 1) MOD S + 1 = d` THEN
      UNDISCH_TAC `q - 1 = c * S + (q - 1) MOD S` THEN
      UNDISCH_TAC `~(q = 0)` THEN ARITH_TAC;
      UNDISCH_TAC `(q - 1) MOD S + 1 = d` THEN
      UNDISCH_TAC `(q - 1) MOD S < S` THEN ARITH_TAC;
      UNDISCH_TAC `c < R` THEN ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&S * &q + &2 * &S * sum(1..c) (\u. &(q - S * u))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_LE_LADD] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS]) THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; REAL_POS; SUBSET_NUMSEG; LE_REFL]] THEN
  SUBGOAL_THEN
   `sum(1..c) (\u. &(q - S * u)) = &c * &q - &S * (&c * (&c + &1) / &2)`
  SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS `sum(1..c) (\u. &q - &S * &u)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `u:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `S * u <= q` (fun th -> SIMP_TAC[GSYM REAL_OF_NUM_SUB; th])
      THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `S * c` THEN
        ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_MUL]];
      REWRITE_TAC[SUM_SUB_NUMSEG; SUM_LMUL; SUM_CONST_NUMSEG;
                  REWRITE_RULE[ETA_AX] GLEMMA_SUM_ID] THEN
      REWRITE_TAC[ADD_SUB]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&q = &S * &c + &d` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &d * (&S - &d)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_SUB_LE] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    REAL_ARITH_TAC]);;

let GLEMMA_GRID_ARITH = prove
 (`!R S q.
     q <= R * S
     ==> &(nsum(1..R - 1) (\u. q - (q - S * (R - u)))) -
         &(nsum(1..R - 1) (\u. q - S * u)) <=
         &q * (&R * &S - &q) / &S`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `q = 0` THENL
   [ASM_REWRITE_TAC[SUB_0; NSUM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(S = 0) /\ ~(R = 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `q <= R * S` THEN
    UNDISCH_TAC `~(q = 0)` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nsum(1..R - 1) (\u. q - (q - S * (R - u))) =
    nsum(1..R - 1) (\u. q - (q - S * u))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\v. q - (q - S * v)`; `R - 1`] GLEMMA_NSUM_REFLECT) THEN
    ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `~(R = 0) ==> 1 <= R`];
    ALL_TAC] THEN
  SIMP_TAC[REAL_OF_NUM_SUM; FINITE_NUMSEG] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `q - x <= q`] THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; SUM_CONST_NUMSEG] THEN
  MP_TAC(SPECL [`R:num`; `S:num`; `q:num`] GLEMMA_GAUSS_CUTOFF) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`sum(1..R - 1) (\u. &(q - S * u))`,`g:real`) THEN GEN_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `~(R = 0) ==> (R - 1 + 1) - 1 = R - 1`;
               GSYM REAL_OF_NUM_SUB; ARITH_RULE `~(R = 0) ==> 1 <= R`] THEN
  SUBGOAL_THEN `&0 < &S` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Target 1: top minus bottom in the grid R x S.                             *)
(* ------------------------------------------------------------------------- *)

let GRID_TOP_MINUS_BOTTOM = prove
 (`!R S (A:num#num->bool) (B:num#num->bool) q.
     A SUBSET {(r,s) | r < R /\ s < S} /\ B SUBSET {(r,s) | r < R /\ s < S} /\
     DISJOINT A B /\ A HAS_SIZE q /\ B HAS_SIZE q
     ==> &(nsum A FST) - &(nsum B FST) <= &q * (&R * &S - &q) / &S`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE; GLEMMA_GRID_CROSS] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `q <= R * S` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A:num#num->bool`;
                   `{r:num | r < R} CROSS {s:num | s < S}`] CARD_SUBSET) THEN
    ASM_SIMP_TAC[CARD_CROSS; FINITE_CROSS; FINITE_NUMSEG_LT; CARD_NUMSEG_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(nsum(1..R - 1) (\u. q - (q - S * (R - u)))) -
              &(nsum(1..R - 1) (\u. q - S * u))` THEN
  ASM_SIMP_TAC[GLEMMA_GRID_ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(a:real) <= a' /\ (b':real) <= b ==> a - b <= a' - b'`) THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN
  SUBGOAL_THEN
   `(!a:num#num. a IN A ==> FST a <= R - 1) /\
    (!a:num#num. a IN B ==> FST a <= R - 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `s:num`] THEN DISCH_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `r < R ==> r <= R - 1`) THENL
     [UNDISCH_TAC `A SUBSET {r:num | r < R} CROSS {s:num | s < S}`;
      UNDISCH_TAC `B SUBSET {r:num | r < R} CROSS {s:num | s < S}`] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `(r:num,s:num)`) THEN
    ASM_SIMP_TAC[IN_CROSS; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:num#num->bool`; `FST:num#num->num`; `R - 1`]
    GLEMMA_LAYER_CAKE) THEN
  MP_TAC(ISPECL [`B:num#num->bool`; `FST:num#num->num`; `R - 1`]
    GLEMMA_LAYER_CAKE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  CONJ_TAC THEN MATCH_MP_TAC NSUM_LE_NUMSEG THEN X_GEN_TAC `u:num` THEN
  STRIP_TAC THEN REWRITE_TAC[] THENL
   [MATCH_MP_TAC(ARITH_RULE `x <= q /\ x <= y ==> x <= q - (q - y)`) THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `CARD(A:num#num->bool) = q` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_REWRITE_TAC[SUBSET_RESTRICT];
      ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD((u..R - 1) CROSS {s:num | s < S})` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN
      SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FINITE_NUMSEG_LT] THEN
      UNDISCH_TAC `A SUBSET {r:num | r < R} CROSS {s:num | s < S}` THEN
      REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM; IN_NUMSEG;
                  FST] THEN
      MESON_TAC[ARITH_RULE `r < R ==> r <= R - 1`];
      SIMP_TAC[CARD_CROSS; FINITE_NUMSEG; FINITE_NUMSEG_LT; CARD_NUMSEG;
               CARD_NUMSEG_LT] THEN
      SUBGOAL_THEN `(R - 1 + 1) - u = R - u` SUBST1_TAC THENL
       [UNDISCH_TAC `1 <= u` THEN ARITH_TAC;
        REWRITE_TAC[MULT_SYM; LE_REFL]]];
    MATCH_MP_TAC(GEN_ALL
     (ARITH_RULE `q <= x + y /\ y <= S * u ==> q - S * u <= x`)) THEN
    EXISTS_TAC `CARD {b:num#num | b IN B /\ FST b < u}` THEN CONJ_TAC THENL
     [UNDISCH_TAC `CARD(B:num#num->bool) = q` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `CARD({b:num#num | b IN B /\ u <= FST b} UNION
                       {b | b IN B /\ FST b < u})` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CARD_SUBSET THEN
        ASM_SIMP_TAC[FINITE_UNION; FINITE_RESTRICT] THEN
        REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
        X_GEN_TAC `b:num#num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
        ARITH_TAC;
        MATCH_MP_TAC CARD_UNION_LE THEN ASM_SIMP_TAC[FINITE_RESTRICT]];
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `CARD({r:num | r < u} CROSS {s:num | s < S})` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CARD_SUBSET THEN
        SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG_LT] THEN
        UNDISCH_TAC `B SUBSET {r:num | r < R} CROSS {s:num | s < S}` THEN
        REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM; FST] THEN
        MESON_TAC[];
        SIMP_TAC[CARD_CROSS; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
        REWRITE_TAC[MULT_SYM; LE_REFL]]]]);;

(* ------------------------------------------------------------------------- *)
(* Step I: threshold decomposition of the centred row index.                 *)
(* ------------------------------------------------------------------------- *)

let GLEMMA_REAL_SUB_SUB = prove
 (`!a b. &(a - b) - &(b - a) = &a - &b`,
  REPEAT GEN_TAC THEN DISJ_CASES_TAC(SPECL [`a:num`; `b:num`] LE_CASES) THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `a <= b ==> a - b = 0`] THEN
  REAL_ARITH_TAC);;

let GLEMMA_COUNT_LAYER = prove
 (`!L l. l < L
         ==> sum(1..L - 1)
               (\t. (if L - MIN t (L - t) <= l then &1 else &0) -
                    (if l < MIN t (L - t) then &1 else &0)) =
             &2 * &l + &1 - &L`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUM_SUB_NUMSEG] THEN
  SIMP_TAC[GLEMMA_SUM_INDICATOR; FINITE_NUMSEG] THEN
  SUBGOAL_THEN `{t | t IN 1..L - 1 /\ L - MIN t (L - t) <= l} = (L - l)..l`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN GEN_TAC THEN
    REWRITE_TAC[ARITH_RULE `L - m <= l <=> L <= l + m`;
                ARITH_RULE `a <= b + MIN c d <=> a <= b + c /\ a <= b + d`] THEN
    UNDISCH_TAC `l < L` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{t | t IN 1..L - 1 /\ l < MIN t (L - t)} = (l + 1)..(L - (l + 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN GEN_TAC THEN
    UNDISCH_TAC `l < L` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[CARD_NUMSEG] THEN
  SUBGOAL_THEN `(L - (l + 1) + 1) = L - l` SUBST1_TAC THENL
   [UNDISCH_TAC `l < L` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GLEMMA_REAL_SUB_SUB] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE; GSYM REAL_OF_NUM_ADD] THEN
  REAL_ARITH_TAC);;

let GLEMMA_LAMBDA_LAYER = prove
 (`!K L i.
     ~(K = 0) /\ i IN 1..K * L
     ==> &((i - 1) DIV K) - (&L - &1) / &2 =
         sum(1..L - 1)
           (\t. (if i IN (K * (L - MIN t (L - t)) + 1)..(K * L)
                 then &1 else &0) -
                (if i IN 1..(K * MIN t (L - t)) then &1 else &0)) / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(i - 1) DIV K < L` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ] THEN UNDISCH_TAC `1 <= i` THEN
    UNDISCH_TAC `i <= K * L` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. (K * (L - m) + 1 <= i /\ i <= K * L <=> L - m <= (i - 1) DIV K) /\
        (1 <= i /\ i <= K * m <=> (i - 1) DIV K < m)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN ASM_SIMP_TAC[LE_RDIV_EQ; RDIV_LT_EQ] THEN
    UNDISCH_TAC `1 <= i` THEN UNDISCH_TAC `i <= K * L` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GLEMMA_COUNT_LAYER] THEN REAL_ARITH_TAC);;

let GLEMMA_SUM_RESTRICT_SUBSET = prove
 (`!s a (h:A->real).
     a SUBSET s ==> sum s (\i. if i IN a then h i else &0) = sum a h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let GLEMMA_SUM_SWAP_IND = prove
 (`!s (u:B->bool) a b (h:A->real).
     FINITE s /\ FINITE u /\ (!t. t IN u ==> a t SUBSET s /\ b t SUBSET s)
     ==> sum s (\i. sum u (\t. (if i IN a t then h i else &0) -
                               (if i IN b t then h i else &0))) =
         sum u (\t. sum (a t) h - sum (b t) h)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\i t. (if i IN (a:B->A->bool) t then (h:A->real) i
                         else &0) -
                        (if i IN (b:B->A->bool) t then h i else &0)`;
                 `s:A->bool`; `u:B->bool`] SUM_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t:B` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[SUM_SUB; GLEMMA_SUM_RESTRICT_SUBSET]);;

let GLEMMA_SUM_LAYER = prove
 (`!K L h.
     ~(K = 0)
     ==> sum(1..K * L) (\i. (&((i - 1) DIV K) - (&L - &1) / &2) * h i) =
         sum(1..L - 1)
           (\t. sum((K * (L - MIN t (L - t)) + 1)..(K * L)) h -
                sum(1..(K * MIN t (L - t))) h) / &2`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `sum(1..K * L)
      (\i. sum(1..L - 1)
             (\t. (if i IN (K * (L - MIN t (L - t)) + 1)..(K * L)
                   then (h:num->real) i else &0) -
                  (if i IN 1..(K * MIN t (L - t)) then h i else &0)) /
           &2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`K:num`; `L:num`; `i:num`] GLEMMA_LAMBDA_LAYER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `(x:real) * y = z ==> x / &2 * y = z / &2`) THEN
    REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; SUM_RMUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC GLEMMA_SUM_SWAP_IND THEN
  REWRITE_TAC[FINITE_NUMSEG; SUBSET_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `t:num` THEN STRIP_TAC THEN
  REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= n + 1`] THEN
  DISJ2_TAC THEN REWRITE_TAC[LE_REFL; LE_MULT_LCANCEL] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Steps II-III: one pair of index sets, then target 2 (the g-lemma).        *)
(* ------------------------------------------------------------------------- *)

let GLEMMA_PAIR_BOUND = prove
 (`!R S (rr:num->num) (ss:num->num) J a b q.
     (!j. j IN J ==> rr j < R /\ ss j < S) /\
     (!j j'. j IN J /\ j' IN J /\ rr j = rr j' /\ ss j = ss j' ==> j = j') /\
     a SUBSET J /\ b SUBSET J /\ DISJOINT a b /\ a HAS_SIZE q /\ b HAS_SIZE q
     ==> abs(sum a (\j. &(rr j)) - sum b (\j. &(rr j))) <=
         &q * (&R * &S - &q) / &S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `g = \j. (rr:num->num) j,(ss:num->num) j` THEN
  SUBGOAL_THEN
   `!x y. x IN (J:num->bool) /\ y IN J /\ (g:num->num#num) x = g y ==> x = y`
  ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN
    UNDISCH_TAC
     `!j j'. j IN (J:num->bool) /\ j' IN J /\
             (rr:num->num) j = rr j' /\ (ss:num->num) j = ss j'
             ==> j = j'` THEN
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c SUBSET (J:num->bool) /\ c HAS_SIZE q
        ==> IMAGE (g:num->num#num) c SUBSET {(r,s) | r < R /\ s < S} /\
            IMAGE g c HAS_SIZE q /\
            &(nsum (IMAGE g c) FST) = sum c (\j. &((rr:num->num) j))`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:num->bool` THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "g" THEN
      UNDISCH_TAC `!j. j IN (J:num->bool) ==> (rr:num->num) j < R /\
                                              (ss:num->num) j < S` THEN
      UNDISCH_TAC `(c:num->bool) SUBSET J` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_PAIR_THM] THEN MESON_TAC[];
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(c:num->bool) SUBSET J` THEN REWRITE_TAC[SUBSET] THEN
      ASM_MESON_TAC[];
      MP_TAC(ISPECL [`g:num->num#num`; `FST:num#num->num`; `c:num->bool`]
        NSUM_IMAGE) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `(c:num->bool) SUBSET J` THEN REWRITE_TAC[SUBSET] THEN
        ASM_MESON_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      EXPAND_TAC "g" THEN REWRITE_TAC[o_DEF; FST] THEN
      UNDISCH_TAC `(c:num->bool) HAS_SIZE q` THEN
      SIMP_TAC[HAS_SIZE; REAL_OF_NUM_SUM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE (g:num->num#num) a) (IMAGE g b) /\
    DISJOINT (IMAGE (g:num->num#num) b) (IMAGE g a)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
    CONJ_TAC THENL [ALL_TAC; SIMP_TAC[DISJOINT_SYM]] THEN
    UNDISCH_TAC
     `!x y. x IN (J:num->bool) /\ y IN J /\ (g:num->num#num) x = g y
            ==> x = y` THEN
    UNDISCH_TAC `DISJOINT (a:num->bool) b` THEN
    UNDISCH_TAC `(a:num->bool) SUBSET J` THEN
    UNDISCH_TAC `(b:num->bool) SUBSET J` THEN
    REWRITE_TAC[SUBSET; IN_DISJOINT; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `a:num->bool` th) THEN
                          MP_TAC(SPEC `b:num->bool` th)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`R:num`; `S:num`; `IMAGE (g:num->num#num) a`;
                 `IMAGE (g:num->num#num) b`; `q:num`]
    GRID_TOP_MINUS_BOTTOM) THEN
  MP_TAC(ISPECL [`R:num`; `S:num`; `IMAGE (g:num->num#num) b`;
                 `IMAGE (g:num->num#num) a`; `q:num`]
    GRID_TOP_MINUS_BOTTOM) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let TWOLOG_G_LEMMA = prove
 (`!K L R S (rr:num->num) (ss:num->num) p.
     1 <= K /\ 1 <= L /\
     (!j. j IN 1..K * L ==> rr j < R /\ ss j < S) /\
     (!j j'. j IN 1..K * L /\ j' IN 1..K * L /\ rr j = rr j' /\ ss j = ss j'
             ==> j = j') /\
     p permutes 1..K * L
     ==> abs(sum(1..K * L)
               (\i. (&((i - 1) DIV K) - (&L - &1) / &2) * &(rr(p i)))) <=
         &L * &R * &(K * L) / &2 * (&1 / &4 - &(K * L) / (&12 * &R * &S))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!i. i IN 1..K * L ==> rr((p:num->num) i) < R /\ ss(p i) < S) /\
    (!i i'. i IN 1..K * L /\ i' IN 1..K * L /\
            rr((p:num->num) i) = rr(p i') /\ ss(p i) = ss(p i') ==> i = i')`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      UNDISCH_TAC `!j. j IN 1..K * L ==> rr j < R /\ ss j < S` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE];
      MAP_EVERY X_GEN_TAC [`i:num`; `i':num`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(p:num->num) i = p i'` MP_TAC THENL
       [UNDISCH_TAC
         `!j j'. j IN 1..K * L /\ j' IN 1..K * L /\
                 (rr:num->num) j = rr j' /\ (ss:num->num) j = ss j'
                 ==> j = j'` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE];
        ASM_MESON_TAC[PERMUTES_INJECTIVE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= K * L` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1 * 1 <= x ==> 1 <= x`) THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= R /\ 1 <= S` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `!i. i IN 1..K * L ==> rr((p:num->num) i) < R /\ ss(p i) < S` THEN
    DISCH_THEN(MP_TAC o SPEC `1`) THEN ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `K * L <= R * S` ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`IMAGE (\i. (rr:num->num)((p:num->num) i),(ss:num->num)(p i))
             (1..K * L)`;
      `{r:num | r < R} CROSS {s:num | s < S}`] CARD_SUBSET) THEN
    SIMP_TAC[CARD_CROSS; FINITE_CROSS; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CROSS; IN_ELIM_THM] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE `x = y ==> x <= z ==> y <= z`) THEN
    MP_TAC(ISPECL [`\i. (rr:num->num)((p:num->num) i),(ss:num->num)(p i)`;
                   `1..K * L`]
      CARD_IMAGE_INJ) THEN
    REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1; PAIR_EQ] THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:num`; `L:num`;
                 `\i. &((rr:num->num)((p:num->num) i)):real`]
    GLEMMA_SUM_LAYER) THEN
  ANTS_TAC THENL [UNDISCH_TAC `1 <= K` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..L - 1) (\t. &(K * MIN t (L - t)) *
                       (&R * &S - &(K * MIN t (L - t))) / &S) / &2` THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC GLEMMA_CLOSED_FORM THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
  MATCH_MP_TAC(REAL_ARITH `(x:real) <= y ==> x / &2 <= y / &2`) THEN
  MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `t:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`R:num`; `S:num`; `\i. (rr:num->num)((p:num->num) i)`;
                 `\i. (ss:num->num)((p:num->num) i)`; `1..K * L`;
                 `(K * (L - MIN t (L - t)) + 1)..(K * L)`;
                 `1..(K * MIN t (L - t))`; `K * MIN t (L - t)`]
    GLEMMA_PAIR_BOUND) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `K * MIN t (L - t) <= K * (L - MIN t (L - t)) /\
    K * (L - MIN t (L - t)) + K * MIN t (L - t) = K * L`
  MP_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL; GSYM LEFT_ADD_DISTRIB] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN ARITH_TAC; AP_TERM_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  SPEC_TAC(`K * MIN t (L - t)`,`y:num`) THEN
  SPEC_TAC(`K * (L - MIN t (L - t))`,`x:num`) THEN
  SPEC_TAC(`K * L`,`z:num`) THEN
  REWRITE_TAC[SUBSET_NUMSEG; DISJOINT_NUMSEG; HAS_SIZE_NUMSEG_1; HAS_SIZE;
              FINITE_NUMSEG; CARD_NUMSEG] THEN
  ARITH_TAC);;
