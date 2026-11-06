(* ========================================================================= *)
(* The upper bound for S(B,P,y) and Chen's theorem ([N] 10.6-10.8).          *)
(*                                                                           *)
(* CHEN_SB_UPPER_GEN: by the bilinear form inequality BILINEAR_BV ([N]       *)
(* Theorem 10.7, bilinear.ml), for every e > 0 there is N0 such that for     *)
(* all even N >= N0 and all even h with 1 <= h <= N                          *)
(*   S_B <= (A c_B / 4 + e) (N / log N) V(N^(1/8)),                          *)
(* S_B the number of triples z <= p1 < y <= p2 <= p3, p1 p2 p3 < N,          *)
(* (p1 p2 p3,h) = 1, with |h - p1 p2 p3| free of primes below y = N^(1/3).   *)
(* With CHEN_FROM_SB_GEN this gives CHEN_GENERAL: chen_sieve_ok h implies    *)
(* #{n in gchen_A (h N) N | n = P2} >= c N / log^2 N; chen.ml takes          *)
(* h(N) = N (Goldbach) and h(N) = 2 (twins).                                 *)
(*                                                                           *)
(* Method.  The triples are covered by the disjoint sets T_k: p1 in          *)
(* (l_k,l_(k+1)], l_k = N^(1/8) exp(k / log N), and the box condition        *)
(* l_k p2 p3 < N instead of p1 p2 p3 < N (at most log^2 N intervals).  For   *)
(* each k the values |h - p1 p2 p3| (chen_dist) are sifted by JURKAT_RICHERT *)
(* at level sqrt N / log^8 N, so s -> 3/2 and F(s) = 2A/3.  The pairs        *)
(* (p2 p3,p1) are counted with the 0/1 weight chen_alpha (PRIME_PAIR_UNIQUE, *)
(* no unique factorisation); each remainder is the bilinear discrepancy      *)
(* (residue h mod d) plus trivially bounded terms for p1 | h (at most 8      *)
(* primes p1 >= z divide h <= N) and for (p1,d) > 1.  Main term:             *)
(* V(y) <= (3/8)(1 + o(1)) V(z) by Mertens' product, and                     *)
(*   sum_k |T_k| <= |T^| <= (1 + o(1)) (N / log N) c_B                       *)
(* by PRIME_SUM_SCALED twice: inner G_b(a) = (log a - log(1 - b - a))/(1-b), *)
(* outer psi(b) = P(1 - 3b)/(1 - b), using log(2 - 3b) <= P(1 - 3b)          *)
(* (LOG_LE_CUBIC), P(x) = x - x^2/2 + x^3/3.                                 *)
(* ========================================================================= *)

needs "Sieve/chen_main.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* General lemmas: counting, sums over subsets, sieving images.              *)
(* ------------------------------------------------------------------------- *)

let CARD_LARGE_PRIME_DIVISORS = prove
 (`!N u k. ~(N = 0) /\ &1 <= u /\ &N < u pow (k + 1)
           ==> CARD {p | prime p /\ u <= &p /\ p divides N} <= k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{p | prime p /\ u <= &p /\ p divides N} SUBSET
    {p | prime p /\ p divides N}`
  ASSUME_TAC THENL [SIMP_TAC[SUBSET; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {p | prime p /\ u <= &p /\ p divides N}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p | prime p /\ p divides N}` THEN
    ASM_SIMP_TAC[FINITE_PRIME_DIVISORS];
    ALL_TAC] THEN
  ABBREV_TAC `D = {p | prime p /\ u <= &p /\ p divides N}` THEN
  SUBGOAL_THEN `u pow (CARD(D:num->bool)) <= &N` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `product D (\p:num. &p)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM PRODUCT_CONST] THEN MATCH_MP_TAC PRODUCT_LE THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_NPRODUCT; REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `nproduct {p | prime p /\ p divides N} (\p. p)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC NPRODUCT_SUBSET_LE THEN
        ASM_SIMP_TAC[FINITE_PRIME_DIVISORS; IN_ELIM_THM] THEN
        X_GEN_TAC `p:num` THEN STRIP_TAC THEN
        MP_TAC(SPEC `p:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
        ARITH_TAC;
        MP_TAC(SPEC `N:num` NPRODUCT_PRIME_DIVISORS_DIVIDES) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `u pow (k + 1) <= u pow (CARD(D:num->bool))` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `k < CARD(D:num->bool)` THEN ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let INV_ONE_MINUS_LE_EXP = prove
 (`!x. &0 <= x /\ x <= &1 / &2 ==> inv(&1 - x) <= exp(&2 * x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 + &2 * x` THEN REWRITE_TAC[REAL_EXP_LE_X] THEN
  SUBGOAL_THEN `&0 < &1 - x` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&1 - x) = &1 / (&1 - x)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= x * (&1 - &2 * x)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let X_DIV_LOG_MONO = prove
 (`!s t. exp(&1) <= s /\ s <= t ==> s / log s <= t / log t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s /\ &1 <= log s /\ log s <= log t` STRIP_ASSUME_TAC
  THENL
   [MP_TAC E_BOUNDS THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log s /\ &0 < log t /\ &0 < t` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RAT_LEMMA4] THEN
  SUBGOAL_THEN `log t <= log s + (t / s - &1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `log t = log s + log(&1 + (t / s - &1))` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ARITH `&1 + (a - &1) = a`] THEN
      ASM_SIMP_TAC[LOG_DIV] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC LOG_LE THEN
      REWRITE_TAC[REAL_SUB_LE] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s * log t <= s * (log s + (t / s - &1))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `s * t / s = t:real` (fun th ->
    REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB; th]) THENL
   [MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(t - s) * &1 <= (t - s) * log s` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let LOG_LE_CUBIC = prove
 (`!x. &0 <= x ==> log(&1 + x) <= x - x pow 2 / &2 + x pow 3 / &3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\t. t - t pow 2 / &2 + t pow 3 / &3 - log(&1 + t)`;
    `\t. t pow 3 / (&1 + t)`; `real_interval[&0,x]`; `&0`; `x:real`]
   HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MP_TAC(DISCH_ALL(REAL_DIFF_CONV
       `((\t. t - t pow 2 / &2 + t pow 3 / &3 - log(&1 + t))
         has_real_derivative f') (atreal t)`)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `~(&1 + t = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[LOG_1] THEN REAL_ARITH_TAC]);;

let POLY_LE_EXP = prove
 (`!n b x. &0 < b /\ (&(n + 1) / b) pow (n + 1) <= x
           ==> x pow n <= exp(b * x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `(&(n + 1) / b) pow (n + 1)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((b * x) / &(n + 1)) pow (n + 1)` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC EXP_GE_POW THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `((b * x) / &(n + 1)) pow (n + 1) =
                x pow n * (x * (b / &(n + 1)) pow (n + 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_POW_MUL; REAL_POW_DIV] THEN
    SUBGOAL_THEN `~(&(n + 1) = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 = (&(n + 1) / b) pow (n + 1) * (b / &(n + 1)) pow (n + 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN
    SUBGOAL_THEN `&(n + 1) / b * b / &(n + 1) = &1` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(&(n + 1) = &0)` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC;
        UNDISCH_TAC `&0 < b` THEN CONV_TAC REAL_FIELD];
      REWRITE_TAC[REAL_POW_ONE]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
  ASM_REAL_ARITH_TAC);;

let EXP_ABS_SMALL = prove
 (`!x. abs x <= inv(&2) ==> exp x <= &1 + &2 * abs x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(abs x)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN ASM_REWRITE_TAC[REAL_ABS_POS]]);;

let CARD_PAIRS_LE = prove
 (`!(s:A->bool) (t:A->B->bool) S.
        FINITE s /\ (!a. a IN s ==> FINITE(t a)) /\
        (!a b. (a,b) IN S ==> a IN s /\ b IN t a)
        ==> &(CARD S) <= sum s (\a. &(CARD(t a)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {a,b | (a:A) IN s /\ (b:B) IN t a}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:A#B->bool) SUBSET {a,b | a IN s /\ b IN t a}` ASSUME_TAC
  THENL
   [REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {a,b | (a:A) IN s /\ (b:B) IN t a})` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  SUBGOAL_THEN `sum s (\a. &(CARD((t:A->B->bool) a))) =
                sum s (\a. sum (t a) (\b. &1))` SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[CARD_EQ_SUM]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_SUM_PRODUCT; CARD_EQ_SUM] THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM]);;

let CARD_TRIPLES_LE = prove
 (`!(s:A->bool) (t:A->B->bool) (u:A->B->C->bool) S.
        FINITE s /\ (!a. a IN s ==> FINITE(t a)) /\
        (!a b. a IN s /\ b IN t a ==> FINITE(u a b)) /\
        (!a b c. (a,b,c) IN S ==> a IN s /\ b IN t a /\ c IN u a b)
        ==> &(CARD S) <= sum s (\a. sum (t a) (\b. &(CARD(u a b))))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s (\a. &(CARD {x:B#C | (a:A,x) IN S}))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_PAIRS_LE THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[PAIR]] THEN
    X_GEN_TAC `a:A` THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{b,c | (b:B) IN t (a:A) /\ (c:C) IN u a b}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_SIMP_TAC[];
      REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM;
                  IN_ELIM_THM] THEN
      ASM_MESON_TAC[]];
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `a:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC CARD_PAIRS_LE THEN ASM_SIMP_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[]]);;

let CARD_PAIRS_LE_SND = prove
 (`!(s:B->bool) (t:B->A->bool) S.
        FINITE S /\ FINITE s /\ (!b. b IN s ==> FINITE(t b)) /\
        (!a b. (a,b) IN S ==> b IN s /\ a IN t b)
        ==> &(CARD S) <= sum s (\b. &(CARD(t b)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CARD(S:A#B->bool) =
                CARD(IMAGE (\x:A#B. (SND x,FST x)) S)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_PAIRS_LE THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[]);;

let SUM_POWERSET_PRODUCT = prove
 (`!g s. FINITE s
         ==> sum {t | t SUBSET s} (\t. product t g) =
             product s (\p:A. &1 + g p)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_EMPTY; SING_GSPEC; SUM_SING; PRODUCT_CLAUSES];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_POWERSET_INSERT; PRODUCT_CLAUSES] THEN
  SUBGOAL_THEN
   `sum {t | t SUBSET s} (\t. product (a INSERT t) g) =
    g a * sum {t | t SUBSET s} (\t. product t (g:A->real))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `t:A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE(t:A->bool) /\ ~((a:A) IN t)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ASM_SIMP_TAC[PRODUCT_CLAUSES]];
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let PRIME_PAIR_UNIQUE = prove
 (`!p q r s. prime p /\ prime q /\ prime r /\ prime s /\ p <= q /\ r <= s /\
             p * q = r * s ==> p = r /\ q = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p divides r * s /\ r divides p * q` MP_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
      MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL];
      FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
      MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[DIVIDES_REFL]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PRIME_DIVPROD_EQ; DIVIDES_PRIME_PRIME] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p:num = r` SUBST_ALL_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(p:num = r \/ p = s) /\ (r = p \/ r = q)`; `p <= q:num`;
      `r <= s:num`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  UNDISCH_TAC `(r:num) * q = r * s` THEN REWRITE_TAC[EQ_MULT_LCANCEL] THEN
  ASM_MESON_TAC[PRIME_IMP_NZ]);;

let CARD_CONG_MULT_LE = prove
 (`!p d c X. coprime(p,d) /\ ~(d = 0) /\ &0 <= X
             ==> &(CARD {m | 1 <= m /\ &m <= X /\ (m * p == c) (mod d)})
                 <= X / &d + &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `X:real` FLOOR_POS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  MP_TAC(SPEC `X:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `S = {m | 1 <= m /\ &m <= X /\ (m * p == c) (mod d)}` THEN
  ASM_CASES_TAC `S:num->bool = {}` THENL
   [ASM_REWRITE_TAC[CARD_CLAUSES] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &1`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `m0:num` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY])
  THEN
  SUBGOAL_THEN `S SUBSET {n | n IN 1..M /\ n MOD d = m0 MOD d}` ASSUME_TAC
  THENL
   [UNDISCH_TAC `(m0:num) IN S` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN STRIP_TAC THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `&m < &M + &1` MP_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM CONG] THEN MATCH_MP_TAC CONG_MULT_RCANCEL THEN
    EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONG_SYM; CONG_TRANS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {n | n IN 1..M /\ n MOD d = m0 MOD d})` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `m0 MOD d`; `M:num`] CARD_RESIDUE_CLASS) THEN
  ASM_SIMP_TAC[MOD_LT_EQ] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(M DIV d) + &1` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + &1 <= y + &1`) THEN
  SUBGOAL_THEN `&0 < &d` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&M` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  ASM_MESON_TAC[DIVISION; LE_ADD; ADD_SYM]);;

let FINITE_PRIME_TRIPLES_LT = prove
 (`!P M. FINITE {p1,p2,p3 | prime p1 /\ prime p2 /\ prime p3 /\
                            P p1 p2 p3 /\ &(p1 * p2 * p3) < M}`,
  REPEAT GEN_TAC THEN MP_TAC(SPEC `M:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(0..n) CROSS ((0..n) CROSS (0..n))` THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_TRIPLE; IN_CROSS;
              IN_NUMSEG; LE_0] THEN
  MAP_EVERY X_GEN_TAC [`p1:num`; `p2:num`; `p3:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p1 * p2 * p3 <= (n:num)` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(p1 = 0) /\ ~(p2 = 0) /\ ~(p3 = 0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `~(p2 * p3 = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MULT_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `p1 <= p1 * p2 * p3 /\ p2 <= p1 * p2 * p3 /\
                p3 <= p1 * p2 * (p3:num)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(CONJUNCT1 LE_MULT_NZ) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p2 * p3:num` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(CONJUNCT1 LE_MULT_NZ);
        MATCH_MP_TAC(CONJUNCT2 LE_MULT_NZ)] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p2 * p3:num` THEN
      CONJ_TAC THEN MATCH_MP_TAC(CONJUNCT2 LE_MULT_NZ) THEN
      ASM_REWRITE_TAC[]];
    ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Mertens' product: V(y) <= (3/8)(1 + o(1)) V(z).                           *)
(* ------------------------------------------------------------------------- *)

let MERTENS_PRODUCT_UPPER = prove
 (`?C. !u v. &2 <= u /\ u <= v
             ==> product {p | prime p /\ u <= &p /\ &p < v}
                         (\p. &1 - inv(&p))
                 <= log u / log v * exp(C / log u)`,
  X_CHOOSE_THEN `C:real` ASSUME_TAC MERTENS_PRODUCT_LOG THEN
  EXISTS_TAC `abs C` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log u /\ log u <= log v /\ &0 < log v`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real`; `v:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `S = {p | prime p /\ u <= &p /\ &p < v}` THEN
  SUBGOAL_THEN `FINITE(S:num->bool) /\ (!p. p IN S ==> &2 <= &p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p | prime p /\ &p < v}` THEN
      REWRITE_TAC[FINITE_PRIMES_LT] THEN SET_TAC[];
      REWRITE_TAC[REAL_OF_NUM_LE] THEN MESON_TAC[PRIME_GE_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product S (\p. &1 - inv(&p)) =
    exp(--(sum S (\p. --log(&1 - inv(&p)))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_NEG; REAL_NEG_NEG] THEN ASM_SIMP_TAC[REAL_EXP_SUM] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXP_LOG THEN
    REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_INV_LT_1 THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `S:num->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(log(log u) - log(log v) + abs C / log u)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    SUBGOAL_THEN `C / log u <= abs C / log u` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC
     `abs(sum S (\p. --log(&1 - inv(&p))) - (log(log v) - log(log u)))
      <= C / log u` THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_EXP_ADD; REAL_EXP_SUB; EXP_LOG; real_div] THEN
    REAL_ARITH_TAC]);;

let CHEN_V_YZ = prove
 (`?C. !h N. EVEN h /\ 1 <= h /\ h <= N /\ EVEN N /\ 256 < N
           ==> product {p | prime p /\ &p < exp(&1 / &3 * log(&N))}
                       (\p. &1 - chen_g h p)
               <= (&3 / &8 * exp(C / (&1 / &8 * log(&N)) +
                                 &16 / exp(&1 / &8 * log(&N)))) *
                  product {p | prime p /\ &p < exp(&1 / &8 * log(&N))}
                          (\p. &1 - chen_g h p)`,
  X_CHOOSE_TAC `C:real` MERTENS_PRODUCT_UPPER THEN EXISTS_TAC `C:real` THEN
  MAP_EVERY X_GEN_TAC [`h:num`; `N:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&h <= &N` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&8 * log(&2) <= log(&N) /\ &0 < log(&N) /\ &0 < &N`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `256 < N` THEN ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      UNDISCH_TAC `256 < N` THEN ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `256 < N` THEN ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `LN = log(&N)` THEN
  SUBGOAL_THEN
   `&2 <= exp(&1 / &8 * LN) /\ exp(&1 / &8 * LN) <= exp(&1 / &3 * LN) /\
    &N < exp(&1 / &8 * LN) pow (8 + 1) /\
    log(exp(&1 / &8 * LN)) = &1 / &8 * LN /\
    log(exp(&1 / &8 * LN)) / log(exp(&1 / &3 * LN)) = &3 / &8`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LOG_EXP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log(&2))` THEN
      CONJ_TAC THENL
       [SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`; REAL_LE_REFL];
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_EXP_N] THEN CONV_TAC NUM_REDUCE_CONV THEN
      SUBGOAL_THEN `&N = exp LN` SUBST1_TAC THENL
       [EXPAND_TAC "LN" THEN ASM_SIMP_TAC[EXP_LOG]; ALL_TAC] THEN
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < LN` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ABBREV_TAC `z = exp(&1 / &8 * LN)` THEN
  ABBREV_TAC `y = exp(&1 / &3 * LN)` THEN
  SUBGOAL_THEN
   `{p | prime p /\ &p < y} =
    {p | prime p /\ &p < z} UNION {p | prime p /\ z <= &p /\ &p < y} /\
    DISJOINT {p | prime p /\ &p < z} {p | prime p /\ z <= &p /\ &p < y}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; DISJOINT; IN_UNION; IN_INTER; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN
    CONJ_TAC THEN X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `S = {p | prime p /\ z <= &p /\ &p < y}` THEN
  SUBGOAL_THEN `FINITE(S:num->bool) /\
                (!p. p IN S ==> prime p /\ z <= &p /\ &2 <= &p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p | prime p /\ &p < y}` THEN
      REWRITE_TAC[FINITE_PRIMES_LT] THEN SIMP_TAC[SUBSET; IN_ELIM_THM];
      X_GEN_TAC `p:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_UNION; FINITE_PRIMES_LT] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[CHEN_V_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `product S (\p. &1 - inv(&p)) *
              product S (\p. if p divides h then inv(&1 - inv(&p))
                             else &1)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM PRODUCT_MUL] THEN MATCH_MP_TAC PRODUCT_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `S:num->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`h:num`; `p:num`] CHEN_G_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 - inv(&p) /\ inv(&p) <= inv(&p - &1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_INV_LT_1 THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[chen_g] THEN COND_CASES_TAC THENL
     [REWRITE_TAC[REAL_SUB_RZERO] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_RINV THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_ADD; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `!x:real. x <= &1 ==> &0 <= &1 - x`) THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `S:num->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log z / log y * exp(C / log z)` THEN CONJ_TAC THENL
     [EXPAND_TAC "S" THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `C:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_INV THEN
    MATCH_MP_TAC(REAL_ARITH `!x:real. x <= &1 ==> &0 <= &1 - x`) THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `S:num->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM PRODUCT_RESTRICT_SET] THEN
  SUBGOAL_THEN `CARD {p | p IN S /\ p divides h} <= 8` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD {p | prime p /\ z <= &p /\ p divides h}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
       [EXPAND_TAC "S" THEN SIMP_TAC[SUBSET; IN_ELIM_THM];
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{p | prime p /\ p divides h}` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC FINITE_PRIME_DIVISORS THEN ASM_ARITH_TAC;
          SIMP_TAC[SUBSET; IN_ELIM_THM]]];
      MATCH_MP_TAC CARD_LARGE_PRIME_DIVISORS THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {p | p IN S /\ p divides h}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `product {p | p IN S /\ p divides h} (\p. exp(&2 / z))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `S:num->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= inv(&p) /\ inv(&p) <= &1 / &2 /\ inv(&p) <= inv z`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&2 * inv(&p))` THEN
    ASM_SIMP_TAC[INV_ONE_MINUS_LE_EXP] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE; real_div] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_CONST] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&2 / z) pow 8` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[REAL_EXP_LE_1_PLUS] THEN
    MATCH_MP_TAC(REAL_ARITH `!x:real. &1 + x <= e /\ &0 <= x ==> &1 <= e`) THEN
    EXISTS_TAC `&2 / z` THEN REWRITE_TAC[REAL_EXP_LE_X] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_EXP_N; REAL_EXP_MONO_LE; real_div] THEN
    REAL_ARITH_TAC]);;

let PRODUCT_ONE_PLUS_LE_INV = prove
 (`!N s. FINITE s /\ (!p. p IN s ==> prime p) /\ EVEN N
         ==> product s (\p. &1 + chen_g N p) <=
             inv(product s (\p. &1 - chen_g N p))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM PRODUCT_INV] THEN
  MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`N:num`; `p:num`] CHEN_G_BOUNDS) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - chen_g N p` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&1 - chen_g N p) = &1 / (&1 - chen_g N p)` SUBST1_TAC
  THENL [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `(&1 + chen_g N p) * (&1 - chen_g N p) =
                &1 - chen_g N p * chen_g N p` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPEC `chen_g N p` REAL_LE_SQUARE) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The number of triples: |T^| <= (1 + e) (M / log N) (c_B + O(1/log N)).    *)
(* ------------------------------------------------------------------------- *)

let PI_LT_REAL_UPPER = prove
 (`!e. &0 < e
       ==> ?X0. !x. X0 <= x
                    ==> &(CARD {p | prime p /\ &p < x})
                        <= (&1 + e) * x / log x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e:real` PI_UPTO_ASYMPTOTIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  EXISTS_TAC `&N1 + &3` THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `n:num`)] THEN
  MP_TAC(SPEC `x:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `N1 <= n /\ 3 <= n` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&N1 < &n + &1 /\ &3 < &n + &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(pi_upto n)` THEN CONJ_TAC THENL
   [REWRITE_TAC[pi_upto; REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&p < &n + &1` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC;
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..n` THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
      ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + e) * &n / log(&n)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC X_DIV_LOG_MONO THEN CONJ_TAC THENL
     [MP_TAC E_BOUNDS THEN
      SUBGOAL_THEN `&3 <= &n` MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC]]);;

let CHEN_P2_SUM = prove
 (`!X b d. &1 < X /\ &1 / &8 <= b /\ b <= &1 / &3 /\
           &0 <= d /\ d <= &1 / &6 /\ &2 <= exp(&1 / &3 * log X)
           ==> sum {p | prime p /\ exp(&1 / &3 * log X) < &p /\
                        &p <= exp((&1 - b + d) / &2 * log X)}
                   (\p. inv(&1 - b - log(&p) / log X) / &p)
               <= ((&1 - &3 * b) - (&1 - &3 * b) pow 2 / &2 +
                   (&1 - &3 * b) pow 3 / &3) / (&1 - b) +
                  &6 * d + &1200 / log X`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log X` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\u. inv(&1 - b - u)`; `\u. inv((&1 - b - u) pow 2)`;
    `\u. (log u - log(&1 - b - u)) / (&1 - b)`; `X:real`; `&1 / &3`;
    `(&1 - b + d) / &2`] PRIME_SUM_SCALED) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      MP_TAC(DISCH_ALL(REAL_DIFF_CONV
        `((\u. inv(&1 - b - u)) has_real_derivative f') (atreal u)`)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      DISJ1_TAC THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_LE_POW_2];
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      MP_TAC(DISCH_ALL(REAL_DIFF_CONV
        `((\u. (log u - log(&1 - b - u)) / (&1 - b)) has_real_derivative f')
         (atreal u)`)) THEN
      REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `~(u = &0) /\ ~(&1 - b - u = &0) /\ ~(&1 - b = &0)`
      MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&1 - b - (&1 - b + d) / &2 = (&1 - b - d) / &2 /\
    &1 - b - &1 / &3 = (&2 - &3 * b) / &3`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 / &2 <= &1 - b - d /\ &1 / &3 <= &2 - &3 * b /\ &2 / &3 <= &1 - b`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(inv((&1 - b - d) / &2)) +
    abs(inv((&1 - b - d) / &2) - inv((&2 - &3 * b) / &3)) <= &8`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `&0 <= inv((&1 - b - d) / &2) /\ inv((&1 - b - d) / &2) <= &4 /\
      &0 <= inv((&2 - &3 * b) / &3) /\ inv((&2 - &3 * b) / &3) <= &4`
    MP_TAC THENL
     [REWRITE_TAC[REAL_INV_DIV] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_LDIV_EQ;
                   REAL_ARITH `&1 / &3 <= x ==> &0 < x`;
                   REAL_ARITH `&1 / &2 <= x ==> &0 < x`;
                   REAL_ARITH `&1 / &3 <= x ==> &0 <= x`;
                   REAL_ARITH `&1 / &2 <= x ==> &0 <= x`] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(log((&1 - b + d) / &2) - log((&1 - b - d) / &2)) / (&1 - b) -
    (log(&1 / &3) - log((&2 - &3 * b) / &3)) / (&1 - b) =
    (log(&1 + (&2 * d) / (&1 - b - d)) + log(&1 + (&1 - &3 * b))) / (&1 - b)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `&1 + (&2 * d) / (&1 - b - d) = ((&1 - b + d) / &2) / ((&1 - b - d) / &2)
      /\ &1 + (&1 - &3 * b) = ((&2 - &3 * b) / &3) / (&1 / &3)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `&1 / &2 <= &1 - b - d` THEN CONV_TAC REAL_FIELD;
        CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (&1 - b + d) / &2 /\ &0 < (&1 - b - d) / &2 /\
                  &0 < (&2 - &3 * b) / &3 /\ &0 < &1 / &3`
    MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[LOG_DIV] THEN REPEAT DISCH_TAC THEN
    UNDISCH_TAC `&2 / &3 <= &1 - b` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `log(&1 + (&2 * d) / (&1 - b - d)) <= &4 * d /\
    log(&1 + (&1 - &3 * b)) <=
    (&1 - &3 * b) - (&1 - &3 * b) pow 2 / &2 + (&1 - &3 * b) pow 3 / &3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * d) / (&1 - b - d)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LOG_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
        ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH
         `&1 / &2 <= x ==> &0 < x`] THEN
        SUBGOAL_THEN `&0 <= d * (&1 - b - d - &1 / &2)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC]];
      MATCH_MP_TAC LOG_LE_CUBIC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!s a e f:real. a + e <= f ==> abs(s - a) <= e ==> s <= f`) THEN
  SUBGOAL_THEN `&50 / (&1 / &3 * log X) * &8 = &1200 / log X` ASSUME_TAC
  THENL [UNDISCH_TAC `&0 < log X` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN
   `&50 / (&1 / &3 * log X) *
    (abs(inv((&1 - b - d) / &2)) +
     abs(inv((&1 - b - d) / &2) - inv((&2 - &3 * b) / &3))) <=
    &1200 / log X`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(log(&1 + (&2 * d) / (&1 - b - d)) + log(&1 + (&1 - &3 * b))) / (&1 - b)
    <= ((&1 - &3 * b) - (&1 - &3 * b) pow 2 / &2 +
        (&1 - &3 * b) pow 3 / &3) / (&1 - b) + &6 * d`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&4 * d + ((&1 - &3 * b) - (&1 - &3 * b) pow 2 / &2 +
                           (&1 - &3 * b) pow 3 / &3)) / (&1 - b)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&2 / &3 <= x ==> &0 < x`] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + z <= z + y`) THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&2 / &3 <= x ==> &0 < x`] THEN
    SUBGOAL_THEN `&0 <= d * (&1 - b - &2 / &3)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let CHEN_P1_SUM = prove
 (`!X. &1 < X /\ &2 <= exp(&1 / &8 * log X)
       ==> sum {p | prime p /\ exp(&1 / &8 * log X) < &p /\
                    &p <= exp(&1 / &3 * log X)}
               (\p. ((&1 - &3 * log(&p) / log X) -
                     (&1 - &3 * log(&p) / log X) pow 2 / &2 +
                     (&1 - &3 * log(&p) / log X) pow 3 / &3) /
                    (&1 - log(&p) / log X) / &p)
           <= chen_cB + &240 / log X`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log X` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\u. ((&1 - &3 * u) - (&1 - &3 * u) pow 2 / &2 +
          (&1 - &3 * u) pow 3 / &3) / (&1 - u)`;
    `\u. ((&9 / &2 + &18 * u) * (&1 - u) pow 2 - &20 / &3) /
         (&1 - u) pow 2`;
    `\u. &9 / &2 * (u + u pow 2) + &5 / &6 * log u +
         &20 / &3 * log(&1 - u)`;
    `X:real`; `&1 / &8`; `&1 / &3`] PRIME_SUM_SCALED) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      MP_TAC(DISCH_ALL(REAL_DIFF_CONV
        `((\u. ((&1 - &3 * u) - (&1 - &3 * u) pow 2 / &2 +
                (&1 - &3 * u) pow 3 / &3) / (&1 - u))
          has_real_derivative f') (atreal u)`)) THEN
      REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `~(&1 - u = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      DISJ2_TAC THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      REWRITE_TAC[real_div; REAL_ARITH `x * y <= &0 <=> &0 <= --x * y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN
      SUBGOAL_THEN `&0 <= u pow 2 * (&1 / &3 - u) /\
                    &0 <= (u - &3 / &17) pow 2`
      MP_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
          ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_LE_POW_2]];
        REAL_ARITH_TAC];
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      MP_TAC(DISCH_ALL(REAL_DIFF_CONV
        `((\u. &9 / &2 * (u + u pow 2) + &5 / &6 * log u +
               &20 / &3 * log(&1 - u)) has_real_derivative f')
         (atreal u)`)) THEN
      REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `~(u = &0) /\ ~(&1 - u = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!s a e f c:real. a = c /\ e <= f ==> abs(s - a) <= e ==> s <= c + f`) THEN
  CONJ_TAC THENL [REWRITE_TAC[chen_cB]; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `&50 / (&1 / &8 * log X) * &785 / &1344 =
                (&400 * &785 / &1344) / log X`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < log X` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let CHEN_P1_RECIP_SUM = prove
 (`!X. &1 < X /\ &2 <= exp(&1 / &8 * log X)
       ==> sum {p | prime p /\ exp(&1 / &8 * log X) < &p /\
                    &p <= exp(&1 / &3 * log X)} (\p. inv(&p))
           <= &2 + &400 / log X`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log X` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\u:real. &1`; `\u:real. &0`; `log`; `X:real`; `&1 / &8`; `&1 / &3`]
   PRIME_SUM_SCALED) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      MP_TAC(SPEC `u:real` HAS_REAL_DERIVATIVE_LOG) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ETA_AX; real_div; REAL_MUL_LID]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH
   `!s s' a e f:real. s' = s /\ a <= &2 /\ e = f
     ==> abs(s - a) <= e ==> s' <= &2 + f`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[real_div; REAL_MUL_LID];
    SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &1 /\ &0 < &3 /\ &0 < &8`; LOG_1] THEN
    SUBGOAL_THEN `log(&8) = &3 * log(&2)` SUBST1_TAC THENL
     [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC LOG_2_UPPER THEN MP_TAC LOG_3_LOWER THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&0 < log X` THEN CONV_TAC REAL_FIELD]);;

let CHEN_THAT_CARD_FIXED = prove
 (`!N M e X0.
        EVEN N /\ 256 < N /\ &400 <= log(&N) /\ &0 < e /\
        X0 <= exp(&1 / &3 * log(&N)) /\
        (!x. X0 <= x
             ==> &(CARD {p | prime p /\ &p < x}) <= (&1 + e) * x / log x) /\
        &N <= M /\ M <= exp(&1) * &N
        ==> &(CARD {p1,p2,p3 | prime p1 /\ prime p2 /\ prime p3 /\
                              exp(&1 / &8 * log(&N)) <= &p1 /\
                              &p1 < exp(&1 / &3 * log(&N)) /\
                              exp(&1 / &3 * log(&N)) <= &p2 /\
                              p2 <= p3 /\ &(p1 * p2 * p3) < M})
            <= (&1 + e) * M / log(&N) * (chen_cB + &4000 / log(&N))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &N /\ &1 < &N /\ &0 < M` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&N` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&N) <= log M /\ log M <= &1 + log(&N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(exp(&1) * &N)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[LOG_MUL; REAL_EXP_POS_LT; LOG_EXP; REAL_LE_REFL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 <= exp(&1 / &8 * log(&N)) /\
    !p. prime p ==> ~(&p = exp(&1 / &8 * log(&N))) /\
                    ~(&p = exp(&1 / &3 * log(&N)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log(&2))` THEN
      CONJ_TAC THENL
       [SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`; REAL_LE_REFL];
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN MP_TAC LOG_2_UPPER THEN
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN CONJ_TAC THEN
      MATCH_MP_TAC ROOT_NOT_PRIME THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `LN = log(&N)` THEN
  SUBGOAL_THEN `&0 < LN` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (log M - LN) / LN /\ (log M - LN) / LN <= inv LN /\
                (log M - LN) / LN <= &1 / &6` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `d = (log M - LN) / LN` THEN
  ABBREV_TAC `z = exp(&1 / &8 * LN)` THEN
  ABBREV_TAC `y = exp(&1 / &3 * LN)` THEN
  SUBGOAL_THEN `z <= y /\ &0 < z` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["z"; "y"] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE; REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. prime p /\ z < &p /\ &p <= y
        ==> &1 / &8 <= log(&p) / LN /\ log(&p) / LN <= &1 / &3 /\
            &0 < &p`
  (LABEL_TAC "p1rng") THENL
   [X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < &p` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `!x a y:real. x = a /\ a <= y ==> x <= y`) THEN
      EXISTS_TAC `log z` THEN CONJ_TAC THENL
       [EXPAND_TAC "z" THEN REWRITE_TAC[LOG_EXP] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `!x a y:real. y = a /\ x <= a ==> x <= y`) THEN
      EXISTS_TAC `log y` THEN CONJ_TAC THENL
       [EXPAND_TAC "y" THEN REWRITE_TAC[LOG_EXP] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `s = {p | prime p /\ z < &p /\ &p <= y}` THEN
  ABBREV_TAC
   `t = \p1. {p | prime p /\ y < &p /\
                  &p <= exp((&1 - log(&p1) / LN + d) / &2 * LN)}` THEN
  ABBREV_TAC `u = \p1 p2. {p | prime p /\ &p < M / (&p1 * &p2)}` THEN
  SUBGOAL_THEN
   `!p1:num. (&1 - log(&p1) / LN + d) / &2 * LN = (log M - log(&p1)) / &2`
  (LABEL_TAC "bexp") THENL
   [GEN_TAC THEN EXPAND_TAC "d" THEN UNDISCH_TAC `&0 < LN` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(s:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p | prime p /\ &p < y + &1}` THEN
    REWRITE_TAC[FINITE_PRIMES_LT; SUBSET; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!p1. FINITE((t:num->num->bool) p1)` (LABEL_TAC "tfin") THENL
   [X_GEN_TAC `p1:num` THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p | prime p /\
                     &p < exp((&1 - log(&p1) / LN + d) / &2 * LN) + &1}` THEN
    REWRITE_TAC[FINITE_PRIMES_LT; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[REAL_ARITH `!x e:real. x <= e ==> x < e + &1`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s (\p1. sum ((t:num->num->bool) p1)
                             (\p2. &(CARD((u:num->num->num->bool) p1 p2))))`
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_TRIPLES_LE THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`p1:num`; `p2:num`] THEN STRIP_TAC THEN
      EXPAND_TAC "u" THEN REWRITE_TAC[FINITE_PRIMES_LT];
      MAP_EVERY X_GEN_TAC [`p1:num`; `p2:num`; `p3:num`] THEN
      REWRITE_TAC[IN_ELIM_TRIPLE] THEN STRIP_TAC THEN
      MAP_EVERY EXPAND_TAC ["s"; "t"; "u"] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < &p1 /\ &0 < &p2 /\ &0 < &p3` STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
        ALL_TAC] THEN
      SUBGOAL_THEN `&p1 * &p2 * &p2 <= &p1 * &p2 * &p3 /\
                    &p1 * &p2 * &p3 < M` STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_MUL] THEN
        REWRITE_TAC[REAL_OF_NUM_LE] THEN
        REPEAT(MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL]) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[REAL_LE_LT];
        ASM_REAL_ARITH_TAC;
        ASM_MESON_TAC[REAL_LE_LT];
        SUBGOAL_THEN `&p2 = exp(log(&p2))` SUBST1_TAC THENL
         [ASM_SIMP_TAC[EXP_LOG]; ALL_TAC] THEN
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN
        SUBGOAL_THEN `log(&p1 * &p2 * &p2) <= log M` MP_TAC THENL
         [MATCH_MP_TAC LOG_MONO_LE_IMP THEN
          ASM_SIMP_TAC[REAL_LT_MUL] THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[LOG_MUL; REAL_LT_MUL] THEN REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_MUL] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `K = (&1 + e) * M / LN` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s (\p1. K * inv(&p1) *
     sum ((t:num->num->bool) p1)
         (\p2. inv(&1 - log(&p1) / LN - log(&p2) / LN) / &p2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p1:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `prime p1 /\ z < &p1 /\ &p1 <= y` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(p1:num) IN s` THEN EXPAND_TAC "s" THEN
      REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    USE_THEN "p1rng" (MP_TAC o SPEC `p1:num`) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
    USE_THEN "tfin" (fun th -> REWRITE_TAC[th]) THEN
    X_GEN_TAC `p2:num` THEN EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    USE_THEN "bexp" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < &p2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `log(&p2) <= (log M - log(&p1)) / &2` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN ASM_SIMP_TAC[EXP_LOG];
      ALL_TAC] THEN
    SUBGOAL_THEN `&p2 <= M / (&p1 * &p2)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL] THEN
      SUBGOAL_THEN `&0 < &p2 * &p1 * &p2` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
      SUBGOAL_THEN `log(&p2 * &p1 * &p2) <= log M` MP_TAC THENL
       [ASM_SIMP_TAC[LOG_MUL; REAL_LT_MUL] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[LOG_MONO_LE]];
      ALL_TAC] THEN
    EXPAND_TAC "u" THEN REWRITE_TAC[] THEN
    ABBREV_TAC `W = M / (&p1 * &p2)` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `W:real` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `X0:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `!a b c:real. b <= c ==> a <= b ==> a <= c`) THEN
    SUBGOAL_THEN
     `&0 < LN * (&1 - log(&p1) / LN - log(&p2) / LN) /\
      LN * (&1 - log(&p1) / LN - log(&p2) / LN) <= log W`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `LN * (&1 - log(&p1) / LN - log(&p2) / LN) =
                    LN - log(&p1) - log(&p2)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < LN` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      EXPAND_TAC "W" THEN
      ASM_SIMP_TAC[LOG_DIV; LOG_MUL; REAL_LT_MUL] THEN
      SUBGOAL_THEN `log(&p1) <= LN / &3` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log y` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
          EXPAND_TAC "y" THEN REWRITE_TAC[LOG_EXP] THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < W` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + e) * W / (LN * (&1 - log(&p1) / LN - log(&p2) / LN))`
    THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ABBREV_TAC `D = LN * (&1 - log(&p1) / LN - log(&p2) / LN)` THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MAP_EVERY EXPAND_TAC ["K"; "W"] THEN
      MAP_EVERY UNDISCH_TAC
       [`&0 < LN * (&1 - log(&p1) / LN - log(&p2) / LN)`;
        `&0 < &p1`; `&0 < &p2`; `&0 < LN`] THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s (\p1. K * inv(&p1) *
     ((((&1 - &3 * log(&p1) / LN) - (&1 - &3 * log(&p1) / LN) pow 2 / &2 +
        (&1 - &3 * log(&p1) / LN) pow 3 / &3) / (&1 - log(&p1) / LN)) +
      &6 * d + &1200 / LN))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p1:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `prime p1 /\ z < &p1 /\ &p1 <= y` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(p1:num) IN s` THEN EXPAND_TAC "s" THEN
      REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    USE_THEN "p1rng" (MP_TAC o SPEC `p1:num`) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`&N`; `log(&p1) / LN`; `d:real`] CHEN_P2_SUM) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum s (\p1. K * inv(&p1) *
     ((((&1 - &3 * log(&p1) / LN) - (&1 - &3 * log(&p1) / LN) pow 2 / &2 +
        (&1 - &3 * log(&p1) / LN) pow 3 / &3) / (&1 - log(&p1) / LN)) +
      &6 * d + &1200 / LN)) =
    K * (sum s (\p1. ((&1 - &3 * log(&p1) / LN) -
                      (&1 - &3 * log(&p1) / LN) pow 2 / &2 +
                      (&1 - &3 * log(&p1) / LN) pow 3 / &3) /
                     (&1 - log(&p1) / LN) / &p1) +
         (&6 * d + &1200 / LN) * sum s (\p1. inv(&p1)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[real_div] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `&N` CHEN_P1_SUM) THEN MP_TAC(SPEC `&N` CHEN_P1_RECIP_SUM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= sum s (\p1. inv(&p1))` MP_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
    ALL_TAC] THEN
  ABBREV_TAC `S1 = sum s (\p1. ((&1 - &3 * log(&p1) / LN) -
                      (&1 - &3 * log(&p1) / LN) pow 2 / &2 +
                      (&1 - &3 * log(&p1) / LN) pow 3 / &3) /
                     (&1 - log(&p1) / LN) / &p1)` THEN
  ABBREV_TAC `S2 = sum s (\p1. inv(&p1))` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(&1 + e) * M / LN * (chen_cB + &4000 / LN) =
                K * (chen_cB + &4000 / LN)` SUBST1_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[REAL_MUL_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&400 / LN <= &1 /\ &0 <= &1 / LN /\ d <= &1 / LN`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_DIV; REAL_POS;
                 REAL_LT_IMP_LE] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&6 * d + &1200 / LN) * S2 <= (&1206 / LN) * &3`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      UNDISCH_TAC `d <= &1 / LN` THEN REWRITE_TAC[real_div] THEN
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `&0 <= &1 / LN` THEN
  REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The intervals l_k = N^(1/8) exp(k / log N) and the sets T_k.              *)
(* ------------------------------------------------------------------------- *)

let chen_l = new_definition
 `chen_l N k = exp(log(&N) / &8 + &k / log(&N))`;;

let chen_Tk = new_definition
 `chen_Tk h N k =
    {p1,p2,p3 | prime p1 /\ prime p2 /\ prime p3 /\
                chen_l N k < &p1 /\ &p1 <= chen_l N (k + 1) /\
                &p1 < exp(&1 / &3 * log(&N)) /\
                exp(&1 / &3 * log(&N)) <= &p2 /\ p2 <= p3 /\
                chen_l N k * &(p2 * p3) < &N /\
                coprime(p1 * p2 * p3,h)}`;;

let CHEN_L_0 = prove
 (`!N. chen_l N 0 = exp(&1 / &8 * log(&N))`,
  REWRITE_TAC[chen_l; real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_SYM]);;

let CHEN_L_SUC = prove
 (`!N k. chen_l N (k + 1) = exp(inv(log(&N))) * chen_l N k`,
  REWRITE_TAC[chen_l; GSYM REAL_EXP_ADD; GSYM REAL_OF_NUM_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN
  REAL_ARITH_TAC);;

let CHEN_L_MONO = prove
 (`!N j k. 1 < N /\ j <= k ==> chen_l N j <= chen_l N k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chen_l; REAL_EXP_MONO_LE] THEN
  REWRITE_TAC[REAL_LE_LADD] THEN
  SUBGOAL_THEN `&0 < log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT];
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LE]]);;

let CHEN_L_POS = prove
 (`!N k. &0 < chen_l N k`,
  REWRITE_TAC[chen_l; REAL_EXP_POS_LT]);;

let FINITE_CHEN_K = prove
 (`!N. 1 < N
       ==> FINITE {k | chen_l N k < exp(&1 / &3 * log(&N))} /\
           &(CARD {k | chen_l N k < exp(&1 / &3 * log(&N))})
           <= &5 / &24 * log(&N) pow 2 + &1`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{k | chen_l N k < exp(&1 / &3 * log(&N))} SUBSET
    {k:num | &k < &5 / &24 * log(&N) pow 2}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; chen_l; REAL_EXP_MONO_LT] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&k / log(&N) < &5 / &24 * log(&N)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{k:num | &k < &5 / &24 * log(&N) pow 2}` THEN
    ASM_REWRITE_TAC[FINITE_NUM_LT_REAL];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(CARD {k:num | &k < &5 / &24 * log(&N) pow 2})` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_REWRITE_TAC[FINITE_NUM_LT_REAL];
      MATCH_MP_TAC CARD_NUM_LT_REAL THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      REAL_ARITH_TAC]]);;

let CHEN_TK_DISJOINT = prove
 (`!h N j k. 1 < N /\ ~(j = k) ==> chen_Tk h N j INTER chen_Tk h N k = {}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p1:num`; `p2:num`; `p3:num`] THEN
  REWRITE_TAC[chen_Tk; IN_ELIM_TRIPLE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `j + 1 <= k \/ k + 1 <= j` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    MP_TAC(SPECL [`N:num`; `j + 1`; `k:num`] CHEN_L_MONO) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`N:num`; `k + 1`; `j:num`] CHEN_L_MONO) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let CHEN_T_COVER = prove
 (`!h N p1 p2 p3.
        EVEN h /\ 1 <= h /\ h <= N /\ EVEN N /\ 256 < N /\
        (p1,p2,p3) IN chen_T h N
        ==> ?k. chen_l N k < exp(&1 / &3 * log(&N)) /\
                (p1,p2,p3) IN chen_Tk h N k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[chen_T; chen_Tk; IN_ELIM_TRIPLE] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `1 < N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&p1 = exp(&1 / &8 * log(&N)))` ASSUME_TAC THENL
   [MATCH_MP_TAC ROOT_NOT_PRIME THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. chen_l N m < &p1 /\ !k. chen_l N k < &p1 ==> k <= m`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM num_MAX] THEN CONJ_TAC THENL
     [EXISTS_TAC `0` THEN REWRITE_TAC[CHEN_L_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `N:num` FINITE_CHEN_K) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o MATCH_MP UPPER_BOUND_FINITE_SET) THEN
    DISCH_THEN(X_CHOOSE_TAC `M:num` o SPEC `\k:num. k`) THEN
    EXISTS_TAC `M:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `m:num` THEN
  SUBGOAL_THEN `&p1 <= chen_l N (m + 1)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m + 1`) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `0 < p2 * p3` ASSUME_TAC THENL
   [REWRITE_TAC[LT_NZ; MULT_EQ_0] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&p1 * &(p2 * p3)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT];
    ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT]]);;

let CHEN_TK_SUB_THAT = prove
 (`!h N k. 1 < N
         ==> chen_Tk h N k SUBSET
             {p1,p2,p3 | prime p1 /\ prime p2 /\ prime p3 /\
                         exp(&1 / &8 * log(&N)) <= &p1 /\
                         &p1 < exp(&1 / &3 * log(&N)) /\
                         exp(&1 / &3 * log(&N)) <= &p2 /\
                         p2 <= p3 /\
                         &(p1 * p2 * p3) < exp(inv(log(&N))) * &N}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; chen_Tk; IN_ELIM_TRIPLE] THEN
  MAP_EVERY X_GEN_TAC [`p1:num`; `p2:num`; `p3:num`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`N:num`; `0`; `k:num`] CHEN_L_MONO) THEN
    ASM_REWRITE_TAC[LE_0; CHEN_L_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `chen_l N (k + 1) * &p2 * &p3` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
    REWRITE_TAC[CHEN_L_SUC; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_MUL]]);;

let FINITE_CHEN_TK = prove
 (`!h N k. 1 < N ==> FINITE(chen_Tk h N k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{p1,p2,p3 | prime p1 /\ prime p2 /\ prime p3 /\
                exp(&1 / &8 * log(&N)) <= &p1 /\
                &p1 < exp(&1 / &3 * log(&N)) /\
                exp(&1 / &3 * log(&N)) <= &p2 /\ p2 <= p3 /\
                &(p1 * p2 * p3) < exp(inv(log(&N))) * &N}` THEN
  ASM_SIMP_TAC[CHEN_TK_SUB_THAT] THEN
  MP_TAC(ISPECL
   [`\p1 p2 p3. exp(&1 / &8 * log(&N)) <= &p1 /\
                &p1 < exp(&1 / &3 * log(&N)) /\
                exp(&1 / &3 * log(&N)) <= &p2 /\ p2 <= p3`;
    `exp(inv(log(&N))) * &N`] FINITE_PRIME_TRIPLES_LT) THEN
  REWRITE_TAC[CONJ_ASSOC]);;

let CHEN_TK_CARD_SUM = prove
 (`!h N. 1 < N
       ==> sum {k | chen_l N k < exp(&1 / &3 * log(&N))}
               (\k. &(CARD(chen_Tk h N k))) <=
           &(CARD {p1,p2,p3 | prime p1 /\ prime p2 /\ prime p3 /\
                              exp(&1 / &8 * log(&N)) <= &p1 /\
                              &p1 < exp(&1 / &3 * log(&N)) /\
                              exp(&1 / &3 * log(&N)) <= &p2 /\
                              p2 <= p3 /\
                              &(p1 * p2 * p3) < exp(inv(log(&N))) * &N})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `N:num` FINITE_CHEN_K) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ABBREV_TAC `KK = {k | chen_l N k < exp(&1 / &3 * log(&N))}` THEN
  ABBREV_TAC
   `TH = {p1,p2,p3 | prime p1 /\ prime p2 /\ prime p3 /\
                     exp(&1 / &8 * log(&N)) <= &p1 /\
                     &p1 < exp(&1 / &3 * log(&N)) /\
                     exp(&1 / &3 * log(&N)) <= &p2 /\
                     p2 <= p3 /\
                     &(p1 * p2 * p3) < exp(inv(log(&N))) * &N}` THEN
  SUBGOAL_THEN `FINITE(TH:num#num#num->bool) /\
                !k. chen_Tk h N k SUBSET TH` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "TH" THEN SIMP_TAC[CHEN_TK_SUB_THAT; ASSUME `1 < N`] THEN
    MP_TAC(ISPECL
     [`\p1 p2 p3. exp(&1 / &8 * log(&N)) <= &p1 /\
                  &p1 < exp(&1 / &3 * log(&N)) /\
                  exp(&1 / &3 * log(&N)) <= &p2 /\ p2 <= p3`;
      `exp(inv(log(&N))) * &N`] FINITE_PRIME_TRIPLES_LT) THEN
    REWRITE_TAC[CONJ_ASSOC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUM; REAL_OF_NUM_LE] THEN
  MP_TAC(ISPECL [`chen_Tk h N`; `KK:num->bool`] CARD_UNIONS_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET];
      ASM_MESON_TAC[CHEN_TK_DISJOINT]];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[]);;

let CHEN_SB_SPLIT = prove
 (`!h N. EVEN h /\ 1 <= h /\ h <= N /\ EVEN N /\ 256 < N
       ==> &(CARD {p1,p2,p3 | (p1,p2,p3) IN chen_T h N /\
                              !q. prime q /\ &q < exp(&1 / &3 * log(&N))
                                  ==> ~(q divides chen_dist h (p1 * p2 * p3))})
           <= sum {k | chen_l N k < exp(&1 / &3 * log(&N))}
                  (\k. &(CARD {x | x IN chen_Tk h N k /\
                                   !q. prime q /\
                                       &q < exp(&1 / &3 * log(&N))
                                       ==> ~(q divides
                                             chen_dist h
                                              (FST x * FST(SND x) *
                                               SND(SND x)))}))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 < N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `N:num` FINITE_CHEN_K) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ABBREV_TAC `KK = {k | chen_l N k < exp(&1 / &3 * log(&N))}` THEN
  ABBREV_TAC `y = exp(&1 / &3 * log(&N))` THEN
  ABBREV_TAC
   `g = \k. {x | x IN chen_Tk h N k /\
                 !q. prime q /\ &q < y
                     ==> ~(q divides chen_dist h
                                     (FST x * FST(SND x) * SND(SND x)))}` THEN
  SUBGOAL_THEN `!k. FINITE((g:num->num#num#num->bool) k) /\
                    g k SUBSET chen_Tk h N k`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    SIMP_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `chen_Tk h N k` THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       `{p1,p2,p3 | prime p1 /\ prime p2 /\ prime p3 /\
                    exp(&1 / &8 * log(&N)) <= &p1 /\
                    &p1 < y /\ y <= &p2 /\ p2 <= p3 /\
                    &(p1 * p2 * p3) < exp(inv(log(&N))) * &N}` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL
         [`\p1 p2 p3. exp(&1 / &8 * log(&N)) <= &p1 /\ &p1 < y /\
                      y <= &p2 /\ p2 <= p3`;
          `exp(inv(log(&N))) * &N`] FINITE_PRIME_TRIPLES_LT) THEN
        REWRITE_TAC[CONJ_ASSOC];
        EXPAND_TAC "y" THEN ASM_SIMP_TAC[CHEN_TK_SUB_THAT]];
      SIMP_TAC[SUBSET; IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum KK (\k. &(CARD {x | x IN chen_Tk h N k /\
                            !q. prime q /\ &q < y
                                ==> ~(q divides chen_dist h
                                        (FST x * FST(SND x) * SND(SND x)))}))
    = &(CARD(UNIONS(IMAGE (g:num->num#num#num->bool) KK)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUM; REAL_OF_NUM_EQ] THEN
    MP_TAC(ISPECL [`g:num->num#num#num->bool`; `KK:num->bool`]
                  CARD_UNIONS_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`h:num`; `N:num`; `t:num`; `u:num`] CHEN_TK_DISJOINT) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE]] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_TRIPLE; IN_UNIONS;
              EXISTS_IN_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`p1:num`; `p2:num`; `p3:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:num`; `N:num`; `p1:num`; `p2:num`;
   `p3:num`] CHEN_T_COVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC)
  THEN EXISTS_TAC `k:num` THEN CONJ_TAC THENL
   [EXPAND_TAC "KK" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  EXPAND_TAC "g" THEN REWRITE_TAC[IN_ELIM_THM; FST; SND] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Pairs (p2 p3, p1) and the bilinear form hypothesis.                       *)
(* ------------------------------------------------------------------------- *)

let chen_alpha = new_definition
 `chen_alpha h N k m =
    if (?p2 p3. prime p2 /\ prime p3 /\ exp(&1 / &3 * log(&N)) <= &p2 /\
                p2 <= p3 /\ m = p2 * p3) /\
       chen_l N k * &m < &N /\ coprime(m,h)
    then &1 else &0`;;

let FINITE_BILINEAR_BOX = prove
 (`!X Y Z P. FINITE {x:num#num | 1 <= FST x /\ &(FST x) <= X /\
                                prime(SND x) /\ Z < &(SND x) /\
                                &(SND x) <= Y /\ P x}`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `X:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  MP_TAC(SPEC `Y:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `(0..m) CROSS (0..n)` THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_THM; IN_CROSS; IN_NUMSEG;
              LE_0; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC);;

let CHEN_ALPHA_BOUNDS = prove
 (`!h N k m. &0 <= chen_alpha h N k m /\ chen_alpha h N k m <= &1 /\
           abs(chen_alpha h N k m) <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[chen_alpha] THEN COND_CASES_TAC THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let CHEN_TK_PAIRS = prove
 (`!h N k Q.
        EVEN h /\ 1 <= h /\ h <= N /\ EVEN N /\ 256 < N
        ==> &(CARD {x | x IN chen_Tk h N k /\
                        Q(FST x * FST(SND x) * SND(SND x))}) =
            sum {x:num#num | 1 <= FST x /\ &(FST x) <= &N / chen_l N k /\
                             prime(SND x) /\ chen_l N k < &(SND x) /\
                             &(SND x) <= min (chen_l N (k + 1))
                                             (exp(&1 / &3 * log(&N))) /\
                             ~(SND x divides h) /\ Q(FST x * SND x)}
                (\x. chen_alpha h N k (FST x))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `y = exp(&1 / &3 * log(&N))` THEN
  SUBGOAL_THEN `!p. prime p ==> ~(&p = y)` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`N:num`; `3`; `p:num`] ROOT_NOT_PRIME) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < chen_l N k` ASSUME_TAC THENL
   [REWRITE_TAC[CHEN_L_POS]; ALL_TAC] THEN
  ABBREV_TAC
   `S' = {x:num#num | 1 <= FST x /\ &(FST x) <= &N / chen_l N k /\
                      prime(SND x) /\ chen_l N k < &(SND x) /\
                      &(SND x) <= min (chen_l N (k + 1)) y /\
                      ~(SND x divides h) /\ Q(FST x * SND x)}` THEN
  SUBGOAL_THEN `FINITE(S':num#num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S'" THEN
    MP_TAC(ISPECL [`&N / chen_l N k`; `min (chen_l N (k + 1)) y`;
                   `chen_l N k`;
                   `\x:num#num. ~(SND x divides h) /\ Q(FST x * SND x)`]
           FINITE_BILINEAR_BOX) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[chen_alpha] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[GSYM CARD_EQ_SUM; FINITE_RESTRICT; REAL_OF_NUM_EQ] THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `CARD(IMAGE (\x:num#num#num. (FST(SND x) * SND(SND x),FST x))
               {x | x IN chen_Tk h N k /\
                    Q(FST x * FST(SND x) * SND(SND x))})` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_IMAGE; EXISTS_PAIR_THM;
                IN_ELIM_THM; PAIR_EQ; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `p:num`] THEN EXPAND_TAC "S'" THEN
    REWRITE_TAC[IN_ELIM_THM; FST; SND; chen_Tk; IN_ELIM_TRIPLE] THEN
    ASM_REWRITE_TAC[] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `q2:num` (X_CHOOSE_THEN `q3:num` STRIP_ASSUME_TAC))
       STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
      MAP_EVERY EXISTS_TAC [`p:num`; `q2:num`; `q3:num`] THEN
      UNDISCH_TAC `&p <= min (chen_l N (k + 1)) y` THEN
      REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&p < y` ASSUME_TAC THENL
       [SUBGOAL_THEN `~(&p = y)` MP_TAC THENL
         [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `coprime(p * q2 * q3,h)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[COPRIME_LMUL] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ];
        ALL_TAC] THEN
      SUBGOAL_THEN `Q(p * q2 * (q3:num)):bool` ASSUME_TAC THENL
       [UNDISCH_TAC `Q((q2 * q3) * (p:num)):bool` THEN REWRITE_TAC[MULT_AC];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `p1:num` (X_CHOOSE_THEN `p2:num`
        (X_CHOOSE_THEN `p3:num` STRIP_ASSUME_TAC))) THEN
      REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)))
      THEN
      SUBGOAL_THEN `coprime(p1,h) /\ coprime(p2 * p3,h)` STRIP_ASSUME_TAC
      THENL [ASM_MESON_TAC[COPRIME_LMUL]; ALL_TAC] THEN
      SUBGOAL_THEN `1 <= p2 * p3` ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
        ASM_MESON_TAC[PRIME_IMP_NZ];
        ALL_TAC] THEN
      SUBGOAL_THEN `&(p2 * p3) <= &N / chen_l N k` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&p1 <= min (chen_l N (k + 1)) y` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_LE_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(p1 divides h)` ASSUME_TAC THENL
       [ASM_MESON_TAC[PRIME_COPRIME_EQ]; ALL_TAC] THEN
      SUBGOAL_THEN `Q((p2 * p3) * (p1:num)):bool` ASSUME_TAC THENL
       [UNDISCH_TAC `Q(p1 * p2 * (p3:num)):bool` THEN REWRITE_TAC[MULT_AC];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`p2:num`; `p3:num`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; FST; SND; PAIR_EQ;
                chen_Tk; IN_ELIM_TRIPLE] THEN
    MAP_EVERY X_GEN_TAC
     [`p1:num`; `p2:num`; `p3:num`; `q1:num`; `q2:num`; `q3:num`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PRIME_PAIR_UNIQUE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FINITE_RESTRICT THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `{p1,p2,p3 | prime p1 /\ prime p2 /\ prime p3 /\
                  exp(&1 / &8 * log(&N)) <= &p1 /\
                  &p1 < y /\ y <= &p2 /\ p2 <= p3 /\
                  &(p1 * p2 * p3) < exp(inv(log(&N))) * &N}` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`\p1 p2 p3. exp(&1 / &8 * log(&N)) <= &p1 /\ &p1 < y /\
                    y <= &p2 /\ p2 <= p3`;
        `exp(inv(log(&N))) * &N`] FINITE_PRIME_TRIPLES_LT) THEN
      REWRITE_TAC[CONJ_ASSOC];
      EXPAND_TAC "y" THEN MATCH_MP_TAC CHEN_TK_SUB_THAT THEN ASM_ARITH_TAC]]);;

let chen_bsum = new_definition
 `chen_bsum h N k (P:num#num->bool) =
    sum {x:num#num | 1 <= FST x /\ &(FST x) <= &N / chen_l N k /\
                     prime(SND x) /\ chen_l N k < &(SND x) /\
                     &(SND x) <= min (chen_l N (k + 1))
                                     (exp(&1 / &3 * log(&N))) /\
                     P x}
        (\x. chen_alpha h N k (FST x))`;;

let chen_bvE = new_definition
 `chen_bvE h N k d =
    abs(chen_bsum h N k
          (\x. (FST x * SND x == (if coprime(h,d) then h else 1)) (mod d)) -
        inv(&(phi d)) * chen_bsum h N k (\x. coprime(FST x * SND x,d)))`;;

(* ------------------------------------------------------------------------- *)
(* Remainders.                                                               *)
(* ------------------------------------------------------------------------- *)

let REMAINDER_SPLIT_BOUND = prove
 (`!X Y Z (alpha:num->real) N d g.
        (!m. &0 <= alpha m) /\ &0 <= g
        ==> abs(sum {x:num#num | 1 <= FST x /\ &(FST x) <= X /\
                                 prime(SND x) /\ Z < &(SND x) /\
                                 &(SND x) <= Y /\ ~(SND x divides N) /\
                                 (FST x * SND x == N) (mod d)}
                    (\x. alpha(FST x)) -
                g * sum {x:num#num | 1 <= FST x /\ &(FST x) <= X /\
                                     prime(SND x) /\ Z < &(SND x) /\
                                     &(SND x) <= Y /\ ~(SND x divides N)}
                        (\x. alpha(FST x)))
            <= abs(sum {x:num#num | 1 <= FST x /\ &(FST x) <= X /\
                                    prime(SND x) /\ Z < &(SND x) /\
                                    &(SND x) <= Y /\
                                    (FST x * SND x == N) (mod d)}
                       (\x. alpha(FST x)) -
                   g * sum {x:num#num | 1 <= FST x /\ &(FST x) <= X /\
                                        prime(SND x) /\ Z < &(SND x) /\
                                        &(SND x) <= Y /\
                                        coprime(FST x * SND x,d)}
                           (\x. alpha(FST x))) +
               sum {x:num#num | 1 <= FST x /\ &(FST x) <= X /\
                                prime(SND x) /\ Z < &(SND x) /\
                                &(SND x) <= Y /\ SND x divides N /\
                                (FST x * SND x == N) (mod d)}
                   (\x. alpha(FST x)) +
               g * (sum {x:num#num | 1 <= FST x /\ &(FST x) <= X /\
                                     prime(SND x) /\ Z < &(SND x) /\
                                     &(SND x) <= Y /\
                                     ~coprime(FST x * SND x,d)}
                        (\x. alpha(FST x)) +
                    sum {x:num#num | 1 <= FST x /\ &(FST x) <= X /\
                                     prime(SND x) /\ Z < &(SND x) /\
                                     &(SND x) <= Y /\ SND x divides N}
                        (\x. alpha(FST x)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `B = {x:num#num | 1 <= FST x /\ &(FST x) <= X /\
                               prime(SND x) /\ Z < &(SND x) /\
                               &(SND x) <= Y}` THEN
  SUBGOAL_THEN `FINITE(B:num#num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    MP_TAC(ISPECL [`X:real`; `Y:real`; `Z:real`; `\x:num#num. T`]
           FINITE_BILINEAR_BOX) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. {x:num#num | 1 <= FST x /\ &(FST x) <= X /\ prime(SND x) /\
                     Z < &(SND x) /\ &(SND x) <= Y /\ P x} =
        {x | x IN B /\ P x}`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "B" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    REWRITE_TAC[CONJ_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_RESTRICT_SET] THEN
  SUBGOAL_THEN
   `!P. &0 <= sum B (\x:num#num. if P x then alpha(FST x) else &0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b e f u v w:real. &0 <= u /\ &0 <= g * v /\ &0 <= g * w /\
      a - g * b = (e - g * f) - u - g * v + g * w
      ==> abs(a - g * b) <= abs(e - g * f) + u + g * (v + w)`) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_SUB; GSYM SUM_ADD] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:num#num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    ASM_CASES_TAC `SND(x:num#num) divides N` THEN
    ASM_CASES_TAC `(FST(x:num#num) * SND x == N) (mod d)` THEN
    ASM_CASES_TAC `coprime(FST(x:num#num) * SND x,d)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let BOX_SUM_LE = prove
 (`!(alpha:num->real) X (P0:num->bool) S.
        &0 <= X /\ FINITE P0 /\ FINITE S /\
        (!m. &0 <= alpha m /\ alpha m <= &1) /\
        (!x. x IN S ==> 1 <= FST x /\ &(FST x) <= X) /\
        (!x. x IN S /\ ~(alpha(FST x) = &0) ==> SND x IN P0)
        ==> sum S (\x. alpha(FST x)) <= &(CARD P0) * X`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sum S (\x:num#num. alpha(FST x)) =
                sum {x | x IN S /\ SND x IN P0} (\x. alpha(FST x))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
     [SIMP_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `x:num#num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `alpha(FST(x:num#num)) = &0` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(x IN S /\ SND(x:num#num) IN P0)` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {x:num#num | x IN S /\ SND x IN P0})` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_SUM; FINITE_RESTRICT] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_RESTRICT];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum P0 (\p:num. &(CARD {m | 1 <= m /\ &m <= X}))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_PAIRS_LE_SND THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{m | 1 <= m /\ &m < X + &1}` THEN
      REWRITE_TAC[FINITE_NUM_RANGE; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[REAL_ARITH `x <= X ==> x < X + &1`];
      MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(a:num,b:num)` o check (fun th ->
        can (find_term ((=) `FST:num#num->num`)) (concl th) &&
        not(can (find_term ((=) `alpha:num->real`)) (concl th)))) THEN
      ASM_REWRITE_TAC[FST]];
    ASM_SIMP_TAC[SUM_CONST] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_POS; CARD_NUM_LE_REAL]]);;

let BOX_SUM_CONG_LE = prove
 (`!(alpha:num->real) X (P0:num->bool) S c d.
        &0 <= X /\ FINITE P0 /\ FINITE S /\ ~(d = 0) /\
        (!m. &0 <= alpha m /\ alpha m <= &1) /\
        (!p. p IN P0 ==> coprime(p,d)) /\
        (!x. x IN S ==> 1 <= FST x /\ &(FST x) <= X /\ SND x IN P0 /\
                        (FST x * SND x == c) (mod d))
        ==> sum S (\x. alpha(FST x)) <= &(CARD P0) * (X / &d + &1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(S:num#num->bool))` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_SUM] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum P0 (\p. &(CARD {m | 1 <= m /\ &m <= X /\
                                     (m * p == c) (mod d)}))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_PAIRS_LE_SND THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{m | 1 <= m /\ &m < X + &1}` THEN
      REWRITE_TAC[FINITE_NUM_RANGE; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[REAL_ARITH `x <= X ==> x < X + &1`];
      MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(a:num,b:num)`) THEN
      ASM_REWRITE_TAC[FST; SND] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum P0 (\p:num. X / &d + &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CARD_CONG_MULT_LE THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[SUM_CONST; REAL_LE_REFL]]);;

let CHEN_TK_REMAINDER_TERM = prove
 (`!h N k t.
        EVEN h /\ 1 <= h /\ h <= N /\ EVEN N /\ 256 < N /\ FINITE t /\
        (!q. q IN t ==> prime q /\ ~(q divides h))
        ==> abs(&(CARD {x | x IN chen_Tk h N k /\
                            !p. p IN t
                                ==> p divides
                                    chen_dist h (FST x * FST(SND x) *
                                                 SND(SND x))}) -
                &(CARD(chen_Tk h N k)) * product t (chen_g h))
            <= abs(chen_bsum h N k
                     (\x. (FST x * SND x == h) (mod (nproduct t (\p. p)))) -
                   inv(&(phi(nproduct t (\p. p)))) *
                   chen_bsum h N k
                     (\x. coprime(FST x * SND x,nproduct t (\p. p)))) +
               chen_bsum h N k
                 (\x. SND x divides h /\
                      (FST x * SND x == h) (mod (nproduct t (\p. p)))) +
               inv(&(phi(nproduct t (\p. p)))) *
               (chen_bsum h N k
                  (\x. ~coprime(FST x * SND x,nproduct t (\p. p))) +
                chen_bsum h N k (\x. SND x divides h))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(!q. q IN t ==> prime q) /\ (!q. q IN t ==> ~(q divides h))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `product t (chen_g h) = inv(&(phi(nproduct t (\p. p))))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_PRODUCT_INV_PRED] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[chen_g];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN chen_Tk h N k /\
         !p. p IN t
             ==> p divides chen_dist h (FST x * FST(SND x) * SND(SND x))} =
    {x | x IN chen_Tk h N k /\
         (\n. (n == h) (mod (nproduct t (\p. p))))
         (FST x * FST(SND x) * SND(SND x))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:num#num#num` THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[PRIMES_DIVIDE_IFF_NPRODUCT; chen_dist; DIVIDES_DIST_CONG];
    ALL_TAC] THEN
  MP_TAC(SPECL [`h:num`; `N:num`; `k:num`;
                `\n. (n == h) (mod (nproduct t (\p. p)))`] CHEN_TK_PAIRS) THEN
  MP_TAC(SPECL [`h:num`; `N:num`; `k:num`; `\n:num. T`] CHEN_TK_PAIRS) THEN
  ASM_REWRITE_TAC[SET_RULE `{x | x IN s} = (s:num#num#num->bool)`] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[chen_bsum] THEN MATCH_MP_TAC REMAINDER_SPLIT_BOUND THEN
  REWRITE_TAC[CHEN_ALPHA_BOUNDS; REAL_LE_INV_EQ; REAL_POS]);;

let CHEN_LARGE_DIVISORS_N = prove
 (`!h N. EVEN h /\ 1 <= h /\ h <= N /\ EVEN N /\ 256 < N
       ==> FINITE {p | prime p /\ exp(&1 / &8 * log(&N)) <= &p /\
                       p divides h} /\
           CARD {p | prime p /\ exp(&1 / &8 * log(&N)) <= &p /\
                     p divides h} <= 8`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p | prime p /\ p divides h}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_PRIME_DIVISORS THEN ASM_ARITH_TAC;
      SIMP_TAC[SUBSET; IN_ELIM_THM]];
    MATCH_MP_TAC CARD_LARGE_PRIME_DIVISORS THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < log(&N)` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `&1 / &8 * log(&N)` REAL_EXP_LE_X) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&N` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_EXP_N] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `&N = exp(log(&N))` (fun th ->
      GEN_REWRITE_TAC LAND_CONV [th]) THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXP_LOG THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC]);;

let CHEN_Z_LE_L = prove
 (`!N k. 1 < N ==> exp(&1 / &8 * log(&N)) <= chen_l N k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CHEN_L_0] THEN
  MATCH_MP_TAC CHEN_L_MONO THEN ASM_REWRITE_TAC[LE_0]);;

let CHEN_BSUM_PN = prove
 (`!h N k. EVEN h /\ 1 <= h /\ h <= N /\ EVEN N /\ 256 < N
         ==> chen_bsum h N k (\x. SND x divides h) <= &8 * (&N / chen_l N k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`h:num`; `N:num`] CHEN_LARGE_DIVISORS_N) THEN
    ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `k:num`] CHEN_Z_LE_L) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= &N / chen_l N k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[CHEN_L_POS];
    ALL_TAC] THEN
  REWRITE_TAC[chen_bsum] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {p | prime p /\ exp(&1 / &8 * log(&N)) <= &p /\
                          p divides h}) * (&N / chen_l N k)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC BOX_SUM_LE THEN ASM_REWRITE_TAC[CHEN_ALPHA_BOUNDS] THEN
    REWRITE_TAC[FINITE_BILINEAR_BOX; IN_ELIM_THM] THEN
    SIMP_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]]);;

let CHEN_BSUM_NONCOPRIME = prove
 (`!h N k t.
        EVEN N /\ 256 < N /\ FINITE t /\
        (!q. q IN t ==> prime q /\ &q < exp(&1 / &3 * log(&N))) /\
        &(nproduct t (\p. p)) < exp(&1 / &2 * log(&N))
        ==> chen_bsum h N k (\x. ~coprime(FST x * SND x,nproduct t (\p. p)))
            <= &3 * (&N / chen_l N k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!q. q IN t ==> prime q` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `d = nproduct t (\p:num. p)` THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[GSYM LT_NZ] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q. prime q ==> (q divides d <=> q IN t)` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC PRIME_DIVIDES_NPRODUCT_PRIMES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `z = exp(&1 / &8 * log(&N))` THEN
  SUBGOAL_THEN `FINITE {p | prime p /\ z <= &p /\ p divides d} /\
                CARD {p | prime p /\ z <= &p /\ p divides d} <= 3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{p | prime p /\ p divides d}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_PRIME_DIVISORS THEN ASM_REWRITE_TAC[];
        SIMP_TAC[SUBSET; IN_ELIM_THM]];
      MATCH_MP_TAC CARD_LARGE_PRIME_DIVISORS THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < log(&N)` ASSUME_TAC THENL
       [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      EXPAND_TAC "z" THEN CONJ_TAC THENL
       [MP_TAC(SPEC `&1 / &8 * log(&N)` REAL_EXP_LE_X) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_EXP_N] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `exp(&1 / &2 * log(&N))` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `k:num`] CHEN_Z_LE_L) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= &N / chen_l N k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[CHEN_L_POS];
    ALL_TAC] THEN
  REWRITE_TAC[chen_bsum] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {p | prime p /\ z <= &p /\ p divides d}) *
              (&N / chen_l N k)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]] THEN
  MATCH_MP_TAC BOX_SUM_LE THEN ASM_REWRITE_TAC[CHEN_ALPHA_BOUNDS] THEN
  REWRITE_TAC[FINITE_BILINEAR_BOX; IN_ELIM_THM] THEN
  SIMP_TAC[] THEN X_GEN_TAC `x:num#num` THEN
  REWRITE_TAC[chen_alpha] THEN COND_CASES_TAC THENL
   [ALL_TAC; REWRITE_TAC[]] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:num` (X_CHOOSE_THEN `p3:num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `coprime(p2 * p3,d)` ASSUME_TAC THENL
   [REWRITE_TAC[COPRIME_LMUL] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ] THEN
    SUBGOAL_THEN `&p2 <= &p3` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `p2:num` o check (fun th ->
        can (find_term ((=) `exp(&1 / &3 * log(&N))`)) (concl th) &&
        is_forall(concl th)));
      FIRST_X_ASSUM(MP_TAC o SPEC `p3:num` o check (fun th ->
        can (find_term ((=) `exp(&1 / &3 * log(&N))`)) (concl th) &&
        is_forall(concl th)))] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~coprime(SND(x:num#num),d)` MP_TAC THENL
   [UNDISCH_TAC `~coprime(FST(x:num#num) * SND x,d)` THEN
    ASM_REWRITE_TAC[COPRIME_LMUL];
    ASM_SIMP_TAC[PRIME_COPRIME_EQ] THEN ASM_REAL_ARITH_TAC]);;

let CHEN_BSUM_CONG_PN = prove
 (`!h N k d. EVEN h /\ 1 <= h /\ h <= N /\ EVEN N /\ 256 < N /\ ~(d = 0) /\
   coprime(d,h)
           ==> chen_bsum h N k (\x. SND x divides h /\
                                  (FST x * SND x == h) (mod d))
               <= &8 * (&N / chen_l N k / &d + &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`h:num`; `N:num`] CHEN_LARGE_DIVISORS_N) THEN
    ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `k:num`] CHEN_Z_LE_L) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= &N / chen_l N k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[CHEN_L_POS];
    ALL_TAC] THEN
  REWRITE_TAC[chen_bsum] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {p | prime p /\ exp(&1 / &8 * log(&N)) <= &p /\
                          p divides h}) * (&N / chen_l N k / &d + &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC BOX_SUM_CONG_LE THEN EXISTS_TAC `h:num` THEN
    ASM_REWRITE_TAC[CHEN_ALPHA_BOUNDS; FINITE_BILINEAR_BOX] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC COPRIME_DIVISORS THEN
      MAP_EVERY EXISTS_TAC [`h:num`; `d:num`] THEN
      ASM_REWRITE_TAC[DIVIDES_REFL] THEN ASM_MESON_TAC[COPRIME_SYM];
      REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &1`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[REAL_POS]]);;

let CHEN_TK_REMAINDER_T = prove
 (`!h N k t Dl.
        EVEN h /\ 1 <= h /\ h <= N /\ EVEN N /\ 256 < N /\
        t SUBSET {p | prime p /\ &p < exp(&1 / &3 * log(&N))} /\
        &(nproduct t (\p. p)) < Dl /\ Dl <= exp(&1 / &2 * log(&N))
        ==> abs(&(CARD {x | x IN chen_Tk h N k /\
                            !p. p IN t
                                ==> p divides
                                    chen_dist h (FST x * FST(SND x) *
                                                 SND(SND x))}) -
                &(CARD(chen_Tk h N k)) * product t (chen_g h))
            <= (if !q. q IN t ==> ~(q divides h)
                then chen_bvE h N k (nproduct t (\p. p)) else &0) +
               &8 + &19 * (&N / chen_l N k) * product t (chen_g h)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `FINITE t /\ (!q. q IN t ==> prime q /\ &q < exp(&1 / &3 * log(&N)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{p | prime p /\ &p < exp(&1 / &3 * log(&N))}` THEN
      ASM_REWRITE_TAC[FINITE_PRIMES_LT];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q. q IN t ==> prime q` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &N / chen_l N k /\ &0 <= product t (chen_g h)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[CHEN_L_POS];
      MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `q:num` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`h:num`; `q:num`] CHEN_G_BOUNDS) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC o
      REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
    SUBGOAL_THEN `product t (chen_g h) = &0` SUBST1_TAC THENL
     [ASM_SIMP_TAC[PRODUCT_EQ_0] THEN EXISTS_TAC `q:num` THEN
      ASM_REWRITE_TAC[chen_g];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{x | x IN chen_Tk h N k /\
           !p. p IN t
               ==> p divides chen_dist h (FST x * FST(SND x) * SND(SND x))}
      = {}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; FORALL_PAIR_THM;
                  chen_Tk; IN_ELIM_TRIPLE; FST; SND] THEN
      MAP_EVERY X_GEN_TAC [`p1:num`; `p2:num`; `p3:num`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN
      ASM_REWRITE_TAC[chen_dist; DIVIDES_DIST_CONG] THEN DISCH_TAC THEN
      SUBGOAL_THEN `q divides p1 * p2 * p3` ASSUME_TAC THENL
       [UNDISCH_TAC `(p1 * p2 * p3 == (h:num)) (mod q)` THEN
        UNDISCH_TAC `q divides h` THEN NUMBER_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `coprime(q,q)` MP_TAC THENL
       [MATCH_MP_TAC COPRIME_DIVISORS THEN
        MAP_EVERY EXISTS_TAC [`p1 * p2 * (p3:num)`; `h:num`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[COPRIME_REFL] THEN ASM_MESON_TAC[PRIME_1]];
      ALL_TAC] THEN
    REWRITE_TAC[CARD_CLAUSES; REAL_MUL_RZERO; REAL_SUB_REFL;
                REAL_ABS_NUM] THEN
    REAL_ARITH_TAC] THEN
  MP_TAC(SPECL [`h:num`; `N:num`; `k:num`;
   `t:num->bool`] CHEN_TK_REMAINDER_TERM) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`h:num`; `N:num`; `k:num`;
   `t:num->bool`] CHEN_BSUM_NONCOPRIME) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`h:num`; `N:num`; `k:num`] CHEN_BSUM_PN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `coprime(nproduct t (\p. p),h)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COPRIME_NPRODUCT_EQ; PRIME_COPRIME_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `~(nproduct t (\p. p) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LT_NZ] THEN MATCH_MP_TAC NPRODUCT_POS_LT THEN
    ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  MP_TAC(SPECL [`h:num`; `N:num`; `k:num`; `nproduct t (\p. p)`]
               CHEN_BSUM_CONG_PN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[chen_bvE] THEN
  SUBGOAL_THEN `coprime(h,nproduct t (\p. p))` (fun th -> REWRITE_TAC[th])
  THENL [ASM_MESON_TAC[COPRIME_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&(phi(nproduct t (\p. p)))) = product t (chen_g h)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_PRODUCT_INV_PRED] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[chen_g];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&(nproduct t (\p. p))) <= product t (chen_g h)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT; GSYM PRODUCT_INV] THEN
    MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&2 <= &q` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_MESON_TAC[PRIME_GE_2];
      ALL_TAC] THEN
    ASM_SIMP_TAC[chen_g] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `g = product t (chen_g h)` THEN
  ABBREV_TAC `X = &N / chen_l N k` THEN
  ABBREV_TAC `d = nproduct t (\p:num. p)` THEN
  SUBGOAL_THEN `X / &d <= X * g` ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `V = chen_bsum h N k (\x. ~coprime(FST x * SND x,d))` THEN
  ABBREV_TAC `W = chen_bsum h N k (\x. SND x divides h)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `g * (V + W) <= &11 * (X * g)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `g * (&11 * X)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!L E U G Xd Xg:real. L <= E + U + G /\ U <= &8 * (Xd + &1) /\
                        Xd <= Xg /\ G <= &11 * Xg
                        ==> L <= E + &8 + &19 * Xg`) THEN
  MAP_EVERY EXISTS_TAC
   [`chen_bsum h N k (\x. SND x divides h /\ (FST x * SND x == h) (mod d))`;
    `(g:real) * (V + W)`; `(X:real) / &d`] THEN
  ASM_REWRITE_TAC[]);;

let CHEN_TK_REMAINDER_SUM = prove
 (`!h N k Dl.
        EVEN h /\ 1 <= h /\ h <= N /\ EVEN N /\ 256 < N /\ &1 <= Dl /\ Dl <=
          exp(&1 / &2 * log(&N))
        ==> sum {t | t SUBSET {p | prime p /\ &p < exp(&1 / &3 * log(&N))} /\
                     &(nproduct t (\p. p)) < Dl}
                (\t. abs(&(CARD {x | x IN chen_Tk h N k /\
                                     !p. p IN t
                                         ==> p divides
                                             chen_dist h
                                              (FST x * FST(SND x) *
                                               SND(SND x))}) -
                         &(CARD(chen_Tk h N k)) * product t (chen_g h)))
            <= sum {d | 1 <= d /\ &d <= Dl} (\d. chen_bvE h N k d) +
               &8 * Dl +
               &19 * (&N / chen_l N k) *
               product {p | prime p /\ &p < exp(&1 / &3 * log(&N))}
                       (\p. &1 + chen_g h p)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P = {p | prime p /\ &p < exp(&1 / &3 * log(&N))}` THEN
  SUBGOAL_THEN `FINITE(P:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[FINITE_PRIMES_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {t | t SUBSET P /\ &(nproduct t (\p. p)) < Dl}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{t:num->bool | t SUBSET P}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `TT = {t | t SUBSET P /\ &(nproduct t (\p. p)) < Dl}` THEN
  SUBGOAL_THEN `!t. t IN TT ==> FINITE t /\ (!q. q IN t ==> prime q) /\
                                1 <= nproduct t (\p. p) /\
                                &(nproduct t (\p. p)) < Dl /\
                                t SUBSET P`
  ASSUME_TAC THENL
   [EXPAND_TAC "TT" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `t:num->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `FINITE(t:num->bool) /\ (!q. q IN t ==> prime q)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET];
        UNDISCH_TAC `t SUBSET (P:num->bool)` THEN EXPAND_TAC "P" THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  ABBREV_TAC `X = &N / chen_l N k` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum TT (\t. (if !q. q IN t ==> ~(q divides h)
                 then chen_bvE h N k (nproduct t (\p. p)) else &0) +
                &8 + &19 * X * product t (chen_g h))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:num->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:num->bool` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `TT:(num->bool)->bool`)) (concl th))) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    EXPAND_TAC "X" THEN MATCH_MP_TAC CHEN_TK_REMAINDER_T THEN
    EXISTS_TAC `Dl:real` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `t SUBSET (P:num->bool)` THEN EXPAND_TAC "P" THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_CONST; SUM_LMUL] THEN
  SUBGOAL_THEN `!d. &0 <= chen_bvE h N k d` ASSUME_TAC THENL
   [REWRITE_TAC[chen_bvE; REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t1 t2. t1 IN TT /\ t2 IN TT /\
            nproduct t1 (\p. p) = nproduct t2 (\p. p) ==> t1 = t2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC NPRODUCT_PRIMES_INJ THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b c a' b' c':real. a <= a' /\ b <= b' /\ c <= c'
                          ==> a + b + c <= a' + b' + c'`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    SUBGOAL_THEN
     `sum {t | t IN TT /\ (!q. q IN t ==> ~(q divides h))}
          (\t. chen_bvE h N k (nproduct t (\p. p))) =
      sum (IMAGE (\t. nproduct t (\p. p))
                 {t | t IN TT /\ (!q. q IN t ==> ~(q divides h))})
          (chen_bvE h N k)`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
      ANTS_TAC THENL [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
                      REWRITE_TAC[o_DEF]];
      ALL_TAC] THEN
    REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[FINITE_NUM_RANGE_LE]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[];
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(CARD {b | 1 <= b /\ &b < Dl})` THEN
    ASM_SIMP_TAC[CARD_NUM_RANGE_LE; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC
     `CARD(IMAGE (\t. nproduct t (\p. p)) (TT:(num->bool)->bool))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUM_RANGE] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    REWRITE_TAC[CHEN_L_POS];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM SUM_POWERSET_PRODUCT] THEN REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_SIMP_TAC[FINITE_POWERSET] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "TT" THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `t:num->bool` THEN
  STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`h:num`; `q:num`] CHEN_G_BOUNDS) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `t SUBSET (P:num->bool)` THEN EXPAND_TAC "P" THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let CHEN_Y_FACTS = prove
 (`!N k. 256 < N /\ chen_l N k < exp(&1 / &3 * log(&N))
         ==> &2 <= min (chen_l N (k + 1)) (exp(&1 / &3 * log(&N))) /\
             chen_l N k < min (chen_l N (k + 1)) (exp(&1 / &3 * log(&N))) /\
             log(&N) / &8 <=
             log(min (chen_l N (k + 1)) (exp(&1 / &3 * log(&N)))) /\
             log(min (chen_l N (k + 1)) (exp(&1 / &3 * log(&N)))) <=
             log(&N) /\
             &N <= &N / chen_l N k *
                   min (chen_l N (k + 1)) (exp(&1 / &3 * log(&N))) /\
             &N / chen_l N k *
             min (chen_l N (k + 1)) (exp(&1 / &3 * log(&N))) <= &3 * &N /\
             exp(&2 / &3 * log(&N)) <= &N / chen_l N k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&8 * log(&2) <= log(&N) /\ &0 < log(&N) /\ &0 < &N /\
                &1 <= log(&N)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(exp(&1))` THEN
      CONJ_TAC THENL [REWRITE_TAC[LOG_EXP; REAL_LE_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
      MP_TAC E_BOUNDS THEN
      SUBGOAL_THEN `&3 <= &N` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `LN = log(&N)` THEN
  ABBREV_TAC `l = chen_l N k` THEN
  ABBREV_TAC `y = exp(&1 / &3 * LN)` THEN
  SUBGOAL_THEN `&0 < l /\ exp(LN / &8) <= l /\
                chen_l N (k + 1) = exp(inv LN) * l`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["l"; "LN"] THEN
    REWRITE_TAC[CHEN_L_POS; CHEN_L_SUC] THEN
    MP_TAC(SPECL [`N:num`; `k:num`] CHEN_Z_LE_L) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= c ==> b <= c`) THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 < exp(inv LN) /\ exp(inv LN) <= &3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `inv(LN:real)` REAL_EXP_LE_X) THEN
      SUBGOAL_THEN `&0 < inv LN` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&1)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
        ASM_REAL_ARITH_TAC;
        MP_TAC E_BOUNDS THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= exp(LN / &8)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log(&2))` THEN
    CONJ_TAC THENL
     [SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`; REAL_LE_REFL];
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `l < exp(inv LN) * l` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Y = min (exp(inv LN) * l) y` THEN
  SUBGOAL_THEN `l < Y /\ exp(LN / &8) <= Y /\ Y <= y /\
                Y <= exp(inv LN) * l`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(REAL_ARITH `!x a y:real. x = a /\ a <= y ==> x <= y`) THEN
    EXISTS_TAC `log(exp(LN / &8))` THEN CONJ_TAC THENL
     [REWRITE_TAC[LOG_EXP]; MATCH_MP_TAC LOG_MONO_LE_IMP] THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log y` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "y" THEN REWRITE_TAC[LOG_EXP] THEN ASM_REAL_ARITH_TAC];
    ASM_SIMP_TAC[REAL_FIELD `&0 < l ==> N / l * Y = N * (Y / l)`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_FIELD `&0 < l ==> N / l * Y = N * (Y / l)`] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(inv LN) * l` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(&2 / &3 * LN) * exp(&1 / &3 * LN)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_EXP_POS_LT; REAL_LT_IMP_LE];
      REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
      SUBGOAL_THEN `&2 / &3 * LN + &1 / &3 * LN = LN` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "LN" THEN ASM_SIMP_TAC[EXP_LOG; REAL_LE_REFL]]]);;

let CHEN_BV_APPLY = prove
 (`!A. ?C. &0 <= C /\
          !h N k Dl. EVEN h /\ 1 <= h /\ h <= N /\ EVEN N /\ 256 < N /\
                   chen_l N k < exp(&1 / &3 * log(&N)) /\
                   log(&N) pow (2 * A) <= exp(&2 / &3 * log(&N)) /\
                   Dl <= sqrt(&N) / log(&N) pow A
                   ==> sum {d | 1 <= d /\ &d <= Dl} (\d. chen_bvE h N k d)
                       <= C * &N * (log(&N) + &2) pow 2 /
                          (log(&N) / &8) pow A`,
  X_GEN_TAC `A:num` THEN
  MP_TAC(SPEC `A:num` BILINEAR_BV) THEN DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN
  EXISTS_TAC `&3 * abs C` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `k:num`] CHEN_Y_FACTS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Y = min (chen_l N (k + 1)) (exp(&1 / &3 * log(&N)))` THEN
  ABBREV_TAC `X = &N / chen_l N k` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log(&N) /\ &0 < &N /\ &1 <= &N` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT; ALL_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `LN = log(&N)` THEN
  SUBGOAL_THEN `&0 < log Y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < X` ASSUME_TAC THENL
   [MP_TAC(SPEC `&2 / &3 * LN` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`X:real`; `Y:real`; `chen_l N k`; `chen_alpha h N k`;
    `\d. if coprime(h,d) then h else 1`] o check (fun th ->
      can (find_term ((=) `C:real`)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CHEN_ALPHA_BOUNDS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(LN:real) pow (2 * A)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[COPRIME_1]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b c d:real. a <= b /\ c <= d ==> b <= c ==> a <= d`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[chen_bvE; chen_bsum] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUM_RANGE_LE; REAL_ABS_POS; IN_DIFF] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `d:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Dl:real` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sqrt(&N) / (LN:real) pow A` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < log Y pow A /\ log Y pow A <= LN pow A`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(X * Y) /\ log(X * Y) <= LN + &2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&3 * &N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[LOG_MUL; REAL_ARITH `&0 < &3`] THEN
      MP_TAC(SPEC `&2` LOG_LE) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (LN / &8) pow A /\ (LN / &8) pow A <= log Y pow A`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `X * Y * log(X * Y) pow 2 / log Y pow A <=
    (&3 * &N) * (LN + &2) pow 2 / (LN / &8) pow A`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= X * Y * log(X * Y) pow 2 / log Y pow A`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(C:real) * X * Y * log(X * Y) pow 2 / log Y pow A` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(C:real) * (&3 * &N) * (LN + &2) pow 2 / (LN / &8) pow A` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[real_div] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The final arithmetic (logarithm bounds are in nt.ml).                     *)
(* ------------------------------------------------------------------------- *)

let CHEN_CB_BOUNDS = prove
 (`&0 <= chen_cB /\ chen_cB <= &1 / &2`,
  CONJ_TAC THENL
   [REWRITE_TAC[chen_cB] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &1 /\ &0 < &2 /\ &0 < &3 /\
                                  &0 < &7 /\ &0 < &8`; LOG_1] THEN
    SUBGOAL_THEN `log(&8) = &3 * log(&2)` SUBST1_TAC THENL
     [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC LOG_2_LOWER THEN MP_TAC LOG_3_UPPER THEN MP_TAC LOG_7_UPPER THEN
    REAL_ARITH_TAC;
    MP_TAC CHEN_CONSTANT_POS THEN REWRITE_TAC[GSYM chen_cB] THEN
    MP_TAC(SPEC `&1 / &2` LOG_LE) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REAL_ARITH_TAC]);;

let CHEN_SB_MAIN_ARITH = prove
 (`!A cB h e. &3 <= A /\ &0 <= cB /\ cB <= &1 / &2 /\ &0 <= h /\
             h <= &1 / &100 /\ &18 * A * h <= e
             ==> &3 / &8 * (&1 + h) pow 3 * (A * (&2 / &3 + h) + h) *
                 (cB + h)
                 <= A * cB / &4 + e / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `h pow 2 <= h /\ h pow 3 <= h /\ &0 <= h pow 2 /\
                &0 <= h pow 3`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; ARITH_RULE `3 = SUC 2`; real_pow] THEN
    REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `h * &1` THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM REAL_POW_2] THEN
      MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]) THEN
      REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + h) pow 3 <= &1 + &7 * h` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&1 + h) pow 3 = &1 + &3 * h + &3 * h pow 2 + h pow 3`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `A * (&2 / &3 + h) + h <= &2 / &3 * A * (&1 + &2 * h)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (A - &3) * h` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&3 / &8 * (&1 + &7 * h) * (&2 / &3 * A * (&1 + &2 * h)) *
              (cB + h)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[]];
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + &7 * h) * (&1 + &2 * h) <= &1 + &23 * h`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(&1 + &7 * h) * (&1 + &2 * h) =
                  &1 + &9 * h + &14 * h pow 2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + &23 * h) * (cB + h) <= cB + &36 * h` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&1 + &23 * h) * (cB + h) =
                  cB + h + &23 * (h * cB) + &23 * h pow 2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `h * cB <= h * (&1 / &2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `A / &4 * (cB + &36 * h)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `A / &4 * ((&1 + &23 * h) * (cB + h))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `A / &4 * ((&1 + &7 * h) * (&1 + &2 * h)) * (cB + h)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let CHEN_S_ARITH = prove
 (`!s eta h. s = &3 / &2 - eta /\ &0 <= eta /\ eta <= h /\ h <= &1 / &100
             ==> &1 <= s /\ s <= &3 /\ inv s <= &2 / &3 + h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&3 / &2 - eta) = &1 / (&3 / &2 - eta)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &3 / &2 - eta` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `eta * h <= h * h /\ h * h <= h / &100` MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let CHEN_ETA_SMALL = prove
 (`!LN Pw h. &1 <= LN /\ &1 <= Pw /\ &0 < h /\
             (&96 / h) pow 2 <= LN /\ &6 * abs(log Pw) / h <= LN
             ==> &0 <= &3 * (&8 * log LN + log Pw) / LN /\
                 &3 * (&8 * log LN + log Pw) / LN <= h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= log LN /\ &0 <= log Pw /\ &0 < LN` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC LOG_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SIEVE_MUL_DIV_ASSOC] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `&96 / h <= sqrt LN` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt((&96 / h) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC POW_2_SQRT THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&48 * sqrt LN <= h / &2 * LN` ASSUME_TAC THENL
   [SUBGOAL_THEN `h * (sqrt LN * sqrt LN) = h * LN` ASSUME_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_POW_2] THEN
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sqrt LN` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&48 <= h / &2 * sqrt LN` ASSUME_TAC THENL
     [UNDISCH_TAC `&96 / h <= sqrt LN` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&48 * sqrt LN <= (h / &2 * sqrt LN) * sqrt LN` MP_TAC
    THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log LN <= &2 * sqrt LN` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_LE_2_SQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&6 * abs(log Pw) <= LN * h` ASSUME_TAC THENL
   [UNDISCH_TAC `&6 * abs(log Pw) / h <= LN` THEN
    ASM_SIMP_TAC[SIEVE_MUL_DIV_ASSOC; REAL_LE_LDIV_EQ];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CHEN_SB_REM_ARITH = prove
 (`!N LN Cb c e z G sN Dl Vz.
        &0 < N /\ &2 <= LN /\ &0 <= Cb /\ &0 < c /\ &0 < e /\
        &3 * &8 pow 8 * Cb / (c * e) + &1 <= LN /\ &12 / (c * e) <= LN /\
        &19 / (&4 * c pow 2 * e) <= LN /\ LN pow 6 <= z /\
        &0 <= G /\ G <= LN / (&3 * c) /\
        &0 < sN /\ sN * sN = N /\ LN / &2 <= sN /\
        Dl = sN / LN pow 8 /\ &8 * c / LN <= Vz
        ==> LN pow 2 * (Cb * N * (LN + &2) pow 2 / (LN / &8) pow 8 +
                        &8 * Dl + &19 * N / z * G)
            <= e / &2 * N / LN * Vz`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < LN /\ &0 < c * e /\ &0 < z /\ &1 <= LN pow 4 /\
                &0 < LN pow 4`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= LN pow 4` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(LN:real) pow 6` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `K = (N:real) / LN pow 2` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LN pow 2 * (Cb * N * (LN + &2) pow 2 / (LN / &8) pow 8) <=
    &4 / &3 * c * e * K`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `LN pow 2 * (Cb * N * (LN + &2) pow 2 / (LN / &8) pow 8) =
      (&8 pow 8 * Cb * (LN + &2) pow 2 / LN pow 4) * K`
    SUBST1_TAC THENL
     [EXPAND_TAC "K" THEN UNDISCH_TAC `&0 < LN` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `&4 / &3 * c * e * K = (&4 / &3 * c * e) * K`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(LN + &2) pow 2 <= &4 * LN pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * LN) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&3 * &8 pow 8 * Cb <= c * e * LN pow 2` ASSUME_TAC THENL
     [UNDISCH_TAC `&3 * &8 pow 8 * Cb / (c * e) + &1 <= LN` THEN
      REWRITE_TAC[SIEVE_MUL_DIV_ASSOC] THEN
      SUBGOAL_THEN `(&3 * &8 pow 8 * Cb) / (c * e) =
                    (&3 * &8 pow 8 * Cb) * inv(c * e)` SUBST1_TAC THENL
       [REWRITE_TAC[real_div]; ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(LN:real) <= LN pow 2` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_POW_2] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(&3 * &8 pow 8 * Cb) * inv(c * e) <= LN pow 2`
      MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&8 pow 8 * Cb * (&4 * LN pow 2) / LN pow 4` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&8 pow 8 * Cb * (&4 * LN pow 2) / LN pow 4 =
                  (&4 * &8 pow 8 * Cb) / LN pow 2`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < LN` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < LN pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `LN pow 2 * (&8 * Dl) <= &4 / &3 * c * e * K` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `sN * sN = N:real`)) THEN
    SUBGOAL_THEN `LN pow 2 * (&8 * sN / LN pow 8) =
                  (&8 / LN pow 4) * (sN / LN pow 2) /\
                  &4 / &3 * c * e * (sN * sN) / LN pow 2 =
                  (&4 / &3 * c * e * sN) * (sN / LN pow 2)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN UNDISCH_TAC `&0 < LN` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `&6 <= c * e * sN` ASSUME_TAC THENL
     [SUBGOAL_THEN `&12 / (c * e) <= &2 * sN` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&8 / LN pow 4 <= &8` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `LN pow 2 * (&19 * N / z * G) <= &4 / &3 * c * e * K`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `LN pow 2 * (&19 * N / z * G) =
                  (&19 * LN pow 4 * G / z) * K` SUBST1_TAC THENL
     [EXPAND_TAC "K" THEN
      MAP_EVERY UNDISCH_TAC [`&0 < LN`; `&0 < z`] THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `&4 / &3 * c * e * K = (&4 / &3 * c * e) * K`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < LN pow 6` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&19 * LN pow 4 * (LN / (&3 * c)) / LN pow 6` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM real_div] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&19 * LN pow 4 * (LN / (&3 * c)) / LN pow 6 =
                  &19 / (&3 * c * LN)` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < LN`; `&0 < c`] THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &3 * c * LN /\ &0 < &4 * c pow 2 * e` STRIP_ASSUME_TAC
    THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
        ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
         ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `&19 / (&4 * c pow 2 * e) <= LN` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REWRITE_TAC[REAL_POW_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * c * e * K <= e / &2 * N / LN * Vz` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e / &2 * N / LN * (&8 * c / LN)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN EXPAND_TAC "K" THEN
      UNDISCH_TAC `&0 < LN` THEN CONV_TAC REAL_FIELD;
      ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`LN pow 2 * (Cb * N * (LN + &2) pow 2 / (LN / &8) pow 8) <=
     &4 / &3 * c * e * K`;
    `LN pow 2 * (&8 * Dl) <= &4 / &3 * c * e * K`;
    `LN pow 2 * (&19 * N / z * G) <= &4 / &3 * c * e * K`] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN REAL_ARITH_TAC);;

let CHEN_SB_COMBINE = prove
 (`!K (sf:num->real) X R S Q Tb Rb LN M E.
        FINITE K /\ S <= sum K sf /\
        (!k. k IN K ==> sf k <= X k * Q + R k) /\
        (!k. k IN K ==> R k <= Rb) /\ &0 <= Rb /\ &0 <= Q /\
        sum K X <= Tb /\ &(CARD K) <= LN /\
        Q * Tb <= M /\ LN * Rb <= E
        ==> S <= M + E`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum K (\k. X k * Q + (R:num->real) k)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum K (sf:num->real)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_RMUL] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Q:real) * Tb` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(CARD(K:num->bool)) * Rb` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(LN:real) * Rb` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The upper bound for S(B) and Chen's theorem.                              *)
(* ------------------------------------------------------------------------- *)

let CHEN_SB_UPPER_GEN = prove
 (`!e. &0 < e
       ==> ?N0. !h N. EVEN h /\ 1 <= h /\ h <= N /\ EVEN N /\ N0 <= N
                ==> &(CARD {p1,p2,p3 | (p1,p2,p3) IN chen_T h N /\
                                       !q. prime q /\
                                           &q < exp(&1 / &3 * log(&N))
                                           ==> ~(q divides chen_dist h
                                                    (p1 * p2 * p3))})
                    <= (sieve_A * chen_cB / &4 + e) * &N / log(&N) *
                       product {p | prime p /\ &p < exp(&1 / &8 * log(&N))}
                               (\p. &1 - chen_g h p)`,
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC SIEVE_A_GE_3 THEN DISCH_TAC THEN
  MP_TAC CHEN_CB_BOUNDS THEN STRIP_TAC THEN
  ABBREV_TAC `hh = min (&1 / &100) (e / (&18 * sieve_A))` THEN
  SUBGOAL_THEN `&0 < hh /\ hh <= &1 / &100 /\ &18 * sieve_A * hh <= e`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &18 * sieve_A` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "hh" THEN REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
      EXPAND_TAC "hh" THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `hh <= e / (&18 * sieve_A)` MP_TAC THENL
       [EXPAND_TAC "hh" THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC CHEN_G_DIMENSION THEN
  MP_TAC(SPECL [`L:real`; `hh:real`] JURKAT_RICHERT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
  X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC CHEN_V_LOWER THEN
  X_CHOOSE_TAC `C1:real` CHEN_V_YZ THEN
  MP_TAC(SPEC `hh:real` PI_LT_REAL_UPPER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `X0:real`) THEN
  MP_TAC(SPEC `8` CHEN_BV_APPLY) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cb:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Pw = &(nproduct {p | prime p /\ &p < w} (\p. p))` THEN
  SUBGOAL_THEN `&1 <= Pw` ASSUME_TAC THENL
   [EXPAND_TAC "Pw" THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN REWRITE_TAC[FINITE_PRIMES_LT] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  MP_TAC(SPEC
   `&400 + &8 * abs(log w) + &3 * abs X0 + (&17 / (&2 / &3)) pow 17 +
    (&9 / (&1 / &2)) pow 9 + (&7 / (&1 / &8)) pow 7 +
    (&2 / (&1 / &8)) pow 2 +
    (&96 / hh) pow 2 + &6 * abs(log Pw) / hh + &4000 / hh +
    &2 * (&8 * abs C1 + &16) / hh +
    &3 * &8 pow 8 * Cb / (c * e) + &1 + &12 / (c * e) +
    &19 / (&4 * c pow 2 * e)` EVENTUALLY_LOG_GE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  EXISTS_TAC `N1 + 257` THEN MAP_EVERY X_GEN_TAC [`h:num`; `N:num`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num` o check (fun th ->
    can (find_term ((=) `N1:num`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `256 < N /\ 1 < N` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &N /\ &1 <= &N` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `LN = log(&N)` THEN
  SUBGOAL_THEN
   `&0 <= (&17 / (&2 / &3)) pow 17 /\ &0 <= (&9 / (&1 / &2)) pow 9 /\
    &0 <= (&7 / (&1 / &8)) pow 7 /\ &0 <= (&2 / (&1 / &8)) pow 2 /\
    &0 <= (&96 / hh) pow 2 /\ &0 <= &6 * abs(log Pw) / hh /\
    &0 <= &4000 / hh /\ &0 <= &2 * (&8 * abs C1 + &16) / hh /\
    &0 <= &3 * &8 pow 8 * Cb / (c * e) /\ &0 <= &12 / (c * e) /\
    &0 <= &19 / (&4 * c pow 2 * e)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < c * e /\ &0 < &4 * c pow 2 * e` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
         ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV;
      CONV_TAC REAL_RAT_REDUCE_CONV;
      CONV_TAC REAL_RAT_REDUCE_CONV;
      CONV_TAC REAL_RAT_REDUCE_CONV;
      REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&400 <= LN /\ &8 * abs(log w) <= LN /\ &3 * abs X0 <= LN /\
    (&17 / (&2 / &3)) pow 17 <= LN /\ (&9 / (&1 / &2)) pow 9 <= LN /\
    (&7 / (&1 / &8)) pow 7 <= LN /\ (&2 / (&1 / &8)) pow 2 <= LN /\
    (&96 / hh) pow 2 <= LN /\ &6 * abs(log Pw) / hh <= LN /\
    &4000 / hh <= LN /\ &2 * (&8 * abs C1 + &16) / hh <= LN /\
    &3 * &8 pow 8 * Cb / (c * e) + &1 <= LN /\ &12 / (c * e) <= LN /\
    &19 / (&4 * c pow 2 * e) <= LN`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `log w` REAL_ABS_POS) THEN MP_TAC(SPEC `X0:real` REAL_ABS_POS)
    THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < LN /\ &1 <= LN` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `LN pow 16 <= exp(&2 / &3 * LN) /\ LN pow 8 <= exp(&1 / &2 * LN) /\
    LN pow 6 <= exp(&1 / &8 * LN) /\ LN pow 1 <= exp(&1 / &8 * LN)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC POLY_LE_EXP THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp LN = &N` ASSUME_TAC THENL
   [EXPAND_TAC "LN" THEN ASM_SIMP_TAC[EXP_LOG]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&N) = exp(&1 / &2 * LN)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt(&N)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP EXP_LOG th)])
    THEN AP_TERM_TAC THEN ASM_SIMP_TAC[LOG_SQRT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `z = exp(&1 / &8 * LN)` THEN
  ABBREV_TAC `y = exp(&1 / &3 * LN)` THEN
  SUBGOAL_THEN
   `&0 < z /\ &0 < y /\ z <= y /\ &2 <= z /\ LN <= z /\ w <= y /\
    X0 <= y /\ log z = LN / &8 /\ log y = LN / &3`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["z"; "y"] THEN
    REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LE; LOG_EXP] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log(&2))` THEN
      CONJ_TAC THENL
       [SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`; REAL_LE_REFL];
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN MP_TAC LOG_2_UPPER THEN
        ASM_REAL_ARITH_TAC];
      UNDISCH_TAC `(LN:real) pow 1 <= z` THEN
      EXPAND_TAC "z" THEN REWRITE_TAC[REAL_POW_1];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log w)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
      MP_TAC(SPEC `&1 / &3 * LN` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Vz = product {p | prime p /\ &p < z} (\p. &1 - chen_g h p)` THEN
  ABBREV_TAC `Vy = product {p | prime p /\ &p < y} (\p. &1 - chen_g h p)` THEN
  SUBGOAL_THEN `&8 * c / LN <= Vz /\ &3 * c / LN <= Vy /\ &0 < Vz /\ &0 < Vy`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c / log z` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        UNDISCH_TAC `&0 < LN` THEN CONV_TAC REAL_FIELD;
        EXPAND_TAC "Vz" THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c / log y` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        UNDISCH_TAC `&0 < LN` THEN CONV_TAC REAL_FIELD;
        EXPAND_TAC "Vy" THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      EXPAND_TAC "Vz" THEN ASM_SIMP_TAC[CHEN_V_POS];
      EXPAND_TAC "Vy" THEN ASM_SIMP_TAC[CHEN_V_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(C1 / (&1 / &8 * LN) + &16 / z) <= hh / &2` ASSUME_TAC
  THENL
   [SUBGOAL_THEN
     `abs(C1 / (&1 / &8 * LN)) = &8 * abs C1 / LN /\
      &16 / z <= &16 / LN /\ &0 <= &16 / z`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_ABS_DIV] THEN
        SUBGOAL_THEN `abs(&1 / &8 * LN) = &1 / &8 * LN` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `&0 < LN` THEN CONV_TAC REAL_FIELD;
        REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&8 * abs C1 + &16) / LN <= hh / &2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      UNDISCH_TAC `&2 * (&8 * abs C1 + &16) / hh <= LN` THEN
      ASM_SIMP_TAC[SIEVE_MUL_DIV_ASSOC; REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Vy <= &3 / &8 * (&1 + hh) * Vz` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`h:num`; `N:num`] o check (fun th ->
      can (find_term ((=) `C1:real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `!a b x:real. a <= b ==> x <= a ==> x <= b`) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 + &2 * abs(C1 / (&1 / &8 * LN) + &16 / z)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EXP_ABS_SMALL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Dl = sqrt(&N) / LN pow 8` THEN
  SUBGOAL_THEN `&0 < LN pow 8 /\ &1 <= LN pow 8` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= Dl /\ Dl <= exp(&1 / &2 * LN) /\ &0 < Dl`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Dl" THEN
    REWRITE_TAC[ASSUME `sqrt(&N) = exp(&1 / &2 * LN)`] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_LT_DIV;
                 REAL_EXP_POS_LT] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Pw` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `s = log(Dl / Pw) / log y` THEN
  SUBGOAL_THEN `&1 <= s /\ s <= &3 /\ inv s <= &2 / &3 + hh`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC CHEN_S_ARITH THEN
    EXISTS_TAC `&3 * (&8 * log LN + log Pw) / LN` THEN
    MP_TAC(SPECL [`LN:real`; `Pw:real`; `hh:real`] CHEN_ETA_SMALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN
    SIMP_TAC[LOG_DIV; ASSUME `&0 < Dl`; ASSUME `&0 < Pw`;
             ASSUME `log y = LN / &3`] THEN
    EXPAND_TAC "Dl" THEN
    REWRITE_TAC[ASSUME `sqrt(&N) = exp(&1 / &2 * LN)`] THEN
    SIMP_TAC[LOG_DIV; REAL_EXP_POS_LT; LOG_EXP; LOG_POW;
             ASSUME `&0 < LN`; ASSUME `&0 < LN pow 8`] THEN
    UNDISCH_TAC `&0 < LN` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `sieve_F s + hh <= sieve_A * (&2 / &3 + hh) + hh`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[SIEVE_UPPER_13] THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC(REAL_ARITH `!x y:real. x <= y ==> x + hh <= y + hh`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `N:num` FINITE_CHEN_K) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sieve_F s + hh` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SIEVE_UPPER_13] THEN
    SUBGOAL_THEN `&0 <= sieve_A / s` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `chen_g h` o check (fun th ->
    can (find_term ((=) `sieve_F`)) (concl th) && is_forall(concl th))) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[CHEN_G_BOUNDS];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `L:real`)) (concl th) && is_forall(concl th)))
      THEN ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `(sieve_A * chen_cB / &4 + e) * &N / LN * Vz =
    (sieve_A * chen_cB / &4 + e / &2) * &N / LN * Vz +
    e / &2 * &N / LN * Vz`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CHEN_SB_COMBINE THEN
  MAP_EVERY EXISTS_TAC
   [`{k | chen_l N k < y}`;
    `\k. &(CARD {x | x IN chen_Tk h N k /\
                     !q. prime q /\ &q < y
                         ==> ~(q divides chen_dist h
                                 (FST x * FST(SND x) * SND(SND x)))})`;
    `\k. &(CARD(chen_Tk h N k))`;
    `\k. sum {t | t SUBSET {p | prime p /\ &p < y} /\
                  &(nproduct t (\p. p)) < Dl}
             (\t. abs(&(CARD {x | x IN chen_Tk h N k /\
                                  !p. p IN t
                                      ==> p divides
                                          chen_dist h
                                           (FST x * FST(SND x) *
                                            SND(SND x))}) -
                      &(CARD(chen_Tk h N k)) * product t (chen_g h)))`;
    `Vy * (sieve_F s + hh)`;
    `(&1 + hh) * (exp(inv LN) * &N) / LN * (chen_cB + &4000 / LN)`;
    `Cb * &N * (LN + &2) pow 2 / (LN / &8) pow 8 + &8 * Dl +
     &19 * (&N / z) * product {p | prime p /\ &p < y} (\p. &1 + chen_g h p)`;
    `(LN:real) pow 2`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`h:num`; `N:num`] CHEN_SB_SPLIT) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`IMAGE (\x:num#num#num. chen_dist h (FST x * FST(SND x) * SND(SND x)))
              (chen_Tk h N k)`;
       `\m. &(CARD {n | n IN chen_Tk h N k /\
                        (\x:num#num#num. chen_dist h
                           (FST x * FST(SND x) * SND(SND x))) n = m})`;
       `&(CARD(chen_Tk h N k))`; `(Dl:real) / Pw`; `y:real`] o check (fun th ->
       can (find_term ((=) `sifted`)) (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_CHEN_TK; REAL_POS; REAL_LT_DIV];
      DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SIFTED_IMAGE; SIEVE_COUNT_IMAGE; FINITE_CHEN_TK;
                 REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[IN_ELIM_THM];
    X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`h:num`; `N:num`; `k:num`;
     `Dl:real`] CHEN_TK_REMAINDER_SUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`h:num`; `N:num`; `k:num`;
     `Dl:real`] o check (fun th ->
      can (find_term ((=) `chen_bvE`)) (concl th) && is_forall(concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ASSUME `log(&N) = LN`] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; DISCH_TAC] THEN
    MP_TAC(SPECL [`N:num`; `k:num`] CHEN_Z_LE_L) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= product {p | prime p /\ &p < y} (\p. &1 + chen_g h p)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE THEN REWRITE_TAC[FINITE_PRIMES_LT] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`h:num`; `x:num`] CHEN_G_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&N / chen_l N k * product {p | prime p /\ &p < y} (\p. &1 + chen_g h p)
      <= &N / z * product {p | prime p /\ &p < y} (\p. &1 + chen_g h p)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!R S1 B D A1 A2:real. R <= S1 + &8 * D + &19 * A1 /\ S1 <= B /\ A1 <= A2
                           ==> R <= B + &8 * D + &19 * A2`) THEN
    MAP_EVERY EXISTS_TAC
     [`sum {d | 1 <= d /\ &d <= Dl} (\d. chen_bvE h N k d)`;
      `&N / chen_l N k *
       product {p | prime p /\ &p < y} (\p. &1 + chen_g h p)`]
    THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `&0 <= product {p | prime p /\ &p < y} (\p. &1 + chen_g h p)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE THEN REWRITE_TAC[FINITE_PRIMES_LT] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`h:num`; `x:num`] CHEN_G_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`h:num`; `N:num`] CHEN_TK_CARD_SUM) THEN
      ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `!a b c:real. b <= c ==> a <= b ==> a <= c`) THEN
    MP_TAC(SPECL [`N:num`; `exp(inv LN) * &N`; `hh:real`; `X0:real`]
           CHEN_THAT_CARD_FIXED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `&0 <= inv LN /\ inv LN <= &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MP_TAC(SPEC `inv(LN:real)` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE]];
    SUBGOAL_THEN `&400 * &400 <= LN pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[REAL_POS] THEN ASM_REWRITE_TAC[];
      ABBREV_TAC `cK = &(CARD {k | chen_l N k < y})` THEN
      MAP_EVERY UNDISCH_TAC
       [`cK <= &5 / &24 * LN pow 2 + &1`; `&400 * &400 <= LN pow 2`] THEN
      REAL_ARITH_TAC];
    SUBGOAL_THEN `&0 <= inv LN /\ &2 / LN <= hh /\ &4000 / LN <= hh`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      UNDISCH_TAC `&4000 / hh <= LN` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(inv LN) <= &1 + hh /\ &0 <= chen_cB + &4000 / LN`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + &2 * abs(inv LN)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC EXP_ABS_SMALL THEN
          UNDISCH_TAC `&2 / LN <= hh` THEN REWRITE_TAC[real_div] THEN
          ASM_REAL_ARITH_TAC;
          UNDISCH_TAC `&2 / LN <= hh` THEN REWRITE_TAC[real_div] THEN
          ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sieve_A * (&2 / &3 + hh) + hh /\ &0 <= Vz /\
                  &0 <= (exp(inv LN) * &N) / LN /\
                  (exp(inv LN) * &N) / LN <= ((&1 + hh) * &N) / LN`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
          ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((&3 / &8 * (&1 + hh) * Vz) *
                 (sieve_A * (&2 / &3 + hh) + hh)) *
                ((&1 + hh) * ((&1 + hh) * &N) / LN * (chen_cB + hh))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`sieve_A`; `chen_cB`; `hh:real`;
     `e:real`] CHEN_SB_MAIN_ARITH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= &N / LN * Vz` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&3 / &8 * (&1 + hh) pow 3 * (sieve_A * (&2 / &3 + hh) + hh) *
                 (chen_cB + hh)) * (&N / LN * Vz)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[real_div] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(sieve_A * chen_cB / &4 + e / &2) * (&N / LN * Vz)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[real_div] THEN
      REAL_ARITH_TAC];
    MATCH_MP_TAC CHEN_SB_REM_ARITH THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `sqrt(&N)`] THEN
    SUBGOAL_THEN `&0 < sqrt(&N) /\ sqrt(&N) * sqrt(&N) = &N /\
                  LN / &2 <= sqrt(&N)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC SQRT_POW_2 THEN
        ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `&1 / &2 * LN` REAL_EXP_LE_X) THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= product {p | prime p /\ &p < y} (\p. &1 + chen_g h p) /\
      product {p | prime p /\ &p < y} (\p. &1 + chen_g h p) <= LN / (&3 * c)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC PRODUCT_POS_LE THEN REWRITE_TAC[FINITE_PRIMES_LT] THEN
        REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        MP_TAC(SPECL [`h:num`; `x:num`] CHEN_G_BOUNDS) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(Vy:real)` THEN
        CONJ_TAC THENL
       [EXPAND_TAC "Vy" THEN MATCH_MP_TAC PRODUCT_ONE_PLUS_LE_INV THEN
        ASM_REWRITE_TAC[FINITE_PRIMES_LT] THEN SIMP_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      SUBGOAL_THEN `LN / (&3 * c) = inv((&3 * c) / LN)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_INV_DIV]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `&3 * c / LN <= Vy` THEN REWRITE_TAC[real_div] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Chen's theorem in both forms, conditionally.                              *)
(* ------------------------------------------------------------------------- *)

let CHEN_GENERAL = prove
 (`!h. chen_sieve_ok h
       ==> ?c N0. &0 < c /\
                  !N. EVEN N /\ N0 <= N
                      ==> c * &N / log(&N) pow 2 <=
                          &(CARD {n | n IN gchen_A (h N) N /\
                                      almost_prime 2 n})`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CHEN_FROM_SB_GEN THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `e:real` CHEN_SB_UPPER_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
  EXISTS_TAC `N0 + 16` THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `chen_sieve_ok h` THEN REWRITE_TAC[chen_sieve_ok] THEN
  DISCH_THEN(MP_TAC o SPEC `N:num` o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[] THEN ASM_ARITH_TAC);;
