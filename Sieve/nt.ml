(* ========================================================================= *)
(* Elementary lemmas shared by the sieve files and the analytic files.       *)
(*                                                                           *)
(* Products of distinct primes: COPRIME_PRIME_NPRODUCT,                      *)
(* PRIMES_DIVIDE_IFF_NPRODUCT, NPRODUCT_PRIME_DIVISORS_DIVIDES,              *)
(* ITLIST_MUL_DIVIDES; the number of prime divisors:                         *)
(* FINITE_PRIME_DIVISORS, OMEGA_LE_LOG                                       *)
(* (omega(N) <= log N / log 2); EXP_GE_POW ((t/n)^n <= e^t); divisor sums:   *)
(* SUM_SUM_DIVISORS (hyperbola regrouping), DIVISOR_REFLECT and              *)
(* SUM_DIVISORS_REFLECT (d -> n/d);                                          *)
(* HARMONIC_LE_LOG (sum_{k<=n} 1/k <= 1 + log n); CARD_MULTIPLES_LE and      *)
(* CARD_MULTIPLES_GE (x/d - 1 <= #{n <= x | d | n} <= x/d);                  *)
(* FINITE_NUM_INTERVAL ({n | x < n <= y} is finite), FINITE_NUM_RANGE_LE     *)
(* ({n | 1 <= n <= y} is finite); inverse squares:                           *)
(* SUM_INV_SQUARE_TAIL_NUMSEG (sum_{m<k<=N} 1/k^2 <= 1/m - 1/N),             *)
(* SUM_INV_SQUARE_TAIL, SUM_INV_SQUARE_LE_2 (sum_{k<=M} 1/k^2 <= 2);         *)
(* LOG_POW_LE_SQRT (log^A y <= (2A)^A sqrt y for y >= 1), LOG_GE_1           *)
(* (log x >= 1 for x >= 4); MANGOLDT_LE_LOG (Lambda(n) <= log n);            *)
(* SUM_CARD_SWAP (double counting of a relation between two finite           *)
(* sets), SUM_INDICATOR_PAIR (a sum of products of two indicators            *)
(* counts the common elements); DIVIDES_ADDH_CONG (d divides p + h iff       *)
(* p == d - h MOD d (mod d)).                                                *)
(* The last sections collect elementary facts used in several files          *)
(* (E_BOUNDS, REAL_LE_DIV_BOTH, CARD_NUM_LE_REAL, FINITE_PRIMES_LE_RESTRICT, *)
(* POLYLOG_EXP_BOUND), rigorous bounds for log 2, log 3 and log 7, and       *)
(* SUM_WEIGHTED_CS: (sum w a)^2 <= sum w * sum w a^2 for w >= 0.             *)
(* Uses the common libraries in base.ml and Examples/mangoldt.ml.            *)
(* ========================================================================= *)

needs "Sieve/base.ml";;
needs "Library/multiplicative.ml";;
needs "Multivariate/transcendentals.ml";;
needs "Examples/mangoldt.ml";;

prioritize_num(); prioritize_complex();;

let COPRIME_PRIME_NPRODUCT = prove
 (`!p t. prime p /\ FINITE t /\ (!q. q IN t ==> prime q) /\ ~(p IN t)
         ==> coprime(p,nproduct t (\q. q))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COPRIME_NPRODUCT_EQ] THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC DISTINCT_PRIME_COPRIME THEN ASM_MESON_TAC[]);;

let PRIMES_DIVIDE_IFF_NPRODUCT = prove
 (`!t N. FINITE t /\ (!p. p IN t ==> prime p)
         ==> ((!p. p IN t ==> p divides N) <=> nproduct t (\p. p) divides N)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY; NPRODUCT_CLAUSES; DIVIDES_1]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `t:num->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN X_GEN_TAC `N:num` THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[NPRODUCT_CLAUSES] THEN EQ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC DIVIDES_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COPRIME_PRIME_NPRODUCT THEN ASM_REWRITE_TAC[];
    MESON_TAC[DIVIDES_TRANS; DIVIDES_LMUL; DIVIDES_RMUL; DIVIDES_REFL]]);;

let FINITE_PRIME_DIVISORS = prove
 (`!N. ~(N = 0) ==> FINITE {p | prime p /\ p divides N}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{d | d divides N}` THEN ASM_SIMP_TAC[FINITE_DIVISORS] THEN
  SET_TAC[]);;

let NPRODUCT_PRIME_DIVISORS_DIVIDES = prove
 (`!N. ~(N = 0) ==> nproduct {p | prime p /\ p divides N} (\p. p) divides N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`{p | prime p /\ p divides N}`; `N:num`]
               PRIMES_DIVIDE_IFF_NPRODUCT) THEN
  ASM_SIMP_TAC[FINITE_PRIME_DIVISORS; IN_ELIM_THM]);;

let ITLIST_MUL_DIVIDES = prove
 (`!l q. MEM q l ==> q divides ITLIST ( * ) l 1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; ITLIST] THEN
  ASM_MESON_TAC[DIVIDES_LMUL; DIVIDES_RMUL; DIVIDES_REFL]);;

let OMEGA_LE_LOG = prove
 (`!N. 1 <= N
       ==> &(CARD {p | prime p /\ p divides N}) <= log(&N) / log(&2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  ABBREV_TAC `P = {p | prime p /\ p divides N}` THEN
  SUBGOAL_THEN `FINITE(P:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC FINITE_PRIME_DIVISORS THEN
    UNDISCH_TAC `1 <= N` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP CARD(P:num->bool) <= N` MP_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `nproduct P (\p:num. p)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM NPRODUCT_CONST] THEN MATCH_MP_TAC NPRODUCT_LE THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "P" THEN
      SIMP_TAC[IN_ELIM_THM; PRIME_GE_2; LE_REFL];
      MATCH_MP_TAC DIVIDES_LE_IMP THEN EXPAND_TAC "P" THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC NPRODUCT_PRIME_DIVISORS_DIVIDES THEN
        UNDISCH_TAC `1 <= N` THEN ARITH_TAC;
        UNDISCH_TAC `1 <= N` THEN ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN DISCH_TAC THEN
  SUBGOAL_THEN `log(&2 pow CARD(P:num->bool)) <= log(&N)` MP_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[LOG_POW; REAL_ARITH `&0 < &2`] THEN REAL_ARITH_TAC);;

let EXP_GE_POW = prove
 (`!n t. &0 <= t ==> (t / &n) pow n <= exp t`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[real_pow] THEN MP_TAC(SPEC `t:real` REAL_EXP_LE_X) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp t = exp(t / &n) pow n` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `~(&n = &0)` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[REAL_POS];
    MP_TAC(SPEC `t / &n` REAL_EXP_LE_X) THEN REAL_ARITH_TAC]);;

let SUM_SUM_DIVISORS = prove
 (`!f x. sum (1..x) (\n. sum {d | d divides n} (f n)) =
         sum (1..x) (\n. sum (1..(x DIV n)) (\k. f (k * n) n))`,
  SIMP_TAC[sum; FINITE_DIVISORS; LE_1] THEN
  SIMP_TAC[sum; FINITE_NUMSEG; ITERATE_ITERATE_DIVISORS;
           MONOIDAL_REAL_ADD]);;

let DIVISOR_REFLECT = prove
 (`!m d. ~(m = 0) /\ d divides m
         ==> ~(d = 0) /\ m DIV d divides m /\ m DIV (m DIV d) = d /\
             d * (m DIV d) = m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:num` SUBST_ALL_TAC))
  THEN RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  ASM_SIMP_TAC[DIV_MULT; ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT] THEN
  MESON_TAC[MULT_SYM]);;

let SUM_DIVISORS_REFLECT = prove
 (`!f n. ~(n = 0)
         ==> sum {d | d divides n} (\d. f(n DIV d)) = sum {d | d divides n} f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
  MAP_EVERY EXISTS_TAC [`\d. n DIV d`; `\d. n DIV d`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `!d. d divides n ==> n DIV d divides n /\ n DIV (n DIV d) = d`
  (fun th -> SIMP_TAC[th]) THEN
  GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num` SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  ASM_SIMP_TAC[DIV_MULT; ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT] THEN
  MESON_TAC[MULT_SYM]);;

let HARMONIC_LE_LOG = prove
 (`!n. 1 <= n ==> sum(1..n) (\k. inv(&k)) <= &1 + log(&n)`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH_RULE `~(1 <= 0)`] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[SUM_SING_NUMSEG; ARITH; LOG_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `y <= l' - l ==> s <= &1 + l ==> s + y <= &1 + l'`) THEN
  SUBGOAL_THEN `&0 < &n /\ &0 < &(SUC n)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM LOG_DIV] THEN
  MP_TAC(SPEC `--inv(&(SUC n))` LOG_LE_STRONG) THEN
  SUBGOAL_THEN `&1 + --inv(&(SUC n)) = &n / &(SUC n)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    UNDISCH_TAC `&0 < &n` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; LOG_DIV] THEN REAL_ARITH_TAC);;

let CARD_MULTIPLES_LE = prove
 (`!d x. ~(d = 0) ==> &(CARD {n | n IN 1..x /\ d divides n}) <= &x / &d`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CARD_EQ_SUM; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  REWRITE_TAC[SUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[SUM_DIVISORS_FLOOR_LEMMA] THEN REWRITE_TAC[FLOOR]);;

let CARD_MULTIPLES_GE = prove
 (`!d x. ~(d = 0) ==> &x / &d - &1 <= &(CARD {n | n IN 1..x /\ d divides n})`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CARD_EQ_SUM; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  REWRITE_TAC[SUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[SUM_DIVISORS_FLOOR_LEMMA] THEN
  MP_TAC(SPEC `&x / &d` FLOOR) THEN REAL_ARITH_TAC);;

let FINITE_NUM_INTERVAL = prove
 (`!x y. FINITE {n | x < &n /\ &n <= y}`,
  REPEAT GEN_TAC THEN MP_TAC(SPEC `y:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..N` THEN
  REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_MESON_TAC[REAL_LE_TRANS]);;

let FINITE_NUM_RANGE_LE = prove
 (`!Y. FINITE {d | 1 <= d /\ &d <= Y}`,
  GEN_TAC THEN MP_TAC(SPEC `Y:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..M` THEN
  REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_MESON_TAC[REAL_LE_TRANS]);;

let SUM_INV_SQUARE_TAIL_NUMSEG = prove
 (`!m N. 1 <= m /\ m <= N
         ==> sum (m+1..N) (\n. inv(&n pow 2)) <= inv(&m) - inv(&N)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_CASES_TAC `m = SUC N` THENL
   [ASM_SIMP_TAC[SUM_TRIV_NUMSEG; ARITH_RULE `n < n + 1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `m + 1 <= SUC N <=> m <= N`] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(m = SUC N) /\ m <= SUC N ==> m <= N`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!s a b c d:real. s <= a - b /\ c <= b - d ==> s + c <= a - d`) THEN
  EXISTS_TAC `inv(&N)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= N` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_SUC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `inv(&N) - inv(&N + &1) = inv(&N * (&N + &1))` SUBST1_TAC THENL
   [UNDISCH_TAC `&1 <= &N` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_POW_2] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]);;

let SUM_INV_SQUARE_TAIL = prove
 (`!a b. 1 <= a ==> sum(a+1..b) (\k. inv(&k pow 2)) <= inv(&a)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `a:num <= b` THENL
   [MP_TAC(SPECL [`a:num`; `b:num`] SUM_INV_SQUARE_TAIL_NUMSEG) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> s <= x - y ==> s <= x`) THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
    ASM_SIMP_TAC[SUM_TRIV_NUMSEG; ARITH_RULE `~(a <= b) ==> b < a + 1`] THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]]);;

let SUM_INV_SQUARE_LE_2 = prove
 (`!M. sum(1..M) (\k. inv(&k pow 2)) <= &2`,
  GEN_TAC THEN ASM_CASES_TAC `M = 0` THENL
   [ASM_SIMP_TAC[SUM_TRIV_NUMSEG; ARITH] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES_LEFT; ARITH_RULE `~(M = 0) ==> 1 <= M`] THEN
  MP_TAC(SPECL [`1`; `M:num`] SUM_INV_SQUARE_TAIL) THEN
  REWRITE_TAC[ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let LOG_POW_LE_SQRT = prove
 (`!A y. &1 <= y ==> log y pow A <= (&2 * &A) pow A * sqrt y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= log y` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt y = exp(log y / &2)` SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    REWRITE_TAC[GSYM REAL_EXP_N; REAL_ARITH `&2 * x / &2 = x`] THEN
    MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `A = 0` THENL
   [ASM_REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
    MP_TAC(SPEC `log y / &2` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log y = (&2 * &A) * ((log y / &2) / &A)`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THENL
   [UNDISCH_TAC `~(A = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL
   [SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS];
    MATCH_MP_TAC EXP_GE_POW THEN ASM_REAL_ARITH_TAC]);;

let MANGOLDT_LE_LOG = prove
 (`!n. ~(n = 0) ==> mangoldt n <= log(&n)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LOG_MANGOLDT_SUM] THEN
  MP_TAC(ISPECL [`{n:num}`; `{d | d divides n}`; `\d. mangoldt d`]
    SUM_SUBSET_SIMPLE) THEN
  ASM_SIMP_TAC[SUM_SING; FINITE_DIVISORS; MANGOLDT_POS_LE] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[SUBSET; IN_SING; IN_ELIM_THM] THEN MESON_TAC[DIVIDES_REFL]);;

let LOG_GE_1 = prove
 (`!x. &4 <= x ==> &1 <= log x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `log(&2 pow 2)` THEN CONJ_TAC THENL
   [SIMP_TAC[LOG_POW; REAL_ARITH `&0 < &2`] THEN
    MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC;
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[]]);;

let SUM_CARD_SWAP = prove
 (`!(R:A->B->bool) s t.
        FINITE s /\ FINITE t
        ==> sum s (\x. &(CARD {y | y IN t /\ R x y})) =
            sum t (\y. &(CARD {x | x IN s /\ R x y}))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CARD_EQ_SUM; FINITE_RESTRICT] THEN
  MATCH_MP_TAC SUM_SUM_RESTRICT THEN ASM_REWRITE_TAC[]);;

let SUM_INDICATOR_PAIR = prove
 (`!s P Q. FINITE s
           ==> sum s (\n:num. (if P n then &1 else &0) *
                              (if Q n then &1 else &0)) =
               &(CARD {n | n IN s /\ P n /\ Q n})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum s (\n:num. if P n /\ Q n then &1 else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    BETA_TAC THEN ASM_CASES_TAC `(P:num->bool) n` THEN
    ASM_CASES_TAC `(Q:num->bool) n` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT; REAL_MUL_RID]]);;

let DIVIDES_ADDH_CONG = prove
 (`!d h p. ~(d = 0) ==> (d divides p + h <=> (p == d - h MOD d) (mod d))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(p == d - h MOD d) (mod d) <=> (p + h == (d - h MOD d) + h) (mod d)`
  SUBST1_TAC THENL [REWRITE_TAC[CONG_ADD_RCANCEL_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(d - h MOD d) + h = d * (h DIV d + 1)` SUBST1_TAC THENL
   [MP_TAC(SPECL [`h:num`; `d:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`h DIV d`,`q:num`) THEN SPEC_TAC(`h MOD d`,`r:num`) THEN
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC;
    CONV_TAC NUMBER_RULE]);;

(* ------------------------------------------------------------------------- *)
(* Elementary facts shared by several files of Sieve/.                       *)
(* ------------------------------------------------------------------------- *)

let E_BOUNDS = prove
 (`&2718 / &1000 <= exp(&1) /\ exp(&1) <= &2719 / &1000`,
  MP_TAC E_APPROX_32 THEN REAL_ARITH_TAC);;

let EXP_1_LE_3 = prove
 (`exp(&1) <= &3`,
  MP_TAC E_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let REAL_LE_DIV_BOTH = prove
 (`!a b c d. &0 <= a /\ a <= b /\ &0 < d /\ d <= c ==> a / c <= b / d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_LE_INV2; REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC);;

let CARD_NUM_LE_REAL = prove
 (`!X. &0 <= X ==> &(CARD {m | 1 <= m /\ &m <= X}) <= X`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `X:real` FLOOR_POS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  MP_TAC(SPEC `X:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{m | 1 <= m /\ &m <= X} = 1..M` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN AP_TERM_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN SUBGOAL_THEN `&m < &M + &1` MP_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC];
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC];
    ASM_REWRITE_TAC[CARD_NUMSEG_1]]);;

let FINITE_PRIMES_LE_RESTRICT = prove
 (`!x P. FINITE {p | prime p /\ p <= x /\ P p}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..x` THEN
  REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
  MESON_TAC[]);;

let POLYLOG_EXP_BOUND = prove
 (`!a Cc e. &0 < e ==> ?L0. !L. L0 <= L ==> Cc * L pow a <= exp(e * L)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `c = (e / (&a + &1)) pow (a + 1)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_POW_LT THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `&1 + abs(Cc:real) / c` THEN X_GEN_TAC `L:real` THEN
    DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= abs(Cc:real) / c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= L /\ abs(Cc:real) / c <= L` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real) * L pow (a + 1) <= exp(e * L)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(c:real) * L pow (a + 1) = (e / (&a + &1) * L) pow (a + 1) /\
                  exp(e * L) = exp(e / (&a + &1) * L) pow (a + 1)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[REAL_POW_MUL] THEN
      REWRITE_TAC[GSYM REAL_EXP_N; GSYM REAL_OF_NUM_ADD] THEN
      AP_TERM_TAC THEN
      SUBGOAL_THEN `&0 < &a + &1` MP_TAC THENL
       [REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      MP_TAC(SPEC `e / (&a + &1) * L` REAL_EXP_LE_X) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(c:real) * L pow (a + 1)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(Cc:real) * L pow a` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
  SUBGOAL_THEN `abs(Cc:real) = c * (abs Cc / c)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Rigorous numerical bounds shared by the sieve and circle methods.         *)
(* ------------------------------------------------------------------------- *)

let REAL_EXP_TAYLOR = prove
 (`!n x. abs(exp x - sum(0..n) (\k. x pow k / &(FACT k)))
         <= exp(abs x) * abs x pow (n + 1) / &(FACT n)`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`n:num`; `Cx x`] TAYLOR_CEXP) THEN
  REWRITE_TAC[RE_CX; GSYM CX_EXP; COMPLEX_NORM_CX; GSYM CX_POW;
              GSYM CX_DIV; VSUM_CX; GSYM CX_SUB]);;

let LOG_2_LOWER = prove
 (`&6931 / &10000 <= log(&2)`,
  ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
  SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`] THEN
  MP_TAC(SPECL [`12`; `&6931 / &10000`] REAL_EXP_TAYLOR) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let LOG_2_UPPER = prove
 (`log(&2) <= &13863 / &20000`,
  ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
  SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`] THEN
  MP_TAC(SPECL [`12`; `&13863 / &20000`] REAL_EXP_TAYLOR) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `exp(&13863 / &20000) <= &3` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&1)` THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC E_BOUNDS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let LOG_3_LOWER = prove
 (`&5493 / &5000 <= log(&3)`,
  ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
  SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &3`] THEN
  MP_TAC(SPECL [`14`; `&5493 / &5000`] REAL_EXP_TAYLOR) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let LOG_3_UPPER = prove
 (`log(&3) <= &10987 / &10000`,
  ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
  SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &3`] THEN
  MP_TAC(SPECL [`14`; `&10987 / &10000`] REAL_EXP_TAYLOR) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let LOG_7_LOWER = prove
 (`&19459 / &10000 <= log(&7)`,
  ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
  SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &7`] THEN
  MP_TAC(SPECL [`18`; `&19459 / &10000`] REAL_EXP_TAYLOR) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let LOG_7_UPPER = prove
 (`log(&7) <= &1946 / &1000`,
  ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
  SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &7`] THEN
  MP_TAC(SPECL [`18`; `&1946 / &1000`] REAL_EXP_TAYLOR) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Weighted Cauchy-Schwarz.                                                  *)
(* ------------------------------------------------------------------------- *)

let SUM_WEIGHTED_CS = prove
 (`!(w:A->real) a s.
     FINITE s /\ (!x. x IN s ==> &0 <= w x)
     ==> sum s (\x. w x * a x) pow 2 <= sum s w * sum s (\x. w x * a x pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 <= sum s (\x:A. sum s (\x'. w x * w x' * (a x - a x') pow 2))`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x':A` THEN DISCH_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x x':A. w x * w x' * (a x - a x') pow 2 =
             (w x * a x pow 2) * w x' + w x * (w x' * a x' pow 2) -
             &2 * (w x * a x) * (w x' * a x')`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_SUB; SUM_LMUL; SUM_RMUL; FINITE_RESTRICT] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH
   `!A B C:real. &0 <= A * C + C * A - &2 * B * B ==> B * B <= C * A`));;
