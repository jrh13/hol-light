(* ========================================================================= *)
(* The Hardy-Ramanujan theorem (1917), with Turan's proof (1934): omega(n),  *)
(* the number of distinct prime factors of n, has normal order log log n.    *)
(*                                                                           *)
(* HARDY_RAMANUJAN: for every e > 0                                          *)
(*   #{n <= x | |omega(n) - log log n| >= e log log n} / x ---> 0.           *)
(* TURAN_VARIANCE: for some C and all x >= 4                                 *)
(*   sum_{n <= x} (omega(n) - log log x)^2 <= x (3 log log x + C).           *)
(*                                                                           *)
(* Method.  For n <= x, omega(n) = sum_{p <= x} [p | n]; swapping the sums,  *)
(*   x P - x <= sum_{n <= x} omega(n) <= x P   (OMEGA_SUM_BOUNDS),           *)
(*   sum_{n <= x} omega(n)^2 <= x P^2 + x P     (OMEGA_SQUARE_SUM_BOUND),    *)
(* with P = sum_{p <= x} 1/p, since #{n <= x | p | n, q | n} <= x/(pq) for   *)
(* p <> q (PAIR_MULTIPLES_BOUND).  Mertens' |P - log log x| <= C0            *)
(* (MERTENS_RECIP, primes.ml) gives Turan's bound.  Chebyshev's inequality   *)
(* (CHEBYSHEV_COUNT) bounds the number of n <= x with |omega(n) - log log x| *)
(* >= (e/2) log log x by O(x / log log x); the n <= sqrt x are negligible,   *)
(* and for sqrt x < n <= x, log log n is within log 2 of log log x           *)
(* (HR_BAD_SUBSET).                                                          *)
(* ========================================================================= *)

needs "Sieve/primes.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The first and second moments of omega(n).                                 *)
(* ------------------------------------------------------------------------- *)

let OMEGA_SUM_BOUNDS = prove
 (`!x. &x * sum {p | prime p /\ p <= x} (\p. inv(&p)) - &x <=
       sum(1..x) (\n. &(CARD {p | prime p /\ p divides n})) /\
       sum(1..x) (\n. &(CARD {p | prime p /\ p divides n})) <=
       &x * sum {p | prime p /\ p <= x} (\p. inv(&p))`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `sum(1..x) (\n. &(CARD {p | prime p /\ p divides n})) =
    sum {p | prime p /\ p <= x} (\p. &(CARD {n | n IN 1..x /\ p divides n}))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\n:num p:num. p divides n`; `1..x`;
                   `{p | prime p /\ p <= x}`] SUM_CARD_SWAP) THEN
    REWRITE_TAC[FINITE_NUMSEG; FINITE_ATMOST] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    ASM_CASES_TAC `p divides n` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p <= x:num` (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(SPECL [`p:num`; `n:num`] DIVIDES_LE) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= n:num`; `n:num <= x`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {p | prime p /\ p <= x} (\p. &x * inv(&p) - &1)` THEN
    CONJ_TAC THENL
     [SIMP_TAC[SUM_SUB; FINITE_ATMOST; SUM_CONST] THEN
      MATCH_MP_TAC(REAL_ARITH `b <= c ==> a - c <= a - b * &1`) THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `CARD(1..x)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
        MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
        REWRITE_TAC[CARD_NUMSEG_1; LE_REFL]];
      MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
      X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC CARD_MULTIPLES_GE THEN ASM_MESON_TAC[PRIME_0]];
    MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[GSYM real_div] THEN
    MATCH_MP_TAC CARD_MULTIPLES_LE THEN ASM_MESON_TAC[PRIME_0]]);;

let PAIR_MULTIPLES_BOUND = prove
 (`!x p q. prime p /\ prime q
           ==> &(CARD {n | n IN 1..x /\ p divides n /\ q divides n}) <=
               &x / (&p * &q) + (if q = p then &x / &p else &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0) /\ ~(q = 0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &x / (&p * &q) /\ &0 <= &x / &p` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POS];
    ALL_TAC] THEN
  ASM_CASES_TAC `q:num = p` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ c <= b ==> c <= a + b`) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[CARD_MULTIPLES_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ADD_RID] THEN
  SUBGOAL_THEN `!n. p divides n /\ q divides n <=> (p * q) divides n`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN MATCH_MP_TAC DIVIDES_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC DISTINCT_PRIME_COPRIME THEN ASM_MESON_TAC[];
      MESON_TAC[DIVIDES_TRANS; DIVIDES_RMUL; DIVIDES_LMUL; DIVIDES_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL] THEN MATCH_MP_TAC CARD_MULTIPLES_LE THEN
  ASM_REWRITE_TAC[MULT_EQ_0]);;

let OMEGA_SQUARE_SUM_BOUND = prove
 (`!x. sum(1..x) (\n. &(CARD {p | prime p /\ p divides n}) pow 2) <=
       &x * sum {p | prime p /\ p <= x} (\p. inv(&p)) pow 2 +
       &x * sum {p | prime p /\ p <= x} (\p. inv(&p))`,
  GEN_TAC THEN ABBREV_TAC `P = {p | prime p /\ p <= x}` THEN
  SUBGOAL_THEN `FINITE(P:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[FINITE_ATMOST]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. n IN 1..x
        ==> &(CARD {p | prime p /\ p divides n}) pow 2 =
            sum P (\p. sum P (\q. (if p divides n then &1 else &0) *
                                  (if q divides n then &1 else &0)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_POW_2] THEN
    SUBGOAL_THEN
     `&(CARD {p | prime p /\ p divides n}) =
      sum P (\p. if p divides n then &1 else &0)`
    SUBST1_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC[REAL_MUL_SUM]] THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC[GSYM CARD_EQ_SUM; FINITE_RESTRICT] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "P" THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    ASM_CASES_TAC `p divides n` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p <= x:num` (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(SPECL [`p:num`; `n:num`] DIVIDES_LE) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= n:num`; `n:num <= x`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_EQ_NUMSEG; GSYM IN_NUMSEG] THEN
  MP_TAC(ISPECL
   [`\n:num p:num. sum P (\q. (if p divides n then &1 else &0) *
                              (if q divides n then &1 else &0))`;
    `1..x`; `P:num->bool`] SUM_SWAP) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum P (\p. &x * inv(&p) * sum P (\p. inv(&p)) + &x * inv(&p))`
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:num` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `!q. q IN P ==> prime q` ASSUME_TAC THENL
     [EXPAND_TAC "P" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\n:num q:num. (if p divides n then &1 else &0) *
                      (if q divides n then &1 else &0)`;
      `1..x`; `P:num->bool`] SUM_SWAP) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum P (\q. &x / (&p * &q) + (if q = p then &x / &p else &0))`
    THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `q:num` THEN
      DISCH_TAC THEN SIMP_TAC[SUM_INDICATOR_PAIR; FINITE_NUMSEG] THEN
      MATCH_MP_TAC PAIR_MULTIPLES_BOUND THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[SUM_ADD; SUM_DELTA; GSYM SUM_LMUL] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN BINOP_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[real_div; REAL_INV_MUL] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[real_div]]];
    ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; SUM_RMUL; REAL_POW_2] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Turan's variance bound.                                                   *)
(* ------------------------------------------------------------------------- *)

let TURAN_VARIANCE = prove
 (`?C. !x. 4 <= x
           ==> sum(1..x) (\n. (&(CARD {p | prime p /\ p divides n}) -
                               log(log(&x))) pow 2)
               <= &x * (&3 * log(log(&x)) + C)`,
  X_CHOOSE_TAC `M:real` MERTENS_RECIP THEN
  EXISTS_TAC `(abs M + &50) + (abs M + &50) pow 2` THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= log(&x)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_GE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&x:real`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:num` OMEGA_SUM_BOUNDS) THEN
  MP_TAC(SPEC `x:num` OMEGA_SQUARE_SUM_BOUND) THEN
  SUBGOAL_THEN
   `sum(1..x) (\n. (&(CARD {p | prime p /\ p divides n}) - log(log(&x)))
                   pow 2) =
    sum(1..x) (\n. &(CARD {p | prime p /\ p divides n}) pow 2) -
    &2 * log(log(&x)) *
    sum(1..x) (\n. &(CARD {p | prime p /\ p divides n})) +
    &x * log(log(&x)) pow 2`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_SUB; FINITE_NUMSEG] THEN
    SUBGOAL_THEN `&x * log(log(&x)) pow 2 = sum(1..x) (\n. log(log(&x)) pow 2)`
    SUBST1_TAC THENL [REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB]; ALL_TAC] THEN
    SIMP_TAC[GSYM SUM_ADD; FINITE_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH
     `!a l:real. (a - l) pow 2 = a pow 2 - &2 * l * a + l pow 2`];
    ALL_TAC] THEN
  ABBREV_TAC `L = log(log(&x))` THEN
  ABBREV_TAC `P1 = sum {p | prime p /\ p <= x} (\p. inv(&p))` THEN
  ABBREV_TAC `S1 = sum(1..x) (\n. &(CARD {p | prime p /\ p divides n}))` THEN
  ABBREV_TAC
   `S2 = sum(1..x) (\n. &(CARD {p | prime p /\ p divides n}) pow 2)` THEN
  ABBREV_TAC `C0 = abs M + &50` THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(P1 - L) <= C0` ASSUME_TAC THENL
   [SUBGOAL_THEN `&50 / log(&x) <= &50` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= l ==> &50 <= &50 * l`) THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `L * (&x * P1 - &x) <= L * S1 /\
    &x * (P1 - L) pow 2 <= &x * C0 pow 2 /\
    &x * P1 <= &x * (L + C0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_POS] THENL
     [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_POW2_ABS] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The normal order of omega(n).                                             *)
(* ------------------------------------------------------------------------- *)

let CHEBYSHEV_COUNT = prove
 (`!(s:A->bool) f t.
        FINITE s /\ &0 < t
        ==> &(CARD {n | n IN s /\ t <= abs(f n)}) * t pow 2 <=
            sum s (\n. f n pow 2)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM SUM_CONST; FINITE_RESTRICT] THEN
  REWRITE_TAC[SUM_RESTRICT_SET] THEN MATCH_MP_TAC SUM_LE THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:A` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_REAL_ARITH_TAC);;

let HR_BAD_SUBSET = prove
 (`!e x. &0 < e /\ 16 <= x /\ &2 * (&1 + e) / e <= log(log(&x))
         ==> {n | n IN 1..x /\
                  e * log(log(&n)) <=
                  abs(&(CARD {p | prime p /\ p divides n}) - log(log(&n)))}
             SUBSET
             {n | n IN 1..x /\ &n <= sqrt(&x)} UNION
             {n | n IN 1..x /\
                  e / &2 * log(log(&x)) <=
                  abs(&(CARD {p | prime p /\ p divides n}) - log(log(&x)))}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `&n <= sqrt(&x)` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE; IN_NUMSEG]) THEN
  SUBGOAL_THEN `&1 <= log(&x)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_GE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&x) /\ &0 < &n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&x) / &2 < log(&n)` ASSUME_TAC THENL
   [SIMP_TAC[GSYM LOG_SQRT; REAL_OF_NUM_LT; ARITH_RULE `16 <= x ==> 0 < x`;
             ASSUME `16 <= x`] THEN
    MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `log(log(&x)) - log(&2) < log(log(&n)) /\ log(log(&n)) <= log(log(&x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `log(log(&x)) - log(&2) = log(log(&x) / &2)` SUBST1_TAC
      THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC LOG_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `e * (log(log(&x)) - log(&2)) <= e * log(log(&n)) /\
    e * log(&2) <= e * &1 /\
    e / &2 * (&2 * (&1 + e) / e) <= e / &2 * log(log(&x))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[LOG_2_BOUNDS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `e / &2 * (&2 * (&1 + e) / e) = &1 + e` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`e * log(log(&n)) <=
     abs(&(CARD {p | prime p /\ p divides n}) - log(log(&n)))`;
    `log(log(&x)) - log(&2) < log(log(&n))`;
    `log(log(&n)) <= log(log(&x))`;
    `e * (log(log(&x)) - log(&2)) <= e * log(log(&n))`;
    `e * log(&2) <= e * &1`;
    `e / &2 * (&2 * (&1 + e) / e) <= e / &2 * log(log(&x))`;
    `e / &2 * (&2 * (&1 + e) / e) = &1 + e`] THEN
  MP_TAC LOG_2_BOUNDS THEN
  SPEC_TAC(`&(CARD {p | prime p /\ p divides n})`, `w:real`) THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let HARDY_RAMANUJAN = prove
 (`!e. &0 < e
       ==> ((\x. &(CARD {n | n IN 1..x /\
                            e * log(log(&n)) <=
                            abs(&(CARD {p | prime p /\ p divides n}) -
                                log(log(&n)))}) / &x) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN X_CHOOSE_TAC `C:real` TURAN_VARIANCE THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  ABBREV_TAC `K1 = &3 + abs C` THEN
  SUBGOAL_THEN `&0 < K1` ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `B = &2 * (&1 + e) / e + &8 * K1 / (e pow 2 * d) + &1` THEN
  SUBGOAL_THEN `&0 <= &2 * (&1 + e) / e /\ &0 < e pow 2 * d /\
                &0 <= &8 * K1 / (e pow 2 * d) /\ &0 <= &4 / d pow 2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < e pow 2 * d` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `exp(exp B) + &4 / d pow 2 + &16` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `exp(exp B) + &4 / d pow 2 + &16 <= &x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `16 <= x` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    MP_TAC(SPEC `exp B` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = log(log(&x))` THEN
  SUBGOAL_THEN `B <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log(exp B)` THEN CONJ_TAC THENL
     [REWRITE_TAC[LOG_EXP; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(exp(exp B))` THEN
    CONJ_TAC THENL [REWRITE_TAC[LOG_EXP; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MP_TAC(SPEC `exp B` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= L /\ &2 * (&1 + e) / e <= L /\
                &8 * K1 / (e pow 2 * d) < L`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`e:real`; `x:num`] HR_BAD_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC
   `cA = &(CARD {n | n IN 1..x /\ &n <= sqrt(&x)})` THEN
  ABBREV_TAC
   `cB = &(CARD {n | n IN 1..x /\
                     e / &2 * L <=
                     abs(&(CARD {p | prime p /\ p divides n}) - L)})` THEN
  SUBGOAL_THEN
   `&(CARD {n | n IN 1..x /\
                e * log(log(&n)) <=
                abs(&(CARD {p | prime p /\ p divides n}) - log(log(&n)))})
    <= cA + cB`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["cA"; "cB"] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC
     `CARD({n | n IN 1..x /\ &n <= sqrt(&x)} UNION
           {n | n IN 1..x /\
                e / &2 * L <= abs(&(CARD {p | prime p /\ p divides n}) - L)})`
    THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[FINITE_UNION; FINITE_RESTRICT; FINITE_NUMSEG];
      MATCH_MP_TAC CARD_UNION_LE THEN
      SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG]];
    ALL_TAC] THEN
  SUBGOAL_THEN `cA <= sqrt(&x)` ASSUME_TAC THENL
   [MP_TAC(SPEC `sqrt(&x)` FLOOR_POS) THEN
    SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
    DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
    MP_TAC(SPEC `sqrt(&x)` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&m` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "cA" THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(1..m)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[CARD_NUMSEG_1; LE_REFL]] THEN
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN X_GEN_TAC `n:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&n < &m + &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e / &2 * L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cB * (e / &2 * L) pow 2 <= &x * (&3 * L + C)` ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`1..x`; `\n. &(CARD {p | prime p /\ p divides n}) - L`;
      `e / &2 * L`] CHEBYSHEV_COUNT) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `cB <= d / &2 * &x` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= cB /\ &0 < L` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "cB" THEN REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&x * (&3 * L + C) <= &x * (L * K1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      EXPAND_TAC "K1" THEN
      SUBGOAL_THEN `abs C * &1 <= abs C * L` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `cB * (e pow 2 / &4 * L) <= &x * K1` ASSUME_TAC THENL
     [MP_TAC(SPECL [`cB * (e pow 2 / &4 * L)`; `&x * K1`; `L:real`]
        REAL_LE_RMUL_EQ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN `(cB * (e pow 2 / &4 * L)) * L = cB * (e / &2 * L) pow 2`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`cB * (e / &2 * L) pow 2 <= &x * (&3 * L + C)`;
        `&x * (&3 * L + C) <= &x * (L * K1)`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `cB * (&2 * K1 / d) <= cB * (e pow 2 / &4 * L)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `e pow 2 / &4 * (&8 * K1 / (e pow 2 * d))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        MAP_EVERY UNDISCH_TAC [`&0 < e`; `&0 < d`] THEN CONV_TAC REAL_FIELD;
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
          REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `cB = (cB * (&2 * K1 / d)) * (d / (&2 * K1)) /\
                  d / &2 * &x = (&x * K1) * (d / (&2 * K1))`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < K1`; `&0 < d`] THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&x) < d / &2 * &x` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt(&x) /\ sqrt(&x) * sqrt(&x) = &x`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
        ASM_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_POW_2] THEN SIMP_TAC[SQRT_POW_2; REAL_POS]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 / d < sqrt(&x)` ASSUME_TAC THENL
     [SUBGOAL_THEN `&2 / d = sqrt(&4 / d pow 2)` SUBST1_TAC THENL
       [SUBGOAL_THEN `&4 / d pow 2 = (&2 / d) pow 2` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_MONO_LT THEN
        MP_TAC(SPEC `exp B` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `d / &2 * &2 / d < d / &2 * sqrt(&x) /\
                  d / &2 * &2 / d = &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 * sqrt(&x) < (d / &2 * sqrt(&x)) * sqrt(&x)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `d / &2 * &x = (d / &2 * sqrt(&x)) * sqrt(&x)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &x` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`;
               REAL_ABS_NUM; REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `cA + cB:real` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
