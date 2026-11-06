(* ========================================================================= *)
(* Chen's theorem with distinct primes: the P2 can be taken squarefree.      *)
(*   CHEN_DISTINCT:                                                          *)
(*     ?N0. !N. EVEN N /\ N0 <= N                                            *)
(*              ==> ?p q. prime p /\                                         *)
(*                        (prime q \/                                        *)
(*                         ?q1 q2. prime q1 /\ prime q2 /\ ~(q1 = q2) /\     *)
(*                                 q = q1 * q2) /\                           *)
(*                        p + q = N                                          *)
(*   CHEN_TWIN_DISTINCT: there are infinitely many primes p such that p + 2  *)
(*   is a prime or a product of two distinct primes.                         *)
(* Also the counting forms CHEN_GOLDBACH_SQUAREFREE, CHEN_TWIN_SQUAREFREE    *)
(* and CHEN_SHIFT_SQUAREFREE (at least c x / log^2 x, for every even shift   *)
(* h > 0 in the last), CHEN_SQUAREFREE and the INFINITE forms, all stated    *)
(* with almost_prime 2 n /\ squarefree n; ALMOST_PRIME_2_SQUAREFREE shows    *)
(* that this means "a prime or a product of two distinct primes".            *)
(*                                                                           *)
(* almost_prime k n (chen_lower.ml) counts prime factors with multiplicity,  *)
(* as Nathanson ("the product of at most r not necessarily distinct prime    *)
(* numbers") and Halberstam-Richert ("at most r prime factors, equal or      *)
(* distinct") do, so q^2 is a P2.  Method: no new sieve argument.  A P2      *)
(* that is not squarefree is q^2 (ALMOST_PRIME_2_NOT_SQUAREFREE), and p + h  *)
(* (or N - p, with x = N and h = 0) is a square for at most sqrt(x + h) of   *)
(* the primes p <= x (CARD_SQUARE_PARAM), while CHEN_GOLDBACH, CHEN_TWIN     *)
(* and CHEN_SHIFT give at least c x / log^2 x, which exceeds 2 sqrt(x + h)   *)
(* for large x (SQRT_SMALL_X_LOG2, CARD_LOWER_SPLIT).                        *)
(* ========================================================================= *)

needs "Sieve/chen.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Squarefree almost-primes of order 2.                                      *)
(* ------------------------------------------------------------------------- *)

let ALMOST_PRIME_2_SQUAREFREE = prove
 (`!n. almost_prime 2 n /\ squarefree n <=>
       prime n \/ ?q1 q2. prime q1 /\ prime q2 /\ ~(q1 = q2) /\ n = q1 * q2`,
  GEN_TAC THEN REWRITE_TAC[ALMOST_PRIME_2] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`p:num`; `q:num`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `squarefree n` THEN ASM_REWRITE_TAC[SQUAREFREE_MUL] THEN
    ASM_MESON_TAC[COPRIME_PRIME_PRIME];
    STRIP_TAC THEN ASM_SIMP_TAC[PRIME_IMP_SQUAREFREE] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SQUAREFREE_MUL; PRIME_IMP_SQUAREFREE; COPRIME_PRIME_PRIME]]);;

let ALMOST_PRIME_2_NOT_SQUAREFREE = prove
 (`!n. almost_prime 2 n /\ ~squarefree n ==> ?q. prime q /\ n = q * q`,
  GEN_TAC THEN REWRITE_TAC[ALMOST_PRIME_2] THEN STRIP_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_SQUAREFREE];
    EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~squarefree n` THEN
    ASM_SIMP_TAC[SQUAREFREE_MUL; PRIME_IMP_SQUAREFREE;
                 COPRIME_PRIME_PRIME] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Few shifted primes are squares of primes.                                 *)
(* ------------------------------------------------------------------------- *)

let CARD_SQUARE_PARAM = prove
 (`!s:num->bool f y.
     (!p. p IN s ==> ?q. 1 <= q /\ q * q <= y /\ p = f q)
     ==> FINITE s /\ &(CARD s) <= sqrt(&y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `Q = {m | 1 <= m /\ &m <= sqrt(&y)}` THEN
  SUBGOAL_THEN `FINITE(Q:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p:num | &p < sqrt(&y) + &1}` THEN
    REWRITE_TAC[FINITE_NUM_LT_REAL; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:num->bool) SUBSET IMAGE (f:num->num) Q` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Q" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN
    ASM_REWRITE_TAC[REAL_POW_2; REAL_OF_NUM_MUL; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(s:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_IMAGE]; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(CARD(Q:num->bool))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(IMAGE (f:num->num) Q)` THEN
    ASM_SIMP_TAC[CARD_IMAGE_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC[FINITE_IMAGE];
    EXPAND_TAC "Q" THEN MATCH_MP_TAC CARD_NUM_LE_REAL THEN
    MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_POS]]);;

let SQRT_SMALL_X_LOG2 = prove
 (`!c a. &0 < c
         ==> ?x0. !x. x0 <= x ==> sqrt(&x + &a) <= c * &x / log(&x) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `(&16384 / c pow 2) pow 2` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  EXISTS_TAC `N1 + a + 3` THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&3 <= &x /\ &a <= &x /\ &N1 <= &x` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t = sqrt(&x)` THEN
  SUBGOAL_THEN `&0 < t /\ (t:real) pow 2 = &x /\ &16384 / c pow 2 <= t`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `L = log(&x)` THEN
  SUBGOAL_THEN `&0 < L /\ (L:real) pow 4 <= &4096 * t` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["L"; "t"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG4_LE_SQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * (t:real)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (L:real) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `c * &x / (L:real) pow 2 = (c * &x) / L pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&16384 <= (c:real) pow 2 * t` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (c:real) pow 2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    UNDISCH_TAC `&16384 / c pow 2 <= t` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (L:real) pow 2 <= c * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&2 * (L:real) pow 2) pow 2 = &4 * L pow 4 /\
                  (c * (t:real)) pow 2 = t * (c pow 2 * t)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(t:real) * &16384` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * t) * (L:real) pow 2 = t * (&2 * L pow 2) /\
                c * &x = (t:real) * (c * t)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [CONV_TAC REAL_RING;
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check
        (fun th -> concl th = `t pow 2 = &x`)) THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Goldbach form.                                                        *)
(* ------------------------------------------------------------------------- *)

let CARD_LOWER_SPLIT = prove
 (`!s sd t:num->bool b e.
     FINITE sd /\ FINITE t /\ s SUBSET sd UNION t /\
     &(CARD t) <= e /\ b <= &(CARD s)
     ==> b - e <= &(CARD sd)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CARD(s:num->bool) <= CARD(sd:num->bool) + CARD(t:num->bool)`
  MP_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD((sd:num->bool) UNION t)` THEN
    ASM_SIMP_TAC[CARD_UNION_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC[FINITE_UNION];
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
    ASM_REAL_ARITH_TAC]);;

let CHEN_GOLDBACH_SQUAREFREE = prove
 (`?c N0. &0 < c /\
          !N. EVEN N /\ N0 <= N
              ==> c * &N / log(&N) pow 2 <=
                  &(CARD {p | prime p /\ p < N /\ almost_prime 2 (N - p) /\
                              squarefree(N - p)})`,
  X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC)
    CHEN_GOLDBACH THEN
  MP_TAC(SPECL [`c / &2`; `0`] SQRT_SMALL_X_LOG2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  MAP_EVERY EXISTS_TAC [`c / &2`; `N0 + N1:num`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{p | prime p /\ p < N /\ ?q. prime q /\ N - p = q * q}`;
                 `\q:num. N - q * q`; `N:num`] CARD_SQUARE_PARAM) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `q:num` THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    UNDISCH_TAC `N - p = q * q:num` THEN UNDISCH_TAC `p < N:num` THEN
    SPEC_TAC(`q * q:num`, `m:num`) THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`{p | prime p /\ p < N /\ almost_prime 2 (N - p)}`;
    `{p | prime p /\ p < N /\ almost_prime 2 (N - p) /\ squarefree(N - p)}`;
    `{p | prime p /\ p < N /\ ?q. prime q /\ N - p = q * q}`;
    `c * &N / log(&N) pow 2`; `sqrt(&N)`] CARD_LOWER_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p:num | p < N}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
      MESON_TAC[ALMOST_PRIME_2_NOT_SQUAREFREE];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID] THEN
  SPEC_TAC(`&(CARD {p | prime p /\ p < N /\ almost_prime 2 (N - p) /\
                        squarefree(N - p)})`, `cd:real`) THEN
  REAL_ARITH_TAC);;

let CHEN_SQUAREFREE = prove
 (`?N0. !N. EVEN N /\ N0 <= N
            ==> ?p q. prime p /\ almost_prime 2 q /\ squarefree q /\
                      p + q = N`,
  X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC)
    CHEN_GOLDBACH_SQUAREFREE THEN
  EXISTS_TAC `N0 + 2` THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c * &N / log(&N) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC LOG_POS_LT THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `S = {p | prime p /\ p < N /\ almost_prime 2 (N - p) /\
                       squarefree(N - p)}` THEN
  ASM_CASES_TAC `S:num->bool = {}` THENL
   [ASM_REWRITE_TAC[CARD_CLAUSES] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  REPEAT DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`p:num`; `N - p:num`] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let CHEN_DISTINCT = prove
 (`?N0. !N. EVEN N /\ N0 <= N
            ==> ?p q. prime p /\
                      (prime q \/
                       ?q1 q2. prime q1 /\ prime q2 /\ ~(q1 = q2) /\
                               q = q1 * q2) /\
                      p + q = N`,
  REWRITE_TAC[GSYM ALMOST_PRIME_2_SQUAREFREE; GSYM CONJ_ASSOC] THEN
  ACCEPT_TAC CHEN_SQUAREFREE);;

(* ------------------------------------------------------------------------- *)
(* The twin and shifted forms.                                               *)
(* ------------------------------------------------------------------------- *)

let SHIFT_SQUAREFREE_COUNT = prove
 (`!h c x0.
     &0 < c /\
     (!x. x0 <= x
          ==> c * &x / log(&x) pow 2 <=
              &(CARD {p | prime p /\ p <= x /\ almost_prime 2 (p + h)}))
     ==> ?x1. !x. x1 <= x
                  ==> c / &2 * &x / log(&x) pow 2 <=
                      &(CARD {p | prime p /\ p <= x /\
                                  almost_prime 2 (p + h) /\
                                  squarefree(p + h)})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c / &2`; `h:num`] SQRT_SMALL_X_LOG2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `x2:num`) THEN
  EXISTS_TAC `x0 + x2:num` THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{p | prime p /\ p <= x /\ ?q. prime q /\ p + h = q * q}`;
                 `\q:num. q * q - h`; `x + h:num`] CARD_SQUARE_PARAM) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `q:num` THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    UNDISCH_TAC `p + h = q * q:num` THEN UNDISCH_TAC `p <= x:num` THEN
    SPEC_TAC(`q * q:num`, `m:num`) THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`{p | prime p /\ p <= x /\ almost_prime 2 (p + h)}`;
    `{p | prime p /\ p <= x /\ almost_prime 2 (p + h) /\ squarefree(p + h)}`;
    `{p | prime p /\ p <= x /\ ?q. prime q /\ p + h = q * q}`;
    `c * &x / log(&x) pow 2`; `sqrt(&x + &h)`] CARD_LOWER_SPLIT) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_ADD]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..x` THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
      MESON_TAC[LE_0];
      REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
      MESON_TAC[ALMOST_PRIME_2_NOT_SQUAREFREE];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`&(CARD {p | prime p /\ p <= x /\ almost_prime 2 (p + h) /\
                        squarefree(p + h)})`, `cd:real`) THEN
  REAL_ARITH_TAC);;

let CHEN_TWIN_SQUAREFREE = prove
 (`?c x0. &0 < c /\
          !x. x0 <= x
              ==> c * &x / log(&x) pow 2 <=
                  &(CARD {p | prime p /\ p <= x /\ almost_prime 2 (p + 2) /\
                              squarefree(p + 2)})`,
  X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `x0:num` STRIP_ASSUME_TAC)
    CHEN_TWIN THEN
  MP_TAC(SPECL [`2`; `c:real`; `x0:num`] SHIFT_SQUAREFREE_COUNT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `x1:num`) THEN
  MAP_EVERY EXISTS_TAC [`c / &2`; `x1:num`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CHEN_TWIN_SQUAREFREE_INFINITE = prove
 (`INFINITE {p | prime p /\ almost_prime 2 (p + 2) /\ squarefree(p + 2)}`,
  X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `x0:num` STRIP_ASSUME_TAC)
    CHEN_TWIN_SQUAREFREE THEN
  MATCH_MP_TAC COUNT_LOWER_INFINITE THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `x0:num`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN CONV_TAC TAUT);;

let CHEN_TWIN_DISTINCT = prove
 (`INFINITE {p | prime p /\
                 (prime(p + 2) \/
                  ?q1 q2. prime q1 /\ prime q2 /\ ~(q1 = q2) /\
                          p + 2 = q1 * q2)}`,
  REWRITE_TAC[GSYM ALMOST_PRIME_2_SQUAREFREE; GSYM CONJ_ASSOC] THEN
  ACCEPT_TAC CHEN_TWIN_SQUAREFREE_INFINITE);;

let CHEN_SHIFT_SQUAREFREE = prove
 (`!h. EVEN h /\ ~(h = 0)
       ==> ?c x0. &0 < c /\
                  !x. x0 <= x
                      ==> c * &x / log(&x) pow 2 <=
                          &(CARD {p | prime p /\ p <= x /\
                                      almost_prime 2 (p + h) /\
                                      squarefree(p + h)})`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `x0:num`
    STRIP_ASSUME_TAC) o MATCH_MP CHEN_SHIFT) THEN
  MP_TAC(SPECL [`h:num`; `c:real`; `x0:num`] SHIFT_SQUAREFREE_COUNT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `x1:num`) THEN
  MAP_EVERY EXISTS_TAC [`c / &2`; `x1:num`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CHEN_SHIFT_SQUAREFREE_INFINITE = prove
 (`!h. EVEN h /\ ~(h = 0)
       ==> INFINITE {p | prime p /\ almost_prime 2 (p + h) /\
                         squarefree(p + h)}`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `x0:num`
    STRIP_ASSUME_TAC) o MATCH_MP CHEN_SHIFT_SQUAREFREE) THEN
  MATCH_MP_TAC COUNT_LOWER_INFINITE THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `x0:num`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN CONV_TAC TAUT);;
