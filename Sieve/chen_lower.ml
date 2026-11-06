(* ========================================================================= *)
(* The lower bound sieve for Chen's theorem ([N] Theorem 10.4).              *)
(*                                                                           *)
(* chen_sieve_ok h: for even N >= 16 the shift h(N) is even with             *)
(* 1 <= h(N) <= N, chen_remainder_ok h holds, and |gchen_A (h N) N| =        *)
(* (1 + o(1)) N / log N.  GOLDBACH_SIEVE_OK: the Goldbach shift h(N) = N     *)
(* satisfies it (BOMBIERI_VINOGRADOV; the size from the prime number         *)
(* theorem, CHEN_A_CARD_LOWER/_UPPER).  Fixed shifts: chen_shift.ml.         *)
(*                                                                           *)
(* CHEN_SIFT_LOWER_GEN: if chen_sieve_ok h, then for 1/8 <= theta <= 1/5     *)
(* and e > 0 every large even N satisfies, with z = N^theta,                 *)
(*   S(A,P,z) >= (f(1/(2 theta)) - e) (N / log N) V(z),                      *)
(* where A = gchen_A (h N) N, V(z) = prod_{p < z} (1 - chen_g (h N) p) and   *)
(* f = sieve_f.                                                              *)
(*                                                                           *)
(* Method: JURKAT_RICHERT (uniform in g) at the level D = Y / P(w), where    *)
(* Y = sqrt N / log^B N and P(w) = prod_{p < w} p, so that the remainder     *)
(* sum runs over d < D P(w) = Y and is o(N V(z) / log N) by                  *)
(* chen_remainder_ok with A = 3 (CHEN_R_ARITH, omega(h) <= log N / log 2);   *)
(* s = log D / log z tends to 1/(2 theta) (CHEN_S_BOUND), f is Lipschitz on  *)
(* [2,4] (SIEVE_F_LIPSCHITZ), and V(z) >> 1 / log z uniformly in h by        *)
(* Mertens' product (CHEN_V_LOWER).                                          *)
(*                                                                           *)
(* CHEN_P4_GEN (theta = 1/5): the sifted numbers other than 1 have all prime *)
(* factors >= N^(1/5), hence between one and four of them (almost_prime k n: *)
(* n is a product of at least one and at most k primes); n = 1 costs at most *)
(* one representation.  Hence                                                *)
(*   GOLDBACH_P4  #{p < N | N - p = P4} >= c N / log^2 N  (N even, large);   *)
(* the forms p + h = P4 are SHIFT_P4 and TWIN_P4 (chen_shift.ml).            *)
(* EVEN_TO_ALL_LOWER passes from even N to all x, and COUNT_LOWER_INFINITE   *)
(* from such a lower bound to an infinite set.                               *)
(* ========================================================================= *)

needs "Sieve/chen_sieve.ml";;
needs "Sieve/dde.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Elementary facts about logarithms.                                        *)
(* ------------------------------------------------------------------------- *)

let SIEVE_MUL_DIV_ASSOC = prove
 (`!x y z:real. x * y / z = (x * y) / z`,
  REWRITE_TAC[real_div; REAL_MUL_ASSOC]);;

let LOG_LE_2_SQRT = prove
 (`!y. &1 <= y ==> log y <= &2 * sqrt y`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`1`; `y:real`] LOG_POW_LE_SQRT) THEN
  ASM_REWRITE_TAC[REAL_POW_1; REAL_MUL_RID]);;

let LOG4_LE_SQRT = prove
 (`!x. &1 <= x ==> log x pow 4 <= &4096 * sqrt x`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`4`; `x:real`] LOG_POW_LE_SQRT) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

let EVENTUALLY_LOG_GE = prove
 (`!Kb. ?N0. !N. N0 <= N ==> Kb <= log(&N)`,
  GEN_TAC THEN MP_TAC(SPEC `exp Kb` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN EXISTS_TAC `M:num` THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&M` THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE]);;

let LOG_SMALL_EVENTUALLY = prove
 (`!Kb e. &0 < e ==> ?N1. !N. N1 <= N ==> Kb * log(&N) pow 2 <= e * &N`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `(&256 * (abs Kb + &1) pow 2) / e pow 2` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN EXISTS_TAC `MAX 1 M` THEN
  X_GEN_TAC `N:num` THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= n <=> a <= n /\ b <= n`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &N /\ &M <= &N` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  MP_TAC(SPEC `&N` LOG_POW4_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(abs Kb + &1) * log(&N) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (abs Kb + &1) * log(&N) pow 2 /\ &0 <= e * &N`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_POW_2; REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`(abs Kb + &1) * log(&N) pow 2`; `e * &N`]
               REAL_LE_SQUARE_ABS) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(abs Kb + &1) pow 2 * (&256 * &N)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(&256 * (abs Kb + &1) pow 2) / e pow 2 <= &M` THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&M * e pow 2) * &N` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(abs Kb + &1) pow 2 * (&256 * &N) =
                  (&256 * (abs Kb + &1) pow 2) * &N` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(&M * e pow 2) * &N = (e pow 2 * &N) * &M /\
                  e pow 2 * &N pow 2 = (e pow 2 * &N) * &N`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The size of A (prime number theorem).                                     *)
(* ------------------------------------------------------------------------- *)

let PI_UPTO_ASYMPTOTIC = prove
 (`!e. &0 < e
       ==> ?N1. !n. N1 <= n
                    ==> (&1 - e) * &n / log(&n) <= &(pi_upto n) /\
                        &(pi_upto n) <= (&1 + e) * &n / log(&n)`,
  REPEAT STRIP_TAC THEN MP_TAC PNT THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN EXISTS_TAC `N2 + 2` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM pi_upto] THEN
  SUBGOAL_THEN `&0 < &n / log(&n)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `u = &n / log(&n)` THEN
  REWRITE_TAC[REAL_ARITH `(&1 - e) * n / l = (&1 - e) * (n / l)`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `abs(x - &1) < e <=> &1 - e < x /\ x < &1 + e`] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC);;

let CHEN_A_CARD_LOWER = prove
 (`!e. &0 < e
       ==> ?N1. !N. N1 <= N
                    ==> (&1 - e) * &N / log(&N) <= &(CARD(chen_A N))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e / &2` PI_UPTO_ASYMPTOTIC) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  MP_TAC(SPECL [`&3`; `e / &2`] LOG_SMALL_EVENTUALLY) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N3:num`) THEN
  EXISTS_TAC `N2 + N3 + 3` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&1 <= log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(exp(&1))` THEN
    CONJ_TAC THENL [REWRITE_TAC[LOG_EXP; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MP_TAC E_BOUNDS THEN
    SUBGOAL_THEN `&3 <= &N` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&N)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&(pi_upto N) <= &(CARD(chen_A N)) +
                    &(CARD {p | prime p /\ p divides N}) + &1`
  ASSUME_TAC THENL
   [REWRITE_TAC[CARD_CHEN_A; pi_upto; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD({p | prime p /\ p < N /\ ~(p divides N)} UNION
                     {p | prime p /\ p divides N} UNION {N})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; IN_SING] THEN
        X_GEN_TAC `x:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_CASES_TAC `(x:num) divides N` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `x <= N:num` THEN ARITH_TAC;
        REWRITE_TAC[FINITE_UNION; FINITE_SING; FINITE_CHEN_PRIMES] THEN
        MATCH_MP_TAC FINITE_PRIME_DIVISORS THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD {p | prime p /\ p < N /\ ~(p divides N)} +
                CARD({p | prime p /\ p divides N} UNION {N})` THEN
    SUBGOAL_THEN `FINITE {p | prime p /\ p divides N}` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_PRIME_DIVISORS THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_UNION_LE; FINITE_UNION; FINITE_SING;
                 FINITE_CHEN_PRIMES; LE_ADD_LCANCEL] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD {p | prime p /\ p divides N} + CARD {N}` THEN
    ASM_SIMP_TAC[CARD_UNION_LE; FINITE_SING; CARD_SING; LE_REFL];
    ALL_TAC] THEN
  MP_TAC(SPEC `N:num` OMEGA_LE_LOG) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&1 / &2 <= log(&2)` ASSUME_TAC THENL
   [REWRITE_TAC[LOG_2_BOUNDS]; ALL_TAC] THEN
  SUBGOAL_THEN `log(&N) / log(&2) <= &2 * log(&N)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < log(&2)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `&0 <= log(&N) * (&2 * log(&2) - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * log(&N) <= e / &2 * &N / log(&N)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `e / &2 * n / l = (e / &2 * n) / l`] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    UNDISCH_TAC `&3 * log(&N) pow 2 <= e / &2 * &N` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`&(pi_upto N) <= &(CARD(chen_A N)) +
                     &(CARD {p | prime p /\ p divides N}) + &1`;
    `(&1 - e / &2) * &N / log(&N) <= &(pi_upto N)`;
    `&(CARD {p | prime p /\ p divides N}) <= log(&N) / log(&2)`;
    `log(&N) / log(&2) <= &2 * log(&N)`;
    `&3 * log(&N) <= e / &2 * &N / log(&N)`; `&1 <= log(&N)`] THEN
  SPEC_TAC(`&(CARD {p | prime p /\ p divides N})`,`w:real`) THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let CHEN_A_CARD_UPPER = prove
 (`!e. &0 < e
       ==> ?N1. !N. N1 <= N
                    ==> &(CARD(chen_A N)) <= (&1 + e) * &N / log(&N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e:real` PI_UPTO_ASYMPTOTIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN EXISTS_TAC `N1:num` THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b c d:real. a <= b ==> (c <= b /\ b <= d) ==> a <= d`) THEN
  REWRITE_TAC[CARD_CHEN_A; pi_upto; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[LT_IMP_LE];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..N` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
    ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The sieve hypotheses for a family of shifts.                              *)
(* ------------------------------------------------------------------------- *)

let chen_sieve_ok = new_definition
 `chen_sieve_ok (h:num->num) <=>
    (!N. EVEN N /\ 16 <= N ==> EVEN(h N) /\ 1 <= h N /\ h N <= N) /\
    chen_remainder_ok h /\
    (!e. &0 < e
         ==> ?N1. !N. EVEN N /\ N1 <= N
                      ==> (&1 - e) * &N / log(&N) <=
                          &(CARD(gchen_A (h N) N)) /\
                          &(CARD(gchen_A (h N) N)) <=
                          (&1 + e) * &N / log(&N))`;;

let GOLDBACH_SIEVE_OK = prove
 (`chen_sieve_ok (\N. N)`,
  REWRITE_TAC[chen_sieve_ok] THEN
  ASM_SIMP_TAC[GOLDBACH_REMAINDER_OK; CHEN_A_GEN] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `e:real` CHEN_A_CARD_LOWER) THEN
  MP_TAC(SPEC `e:real` CHEN_A_CARD_UPPER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `N1 + N2:num` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The product V(z).                                                         *)
(* ------------------------------------------------------------------------- *)

let SIEVE_PRIMES_2 = prove
 (`!z. sieve_primes (&2) z = {p | prime p /\ &p < z}`,
  GEN_TAC THEN REWRITE_TAC[sieve_primes; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_SIMP_TAC[PRIME_GE_2]);;

let CHEN_V_POS = prove
 (`!N z. EVEN N
         ==> &0 < product {p | prime p /\ &p < z} (\p. &1 - chen_g N p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LT THEN
  REWRITE_TAC[FINITE_PRIMES_LT; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `x:num`] CHEN_G_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let CHEN_V_LOWER = prove
 (`?c. &0 < c /\
       !N z. EVEN N /\ &2 <= z
             ==> c / log z <=
                 product {p | prime p /\ &p < z} (\p. &1 - chen_g N p)`,
  X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC CHEN_G_DIMENSION THEN
  SUBGOAL_THEN `&0 < log(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `log(&2) / (&1 + L / log(&2))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `&2`; `z:real`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; SIEVE_PRIMES_2] THEN
  MP_TAC(SPECL [`N:num`; `z:real`] CHEN_V_POS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `V = product {p | prime p /\ &p < z} (\p. &1 - chen_g N p)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < log z /\ &0 < &1 + L / log(&2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
                    ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(log z / log(&2) * (&1 + L / log(&2)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MAP_EVERY UNDISCH_TAC [`&0 < log z`; `&0 < log(&2)`;
                           `&0 < &1 + L / log(&2)`] THEN
    CONV_TAC REAL_FIELD;
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_LT_INV]]);;

(* ------------------------------------------------------------------------- *)
(* The lower sieve function near s = 4.                                      *)
(* ------------------------------------------------------------------------- *)

let SIEVE_F_LIPSCHITZ = prove
 (`!s s0. &2 <= s /\ s <= s0 /\ s0 <= &4
          ==> sieve_f s0 - sieve_A * (s0 - s) <= sieve_f s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= s0 /\ s <= &4` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SIEVE_LOWER_24_EXPLICIT] THEN
  MP_TAC SIEVE_A_GE_3 THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= log(s - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(s0 - &1) <= log(s - &1) + (s0 - s)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (s0 - s) / (s - &1) /\ (s0 - s) / (s - &1) <= s0 - s`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < s - &1` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      SUBGOAL_THEN `&0 <= (s0 - s) * (s - &2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `x = (s0 - s) / (s - &1)` THEN
    SUBGOAL_THEN `s0 - &1 = (s - &1) * (&1 + x)` SUBST1_TAC THENL
     [EXPAND_TAC "x" THEN UNDISCH_TAC `&2 <= s` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `log((s - &1) * (&1 + x)) = log(s - &1) + log(&1 + x)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LOG_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `x:real` LOG_LE) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s /\ &0 < s0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(sieve_A * log(s - &1)) / s0` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_RDISTRIB] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `!a b c:real. a - b <= c <=> a <= c + b`] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sieve_A * (log(s - &1) + (s0 - s))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sieve_A * (s0 - s) * (s0 - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The sieve level and the remainder: real arithmetic.                       *)
(* ------------------------------------------------------------------------- *)

let CHEN_S_BOUND = prove
 (`!theta LN lx B Pw delta.
        &1 / &8 <= theta /\ &2 <= LN /\ &1 <= lx /\ lx <= LN /\
        LN - lx <= &1 /\ &1 <= Pw /\ &0 < delta /\
        (&16 * (&1 / &2 + log Pw)) / delta + ((&32 * &B) / delta) pow 2 + &1
        <= LN
        ==> (lx / &2 - &B * log lx - log Pw) / (theta * LN)
            <= &1 / (&2 * theta) /\
            &1 / (&2 * theta) -
            (lx / &2 - &B * log lx - log Pw) / (theta * LN) <= delta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < theta /\ &0 < LN /\ &0 <= log lx /\ &0 <= log Pw /\
                &0 <= &B` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &B * log lx` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < theta * LN` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / (&2 * theta) -
                (lx / &2 - &B * log lx - log Pw) / (theta * LN) =
                (LN / &2 - (lx / &2 - &B * log lx - log Pw)) / (theta * LN)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < theta`; `&0 < LN`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `g = LN / &2 - (lx / &2 - &B * log lx - log Pw)` THEN
  SUBGOAL_THEN `&0 <= g` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN UNDISCH_TAC `&0 <= &B * log lx` THEN
    UNDISCH_TAC `&0 <= log Pw` THEN UNDISCH_TAC `(lx:real) <= LN` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!a b c:real. &0 <= c /\ b - a = c ==> a <= b`)
    THEN EXISTS_TAC `(g:real) / (theta * LN)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "g" THEN MAP_EVERY UNDISCH_TAC [`&0 < theta`; `&0 < LN`] THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&16 * (&1 / &2 + log Pw)) / delta /\
                &0 <= ((&32 * &B) / delta) pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
                    REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&16 * (&1 / &2 + log Pw)) / delta <= LN /\
                ((&32 * &B) / delta) pow 2 <= LN` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&16 * (&1 / &2 + log Pw) <= delta * LN` ASSUME_TAC THENL
   [UNDISCH_TAC `(&16 * (&1 / &2 + log Pw)) / delta <= LN` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&32 * &B) / delta <= sqrt LN` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&32 * &B <= delta * sqrt LN` ASSUME_TAC THENL
   [UNDISCH_TAC `(&32 * &B) / delta <= sqrt LN` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt LN /\ sqrt LN pow 2 = LN` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC SQRT_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&32 * &B) * sqrt LN <= delta * LN` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(delta * sqrt LN) * sqrt LN` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `log lx <= &2 * sqrt LN` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * sqrt lx` THEN
    ASM_SIMP_TAC[LOG_LE_2_SQRT] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC SQRT_MONO_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&B * log lx <= &B * (&2 * sqrt LN)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `delta * LN / &8 <= delta * (theta * LN)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `d * l / &8 = d * (&1 / &8 * l)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  EXPAND_TAC "g" THEN ASM_REAL_ARITH_TAC);;

let CHEN_R_ARITH = prove
 (`!R Cb W Y Nr LN lx e1 c V.
        &16 <= Nr /\ LN = log Nr /\ LN / &2 <= lx /\ &1 <= lx /\
        &0 < c /\ &0 < e1 /\ c / LN <= V /\ W <= LN / log(&2) /\ &0 <= W /\
        Y <= sqrt Nr /\ &0 <= Y /\
        (&8 * abs Cb + &16384) / (e1 * c) + &1 <= LN /\
        R <= Cb * (Nr - &1) / lx pow 3 + &2 * W * Y
        ==> R <= e1 * (Nr / LN) * V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LN pow 4 <= &4096 * sqrt Nr /\ sqrt Nr pow 2 = Nr /\
                &0 <= sqrt Nr /\ &1 <= LN`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG4_LE_SQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(exp(&1))` THEN
      CONJ_TAC THENL [REWRITE_TAC[LOG_EXP; REAL_LE_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
      MP_TAC E_BOUNDS THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `LN = log Nr` THEN DISCH_THEN(K ALL_TAC) THEN
  ABBREV_TAC `Kc = &8 * abs Cb + &16384` THEN
  SUBGOAL_THEN `&0 < e1 * c /\ &0 < LN /\ &0 < lx /\ &1 <= Nr`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < LN pow 3 /\ &0 < lx pow 3 /\ &0 < LN pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LN pow 3 <= &8 * lx pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&8 * ((LN:real) / &2) pow 3` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_DIV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `Cb * (Nr - &1) / lx pow 3 <= (&8 * abs Cb * Nr) / LN pow 3`
  ASSUME_TAC THENL
   [REWRITE_TAC[SIEVE_MUL_DIV_ASSOC] THEN ASM_SIMP_TAC[RAT_LEMMA4] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(abs Cb * Nr) * (LN:real) pow 3` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!c x y:real. abs(c * x) <= y ==> c * x <= y`) THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH
       `(&8 * c * n) * l:real = (c * n) * (&8 * l)`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `W <= &2 * LN` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `LN / log(&2)` THEN
    ASM_REWRITE_TAC[] THEN MP_TAC LOG_2_BOUNDS THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 / &2 <= x ==> &0 < x`] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= LN * (&2 * l - &1) ==> LN <= (&2 * LN) * l:real`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * W * Y <= (&16384 * Nr) / LN pow 3` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&4 * sqrt Nr * LN pow 4` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH
       `&4 * s * (LN:real) pow 4 = (&2 * (&2 * LN) * s) * LN pow 3`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&4 * sqrt Nr * (&4096 * sqrt Nr)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `sqrt Nr pow 2 = Nr` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Kc <= LN * (e1 * c)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(Kc * Nr) / LN pow 3 <= ((e1 * c) * Nr) / LN pow 2`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RAT_LEMMA4] THEN
    REWRITE_TAC[REAL_ARITH
     `((e * c) * n) * (l:real) pow 3 = (l * (e * c)) * (n * l pow 2)`;
     REAL_ARITH `(k * n) * (l:real) pow 2 = k * (n * l pow 2)`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((e1 * c) * Nr) / LN pow 2 <= e1 * (Nr / LN) * V`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e1 * ((Nr:real) / LN) * (c / LN)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < LN` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`R <= Cb * (Nr - &1) / lx pow 3 + &2 * W * Y`;
    `Cb * (Nr - &1) / lx pow 3 <= (&8 * abs Cb * Nr) / LN pow 3`;
    `&2 * W * Y <= (&16384 * Nr) / LN pow 3`;
    `(Kc * Nr) / LN pow 3 <= ((e1 * c) * Nr) / LN pow 2`;
    `((e1 * c) * Nr) / LN pow 2 <= e1 * (Nr / LN) * V`] THEN
  EXPAND_TAC "Kc" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The lower bound ([N] Theorem 10.4).                                       *)
(* ------------------------------------------------------------------------- *)

let CHEN_SIFT_LOWER_GEN = prove
 (`!h. chen_sieve_ok h
       ==> !theta e.
         &1 / &8 <= theta /\ theta <= &1 / &5 /\ &0 < e
         ==> ?N0. !N. EVEN N /\ N0 <= N
                      ==> (sieve_f(&1 / (&2 * theta)) - e) * &N / log(&N) *
                          product {p | prime p /\ &p < exp(theta * log(&N))}
                                  (\p. &1 - chen_g (h N) p)
                          <= sifted (gchen_A (h N) N) (\n. &1)
                               {p | prime p /\ &p < exp(theta * log(&N))}`,
  GEN_TAC THEN REWRITE_TAC[chen_sieve_ok; chen_remainder_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h")
    (CONJUNCTS_THEN2 (LABEL_TAC "rem") (LABEL_TAC "card"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < theta` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&5 / &2 <= &1 / (&2 * theta) /\ &1 / (&2 * theta) <= &4`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `!a b:real. &0 <= b - a ==> a <= b`) THENL
     [SUBGOAL_THEN `&1 / (&2 * theta) - &5 / &2 =
                    (&1 - &5 * theta) / (&2 * theta)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < theta` THEN CONV_TAC REAL_FIELD;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&4 - &1 / (&2 * theta) =
                    (&8 * theta - &1) / (&2 * theta)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < theta` THEN CONV_TAC REAL_FIELD;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `s0 = &1 / (&2 * theta)` THEN
  SUBGOAL_THEN `!N z. EVEN N /\ 16 <= N
                      ==> &0 <= &N / log(&N) *
                               product {p | prime p /\ &p < z}
                                       (\p. &1 - chen_g ((h:num->num) N) p) /\
                          &0 <= sifted (gchen_A (h N) N) (\n. &1)
                                       {p | prime p /\ &p < z}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "h" (MP_TAC o SPEC `N:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ASM_ARITH_TAC;
        ASM_SIMP_TAC[CHEN_V_POS; REAL_LT_IMP_LE]];
      REWRITE_TAC[sifted] THEN MATCH_MP_TAC SUM_POS_LE THEN
      REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  ASM_CASES_TAC `sieve_f s0 - e <= &0` THENL
   [EXISTS_TAC `16` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ARITH `x <= &0 <=> &0 <= --x`] THEN
      REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC SIEVE_A_GE_3 THEN DISCH_TAC THEN
  SUBGOAL_THEN `sieve_f s0 <= sieve_A` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SIEVE_LOWER_24_EXPLICIT; REAL_ARITH
      `&5 / &2 <= s ==> &2 <= s`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&5 / &2 <= s ==> &0 < s`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `!a b:real. a < b ==> a <= b`) THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `s0 - &1` THEN
    CONJ_TAC THENL [MATCH_MP_TAC LOG_LT_X THEN ASM_REAL_ARITH_TAC;
                    ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "rem" (MP_TAC o SPEC `3`) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:num` (X_CHOOSE_THEN `Cb:real`
    (LABEL_TAC "remB"))) THEN
  X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC CHEN_G_DIMENSION THEN
  MP_TAC(SPECL [`L:real`; `e / &4`] JURKAT_RICHERT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
  X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC CHEN_V_LOWER THEN
  ABBREV_TAC `Pw = &(nproduct {p | prime p /\ &p < w} (\p. p))` THEN
  SUBGOAL_THEN `&1 <= Pw` ASSUME_TAC THENL
   [EXPAND_TAC "Pw" THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN REWRITE_TAC[FINITE_PRIMES_LT] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  ABBREV_TAC `e1 = e / &4` THEN
  ABBREV_TAC `delta = e1 / sieve_A` THEN
  SUBGOAL_THEN `&0 < e1 /\ &0 < delta /\ delta <= &1 / &2 /\
                sieve_A * delta = e1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["delta"; "e1"] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&3 <= a ==> &0 < a`] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `ep = e1 / (sieve_A + &1)` THEN
  SUBGOAL_THEN `&0 < ep /\ ep * sieve_f s0 <= e1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ep" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `e1 / (sieve_A + &1) * (sieve_A + &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  USE_THEN "card" (MP_TAC o SPEC `ep:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  MP_TAC(SPEC `(&8 * abs(&2 * abs Cb) + &16384) / (e1 * c) + &1`
    EVENTUALLY_LOG_GE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  MP_TAC(SPEC `(&16 * (&1 / &2 + log Pw)) / delta +
               ((&32 * &B) / delta) pow 2 + &1` EVENTUALLY_LOG_GE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N3:num`) THEN
  MP_TAC(SPEC `log w / theta + &1` EVENTUALLY_LOG_GE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N4:num`) THEN
  EXISTS_TAC `N1 + N2 + N3 + N4 + 16` THEN
  X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "h" (MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&16 <= &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= log(&N)` ASSUME_TAC THENL
   [MP_TAC E_BOUNDS THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log(exp(&1) * exp(&1))` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD; LOG_EXP] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 * &3` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `LN = log(&N)` THEN
  ABBREV_TAC `z = exp(theta * LN)` THEN
  SUBGOAL_THEN `log z = theta * LN /\ w <= z /\ &2 <= z` STRIP_ASSUME_TAC
  THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[LOG_EXP] THEN
    SUBGOAL_THEN `w <= exp(theta * LN)` (fun th -> REWRITE_TAC[th] THEN
      ASSUME_TAC th) THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log w)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN
        UNDISCH_TAC `log w / theta + &1 <= LN` THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH
          `l / t + &1 <= x <=> l / t <= x - &1`] THEN
        SUBGOAL_THEN `&0 <= theta` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `V = product {p | prime p /\ &p < z} (\p. &1 - chen_g
              ((h:num->num) N) p)`
  THEN
  SUBGOAL_THEN `c / LN <= V /\ &0 < V` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c / log z` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
        EXPAND_TAC "V" THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `c:real`)) (concl th) &&
          is_forall(concl th))) THEN
        ASM_REWRITE_TAC[]];
      EXPAND_TAC "V" THEN ASM_SIMP_TAC[CHEN_V_POS]];
    ALL_TAC] THEN
  ABBREV_TAC `X = &(CARD(gchen_A ((h:num->num) N) N))` THEN
  SUBGOAL_THEN `&0 < sqrt(&N) / LN pow B /\
                sqrt(&N) / LN pow B <= sqrt(&N) /\
                log(sqrt(&N) / LN pow B) = LN / &2 - &B * log LN`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= LN pow B /\ &0 < sqrt(&N)` STRIP_ASSUME_TAC
    THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < LN pow B /\ &0 < LN /\ &0 < &N`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ; LOG_DIV; LOG_POW; LOG_SQRT] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `Y = sqrt(&N) / LN pow B` THEN
  SUBGOAL_THEN `&0 < Pw /\ &0 <= Y /\ log(Y / Pw) = log Y - log Pw`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `D = (Y:real) / Pw` THEN
  SUBGOAL_THEN `&0 < D /\ D * Pw = Y` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&1 <= Pw` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `log D = LN / &2 - &B * log LN - log Pw`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `log D = log Y - log Pw` THEN DISCH_THEN(K ALL_TAC) THEN
  UNDISCH_TAC `log Y = LN / &2 - &B * log LN` THEN
  DISCH_THEN(K ALL_TAC) THEN
  ABBREV_TAC `s = log D / (theta * LN)` THEN
  SUBGOAL_THEN `s <= s0 /\ s0 - s <= delta` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s"; "s0"] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) = `log D`)) THEN
    MATCH_MP_TAC CHEN_S_BOUND THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_SUB_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= s /\ sieve_f s0 - e1 <= sieve_f s` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sieve_f s0 - sieve_A * (s0 - s)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `!a b c:real. b <= c ==> a - c <= a - b`) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sieve_A * delta` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC SIEVE_F_LIPSCHITZ THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `chen_g ((h:num->num) N)` o check (fun th ->
    can (find_term ((=) `sieve_F`)) (concl th))) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[CHEN_G_BOUNDS];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `L:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`gchen_A ((h:num->num) N) N`; `\n:num. &1`;
   `X:real`;
                             `D:real`; `z:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POS; FINITE_GCHEN_A] THEN
    EXPAND_TAC "X" THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[ASSUME `log z = theta * LN`; ASSUME `D * Pw = Y:real`;
              ASSUME `log D / (theta * LN) = s`; ASSUME `&2 <= s`;
              ASSUME `product {p | prime p /\ &p < z}
                              (\p. &1 - chen_g ((h:num->num) N) p) = V`] THEN
  ABBREV_TAC `R = sum {t | t SUBSET {p | prime p /\ &p < z} /\
                           &(nproduct t (\p. p)) < Y}
                      (\t. abs(sieve_count (gchen_A ((h:num->num) N) N)
                                           (\n. &1) t -
                               X * product t (chen_g (h N))))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `R <= e1 * (&N / LN) * V` ASSUME_TAC THENL
   [ASM_CASES_TAC `&1 <= Y` THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
       [EXPAND_TAC "R" THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `t:num->bool` THEN
        REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        SUBGOAL_THEN `1 <= nproduct t (\p:num. p)` MP_TAC THENL
         [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
          SUBGOAL_THEN `FINITE (t:num->bool)` ASSUME_TAC THENL
           [MATCH_MP_TAC FINITE_SUBSET THEN
            EXISTS_TAC `{p | prime p /\ &p < z}` THEN
            ASM_REWRITE_TAC[FINITE_PRIMES_LT];
            ALL_TAC] THEN
          ASM_SIMP_TAC[NPRODUCT_EQ_0] THEN
          REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `q:num` THEN
          ASM_CASES_TAC `(q:num) IN t` THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `t SUBSET {p | prime p /\ &p < z}` THEN
          REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
          DISCH_THEN(MP_TAC o SPEC `q:num`) THEN ASM_REWRITE_TAC[] THEN
          MESON_TAC[PRIME_IMP_NZ];
          REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC]]] THEN
    USE_THEN "remB" (MP_TAC o SPECL [`N:num`; `z:real`; `Y:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPEC `(h:num->num) N` OMEGA_LE_LOG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `log(&((h:num->num) N)) <= LN` ASSUME_TAC THENL
     [EXPAND_TAC "LN" THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `Y <= sqrt(&N)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CHEN_R_ARITH THEN
    MAP_EVERY EXISTS_TAC
     [`&2 * abs Cb`; `&(CARD {p | prime p /\ p divides (h:num->num) N})`;
      `Y:real`;
      `LN:real`; `c:real`] THEN
    ASM_REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `log(&((h:num->num) N)) / log(&2)` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
      MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH
       `!r a b d:real. r <= a + d /\ a <= b ==> r <= b + d`) THEN
      EXISTS_TAC `Cb * &N / LN pow 3` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < LN pow 3` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SIEVE_MUL_DIV_ASSOC] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs Cb * &N` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        ONCE_REWRITE_TAC[REAL_ARITH
         `(&2 * c) * (n - &1) = c * (&2 * n - &2)`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `Q = &N / LN * V` THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((&1 - ep) * (sieve_f s0 - &2 * e1)) * Q <=
                X * V * (sieve_f s - e1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `X * V * (sieve_f s0 - &2 * e1)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `((&1 - ep) * (sieve_f s0 - &2 * e1)) * Q =
                    ((&1 - ep) * (&N / LN)) * (V * (sieve_f s0 - &2 * e1))`
      SUBST1_TAC THENL [EXPAND_TAC "Q" THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [EXPAND_TAC "X" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((&1 - ep) * (sieve_f s0 - &2 * e1)) * Q - e1 * Q` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_SUB_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= ep * e1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`ep * sieve_f s0 <= e1`; `e / &4 = e1`] THEN
    REAL_ARITH_TAC;
    MAP_EVERY UNDISCH_TAC
     [`R <= e1 * Q`;
      `X * V * (sieve_f s - e1) - R <=
       sifted (gchen_A ((h:num->num) N) N) (\n. &1) {p | prime p /\ &p < z}`;
      `((&1 - ep) * (sieve_f s0 - &2 * e1)) * Q <=
       X * V * (sieve_f s - e1)`] THEN
    SPEC_TAC(`sifted (gchen_A ((h:num->num) N) N) (\n. &1)
                     {p | prime p /\ &p < z}`,
             `S:real`) THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Almost primes; every large even number is p + P4.                         *)
(* ------------------------------------------------------------------------- *)

let almost_prime = new_definition
 `almost_prime k n <=>
    ?l. ~(l = []) /\ ALL prime l /\ LENGTH l <= k /\ ITLIST ( * ) l 1 = n`;;

let PRIME_FACTORIZATION_LIST = prove
 (`!n. ~(n = 0) ==> ?l. ALL prime l /\ ITLIST ( * ) l 1 = n`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 1` THENL
   [EXISTS_TAC `[]:num list` THEN ASM_REWRITE_TAC[ALL; ITLIST]; ALL_TAC] THEN
  MP_TAC(SPEC `n:num` PRIME_FACTOR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  SUBGOAL_THEN `~(m = 0) /\ m < n` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `2 <= p` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
    ASM_CASES_TAC `m = 0` THENL
     [UNDISCH_TAC `n = p * (m:num)` THEN ASM_REWRITE_TAC[MULT_CLAUSES];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `m = 1 * m`] THEN
    ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `CONS (p:num) l` THEN ASM_REWRITE_TAC[ALL; ITLIST]);;

let ITLIST_MUL_LOWER = prove
 (`!z l. &0 <= z /\ (!q. MEM q l ==> z <= &q)
         ==> z pow (LENGTH l) <= &(ITLIST ( * ) l 1)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; ITLIST; LENGTH; real_pow; REAL_LE_REFL] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
  ASM_MESON_TAC[]);;

let ALMOST_PRIME_LARGE_FACTORS = prove
 (`!k n z. ~(n = 0) /\ ~(n = 1) /\ &1 <= z /\ &n < z pow (k + 1) /\
           (!q. prime q /\ q divides n ==> z <= &q)
           ==> almost_prime k n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[almost_prime] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_FACTORIZATION_LIST) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `l:num list` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `ITLIST ( * ) l 1 = n` THEN
    ASM_REWRITE_TAC[ITLIST] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `~(k + 1 <= a) ==> a <= k`) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`z:real`; `l:num list`] ITLIST_MUL_LOWER) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[ALL_MEM];
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC ITLIST_MUL_DIVIDES THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`k + 1`; `LENGTH(l:num list)`; `z:real`] REAL_POW_MONO) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CHEN_P4_GEN = prove
 (`!h. chen_sieve_ok h
       ==> ?c N0. &0 < c /\
                  !N. EVEN N /\ N0 <= N
                      ==> c * &N / log(&N) pow 2 <=
                          &(CARD {n | n IN gchen_A (h N) N /\
                                      almost_prime 4 n})`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sieve_f(&5 / &2)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&5 / &2` SIEVE_LOWER_24_EXPLICIT) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MP_TAC SIEVE_A_GE_3 THEN REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`&1 / &5`; `sieve_f(&5 / &2) / &2`] o
    MATCH_MP CHEN_SIFT_LOWER_GEN) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  X_CHOOSE_THEN `c0:real` STRIP_ASSUME_TAC CHEN_V_LOWER THEN
  ABBREV_TAC `cc = c0 * &5 * sieve_f(&5 / &2) / &4` THEN
  SUBGOAL_THEN `&0 < cc` ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&1`; `cc:real`] LOG_SMALL_EVENTUALLY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  EXISTS_TAC `cc:real` THEN EXISTS_TAC `N1 + N2 + 32` THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `EVEN((h:num->num) N)` ASSUME_TAC THENL
   [UNDISCH_TAC `chen_sieve_ok h` THEN REWRITE_TAC[chen_sieve_ok] THEN
    DISCH_THEN(MP_TAC o SPEC `N:num` o CONJUNCT1) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num` o check (fun th ->
    can (find_term ((=) `sifted`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&5 * log(&2) <= log(&N) /\ &0 < log(&N)` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THENL
     [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `LN = log(&N)` THEN
  SUBGOAL_THEN `&2 <= exp(&1 / &5 * LN) /\ exp(&1 / &5 * LN) pow 5 = &N /\
                log(exp(&1 / &5 * LN)) = LN / &5`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log(&2))` THEN
      CONJ_TAC THENL
       [SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`; REAL_LE_REFL];
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[GSYM REAL_EXP_N] THEN
      SUBGOAL_THEN `&5 * &1 / &5 * LN = LN` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "LN" THEN MATCH_MP_TAC EXP_LOG THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      REWRITE_TAC[LOG_EXP] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `z = exp(&1 / &5 * LN)` THEN
  ABBREV_TAC
   `V = product {p | prime p /\ &p < z} (\p. &1 - chen_g ((h:num->num) N) p)`
  THEN
  SUBGOAL_THEN `&5 * c0 / LN <= V` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c0 / log z` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < LN` THEN CONV_TAC REAL_FIELD;
      EXPAND_TAC "V" THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `c0:real`)) (concl th) &&
        is_forall(concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= cc * &N / LN pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < LN pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SIEVE_MUL_DIV_ASSOC] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    USE_THEN "N2" (MP_TAC o SPEC `N:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[REAL_MUL_LID]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!b s. a + &1 <= b /\ b <= s /\ s <= k + &1 ==> a <= k`) THEN
  MAP_EVERY EXISTS_TAC
   [`(sieve_f(&5 / &2) - sieve_f(&5 / &2) / &2) * &N / LN * V`;
    `sifted (gchen_A ((h:num->num) N) N) (\n. &1)
            {p | prime p /\ &p < z}`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(sieve_f(&5 / &2) - sieve_f(&5 / &2) / &2) * &N / LN *
                (&5 * c0 / LN)` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `(sieve_f(&5 / &2) - sieve_f(&5 / &2) / &2) * &N / LN *
        (&5 * c0 / LN) = &2 * (cc * &N / LN pow 2)`
      SUBST1_TAC THENL
       [EXPAND_TAC "cc" THEN UNDISCH_TAC `&0 < LN` THEN
        CONV_TAC REAL_FIELD;
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[sifted] THEN
  SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_GCHEN_A; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD({n | n IN gchen_A ((h:num->num) N) N /\
                        almost_prime 4 n} UNION {1})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; IN_SING] THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `n IN gchen_A ((h:num->num) N) N` THEN
      REWRITE_TAC[gchen_A; IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC ALMOST_PRIME_LARGE_FACTORS THEN EXISTS_TAC `z:real` THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
        X_GEN_TAC `q:num` THEN STRIP_TAC THEN
        REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN
        ASM_REWRITE_TAC[IN_ELIM_THM]];
      SIMP_TAC[FINITE_UNION; FINITE_SING; FINITE_RESTRICT; FINITE_GCHEN_A]];
    MP_TAC(ISPECL [`{n | n IN gchen_A ((h:num->num) N) N /\
                         almost_prime 4 n}`; `{1}`] CARD_UNION_LE) THEN
    SIMP_TAC[FINITE_SING; FINITE_RESTRICT; FINITE_GCHEN_A; CARD_SING]]);;

let GOLDBACH_P4 = prove
 (`?c N0. &0 < c /\
          !N. EVEN N /\ N0 <= N
              ==> c * &N / log(&N) pow 2 <=
                  &(CARD {p | prime p /\ p < N /\ almost_prime 4 (N - p)})`,
  MP_TAC(MATCH_MP CHEN_P4_GEN GOLDBACH_SIEVE_OK) THEN
  REWRITE_TAC[CHEN_A_GEN] THEN
  SUBGOAL_THEN
   `!N. &(CARD {n | n IN chen_A N /\ almost_prime 4 n}) <=
        &(CARD {p | prime p /\ p < N /\ almost_prime 4 (N - p)})`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`N:num`; `almost_prime 4`] SUM_CHEN_A) THEN
    SIMP_TAC[SUM_CONST; FINITE_RESTRICT; GSYM CHEN_A_GEN; FINITE_GCHEN_A;
             REAL_MUL_RID] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_CHEN_PRIMES; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[REAL_LE_TRANS]);;

let EVEN_TO_ALL_LOWER = prove
 (`!f:num->real c N0.
     &0 < c /\ (!m n. m <= n ==> f m <= f n) /\
     (!N. EVEN N /\ N0 <= N ==> c * &N / log(&N) pow 2 <= f N)
     ==> ?c' N1. &0 < c' /\
                 !x. N1 <= x ==> c' * &x / log(&x) pow 2 <= f x`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`c / &2`; `N0 + 4`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  ABBREV_TAC `N = 2 * x DIV 2` THEN
  SUBGOAL_THEN `EVEN N /\ N0 <= N /\ N <= x /\ x <= N + 1 /\ 3 <= N`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[EVEN_DOUBLE] THEN
    MP_TAC(SPECL [`x:num`; `2`] DIVISION) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:num->real) N` THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c * &N / log(&N) pow 2` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `&0 < log(&N) /\ log(&N) <= log(&x) /\ &x <= &2 * &N`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&N) pow 2 /\ log(&N) pow 2 <= log(&x) pow 2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&x) pow 2` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LTE_TRANS]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[MESON[real_div; REAL_MUL_ASSOC]
   `!a b c:real. a * b / c = (a * b) / c`] THEN
  ASM_SIMP_TAC[RAT_LEMMA4] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LE_MUL; REAL_POS;
               REAL_ARITH `&0 < c ==> &0 <= c / &2`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c / &2 * (&2 * &N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let COUNT_LOWER_INFINITE = prove
 (`!s:num->bool c x0.
     &0 < c /\
     (!x. x0 <= x ==> c * &x / log(&x) pow 2 <= &(CARD {p | p IN s /\ p <= x}))
     ==> INFINITE s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[INFINITE] THEN DISCH_TAC THEN
  MP_TAC(SPEC `c:real` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num` o
    SPEC `&16 * (&(CARD(s:num->bool)) + &1)`) THEN
  ABBREV_TAC `x = x0 + n * n + 3` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN
  ANTS_TAC THENL [EXPAND_TAC "x" THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `CARD {p | p IN s /\ p <= x} <= CARD(s:num->bool)` MP_TAC
  THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[GSYM REAL_OF_NUM_LE]] THEN
  SUBGOAL_THEN `&3 <= &x /\ &n * &n <= &x` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&x) pow 2 <= &16 * sqrt(&x) /\ &0 < log(&x) pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`2`; `&x`] LOG_POW_LE_SQRT) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC LOG_POS_LT THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&n <= sqrt(&x) /\ &0 < sqrt(&x) /\ sqrt(&x) pow 2 = &x`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW_2] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `c * sqrt(&x) / &16 <= c * &x / log(&x) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[RAT_LEMMA4; REAL_ARITH `&0 < &16`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&x) * &16 * sqrt(&x)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      UNDISCH_TAC `sqrt(&x) pow 2 = &x` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(CARD(s:num->bool)) + &1 <= c * sqrt(&x) / &16` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c * &n / &16` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `&16 * (&(CARD(s:num->bool)) + &1) < &n * c` THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ABBREV_TAC `nK = &(CARD {p:num | p IN s /\ &p <= &x})` THEN
    REAL_ARITH_TAC]);;
