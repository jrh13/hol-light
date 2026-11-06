(* ========================================================================= *)
(* Bounded gaps between primes (Zhang 2013) and the Maynard-Tao theorem      *)
(* (Maynard 2013, independently Tao), by Maynard's method at level of        *)
(* distribution 1/2 (from BOMBIERI_VINOGRADOV):                              *)
(*   MAYNARD_TAO: for every m, infinitely many intervals [p, p + H], p       *)
(*   prime, contain at least m primes:                                       *)
(*     !m. ?H. INFINITE {p | prime p /\                                      *)
(*                          m <= CARD {q | prime q /\ p <= q /\ q <= p + H}} *)
(*   explicitly MAYNARD_TAO_EXPLICIT: r + 1 primes with H = k k!,            *)
(*   k = 2^(10^6 r).  The case r = 1:                                        *)
(*   BOUNDED_GAPS:                                                           *)
(*     ?H. INFINITE {p | prime p /\ ?q. prime q /\ p < q /\ q <= p + H}      *)
(*   with BOUNDED_GAPS_EXPLICIT (H = k k!, k = 2^(10^6)) and                 *)
(*   BOUNDED_GAPS_CONSECUTIVE (q the next prime after p).                    *)
(*                                                                           *)
(* Method (files bg_s1, bg_s2, bg_weights, bg_dyadic, bg_assembly).          *)
(* * MAYNARD_FIXED_N: if N satisfies explicit size conditions (in log N and  *)
(*   the constants of Mertens, Titchmarsh and Bombieri-Vinogradov) then some *)
(*   n in [N, 2N) has at least r + 1 primes among n + i k!, i = 1..k.  The   *)
(*   weights are col_weight (maynard_gdy J l0) k on the colourings with      *)
(*   support in P = {p | prime p /\ D0 < p /\ p < R} and support product < R *)
(*   = N^(1/5), l0 = log R / (Kp k); then sum_m S2(m) > r S1                 *)
(*   (MANY_PRIMES_WEIGHTS).  The ratio of the main terms is about            *)
(*   theta (J - 1)^2 / (3 K Kp), theta = 1/5, which grows linearly in J      *)
(*   for Kp = 960 J (as Maynard's M_k grows like log k).                     *)
(*   D0 is a fixed constant: every D0-dependent error carries the factor c0  *)
(*   to the same power as the main term.                                     *)
(* * LOG_RANGE, BV_RANGE, N5_LEMMA and N6_LEMMA reduce the N-conditions to   *)
(*   log N large (POLYLOG_EXP_BOUND): MAYNARD_EVENTUALLY.                    *)
(* * D0_CONDITIONS derives the D0-conditions from exp x <= 1 + 2 x.  With    *)
(*   J = 10^6 r, Kp = 960 J, k = 2^J, K <= 3 (TITCHMARSH_K_LE_3) and A, B, C *)
(*   from BOMBIERI_VINOGRADOV, infinitely many N give MAYNARD_TAO_EXPLICIT.  *)
(* ========================================================================= *)

needs "Sieve/bg_assembly.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Many primes for one large N.                                              *)
(* ------------------------------------------------------------------------- *)

let MAYNARD_FIXED_N = prove
 (`!r Kt M2 J Kp k D0 A B Cb E N L R l0 W c0 PW s q1 M.
     ((\n. product {p | prime p /\ p <= n}
                   (\p. &1 + inv(&p * (&p - &1)))) ---> Kt) sequentially /\
     (!D0 R. 2 <= D0 /\ &D0 < R
             ==> product {p | prime p /\ D0 < p /\ &p < R}
                         (\p. &1 + inv(&p - &1))
                 <= product {p | prime p /\ p <= D0} (\p. &1 - inv(&p)) *
                    M2 * log R) /\
     (!x a. 2 <= x /\ (!d. coprime(a d,d))
            ==> sum {d | 1 <= d /\ &d <= sqrt(&x) / log(&x) pow B}
                    (\d. abs(&(pi_ap x d (a d)) - &(pi_upto x) / &(phi d)))
                <= Cb * &x / log(&x) pow A) /\
     &0 <= Cb /\ 1 <= r /\ 1 <= J /\ 2 <= k /\ 2 * 2 EXP J <= Kp * k /\
     &320 * Kt * &J <= &Kp /\ &300 * &r * Kt * &Kp <= (&J - &1) pow 2 /\
     2 <= D0 /\ k <= D0 /\
     &19 / &20 <= &1 - (&k - &1) pow 2 * (&2 / &D0) -
                  &2 * (&k - &1) * (&2 / &D0) /\
     &10 * (&4 * q1) pow k * (exp(&k pow 2 * (&2 / &D0)) - &1) <= &1 /\
     &8 * q1 * (&4 * q1) pow k *
     (exp(&k * (&2 / &D0)) * (exp(&3 * &k pow 2 * (&2 / &D0)) - &1))
     <= &Kp /\
     log(&N) = L /\ exp(L / &5) = R /\ log R / (&Kp * &k) = l0 /\
     nproduct {p | prime p /\ p <= D0} (\p. p) = W /\
     product {p | prime p /\ p <= D0} (\p. &1 - inv(&p)) = c0 /\
     product {p | prime p /\ p <= D0} (\p. &p - &1) = PW /\
     c0 * l0 = s /\ M2 * &Kp * &k = q1 /\ L pow E = M /\
     &1 + log(&W) <= l0 /\ &D0 < R /\ R <= &N /\ &0 < L /\
     2 * k * FACT k + 2 <= N /\
     (!h0. h0 <= k * FACT k
           ==> &N / (&4 * L) <=
               &(pi_upto((2 * N + h0) - 1)) - &(pi_upto((N + h0) - 1)) /\
               &(pi_upto((2 * N + h0) - 1)) <= &4 * &N / L) /\
     (!x. N <= x + 1 /\ x <= 3 * N
          ==> 2 <= x /\ &W * R pow 2 <= sqrt(&x) / log(&x) pow B /\
              sqrt(&x) / log(&x) pow B <= &x /\
              &x / log(&x) pow A <= &3 * &2 pow A * &N / L pow A) /\
     &20 * &W * R pow 2 * &4 pow k * (q1 * s) pow (6 * k) <= &N * s pow k /\
     &10 * &W * &4 pow k *
     (&k * (q1 * s) pow (2 * k + 2) *
      (&6 * &2 pow A * M * Cb / L pow A +
       &18 * (q1 * s) pow ((k + 1) EXP 4) / (PW * M))) <= s pow k
     ==> ?n. N <= n /\ n < 2 * N /\
             r + 1 <= CARD {i | i IN 1..k /\ prime(n + i * FACT k)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Wp = {p | prime p /\ p <= D0}` THEN
  ABBREV_TAC `P = {p | prime p /\ D0 < p /\ &p < R}` THEN
  ABBREV_TAC `nu = nproduct {q | prime q /\ k < q /\ q <= D0} (\q. q)` THEN
  ABBREV_TAC `Lam = sum {A | A SUBSET P}
     (\A. maynard_gdy J l0 (nproduct A (\p. p)) *
          product A (\p. inv(&p - &1)))` THEN
  ABBREV_TAC `Gam = sum {A | A SUBSET P}
     (\A. maynard_gdy J l0 (nproduct A (\p. p)) pow 2 *
          product A (\p. inv(&p - &1)))` THEN
  ABBREV_TAC `M1 = sum {A | A SUBSET P}
     (\A. (maynard_gdy J l0 (nproduct A (\p. p)) pow 2 *
           product A (\p. inv(&p - &1))) * log(&(nproduct A (\p. p))))` THEN
  ABBREV_TAC `Q = product P (\p. &1 + inv(&p - &1))` THEN
  ABBREV_TAC `eta = sum P (\p. inv(&p - &1) pow 2)` THEN
  MP_TAC(SPECL [`Kt:real`; `M2:real`; `J:num`; `Kp:num`; `k:num`; `D0:num`;
                `R:real`; `l0:real`; `c0:real`; `P:num->bool`; `Lam:real`;
                `Gam:real`; `M1:real`; `Q:real`;
                `eta:real`] MAYNARD_GDY_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `Kt <= &3 /\ &1 <= Kt` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[TITCHMARSH_K_LE_3; TITCHMARSH_K_GE_1]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(Wp:num->bool) /\ (!p. p IN Wp ==> prime p) /\
                DISJOINT Wp (P:num->bool) /\ (!p. p IN P ==> prime p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Wp" THEN REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
      NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[NOT_LT];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &W` ASSUME_TAC THENL
   [MP_TAC(SPEC `D0:num` DYW_FACTS) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c0 * &W = PW` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["c0"; "W"; "PW"] THEN
    SIMP_TAC[REAL_OF_NUM_NPRODUCT; ASSUME `FINITE(Wp:num->bool)`;
             GSYM PRODUCT_MUL] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [ASM_MESON_TAC[PRIME_GE_2; REAL_OF_NUM_LE]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < PW` ASSUME_TAC THENL
   [UNDISCH_TAC `c0 * &W = PW` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `maynard_hdist (\i. i * FACT k) k P` ASSUME_TAC THENL
   [MATCH_MP_TAC TUPLE_MAYNARD_HDIST THEN EXPAND_TAC "P" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[LET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. &0 <= maynard_gdy J l0 r /\ maynard_gdy J l0 r <= &1`
  ASSUME_TAC THENL
   [REWRITE_TAC[MAYNARD_GDY_POS; MAYNARD_GDY_LE_1]; ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN P ==> 2 <= p /\ &0 <= inv(&p - &1) /\
                              &3 / &p <= &3 * inv(&p - &1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `2 <= p` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `product P (\p. &1 + &k * inv(&p - &1)) <= Q pow k /\
                product P (\p. &1 + &k * &3 / &p) <= Q pow (3 * k) /\
                &0 <= product P (\p. &1 + &k * &3 / &p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_BERNOULLI THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `product P (\p. &1 + &(3 * k) * inv(&p - &1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `p:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
          can (find_term ((=) `&3 / &p`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
          MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC;
          MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
          REWRITE_TAC[REAL_ARITH `(&3 * &k) * x = &k * (&3 * x)`] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]];
        MATCH_MP_TAC PRODUCT_BERNOULLI THEN ASM_SIMP_TAC[]];
      MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`)
      THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`\i. i * FACT k`; `k:num`; `P:num->bool`; `R:real`; `W:num`;
                `nu:num`; `N:num`; `maynard_gdy J l0`] S1_ASSEMBLED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`; GSYM REAL_OF_NUM_LT] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      EXPAND_TAC "W" THEN
      ASM_SIMP_TAC[PRIME_DIVIDES_NPRODUCT_PRIMES] THEN
      EXPAND_TAC "Wp" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      UNDISCH_TAC `(p:num) IN P` THEN EXPAND_TAC "P" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ARITH_TAC;
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&D0` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s / &4 <= Gam /\ Gam <= &4 * Kt * s /\
                s * (&J - &1) <= Lam /\ M1 <= &6 * Kt * &J * s * l0`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "s" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `Q <= q1 * s` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q1"; "s"] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Q /\ &0 <= eta /\ &0 <= M1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Q"; "eta"; "M1"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[] THEN
       REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `A:num->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        MATCH_MP_TAC PRODUCT_POS_LE THEN
        CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
        ASM_MESON_TAC[SUBSET];
        MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
        MATCH_MP_TAC NPRODUCT_POS_LT THEN
        CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
        X_GEN_TAC `p:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `2 <= p` MP_TAC THENL
         [ASM_MESON_TAC[SUBSET]; ARITH_TAC]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= exp(&k pow 2 * eta) - &1 /\
                exp(&k pow 2 * eta) - &1 <= exp(&k pow 2 * (&2 / &D0)) - &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `&k pow 2 * eta` REAL_EXP_LE_X) THEN
      SUBGOAL_THEN `&0 <= &k pow 2 * eta` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
        REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x - &1 <= y - &1`) THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `Q:real`; `Gam:real`; `s:real`; `q1:real`;
                `exp(&k pow 2 * (&2 / &D0)) - &1`; `&N`; `&W`] F4_LEMMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`k:num`; `Q:real`; `Gam:real`; `s:real`; `q1:real`;
                `&N`; `&W`; `R:real`;
                `product P (\p. &1 + &k * &3 / &p)`] F5_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC `&D0` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `&N / &W * (product P (\p. &1 + &k * inv (&p - &1)) *
               (exp (&k pow 2 * eta) - &1)) <=
    &N / &W * (Q pow k * (exp(&k pow 2 * (&2 / &D0)) - &1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`)
    THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS];
    ALL_TAC] THEN
  ABBREV_TAC `U = &N / &W * Gam pow k` THEN
  SUBGOAL_THEN
   `sum {n | N <= n /\ n < 2 * N /\ (n == nu) (mod W)}
      (\n. sum {c | c IN col_set k P /\ &(nproduct (col_supp c) (\p. p)) < R}
             (\c. col_weight (maynard_gdy J l0) k c / product (col_supp c)
                    (\p. &p - &1) *
                  product (col_supp c)
                    (\p. maynard_lfac (\i. i * FACT k) c p n)) pow 2)
    <= U + U / &10 + U / &10`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `&N / &W *
      (Gam pow k +
       product P (\p. &1 + &k * inv (&p - &1)) * (exp (&k pow 2 * eta) - &1))
      + &2 * (R * product P (\p. &1 + &k * &3 / &p)) pow 2` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `E0 = (k + 1) EXP 4` THEN
  ABBREV_TAC `BVu = &N * (&6 * &2 pow A * M * Cb / L pow A +
                          &18 * Q pow E0 / (PW * M))` THEN
  ABBREV_TAC `Wl = Lam pow 2 *
       (Gam pow (k - 1) *
        (&1 - (&k - &1) pow 2 * eta - &2 * (&k - &1) * eta) -
        (&k - &1) * M1 * Gam pow (k - 2) / log (R / maynard_dyx l0 J))` THEN
  ABBREV_TAC `E2 = Q pow (k + 1) * exp(&k * eta) *
                   (exp(&3 * &k pow 2 * eta) - &1)` THEN
  SUBGOAL_THEN `&0 < M /\ &0 <= E2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "M" THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "E2" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MP_TAC(SPEC `&3 * &k pow 2 * eta` REAL_EXP_LE_X) THEN
      SUBGOAL_THEN `&0 <= &3 * &k pow 2 * eta` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ARITH `&0 <= &3`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&5 * &Kp * &k * l0 = L` ASSUME_TAC THENL
   [SUBGOAL_THEN `log R = L / &5` MP_TAC THENL
     [EXPAND_TAC "R" THEN REWRITE_TAC[LOG_EXP]; ALL_TAC] THEN
    UNDISCH_TAC `log R = &Kp * &k * l0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&19 / &20 <= &1 - (&k - &1) pow 2 * eta - &2 * (&k - &1) * eta`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 - (&k - &1) pow 2 * (&2 / &D0) -
                &2 * (&k - &1) * (&2 / &D0)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 <= &k` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b /\ c <= d ==> &1 - b - d <= &1 - a - c`)
    THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`r:num`; `k:num`; `Lam:real`; `Gam:real`; `M1:real`;
                `log(R / maynard_dyx l0 J)`;
                `&1 - (&k - &1) pow 2 * eta - &2 * (&k - &1) * eta`;
                `s:real`; `Kt:real`; `J:num`; `Kp:num`; `l0:real`; `&N`; `&W`;
                `PW:real`; `L:real`; `c0:real`] F1_MAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < U` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `U <= &r * U` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Wl` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &k * &N / (&4 * L * PW)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`&0`; `Wl:real`; `&k * &N / (&4 * L * PW)`]
                 REAL_LE_LMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. m IN 1..k
        ==> &N / (&4 * L * PW) * Wl - &4 * &N / (L * PW) * E2 -
            Q pow (2 * k + 2) * BVu <=
            sum {n | n IN {n | N <= n /\ n < 2 * N /\ (n == nu) (mod W)} /\
                     prime(n + m * FACT k)}
                (\n. sum {c | c IN col_set k P /\
                              &(nproduct (col_supp c) (\p. p)) < R}
                       (\c. col_weight (maynard_gdy J l0) k c /
                            product (col_supp c) (\p. &p - &1) *
                            product (col_supp c)
                              (\p. maynard_lfac (\i. i * FACT k) c
                                     p n)) pow 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`\i. i * FACT k`; `k:num`; `m:num`; `Wp:num->bool`;
                `P:num->bool`; `nu:num`; `N:num`; `R:real`; `maynard_dyx l0 J`;
                `maynard_gdy J l0`] S2_ASSEMBLED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `p:num` THEN EXPAND_TAC "Wp" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN EXPAND_TAC "nu" THEN MATCH_MP_TAC TUPLE_NU_OK THEN
      ASM_REWRITE_TAC[];
      ASM_ARITH_TAC;
      X_GEN_TAC `p:num` THEN EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
      ASM_MESON_TAC[REAL_LTE_TRANS];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MAYNARD_GDY_MONO THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MAYNARD_GDY_ZERO THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num->num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m * FACT k` o check (fun th ->
    can (find_term ((=) `pi_upto`)) (concl th) && is_forall (concl th))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL] THEN
    UNDISCH_TAC `m IN 1..k` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x2 = (2 * N + m * FACT k) - 1` THEN
  ABBREV_TAC `x1 = (N + m * FACT k) - 1` THEN
  ABBREV_TAC `cc = (&(pi_upto x2) - &(pi_upto x1)) / PW` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&N / (&4 * L * PW) <= cc /\ cc <= &4 * &N / (L * PW)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN
    SUBGOAL_THEN `&N / (&4 * L * PW) = (&N / (&4 * L)) / PW /\
                  &4 * &N / (L * PW) = (&4 * &N / L) / PW`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < PW`; `&0 < L`] THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    MP_TAC(SPEC `pi_upto x1` REAL_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `N <= x2 + 1 /\ x2 <= 3 * N /\ N <= x1 + 1 /\ x1 <= 3 * N`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x1"; "x2"] THEN
    SUBGOAL_THEN `m * FACT k <= k * FACT k` MP_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL] THEN
      UNDISCH_TAC `m IN 1..k` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
    SUBGOAL_THEN
   `!x. N <= x + 1 /\ x <= 3 * N
        ==> sum {t | t SUBSET P /\ &(nproduct t (\p. p)) < R pow 2}
              (\t. (&k + &1) pow (2 * CARD t) *
                   bv_disc x (nproduct (Wp UNION t) (\p. p))
                          ((a:num->num) (nproduct (Wp UNION t) (\p. p))))
            <= M * Cb * (&3 * &2 pow A * &N / L pow A) +
               &3 * (&3 * &N) / PW * Q pow E0 / M`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `2 <= x /\ &W * R pow 2 <= sqrt(&x) / log(&x) pow B /\
      sqrt(&x) / log(&x) pow B <= &x /\
      &x / log(&x) pow A <= &3 * &2 pow A * &N / L pow A`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`Wp:num->bool`; `P:num->bool`; `k:num`; `R:real`; `x:num`;
                  `a:num->num`; `M:real`; `B:num`; `Cb:real`; `A:num`]
           BV_ASSEMBLED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `product P (\p. &1 + (&k + &1) pow 4 * inv(&p - &1)) <= Q pow E0 /\
      &0 <= product P (\p. &1 + (&k + &1) pow 4 * inv(&p - &1))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "Q" THEN EXPAND_TAC "E0" THEN
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW] THEN
        MATCH_MP_TAC PRODUCT_BERNOULLI THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ARITH `&0 <= &3`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ]];
    ALL_TAC] THEN
    ABBREV_TAC
   `Sg = sum {t | t SUBSET P /\ &(nproduct t (\p. p)) < R pow 2}
     (\t. (&k + &1) pow (2 * CARD t) *
          (bv_disc x2 (nproduct (Wp UNION t) (\p. p))
                  ((a:num->num) (nproduct (Wp UNION t) (\p. p))) +
           bv_disc x1 (nproduct (Wp UNION t) (\p. p))
                  (a (nproduct (Wp UNION t) (\p. p)))))` THEN
  SUBGOAL_THEN `&0 <= Sg /\ Sg <= BVu` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `FINITE {t | t SUBSET P /\ &(nproduct t (\p:num. p)) < R pow 2}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{t:num->bool | t SUBSET P}`
      THEN SIMP_TAC[FINITE_POWERSET; ASSUME `FINITE(P:num->bool)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Sg" THEN MATCH_MP_TAC SUM_POS_LE THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      SIMP_TAC[REAL_LE_ADD; BV_DISC_POS; REAL_POW_LE;
               REAL_ARITH `&0 <= &k + &1`];
      ALL_TAC] THEN
    EXPAND_TAC "Sg" THEN
    SIMP_TAC[REAL_ADD_LDISTRIB; SUM_ADD; ASSUME
      `FINITE {t | t SUBSET P /\ &(nproduct t (\p:num. p)) < R pow 2}`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * (M * Cb * (&3 * &2 pow A * &N / L pow A) +
                      &3 * (&3 * &N) / PW * Q pow E0 / M)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a <= c /\ b <= c ==> a + b <= &2 * c`) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN EXPAND_TAC "BVu" THEN
      MAP_EVERY UNDISCH_TAC [`&0 < PW`; `&0 < M`; `&0 < L`] THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
    SUBGOAL_THEN `(Q * product P (\p. &1 + &k * inv(&p - &1))) pow 2 <=
                Q pow (2 * k + 2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * k + 2 = (k + 1) * 2`; GSYM REAL_POW_POW] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`)
      THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS];
      REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&N / (&4 * L * PW) * Wl - &4 * &N / (L * PW) * E2 <=
                cc * (Wl - E2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b /\ d <= c ==> a - c <= b - d`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_ARITH `&4 * x / y * z = (&4 * x / y) * z`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Q * product P (\p. &1 + &k * inv(&p - &1))) pow 2 * Sg <=
                Q pow (2 * k + 2) * BVu`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!x y. t1 - t2 <= x /\ y <= t3 /\ x - y <= s
                                ==> t1 - t2 - t3 <= s:real`) THEN
  MAP_EVERY EXISTS_TAC
   [`(cc:real) * (Wl - E2)`;
    `(Q * product P (\p. &1 + &k * inv(&p - &1))) pow 2 * Sg`] THEN
  ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `e0 = exp(&k * (&2 / &D0)) *
                   (exp(&3 * &k pow 2 * (&2 / &D0)) - &1)`
  THEN
  SUBGOAL_THEN `E2 <= Q pow (k + 1) * e0` ASSUME_TAC THENL
   [EXPAND_TAC "E2" THEN EXPAND_TAC "e0" THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[]; ALL_TAC]
    THEN MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_POS];
      MP_TAC(SPEC `&3 * &k pow 2 * eta` REAL_EXP_LE_X) THEN
      SUBGOAL_THEN `&0 <= &3 * &k pow 2 * eta` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ARITH `&0 <= &3`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
        REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x - &1 <= y - &1`) THEN
      REWRITE_TAC[REAL_EXP_MONO_LE; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e0` ASSUME_TAC THENL
   [EXPAND_TAC "e0" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MP_TAC(SPEC `&3 * &k pow 2 * (&2 / &D0)` REAL_EXP_LE_X) THEN
    SUBGOAL_THEN `&0 <= &3 * &k pow 2 * (&2 / &D0)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ARITH `&0 <= &3`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `Q:real`; `Gam:real`; `s:real`; `q1:real`;
                `e0:real`; `c0:real`; `l0:real`; `&N`; `&W`; `PW:real`;
                `L:real`; `Kp:num`] F2_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&320 * Kt * &J` THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(SPECL [`k:num`; `Q:real`; `Gam:real`; `s:real`; `q1:real`; `&N`;
                `&W`; `PW:real`; `L:real`; `M:real`; `Cb:real`; `A:num`;
                `E0:num`; `&k * Q pow (2 * k + 2) * BVu`] F3_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "BVu" THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `&k * (&4 * &N / (L * PW) * E2) <= U / &10` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&k * &4 * &N / (L * PW)) * Q pow (k + 1) * e0` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= &k * &4 * &N / (L * PW)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ARITH `&0 <= &4`] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP REAL_LE_LMUL
      (CONJ th (ASSUME `E2 <= Q pow (k + 1) * e0`)))) THEN
    REWRITE_TAC[REAL_MUL_AC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{n | N <= n /\ n < 2 * N /\ (n == nu) (mod W)}`;
    `\n. sum {c | c IN col_set k P /\ &(nproduct (col_supp c) (\p. p)) < R}
           (\c. col_weight (maynard_gdy J l0) k c / product (col_supp c)
                  (\p. &p - &1) *
                product (col_supp c)
                  (\p. maynard_lfac (\i. i * FACT k) c p n)) pow 2`;
    `\i. i * FACT k`; `k:num`; `r:num`] MANY_PRIMES_WEIGHTS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{n:num | n < 2 * N}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&r * (U + U / &10 + U / &10)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `sum (1..k) (\m. &N / (&4 * L * PW) * Wl -
                                &4 * &N / (L * PW) * E2 -
                                Q pow (2 * k + 2) * BVu)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
      MAP_EVERY UNDISCH_TAC
       [`U <= &r * U`; `&3 * &r * U <= (&k * &N / (&4 * L * PW)) * Wl`;
        `&k * Q pow (2 * k + 2) * BVu <= U / &10`;
        `&k * &4 * &N / (L * PW) * E2 <= U / &10`; `&0 < U`] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_NUMSEG]];
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The conditions on N hold for all large N.                                 *)
(* ------------------------------------------------------------------------- *)

let LOG_RANGE = prove
 (`!N x. 4 <= N /\ N <= x + 1 /\ x <= 3 * N /\ &2 <= log(&N)
         ==> log(&N) / &2 <= log(&x) /\ log(&x) <= &2 * log(&N) /\
             &3 <= &x /\ &N / &2 <= &x /\ &x <= &3 * &N`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&4 <= &N /\ &N <= &x + &1 /\ &x <= &3 * &N`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 <= &x /\ &N / &2 <= &x` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `log(&2) <= &1 /\ log(&3) <= &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      MP_TAC(SPEC `&2` REAL_EXP_LE_X) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&N / &2)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[LOG_DIV; REAL_ARITH `&4 <= x ==> &0 < x`;
                   REAL_ARITH `&0 < &2`] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&3 * &N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[LOG_MUL; REAL_ARITH `&4 <= x ==> &0 < x`;
                   REAL_ARITH `&0 < &3`] THEN ASM_REAL_ARITH_TAC]]);;

let SQRT_EXP = prove
 (`!x. sqrt(exp x) = exp(x / &2)`,
  GEN_TAC THEN
  SUBGOAL_THEN `exp x = exp(x / &2) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC POW_2_SQRT THEN REWRITE_TAC[REAL_EXP_POS_LE]]);;

let BV_RANGE = prove
 (`!N x W B A L R.
     4 <= N /\ N <= x + 1 /\ x <= 3 * N /\ log(&N) = L /\ &2 <= L /\
     exp(L / &5) = R /\ &0 < W /\
     sqrt(&2) * W * &2 pow B * L pow B <= exp(L / &10)
     ==> 2 <= x /\ W * R pow 2 <= sqrt(&x) / log(&x) pow B /\
         sqrt(&x) / log(&x) pow B <= &x /\
         &x / log(&x) pow A <= &3 * &2 pow A * &N / L pow A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `x:num`] LOG_RANGE) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `exp L = &N` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC EXP_LOG THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= log(&x)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= log(&x) pow B /\ &1 <= log(&x) pow A /\
                &0 < L pow A /\ &0 < sqrt(&2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_POW_LE_1) THEN
    TRY(MATCH_MP_TAC REAL_POW_LT) THEN ASM_REWRITE_TAC[] THEN
    TRY(MATCH_MP_TAC SQRT_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&x)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS];
      GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP POW_2_SQRT
        (SPEC `x:num` REAL_POS))] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&3 * &2 pow A * &N / L pow A) * (L / &2) pow A` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(&3 * &2 pow A * &N / L pow A) * (L / &2) pow A = &3 * &N`
      SUBST1_TAC THENL
       [REWRITE_TAC[REAL_POW_DIV] THEN
        SUBGOAL_THEN `&0 < &2 pow A` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `&0 < L pow A` THEN CONV_TAC REAL_FIELD;
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]
        THEN MATCH_MP_TAC REAL_LE_MUL THEN
        SIMP_TAC[REAL_POW_LE; REAL_ARITH `&0 <= &2`] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]]] THEN
  SUBGOAL_THEN `sqrt(&N / &2) <= sqrt(&x) /\
                log(&x) pow B <= (&2 * L) pow B /\ &0 < log(&x) pow B`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((W:real) * R pow 2) * (&2 * L) pow B` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&N / &2)` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV)
   [SYM th]) THEN
  REWRITE_TAC[SQRT_DIV; SQRT_EXP] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `exp(L / &2) = exp(L / &10) * R pow 2` SUBST1_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[GSYM REAL_EXP_N; GSYM REAL_EXP_ADD] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= R pow 2` MP_TAC THENL [REWRITE_TAC[REAL_LE_POW_2];
                                             ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_RMUL o CONJ
    (ASSUME `sqrt(&2) * W * &2 pow B * L pow B <= exp(L / &10)`)) THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> b <= c ==> a <= c`) THEN
  REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC);;

let N5_LEMMA = prove
 (`!W q1 sg L k R Nr.
     &0 < W /\ &0 <= q1 /\ &0 < sg /\ &0 < L /\ exp(L / &5) = R /\
     exp L = Nr /\
     &20 * W * &4 pow k * q1 pow (6 * k) * sg pow (5 * k) * L pow (5 * k)
     <= exp(&3 / &5 * L)
     ==> &20 * W * R pow 2 * &4 pow k * (q1 * (sg * L)) pow (6 * k) <=
         Nr * (sg * L) pow k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `R pow 2 = exp(&2 / &5 * L) /\
                Nr = exp(&2 / &5 * L) * exp(&3 / &5 * L)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["R"; "Nr"] THEN
    REWRITE_TAC[GSYM REAL_EXP_N; GSYM REAL_EXP_ADD] THEN
    CONJ_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&20 * W * exp(&2 / &5 * L) * &4 pow k * (q1 * (sg * L)) pow (6 * k) =
    (&20 * W * &4 pow k * q1 pow (6 * k) * sg pow (5 * k) * L pow (5 * k)) *
    (exp(&2 / &5 * L) * (sg * L) pow k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL; ARITH_RULE `6 * k = 5 * k + k`; REAL_POW_ADD]
    THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(exp(&2 / &5 * L) * exp(&3 / &5 * L)) * (sg * L) pow k =
    exp(&3 / &5 * L) * (exp(&2 / &5 * L) * (sg * L) pow k)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
  MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_REAL_ARITH_TAC);;

let N6_LEMMA = prove
 (`!W k q1 sg L Cb A E E0 PW.
     E = E0 + k + 3 /\ A = E + k + 3 /\ 1 <= k /\ &0 < L /\ &0 < sg /\
     &0 <= q1 /\ &0 < PW /\ &0 <= Cb /\ &0 < W /\
     &10 * W * &4 pow k *
     (&k * (q1 * sg) pow (2 * k + 2) *
      (&6 * &2 pow A * Cb + &18 * (q1 * sg) pow E0 / PW)) <= sg pow k * L
     ==> &10 * W * &4 pow k *
         (&k * (q1 * (sg * L)) pow (2 * k + 2) *
          (&6 * &2 pow A * L pow E * Cb / L pow A +
           &18 * (q1 * (sg * L)) pow E0 / (PW * L pow E))) <=
         (sg * L) pow k`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = &10 * W * &4 pow k *
                  (&k * (q1 * sg) pow (2 * k + 2) *
                   (&6 * &2 pow A * Cb + &18 * (q1 * sg) pow E0 / PW))` THEN
  SUBGOAL_THEN `&0 < L pow (k + 3) /\ &0 < L pow (k - 1) /\ &0 < L pow E0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&10 * W * &4 pow k *
    (&k * (q1 * (sg * L)) pow (2 * k + 2) *
     (&6 * &2 pow A * L pow E * Cb / L pow A +
      &18 * (q1 * (sg * L)) pow E0 / (PW * L pow E))) =
    D * L pow (k - 1)`
  SUBST1_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[REAL_POW_MUL] THEN
    SUBGOAL_THEN `(L:real) pow A = L pow E0 * L pow (k + 3) * L pow (k + 3) /\
                  L pow E = L pow E0 * L pow (k + 3) /\
                  L pow (2 * k + 2) = L pow (k - 1) * L pow (k + 3)`
    (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_REWRITE_TAC[GSYM REAL_POW_ADD] THEN REPEAT CONJ_TAC THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < L pow (k + 3)`; `&0 < L pow E0`;
                           `&0 < PW`] THEN
    SPEC_TAC(`(L:real) pow (k + 3)`,`X1:real`) THEN
    SPEC_TAC(`(L:real) pow E0`,`X2:real`) THEN
    SPEC_TAC(`(L:real) pow (k - 1)`,`X3:real`) THEN
    REPEAT GEN_TAC THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `((sg:real) * L) pow k = (sg pow k * L) * L pow (k - 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL] THEN
    SUBGOAL_THEN `(L:real) pow k = L * L pow (k - 1)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let MAYNARD_EVENTUALLY = prove
 (`!r Kt M2 J Kp k D0 A B Cb E.
     ((\n. product {p | prime p /\ p <= n}
                   (\p. &1 + inv(&p * (&p - &1)))) ---> Kt) sequentially /\
     &0 < M2 /\
     (!D0 R. 2 <= D0 /\ &D0 < R
             ==> product {p | prime p /\ D0 < p /\ &p < R}
                         (\p. &1 + inv(&p - &1))
                 <= product {p | prime p /\ p <= D0} (\p. &1 - inv(&p)) *
                    M2 * log R) /\
     (!x a. 2 <= x /\ (!d. coprime(a d,d))
            ==> sum {d | 1 <= d /\ &d <= sqrt(&x) / log(&x) pow B}
                    (\d. abs(&(pi_ap x d (a d)) - &(pi_upto x) / &(phi d)))
                <= Cb * &x / log(&x) pow A) /\
     &0 <= Cb /\ 1 <= r /\ 1 <= J /\ 2 <= k /\ 2 * 2 EXP J <= Kp * k /\
     &320 * Kt * &J <= &Kp /\ &300 * &r * Kt * &Kp <= (&J - &1) pow 2 /\
     2 <= D0 /\ k <= D0 /\
     &19 / &20 <= &1 - (&k - &1) pow 2 * (&2 / &D0) -
                  &2 * (&k - &1) * (&2 / &D0) /\
     &10 * (&4 * (M2 * &Kp * &k)) pow k *
     (exp(&k pow 2 * (&2 / &D0)) - &1) <= &1 /\
     &8 * (M2 * &Kp * &k) * (&4 * (M2 * &Kp * &k)) pow k *
     (exp(&k * (&2 / &D0)) * (exp(&3 * &k pow 2 * (&2 / &D0)) - &1))
     <= &Kp /\
     E = (k + 1) EXP 4 + k + 3 /\ A = E + k + 3
     ==> eventually
          (\N. ?n. N <= n /\ n < 2 * N /\
                   r + 1 <= CARD {i | i IN 1..k /\ prime(n + i * FACT k)})
          sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `W = nproduct {p | prime p /\ p <= D0} (\p. p)` THEN
  ABBREV_TAC `c0 = product {p | prime p /\ p <= D0} (\p. &1 - inv(&p))` THEN
  ABBREV_TAC `PW = product {p | prime p /\ p <= D0} (\p. &p - &1)` THEN
  ABBREV_TAC `q1 = M2 * &Kp * &k` THEN
  ABBREV_TAC `sg = c0 / (&5 * &Kp * &k)` THEN
  ABBREV_TAC `E0 = (k + 1) EXP 4` THEN
  MP_TAC(SPEC `D0:num` DYW_FACTS) THEN MP_TAC(SPEC `D0:num` MERTENS_C0_BOUNDS)
  THEN ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `c0 * &W = PW` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["c0"; "W"; "PW"] THEN
    SIMP_TAC[REAL_OF_NUM_NPRODUCT; FINITE_ATMOST; GSYM PRODUCT_MUL] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [ASM_MESON_TAC[PRIME_GE_2; REAL_OF_NUM_LE]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &Kp /\ &1 <= &k /\ &0 < PW /\ &0 < sg /\ &0 <= q1 /\
                &0 < &W`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &Kp` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&320 * Kt * &J` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&1 <= Kt` MP_TAC THENL
       [ASM_MESON_TAC[TITCHMARSH_K_GE_1]; ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= &J` MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
      REPEAT DISCH_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 <= &k` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `c0 * &W = PW` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "sg" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "q1" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`5 * k`;
                `&20 * &W * &4 pow k * q1 pow (6 * k) * sg pow (5 * k)`;
                `&3 / &5`] POLYLOG_EXP_BOUND) THEN
  REWRITE_TAC[REAL_ARITH `&0 < &3 / &5`] THEN
  DISCH_THEN(X_CHOOSE_TAC `L5:real`) THEN
  MP_TAC(SPECL [`B:num`; `sqrt(&2) * &W * &2 pow B`; `&1 / &10`]
               POLYLOG_EXP_BOUND) THEN
  REWRITE_TAC[REAL_ARITH `&0 < &1 / &10`] THEN
  DISCH_THEN(X_CHOOSE_TAC `Lb:real`) THEN
  ABBREV_TAC `D3 = &10 * &W * &4 pow k *
                   (&k * (q1 * sg) pow (2 * k + 2) *
                    (&6 * &2 pow A * Cb + &18 * (q1 * sg) pow E0 / PW))` THEN
  ABBREV_TAC `Lbig = &2 + &5 * &Kp * &k * (&1 + log(&W)) +
                     &5 * (log(&D0) + &1) + abs L5 + abs Lb +
                     abs(D3 / sg pow k)` THEN
  MP_TAC(SPEC `k * FACT k` PNT_DIFF) THEN
  MP_TAC(SPEC `Lbig:real` EVENTUALLY_LOG_GE_SEQUENTIALLY) THEN
  SUBGOAL_THEN `eventually (\N. 2 * k * FACT k + 4 <= N) sequentially`
  MP_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `N:num` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `L = log(&N)` THEN
  ABBREV_TAC `R = exp(L / &5)` THEN
  ABBREV_TAC `l0 = log R / (&Kp * &k)` THEN
  ABBREV_TAC `s = (c0:real) * l0` THEN
  ABBREV_TAC `M = (L:real) pow E` THEN
  SUBGOAL_THEN `&2 <= L /\ &5 * &Kp * &k * (&1 + log(&W)) <= L /\
                &5 * (log(&D0) + &1) <= L /\ L5 <= L /\ Lb <= L /\
                D3 / sg pow k <= L`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= log(&W)` ASSUME_TAC THENL
     [MP_TAC(SPEC `D0:num` DYW_FACTS) THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`Lbig <= L`] THEN EXPAND_TAC "Lbig" THEN
    SUBGOAL_THEN `&0 <= log(&D0) + &1` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &1`) THEN
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &5 * &Kp * &k * (&1 + log(&W))` MP_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log R = (L:real) / &5` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[LOG_EXP]; ALL_TAC] THEN
  SUBGOAL_THEN `(l0:real) = L / (&5 * &Kp * &k)` ASSUME_TAC THENL
   [EXPAND_TAC "l0" THEN REWRITE_TAC[ASSUME `log R = L / &5`] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < &Kp`; `&1 <= &k`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real) = sg * L` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN EXPAND_TAC "sg" THEN
    REWRITE_TAC[ASSUME `l0 = L / (&5 * &Kp * &k)`] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < &Kp`; `&1 <= &k`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp L = &N` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC EXP_LOG THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`r:num`; `Kt:real`; `M2:real`; `J:num`; `Kp:num`; `k:num`;
                `D0:num`; `A:num`; `B:num`; `Cb:real`; `E:num`; `N:num`;
                `L:real`; `R:real`; `l0:real`; `W:num`; `c0:real`;
                `PW:real`; `s:real`; `q1:real`; `M:real`] MAYNARD_FIXED_N)
  THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < &5 * &Kp * &k` ASSUME_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    EXPAND_TAC "R" THEN
    SUBGOAL_THEN `&D0 = exp(log(&D0))` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXP_LOG THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC];
    EXPAND_TAC "R" THEN REWRITE_TAC[GSYM(ASSUME `exp L = &N`)] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_ARITH_TAC;
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN MATCH_MP_TAC BV_RANGE THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(L:real) / &10 = &1 / &10 * L` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a * b * c * d:real = (a * b * c) * d`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC N5_LEMMA THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `a * b * c * d * e * f:real = (a * b * c * d * e) * f`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(D3:real) <= sg pow k * L` ASSUME_TAC THENL
     [MP_TAC(ASSUME `(D3:real) / sg pow k <= L`) THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; ASSUME `&0 < sg`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(E0 + k + 3) + k + 3 = A` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "M" THEN
    MP_TAC(SPECL [`&W`; `k:num`; `q1:real`; `sg:real`; `L:real`; `Cb:real`;
                  `A:num`; `E:num`; `E0:num`; `PW:real`] N6_LEMMA) THEN
    ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> rand(concl th) = `D3:real`))
      THEN FIRST_ASSUM ACCEPT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The constants; the Maynard-Tao theorem and bounded gaps.                  *)
(* ------------------------------------------------------------------------- *)

let D0_CONDITIONS = prove
 (`!k q1 Kp D0.
     1 <= k /\ &0 <= q1 /\ 1 <= Kp /\ &40 * &k pow 2 <= &D0 /\
     &40 * &k pow 2 * (&4 * q1) pow k <= &D0 /\
     &192 * &k pow 2 * q1 * (&4 * q1) pow k <= &D0
     ==> &19 / &20 <= &1 - (&k - &1) pow 2 * (&2 / &D0) -
                      &2 * (&k - &1) * (&2 / &D0) /\
         &10 * (&4 * q1) pow k * (exp(&k pow 2 * (&2 / &D0)) - &1) <= &1 /\
         &8 * q1 * (&4 * q1) pow k *
         (exp(&k * (&2 / &D0)) * (exp(&3 * &k pow 2 * (&2 / &D0)) - &1))
         <= &Kp`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `X = (&4 * q1) pow k` THEN
  SUBGOAL_THEN `&1 <= &k /\ &1 <= &Kp /\ &0 <= X` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN EXPAND_TAC "X" THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&k <= &k pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &D0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 / &D0 /\ &0 <= &k * (&2 / &D0)` STRIP_ASSUME_TAC
  THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC;
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  ABBREV_TAC `x = &k pow 2 * (&2 / &D0)` THEN
  SUBGOAL_THEN `&0 <= x /\ x <= &1 / &20 /\ X * x <= &1 / &20 /\
                q1 * X * x <= &1 / &96 /\ &k * (&2 / &D0) <= x`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN
    REWRITE_TAC[REAL_ARITH `X * k * (&2 / d) = (&2 * X * k) / d`;
                REAL_ARITH `q * X * k * (&2 / d) = (&2 * q * X * k) / d`;
                REAL_ARITH `k * (&2 / d) = (&2 * k) / d`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LE_DIV2_EQ] THEN
    REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `x:real` REAL_EXP_BOUND_LEMMA) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&10 * X * (&2 * x)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * &k pow 2 * (&2 / &D0) = &3 * x` SUBST1_TAC THENL
   [EXPAND_TAC "x" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(&k * (&2 / &D0)) <= &2 /\ exp(&3 * x) - &1 <= &6 * x /\
                &0 <= exp(&3 * x) - &1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&1 + &2 * (&k * (&2 / &D0))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EXP_BOUND_LEMMA; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `e <= &1 + &2 * (&3 * x) ==> e - &1 <= &6 * x`)
      THEN MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `&3 * x` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&8 * q1 * X * &2 * &6 * x` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]);;

let MAYNARD_TAO_EXPLICIT = prove
 (`!r. 1 <= r
       ==> INFINITE {p | prime p /\
                         r + 1 <= CARD {q | prime q /\ p <= q /\
                                            q <= p + 2 EXP (1000000 * r) *
                                                 FACT(2 EXP (1000000 * r))}}`,
  GEN_TAC THEN DISCH_TAC THEN
  X_CHOOSE_THEN `Kt:real` (ASSUME_TAC o CONJUNCT2) TITCHMARSH_CONSTANT THEN
  X_CHOOSE_THEN `M2:real` STRIP_ASSUME_TAC MERTENS_P_UPPER THEN
  MP_TAC(SPECL [`r:num`; `Kt:real`; `M2:real`; `1000000 * r`;
                `960000000 * r`; `2 EXP (1000000 * r)`]
               MAYNARD_EVENTUALLY) THEN
  MP_TAC(SPEC `1000000 * r` LT_POW2_REFL) THEN
  ABBREV_TAC `k = 2 EXP (1000000 * r)` THEN POP_ASSUM(K ALL_TAC) THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `E = (k + 1) EXP 4 + k + 3` THEN
  ABBREV_TAC `A = E + k + 3` THEN
  MP_TAC BOMBIERI_VINOGRADOV THEN
  DISCH_THEN(X_CHOOSE_THEN `B:num` (X_CHOOSE_TAC `C0:real`) o
             SPEC `A:num`) THEN
  ABBREV_TAC `q1 = M2 * &(960000000 * r) * &k` THEN
  SUBGOAL_THEN `&0 <= q1` ASSUME_TAC THENL
   [EXPAND_TAC "q1" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `&2 + &k + &40 * &k pow 2 + &40 * &k pow 2 * (&4 * q1) pow k +
               &192 * &k pow 2 * q1 * (&4 * q1) pow k` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `D0:num`) THEN
  SUBGOAL_THEN `&0 <= &k pow 2 /\ &0 <= (&4 * q1) pow k` STRIP_ASSUME_TAC
  THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &40 * &k pow 2 * (&4 * q1) pow k /\
                &0 <= &192 * &k pow 2 * q1 * (&4 * q1) pow k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `q1:real`; `960000000 * r`; `D0:num`]
               D0_CONDITIONS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY ASM_ARITH_TAC THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`D0:num`; `A:num`; `B:num`; `abs C0`;
                                `E:num`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(C0:real) * &x / log(&x) pow A` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC LOG_POS THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_ABS_POS];
      ASM_ARITH_TAC;
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP TITCHMARSH_K_LE_3) THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= (&3 - Kt) * &r` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP TITCHMARSH_K_LE_3) THEN DISCH_TAC THEN
      SUBGOAL_THEN `&1 <= &r` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= (&3 - Kt) * (&r * &r) /\ &r <= &r * &r` MP_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_SQUARE] THEN
          ASM_REAL_ARITH_TAC;
          GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
        UNDISCH_TAC `&1 <= &r` THEN REAL_ARITH_TAC];
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; INFINITE; num_FINITE; NOT_EXISTS_THM;
                NOT_FORALL_THM; NOT_IMP; IN_ELIM_THM; NOT_LE] THEN
    DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN X_GEN_TAC `a:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N0 + a + 1`) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `S = {i | i IN 1..k /\ prime(n + i * FACT k)}` THEN
    SUBGOAL_THEN `FINITE(S:num->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `1..k` THEN REWRITE_TAC[FINITE_NUMSEG] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?i0:num. i0 IN S /\ !i. i IN S ==> i0 <= i`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `\i. i IN (S:num->bool)` num_WOP) THEN REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ANTS_TAC THENL
       [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
        UNDISCH_TAC `r + 1 <= CARD(S:num->bool)` THEN
        ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
        MESON_TAC[NOT_LT]];
      ALL_TAC] THEN
    UNDISCH_TAC `(i0:num) IN S` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN STRIP_TAC THEN
    EXISTS_TAC `n + i0 * FACT k` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(S:num->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(IMAGE (\i. n + i * FACT k) (S:num->bool))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC CARD_IMAGE_INJ THEN
      ASM_SIMP_TAC[EQ_ADD_LCANCEL; EQ_MULT_RCANCEL; FACT_NZ];
      ALL_TAC] THEN
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `(i:num) IN S` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[LE_ADD_LCANCEL; GSYM ADD_ASSOC; GSYM RIGHT_ADD_DISTRIB;
                      LE_MULT_RCANCEL] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `0..(n + i0 * FACT k) + k * FACT k` THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
      ARITH_TAC]]);;

let MAYNARD_TAO = prove
 (`!m. ?H. INFINITE {p | prime p /\
                         m <= CARD {q | prime q /\ p <= q /\ q <= p + H}}`,
  GEN_TAC THEN
  EXISTS_TAC `2 EXP (1000000 * (m + 1)) * FACT(2 EXP (1000000 * (m + 1)))`
  THEN MP_TAC(SPEC `m + 1` MAYNARD_TAO_EXPLICIT) THEN
  REWRITE_TAC[ARITH_RULE `1 <= m + 1`] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] INFINITE_SUPERSET)) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[ARITH_RULE `(m + 1) + 1 <= c ==> m <= c`]);;

let BOUNDED_GAPS_EXPLICIT = prove
 (`INFINITE {p | prime p /\
                 ?q. prime q /\ p < q /\
                     q <= p + 2 EXP 1000000 * FACT(2 EXP 1000000)}`,
  MP_TAC(SPEC `1` MAYNARD_TAO_EXPLICIT) THEN
  REWRITE_TAC[LE_REFL; MULT_CLAUSES] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] INFINITE_SUPERSET)) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
  ABBREV_TAC `H = 2 EXP 1000000 * FACT(2 EXP 1000000)` THEN
  POP_ASSUM(K ALL_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `1 + 1 <= CARD {q | prime q /\ p <= q /\ q <= p + H}` THEN
  REWRITE_TAC[NOT_LE; ARITH_RULE `c < 1 + 1 <=> c <= 1`] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {p:num}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REWRITE_TAC[CARD_SING; LE_REFL]]);;

let BOUNDED_GAPS = prove
 (`?H. INFINITE {p | prime p /\ ?q. prime q /\ p < q /\ q <= p + H}`,
  EXISTS_TAC `2 EXP 1000000 * FACT(2 EXP 1000000)` THEN
  ACCEPT_TAC BOUNDED_GAPS_EXPLICIT);;

let BOUNDED_GAPS_CONSECUTIVE = prove
 (`?H. INFINITE {p | prime p /\
                     ?q. prime q /\ p < q /\ q <= p + H /\
                         !r. p < r /\ r < q ==> ~prime r}`,
  X_CHOOSE_TAC `H:num` BOUNDED_GAPS THEN EXISTS_TAC `H:num` THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] INFINITE_SUPERSET)) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `q:num`)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `\r. prime r /\ p < r` num_WOP) THEN REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r0:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[]]);;
