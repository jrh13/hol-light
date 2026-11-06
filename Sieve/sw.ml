(* ========================================================================= *)
(* The Siegel-Walfisz theorem for character sums over primes.                *)
(*                                                                           *)
(* SIEGEL_WALFISZ:                                                           *)
(*   !A B. ?C. !x q c. &2 <= x /\ 1 <= q /\ &q <= log x pow B /\             *)
(*                     dirichlet_character q c /\ ~(c = chi_0 q)             *)
(*                     ==> norm(vsum {p | prime p /\ &p <= x} c) <=          *)
(*                         C * x / log x pow A                               *)
(* (the input of bilinear.ml, bv.ml and the results on progressions).        *)
(*                                                                           *)
(* Method.  PSI1_ZF: PSI1_ESTIMATE (perron.ml) on the zero-free rectangle of *)
(* ZF_RECT (zerofree.ml) bounds psi_1(x,c) = sum_{n<=x} Lambda(n) c(n)       *)
(* (1 - n/x).  Differencing x psi_1(x) with step h gives psi(x,c)            *)
(* (PSI_FROM_PSI1), removing the prime powers gives theta(k,c)               *)
(* (THETA_PSI_DIFF: |psi - theta| <= sqrt k log^2 k), and partial summation  *)
(* gives the sum over primes (PI_FROM_THETA_BOUND, via PI_THETA_NORM in      *)
(* vaughan.ml): SW_PI_BOUND.  Parameters, for u = log x >= 256 and           *)
(* w = u^(1/8): T = floor(w^(16A + 24)) + 1, h = x / u^(A + 1) and           *)
(* kap = k0 q^(-1/(4B)) >= k0 w^-2 with k0 from SIEGEL (e = 1/(4B)).         *)
(* Then Lg^12 <= K w (LG_W_BOUND, ONE_PLUS_LOG_POW), the bound for L'/L is   *)
(* at most KM w^5 and the width of the zero-free region is at least          *)
(* cd w^5 / u (SW_MZ_DZ_BOUNDS), so the term x^(1 - width) is at most        *)
(* x exp(-cd w^5) <= x (m / (cd w^5))^m with m = 7A + 8 (EXP_GE_POW), which  *)
(* beats every power of u (SW_E_TERM, SW_SMALL_TERMS).  For u < 256 the      *)
(* trivial bound 2x (PI_TRIVIAL) suffices.                                   *)
(* ========================================================================= *)

needs "Sieve/perron.ml";;
needs "Sieve/siegel.ml";;
needs "Sieve/zerofree.ml";;
needs "Sieve/vaughan.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* From psi_1(x,c) to the sum over primes.                                   *)
(* ------------------------------------------------------------------------- *)

let PSI1_ZF = prove
 (`!d c Tn kap x Lg.
     dirichlet_character d c /\ ~(c = chi_0 d) /\ 6 <= Tn /\
     &0 < kap /\ kap <= &1 /\
     ((!n. real(c n)) ==> kap <= Re(dseries c (Cx(&1)))) /\
     exp(&1) <= x /\ &1 + log(&(16 * d * (Tn + 4))) = Lg
     ==> norm(vsum {n | 1 <= n /\ &n <= x}
                   (\n. Cx(mangoldt n) * c n * Cx(&1 - &n / x))) <=
         &500 * x * log x pow 2 / &Tn +
         (&10 pow 20 * Lg pow 12 / kap pow 2) * x / &Tn +
         &Tn * (&10 pow 20 * Lg pow 12 / kap pow 2) *
         exp((&1 - kap / (&10 pow 20 * Lg pow 12)) * log x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PSI1_ESTIMATE THEN
  EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 <= Lg` ASSUME_TAC THENL
   [EXPAND_TAC "Lg" THEN REWRITE_TAC[REAL_ARITH `&1 <= &1 + x <=> &0 <= x`]
     THEN
    MATCH_MP_TAC LOG_POS THEN
    REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`;
                MULT_EQ_0; ADD_EQ_0; ARITH_EQ] THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < kap / (&10 pow 20 * Lg pow 12) /\
                kap / (&10 pow 20 * Lg pow 12) <= &1 / &2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= Lg pow 12` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &10 pow 20`;
                   REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&4 <= y ==> &1 <= &1 / &2 * y`) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&10 pow 20 * &1` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:complex` THEN STRIP_TAC THEN
    EXPAND_TAC "Lg" THEN MATCH_MP_TAC ZF_RECT THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let VSUM_TIMES_SCALE = prove
 (`!f z. &0 < z
         ==> vsum {n | 1 <= n /\ &n <= z} (\n. f n * Cx(z - &n)) =
             Cx z * vsum {n | 1 <= n /\ &n <= z}
                         (\n. f n * Cx(&1 - &n / z))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUM_RANGE_LE] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN REWRITE_TAC[CX_SUB; CX_DIV] THEN
  SUBGOAL_THEN `~(Cx z = Cx(&0))` MP_TAC THENL
   [REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC; CONV_TAC COMPLEX_FIELD]);;

let PSI_FROM_PSI1 = prove
 (`!f y h. (!n. 1 <= n ==> norm(f n) <= log(&n)) /\ &1 <= y /\ &0 < h
           ==> norm(vsum {n | 1 <= n /\ &n <= y} f) <=
               ((y + h) * norm(vsum {n | 1 <= n /\ &n <= y + h}
                                  (\n. f n * Cx(&1 - &n / (y + h)))) +
                y * norm(vsum {n | 1 <= n /\ &n <= y}
                              (\n. f n * Cx(&1 - &n / y)))) / h +
               (h + &1) * log(y + h)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `T0 = {n | y < &n /\ &n <= y + h}` THEN
  SUBGOAL_THEN
   `{n | 1 <= n /\ &n <= y + h} = {n | 1 <= n /\ &n <= y} UNION T0 /\
    DISJOINT {n | 1 <= n /\ &n <= y} T0 /\ FINITE T0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN REWRITE_TAC[FINITE_NUM_INTERVAL] THEN
    REWRITE_TAC[EXTENSION; DISJOINT; IN_UNION; IN_INTER; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN
    CONJ_TAC THEN X_GEN_TAC `n:num` THENL
     [ASM_CASES_TAC `&n <= y` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum {n | 1 <= n /\ &n <= y + h}
         (\n. (f:num->complex) n * Cx((y + h) - &n)) =
    vsum {n | 1 <= n /\ &n <= y} (\n. f n * Cx((y + h) - &n)) +
    vsum T0 (\n. f n * Cx((y + h) - &n))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC VSUM_UNION THEN
    ASM_REWRITE_TAC[FINITE_NUM_RANGE_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum {n | 1 <= n /\ &n <= y} (\n. (f:num->complex) n * Cx((y + h) - &n)) =
    vsum {n | 1 <= n /\ &n <= y} (\n. f n * Cx(y - &n)) +
    Cx h * vsum {n | 1 <= n /\ &n <= y} f`
  ASSUME_TAC THENL
   [SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_ADD; FINITE_NUM_RANGE_LE] THEN
    MATCH_MP_TAC VSUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[CX_SUB; CX_ADD] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(vsum T0 (\n. (f:num->complex) n * Cx((y + h) - &n))) <=
    (h + &1) * (log(y + h) * h)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum T0 (\n:num. log(y + h) * h)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "T0" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[NORM_POS_LE];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&n)` THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
        CONJ_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CONST] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [EXPAND_TAC "T0" THEN
      MATCH_MP_TAC(REAL_ARITH `x <= (y + h) - y + &1 ==> x <= h + &1`) THEN
      MATCH_MP_TAC CARD_REAL_INTERVAL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:num->complex`; `y + h:real`] VSUM_TIMES_SCALE) THEN
  MP_TAC(ISPECL [`f:num->complex`; `y:real`] VSUM_TIMES_SCALE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `Ps = vsum {n | 1 <= n /\ &n <= y} (f:num->complex)` THEN
  ABBREV_TAC `W1 = vsum {n | 1 <= n /\ &n <= y}
                        (\n. (f:num->complex) n * Cx(&1 - &n / y))` THEN
  ABBREV_TAC `W2 = vsum {n | 1 <= n /\ &n <= y + h}
                        (\n. (f:num->complex) n * Cx(&1 - &n / (y + h)))` THEN
  ABBREV_TAC `R = vsum T0 (\n. (f:num->complex) n * Cx((y + h) - &n))` THEN
  ABBREV_TAC `A = vsum {n | 1 <= n /\ &n <= y + h}
                       (\n. (f:num->complex) n * Cx((y + h) - &n))` THEN
  ABBREV_TAC `B = vsum {n | 1 <= n /\ &n <= y}
                       (\n. (f:num->complex) n * Cx((y + h) - &n))` THEN
  ABBREV_TAC `C0 = vsum {n | 1 <= n /\ &n <= y}
                        (\n. (f:num->complex) n * Cx(y - &n))` THEN
  SUBGOAL_THEN `Cx h * Ps = Cx(y + h) * W2 - Cx y * W1 - R` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`A = B + R:complex`; `B = C0 + Cx h * Ps`; `C0 = Cx y * W1`;
      `A = Cx(y + h) * W2`] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `h * norm(Ps:complex) <=
                (y + h) * norm(W2:complex) + y * norm(W1:complex) +
                (h + &1) * (log(y + h) * h)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(Cx h * Ps)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < h ==> abs h = h`; REAL_LE_REFL];
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `norm(Cx(y + h) * W2) = (y + h) * norm(W2:complex) /\
                    norm(Cx y * W1) = y * norm(W1:complex)`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
        CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(NORM_ARITH
       `!a b r:complex e A B. norm r <= e /\ norm a = A /\ norm b = B
                              ==> norm(a - b - r) <= A + B + e`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `h:real` THEN
  ASM_REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC);;

let PI_FROM_THETA_BOUND = prove
 (`!N (c:num->complex) Th.
     2 <= N /\
     (!k. 1 <= k /\ k <= N
          ==> norm(vsum(1..k) (\m. Cx(if prime m then log(&m) else &0) * c m))
              <= Th)
     ==> norm(vsum {p | prime p /\ p <= N} c) <= &2 * Th`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Th` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`N:num`; `c:num->complex`] PI_THETA_NORM) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(log(&N + &1)) * Th +
              sum(2..N) (\k. (inv(log(&k)) - inv(log(&k + &1))) * Th)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC LOG_POS THEN
        REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
          ASM_ARITH_TAC;
          MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
          CONJ_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC]];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_RMUL] THEN
  SUBGOAL_THEN `sum(2..N) (\k. inv(log(&k)) - inv(log(&k + &1))) =
                inv(log(&2)) - inv(log(&N + &1))`
  SUBST1_TAC THENL
   [MP_TAC(INST [`\k. inv(log(&k))`,`f:num->real`]
     (SPECL [`2`; `N:num`] SUM_DIFFS)) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD];
    ALL_TAC] THEN
  MP_TAC LOG_2_BOUNDS THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv(log(&2)) <= &2` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `i * t + (j - i) * t = j * t:real`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

let THETA_PSI_DIFF = prove
 (`!q k (c:num->complex). dirichlet_character q c /\ 1 <= k
       ==> norm(vsum(1..k) (\m. Cx(if prime m then log(&m) else &0) * c m) -
                vsum(1..k) (\m. Cx(mangoldt m) * c m))
           <= sqrt(&k) * log(&k) pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VSUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..k) (\m. mangoldt m - (if prime m then log(&m) else &0))`
    THEN
  ASM_SIMP_TAC[PRIME_POWER_SUM_BOUND] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB; GSYM CX_SUB; COMPLEX_NORM_MUL;
              COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN `(if prime m then log(&m) else &0) <= mangoldt m` ASSUME_TAC
    THENL
   [COND_CASES_TAC THEN REWRITE_TAC[MANGOLDT_POS_LE] THEN
    MP_TAC(SPECL [`m:num`; `1`] MANGOLDT_PRIMEPOW) THEN
    ASM_REWRITE_TAC[EXP_1; LE_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((if prime m then log(&m) else &0) - mangoldt m) * &1` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_NORM_LE];
    ASM_REAL_ARITH_TAC]);;

let PSI_SMALL = prove
 (`!k (c:num->complex) q.
     dirichlet_character q c /\ k <= 3
     ==> norm(vsum(1..k) (\m. Cx(mangoldt m) * c m)) <= &6`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..k) (\m. &2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * &1` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `m:num` MANGOLDT_POS_LE) THEN
      MP_TAC(SPEC `m:num` MANGOLDT_LE_LOG) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `&m - &1` LOG_LE) THEN
      REWRITE_TAC[REAL_ARITH `&1 + (x - &1) = x`] THEN
      SUBGOAL_THEN `&1 <= &m /\ &m <= &3` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
      ASM_MESON_TAC[DIRICHLET_CHARACTER_NORM_LE]];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
    REWRITE_TAC[REAL_ARITH `&k * &2 <= &6 <=> &k <= &3`; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC]);;

let PSI1_MONO_BOUND = prove
 (`!d c Tn kap x X Lg.
     dirichlet_character d c /\ ~(c = chi_0 d) /\ 6 <= Tn /\
     &0 < kap /\ kap <= &1 /\
     ((!n. real(c n)) ==> kap <= Re(dseries c (Cx(&1)))) /\
     &1 + log(&(16 * d * (Tn + 4))) = Lg /\
     exp(&1) <= X /\ X <= &2 * x
     ==> norm(vsum {n | 1 <= n /\ &n <= X}
                   (\n. Cx(mangoldt n) * c n * Cx(&1 - &n / X))) <=
         &500 * (&2 * x) * log(&2 * x) pow 2 / &Tn +
         (&10 pow 20 * Lg pow 12 / kap pow 2) * (&2 * x) / &Tn +
         &Tn * (&10 pow 20 * Lg pow 12 / kap pow 2) *
         exp((&1 - kap / (&10 pow 20 * Lg pow 12)) * log(&2 * x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`; `Tn:num`; `kap:real`; `X:real`;
                `Lg:real`] PSI1_ZF) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= a' /\ b <= b' /\ c <= c'
                           ==> x <= a + b + c ==> x <= a' + b' + c'`) THEN
  SUBGOAL_THEN `&1 <= X /\ &0 < X /\ &0 <= log X /\ log X <= log(&2 * x) /\
                &0 < &Tn /\ &1 <= Lg`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 <= X` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_POS; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      EXPAND_TAC "Lg" THEN
      REWRITE_TAC[REAL_ARITH `&1 <= &1 + x <=> &0 <= x`] THEN
      MATCH_MP_TAC LOG_POS THEN
      REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`;
                  MULT_EQ_0; ADD_EQ_0; ARITH_EQ] THEN
      ASM_MESON_TAC[DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &10 pow 20 * Lg pow 12 / kap pow 2 /\
                &0 <= &1 - kap / (&10 pow 20 * Lg pow 12)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= Lg pow 12` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
      ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_SUB_LE] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &10 pow 20`;
                   REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
    ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS];
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let NUMSEG_AS_UPTO = prove
 (`!k. {n | 1 <= n /\ &n <= &k} = 1..k`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG; REAL_OF_NUM_LE]);;

let SW_PI_BOUND = prove
 (`!d c Tn kap x h Lg E.
     dirichlet_character d c /\ ~(c = chi_0 d) /\ 6 <= Tn /\
     &0 < kap /\ kap <= &1 /\
     ((!n. real(c n)) ==> kap <= Re(dseries c (Cx(&1)))) /\
     &1 + log(&(16 * d * (Tn + 4))) = Lg /\ &4 <= x /\ &0 < h /\ h <= x /\
     &500 * (&2 * x) * log(&2 * x) pow 2 / &Tn +
     (&10 pow 20 * Lg pow 12 / kap pow 2) * (&2 * x) / &Tn +
     &Tn * (&10 pow 20 * Lg pow 12 / kap pow 2) *
     exp((&1 - kap / (&10 pow 20 * Lg pow 12)) * log(&2 * x)) = E
     ==> norm(vsum {p | prime p /\ &p <= x} c) <=
         &2 * ((&3 * x * E / h + (h + &1) * log(&2 * x) + &6) +
               sqrt x * log x pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!X. exp(&1) <= X /\ X <= &2 * x
        ==> norm(vsum {n | 1 <= n /\ &n <= X}
                      (\n. (Cx(mangoldt n) * c n) * Cx(&1 - &n / X))) <= E`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "E" THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
    MATCH_MP_TAC PSI1_MONO_BOUND THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [MP_TAC REAL_EXP_1_LE_4 THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&4`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]];
    ALL_TAC] THEN
  MP_TAC(SPEC `x:real` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MP_TAC(SPEC `x:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{p | prime p /\ &p <= x} = {p | prime p /\ p <= N}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    AP_TERM_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      SUBGOAL_THEN `&p < &N + &1 ==> &p <= &N` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
        ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC PI_FROM_THETA_BOUND THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `&1 < &N ==> &2 <= &N` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&k <= x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `k:num`; `c:num->complex`] THETA_PSI_DIFF) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(b:complex) <= p /\ s <= t
    ==> norm(a - b) <= s ==> norm(a) <= p + t`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `&1 <= &k` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_POW_LE; LOG_POS;
                 REAL_ARITH `&1 <= x ==> &0 <= x`] THEN
    CONJ_TAC THENL [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[LOG_POS] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC] THEN
  ASM_CASES_TAC `k <= 3` THENL
   [MP_TAC(SPECL [`k:num`; `c:num->complex`; `d:num`] PSI_SMALL) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= a /\ &0 <= b ==> x <= &6 ==> x <= a + b + &6`) THEN
    SUBGOAL_THEN `&0 <= E / h` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NUMSEG_AS_UPTO] THEN
  MP_TAC(ISPECL [`\m. Cx(mangoldt m) * (c:num->complex) m`; `&k`; `h:real`]
    PSI_FROM_PSI1) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&n) * &1` THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS;
       NORM_POS_LE] THEN
      CONJ_TAC THENL
       [MP_TAC(SPEC `n:num` MANGOLDT_POS_LE) THEN
        MP_TAC(SPEC `n:num` MANGOLDT_LE_LOG) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC];
        ASM_MESON_TAC[DIRICHLET_CHARACTER_NORM_LE]];
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= a' /\ b <= b' ==> x <= a + b ==> x <= a' + b' + &6`) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&3 * x * E / h = (&3 * x * E) / h` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= &2 * x * E /\ b <= x * E ==> a + b <= &3 * x * E`) THEN
    SUBGOAL_THEN `exp(&1) <= &k` ASSUME_TAC THENL
     [MP_TAC REAL_EXP_1_LE_4 THEN
      SUBGOAL_THEN `&4 <= &k` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[NORM_POS_LE] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE; REAL_POS] THEN
      CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The parameters.                                                           *)
(* ------------------------------------------------------------------------- *)

let W_FACTS = prove
 (`!u. &256 <= u
       ==> &2 <= exp(log u / &8) /\ exp(log u / &8) pow 8 = u /\
           log u = &8 * log(exp(log u / &8))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[LOG_EXP] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log(&2))` THEN
    CONJ_TAC THENL [SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`; REAL_LE_REFL];
                    ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    SUBGOAL_THEN `&8 * log(&2) <= log u` MP_TAC THENL
     [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    REWRITE_TAC[GSYM REAL_EXP_N] THEN
    REWRITE_TAC[REAL_ARITH `&8 * x / &8 = x`] THEN
    MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let ONE_PLUS_LOG_POW = prove
 (`!w. &2 <= w ==> (&1 + log w) pow 12 <= &2 * &24 pow 12 * w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= log w` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&4 * w) pow 12` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[LOG_MUL; REAL_ARITH `&0 < &4`;
             ASSUME `&2 <= w`; REAL_ARITH `&2 <= w ==> &0 < w`] THEN
    REWRITE_TAC[REAL_LE_RADD] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_1_LE_4];
    ALL_TAC] THEN
  MP_TAC(SPECL [`12`; `&4 * w`] LOG_POW_LE_SQRT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  CONV_TAC(LAND_CONV(LAND_CONV REAL_RAT_REDUCE_CONV)) THEN
  SIMP_TAC[SQRT_MUL; REAL_ARITH `&0 <= &4`; ASSUME `&2 <= w`;
           REAL_ARITH `&2 <= w ==> &0 <= w`] THEN
  SUBGOAL_THEN `sqrt(&4) = &2` SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt w <= w` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN REWRITE_TAC[REAL_POW_2] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 * w <= w * w ==> w <= w * w`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let LG_W_BOUND = prove
 (`!q Tn w B n1. 1 <= q /\ &2 <= w /\ &q <= (w pow 8) pow B /\
                 &Tn <= w pow n1 + &1
                 ==> &1 + log(&(16 * q * (Tn + 4))) <=
                     (&8 + &8 * &B + &n1) * (&1 + log w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < w /\ &0 <= log w /\ &1 <= w pow n1 /\
                &1 <= w pow (8 * B)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LE_1; LOG_POS; REAL_ARITH `&2 <= w ==> &1 <= w`;
                 REAL_ARITH `&2 <= w ==> &0 < w`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(16 * q * (Tn + 4)) <= &96 * w pow (8 * B + n1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD; REAL_POW_ADD] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&16 * w pow (8 * B) * (&6 * w pow n1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[GSYM REAL_POW_POW]; ASM_REAL_ARITH_TAC] THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(16 * q * (Tn + 4))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < n <=> ~(n = 0)`;
                MULT_EQ_0; ADD_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&(16 * q * (Tn + 4))) <=
                log(&96) + &(8 * B + n1) * log w` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log(&96 * w pow (8 * B + n1))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[LOG_MUL; LOG_POW; REAL_POW_LT; REAL_ARITH `&0 < &96`;
                   REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&96) <= &7` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&2 pow 7)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      SIMP_TAC[LOG_POW; REAL_ARITH `&0 < &2`] THEN
      MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `log(&(16 * q * (Tn + 4))) <=
               log(&96) + &(8 * B + n1) * log w` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC(SPEC `B:num` REAL_POS) THEN MP_TAC(SPEC `n1:num` REAL_POS) THEN
  ASM_REAL_ARITH_TAC);;

let KAP_W_LOWER = prove
 (`!q w B. 1 <= B /\ 1 <= q /\ &2 <= w /\ &q <= (w pow 8) pow B
           ==> inv(w pow 2) <= exp(--(inv(&4 * &B) * log(&q)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < w` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(w pow 2) = exp(--(&2 * log w))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_EXP_NEG; REAL_EXP_N] THEN ASM_SIMP_TAC[EXP_LOG];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
  SUBGOAL_THEN `log(&q) <= &(8 * B) * log w` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log((w pow 8) pow B)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ASM_SIMP_TAC[REAL_POW_POW; LOG_POW; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&4 * &B)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&4 * &B) * (&(8 * B) * log w)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `~(&B = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD]]);;

let PI_TRIVIAL = prove
 (`!x q (c:num->complex). dirichlet_character q c /\ &1 <= x
         ==> norm(vsum {p | prime p /\ &p <= x} c) <= &2 * x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{p | prime p /\ &p <= x} SUBSET {n | &0 < &n /\ &n <= x}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; REAL_OF_NUM_LT] THEN
    MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 0 < p`];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {p | prime p /\ &p <= x}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{n | &0 < &n /\ &n <= x}` THEN
    ASM_REWRITE_TAC[FINITE_NUM_INTERVAL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {p | prime p /\ &p <= x} (\p. &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN ASM_MESON_TAC[DIRICHLET_CHARACTER_NORM_LE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {n | &0 < &n /\ &n <= x})` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[FINITE_NUM_INTERVAL];
    MATCH_MP_TAC(REAL_ARITH
     `&1 <= x /\ c <= x - &0 + &1 ==> c <= &2 * x`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_REAL_INTERVAL THEN
    ASM_REAL_ARITH_TAC]);;

let DIV_LE_INV = prove
 (`!a b c. &0 < b /\ &0 < c /\ a * c <= b ==> a / b <= inv c`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ]);;

let SW_NORM1 = prove
 (`!w u A Tn. &2 <= w /\ w pow 8 = u /\ w pow (16 * A + 24) <= Tn
              ==> u pow (A + 3) / Tn <= inv(u pow A) /\
                  w pow 5 * u pow (A + 1) / Tn <= inv(u pow A)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < w /\ &1 <= w` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Tn` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `(w:real) pow (16 * A + 24)` THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  EXPAND_TAC "u" THEN REWRITE_TAC[REAL_POW_POW] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
  REWRITE_TAC[GSYM real_div] THEN CONJ_TAC THEN
  MATCH_MP_TAC DIV_LE_INV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
  REWRITE_TAC[GSYM REAL_POW_ADD] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(w:real) pow (16 * A + 24)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_MONO THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let SW_NORM2 = prove
 (`!w u A Tn cd m. &2 <= w /\ w pow 8 = u /\ &0 <= Tn /\
                   Tn <= &2 * w pow (16 * A + 24) /\
                   &0 < cd /\ 1 <= m /\ 32 * A + 37 <= 5 * m
                   ==> Tn * w pow 5 * exp(--(cd * w pow 5)) * u pow (A + 1)
                       <= &2 * (&m / cd) pow m * inv(u pow A)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < w /\ &1 <= w /\ &0 < &m` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(--(cd * w pow 5)) <= (&m / cd) pow m * inv(w pow (5 * m))`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`m:num`; `cd * (w:real) pow 5`] EXP_GE_POW) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_NEG] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(cd * (w:real) pow 5) / &m = (cd / &m) * w pow 5`
      SUBST_ALL_TAC
    THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(((cd / &m) * (w:real) pow 5) pow m)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      REWRITE_TAC[REAL_POW_MUL; REAL_INV_MUL; GSYM REAL_POW_POW] THEN
      REWRITE_TAC[GSYM REAL_POW_INV; REAL_INV_DIV]];
    ALL_TAC] THEN
  ABBREV_TAC `K = (&m / cd) pow m` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "u" THEN REWRITE_TAC[REAL_POW_POW] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * (w:real) pow (16 * A + 24)) * w pow 5 *
              (K * inv(w pow (5 * m))) * w pow (8 * (A + 1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE; REAL_EXP_POS_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE;
     REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&2 * (w:real) pow (16 * A + 24)) * w pow 5 * (K * inv(w pow (5 * m))) *
    w pow (8 * (A + 1)) =
    &2 * K * (w pow (24 * A + 37) * inv(w pow (5 * m)))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `(w:real) pow (24 * A + 37) =
                  w pow (16 * A + 24) * w pow 5 * w pow (8 * (A + 1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
      CONV_TAC REAL_RING];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC DIV_LE_INV THEN
  ASM_SIMP_TAC[REAL_POW_LT; GSYM REAL_POW_ADD] THEN
  MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let SW_E_TERM = prove
 (`!x u w A Tn Mz dz KM cd m E.
     &4 <= x /\ log x = u /\ &256 <= u /\ &2 <= w /\ w pow 8 = u /\
     w pow (16 * A + 24) <= &Tn /\ &Tn <= &2 * w pow (16 * A + 24) /\
     &0 <= Mz /\ Mz <= KM * w pow 5 /\ &0 < cd /\ cd * w pow 5 <= dz * u /\
     1 <= m /\ 32 * A + 37 <= 5 * m /\
     &500 * (&2 * x) * log(&2 * x) pow 2 / &Tn + Mz * (&2 * x) / &Tn +
     &Tn * Mz * exp((&1 - dz) * log(&2 * x)) = E
     ==> &3 * x * E / (x / u pow (A + 1)) <=
         (&12000 + &6 * KM + &12 * KM * (&m / cd) pow m) * x / u pow A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < w /\ &0 < u /\ &0 < &Tn /\ &0 < x` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `(w:real) pow (16 * A + 24)` THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_ARITH `&2 <= w ==> &0 < w`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= KM /\ &0 < dz` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `&0 <= KM * w pow 5` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_MUL_EQ; REAL_POW_LT]];
      SUBGOAL_THEN `&0 < dz * u` MP_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `cd * (w:real) pow 5` THEN
        ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT];
        ASM_SIMP_TAC[REAL_LT_MUL_EQ]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * x * E / (x / u pow (A + 1)) = &3 * E * u pow (A + 1)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `~(x = &0) /\ ~(u pow (A + 1) = &0)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_NZ; REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&2 * x) /\ log(&2 * x) <= &2 * u /\
                u <= log(&2 * x)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_MUL; REAL_ARITH `&0 < &2`] THEN
    MP_TAC LOG_2_BOUNDS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `E <= &4000 * x * (u pow 2 / &Tn) + &2 * KM * x * (w pow 5 / &Tn) +
         &2 * KM * x * (&Tn * w pow 5 * exp(--(cd * w pow 5)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= a' /\ b <= b' /\ c <= c' ==> a + b + c <= a' + b' + c'`) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&500 * (&2 * x) * (&4 * u pow 2) / &Tn):real` THEN
        CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
        ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
        REWRITE_TAC[REAL_ARITH `&4 * u pow 2 = (&2 * u) pow 2`] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `((KM * w pow 5) * (&2 * x) / &Tn):real` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `exp((&1 - dz) * log(&2 * x)) <=
                    &2 * x * exp(--(cd * w pow 5))` ASSUME_TAC THENL
       [SUBGOAL_THEN `exp((&1 - dz) * log(&2 * x)) =
                      (&2 * x) * exp(--(dz * log(&2 * x)))` SUBST1_TAC THENL
         [REWRITE_TAC[REAL_ARITH `(&1 - d) * l = l + --(d * l)`;
                      REAL_EXP_ADD] THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC EXP_LOG THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dz * u:real` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&Tn * (KM * w pow 5) * (&2 * x * exp(--(cd * w pow 5)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`w:real`; `u:real`; `A:num`; `&Tn`] SW_NORM1) THEN
  MP_TAC(SPECL [`w:real`; `u:real`; `A:num`; `&Tn`; `cd:real`; `m:num`]
    SW_NORM2) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&3 * (&4000 * x * (u pow 2 / &Tn) +
                    &2 * KM * x * (w pow 5 / &Tn) +
                    &2 * KM * x * (&Tn * w pow 5 * exp(--(cd * w pow 5)))) *
              u pow (A + 1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
    ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&3 * (&4000 * x * (u pow 2 / &Tn) +
          &2 * KM * x * (w pow 5 / &Tn) +
          &2 * KM * x * (&Tn * w pow 5 * exp(--(cd * w pow 5)))) *
    u pow (A + 1) =
    &12000 * x * (u pow (A + 3) / &Tn) +
    &6 * KM * x * (w pow 5 * u pow (A + 1) / &Tn) +
    &6 * KM * x * (&Tn * w pow 5 * exp(--(cd * w pow 5)) * u pow (A + 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `A + 3 = 2 + (A + 1)`; REAL_POW_ADD] THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&12000 * x * inv(u pow A) + &6 * KM * x * inv(u pow A) +
               &6 * KM * x * (&2 * (&m / cd) pow m * inv(u pow A))):real` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `a <= a' /\ b <= b' /\ c <= c' ==> a + b + c <= a' + b' + c'`) THEN
    REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN
           CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;

let SW_SMALL_TERMS = prove
 (`!x A. &4 <= x /\ &256 <= log x
         ==> (x / log x pow (A + 1) + &1) * log(&2 * x) + &6 +
             sqrt x * log x pow 2 <=
             (&2 + &2 * (&2 * &(A + 1)) pow (A + 1) + &6 * (&2 * &A) pow A +
              (&2 * &(A + 2)) pow (A + 2)) * x / log x pow A`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `u = log x` THEN
  SUBGOAL_THEN `&0 < u /\ &0 < u pow A /\ &0 < x /\ &1 <= x /\
                &0 <= sqrt x /\ sqrt x * sqrt x = x`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; REAL_ARITH `&256 <= u ==> &0 < u`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC SQRT_POW_2 THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&2 * x) <= &2 * u /\ &0 <= log(&2 * x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_SIMP_TAC[LOG_MUL; REAL_ARITH `&0 < &2`] THEN
    MP_TAC LOG_2_BOUNDS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. u pow k <= (&2 * &k) pow k * sqrt x` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "u" THEN MATCH_MP_TAC LOG_POW_LE_SQRT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt x <= x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN REWRITE_TAC[REAL_POW_2] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 * x <= x * x ==> x <= x * x`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `c * x * i = c * (x * i):real`] THEN
  ABBREV_TAC `v = (x:real) * inv(u pow A)` THEN
  SUBGOAL_THEN `!y K. y * u pow A <= K * x ==> y <= K * v` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "v" THEN
    REWRITE_TAC[REAL_MUL_ASSOC; GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `x * inv(u pow (A + 1)) * log(&2 * x) <= &2 * v`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(x * inv(u pow (A + 1)) * &2 * u) * u pow A` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[REAL_POW_ADD;
       REAL_POW_1] THEN
      SUBGOAL_THEN `~(u = &0) /\ ~(u pow A = &0)` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&2 * x) <= &2 * (&2 * &(A + 1)) pow (A + 1) * v`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * u` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
     ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * &(A + 1)) pow (A + 1) * sqrt x` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(u:real) * u pow A = u pow (A + 1)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_MUL_SYM];
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&6 <= &6 * (&2 * &A) pow A * v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= y ==> &6 <= &6 * y`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * &A) pow A * sqrt x` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt x * u pow 2 <= (&2 * &(A + 2)) pow (A + 2) * v`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `2 + A = A + 2`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt x * (&2 * &(A + 2)) pow (A + 2) * sqrt x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `sqrt x * sqrt x = x` THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let SW_MZ_DZ_BOUNDS = prove
 (`!q w B A Tn kap k0 Lg.
     1 <= B /\ 1 <= q /\ &2 <= w /\ &q <= (w pow 8) pow B /\
     &Tn <= w pow (16 * A + 24) + &1 /\ &0 < k0 /\
     k0 * exp(--(inv(&4 * &B) * log(&q))) = kap /\
     &1 + log(&(16 * q * (Tn + 4))) = Lg
     ==> &10 pow 20 * Lg pow 12 / kap pow 2 <=
         (&10 pow 20 * (&2 * &24 pow 12 *
                        (&8 + &8 * &B + &(16 * A + 24)) pow 12) / k0 pow 2) *
         w pow 5 /\
         (k0 / (&10 pow 20 * (&2 * &24 pow 12 *
                              (&8 + &8 * &B + &(16 * A + 24)) pow 12))) *
         w pow 5 <= kap / (&10 pow 20 * Lg pow 12) * w pow 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `K1 = &8 + &8 * &B + &(16 * A + 24)` THEN
  ABBREV_TAC `K3 = &2 * &24 pow 12 * K1 pow 12` THEN
  SUBGOAL_THEN `&0 < w /\ &1 <= K1 /\ &0 < K3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= K1` ASSUME_TAC THENL
     [EXPAND_TAC "K1" THEN MP_TAC(SPEC `B:num` REAL_POS) THEN
      MP_TAC(SPEC `16 * A + 24` REAL_POS) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "K3" THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= Lg /\ Lg pow 12 <= K3 * w` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`q:num`; `Tn:num`; `w:real`; `B:num`; `16 * A + 24`]
      LG_W_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 <= Lg` ASSUME_TAC THENL
     [EXPAND_TAC "Lg" THEN
      REWRITE_TAC[REAL_ARITH `&1 <= &1 + x <=> &0 <= x`] THEN
      MATCH_MP_TAC LOG_POS THEN
      REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`;
                  MULT_EQ_0; ADD_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(K1 * (&1 + log w)) pow 12` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN EXPAND_TAC "K3" THEN
    SUBGOAL_THEN `(&2 * &24 pow 12 * K1 pow 12) * w =
                  K1 pow 12 * (&2 * &24 pow 12 * w)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC ONE_PLUS_LOG_POW THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`q:num`; `w:real`; `B:num`] KAP_W_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `k0 * inv(w pow 2) <= kap /\ &0 < kap` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "kap" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Lg pow 12 /\ &0 < w pow 2 /\ &0 < w pow 5`
    STRIP_ASSUME_TAC
  THENL [ASM_SIMP_TAC[REAL_POW_LT; REAL_ARITH `&1 <= x ==> &0 < x`];
         ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_div] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b * c) * d = a * (b * (c * d)):real`]
      THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
     ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((K3 * w) * inv(k0 * inv(w pow 2)) pow 2):real` THEN
      CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LE THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_POW_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        SUBGOAL_THEN `&0 < k0 * inv(w pow 2)` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ];
          ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      SUBGOAL_THEN `~(k0 = &0) /\ ~(w = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((k0 * inv(w pow 2)) / (&10 pow 20 * (K3 * w)) * w pow 8):real`
  THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `~(K3 = &0) /\ ~(w = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_POW_LE];
    REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The Siegel-Walfisz theorem.                                               *)
(* ------------------------------------------------------------------------- *)

let SIEGEL_WALFISZ = prove
 (`!A B. ?C. !x q c. &2 <= x /\ 1 <= q /\ &q <= log x pow B /\
                     dirichlet_character q c /\ ~(c = chi_0 q)
                     ==> norm(vsum {p | prime p /\ &p <= x} c) <=
                         C * x / log x pow A`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `B = 0` THENL
   [EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[real_pow] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`q:num`; `c:num->complex`]
      DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&q <= &1` THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `inv(&4 * &B)` SIEGEL) THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `kS:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "siegel")))] THEN
  ABBREV_TAC `k0 = min kS (&1)` THEN
  SUBGOAL_THEN `&0 < k0 /\ k0 <= &1 /\ k0 <= kS` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `K3 = &2 * &24 pow 12 * (&8 + &8 * &B + &(16 * A + 24)) pow 12`
    THEN
  ABBREV_TAC `KM = &10 pow 20 * K3 / k0 pow 2` THEN
  ABBREV_TAC `cd = k0 / (&10 pow 20 * K3)` THEN
  ABBREV_TAC `m = 7 * A + 8` THEN
  ABBREV_TAC
   `C1 = &2 * ((&12000 + &6 * KM + &12 * KM * (&m / cd) pow m) +
               (&2 + &2 * (&2 * &(A + 1)) pow (A + 1) +
                &6 * (&2 * &A) pow A + (&2 * &(A + 2)) pow (A + 2)))` THEN
  SUBGOAL_THEN `&0 < K3 /\ &0 < cd /\ &0 <= KM /\ &0 <= C1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < K3` ASSUME_TAC THENL
     [EXPAND_TAC "K3" THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
       ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
       ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(SPEC `B:num` REAL_POS) THEN
      MP_TAC(SPEC `16 * A + 24` REAL_POS) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= KM /\ &0 < cd` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["KM"; "cd"] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
        ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "C1" THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `&0 <= a /\ &0 <= a * b ==> &0 <= &12000 + &6 * a + &12 * a * b`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 <= &2 + &2 * a + &6 * b + c`) THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `C1 + &2 * &256 pow A` THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `q:num`; `c:num->complex`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`q:num`; `c:num->complex`]
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `u = log x` THEN
  SUBGOAL_THEN `&0 < u` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < u pow A /\ &0 <= x / u pow A` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  ASM_CASES_TAC `u < &256` THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ y <= b ==> y <= a + b`) THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * x` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PI_TRIVIAL THEN EXISTS_TAC `q:num` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= b /\ y <= a ==> y <= a + b`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&256 <= u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `u:real` W_FACTS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `w = exp(log u / &8)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&4 <= x` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `log x <= log(&2 pow 2)` MP_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC;
      SIMP_TAC[LOG_POW; REAL_ARITH `&0 < &2`] THEN MP_TAC LOG_2_BOUNDS THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `(w:real) pow (16 * A + 24)` FLOOR_POS) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
  MP_TAC(SPEC `(w:real) pow (16 * A + 24)` FLOOR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&8 <= (w:real) pow (16 * A + 24)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(w:real) pow 3` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2:real) pow 3` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE2] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `Tn = N0 + 1` THEN
  SUBGOAL_THEN `(w:real) pow (16 * A + 24) <= &Tn /\
                &Tn <= w pow (16 * A + 24) + &1 /\
                &Tn <= &2 * w pow (16 * A + 24) /\ 6 <= Tn`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Tn" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `kap = k0 * exp(--(inv(&4 * &B) * log(&q)))` THEN
  SUBGOAL_THEN `&0 < kap /\ kap <= &1 /\
                ((!n. real(c n)) ==> kap <= Re(dseries c (Cx(&1))))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= inv(&4 * &B) * log(&q)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_INV_EQ] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
      ALL_TAC] THEN
    EXPAND_TAC "kap" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_POS_LE] THEN
      REWRITE_TAC[REAL_EXP_NEG] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
      MP_TAC(SPEC `inv(&4 * &B) * log(&q)` REAL_EXP_LE_X) THEN
      ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `kS * exp(--(inv(&4 * &B) * log(&q)))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
        USE_THEN "siegel" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `Lg = &1 + log(&(16 * q * (Tn + 4)))` THEN
  ABBREV_TAC `h = (x:real) / u pow (A + 1)` THEN
  SUBGOAL_THEN `&0 < h /\ h <= x` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN
    SUBGOAL_THEN `&1 <= u pow (A + 1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&1 <= x ==> &0 < x`;
                 REAL_LE_LDIV_EQ; REAL_ARITH `&4 <= x ==> &0 < x`] THEN
    MATCH_MP_TAC(REAL_ARITH `x * &1 <= x * y ==> x <= x * y`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `E = &500 * (&2 * x) * log(&2 * x) pow 2 / &Tn +
        (&10 pow 20 * Lg pow 12 / kap pow 2) * (&2 * x) / &Tn +
        &Tn * (&10 pow 20 * Lg pow 12 / kap pow 2) *
        exp((&1 - kap / (&10 pow 20 * Lg pow 12)) * log(&2 * x))` THEN
  MP_TAC(SPECL [`q:num`; `c:num->complex`; `Tn:num`; `kap:real`; `x:real`;
                `h:real`; `Lg:real`; `E:real`] SW_PI_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`q:num`; `w:real`; `B:num`; `A:num`; `Tn:num`; `kap:real`;
                `k0:real`; `Lg:real`] SW_MZ_DZ_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `u:real`; `w:real`; `A:num`; `Tn:num`;
                `&10 pow 20 * Lg pow 12 / kap pow 2`;
                `kap / (&10 pow 20 * Lg pow 12)`; `KM:real`; `cd:real`;
                `m:num`; `E:real`] SW_E_TERM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
      ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MP_TAC(SPEC `(Lg:real) pow 6` REAL_LE_POW_2) THEN
      REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV;
      EXPAND_TAC "m" THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:real`; `A:num`] SW_SMALL_TERMS) THEN
  ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "C1" THEN EXPAND_TAC "h" THEN REWRITE_TAC[real_div] THEN
  ABBREV_TAC `T0 = &3 * x * E * inv(x * inv(u pow (A + 1)))` THEN
  ABBREV_TAC `S1 = (x * inv(u pow (A + 1)) + &1) * log(&2 * x)` THEN
  ABBREV_TAC `S2 = sqrt x * u pow 2` THEN
  ABBREV_TAC `X = (x:real) * inv(u pow A)` THEN
  ABBREV_TAC `CE = &12000 + &6 * KM + &12 * KM * (&m * inv cd) pow m` THEN
  ABBREV_TAC `CS = (&2 + &2 * (&2 * &(A + 1)) pow (A + 1) +
                    &6 * (&2 * &A) pow A + (&2 * &(A + 2)) pow (A + 2)):real`
                      THEN
  ABBREV_TAC `nv = norm(vsum {p | prime p /\ &p <= x} (c:num->complex))` THEN
  REAL_ARITH_TAC);;
