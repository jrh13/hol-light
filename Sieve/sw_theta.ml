(* ========================================================================= *)
(* The Siegel-Walfisz theorem for theta in arithmetic progressions,          *)
(* uniformly in the length of the sum:                                       *)
(*   THETA_AP_UNIFORM:                                                       *)
(*     !A B. ?Cb. !x q b k.                                                  *)
(*       &2 <= x /\ 1 <= q /\ &q <= log x pow B /\ coprime(b,q) /\ &k <= x   *)
(*       ==> abs(sum {p | prime p /\ p <= k /\ (p == b) (mod q)}             *)
(*                   (\p. log(&p)) - &k / &(phi q)) <= Cb * x / log x pow A  *)
(*                                                                           *)
(* * SW_THETA_BOUND, SIEGEL_WALFISZ_THETA: the analogue of SW_PI_BOUND and   *)
(*   SIEGEL_WALFISZ (sw.ml) for theta(k,c) = sum_{m <= k} [prime m] log m    *)
(*   c(m), uniformly for k <= x (THETA_CHAR_TRIVIAL for small k).            *)
(* * PNT_THETA_UNIFORM: PNT_THETA_ERROR, also uniform in k <= x.             *)
(* * THETA_AP_UNIFORM: the character decomposition of the progression        *)
(*   (VSUM_THETA_CHAR), the principal character from PNT_THETA_UNIFORM up to *)
(*   the primes dividing q (LOG_SUM_PRIME_DIVISORS).                         *)
(* ========================================================================= *)

needs "Sieve/pnt_error.ml";;
needs "Sieve/bv.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Siegel-Walfisz for theta with nonprincipal characters.                    *)
(* ------------------------------------------------------------------------- *)

let SW_THETA_BOUND = prove
 (`!d c Tn kap x h Lg E k.
     dirichlet_character d c /\ ~(c = chi_0 d) /\ 6 <= Tn /\
     &0 < kap /\ kap <= &1 /\
     ((!n. real(c n)) ==> kap <= Re(dseries c (Cx(&1)))) /\
     &1 + log(&(16 * d * (Tn + 4))) = Lg /\ &4 <= x /\ &0 < h /\ h <= x /\
     &500 * (&2 * x) * log(&2 * x) pow 2 / &Tn +
     (&10 pow 20 * Lg pow 12 / kap pow 2) * (&2 * x) / &Tn +
     &Tn * (&10 pow 20 * Lg pow 12 / kap pow 2) *
     exp((&1 - kap / (&10 pow 20 * Lg pow 12)) * log(&2 * x)) = E /\
     1 <= k /\ &k <= x
     ==> norm(vsum(1..k) (\m. Cx(if prime m then log(&m) else &0) * c m))
         <= (&3 * x * E / h + (h + &1) * log(&2 * x) + &6) +
            sqrt x * log x pow 2`,
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

let THETA_CHAR_TRIVIAL = prove
 (`!q (c:num->complex) k.
     dirichlet_character q c /\ 1 <= k
     ==> norm(vsum(1..k) (\m. Cx(if prime m then log(&m) else &0) * c m))
         <= &k * log(&k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..k) (\m. log(&k))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&m) * &1` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `&0 <= log(&m)` ASSUME_TAC THENL
         [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
          ASM_ARITH_TAC;
          COND_CASES_TAC THEN ASM_REAL_ARITH_TAC];
        ASM_MESON_TAC[DIRICHLET_CHARACTER_NORM_LE]];
      REWRITE_TAC[REAL_MUL_RID] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]]);;

let SIEGEL_WALFISZ_THETA = prove
 (`!A B. ?Cb. !x q c k.
       &2 <= x /\ 1 <= q /\ &q <= log x pow B /\
       dirichlet_character q c /\ ~(c = chi_0 q) /\ 1 <= k /\ &k <= x
       ==> norm(vsum(1..k) (\m. Cx(if prime m then log(&m) else &0) * c m))
           <= Cb * x / log x pow A`,
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
   `C1 = (&12000 + &6 * KM + &12 * KM * (&m / cd) pow m) +
         (&2 + &2 * (&2 * &(A + 1)) pow (A + 1) +
          &6 * (&2 * &A) pow A + (&2 * &(A + 2)) pow (A + 2))` THEN
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
  EXISTS_TAC `C1 + &256 pow (A + 1)` THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `q:num`; `c:num->complex`; `k:num`] THEN
  STRIP_TAC THEN
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
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `x * u:real` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&k * log(&k)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC THETA_CHAR_TRIVIAL THEN EXISTS_TAC `q:num` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
          EXPAND_TAC "u" THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
          ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC]];
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM(CONJUNCT2 real_pow)] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[ADD1] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= b /\ y <= a ==> y <= a + b`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
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
                `h:real`; `Lg:real`; `E:real`; `k:num`] SW_THETA_BOUND) THEN
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
  ABBREV_TAC `nv = norm(vsum(1..k) (\m. Cx(if prime m then log(&m) else &0) *
                                       (c:num->complex) m))` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Theta in arithmetic progressions.                                         *)
(* ------------------------------------------------------------------------- *)

let VSUM_THETA_CHAR = prove
 (`!k (c:num->complex).
     vsum(1..k) (\m. Cx(if prime m then log(&m) else &0) * c m) =
     vsum {p | prime p /\ p <= k} (\p. Cx(log(&p)) * c p)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{p | prime p /\ p <= k} = {m | m IN 1..k /\ prime m}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `p:num` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_RESTRICT_SET] THEN MATCH_MP_TAC VSUM_EQ THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0]);;

let LOG_SUM_PRIME_DIVISORS = prove
 (`!q. 1 <= q ==> sum {p | prime p /\ p divides q} (\p. log(&p)) <= log(&q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `q:num` LOG_MANGOLDT_SUM) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {p | prime p /\ p divides q} (\d. mangoldt d)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:num`; `1`] MANGOLDT_PRIMEPOW) THEN
    ASM_REWRITE_TAC[EXP_1; LE_REFL] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[FINITE_DIVISORS; ARITH_RULE `1 <= q ==> ~(q = 0)`;
                 MANGOLDT_POS_LE] THEN
    SET_TAC[]]);;

let PNT_THETA_UNIFORM = prove
 (`!A. ?Cb. !x k. &2 <= x /\ &k <= x
                 ==> abs(sum {p | prime p /\ p <= k} (\p. log(&p)) - &k) <=
                     Cb * x / log x pow A`,
  GEN_TAC THEN MP_TAC(SPEC `A:num` PNT_THETA_ERROR) THEN
  DISCH_THEN(X_CHOOSE_TAC `C0:real`) THEN
  ABBREV_TAC `D = (&2 * &(A + 1)) pow (A + 1)` THEN
  EXISTS_TAC `abs C0 * &2 pow A + &3 * D` THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `k:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{p | prime p /\ p <= k} = {p | prime p /\ &p <= &k}`
  SUBST1_TAC THENL [REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  ABBREV_TAC `th = sum {p | prime p /\ &p <= &k} (\p. log(&p))` THEN
  ABBREV_TAC `u = log x` THEN
  MP_TAC(SPECL [`A + 1`; `x:real`] LOG_POW_LE_SQRT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 / &2 <= u` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN MP_TAC LOG_2_BOUNDS THEN
    MP_TAC(SPECL [`&2`; `x:real`] LOG_MONO_LE_IMP) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < u pow A /\ &0 <= x / u pow A /\ &0 <= D`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "D" THEN MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= abs C0 * &2 pow A * x / u pow A /\
                &0 <= D * x / u pow A`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `k = 0` THENL
   [SUBGOAL_THEN `th = &0` SUBST1_TAC THENL
     [EXPAND_TAC "th" THEN UNDISCH_TAC `k = 0` THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_OF_NUM_LE; LE] THEN
      MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MESON_TAC[PRIME_0];
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= th /\ th <= &k * u` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `&k` THETA_TRIVIAL) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&k * log(&k)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS] THEN EXPAND_TAC "u" THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&k < sqrt x` THENL
   [SUBGOAL_THEN `sqrt x * u <= D * x / u pow A` ASSUME_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      SUBGOAL_THEN `(sqrt x * u) * u pow A = sqrt x * u pow (A + 1) /\
                    D * x = sqrt x * (D * sqrt x)`
      (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THENL
         [REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN REAL_ARITH_TAC;
          MP_TAC(SPEC `x:real` SQRT_POW_2) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RING]];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sqrt x` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&k * u <= sqrt x * u /\ sqrt x <= &2 * sqrt x * u`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `s * &1 <= s * (&2 * u) ==> s <= &2 * s * u`)
        THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < sqrt x` ASSUME_TAC THENL
   [SUBST1_TAC(SYM SQRT_1) THEN MATCH_MP_TAC SQRT_MONO_LT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= &k` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 < &k` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&k`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `y <= b * X /\ &0 <= d * X ==> a <= y ==> a <= (b + d) * X`) THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `u / &2 <= log(&k)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(sqrt x)` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "u" THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC LOG_SQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (u / &2) pow A` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&k / log(&k) pow A <= &2 pow A * x / u pow A` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `x / (u / &2) pow A` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LE THEN
        ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_INV] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_POW_INV] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]];
      REWRITE_TAC[REAL_POW_DIV] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      SUBGOAL_THEN `~(u pow A = &0) /\ ~(&2 pow A = &0)` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC;
        CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs C0 * &k / log(&k) pow A` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_ABS_POS]]);;

let THETA_AP_UNIFORM = prove
 (`!A B. ?Cb. !x q b k.
       &2 <= x /\ 1 <= q /\ &q <= log x pow B /\ coprime(b,q) /\ &k <= x
       ==> abs(sum {p | prime p /\ p <= k /\ (p == b) (mod q)} (\p. log(&p)) -
               &k / &(phi q)) <= Cb * x / log x pow A`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`A:num`; `B:num`] SIEGEL_WALFISZ_THETA) THEN
  DISCH_THEN(X_CHOOSE_TAC `C1:real`) THEN
  MP_TAC(SPEC `A:num` PNT_THETA_UNIFORM) THEN
  DISCH_THEN(X_CHOOSE_TAC `C2:real`) THEN
  ABBREV_TAC `D = (&2 * &(A + B)) pow (A + B)` THEN
  EXISTS_TAC `abs C1 + abs C2 + D` THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `q:num`; `b:num`; `k:num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log x` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log x pow A /\ &0 <= x / log x pow A /\ &0 <= D`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_DIV THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "D" THEN MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= abs C1 * x / log x pow A /\
                &0 <= abs C2 * x / log x pow A /\
                C2 * x / log x pow A <= abs C2 * x / log x pow A /\
                &0 <= D * x / log x pow A`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
        NO_TAC) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `k = 0` THENL
   [SUBGOAL_THEN
     `sum {p | prime p /\ p <= k /\ (p == b) (mod q)} (\p. log(&p)) = &0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_0 THEN ASM_REWRITE_TAC[IN_ELIM_THM; LE] THEN
      MESON_TAC[PRIME_0];
      ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= phi q` ASSUME_TAC THENL
   [MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&(phi q)) /\ inv(&(phi q)) <= &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:num`; `b:num`; `\p:num. p`; `\p:num. log(&p)`;
                 `{p | prime p /\ p <= k}`] CHARACTER_DISCREPANCY_BOUND) THEN
  ASM_REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
  ABBREV_TAC
   `S = sum ({c | dirichlet_character q c} DELETE chi_0 q)
            (\c. norm(vsum {p | prime p /\ p <= k}
                           (\x. Cx(log(&x)) * c x)))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `inv(&(phi q)) * S <= abs C1 * x / log x pow A` ASSUME_TAC
  THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&(phi q)) * (&(phi q) * abs C1 * x / log x pow A)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      EXPAND_TAC "S" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(CARD({c | dirichlet_character q c} DELETE chi_0 q)) *
                  abs C1 * x / log x pow A` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_BOUND THEN
        SIMP_TAC[FINITE_DELETE; FINITE_DIRICHLET_CHARACTERS] THEN
        X_GEN_TAC `c:num->complex` THEN
        REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN STRIP_TAC THEN
        REWRITE_TAC[GSYM VSUM_THETA_CHAR] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `C1 * x / log x pow A` THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPECL
           [`x:real`; `q:num`; `c:num->complex`; `k:num`]) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
          REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ASM_SIMP_TAC[GSYM CARD_DIRICHLET_CHARACTERS] THEN
        MATCH_MP_TAC CARD_SUBSET THEN
        REWRITE_TAC[DELETE_SUBSET; FINITE_DIRICHLET_CHARACTERS]];
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      SUBGOAL_THEN `inv(&(phi q)) * &(phi q) = &1` SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
        ASM_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_LID; GSYM REAL_MUL_ASSOC; REAL_LE_REFL]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{p | prime p /\ p <= k}`; `\p. coprime(p,q)`;
                 `\p. log(&p)`; `\p. log(&p)`] SUM_CASES) THEN
  REWRITE_TAC[COND_ID; FINITE_ATMOST; IN_ELIM_THM; GSYM CONJ_ASSOC;
              ETA_AX] THEN
  ABBREV_TAC `Ta = sum {p | prime p /\ p <= k /\ (p == b) (mod q)}
                       (\p. log(&p))` THEN
  ABBREV_TAC `Tc = sum {p | prime p /\ p <= k /\ coprime(p,q)}
                       (\p. log(&p))` THEN
  ABBREV_TAC `Y = sum {p | prime p /\ p <= k /\ ~coprime(p,q)}
                      (\p. log(&p))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= Y /\ Y <= log(&q)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `FINITE {p | prime p /\ p divides q}` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{d | d divides q}` THEN
      ASM_SIMP_TAC[FINITE_DIVISORS; ARITH_RULE `1 <= q ==> ~(q = 0)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `{p | prime p /\ p <= k /\ ~coprime(p,q)} SUBSET
                  {p | prime p /\ p divides q}` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[PRIME_COPRIME_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `!p. prime p ==> &0 <= log(&p)` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC LOG_POS THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "Y" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum {p | prime p /\ p divides q} (\p. log(&p))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC LOG_SUM_PRIME_DIVISORS THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&q) <= D * x / log x pow A` ASSUME_TAC THENL
   [MP_TAC(SPECL [`A + B:num`; `x:real`] LOG_POW_LE_SQRT) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `sqrt x <= x` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC(REAL_ARITH `x * &1 <= x * x ==> x <= x * x`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log x pow (A + B)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_ADD] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&q` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOG_LE_REFL THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `D * sqrt x` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `k:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `inv(&(phi q)) * Y <= Y /\ &0 <= inv(&(phi q)) * Y`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `i * y <= &1 * y ==> i * y <= y`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(inv(&(phi q)) * ((Tc + Y) - &k)) <= abs((Tc + Y) - &k)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `i * y <= &1 * y ==> i * y <= y`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < i ==> abs i = i`];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC);;
