(* ========================================================================= *)
(* The prime number theorem for arithmetic progressions (de la Vallee        *)
(* Poussin, 1896): for q >= 1 and (a,q) = 1,                                 *)
(*   pi(x;q,a) / (x / log x) ---> 1 / phi(q)                  (PNT_AP),      *)
(* with the error term, uniform in x and a,                                  *)
(*   |pi(x;q,a) - pi(x) / phi(q)| <= C(q,A) x / log^A x  (PRIMES_AP_ERROR).  *)
(*                                                                           *)
(* The discrepancy is bounded by sums over the primitive characters c mod    *)
(* r, r | q, r > 1, of |sum_{p <= x} c(p)| (BV_AP_DISCREPANCY, bv.ml); each  *)
(* such sum is O(x / log^A x) by Siegel-Walfisz (sw.ml) once q <= log x,     *)
(* and for smaller x the trivial bound 2x suffices.  The main term is the    *)
(* PNT of 100/pnt.ml.                                                        *)
(* ========================================================================= *)

needs "Sieve/sw.ml";;
needs "Sieve/bv.ml";;

prioritize_num(); prioritize_complex();;

let PRIMES_AP_ERROR = prove
 (`!q A. 1 <= q
         ==> ?C. !x a.
               2 <= x /\ coprime(a,q)
               ==> abs(&(CARD {p | prime p /\ p <= x /\ (p == a) (mod q)}) -
                       &(CARD {p | prime p /\ p <= x}) / &(phi q))
                   <= C * &x / log(&x) pow A`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`A:num`; `1`] SIEGEL_WALFISZ) THEN
  REWRITE_TAC[REAL_POW_1] THEN
  DISCH_THEN(X_CHOOSE_TAC `C0:real`) THEN
  ABBREV_TAC `R = {r | r divides q /\ ~(r = 1)}` THEN
  SUBGOAL_THEN `FINITE(R:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{r | r divides q}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC; SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `K = sum R (\r. &(CARD {c | primitive_character r c}))` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  ABBREV_TAC `T0 = (&q + &1) * log(&q) / log(&2)` THEN
  ABBREV_TAC `D = (&2 * &A) pow A` THEN
  EXISTS_TAC `K * abs C0 + T0 * D + &2 * &q pow A` THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `a:num`] THEN STRIP_TAC THEN
  ABBREV_TAC `Y = &x / log(&x) pow A` THEN
  SUBGOAL_THEN `&0 < log(&x)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&x) pow A` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Y /\ &x = log(&x) pow A * Y` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN
    SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE;
             ASSUME `&0 < log(&x) pow A`] THEN
    UNDISCH_TAC `&0 < log(&x) pow A` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= T0 /\ &0 <= D` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["T0"; "D"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= D * Y` ASSUME_TAC THENL
   [MP_TAC(SPECL [`A:num`; `&x:real`] LOG_POW_LE_SQRT) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&1 <= sqrt(&x) /\ sqrt(&x) * sqrt(&x) = &x`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RSQRT THEN
        REWRITE_TAC[REAL_POW_ONE; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_POW_2] THEN SIMP_TAC[SQRT_POW_2; REAL_POS]];
      ALL_TAC] THEN
    SUBGOAL_THEN `log(&x) pow A * Y <= (D * sqrt(&x)) * Y` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> rand(concl th) = `log(&x) pow A * Y`)) THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
      [SYM(check (fun th -> rand(concl th) = `&x:real`) th)]) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `sqrt(&x) <= D * Y` MP_TAC THENL
     [ALL_TAC; UNDISCH_TAC `&1 <= sqrt(&x)` THEN REAL_ARITH_TAC] THEN
    MP_TAC(SPECL [`sqrt(&x)`; `(D:real) * Y`; `sqrt(&x)`]
      REAL_LE_LMUL_EQ) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!P. &(CARD {p | prime p /\ p <= x /\ P p}) <= &x`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(1..x)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
      MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
      REWRITE_TAC[CARD_NUMSEG_1; LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &(phi q)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_SIMP_TAC[PHI_LOWERBOUND_1_STRONG];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(CARD {p | prime p /\ p <= x}) / &(phi q) <= &x /\
                &0 <= &(CARD {p | prime p /\ p <= x}) / &(phi q)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS]] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&x * &1` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_RID] THEN
      MP_TAC(SPEC `\p:num. T` (ASSUME
        `!P. &(CARD {p | prime p /\ p <= x /\ P p}) <= &x`)) THEN
      REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (K * abs C0) * Y /\ &0 <= (T0 * D) * Y`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  ASM_CASES_TAC `&q <= log(&x)` THENL
   [ALL_TAC;
    SUBGOAL_THEN `log(&x) pow A * Y <= &q pow A * Y` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `\p:num. (p == a) (mod q)` (ASSUME
        `!P. &(CARD {p | prime p /\ p <= x /\ P p}) <= &x`)) THEN
    REWRITE_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * &x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `&0 <= a /\ a <= x /\ &0 <= b /\ b <= x ==> abs(a - b) <= &2 * x`) THEN
      ASM_REWRITE_TAC[REAL_POS];
      UNDISCH_TAC `&x = log(&x) pow A * Y` THEN
      UNDISCH_TAC `log(&x) pow A * Y <= &q pow A * Y` THEN
      UNDISCH_TAC `&0 <= (K * abs C0) * Y` THEN
      UNDISCH_TAC `&0 <= (T0 * D) * Y` THEN REAL_ARITH_TAC]] THEN
  MP_TAC(SPECL [`x:num`; `q:num`; `a:num`] BV_AP_DISCREPANCY) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s = sum R (\r. sum {c | primitive_character r c}
                          (\c. norm (vsum {p | prime p /\ &p <= &x} c)))` THEN
  SUBGOAL_THEN `&0 <= s /\ s <= K * (C0 * Y)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN EXPAND_TAC "K" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN
      REWRITE_TAC[ASSUME `FINITE(R:num->bool)`] THEN
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC SUM_POS_LE THEN
      REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS; NORM_POS_LE];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE THEN
    REWRITE_TAC[ASSUME `FINITE(R:num->bool)`] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `1 <= r /\ r <= q /\ ~(r = 1)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(r:num) IN R` THEN EXPAND_TAC "R" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`r:num`; `q:num`] DIVIDES_LE) THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `r = 0` THENL
       [UNDISCH_TAC `r divides q` THEN ASM_REWRITE_TAC[DIVIDES_ZERO] THEN
        ASM_ARITH_TAC;
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    SIMP_TAC[GSYM SUM_CONST; FINITE_PRIMITIVE_CHARACTERS] THEN
    MATCH_MP_TAC SUM_LE THEN
    REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS; IN_ELIM_THM] THEN
    X_GEN_TAC `c:num->complex` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`&x:real`; `r:num`; `c:num->complex`]) THEN
    REWRITE_TAC[ASSUME `&x / log(&x) pow A = Y`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&q` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ASM_MESON_TAC[primitive_character];
      ASM_MESON_TAC[PRIMITIVE_CHARACTER_NONPRINCIPAL]];
    ALL_TAC] THEN
  ABBREV_TAC `e = abs(&(CARD {p | prime p /\ p <= x /\ (p == a) (mod q)}) -
                      &(CARD {p | prime p /\ p <= x}) / &(phi q))` THEN
  ABBREV_TAC `ip = inv(&(phi q))` THEN
  SUBGOAL_THEN `&0 <= ip /\ ip <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ip" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ip * s <= &1 * s /\ ip * T0 <= &1 * T0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K * Y) * C0 <= (K * Y) * abs C0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `T0 * &1 <= T0 * (D * Y)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&2 * &q pow A) * Y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`ip * s <= &1 * s`; `ip * T0 <= &1 * T0`; `s <= K * (C0 * Y)`;
    `(K * Y) * C0 <= (K * Y) * abs C0`; `T0 * &1 <= T0 * (D * Y)`;
    `&0 <= (&2 * &q pow A) * Y`] THEN
  REAL_ARITH_TAC);;

let PNT_AP = prove
 (`!q a. 1 <= q /\ coprime(a,q)
         ==> ((\n. &(CARD {p | prime p /\ p <= n /\ (p == a) (mod q)}) /
                   (&n / log(&n))) ---> inv(&(phi q))) sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `C:real` o SPEC `2` o MATCH_MP PRIMES_AP_ERROR) THEN
  MATCH_MP_TAC REALLIM_TRANSFORM THEN
  EXISTS_TAC `\n. inv(&(phi q)) *
                  &(CARD {p | prime p /\ p <= n}) / (&n / log(&n))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REALLIM_LMUL THEN REWRITE_TAC[PNT]] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. abs C * inv(log(&n))` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REALLIM_NULL_LMUL THEN REWRITE_TAC[REALLIM_1_OVER_LOG]] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `2` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `a:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < log(&n) /\ &0 < &n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC LOG_POS_LT; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `a1 = &(CARD {p | prime p /\ p <= n /\ (p == a) (mod q)})` THEN
  ABBREV_TAC `b1 = &(CARD {p | prime p /\ p <= n})` THEN
  ABBREV_TAC `l = log(&n)` THEN ABBREV_TAC `m = &n` THEN
  ABBREV_TAC `f = &(phi q)` THEN
  SUBGOAL_THEN `&0 < m / l` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(f:real) * b1 / (m / l) - a1 / (m / l) = --((a1 - b1 / f) / (m / l))`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_NEG] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`;
               REAL_LE_LDIV_EQ] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(C:real) * m / l pow 2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(abs C * inv l) * m / l = abs C * m / l pow 2` SUBST1_TAC
  THENL [UNDISCH_TAC `&0 < l` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE]);;
