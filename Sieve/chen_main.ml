(* ========================================================================= *)
(* Chen's theorem from the bound for S(B) ([N] 10.8).                        *)
(*                                                                           *)
(* CHEN_FROM_SB_GEN: if chen_sieve_ok h and, for every e > 0,                *)
(*   S_B <= (A c_B / 4 + e) (N / log N) V(N^(1/8))     (large even N),       *)
(* for the shift h(N), some c > 0 has, for all large even N,                 *)
(*   #{n in gchen_A (h N) N | n = P2} >= c N / log^2 N.                      *)
(* Here c_B = chen_cB = G(1/3) - G(1/8) for                                  *)
(*   G(b) = 9/2 (b + b^2) + 5/6 log b + 20/3 log(1 - b),                     *)
(* an antiderivative of P(1 - 3b)/(b (1 - b)), P(x) = x - x^2/2 + x^3/3,     *)
(* which bounds [N]'s int log(2 - 3b)/(b (1 - b)): c_B = 0.3717 (true        *)
(* 0.3631).  Combining CHEN_SIFT_LOWER_GEN (f(4) = A log 3/4),               *)
(* CHEN_SUM_AQ_UPPER_GEN (A log 6/4) and CHEN_WEIGHTS_GEN gives the          *)
(* coefficient                                                               *)
(*   (A/8) (log(3/2) - c_B) - O(e)  with  log(3/2) - c_B >= 1/30             *)
(* (CHEN_CONSTANT_POS, from log 2 <= 0.69315, log 3 >= 1.0986 and            *)
(* log 7 >= 1.9459, all by the Taylor bound REAL_EXP_TAYLOR of nt.ml).       *)
(* ========================================================================= *)

needs "Sieve/chen_aq.ml";;
needs "Sieve/chen_weights.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The coefficient in the upper bound for S(B).                              *)
(* ------------------------------------------------------------------------- *)

let chen_cB = new_definition
 `chen_cB =
    (&9 / &2 * (&1 / &3 + (&1 / &3) pow 2) + &5 / &6 * log(&1 / &3) +
     &20 / &3 * log(&1 - &1 / &3)) -
    (&9 / &2 * (&1 / &8 + (&1 / &8) pow 2) + &5 / &6 * log(&1 / &8) +
     &20 / &3 * log(&1 - &1 / &8))`;;

let CHEN_CONSTANT_POS = prove
 (`&1 / &30 <=
   log(&3 / &2) -
   ((&9 / &2 * (&1 / &3 + (&1 / &3) pow 2) + &5 / &6 * log(&1 / &3) +
     &20 / &3 * log(&1 - &1 / &3)) -
    (&9 / &2 * (&1 / &8 + (&1 / &8) pow 2) + &5 / &6 * log(&1 / &8) +
     &20 / &3 * log(&1 - &1 / &8)))`,
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &1 /\ &0 < &2 /\ &0 < &3 /\ &0 < &7 /\
                                &0 < &8`; LOG_1] THEN
  SUBGOAL_THEN `log(&8) = &3 * log(&2)` SUBST1_TAC THENL
   [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC LOG_2_UPPER THEN MP_TAC LOG_3_LOWER THEN MP_TAC LOG_7_LOWER THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The lower-order terms.                                                    *)
(* ------------------------------------------------------------------------- *)

let EXP_GE_CUBE = prove
 (`!t. &0 <= t ==> t pow 3 / &27 <= exp t`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`3`; `t:real`] EXP_GE_POW) THEN
  ASM_REWRITE_TAC[REAL_POW_DIV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let CHEN_ERROR_SMALL = prove
 (`!c. &0 < c
       ==> ?N0. !N. N0 <= N
                    ==> &3 * &N / exp(&1 / &8 * log(&N)) +
                        exp(&1 / &3 * log(&N))
                        <= c * &N / log(&N) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&110592 / c + &16` EVENTUALLY_LOG_GE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN EXISTS_TAC `N0 + 3` THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `LN = log(&N)` THEN
  SUBGOAL_THEN `&0 <= &110592 / c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&16 <= LN /\ &110592 / c <= LN` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp LN = &N` ASSUME_TAC THENL
   [EXPAND_TAC "LN" THEN ASM_SIMP_TAC[EXP_LOG]; ALL_TAC] THEN
  SUBGOAL_THEN `exp(&1 / &3 * LN) <= &N / exp(&1 / &8 * LN)` ASSUME_TAC THENL
   [SIMP_TAC[REAL_LE_RDIV_EQ; REAL_EXP_POS_LT; GSYM REAL_EXP_ADD] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `exp LN = &N`)) THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&4 * &N / exp(&1 / &8 * LN)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(LN / &8) pow 3 / &27 <= exp(&1 / &8 * LN)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&1 / &8 * LN = LN / &8`] THEN
    MATCH_MP_TAC EXP_GE_CUBE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < LN pow 2 /\ &0 < exp(&1 / &8 * LN)` STRIP_ASSUME_TAC
  THENL
   [REWRITE_TAC[REAL_EXP_POS_LT] THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SIEVE_MUL_DIV_ASSOC] THEN ASM_SIMP_TAC[RAT_LEMMA4] THEN
  REWRITE_TAC[REAL_ARITH `(&4 * n) * l = n * (&4 * l)`;
              REAL_ARITH `((c:real) * n) * e = n * (c * e)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c * (LN / &8) pow 3 / &27` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `c * (LN / &8) pow 3 / &27 = (c * LN) * LN pow 2 / &13824`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_DIV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&110592 <= c * LN` ASSUME_TAC THENL
     [UNDISCH_TAC `&110592 / c <= LN` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&110592 * LN pow 2 <= (c * LN) * LN pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= LN pow 2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* ------------------------------------------------------------------------- *)
(* Assembly.                                                                 *)
(* ------------------------------------------------------------------------- *)

let CHEN_FROM_SB_GEN = prove
 (`!h. chen_sieve_ok h /\
       (!e. &0 < e
            ==> ?N0. !N. EVEN N /\ N0 <= N
                         ==> &(CARD {p1,p2,p3 |
                                     (p1,p2,p3) IN chen_T (h N) N /\
                                     !q. prime q /\
                                         &q < exp(&1 / &3 * log(&N))
                                         ==> ~(q divides
                                               chen_dist (h N)
                                                 (p1 * p2 * p3))})
                             <= (sieve_A * chen_cB / &4 + e) * &N / log(&N) *
                                product {p | prime p /\
                                             &p < exp(&1 / &8 * log(&N))}
                                        (\p. &1 - chen_g (h N) p))
       ==> ?c N0. &0 < c /\
                  !N. EVEN N /\ N0 <= N
                      ==> c * &N / log(&N) pow 2 <=
                          &(CARD {n | n IN gchen_A (h N) N /\
                                      almost_prime 2 n})`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC SIEVE_A_GE_3 THEN DISCH_TAC THEN
  ABBREV_TAC `e = sieve_A / &1000` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`&1 / &8`; `e:real`] o
    MATCH_MP CHEN_SIFT_LOWER_GEN) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `e:real` o MATCH_MP CHEN_SUM_AQ_UPPER_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th ->
    can (find_term ((=) `chen_cB`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N3:num`) THEN
  X_CHOOSE_THEN `c0:real` STRIP_ASSUME_TAC CHEN_V_LOWER THEN
  ABBREV_TAC `kap = &13 * sieve_A / &6000` THEN
  SUBGOAL_THEN `&0 < kap` ASSUME_TAC THENL
   [EXPAND_TAC "kap" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &4 * c0 * kap` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPEC `&2 * c0 * kap` CHEN_ERROR_SMALL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N4:num`) THEN
  EXISTS_TAC `&4 * c0 * kap` THEN EXISTS_TAC `N1 + N2 + N3 + N4 + 257` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num` o check (fun th ->
    can (find_term ((=) `kap:real`)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `N1 + N2 + N3 + N4 + 257 <= N` THEN ARITH_TAC;
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num` o check (fun th ->
    can (find_term ((=) `chen_cB`)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `N1 + N2 + N3 + N4 + 257 <= N` THEN ARITH_TAC;
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num` o check (fun th ->
    can (find_term ((=) `log(&6)`)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `N1 + N2 + N3 + N4 + 257 <= N` THEN ARITH_TAC;
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num` o check (fun th ->
    can (find_term ((=) `sieve_f`)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `N1 + N2 + N3 + N4 + 257 <= N` THEN ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`(h:num->num) N`; `N:num`] CHEN_WEIGHTS_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `N1 + N2 + N3 + N4 + 257 <= N` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `EVEN((h:num->num) N)` ASSUME_TAC THENL
   [UNDISCH_TAC `chen_sieve_ok h` THEN REWRITE_TAC[chen_sieve_ok] THEN
    DISCH_THEN(MP_TAC o SPEC `N:num` o CONJUNCT1) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `N1 + N2 + N3 + N4 + 257 <= N` THEN ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&8 * log(&2) <= log(&N) /\ &0 < log(&N) /\ &0 < &N`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      UNDISCH_TAC `N1 + N2 + N3 + N4 + 257 <= N` THEN ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      UNDISCH_TAC `N1 + N2 + N3 + N4 + 257 <= N` THEN ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN
      UNDISCH_TAC `N1 + N2 + N3 + N4 + 257 <= N` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= exp(&1 / &8 * log(&N))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log(&2))` THEN
    CONJ_TAC THENL
     [SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`; REAL_LE_REFL];
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(h:num->num) N`; `exp(&1 / &8 * log(&N))`] o
    check (fun th -> can (find_term ((=) `c0:real`)) (concl th) &&
                     is_forall(concl th))) THEN
  ASM_REWRITE_TAC[LOG_EXP] THEN DISCH_TAC THEN
  MP_TAC(SPEC `&4` SIEVE_LOWER_24_EXPLICIT) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `sieve_A * (&1 / &30) <= sieve_A * (log(&3) - log(&2) - chen_cB)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC CHEN_CONSTANT_POS THEN REWRITE_TAC[GSYM chen_cB] THEN
    SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &2 /\ &0 < &3`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&6) = log(&2) + log(&3)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&6 = &2 * &3` SUBST1_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC LOG_MUL THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `LN = log(&N)` THEN
  ABBREV_TAC `z = exp(&1 / &8 * LN)` THEN
  ABBREV_TAC `y = exp(&1 / &3 * LN)` THEN
  ABBREV_TAC
   `V = product {p | prime p /\ &p < z} (\p. &1 - chen_g ((h:num->num) N) p)`
  THEN
  ABBREV_TAC `SA = sifted (gchen_A ((h:num->num) N) N) (\n. &1)
                          {p | prime p /\ &p < z}` THEN
  ABBREV_TAC `SQ = sum {q | prime q /\ z <= &q /\ &q < y}
                       (\q. sifted (gchen_A ((h:num->num) N) N)
                                   (\n. if q divides n then &1 else &0)
                                   {p | prime p /\ &p < z})` THEN
  ABBREV_TAC
   `SB = &(CARD {p1,p2,p3 | (p1,p2,p3) IN chen_T ((h:num->num) N) N /\
                            !q. prime q /\ &q < y
                                ==> ~(q divides chen_dist (h N)
                                                (p1 * p2 * p3))})` THEN
  ABBREV_TAC
   `P2 = &(CARD {n | n IN gchen_A ((h:num->num) N) N /\
                     almost_prime 2 n})` THEN
  ABBREV_TAC `M = &N / LN * V` THEN
  SUBGOAL_THEN `&8 * c0 * &N / LN pow 2 <= M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&N / LN * (c0 / (&1 / &8 * LN))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < LN` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&8 * c0 * &N / LN pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `kap * (&8 * c0 * &N / LN pow 2) <= kap * M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(sieve_A / &240 - &2 * e) * M <=
    (sieve_f(&4) - e) * M - (sieve_A * log(&6) / &4 + e) * M / &2 -
    (sieve_A * chen_cB / &4 + e) * M / &2`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `a * M - b * M / &2 - c * M / &2 = (a - b / &2 - c / &2) * (M:real)`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &3 * &N / z /\ &0 <= y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "y" THEN REWRITE_TAC[REAL_EXP_POS_LE]];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`&0 <= &3 * &N / z`; `&0 <= y`;
    `&3 * &N / z + y <= (&2 * c0 * kap) * &N / LN pow 2`;
    `SB <= (sieve_A * chen_cB / &4 + e) * M`;
    `SQ <= (sieve_A * log (&6) / &4 + e) * M`;
    `(sieve_f (&4) - e) * M <= SA`;
    `SA - &1 / &2 * SQ - &1 / &2 * SB <= P2 + &3 * &N / z + &2 * y`;
    `kap * (&8 * c0 * &N / LN pow 2) <= kap * M`;
    `(sieve_A / &240 - &2 * e) * M <=
     (sieve_f(&4) - e) * M - (sieve_A * log(&6) / &4 + e) * M / &2 -
     (sieve_A * chen_cB / &4 + e) * M / &2`] THEN
  EXPAND_TAC "kap" THEN EXPAND_TAC "e" THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;
