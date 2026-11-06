(* ========================================================================= *)
(* The Brun-Titchmarsh theorem: for every e > 0 there is y such that         *)
(*   pi(x;q,a) <= (2 + e) x / (phi(q) log(x/q))   whenever x >= y q,         *)
(* uniformly in q >= 1 and a (BRUN_TITCHMARSH).                              *)
(*                                                                           *)
(* Selberg's sieve (SELBERG_SIEVE, selberg.ml) for the progression           *)
(* A = {n <= x | n == a mod q} with g(p) = 1/p, sifting by the primes        *)
(* p < z that do not divide q, gives for every z >= 2                        *)
(*   pi(x;q,a) <= x / (phi(q) log z) + K z^2 log^4(z^2) + z                  *)
(* (BRUN_TITCHMARSH_SIEVE):                                                  *)
(* * |A_d - x/(qd)| <= 1 for (d,q) = 1, by the Chinese remainder theorem     *)
(*   (AP_MULTIPLES_COUNT, pairs_sieve.ml);                                   *)
(* * G(z) >= (phi(q)/q) log z (SELBERG_G_ONE_LOWER): compare G with          *)
(*   sum 1/b over the b < z built from the sifting primes                    *)
(*   (SELBERG_G_COMPARISON, pairs_sieve.ml), then SUM_RECIP_COPRIME and      *)
(*   phi(n)/n = prod_{p | n} (1 - 1/p) (PHI_PRODUCT_PRIMES);                 *)
(* * sum_{d < Y} 4^omega(d) <= K Y log^4 Y, d squarefree, by Rankin's        *)
(*   trick and Mertens (SUM_FOUR_POW_CARD).                                  *)
(* The level is z = exp(L/2 - 3 log L) = sqrt(x/q) / L^3, L = log(x/q).      *)
(* ========================================================================= *)

needs "Sieve/brun.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Euler's function and the Selberg main term in dimension 1.                *)
(* ------------------------------------------------------------------------- *)

let PHI_PRODUCT_PRIMES = prove
 (`!n. ~(n = 0)
       ==> &(phi n) =
           &n * product {p | prime p /\ p divides n} (\p. &1 - inv(&p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {p | prime p /\ p divides n}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_PRIME_DIVISORS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[PHI_EXPAND] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
    [SYM(MATCH_MP PRIME_FACTORIZATION th)]) THEN
  ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT; GSYM PRODUCT_MUL] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(index p n = 0) /\ 2 <= p` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INDEX_EQ_0] THEN ASM_MESON_TAC[PRIME_1; PRIME_GE_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `?k. index p n = k + 1` (X_CHOOSE_THEN `k:num` SUBST1_TAC)
  THENL [EXISTS_TAC `index p n - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_SUB; EXP_ADD; EXP_1] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUB;
               GSYM REAL_OF_NUM_POW; ARITH_RULE `2 <= p ==> 1 <= p`] THEN
  SUBGOAL_THEN `&0 < &p` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let SMOOTH_RECIP_SPLIT = prove
 (`!s p y.
        prime p /\ p IN s
        ==> {b | 1 <= b /\ &b < y /\ !r. prime r /\ r divides b ==> r IN s} =
            {b | 1 <= b /\ &b < y /\ ~(p divides b) /\
                 !r. prime r /\ r divides b ==> r IN s} UNION
            IMAGE (\c. p * c)
                  {b | 1 <= b /\ &b < y / &p /\
                       !r. prime r /\ r divides b ==> r IN s}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &p /\ ~(p = 0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `b:num` THEN ASM_CASES_TAC `(p:num) divides b` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `c:num` SUBST_ALL_TAC o
      REWRITE_RULE[divides]) THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; GSYM REAL_OF_NUM_MUL] THEN
    ASM_REWRITE_TAC[EQ_MULT_LCANCEL; UNWIND_THM1] THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(c <=> c') /\ (b <=> b')
                       ==> (a /\ b /\ c <=> a /\ b' /\ c')`) THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    ASM_CASES_TAC `prime r` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN
    ASM_MESON_TAC[DIVIDES_PRIME_PRIME];
    REWRITE_TAC[TAUT `(a <=> a \/ b) <=> (b ==> a)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~((p:num) divides b)` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL]]);;

let SMOOTH_RECIP_STEP = prove
 (`!s p y.
        prime p /\ p IN s
        ==> sum {b | 1 <= b /\ &b < y /\
                     !r. prime r /\ r divides b ==> r IN s} (\b. inv(&b))
            <= sum {b | 1 <= b /\ &b < y /\
                        !r. prime r /\ r divides b ==> r IN s DELETE p}
                   (\b. inv(&b)) +
               inv(&p) *
               sum {b | 1 <= b /\ &b < y / &p /\
                        !r. prime r /\ r divides b ==> r IN s}
                   (\b. inv(&b))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:num->bool`; `p:num`; `y:real`] SMOOTH_RECIP_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [th]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_IMAGE; FINITE_RECIP_RANGE] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; IN_IMAGE;
                NOT_IN_EMPTY] THEN
    MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_RECIP_RANGE; REAL_LE_INV_EQ; REAL_POS] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE] THEN
    X_GEN_TAC `b:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EQ_MULT_LCANCEL] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL; o_DEF; GSYM REAL_OF_NUM_MUL; REAL_INV_MUL;
              REAL_LE_REFL]);;

let SELBERG_G_RECIP = prove
 (`!s y. FINITE s /\ (!p. p IN s ==> prime p)
         ==> sum {b | 1 <= b /\ &b < y /\
                      !r. prime r /\ r divides b ==> r IN s} (\b. inv(&b))
             <= selberg_G (\p. inv(&p)) s y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\s y. sum {b | 1 <= b /\ &b < y /\
                    !r. prime r /\ r divides b ==> r IN s} (\b. inv(&b))`;
    `\p:num. inv(&p)`; `{p | prime p}`] SELBERG_G_COMPARISON) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM]] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `p:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_SIMP_TAC[PRIME_GE_2]; ALL_TAC] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`t:num->bool`; `w:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    UNDISCH_TAC `&b < w` THEN UNDISCH_TAC `w <= &1` THEN
    UNDISCH_TAC `1 <= b` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `w:real` THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum {1} (\b. inv(&b))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_SING; REAL_LE_INV_EQ; REAL_POS] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `b:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `b = 1` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(X_CHOOSE_TAC `r:num` o MATCH_MP PRIME_FACTOR) THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[SUM_SING; REAL_INV_1; REAL_LE_REFL]];
    MAP_EVERY X_GEN_TAC [`t:num->bool`; `p:num`; `w:real`] THEN
    STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC SMOOTH_RECIP_STEP THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(t:num->bool) SUBSET {p | prime p}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let SELBERG_G_ONE_LOWER = prove
 (`!q z. 1 <= q /\ &1 <= z
         ==> &(phi q) / &q * log z <=
             selberg_G (\p. inv(&p)) {p | prime p /\ &p < z /\ ~(p divides q)}
                       z`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = {p | prime p /\ &p < z /\ ~(p divides q)}` THEN
  ABBREV_TAC `P = {p | prime p /\ p divides q}` THEN
  SUBGOAL_THEN `FINITE(P:num->bool) /\ (!p. p IN P ==> prime p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN
    ASM_SIMP_TAC[FINITE_PRIME_DIVISORS; IN_ELIM_THM;
                 ARITH_RULE `1 <= q ==> ~(q = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(s:num->bool) /\ (!p. p IN s ==> prime p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{p | prime p /\ &p < z}` THEN
      REWRITE_TAC[FINITE_PRIMES_LT] THEN SET_TAC[];
      SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {b | 1 <= b /\ &b < z /\
                       !r. prime r /\ r divides b ==> r IN s}
                  (\b. inv(&b))` THEN
  ASM_SIMP_TAC[SELBERG_G_RECIP] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {b | 1 <= b /\ &b < z /\ !p. p IN P ==> ~(p divides b)}
                  (\b. inv(&b))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `product P (\p. &1 - inv(&p)) *
                sum {b | 1 <= b /\ &b < z} (\b. inv(&b))` THEN
    ASM_SIMP_TAC[SUM_RECIP_COPRIME] THEN
    SUBGOAL_THEN `&(phi q) / &q = product P (\p. &1 - inv(&p))`
    SUBST1_TAC THENL
     [EXPAND_TAC "P" THEN
      ASM_SIMP_TAC[PHI_PRODUCT_PRIMES; ARITH_RULE `1 <= q ==> ~(q = 0)`] THEN
      MATCH_MP_TAC(REAL_FIELD `~(a = &0) ==> (a * x) / a = x`) THEN
      REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
      MATCH_MP_TAC LOG_LE_RECIP_SUM THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_RECIP_RANGE; REAL_LE_INV_EQ; REAL_POS] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `b:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `r <= b:num` MP_TAC THENL
       [MP_TAC(SPECL [`r:num`; `b:num`] DIVIDES_LE) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `1 <= b` THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN
      EXPAND_TAC "P" THEN ASM_REWRITE_TAC[IN_ELIM_THM]]]);;

(* ------------------------------------------------------------------------- *)
(* The remainder: residue classes and sums of 4^omega(d).                    *)
(* ------------------------------------------------------------------------- *)

let SUM_FOUR_POW_CARD = prove
 (`?K. &0 < K /\
       !s Y. FINITE s /\ (!p. p IN s ==> prime p) /\ &2 <= Y
             ==> sum {t | t SUBSET s /\ &(nproduct t (\p. p)) < Y}
                     (\t. &4 pow CARD t)
                 <= K * Y * log Y pow 4`,
  X_CHOOSE_TAC `M:real` MERTENS_RECIP_LT THEN
  EXISTS_TAC `exp(&4 * (abs M + &51 / log(&2)))` THEN
  REWRITE_TAC[REAL_EXP_POS_LT] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `s1 = {p | p IN s /\ &p < Y}` THEN
  SUBGOAL_THEN `FINITE(s1:num->bool) /\ s1 SUBSET s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:num->bool` THEN
      REWRITE_TAC[ASSUME `FINITE(s:num->bool)`] THEN SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log Y /\ log(&2) <= log Y /\ &0 < log(&2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t | t SUBSET s1} (\t. Y * product t (\p. &4 / &p))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {t | t SUBSET s /\ &(nproduct t (\p. p)) < Y}
                    (\t. Y * product t (\p. &4 / &p))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{t:num->bool | t SUBSET s}` THEN
        ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `FINITE(t:num->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= &(nproduct t (\p. p))` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
        ASM_SIMP_TAC[NPRODUCT_EQ_0] THEN
        ASM_MESON_TAC[PRIME_IMP_NZ; SUBSET];
        ALL_TAC] THEN
      SUBGOAL_THEN `product t (\p. &4 / &p) =
                    &4 pow CARD t / &(nproduct t (\p. p))` SUBST1_TAC THENL
       [ASM_SIMP_TAC[PRODUCT_DIV; PRODUCT_CONST; REAL_OF_NUM_NPRODUCT];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(nproduct t (\p. p)) *
                  &4 pow CARD t / &(nproduct t (\p. p))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      ASM_SIMP_TAC[FINITE_POWERSET] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `t:num->bool` THEN
        STRIP_TAC THEN X_GEN_TAC `p:num` THEN
        DISCH_TAC THEN EXPAND_TAC "s1" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `&(nproduct t (\p. p))` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_OF_NUM_LE] THEN
        SUBGOAL_THEN `FINITE(t:num->bool)` ASSUME_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:num->bool` THEN
          ASM_REWRITE_TAC[SUBSET];
          ALL_TAC] THEN
        SUBGOAL_THEN `~(nproduct t (\p. p) = 0)` ASSUME_TAC THENL
         [ASM_SIMP_TAC[NPRODUCT_EQ_0] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
          X_GEN_TAC `r:num` THEN STRIP_TAC THEN
          SUBGOAL_THEN `prime r` MP_TAC THENL
           [ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[PRIME_IMP_NZ]];
          ALL_TAC] THEN
        SUBGOAL_THEN `p divides nproduct t (\p. p)` ASSUME_TAC THENL
         [MP_TAC(SPECL [`p:num`; `t:num->bool`]
            PRIME_DIVIDES_NPRODUCT_PRIMES) THEN
          ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ASM_SIMP_TAC[]];
          ALL_TAC] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
        STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC PRODUCT_POS_LE THEN CONJ_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s1:num->bool` THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        REPEAT STRIP_TAC THEN BETA_TAC THEN
        MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  ASM_SIMP_TAC[GSYM PRODUCT_ADD_EXPAND] THEN
  SUBGOAL_THEN `sum s1 (\p. inv(&p)) <= log(log Y) + abs M + &51 / log(&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {p | prime p /\ &p < Y} (\p. inv(&p))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_PRIMES_LT] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "s1" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        ASM_MESON_TAC[];
        REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]];
      FIRST_X_ASSUM(MP_TAC o SPEC `Y:real`) THEN ASM_REWRITE_TAC[] THEN
      ABBREV_TAC `S = sum {p | prime p /\ &p < Y} (\p. inv(&p))` THEN
      SUBGOAL_THEN `&51 / log Y <= &51 / log(&2)` MP_TAC THENL
       [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `Y * exp(&4 * sum s1 (\p. inv(&p)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM SUM_LMUL; REAL_EXP_SUM] THEN
    MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN BETA_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC;
      REWRITE_TAC[real_div; REAL_EXP_LE_X]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `Y * exp(&4 * (log(log Y) + abs M + &51 / log(&2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&4 * (a + b + c) = &4 * a + &4 * (b + c)`] THEN
  REWRITE_TAC[REAL_EXP_ADD; REAL_EXP_N] THEN
  ASM_SIMP_TAC[EXP_LOG] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The theorem.                                                              *)
(* ------------------------------------------------------------------------- *)

let BRUN_TITCHMARSH_SIEVE = prove
 (`?K. !x q a z.
        1 <= q /\ &2 <= z
        ==> &(CARD {p | prime p /\ p <= x /\ (p == a) (mod q)})
            <= &x / (&(phi q) * log z) + K * z pow 2 * log(z pow 2) pow 4 + z`,
  X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC SUM_FOUR_POW_CARD THEN
  EXISTS_TAC `K:real` THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `A = {n | n IN 1..x /\ (n == a) (mod q)}` THEN
  ABBREV_TAC `s = {p | prime p /\ &p < z /\ ~(p divides q)}` THEN
  SUBGOAL_THEN `FINITE(s:num->bool) /\ (!p. p IN s ==> prime p) /\
                FINITE(A:num->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s"; "A"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{p | prime p /\ &p < z}` THEN
      REWRITE_TAC[FINITE_PRIMES_LT] THEN SET_TAC[];
      SIMP_TAC[IN_ELIM_THM];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..x` THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log z /\ &1 < z` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC LOG_POS_LT; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:num->bool`; `\n:num. &1`; `s:num->bool`; `&x / &q`;
                 `\p:num. inv(&p)`; `z:real`] SELBERG_SIEVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
     [X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `2 <= p ==> 1 <= p`) THEN
      ASM_MESON_TAC[PRIME_GE_2];
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&2 <= &p` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_MESON_TAC[PRIME_GE_2];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM selberg_G] THEN
  SUBGOAL_THEN `&x / &q / selberg_G (\p. inv (&p)) s z <=
                &x / (&(phi q) * log z)`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`q:num`; `z:real`] SELBERG_G_ONE_LOWER) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `&1 <= &(phi q) /\ &1 <= &q` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_SIMP_TAC[PHI_LOWERBOUND_1_STRONG];
      ALL_TAC] THEN
    ABBREV_TAC `G = selberg_G (\p. inv (&p)) s z` THEN
    ABBREV_TAC `f = &(phi q)` THEN ABBREV_TAC `m = &q` THEN
    ABBREV_TAC `l = log z` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < f / m * l` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&x / m / (f / m * l)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_REWRITE_TAC[GSYM real_div]];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < l` THEN UNDISCH_TAC `&1 <= m` THEN
      UNDISCH_TAC `&1 <= f` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {t | t SUBSET s /\ &(nproduct t (\p. p)) < z pow 2}
        (\t. &4 pow CARD t *
             abs (sieve_count A (\n. &1) t -
                  &x / &q * product t (\p. inv (&p))))
    <= K * z pow 2 * log(z pow 2) pow 4`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {t | t SUBSET s /\ &(nproduct t (\p. p)) < z pow 2}
                    (\t. &4 pow CARD t)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * &2` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{t:num->bool | t SUBSET s}` THEN
      ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `FINITE(t:num->bool) /\ (!p. p IN t ==> prime p) /\
                  (!p. p IN t ==> ~(p divides q))` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET];
        ASM_MESON_TAC[SUBSET];
        UNDISCH_TAC `(t:num->bool) SUBSET s` THEN EXPAND_TAC "s" THEN
        SIMP_TAC[SUBSET; IN_ELIM_THM]];
      ALL_TAC] THEN
    ABBREV_TAC `d = nproduct t (\p. p)` THEN
    SUBGOAL_THEN `1 <= d /\ coprime(d,q)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "d" THEN CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
        ASM_SIMP_TAC[NPRODUCT_EQ_0] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
        ASM_SIMP_TAC[COPRIME_NPRODUCT_EQ; PRIME_COPRIME_EQ]];
      ALL_TAC] THEN
    SUBGOAL_THEN `sieve_count A (\n. &1) t =
                  &(CARD {n | n IN 1..x /\ (n == a) (mod q) /\ d divides n})`
    SUBST1_TAC THENL
     [REWRITE_TAC[sieve_count] THEN
      SIMP_TAC[SUM_CONST; FINITE_RESTRICT; ASSUME `FINITE(A:num->bool)`] THEN
      REWRITE_TAC[REAL_MUL_RID] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      EXPAND_TAC "A" THEN EXPAND_TAC "d" THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; CONJ_ASSOC] THEN
      X_GEN_TAC `n:num` THEN AP_TERM_TAC THEN
      MATCH_MP_TAC PRIMES_DIVIDE_IFF_NPRODUCT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&x / &q * product t (\p. inv(&p)) = &x / (&q * &d)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[PRODUCT_INV] THEN EXPAND_TAC "d" THEN
      ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT] THEN
      REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC AP_MULTIPLES_COUNT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(CARD {p | prime p /\ p <= x /\ (p == a) (mod q)}) <=
    sifted A (\n. &1) s + z`
  ASSUME_TAC THENL
   [REWRITE_TAC[sifted] THEN
    SIMP_TAC[SUM_CONST; FINITE_RESTRICT; ASSUME `FINITE(A:num->bool)`] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(CARD {n | n IN A /\ !p. p IN s ==> ~(p divides n)}) +
                &(CARD {p | prime p /\ &p < z})` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC CARD_PRIMES_LT_LE THEN
      ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD({n | n IN A /\ !p. p IN s ==> ~(p divides n)} UNION
                     {p | prime p /\ &p < z})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC FINITE_UNION_IMP THEN
        SIMP_TAC[FINITE_RESTRICT; FINITE_PRIMES_LT;
                 ASSUME `FINITE(A:num->bool)`]] THEN
      REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
      X_GEN_TAC `p:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `&p < z` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
        ALL_TAC] THEN
      X_GEN_TAC `r:num` THEN EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `(r:num) = p` SUBST_ALL_TAC THENL
       [MP_TAC(SPECL [`r:num`; `p:num`] DIVIDES_PRIME_PRIME) THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[]];
      MATCH_MP_TAC CARD_UNION_LE THEN
      SIMP_TAC[FINITE_RESTRICT; FINITE_PRIMES_LT;
               ASSUME `FINITE(A:num->bool)`]];
    ALL_TAC] THEN
  ABBREV_TAC `c1 = &(CARD {p | prime p /\ p <= x /\ (p == a) (mod q)})` THEN
  ABBREV_TAC `s1 = sifted A (\n. &1) s` THEN
  ABBREV_TAC `m1 = &x / &q / selberg_G (\p. inv (&p)) s z` THEN
  ABBREV_TAC `r1 = sum {t | t SUBSET s /\ &(nproduct t (\p. p)) < z pow 2}
        (\t. &4 pow CARD t *
             abs (sieve_count A (\n. &1) t -
                  &x / &q * product t (\p. inv (&p))))` THEN
  MAP_EVERY UNDISCH_TAC
   [`c1 <= s1 + z`; `m1 <= &x / (&(phi q) * log z)`;
    `r1 <= K * z pow 2 * log(z pow 2) pow 4`] THEN
  REAL_ARITH_TAC);;

let BRUN_TITCHMARSH = prove
 (`!e. &0 < e
       ==> ?y. !x q a. 1 <= q /\ y * &q <= &x
                       ==> &(CARD {p | prime p /\ p <= x /\ (p == a) (mod q)})
                           <= (&2 + e) * &x / (&(phi q) * log(&x / &q))`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC `K:real` BRUN_TITCHMARSH_SIEVE THEN
  ABBREV_TAC `c = e / (&8 + &2 * e)` THEN
  SUBGOAL_THEN `&0 < c /\ &1 / &2 - c = &2 / (&4 + e)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ABBREV_TAC `L0 = &576 + &36 / c pow 2 + &4 * abs K / e + &64 / e` THEN
  EXISTS_TAC `exp L0` THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `q:num`; `a:num`] THEN STRIP_TAC THEN
  ABBREV_TAC `u = &x / &q` THEN
  SUBGOAL_THEN `&0 < &q /\ &1 <= &q` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&x = u * &q` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN UNDISCH_TAC `&0 < &q` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp L0 <= u` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < u /\ L0 <= log u` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `L0:real` REAL_EXP_POS_LT) THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `L = log u` THEN
  SUBGOAL_THEN `&0 <= &36 / c pow 2 /\ &0 <= &4 * abs K / e /\
                &0 <= &64 / e`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&576 <= L /\ &36 / c pow 2 <= L /\ &4 * abs K / e <= L /\
                &64 / e <= L`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `L0 <= L` THEN EXPAND_TAC "L0" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log L /\ &3 * log L <= L / &4 /\ &3 * log L <= c * L`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`1`; `L:real`] LOG_POW_LE_SQRT) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_1; REAL_MUL_RID] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= sqrt L /\ sqrt L * sqrt L = L` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_2] THEN
      ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2;
                   REAL_ARITH `&576 <= L ==> &0 <= L`];
      ALL_TAC] THEN
    SUBGOAL_THEN `&24 <= sqrt L /\ &6 / c <= sqrt L` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `&24 = sqrt(&576)` SUBST1_TAC THENL
         [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN
          CONV_TAC REAL_RAT_REDUCE_CONV;
          MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN `&6 / c = sqrt(&36 / c pow 2)` SUBST1_TAC THENL
         [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
            UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD];
          MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&24 * sqrt L <= sqrt L * sqrt L /\
                  &6 * sqrt L <= (c * sqrt L) * sqrt L`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&6 / c <= sqrt L` THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&24 * sqrt L <= sqrt L * sqrt L` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `log L <= &2 * sqrt L` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&6 * sqrt L <= (c * sqrt L) * sqrt L` THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `log L <= &2 * sqrt L` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `w = L / &2 - &3 * log L` THEN
  SUBGOAL_THEN `L / &4 <= w /\ &2 / (&4 + e) * L <= w /\ w <= L / &2 /\
                &2 * w <= L`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN
    SUBGOAL_THEN `&2 / (&4 + e) * L = L / &2 - c * L` SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        lhand(concl th) = `&1 / &2 - c`)) THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `z = exp w` THEN
  SUBGOAL_THEN `&2 <= z /\ log z = w /\ log(z pow 2) = &2 * w /\
                z pow 2 * L pow 6 = u`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[LOG_EXP; GSYM REAL_EXP_N] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + w` THEN
      REWRITE_TAC[REAL_EXP_LE_X] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `L pow 6 = exp(&6 * log L)` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_EXP_N] THEN
      ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&576 <= L ==> &0 < L`];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_EXP_ADD] THEN EXPAND_TAC "w" THEN
    SUBGOAL_THEN `u = exp L` SUBST1_TAC THENL
     [EXPAND_TAC "L" THEN ASM_SIMP_TAC[EXP_LOG]; ALL_TAC] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `q:num`; `a:num`; `z:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `log z = w`; ASSUME `log(z pow 2) = &2 * w`] THEN
  ABBREV_TAC `X = &x / (&(phi q) * L)` THEN
  SUBGOAL_THEN `&1 <= &(phi q) /\ &(phi q) <= &q` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_SIMP_TAC[PHI_LOWERBOUND_1_STRONG; PHI_LIMIT];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L /\ &0 < w` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&x / (&(phi q) * w) <= (&2 + e / &2) * X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN
    SUBGOAL_THEN `&0 < &2 / (&4 + e) * L` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&x / (&(phi q) * (&2 / (&4 + e) * L))` THEN CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[GSYM real_div] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < L` THEN UNDISCH_TAC `&1 <= &(phi q)` THEN
      UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `u / L <= X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN SUBST1_TAC(SYM(ASSUME `&x / &q = u:real`)) THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u = exp(L / &2) * exp(L / &2)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_ARITH `L / &2 + L / &2 = L`] THEN
    EXPAND_TAC "L" THEN ASM_SIMP_TAC[EXP_LOG];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * L <= e * exp(L / &2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(L / &4) pow 2 <= exp(L / &2)` ASSUME_TAC THENL
     [SUBGOAL_THEN `exp(L / &2) = exp(L / &4) pow 2` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + L / &4` THEN
      REWRITE_TAC[REAL_EXP_LE_X] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `e * (L / &4) pow 2 <= e * exp(L / &2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    UNDISCH_TAC `&64 / e <= L` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= L * (L * e - &64)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `z <= e / &4 * (u / L)` ASSUME_TAC THENL
   [SUBGOAL_THEN `e / &4 * (u / L) = (e / &4 * u) / L` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `z <= exp(L / &2)` ASSUME_TAC THENL
     [EXPAND_TAC "z" THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= L * (exp(L / &2) - z) /\
                  &0 <= exp(L / &2) * (e * exp(L / &2) - &4 * L)`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBST1_TAC(ASSUME `u = exp(L / &2) * exp(L / &2)`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `K * z pow 2 * (&2 * w) pow 4 <= e / &4 * (u / L)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= z pow 2 /\ (&2 * w) pow 4 <= L pow 4 /\
                  &0 <= (&2 * w) pow 4`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs K * z pow 2 * L pow 4` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs K * z pow 2 * (&2 * w) pow 4` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&4 * abs K <= e * L` ASSUME_TAC THENL
     [UNDISCH_TAC `&4 * abs K / e <= L` THEN
      SUBGOAL_THEN `&4 * abs K / e = (&4 * abs K) / e` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `e / &4 * (u / L) - abs K * z pow 2 * L pow 4 =
                  (z pow 2 * L pow 4) * ((e * L - &4 * abs K) / &4)`
    MP_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `z pow 2 * L pow 6 = u:real`)) THEN
      UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= c ==> a - b = c ==> b <= a`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `e / &4 * (u / L) <= e / &4 * X` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c1 = &(CARD {p | prime p /\ p <= x /\ (p == a) (mod q)})` THEN
  MAP_EVERY UNDISCH_TAC
   [`&x / (&(phi q) * w) <= (&2 + e / &2) * X`;
    `K * z pow 2 * (&2 * w) pow 4 <= e / &4 * (u / L)`;
    `z <= e / &4 * (u / L)`; `e / &4 * (u / L) <= e / &4 * X`] THEN
  REAL_ARITH_TAC);;
