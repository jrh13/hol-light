(* ========================================================================= *)
(* The Goldbach-Shnirel'man theorem ([N] 7.5): every integer n >= 2 is a     *)
(* sum of at most C primes (GOLDBACH_SHNIRELMAN).                            *)
(*                                                                           *)
(* With r(N) = goldbach_r N = #{p <= N | p, N - p prime}:                    *)
(* * SUM_GOLDBACH_R_LOWER: sum_{N <= x} r(N) >= pi(x/2)^2;                   *)
(* * SUM_GOLDBACH_R_SQUARE: sum_{N <= x} r(N)^2 <= K x^3 / (log x)^4, from   *)
(*   GOLDBACH_SELBERG and the average SUM_INV_V_POW4 of                      *)
(*   prod_{p | N} (1 - 1/p)^-4 (expand over subsets of the prime divisors,   *)
(*   count multiples, bound prod (1 + 30/p^2) by exp(45));                   *)
(* * Cauchy-Schwarz and PNT (pi(x) >= x / (2 log x) eventually) give         *)
(*   GOLDBACH_SUMS_DENSE: a positive proportion of N <= x are p + q;         *)
(* * so {1} UNION {p + q} has positive Shnirel'man density                   *)
(*   (GOLDBACH_SET_DENSITY); by SCHNIRELMANN_DIRECT of                       *)
(*   Examples/schnirelmann.ml every n is a sum of boundedly many of its      *)
(*   elements, and the 1s are absorbed by 2s and a 3.                        *)
(* ========================================================================= *)

needs "Sieve/brun.ml";;
needs "Examples/schnirelmann.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Averages of prod_{p | N} (1 + h(p)) with h(p) <= C/p.                     *)
(* ------------------------------------------------------------------------- *)

let SUM_PRIME_DIVISOR_PRODUCT = prove
 (`!h C x.
        &0 <= C /\ (!p. prime p ==> &0 <= h p /\ h p <= C / &p)
        ==> sum (1..x) (\N. product {p | prime p /\ p divides N}
                                    (\p. &1 + h p))
            <= &x * exp(&3 / &2 * C)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P = {p | prime p /\ p <= x}` THEN
  SUBGOAL_THEN `FINITE(P:num->bool) /\ (!p. p IN P ==> prime p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..x` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!N. N IN 1..x
        ==> product {p | prime p /\ p divides N} (\p. &1 + h p) =
            sum {t | t SUBSET P}
                (\t. if t SUBSET {p | prime p /\ p divides N}
                     then product t h else &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `N:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_ADD_EXPAND o lhand o snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FINITE_PRIME_DIVISORS THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC SUM_POWERSET_RESTRICT THEN EXPAND_TAC "P" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`p:num`; `N:num`] DIVIDES_LE) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `1 <= N` THEN UNDISCH_TAC `N <= x:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_EQ_NUMSEG; GSYM IN_NUMSEG] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; FINITE_POWERSET] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t | t SUBSET P}
                  (\t. &x * product t (\p. (h:num->real) p / &p))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_POWERSET] THEN
    X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE(t:num->bool) /\ (!p. p IN t ==> prime p)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG] THEN
    SUBGOAL_THEN
     `{N | N IN 1..x /\ t SUBSET {p | prime p /\ p divides N}} =
      {N | N IN 1..x /\ nproduct t (\p. p) divides N}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `N:num` THEN
      AP_TERM_TAC THEN ASM_SIMP_TAC[GSYM PRIMES_DIVIDE_IFF_NPRODUCT] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &(nproduct t (\p. p)) /\ &0 <= product t h`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[NPRODUCT_EQ_0; FINITE_RESTRICT] THEN
        ASM_MESON_TAC[PRIME_IMP_NZ];
        MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&x / &(nproduct t (\p. p))) * product t h` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CARD_MULTIPLES_LE THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[PRODUCT_DIV; REAL_OF_NUM_NPRODUCT] THEN
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_LMUL; GSYM PRODUCT_ADD_EXPAND] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `product P (\p. exp((h:num->real) p / &p))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[REAL_EXP_LE_X] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_MESON_TAC[REAL_POS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_EXP_SUM; REAL_EXP_MONO_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C * sum P (\p. inv(&p pow 2))` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &p` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C / &p` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2; REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `&0 < &p` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`&2`; `&x + &1`] SUM_PRIME_SQUARES_TAIL) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> b <= &3 / &2 ==> a <= &3 / &2`) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "P" THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
  ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN
  MP_TAC(SPEC `p:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let PRODUCT_POW_REAL = prove
 (`!f:A->real s n. FINITE s ==> product s (\x. f x pow n) = product s f pow n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[real_pow; PRODUCT_ONE; PRODUCT_MUL]);;

let INV_POW4_BOUND = prove
 (`!y. &0 <= y /\ y <= &1 / &2
       ==> &1 <= inv((&1 - y) pow 4) /\ inv((&1 - y) pow 4) <= &1 + &30 * y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - y /\ &1 - y <= &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_POW_INV] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN MATCH_MP_TAC REAL_INV_1_LE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + &2 * y) pow 4` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&1 - y) * ((&1 - y) * (&1 + &2 * y))` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
      MP_TAC(SPECL [`y:real`; `&1 - &2 * y`] REAL_LE_MUL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `y pow 2 <= y / &2 /\ y pow 3 <= y / &4 /\ y pow 4 <= y / &8`
  MP_TAC THENL
   [REWRITE_TAC[REAL_RING
         `(y:real) pow 3 = y * y pow 2 /\ y pow 4 = y * y pow 3`] THEN
    SUBGOAL_THEN `y pow 2 <= y / &2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      MP_TAC(SPECL [`y:real`; `&1 / &2 - y`] REAL_LE_MUL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `y * y pow 2 <= y / &4` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `y * y / &2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
        MP_TAC(SPECL [`y:real`; `&1 / &2 - y`] REAL_LE_MUL) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `y * y / &4` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`y:real`; `&1 / &2 - y`] REAL_LE_MUL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_POLY_CONV) THEN ASM_REAL_ARITH_TAC);;

let SUM_INV_V_POW4 = prove
 (`!x. sum (1..x) (\N. inv(product {p | prime p /\ p divides N}
                                   (\p. &1 - inv(&p)) pow 4))
       <= &x * exp(&45)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\p. inv((&1 - inv(&p)) pow 4) - &1`; `&30`; `x:num`]
                SUM_PRIME_DIVISOR_PRODUCT) THEN
  REWRITE_TAC[REAL_ARITH `&1 + (x - &1) = x`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
   [X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    MP_TAC(SPEC `inv(&p)` INV_POW4_BOUND) THEN ANTS_TAC THENL
     [SUBGOAL_THEN `&2 <= &p` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_MESON_TAC[PRIME_GE_2];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c:real. a = b ==> b <= c ==> a <= c`) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE {p | prime p /\ p divides N}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_PRIME_DIVISORS THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM PRODUCT_POW_REAL; GSYM PRODUCT_INV]);;

(* ------------------------------------------------------------------------- *)
(* The number of representations as a sum of two primes.                     *)
(* ------------------------------------------------------------------------- *)

let goldbach_r = new_definition
 `goldbach_r N = CARD {p | prime p /\ p <= N /\ prime(N - p)}`;;

let GOLDBACH_R_LE = prove
 (`!N. goldbach_r N <= N`,
  GEN_TAC THEN REWRITE_TAC[goldbach_r] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_1] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
  MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`]);;

let GOLDBACH_R_ODD = prove
 (`!N. ODD N ==> goldbach_r N <= 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[goldbach_r] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {2, N - 2}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    MP_TAC(SPEC `p:num` PRIME_ODD) THEN
    MP_TAC(SPEC `N - p:num` PRIME_ODD) THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `p = 2` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `N - p = 2` THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `ODD(p + (N - p))` MP_TAC THENL
     [SUBGOAL_THEN `p + (N - p) = N:num` SUBST1_TAC THENL
       [UNDISCH_TAC `p <= N:num` THEN ARITH_TAC; ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[ODD_ADD]];
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN ARITH_TAC]);;

let GOLDBACH_R_UNIFORM = prove
 (`!x N. 2 <= x /\ N IN 1..x
         ==> &(goldbach_r N) <=
             sqrt(&x) + &2 +
             (&1792 * &x / log(&x) pow 2) *
             inv(product {p | prime p /\ p divides N}
                         (\p. &1 - inv(&p)) pow 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  ABBREV_TAC `Q = product {p | prime p /\ p divides N} (\p. &1 - inv(&p))` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC PRODUCT_POS_LT THEN
    ASM_SIMP_TAC[FINITE_PRIME_DIVISORS; IN_ELIM_THM;
                 ARITH_RULE `1 <= N ==> ~(N = 0)`] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[REAL_SUB_LT] THEN
    MATCH_MP_TAC REAL_INV_LT_1 THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 < p`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&x) /\ &0 <= sqrt(&x)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1792 * &x / log(&x) pow 2) * inv(Q pow 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  ASM_CASES_TAC `&N <= sqrt(&x)` THENL
   [MP_TAC(SPEC `N:num` GOLDBACH_R_LE) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `ODD N` THENL
   [MP_TAC(SPEC `N:num` GOLDBACH_R_ODD) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `EVEN N /\ 2 <= N` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_ODD] THEN
    UNDISCH_TAC `~ODD N` THEN UNDISCH_TAC `1 <= N` THEN
    REWRITE_TAC[GSYM NOT_EVEN] THEN
    SPEC_TAC(`N:num`,`n:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[EVEN] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `N:num` GOLDBACH_SELBERG) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM goldbach_r] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!r a b s:real. &0 <= s /\ a <= b ==> r <= a ==> r <= s + &2 + b`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `log(&x) / &2 <= log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(sqrt(&x))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[LOG_SQRT; REAL_OF_NUM_LT; ARITH_RULE `2 <= x ==> 0 < x`;
                   REAL_LE_REFL];
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN
        REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&448 * &N / (log(&N) pow 2 * Q pow 2) =
                (&448 * &N) / (log(&N) pow 2 * Q pow 2)`
  SUBST1_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1792 * &x / log(&x) pow 2) * inv(Q pow 2) =
                (&448 * &x) / ((log(&x) / &2) pow 2 * Q pow 2)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < log(&x)`; `&0 < Q`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV_BOTH THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS];
    MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* First and second moments.                                                 *)
(* ------------------------------------------------------------------------- *)

let LOG_POW4_LE = prove
 (`!x. &1 <= x ==> log x pow 4 <= &256 * x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= log x` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(log x / &4) pow 4 <= exp(log x / &4) pow 4` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `log x / &4` REAL_EXP_LE_X) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_EXP_N] THEN
  ASM_SIMP_TAC[REAL_ARITH `&4 * l / &4 = l`; EXP_LOG;
               REAL_ARITH `&1 <= x ==> &0 < x`] THEN
  REWRITE_TAC[REAL_POW_DIV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &256`] THEN REAL_ARITH_TAC);;

let SQUARE_SUM3_LE = prove
 (`!a b c:real. (a + b + c) pow 2 <= &3 * (a pow 2 + b pow 2 + c pow 2)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `a - b:real` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `a - c:real` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `b - c:real` REAL_LE_POW_2) THEN
  REAL_ARITH_TAC);;

let SUM_GOLDBACH_R_SQUARE = prove
 (`?K. !x. 2 <= x
           ==> sum (1..x) (\N. &(goldbach_r N) pow 2) <=
               K * &x pow 3 / log(&x) pow 4`,
  EXISTS_TAC `&3840 + &3 * &1792 pow 2 * exp(&45)` THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 <= &x /\ &0 < log(&x)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC LOG_POS_LT THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c = &1792 * &x / log(&x) pow 2` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (1..x) (\N. &3 * (&x + &4) +
                 &3 * c pow 2 *
                 inv(product {p | prime p /\ p divides N}
                             (\p. &1 - inv(&p)) pow 4))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`x:num`; `N:num`] GOLDBACH_R_UNIFORM) THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN
    ABBREV_TAC `w = inv(product {p | prime p /\ p divides N}
                                (\p. &1 - inv(&p)) pow 2)` THEN
    SUBGOAL_THEN `inv(product {p | prime p /\ p divides N}
                              (\p. &1 - inv(&p)) pow 4) = w pow 2`
    SUBST1_TAC THENL
     [EXPAND_TAC "w" THEN REWRITE_TAC[REAL_POW_INV; REAL_POW_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= w /\ &0 <= c /\ sqrt(&x) pow 2 = &x`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["w"; "c"] THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN
      SIMP_TAC[SQRT_POW_2; REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sqrt(&x)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    ABBREV_TAC `s = sqrt(&x)` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(s + &2 + c * w) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 * (s pow 2 + &2 pow 2 + (c * w) pow 2)` THEN
    REWRITE_TAC[SQUARE_SUM3_LE] THEN
    ASM_REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_CONST_NUMSEG; SUM_LMUL; ADD_SUB] THEN
  MP_TAC(SPEC `x:num` SUM_INV_V_POW4) THEN
  ABBREV_TAC `S = sum (1..x) (\N. inv(product {p | prime p /\ p divides N}
                                              (\p. &1 - inv(&p)) pow 4))` THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `&x` LOG_POW4_LE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `L = log(&x)` THEN
  SUBGOAL_THEN `&0 < L pow 4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c pow 2 = &1792 pow 2 * &x pow 2 / L pow 4` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[REAL_POW_DIV; REAL_POW_MUL] THEN
    REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * c pow 2 * S <=
                (&3 * &1792 pow 2 * exp(&45)) * &x pow 3 / L pow 4`
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 * (&1792 pow 2 * &x pow 2 / L pow 4) * (&x * exp(&45))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * (&x + &4) * &x <= (&3840 * &x pow 3) / L pow 4`
  MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&15 * &x pow 2 * L pow 4` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `(&3 * (x + &4) * x) * l =
                              (&3 * x pow 2 + &12 * x) * l`] THEN
      REWRITE_TAC[REAL_ARITH `&15 * x pow 2 * l = (&15 * x pow 2) * l`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `&12 * x <= &12 * x pow 2
                ==> &3 * x pow 2 + &12 * x <= &15 * x pow 2`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; REAL_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&15 * &x pow 2 * (&256 * &x)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let SUM_GOLDBACH_R_LOWER = prove
 (`!m x. 2 * m <= x
         ==> &(CARD {p | prime p /\ p <= m}) pow 2 <=
             sum (1..x) (\N. &(goldbach_r N))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P = {p | prime p /\ p <= m}` THEN
  SUBGOAL_THEN `FINITE(P:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..m` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(CARD(P:num->bool)) pow 2 = sum (P CROSS P) (\z. &1)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM CARD_EQ_SUM; FINITE_CROSS; CARD_CROSS] THEN
    REWRITE_TAC[REAL_POW_2; REAL_OF_NUM_MUL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:num#num. FST z + SND z`; `\z:num#num. &1`;
                 `(P:num->bool) CROSS P`; `1..x`] SUM_GROUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_CROSS] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS;
                IN_NUMSEG] THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
    MP_TAC(SPEC `p:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p <= m:num` THEN UNDISCH_TAC `q <= m:num` THEN
    UNDISCH_TAC `2 * m <= x` THEN ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SIMP_TAC[GSYM CARD_EQ_SUM; FINITE_RESTRICT; FINITE_CROSS;
           ASSUME `FINITE(P:num->bool)`] THEN
  REWRITE_TAC[REAL_OF_NUM_LE; goldbach_r] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE FST {z | z IN (P:num->bool) CROSS P /\
                                  FST z + SND z = N})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_CROSS] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; PAIR_EQ] THEN ARITH_TAC;
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_PRIMES_LE_RESTRICT] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_THM;
                IN_CROSS] THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `N - p = q:num` SUBST1_TAC THENL
     [UNDISCH_TAC `p + q = N:num` THEN ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    UNDISCH_TAC `p + q = N:num` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A positive proportion of integers are sums of two primes.                 *)
(* ------------------------------------------------------------------------- *)

let PI_LOWER = prove
 (`?N0. !n. N0 <= n
            ==> &n / (&2 * log(&n)) <= &(CARD {p | prime p /\ p <= n})`,
  MP_TAC PNT THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN EXISTS_TAC `N1 + 2` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&n) /\ &0 < &n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC LOG_POS_LT; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `P = &(CARD {p | prime p /\ p <= n})` THEN
  SUBGOAL_THEN `P / (&n / log(&n)) = P * log(&n) / &n /\
                &n / (&2 * log(&n)) = (&n / log(&n)) / &2`
  (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < log(&n)`; `&0 < &n`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&1 / &2 <= P * log(&n) / &n` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_LT_DIV;
               REAL_ARITH `&0 < &2`] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((P * log(&n) / &n) * &2) * &n` THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < &n` THEN
    CONV_TAC REAL_FIELD]);;

let SUM_SQUARE_CAUCHY = prove
 (`!f:A->real s.
        FINITE s ==> sum s f pow 2 <= &(CARD s) * sum s (\x. f x pow 2)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_REWRITE_TAC[SUM_CLAUSES; CARD_CLAUSES] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `&0 < &(CARD(s:A->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN ASM_MESON_TAC[CARD_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sum s (\x. ((f:A->real) x -
                                  sum s f / &(CARD(s:A->bool))) pow 2)`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(a - b) pow 2 = a pow 2 - &2 * b * a + b pow 2`] THEN
  ASM_SIMP_TAC[SUM_SUB; SUM_ADD; SUM_LMUL; SUM_CONST] THEN
  ABBREV_TAC `n = &(CARD(s:A->bool))` THEN
  ABBREV_TAC `S = sum s (f:A->real)` THEN
  ABBREV_TAC `Q = sum s (\x. (f:A->real) x pow 2)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= n * (Q - &2 * S / n * S + n * (S / n) pow 2)` MP_TAC
  THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c:real. a = c - b ==> &0 <= a ==> b <= c`) THEN
  UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD);;

let GOLDBACH_DENSE_ARITH = prove
 (`!X L P S1 S2 t K.
        &0 < X /\ &0 < L /\ &0 <= t /\ X / (&6 * L) <= P /\
        P pow 2 <= S1 /\ S1 pow 2 <= t * S2 /\ S2 <= K * X pow 3 / L pow 4
        ==> inv(&1296 * (abs K + &1)) * X <= t`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `A = X / (&6 * L)` THEN
  SUBGOAL_THEN `&0 < A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `A pow 4 <= t * (abs K + &1) * X pow 3 / L pow 4`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(S1:real) pow 2` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
                      ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(P:real) pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(t:real) * S2` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(K:real) * X pow 3 * inv(L pow 4)` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(S2:real) <= K * X pow 3 / L pow 4` THEN
      REWRITE_TAC[real_div; REAL_MUL_ASSOC];
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `A pow 4 = (X / &1296) * (X pow 3 / L pow 4)` SUBST_ALL_TAC
  THENL
   [EXPAND_TAC "A" THEN UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < X pow 3 / L pow 4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `X / &1296 <= t * (abs K + &1)` MP_TAC THENL
   [UNDISCH_TAC `X / &1296 * X pow 3 / L pow 4 <=
                 t * (abs K + &1) * X pow 3 / L pow 4` THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1296 * (abs K + &1)` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

let GOLDBACH_SUMS_DENSE = prove
 (`?c X0. &0 < c /\
          !x. X0 <= x
              ==> c * &x <= &(CARD {N | N IN 1..x /\ ~(goldbach_r N = 0)})`,
  X_CHOOSE_TAC `N0:num` PI_LOWER THEN
  X_CHOOSE_TAC `K:real` SUM_GOLDBACH_R_SQUARE THEN
  EXISTS_TAC `inv(&1296 * (abs K + &1))` THEN
  EXISTS_TAC `2 * N0 + 6` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  ABBREV_TAC `m = x DIV 2` THEN
  SUBGOAL_THEN `2 * m <= x /\ N0 <= m /\ 2 <= m /\ x <= 3 * m`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`x:num`; `2`] DIVISION) THEN ASM_REWRITE_TAC[ARITH] THEN
    UNDISCH_TAC `2 * N0 + 6 <= x` THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `SR = {N | N IN 1..x /\ ~(goldbach_r N = 0)}` THEN
  SUBGOAL_THEN `FINITE(SR:num->bool) /\ SR SUBSET 1..x` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "SR" THEN SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (1..x) (\N. &(goldbach_r N)) = sum SR (\N. &(goldbach_r N)) /\
    sum (1..x) (\N. &(goldbach_r N) pow 2) =
    sum SR (\N. &(goldbach_r N) pow 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUM_SUPERSET THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "SR" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `N:num` THEN
    ASM_CASES_TAC `goldbach_r N = 0` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\N. &(goldbach_r N)`; `SR:num->bool`] SUM_SQUARE_CAUCHY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o BETA_RULE)] THEN
  MP_TAC(SPECL [`m:num`; `x:num`] SUM_GOLDBACH_R_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (is_forall o concl) o
    check (fun th -> can (find_term ((=) `K:real`)) (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `2 * N0 + 6 <= x` THEN ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC GOLDBACH_DENSE_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`log(&x)`; `&(CARD {p | prime p /\ p <= m})`;
    `sum SR (\N. &(goldbach_r N))`; `sum SR (\N. &(goldbach_r N) pow 2)`] THEN
  REWRITE_TAC[REAL_POS] THEN
  SUBGOAL_THEN `&2 <= &m /\ &m <= &x /\ &x <= &3 * &m` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_MUL] THEN
    MAP_EVERY UNDISCH_TAC [`2 <= m`; `2 * m <= x`; `x <= 3 * m`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&m) /\ log(&m) <= log(&x)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC LOG_POS_LT; MATCH_MP_TAC LOG_MONO_LE_IMP] THEN
    MAP_EVERY UNDISCH_TAC [`&2 <= &m`; `&m <= &x`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&2 <= &m`; `&m <= &x`] THEN REAL_ARITH_TAC;
    MAP_EVERY UNDISCH_TAC [`&0 < log(&m)`; `log(&m) <= log(&x)`] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&m / (&2 * log(&m))` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&x / (&6 * log(&x)) = (&x / &3) / (&2 * log(&x))`
    SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV_BOTH THEN
    MAP_EVERY UNDISCH_TAC [`&2 <= &m`; `&x <= &3 * &m`; `&0 < log(&m)`;
                           `log(&m) <= log(&x)`] THEN
    REAL_ARITH_TAC;
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Every integer >= 2 is a sum of boundedly many primes.                     *)
(* ------------------------------------------------------------------------- *)

let GOLDBACH_SET_DENSITY = prove
 (`schnirelmann ({1} UNION {p + q | prime p /\ prime q}) > &0`,
  X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `X0:num` STRIP_ASSUME_TAC)
    GOLDBACH_SUMS_DENSE THEN
  REWRITE_TAC[real_gt] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `min c (inv(&X0 + &1))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SCHNIRELMANN_LBOUND] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LE_1; count] THEN
  ABBREV_TAC `A = {1} UNION {p + q | prime p /\ prime q}` THEN
  ASM_CASES_TAC `X0 <= n:num` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c * &n` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(CARD {N | N IN 1..n /\ ~(goldbach_r N = 0)})` THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_INTER_NUMSEG] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `N:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(goldbach_r N = 0)` THEN
    REWRITE_TAC[goldbach_r] THEN
    SIMP_TAC[CARD_EQ_0; FINITE_PRIMES_LE_RESTRICT] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "A" THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`p:num`; `N - p:num`] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p <= N:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&X0 + &1) * &n` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &X0 + &1` ASSUME_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `~(X0 <= n:num)` THEN
    REWRITE_TAC[NOT_LE; GSYM REAL_OF_NUM_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {1}` THEN CONJ_TAC THENL
   [REWRITE_TAC[CARD_SING; LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_INTER_NUMSEG] THEN
  REWRITE_TAC[SUBSET; IN_SING; IN_INTER; IN_NUMSEG] THEN
  X_GEN_TAC `y:num` THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[LE_REFL] THEN EXPAND_TAC "A" THEN
  REWRITE_TAC[IN_UNION; IN_INSERT]);;

let ITLIST_ADD_ACC = prove
 (`!l a. ITLIST (+) l a = ITLIST (+) l 0 + a`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; ADD_CLAUSES] THEN
  FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN ARITH_TAC);;

let SUM_OF_TWOS_AND_THREES = prove
 (`!m. 2 <= m ==> ?l. ALL prime l /\ LENGTH l <= m /\ ITLIST (+) l 0 = m`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `m = 2` THENL
   [EXISTS_TAC `[2]` THEN ASM_REWRITE_TAC[ALL; ITLIST; LENGTH; PRIME_2] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `m = 3` THENL
   [EXISTS_TAC `[3]` THEN
    ASM_REWRITE_TAC[ALL; ITLIST; LENGTH; PRIME_CONV `prime 3`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m - 2`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `CONS 2 l` THEN
  ASM_REWRITE_TAC[ALL; ITLIST; LENGTH; PRIME_2] THEN ASM_ARITH_TAC);;

let GOLDBACH_SET_NSUM = prove
 (`!m f. (!i. i IN 1..m ==> f i IN {1} UNION {p + q | prime p /\ prime q})
         ==> ?u l. u <= m /\ LENGTH l <= 2 * m /\ ALL prime l /\
                   nsum(1..m) f = u + ITLIST (+) l 0`,
  INDUCT_TAC THEN GEN_TAC THEN DISCH_TAC THENL
   [MAP_EVERY EXISTS_TAC [`0`; `[]:num list`] THEN
    REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH_EQ; LENGTH; ALL; ITLIST] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `f:num->num`) THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:num` (X_CHOOSE_THEN `l:num list`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC m`) THEN
  REWRITE_TAC[IN_NUMSEG; LE_REFL; ARITH_RULE `1 <= SUC m`] THEN
  REWRITE_TAC[IN_UNION; IN_SING; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC m`] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
   (X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC))) THENL
   [MAP_EVERY EXISTS_TAC [`u + 1`; `l:num list`] THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    MAP_EVERY EXISTS_TAC [`u:num`; `CONS (p:num) (CONS q l)`] THEN
    ASM_REWRITE_TAC[ALL; LENGTH; ITLIST] THEN ASM_ARITH_TAC]);;

let GOLDBACH_SHNIRELMAN = prove
 (`?C. !n. 2 <= n
           ==> ?l. ALL prime l /\ LENGTH l <= C /\ ITLIST (+) l 0 = n`,
  X_CHOOSE_TAC `k:num` (MATCH_MP SCHNIRELMANN_DIRECT GOLDBACH_SET_DENSITY) THEN
  EXISTS_TAC `3 * k + 2` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `f:num->num`
    STRIP_ASSUME_TAC) o SPEC `n - 2`) THEN
  MP_TAC(SPECL [`m:num`; `f:num->num`] GOLDBACH_SET_NSUM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:num` (X_CHOOSE_THEN `l:num list`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPEC `u + 2` SUM_OF_TWOS_AND_THREES) THEN
  REWRITE_TAC[ARITH_RULE `2 <= u + 2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `APPEND (l2:num list) l` THEN
  ASM_REWRITE_TAC[ALL_APPEND; LENGTH_APPEND; ITLIST_APPEND] THEN
  ONCE_REWRITE_TAC[ITLIST_ADD_ACC] THEN ASM_ARITH_TAC);;
