(* ========================================================================= *)
(* The Titchmarsh divisor problem (Titchmarsh 1930 under GRH; Linnik 1961    *)
(* unconditionally; via Bombieri-Vinogradov, the route taken here, by        *)
(* Rodriquez 1965 and Halberstam 1967):                                      *)
(*   sum_{p <= x} tau(p - 1) / x ---> zeta(2) zeta(3) / zeta(6)              *)
(* (TITCHMARSH_DIVISOR; real form TITCHMARSH_DIVISOR_LIMIT with              *)
(* K = lim prod_{p <= n} (1 + 1/(p(p-1)))).                                  *)
(*                                                                           *)
(* Method.                                                                   *)
(* * Hyperbola: for 1 <= m <= y^2 the divisors d, m/d pair off, so           *)
(*     tau(m) = 2 #{d | m : d <= y} - #{d | m : d <= y, m <= d y}            *)
(*   (HYPERBOLA_TAU).  With y = sqrt x and m = p - 1, swapping the sums      *)
(*   gives 2 sum_{d <= sqrt x} pi(x;d,1) minus a pair term                   *)
(*   (TITCHMARSH_SPLIT_EXACT, TITCHMARSH_SPLIT).                             *)
(* * For d <= sqrt x / log^B x Bombieri-Vinogradov replaces pi(x;d,1) by     *)
(*   pi(x)/phi(d) (TITCHMARSH_BV).  Brun-Titchmarsh bounds the rest of       *)
(*   the range by 6 x / (phi(d) log x) (TITCHMARSH_BT).  The pair term is    *)
(*   at most sqrt x for each small d.                                        *)
(* * sum_{d <= y} 1/phi(d) ~ K log y (SUM_INV_PHI_ASYMPTOTIC) from           *)
(*     d/phi(d) = sum_{t SUBSET {p | d}} prod_{p IN t} 1/(p - 1),            *)
(*   that is sum_{d <= n} 1/phi(d) =                                         *)
(*     sum_{t SUBSET {p <= n}} prod_{p IN t} 1/(p(p-1)) H(n DIV prod t)      *)
(*   with H the harmonic sum (PHI_RECIP_SUM_EXPAND).  Upper and lower        *)
(*   bounds are both of the form K log n (SUM_INV_PHI_UPPER,                 *)
(*   SUM_INV_PHI_LOWER).                                                     *)
(* * The prime number theorem then gives TITCHMARSH_DIVISOR_LIMIT            *)
(*   (TITCHMARSH_ERROR collects the error terms).                            *)
(* * K = zeta(2) zeta(3) / zeta(6) (TITCHMARSH_CONSTANT) from EULER_PRODUCT  *)
(*   (100/pnt.ml) and 1 + 1/(p(p-1)) = (1 - p^-6) / ((1 - p^-2)(1 - p^-3)).  *)
(* ========================================================================= *)

needs "Sieve/sw.ml";;
needs "Sieve/bv.ml";;
needs "Sieve/brun_titchmarsh.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The constant: Euler product for zeta(2) zeta(3) / zeta(6).                *)
(* ------------------------------------------------------------------------- *)

let TITCHMARSH_EULER_FACTOR = prove
 (`!p. 2 <= p
       ==> Cx(&1 + inv(&p * (&p - &1))) =
           inv(Cx(&1) - inv(Cx(&p) cpow Cx(&2))) *
           inv(Cx(&1) - inv(Cx(&p) cpow Cx(&3))) /
           inv(Cx(&1) - inv(Cx(&p) cpow Cx(&6)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CPOW_N; CX_INJ; REAL_OF_NUM_EQ] THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= p ==> ~(p = 0)`] THEN
  REWRITE_TAC[GSYM CX_POW; GSYM CX_INV; GSYM CX_SUB; GSYM CX_MUL;
              GSYM CX_DIV; CX_INJ] THEN
  SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SPEC_TAC(`&p:real`,`q:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < q - &1 /\ &0 < q pow 2 - &1 /\ &0 < q pow 3 - &1 /\
                &0 < q pow 6 - &1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&1 < x ==> &0 < x - &1`) THEN
    TRY(MATCH_MP_TAC REAL_POW_LT_1 THEN REWRITE_TAC[ARITH_EQ]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let TITCHMARSH_CONSTANT = prove
 (`?K. Cx K = zeta(Cx(&2)) * zeta(Cx(&3)) / zeta(Cx(&6)) /\
       ((\n. product {p | prime p /\ p <= n} (\p. &1 + inv(&p * (&p - &1))))
        ---> K) sequentially`,
  ABBREV_TAC `Z = zeta(Cx(&2)) * zeta(Cx(&3)) / zeta(Cx(&6))` THEN
  SUBGOAL_THEN
   `((\n. Cx(product {p | prime p /\ p <= n}
                     (\p. &1 + inv(&p * (&p - &1))))) --> Z) sequentially`
  ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN SIMP_TAC[CX_PRODUCT; FINITE_ATMOST] THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC
     `\n. cproduct {p | prime p /\ p <= n}
                   (\p. inv(Cx(&1) - inv(Cx(&p) cpow Cx(&2)))) *
          cproduct {p | prime p /\ p <= n}
                   (\p. inv(Cx(&1) - inv(Cx(&p) cpow Cx(&3)))) /
          cproduct {p | prime p /\ p <= n}
                   (\p. inv(Cx(&1) - inv(Cx(&p) cpow Cx(&6))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
      REWRITE_TAC[complex_div] THEN
      SIMP_TAC[GSYM CPRODUCT_INV; GSYM CPRODUCT_MUL; FINITE_ATMOST] THEN
      MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `p:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[TITCHMARSH_EULER_FACTOR; PRIME_GE_2] THEN
      REWRITE_TAC[complex_div; COMPLEX_MUL_ASSOC];
      ALL_TAC] THEN
    MATCH_MP_TAC LIM_COMPLEX_MUL THEN CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC LIM_COMPLEX_DIV THEN REPEAT CONJ_TAC] THEN
    TRY(MATCH_MP_TAC EULER_PRODUCT) THEN
    TRY(MATCH_MP_TAC ZETA_NONZERO_LEMMA) THEN
    REWRITE_TAC[RE_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `real Z` MP_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IN] (ISPEC `sequentially` LIM_IN_CLOSED_SET))
    THEN EXISTS_TAC
     `\n. Cx(product {p | prime p /\ p <= n}
                     (\p. &1 + inv(&p * (&p - &1))))` THEN
    ASM_REWRITE_TAC[CLOSED_REAL; TRIVIAL_LIMIT_SEQUENTIALLY; REAL_CX;
                    EVENTUALLY_TRUE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL] THEN DISCH_TAC THEN EXISTS_TAC `Re Z` THEN
  ASM_REWRITE_TAC[REALLIM_COMPLEX; o_DEF]);;

let TITCHMARSH_EULER_MONO = prove
 (`!m n. m <= n
         ==> product {p | prime p /\ p <= m} (\p. &1 + inv(&p * (&p - &1))) <=
             product {p | prime p /\ p <= n} (\p. &1 + inv(&p * (&p - &1)))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[PRODUCT_ADD_EXPAND; FINITE_ATMOST] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  SIMP_TAC[FINITE_POWERSET; FINITE_ATMOST] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `t:num->bool` THEN
    DISCH_TAC THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
  STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p | prime p /\ p <= n}` THEN
    ASM_REWRITE_TAC[FINITE_ATMOST];
    ALL_TAC] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN
  REWRITE_TAC[REAL_POS; REAL_SUB_LE; REAL_OF_NUM_LE] THEN
  SUBGOAL_THEN `prime p` MP_TAC THENL
   [ASM SET_TAC[]; MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`]]);;

let TITCHMARSH_EULER_LE = prove
 (`!K n. ((\n. product {p | prime p /\ p <= n}
                       (\p. &1 + inv(&p * (&p - &1)))) ---> K) sequentially
         ==> product {p | prime p /\ p <= n}
                     (\p. &1 + inv(&p * (&p - &1))) <= K`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
  EXISTS_TAC `\n. product {p | prime p /\ p <= n}
                          (\p. &1 + inv(&p * (&p - &1)))` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `n:num` THEN REWRITE_TAC[TITCHMARSH_EULER_MONO]);;

let TITCHMARSH_K_GE_1 = prove
 (`!K. ((\n. product {p | prime p /\ p <= n}
                     (\p. &1 + inv(&p * (&p - &1)))) ---> K) sequentially
       ==> &1 <= K`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP TITCHMARSH_EULER_LE) THEN
  SUBGOAL_THEN `{p | prime p /\ p <= 1} = {}`
   (fun th -> REWRITE_TAC[th; PRODUCT_CLAUSES]) THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  MESON_TAC[PRIME_GE_2; ARITH_RULE `~(2 <= p /\ p <= 1)`]);;

(* ------------------------------------------------------------------------- *)
(* The sum of 1/phi(d): sum_{d <= y} 1/phi(d) ~ K log y.                     *)
(* ------------------------------------------------------------------------- *)

let SUM_RECIP_MULTIPLES = prove
 (`!n k. ~(k = 0)
         ==> sum {d | d IN 1..n /\ k divides d} (\d. inv(&d)) =
             inv(&k) * sum(1..n DIV k) (\j. inv(&j))`,
  SIMP_TAC[SUM_RESTRICT_SET; SUM_MULTIPLES] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_INV_MUL; SUM_LMUL]);;

let PHI_RECIP_PRODUCT = prove
 (`!d. ~(d = 0)
       ==> inv(&(phi d)) =
           inv(&d) * product {p | prime p /\ p divides d}
                             (\p. &1 + inv(&p - &1))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PHI_PRODUCT_PRIMES; REAL_INV_MUL] THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC[GSYM PRODUCT_INV; FINITE_PRIME_DIVISORS] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_LE; PRIME_GE_2]; CONV_TAC REAL_FIELD]);;

let PHI_RECIP_SUM_EXPAND = prove
 (`!n. sum(1..n) (\d. inv(&(phi d))) =
       sum {t | t SUBSET {p | prime p /\ p <= n}}
           (\t. product t (\p. inv(&p * (&p - &1))) *
                sum(1..n DIV nproduct t (\p. p)) (\j. inv(&j)))`,
  GEN_TAC THEN ABBREV_TAC `P = {p | prime p /\ p <= n}` THEN
  SUBGOAL_THEN `FINITE(P:num->bool) /\ (!p. p IN P ==> prime p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN SIMP_TAC[FINITE_ATMOST; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN {t | t SUBSET (P:num->bool)}
        ==> FINITE t /\ (!p. p IN t ==> prime p) /\
            ~(nproduct t (\p. p) = 0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE(t:num->bool) /\ (!p. p IN t ==> prime p)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[NPRODUCT_EQ_0] THEN ASM_MESON_TAC[PRIME_0];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..n) (\d. sum {t | t IN {t | t SUBSET (P:num->bool)} /\
                            nproduct t (\p. p) divides d}
                       (\t. inv(&d) * product t (\p. inv(&p - &1))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    ASM_SIMP_TAC[PHI_RECIP_PRODUCT; ARITH_RULE `1 <= d ==> ~(d = 0)`] THEN
    REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[PRODUCT_ADD_EXPAND; FINITE_PRIME_DIVISORS;
                 ARITH_RULE `1 <= d ==> ~(d = 0)`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `t:num->bool` THEN
    EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN
       `FINITE(t:num->bool) /\ (!p. p IN t ==> prime p /\ p divides d)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{p | prime p /\ p divides d}` THEN
        ASM_SIMP_TAC[FINITE_PRIME_DIVISORS;
                     ARITH_RULE `1 <= d ==> ~(d = 0)`];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "P" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        X_GEN_TAC `p:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPECL [`p:num`; `d:num`] DIVIDES_LE) THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        MP_TAC(SPECL [`t:num->bool`; `d:num`] PRIMES_DIVIDE_IFF_NPRODUCT) THEN
        ASM_SIMP_TAC[]];
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:num->bool` o
        check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`t:num->bool`; `d:num`] PRIMES_DIVIDE_IFF_NPRODUCT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\d:num t:num->bool. nproduct t (\p. p) divides d`;
    `\d:num t:num->bool. inv(&d) * product t (\p. inv(&p - &1))`;
    `1..n`; `{t | t SUBSET (P:num->bool)}`] SUM_SUM_RESTRICT) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; FINITE_POWERSET] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t:num->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:num->bool`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN REWRITE_TAC[SUM_RMUL] THEN
  ASM_SIMP_TAC[SUM_RECIP_MULTIPLES] THEN
  SUBGOAL_THEN
   `product t (\p. inv(&p * (&p - &1))) =
    product t (\p. inv(&p - &1)) * inv(&(nproduct t (\p. p)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT; GSYM PRODUCT_INV;
                 GSYM PRODUCT_MUL] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_MUL_SYM];
    REAL_ARITH_TAC]);;

let TITCHMARSH_G_POS = prove
 (`!t. FINITE t /\ (!p. p IN t ==> prime p)
       ==> &0 <= product t (\p. inv(&p * (&p - &1)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN
  REWRITE_TAC[REAL_POS; REAL_SUB_LE; REAL_OF_NUM_LE] THEN
  ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`]);;

let SUM_INV_PHI_UPPER = prove
 (`!K n. ((\n. product {p | prime p /\ p <= n}
                       (\p. &1 + inv(&p * (&p - &1)))) ---> K) sequentially /\
         1 <= n
         ==> sum(1..n) (\d. inv(&(phi d))) <= K * (&1 + log(&n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PHI_RECIP_SUM_EXPAND] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t | t SUBSET {p | prime p /\ p <= n}}
                  (\t. product t (\p. inv(&p * (&p - &1))) *
                       (&1 + log(&n)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN SIMP_TAC[FINITE_POWERSET; FINITE_ATMOST] THEN
    X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE(t:num->bool) /\ (!p. p IN t ==> prime p)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{p | prime p /\ p <= n}` THEN
      ASM_REWRITE_TAC[FINITE_ATMOST];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[TITCHMARSH_G_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..n) (\j. inv(&j))` THEN
    ASM_SIMP_TAC[HARMONIC_LE_LOG] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_DIFF] THEN
    SIMP_TAC[REAL_LE_INV; REAL_POS] THEN
    MESON_TAC[DIV_LE; LE_TRANS];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_RMUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [SIMP_TAC[GSYM PRODUCT_ADD_EXPAND; FINITE_ATMOST] THEN
    MATCH_MP_TAC TITCHMARSH_EULER_LE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]]);;

let HARMONIC_DIV_LOWER = prove
 (`!n k P0. 1 <= k /\ k <= P0
            ==> log(&n + &1) - log(&P0) <= sum(1..n DIV k) (\j. inv(&j))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `log(&(n DIV k) + &1)` THEN REWRITE_TAC[LOG_LE_HARMONIC] THEN
  SUBGOAL_THEN `&0 < &k /\ &0 < &P0 /\ &0 < &n + &1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM LOG_DIV] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&n + &1) / &k` THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  MP_TAC(SPECL [`n:num`; `k:num`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC);;

let SUM_INV_PHI_LOWER = prove
 (`!K. ((\n. product {p | prime p /\ p <= n}
                     (\p. &1 + inv(&p * (&p - &1)))) ---> K) sequentially
       ==> !e. &0 < e
               ==> ?N. !n. N <= n
                           ==> (K - e) * log(&n + &1) <=
                               sum(1..n) (\d. inv(&(phi d)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:num` (MP_TAC o SPEC `n0:num`)) THEN
  REWRITE_TAC[LE_REFL] THEN
  ABBREV_TAC `P0 = nproduct {p | prime p /\ p <= n0} (\p. p)` THEN
  ABBREV_TAC `E0 = product {p | prime p /\ p <= n0}
                           (\p. &1 + inv(&p * (&p - &1)))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `1 <= P0` ASSUME_TAC THENL
   [EXPAND_TAC "P0" THEN REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    SIMP_TAC[NPRODUCT_EQ_0; FINITE_ATMOST; IN_ELIM_THM] THEN
    MESON_TAC[PRIME_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&P0)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  MP_TAC(SPEC `exp(&2 * K * log(&P0) / e)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  EXISTS_TAC `n0 + P0 + N1:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `E0 * (log(&n + &1) - log(&P0))` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `log(&P0) <= log(&n + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 * K * log(&P0) / e <= log(&n + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `log(exp(&2 * K * log(&P0) / e))` THEN CONJ_TAC THENL
       [REWRITE_TAC[LOG_EXP; REAL_LE_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N1` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `K * log(&P0) <= e / &2 * log(&n + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `e / &2 * (&2 * K * log(&P0) / e)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < e` THEN
        CONV_TAC REAL_FIELD;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= (E0 - (K - e / &2)) * (log(&n + &1) - log(&P0)) /\
      &0 <= e * log(&P0)`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `K * log(&P0) <= e / &2 * log(&n + &1)` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[PHI_RECIP_SUM_EXPAND] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t | t SUBSET {p | prime p /\ p <= n0}}
                  (\t. product t (\p. inv(&p * (&p - &1))) *
                       sum(1..n DIV nproduct t (\p. p)) (\j. inv(&j)))` THEN
  SUBGOAL_THEN
   `!m t. t SUBSET {p | prime p /\ p <= m}
          ==> FINITE t /\ (!p. p IN t ==> prime p)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]]
    THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p | prime p /\ p <= m}` THEN
    ASM_REWRITE_TAC[FINITE_ATMOST];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "E0" THEN SIMP_TAC[PRODUCT_ADD_EXPAND; FINITE_ATMOST] THEN
    REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE THEN
    SIMP_TAC[FINITE_POWERSET; FINITE_ATMOST] THEN
    X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n0:num`; `t:num->bool`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[TITCHMARSH_G_POS] THEN
    MATCH_MP_TAC HARMONIC_DIV_LOWER THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
      ASM_SIMP_TAC[NPRODUCT_EQ_0] THEN ASM_MESON_TAC[PRIME_0];
      EXPAND_TAC "P0" THEN MATCH_MP_TAC NPRODUCT_SUBSET_LE THEN
      ASM_REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
      MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  SIMP_TAC[FINITE_POWERSET; FINITE_ATMOST] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `t:num->bool` THEN
    DISCH_TAC THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `t:num->bool`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[TITCHMARSH_G_POS] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN SIMP_TAC[REAL_LE_INV; REAL_POS]);;

let SUM_INV_PHI_UPPER_REAL = prove
 (`!K y. ((\n. product {p | prime p /\ p <= n}
                       (\p. &1 + inv(&p * (&p - &1)))) ---> K) sequentially /\
         &1 <= y
         ==> sum {d | 1 <= d /\ &d <= y} (\d. inv(&(phi d))) <=
             K * (&1 + log y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `y:real` NUMSEG_REAL_FLOOR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= n:num` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `&0 < &n` MP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * (&1 + log(&n))` THEN
  ASM_SIMP_TAC[SUM_INV_PHI_UPPER] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `K:real` TITCHMARSH_K_GE_1) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> &1 + a <= &1 + b`) THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
  ASM_ARITH_TAC);;

let SUM_INV_PHI_LOWER_REAL = prove
 (`!K. ((\n. product {p | prime p /\ p <= n}
                     (\p. &1 + inv(&p * (&p - &1)))) ---> K) sequentially
       ==> !e. &0 < e
               ==> ?y0. !y. y0 <= y
                            ==> (K - e) * log y <=
                                sum {d | 1 <= d /\ &d <= y}
                                    (\d. inv(&(phi d)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `e:real` o MATCH_MP SUM_INV_PHI_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `&N + &1` THEN X_GEN_TAC `y:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `y:real` NUMSEG_REAL_FLOOR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `N:num <= n` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= log y /\ log y <= log(&n + &1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= K - e` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(K - e) * log(&n + &1)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= --a * b ==> a * b <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN SIMP_TAC[REAL_LE_INV; REAL_POS]]]);;

let SUM_INV_PHI_ASYMPTOTIC = prove
 (`!K Y c.
     ((\n. product {p | prime p /\ p <= n}
                   (\p. &1 + inv(&p * (&p - &1)))) ---> K) sequentially /\
     (!x. 2 <= x ==> &0 < Y x) /\
     ((\x. log(Y x) / log(&x)) ---> c) sequentially /\ &0 < c
     ==> ((\x. sum {d | 1 <= d /\ &d <= Y x} (\d. inv(&(phi d))) / log(&x))
          ---> c * K) sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TITCHMARSH_K_GE_1) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `ee:real` THEN
  DISCH_TAC THEN
  ABBREV_TAC `e1 = min (c / &2) (min (&1 / &2) (ee / (&2 * (K + c + &1))))`
  THEN
  SUBGOAL_THEN `&0 < e1 /\ e1 <= c / &2 /\ e1 <= &1 / &2 /\
                e1 * (K + c + &1) <= ee / &2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * (K + c + &1)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < ee / (&2 * (K + c + &1)) /\
                  ee / (&2 * (K + c + &1)) * (K + c + &1) = ee / &2`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV] THEN
      UNDISCH_TAC `&0 < &2 * (K + c + &1)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    EXPAND_TAC "e1" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `e1:real` o MATCH_MP SUM_INV_PHI_LOWER_REAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `y0:real`) THEN
  UNDISCH_TAC `((\x. log(Y x) / log(&x)) ---> c) sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e1:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  ABBREV_TAC `M = &2 * abs(log(max y0 (&1))) / c + &2 * K / ee + &1` THEN
  MP_TAC(SPEC `exp M` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `N1 + N2 + 2` THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]] THEN DISCH_TAC THEN
  ABBREV_TAC `L = log(&x)` THEN ABBREV_TAC `lY = log(Y(x:num))` THEN
  ABBREV_TAC `S = sum {d | 1 <= d /\ &d <= Y(x:num)} (\d. inv(&(phi d)))`
  THEN
  SUBGOAL_THEN `M <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log(exp M)` THEN CONJ_TAC THENL
     [REWRITE_TAC[LOG_EXP; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N2` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= abs(log(max y0 (&1))) / c /\ &0 <= K / ee`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`M <= L`; `&0 <= abs(log(max y0 (&1))) / c`; `&0 <= K / ee`] THEN
    EXPAND_TAC "M" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c - e1) * L < lY /\ lY < (c + e1) * L` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; GSYM REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `max y0 (&1) <= Y(x:num)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < Y(x:num)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < max y0 (&1)` ASSUME_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM LOG_MONO_LE] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `abs a <= b ==> a <= b`) THEN
    SUBGOAL_THEN `abs(log(max y0 (&1))) <= c / &2 * M` ASSUME_TAC THENL
     [EXPAND_TAC "M" THEN
      SUBGOAL_THEN `c / &2 * (&2 * abs(log(max y0 (&1))) / c) =
                    abs(log(max y0 (&1)))` MP_TAC THENL
       [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= c / &2 * (&2 * K / ee + &1)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `c / &2 * M <= c / &2 * L /\ c / &2 * L <= (c - e1) * L`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K - e1) * lY <= S /\ S <= K * (&1 + lY)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S"; "lY"] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUM_INV_PHI_UPPER_REAL THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `K / L < ee / &2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    SUBGOAL_THEN `K = ee / &2 * (&2 * K / ee)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < ee` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`M <= L`; `&0 <= abs(log(max y0 (&1))) / c`] THEN
    EXPAND_TAC "M" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((K - e1) * lY) / L <= S / L /\ S / L <= (K * (&1 + lY)) / L`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `c - e1 <= lY / L /\ lY / L <= c + e1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(K - e1) * (c - e1) <= (K - e1) * lY / L /\
                K * lY / L <= K * (c + e1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= e1 * c /\ &0 <= e1 * e1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`((K - e1) * lY) / L <= S / L`; `S / L <= (K * (&1 + lY)) / L`;
    `(K - e1) * (c - e1) <= (K - e1) * lY / L`;
    `K * lY / L <= K * (c + e1)`; `K / L < ee / &2`;
    `e1 * (K + c + &1) <= ee / &2`; `&0 <= e1 * c`; `&0 <= e1 * e1`;
    `&0 < e1`] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The hyperbola method for tau(p - 1).                                      *)
(* ------------------------------------------------------------------------- *)

let HYPERBOLA_TAU = prove
 (`!m y. 1 <= m /\ &0 <= y /\ &m <= y * y
         ==> &(tau m) +
             &(CARD {d | d divides m /\ &d <= y /\ &m <= &d * y}) =
             &2 * &(CARD {d | d divides m /\ &d <= y})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `A = {d | d divides m /\ &d <= y}` THEN
  ABBREV_TAC `B = {d | d divides m /\ &m <= &d * y}` THEN
  SUBGOAL_THEN `FINITE(A:num->bool) /\ FINITE(B:num->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{d | d divides m}` THEN
    SIMP_TAC[FINITE_DIVISORS; ASSUME `~(m = 0)`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{d | d divides m /\ &d <= y /\ &m <= &d * y} = A INTER B`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `tau m = CARD(A UNION B:num->bool)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[tau] THEN AP_TERM_TAC THEN
    MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `d:num` THEN
    ASM_CASES_TAC `d divides m` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `&d <= y` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`m:num`; `d:num`] DIVISOR_REFLECT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&(m DIV d) <= y` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `&m <= y * y` THEN REWRITE_TAC[REAL_NOT_LE] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
        [SYM th]) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
        [SYM th]) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(B:num->bool) = CARD(A:num->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
    MAP_EVERY EXISTS_TAC [`\d. m DIV d`; `\d. m DIV d`] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THEN X_GEN_TAC `d:num` THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`m:num`; `d:num`] DIVISOR_REFLECT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(SPECL [`&(m DIV d)`; `y:real`; `&d:real`] REAL_LE_LMUL_EQ) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[REAL_OF_NUM_MUL];
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
        [SYM th]) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_UNION_GEN] THEN
  SUBGOAL_THEN `CARD(A INTER B:num->bool) <= CARD(A:num->bool)` MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[INTER_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
  ARITH_TAC);;

let TITCHMARSH_SWAP = prove
 (`!x y Q. sum {p | prime p /\ p <= x}
               (\p. &(CARD {d | d divides p - 1 /\ &d <= y /\ Q p d})) =
           sum {d | 1 <= d /\ &d <= y}
               (\d. &(CARD {p | prime p /\ p <= x /\ (p == 1) (mod d) /\
                                Q p d}))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\p d. d divides p - 1 /\ (Q:num->num->bool) p d`;
                 `{p | prime p /\ p <= x}`; `{d | 1 <= d /\ &d <= y}`]
         SUM_CARD_SWAP) THEN
  REWRITE_TAC[FINITE_ATMOST; FINITE_NUM_RANGE_LE] THEN
  MATCH_MP_TAC(MESON[]
   `(a:real) = a' /\ (b:real) = b' ==> a = b ==> a' = b'`) THEN
  CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THENL
   [X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `d:num` THEN
    ASM_CASES_TAC `d divides p - 1` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `1 <= d` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ARITH_RULE `1 <= d <=> ~(d = 0)`] THEN DISCH_TAC THEN
    UNDISCH_TAC `d divides p - 1` THEN ASM_REWRITE_TAC[DIVIDES_ZERO] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
    X_GEN_TAC `d:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
      ASM_REWRITE_TAC[CONG_1_DIVIDES_EQ]]]);;

let TITCHMARSH_SPLIT_EXACT = prove
 (`!x. 1 <= x
       ==> sum {p | prime p /\ p <= x} (\p. &(tau(p - 1))) +
           sum {d | 1 <= d /\ &d <= sqrt(&x)}
               (\d. &(CARD {p | prime p /\ p <= x /\ (p == 1) (mod d) /\
                                &(p - 1) <= &d * sqrt(&x)})) =
           &2 * sum {d | 1 <= d /\ &d <= sqrt(&x)}
                    (\d. &(CARD {p | prime p /\ p <= x /\
                                     (p == 1) (mod d)}))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:num`; `sqrt(&x)`; `\p:num d:num. T`] TITCHMARSH_SWAP) THEN
  MP_TAC(ISPECL [`x:num`; `sqrt(&x)`;
                 `\p:num d:num. &(p - 1) <= &d * sqrt(&x)`]
         TITCHMARSH_SWAP) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN SIMP_TAC[GSYM SUM_ADD; FINITE_ATMOST] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC HYPERBOLA_TAU THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    SIMP_TAC[SQRT_POS_LE; REAL_POS];
    REWRITE_TAC[GSYM REAL_POW_2] THEN SIMP_TAC[SQRT_POW_2; REAL_POS] THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]);;

let TITCHMARSH_PAIRS_LE = prove
 (`!x d y. 1 <= d /\ &0 <= y
           ==> &(CARD {p | prime p /\ p <= x /\ (p == 1) (mod d) /\
                           &(p - 1) <= &d * y}) <= y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {e | 1 <= e /\ &e <= y})` THEN
  ASM_SIMP_TAC[CARD_NUM_LE_REAL; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (\e. d * e + 1) {e | 1 <= e /\ &e <= y})` THEN
  SIMP_TAC[CARD_IMAGE_LE; FINITE_NUM_RANGE_LE] THEN
  MATCH_MP_TAC CARD_SUBSET THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUM_RANGE_LE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `p:num` THEN
  STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  UNDISCH_TAC `(p == 1) (mod d)` THEN
  ASM_SIMP_TAC[CONG_1_DIVIDES_EQ; ARITH_RULE `2 <= p ==> ~(p = 0)`] THEN
  REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_TAC `e:num`) THEN
  EXISTS_TAC `e:num` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= e <=> ~(e = 0)`] THEN DISCH_TAC THEN
    UNDISCH_TAC `p - 1 = d * e` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&(p - 1) <= &d * y` THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_LCANCEL_IMP) THEN
  REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC);;

let TITCHMARSH_SPLIT = prove
 (`!x Y1. 1 <= x /\ &0 <= Y1 /\ Y1 <= sqrt(&x)
          ==> abs(sum {p | prime p /\ p <= x} (\p. &(tau(p - 1))) -
                  &2 * sum {d | 1 <= d /\ &d <= Y1}
                           (\d. &(CARD {p | prime p /\ p <= x /\
                                            (p == 1) (mod d)})))
              <= &3 * sum {d | 1 <= d /\ Y1 < &d /\ &d <= sqrt(&x)}
                          (\d. &(CARD {p | prime p /\ p <= x /\
                                           (p == 1) (mod d)})) +
                 Y1 * sqrt(&x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP TITCHMARSH_SPLIT_EXACT) THEN
  ABBREV_TAC `y = sqrt(&x)` THEN
  SUBGOAL_THEN `&0 <= y` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN SIMP_TAC[SQRT_POS_LE; REAL_POS]; ALL_TAC] THEN
  ABBREV_TAC
   `pd = \d. &(CARD {p | prime p /\ p <= x /\ (p == 1) (mod d)})` THEN
  ABBREV_TAC
   `cd = \d. &(CARD {p | prime p /\ p <= x /\ (p == 1) (mod d) /\
                         &(p - 1) <= &d * y})` THEN
  SUBGOAL_THEN
   `{d | 1 <= d /\ &d <= y} =
    {d | 1 <= d /\ &d <= Y1} UNION {d | 1 <= d /\ Y1 < &d /\ &d <= y}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `d:num` THEN
    ASM_CASES_TAC `1 <= d` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {d | 1 <= d /\ Y1 < &d /\ &d <= y}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{d | 1 <= d /\ &d <= y}` THEN
    REWRITE_TAC[FINITE_NUM_RANGE_LE] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT {d | 1 <= d /\ &d <= Y1} {d | 1 <= d /\ Y1 < &d /\ &d <= y}`
  ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY]
    THEN X_GEN_TAC `d:num` THEN
    ASM_CASES_TAC `1 <= d` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_UNION; FINITE_NUM_RANGE_LE] THEN
  SUBGOAL_THEN `!d:num. &0 <= cd d /\ cd d <= pd d /\ &0 <= (pd:num->real) d`
  ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["cd"; "pd"] THEN
    REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_PRIMES_LE_RESTRICT; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum {d | 1 <= d /\ &d <= Y1} (cd:num->real) <= Y1 * y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(CARD {d | 1 <= d /\ &d <= Y1}) * y` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUM_RANGE_LE] THEN
      X_GEN_TAC `d:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      EXPAND_TAC "cd" THEN MATCH_MP_TAC TITCHMARSH_PAIRS_LE THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[CARD_NUM_LE_REAL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sum {d | 1 <= d /\ &d <= Y1} (cd:num->real) /\
    &0 <= sum {d | 1 <= d /\ Y1 < &d /\ &d <= y} cd /\
    sum {d | 1 <= d /\ Y1 < &d /\ &d <= y} cd <=
    sum {d | 1 <= d /\ Y1 < &d /\ &d <= y} pd /\
    &0 <= Y1 * y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[FINITE_NUM_RANGE_LE];
      MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`sum {d | 1 <= d /\ &d <= Y1} (cd:num->real) <= Y1 * y`;
    `&0 <= sum {d | 1 <= d /\ &d <= Y1} (cd:num->real)`;
    `&0 <= sum {d | 1 <= d /\ Y1 < &d /\ &d <= y} (cd:num->real)`;
    `sum {d | 1 <= d /\ Y1 < &d /\ &d <= y} (cd:num->real) <=
     sum {d | 1 <= d /\ Y1 < &d /\ &d <= y} pd`;
    `&0 <= Y1 * y`] THEN
  ABBREV_TAC `D1 = {d | 1 <= d /\ &d <= Y1}` THEN
  ABBREV_TAC `D2 = {d | 1 <= d /\ Y1 < &d /\ &d <= y}` THEN
  ABBREV_TAC `S = sum {p | prime p /\ p <= x} (\p. &(tau(p - 1)))` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bombieri-Vinogradov and Brun-Titchmarsh for the progressions 1 mod d.     *)
(* ------------------------------------------------------------------------- *)

let TITCHMARSH_BV = prove
 (`?B C. 1 <= B /\
         !x. 4 <= x
             ==> abs(sum {d | 1 <= d /\ &d <= sqrt(&x) / log(&x) pow B}
                         (\d. &(CARD {p | prime p /\ p <= x /\
                                          (p == 1) (mod d)}) -
                              &(CARD {p | prime p /\ p <= x}) / &(phi d)))
                 <= C * &x / log(&x) pow 2`,
  MP_TAC(SPEC `2` BOMBIERI_VINOGRADOV) THEN REWRITE_TAC[pi_ap; pi_upto] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:num` (X_CHOOSE_TAC `C:real`)) THEN
  MAP_EVERY EXISTS_TAC [`B + 1`; `C:real`] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `\d:num. 1`]) THEN
  REWRITE_TAC[COPRIME_1] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_ABS o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUM_RANGE_LE] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  REWRITE_TAC[FINITE_NUM_RANGE_LE; REAL_ABS_POS] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&x) / log(&x) pow (B + 1)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 <= log(&x)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_GE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let TITCHMARSH_BT = prove
 (`?x0. !x d. x0 <= x /\ 1 <= d /\ &d <= sqrt(&x)
              ==> &(CARD {p | prime p /\ p <= x /\ (p == 1) (mod d)}) <=
                  &6 * &x / (&(phi d) * log(&x))`,
  MP_TAC(SPEC `&1` BRUN_TITCHMARSH) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real`) THEN
  MP_TAC(SPEC `y pow 2 + &4` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `x0:num`) THEN EXISTS_TAC `x0:num` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `y pow 2 + &4 <= &x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&x0` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&x) /\ sqrt(&x) * sqrt(&x) = &x`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LE; REAL_POS; GSYM REAL_POW_2; SQRT_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `y <= sqrt(&x)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs y` THEN
    REWRITE_TAC[REAL_ABS_LE] THEN REWRITE_TAC[GSYM POW_2_SQRT_ABS] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &d` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `d:num`; `1`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `y <= &0` THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN
      REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= --y * d ==> y * d <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        rand(concl th) = `&x:real`)) THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `&4 <= &x /\ &0 < log(&x)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN
      MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&x) / &2 <= log(&x / &d)` ASSUME_TAC THENL
   [SIMP_TAC[GSYM LOG_SQRT; REAL_ARITH `&4 <= x ==> &0 < x`;
             ASSUME `&4 <= &x`] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= d ==> &0 < d`] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &(phi d)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&6 * &x / (&(phi d) * log(&x)) =
                (&2 + &1) * &x / (&(phi d) * (log(&x) / &2))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&1 <= &(phi d)` THEN UNDISCH_TAC `&0 < log(&x)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The limit.                                                                *)
(* ------------------------------------------------------------------------- *)

let LOG_LOG_OVER_LOG = prove
 (`((\x. log(log(&x)) / log(&x)) ---> &0) sequentially`,
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `exp(&16 / e pow 2 + &1)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN ABBREV_TAC `L = log(&x)` THEN
  SUBGOAL_THEN `&16 / e pow 2 + &1 <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log(exp(&16 / e pow 2 + &1))` THEN CONJ_TAC THENL
     [REWRITE_TAC[LOG_EXP; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &16 / e pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= L` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `s = sqrt L` THEN
  SUBGOAL_THEN `&0 < s /\ s * s = L` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC SQRT_POW_2 THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log L /\ log L <= &2 * s` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`1`; `L:real`] LOG_POW_LE_SQRT) THEN
    ASM_REWRITE_TAC[REAL_POW_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 <= e * s` ASSUME_TAC THENL
   [SUBGOAL_THEN `&4 / e <= s` MP_TAC THENL
     [EXPAND_TAC "s" THEN
      SUBGOAL_THEN `&4 / e = sqrt(&16 / e pow 2)` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN
        SUBGOAL_THEN `&16 / e pow 2 = (&4 / e) pow 2` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        MATCH_MP_TAC POW_2_SQRT THEN MATCH_MP_TAC REAL_LE_DIV THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * s <= (e * s) * s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < L ==> abs L = L`;
               REAL_ARITH `&0 <= x ==> abs x = x`; REAL_LT_LDIV_EQ] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [SYM(check (fun th -> rand(concl th) = `L:real`) th)]) THEN
  ASM_REAL_ARITH_TAC);;

let TITCHMARSH_ERROR = prove
 (`!B C x.
     1 <= B /\ 4 <= x /\
     abs(sum {d | 1 <= d /\ &d <= sqrt(&x) / log(&x) pow B}
             (\d. &(CARD {p | prime p /\ p <= x /\ (p == 1) (mod d)}) -
                  &(CARD {p | prime p /\ p <= x}) / &(phi d)))
     <= C * &x / log(&x) pow 2 /\
     (!d. 1 <= d /\ &d <= sqrt(&x)
          ==> &(CARD {p | prime p /\ p <= x /\ (p == 1) (mod d)}) <=
              &6 * &x / (&(phi d) * log(&x)))
     ==> abs(sum {p | prime p /\ p <= x} (\p. &(tau(p - 1))) / &x -
             &2 * &(CARD {p | prime p /\ p <= x}) *
             sum {d | 1 <= d /\ &d <= sqrt(&x) / log(&x) pow B}
                 (\d. inv(&(phi d))) / &x)
         <= &18 * (sum {d | 1 <= d /\ &d <= sqrt(&x)} (\d. inv(&(phi d))) -
                   sum {d | 1 <= d /\ &d <= sqrt(&x) / log(&x) pow B}
                       (\d. inv(&(phi d)))) / log(&x) +
            (&1 + &2 * abs C) / log(&x)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `L = log(&x)` THEN ABBREV_TAC `sx = sqrt(&x)` THEN
  ABBREV_TAC `Y1 = (sx:real) / L pow B` THEN
  ABBREV_TAC `P = &(CARD {p | prime p /\ p <= x})` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "bv") (LABEL_TAC "bt")))) THEN
  SUBGOAL_THEN `&4 <= &x /\ &1 <= L` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN EXPAND_TAC "L" THEN
    MATCH_MP_TAC LOG_GE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sx /\ sx * sx = &x` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sx" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC SQRT_POW_2 THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `L <= L pow B` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Y1 /\ Y1 <= sx /\ Y1 * sx <= &x / L`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Y1" THEN
    SUBGOAL_THEN `&0 < L pow B` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `sx / L pow B * sx = &x / L pow B` SUBST1_TAC THENL
       [UNDISCH_TAC `sx * sx = &x` THEN UNDISCH_TAC `&0 < L pow B` THEN
        CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:num`; `Y1:real`] TITCHMARSH_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `D2 = {d | 1 <= d /\ Y1 < &d /\ &d <= sx}` THEN
  ABBREV_TAC `D1 = {d | 1 <= d /\ &d <= Y1}` THEN
  SUBGOAL_THEN `FINITE(D1:num->bool) /\ FINITE(D2:num->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D1"; "D2"] THEN
    REWRITE_TAC[FINITE_NUM_RANGE_LE] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{d | 1 <= d /\ &d <= sx}` THEN
    REWRITE_TAC[FINITE_NUM_RANGE_LE] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {d | 1 <= d /\ &d <= sx} (\d. inv(&(phi d))) =
    sum D1 (\d. inv(&(phi d))) + sum D2 (\d. inv(&(phi d)))`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D1"; "D2"] THEN
    SUBGOAL_THEN
     `{d | 1 <= d /\ &d <= sx} =
      {d | 1 <= d /\ &d <= Y1} UNION {d | 1 <= d /\ Y1 < &d /\ &d <= sx}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
      X_GEN_TAC `d:num` THEN
      ASM_CASES_TAC `1 <= d` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_UNION THEN
    REWRITE_TAC[FINITE_NUM_RANGE_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{d | 1 <= d /\ &d <= sx}` THEN
      REWRITE_TAC[FINITE_NUM_RANGE_LE] THEN SET_TAC[];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY]
      THEN X_GEN_TAC `d:num` THEN
      ASM_CASES_TAC `1 <= d` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum D2 (\d. &(CARD {p | prime p /\ p <= x /\ (p == 1) (mod d)})) <=
    &6 * (&x / L) * sum D2 (\d. inv(&(phi d)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `d:num` THEN EXPAND_TAC "D2" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "bt" (MP_TAC o SPEC `d:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> c <= a ==> c <= b`) THEN
    REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(sum D1 (\d. &(CARD {p | prime p /\ p <= x /\ (p == 1) (mod d)})) -
        P * sum D1 (\d. inv(&(phi d)))) <= abs C * (&x / L)`
  ASSUME_TAC THENL
   [REMOVE_THEN "bv" MP_TAC THEN
    ASM_SIMP_TAC[SUM_SUB; GSYM SUM_LMUL] THEN
    REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs C * &x * inv(L pow 2)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE; REAL_POS];
        MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_LE_POW_2]];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_POW_2] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`sum D2 (\d. &(CARD {p | prime p /\ p <= x /\ (p == 1) (mod d)})) <=
     &6 * (&x / L) * sum D2 (\d. inv(&(phi d)))`;
    `abs(sum D1 (\d. &(CARD {p | prime p /\ p <= x /\ (p == 1) (mod d)})) -
         P * sum D1 (\d. inv(&(phi d)))) <= abs C * (&x / L)`;
    `Y1 * sx <= &x / L`] THEN
  ABBREV_TAC `S = sum {p | prime p /\ p <= x} (\p. &(tau(p - 1)))` THEN
  ABBREV_TAC
   `A1 = sum D1 (\d. &(CARD {p | prime p /\ p <= x /\ (p == 1) (mod d)}))`
  THEN
  ABBREV_TAC
   `A2 = sum D2 (\d. &(CARD {p | prime p /\ p <= x /\ (p == 1) (mod d)}))`
  THEN
  ABBREV_TAC `s1 = sum D1 (\d. inv(&(phi d)))` THEN
  ABBREV_TAC `s2 = sum D2 (\d. inv(&(phi d)))` THEN
  ABBREV_TAC `u = &x / L` THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `abs(S - &2 * P * s1) <= (&18 * s2 + &1 + &2 * abs C) * u`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `S / &x - &2 * P * s1 / &x = (S - &2 * P * s1) / &x`
  SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`;
               REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&18 * s2 + &1 + &2 * abs C) * u` THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "u" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let TITCHMARSH_DIVISOR_LIMIT = prove
 (`!K. ((\n. product {p | prime p /\ p <= n}
                     (\p. &1 + inv(&p * (&p - &1)))) ---> K) sequentially
       ==> ((\x. sum {p | prime p /\ p <= x} (\p. &(tau(p - 1))) / &x)
            ---> K) sequentially`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `B:num` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)
    TITCHMARSH_BV THEN
  X_CHOOSE_TAC `x0:num` TITCHMARSH_BT THEN
  SUBGOAL_THEN
   `!x. 2 <= x ==> &0 < log(&x) /\ &0 < sqrt(&x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT; MATCH_MP_TAC SQRT_POS_LT] THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x. sum {d | 1 <= d /\ &d <= sqrt(&x) / log(&x) pow B}
              (\d. inv(&(phi d))) / log(&x)) ---> &1 / &2 * K) sequentially`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_INV_PHI_ASYMPTOTIC THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\x. &1 / &2 - &B * log(log(&x)) / log(&x)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `2` THEN
      X_GEN_TAC `x:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[LOG_DIV; REAL_POW_LT; LOG_POW; LOG_SQRT;
                                  REAL_ARITH `&2 <= x ==> &0 < x`;
                                  REAL_OF_NUM_LE] THEN
      UNDISCH_TAC `&0 < log(&x)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&1 / &2 = &1 / &2 - &B * &0`] THEN
    MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REALLIM_LMUL THEN REWRITE_TAC[GSYM real_div] THEN
    REWRITE_TAC[LOG_LOG_OVER_LOG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x. sum {d | 1 <= d /\ &d <= sqrt(&x)} (\d. inv(&(phi d))) / log(&x))
     ---> &1 / &2 * K) sequentially`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_INV_PHI_ASYMPTOTIC THEN
    ASM_SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\x:num. &1 / &2` THEN REWRITE_TAC[REALLIM_CONST] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `2` THEN
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[LOG_SQRT; REAL_ARITH `&2 <= x ==> &0 < x`;
                 REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `&0 < log(&x)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM THEN
  EXISTS_TAC
   `\x. &2 * (&(CARD {p | prime p /\ p <= x}) / (&x / log(&x)) *
              sum {d | 1 <= d /\ &d <= sqrt(&x) / log(&x) pow B}
                  (\d. inv(&(phi d))) / log(&x))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `K = &2 * (&1 * (&1 / &2 * K))` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_LMUL THEN MATCH_MP_TAC REALLIM_MUL THEN
    ASM_REWRITE_TAC[PNT]] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC
   `\x. &18 * (sum {d | 1 <= d /\ &d <= sqrt(&x)} (\d. inv(&(phi d))) /
               log(&x) -
               sum {d | 1 <= d /\ &d <= sqrt(&x) / log(&x) pow B}
                   (\d. inv(&(phi d))) / log(&x)) +
        (&1 + &2 * abs C) * inv(log(&x))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `&0 = &18 * (&1 / &2 * K - &1 / &2 * K) +
                       (&1 + &2 * abs C) * &0` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC REALLIM_LMUL THEN
    ASM_SIMP_TAC[REALLIM_SUB; REALLIM_1_OVER_LOG]] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `x0 + 4` THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`B:num`; `C:real`; `x:num`] TITCHMARSH_ERROR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a + b = &0 /\ c = d ==> abs a <= c ==> abs b <= d`) THEN
  SUBGOAL_THEN `&0 < &x` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 < log(&x)` THEN
  ABBREV_TAC `S = sum {p | prime p /\ p <= x} (\p. &(tau(p - 1)))` THEN
  ABBREV_TAC `P = &(CARD {p | prime p /\ p <= x})` THEN
  ABBREV_TAC `s1 = sum {d | 1 <= d /\ &d <= sqrt(&x) / log(&x) pow B}
                       (\d. inv(&(phi d)))` THEN
  ABBREV_TAC `sD = sum {d | 1 <= d /\ &d <= sqrt(&x)} (\d. inv(&(phi d)))`
  THEN ABBREV_TAC `L = log(&x)` THEN REPEAT DISCH_TAC THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `&0 < L` THEN UNDISCH_TAC `&0 < &x` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;

let TITCHMARSH_DIVISOR = prove
 (`((\x. Cx(sum {p | prime p /\ p <= x} (\p. &(tau(p - 1))) / &x)) -->
    zeta(Cx(&2)) * zeta(Cx(&3)) / zeta(Cx(&6))) sequentially`,
  X_CHOOSE_THEN `K:real` (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC)
    TITCHMARSH_CONSTANT THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP TITCHMARSH_DIVISOR_LIMIT) THEN
  REWRITE_TAC[REALLIM_COMPLEX; o_DEF]);;
