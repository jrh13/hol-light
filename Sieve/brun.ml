(* ========================================================================= *)
(* Prime pairs by Selberg's sieve; Brun's theorem.                           *)
(*                                                                           *)
(* For even N >= 2 and M >= 2 (with V(N) = prod_{p | N} (1 - 1/p)):          *)
(*                                                                           *)
(*   GOLDBACH_SELBERG: #{p <= N | p, N - p prime} <= 448 N / (V(N) log N)^2  *)
(*   TWIN_SELBERG:     #{p <= M | p, p + N prime} <= 448 M / (V(N) log M)^2  *)
(*                                                                           *)
(* from SIEVE_TWO_RESIDUES with f(n) = n(N - n) resp. n(n + N) and level     *)
(* z = M^(1/8); in particular there are at most 1792 M / (log M)^2 twin      *)
(* primes up to M, and BRUN: the sum of 1/p over the primes p with p + 2     *)
(* prime converges (by dyadic blocks).                                       *)
(* ========================================================================= *)

needs "Sieve/pairs_sieve.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The two residue classes of n(N - n) and n(n + N).                         *)
(* ------------------------------------------------------------------------- *)

let GOLDBACH_RESIDUES = prove
 (`!N p n. prime p /\ ~(p divides N) /\ n IN 1..N
           ==> (p divides n * (N - n) <=> n MOD p = 0 \/ n MOD p = N MOD p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  ASM_SIMP_TAC[DIVIDES_MOD] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[GSYM DIVIDES_MOD; GSYM CONG; CONG_SUB_CASES; CONG_0]);;

let GOLDBACH_RESIDUE_CLASS = prove
 (`!N p. prime p /\ ~(p divides N) ==> ~(N MOD p = 0) /\ N MOD p < p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  ASM_SIMP_TAC[DIVISION; GSYM DIVIDES_MOD]);;

let TWIN_RESIDUES = prove
 (`!N p n. prime p /\ ~(p divides N)
           ==> (p divides n * (n + N) <=>
                n MOD p = 0 \/ n MOD p = p - N MOD p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  ASM_SIMP_TAC[DIVIDES_MOD] THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  SUBGOAL_THEN `n MOD p < p /\ N MOD p < p /\ ~(N MOD p = 0)` MP_TAC THENL
   [ASM_SIMP_TAC[DIVISION; GSYM DIVIDES_MOD]; ALL_TAC] THEN
  SPEC_TAC(`n MOD p`,`r:num`) THEN SPEC_TAC(`N MOD p`,`s:num`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[MOD_ADD_CASES] THEN
  ASM_ARITH_TAC);;

let TWIN_RESIDUE_CLASS = prove
 (`!N p. prime p /\ ~(p divides N)
         ==> ~(p - N MOD p = 0) /\ p - N MOD p < p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `~(N MOD p = 0)` MP_TAC THENL
   [ASM_SIMP_TAC[GSYM DIVIDES_MOD]; ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `p:num`] DIVISION) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The choice z = M^(1/8).                                                   *)
(* ------------------------------------------------------------------------- *)

let SELBERG_EXPONENT_CHOICE = prove
 (`!M Q. &2 <= M /\ &0 < Q /\ Q <= &1
         ==> &4 * M / (Q * (log M / &8)) pow 2 + exp(log M / &8) pow 6 +
             &2 * exp(log M / &8)
             <= &448 * M / (log M pow 2 * Q pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log M` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `u = log M / &8` THEN
  SUBGOAL_THEN `log M = &8 * u /\ &0 < u` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `M = exp(&8 * u)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&2 <= M ==> &0 < M`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `u pow 2 <= exp(&2 * u)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_N] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `u:real` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp u pow 6 = exp(&6 * u)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N]; ALL_TAC] THEN
  SUBGOAL_THEN `exp(&2 * u) * exp(&6 * u) = exp(&8 * u)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(&2 * u) * exp u <= exp(&8 * u)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `A = (u:real) pow 2 * Q pow 2` THEN
  SUBGOAL_THEN `&0 < A /\ A <= exp(&2 * u)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(u:real) pow 2 * &1` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[REAL_MUL_RID]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((Q:real) * u) pow 2 = A /\ (&8 * u) pow 2 * Q pow 2 = &64 * A`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `exp(&6 * u) <= exp(&8 * u) / A /\
                exp u <= exp(&8 * u) / A`
  MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `exp(&6 * u) * exp(&2 * u)`;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `exp u * exp(&2 * u)`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
       GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
       ASM_REWRITE_TAC[REAL_LE_REFL]]);
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC);;

let CARD_PRIMES_LT_LE = prove
 (`!z. &1 <= z ==> &(CARD {p | prime p /\ &p < z}) <= z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {b | 1 <= b /\ &b < z})` THEN
  ASM_SIMP_TAC[CARD_NUM_RANGE_LE; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUM_RANGE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`]);;

(* ------------------------------------------------------------------------- *)
(* Upper bounds for Goldbach representations and prime pairs.                *)
(* ------------------------------------------------------------------------- *)

let GOLDBACH_SELBERG = prove
 (`!N. EVEN N /\ 2 <= N
       ==> &(CARD {p | prime p /\ p <= N /\ prime(N - p)}) <=
           &448 * &N /
           (log(&N) pow 2 *
            product {p | prime p /\ p divides N} (\p. &1 - inv(&p)) pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `z = exp(log(&N) / &8)` THEN
  SUBGOAL_THEN `&0 < log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < z /\ log z = log(&N) / &8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[LOG_EXP] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`\n:num. n * (N - n)`; `\p. N MOD p`; `N:num`; `N:num`;
                `z:real`]
               SIEVE_TWO_RESIDUES) THEN
  ASM_SIMP_TAC[GOLDBACH_RESIDUES; GOLDBACH_RESIDUE_CLASS;
               ARITH_RULE `2 <= N ==> ~(N = 0)`] THEN
  ABBREV_TAC `Q = product {p | prime p /\ p divides N} (\p. &1 - inv(&p))` THEN
  ABBREV_TAC `S = {n | n IN 1..N /\
                       !p. prime p /\ &p < z /\ ~(p divides N)
                           ==> ~(p divides n * (N - n))}` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < Q /\ Q <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LT;
      MATCH_MP_TAC PRODUCT_LE_1] THEN
    ASM_SIMP_TAC[FINITE_PRIME_DIVISORS; IN_ELIM_THM;
                 ARITH_RULE `2 <= N ==> ~(N = 0)`] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    (SUBGOAL_THEN `&0 < inv(&p) /\ inv(&p) < &1` MP_TAC THENL
      [SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
        [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_MESON_TAC[PRIME_GE_2];
         DISCH_TAC] THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
         MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC];
       REAL_ARITH_TAC]);
    ALL_TAC] THEN
  MP_TAC(SPECL [`&N`; `Q:real`] SELBERG_EXPONENT_CHOICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!x s a b z c:real. x <= s + &2 * z /\ s <= a + b
                       ==> a + b + &2 * z <= c ==> x <= c`) THEN
  EXISTS_TAC `&(CARD(S:num->bool))` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE(S:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG]; ALL_TAC] THEN
  MP_TAC(SPEC `z:real` CARD_PRIMES_LT_LE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(S UNION {p | prime p /\ &p < z} UNION
                     IMAGE (\q. N - q) {p | prime p /\ &p < z}))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; FINITE_PRIMES_LT] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `&p < z` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `&(N - p) < z` THENL
     [DISJ2_TAC THEN EXISTS_TAC `N - p:num` THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      DISJ1_TAC THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
        ALL_TAC] THEN
      X_GEN_TAC `q:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[PRIME_DIVPROD_EQ; DIVIDES_PRIME_PRIME] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(S:num->bool)) + &(CARD {p | prime p /\ &p < z}) +
              &(CARD(IMAGE (\q. N - q) {p | prime p /\ &p < z}))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(S:num->bool) +
                CARD({p | prime p /\ &p < z} UNION
                     IMAGE (\q. N - q) {p | prime p /\ &p < z})` THEN
    ASM_SIMP_TAC[CARD_UNION_LE; FINITE_UNION; FINITE_IMAGE;
                 FINITE_PRIMES_LT; LE_ADD_LCANCEL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b c z:real. b <= z /\ c <= b ==> a + b + c <= a + &2 * z`) THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LE; CARD_IMAGE_LE; FINITE_PRIMES_LT]);;

let TWIN_SELBERG = prove
 (`!N M. EVEN N /\ ~(N = 0) /\ 2 <= M
         ==> &(CARD {p | prime p /\ p <= M /\ prime(p + N)}) <=
             &448 * &M /
             (log(&M) pow 2 *
              product {p | prime p /\ p divides N} (\p. &1 - inv(&p)) pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `z = exp(log(&M) / &8)` THEN
  SUBGOAL_THEN `&0 < log(&M)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < z /\ log z = log(&M) / &8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[LOG_EXP] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`\n:num. n * (n + N)`; `\p. p - N MOD p`; `N:num`; `M:num`;
                `z:real`]
               SIEVE_TWO_RESIDUES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[TWIN_RESIDUES; TWIN_RESIDUE_CLASS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Q = product {p | prime p /\ p divides N} (\p. &1 - inv(&p))` THEN
  ABBREV_TAC `S = {n | n IN 1..M /\
                       !p. prime p /\ &p < z /\ ~(p divides N)
                           ==> ~(p divides n * (n + N))}` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < Q /\ Q <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LT;
      MATCH_MP_TAC PRODUCT_LE_1] THEN
    ASM_SIMP_TAC[FINITE_PRIME_DIVISORS; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    (SUBGOAL_THEN `&0 < inv(&p) /\ inv(&p) < &1` MP_TAC THENL
      [SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
        [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_MESON_TAC[PRIME_GE_2];
         DISCH_TAC] THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
         MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC];
       REAL_ARITH_TAC]);
    ALL_TAC] THEN
  MP_TAC(SPECL [`&M`; `Q:real`] SELBERG_EXPONENT_CHOICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!x s a b z c:real. x <= s + &2 * z /\ s <= a + b
                       ==> a + b + &2 * z <= c ==> x <= c`) THEN
  EXISTS_TAC `&(CARD(S:num->bool))` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE(S:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG]; ALL_TAC] THEN
  MP_TAC(SPEC `z:real` CARD_PRIMES_LT_LE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(S UNION {p | prime p /\ &p < z}))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC[FINITE_UNION; FINITE_PRIMES_LT] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `&p < z` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
      ALL_TAC] THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[PRIME_DIVPROD_EQ; DIVIDES_PRIME_PRIME] THEN
    SUBGOAL_THEN `q < p:num` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
      UNDISCH_TAC `&q < z` THEN UNDISCH_TAC `~(&p < z)` THEN REAL_ARITH_TAC;
      ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(S:num->bool)) + &(CARD {p | prime p /\ &p < z})` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    ASM_SIMP_TAC[CARD_UNION_LE; FINITE_PRIMES_LT];
    UNDISCH_TAC `&(CARD {p | prime p /\ &p < z}) <= z` THEN
    UNDISCH_TAC `&1 < z` THEN
    SPEC_TAC(`CARD {p | prime p /\ &p < z}`,`k:num`) THEN
    SPEC_TAC(`CARD(S:num->bool)`,`m:num`) THEN REAL_ARITH_TAC]);;

let TWIN_PRIMES_COUNT = prove
 (`!M. 2 <= M
       ==> &(CARD {p | prime p /\ p <= M /\ prime(p + 2)}) <=
           &1792 * &M / log(&M) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2`; `M:num`] TWIN_SELBERG) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  SUBGOAL_THEN `{p | prime p /\ p divides 2} = {2}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
    MESON_TAC[DIVIDES_PRIME_PRIME; PRIME_2];
    ALL_TAC] THEN
  REWRITE_TAC[PRODUCT_SING] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH `!x y z:real. y = z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[real_div; REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Brun's theorem.                                                           *)
(* ------------------------------------------------------------------------- *)

let REAL_SUMMABLE_POS_BOUNDED = prove
 (`!f:num->real s B.
        (!n. n IN s ==> &0 <= f n) /\ (!n. sum (s INTER (0..n)) f <= B)
        ==> real_summable s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_summable; real_sums] THEN
  MATCH_MP_TAC(ISPEC `\n. sum (s INTER (0..n)) (f:num->real)`
    CONVERGENT_REAL_BOUNDED_MONOTONE) THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
    EXISTS_TAC `B:real` THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= B ==> abs x <= B`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_SIMP_TAC[IN_INTER];
    DISJ1_TAC THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    SIMP_TAC[FINITE_INTER; FINITE_NUMSEG; IN_DIFF; IN_INTER] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_NUMSEG] THEN
    MESON_TAC[ARITH_RULE `x <= n ==> x <= SUC n`]]);;

let FINITE_RESTRICT_LE = prove
 (`!t M. FINITE {p:num | p IN t /\ p <= M}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `0..M` THEN REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM;
                                     IN_NUMSEG; LE_0] THEN
  MESON_TAC[]);;

let DYADIC_STEP_ARITH = prove
 (`!a b C X k L.
        &0 <= C /\ &0 < X /\ &1 <= k /\ &1 / &2 <= L /\ &0 <= a /\ a <= b /\
        b <= C * (&2 * X) / (k * L) pow 2
        ==> a * inv X <= &8 * C * inv(k pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= inv X /\ &0 < k /\ &0 < L` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(C * (&2 * X) / (k * L) pow 2) * inv X` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(C * (&2 * X) / (k * L) pow 2) * inv X =
                (&2 * C * inv(L pow 2)) * inv(k pow 2)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < X`; `&0 < k`; `&0 < L`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_LT_IMP_LE;
           ASSUME `&0 < k`] THEN
  SUBGOAL_THEN `inv(L pow 2) <= &4` MP_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `&4 = inv(inv(&4))`] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &2) * (&1 / &2)` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `C * inv(L pow 2) <= C * &4` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let DYADIC_RECIP_SUM = prove
 (`!t C. &0 <= C /\ (!p. p IN t ==> 2 <= p) /\
         (!M. 2 <= M
              ==> &(CARD {p | p IN t /\ p <= M}) <= C * &M / log(&M) pow 2)
         ==> !K. sum {p | p IN t /\ p <= 2 EXP K} (\p. inv(&p)) <=
                 &8 * C * sum(1..K) (\n. inv(&n pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[EXP; SUM_CLAUSES_NUMSEG; ARITH; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x <= &0`) THEN
    MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[ARITH_RULE `~(2 <= p /\ p <= 1)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{p | p IN t /\ p <= 2 EXP SUC K} =
    {p | p IN t /\ p <= 2 EXP K} UNION
    {p | p IN t /\ 2 EXP K < p /\ p <= 2 EXP SUC K}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; EXP] THEN
    X_GEN_TAC `p:num` THEN ASM_CASES_TAC `(p:num) IN t` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FINITE_RESTRICT_LE];
      CONJ_TAC THENL [ALL_TAC; ARITH_TAC]] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p | p IN t /\ p <= 2 EXP SUC K}` THEN
    REWRITE_TAC[FINITE_RESTRICT_LE; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC K`] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `X = &(2 EXP K)` THEN
  SUBGOAL_THEN `&0 < X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[REAL_OF_NUM_LT; EXP_LT_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {p | p IN t /\ 2 EXP K < p /\ p <= 2 EXP SUC K}) *
              inv X` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_BOUND THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{p | p IN t /\ p <= 2 EXP SUC K}` THEN
      REWRITE_TAC[FINITE_RESTRICT_LE; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "X" THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `2 EXP SUC K` (ASSUME
   `!M. 2 <= M
        ==> &(CARD {p | p IN t /\ p <= M}) <= C * &M / log(&M) pow 2`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EXP] THEN MP_TAC(SPECL [`K:num`; `2`] EXP_LT_0) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(2 EXP SUC K) = &2 * X /\
                log(&(2 EXP SUC K)) = &(SUC K) * log(&2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "X" THEN REWRITE_TAC[GSYM REAL_OF_NUM_POW; real_pow];
      REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN MATCH_MP_TAC LOG_POW THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(CARD {p | p IN t /\ 2 EXP K < p /\ p <= 2 EXP SUC K}) <=
    &(CARD {p | p IN t /\ p <= 2 EXP SUC K})`
  MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_RESTRICT_LE; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC DYADIC_STEP_ARITH THEN
  EXISTS_TAC `&(CARD {p | p IN t /\ p <= 2 EXP SUC K})` THEN
  EXISTS_TAC `log(&2)` THEN
  ASM_REWRITE_TAC[REAL_POS; LOG_2_BOUNDS; REAL_OF_NUM_LE] THEN ARITH_TAC);;

let BRUN = prove
 (`real_summable {p | prime p /\ prime(p + 2)} (\p. inv(&p))`,
  MATCH_MP_TAC REAL_SUMMABLE_POS_BOUNDED THEN
  EXISTS_TAC `&8 * &1792 * &2` THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_LE_INV_EQ; REAL_POS] THEN
  X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`{p | prime p /\ prime(p + 2)}`; `&1792`]
                DYADIC_RECIP_SUM) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
     [MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    SUBGOAL_THEN `!M. {p | prime p /\ prime (p + 2) /\ p <= M} =
                      {p | prime p /\ p <= M /\ prime(p + 2)}`
     (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[TWIN_PRIMES_COUNT];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= b /\ c <= &2 ==> b <= &8 * &1792 * c ==> a <= &8 * &1792 * &2`) THEN
  REWRITE_TAC[SUM_INV_SQUARE_LE_2] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..2 EXP n` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
    MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_NUMSEG] THEN
    MP_TAC(SPEC `n:num` LT_POW2_REFL) THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;
