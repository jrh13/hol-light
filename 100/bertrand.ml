(* ========================================================================= *)
(* Bertrand's postulate (BERTRAND): for every n >= 1 there is a prime p      *)
(* with n < p <= 2 n.                                                        *)
(*                                                                           *)
(* Erdos's proof, with natural numbers only:                                 *)
(* * BINOM_CENTRAL_LOWER: 4^n <= (2 n + 1) binom(2 n,n).                     *)
(* * PRIMORIAL_LE_4_EXP: the product of the primes p <= m is at most 4^m,    *)
(*   by strong induction on m; for m = 2 k + 1 the primes in                 *)
(*   (k + 1, 2 k + 1] divide binom(2 k + 1,k) <= 4^k.                        *)
(* * By Legendre's formula INDEX_FACT_ALT, the index e of a prime p in       *)
(*   binom(2 n,n) has p^e <= 2 n (INDEX_BINOM_CENTRAL_LE), e <= 1 when       *)
(*   2 n < p^2 (INDEX_BINOM_CENTRAL_SQRT) and e = 0 when 3 <= p <= n and     *)
(*   2 n < 3 p (INDEX_BINOM_CENTRAL_ZERO).                                   *)
(* * BINOM_CENTRAL_UPPER: if there is no prime in (n, 2 n] and 2 n < s^2     *)
(*   then binom(2 n,n) <= (2 n)^s prod_{p <= 2 n / 3} p.                     *)
(* * BERTRAND_LARGE (n >= 8192): with s = 2^(t + 1), where                   *)
(*   4^t <= 2 n + 1 < 4^(t + 1), the bounds give n <= 3 (t + 1) (s + 1),     *)
(*   which is false for t >= 7 (BERTRAND_THRESHOLD).                         *)
(* * For n < 8192 one of 2, 3, 5, 7, 13, 23, 43, 83, 163, 317, 631, 1259,    *)
(*   2503, 5003, 9973 will do, each a prime below twice the previous one     *)
(*   (PRIME_TRIAL_DIVISION).                                                 *)
(* ========================================================================= *)

needs "Library/prime.ml";;
needs "Library/binomial.ml";;
needs "Library/products.ml";;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Central binomial coefficients.                                            *)
(* ------------------------------------------------------------------------- *)

let BINOM_CENTRAL_STEP = prove
 (`!n. (n + 1) * binom(2 * n + 2,n + 1) = 2 * (2 * n + 1) * binom(2 * n,n)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `n:num`] BINOM_FACT) THEN
  MP_TAC(SPECL [`n + 1`; `n + 1`] BINOM_FACT) THEN
  REWRITE_TAC[ARITH_RULE `n + n = 2 * n`;
              ARITH_RULE `(n + 1) + n + 1 = 2 * n + 2`] THEN
  REWRITE_TAC[ARITH_RULE `2 * n + 2 = SUC(SUC(2 * n))`;
              ARITH_RULE `n + 1 = SUC n`; FACT] THEN
  MP_TAC(SPEC `n:num` FACT_NZ) THEN
  SPEC_TAC(`FACT n`,`a:num`) THEN SPEC_TAC(`FACT(2 * n)`,`c:num`) THEN
  SPEC_TAC(`binom(2 * n,n)`,`b:num`) THEN
  SPEC_TAC(`binom(SUC(SUC(2 * n)),SUC n)`,`d:num`) THEN
  REWRITE_TAC[ADD1] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[EQ_MULT_LCANCEL]
   `!c x y:num. ~(c = 0) /\ c * x = c * y ==> x = y`) THEN
  EXISTS_TAC `(n + 1) * a * a` THEN
  ASM_REWRITE_TAC[MULT_EQ_0; ADD_EQ_0; ARITH_EQ] THEN
  UNDISCH_TAC `a * a * b = c:num` THEN
  UNDISCH_TAC `((n + 1) * a) * ((n + 1) * a) * d =
               ((2 * n + 1) + 1) * (2 * n + 1) * c` THEN
  CONV_TAC NUM_RING);;

let BINOM_CENTRAL_LOWER = prove
 (`!n. 4 EXP n <= (2 * n + 1) * binom(2 * n,n)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[EXP; MULT_CLAUSES; ADD_CLAUSES; binom; LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[EXP] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC n = 2 * n + 2`; ADD1] THEN
  MATCH_MP_TAC(MESON[LE_MULT_LCANCEL]
   `!c x y:num. ~(c = 0) /\ c * x <= c * y ==> x <= y`) THEN
  EXISTS_TAC `n + 1` THEN REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[ARITH_RULE
   `(n + 1) * ((2 * n + 2) + 1) * b = ((2 * n + 2) + 1) * (n + 1) * b`] THEN
  REWRITE_TAC[BINOM_CENTRAL_STEP] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(n + 1) * 4 * (2 * n + 1) * binom(2 * n,n)` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_LCANCEL];
    REWRITE_TAC[MULT_ASSOC; LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ARITH_TAC]);;

let BINOM_ODD_UPPER = prove
 (`!k. binom(2 * k + 1,k) <= 4 EXP k`,
  GEN_TAC THEN
  MP_TAC(SPECL [`2 * k + 1`; `1`; `1`] BINOMIAL_THEOREM) THEN
  REWRITE_TAC[EXP_ONE; MULT_CLAUSES; ARITH_RULE `1 + 1 = 2`] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  MP_TAC(ISPECL [`{k,k + 1}`; `0..2 * k + 1`; `\i. binom(2 * k + 1,i)`]
    NSUM_SUBSET_SIMPLE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
           NOT_IN_EMPTY; ARITH_RULE `~(k = k + 1)`; ADD_CLAUSES] THEN
  MP_TAC(SPECL [`2 * k + 1`; `k:num`] BINOM_SYM) THEN
  REWRITE_TAC[ARITH_RULE `k <= 2 * k + 1`;
              ARITH_RULE `(2 * k + 1) - k = k + 1`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[EXP_ADD; GSYM EXP_EXP; ARITH] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The product of the primes up to m is at most 4^m.                         *)
(* ------------------------------------------------------------------------- *)

let PRIME_DIVIDES_BINOM_ODD = prove
 (`!k p. prime p /\ k + 2 <= p /\ p <= 2 * k + 1
         ==> p divides binom(2 * k + 1,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k + 1`; `k:num`] BINOM_FACT) THEN
  REWRITE_TAC[ARITH_RULE `(k + 1) + k = 2 * k + 1`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p divides FACT(k + 1) * FACT k * binom(2 * k + 1,k)`
  MP_TAC THENL
   [ASM_SIMP_TAC[DIVIDES_FACT_PRIME]; ALL_TAC] THEN
  ASM_SIMP_TAC[PRIME_DIVPROD_EQ; DIVIDES_FACT_PRIME] THEN
  MATCH_MP_TAC(TAUT `~a /\ ~b ==> a \/ b \/ c ==> c`) THEN ASM_ARITH_TAC);;

let NPRODUCT_PRIMES_DIVIDES = prove
 (`!s x. FINITE s /\ (!p. p IN s ==> prime p /\ p divides x)
         ==> nproduct s (\p. p) divides x`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; DIVIDES_1; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `s:num->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `x:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC DIVIDES_MUL THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC COPRIME_NPRODUCT THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC DISTINCT_PRIME_COPRIME THEN ASM_MESON_TAC[]);;

let FINITE_PRIMES_LE = prove
 (`!m (P:num->bool). FINITE {p | prime p /\ P p /\ p <= m}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{p:num | p <= m}` THEN REWRITE_TAC[FINITE_NUMSEG_LE] THEN
  SET_TAC[]);;

let PRIMORIAL_LE_4_EXP = prove
 (`!m. nproduct {p | prime p /\ p <= m} (\p. p) <= 4 EXP m`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `m <= 2` THENL
   [SUBGOAL_THEN `{p | prime p /\ p <= m} = if m = 2 then {2} else {}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY] THENL
       [EQ_TAC THENL
         [DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP PRIME_GE_2) MP_TAC)
          THEN ARITH_TAC;
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PRIME_2; LE_REFL]];
        STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
        ASM_ARITH_TAC];
      COND_CASES_TAC THEN REWRITE_TAC[NPRODUCT_CLAUSES; NPRODUCT_SING] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ]];
    ALL_TAC] THEN
  DISJ_CASES_TAC(SPEC `m:num` EVEN_OR_ODD) THENL
   [SUBGOAL_THEN `{p | prime p /\ p <= m} = {p | prime p /\ p <= m - 1}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
      ASM_CASES_TAC `p:num = m` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        SUBGOAL_THEN `~prime m` (fun th -> REWRITE_TAC[th]) THEN
        DISCH_THEN(MP_TAC o MATCH_MP PRIME_ODD) THEN
        ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN ASM_ARITH_TAC;
        AP_TERM_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `4 EXP (m - 1)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[LE_EXP] THEN ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o
    REWRITE_RULE[ODD_EXISTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD1]) THEN REWRITE_TAC[ADD1] THEN
  SUBGOAL_THEN
   `{p | prime p /\ p <= 2 * k + 1} =
    {p | prime p /\ p <= k + 1} UNION
    {p | prime p /\ k + 2 <= p /\ p <= 2 * k + 1}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NPRODUCT_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`k + 1`; `\p:num. T`] FINITE_PRIMES_LE) THEN
      REWRITE_TAC[];
      REWRITE_TAC[FINITE_PRIMES_LE];
      MESON_TAC[ARITH_RULE `~(p <= k + 1 /\ k + 2 <= p)`]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `4 EXP (k + 1) * 4 EXP k` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[GSYM EXP_ADD; LE_EXP] THEN ARITH_TAC] THEN
  MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `binom(2 * k + 1,k)` THEN
  REWRITE_TAC[BINOM_ODD_UPPER] THEN
  MP_TAC(ISPECL [`{p | prime p /\ k + 2 <= p /\ p <= 2 * k + 1}`;
                 `binom(2 * k + 1,k)`] NPRODUCT_PRIMES_DIVIDES) THEN
  REWRITE_TAC[FINITE_PRIMES_LE; IN_ELIM_THM] THEN ANTS_TAC THENL
   [MESON_TAC[PRIME_DIVIDES_BINOM_ODD]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  REWRITE_TAC[BINOM_EQ_0] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The index of a prime in binom(2 n,n).                                     *)
(* ------------------------------------------------------------------------- *)

let DIV_DOUBLE_LE = prove
 (`!n q. ~(q = 0) ==> (2 * n) DIV q <= 2 * (n DIV q) + 1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `x <= y + 1 <=> x < y + 2`] THEN
  ASM_SIMP_TAC[RDIV_LT_EQ] THEN
  MP_TAC(SPECL [`n:num`; `q:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let INDEX_BINOM_CENTRAL = prove
 (`!n p. prime p
         ==> index p (FACT n) + index p (FACT n) + index p (binom(2 * n,n)) =
             index p (FACT(2 * n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `n:num`] BINOM_FACT) THEN
  REWRITE_TAC[ARITH_RULE `n + n = 2 * n`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[INDEX_MUL; FACT_NZ; MULT_EQ_0; BINOM_EQ_0;
               ARITH_RULE `~(2 * n < n)`]);;

let INDEX_BINOM_CENTRAL_CARD = prove
 (`!n p. prime p
         ==> index p (binom(2 * n,n)) <=
             CARD {j | 1 <= j /\ p EXP j <= 2 * n}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  SUBGOAL_THEN `!j. ~(p EXP j = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[EXP_EQ_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `p:num`] INDEX_BINOM_CENTRAL) THEN
  ASM_SIMP_TAC[INDEX_FACT_ALT] THEN
  SUBGOAL_THEN
   `nsum {j | 1 <= j /\ p EXP j <= n} (\j. n DIV p EXP j) =
    nsum {j | 1 <= j /\ p EXP j <= 2 * n} (\j. n DIV p EXP j)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
     [ARITH_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[DIV_EQ_0] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE
   `b <= a + a + c ==> a + a + e = b ==> e:num <= c`) THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
   `nsum {j | 1 <= j /\ p EXP j <= 2 * n} (\j. 2 * n DIV p EXP j + 1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_LE THEN ASM_SIMP_TAC[FINITE_EXP_LE; DIV_DOUBLE_LE];
    ASM_SIMP_TAC[NSUM_ADD; NSUM_LMUL; NSUM_CONST; FINITE_EXP_LE] THEN
    ARITH_TAC]);;

let INDEX_BINOM_CENTRAL_LE = prove
 (`!n p. prime p /\ 1 <= n ==> p EXP index p (binom(2 * n,n)) <= 2 * n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  MP_TAC(SPECL [`n:num`; `p:num`] INDEX_BINOM_CENTRAL_CARD) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`index p (binom(2 * n,n))`,`e:num`) THEN GEN_TAC THEN
  ASM_CASES_TAC `e = 0` THENL
   [ASM_REWRITE_TAC[EXP] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[NOT_LE] THEN
  DISCH_TAC THEN MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `CARD(1..e-1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p EXP j < p EXP e` MP_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[LT_EXP] THEN ASM_ARITH_TAC];
    REWRITE_TAC[CARD_NUMSEG_1] THEN ASM_ARITH_TAC]);;

let INDEX_BINOM_CENTRAL_SQRT = prove
 (`!n p. prime p /\ 2 * n < p * p ==> index p (binom(2 * n,n)) <= 1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD {j | 1 <= j /\ p EXP j <= 2 * n}` THEN
  ASM_SIMP_TAC[INDEX_BINOM_CENTRAL_CARD] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {1}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `p EXP j < p EXP 2` MP_TAC THENL
     [REWRITE_TAC[EXP_2] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[LT_EXP] THEN ASM_ARITH_TAC];
    REWRITE_TAC[CARD_SING; LE_REFL]]);;

let PRIMEPOW_INDICES_SING = prove
 (`!p m. 2 <= p /\ p <= m /\ m < p * p
         ==> {j | 1 <= j /\ p EXP j <= m} = {1}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
  X_GEN_TAC `j:num` THEN EQ_TAC THENL
   [STRIP_TAC THEN SUBGOAL_THEN `p EXP j < p EXP 2` MP_TAC THENL
     [REWRITE_TAC[EXP_2] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[LT_EXP] THEN ASM_ARITH_TAC];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[EXP_1; LE_REFL]]);;

let INDEX_BINOM_CENTRAL_ZERO = prove
 (`!n p. prime p /\ 3 <= p /\ p <= n /\ 2 * n < 3 * p
         ==> index p (binom(2 * n,n)) = 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `3 * p <= p * p` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `p:num`] INDEX_BINOM_CENTRAL) THEN
  ASM_SIMP_TAC[INDEX_FACT_ALT] THEN
  MP_TAC(SPECL [`p:num`; `n:num`] PRIMEPOW_INDICES_SING) THEN
  MP_TAC(SPECL [`p:num`; `2 * n`] PRIMEPOW_INDICES_SING) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[NSUM_SING; EXP_1] THEN
  SUBGOAL_THEN `n DIV p = 1 /\ (2 * n) DIV p = 2`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC DIV_UNIQ THENL
     [EXISTS_TAC `n - p:num`; EXISTS_TAC `2 * n - 2 * p`] THEN
    ASM_ARITH_TAC;
    ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Bertrand's postulate.                                                     *)
(* ------------------------------------------------------------------------- *)

let BINOM_CENTRAL_UPPER = prove
 (`!n s. 3 <= n /\ 2 * n < s * s /\ (!p. prime p /\ n < p ==> 2 * n < p)
         ==> binom(2 * n,n) <=
             (2 * n) EXP s *
             nproduct {p | prime p /\ p <= (2 * n) DIV 3} (\p. p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(binom(2 * n,n) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[BINOM_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
   [SYM(MATCH_MP PRIME_FACTORIZATION_ALT th)]) THEN
  ABBREV_TAC `b = binom(2 * n,n)` THEN
  SUBGOAL_THEN `FINITE {p | prime p /\ p <= 2 * n}` ASSUME_TAC THENL
   [MP_TAC(SPECL [`2 * n`; `\p:num. T`] FINITE_PRIMES_LE) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nproduct {p | prime p} (\p. p EXP index p b) =
    nproduct {p | prime p /\ p <= 2 * n} (\p. p EXP index p b)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC NPRODUCT_SUPERSET THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `2 * n < p` ASSUME_TAC THENL
     [ASM_MESON_TAC[NOT_LE]; ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[EXP_EQ_1] THEN DISJ2_TAC THEN
    MP_TAC(SPECL [`n:num`; `p:num`] INDEX_BINOM_CENTRAL_LE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[NOT_LE] THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `p EXP 1` THEN CONJ_TAC THENL
     [REWRITE_TAC[EXP_1] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
   `nproduct {p | prime p /\ p <= 2 * n}
      (\p. (if p * p <= 2 * n then 2 * n else 1) *
           (if 3 * p <= 2 * n then p else 1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NPRODUCT_LE THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    ASM_CASES_TAC `p * p <= 2 * n` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 * n` THEN CONJ_TAC THENL
       [EXPAND_TAC "b" THEN MATCH_MP_TAC INDEX_BINOM_CENTRAL_LE THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        REWRITE_TAC[ARITH_RULE `x <= x * p <=> x * 1 <= x * p`] THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
        COND_CASES_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `index p b <= 1` ASSUME_TAC THENL
       [EXPAND_TAC "b" THEN MATCH_MP_TAC INDEX_BINOM_CENTRAL_SQRT THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM EXP_1] THEN
        REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `index p b = 0` (fun th -> REWRITE_TAC[th; EXP; LE_REFL]) THEN
    EXPAND_TAC "b" THEN MATCH_MP_TAC INDEX_BINOM_CENTRAL_ZERO THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(n < p)` MP_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[NPRODUCT_MUL] THEN MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM NPRODUCT_RESTRICT_SET] THEN
    ASM_SIMP_TAC[NPRODUCT_CONST; FINITE_RESTRICT] THEN
    REWRITE_TAC[LE_EXP] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; DISJ2_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {p:num | p < s}` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[CARD_NUMSEG_LT; LE_REFL]] THEN
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`s:num`; `p:num`; `s:num`; `p:num`] LE_MULT2) THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[GSYM NPRODUCT_RESTRICT_SET] THEN
    MATCH_MP_TAC EQ_IMP_LE THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
    ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let EXP_4_BRACKET = prove
 (`!m. 1 <= m ==> ?t. 4 EXP t <= m /\ m < 4 EXP (t + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?t. m < 4 EXP (t + 1)` MP_TAC THENL
   [EXISTS_TAC `m:num` THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `2 EXP m` THEN REWRITE_TAC[LT_POW2_REFL] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `4 EXP m` THEN CONJ_TAC THENL
     [MATCH_MP_TAC EXP_MONO_LE_IMP THEN ARITH_TAC;
      REWRITE_TAC[LE_EXP] THEN ARITH_TAC];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `t = 0` THENL
   [ASM_REWRITE_TAC[EXP];
    FIRST_X_ASSUM(MP_TAC o SPEC `t - 1`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(t = 0) ==> t - 1 < t /\ t - 1 + 1 = t`] THEN
    REWRITE_TAC[NOT_LT]]);;

let BERTRAND_THRESHOLD = prove
 (`!t. 7 <= t ==> 6 * (t + 1) * (2 EXP (t + 1) + 1) + 1 < 4 EXP t`,
  SUBGOAL_THEN
   `!d. 6 * (d + 8) * (2 EXP (d + 8) + 1) + 1 < 4 EXP (d + 7)`
  MP_TAC THENL
   [INDUCT_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `SUC d + 8 = SUC(d + 8)`;
                ARITH_RULE `SUC d + 7 = SUC(d + 7)`; EXP] THEN
    POP_ASSUM MP_TAC THEN
    SPEC_TAC(`2 EXP (d + 8)`,`a:num`) THEN
    SPEC_TAC(`4 EXP (d + 7)`,`b:num`) THEN ARITH_TAC;
    DISCH_TAC THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t - 7`) THEN
    ASM_SIMP_TAC[ARITH_RULE
     `7 <= t ==> (t - 7) + 8 = t + 1 /\ t - 7 + 7 = t`]]);;

let BERTRAND_LARGE = prove
 (`!n. 8192 <= n ==> ?p. prime p /\ n < p /\ p <= 2 * n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `2 * n + 1` EXP_4_BRACKET) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `7 <= t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `4 EXP (t + 1) <= 4 EXP 7` MP_TAC THENL
     [REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `t:num` BERTRAND_THRESHOLD) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM; NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `s = 2 EXP (t + 1)` THEN
  SUBGOAL_THEN `s * s = 4 EXP (t + 1)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[GSYM MULT_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `s:num`] BINOM_CENTRAL_UPPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[NOT_LE];
    ALL_TAC] THEN
  MP_TAC(SPEC `(2 * n) DIV 3` PRIMORIAL_LE_4_EXP) THEN
  MP_TAC(SPEC `n:num` BINOM_CENTRAL_LOWER) THEN
  SPEC_TAC(`binom(2 * n,n)`,`b:num`) THEN
  SPEC_TAC(`nproduct {p | prime p /\ p <= (2 * n) DIV 3} (\p. p)`,`q:num`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(2 * n) EXP s <= 4 EXP ((t + 1) * s)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXP_EXP] THEN MATCH_MP_TAC EXP_MONO_LE_IMP THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `4 EXP n <= 4 EXP (t + 1) * 4 EXP ((t + 1) * s) * 4 EXP ((2 * n) DIV 3)`
  MP_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `(2 * n + 1) * b` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(2 * n) EXP s * q` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM EXP_ADD; LE_EXP; ARITH_EQ]] THEN
  MP_TAC(SPECL [`2 * n`; `3`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  ASM_ARITH_TAC);;

let PRIME_TRIAL_DIVISION = prove
 (`!p m. 2 <= p /\ p < m * m /\
         (!d. d < m ==> 2 <= d /\ d * d <= p ==> ~(d divides p))
         ==> prime p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[prime] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num` SUBST_ALL_TAC) THEN
  ASM_CASES_TAC `x = 1` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `y = 1` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  SUBGOAL_THEN `~(x = 0) /\ ~(y = 0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DE_MORGAN_THM; GSYM MULT_EQ_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?d. 2 <= d /\ d * d <= x * y /\ d divides x * y`
  STRIP_ASSUME_TAC THENL
   [DISJ_CASES_TAC(SPECL [`x:num`; `y:num`] LE_CASES) THENL
     [EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
      REWRITE_TAC[NUMBER_RULE `x divides x * y`] THEN ASM_ARITH_TAC;
      EXISTS_TAC `y:num` THEN ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN
      REWRITE_TAC[NUMBER_RULE `y divides x * y`] THEN ASM_ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o SPEC `d:num`) THEN ASM_REWRITE_TAC[NOT_LT] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`m:num`; `d:num`; `m:num`; `d:num`] LE_MULT2) THEN
    ASM_ARITH_TAC]);;

let BERTRAND = prove
 (`!n. ~(n = 0) ==> ?p. prime p /\ n < p /\ p <= 2 * n`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `8192 <= n` THEN
  ASM_SIMP_TAC[BERTRAND_LARGE] THEN
  SUBGOAL_THEN
   `?q. q IN {2,3,5,7,13,23,43,83,163,317,631,1259,2503,5003,9973} /\
        n < q /\ q <= 2 * n`
  MP_TAC THENL
   [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
    REPEAT(MATCH_MP_TAC(TAUT `(a ==> b) /\ (~a ==> r) ==> a /\ b \/ r`) THEN
           CONJ_TAC THENL [ASM_ARITH_TAC; DISCH_TAC]) THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `q IN {2,3,5,7,13,23,43,83,163,317,631,1259,2503,5003,9973}` THEN
    SPEC_TAC(`q:num`,`q:num`) THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC PRIME_TRIAL_DIVISION THEN
    EXISTS_TAC `100` THEN CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[DIVIDES_MOD] THEN CONV_TAC NUM_REDUCE_CONV]);;
