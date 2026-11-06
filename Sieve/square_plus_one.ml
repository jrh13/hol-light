(* ========================================================================= *)
(* n^2 + 1 is a product of at most four primes for infinitely many n (the    *)
(* linear sieve with level of distribution M^(1 - e) for the values n^2 + 1, *)
(* n <= M; Richert's weighted sieve gives P3 and Iwaniec's bilinear form of  *)
(* the remainder P2).                                                        *)
(*   SQUARE_PLUS_ONE_P4: INFINITE {n | almost_prime 4 (n EXP 2 + 1)}         *)
(*   SQUARE_PLUS_ONE_P4_COUNT:                                               *)
(*     ?c M0. &0 < c /\                                                      *)
(*            !M. M0 <= M                                                    *)
(*                ==> c * &M / log(&M) <=                                    *)
(*                    &(CARD {n | n IN 1..M /\                               *)
(*                                almost_prime 4 (n EXP 2 + 1)})             *)
(* Method.  The values n^2 + 1 (n <= M, with multiplicity) are sifted by     *)
(* JURKAT_RICHERT with the density g(p) = rho(p)/p, rho(p) the number of     *)
(* roots of x^2 + 1 modulo p (sqp_rho, sqp_g): rho(2) = 1, rho(p) <= 2, and  *)
(* rho(p) = 0 for p == 3 (mod 4) by Fermat's little theorem.  The Chinese    *)
(* remainder theorem (CRT_COUNT) gives |A_d - M g(d)| <= rho(d) <=           *)
(* 4^omega(d) (SQP_SIEVE_COUNT), so the remainder over the d < Y is          *)
(* O(Y log^4 Y) (SUM_FOUR_POW_CARD).  The dimension condition                *)
(* (SQP_G_DIMENSION) comes from Mertens' theorem in the progression 1 mod 4: *)
(* DIRICHLET_STRONG gives sum_{p <= x, p == 1 (4)} log p / p =               *)
(* (1/2) log x + O(1), and partial summation the sum of 1/p                  *)
(* (MERTENS_AP4_VARIATION, MERTENS_AP4_INTERVAL).  With z = M^(9/20) and     *)
(* D = M^(99/100) the sieve parameter is s = 11/5, f(11/5) - 1/10 >= 7/55    *)
(* (SQP_F_LOWER), and the remainder is o(M / log M)                          *)
(* (SQP_REMAINDER_SMALL); so at least c M / log M of the n <= M have no      *)
(* prime factor of n^2 + 1 below z (SQP_SIFTED_LOWER).  As n^2 + 1 < z^5,    *)
(* such n^2 + 1 has at most four prime factors (SQP_LARGE_FACTORS).          *)
(* ========================================================================= *)

needs "Sieve/chen_lower.ml";;
needs "Sieve/brun_titchmarsh.ml";;
needs "100/dirichlet.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The local densities: the roots of x^2 + 1 modulo p.                       *)
(* ------------------------------------------------------------------------- *)

let sqp_rho = new_definition
 `sqp_rho d = CARD {r | r < d /\ d divides r EXP 2 + 1}`;;

let sqp_g = new_definition
 `sqp_g p = &(sqp_rho p) / &p`;;

let FINITE_SQP_ROOTS = prove
 (`!d. FINITE {r | r < d /\ d divides r EXP 2 + 1}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{r:num | r < d}` THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]);;

let SQP_RHO_2 = prove
 (`sqp_rho 2 = 1`,
  REWRITE_TAC[sqp_rho] THEN
  SUBGOAL_THEN `{r | r < 2 /\ 2 divides r EXP 2 + 1} = {1}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN X_GEN_TAC `r:num` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `r = 0 \/ r = 1` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `2 divides r EXP 2 + 1` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[]];
    REWRITE_TAC[CARD_SING]]);;

let SQP_ROOTS_PM_LE = prove
 (`!p r s. prime p /\ s <= r /\ r < p /\ s < p /\
           p divides r EXP 2 + 1 /\ p divides s EXP 2 + 1
           ==> r = s \/ r + s = p`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o
    REWRITE_RULE[LE_EXISTS]) THEN
  SUBGOAL_THEN `p divides k * (s + k + s)` MP_TAC THENL
   [SUBGOAL_THEN `k * (s + k + s) = ((s + k) EXP 2 + 1) - (s EXP 2 + 1)`
    SUBST1_TAC THENL [REWRITE_TAC[EXP_2] THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC DIVIDES_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC;
    DISJ2_TAC THEN
    SUBGOAL_THEN `~(s + k + s = 0:num)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `s = 0 /\ k = 0` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `p divides s EXP 2 + 1` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIVIDES_ONE] THEN
      ASM_MESON_TAC[PRIME_1];
      ALL_TAC] THEN
    UNDISCH_TAC `p divides s + k + s` THEN
    REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_THEN `m:num` ASSUME_TAC) THEN
    SUBGOAL_THEN `m = 1` (fun th -> UNDISCH_TAC `s + k + s = p * m:num` THEN
                                     REWRITE_TAC[th] THEN ARITH_TAC) THEN
    SUBGOAL_THEN `~(m = 0) /\ ~(2 <= m)` MP_TAC THENL
     [CONJ_TAC THEN DISCH_TAC THENL
       [UNDISCH_TAC `s + k + s = p * m:num` THEN ASM_REWRITE_TAC[MULT_CLAUSES];
        SUBGOAL_THEN `p * 2 <= p * m:num` MP_TAC THENL
         [ASM_REWRITE_TAC[LE_MULT_LCANCEL]; ASM_ARITH_TAC]];
      ARITH_TAC]]);;

let SQP_ROOTS_PM = prove
 (`!p r s. prime p /\ r < p /\ s < p /\
           p divides r EXP 2 + 1 /\ p divides s EXP 2 + 1
           ==> r = s \/ r + s = p`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(SPECL [`s:num`; `r:num`] LE_CASES) THENL
   [MATCH_MP_TAC SQP_ROOTS_PM_LE THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`p:num`; `s:num`; `r:num`] SQP_ROOTS_PM_LE) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let SQP_RHO_LE_2 = prove
 (`!p. prime p ==> sqp_rho p <= 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sqp_rho] THEN
  ASM_CASES_TAC `{r | r < p /\ p divides r EXP 2 + 1} = {}` THENL
   [ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {r0, p - r0:num}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; SUBSET; IN_ELIM_THM;
                IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:num`; `r:num`; `r0:num`] SQP_ROOTS_PM) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    REPEAT(COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY]) THEN ARITH_TAC]);;

let SQP_NO_ROOT_3MOD4 = prove
 (`!p r. prime p /\ (p == 3) (mod 4) ==> ~(p divides r EXP 2 + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?k. 4 * k + 3 = p` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `p DIV 4` THEN
    MP_TAC(SPECL [`p:num`; `4`] DIVISION) THEN
    UNDISCH_TAC `(p == 3) (mod 4)` THEN REWRITE_TAC[CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(r,p)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `p divides 1` MP_TAC THENL
     [MATCH_MP_TAC(NUMBER_RULE
       `!p r. p divides r /\ p divides r EXP 2 + 1 ==> p divides 1`) THEN
      EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[DIVIDES_ONE; PRIME_1]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`r:num`; `p:num`] FERMAT_LITTLE) THEN
  ASM_SIMP_TAC[PHI_PRIME] THEN
  SUBGOAL_THEN `p - 1 = 2 * (2 * k + 1) /\ (p - 1) + 1 = p` STRIP_ASSUME_TAC
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[EXP_MULT] THEN
  ABBREV_TAC `B = p - 1` THEN
  SUBGOAL_THEN `(r EXP 2 == B) (mod p) /\ (B EXP 2 == 1) (mod p)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p divides r EXP 2 + 1` THEN UNDISCH_TAC `B + 1 = p` THEN
    REWRITE_TAC[EXP_2] THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `((r EXP 2) EXP (2 * k + 1) == B) (mod p)` MP_TAC THENL
   [MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `B EXP (2 * k + 1)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC CONG_EXP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[EXP_ADD; EXP_MULT; EXP_1] THEN
    SUBGOAL_THEN `((B EXP 2) EXP k == 1 EXP k) (mod p)` MP_TAC THENL
     [MATCH_MP_TAC CONG_EXP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[EXP_ONE] THEN
    SPEC_TAC(`(B EXP 2) EXP k`,`X:num`) THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  SPEC_TAC(`(r EXP 2) EXP (2 * k + 1)`,`Y:num`) THEN GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `p divides 2` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(Y:num == B) (mod p)`; `(Y:num == 1) (mod p)`;
                           `B + 1 = p:num`] THEN
    CONV_TAC NUMBER_RULE;
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC]);;

let SQP_RHO_3MOD4 = prove
 (`!p. prime p /\ (p == 3) (mod 4) ==> sqp_rho p = 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sqp_rho] THEN
  SIMP_TAC[CARD_EQ_0; FINITE_SQP_ROOTS] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[SQP_NO_ROOT_3MOD4]);;

let SQP_G_BOUNDS = prove
 (`!p. prime p ==> &0 <= sqp_g p /\ sqp_g p < &1`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[sqp_g] THEN
  SUBGOAL_THEN `&0 < &p` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_OF_NUM_LT] THEN
  ASM_CASES_TAC `p = 2` THENL
   [ASM_REWRITE_TAC[SQP_RHO_2] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `p:num` SQP_RHO_LE_2) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `p:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(p = 2)` THEN ARITH_TAC);;

let ODD_MOD4 = prove
 (`!n. ODD n ==> (n == 1) (mod 4) \/ (n == 3) (mod 4)`,
  GEN_TAC THEN REWRITE_TAC[ODD_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  DISJ_CASES_TAC(SPEC `m:num` EVEN_OR_ODD) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST1_TAC o
    REWRITE_RULE[EVEN_EXISTS; ODD_EXISTS]) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV THENL
   [DISJ1_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `j:num`;
    DISJ2_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `j:num`] THEN
  ARITH_TAC);;

let SQP_G_UPPER = prove
 (`!p. prime p /\ ~(p = 2)
       ==> sqp_g p <= if (p == 1) (mod 4) then &2 / &p else &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sqp_g] THEN
  SUBGOAL_THEN `&0 < &p` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_POS; REAL_OF_NUM_LE; LE_0] THEN
    ASM_SIMP_TAC[SQP_RHO_LE_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p == 3) (mod 4)` ASSUME_TAC THENL
   [MP_TAC(SPEC `p:num` ODD_MOD4) THEN ANTS_TAC THENL
     [MP_TAC(SPEC `p:num` PRIME_ODD) THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ASM_SIMP_TAC[SQP_RHO_3MOD4] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Mertens' theorem in the progression 1 mod 4.                              *)
(* ------------------------------------------------------------------------- *)

let PHI_4 = prove
 (`phi 4 = 2`,
  MP_TAC(SPECL [`2`; `2`] PHI_PRIMEPOW) THEN REWRITE_TAC[PRIME_2] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MERTENS_AP4_REAL = prove
 (`?B. &0 < B /\
       !x. &1 <= x
           ==> abs(sum {p | prime p /\ &p <= x}
                       (\p. if (p == 1) (mod 4) then log(&p) / &p else &0) -
                   log x / &2) <= B`,
  MP_TAC(SPECL [`4`; `1`] DIRICHLET_STRONG) THEN
  REWRITE_TAC[PHI_4; COPRIME_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  SUBGOAL_THEN `!r. integer r ==> (r <= x <=> r <= &n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_FLOOR]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {p | prime p /\ &p <= x}
        (\p. if (p == 1) (mod 4) then log(&p) / &p else &0) =
    sum {p | p IN 1..n /\ prime p /\ (p == 1) (mod 4)} (\p. log(&p) / &p)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `p:num` THEN
    ASM_SIMP_TAC[INTEGER_CLOSED; REAL_OF_NUM_LE] THEN
    ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `1 <= p` (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(SPEC `p:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  SUBGOAL_THEN `&n <= x /\ x < &n + &1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FLOOR]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &n` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `log(&n) <= log x /\ log x - log(&n) <= &1` MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `log x - log(&n) = log(&1 + (x - &n) / &n)` SUBST1_TAC THENL
     [SUBGOAL_THEN `&1 + (x - &n) / &n = x / &n` SUBST1_TAC THENL
       [UNDISCH_TAC `&1 <= &n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC LOG_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(x - &n) / &n` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= n ==> &0 < n`] THEN
      ASM_REAL_ARITH_TAC];
    ABBREV_TAC
     `S = sum {p | p IN 1..n /\ prime p /\ (p == 1) (mod 4)}
              (\p. log(&p) / &p)` THEN
    REAL_ARITH_TAC]);;

let MERTENS_AP4_VARIATION = prove
 (`?C. &0 < C /\
       !x y. &2 <= x /\ x <= y
             ==> abs((sum {p | prime p /\ &p <= y}
                          (\p. if (p == 1) (mod 4) then inv(&p) else &0) -
                      log(log y) / &2) -
                     (sum {p | prime p /\ &p <= x}
                          (\p. if (p == 1) (mod 4) then inv(&p) else &0) -
                      log(log x) / &2))
                 <= C / log x`,
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC MERTENS_AP4_REAL THEN
  EXISTS_TAC `&2 * B` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n. if prime n then (if (n == 1) (mod 4) then log(&n) / &n else &0)
         else &0`;
    `\t. inv(log t)`; `\t. --(&1 * inv t) / log t pow 2`;
    `\t. inv(&2) * log t`; `\t:real. inv(&2) * inv t`; `&2 * B`;
    `y:real`; `x:real`]
   ABEL_SUMMATION_ASYMPTOTIC) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < t /\ &0 < log t` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MP_TAC(DISCH_ALL(REAL_DIFF_CONV
        `((\t. inv(log t)) has_real_derivative f') (atreal t)`)) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      DISJ2_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_MUL_LID; real_div; REAL_MUL_LNEG; REAL_NEG_LE0] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`\t:real. inv t`; `inv(&2)`; `real_interval[x,y]`]
                    REAL_CONTINUOUS_ON_LMUL) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_INV THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID; IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[SUM_PRIMES_INTERVAL] THEN
      FIRST_X_ASSUM(fun th ->
        MP_TAC(SPEC `x:real` th) THEN MP_TAC(SPEC `t:real` th)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
      ABBREV_TAC `S1 = sum {p | prime p /\ &p <= x}
        (\p. if (p == 1) (mod 4) then log(&p) / &p else &0)` THEN
      ABBREV_TAC `S2 = sum {p | prime p /\ &p <= t}
        (\p. if (p == 1) (mod 4) then log(&p) / &p else &0)` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log x /\ log x <= log y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC LOG_POS_LT; MATCH_MP_TAC LOG_MONO_LE_IMP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {n | x < &n /\ &n <= y}
        (\n. (if prime n
              then (if (n == 1) (mod 4) then log(&n) / &n else &0)
              else &0) * inv(log(&n))) =
    sum {p | prime p /\ &p <= y}
        (\p. if (p == 1) (mod 4) then inv(&p) else &0) -
    sum {p | prime p /\ &p <= x}
        (\p. if (p == 1) (mod 4) then inv(&p) else &0)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_PRIMES_INTERVAL] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    SUBGOAL_THEN `&0 < log(&n)` MP_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN
      FIRST_X_ASSUM(K ALL_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(n = 0)` MP_TAC THENL
     [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[x,y]) (\t. (inv(&2) * inv t) * inv(log t)) =
    log(log y) / &2 - log(log x) / &2`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    MP_TAC(ISPECL [`\t. log(log t) / &2`;
                   `\t. (inv(&2) * inv t) * inv(log t)`;
                   `x:real`; `y:real`]
           REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < t /\ &0 < log t` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MP_TAC(DISCH_ALL(REAL_DIFF_CONV
      `((\t. log(log t) / &2) has_real_derivative f') (atreal t)`)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&2 * B) * (abs(inv(log y)) + abs(inv(log y) - inv(log x))) =
    (&2 * B) / log x`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < inv(log y) /\ inv(log y) <= inv(log x)` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `abs(inv(log y)) = inv(log y) /\
                  abs(inv(log y) - inv(log x)) = inv(log x) - inv(log y)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `S1 = sum {p | prime p /\ &p <= x}
                       (\p. if (p == 1) (mod 4) then inv(&p) else &0)` THEN
  ABBREV_TAC `S2 = sum {p | prime p /\ &p <= y}
                       (\p. if (p == 1) (mod 4) then inv(&p) else &0)` THEN
  REAL_ARITH_TAC);;

let SUM_PRIMES_LE_LT_GEN = prove
 (`!g x. &0 < x /\ (!p. prime p ==> &0 <= g p /\ g p <= inv(&p))
         ==> &0 <= sum {p | prime p /\ &p <= x} g -
                   sum {p | prime p /\ &p < x} g /\
             sum {p | prime p /\ &p <= x} g -
             sum {p | prime p /\ &p < x} g <= inv x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `sum {p | prime p /\ &p <= x} g - sum {p | prime p /\ &p < x} g =
    sum {p | prime p /\ &p = x} g`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a = b + c ==> a - b = c:real`) THEN
    W(MP_TAC o PART_MATCH (rand o rand) SUM_UNION o rand o snd) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[FINITE_PRIMES_LT];
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{p | prime p /\ &p <= x}` THEN
        REWRITE_TAC[FINITE_PRIMES_LE_REAL; SUBSET; IN_ELIM_THM] THEN
        MESON_TAC[REAL_LE_REFL];
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
                    NOT_IN_EMPTY] THEN
        X_GEN_TAC `p:num` THEN REAL_ARITH_TAC];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `?n. prime n /\ &n = x` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `{p | prime p /\ &p = x} = {n}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
      ASM_MESON_TAC[REAL_OF_NUM_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_SING] THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `{p | prime p /\ &p = x} = {}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CLAUSES; REAL_LE_REFL; REAL_LE_INV; REAL_LT_IMP_LE]]);;

let MERTENS_AP4_INTERVAL = prove
 (`?C. &0 < C /\
       !u v. &2 <= u /\ u <= v
             ==> sum {p | prime p /\ u <= &p /\ &p < v}
                     (\p. if (p == 1) (mod 4) then inv(&p) else &0)
                 <= (log(log v) - log(log u)) / &2 + C / log u`,
  X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC MERTENS_AP4_VARIATION THEN
  EXISTS_TAC `C + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_PRIMES_LT_INTERVAL] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real`; `v:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!p. prime p ==> &0 <= (\p. if (p == 1) (mod 4) then inv(&p) else &0) p /\
                    (\p. if (p == 1) (mod 4) then inv(&p) else &0) p
                    <= inv(&p)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_REFL; REAL_LE_INV_EQ; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p. if (p == 1) (mod 4) then inv(&p) else &0`; `u:real`]
                SUM_PRIMES_LE_LT_GEN) THEN
  MP_TAC(ISPECL [`\p. if (p == 1) (mod 4) then inv(&p) else &0`; `v:real`]
                SUM_PRIMES_LE_LT_GEN) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < log u /\ inv u <= inv(log u)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < log u` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC LOG_LT_X THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM(K ALL_TAC) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[real_div] THEN
  ABBREV_TAC `S1 = sum {p | prime p /\ &p <= u}
                       (\p. if (p == 1) (mod 4) then inv(&p) else &0)` THEN
  ABBREV_TAC `S2 = sum {p | prime p /\ &p <= v}
                       (\p. if (p == 1) (mod 4) then inv(&p) else &0)` THEN
  ABBREV_TAC `T1 = sum {p | prime p /\ &p < u}
                       (\p. if (p == 1) (mod 4) then inv(&p) else &0)` THEN
  ABBREV_TAC `T2 = sum {p | prime p /\ &p < v}
                       (\p. if (p == 1) (mod 4) then inv(&p) else &0)` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The dimension condition and the product V(z).                             *)
(* ------------------------------------------------------------------------- *)

let SQP_P_GE_5 = prove
 (`!p. prime p /\ (p == 1) (mod 4) ==> 5 <= p`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(p == 1) (mod 4)` THEN REWRITE_TAC[CONG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MP_TAC(SPECL [`p:num`; `4`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `p DIV 4 = 0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[PRIME_1];
    UNDISCH_TAC `~(p DIV 4 = 0)` THEN ARITH_TAC]);;

let SQP_LOG_FACTOR = prove
 (`!p. prime p
       ==> --log(&1 - sqp_g p) <=
           &2 * (if (p == 1) (mod 4) then inv(&p) else &0) +
           &8 * inv(&p pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= &p` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_SIMP_TAC[PRIME_GE_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(&p pow 2) /\ &0 <= inv(&p)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * (if (p == 1) (mod 4) then inv(&p) else &0)`
  ASSUME_TAC THENL
   [COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `p = 2` THENL
   [UNDISCH_TAC `&0 <= &2 * (if (p == 1) (mod 4) then inv(&p) else &0)` THEN
    ASM_REWRITE_TAC[sqp_g; SQP_RHO_2] THEN
    MP_TAC(SPEC `&1 / &2` LOG_ONE_MINUS_BOUNDS) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `p:num` SQP_G_UPPER) THEN MP_TAC(SPEC `p:num` SQP_G_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `&5 <= &p` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_MESON_TAC[SQP_P_GE_5]; ALL_TAC] THEN
    SUBGOAL_THEN `&2 / &p <= inv(&2)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&5 <= p ==> &0 < p`] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `sqp_g p` LOG_ONE_MINUS_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `sqp_g p pow 2 <= (&2 / &p) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(&2 / &p) pow 2 = &4 * inv(&p pow 2) /\ &2 / &p = &2 * inv(&p)`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [CONJ_TAC THEN UNDISCH_TAC `&5 <= &p` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `sqp_g p = &0` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_RZERO; LOG_1] THEN ASM_REAL_ARITH_TAC]);;

let SQP_G_DIMENSION = prove
 (`?L. &0 <= L /\
       !u v. &2 <= u /\ u <= v
             ==> inv(product (sieve_primes u v) (\p. &1 - sqp_g p)) <=
                 log v / log u * (&1 + L / log u)`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mert"))
    MERTENS_AP4_INTERVAL THEN
  ABBREV_TAC `M = &2 * C + &24` THEN
  EXISTS_TAC `M * exp(M / log(&2))` THEN
  SUBGOAL_THEN `&0 <= M /\ &0 < log(&2)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log u /\ log(&2) <= log u /\ log u < u /\ &0 < log v`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_LT_X THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(sieve_primes u v) /\
                (!p. p IN sieve_primes u v ==> prime p)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[sieve_primes; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p | prime p /\ &p < v}` THEN
      REWRITE_TAC[FINITE_PRIMES_LT] THEN SET_TAC[];
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN sieve_primes u v ==> &0 < &1 - sqp_g p`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(SPEC `p:num` SQP_G_BOUNDS) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(product (sieve_primes u v) (\p. &1 - sqp_g p)) =
                exp(sum (sieve_primes u v) (\p. --log(&1 - sqp_g p)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM PRODUCT_INV; REAL_EXP_SUM] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_EXP_NEG] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXP_LOG THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(log(log v) - log(log u) + M / log u)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (sieve_primes u v)
                  (\p. &2 * (if (p == 1) (mod 4) then inv(&p) else &0) +
                       &8 * inv(&p pow 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[SQP_LOG_FACTOR]; ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_ADD; SUM_LMUL] THEN
    REMOVE_THEN "mert" (MP_TAC o SPECL [`u:real`; `v:real`]) THEN
    MP_TAC(SPECL [`u:real`; `v:real`] SUM_PRIME_SQUARES_TAIL) THEN
    ASM_REWRITE_TAC[sieve_primes] THEN
    SUBGOAL_THEN `&3 / u <= &3 / log u` MP_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `M / log u = &2 * (C / log u) + &8 * (&3 / log u)`
    SUBST1_TAC THENL
     [EXPAND_TAC "M" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `A1 = sum {p | prime p /\ u <= &p /\ &p < v}
                         (\p. if (p == 1) (mod 4) then inv(&p) else &0)` THEN
    ABBREV_TAC `A2 = sum {p | prime p /\ u <= &p /\ &p < v}
                         (\p. inv(&p pow 2))` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_EXP_ADD; REAL_EXP_SUB; EXP_LOG] THEN
  REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M / log u /\ M / log u <= M / log(&2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 + M / log u * exp(M / log u)` THEN
  ASM_SIMP_TAC[REAL_EXP_LE_1_PLUS] THEN
  REWRITE_TAC[REAL_LE_LADD] THEN
  SUBGOAL_THEN `(M * exp(M / log(&2))) / log u = M / log u * exp(M / log(&2))`
  SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_MONO_LE]);;

let SQP_V_POS = prove
 (`!z. &0 < product {p | prime p /\ &p < z} (\p. &1 - sqp_g p)`,
  GEN_TAC THEN MATCH_MP_TAC PRODUCT_POS_LT THEN
  REWRITE_TAC[FINITE_PRIMES_LT; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:num` SQP_G_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let SQP_V_LOWER = prove
 (`?c. &0 < c /\
       !z. &2 <= z
           ==> c / log z <=
               product {p | prime p /\ &p < z} (\p. &1 - sqp_g p)`,
  X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC SQP_G_DIMENSION THEN
  SUBGOAL_THEN `&0 < log(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `log(&2) / (&1 + L / log(&2))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&2`; `z:real`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; SIEVE_PRIMES_2] THEN
  MP_TAC(SPEC `z:real` SQP_V_POS) THEN
  ABBREV_TAC `V = product {p | prime p /\ &p < z} (\p. &1 - sqp_g p)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < log z /\ &0 < &1 + L / log(&2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
                    ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(log z / log(&2) * (&1 + L / log(&2)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MAP_EVERY UNDISCH_TAC [`&0 < log z`; `&0 < log(&2)`;
                           `&0 < &1 + L / log(&2)`] THEN
    CONV_TAC REAL_FIELD;
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_LT_INV]]);;

(* ------------------------------------------------------------------------- *)
(* The remainder: the Chinese remainder theorem.                             *)
(* ------------------------------------------------------------------------- *)

let SQP_DIVIDES_MOD = prove
 (`!p n. p divides n EXP 2 + 1 <=> p divides (n MOD p) EXP 2 + 1`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONG_DIVIDES THEN
  MATCH_MP_TAC CONG_ADD THEN REWRITE_TAC[CONG_REFL] THEN
  MATCH_MP_TAC CONG_EXP THEN ONCE_REWRITE_TAC[CONG_SYM] THEN
  REWRITE_TAC[CONG_MOD]);;

let SQP_SIEVE_COUNT = prove
 (`!M t. FINITE t /\ (!p. p IN t ==> prime p)
         ==> abs(sieve_count (IMAGE (\n. n EXP 2 + 1) (1..M))
                   (\m. &(CARD {n | n IN 1..M /\ n EXP 2 + 1 = m})) t -
                 &M * product t sqp_g) <= &4 pow CARD t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. n EXP 2 + 1`; `1..M`; `t:num->bool`]
                SIEVE_COUNT_IMAGE) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\p r. p divides r EXP 2 + 1`; `t:num->bool`; `M:num`]
                CRT_COUNT) THEN
  ASM_REWRITE_TAC[GSYM SQP_DIVIDES_MOD] THEN
  REWRITE_TAC[GSYM sqp_rho; GSYM sqp_g; ETA_AX] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `product t (\p:num. &2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC SQP_RHO_LE_2 THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[PRODUCT_CONST] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REAL_ARITH_TAC]);;

let SQP_REMAINDER_SUM = prove
 (`?K. &0 < K /\
       !M z Y. &2 <= Y
               ==> sum {t | t SUBSET {p | prime p /\ &p < z} /\
                            &(nproduct t (\p. p)) < Y}
                       (\t. abs(sieve_count (IMAGE (\n. n EXP 2 + 1) (1..M))
                                  (\m. &(CARD {n | n IN 1..M /\
                                                   n EXP 2 + 1 = m})) t -
                                &M * product t sqp_g))
                   <= K * Y * log Y pow 4`,
  X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC SUM_FOUR_POW_CARD THEN
  EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t | t SUBSET {p | prime p /\ &p < z} /\
                       &(nproduct t (\p. p)) < Y} (\t. &4 pow CARD t)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{t:num->bool | t SUBSET {p | prime p /\ &p < z}}` THEN
      SIMP_TAC[FINITE_POWERSET; FINITE_PRIMES_LT] THEN SET_TAC[];
      X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN MATCH_MP_TAC SQP_SIEVE_COUNT THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{p | prime p /\ &p < z}` THEN
        ASM_REWRITE_TAC[FINITE_PRIMES_LT];
        UNDISCH_TAC `(t:num->bool) SUBSET {p | prime p /\ &p < z}` THEN
        SET_TAC[]]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[FINITE_PRIMES_LT] THEN
    SIMP_TAC[IN_ELIM_THM]]);;

(* ------------------------------------------------------------------------- *)
(* The sieve lower bound.                                                    *)
(* ------------------------------------------------------------------------- *)

let SQP_F_LOWER = prove
 (`&7 / &55 <= sieve_f(&11 / &5) - &1 / &10`,
  MP_TAC(SPEC `&11 / &5` SIEVE_LOWER_24_EXPLICIT) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC SIEVE_A_GE_3 THEN
  MP_TAC(SPEC `&1 / &6` LOG_ONE_MINUS_BOUNDS) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `log(&6 / &5) = --log(&5 / &6)` SUBST1_TAC THENL
   [SUBGOAL_THEN `&6 / &5 = inv(&5 / &6)` SUBST1_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    MATCH_MP_TAC LOG_INV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `l = --log(&5 / &6)` THEN
  ABBREV_TAC `A = sieve_A` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&3 * &1 / &6 <= A * l` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let SQP_REMAINDER_SMALL = prove
 (`!K Pw c0 LN R.
        &0 < K /\ &1 <= Pw /\ &0 < c0 /\ &2 <= LN /\ log Pw <= LN /\
        (&16 * &600 pow 6 * &99 * K * Pw) / (&14 * c0) <= LN /\
        R <= K * (exp(&99 / &100 * LN) * Pw) *
             log(exp(&99 / &100 * LN) * Pw) pow 4
        ==> R <= &14 * c0 / &99 * exp LN / LN`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = exp(&99 / &100 * LN)` THEN
  SUBGOAL_THEN `&0 < D /\ &0 < Pw /\ &0 < LN` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(D * Pw) /\ log(D * Pw) <= &2 * LN`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_MUL] THEN EXPAND_TAC "D" THEN REWRITE_TAC[LOG_EXP] THEN
    MP_TAC(SPEC `Pw:real` LOG_POS) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `R <= &16 * K * Pw * LN pow 4 * D` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `K * (D * Pw) * log(D * Pw) pow 4` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `K * (D * Pw) * (&2 * LN) pow 4` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `D * exp(LN / &100) = exp LN` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(LN / &600) pow 6 <= exp(LN / &100)` ASSUME_TAC THENL
   [SUBGOAL_THEN `exp(LN / &100) = exp(LN / &600) pow 6` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN
    MP_TAC(SPEC `LN / &600` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&16 * &600 pow 6 * K * Pw <= &14 * c0 / &99 * LN`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(&16 * &600 pow 6 * &99 * K * Pw) / (&14 * c0) <= LN` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < c ==> &0 < &14 * c`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (LN / &600) pow 6` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `R * (LN / &600) pow 6 <= (&16 * K * Pw * LN pow 4) * exp LN`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&16 * K * Pw * LN pow 4 * D) * (LN / &600) pow 6` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `D * (LN / &600) pow 6 <= exp LN` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `D * exp(LN / &100)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_REWRITE_TAC[REAL_LE_REFL]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &16 * K * Pw * LN pow 4` MP_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `Z = &16 * K * Pw * LN pow 4` THEN
    ABBREV_TAC `Y = (LN / &600) pow 6` THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Z:real) * D * Y` THEN
      CONJ_TAC THENL
     [EXPAND_TAC "Z" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&14 * c0 / &99 * exp LN / LN =
    (&14 * c0 / &99 * LN pow 5 * exp LN / &600 pow 6) / (LN / &600) pow 6`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < LN` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&16 * K * Pw * LN pow 4) * exp LN` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(&16 * &600 pow 6 * K * Pw) * (LN pow 4 * exp LN / &600 pow 6) <=
    (&14 * c0 / &99 * LN) * (LN pow 4 * exp LN / &600 pow 6)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;

let SQP_SIFTED_LOWER = prove
 (`?c M0. &0 < c /\
          !M. M0 <= M
              ==> c * &M / log(&M) <=
                  &(CARD {n | n IN 1..M /\
                              !p. prime p /\ &p < exp(&9 / &20 * log(&M))
                                  ==> ~(p divides n EXP 2 + 1)})`,
  X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC SQP_G_DIMENSION THEN
  MP_TAC(SPECL [`L:real`; `&1 / &10`] JURKAT_RICHERT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `sqp_g`))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SQP_G_BOUNDS]; DISCH_THEN(LABEL_TAC "jr")] THEN
  X_CHOOSE_THEN `c0:real` STRIP_ASSUME_TAC SQP_V_LOWER THEN
  X_CHOOSE_THEN `K:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rem"))
    SQP_REMAINDER_SUM THEN
  ABBREV_TAC `Pw = &(nproduct {p | prime p /\ &p < w} (\p. p))` THEN
  SUBGOAL_THEN `&1 <= Pw` ASSUME_TAC THENL
   [EXPAND_TAC "Pw" THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN REWRITE_TAC[FINITE_PRIMES_LT] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log w /\ &0 <= log Pw` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC LOG_POS_LT; MATCH_MP_TAC LOG_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Kc = (&16 * &600 pow 6 * &99 * K * Pw) / (&14 * c0)` THEN
  SUBGOAL_THEN `&0 <= Kc` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `&20 / &9 * log w + log Pw + Kc + &2` EVENTUALLY_LOG_GE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
  EXISTS_TAC `&14 * c0 / &99` THEN EXISTS_TAC `N0 + 1` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `M:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `M:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&1 <= &M` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(log(&M)) = &M` ASSUME_TAC THENL
   [MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `LN = log(&M)` THEN
  SUBGOAL_THEN `&2 <= LN /\ &20 / &9 * log w <= LN /\ log Pw <= LN /\
                Kc <= LN`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `z = exp(&9 / &20 * LN)` THEN
  ABBREV_TAC `D = exp(&99 / &100 * LN)` THEN
  SUBGOAL_THEN `log z = &9 / &20 * LN /\ log D = &99 / &100 * LN`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["z"; "D"] THEN REWRITE_TAC[LOG_EXP]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real) <= z` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log w)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "z" THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 + &99 / &100 * LN` THEN REWRITE_TAC[REAL_EXP_LE_X] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "jr" (MP_TAC o SPECL
   [`IMAGE (\n. n EXP 2 + 1) (1..M)`;
    `\m. &(CARD {n | n IN 1..M /\ n EXP 2 + 1 = m})`;
    `&M`; `D:real`; `z:real`]) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; REAL_POS] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `log D / log z = &11 / &5` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&2 <= LN` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. n EXP 2 + 1`; `1..M`; `{p | prime p /\ &p < z}`]
                SIFTED_IMAGE) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `R = sum {t | t SUBSET {p | prime p /\ &p < z} /\
                 &(nproduct t (\p. p)) < D * Pw}
            (\t. abs(sieve_count (IMAGE (\n. n EXP 2 + 1) (1..M))
                       (\m. &(CARD {n | n IN 1..M /\ n EXP 2 + 1 = m})) t -
                     &M * product t sqp_g))` THEN
  ABBREV_TAC
   `V = product {p | prime p /\ &p < z} (\p. &1 - sqp_g p)` THEN
  ABBREV_TAC
   `S = &(CARD {n | n IN 1..M /\
                    !p. prime p /\ &p < z ==> ~(p divides n EXP 2 + 1)})` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `R <= &14 * c0 / &99 * &M / LN` ASSUME_TAC THENL
   [SUBGOAL_THEN `&M = exp LN` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SQP_REMAINDER_SMALL THEN
    MAP_EVERY EXISTS_TAC [`K:real`; `Pw:real`] THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "R" THEN USE_THEN "rem" MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `D * &1` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&28 / &99 * c0 * &M / LN <=
                &M * V * (sieve_f(&11 / &5) - &1 / &10)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `c0 / log z <= V` MP_TAC THENL
     [EXPAND_TAC "V" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC SQP_F_LOWER THEN
    ABBREV_TAC `F0 = sieve_f(&11 / &5) - &1 / &10` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&M * c0 / (&9 / &20 * LN) * &7 / &55` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&2 <= LN` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&M * V * (sieve_f(&11 / &5) - &1 / &10) - R <= S` THEN
  UNDISCH_TAC `R <= &14 * c0 / &99 * &M / LN` THEN
  UNDISCH_TAC `&28 / &99 * c0 * &M / LN <=
               &M * V * (sieve_f(&11 / &5) - &1 / &10)` THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* n^2 + 1 is a product of at most four primes infinitely often.             *)
(* ------------------------------------------------------------------------- *)

let SQP_LARGE_FACTORS = prove
 (`!M n. 16 <= M /\ n IN 1..M /\
         (!p. prime p /\ &p < exp(&9 / &20 * log(&M))
              ==> ~(p divides n EXP 2 + 1))
         ==> almost_prime 4 (n EXP 2 + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&16 <= &M` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `exp(log(&M)) = &M` ASSUME_TAC THENL
   [MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= log(&M)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_GE_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `LN = log(&M)` THEN
  ABBREV_TAC `z = exp(&9 / &20 * LN)` THEN
  MATCH_MP_TAC ALMOST_PRIME_LARGE_FACTORS THEN EXISTS_TAC `z:real` THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    REWRITE_TAC[EXP_2; ARITH_RULE `n * n + 1 = 1 <=> n * n = 0`] THEN
    REWRITE_TAC[MULT_EQ_0] THEN ASM_ARITH_TAC;
    EXPAND_TAC "z" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 + &9 / &20 * LN` THEN REWRITE_TAC[REAL_EXP_LE_X] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `z pow 5 = &M pow 2 * exp(LN / &4)` SUBST1_TAC THENL
     [EXPAND_TAC "z" THEN REWRITE_TAC[GSYM REAL_EXP_N] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o
        LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[GSYM REAL_EXP_N; GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&M pow 2 + &1` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
      REWRITE_TAC[REAL_LE_RADD] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPEC `LN / &4` REAL_EXP_LE_X) THEN
    SUBGOAL_THEN `&256 <= &M pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&16 pow 2` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `Q = &M pow 2` THEN ABBREV_TAC `E = exp(LN / &4)` THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `Q * (&1 + &1 / &4) <= Q * E` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN ASM_REWRITE_TAC[]]);;

let SQUARE_PLUS_ONE_P4_COUNT = prove
 (`?c M0. &0 < c /\
          !M. M0 <= M
              ==> c * &M / log(&M) <=
                  &(CARD {n | n IN 1..M /\ almost_prime 4 (n EXP 2 + 1)})`,
  X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `M0:num` STRIP_ASSUME_TAC)
    SQP_SIFTED_LOWER THEN
  EXISTS_TAC `c:real` THEN EXISTS_TAC `M0 + 16` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `M:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `M:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `n:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQP_LARGE_FACTORS THEN EXISTS_TAC `M:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..M` THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN SET_TAC[]]);;

let SQUARE_PLUS_ONE_P4 = prove
 (`INFINITE {n | almost_prime 4 (n EXP 2 + 1)}`,
  X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `M0:num` STRIP_ASSUME_TAC)
    SQUARE_PLUS_ONE_P4_COUNT THEN
  MATCH_MP_TAC COUNT_LOWER_INFINITE THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `M0 + 4`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= log(&x)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_GE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b /\ c <= d ==> b <= c ==> a <= d`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN MESON_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..x` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
    ARITH_TAC]);;
