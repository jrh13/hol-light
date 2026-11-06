(* ========================================================================= *)
(* n^2 + 1 is a product of at most three primes for infinitely many n (a     *)
(* weighted sieve with Kuhn's weights on top of the linear sieve; the sieve  *)
(* alone gives four primes, square_plus_one.ml).                             *)
(*   SQUARE_PLUS_ONE_P3: INFINITE {n | almost_prime 3 (n EXP 2 + 1)}         *)
(*   SQUARE_PLUS_ONE_P3_COUNT:                                               *)
(*     ?c M0. &0 < c /\                                                      *)
(*            !M. M0 <= M                                                    *)
(*                ==> c * &M / log(&M) <=                                    *)
(*                    &(CARD {n | n IN 1..M /\                               *)
(*                                almost_prime 3 (n EXP 2 + 1)})             *)
(* (the prime factors counted with multiplicity).                            *)
(* Method.  Let L = log M, D = M^(99/100), z = D^(1/4), y = M^(17/25)        *)
(* and omega(n) the number of primes q in [z, y) dividing n^2 + 1.  The n    *)
(* with no prime factor of n^2 + 1 below z and omega(n) <= 1 number at       *)
(* least S(A,z) - 1/2 sum_q S(A_q,z) (WEIGHTED_COUNT_LOWER).                 *)
(* JURKAT_RICHERT gives S(A,z) >= M V(z) (f(4) - e) - R and, for the values  *)
(* divisible by q at level D/q (SQP_SIEVE_COUNT_Q),                          *)
(* S(A_q,z) <= M g(q) V(z) (F(s_q) + e) + R_q with F(s_q) = A/s_q.  Partial  *)
(* summation against Mertens mod 4 (SQP_ABEL_RECIP_LOG, SQP_GF_SUM) gives    *)
(* sum_q g(q) F(s_q) <= (A/4) log(204/31) + O(1/L), so the main term is at   *)
(* least (A/4)(log 3 - (1/2) log(204/31)) - O(e) >= 7/100 times M V(z)       *)
(* (SQP3_LOG_CONST).  The remainders are O(D L^5), and the n with            *)
(* q^2 | n^2 + 1 for some q in [z, y) number O(M/z + y)                      *)
(* (SQP_REPEATED_COUNT: two roots mod q^2).  For the other n, n^2 + 1 < y^3  *)
(* has all prime factors >= z and at most one in [z, y), to the first        *)
(* power, hence at most three prime factors (P3_STRUCTURE).                  *)
(* ========================================================================= *)

needs "Sieve/square_plus_one.ml";;
needs "Sieve/chen_weights.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Roots modulo q^2 and the values with a repeated prime factor.             *)
(* ------------------------------------------------------------------------- *)

let SQP_ROOTS_SQ_LE = prove
 (`!q r s. prime q /\ ~(q = 2) /\ s <= r /\ r < q EXP 2 /\
           q EXP 2 divides r EXP 2 + 1 /\ q EXP 2 divides s EXP 2 + 1
           ==> r = s \/ r + s = q EXP 2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o
    REWRITE_RULE[LE_EXISTS]) THEN
  SUBGOAL_THEN `q EXP 2 divides k * (s + k + s)` ASSUME_TAC THENL
   [SUBGOAL_THEN `k * (s + k + s) = ((s + k) EXP 2 + 1) - (s EXP 2 + 1)`
    SUBST1_TAC THENL [REWRITE_TAC[EXP_2] THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC DIVIDES_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `q divides s EXP 2 + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC DIVIDES_TRANS THEN EXISTS_TAC `q EXP 2` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXP_2] THEN
    MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(q divides k) \/ ~(q divides s + k + s)` MP_TAC THENL
   [REWRITE_TAC[GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `q divides 2 * s` MP_TAC THENL
     [SUBGOAL_THEN `2 * s = (s + k + s) - k:num` SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC DIVIDES_SUB THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
      MP_TAC(SPEC `q:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(q = 2)` THEN ARITH_TAC;
      SUBGOAL_THEN `q divides 1` MP_TAC THENL
       [MATCH_MP_TAC(NUMBER_RULE
         `!q s. q divides s /\ q divides s EXP 2 + 1 ==> q divides 1`) THEN
        EXISTS_TAC `s:num` THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[DIVIDES_ONE; PRIME_1]]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ2_TAC THEN
    SUBGOAL_THEN `q EXP 2 divides s + k + s` MP_TAC THENL
     [MATCH_MP_TAC COPRIME_DIVPROD THEN EXISTS_TAC `k:num` THEN
      ASM_REWRITE_TAC[COPRIME_LEXP; ARITH_EQ] THEN
      ASM_SIMP_TAC[PRIME_COPRIME_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(s + k + s = 0:num)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `s = 0 /\ k = 0:num` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `q divides s EXP 2 + 1` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIVIDES_ONE] THEN
      ASM_MESON_TAC[PRIME_1];
      ALL_TAC] THEN
    REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_THEN `m:num` ASSUME_TAC) THEN
    SUBGOAL_THEN `m = 1` (fun th -> UNDISCH_TAC `s + k + s = q EXP 2 * m` THEN
                                     REWRITE_TAC[th] THEN ARITH_TAC) THEN
    SUBGOAL_THEN `~(m = 0) /\ ~(2 <= m)` MP_TAC THENL
     [CONJ_TAC THEN DISCH_TAC THENL
       [UNDISCH_TAC `s + k + s = q EXP 2 * m` THEN
        ASM_REWRITE_TAC[MULT_CLAUSES];
        SUBGOAL_THEN `q EXP 2 * 2 <= q EXP 2 * m` MP_TAC THENL
         [ASM_REWRITE_TAC[LE_MULT_LCANCEL]; ASM_ARITH_TAC]];
      ARITH_TAC];
    DISJ1_TAC THEN
    SUBGOAL_THEN `q EXP 2 divides k` MP_TAC THENL
     [MATCH_MP_TAC COPRIME_DIVPROD THEN EXISTS_TAC `s + k + s:num` THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN
      ASM_REWRITE_TAC[COPRIME_LEXP; ARITH_EQ] THEN
      ASM_SIMP_TAC[PRIME_COPRIME_EQ];
      ALL_TAC] THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC]);;

let SQP_RHO_SQ_LE_2 = prove
 (`!q. prime q /\ ~(q = 2)
       ==> CARD {r | r < q EXP 2 /\ q EXP 2 divides r EXP 2 + 1} <= 2`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `{r | r < q EXP 2 /\ q EXP 2 divides r EXP 2 + 1} = {}` THENL
   [ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {r0, q EXP 2 - r0:num}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; SUBSET; IN_ELIM_THM;
                IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    DISJ_CASES_TAC(SPECL [`r0:num`; `r:num`] LE_CASES) THENL
     [MP_TAC(SPECL [`q:num`; `r:num`; `r0:num`] SQP_ROOTS_SQ_LE);
      MP_TAC(SPECL [`q:num`; `r0:num`; `r:num`] SQP_ROOTS_SQ_LE)] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    REPEAT(COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY]) THEN ARITH_TAC]);;

let SQP_SQ_COUNT = prove
 (`!q M. prime q /\ ~(q = 2)
         ==> &(CARD {n | n IN 1..M /\ q EXP 2 divides n EXP 2 + 1})
             <= &2 * &M / &q pow 2 + &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(q EXP 2 = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[EXP_EQ_0] THEN ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`q EXP 2`; `\r. q EXP 2 divides r EXP 2 + 1`; `M:num`]
                CARD_RESIDUE_SET) THEN
  ASM_REWRITE_TAC[GSYM SQP_DIVIDES_MOD] THEN
  MP_TAC(SPEC `q:num` SQP_RHO_SQ_LE_2) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
  ABBREV_TAC
   `c = &(CARD {r | r < q EXP 2 /\ q EXP 2 divides r EXP 2 + 1})` THEN
  SUBGOAL_THEN `&0 < &q pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &M / &q pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `!N X Y c:real. abs(N - X) <= c /\ X <= Y /\ c <= &2 ==> N <= Y + &2`) THEN
  MAP_EVERY EXISTS_TAC [`&M * c / &q pow 2`; `c:real`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]);;

let SQP_REPEATED_COUNT = prove
 (`!M z y. &3 <= z /\ z <= y
           ==> &(CARD {n | n IN 1..M /\
                           ?q. prime q /\ z <= &q /\ &q < y /\
                               q EXP 2 divides n EXP 2 + 1})
               <= &6 * &M / z + &2 * y + &2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Q = {q | prime q /\ z <= &q /\ &q < y}` THEN
  ABBREV_TAC `S = {n | n IN 1..M /\
                       ?q. prime q /\ z <= &q /\ &q < y /\
                           q EXP 2 divides n EXP 2 + 1}` THEN
  SUBGOAL_THEN `FINITE(Q:num->bool) /\ FINITE(S:num->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Q"; "S"] THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THENL
     [EXISTS_TAC `{p | prime p /\ &p < y}` THEN
      REWRITE_TAC[FINITE_PRIMES_LT] THEN SET_TAC[];
      EXISTS_TAC `1..M` THEN REWRITE_TAC[FINITE_NUMSEG] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q. q IN Q ==> prime q /\ ~(q = 2) /\ z <= &q`
  ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `z <= &q` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Q (\q. &(CARD {n | n IN S /\ q EXP 2 divides n EXP 2 + 1}))`
  THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) SUM_CARD_SWAP o rand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[CARD_EQ_SUM] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `?q. q IN Q /\ q EXP 2 divides n EXP 2 + 1` MP_TAC THENL
     [UNDISCH_TAC `(n:num) IN S` THEN MAP_EVERY EXPAND_TAC ["S"; "Q"] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q0:num` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    ASM_SIMP_TAC[CARD_EQ_0; FINITE_RESTRICT] THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Q (\q. &2 * &M / &q pow 2 + &2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(CARD {n | n IN 1..M /\ q EXP 2 divides n EXP 2 + 1})` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
      CONJ_TAC THENL
       [EXPAND_TAC "S" THEN SET_TAC[];
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..M` THEN
        REWRITE_TAC[FINITE_NUMSEG] THEN SET_TAC[]];
      MATCH_MP_TAC SQP_SQ_COUNT THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_CONST; SUM_LMUL] THEN
  REWRITE_TAC[real_div] THEN
  SUBGOAL_THEN `sum Q (\q. &M * inv(&q pow 2)) <= &M * (&3 / z)` MP_TAC THENL
   [ASM_SIMP_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS] THEN EXPAND_TAC "Q" THEN
    MATCH_MP_TAC SUM_PRIME_SQUARES_TAIL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(CARD(Q:num->bool)) <= y + &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(CARD {p:num | &p < y})` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
      REWRITE_TAC[FINITE_NUM_LT_REAL] THEN EXPAND_TAC "Q" THEN SET_TAC[];
      MATCH_MP_TAC CARD_NUM_LT_REAL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Almost primes and the weighted count.                                     *)
(* ------------------------------------------------------------------------- *)

let ALMOST_PRIME_MONO = prove
 (`!j k n. j <= k /\ almost_prime j n ==> almost_prime k n`,
  REWRITE_TAC[almost_prime] THEN MESON_TAC[LE_TRANS]);;

let ALMOST_PRIME_PRIME_MUL = prove
 (`!k q m. prime q /\ almost_prime k m ==> almost_prime (k + 1) (q * m)`,
  REWRITE_TAC[almost_prime] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `CONS (q:num) l` THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; ALL; LENGTH; ITLIST] THEN ASM_ARITH_TAC);;

let ALMOST_PRIME_PRIME = prove
 (`!k q. prime q /\ 1 <= k ==> almost_prime k q`,
  REWRITE_TAC[almost_prime] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `[q:num]` THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; ALL; LENGTH; ITLIST; MULT_CLAUSES] THEN
  ASM_ARITH_TAC);;

let P3_STRUCTURE = prove
 (`!m z y. ~(m = 0) /\ ~(m = 1) /\ &1 <= z /\ z <= y /\ &m < y pow 3 /\
           (!p. prime p /\ p divides m ==> z <= &p) /\
           CARD {q | prime q /\ z <= &q /\ &q < y /\ q divides m} <= 1 /\
           (!q. prime q /\ z <= &q /\ &q < y ==> ~(q EXP 2 divides m))
           ==> almost_prime 3 m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {q | prime q /\ z <= &q /\ &q < y /\ q divides m}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{d | d divides m}` THEN
    ASM_SIMP_TAC[FINITE_DIVISORS] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{q | prime q /\ z <= &q /\ &q < y /\ q divides m}`
               CARD_LE_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `a:num` MP_TAC) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN DISCH_TAC THEN
  ASM_CASES_TAC `prime a /\ z <= &a /\ &a < y /\ a divides m` THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `a divides m` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `~(a divides k)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a:num` o check (is_forall o concl) o
        check (fun th -> can (find_term ((=) `EXP`)) (concl th))) THEN
      ASM_REWRITE_TAC[EXP_2] THEN MATCH_MP_TAC DIVIDES_MUL_L THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `k = 1` THENL
     [ASM_REWRITE_TAC[MULT_CLAUSES] THEN MATCH_MP_TAC ALMOST_PRIME_PRIME THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `3 = 2 + 1` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ALMOST_PRIME_PRIME_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ALMOST_PRIME_LARGE_FACTORS THEN EXISTS_TAC `y:real` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(a * k = 0)` THEN
      ASM_REWRITE_TAC[MULT_CLAUSES];
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&(a * k)` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC(CONJUNCT2 LE_MULT_NZ) THEN ASM_MESON_TAC[PRIME_IMP_NZ];
      X_GEN_TAC `p:num` THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `p:num = a` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC DIVIDES_LMUL THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC DIVIDES_LMUL THEN ASM_REWRITE_TAC[]];
        ASM_MESON_TAC[]]];
    MATCH_MP_TAC ALMOST_PRIME_MONO THEN EXISTS_TAC `2` THEN
    REWRITE_TAC[ARITH] THEN
    MATCH_MP_TAC ALMOST_PRIME_LARGE_FACTORS THEN EXISTS_TAC `y:real` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `z <= &p` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

let WEIGHTED_COUNT_LOWER = prove
 (`!(R:num->num->bool) S Q.
        FINITE S /\ FINITE Q
        ==> &(CARD S) - inv(&2) * sum Q (\q. &(CARD {n | n IN S /\ R q n}))
            <= &(CARD {n | n IN S /\ CARD {q | q IN Q /\ R q n} <= 1})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n q. (R:num->num->bool) q n`; `S:num->bool`;
                 `Q:num->bool`] SUM_CARD_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  SUBGOAL_THEN
   `&(CARD(S:num->bool)) = sum S (\n:num. &1) /\
    &(CARD {n | n IN S /\ CARD {q | q IN Q /\ R q n} <= 1}) =
    sum S (\n. if CARD {q | q IN Q /\ (R:num->num->bool) q n} <= 1
               then &1 else &0)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_SIMP_TAC[CARD_EQ_SUM; FINITE_RESTRICT] THEN
    REWRITE_TAC[SUM_RESTRICT_SET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_SUB] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 - inv(&2) * x <= &1`) THEN
    REWRITE_TAC[REAL_POS];
    MATCH_MP_TAC(REAL_ARITH `&2 <= x ==> &1 - inv(&2) * x <= &0`) THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]);;

let SQP3_COMBINATORIAL = prove
 (`!M z y.
     &3 <= z /\ z <= y /\ &(M EXP 2 + 1) < y pow 3
     ==> &(CARD {n | n IN 1..M /\
                     !p. prime p /\ &p < z ==> ~(p divides n EXP 2 + 1)}) -
         inv(&2) *
         sum {q | prime q /\ z <= &q /\ &q < y}
             (\q. &(CARD {n | n IN 1..M /\ q divides n EXP 2 + 1 /\
                              !p. prime p /\ &p < z
                                  ==> ~(p divides n EXP 2 + 1)})) -
         (&6 * &M / z + &2 * y + &2)
         <= &(CARD {n | n IN 1..M /\ almost_prime 3 (n EXP 2 + 1)})`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = {n | n IN 1..M /\
                       !p. prime p /\ &p < z
                           ==> ~(p divides n EXP 2 + 1)}` THEN
  ABBREV_TAC `Q = {q | prime q /\ z <= &q /\ &q < y}` THEN
  SUBGOAL_THEN `FINITE(S:num->bool) /\ FINITE(Q:num->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S"; "Q"] THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THENL
     [EXISTS_TAC `1..M` THEN REWRITE_TAC[FINITE_NUMSEG] THEN SET_TAC[];
      EXISTS_TAC `{p | prime p /\ &p < y}` THEN
      REWRITE_TAC[FINITE_PRIMES_LT] THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\q n. q divides n EXP 2 + 1`; `S:num->bool`;
                 `Q:num->bool`] WEIGHTED_COUNT_LOWER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sum Q (\q. &(CARD {n | n IN S /\ q divides n EXP 2 + 1})) =
    sum Q (\q. &(CARD {n | n IN 1..M /\ q divides n EXP 2 + 1 /\
                           !p. prime p /\ &p < z
                               ==> ~(p divides n EXP 2 + 1)}))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    BETA_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b c d e. c <= d + e ==> a - b <= c ==> a - b - e <= d`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `&(CARD {n | n IN 1..M /\ almost_prime 3 (n EXP 2 + 1)}) +
    &(CARD {n | n IN 1..M /\
                ?q. prime q /\ z <= &q /\ &q < y /\
                    q EXP 2 divides n EXP 2 + 1})` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC SQP_REPEATED_COUNT THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD({n | n IN 1..M /\ almost_prime 3 (n EXP 2 + 1)} UNION
                   {n | n IN 1..M /\
                        ?q. prime q /\ z <= &q /\ &q < y /\
                            q EXP 2 divides n EXP 2 + 1})` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CARD_UNION_LE THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..M` THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN SET_TAC[]] THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..M` THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN SET_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `n:num` THEN
  EXPAND_TAC "S" THEN EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `?q. prime q /\ z <= &q /\ &q < y /\
                     q EXP 2 divides n EXP 2 + 1` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3_STRUCTURE THEN
  MAP_EVERY EXISTS_TAC [`z:real`; `y:real`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `n IN 1..M` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    REWRITE_TAC[EXP_2; ARITH_RULE `n * n + 1 = 1 <=> n * n = 0`] THEN
    REWRITE_TAC[MULT_EQ_0] THEN ASM_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&(M EXP 2 + 1)` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE; LE_ADD_RCANCEL] THEN
    MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (is_forall o concl) o
      check (fun th -> can (find_term ((=) `z:real`)) (concl th) &&
                       not (can (find_term ((=) `y:real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `CARD:(num->bool)->num`)) (concl th))) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; CONJ_ASSOC];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Partial summation: the sum of g(q) F(s_q).                                *)
(* ------------------------------------------------------------------------- *)

let SQP_ABEL_RECIP_LOG = prove
 (`?C. &0 < C /\
       !D z y. &2 <= z /\ z <= y /\ y < D
               ==> sum {n | z < &n /\ &n <= y}
                     (\n. (if prime n
                           then (if (n == 1) (mod 4) then inv(&n) else &0)
                           else &0) * inv(log D - log(&n)))
                   <= ((log(log y) - log(log D - log y)) -
                       (log(log z) - log(log D - log z))) / (&2 * log D) +
                      C / (log z * (log D - log y))`,
  X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC MERTENS_AP4_VARIATION THEN
  EXISTS_TAC `&2 * C0` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log z /\ log z <= log y /\ log y < log D`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n. if prime n then (if (n == 1) (mod 4) then inv(&n) else &0)
         else &0`;
    `\t. inv(log D - log t)`;
    `\t. --(&0 - &1 * inv t) / (log D - log t) pow 2`;
    `\t. log(log t) / &2`; `\t. ((&1 * inv t) * inv(log t)) / &2`;
    `C0 / log z`; `y:real`; `z:real`]
   ABEL_SUMMATION_ASYMPTOTIC) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < t /\ log t < log D` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MP_TAC(DISCH_ALL(REAL_DIFF_CONV
        `((\t. inv(log D - log t)) has_real_derivative f') (atreal t)`)) THEN
      ASM_SIMP_TAC[REAL_ARITH `a < b ==> ~(b - a = &0)`];
      DISJ1_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN
      REWRITE_TAC[REAL_ARITH `--(&0 - &1 * x) = x`] THEN
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < t /\ &0 < log t` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MP_TAC(DISCH_ALL(REAL_DIFF_CONV
        `((\t. log(log t) / &2) has_real_derivative f') (atreal t)`)) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      SUBGOAL_THEN `&0 < t /\ &0 < log t` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(DISCH_ALL(REAL_DIFF_CONV
        `((\t. ((&1 * inv t) * inv(log t)) / &2) has_real_derivative f')
         (atreal t)`)) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN MESON_TAC[];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[SUM_PRIMES_INTERVAL] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`z:real`; `t:real`]) THEN
      ASM_REWRITE_TAC[] THEN
      ABBREV_TAC `S1 = sum {p | prime p /\ &p <= z}
                        (\p. if (p == 1) (mod 4) then inv(&p) else &0)` THEN
      ABBREV_TAC `S2 = sum {p | prime p /\ &p <= t}
                        (\p. if (p == 1) (mod 4) then inv(&p) else &0)` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[z,y])
      (\t. ((&1 * inv t) * inv(log t)) / &2 * inv(log D - log t)) =
    ((log(log y) - log(log D - log y)) -
     (log(log z) - log(log D - log z))) / (&2 * log D)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    MP_TAC(ISPECL
     [`\t. (log(log t) - log(log D - log t)) / (&2 * log D)`;
      `\t. ((&1 * inv t) * inv(log t)) / &2 * inv(log D - log t)`;
      `z:real`; `y:real`]
     REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; GSYM REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[GSYM real_div] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < t /\ &0 < log t /\ &0 < log D - log t`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `a < b ==> &0 < b - a`) THEN
        MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MP_TAC(DISCH_ALL(REAL_DIFF_CONV
      `((\t. (log(log t) - log(log D - log t)) / (&2 * log D))
        has_real_derivative f') (atreal t)`)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `~(log D = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < t`; `&0 < log t`; `&0 < log D - log t`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `C0 / log z * (abs(inv(log D - log y)) +
                  abs(inv(log D - log y) - inv(log D - log z))) <=
    (&2 * C0) / (log z * (log D - log y))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(log D - log z) /\
                  inv(log D - log z) <= inv(log D - log y)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `abs(inv(log D - log y)) = inv(log D - log y) /\
      abs(inv(log D - log y) - inv(log D - log z)) =
      inv(log D - log y) - inv(log D - log z)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL] THEN
    SUBGOAL_THEN `&0 <= C0 * inv(log z)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `c = C0 * inv(log z)` THEN
    ABBREV_TAC `a = inv(log D - log y)` THEN
    ABBREV_TAC `b = inv(log D - log z)` THEN DISCH_TAC THEN
    SUBGOAL_THEN `c * (a + a - b) <= c * (&2 * a)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "c" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!s i e b:real. e <= b ==> abs(s - i) <= e ==> s <= i + b`) THEN
  ASM_REWRITE_TAC[]);;

let SUM_PRIMES_HALF_OPEN_LE = prove
 (`!b z y B.
        z <= y /\ &0 <= B /\
        (!q. prime q /\ z <= &q /\ &q <= y ==> &0 <= b q) /\
        (!q. prime q /\ &q = z ==> b q <= B)
        ==> sum {q | prime q /\ z <= &q /\ &q < y} b <=
            sum {n | z < &n /\ &n <= y} (\n. if prime n then b n else &0) +
            B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum {n | z < &n /\ &n <= y} (\n. if prime n then b n else &0) =
    sum {q | prime q /\ z < &q /\ &q <= y} b`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {q | prime q /\ &q = z} /\
                FINITE {q | prime q /\ z < &q /\ &q <= y}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THENL
     [EXISTS_TAC `{p | prime p /\ &p <= z}`;
      EXISTS_TAC `{p | prime p /\ &p <= y}`] THEN
    REWRITE_TAC[FINITE_PRIMES_LE_REAL; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum ({q | prime q /\ &q = z} UNION
                   {q | prime q /\ z < &q /\ &q <= y}) b` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[FINITE_UNION] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `x:num` THEN
      MP_TAC(REAL_ARITH
       `z <= &x /\ &x < y ==> &x = z \/ z < &x /\ &x <= y`) THEN
      MESON_TAC[];
      REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `x:num` THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
                    NOT_IN_EMPTY] THEN X_GEN_TAC `x:num` THEN REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a + b <= b + c <=> a <= c:real`] THEN
  ASM_CASES_TAC `{q | prime q /\ &q = z} = {}` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `q0:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{q | prime q /\ &q = z} = {q0}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
    ASM_MESON_TAC[REAL_OF_NUM_EQ];
    ASM_SIMP_TAC[SUM_SING]]);;

let SQP_GF_SUM = prove
 (`?C. &0 < C /\
       !D z y. &3 <= z /\ z <= y /\ y < D /\
               log z <= log D - log y /\ log D - log z <= &3 * log z
               ==> sum {q | prime q /\ z <= &q /\ &q < y}
                       (\q. sqp_g q * sieve_F((log D - log(&q)) / log z))
                   <= &2 * sieve_A * log z *
                      (((log(log y) - log(log D - log y)) -
                        (log(log z) - log(log D - log z))) / (&2 * log D) +
                       C / (log z * (log D - log y)) +
                       inv z * inv(log D - log z))`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "abel"))
    SQP_ABEL_RECIP_LOG THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log z /\ log z <= log y /\ log y < log D`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC SIEVE_A_GE_3 THEN DISCH_TAC THEN
  ABBREV_TAC `Q = {q | prime q /\ z <= &q /\ &q < y}` THEN
  SUBGOAL_THEN `FINITE(Q:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p | prime p /\ &p < y}` THEN
    REWRITE_TAC[FINITE_PRIMES_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum Q (\q. (&2 * sieve_A * log z) *
               ((if (q == 1) (mod 4) then inv(&q) else &0) *
                inv(log D - log(&q))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `q:num` THEN EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < &q /\ ~(q = 2) /\ log z <= log D - log(&q) /\
                  log D - log(&q) <= &3 * log z /\ log(&q) < log D`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `log z <= log(&q) /\ log(&q) < log y` MP_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC LOG_MONO_LE_IMP; MATCH_MP_TAC LOG_MONO_LT_IMP] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REPEAT STRIP_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      UNDISCH_TAC `z <= &q` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `sieve_F((log D - log(&q)) / log z) =
                  sieve_A * log z * inv(log D - log(&q))`
    SUBST1_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) SIEVE_UPPER_13 o lhand o snd) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN `&0 < log D - log(&q)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&0 < log z` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MP_TAC(SPEC `q:num` SQP_G_UPPER) THEN
      MP_TAC(SPEC `q:num` SQP_G_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= sieve_A * log z * inv(log D - log(&q))` MP_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_LE_INV) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `W = sieve_A * log z * inv(log D - log(&q))` THEN
    REPEAT DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(if (q == 1) (mod 4) then &2 / &q else &0) * W` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "W" THEN COND_CASES_TAC THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {n | z < &n /\ &n <= y}
      (\n. if prime n
           then (if (n == 1) (mod 4) then inv(&n) else &0) *
                inv(log D - log(&n))
           else &0) +
    inv z * inv(log D - log z)` THEN
  CONJ_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC SUM_PRIMES_HALF_OPEN_LE THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `q:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `log(&q) < log D` ASSUME_TAC THENL
       [MATCH_MP_TAC LOG_MONO_LT_IMP THEN
        MP_TAC(SPEC `q:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_LE_INV_EQ] THEN
        REWRITE_TAC[REAL_POS];
        MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
      X_GEN_TAC `q:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_MUL_LZERO] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {n | z < &n /\ &n <= y}
      (\n. if prime n
           then (if (n == 1) (mod 4) then inv(&n) else &0) *
                inv(log D - log(&n))
           else &0) =
    sum {n | z < &n /\ &n <= y}
      (\n. (if prime n then (if (n == 1) (mod 4) then inv(&n) else &0)
            else &0) * inv(log D - log(&n)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    BETA_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!s a b e:real. s <= a + b ==> s + e <= a + b + e`) THEN
  USE_THEN "abel" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let SQP_G_SUM = prove
 (`?C. &0 < C /\
       !z y. &3 <= z /\ z <= y
             ==> sum {q | prime q /\ z <= &q /\ &q < y} sqp_g
                 <= (log(log y) - log(log z)) + C / log z`,
  X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC MERTENS_AP4_INTERVAL THEN
  EXISTS_TAC `&2 * C` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:real`; `y:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b c d l. a <= &2 * b
                ==> b <= c / &2 + d / l ==> a <= c + (&2 * d) / l`) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p | prime p /\ &p < y}` THEN
    REWRITE_TAC[FINITE_PRIMES_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `q:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(SPEC `q:num` SQP_G_UPPER) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN UNDISCH_TAC `z <= &q` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The values divisible by q.                                                *)
(* ------------------------------------------------------------------------- *)

let SQP_SIEVE_COUNT_Q = prove
 (`!M q t. prime q /\ FINITE t /\ (!p. p IN t ==> prime p) /\ ~(q IN t)
           ==> abs(sieve_count
                     (IMAGE (\n. n EXP 2 + 1)
                            {n | n IN 1..M /\ q divides n EXP 2 + 1})
                     (\m. &(CARD {n | n IN {n | n IN 1..M /\
                                                q divides n EXP 2 + 1} /\
                                      n EXP 2 + 1 = m})) t -
                   (&M * sqp_g q) * product t sqp_g) <= &4 * &4 pow CARD t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. n EXP 2 + 1`; `{n | n IN 1..M /\ q divides n EXP 2 + 1}`;
                 `t:num->bool`] SIEVE_COUNT_IMAGE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..M` THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `{n | n IN {n | n IN 1..M /\ q divides n EXP 2 + 1} /\
         (!p. p IN t ==> p divides n EXP 2 + 1)} =
    {n | n IN 1..M /\
         !p. p IN (q:num) INSERT (t:num->bool)
             ==> p divides (n MOD p) EXP 2 + 1}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; GSYM SQP_DIVIDES_MOD] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p r. p divides r EXP 2 + 1`; `(q:num) INSERT t`; `M:num`]
                CRT_COUNT) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT] THEN
  REWRITE_TAC[GSYM sqp_rho; GSYM sqp_g; ETA_AX] THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `product t (\p. &(sqp_rho p)) <= &4 pow CARD t /\
                &0 <= product t (\p. &(sqp_rho p))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `product t (\p:num. &2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `p:num` THEN DISCH_TAC THEN
        REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
        MATCH_MP_TAC SQP_RHO_LE_2 THEN ASM_SIMP_TAC[];
        ASM_SIMP_TAC[PRODUCT_CONST] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
        REAL_ARITH_TAC];
      MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN
  MP_TAC(SPEC `q:num` SQP_RHO_LE_2) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC);;

let SQP_REMAINDER_SUM_Q = prove
 (`?K. &0 < K /\
       !M q z Y. prime q /\ z <= &q /\ &2 <= Y
               ==> sum {t | t SUBSET {p | prime p /\ &p < z} /\
                            &(nproduct t (\p. p)) < Y}
                     (\t. abs(sieve_count
                               (IMAGE (\n. n EXP 2 + 1)
                                      {n | n IN 1..M /\
                                           q divides n EXP 2 + 1})
                               (\m. &(CARD {n | n IN {n | n IN 1..M /\
                                                   q divides n EXP 2 + 1} /\
                                                n EXP 2 + 1 = m})) t -
                              (&M * sqp_g q) * product t sqp_g))
                   <= K * Y * log Y pow 4`,
  X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC SUM_FOUR_POW_CARD THEN
  EXISTS_TAC `&4 * K` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t | t SUBSET {p | prime p /\ &p < z} /\
                       &(nproduct t (\p. p)) < Y}
                  (\t. &4 * &4 pow CARD t)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{t:num->bool | t SUBSET {p | prime p /\ &p < z}}` THEN
      SIMP_TAC[FINITE_POWERSET; FINITE_PRIMES_LT] THEN SET_TAC[];
      X_GEN_TAC `t:num->bool` THEN
      DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[IN_ELIM_THM]) THEN
      BETA_TAC THEN MATCH_MP_TAC SQP_SIEVE_COUNT_Q THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{p | prime p /\ &p < z}` THEN
        ASM_REWRITE_TAC[FINITE_PRIMES_LT];
        UNDISCH_TAC `(t:num->bool) SUBSET {p | prime p /\ &p < z}` THEN
        SET_TAC[];
        DISCH_TAC THEN
        UNDISCH_TAC `(t:num->bool) SUBSET {p | prime p /\ &p < z}` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `q:num`) THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[SUM_LMUL; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[FINITE_PRIMES_LT] THEN
    SIMP_TAC[IN_ELIM_THM]]);;

let SQP_SIFTED_Q = prove
 (`!M q z.
     sifted (IMAGE (\n. n EXP 2 + 1) {n | n IN 1..M /\ q divides n EXP 2 + 1})
            (\m. &(CARD {n | n IN {n | n IN 1..M /\ q divides n EXP 2 + 1} /\
                             n EXP 2 + 1 = m}))
            {p | prime p /\ &p < z} =
     &(CARD {n | n IN 1..M /\ q divides n EXP 2 + 1 /\
                 !p. prime p /\ &p < z ==> ~(p divides n EXP 2 + 1)})`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\n. n EXP 2 + 1`; `{n | n IN 1..M /\ q divides n EXP 2 + 1}`;
                 `{p | prime p /\ &p < z}`] SIFTED_IMAGE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..M` THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; CONJ_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Numerical and asymptotic lemmas.                                          *)
(* ------------------------------------------------------------------------- *)

let SQP3_LOG_CONST = prove
 (`&13 / &100 <= log(&3) - log(&204 / &31) / &2`,
  SUBGOAL_THEN `log(&204 / &31) = log(&3) + log(&3) + log(&1 - &25 / &93)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `&204 / &31 = &3 * &3 * (&1 - &25 / &93)` SUBST1_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    SIMP_TAC[LOG_MUL; REAL_ARITH `&0 < &3`; REAL_LT_MUL;
             REAL_ARITH `&0 < &1 - &25 / &93`];
    ALL_TAC] THEN
  MP_TAC(SPEC `&25 / &93` LOG_ONE_MINUS_BOUNDS) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ABBREV_TAC `l = log(&68 / &93)` THEN REAL_ARITH_TAC);;

let EXP_POLY_SMALL = prove
 (`!a k e. &0 < a /\ &0 < e
           ==> ?L0. &1 <= L0 /\
                    !LN. L0 <= LN ==> LN pow k <= e * exp(a * LN)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `inv(e:real)`; `a:real`] POLYLOG_EXP_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `L0:real`) THEN
  EXISTS_TAC `max (&1) L0` THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
  X_GEN_TAC `LN:real` THEN REWRITE_TAC[REAL_MAX_LE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `LN:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(LN:real) pow k = e * (inv e * LN pow k)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let SUM_PRIMES_INV_LE = prove
 (`!y. &1 <= y ==> sum {p | prime p /\ &p < y} (\p. inv(&p)) <= &1 + log y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `y:real` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  SUBGOAL_THEN `&n <= y /\ y < &n + &1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FLOOR]; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    ASM_MESON_TAC[REAL_LE_FLOOR; INTEGER_CLOSED];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..n) (\k. inv(&k))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    SIMP_TAC[FINITE_NUMSEG; REAL_LE_INV_EQ; REAL_POS] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    MP_TAC(SPEC `p:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p < n + 1` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD] THEN
      ASM_REAL_ARITH_TAC;
      ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + log(&n)` THEN
    ASM_SIMP_TAC[HARMONIC_LE_LOG] THEN REWRITE_TAC[REAL_LE_LADD] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC]);;

let SQP3_LOG_IDENTITY = prove
 (`log(&17 / &25) - log(&31 / &100) - (log(&99 / &400) - log(&297 / &400)) =
   log(&204 / &31) /\
   log(&17 / &25) - log(&99 / &400) = log(&272 / &99)`,
  SUBGOAL_THEN `&204 / &31 = (&17 / &25) / (&31 / &100) *
                             ((&297 / &400) / (&99 / &400)) /\
                &272 / &99 = (&17 / &25) / (&99 / &400)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SIMP_TAC[LOG_MUL; LOG_DIV; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* n^2 + 1 is a product of at most three primes infinitely often.            *)
(* ------------------------------------------------------------------------- *)

let SQUARE_PLUS_ONE_P3_COUNT = prove
 (`?c M0. &0 < c /\
          !M. M0 <= M
              ==> c * &M / log(&M) <=
                  &(CARD {n | n IN 1..M /\ almost_prime 3 (n EXP 2 + 1)})`,
  X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC SQP_G_DIMENSION THEN
  MP_TAC(SPECL [`L:real`; `&1 / &100`] JURKAT_RICHERT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `sqp_g`))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SQP_G_BOUNDS]; DISCH_THEN(LABEL_TAC "jr")] THEN
  X_CHOOSE_THEN `c0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vlow"))
    SQP_V_LOWER THEN
  X_CHOOSE_THEN `K0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rem0"))
    SQP_REMAINDER_SUM THEN
  X_CHOOSE_THEN `Kq:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "remq"))
    SQP_REMAINDER_SUM_Q THEN
  X_CHOOSE_THEN `Cf:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gf"))
    SQP_GF_SUM THEN
  X_CHOOSE_THEN `Cg:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gs"))
    SQP_G_SUM THEN
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
  ABBREV_TAC `ep = &7 / &198 * c0` THEN
  SUBGOAL_THEN `&0 < ep` ASSUME_TAC THENL
   [EXPAND_TAC "ep" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ep / (&16 * K0 * Pw) /\ &0 < ep / (&16 * Kq * Pw) /\
                &0 < ep / &6 /\ &0 < ep / &4`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&1 / &100`; `5`; `ep / (&16 * K0 * Pw)`] EXP_POLY_SMALL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l1"))) THEN
  MP_TAC(SPECL [`&1 / &100`; `6`; `ep / (&16 * Kq * Pw)`] EXP_POLY_SMALL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L2:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l2"))) THEN
  MP_TAC(SPECL [`&99 / &400`; `1`; `ep / &6`] EXP_POLY_SMALL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L3:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l3"))) THEN
  MP_TAC(SPECL [`&8 / &25`; `1`; `ep / &4`] EXP_POLY_SMALL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L4:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l4"))) THEN
  MP_TAC(SPECL [`&99 / &400`; `0`; `&1 / &267`] EXP_POLY_SMALL) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L5:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l5"))) THEN
  MP_TAC(SPEC `L1 + L2 + L3 + L4 + L5 + &400 / &99 * log w + log Pw +
               &80000 / &31 * abs Cf + &1600 / &99 * abs Cg + &3`
              EVENTUALLY_LOG_GE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
  EXISTS_TAC `&14 / &99 * c0` THEN EXISTS_TAC `N0 + 16` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `M:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `M:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&16 <= &M` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(log(&M)) = &M` ASSUME_TAC THENL
   [MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `LN = log(&M)` THEN
  SUBGOAL_THEN
   `L1 <= LN /\ L2 <= LN /\ L3 <= LN /\ L4 <= LN /\ L5 <= LN /\
    &400 / &99 * log w <= LN /\ log Pw <= LN /\
    &80000 / &31 * abs Cf <= LN /\ &1600 / &99 * abs Cg <= LN /\ &3 <= LN`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= abs Cf /\ &0 <= abs Cg` MP_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `D = exp(&99 / &100 * LN)` THEN
  ABBREV_TAC `z = exp(&99 / &400 * LN)` THEN
  ABBREV_TAC `y = exp(&17 / &25 * LN)` THEN
  SUBGOAL_THEN `log D = &99 / &100 * LN /\ log z = &99 / &400 * LN /\
                log y = &17 / &25 * LN`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "z"; "y"] THEN REWRITE_TAC[LOG_EXP];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < D /\ &0 < z /\ &0 < y` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "z"; "y"] THEN REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `&267 <= z` ASSUME_TAC THENL
   [REMOVE_THEN "l5" (MP_TAC o SPEC `LN:real`) THEN
    ASM_REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real) <= z` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log w)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "z" THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real) <= y /\ y < D` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["z"; "y"; "D"] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE; REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(M EXP 2 + 1) < y pow 3` ASSUME_TAC THENL
   [SUBGOAL_THEN `y pow 3 = &M pow 2 * exp(LN / &25)` SUBST1_TAC THENL
     [EXPAND_TAC "y" THEN REWRITE_TAC[GSYM REAL_EXP_N] THEN
      SUBGOAL_THEN `&M pow 2 = exp(&2 * LN)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[REAL_EXP_N]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
    MP_TAC(SPEC `LN / &25` REAL_EXP_LE_X) THEN
    SUBGOAL_THEN `&256 <= &M pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&16 pow 2` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `P2 = &M pow 2` THEN ABBREV_TAC `E = exp(LN / &25)` THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `P2 * (&1 + &3 / &25) <= P2 * E` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log z <= log D - log y /\ log D - log z <= &3 * log z /\
                &0 < log z /\ log y < log D`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`M:num`; `z:real`; `y:real`] SQP3_COMBINATORIAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `S0 = &(CARD {n | n IN 1..M /\
                        !p. prime p /\ &p < z
                            ==> ~(p divides n EXP 2 + 1)})` THEN
  ABBREV_TAC `Q = {q | prime q /\ z <= &q /\ &q < y}` THEN
  ABBREV_TAC `T0 = sum Q (\q. &(CARD {n | n IN 1..M /\ q divides n EXP 2 + 1 /\
                              !p. prime p /\ &p < z
                                  ==> ~(p divides n EXP 2 + 1)}))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `FINITE(Q:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p | prime p /\ &p < y}` THEN
    REWRITE_TAC[FINITE_PRIMES_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `V = product {p | prime p /\ &p < z} (\p. &1 - sqp_g p)` THEN
  SUBGOAL_THEN `&400 / &99 * c0 / LN <= V /\ &0 < V` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c0 / log z` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        UNDISCH_TAC `&3 <= LN` THEN CONV_TAC REAL_FIELD;
        EXPAND_TAC "V" THEN USE_THEN "vlow" MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC];
      EXPAND_TAC "V" THEN REWRITE_TAC[SQP_V_POS]];
    ALL_TAC] THEN
  USE_THEN "jr" (MP_TAC o SPECL
   [`IMAGE (\n. n EXP 2 + 1) (1..M)`;
    `\m. &(CARD {n | n IN 1..M /\ n EXP 2 + 1 = m})`;
    `&M`; `D:real`; `z:real`]) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; REAL_POS] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `log D / log z = &4` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&3 <= LN` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. n EXP 2 + 1`; `1..M`; `{p | prime p /\ &p < z}`]
                SIFTED_IMAGE) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `R0 = sum {t | t SUBSET {p | prime p /\ &p < z} /\
                  &(nproduct t (\p. p)) < D * Pw}
             (\t. abs(sieve_count (IMAGE (\n. n EXP 2 + 1) (1..M))
                        (\m. &(CARD {n | n IN 1..M /\ n EXP 2 + 1 = m})) t -
                      &M * product t sqp_g))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!q. q IN Q
        ==> &(CARD {n | n IN 1..M /\ q divides n EXP 2 + 1 /\
                        !p. prime p /\ &p < z ==> ~(p divides n EXP 2 + 1)})
            <= &M * V * (sqp_g q * sieve_F((log D - log(&q)) / log z)) +
               (&M * V / &100) * sqp_g q +
               Kq * (D / &q * Pw) * log(D / &q * Pw) pow 4`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:num` THEN EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < &q /\ log(&q) < log y /\ log z <= log(&q)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOG_MONO_LT_IMP; MATCH_MP_TAC LOG_MONO_LE_IMP] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "jr" (MP_TAC o SPECL
     [`IMAGE (\n. n EXP 2 + 1) {n | n IN 1..M /\ q divides n EXP 2 + 1}`;
      `\m. &(CARD {n | n IN {n | n IN 1..M /\ q divides n EXP 2 + 1} /\
                       n EXP 2 + 1 = m})`;
      `&M * sqp_g q`; `D / &q`; `z:real`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `1..M` THEN REWRITE_TAC[FINITE_NUMSEG] THEN SET_TAC[];
        REWRITE_TAC[REAL_POS];
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MP_TAC(SPEC `q:num` SQP_G_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC;
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `log(D / &q) = log D - log(&q)` SUBST1_TAC THENL
     [MATCH_MP_TAC LOG_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SQP_SIFTED_Q] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!s a b c r r':real.
        r <= r' /\ a = b + c ==> s <= a + r ==> s <= b + c + r'`) THEN
    CONJ_TAC THENL
     [USE_THEN "remq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `D / y * &1` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_RID] THEN
        SUBGOAL_THEN `D / y = z * exp(&1 / &16 * LN)` SUBST1_TAC THENL
         [MAP_EVERY EXPAND_TAC ["D"; "y"; "z"] THEN
          REWRITE_TAC[GSYM REAL_EXP_SUB; GSYM REAL_EXP_ADD] THEN
          AP_TERM_TAC THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `z * &1` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&1 + &1 / &16 * LN` THEN
        REWRITE_TAC[REAL_EXP_LE_X] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `T0 <= &M * V * sum Q (\q. sqp_g q * sieve_F((log D - log(&q)) / log z)) +
          (&M * V / &100) * sum Q sqp_g +
          sum Q (\q. Kq * (D / &q * Pw) * log(D / &q * Pw) pow 4)`
  ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum Q (\q. &M * V * (sqp_g q * sieve_F((log D - log(&q)) / log z)) +
                 (&M * V / &100) * sqp_g q +
                 Kq * (D / &q * Pw) * log(D / &q * Pw) pow 4)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `q:num` THEN DISCH_TAC THEN BETA_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; ETA_AX; REAL_LE_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC
   `GF = sum Q (\q. sqp_g q * sieve_F((log D - log(&q)) / log z))` THEN
  ABBREV_TAC `G = sum Q sqp_g` THEN
  ABBREV_TAC
   `RQ = sum Q (\q. Kq * (D / &q * Pw) * log(D / &q * Pw) pow 4)` THEN
  MP_TAC SIEVE_A_GE_3 THEN DISCH_TAC THEN
  SUBGOAL_THEN `GF <= sieve_A / &4 * log(&204 / &31) + sieve_A / &200`
  ASSUME_TAC THENL
   [EXPAND_TAC "GF" THEN EXPAND_TAC "Q" THEN
    USE_THEN "gf" (MP_TAC o SPECL [`D:real`; `z:real`; `y:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    SUBGOAL_THEN
     `(log(log y) - log(log D - log y)) - (log(log z) - log(log D - log z)) =
      log(&204 / &31)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&99 / &100 * LN - &17 / &25 * LN = &31 / &100 * LN /\
                    &99 / &100 * LN - &99 / &400 * LN = &297 / &400 * LN`
      (CONJUNCTS_THEN SUBST1_TAC) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < LN` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC;
       ALL_TAC] THEN
      ASM_SIMP_TAC[LOG_MUL; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
      MP_TAC SQP3_LOG_IDENTITY THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&2 * sieve_A * log z *
      (log(&204 / &31) / (&2 * log D) + Cf / (log z * (log D - log y)) +
       inv z * inv(log D - log z)) =
      sieve_A / &4 * log(&204 / &31) +
      sieve_A * (&200 / &31 * Cf / LN) + sieve_A * (&2 / &3 * inv z)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`&3 <= LN`; `&267 <= z`] THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `a + b * x + b * y <= a + b / &200 <=>
                            b * (x + y) <= b * (&1 / &200)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `x <= &1 / &400 /\ y <= &1 / &400 ==> x + y <= &1 / &200`) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `Cf / LN <= &31 / &80000` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&3 <= x ==> &0 < x`] THEN
        UNDISCH_TAC `&80000 / &31 * abs Cf <= LN` THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      SUBGOAL_THEN `inv z <= inv(&267)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `G <= &2` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN EXPAND_TAC "Q" THEN
    USE_THEN "gs" (MP_TAC o SPECL [`z:real`; `y:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    SUBGOAL_THEN `log(log y) - log(log z) = log(&272 / &99)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < LN` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC;
       ALL_TAC] THEN
      ASM_SIMP_TAC[LOG_MUL; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
      MP_TAC SQP3_LOG_IDENTITY THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `log(&272 / &99) <= &173 / &99` ASSUME_TAC THENL
     [SUBGOAL_THEN `&272 / &99 = &1 + &173 / &99` SUBST1_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC LOG_LE THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `Cg / log z <= &1 / &4` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < &99 / &400 * LN` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      UNDISCH_TAC `&1600 / &99 * abs Cg <= LN` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `log(&272 / &99) <= &173 / &99` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `D * exp(LN / &100) = &M /\ y * exp(&8 / &25 * LN) = &M /\
                &0 < LN /\ &1 <= y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "D" THEN REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
      SUBGOAL_THEN `&M = exp LN` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC;
      EXPAND_TAC "y" THEN REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
      SUBGOAL_THEN `&M = exp LN` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= D * Pw` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `D * &1` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(D * Pw) /\ log(D * Pw) <= &2 * LN`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[LOG_MUL; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &16 * K0 * Pw /\ &0 < &16 * Kq * Pw`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `R0 <= ep * &M / LN` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `K0 * (D * Pw) * log(D * Pw) pow 4` THEN CONJ_TAC THENL
     [EXPAND_TAC "R0" THEN USE_THEN "rem0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&16 * K0 * Pw * LN pow 4) * D` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `K0 * (D * Pw) * (&2 * LN) pow 4` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    REMOVE_THEN "l1" (MP_TAC o SPEC `LN:real`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&1 / &100 * LN = LN / &100`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&16 * K0 * Pw) * LN pow 5 <= ep * exp(LN / &100)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&16 * K0 * Pw) * (ep / (&16 * K0 * Pw) * exp(LN / &100))`
      THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        UNDISCH_TAC `&0 < &16 * K0 * Pw` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `&M = D * exp(LN / &100)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((&16 * K0 * Pw) * LN pow 5) * D` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(ep * exp(LN / &100)) * D` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `RQ <= &2 * ep * &M / LN` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum Q (\q. (&16 * Kq * Pw * LN pow 4 * D) * inv(&q))` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "RQ" THEN MATCH_MP_TAC SUM_LE THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `q:num` THEN EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `&1 <= &q /\ z <= D / &q` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&0 < &q` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
        SUBGOAL_THEN `D = z * exp(&3 / &4 * &99 / &100 * LN)` SUBST1_TAC THENL
         [MAP_EVERY EXPAND_TAC ["D"; "z"] THEN
          REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `y:real` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        EXPAND_TAC "y" THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= D / &q * Pw /\ D / &q * Pw <= D * Pw`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(D / &q) * &1` THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
           [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
            GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
            MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
            ASM_REAL_ARITH_TAC]];
        ALL_TAC] THEN
      SUBGOAL_THEN `log(D / &q * Pw) pow 4 <= (&2 * LN) pow 4` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(D * Pw)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= inv(&q) /\ &0 <= D * Pw` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      UNDISCH_TAC `log(D / &q * Pw) pow 4 <= (&2 * LN) pow 4` THEN
      SUBGOAL_THEN `D / &q * Pw = (D * Pw) * inv(&q)` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ABBREV_TAC `l4 = log((D * Pw) * inv(&q)) pow 4` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Kq * ((D * Pw) * inv(&q)) * (&2 * LN) pow 4` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_LMUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&16 * Kq * Pw * LN pow 4 * D) * (&2 * LN)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum {p | prime p /\ &p < y} (\p. inv(&p))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
        REWRITE_TAC[FINITE_PRIMES_LT] THEN CONJ_TAC THENL
         [EXPAND_TAC "Q" THEN SET_TAC[];
          SIMP_TAC[IN_DIFF; IN_ELIM_THM; REAL_LE_INV_EQ; REAL_POS]];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + log y` THEN
        ASM_SIMP_TAC[SUM_PRIMES_INV_LE] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REMOVE_THEN "l2" (MP_TAC o SPEC `LN:real`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&1 / &100 * LN = LN / &100`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&16 * Kq * Pw) * LN pow 6 <= ep * exp(LN / &100)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&16 * Kq * Pw) * (ep / (&16 * Kq * Pw) * exp(LN / &100))`
      THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        UNDISCH_TAC `&0 < &16 * Kq * Pw` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `&M = D * exp(LN / &100)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * ((&16 * Kq * Pw) * LN pow 6) * D` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * (ep * exp(LN / &100)) * D` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&6 * &M / z + &2 * y + &2 <= &2 * ep * &M / LN`
  ASSUME_TAC THENL
   [REMOVE_THEN "l3" (MP_TAC o SPEC `LN:real`) THEN
    REMOVE_THEN "l4" (MP_TAC o SPEC `LN:real`) THEN
    ASM_REWRITE_TAC[REAL_POW_1] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `&6 * LN <= ep * z /\ &4 * LN <= ep * exp(&8 / &25 * LN)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&6 * &M / z <= ep * &M / LN` ASSUME_TAC THENL
     [SUBGOAL_THEN `&6 * &M / z = (&6 * LN) * (&M / (z * LN)) /\
                    ep * &M / LN = (ep * z) * (&M / (z * LN))`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN MAP_EVERY UNDISCH_TAC [`&0 < LN`; `&267 <= z`] THEN
        CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&4 * y <= ep * &M / LN` ASSUME_TAC THENL
     [SUBGOAL_THEN `&M = y * exp(&8 / &25 * LN)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&4 * y = (&4 * LN) * (y / LN) /\
                    ep * (y * exp(&8 / &25 * LN)) / LN =
                    (ep * exp(&8 / &25 * LN)) * (y / LN)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN UNDISCH_TAC `&0 < LN` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN
    UNDISCH_TAC `&6 * &M / z <= ep * &M / LN` THEN
    UNDISCH_TAC `&4 * y <= ep * &M / LN` THEN
    UNDISCH_TAC `&1 <= y` THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sieve_f(&4) = sieve_A * log(&3) / &4` ASSUME_TAC THENL
   [MP_TAC(SPEC `&4` SIEVE_LOWER_24_EXPLICIT) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&13 / &100 * sieve_A <=
                sieve_A * log(&3) - sieve_A * log(&204 / &31) / &2`
  ASSUME_TAC THENL
   [MP_TAC SQP3_LOG_CONST THEN DISCH_TAC THEN
    SUBGOAL_THEN `sieve_A * (&13 / &100) <=
                  sieve_A * (log(&3) - log(&204 / &31) / &2)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&7 / &100 <= sieve_f(&4) - &1 / &100 - (GF + G / &100) / &2`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`&13 / &100 * sieve_A <=
       sieve_A * log(&3) - sieve_A * log(&204 / &31) / &2`;
      `GF <= sieve_A / &4 * log(&204 / &31) + sieve_A / &200`;
      `G <= &2`; `&3 <= sieve_A`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &M * V` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&M * V) * (&7 / &100) <=
    (&M * V) * (sieve_f(&4) - &1 / &100 - (GF + G / &100) / &2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&28 / &99 * c0 * &M / LN <= (&M * V) * (&7 / &100)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&M * (&400 / &99 * c0 / LN)) * (&7 / &100)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`S0 - inv(&2) * T0 - (&6 * &M / z + &2 * y + &2) <=
     &(CARD {n | n IN 1..M /\ almost_prime 3 (n EXP 2 + 1)})`;
    `&M * V * (sieve_f(&4) - &1 / &100) - R0 <= S0`;
    `T0 <= &M * V * GF + (&M * V / &100) * G + RQ`;
    `(&M * V) * (&7 / &100) <=
     (&M * V) * (sieve_f(&4) - &1 / &100 - (GF + G / &100) / &2)`;
    `&28 / &99 * c0 * &M / LN <= (&M * V) * (&7 / &100)`;
    `R0 <= ep * &M / LN`; `RQ <= &2 * ep * &M / LN`;
    `&6 * &M / z + &2 * y + &2 <= &2 * ep * &M / LN`] THEN
  EXPAND_TAC "ep" THEN
  ABBREV_TAC `X = &(CARD {n | n IN 1..M /\ almost_prime 3 (n EXP 2 + 1)})` THEN
  ABBREV_TAC `Rep = &6 * &M / z + &2 * y + &2` THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let SQUARE_PLUS_ONE_P3 = prove
 (`INFINITE {n | almost_prime 3 (n EXP 2 + 1)}`,
  X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `M0:num` STRIP_ASSUME_TAC)
    SQUARE_PLUS_ONE_P3_COUNT THEN
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
