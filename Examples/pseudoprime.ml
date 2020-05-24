(* ========================================================================= *)
(* Fermat, weak Euler and Euler-Jacobi pseudoprimes, Carmichael numbers etc. *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "Examples/miller_rabin.ml";;

(* ------------------------------------------------------------------------- *)
(* A little set cardinality lemma we use repeatedly. In an explicitly group  *)
(* theoretic setting, Lagrange's theorem takes the place of this.            *)
(* ------------------------------------------------------------------------- *)

let CARD_SUBSET_HALF_LEMMA = prove
 (`!f s (t:A->bool) n.
        FINITE t /\ CARD t <= n /\
        s SUBSET t /\ IMAGE f s SUBSET t DIFF s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> 2 * CARD s <= n`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE
   `!f t. CARD t <= n /\
          CARD(IMAGE f s) <= CARD(t DIFF s) /\
          CARD(t DIFF s) + CARD(s) = CARD t /\
          CARD(IMAGE (f:A->A) s) = CARD s
          ==> 2 * CARD s <= n`) THEN
  MAP_EVERY EXISTS_TAC [`f:A->A`; `t:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_SIMP_TAC[FINITE_DIFF] THEN ASM SET_TAC[];
    MATCH_MP_TAC CARD_UNION_EQ THEN ASM SET_TAC[];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[FINITE_SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* Fermat pseudoprimes and Carmichael numbers.                               *)
(* ------------------------------------------------------------------------- *)

let fermat_pseudoprime = new_definition
 `fermat_pseudoprime a n <=>
        (a EXP (n - 1) == 1) (mod n)`;;

let carmichael_number = new_definition
 `carmichael_number n <=>
     2 <= n /\ ~prime n /\ !a. coprime(a,n) ==> fermat_pseudoprime a n`;;

let CARMICHAEL_NUMBER,CARMICHAEL_NUMBER_KORSELT_ALT = (CONJ_PAIR o prove)
 (`(!n. carmichael_number n <=>
        2 <= n /\ ~prime n /\ !a. (a EXP n == a) (mod n)) /\
   (!n. carmichael_number n <=>
        2 <= n /\ ~prime n /\ ODD n /\
        !p. prime p /\ p divides n
            ==> ~(p EXP 2 divides n) /\ (p - 1) divides (n - 1))`,
  REWRITE_TAC[carmichael_number; fermat_pseudoprime; AND_FORALL_THM] THEN
  X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ARITH] THEN MATCH_MP_TAC(TAUT
   `(q ==> p) /\ (p ==> r) /\ (r ==> q) ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [GEN_TAC THEN MATCH_MP_TAC(NUMBER_RULE
     `(a * x == a) (mod n) ==> coprime(a,n) ==> (x == 1) (mod n)`) THEN
    ASM_SIMP_TAC[GSYM(CONJUNCT2 EXP); ARITH_RULE `2 <= n ==> SUC(n - 1) = n`];
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM NOT_EVEN] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN ANTS_TAC THENL
       [MATCH_MP_TAC COPRIME_MINUS1 THEN ASM_ARITH_TAC;
        REWRITE_TAC[fermat_pseudoprime]] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
       `(a EXP k == 1) (mod n) ==> (a * a EXP k == a) (mod n)`)) THEN
      ASM_SIMP_TAC[GSYM(CONJUNCT2 EXP); ARITH_RULE
       `2 <= n ==> SUC(n - 1) = n`] THEN
      SUBGOAL_THEN
       `?m. (n - 1) EXP n = (n - 1) EXP (2 * m)`
       (X_CHOOSE_THEN `m:num` SUBST1_TAC) THENL
        [ASM_MESON_TAC[EVEN_EXISTS]; REWRITE_TAC[GSYM EXP_EXP]] THEN
      MATCH_MP_TAC(MESON[CONG_TRANS; CONG_SYM]
       `(x == 1) (mod n) /\ ~(y == 1) (mod n) ==> ~(x == y) (mod n)`) THEN
      ASM_SIMP_TAC[CONG_EXP_1; CONG_MINUS1_SQUARED] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONG_SUB)) THEN
      DISCH_THEN(MP_TAC o SPECL [`1`; `1`]) THEN
      REWRITE_TAC[CONG_REFL; LE_REFL; CONG_0_DIVIDES; SUB_REFL; NOT_IMP] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE_STRONG) THEN
      ASM_CASES_TAC `n = 2` THENL [ASM_MESON_TAC[PRIME_2]; ASM_ARITH_TAC];
      DISCH_TAC] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `ODD p` THENL
     [ALL_TAC; ASM_MESON_TAC[DIVIDES_TRANS; DIVIDES_2; NOT_ODD]] THEN
    ASM_CASES_TAC `p = 0` THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
    ASM_CASES_TAC `p = 1` THENL [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
    MP_TAC(SPECL [`n:num`; `p:num`] INDEX_DECOMPOSITION_PRIME) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `m:num` THEN
    ABBREV_TAC `k = index p n` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
     [EXPAND_TAC "k" THEN REWRITE_TAC[INDEX_EQ_0] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(snd(EQ_IMP_RULE(SPEC `p EXP k` PRIMITIVE_ROOT_EXISTS))) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ODD_PRIME]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `g:num`) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIMITIVE_ROOT_IMP_COPRIME) THEN
    REWRITE_TAC[EXP_EQ_0; COPRIME_LEXP; ARITH_EQ] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p EXP k`; `m:num`; `g:num`; `1`]
      CHINESE_REMAINDER_USUAL) THEN
    ASM_REWRITE_TAC[COPRIME_LEXP; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `t:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:num`) THEN
    EXPAND_TAC "n" THEN ANTS_TAC THENL
     [REWRITE_TAC[COPRIME_RMUL; COPRIME_REXP] THEN CONJ_TAC THENL
       [DISJ1_TAC THEN UNDISCH_TAC `(t == g) (mod (p EXP k))` THEN
        DISCH_THEN(MP_TAC o MATCH_MP CONG_COPRIME) THEN
        ASM_REWRITE_TAC[COPRIME_LEXP] THEN MESON_TAC[COPRIME_SYM];
        ASM_MESON_TAC[NUMBER_RULE `(t == 1) (mod m) ==> coprime(t,m)`]];
      DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
       `(a == 1) (mod (n * m)) ==> (a == 1) (mod n)`))] THEN
    ASM_REWRITE_TAC[ORDER_DIVIDES] THEN
    SUBGOAL_THEN `order (p EXP k) t = order (p EXP k) g` SUBST1_TAC THENL
     [ASM_MESON_TAC[ORDER_CONG]; ASM_REWRITE_TAC[]] THEN
    ASM_SIMP_TAC[PHI_PRIMEPOW_ALT] THEN DISCH_THEN(MP_TAC o MATCH_MP
     (NUMBER_RULE `(a:num) * b divides c ==> a divides c /\ b divides c`)) THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`p EXP (k - 1)`; `n:num`] CONG_1_DIVIDES_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXPAND_TAC "n" THEN DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
     `(p * m == 1) (mod q) ==> q divides p ==> q = 1`)) THEN
    ASM_SIMP_TAC[DIVIDES_EXP_LE; PRIME_GE_2; EXP_EQ_1] THEN
    ASM_REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX; ARITH_RULE `k - 1 <= k`] THEN
    ARITH_TAC;
    X_GEN_TAC `a:num` THEN
    ABBREV_TAC `b = a EXP n` THEN
    SUBGOAL_THEN
     `!m:num. m divides n ==> (b == a) (mod m)`
     (fun th -> MESON_TAC[th; DIVIDES_REFL]) THEN
    MATCH_MP_TAC INDUCT_COPRIME_ALT THEN
    ASM_REWRITE_TAC[DIVIDES_ZERO] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[DIVIDES_LMUL2; DIVIDES_RMUL2; CONG_CHINESE]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `k:num`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[EXP; CONG_MOD_1] THEN
    ASM_CASES_TAC `k = 1` THENL
     [ALL_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT
       `(dk ==> d2) /\ (dk ==> d)
        ==> (d ==> ~d2 /\ p) ==> dk ==> q`) THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [GSYM EXP_1] THEN
      CONJ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] DIVIDES_TRANS) THEN
      MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ASM_ARITH_TAC] THEN
    ASM_REWRITE_TAC[EXP_1] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `coprime(a:num,p)` THENL
     [SUBGOAL_THEN `b = a * a EXP (n - 1)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
        ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> SUC(n - 1) = n`];
        ALL_TAC] THEN
      MATCH_MP_TAC(NUMBER_RULE
       `(b == 1) (mod n) ==> (a * b == a) (mod n)`) THEN
      UNDISCH_TAC `p - 1 divides n - 1` THEN
      SIMP_TAC[divides; LEFT_IMP_EXISTS_THM; GSYM EXP_EXP] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_EXP_1 THEN
      ASM_SIMP_TAC[FERMAT_LITTLE_PRIME];
      MATCH_MP_TAC(NUMBER_RULE
       `p divides a /\ p divides b ==> (b:num == a) (mod p)`) THEN
      EXPAND_TAC "b" THEN ASM_SIMP_TAC[PRIME_DIVEXP_EQ] THEN
      ASM_MESON_TAC[PRIME_COPRIME_EQ; COPRIME_SYM]]]);;

let CARMICHAEL_NUMBER_KORSELT = prove
 (`!n. carmichael_number n <=>
        2 <= n /\ ~prime n /\ ODD n /\ squarefree n /\
        !p. prime p /\ p divides n ==> (p - 1) divides (n - 1)`,
  REWRITE_TAC[CARMICHAEL_NUMBER_KORSELT_ALT; SQUAREFREE_PRIME_DIVISOR] THEN
  MESON_TAC[]);;

let CARMICHAEL_NUMBER_IMP_ODD = prove
 (`!n. carmichael_number n ==> ODD n`,
  SIMP_TAC[CARMICHAEL_NUMBER_KORSELT]);;

let CARMICHAEL_NUMBER_IMP_SQUAREFREE = prove
 (`!n. carmichael_number n ==> squarefree n`,
  SIMP_TAC[CARMICHAEL_NUMBER_KORSELT]);;

let CARMICHAEL_NUMBER_IMP_NZ = prove
 (`!n. carmichael_number n ==> ~(n = 0)`,
  MESON_TAC[CARMICHAEL_NUMBER_IMP_ODD; ODD]);;

let CARMICHAEL_NUMBER_IMP_TRIPLET = prove
 (`!n. carmichael_number n ==> CARD {p | prime p /\ p divides n} >= 3`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `n >= 3 <=> ~(n = 0) /\ ~(n = 1) /\ ~(n = 2)`] THEN
  ASM_SIMP_TAC[MESON[HAS_SIZE] `FINITE s ==> (CARD s = n <=> s HAS_SIZE n)`;
               FINITE_SPECIAL_DIVISORS; CARMICHAEL_NUMBER_IMP_NZ] THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC; X_GEN_TAC `p:num`; MAP_EVERY X_GEN_TAC [`p:num`; `q:num`]] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CARMICHAEL_NUMBER_IMP_SQUAREFREE) THEN
  ASM_SIMP_TAC[SQUAREFREE_EXPAND_EQ; NPRODUCT_CLAUSES; FINITE_INSERT;
               FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY; MULT_CLAUSES]
  THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [carmichael_number]) THEN
    ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [carmichael_number]) THEN
    ASM SET_TAC[];
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev)] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`q:num`; `p:num`] THEN
  MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[MULT_SYM] THEN SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[CARMICHAEL_NUMBER_KORSELT_ALT] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  SUBGOAL_THEN `n - 1 = p * (q - 1) + p - 1` SUBST1_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[LEFT_SUB_DISTRIB] THEN
    MATCH_MP_TAC(ARITH_RULE
     `~(p = 0) /\ p * 1 <= pq ==> pq - 1 = (pq - p * 1) + p - 1`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL; ARITH_RULE `1 <= q <=> ~(q = 0)`] THEN
    MP_TAC PRIME_IMP_NZ THEN ASM SET_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
     `(q:num) divides p * q + r ==> q divides r`)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE_STRONG) THEN
    SUBGOAL_THEN `2 <= p /\ 2 <= q` MP_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC PRIME_GE_2 THEN ASM SET_TAC[]]);;

let CARMICHAEL_NUMBER_PRIME_FACTOR_CONG_1 = prove
 (`!n p q.
        carmichael_number n /\
        prime p /\ p divides n /\
        prime q /\ q divides n
        ==> ~((q == 1) (mod p))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [CARMICHAEL_NUMBER_KORSELT]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CONG_1_DIVIDES) THEN
  UNDISCH_TAC `(p:num) divides n` THEN
  REWRITE_TAC[TAUT `p ==> ~q <=> ~(p /\ q)`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
   `q divides n /\ q divides q' /\ q' divides n'
    ==> (n' + 1 == n + 1) (mod q)`)) THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> n - 1 + 1 = n`] THEN
  REWRITE_TAC[NUMBER_RULE `(n == n + 1) (mod q) <=> q = 1`] THEN
  ASM_MESON_TAC[PRIME_1]);;

let FERMAT_PSEUDOPRIME_IMP_COPRIME = prove
 (`!a n. fermat_pseudoprime a n ==> n = 0 \/ coprime(a,n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[COPRIME_1] THEN
  REWRITE_TAC[fermat_pseudoprime] THEN DISCH_THEN(MP_TAC o MATCH_MP
   (NUMBER_RULE `(a == 1) (mod n) ==> coprime(a,n)`)) THEN
  ASM_REWRITE_TAC[COPRIME_LEXP] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let PRIME_IMP_FERMAT_PSEUDOPRIME = prove
 (`!p a. prime p /\ ~(p divides a) ==> fermat_pseudoprime a p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fermat_pseudoprime] THEN
  MATCH_MP_TAC FERMAT_LITTLE_PRIME THEN
  ASM_MESON_TAC[PRIME_COPRIME_EQ; COPRIME_SYM]);;

let PRIME_EQ_FERMAT_PSEUDOPRIME = prove
 (`!p. prime p <=> 2 <= p /\ (!a. 0 < a /\ a < p ==> fermat_pseudoprime a p)`,
  GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PRIME_GE_2] THENL
   [MATCH_MP_TAC PRIME_IMP_FERMAT_PSEUDOPRIME THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE_STRONG) THEN ASM_ARITH_TAC;
    REWRITE_TAC[PRIME] THEN
    REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:num`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP FERMAT_PSEUDOPRIME_IMP_COPRIME) THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let ABSOLUTE_FERMAT_PSEUDOPRIME = prove
 (`!n. (!a. coprime(a,n) ==> fermat_pseudoprime a n) <=>
       n = 0 \/ n = 1 \/ prime n \/ carmichael_number n`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[fermat_pseudoprime; COPRIME_0; CONG_MOD_0] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_SIMP_TAC[fermat_pseudoprime; CONG_MOD_1];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[carmichael_number; ARITH_RULE
   `2 <= n <=> ~(n = 0 \/ n = 1)`] THEN
  ASM_CASES_TAC `prime n` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PRIME_IMP_FERMAT_PSEUDOPRIME; PRIME_COPRIME_EQ; COPRIME_SYM]);;

let FERMAT_PSEUDOPRIME_BOUND_PHI_ALT = prove
 (`!n. ~(n = 1) /\ ~prime n /\ ~carmichael_number n
        ==> 2 * CARD {a | a < n /\ fermat_pseudoprime a n} <= phi n`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[LT; EMPTY_GSPEC; CARD_CLAUSES; MULT_CLAUSES; LE_0] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[carmichael_number; NOT_FORALL_THM; NOT_IMP;
         LEFT_IMP_EXISTS_THM; ARITH_RULE `2 <= n <=> ~(n = 0 \/ n = 1)`] THEN
  X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC CARD_SUBSET_HALF_LEMMA THEN
  EXISTS_TAC `\a. (a * b) MOD n` THEN
  EXISTS_TAC `{a:num | coprime(a,n) /\ a < n}` THEN
  SIMP_TAC[PHI_ALT; LE_REFL; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i < n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ASM_MESON_TAC[FERMAT_PSEUDOPRIME_IMP_COPRIME; LT];
    ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `n:num` THEN
    ASM_MESON_TAC[CONG_MULT_RCANCEL]] THEN
  X_GEN_TAC `a:num` THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[LT] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FERMAT_PSEUDOPRIME_IMP_COPRIME) THEN
  ASM_REWRITE_TAC[COPRIME_LMOD; COPRIME_LMUL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[MOD_LT_EQ; fermat_pseudoprime] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[fermat_pseudoprime]) THEN
  REWRITE_TAC[MOD_EXP_MOD; CONG] THEN REWRITE_TAC[GSYM CONG; MULT_EXP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
   `(a * b == 1) (mod n) ==> (a == 1) (mod n) ==> (b == 1) (mod n)`)) THEN
  ASM_REWRITE_TAC[]);;

let FERMAT_PSEUDOPRIME_BOUND_PHI = prove
 (`!n. ~(n = 1) /\ ~prime n /\ ~carmichael_number n
        ==> CARD {a | a < n /\ fermat_pseudoprime a n} <= phi n DIV 2`,
  REWRITE_TAC[ARITH_RULE `a <= b DIV 2 <=> 2 * a <= b`] THEN
  REWRITE_TAC[FERMAT_PSEUDOPRIME_BOUND_PHI_ALT]);;

let FERMAT_PSEUDOPRIME_BOUND_LT = prove
 (`!n. ~(n = 0) /\ ~(n = 1) /\ ~prime n /\ ~carmichael_number n
        ==> CARD {a | a < n /\ fermat_pseudoprime a n} < n DIV 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `n:num` FERMAT_PSEUDOPRIME_BOUND_PHI_ALT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `p < n - 1  ==> 2 * a <= p ==> a < n DIV 2`) THEN
  MATCH_MP_TAC PHI_LIMIT_COMPOSITE THEN ASM_REWRITE_TAC[]);;

let MILLER_RABIN_IMP_FERMAT_PSEUDOPRIME = prove
 (`!a q. miller_rabin_pseudoprime a q /\ ~(q = 2) ==> fermat_pseudoprime a q`,
  REWRITE_TAC[fermat_pseudoprime] THEN
  REWRITE_TAC[MILLER_RABIN_IMP_FERMAT_PSEUDOPRIME_EXPLICIT]);;

let MILLER_RABIN_EQ_FERMAT_PSEUDOPRIME = prove
 (`!a q. (?p k. prime p /\ ODD p /\ p EXP k = q)
         ==> (miller_rabin_pseudoprime a q <=> fermat_pseudoprime a q)`,
  REWRITE_TAC[fermat_pseudoprime] THEN
  REWRITE_TAC[MILLER_RABIN_EQ_FERMAT_PSEUDOPRIME_EXPLICIT]);;

(* ------------------------------------------------------------------------- *)
(* Weak Euler pseudoprimes.                                                  *)
(* ------------------------------------------------------------------------- *)

let weak_euler_pseudoprime = new_definition
 `weak_euler_pseudoprime a n <=>
        ODD n /\
        ((&a pow ((n - 1) DIV 2) == (&1:int)) (mod &n) \/
         (&a pow ((n - 1) DIV 2) == (-- &1:int)) (mod &n))`;;

let WEAK_EULER_IMP_FERMAT_PSEUDOPRIME = prove
 (`!a n. weak_euler_pseudoprime a n ==> fermat_pseudoprime a n`,
  REWRITE_TAC[fermat_pseudoprime; weak_euler_pseudoprime] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (INTEGER_RULE
   `(x:int == y) (mod m) ==> (x pow 2 == y pow 2) (mod m)`)) THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW; INT_POW_POW] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `x:int = y ==> (x == &1) (mod n) ==> (y == &1) (mod n)`) THEN
  AP_TERM_TAC THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[ODD_EXISTS]) THEN
  REWRITE_TAC[SUC_SUB1; ARITH_RULE `(2 * m) DIV 2 = m`] THEN ARITH_TAC);;

let WEAK_EULER_PSEUDOPRIME_IMP_ODD = prove
 (`!a n. weak_euler_pseudoprime a n ==> ODD n`,
  SIMP_TAC[weak_euler_pseudoprime]);;

let WEAK_EULER_PSEUDOPRIME_IMP_COPRIME = prove
 (`!a n. weak_euler_pseudoprime a n ==> coprime(a,n)`,
  MESON_TAC[WEAK_EULER_IMP_FERMAT_PSEUDOPRIME; FERMAT_PSEUDOPRIME_IMP_COPRIME;
            ODD; weak_euler_pseudoprime]);;

let PRIME_IMP_WEAK_EULER_PSEUDOPRIME = prove
 (`!p a. prime p /\ ~(p = 2) /\ ~(p divides a) ==> weak_euler_pseudoprime a p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[weak_euler_pseudoprime] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[PRIME_ODD]; ONCE_REWRITE_TAC[DISJ_SYM]] THEN
  MP_TAC(SPECL [`a:num`; `p:num`] JACOBI_CASES) THEN
  MP_TAC(SPECL [`a:num`; `p:num`] JACOBI_EULER) THEN
  ASM_REWRITE_TAC[JACOBI_EQ_0] THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  ASM_SIMP_TAC[PRIME_COPRIME_EQ] THEN ASM_MESON_TAC
   [INTEGER_RULE `(j == a) (mod p) ==> j:int = z ==> (a == z) (mod p)`]);;

let PRIME_EQ_WEAK_EULER_PSEUDOPRIME = prove
 (`!p. prime p <=>
       p = 2 \/ 2 <= p /\
       (!a. 0 < a /\ a < p ==> weak_euler_pseudoprime a p)`,
  GEN_TAC THEN ASM_CASES_TAC `p = 2` THEN ASM_REWRITE_TAC[PRIME_2] THEN
  EQ_TAC THENL
   [SIMP_TAC[PRIME_GE_2] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC PRIME_IMP_WEAK_EULER_PSEUDOPRIME THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE_STRONG) THEN ASM_ARITH_TAC;
    MESON_TAC[WEAK_EULER_IMP_FERMAT_PSEUDOPRIME;
              PRIME_EQ_FERMAT_PSEUDOPRIME]]);;

let MILLER_RABIN_IMP_WEAK_EULER_PSEUDOPRIME = prove
 (`!a q. miller_rabin_pseudoprime a q /\ ~(q = 2)
         ==> weak_euler_pseudoprime a q`,
  MAP_EVERY X_GEN_TAC [`a:num`; `n:num`] THEN
  REWRITE_TAC[miller_rabin_pseudoprime; weak_euler_pseudoprime] THEN
  ASM_CASES_TAC `n = 2` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ODD] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[INT_CONG_MOD_1; ARITH] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW] THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LE_1] THEN
  REWRITE_TAC[INTEGER_RULE
   `(x:int == n - z) (mod n) <=> (x == --z) (mod n)`] THEN
  MP_TAC(SPECL [`n - 1`; `2`] INDEX_DECOMPOSITION) THEN
  ASM_REWRITE_TAC[ARITH_EQ; ARITH_RULE `n - 1 = 0 <=> n = 0 \/ n = 1`] THEN
  ABBREV_TAC `e = index 2 (n - 1)` THEN
  REWRITE_TAC[DIVIDES_2; NOT_EVEN; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBST1_TAC(SYM(ASSUME `2 EXP e * m = n - 1`)) THEN
  SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `(2 EXP e * m) DIV 2 = 2 EXP (e - 1) * m` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[ARITH_RULE `(ee * m) * 2 + 0 = (2 * ee) * m`] THEN
    REWRITE_TAC[ARITH] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `e = SUC(e - 1) <=> ~(e = 0)`] THEN
    EXPAND_TAC "e" THEN REWRITE_TAC[INDEX_EQ_0] THEN
    ASM_REWRITE_TAC[NOT_EVEN; DIVIDES_2; ODD_SUB] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
   [DISJ1_TAC THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] (GSYM INT_POW_POW)] THEN
    ASM_SIMP_TAC[INT_CONG_POW_1];
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `i < e ==> e - 1 = SUC(i + (e - i - 2)) \/ e - 1 = i`)) THEN
  MATCH_MP_TAC MONO_OR THEN ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[EXP; EXP_ADD] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `2 * 2 EXP (e - i - 2)` o
    MATCH_MP INT_CONG_POW) THEN
  REWRITE_TAC[GSYM INT_POW_POW; INT_POW_NEG; INT_POW_ONE] THEN
  REWRITE_TAC[EVEN_MULT; ARITH; INT_POW_POW] THEN REWRITE_TAC[MULT_AC]);;

let MILLER_RABIN_EQ_WEAK_EULER_PSEUDOPRIME = prove
 (`!a n. ~(n = 2) /\ (?p k. prime p /\ ODD p /\ p EXP k = n) \/
         (n == 3) (mod 4)
         ==> (miller_rabin_pseudoprime a n <=> weak_euler_pseudoprime a n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 2` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
   [EQ_TAC THEN ASM_SIMP_TAC[MILLER_RABIN_IMP_WEAK_EULER_PSEUDOPRIME] THEN
    ASM_SIMP_TAC[MILLER_RABIN_EQ_FERMAT_PSEUDOPRIME] THEN
    REWRITE_TAC[WEAK_EULER_IMP_FERMAT_PSEUDOPRIME];
    REWRITE_TAC[CONG] THEN
    REWRITE_TAC[weak_euler_pseudoprime; miller_rabin_pseudoprime] THEN
    ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_CASES_TAC `ODD n` THEN ASM_REWRITE_TAC[CONG_MINUS1] THEN
    REWRITE_TAC[num_divides; GSYM INT_OF_NUM_ADD; num_congruent] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_POW; INTEGER_RULE
      `n divides (x + &1:int) <=> (x == -- &1) (mod n)`] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `n MOD 4 = 3 ==> n - 1 = 2 * (2 * (n DIV 4) + 1)`)) THEN
    ABBREV_TAC `m = n DIV 4` THEN
    SIMP_TAC[INDEX_MUL; PRIME_2; INDEX_REFL; ARITH;
             ARITH_RULE `~(2 * n + 1 = 0)`] THEN
    SIMP_TAC[INDEX_ZERO; DIVIDES_2; EVEN_ADD; EVEN_MULT; ARITH] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n`] THEN
    REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`; UNWIND_THM2] THEN
    REWRITE_TAC[EXP; MULT_CLAUSES]]);;

let ABSOLUTE_WEAK_EULER_PSEUDOPRIME,ABSOLUTE_WEAK_EULER_PSEUDOPRIME_ALT =
 (CONJ_PAIR o prove)
 (`(!n. (!a. coprime(a,n) ==> weak_euler_pseudoprime a n) <=>
        ODD n /\
        (prime n \/
         squarefree n /\
         !p. prime p /\ p divides n ==> (p - 1) divides ((n - 1) DIV 2))) /\
   (!n. (!a. coprime(a,n) ==> weak_euler_pseudoprime a n) <=>
        ODD n /\
        (prime n \/
         !a. coprime(a,n) ==> (a EXP ((n - 1) DIV 2) == 1) (mod n)))`,
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `ODD n` THENL
   [ASM_REWRITE_TAC[];
    ASM_MESON_TAC[WEAK_EULER_PSEUDOPRIME_IMP_ODD; COPRIME_1]] THEN
  ASM_CASES_TAC `prime n` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[COPRIME_SYM; PRIME_COPRIME_EQ;
                  PRIME_IMP_WEAK_EULER_PSEUDOPRIME;
                  NUM_REDUCE_CONV `ODD 2`];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[weak_euler_pseudoprime; CONG_MOD_1; INT_CONG_MOD_1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIVIDES_0; SQUAREFREE_1];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT
   `(r ==> p) /\ (q ==> r) /\ (p ==> q)
    ==> (p <=> q) /\ (p <=> r)`) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[weak_euler_pseudoprime; INT_OF_NUM_POW; GSYM num_congruent];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [STRIP_TAC THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC CONG_MOD_SQUAREFREE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN
    ASM_REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
    REWRITE_TAC[GSYM EXP_EXP] THEN MATCH_MP_TAC CONG_EXP_1 THEN
    MATCH_MP_TAC FERMAT_LITTLE_PRIME THEN
    MAP_EVERY UNDISCH_TAC [`coprime(a:num,n)`; `(p:num) divides n`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUMBER_RULE;
    DISCH_TAC] THEN
  MP_TAC(SPEC `n:num` ABSOLUTE_FERMAT_PSEUDOPRIME) THEN
  ASM_SIMP_TAC[WEAK_EULER_IMP_FERMAT_PSEUDOPRIME] THEN
  STRIP_TAC THENL [ASM_MESON_TAC[ODD]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CARMICHAEL_NUMBER_KORSELT]) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `p:num` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC) THEN
  DISJ_CASES_TAC(SPEC `m:num` EVEN_OR_ODD) THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:num` SUBST1_TAC) THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ARITH_RULE `(a * 2 * b) DIV 2 = a * b`] THEN
    CONV_TAC NUMBER_RULE;
    DISCH_THEN(ASSUME_TAC o SYM)] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  SUBGOAL_THEN `?q:num. p * q = n` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[divides]; ALL_TAC] THEN
  SUBGOAL_THEN `coprime(p:num,q)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SQUAREFREE_MUL]; ALL_TAC] THEN
  MP_TAC(snd(EQ_IMP_RULE(SPEC `p:num` QUADRATIC_NONRESIDUE_EXISTS))) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ODD_PRIME; PRIME_ODD; CARMICHAEL_NUMBER_IMP_ODD;
                  ODD_MULT; NUM_ODD_CONV `ODD 2`];
    DISCH_THEN(X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`p:num`; `q:num`; `b:num`; `1`]
        CHINESE_REMAINDER_USUAL) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:num`) THEN ANTS_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[COPRIME_RMUL] THEN
    ASM_SIMP_TAC[NUMBER_RULE `(a == 1) (mod q) ==> coprime(a,q)`] THEN
    MAP_EVERY UNDISCH_TAC [`coprime(p:num,b)`; `(a:num == b) (mod p)`] THEN
    CONV_TAC NUMBER_RULE;
    ASM_REWRITE_TAC[weak_euler_pseudoprime; DE_MORGAN_THM]] THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
      `(a:int == --z) (mod (p * q))
       ==> (a == z) (mod q) ==> q divides (&2 * z)`)) THEN
    ASM_SIMP_TAC[INT_OF_NUM_POW; GSYM num_congruent; CONG_EXP_1] THEN
    REWRITE_TAC[INT_OF_NUM_MUL; MULT_CLAUSES; GSYM num_divides] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    REWRITE_TAC[ARITH_RULE `q <= 2 \/ 2 = 0 <=> q = 0 \/ q = 1 \/ q = 2`] THEN
    ASM_MESON_TAC[NUM_REDUCE_CONV `~ODD 0 /\ ~ODD 2`;
                  ODD_MULT; MULT_CLAUSES]] THEN
  MP_TAC(SPECL [`a:num`; `p:num`] JACOBI_EULER) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[ODD_MULT; NUM_REDUCE_CONV `ODD 2`]; ALL_TAC] THEN
  SUBGOAL_THEN `jacobi(a,p) = jacobi(b,p)` SUBST1_TAC THENL
   [ASM_MESON_TAC[JACOBI_CONG]; ASM_SIMP_TAC[JACOBI_PRIME]] THEN
  COND_CASES_TAC THENL
   [MP_TAC(SPECL [`p:num`; `b:num`] DIVIDES_LE) THEN
    ASM_REWRITE_TAC[GSYM NOT_LT] THEN ASM_MESON_TAC[COPRIME_0; PRIME_1];
    DISCH_THEN(MP_TAC o SPEC `m:num` o MATCH_MP INT_CONG_POW)] THEN
  REWRITE_TAC[INT_POW_POW] THEN
  SUBGOAL_THEN `(p - 1) DIV 2 * m = (n - 1) DIV 2` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `(p - 1) * m = n - 1`)) THEN
    SUBGOAL_THEN `ODD p` MP_TAC THENL [ASM_MESON_TAC[ODD_MULT]; ALL_TAC] THEN
    REWRITE_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `r:num` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SUC_SUB1; GSYM MULT_ASSOC] THEN
    REWRITE_TAC[ARITH_RULE `(2 * r) DIV 2 = r`];
    REWRITE_TAC[TAUT `p ==> ~q <=> ~(p /\ q)`]] THEN
  ASM_REWRITE_TAC[INT_POW_NEG; INT_POW_ONE; GSYM NOT_ODD] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
   `(--z:int == a) (mod p) /\ (a == z) (mod (p * q))
    ==> p divides &2 * z`)) THEN
  REWRITE_TAC[INT_OF_NUM_MUL; MULT_CLAUSES; GSYM num_divides] THEN
  ASM_MESON_TAC[DIVIDES_PRIME_PRIME; ODD_MULT;
                NUM_REDUCE_CONV `ODD 2`; PRIME_2]);;

let WEAK_EULER_PSEUDOPRIME_BOUND_PHI_ALT = prove
 (`!n. ~prime n /\
       ~(squarefree n /\
         !p. prime p /\ p divides n ==> p - 1 divides (n - 1) DIV 2)
        ==> 2 * CARD {a | a < n /\ weak_euler_pseudoprime a n} <= phi n`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[LT; EMPTY_GSPEC; CARD_CLAUSES; MULT_CLAUSES; LE_0] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `n:num` ABSOLUTE_WEAK_EULER_PSEUDOPRIME) THEN
  ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC CARD_SUBSET_HALF_LEMMA THEN
  EXISTS_TAC `\a. (a * b) MOD n` THEN
  EXISTS_TAC `{a:num | coprime(a,n) /\ a < n}` THEN
  SIMP_TAC[PHI_ALT; LE_REFL; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i < n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ASM_MESON_TAC[WEAK_EULER_PSEUDOPRIME_IMP_COPRIME; LT];
    ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `n:num` THEN
    ASM_MESON_TAC[CONG_MULT_RCANCEL]] THEN
  X_GEN_TAC `a:num` THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[LT] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WEAK_EULER_PSEUDOPRIME_IMP_COPRIME) THEN
  ASM_REWRITE_TAC[COPRIME_LMOD; COPRIME_LMUL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[MOD_LT_EQ; weak_euler_pseudoprime] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; INT_POW_REM; GSYM INT_REM_EQ] THEN
  REWRITE_TAC[INT_REM_EQ; GSYM INT_OF_NUM_MUL; INT_POW_MUL] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [weak_euler_pseudoprime]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
   [weak_euler_pseudoprime]) THEN
  ASM_CASES_TAC `ODD n` THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC (map INTEGER_RULE
   [`(a * b:int == &1) (mod n)
     ==> (a == &1) (mod n) ==> (b == &1) (mod n)`;
    `(a * b:int == &1) (mod n)
     ==> (a == -- &1) (mod n) ==> (b == -- &1) (mod n)`;
    `(a * b:int == -- &1) (mod n)
     ==> (a == &1) (mod n) ==> (b == -- &1) (mod n)`;
    `(a * b:int == -- &1) (mod n)
     ==> (a == -- &1) (mod n) ==> (b == &1) (mod n)`]));;

let WEAK_EULER_PSEUDOPRIME_BOUND_PHI = prove
 (`!n. ~prime n /\
       ~(squarefree n /\
         !p. prime p /\ p divides n ==> p - 1 divides (n - 1) DIV 2)
        ==> CARD {a | a < n /\ weak_euler_pseudoprime a n} <= phi n DIV 2`,
  REWRITE_TAC[ARITH_RULE `a <= b DIV 2 <=> 2 * a <= b`] THEN
  REWRITE_TAC[WEAK_EULER_PSEUDOPRIME_BOUND_PHI_ALT]);;

let WEAK_EULER_PSEUDOPRIME_BOUND_LT = prove
 (`!n. ~(n = 0) /\ ~(n = 1) /\ ~prime n /\
       ~(squarefree n /\
         !p. prime p /\ p divides n ==> p - 1 divides (n - 1) DIV 2)
       ==> CARD {a | a < n /\ weak_euler_pseudoprime a n} < n DIV 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `n:num` WEAK_EULER_PSEUDOPRIME_BOUND_PHI_ALT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `p < n - 1  ==> 2 * a <= p ==> a < n DIV 2`) THEN
  MATCH_MP_TAC PHI_LIMIT_COMPOSITE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Euler (-Jacobi) pseudoprimes, as used in the Solovay-Strassen test.       *)
(* ------------------------------------------------------------------------- *)

let euler_jacobi_pseudoprime = new_definition
 `euler_jacobi_pseudoprime a n <=>
        ODD n /\ coprime(a,n) /\
        (jacobi(a,n) == &a pow ((n - 1) DIV 2)) (mod &n)`;;

let EULER_JACOBI_PSEUDOPRIME_IMP_COPRIME = prove
 (`!a n. euler_jacobi_pseudoprime a n ==> coprime(a,n)`,
  SIMP_TAC[euler_jacobi_pseudoprime]);;

let EULER_JACOBI_PSEUDOPRIME_IMP_ODD = prove
 (`!a n. euler_jacobi_pseudoprime a n ==> ODD n`,
  SIMP_TAC[euler_jacobi_pseudoprime]);;

let EULER_JACOBI_IMP_WEAK_EULER_PSEUDOPRIME = prove
 (`!a n. euler_jacobi_pseudoprime a n ==> weak_euler_pseudoprime a n`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[weak_euler_pseudoprime; euler_jacobi_pseudoprime] THEN
  MP_TAC(SPECL [`a:num`; `n:num`] JACOBI_CASES) THEN
  REWRITE_TAC[JACOBI_EQ_0; COPRIME_SYM] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[INT_CONG_SYM]);;

let EULER_JACOBI_IMP_FERMAT_PSEUDOPRIME = prove
 (`!a n. euler_jacobi_pseudoprime a n ==> fermat_pseudoprime a n`,
  MESON_TAC[EULER_JACOBI_IMP_WEAK_EULER_PSEUDOPRIME;
            WEAK_EULER_IMP_FERMAT_PSEUDOPRIME]);;

let PRIME_IMP_EULER_JACOBI_PSEUDOPRIME = prove
 (`!p a. prime p /\ ~(p = 2) /\ ~(p divides a)
         ==> euler_jacobi_pseudoprime a p`,
  SIMP_TAC[euler_jacobi_pseudoprime; JACOBI_EULER] THEN
  ASM_MESON_TAC[PRIME_COPRIME_EQ; COPRIME_SYM; PRIME_ODD]);;

let PRIME_EQ_EULER_JACOBI_PSEUDOPRIME = prove
 (`!p. prime p <=>
       p = 2 \/ 2 <= p /\
       (!a. 0 < a /\ a < p ==> euler_jacobi_pseudoprime a p)`,
  GEN_TAC THEN ASM_CASES_TAC `p = 2` THEN ASM_REWRITE_TAC[PRIME_2] THEN
  EQ_TAC THENL
   [SIMP_TAC[PRIME_GE_2] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC PRIME_IMP_EULER_JACOBI_PSEUDOPRIME THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE_STRONG) THEN ASM_ARITH_TAC;
    MESON_TAC[EULER_JACOBI_IMP_FERMAT_PSEUDOPRIME;
              PRIME_EQ_FERMAT_PSEUDOPRIME]]);;

let ABSOLUTE_EULER_JACOBI_PSEUDOPRIME = prove
 (`!n. (!a. coprime(a,n) ==> euler_jacobi_pseudoprime a n) <=>
       n = 1 \/ ODD n /\ prime n`,
  GEN_TAC THEN ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[euler_jacobi_pseudoprime; JACOBI_1] THEN
    REWRITE_TAC[INT_CONG_MOD_1; COPRIME_1; ARITH];
    ALL_TAC] THEN
  ASM_CASES_TAC `prime n` THEN ASM_REWRITE_TAC[] THENL
   [EQ_TAC THENL
     [MESON_TAC[EULER_JACOBI_PSEUDOPRIME_IMP_ODD; COPRIME_1];
      DISCH_TAC THEN REPEAT STRIP_TAC] THEN
    MATCH_MP_TAC PRIME_IMP_EULER_JACOBI_PSEUDOPRIME THEN
    ASM_MESON_TAC[NUM_REDUCE_CONV `ODD 2`; PRIME_COPRIME_EQ; COPRIME_SYM];
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP]] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[euler_jacobi_pseudoprime; ARITH] THEN
    MESON_TAC[COPRIME_1];
    ALL_TAC] THEN
  ASM_CASES_TAC `carmichael_number n` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [carmichael_number]) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 <= n <=> ~(n = 0) /\ ~(n = 1)`] THEN
    MESON_TAC[EULER_JACOBI_IMP_FERMAT_PSEUDOPRIME]] THEN
  MP_TAC(SPEC `n:num` PRIME_FACTOR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` (MP_TAC o SYM)) THEN
  ASM_CASES_TAC `q = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  ASM_CASES_TAC `q = 1` THENL [ASM_MESON_TAC[MULT_CLAUSES]; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CARMICHAEL_NUMBER_IMP_SQUAREFREE) THEN
  REWRITE_TAC[SQUAREFREE_COPRIME] THEN
  DISCH_THEN(MP_TAC o SPECL [`p:num`; `q:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(snd(EQ_IMP_RULE(SPEC `p:num` QUADRATIC_NONRESIDUE_EXISTS))) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ODD_PRIME; PRIME_ODD; CARMICHAEL_NUMBER_IMP_ODD;
                  ODD_MULT; NUM_ODD_CONV `ODD 2`];
    DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`p:num`; `q:num`; `a:num`; `1`]
        CHINESE_REMAINDER_USUAL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:num` THEN
  STRIP_TAC THEN EXPAND_TAC "n" THEN REWRITE_TAC[COPRIME_RMUL] THEN
  ASM_SIMP_TAC[NUMBER_RULE `(t == 1) (mod q) ==> coprime(t,q)`] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONG_COPRIME; COPRIME_SYM]; ALL_TAC] THEN
  REWRITE_TAC[euler_jacobi_pseudoprime] THEN
  DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[JACOBI_RMUL] THEN
  SUBGOAL_THEN `jacobi(t,q) = &1` SUBST1_TAC THENL
   [ASM_MESON_TAC[JACOBI_CONG; JACOBI_1]; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL; INT_MUL_RID] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
   `(x:int == y) (mod (p * q)) ==> (x == y) (mod q)`)) THEN
  ASM_SIMP_TAC[JACOBI_PRIME] THEN MP_TAC(NUMBER_RULE
   `coprime(p:num,a) /\ (t == a) (mod p) /\ p divides t ==> p = 1`) THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[PRIME_1]; DISCH_THEN(K ALL_TAC)] THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[CONG_TRANS; CONG_SYM]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
   `(--a == y) (mod q) ==> (y == a) (mod q) ==> q divides (a - --a)`)) THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM num_congruent; GSYM num_divides; INT_OF_NUM_POW] THEN
  ASM_SIMP_TAC[CONG_EXP_1] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE_STRONG) THEN
  REWRITE_TAC[ARITH_RULE `1 <= q /\ q <= 2 <=> q = 1 \/ q = 2`; ARITH_EQ] THEN
  ASM_MESON_TAC[CARMICHAEL_NUMBER_IMP_ODD; NOT_ODD;
                  ODD_MULT; NUM_ODD_CONV `ODD 2`]);;

let EULER_JACOBI_PSEUDOPRIME_BOUND_PHI_ALT = prove
 (`!n. ~(n = 1) /\ ~prime n
        ==> 2 * CARD {a | a < n /\ euler_jacobi_pseudoprime a n} <= phi n`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[LT; EMPTY_GSPEC; CARD_CLAUSES; MULT_CLAUSES; LE_0] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `n:num` ABSOLUTE_EULER_JACOBI_PSEUDOPRIME) THEN
  ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC CARD_SUBSET_HALF_LEMMA THEN
  EXISTS_TAC `\a. (a * b) MOD n` THEN
  EXISTS_TAC `{a:num | coprime(a,n) /\ a < n}` THEN
  SIMP_TAC[PHI_ALT; LE_REFL; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i < n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ASM_MESON_TAC[EULER_JACOBI_PSEUDOPRIME_IMP_COPRIME; LT];
    ALL_TAC;
    REWRITE_TAC[GSYM CONG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `n:num` THEN
    ASM_MESON_TAC[CONG_MULT_RCANCEL]] THEN
  X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EULER_JACOBI_PSEUDOPRIME_IMP_COPRIME) THEN
  ASM_REWRITE_TAC[euler_jacobi_pseudoprime; COPRIME_LMOD; COPRIME_LMUL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[MOD_LT_EQ] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[JACOBI_MOD; GSYM INT_OF_NUM_REM; JACOBI_LMUL] THEN
  REWRITE_TAC[GSYM INT_REM_EQ; INT_POW_REM] THEN
  REWRITE_TAC[INT_REM_EQ; GSYM INT_OF_NUM_MUL; INT_POW_MUL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
   `(x * y:int == a * b) (mod n)
    ==> (x == a) (mod n) /\ coprime(a,n) ==> (y == b) (mod n)`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[euler_jacobi_pseudoprime]) THEN
  ASM_REWRITE_TAC[INT_COPRIME_LPOW; GSYM num_coprime] THEN
  ASM_MESON_TAC[]);;

let EULER_JACOBI_PSEUDOPRIME_BOUND_PHI = prove
 (`!n. ~(n = 1) /\ ~prime n
        ==> CARD {a | a < n /\ euler_jacobi_pseudoprime a n} <= phi n DIV 2`,
  REWRITE_TAC[ARITH_RULE `a <= b DIV 2 <=> 2 * a <= b`] THEN
  REWRITE_TAC[EULER_JACOBI_PSEUDOPRIME_BOUND_PHI_ALT]);;

let EULER_JACOBI_PSEUDOPRIME_BOUND_LT = prove
 (`!n. ~(n = 0) /\ ~(n = 1) /\ ~prime n
        ==> CARD {a | a < n /\ euler_jacobi_pseudoprime a n} < n DIV 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `n:num` EULER_JACOBI_PSEUDOPRIME_BOUND_PHI_ALT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `p < n - 1  ==> 2 * a <= p ==> a < n DIV 2`) THEN
  MATCH_MP_TAC PHI_LIMIT_COMPOSITE THEN ASM_REWRITE_TAC[]);;

let MILLER_RABIN_IMP_EULER_JACOBI_PSEUDOPRIME = prove
 (`!a q. miller_rabin_pseudoprime a q /\ ~(q = 2)
         ==> euler_jacobi_pseudoprime a q`,
  let lemma0 = prove
   (`!x m n (k:A->bool).
          n divides m EXP 2 /\ FINITE k
          ==> (nproduct k (\i. m * x i + 1) == m * nsum k x + 1) (mod n)`,
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC[NPRODUCT_CLAUSES; NSUM_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
    REWRITE_TAC[CONG_REFL] THEN MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) THEN
    POP_ASSUM MP_TAC THEN CONV_TAC NUMBER_RULE) in
  let lemma1 = prove
   (`!x k m n (s:A->bool).
          n divides m EXP 2 /\ FINITE s
          ==> (nproduct s (\i. (m * x i + 1) EXP k i) ==
               m * nsum s (\i. k i * x i) + 1) (mod n)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_TRANS THEN
    EXISTS_TAC `nproduct s (\i:A. m * k i * x i + 1)` THEN
    ASM_SIMP_TAC[lemma0] THEN MATCH_MP_TAC CONG_NPRODUCT THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[MESON[CARD_NUMSEG_1] `a EXP k = a EXP CARD(1..k)`] THEN
    SIMP_TAC[GSYM NPRODUCT_CONST; FINITE_NUMSEG] THEN
    W(MP_TAC o PART_MATCH (lhand o rator o rand) lemma0 o
      lhand o rator o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; NSUM_CONST; CARD_NUMSEG_1]) in
  MAP_EVERY X_GEN_TAC [`a:num`; `n:num`] THEN
  ASM_CASES_TAC `n = 2` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `coprime(a:num,n)` THENL
   [ALL_TAC; ASM_MESON_TAC[MILLER_RABIN_PSEUDOPRIME_IMP_COPRIME]] THEN
  REWRITE_TAC[miller_rabin_pseudoprime; euler_jacobi_pseudoprime] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ODD] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[INT_CONG_MOD_1; ARITH] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW] THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LE_1] THEN
  REWRITE_TAC[INTEGER_RULE
   `(x:int == n - z) (mod n) <=> (x == --z) (mod n)`] THEN
  MP_TAC(SPECL [`n - 1`; `2`] INDEX_DECOMPOSITION) THEN
  ASM_REWRITE_TAC[ARITH_EQ; ARITH_RULE `n - 1 = 0 <=> n = 0 \/ n = 1`] THEN
  ABBREV_TAC `e = index 2 (n - 1)` THEN
  REWRITE_TAC[DIVIDES_2; NOT_EVEN; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBST1_TAC(SYM(ASSUME `2 EXP e * m = n - 1`)) THEN
  SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ] THEN
  SUBGOAL_THEN `~(e = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[INDEX_EQ_0] THEN
    ASM_REWRITE_TAC[NOT_EVEN; DIVIDES_2; ODD_SUB] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(2 EXP e * m) DIV 2 = 2 EXP (e - 1) * m` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[ARITH_RULE `(ee * m) * 2 + 0 = (2 * ee) * m`] THEN
    REWRITE_TAC[ARITH] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM INT_POW_POW] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `(a:int == &1) (mod n) /\ j = &1 ==> (j == a) (mod n)`) THEN
    ASM_SIMP_TAC[INT_CONG_POW_1] THEN
    FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
        [SYM(MATCH_MP PRIME_FACTORIZATION th)]) THEN
    ASM_SIMP_TAC[JACOBI_NPRODUCT_RIGHT; FINITE_SPECIAL_DIVISORS] THEN
    MATCH_MP_TAC IPRODUCT_EQ_1 THEN X_GEN_TAC `p:num` THEN
    REWRITE_TAC[IN_ELIM_THM; JACOBI_REXP] THEN STRIP_TAC THEN
    MATCH_MP_TAC(MESON[INT_POW_ONE] `x:int = &1 ==> x pow n = &1`) THEN
    MATCH_MP_TAC JACOBI_EQ_1 THEN ASM_SIMP_TAC[EULER_CRITERION] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[NUMBER_RULE
       `coprime(a:num,n) /\ p divides n ==> coprime(a,p)`];
      DISCH_TAC THEN DISJ2_TAC] THEN
    REWRITE_TAC[ORDER_DIVIDES] THEN MATCH_MP_TAC DIVIDES_DIVIDES_DIV_IMP THEN
    MATCH_MP_TAC DIVIDES_MUL THEN
    ASM_REWRITE_TAC[COPRIME_2; DIVIDES_2; EVEN_SUB; ARITH] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[NOT_EVEN; divides; EVEN_MULT]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM PHI_PRIME] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[ORDER_DIVIDES_PHI; COPRIME_SYM]; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[divides; ODD_MULT]
     `!n. ODD n /\ m divides n ==> ODD m`) THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[GSYM ORDER_DIVIDES] THEN
    REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INTEGER_RULE
     `(x:int == y) (mod n) ==> p divides n ==> (x == y) (mod p)`)) THEN
    ASM_REWRITE_TAC[GSYM num_divides];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!p. prime p /\ p divides n
        ==> ?d. jacobi(a,p) = --(&1) pow d /\ 2 EXP (r + 1) * d + 1 = p`
  MP_TAC THENL
   [X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `p:num` o MATCH_MP (NUMBER_RULE
     `coprime(a:num,n) ==> !p. p divides n ==> coprime(p,a)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `ODD p /\ ~(p = 2)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_ODD; ODD_PRIME; divides; ODD_MULT;
                    NUM_REDUCE_CONV `ODD 2`];
      ALL_TAC] THEN
    MP_TAC(SPECL [`order p a`; `2`] INDEX_DECOMPOSITION) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` MP_TAC) THEN
    ABBREV_TAC `j = index 2 (order p a)` THEN
    ASM_REWRITE_TAC[ORDER_EQ_0; ARITH_EQ; DIVIDES_2; NOT_EVEN] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `j = r + 1` SUBST_ALL_TAC THENL
     [SUBGOAL_THEN
       `2 EXP j * i divides 2 EXP (r + 1) * m /\
        ~(2 EXP j * i divides 2 EXP r * m)`
      MP_TAC THENL
       [ASM_REWRITE_TAC[GSYM ORDER_DIVIDES] THEN
        REWRITE_TAC[EXP_ADD; EXP_1] THEN
        REWRITE_TAC[ARITH_RULE `(a * 2) * b = a * b + a * b`] THEN
        REWRITE_TAC[EXP_ADD; GSYM EXP_2] THEN
        REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `&p:int` o MATCH_MP (INTEGER_RULE
         `(x:int == y) (mod n) ==> !p. p divides n ==> (x == y) (mod p)`)) THEN
        ASM_SIMP_TAC[GSYM num_divides; INTEGER_RULE
         `(a:int == -- &1) (mod n) ==> (a pow 2 == &1) (mod n)`] THEN
        REWRITE_TAC[TAUT `p ==> ~q <=> ~(p /\ q)`] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
         `(x:int == -- &1) (mod p) /\ (x == &1) (mod p)
          ==> p divides &2`)) THEN
        ASM_SIMP_TAC[GSYM num_divides; DIVIDES_PRIME_PRIME; PRIME_2];
        REWRITE_TAC[IMP_CONJ] THEN DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
          `e1 * m divides e2 * n
           ==> coprime(e1:num,n) /\ coprime(e2,m)
                ==> e1 divides e2 /\ m divides n`)) THEN
        ASM_REWRITE_TAC[COPRIME_LEXP; COPRIME_2] THEN
        ASM_SIMP_TAC[DIVIDES_EXP_LE; LE_REFL] THEN
        REWRITE_TAC[ARITH_RULE `j <= r + 1 <=> j = r + 1 \/ j <= r`] THEN
        ASM_CASES_TAC `j = r + 1` THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
        MATCH_MP_TAC DIVIDES_MUL2 THEN ASM_SIMP_TAC[DIVIDES_EXP_LE; LE_REFL]];
      MP_TAC(SPECL [`a:num`; `p:num`] ORDER_DIVIDES_PHI) THEN
      ASM_SIMP_TAC[PHI_PRIME; divides; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `q:num` THEN DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `p - 1 = d ==> ~(p = 0) ==> d + 1 = p`)) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[PRIME_0]; DISCH_TAC] THEN
      EXISTS_TAC `i * q:num` THEN ASM_REWRITE_TAC[MULT_ASSOC] THEN
      MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `&p:int` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(INT_ARITH
         `&3 <= p /\ abs(x) <= &1 /\ abs(y) <= &1 ==> abs(x - y:int) < p`) THEN
        REWRITE_TAC[JACOBI_BOUND; INT_ABS_POW; INT_ABS_NEG] THEN
        REWRITE_TAC[INT_ABS_NUM; INT_POW_ONE; INT_LE_REFL] THEN
        ASM_MESON_TAC[INT_OF_NUM_LE; ODD_PRIME; divides; ODD_MULT];
        ALL_TAC] THEN
      MATCH_MP_TAC INT_CONG_TRANS THEN
      EXISTS_TAC `(&a:int) pow ((p - 1) DIV 2)` THEN
      ASM_SIMP_TAC[JACOBI_EULER] THEN
      SUBGOAL_THEN `(-- &1:int) pow (i * q) = -- &1 pow q`
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC[INT_POW_NEG; INT_POW_ONE; GSYM NOT_ODD] THEN
        ASM_REWRITE_TAC[ODD_MULT];
        ALL_TAC] THEN
      SUBGOAL_THEN `(p - 1) DIV 2 = order p a DIV 2 * q` SUBST1_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
         `a + 1 = p ==> p - 1 = a`)) THEN
        SUBST1_TAC(SYM(ASSUME `2 EXP (r + 1) * i = order p a`)) THEN
        REWRITE_TAC[GSYM ADD1; EXP; GSYM MULT_ASSOC] THEN
        SIMP_TAC[DIV_MULT; ARITH_EQ] THEN REWRITE_TAC[MULT_AC];
        REWRITE_TAC[GSYM INT_POW_POW]] THEN
      MATCH_MP_TAC INT_CONG_POW THEN REWRITE_TAC[INTEGER_RULE
       `(a:int == -- &1) (mod p) <=> p divides (a + &1)`] THEN
      MP_TAC(SPECL [`p:num`; `1`; `a EXP (order p a DIV 2)`]
       CONG_SQUARE_1_PRIME_POWER) THEN
      ASM_REWRITE_TAC[EXP_1; INT_OF_NUM_ADD; INT_OF_NUM_POW] THEN
      REWRITE_TAC[CONG_MINUS1; EXP_EXP; GSYM num_divides] THEN
      REWRITE_TAC[ORDER_DIVIDES] THEN MATCH_MP_TAC(TAUT
       `~r /\ ~q /\ p ==> (p <=> q \/ r \/ s) ==> s`) THEN
      CONJ_TAC THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
      SUBST1_TAC(SYM(ASSUME `2 EXP (r + 1) * i = order p a`)) THEN
      REWRITE_TAC[GSYM ADD1; EXP; GSYM MULT_ASSOC] THEN
      SIMP_TAC[DIV_MULT; ARITH_EQ] THEN CONJ_TAC THENL
       [ALL_TAC; REWRITE_TAC[MULT_AC; DIVIDES_REFL]] THEN
      DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
      REWRITE_TAC[ARITH_RULE `2 * n <= n <=> n = 0`] THEN
      REWRITE_TAC[EXP_EQ_0; MULT_EQ_0; ARITH_EQ] THEN ASM_MESON_TAC[ODD]];
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `d:num->num` THEN
  REWRITE_TAC[TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(nsum {p | prime p /\ p divides n} (\p. index p n * d p) ==
     2 EXP (e - r - 1) * m) (mod 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(NUMBER_RULE
     `!a. (a * x == a * y) (mod (a * n)) /\ ~(a = 0)
          ==> (x == y) (mod n)`) THEN
    EXISTS_TAC `2 EXP (r + 1)` THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ; MULT_ASSOC; GSYM EXP_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `r < e ==> (r + 1) + e - r - 1 = e`] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `(x + 1 == y + 1) (mod n) ==> (y == x) (mod n)`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - 1 + 1 = n`] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] (GSYM(CONJUNCT2 EXP))] THEN
    REWRITE_TAC[ARITH_RULE `SUC(r + 1) = r + 2`] THEN
    MP_TAC(ISPECL
     [`d:num->num`; `\p. index p n`; `2 EXP (r + 1)`; `2 EXP (r + 2)`;
      `{p | prime p /\ p divides n}`] lemma1) THEN
    SIMP_TAC[EXP_EXP; DIVIDES_EXP_LE; LE_REFL] THEN
    REWRITE_TAC[ARITH_RULE `r + 2 <= (r + 1) * 2`] THEN
    ASM_SIMP_TAC[FINITE_SPECIAL_DIVISORS; PRIME_FACTORIZATION];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o RAND_CONV o RAND_CONV)
      [SYM(MATCH_MP PRIME_FACTORIZATION th)]) THEN
  ASM_SIMP_TAC[JACOBI_NPRODUCT_RIGHT; FINITE_SPECIAL_DIVISORS] THEN
  ASM_SIMP_TAC[JACOBI_REXP] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] INT_POW_POW] THEN
  ASM_SIMP_TAC[GSYM INT_POW_NSUM; FINITE_SPECIAL_DIVISORS] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONG_DIVIDES) THEN REWRITE_TAC[DIVIDES_2] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP (METIS[INT_POW_NEG; INT_POW_ONE]
  `(EVEN m <=> EVEN n) ==> (--(&1:int) pow m = --(&1) pow n)`)) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `r < e ==> e - 1 = r + (e - r - 1)`)) THEN
  REWRITE_TAC[EXP_ADD; ARITH_RULE `(a * b) * m:num = b * a * m`] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ONCE_REWRITE_TAC[GSYM INT_POW_POW] THEN
  MATCH_MP_TAC INT_CONG_POW THEN ONCE_REWRITE_TAC[INT_CONG_SYM] THEN
  ASM_REWRITE_TAC[INT_POW_NEG; INT_POW_ONE; GSYM NOT_ODD]);;

let MILLER_RABIN_EQ_EULER_JACOBI_PSEUDOPRIME = prove
 (`!a n. ~(n = 2) /\ (?p k. prime p /\ ODD p /\ p EXP k = n) \/
         (n == 3) (mod 4)
         ==> (miller_rabin_pseudoprime a n <=> euler_jacobi_pseudoprime a n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 2` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN
  MP_TAC(SPECL [`a:num`; `n:num`] MILLER_RABIN_EQ_WEAK_EULER_PSEUDOPRIME) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
   `(q ==> r) /\ (p ==> q)
    ==> (p <=> r) ==> (p <=> q)`) THEN
  REWRITE_TAC[EULER_JACOBI_IMP_WEAK_EULER_PSEUDOPRIME] THEN
  ASM_SIMP_TAC[ MILLER_RABIN_IMP_EULER_JACOBI_PSEUDOPRIME]);;
