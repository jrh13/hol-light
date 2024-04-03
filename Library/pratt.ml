(* ========================================================================= *)
(* HOL primality proving procedure, based on Pratt certificates.             *)
(* ========================================================================= *)

needs "Library/prime.ml";;

prioritize_num();;

let num_0 = Num.num_of_int 0;;
let num_1 = Num.num_of_int 1;;
let num_2 = Num.num_of_int 2;;

(* ------------------------------------------------------------------------- *)
(* Mostly for compatibility. Should eliminate this eventually.               *)
(* ------------------------------------------------------------------------- *)

let nat_mod_lemma = prove
 (`!x y n:num. (x == y) (mod n) /\ y <= x ==> ?q. x = y + n * q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[num_congruent] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ONCE_REWRITE_TAC
   [INTEGER_RULE `(x == y) (mod &n) <=> &n divides (x - y)`] THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB;
               ARITH_RULE `x <= y ==> (y:num = x + d <=> y - x = d)`] THEN
  REWRITE_TAC[GSYM num_divides; divides]);;

let nat_mod = prove
 (`!x y n:num. (mod n) x y <=> ?q1 q2. x + n * q1 = y + n * q2`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM cong] THEN
  EQ_TAC THENL [ALL_TAC; NUMBER_TAC] THEN
  MP_TAC(SPECL [`x:num`; `y:num`] LE_CASES) THEN
  REWRITE_TAC[TAUT `a \/ b ==> c ==> d <=> (c /\ b) \/ (c /\ a) ==> d`] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[NUMBER_RULE
      `(x:num == y) (mod n) <=> (y == x) (mod n)`]] THEN
  MESON_TAC[nat_mod_lemma; ARITH_RULE `x + y * 0 = x`]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas about previously defined terms.                                    *)
(* ------------------------------------------------------------------------- *)

let PRIME = prove
 (`!p. prime p <=>
       ~(p = 0) /\ ~(p = 1) /\ !m. 0 < m /\ m < p ==> coprime(p,m)`,
  GEN_TAC THEN ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[PRIME_0] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[PRIME_1] THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP PRIME_COPRIME) THEN
    DISCH_TAC THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[COPRIME_1] THEN
    ASM_MESON_TAC[NOT_LT; LT_REFL; DIVIDES_LE]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `q:num` MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN
  SUBGOAL_THEN `~(coprime(p,q))` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[coprime; NOT_FORALL_THM] THEN
    EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[DIVIDES_REFL] THEN
    ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_REWRITE_TAC[LT_LE; LE_0] THEN
  ASM_CASES_TAC `p:num = q` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[] THEN DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_MESON_TAC[DIVIDES_ZERO]);;

let FINITE_NUMBER_SEGMENT = prove
 (`!n. { m | 0 < m /\ m < n } HAS_SIZE (n - 1)`,
  INDUCT_TAC THENL
   [SUBGOAL_THEN `{m | 0 < m /\ m < 0} = EMPTY` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; LT]; ALL_TAC] THEN
    REWRITE_TAC[HAS_SIZE; FINITE_RULES; CARD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ASM_CASES_TAC `n = 0` THENL
     [SUBGOAL_THEN `{m | 0 < m /\ m < SUC n} = EMPTY` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
        ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[HAS_SIZE_0];
      SUBGOAL_THEN `{m | 0 < m /\ m < SUC n} = n INSERT {m | 0 < m /\ m < n}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN
        UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `~(n = 0)` THEN
      POP_ASSUM MP_TAC THEN
      SIMP_TAC[FINITE_RULES; HAS_SIZE; CARD_CLAUSES] THEN
      DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM; LT_REFL] THEN
      ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Congruences.                                                              *)
(* ------------------------------------------------------------------------- *)

let CONG_MOD_0 = prove
 (`!x y. (x == y) (mod 0) <=> (x = y)`,
  NUMBER_TAC);;

let CONG_MOD_1 = prove
 (`!x y. (x == y) (mod 1)`,
  NUMBER_TAC);;

let CONG_0 = prove
 (`!x n. ((x == 0) (mod n) <=> n divides x)`,
  NUMBER_TAC);;

let CONG_SUB_CASES = prove
 (`!x y n. (x == y) (mod n) <=>
           if x <= y then (y - x == 0) (mod n)
           else (x - y == 0) (mod n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cong; nat_mod] THEN
  COND_CASES_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM]; ALL_TAC] THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let CONG_MULT_LCANCEL = prove
 (`!a n x y. coprime(a,n) /\ (a * x == a * y) (mod n) ==> (x == y) (mod n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = 0` THENL
   [ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[COPRIME_0] THEN
    SIMP_TAC[CONG_MOD_1]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[CONG_SUB_CASES] THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
  REWRITE_TAC[GSYM LEFT_SUB_DISTRIB; CONG_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[COPRIME_DIVPROD; COPRIME_SYM]);;

let CONG_REFL = prove
 (`!x n. (x == x) (mod n)`,
  MESON_TAC[cong; nat_mod; ADD_CLAUSES; MULT_CLAUSES]);;

let CONG_SYM = prove
 (`!x y n. (x == y) (mod n) <=> (y == x) (mod n)`,
  REWRITE_TAC[cong; nat_mod] THEN MESON_TAC[]);;

let CONG_TRANS = prove
 (`!x y z n. (x == y) (mod n) /\ (y == z) (mod n) ==> (x == z) (mod n)`,
  REWRITE_TAC[cong; nat_mod] THEN
  MESON_TAC[ARITH_RULE
   `(x + n * q1 = y + n * q2) /\
    (y + n * q3 = z + n * q4)
    ==> (x + n * (q1 + q3) = z + n * (q2 + q4))`]);;

(* ------------------------------------------------------------------------- *)
(* Euler totient function.                                                   *)
(* ------------------------------------------------------------------------- *)

let phi = new_definition
  `phi(n) = CARD { m | 0 < m /\ m <= n /\ coprime(m,n) }`;;

let PHI_ALT = prove
 (`phi(n) = CARD { m | coprime(m,n) /\ m < n}`,
  REWRITE_TAC[phi] THEN
  ASM_CASES_TAC `n = 0` THENL
   [AP_TERM_TAC THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    MESON_TAC[LT; NOT_LT];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [SUBGOAL_THEN
     `({m | 0 < m /\ m <= n /\ coprime (m,n)} = {1}) /\
      ({m | coprime (m,n) /\ m < n} = {0})`
     (CONJUNCTS_THEN SUBST1_TAC)
    THENL [ALL_TAC; SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY]] THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
    REWRITE_TAC[COPRIME_1] THEN REPEAT STRIP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  AP_TERM_TAC THEN ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `m:num` THEN ASM_CASES_TAC `m = 0` THEN
  ASM_REWRITE_TAC[LT] THENL
   [ASM_MESON_TAC[COPRIME_0; COPRIME_SYM];
    ASM_MESON_TAC[LE_LT; COPRIME_REFL; LT_NZ]]);;

let PHI_ANOTHER = prove
 (`!n. ~(n = 1) ==> (phi(n) = CARD {m | 0 < m /\ m < n /\ coprime(m,n)})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[phi] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[LE_LT; COPRIME_REFL; COPRIME_1; LT_NZ]);;

let PHI_LIMIT = prove
 (`!n. phi(n) <= n`,
  GEN_TAC THEN REWRITE_TAC[PHI_ALT] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM]);;

let PHI_LIMIT_STRONG = prove
 (`!n. ~(n = 1) ==> phi(n) <= n - 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `n:num` FINITE_NUMBER_SEGMENT) THEN
  ASM_SIMP_TAC[PHI_ANOTHER; HAS_SIZE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM]);;

let PHI_0 = prove
 (`phi 0 = 0`,
  MP_TAC(SPEC `0` PHI_LIMIT) THEN REWRITE_TAC[ARITH] THEN ARITH_TAC);;

let PHI_1 = prove
 (`phi 1 = 1`,
  REWRITE_TAC[PHI_ALT; COPRIME_1; CARD_NUMSEG_LT]);;

let PHI_LOWERBOUND_1_STRONG = prove
 (`!n. 1 <= n ==> 1 <= phi(n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 = CARD {1}` SUBST1_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; NOT_IN_EMPTY; FINITE_RULES; ARITH]; ALL_TAC] THEN
  REWRITE_TAC[phi] THEN MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [SIMP_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[COPRIME_SYM] COPRIME_1] THEN
    GEN_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{b | b <= n}` THEN
    REWRITE_TAC[CARD_NUMSEG_LE; FINITE_NUMSEG_LE] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM]]);;

let PHI_LOWERBOUND_1 = prove
 (`!n. 2 <= n ==> 1 <= phi(n)`,
  MESON_TAC[PHI_LOWERBOUND_1_STRONG; LE_TRANS; ARITH_RULE `1 <= 2`]);;

let PHI_LOWERBOUND_2 = prove
 (`!n. 3 <= n ==> 2 <= phi(n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 = CARD {1,(n-1)}` SUBST1_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; IN_INSERT; NOT_IN_EMPTY; FINITE_RULES; ARITH] THEN
    ASM_SIMP_TAC[ARITH_RULE `3 <= n ==> ~(1 = n - 1)`]; ALL_TAC] THEN
  REWRITE_TAC[phi] THEN MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [SIMP_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[COPRIME_1] THEN
    ASM_SIMP_TAC[ARITH;
               ARITH_RULE `3 <= n ==> 0 < n - 1 /\ n - 1 <= n /\ 1 <= n`] THEN
    REWRITE_TAC[coprime] THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    MP_TAC(SPEC `n:num` (CONJUNCT1 COPRIME_1)) THEN REWRITE_TAC[coprime] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `1 = n - (n - 1)` SUBST1_TAC THENL
     [UNDISCH_TAC `3 <= n` THEN ARITH_TAC;
      ASM_SIMP_TAC[DIVIDES_SUB]];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{b | b <= n}` THEN
    REWRITE_TAC[CARD_NUMSEG_LE; FINITE_NUMSEG_LE] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM]]);;

let PHI_PRIME_EQ = prove
 (`!n. (phi n = n - 1) /\ ~(n = 0) /\ ~(n = 1) <=> prime n`,
  GEN_TAC THEN REWRITE_TAC[PRIME] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[PHI_1; ARITH] THEN
  MP_TAC(SPEC `n:num` FINITE_NUMBER_SEGMENT) THEN
  ASM_SIMP_TAC[PHI_ANOTHER; HAS_SIZE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `{m | 0 < m /\ m < n /\ coprime (m,n)} = {m | 0 < m /\ m < n}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    REWRITE_TAC[COPRIME_SYM] THEN CONV_TAC TAUT] THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM]);;

let PHI_PRIME = prove
 (`!p. prime p ==> phi p = p - 1`,
  MESON_TAC[PHI_PRIME_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Fermat's Little theorem.                                                  *)
(* ------------------------------------------------------------------------- *)

let DIFFERENCE_POS_LEMMA = prove
 (`b <= a /\
   (?x1 x2. x1 * n + a = x2 * n + b)
   ==> ?x. a = x * n + b`,
  STRIP_TAC THEN EXISTS_TAC `x2 - x1` THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[RIGHT_SUB_DISTRIB] THEN ARITH_TAC);;

let ITSET_MODMULT = prove
 (`!n s. FINITE s /\ ~(n = 0) /\ ~(n = 1) /\ coprime(a,n)
       ==> (!b. b IN s ==> b < n)
           ==> (ITSET (\x y. (x * y) MOD n) (IMAGE (\b. (a * b) MOD n) s) 1 =
                (a EXP (CARD s) * ITSET (\x y. (x * y) MOD n) s 1) MOD n)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `coprime(a,n)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  MP_TAC(ISPECL [`\x y. (x * y) MOD n`; `1`] FINITE_RECURSION) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [ASM_SIMP_TAC[MOD_MULT_RMOD] THEN REWRITE_TAC[MULT_AC]; ALL_TAC] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[IMAGE_CLAUSES; CARD_CLAUSES; FINITE_IMAGE] THEN CONJ_TAC THENL
   [REWRITE_TAC[EXP; MULT_CLAUSES] THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
    MAP_EVERY UNDISCH_TAC [`~(n = 0)`; `~(n = 1)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `b:num` THEN X_GEN_TAC `s:num->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_INSERT] THEN
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  ASM_CASES_TAC `!b. b IN s ==> b < n` THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `b:num`) THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((a * b) MOD n IN IMAGE (\b. (a * b) MOD n) s)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    ASM_SIMP_TAC[GSYM CONG] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(b:num IN s)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `b:num = c` (fun th -> ASM_REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `b MOD n = c MOD n` MP_TAC THENL
     [ASM_SIMP_TAC[GSYM CONG] THEN
      MATCH_MP_TAC CONG_MULT_LCANCEL THEN
      EXISTS_TAC `a:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  REWRITE_TAC[EXP] THEN
  ASM_SIMP_TAC[MOD_MULT_LMOD; MOD_MULT_RMOD] THEN
  REWRITE_TAC[MULT_AC]);;

let ITSET_MODMULT_COPRIME = prove
 (`!n s. FINITE s /\ (!b. b IN s ==> coprime(b,n)) /\ ~(n = 0)
         ==> coprime(ITSET (\x y. (x * y) MOD n) s 1,n)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  MP_TAC(ISPECL [`\x y. (x * y) MOD n`; `1`] FINITE_RECURSION) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [ASM_SIMP_TAC[MOD_MULT_RMOD] THEN REWRITE_TAC[MULT_AC]; ALL_TAC] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[IMAGE_CLAUSES; CARD_CLAUSES; FINITE_IMAGE] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[COPRIME_SYM] COPRIME_1] THEN
  REWRITE_TAC[IN_INSERT] THEN
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `s:num->bool`] THEN
  ASM_CASES_TAC `!b. b IN s ==> coprime(b,n)` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
  ASM_SIMP_TAC[COPRIME_LMOD; ONCE_REWRITE_RULE[COPRIME_SYM] COPRIME_MUL]);;

let FERMAT_LITTLE = prove
 (`!a n. coprime(a,n) ==> (a EXP (phi n) == 1) (mod n)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[COPRIME_0; PHI_0; CONG_MOD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[CONG_MOD_1] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{ c | ?b. 0 < b /\ b < n /\ coprime(b,n) /\ (c = (a * b) MOD n) } =
    { b | 0 < b /\ b < n /\ coprime(b,n) }`
  MP_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `c:num` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `b:num` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[DIVISION] THEN
      MATCH_MP_TAC(TAUT `b /\ (~a ==> ~b) ==> a /\ b`) THEN
      SIMP_TAC[ARITH_RULE `~(0 < n) <=> (n = 0)`] THEN
      ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[COPRIME_0] THEN
      SUBGOAL_THEN `coprime(n,a * b)` MP_TAC THENL
       [MATCH_MP_TAC COPRIME_MUL THEN
        ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `a * b = (a * b) DIV n * n + (a * b) MOD n`
       (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
      THENL [ASM_SIMP_TAC[DIVISION]; ALL_TAC] THEN
      REWRITE_TAC[coprime] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[DIVIDES_ADD; DIVIDES_LMUL; DIVIDES_REFL]; ALL_TAC] THEN
    STRIP_TAC THEN MP_TAC(SPECL [`a:num`; `n:num`] BEZOUT) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num`
     (X_CHOOSE_THEN `x:num` (X_CHOOSE_THEN `y:num`
        (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)))) THEN
    SUBGOAL_THEN `d = 1` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[coprime]; ALL_TAC] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `(c * x) MOD n` THEN
      MATCH_MP_TAC(TAUT `(~a ==> ~c) /\ b /\ c /\ d ==> a /\ b /\ c /\ d`) THEN
      CONJ_TAC THENL
       [SIMP_TAC[ARITH_RULE `~(0 < n) <=> (n = 0)`] THEN
        ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[COPRIME_0];
        ALL_TAC] THEN
      ASM_SIMP_TAC[DIVISION] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `coprime(n,c * x)` MP_TAC THENL
         [MATCH_MP_TAC COPRIME_MUL THEN
          ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[coprime; GSYM DIVIDES_ONE] THEN
          FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
          SIMP_TAC[DIVIDES_SUB; DIVIDES_LMUL; DIVIDES_RMUL; DIVIDES_REFL];
          ALL_TAC] THEN
        SUBGOAL_THEN `c * x = (c * x) DIV n * n + (c * x) MOD n`
         (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
        THENL [ASM_SIMP_TAC[DIVISION]; ALL_TAC] THEN
        REWRITE_TAC[coprime] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC[DIVIDES_ADD; DIVIDES_LMUL; DIVIDES_REFL]; ALL_TAC] THEN
      ASM_SIMP_TAC[MOD_MULT_RMOD] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `c * y:num` THEN
      ASM_REWRITE_TAC[GSYM MULT_ASSOC] THEN
      ONCE_REWRITE_TAC[ARITH_RULE
       `(a * c * x = b:num) <=> (c * a * x = b)`] THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
       `(a - b = 1) ==> (a = b + 1)`)) THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; MULT_AC];

      EXISTS_TAC `(c * (n - y MOD n)) MOD n` THEN
      MATCH_MP_TAC(TAUT `(~a ==> ~c) /\ b /\ c /\ d ==> a /\ b /\ c /\ d`) THEN
      CONJ_TAC THENL
       [SIMP_TAC[ARITH_RULE `~(0 < n) <=> (n = 0)`] THEN
        ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[COPRIME_0];
        ALL_TAC] THEN
      ASM_SIMP_TAC[DIVISION] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `coprime(n,c * (n - y MOD n))` MP_TAC THENL
         [MATCH_MP_TAC COPRIME_MUL THEN
          ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[coprime; GSYM DIVIDES_ONE] THEN
          FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
          X_GEN_TAC `e:num` THEN STRIP_TAC THEN MATCH_MP_TAC DIVIDES_SUB THEN
          ASM_SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL] THEN
          MATCH_MP_TAC DIVIDES_LMUL THEN
          SUBGOAL_THEN `y = (y DIV n) * n + y MOD n` SUBST1_TAC THENL
           [ASM_SIMP_TAC[DIVISION]; ALL_TAC] THEN
          MATCH_MP_TAC DIVIDES_ADD THEN
          ASM_SIMP_TAC[DIVIDES_LMUL; DIVIDES_REFL] THEN
          MATCH_MP_TAC DIVIDES_ADD_REVR THEN
          EXISTS_TAC `n - y MOD n` THEN ASM_REWRITE_TAC[] THEN
          ASM_SIMP_TAC[ARITH_RULE `m < n ==> ((n - m) + m = n:num)`;
                       DIVISION];
          ALL_TAC] THEN
        SUBGOAL_THEN `!x. c * x = (c * x) DIV n * n + (c * x) MOD n`
         (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
        THENL [ASM_SIMP_TAC[DIVISION]; ALL_TAC] THEN
        REWRITE_TAC[coprime] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC[DIVIDES_ADD; DIVIDES_LMUL; DIVIDES_REFL]; ALL_TAC] THEN
      ASM_SIMP_TAC[MOD_MULT_RMOD] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIFFERENCE_POS_LEMMA THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[ARITH_RULE
         `c <= a * c * x <=> c * 1 <= c * a * x`] THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
        REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0;
                    SUB_EQ_0; DE_MORGAN_THM] THEN
        UNDISCH_TAC `coprime(a,n)` THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
        ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[COPRIME_0] THEN
        DISCH_TAC THEN ASM_SIMP_TAC[DIVISION; NOT_LE]; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`c * x`; `c * a * (1 + y DIV n)`] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; LEFT_SUB_DISTRIB] THEN
      MATCH_MP_TAC(ARITH_RULE
       `y <= n /\ (a + n = x + y) ==> (a + (n - y) = x)`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[MULT_ASSOC] THEN REWRITE_TAC[LE_MULT_LCANCEL] THEN
        ASM_SIMP_TAC[LT_IMP_LE; DIVISION]; ALL_TAC] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
      REWRITE_TAC[GSYM ADD_ASSOC; GSYM MULT_ASSOC] THEN
      REWRITE_TAC[ARITH_RULE
       `(x + a * c * n = c * a * n + y) <=> (x = y)`] THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
       `(n * x - a * y = 1) ==> (x * n = a * y + 1)`)) THEN
      SUBGOAL_THEN `y = (y DIV n) * n + y MOD n`
       (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
      THENL [ASM_SIMP_TAC[DIVISION]; ALL_TAC] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
      REWRITE_TAC[MULT_AC; ADD_AC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{c | ?b. 0 < b /\ b < n /\ coprime (b,n) /\ (c = (a * b) MOD n)} =
    IMAGE (\b. (a * b) MOD n) {b | 0 < b /\ b < n /\ coprime (b,n)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[IMAGE; EXTENSION; IN_ELIM_THM; CONJ_ASSOC]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `ITSET (\x y. (x * y) MOD n)`) THEN
  DISCH_THEN(MP_TAC o C AP_THM `1`) THEN
  SUBGOAL_THEN `FINITE {b | 0 < b /\ b < n /\ coprime (b,n)} /\
                !b. b IN {b | 0 < b /\ b < n /\ coprime (b,n)} ==> b < n`
  ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; SIMP_TAC[IN_ELIM_THM]] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{b | 0 < b /\ b < n}` THEN
    REWRITE_TAC[REWRITE_RULE[HAS_SIZE] FINITE_NUMBER_SEGMENT] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM]; ALL_TAC] THEN
  ASM_SIMP_TAC[REWRITE_RULE[IMP_IMP]
    ITSET_MODMULT] THEN
  ASM_SIMP_TAC[GSYM PHI_ANOTHER] THEN
  DISCH_THEN(MP_TAC o AP_TERM `(MOD)`) THEN
  DISCH_THEN(MP_TAC o C AP_THM `n:num`) THEN
  ASM_SIMP_TAC[MOD_MOD_REFL] THEN ASM_SIMP_TAC[GSYM CONG] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV)
   [ARITH_RULE `x = x * 1`] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV) [MULT_SYM] THEN
  DISCH_TAC THEN MATCH_MP_TAC CONG_MULT_LCANCEL THEN
  EXISTS_TAC `ITSET (\x y. (x * y) MOD n)
                    {b | 0 < b /\ b < n /\ coprime (b,n)} 1` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ITSET_MODMULT_COPRIME; IN_ELIM_THM]);;

let FERMAT_LITTLE_PRIME = prove
 (`!p a. prime p ==> (a EXP p == a) (mod p)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:num` o MATCH_MP PRIME_COPRIME) THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[EXP_ONE; CONG_REFL];
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `0` THEN
    GEN_REWRITE_TAC RAND_CONV [CONG_SYM] THEN ASM_REWRITE_TAC[CONG_0] THEN
    ASM_MESON_TAC[DIVIDES_EXP; DIVIDES_EXP2; PRIME_0];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FERMAT_LITTLE) THEN
  ASM_SIMP_TAC[snd(EQ_IMP_RULE (SPEC_ALL PHI_PRIME_EQ))] THEN
  REWRITE_TAC[cong; nat_mod] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:num` (X_CHOOSE_THEN `q2:num` MP_TAC)) THEN
  DISCH_THEN(MP_TAC o AP_TERM `( * ) a`) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM(CONJUNCT2 EXP)] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
  REWRITE_TAC[MULT_CLAUSES; GSYM MULT_ASSOC] THEN
  ASM_MESON_TAC[ARITH_RULE `~(p = 0) ==> (SUC(p - 1) = p)`; PRIME_0]);;

(* ------------------------------------------------------------------------- *)
(* Lucas's theorem.                                                          *)
(* ------------------------------------------------------------------------- *)

let LUCAS_COPRIME_LEMMA = prove
 (`!m n a. ~(m = 0) /\ (a EXP m == 1) (mod n) ==> coprime(a,n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[CONG_MOD_0; EXP_EQ_1] THEN
    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN SIMP_TAC[COPRIME_1];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[COPRIME_1] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[coprime] THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
  UNDISCH_TAC `(a EXP m == 1) (mod n)` THEN
  ASM_SIMP_TAC[CONG] THEN
  SUBGOAL_THEN `1 MOD n = 1` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    MAP_EVERY UNDISCH_TAC [`~(n = 0)`; `~(n = 1)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `d divides (a EXP m) MOD n` MP_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[DIVIDES_ONE]] THEN
  MATCH_MP_TAC DIVIDES_ADD_REVR THEN
  EXISTS_TAC `a EXP m DIV n * n` THEN
  ASM_SIMP_TAC[GSYM DIVISION; DIVIDES_LMUL] THEN
  SUBGOAL_THEN `m = SUC(m - 1)` SUBST1_TAC THENL
   [UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC;
    ASM_SIMP_TAC[EXP; DIVIDES_RMUL]]);;

let LUCAS_WEAK = prove
 (`!a n. 2 <= n /\
         (a EXP (n - 1) == 1) (mod n) /\
         (!m. 0 < m /\ m < n - 1 ==> ~(a EXP m == 1) (mod n))
         ==> prime(n)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM PHI_PRIME_EQ; PHI_LIMIT_STRONG; GSYM LE_ANTISYM;
               ARITH_RULE `2 <= n ==> ~(n = 0) /\ ~(n = 1)`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `phi n`) THEN
  SUBGOAL_THEN `coprime(a,n)` (fun th -> SIMP_TAC[FERMAT_LITTLE; th]) THENL
   [MATCH_MP_TAC LUCAS_COPRIME_LEMMA THEN EXISTS_TAC `n - 1` THEN
    ASM_SIMP_TAC [ARITH_RULE `2 <= n ==> ~(n - 1 = 0)`]; ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_LT] THEN
  MATCH_MP_TAC(TAUT `a ==> ~(a /\ b) ==> ~b`) THEN
  ASM_SIMP_TAC[PHI_LOWERBOUND_1; ARITH_RULE `1 <= n ==> 0 < n`]);;

let LUCAS = prove
 (`!a n. 2 <= n /\
         (a EXP (n - 1) == 1) (mod n) /\
         (!p. prime(p) /\ p divides (n - 1)
              ==> ~(a EXP ((n - 1) DIV p) == 1) (mod n))
         ==> prime(n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP(ARITH_RULE `2 <= n ==> ~(n = 0)`)) THEN
  MATCH_MP_TAC LUCAS_WEAK THEN EXISTS_TAC `a:num` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[TAUT `a ==> ~b <=> ~(a /\ b)`; GSYM NOT_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP(ARITH_RULE `0 < n ==> ~(n = 0)`)) THEN
  SUBGOAL_THEN `m divides (n - 1)` MP_TAC THENL
   [REWRITE_TAC[divides] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_SIMP_TAC[GSYM MOD_EQ_0] THEN
    MATCH_MP_TAC(ARITH_RULE `~(0 < n) ==> (n = 0)`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(n - 1) MOD m`) THEN
    ASM_SIMP_TAC[DIVISION] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `m:num` THEN
      ASM_SIMP_TAC[DIVISION]; ALL_TAC] THEN
    MATCH_MP_TAC CONG_MULT_LCANCEL THEN
    EXISTS_TAC `a EXP ((n - 1) DIV m * m)` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_EXP THEN
      ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC LUCAS_COPRIME_LEMMA THEN
      EXISTS_TAC `m:num` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM EXP_ADD] THEN
    ASM_SIMP_TAC[GSYM DIVISION] THEN REWRITE_TAC[MULT_CLAUSES] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM EXP_EXP] THEN
    UNDISCH_TAC `(a EXP (n - 1) == 1) (mod n)` THEN
    UNDISCH_TAC `(a EXP m == 1) (mod n)` THEN
    ASM_SIMP_TAC[CONG] THEN REPEAT DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `((a EXP m) MOD n) EXP ((n - 1) DIV m) MOD n` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[MOD_EXP_MOD]] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MOD_EXP_MOD] THEN
    REWRITE_TAC[EXP_ONE]; ALL_TAC] THEN
  REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `~(r = 1)` MP_TAC THENL
   [UNDISCH_TAC `m < m * r` THEN CONV_TAC CONTRAPOS_CONV THEN
    SIMP_TAC[MULT_CLAUSES; LT_REFL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` MP_TAC) THEN STRIP_TAC THEN
  UNDISCH_TAC `!p. prime p /\ p divides m * r
                   ==> ~(a EXP ((m * r) DIV p) == 1) (mod n)` THEN
  DISCH_THEN(MP_TAC o SPEC `p:num`) THEN ASM_SIMP_TAC[DIVIDES_LMUL] THEN
  SUBGOAL_THEN `(m * r) DIV p = m * (r DIV p)` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    UNDISCH_TAC `prime p` THEN
    ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[PRIME_0] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(p = 0) ==> 0 < p`] THEN
    DISCH_TAC THEN REWRITE_TAC[ADD_CLAUSES; GSYM MULT_ASSOC] THEN
    AP_TERM_TAC THEN UNDISCH_TAC `p divides r` THEN
    REWRITE_TAC[divides] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[DIV_MULT] THEN REWRITE_TAC[MULT_AC]; ALL_TAC] THEN
  UNDISCH_TAC `(a EXP m == 1) (mod n)` THEN
  ASM_SIMP_TAC[CONG] THEN
  DISCH_THEN(MP_TAC o C AP_THM `r DIV p` o AP_TERM `(EXP)`) THEN
  DISCH_THEN(MP_TAC o C AP_THM `n:num` o AP_TERM `(MOD)`) THEN
  ASM_SIMP_TAC[MOD_EXP_MOD] THEN
  REWRITE_TAC[EXP_EXP; EXP_ONE]);;

(* ------------------------------------------------------------------------- *)
(* Prime factorizations.                                                     *)
(* ------------------------------------------------------------------------- *)

let primefact = new_definition
  `primefact ps n <=> (ITLIST (*) ps 1 = n) /\ !p. MEM p ps ==> prime(p)`;;

let PRIMEFACT = prove
 (`!n. ~(n = 0) ==> ?ps. primefact ps n`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[] THENL
   [REPEAT DISCH_TAC THEN EXISTS_TAC `[]:num list` THEN
    REWRITE_TAC[primefact; ITLIST; MEM]; ALL_TAC] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC o
    MATCH_MP PRIME_FACTOR) THEN
  UNDISCH_TAC `p divides n` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  UNDISCH_TAC `~(p * m = 0)` THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (funpow 3 LAND_CONV) [ARITH_RULE `n = 1 * n`] THEN
  ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN
  SUBGOAL_THEN `1 < p` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC(ARITH_RULE `~(p = 0) /\ ~(p = 1) ==> 1 < p`) THEN
    REPEAT STRIP_TAC THEN UNDISCH_TAC `prime p` THEN
    ASM_REWRITE_TAC[PRIME_0; PRIME_1]; ALL_TAC] THEN
  REWRITE_TAC[primefact] THEN
  DISCH_THEN(X_CHOOSE_THEN `ps:num list` ASSUME_TAC) THEN
  EXISTS_TAC `CONS (p:num) ps` THEN
  ASM_REWRITE_TAC[MEM; ITLIST] THEN ASM_MESON_TAC[]);;

let PRIMAFACT_CONTAINS = prove
 (`!ps n. primefact ps n ==> !p. prime p /\ p divides n ==> MEM p ps`,
  REPEAT GEN_TAC THEN REWRITE_TAC[primefact] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  POP_ASSUM(SUBST1_TAC o SYM) THEN
  SPEC_TAC(`ps:num list`,`ps:num list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ITLIST; MEM] THENL
   [ASM_MESON_TAC[DIVIDES_ONE; PRIME_1]; ALL_TAC] THEN
  STRIP_TAC THEN GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN MP_TAC th) THEN
  DISCH_THEN(DISJ_CASES_TAC o MATCH_MP PRIME_DIVPROD) THEN
  ASM_MESON_TAC[prime; PRIME_1]);;

let PRIMEFACT_VARIANT = prove
 (`!ps n. primefact ps n <=> (ITLIST (*) ps 1 = n) /\ ALL prime ps`,
  REPEAT GEN_TAC THEN REWRITE_TAC[primefact] THEN AP_TERM_TAC THEN
  SPEC_TAC(`ps:num list`,`ps:num list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MEM; ALL] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Variant of Lucas theorem.                                                 *)
(* ------------------------------------------------------------------------- *)

let LUCAS_PRIMEFACT = prove
 (`2 <= n /\
   (a EXP (n - 1) == 1) (mod n) /\
   (ITLIST (*) ps 1 = n - 1) /\
   ALL (\p. prime p /\ ~(a EXP ((n - 1) DIV p) == 1) (mod n)) ps
   ==> prime n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LUCAS THEN
  EXISTS_TAC `a:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `primefact ps (n - 1)` MP_TAC THENL
   [ASM_REWRITE_TAC[PRIMEFACT_VARIANT] THEN MATCH_MP_TAC ALL_IMP THEN
    EXISTS_TAC `\p. prime p /\ ~(a EXP ((n - 1) DIV p) == 1) (mod n)` THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP PRIMAFACT_CONTAINS) THEN
  X_GEN_TAC `p:num` THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN UNDISCH_TAC
   `ALL (\p. prime p /\ ~(a EXP ((n - 1) DIV p) == 1) (mod n)) ps` THEN
  SPEC_TAC(`ps:num list`,`ps:num list`) THEN LIST_INDUCT_TAC THEN
  SIMP_TAC[ALL; MEM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Utility functions.                                                        *)
(* ------------------------------------------------------------------------- *)

let even_num n =
  mod_num n num_2 =/ num_0;;

let odd_num = not o even_num;;

(* ------------------------------------------------------------------------- *)
(* Least p >= 0 with x <= 2^p.                                               *)
(* ------------------------------------------------------------------------- *)

let log2 =
  let rec log2 x y =
    if x </ num_1 then y
    else log2 (quo_num x num_2) (y +/ num_1) in
  fun x -> log2 (x -/ num_1) num_0;;

(* ------------------------------------------------------------------------- *)
(* Raise number to power (x^m) modulo n.                                     *)
(* ------------------------------------------------------------------------- *)

let rec powermod x m n =
  if m =/ num_0 then num_1 else
  let y = powermod x (quo_num m num_2) n in
  let z = mod_num (y */ y) n in
  if even_num m then z else
  mod_num (x */ z) n;;

(* ------------------------------------------------------------------------- *)
(* Make a call to PARI/GP to factor a number into (probable) primes.         *)
(* ------------------------------------------------------------------------- *)

let factor =
  let suck_file s = let data = string_of_file s in Sys.remove s; data in
  let extract_output s =
    let l0 = explode s in
    let l0' = rev l0 in
    let l1 = snd(chop_list(index "]" l0') l0') in
    let l2 = "["::rev(fst(chop_list(index "[" l1) l1)) in
    let tm = parse_term (implode l2) in
    map ((dest_numeral F_F dest_numeral) o dest_pair) (dest_list tm) in
  fun n ->
    if n =/ num_1 then [] else
    let filename = Filename.temp_file "pocklington" ".out" in
    let s = "echo 'print(factorint(" ^
            (string_of_num n) ^
            "))  \n quit' | gp >" ^ filename ^ " 2>/dev/null" in
    if Sys.command s = 0 then
      let output = suck_file filename in
      extract_output output
    else
       failwith "factor: Call to GP/PARI failed";;

(* ------------------------------------------------------------------------- *)
(* Alternative giving multiset instead of set plus indices.                  *)
(* ------------------------------------------------------------------------- *)

let multifactor =
  let rec multilist l =
    if l = [] then [] else
    let (x,n) = hd l in
    replicate x (Num.int_of_num n) @ multilist (tl l) in
  fun n -> multilist (factor n);;

(* ------------------------------------------------------------------------- *)
(* Recursive creation of Pratt primality certificates.                       *)
(* ------------------------------------------------------------------------- *)

type certificate =
    Prime_2
  | Primroot_and_factors of
      ((num * num list) * num * (num * certificate) list);;

let find_primitive_root =
  let rec find_primitive_root a m ms n =
    if gcd_num a n =/ num_1 &&
       powermod a m n =/ num_1 &&
       forall (fun k -> powermod a k n <>/ num_1) ms
    then a
    else find_primitive_root (a +/ num_1) m ms n in
  let find_primitive_root_from_2 = find_primitive_root num_2 in
  fun m ms n ->
    if n </ num_2 then failwith "find_primitive_root: input too small"
    else find_primitive_root_from_2 m ms n;;

let uniq_num =
  let rec uniq x l =
    match l with
      [] -> raise Unchanged
    | (h::t) -> if x =/ h then
                  try uniq x t
                  with Unchanged -> l
                else x::(uniq h t) in
  fun l -> if l = [] then [] else uniq (hd l) (tl l);;

let setify_num s =
  let s' = sort (<=/) s in
  try uniq_num s' with Unchanged -> s';;

let certify_prime =
  let rec cert_prime n =
    if n <=/ num_2 then
       if n =/ num_2 then Prime_2
       else failwith "certify_prime: not a prime!"
    else
      let m = n -/ num_1 in
      let pfact = multifactor m in
      let primes = setify_num pfact in
      let ms = map (fun d -> div_num m d) primes in
      let a = find_primitive_root m ms n in
      Primroot_and_factors((n,pfact),a,map (fun n -> n,cert_prime n) primes) in
  fun n -> if length(multifactor n) = 1 then cert_prime n
           else failwith "certify_prime: input is not a prime";;

(* ------------------------------------------------------------------------- *)
(* Relatively efficient evaluation of "(a EXP m == 1) (mod n)".              *)
(* ------------------------------------------------------------------------- *)

let EXP_EQ_MOD_CONV =
  let pth = prove
   (`~(n = 0)
     ==> ((a EXP 0) MOD n = 1 MOD n) /\
         ((a EXP (NUMERAL (BIT0 m))) MOD n =
                let b = (a EXP (NUMERAL m)) MOD n in
                (b * b) MOD n) /\
         ((a EXP (NUMERAL (BIT1 m))) MOD n =
                let b = (a EXP (NUMERAL m)) MOD n in
                (a * ((b * b) MOD n)) MOD n)`,
    DISCH_TAC THEN REWRITE_TAC[EXP] THEN
    REWRITE_TAC[NUMERAL; BIT0; BIT1] THEN
    REWRITE_TAC[EXP; EXP_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    ASM_SIMP_TAC[MOD_MULT_LMOD; MOD_MULT_RMOD] THEN
    REWRITE_TAC[MULT_ASSOC] THEN
    ASM_SIMP_TAC[MOD_MULT_LMOD; MOD_MULT_RMOD] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN
    REWRITE_TAC[MULT_ASSOC] THEN
    ASM_SIMP_TAC[MOD_MULT_LMOD; MOD_MULT_RMOD])
  and pth_cong = prove
   (`~(n = 0) ==> ((x == y) (mod n) <=> x MOD n = y MOD n)`,
    REWRITE_TAC[CONG])
  and n_tm = `n:num` in
  let raw_conv tm =
    let ntm = rand(rand tm) in
    let th1 = INST [ntm,n_tm] pth_cong in
    let th2 = EQF_ELIM(NUM_EQ_CONV(rand(lhand(concl th1)))) in
    let th3 = REWR_CONV (MP th1 th2) tm in
    let th4 = MP (INST [ntm,n_tm] pth) th2 in
    let th4a,th4b = CONJ_PAIR th4 in
    let conv_base = GEN_REWRITE_CONV I [th4a]
    and conv_step = GEN_REWRITE_CONV I [th4b] in
    let rec conv tm =
      try conv_base tm with Failure _ ->
      (conv_step THENC
       RAND_CONV conv THENC
       let_CONV THENC
       NUM_REDUCE_CONV) tm in
    let th5 = (LAND_CONV conv THENC NUM_REDUCE_CONV) (rand(concl th3)) in
    TRANS th3 th5 in
  let gconv_net = itlist (uncurry net_of_conv)
   [`(a EXP m == 1) (mod n)`,raw_conv] empty_net in
  REWRITES_CONV gconv_net;;

(* ------------------------------------------------------------------------- *)
(* HOL checking of such a certificate. We retain a cache for efficiency.     *)
(* ------------------------------------------------------------------------- *)

let prime_theorem_cache = ref [];;

let rec lookup_under_num n l =
  if l = [] then failwith "lookup_under_num" else
  let h = hd l in
  if fst h =/ n then snd h
  else lookup_under_num n (tl l);;

let check_certificate =
  let n_tm = `n:num`
  and a_tm = `a:num`
  and ps_tm = `ps:num list`
  and SIMPLE_REWRITE_CONV = REWRITE_CONV[]
  and CONJ_AC_SORTED = TAUT `(a /\ a /\ b <=> a /\ b) /\ (a /\ a <=> a)` in
  let CLEAN_RULE = CONV_RULE
    (REWRITE_CONV[ITLIST; ALL; CONJ_AC_SORTED] THENC
     ONCE_DEPTH_CONV NUM_SUB_CONV THENC
     DEPTH_CONV NUM_MULT_CONV THENC
     ONCE_DEPTH_CONV NUM_DIV_CONV THENC
     ONCE_DEPTH_CONV(NUM_EQ_CONV ORELSEC NUM_LE_CONV) THENC
     SIMPLE_REWRITE_CONV) in
  let rec check_certificate cert =
    match cert with
      Prime_2 ->
          PRIME_2
    | Primroot_and_factors((n,ps),a,ncerts) ->
          try lookup_under_num n (!prime_theorem_cache) with Failure _ ->
          let th1 = INST [mk_numeral n,n_tm;
                          mk_flist (map mk_numeral ps),ps_tm;
                          mk_numeral a,a_tm]
                         LUCAS_PRIMEFACT in
          let th2 = CLEAN_RULE th1 in
          let th3 = ONCE_DEPTH_CONV EXP_EQ_MOD_CONV (concl th2) in
          let th4 = CONV_RULE SIMPLE_REWRITE_CONV (EQ_MP th3 th2) in
          let ants = conjuncts(lhand(concl th4)) in
          let certs =
            map (fun t -> lookup_under_num (dest_numeral(rand t)) ncerts)
                ants in
          let ths = map check_certificate certs in
          let fth = MP th4 (end_itlist CONJ ths) in
          prime_theorem_cache := (n,fth)::(!prime_theorem_cache); fth in
  check_certificate;;

(* ------------------------------------------------------------------------- *)
(* Hence a primality-proving rule.                                           *)
(* ------------------------------------------------------------------------- *)

let PROVE_PRIME = check_certificate o certify_prime;;

(* ------------------------------------------------------------------------- *)
(* Rule to generate prime factorization theorems.                            *)
(* ------------------------------------------------------------------------- *)

let PROVE_PRIMEFACT =
  let pth = SPEC_ALL PRIMEFACT_VARIANT
  and start_CONV = PURE_REWRITE_CONV[ITLIST; ALL] THENC NUM_REDUCE_CONV
  and ps_tm = `ps:num list`
  and n_tm = `n:num` in
  fun n ->
     let pfact = multifactor n in
     let th1 = INST [mk_flist(map mk_numeral pfact),ps_tm;
                     mk_numeral n,n_tm] pth in
     let th2 = TRANS th1 (start_CONV(rand(concl th1))) in
     let ths = map PROVE_PRIME pfact in
     EQ_MP (SYM th2) (end_itlist CONJ ths);;

(* ------------------------------------------------------------------------- *)
(* Conversion for truth or falsity of primality assertion.                   *)
(* ------------------------------------------------------------------------- *)

let PRIME_TEST =
  let NOT_PRIME_THM = prove
   (`((m = 1) <=> F) ==> ((m = p) <=> F) ==> (m * n = p) ==> (prime(p) <=> F)`,
    MESON_TAC[prime; divides])
  and m_tm = `m:num` and n_tm = `n:num` and p_tm = `p:num` in
  fun tm ->
    let p = dest_numeral tm in
    if p =/ Num.num_of_int 0 then EQF_INTRO PRIME_0
    else if p =/ Num.num_of_int 1 then EQF_INTRO PRIME_1 else
    let pfact = multifactor p in
    if length pfact = 1 then
     (remark ("proving that " ^ string_of_num p ^ " is prime");
      EQT_INTRO(PROVE_PRIME p))
    else
     (remark ("proving that " ^ string_of_num p ^ " is composite");
      let m = hd pfact and n = end_itlist ( */ ) (tl pfact) in
      let th0 = INST [mk_numeral m,m_tm; mk_numeral n,n_tm; mk_numeral p,p_tm]
                     NOT_PRIME_THM in
      let th1 = MP th0 (NUM_EQ_CONV (lhand(lhand(concl th0)))) in
      let th2 = MP th1 (NUM_EQ_CONV (lhand(lhand(concl th1)))) in
      MP th2 (NUM_MULT_CONV(lhand(lhand(concl th2)))));;

let PRIME_CONV =
  let prime_tm = `prime` in
  fun tm0 ->
    let ptm,tm = dest_comb tm0 in
    if ptm <> prime_tm then failwith "expected term of form prime(n)"
    else PRIME_TEST tm;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

map (time PRIME_TEST o mk_small_numeral) (0--50);;

time PRIME_TEST `65535`;;

time PRIME_TEST `65536`;;

time PRIME_TEST `65537`;;

time PROVE_PRIMEFACT (Num.num_of_int 222);;

time PROVE_PRIMEFACT (Num.num_of_int 151);;

(* ------------------------------------------------------------------------- *)
(* The "Landau trick" in Erdos's proof of Chebyshev-Bertrand theorem.        *)
(* ------------------------------------------------------------------------- *)

map (time PRIME_TEST o mk_small_numeral)
  [3; 5; 7; 13; 23; 43; 83; 163; 317; 631; 1259; 2503; 4001];;
