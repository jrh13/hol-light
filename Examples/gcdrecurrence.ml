(* ========================================================================= *)
(* Some divisibility properties of certain linear integer recurrences.       *)
(* ========================================================================= *)

needs "Library/prime.ml";;
needs "Library/integer.ml";;

prioritize_int();;

(* ------------------------------------------------------------------------- *)
(* A customized induction principle.                                         *)
(* ------------------------------------------------------------------------- *)

let INDUCT_SPECIAL = prove
 (`!P. (!n. P 0 n) /\
       (!m n. P m n <=> P n m) /\
       (!m n. P m n ==> P n (m + n))
       ==> !m n. P m n`,
  GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN WF_INDUCT_TAC `m + n:num` THEN
  ASM_CASES_TAC `m = 0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISJ_CASES_THEN MP_TAC (ARITH_RULE `m <= n:num \/ n <= m`) THEN
  REWRITE_TAC[LE_EXISTS] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST_ALL_TAC) THENL
   [ALL_TAC; ASM (GEN_REWRITE_TAC I) []] THEN
  MATCH_MP_TAC(ASSUME `!m n:num. P m n ==> P n (m + n)`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The main results; to literally apply integer gcd we need nonnegativity.   *)
(* ------------------------------------------------------------------------- *)

let INT_DIVISORS_RECURRENCE = prove
 (`!G a b. G(0) = &0 /\ G(1) = &1 /\
           coprime(a,b) /\ (!n. G(n + 2) = a * G(n + 1) + b * G(n))
           ==> !d m n. d divides (G m) /\ d divides (G n) <=>
                       d divides G(gcd(m,n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. coprime(G(n + 1),b)` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[ARITH; ARITH_RULE `SUC n + 1 = n + 2`] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN NUMBER_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. coprime(G(n + 1),G n)` ASSUME_TAC THENL
   [INDUCT_TAC THENL [ASM_REWRITE_TAC[ARITH] THEN NUMBER_TAC; ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SPEC `n:num`)) THEN
    ASM_REWRITE_TAC[ADD1; ARITH_RULE `(n + 1) + 1 = n + 2`] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN INTEGER_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!m p. G(m + 1 + p) = G(m + 1) * G(p + 1) + b * G(m) * G(p)`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [ASM_REWRITE_TAC[ADD_CLAUSES; ADD_AC] THEN INTEGER_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC m + 1 + p = (m + p) + 2`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC m + 1 = m + 2`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `(m + p) + 1 = m + 1 + p`] THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[ARITH; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC(m + p) = m + 1 + p`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC(m + 1) = m + 2`; ARITH] THEN
    REWRITE_TAC[ADD1] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!m p:num. gcd(G(m + p),G m) = gcd(G m,G p)` ASSUME_TAC THENL
   [INDUCT_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; EQT_INTRO(SPEC_ALL INT_GCD_SYM)] THEN
    ASM_REWRITE_TAC[ADD1; ARITH_RULE `(m + p) + 1 = m + 1 + p`] THEN
    GEN_TAC THEN SIMP_TAC[INT_GCD_POS; GSYM INT_DIVIDES_ANTISYM_POS] THEN
    MP_TAC(SPEC `m:num` (ASSUME `!n. coprime(G(n + 1),b)`)) THEN
    MP_TAC(SPEC `m:num` (ASSUME `!n. coprime(G(n + 1),G n)`)) THEN
    INTEGER_TAC;
    ALL_TAC] THEN
  GEN_TAC THEN MATCH_MP_TAC INDUCT_SPECIAL THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[GCD_0; INT_DIVIDES_0]; MESON_TAC[GCD_SYM]; ALL_TAC] THEN
  ASM_MESON_TAC[GCD_ADD; INT_DIVIDES_GCD; INT_GCD_SYM; ADD_SYM; GCD_SYM]);;

let INT_GCD_RECURRENCE = prove
 (`!G a b. G(0) = &0 /\ G(1) = &1 /\
           coprime(a,b) /\ (!n. G(n + 2) = a * G(n + 1) + b * G(n)) /\
           (!n. &0 <= G n)
           ==> !m n. gcd(G m,G n) = G(gcd(m,n))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[GSYM INT_DIVIDES_ANTISYM_POS; INT_GCD_POS] THEN
  REWRITE_TAC[INT_DIVIDES_ANTISYM_DIVISORS; INT_DIVIDES_GCD] THEN
  ASM_MESON_TAC[INT_DIVISORS_RECURRENCE]);;

(* ------------------------------------------------------------------------- *)
(* Natural number variants of the same results.                              *)
(* ------------------------------------------------------------------------- *)

let GCD_RECURRENCE = prove
 (`!G a b. G(0) = 0 /\ G(1) = 1 /\
           coprime(a,b) /\ (!n. G(n + 2) = a * G(n + 1) + b * G(n))
           ==> !m n. gcd(G m,G n) = G(gcd(m,n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`& o (G:num->num)`; `&a:int`; `&b:int`]
        INT_GCD_RECURRENCE) THEN
  ASM_REWRITE_TAC[o_THM; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
  ASM_SIMP_TAC[GSYM num_coprime; INT_POS; GSYM NUM_GCD; INT_OF_NUM_EQ]);;

let DIVISORS_RECURRENCE = prove
 (`!G a b. G(0) = 0 /\ G(1) = 1 /\
           coprime(a,b) /\ (!n. G(n + 2) = a * G(n + 1) + b * G(n))
           ==> !d m n. d divides (G m) /\ d divides (G n) <=>
                       d divides G(gcd(m,n))`,
  REWRITE_TAC[GSYM DIVIDES_GCD] THEN MESON_TAC[DIVISORS_EQ; GCD_RECURRENCE]);;

(* ------------------------------------------------------------------------- *)
(* Application 1: Mersenne numbers.                                          *)
(* ------------------------------------------------------------------------- *)

let GCD_MERSENNE = prove
 (`!m n. gcd(2 EXP m - 1,2 EXP n - 1) = 2 EXP (gcd(m,n)) - 1`,
  SIMP_TAC[GSYM INT_OF_NUM_EQ; NUM_GCD; GSYM INT_OF_NUM_SUB;
           GSYM INT_OF_NUM_POW; EXP_LT_0; ARITH;
           ARITH_RULE `1 <= n <=> 0 < n`] THEN
  MATCH_MP_TAC INT_GCD_RECURRENCE THEN
  MAP_EVERY EXISTS_TAC [`&3`; `-- &2`] THEN
  REWRITE_TAC[INT_POW_ADD; INT_LE_SUB_LADD] THEN
  CONV_TAC INT_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM(INT_REDUCE_CONV `&2 * &2 - &1`)] THEN
    SPEC_TAC(`&2`,`t:int`) THEN INTEGER_TAC;
    INT_ARITH_TAC;
    GEN_TAC THEN MATCH_MP_TAC INT_POW_LE_1 THEN INT_ARITH_TAC]);;

let DIVIDES_MERSENNE = prove
 (`!m n. (2 EXP m - 1) divides (2 EXP n - 1) <=> m divides n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DIVIDES_GCD_LEFT; GCD_MERSENNE] THEN
  SIMP_TAC[EXP_EQ_0; EQ_EXP; ARITH_EQ; ARITH_RULE
   `~(x = 0) /\ ~(y = 0) ==> (x - 1 = y - 1 <=> x = y)`]);;

(* ------------------------------------------------------------------------- *)
(* Application 2: the Fibonacci series.                                      *)
(* ------------------------------------------------------------------------- *)

let fib = define
 `fib 0 = 0 /\ fib 1 = 1 /\ !n. fib(n + 2) = fib(n + 1) + fib(n)`;;

let GCD_FIB = prove
 (`!m n. gcd(fib m,fib n) = fib(gcd(m,n))`,
  MATCH_MP_TAC GCD_RECURRENCE THEN
  REPEAT(EXISTS_TAC `1`) THEN REWRITE_TAC[fib; COPRIME_1] THEN ARITH_TAC);;

let FIB_EQ_0 = prove
 (`!n. fib n = 0 <=> n = 0`,
  MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[fib] THEN
  MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[fib; ARITH_RULE `SUC(SUC n) = n + 2`; ADD_EQ_0] THEN
  SIMP_TAC[ADD1; ADD_EQ_0; ARITH_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[fib; ARITH_EQ]);;

let FIB_INCREASES_LE = prove
 (`!m n. m <= n ==> fib m <= fib n`,
  MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
  REWRITE_TAC[LE_REFL; LE_TRANS] THEN
  MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[fib; ARITH] THEN
  REWRITE_TAC[ADD1; fib; ARITH_RULE `(n + 1) + 1 = n + 2`] THEN
  ARITH_TAC);;

let FIB_INCREASES_LT = prove
 (`!m n. 2 <= m /\ m < n ==> fib m < fib n`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
  REPEAT STRIP_TAC THEN TRANS_TAC LTE_TRANS `fib(m + 2)` THEN
  ASM_SIMP_TAC[FIB_INCREASES_LE; ARITH_RULE `m + 2 <= n <=> SUC m < n`] THEN
  REWRITE_TAC[fib; ADD1; ARITH_RULE `m < m + n <=> ~(n = 0)`; FIB_EQ_0] THEN
  ASM_ARITH_TAC);;

let FIB_EQ_1 = prove
 (`!n. fib n = 1 <=> n = 1 \/ n = 2`,
  MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[fib; ARITH] THEN
  MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[fib; ARITH] THEN
  REWRITE_TAC[fib; ARITH_RULE `SUC(SUC n) = n + 2`] THEN
  REWRITE_TAC[FIB_EQ_0; ADD_EQ_0; ARITH; ARITH_RULE
   `m + n = 1 <=> m = 0 /\ n = 1 \/ m = 1 /\ n = 0`] THEN
  ARITH_TAC);;

let DIVIDES_FIB = prove
 (`!m n. (fib m) divides (fib n) <=> m divides n \/ n = 0 \/ m = 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DIVIDES_GCD_LEFT; GCD_FIB] THEN
  MP_TAC(SPECL [`gcd(m:num,n)`; `m:num`] DIVIDES_LE) THEN REWRITE_TAC[GCD] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[GCD_0; fib; FIB_EQ_0; ARITH] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[GCD_0] THEN
  ASM_CASES_TAC `gcd(m:num,n) = m` THEN ASM_REWRITE_TAC[LE_LT] THEN
  ASM_CASES_TAC `gcd(m:num,n) = 0` THENL
   [ASM_MESON_TAC[GCD_ZERO]; ALL_TAC] THEN
  ASM_CASES_TAC `m:num = n` THEN ASM_REWRITE_TAC[GCD_REFL; LT_REFL] THEN
  ASM_CASES_TAC `2 <= gcd(m,n)` THENL
   [MP_TAC(SPECL [`gcd(m:num,n)`; `m:num`] FIB_INCREASES_LT) THEN
    ASM_ARITH_TAC;
    ASM_CASES_TAC `gcd(m,n) = 1` THENL [ASM_REWRITE_TAC[]; ASM_ARITH_TAC] THEN
    DISCH_TAC THEN CONV_TAC(LAND_CONV SYM_CONV) THEN
    REWRITE_TAC[FIB_EQ_1; fib] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Application 3: solutions of the Pell equation x^2 = (a^2 - 1) y^2 + 1.    *)
(* All solutions are of the form (pellx a n,pelly a n); see Examples/pell.ml *)
(* ------------------------------------------------------------------------- *)

let pellx = define
  `(!a. pellx a 0 = 1) /\
   (!a. pellx a 1 = a) /\
   (!a n. pellx a (n + 2) = 2 * a * pellx a (n + 1) - pellx a n)`;;

let pelly = define
  `(!a. pelly a 0 = 0) /\
   (!a. pelly a 1 = 1) /\
   (!a n. pelly a (n + 2) = 2 * a * pelly a (n + 1) - pelly a (n))`;;

let PELLY_INCREASES = prove
 (`!a n. ~(a = 0) ==> pelly a n <= pelly a (n + 1)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[pelly; ARITH; LE_1; ADD1; ARITH_RULE `(n + 1) + 1 = n + 2`] THEN
  TRANS_TAC LE_TRANS `2 * pelly a (n + 1) - pelly a n` THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `a:num <= b ==> a - c <= b - c`) THEN
  REWRITE_TAC[MULT_ASSOC; LE_MULT_RCANCEL] THEN ASM_ARITH_TAC);;

let GCD_PELLY = prove
 (`!a m n. ~(a = 0) ==> gcd(pelly a m,pelly a n) = pelly a (gcd(m,n))`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; NUM_GCD] THEN
  MATCH_MP_TAC INT_GCD_RECURRENCE THEN
  MAP_EVERY EXISTS_TAC [`&2 * &a:int`; `-- &1:int`] THEN
  REWRITE_TAC[pelly; INT_POS; INT_COPRIME_NEG; INT_COPRIME_1] THEN
  GEN_TAC THEN REWRITE_TAC[INT_OF_NUM_MUL; MULT_ASSOC] THEN
  REWRITE_TAC[INT_ARITH `a + -- &1 * b:int = a - b`] THEN
  MATCH_MP_TAC(GSYM INT_OF_NUM_SUB) THEN
  TRANS_TAC LE_TRANS `1 * pelly a (n + 1)` THEN
  REWRITE_TAC[LE_MULT_RCANCEL] THEN
  ASM_SIMP_TAC[MULT_CLAUSES; PELLY_INCREASES] THEN ASM_ARITH_TAC);;
