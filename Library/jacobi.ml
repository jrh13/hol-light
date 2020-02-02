(* ========================================================================= *)
(* Jacobi symbols for N and Z, taking in Legendre symbols as a special case. *)
(* ========================================================================= *)

needs "Library/primitive.ml";;

(* ------------------------------------------------------------------------- *)
(* Some fairly generic lemmas, but it's not quite clear where to put them.   *)
(* ------------------------------------------------------------------------- *)

let COPRIME_IPRODUCT = prove
 (`!s (a:A->int) n.
        (!i. i IN s ==> coprime(n,a i)) ==> coprime(n,iproduct s a)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\i:int. coprime(n,i)`; `a:A->int`; `s:A->bool`]
        IPRODUCT_CLOSED) THEN
  REWRITE_TAC[INT_COPRIME_1; IMP_CONJ] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONV_TAC INTEGER_RULE);;

let CONG_IPRODUCT = prove
 (`!s (a:A->int) (b:A->int) n.
        FINITE s /\
        (!i. i IN s ==> (a i == b i) (mod n))
        ==> (iproduct s a == iproduct s b) (mod n)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`\i j:int. (i == j) (mod n)`; `a:A->int`; `b:A->int`; `s:A->bool`]
   IPRODUCT_RELATED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONV_TAC INTEGER_RULE);;

(* ------------------------------------------------------------------------- *)
(* The definition over N (with the range still being Z).                     *)
(* ------------------------------------------------------------------------- *)

let jacobi = new_definition
 `(jacobi:num#num->int)(a,n) =
        if n = 0 then if a = 1 then &1 else &0
        else iproduct {p | prime p /\ p divides n}
                      (\p. (if p divides a then &0
                            else if ?x. (x EXP 2 == a) (mod p) then &1
                            else --(&1)) pow index p n)`;;

let JACOBI_BOUND = prove
 (`!a n. abs(jacobi(a,n)) <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[jacobi] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
         CONV_TAC INT_REDUCE_CONV) THEN
  ASM_SIMP_TAC[GSYM IPRODUCT_ABS; FINITE_SPECIAL_DIVISORS] THEN
  MATCH_MP_TAC IPRODUCT_LE_1 THEN
  ASM_SIMP_TAC[FINITE_SPECIAL_DIVISORS; FORALL_IN_GSPEC; INT_ABS_POS] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[INT_ABS_POW] THEN
  MATCH_MP_TAC INT_POW_1_LE THEN INT_ARITH_TAC);;

let JACOBI_CASES = prove
 (`!a n. jacobi(a,n) = -- &1 \/ jacobi(a,n) = &0 \/ jacobi(a,n) = &1`,
  MP_TAC JACOBI_BOUND THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  INT_ARITH_TAC);;

let JACOBI_PRIME = prove
 (`!a p. prime p
         ==> jacobi(a,p) =
             if p divides a then &0
             else if ?x. (x EXP 2 == a) (mod p) then &1
             else --(&1)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[jacobi; PRIME_IMP_NZ] THEN
  ONCE_REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | ~(P x ==> ~Q x)}`] THEN
  ASM_SIMP_TAC[DIVIDES_PRIME_PRIME] THEN
  REWRITE_TAC[MESON[] `~(prime q ==> ~(q = p)) <=> prime p /\ q = p`] THEN
  ASM_REWRITE_TAC[SING_GSPEC; IPRODUCT_SING; INDEX_REFL] THEN
  ASM_CASES_TAC `p <= 1` THEN ASM_REWRITE_TAC[INT_POW_1] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ASM_ARITH_TAC);;

let JACOBI = prove
 (`!a n. jacobi(a,n) =
         if n = 0 then if a = 1 then &1 else &0
         else iproduct {p | prime p /\ p divides n}
                       (\p. jacobi(a,p) pow index p n)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [jacobi] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC IPRODUCT_EQ THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
  SIMP_TAC[JACOBI_PRIME]);;

let JACOBI_ALT = prove
 (`!s a n.
        FINITE s /\
        {p | prime p /\ p divides n} SUBSET s /\
        s SUBSET {p | prime p}
        ==> jacobi(a,n) = iproduct s (\p. jacobi(a,p) pow index p n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [REWRITE_TAC[CONJ_ASSOC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o MATCH_MP FINITE_SUBSET) THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    ASM_REWRITE_TAC[GSYM INFINITE; PRIMES_INFINITE; DIVIDES_0];
    STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [JACOBI] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC IPRODUCT_SUPERSET THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
    ASM_SIMP_TAC[IN_ELIM_THM; IMP_CONJ; INDEX_ZERO; INT_POW]]);;

let JACOBI_EQ_0 = prove
 (`!a n. jacobi(a,n) = &0 <=> ~coprime(a,n)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [JACOBI] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[COPRIME_0] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV;
    ASM_SIMP_TAC[IPRODUCT_EQ_0; FINITE_SPECIAL_DIVISORS] THEN
    REWRITE_TAC[EXISTS_IN_GSPEC; INT_POW_EQ_0] THEN
    REWRITE_TAC[COPRIME_PRIME_EQ; NOT_FORALL_THM] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(p:num) divides n` THEN ASM_REWRITE_TAC[INDEX_EQ_0] THEN
    ASM_SIMP_TAC[MESON[PRIME_1] `prime p ==> ~(p = 1)`] THEN
    ASM_SIMP_TAC[JACOBI_PRIME] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    CONV_TAC INT_REDUCE_CONV]);;

let JACOBI_ZERO = prove
 (`!a b. ~coprime(a,n) ==> jacobi(a,n) = &0`,
  REWRITE_TAC[JACOBI_EQ_0]);;

let JACOBI_1 = prove
 (`(!n. jacobi(1,n) = &1) /\
   (!a. jacobi(a,1) = &1)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [JACOBI] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[INDEX_1; INT_POW; IPRODUCT_ONE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC IPRODUCT_EQ_1 THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[JACOBI_PRIME; DIVIDES_ONE] THEN
  ASM_SIMP_TAC[MESON[PRIME_1] `prime p ==> ~(p = 1)`] THEN
  SUBGOAL_THEN `?x. (x EXP 2 == 1) (mod p)`
   (fun th -> REWRITE_TAC[th; INT_POW_ONE]) THEN
  EXISTS_TAC `1` THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[CONG_REFL]);;

let JACOBI_0 = prove
 (`(!n. jacobi(0,n) = if n = 1 then &1 else &0) /\
   (!a. jacobi(a,0) = if a = 1 then &1 else &0)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[JACOBI_1] THEN
  ASM_REWRITE_TAC[JACOBI_EQ_0; COPRIME_0]);;

let JACOBI_2_CASES = prove
 (`!a. jacobi(a,2) = if ODD a then &1 else &0`,
  GEN_TAC THEN SIMP_TAC[JACOBI_PRIME; PRIME_2; DIVIDES_2; GSYM NOT_EVEN] THEN
  ASM_CASES_TAC `EVEN a` THEN ASM_REWRITE_TAC[CONG_MOD_2] THEN
  REWRITE_TAC[EVEN_EXP; ARITH_EQ] THEN REWRITE_TAC[NOT_EVEN] THEN
  MESON_TAC[ODD]);;

let JACOBI_2 = prove
 (`!a. jacobi(a,2) = &(a MOD 2)`,
  GEN_TAC THEN REWRITE_TAC[JACOBI_2_CASES; MOD_2_CASES] THEN
  REWRITE_TAC[GSYM NOT_ODD; COND_SWAP] THEN MESON_TAC[]);;

let JACOBI_EULER = prove
 (`!a p. prime p /\ ~(p = 2)
         ==> (jacobi(a,p) == &a pow ((p - 1) DIV 2)) (mod &p)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EULER_CRITERION; JACOBI_PRIME] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[INTEGER_RULE `(&0:int == a) (mod p) <=> p divides a`] THEN
    ASM_SIMP_TAC[INT_OF_NUM_POW; GSYM num_divides; PRIME_DIVEXP_EQ] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((a EXP ((p - 1) DIV 2)) EXP 2 == 1) (mod p)` MP_TAC THENL
   [MP_TAC(SPECL [`a:num`; `p:num`] FERMAT_LITTLE_PRIME) THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[COPRIME_SYM] PRIME_COPRIME_EQ] THEN
    REWRITE_TAC[EXP_EXP] THEN
    SUBGOAL_THEN `(p - 1) DIV 2 * 2 = p - 1` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM DIVIDES_DIV_MULT; DIVIDES_2; EVEN_SUB; ARITH] THEN
    ASM_MESON_TAC[PRIME_ODD; NOT_EVEN];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `1`; `a EXP ((p - 1) DIV 2)`]
    CONG_SQUARE_1_PRIME_POWER) THEN
  ASM_REWRITE_TAC[EXP_1] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `(a EXP ((p - 1) DIV 2) == 1) (mod p)` THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_POW] THEN
    ASM_MESON_TAC[CONG_SYM];
    REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LE_1; PRIME_IMP_NZ] THEN
    CONV_TAC INTEGER_RULE]);;

let JACOBI_EULER_ALT = prove
 (`!a p. prime p
         ==> (jacobi(a,p) == &a pow (if p = 2 then 1 else (p - 1) DIV 2))
             (mod &p)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[JACOBI_EULER] THEN
  DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[INT_POW_1; JACOBI_2_CASES] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM num_congruent; CONG_MOD_2_ALT] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let JACOBI_RMUL = prove
 (`!a m n. jacobi(a,m * n) = jacobi(a,m) * jacobi(a,n)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a = 1` THEN ASM_REWRITE_TAC[JACOBI_1; INT_MUL_LID] THEN
  ASM_CASES_TAC `m = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; JACOBI_0; INT_MUL_LZERO] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; JACOBI_0; INT_MUL_RZERO] THEN
  MP_TAC(SPECL [`{p | prime p /\ p divides m * n}`; `a:num`] JACOBI_ALT) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `m:num` th) THEN MP_TAC(SPEC `n:num` th)) THEN
  ASM_SIMP_TAC[FINITE_SPECIAL_DIVISORS; MULT_EQ_0] THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; DIVIDES_LMUL; DIVIDES_RMUL] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [JACOBI] THEN
  ASM_REWRITE_TAC[MULT_EQ_0] THEN
  ASM_SIMP_TAC[GSYM IPRODUCT_MUL; FINITE_SPECIAL_DIVISORS; MULT_EQ_0] THEN
  MATCH_MP_TAC IPRODUCT_EQ THEN
  REWRITE_TAC[FORALL_IN_GSPEC; GSYM INT_POW_ADD] THEN
  ASM_SIMP_TAC[INDEX_MUL]);;

let JACOBI_LMUL = prove
 (`!a b n. jacobi(a * b,n) = jacobi(a,n) * jacobi(b,n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[JACOBI_0; MULT_EQ_1] THEN
    MAP_EVERY ASM_CASES_TAC [`a = 1`; `b = 1`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV;
    ONCE_REWRITE_TAC[JACOBI] THEN ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[GSYM IPRODUCT_MUL; FINITE_SPECIAL_DIVISORS] THEN
  MATCH_MP_TAC IPRODUCT_EQ THEN
  REWRITE_TAC[FORALL_IN_GSPEC; GSYM INT_POW_MUL] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  X_GEN_TAC `p:num` THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_CASES_TAC `p = 2` THENL
   [ASM_REWRITE_TAC[JACOBI_2_CASES; ODD_MULT] THEN
    MAP_EVERY ASM_CASES_TAC [`ODD a`; `ODD b`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV;
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `&p:int` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(INT_ARITH
       `abs(x:int) <= &1 /\ abs(y) <= &1 /\ &3 <= p ==> abs(x - y) < p`) THEN
      REWRITE_TAC[INT_OF_NUM_LE; JACOBI_BOUND] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[ODD_PRIME; PRIME_ODD]] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM INT_MUL_LID] THEN
      REWRITE_TAC[INT_ABS_MUL] THEN MATCH_MP_TAC INT_LE_MUL2 THEN
      REWRITE_TAC[JACOBI_BOUND; INT_ABS_POS];
      MP_TAC(SPECL [`a * b:num`; `p:num`] JACOBI_EULER) THEN
      MP_TAC(SPECL [`b:num`; `p:num`] JACOBI_EULER) THEN
      MP_TAC(SPECL [`a:num`; `p:num`] JACOBI_EULER) THEN
      ASM_REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN MATCH_MP_TAC(INTEGER_RULE
       `(a' * b':int == c') (mod p)
        ==> (a == a') (mod p) /\ (b == b') (mod p) /\ (c == c') (mod p)
            ==> (c == a * b) (mod p)`) THEN
      REWRITE_TAC[GSYM INT_POW_MUL; GSYM INT_OF_NUM_MUL] THEN
      CONV_TAC INTEGER_RULE]]);;

let JACOBI_REXP = prove
 (`!a n k. jacobi(a,n EXP k) = jacobi(a,n) pow k`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[EXP; JACOBI_RMUL; JACOBI_1; INT_POW]);;

let JACOBI_LEXP = prove
 (`!a n k. jacobi(a EXP k,n) = jacobi(a,n) pow k`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[EXP; JACOBI_LMUL; JACOBI_1; INT_POW] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_MUL_RZERO]);;

let JACOBI_EXP_2 = prove
 (`!a k. jacobi(a,2 EXP k) = if k = 0 then &1 else &(a MOD 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[JACOBI_REXP; JACOBI_2] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_POW] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_EQ] THEN
  REWRITE_TAC[MOD_2_CASES] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[EXP_ZERO; EXP_ONE]);;

let JACOBI_EXP_2_ALT = prove
 (`!a k. jacobi(a,2 EXP k) = if k = 0 \/ ODD a then &1 else &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[JACOBI_REXP; JACOBI_2_CASES] THEN
  ASM_CASES_TAC `ODD a` THEN ASM_REWRITE_TAC[INT_POW_ONE; INT_POW_ZERO]);;

let JACOBI_CONG = prove
 (`!a b n. (a == b) (mod n) ==> jacobi(a,n) = jacobi(b,n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN ASM_SIMP_TAC[CONG_MOD_0] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[jacobi] THEN MATCH_MP_TAC IPRODUCT_EQ THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  REWRITE_TAC[NUMBER_RULE `p divides a <=> (0 == a) (mod p)`] THEN
  MP_TAC(NUMBER_RULE
   `p divides n /\ (a:num == b) (mod n) ==> (a == b) (mod p)`) THEN
  ASM_MESON_TAC[CONG_TRANS; CONG_SYM]);;

let JACOBI_MOD_GEN = prove
 (`!a m n. n divides m ==> jacobi(a MOD m,n) = jacobi(a,n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC JACOBI_CONG THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
    `(n:num) divides m ==> (x == y) (mod m) ==> (x == y) (mod n)`)) THEN
  REWRITE_TAC[CONG_LMOD; CONG_REFL]);;

let JACOBI_MOD = prove
 (`!a n. jacobi(a MOD n,n) = jacobi(a,n)`,
  SIMP_TAC[JACOBI_MOD_GEN; DIVIDES_REFL]);;

let JACOBI_SQUARED = prove
 (`(!a n. jacobi(a EXP 2,n) = if coprime(a,n) then &1 else &0) /\
   (!a n. jacobi(a,n EXP 2) = if coprime(a,n) then &1 else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_2; JACOBI_LMUL; JACOBI_RMUL] THEN
  ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN REWRITE_TAC[GSYM JACOBI_EQ_0] THEN
  MP_TAC(SPECL [`a:num`; `n:num`] JACOBI_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV);;

let JACOBI_MINUS1 = prove
 (`!n. ODD n ==> jacobi(n - 1,n) = --(&1) pow ((n - 1) DIV 2)`,
  MATCH_MP_TAC PRIME_FACTOR_INDUCT THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[JACOBI_0] THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `n:num`] THEN
  ASM_CASES_TAC `ODD n` THEN ASM_REWRITE_TAC[ODD_MULT] THEN
  ASM_CASES_TAC `p = 2` THEN ASM_REWRITE_TAC[ARITH] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[JACOBI_RMUL] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  SUBGOAL_THEN `jacobi(p * n - 1,n) = jacobi (n - 1,n)` SUBST1_TAC THENL
   [MATCH_MP_TAC JACOBI_CONG THEN MATCH_MP_TAC CONG_SUB THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [CONV_TAC NUMBER_RULE; ALL_TAC]) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `jacobi (p * n - 1,p) = --(&1) pow ((p - 1) DIV 2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `&p:int` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(INT_ARITH
       `abs(x:int) <= &1 /\ abs(y) <= &1 /\ &3 <= p ==> abs(x - y) < p`) THEN
      REWRITE_TAC[INT_OF_NUM_LE; JACOBI_BOUND] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[ODD_PRIME; PRIME_ODD]] THEN
      REWRITE_TAC[INT_ABS_POW; INT_ABS_NEG; INT_POW_ONE; INT_ABS_NUM] THEN
      REWRITE_TAC[INT_LE_REFL];
      MP_TAC(SPECL [`p * n - 1`; `p:num`] JACOBI_EULER_ALT) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      MATCH_MP_TAC INT_CONG_POW THEN
      ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LE_1; MULT_EQ_0] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN CONV_TAC INTEGER_RULE];
    REWRITE_TAC[GSYM INT_POW_ADD] THEN
    REWRITE_TAC[INT_POW_NEG; INT_POW_ONE] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REPEAT(FIRST_X_ASSUM
     (CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[ODD_EXISTS])) THEN
    REWRITE_TAC[SUC_SUB1; ADD_CLAUSES; MULT_CLAUSES] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; GSYM MULT_ASSOC] THEN
    REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n`] THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH]]);;

let JACOBI_MINUS1_CASES = prove
 (`!n. ODD n
       ==> jacobi(n - 1,n) =
           if (n == 1) (mod 4) then &1 else -- &1`,
  SIMP_TAC[JACOBI_MINUS1] THEN
  SIMP_TAC[ODD_EXISTS; ADD1; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[ARITH_RULE `((2 * n + 1) - 1) DIV 2 = n`] THEN
  SIMP_TAC[ARITH_EQ; ARITH_RULE `4 = 2 * 2`; NUMBER_RULE
   `~(t = 0) ==> ((t * n + 1 == 1) (mod (t * t)) <=> t divides n)`] THEN
  REWRITE_TAC[INT_POW_NEG; INT_POW_ONE; DIVIDES_2]);;

let JACOBI_GAUSS_LEMMA = prove
 (`!a p. prime p /\ ~(p = 2)
         ==> jacobi(a,p) =
             if coprime(a,p)
             then --(&1) pow CARD {x | x IN 1 .. (p - 1) DIV 2 /\
                                       (p - 1) DIV 2 < (a * x) MOD p}
             else &0`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[JACOBI_EQ_0] THEN
  SUBGOAL_THEN `ODD(p)` MP_TAC THENL
   [ASM_MESON_TAC[PRIME_ODD; ODD_PRIME];
    REWRITE_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `r:num` THEN REWRITE_TAC[ADD1] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `&p:int` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(INT_ARITH
       `abs(x:int) <= &1 /\ abs(y) <= &1 /\ &3 <= p ==> abs(x - y) < p`) THEN
    REWRITE_TAC[INT_OF_NUM_LE; JACOBI_BOUND] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[ODD_PRIME; PRIME_ODD]] THEN
    SIMP_TAC[INT_ABS_POW; INT_ABS_NEG; INT_POW_ONE; INT_ABS_NUM; INT_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:num`; `p:num`] JACOBI_EULER) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
  SUBGOAL_THEN `(p - 1) DIV 2 = r` SUBST1_TAC THENL
   [EXPAND_TAC "p" THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!c:int. x pow 2 = &1 /\ coprime(p,c) /\ (a * x * c == c) (mod p)
            ==> (a == x) (mod p)`) THEN
  EXISTS_TAC `iproduct (1..r) (\i. &i)` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] INT_POW_POW] THEN
    REWRITE_TAC[GSYM INT_POW_POW] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[INT_POW_ONE];
    MATCH_MP_TAC COPRIME_IPRODUCT THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; GSYM num_coprime] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
    MATCH_MP_TAC PRIME_COPRIME_LT THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
      [GSYM CARD_NUMSEG_1] THEN
    SIMP_TAC[GSYM IPRODUCT_CONST; FINITE_RESTRICT; FINITE_NUMSEG] THEN
    REWRITE_TAC[IPRODUCT_RESTRICT_SET]] THEN
  MP_TAC(ISPECL
   [`(\i. &i):num->int`;
    `(\x. if x <= r then x else p - x) o (\x. (a * x) MOD p)`;
    `1..r`] IPRODUCT_INJECTION) THEN
  REWRITE_TAC[o_THM; FINITE_NUMSEG] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THENL
       [ALL_TAC; EXPAND_TAC "p" THEN ARITH_TAC] THEN
      REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`] THEN COND_CASES_TAC THENL
       [ALL_TAC; ASM_MESON_TAC[DIVISION; NOT_LE; SUB_EQ_0; PRIME_0]] THEN
      ASM_SIMP_TAC[GSYM DIVIDES_MOD; PRIME_IMP_NZ] THEN
      ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN STRIP_TAC THENL
       [ASM_MESON_TAC[coprime; DIVIDES_REFL; PRIME_1];
        ASM_MESON_TAC[DIVIDES_LE; ARITH_RULE `~(1 <= 0)`;
                      ARITH_RULE `~(2 * r + 1 <= i /\ i <= r)`]];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN REWRITE_TAC[IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN
      EXISTS_TAC `p:num` THEN REPEAT(CONJ_TAC THENL
       [ASM_MESON_TAC[ARITH_RULE `i <= r ==> i < 2 * r + 1`] ; ALL_TAC]) THEN
      MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `a:num` THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `(if a then x else p - x) = (if b then y else p - y) ==> x < p /\ y < p
        ==> x:num = y \/ x + y = p`)) THEN
      ASM_SIMP_TAC[MOD_LT_EQ; PRIME_IMP_NZ] THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
       [ASM_MESON_TAC[CONG]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o C AP_THM `p:num` o AP_TERM `(MOD)`) THEN
      ASM_SIMP_TAC[MOD_ADD_MOD] THEN ASM_SIMP_TAC[GSYM CONG] THEN
      DISCH_THEN(MP_TAC o MATCH_MP CONG_DIVIDES) THEN
      ASM_SIMP_TAC[GSYM LEFT_ADD_DISTRIB; PRIME_DIVPROD_EQ; DIVIDES_REFL] THEN
      STRIP_TAC THENL
       [ASM_MESON_TAC[coprime; DIVIDES_REFL; PRIME_1]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> ~(i + j = 0)`] THEN
      MAP_EVERY UNDISCH_TAC [`i:num <= r`; `j:num <= r`; `2 * r + 1 = p`] THEN
      ARITH_TAC];
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV) [GSYM th])] THEN
  SIMP_TAC[GSYM IPRODUCT_MUL; FINITE_NUMSEG; o_DEF] THEN
  MATCH_MP_TAC CONG_IPRODUCT THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[COND_SWAP; GSYM NOT_LE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; MOD_LT_EQ; PRIME_IMP_NZ; INT_OF_NUM_EQ;
               LT_IMP_LE; INT_MUL_LID; INT_MUL_LNEG; INT_MUL_RNEG] THEN
  REWRITE_TAC[INTEGER_RULE `(--x:int == p - a) (mod p) <=> (x == a) (mod p)`;
              GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_MUL] THEN
  REWRITE_TAC[INT_CONG_RREM; INT_CONG_REFL]);;

let JACOBI_OF_2 = prove
 (`!n. jacobi(2,n) = if EVEN n then &0 else --(&1) pow ((n EXP 2 - 1) DIV 8)`,
  let lemma0 = prove
   (`!n. ODD n ==> 8 divides (n EXP 2 - 1)`,
    GEN_TAC THEN REWRITE_TAC[ODD_EXISTS; ADD1; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `m:num` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ARITH_RULE `(2 * n + 1) EXP 2 - 1 = 4 * (n EXP 2 + n)`] THEN
    REWRITE_TAC[ARITH_RULE `8 = 4 * 2`] THEN MATCH_MP_TAC DIVIDES_MUL_L THEN
    REWRITE_TAC[DIVIDES_2; EVEN_ADD; EVEN_EXP; ARITH_EQ]) in
  let lemma1 = prove
   (`!m n. ODD m /\ ODD n
           ==> (EVEN(((m * n) EXP 2 - 1) DIV 8) <=>
                EVEN((m EXP 2 - 1) DIV 8 + (n EXP 2 - 1) DIV 8))`,
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM DIV_ADD; lemma0; GSYM DIVIDES_2] THEN
    ASM_SIMP_TAC[DIVIDES_DIVIDES_DIV; lemma0; ODD_MULT; DIVIDES_ADD] THEN
    SUBGOAL_THEN
     `(m * n) EXP 2 - 1 =
      (m EXP 2 - 1) * (n EXP 2 - 1) + (m EXP 2 - 1) + (n EXP 2 - 1)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD;
                   GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_SUB; LE_1;
                   MULT_EQ_0; EXP_2; MESON[ODD] `ODD n ==> ~(n = 0)`] THEN
      INT_ARITH_TAC;
      MATCH_MP_TAC(NUMBER_RULE
       `(d:num) divides a ==> (d divides (a + b) <=> d divides b)`) THEN
      MATCH_MP_TAC(NUMBER_RULE
       `e divides d /\ d divides a /\ d divides b
        ==> d * e divides a * b`) THEN
      ASM_SIMP_TAC[lemma0] THEN REWRITE_TAC[DIVIDES_2; ARITH]]) in
  GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[JACOBI_EQ_0; COPRIME_2; GSYM NOT_EVEN];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EVEN])] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN  MATCH_MP_TAC PRIME_FACTOR_INDUCT THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[JACOBI_1] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `n:num`] THEN
  ASM_CASES_TAC `ODD n` THEN ASM_REWRITE_TAC[ODD_MULT] THEN
  ASM_CASES_TAC `p = 2` THEN ASM_REWRITE_TAC[ARITH] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[JACOBI_RMUL] THEN
  ASM_SIMP_TAC[JACOBI_GAUSS_LEMMA; COPRIME_2; IN_NUMSEG] THEN
  ONCE_REWRITE_TAC[TAUT `(p /\ q) /\ r <=> ~(p /\ q ==> ~r)`] THEN
  ASM_SIMP_TAC[PRIME_IMP_NZ; MOD_LT; ARITH_RULE
   `1 <= x /\ x <= (p - 1) DIV 2 ==> 2 * x < p`] THEN
  REWRITE_TAC[NOT_IMP; ARITH_RULE
   `(1 <= x /\ x <= b) /\ c < 2 * x <=> c DIV 2 + 1 <= x /\ x <= b`] THEN
  REWRITE_TAC[GSYM numseg; CARD_NUMSEG] THEN
  REWRITE_TAC[GSYM INT_POW_ADD] THEN REWRITE_TAC[INT_POW_NEG; INT_POW_ONE] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[EVEN_ADD; lemma1] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `(n + 1) - (n DIV 2 + 1) = n DIV 2 + n MOD 2`] THEN
  UNDISCH_TAC `ODD p` THEN
  REWRITE_TAC[ODD_EXISTS; ADD1; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `t:num` THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[ADD_SUB; DIV_MULT; ARITH_EQ] THEN
  REWRITE_TAC[ARITH_RULE
   `((2 * n + 1) EXP 2 - 1) DIV 8 = (n EXP 2 + n) DIV 2`] THEN
  MP_TAC(SPEC `t:num` (REWRITE_RULE[EVEN_EXISTS; ODD_EXISTS] EVEN_OR_ODD)) THEN
  REWRITE_TAC[ADD1; OR_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ; DIV_MULT; MOD_MULT] THEN
  REWRITE_TAC[ARITH_RULE `((2 * q) EXP 2) DIV 2 = 2 * q * q`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH] THEN
  REWRITE_TAC[ARITH_RULE
   `((2 * q + 1) EXP 2 + 2 * q + 1) DIV 2 =
    2 * q EXP 2 + 3 * q + 1`] THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; EVEN_EXP; ARITH]);;

let JACOBI_OF_2_CASES = prove
 (`!n. jacobi(2,n) =
       if EVEN n then &0
       else if (n == 1) (mod 8) \/ (n == 7) (mod 8) then &1 else --(&1)`,
  GEN_TAC THEN REWRITE_TAC[JACOBI_OF_2] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EVEN]) THEN
  SIMP_TAC[ODD_EXISTS; ADD1; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[ARITH_RULE
   `((2 * m + 1) EXP 2 - 1) DIV 8 = (m * (m + 1)) DIV 2`] THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NUMBER_RULE `(n + 1 == 1) (mod p) <=> (n == 0) (mod p)`] THEN
  REWRITE_TAC[NUMBER_RULE `(n + 1 == 7) (mod p) <=> (n == 6) (mod p)`] THEN
  REWRITE_TAC[INT_POW_NEG; INT_POW_ONE] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPEC `m:num`
   (REWRITE_RULE[EVEN_EXISTS; ODD_EXISTS; ADD1] EVEN_OR_ODD)) THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `p:num` SUBST1_TAC)) THENL
   [REWRITE_TAC[ARITH_RULE `((2 * p) * (2 * p + 1)) DIV 2 = p * (2 * p + 1)`];
    REWRITE_TAC[ARITH_RULE `((2 * p + 1) * ((2 * p + 1) + 1)) DIV 2 =
                            (p + 1) * (2 * p + 1)`]] THEN
  MP_TAC(GEN `n:num` (SPECL [`2`; `n:num`; `4`] DIVIDES_LMUL2_EQ)) THEN
  REWRITE_TAC[GSYM DIVIDES_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[DIVIDES_MOD; CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (W(fun(asl,w) -> SUBGOAL_THEN (subst [`p MOD 8`,`p:num`] w) MP_TAC) THENL
   [ALL_TAC;
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL [ALL_TAC; BINOP_TAC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM CONG] THEN
    REPEAT(MATCH_MP_TAC CONG_ADD ORELSE MATCH_MP_TAC CONG_MULT THEN
           REPEAT CONJ_TAC THEN REWRITE_TAC[CONG_REFL; CONG_LMOD])]) THEN
  MP_TAC(ARITH_RULE `p MOD 8 < 8`) THEN SPEC_TAC(`p MOD 8`,`k:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let JACOBI_RECIPROCITY_ALT = prove
 (`!m n. ODD m /\ ODD n
         ==> jacobi(m,n) * jacobi(n,m) =
             if coprime(m,n) then --(&1) pow ((m - 1) DIV 2 * (n - 1) DIV 2)
             else &0`,
  let lemma0 = prove
   (`!n. ODD n ==> 2 divides (n - 1)`,
    SIMP_TAC[DIVIDES_2; EVEN_SUB; GSYM NOT_EVEN; ARITH]) in
  let lemma1 = prove
   (`!m n. ODD m /\ ODD n
           ==> (EVEN((m * n - 1) DIV 2) <=>
                EVEN((m - 1) DIV 2 + (n - 1) DIV 2))`,
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM DIV_ADD; DIVIDES_2; lemma0] THEN
    ASM_SIMP_TAC[DIVIDES_DIVIDES_DIV; GSYM DIVIDES_2;
                 ODD_MULT; DIVIDES_ADD; lemma0] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `d divides a * b /\ a * b + a + b = c
      ==> (d divides c <=> d divides (a + b))`) THEN
    ASM_SIMP_TAC[DIVIDES_MUL2; lemma0] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS])) THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[SUC_SUB1; MULT_CLAUSES; ADD_CLAUSES] THEN ARITH_TAC) in
  let flemma = prove
   (`!r s p. FINITE {x,y | x IN 1..r /\ y IN 1..s /\ p x y}`,
    REPEAT GEN_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `(1..r) CROSS (1..s)` THEN
    REWRITE_TAC[FINITE_CROSS_EQ; FINITE_NUMSEG] THEN
    SIMP_TAC[SUBSET; FORALL_IN_GSPEC; IN_CROSS]) in
  let glemma = prove
   (`!p q r s. prime p /\ prime q /\ coprime(p,q) /\
               2 * r + 1 = p /\ 2 * s + 1 = q
               ==> jacobi(q,p) =
                   -- &1 pow CARD {x,y | x IN 1..r /\ y IN 1..s /\
                                         q * x < p * y /\ p * y <= q * x + r}`,
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`q:num`; `p:num`] JACOBI_GAUSS_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [EXPAND_TAC "p" THEN DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
      REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH];
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC] THEN
    SUBGOAL_THEN `(p - 1) DIV 2 = r` SUBST1_TAC THENL
     [EXPAND_TAC "p" THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `CARD {x,y | x IN 1..r /\ y IN 1..s /\
                  y = (q * x) DIV p + 1 /\ r < (q * x) MOD p}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN EXISTS_TAC `\(x:num,y:num). x` THEN
      REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_UNIQUE_THM; IN_NUMSEG; flemma;
                  IMP_CONJ; RIGHT_FORALL_IMP_THM; EXISTS_IN_GSPEC] THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `x:num` THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
      SIMP_TAC[PAIR_EQ] THEN EXISTS_TAC `x:num` THEN
      EXISTS_TAC `(q * x) DIV p + 1` THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= n + 1`] THEN
      SUBGOAL_THEN `p * (q * x) DIV p + r < q * r` MP_TAC THENL
       [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `q * x:num` THEN
        ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
        ASM_MESON_TAC[PRIME_IMP_NZ; LT_ADD_LCANCEL; DIVISION];
        MAP_EVERY EXPAND_TAC ["p"; "q"] THEN DISCH_THEN(MP_TAC o MATCH_MP
         (ARITH_RULE `(2 * r + 1) * d + r < (2 * s + 1) * r
                      ==> (2 * r) * d < (2 * r) * s`)) THEN
        SIMP_TAC[LT_MULT_LCANCEL; ARITH_RULE `x < y ==> x + 1 <= y`]];
      AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_PAIR_THM; FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN EQ_TAC THEN DISCH_TAC THENL
       [MP_TAC(MATCH_MP PRIME_IMP_NZ (ASSUME `prime p`)) THEN
        DISCH_THEN(MP_TAC o SPEC `q * x:num` o MATCH_MP DIVISION) THEN
        FIRST_ASSUM(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
        UNDISCH_TAC `2 * r + 1 = p` THEN ARITH_TAC;
        MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
         [ALL_TAC;
          DISCH_THEN SUBST_ALL_TAC THEN
          MATCH_MP_TAC(ARITH_RULE
           `!p d. 2 * r + 1 = p /\ p * (d + 1) <= (d * p + m) + r
                  ==> r < m`) THEN
          MAP_EVERY EXISTS_TAC [`p:num`; `(q * x) DIV p`] THEN
          ASM_MESON_TAC[DIVISION; PRIME_IMP_NZ]] THEN
        MATCH_MP_TAC(ARITH_RULE
         `~(x <= y) /\ ~(y + 2 <= x) ==> x = y + 1`) THEN
        REPEAT STRIP_TAC THENL
         [SUBGOAL_THEN `y * p <= ((q * x) DIV p) * p` MP_TAC THENL
           [ASM_SIMP_TAC[LE_MULT_RCANCEL; PRIME_IMP_NZ]; ALL_TAC];
          SUBGOAL_THEN `((q * x) DIV p + 2) * p <= y * p` MP_TAC THENL
           [ASM_SIMP_TAC[LE_MULT_RCANCEL; PRIME_IMP_NZ]; ALL_TAC]] THEN
        MP_TAC(MATCH_MP PRIME_IMP_NZ (ASSUME `prime p`)) THEN
        DISCH_THEN(MP_TAC o SPEC `q * x:num` o MATCH_MP DIVISION) THEN
        ASM_ARITH_TAC]]) in
  let hlemma = prove
   (`!p q r s. prime p /\ prime q /\ coprime(p,q) /\
               2 * r + 1 = p /\ 2 * s + 1 = q
               ==> jacobi(p,q) =
                   -- &1 pow CARD {x,y | x IN 1..r /\ y IN 1..s /\
                                         p * y < q * x /\ q * x <= p * y + s}`,
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`q:num`; `p:num`; `s:num`; `r:num`] glemma) THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN
    EXISTS_TAC `\(x:num,y:num). (y,x)` THEN REWRITE_TAC[flemma] THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM; FORALL_PAIR_THM; EXISTS_PAIR_THM] THEN
    SIMP_TAC[IN_ELIM_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]) in
  let rlemma = prove
   (`!a b c d r s.
          a UNION b UNION c UNION d = (1..r) CROSS (1..s) /\
          PAIRWISE DISJOINT [a;b;c;d] /\ CARD b = CARD c
          ==> ((EVEN(CARD a) <=> EVEN(CARD d)) <=> ~(ODD r /\ ODD s))`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `CARD(a:num#num->bool) + CARD(b:num#num->bool) +
                  CARD(c:num#num->bool) + CARD(d:num#num->bool) = r * s`
     (fun th -> MP_TAC(AP_TERM `EVEN` th) THEN
                ASM_REWRITE_TAC[EVEN_ADD; GSYM NOT_EVEN; EVEN_MULT] THEN
                CONV_TAC TAUT) THEN
    SUBGOAL_THEN
     `FINITE(a:num#num->bool) /\ FINITE(b:num#num->bool) /\
      FINITE(c:num#num->bool) /\ FINITE(d:num#num->bool)`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM FINITE_UNION] THEN
      REWRITE_TAC[FINITE_CROSS_EQ; FINITE_NUMSEG];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `CARD:(num#num->bool)->num`) THEN
    SIMP_TAC[CARD_CROSS; CARD_NUMSEG_1; FINITE_NUMSEG] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PAIRWISE]) THEN
    REWRITE_TAC[PAIRWISE; DISJOINT; ALL] THEN
    ASM_SIMP_TAC[CARD_UNION; FINITE_UNION; SET_RULE
      `a INTER (b UNION c) = {} <=> a INTER b = {} /\ a INTER c = {}`]) in
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[INT_ENTIRE; JACOBI_EQ_0] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM IMP_CONJ_ALT; GSYM CONJ_ASSOC] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`n:num`; `m:num`] THEN
  MATCH_MP_TAC COMPLETE_FACTOR_INDUCT THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[COPRIME_1; JACOBI_1; MULT_CLAUSES; ODD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
    X_GEN_TAC `p:num` THEN DISCH_TAC;
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    REWRITE_TAC[COPRIME_LMUL; COPRIME_RMUL; ODD_MULT;
                JACOBI_LMUL; JACOBI_RMUL] THEN
    ONCE_REWRITE_TAC[INT_ARITH
     `(a * b) * (c * d):int = (a * c) * (b * d)`] THEN
    SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN REWRITE_TAC[GSYM INT_POW_POW] THEN
    REWRITE_TAC[GSYM INT_POW_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM INT_POW_ADD] THEN
    REWRITE_TAC[INT_POW_NEG; INT_POW_ONE] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[lemma1]] THEN
  MATCH_MP_TAC COMPLETE_FACTOR_INDUCT THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[COPRIME_1; JACOBI_1; MULT_CLAUSES; ODD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN STRIP_TAC;
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    REWRITE_TAC[COPRIME_LMUL; COPRIME_RMUL; ODD_MULT;
                JACOBI_LMUL; JACOBI_RMUL] THEN
    ONCE_REWRITE_TAC[INT_ARITH
     `(a * b) * (c * d):int = (a * c) * (b * d)`] THEN
    SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM INT_POW_POW] THEN
    REWRITE_TAC[GSYM INT_POW_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM INT_POW_ADD] THEN
    REWRITE_TAC[INT_POW_NEG; INT_POW_ONE] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[lemma1]] THEN
  MAP_EVERY UNDISCH_TAC [`ODD q`; `ODD p`] THEN
  REWRITE_TAC[ODD_EXISTS; ADD1; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:num` THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  X_GEN_TAC `s:num` THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `r:num`; `s:num`] glemma) THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `r:num`; `s:num`] hlemma) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN `(p - 1) DIV 2 = r /\ (q - 1) DIV 2 = s`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["p"; "q"] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_POW_ADD] THEN
  REWRITE_TAC[INT_POW_NEG; INT_POW_ONE] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM NOT_ODD] THEN
  REWRITE_TAC[EVEN_ADD; ODD_MULT] THEN
  MATCH_MP_TAC rlemma THEN
  EXISTS_TAC `{x,y | x IN 1..r /\ y IN 1..s /\ q * x + r < p * y}` THEN
  EXISTS_TAC `{x,y | x IN 1..r /\ y IN 1..s /\ p * y + s < q * x}` THEN
  REPEAT CONJ_TAC THEN
  REWRITE_TAC[PAIRWISE; DISJOINT; EXTENSION; NOT_IN_EMPTY; FORALL_PAIR_THM;
              ALL; IN_UNION; IN_CROSS; IN_ELIM_PAIR_THM; IN_INTER]
  THENL
   [MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    MAP_EVERY ASM_CASES_TAC [`x IN 1..r`; `y IN 1..s`] THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `~(q * x:num = p * y)`
     (fun th -> MP_TAC th THEN ARITH_TAC) THEN
    DISCH_THEN(MP_TAC o AP_TERM `(divides) (p:num)`) THEN
    ASM_SIMP_TAC[PRIME_DIVPROD_EQ; DIVIDES_REFL] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[DIVIDES_REFL; PRIME_1; coprime]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    UNDISCH_TAC `x IN 1..r` THEN REWRITE_TAC[IN_NUMSEG] THEN
    EXPAND_TAC "p" THEN ARITH_TAC;
    ARITH_TAC;
    MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
    REPEAT(EXISTS_TAC `\(x,y). (r + 1) - x,(s + 1) - y`) THEN
    REWRITE_TAC[flemma] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_NUMSEG; PAIR_EQ] THEN
    CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    SIMP_TAC[ARITH_RULE `x <= y ==> (y + 1) - ((y + 1) - x) = x`] THEN
    SIMP_TAC[ARITH_RULE
     `1 <= x /\ x <= y ==> 1 <= (y + 1) - x /\ (y + 1) - x <= y`] THEN
    REWRITE_TAC[LEFT_SUB_DISTRIB] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE
     `x:num <= y /\ v + y + z < x + u ==> (y - x) + z < u - v`) THEN
    ASM_SIMP_TAC[LE_MULT_LCANCEL; ARITH_RULE `x <= r ==> x <= r + 1`] THEN
    REWRITE_TAC[ARITH_RULE `a + x:num < y + a <=> x < y`] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
    ASM_ARITH_TAC]);;

let JACOBI_RECIPROCITY = prove
 (`!m n. ODD m /\ ODD n
         ==> jacobi(n,m) =
             if coprime(m,n)
             then --(&1) pow ((m - 1) DIV 2 * (n - 1) DIV 2) * jacobi(m,n)
             else &0`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[JACOBI_EQ_0; COPRIME_SYM]] THEN
  MATCH_MP_TAC(INT_RING
   `!x y:int.
        x pow 2 = &1 /\ y pow 2 = &1 /\ x * y = z
        ==> y = z * x`) THEN
  ASM_SIMP_TAC[JACOBI_RECIPROCITY_ALT] THEN CONJ_TAC THEN
  MATCH_MP_TAC(INT_RING
   `(x:int = -- &1 \/ x = &0 \/ x = &1) /\ ~(x = &0) ==> x pow 2 = &1`) THEN
  REWRITE_TAC[JACOBI_CASES] THEN ASM_REWRITE_TAC[JACOBI_EQ_0] THEN
  ASM_MESON_TAC[ODD; COPRIME_SYM]);;

let JACOBI_EQ_1 = prove
 (`!n a. coprime(a,n) /\ (?x. (x EXP 2 == a) (mod n))
         ==> jacobi(a,n) = &1`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[COPRIME_0; JACOBI_1] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[jacobi] THEN MATCH_MP_TAC IPRODUCT_EQ_1 THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[INT_POW_ONE] `x:int = &1 ==> x pow n = &1`) THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[COPRIME_PRIME_EQ]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[NUMBER_RULE
   `(a == b) (mod m) /\ n divides m ==> (a == b) (mod n)`]);;

let JACOBI_NE_MINUS1 = prove
 (`!n a. (?x. (x EXP 2 == a) (mod n)) ==> ~(jacobi(a,n) = -- &1)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `coprime(a:num,n)` THEN
  ASM_SIMP_TAC[JACOBI_ZERO; JACOBI_EQ_1] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Integer version. The totalization at zero is a bit blunter; it's hard to  *)
(* keep all the nice properties in the light of -1 * -1 = 1; we prioritize   *)
(* simple complete multiplicativity over the relation with coprimality.      *)
(* ------------------------------------------------------------------------- *)

let int_jacobi = new_definition
 `int_jacobi(a,n) =
        if n = &0 then &0
        else jacobi(num_of_int(a rem n),num_of_int(abs n))`;;

let INT_JACOBI_RNEG = prove
 (`!a n. int_jacobi(a,--n) = int_jacobi(a,n)`,
  REWRITE_TAC[int_jacobi; INT_ABS_NEG; INT_NEG_EQ_0; INT_REM_RNEG]);;

let INT_JACOBI_RABS = prove
 (`!a n. int_jacobi(a,abs n) = int_jacobi(a,n)`,
  REWRITE_TAC[int_jacobi; INT_ABS_ABS; INT_REM_RABS; INT_ABS_ZERO]);;

let INT_JACOBI_NUMS = prove
 (`!a n. int_jacobi(&a,&n) = if n = 0 /\ a = 1 then &0 else jacobi(a,n)`,
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC [`n = 0`; `a = 1`] THEN
  ASM_REWRITE_TAC[int_jacobi; JACOBI_0; JACOBI_1; INT_OF_NUM_EQ] THEN
  REWRITE_TAC[int_jacobi; INT_ABS_NUM; INT_OF_NUM_REM; NUM_OF_INT_OF_NUM] THEN
  ASM_REWRITE_TAC[INT_OF_NUM_EQ; JACOBI_0; MOD_ZERO; JACOBI_MOD; JACOBI_1]);;

let INT_JACOBI_BOUND = prove
 (`!a n. abs(int_jacobi(a,n)) <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_jacobi] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[JACOBI_BOUND]) THEN
  CONV_TAC INT_REDUCE_CONV);;

let INT_JACOBI_CASES = prove
 (`!a n. int_jacobi(a,n) = -- &1 \/
         int_jacobi(a,n) = &0 \/
         int_jacobi(a,n) = &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_jacobi] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[JACOBI_CASES]) THEN
  CONV_TAC INT_REDUCE_CONV);;

let INT_JACOBI_CONG = prove
 (`!a b n. (a == b) (mod n) ==> int_jacobi(a,n) = int_jacobi(b,n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_jacobi] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[INT_CONG_MOD_0] THEN
  SIMP_TAC[GSYM INT_REM_EQ]);;

let INT_JACOBI_REM_GEN = prove
 (`!a m n. n divides m ==> int_jacobi(a rem m,n) = int_jacobi(a,n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_JACOBI_CONG THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
    `(n:int) divides m ==> (x == y) (mod m) ==> (x == y) (mod n)`)) THEN
  REWRITE_TAC[INT_CONG_LREM; INT_CONG_REFL]);;

let INT_JACOBI_REM = prove
 (`!a n. int_jacobi(a rem n,n) = int_jacobi(a,n)`,
  SIMP_TAC[INT_JACOBI_REM_GEN; INT_DIVIDES_REFL]);;

let INT_JACOBI_1 = prove
 (`(!n. int_jacobi(&1,n) = if n = &0 then &0 else &1) /\
   (!a. int_jacobi(a,&1) = &1)`,
  REWRITE_TAC[int_jacobi] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; JACOBI_1] THEN
  X_GEN_TAC `n:int` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `abs(n:int) = &1` THEN
  ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM; JACOBI_1] THEN
  SUBGOAL_THEN `&1 rem n = &1` SUBST1_TAC THENL
   [REWRITE_TAC[INT_REM_EQ_SELF] THEN ASM_INT_ARITH_TAC;
    REWRITE_TAC[NUM_OF_INT_OF_NUM; JACOBI_1] THEN
    SIMP_TAC[GSYM INT_OF_NUM_EQ; INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
    ASM_REWRITE_TAC[INT_ABS_ZERO]]);;

let INT_JACOBI_0 = prove
 (`(!n. int_jacobi(&0,n) = if abs n = &1 then &1 else &0) /\
   (!a. int_jacobi(a,&0) = &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[int_jacobi] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_REM_ZERO] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; JACOBI_0] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  SIMP_TAC[GSYM INT_OF_NUM_EQ; INT_OF_NUM_OF_INT; INT_ABS_POS]);;

let INT_JACOBI_RMUL = prove
 (`!a m n. int_jacobi(a,m * n) = int_jacobi(a,m) * int_jacobi(a,n)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `m:int = &0` THEN
  ASM_REWRITE_TAC[INT_JACOBI_0; INT_MUL_LZERO] THEN
  ASM_CASES_TAC `n:int = &0` THEN
  ASM_REWRITE_TAC[INT_JACOBI_0; INT_MUL_RZERO] THEN
  ASM_REWRITE_TAC[int_jacobi; INT_ENTIRE; INT_ABS_MUL] THEN
  SIMP_TAC[NUM_OF_INT_MUL; INT_ABS_POS; JACOBI_RMUL] THEN
  BINOP_TAC THEN MATCH_MP_TAC JACOBI_CONG THEN REWRITE_TAC[num_congruent] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS; INT_DIVISION; INT_ENTIRE] THEN
  REWRITE_TAC[INT_CONG_MOD_ABS] THEN REWRITE_TAC[GSYM INT_REM_EQ] THEN
  REWRITE_TAC[INT_REM_REM_MUL; INT_REM_REM]);;

let INT_JACOBI_LMUL = prove
 (`!a b n. int_jacobi(a * b,n) = int_jacobi(a,n) * int_jacobi(b,n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n:int = &0` THEN
  ASM_REWRITE_TAC[INT_JACOBI_0; INT_MUL_LZERO] THEN
  ASM_REWRITE_TAC[int_jacobi; GSYM JACOBI_LMUL] THEN
  MATCH_MP_TAC JACOBI_CONG THEN REWRITE_TAC[num_congruent] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_LE_MUL; INT_DIVISION; INT_ABS_POS;
               GSYM INT_OF_NUM_MUL; INT_CONG_MOD_ABS] THEN
  REWRITE_TAC[GSYM INT_REM_EQ; INT_REM_REM; INT_MUL_REM]);;

let INT_JACOBI_RPOW = prove
 (`!a n k. int_jacobi(a,n pow k) = int_jacobi(a,n) pow k`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[INT_JACOBI_RMUL; INT_JACOBI_1; INT_POW]);;

let INT_JACOBI_LPOW = prove
 (`!a n k. int_jacobi(a pow k,n) =
           if n = &0 then &0 else int_jacobi(a,n) pow k`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[INT_JACOBI_LMUL; INT_JACOBI_1; INT_POW] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_MUL_RZERO]);;

let INT_JACOBI_2 = prove
 (`!a. int_jacobi(a,&2) = a rem &2`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_JACOBI_REM] THEN
  MP_TAC(SPEC `a:int` INT_REM_2_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[INT_JACOBI_NUMS; JACOBI_2_CASES] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let INT_JACOBI_POW_2 = prove
 (`!a k. int_jacobi(a,&2 pow k) = if k = 0 then &1 else a rem &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_JACOBI_RPOW; INT_JACOBI_2] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_POW] THEN
  MP_TAC(SPEC `a:int` INT_REM_2_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[INT_POW_ZERO; INT_POW_ONE]);;

let INT_JACOBI_EQ_0 = prove
 (`!a n. int_jacobi(a,n) = &0 <=> coprime(a,n) ==> n = &0`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n:int = &0` THEN ASM_REWRITE_TAC[INT_JACOBI_0] THEN
  ONCE_REWRITE_TAC[GSYM INT_JACOBI_RABS; GSYM INT_COPRIME_RABS] THEN
  ONCE_REWRITE_TAC[GSYM INT_COPRIME_LREM; GSYM INT_JACOBI_REM] THEN
  SUBGOAL_THEN `&0 <= a rem abs n` MP_TAC THENL
   [ASM_SIMP_TAC[INT_DIVISION; INT_ABS_ZERO];
    SPEC_TAC(`a rem abs n`,`x:int`)] THEN
  SUBGOAL_THEN `&0 <= abs(n:int) /\ ~(abs n = &0)` MP_TAC THENL
   [ASM_INT_ARITH_TAC; REWRITE_TAC[IMP_CONJ]] THEN
  SPEC_TAC(`abs n:int`,`y:int`) THEN
  REWRITE_TAC[GSYM INT_FORALL_POS] THEN
  SIMP_TAC[INT_OF_NUM_EQ; INT_JACOBI_NUMS; GSYM num_coprime] THEN
  SIMP_TAC[JACOBI_EQ_0]);;

let INT_JACOBI_MINUS1 = prove
 (`!n. ~(&2 divides n)
       ==> int_jacobi(--(&1),n) =
           if (abs n == &1) (mod &4) then &1 else -- &1`,
  ONCE_REWRITE_TAC[GSYM INT_JACOBI_RABS; GSYM INT_DIVIDES_RABS] THEN
  REWRITE_TAC[GSYM INT_FORALL_ABS; GSYM num_divides; GSYM num_congruent] THEN
  SIMP_TAC[DIVIDES_2; NOT_EVEN; GSYM JACOBI_MINUS1_CASES] THEN
  X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ODD] THEN DISCH_TAC THEN
  TRANS_TAC EQ_TRANS `int_jacobi(&n - &1,&n)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INT_JACOBI_CONG THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INT_OF_NUM_EQ; INT_OF_NUM_SUB; LE_1; INT_JACOBI_NUMS]]);;

let INT_JACOBI_OF_2 = prove
 (`!n. int_jacobi(&2,n) =
       if &2 divides n then &0
       else if (abs n == &1) (mod &8) \/ (abs n == &7) (mod &8) then &1
       else --(&1)`,
  ONCE_REWRITE_TAC[GSYM INT_JACOBI_RABS; GSYM INT_DIVIDES_RABS] THEN
  REWRITE_TAC[GSYM INT_FORALL_ABS; GSYM num_divides; GSYM num_congruent] THEN
  REWRITE_TAC[DIVIDES_2; GSYM JACOBI_OF_2_CASES] THEN
  SIMP_TAC[INT_JACOBI_NUMS] THEN CONV_TAC NUM_REDUCE_CONV);;

let INT_JACOBI_LNEG = prove
 (`!n. ~(&2 divides n)
       ==> int_jacobi(--a,n) =
           if (abs n == &1) (mod &4) then int_jacobi(a,n)
           else --(int_jacobi(a,n))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[INT_NEG_MINUS1] THEN
  ASM_SIMP_TAC[INT_JACOBI_LMUL; INT_JACOBI_MINUS1] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let INT_JACOBI_SQUARED = prove
 (`(!a n. int_jacobi(a pow 2,n) =
          if coprime(a,n) /\ ~(n = &0) then &1 else &0) /\
   (!a n. int_jacobi(a,n pow 2) =
          if coprime(a,n) /\ ~(n = &0) then &1 else &0)`,
  REWRITE_TAC[INT_JACOBI_LPOW; INT_JACOBI_RPOW] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n:int = &0` THEN
  ASM_REWRITE_TAC[INT_JACOBI_EQ_0; INT_POW_EQ_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `coprime(a:int,n)` THEN
  ASM_REWRITE_TAC[INT_JACOBI_EQ_0; INT_POW_EQ_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC(INT_RING
   `(x:int = -- &1 \/ x = &0 \/ x = &1) /\ ~(x = &0) ==> x pow 2 = &1`) THEN
  REWRITE_TAC[INT_JACOBI_CASES] THEN ASM_REWRITE_TAC[INT_JACOBI_EQ_0]);;
