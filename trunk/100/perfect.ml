(* ========================================================================= *)
(* Perfect number theorems.                                                  *)
(* ========================================================================= *)

needs "Library/prime.ml";;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The sum-of-divisors function.                                             *)
(* ------------------------------------------------------------------------- *)

let sigma = new_definition
 `sigma(n) = if n = 0 then 0 else nsum {d | d divides n} (\i. i)`;;

(* ------------------------------------------------------------------------- *)
(* Definition of perfection.                                                 *)
(* ------------------------------------------------------------------------- *)

let perfect = new_definition
 `perfect n <=> ~(n = 0) /\ sigma(n) = 2 * n`;;

(* ------------------------------------------------------------------------- *)
(* Various number-theoretic lemmas.                                          *)
(* ------------------------------------------------------------------------- *)

let ODD_POW2_MINUS1 = prove
 (`!k. ~(k = 0) ==> ODD(2 EXP k - 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `EVEN(2 EXP k) <=> EVEN((2 EXP k - 1) + 1)` MP_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `k = k - 1 + 1 <=> ~(k = 0)`] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH];
    ASM_REWRITE_TAC[GSYM NOT_EVEN; EVEN_ADD; EVEN_EXP; ARITH]]);;

let EVEN_ODD_DECOMP = prove
 (`!n. ~(n = 0) ==> ?r s. ODD s /\ n = 2 EXP r * s`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  MP_TAC(SPEC `n:num` EVEN_OR_ODD) THEN
  REWRITE_TAC[EVEN_EXISTS; ODD_EXISTS] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC)) THENL
   [DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
    REWRITE_TAC[MULT_EQ_0; ARITH; ARITH_RULE `m < 2 * m <=> ~(m = 0)`] THEN
    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `s:num` THEN DISCH_THEN(X_CHOOSE_TAC `r:num`) THEN
    EXISTS_TAC `SUC r` THEN ASM_REWRITE_TAC[EXP; GSYM MULT_ASSOC];
    REPEAT(DISCH_THEN(K ALL_TAC)) THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[EXP; MULT_CLAUSES] THEN MESON_TAC[]]);;

let FINITE_DIVISORS = prove
 (`!n. ~(n = 0) ==> FINITE {d | d divides n}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{d | d <= n}` THEN REWRITE_TAC[FINITE_NUMSEG_LE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[DIVIDES_LE]);;

let MULT_EQ_COPRIME = prove
 (`!a b x y. a * b = x * y /\ coprime(a,x)
             ==> ?d. y = a * d /\ b = x * d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `x:num`; `y:num`] COPRIME_DIVPROD) THEN
  MP_TAC(SPECL [`x:num`; `a:num`; `b:num`] COPRIME_DIVPROD) THEN
  REPEAT(ANTS_TAC THENL
   [ASM_MESON_TAC[DIVIDES_REFL; DIVIDES_RMUL; COPRIME_SYM];
    REWRITE_TAC[divides] THEN STRIP_TAC]) THEN
  UNDISCH_TAC `a * b = x * y` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE
    `(a * x * u = x * a * v) <=> (a * x) * u = (a * x) * v`] THEN
  REWRITE_TAC[EQ_MULT_LCANCEL; MULT_EQ_0] THEN ASM_MESON_TAC[]);;

let COPRIME_ODD_POW2 = prove
 (`!k n. ODD(n) ==> coprime(2 EXP k,n)`,
  SIMP_TAC[coprime; PRIME_2; DIVIDES_PRIMEPOW] THEN REWRITE_TAC[divides] THEN
  REPEAT STRIP_TAC THEN UNDISCH_TAC `ODD n` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[ODD_MULT; ODD_EXP; ARITH]);;

let MULT_NSUM = prove
 (`!s t. FINITE s /\ FINITE t
         ==> nsum s f * nsum t g =
             nsum {(x:A,y:B) | x IN s /\ y IN t} (\(x,y). f(x) * g(y))`,
  SIMP_TAC[GSYM NSUM_NSUM_PRODUCT; NSUM_LMUL; NSUM_RMUL]);;

(* ------------------------------------------------------------------------- *)
(* Some elementary properties of the sigma function.                         *)
(* ------------------------------------------------------------------------- *)

let SIGMA_0 = prove
 (`sigma 0 = 0`,
  REWRITE_TAC[sigma]);;

let SIGMA_1 = prove
 (`sigma(1) = 1`,
  REWRITE_TAC[sigma; DIVIDES_ONE; SET_RULE `{d | d = 1} = {1}`] THEN
  REWRITE_TAC[ARITH; NSUM_SING]);;

let SIGMA_LBOUND = prove
 (`!n. 1 < n ==> n + 1 <= sigma(n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `1 < n ==> ~(n = 0)`)) THEN
  ASM_REWRITE_TAC[sigma] THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum {1,n} (\i. i)` THEN CONJ_TAC THENL
   [SIMP_TAC[NSUM_CLAUSES; FINITE_RULES; IN_SING; NOT_IN_EMPTY] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN ASM_SIMP_TAC[FINITE_DIVISORS] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; NOT_IN_EMPTY; IN_INSERT] THEN
    MESON_TAC[DIVIDES_1; DIVIDES_REFL]]);;

let SIGMA_MULT = prove
 (`!a b. 1 < a /\ 1 < b ==> 1 + b + a * b <= sigma(a * b)`,
  REPEAT STRIP_TAC THEN
  EVERY_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `1 < n ==> ~(n = 0)`)) THEN
  ASM_REWRITE_TAC[sigma] THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum {1,b,a*b} (\i. i)` THEN CONJ_TAC THENL
   [SIMP_TAC[NSUM_CLAUSES; FINITE_RULES; IN_INSERT; NOT_IN_EMPTY] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `x = a * b <=> a * b = 1 * x`] THEN
    ASM_REWRITE_TAC[EQ_MULT_RCANCEL] THEN
    REWRITE_TAC[MULT_CLAUSES; MULT_EQ_1] THEN
    ASM_ARITH_TAC;
    ASM_REWRITE_TAC[MULT_EQ_0] THEN
    MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[FINITE_DIVISORS; MULT_EQ_0] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; NOT_IN_EMPTY; IN_INSERT] THEN
    MESON_TAC[DIVIDES_1; DIVIDES_REFL; DIVIDES_LMUL]]);;

let SIGMA_PRIME = prove
 (`!p. prime(p) ==> sigma(p) = p + 1`,
  GEN_TAC THEN
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[PRIME_0; SIGMA_0; ARITH] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[PRIME_1; SIGMA_1; ARITH] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[sigma] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `nsum {1,p} (\i. i)` THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[prime; DIVIDES_1; DIVIDES_REFL];
    ASM_SIMP_TAC[NSUM_CLAUSES; IN_SING; FINITE_RULES; NOT_IN_EMPTY] THEN
    ARITH_TAC]);;

let SIGMA_PRIME_EQ = prove
 (`!p. prime(p) <=> sigma(p) = p + 1`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[SIGMA_PRIME] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[prime; DE_MORGAN_THM] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[SIGMA_1; ARITH] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; divides; DE_MORGAN_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` SUBST_ALL_TAC) THEN
  MP_TAC(SPECL [`a:num`; `b:num`] SIGMA_MULT) THEN
  ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; SIGMA_0; ARITH] THEN
  ASM_CASES_TAC `b = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; SIGMA_0; ARITH] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[MULT_EQ_1] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `a = a * b <=> a * b = a * 1`] THEN
  REWRITE_TAC[EQ_MULT_LCANCEL] THEN ARITH_TAC);;

let SIGMA_POW2 = prove
 (`!k. sigma(2 EXP k) = 2 EXP (k + 1) - 1`,
  GEN_TAC THEN REWRITE_TAC[sigma; EXP_EQ_0; ARITH] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `nsum {2 EXP i | i <= k} (\i. i)` THEN CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[DIVIDES_PRIMEPOW; PRIME_2; EXTENSION; IN_ELIM_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `x + 1 = y ==> x = y - 1`) THEN
  SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THEN REWRITE_TAC[LE] THENL
   [REWRITE_TAC[SET_RULE `{2 EXP i | i = 0} = {2 EXP 0}`] THEN
    REWRITE_TAC[ARITH; NSUM_SING];
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE
   `{2 EXP i | i = SUC k \/ i <= k} =
    (2 EXP (SUC k)) INSERT {2 EXP i | i <= k}`] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[SET_RULE
   `{2 EXP i | i <= k} = IMAGE (\i. 2 EXP i) {i | i <= k}`] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_IMAGE; FINITE_NUMSEG_LE] THEN
  REWRITE_TAC[IN_IMAGE; GSYM LE_ANTISYM; LE_EXP; ARITH] THEN
  REWRITE_TAC[LE_ANTISYM; IN_ELIM_THM; UNWIND_THM1] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC k <= k)`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[GSYM ADD_ASSOC] THEN
  REWRITE_TAC[EXP; EXP_ADD; ARITH] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Multiplicativity of sigma, the most interesting property.                 *)
(* ------------------------------------------------------------------------- *)

let SIGMA_MULTIPLICATIVE = prove
 (`!a b. coprime(a,b) ==> sigma(a * b) = sigma(a) * sigma(b)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[SIGMA_0; MULT_CLAUSES] THEN
  ASM_CASES_TAC `b = 0` THEN ASM_REWRITE_TAC[SIGMA_0; MULT_CLAUSES] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[sigma; MULT_EQ_0] THEN
  ASM_SIMP_TAC[FINITE_DIVISORS; MULT_NSUM] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `nsum (IMAGE (\(x,y). x * y)
         {x,y | x divides a /\ y divides b}) (\i. i)` THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; EXISTS_PAIR_THM] THEN
    REWRITE_TAC[PAIR_EQ] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> c /\ a /\ b`] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    X_GEN_TAC `n:num` THEN EQ_TAC THEN REWRITE_TAC[DIVISION_DECOMP] THEN
    REWRITE_TAC[divides] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[MULT_AC];
    ALL_TAC] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhs o rand) NSUM_IMAGE (lhand w))) THEN
  REWRITE_TAC[o_DEF; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`w:num`; `x:num`; `y:num`; `z:num`] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (is_var o rand o concl))) THEN
  REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN
  ASM_MESON_TAC[COPRIME_DIVISORS; COPRIME_SYM; COPRIME_DIVPROD;
                DIVIDES_RMUL; DIVIDES_REFL; MULT_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Hence the main theorems.                                                  *)
(* ------------------------------------------------------------------------- *)

let PERFECT_EUCLID = prove
 (`!k. prime(2 EXP k - 1) ==> perfect(2 EXP (k - 1) * (2 EXP k - 1))`,
  GEN_TAC THEN ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[ARITH; PRIME_0] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `coprime(2 EXP (k - 1),2 EXP k - 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC COPRIME_ODD_POW2 THEN ASM_SIMP_TAC[ODD_POW2_MINUS1];
    ALL_TAC] THEN
  ASM_SIMP_TAC[perfect; SIGMA_MULTIPLICATIVE; SIGMA_PRIME; SIGMA_POW2] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> k - 1 + 1 = k`; EXP_EQ_0;
               MULT_EQ_0; ARITH] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  REWRITE_TAC[MULT_ASSOC] THEN GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
  AP_TERM_TAC THEN UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC);;

let PERFECT_EULER = prove
 (`!n. EVEN(n) /\ perfect(n)
       ==> ?k. prime(2 EXP k - 1) /\ n = 2 EXP (k - 1) * (2 EXP k - 1)`,
  GEN_TAC THEN MP_TAC(SPEC `n:num` EVEN_ODD_DECOMP) THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[perfect]; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; GSYM NOT_EVEN] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `s:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[EVEN_EXP; EVEN_MULT; ARITH] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[perfect] THEN
  ASM_SIMP_TAC[SIGMA_MULTIPLICATIVE; SIGMA_POW2;
               COPRIME_ODD_POW2; GSYM NOT_EVEN] THEN
  DISCH_TAC THEN EXISTS_TAC `r + 1` THEN
  REWRITE_TAC[ADD_SUB; EQ_MULT_LCANCEL] THEN REWRITE_TAC[EXP_EQ_0; ARITH] THEN
  FIRST_X_ASSUM(MP_TAC o check(is_eq o concl)) THEN
  REWRITE_TAC[MULT_ASSOC; GSYM(CONJUNCT2 EXP); ADD1] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] MULT_EQ_COPRIME)) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_ODD_POW2 THEN
    SIMP_TAC[ODD_POW2_MINUS1; ADD_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` MP_TAC) THEN
  ASM_CASES_TAC `d = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THENL
   [ASM_MESON_TAC[EVEN]; ALL_TAC] THEN
  ASM_CASES_TAC `d = 1` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; SIGMA_PRIME_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN
    MATCH_MP_TAC(GSYM SUB_ADD) THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  MP_TAC(SPECL [`2 EXP (r + 1) - 1`; `d:num`] SIGMA_MULT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ ~b ==> (a ==> b) ==> c`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `2 EXP 1 < a ==> 1 < a - 1`) THEN
    REWRITE_TAC[LT_EXP; ARITH] THEN
    UNDISCH_TAC `~(r = 0)` THEN ARITH_TAC;
    MAP_EVERY UNDISCH_TAC [`~(d = 0)`; `~(d = 1)`] THEN ARITH_TAC;
    REWRITE_TAC[NOT_LE] THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[RIGHT_SUB_DISTRIB; MULT_CLAUSES] THEN
    MATCH_MP_TAC(ARITH_RULE `1 * d < x * d ==> x * d < 1 + d + x * d - d`) THEN
    ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN
    MATCH_MP_TAC(ARITH_RULE `2 EXP 0 < a ==> 1 < a`) THEN
    REWRITE_TAC[LT_EXP] THEN UNDISCH_TAC `~(r = 0)` THEN ARITH_TAC]);;
