(* ========================================================================= *)
(* Multiplicative functions into N or R (could add Z, C etc.)                *)
(* ========================================================================= *)

needs "Library/prime.ml";;
needs "Library/pocklington.ml";;

(* ------------------------------------------------------------------------- *)
(* Definition of multiplicativity of functions into N.                       *)
(* ------------------------------------------------------------------------- *)

let multiplicative = new_definition
 `multiplicative f <=>
     f(1) = 1 /\ !m n. coprime(m,n) ==> f(m * n) = f(m) * f(n)`;;

let MULTIPLICATIVE_1 = prove
 (`!f. multiplicative f ==> f(1) = 1`,
  SIMP_TAC[multiplicative]);;

(* ------------------------------------------------------------------------- *)
(* We can really ignore the value at zero.                                   *)
(* ------------------------------------------------------------------------- *)

let MULTIPLICATIVE = prove
 (`multiplicative f <=>
        f(1) = 1 /\
        !m n. ~(m = 0) /\ ~(n = 0) /\ coprime(m,n) ==> f(m * n) = f(m) * f(n)`,
  REWRITE_TAC[multiplicative] THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_SIMP_TAC[MULT_CLAUSES] THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_SIMP_TAC[MULT_CLAUSES] THEN
  ASM_MESON_TAC[COPRIME_SYM; COPRIME_0; DIVIDES_ONE; MULT_CLAUSES]);;

let MULTIPLICATIVE_IGNOREZERO = prove
 (`!f g. (!n. ~(n = 0) ==> g(n) = f(n)) /\ multiplicative f
         ==> multiplicative g`,
  REPEAT GEN_TAC THEN SIMP_TAC[MULTIPLICATIVE; ARITH_EQ] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MULT_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* A key "building block" theorem.                                           *)
(* ------------------------------------------------------------------------- *)


let MULTIPLICATIVE_CONVOLUTION = prove
 (`!f g. multiplicative f /\ multiplicative g
         ==> multiplicative (\n. nsum {d | d divides n}
                                      (\d. f(d) * g(n DIV d)))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [multiplicative] THEN
  REWRITE_TAC[MULTIPLICATIVE; GSYM NSUM_LMUL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[DIVIDES_ONE; DIV_1; SING_GSPEC; NSUM_SING; MULT_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
  ASM_SIMP_TAC[GSYM NSUM_LMUL; NSUM_NSUM_PRODUCT; FINITE_DIVISORS] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_EQ_GENERAL THEN
  EXISTS_TAC `\(a:num,b). a * b` THEN REWRITE_TAC[EXISTS_UNIQUE_DEF] THEN
  REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP DIVISION_DECOMP) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MULT_SYM]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a1:num`; `b1:num`; `a2:num`; `b2:num`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC COPRIME_DIVPROD THENL
     (map EXISTS_TAC [`b2:num`; `b1:num`; `a2:num`; `a1:num`]) THEN
    ASM_MESON_TAC[COPRIME_DIVISORS; DIVIDES_REFL;
                  DIVIDES_RMUL; COPRIME_SYM; MULT_SYM];
    MAP_EVERY X_GEN_TAC [`d:num`; `e:num`] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[DIVIDES_MUL2; MULT_SYM]; ALL_TAC] THEN
    MP_TAC(REWRITE_RULE[divides] (ASSUME `(d:num) divides n`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `d':num` SUBST_ALL_TAC) THEN
    MP_TAC(REWRITE_RULE[divides] (ASSUME `(e:num) divides m`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `e':num` SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
    ONCE_REWRITE_TAC[AC MULT_AC
     `(e * e') * d * d':num = (d * e) * (d' * e')`] THEN
    ASM_SIMP_TAC[DIV_MULT; MULT_EQ_0] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (NUMBER_RULE
     `coprime(a * b,c * d) ==> coprime(c,a) /\ coprime(d,b)`)) THEN
    ASM_SIMP_TAC[] THEN ARITH_TAC]);;

let MULTIPLICATIVE_CONST = prove
 (`!c. multiplicative(\n. c) <=> c = 1`,
  GEN_TAC THEN REWRITE_TAC[multiplicative] THEN
  ASM_CASES_TAC `c = 1` THEN ASM_REWRITE_TAC[MULT_CLAUSES]);;

let MULTIPLICATIVE_DELTA = prove
 (`multiplicative(\n. if n = 1 then 1 else 0)`,
  REWRITE_TAC[MULTIPLICATIVE; MULT_EQ_1] THEN ARITH_TAC);;

let MULTIPLICATIVE_DIVISORSUM = prove
 (`!f. multiplicative f ==> multiplicative (\n. nsum {d | d divides n} f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->num`; `\n:num. 1`] MULTIPLICATIVE_CONVOLUTION) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; MULTIPLICATIVE_CONST; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Some particular multiplicative functions.                                 *)
(* ------------------------------------------------------------------------- *)

let MULTIPLICATIVE_ID = prove
 (`multiplicative(\n. n)`,
  REWRITE_TAC[multiplicative]);;

let MULTIPLICATIVE_POWERSUM = prove
 (`!k. multiplicative(\n. nsum {d | d divides n} (\d. d EXP k))`,
  GEN_TAC THEN MATCH_MP_TAC MULTIPLICATIVE_DIVISORSUM THEN
  REWRITE_TAC[MULTIPLICATIVE; EXP_ONE; MULT_EXP]);;

let sigma = new_definition
 `sigma(n) = if n = 0 then 0 else nsum {d | d divides n} (\i. i)`;;

let tau = new_definition
 `tau(n) = if n = 0 then 0 else CARD {d | d divides n}`;;

let MULTIPLICATIVE_SIGMA = prove
 (`multiplicative(sigma)`,
  MP_TAC(SPEC `1` MULTIPLICATIVE_POWERSUM) THEN
  MATCH_MP_TAC(REWRITE_RULE[GSYM IMP_IMP] MULTIPLICATIVE_IGNOREZERO) THEN
  SIMP_TAC[sigma; EXP_1]);;

let MULTIPLICATIVE_TAU = prove
 (`multiplicative(tau)`,
  MP_TAC(SPEC `0` MULTIPLICATIVE_POWERSUM) THEN
  MATCH_MP_TAC(REWRITE_RULE[GSYM IMP_IMP] MULTIPLICATIVE_IGNOREZERO) THEN
  SIMP_TAC[tau; EXP; NSUM_CONST; MULT_CLAUSES; FINITE_DIVISORS]);;

let MULTIPLICATIVE_PHI = prove
 (`multiplicative(phi)`,
  REWRITE_TAC[multiplicative; PHI_MULTIPLICATIVE; PHI_1]);;

let MULTIPLICATIVE_GCD = prove
 (`!n. multiplicative(\m. gcd(n,m))`,
  REWRITE_TAC[multiplicative; ONCE_REWRITE_RULE[GCD_SYM] GCD_1] THEN
  ONCE_REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN NUMBER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness of multiplicative functions if equal on prime powers.          *)
(* ------------------------------------------------------------------------- *)

let MULTIPLICATIVE_UNIQUE = prove
 (`!f g. multiplicative f /\ multiplicative g /\
         (!p k. prime p ==> f(p EXP k) = g(p EXP k))
         ==> !n. ~(n = 0) ==> f n = g n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC o MATCH_MP (ARITH_RULE
   `~(n = 0) ==> n = 1 \/ 1 < n`))
  THENL [ASM_MESON_TAC[multiplicative]; ALL_TAC] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC INDUCT_COPRIME_STRONG THEN
  ASM_MESON_TAC[multiplicative]);;

(* ------------------------------------------------------------------------- *)
(* Derive the divisor-sum identity for phi from this.                        *)
(* ------------------------------------------------------------------------- *)

let PHI_DIVISORSUM = prove
 (`!n. ~(n = 0) ==> nsum {d | d divides n} (\d. phi(d)) = n`,
  MATCH_MP_TAC MULTIPLICATIVE_UNIQUE THEN REWRITE_TAC[MULTIPLICATIVE_ID] THEN
  SIMP_TAC[MULTIPLICATIVE_DIVISORSUM; ETA_AX; MULTIPLICATIVE_PHI] THEN
  SIMP_TAC[DIVIDES_PRIMEPOW; SET_RULE
    `{d | ?i. i <= k /\ d = p EXP i} = IMAGE (\i. p EXP i) {i | i <= k}`] THEN
  SIMP_TAC[NSUM_IMAGE; EQ_PRIMEPOW; o_DEF; PHI_PRIMEPOW] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[LE; NOT_SUC] THEN
  REWRITE_TAC[CONJUNCT1 EXP; SET_RULE `{x | x = 0} = {0}`; NSUM_SING] THEN
  REWRITE_TAC[SET_RULE `{i | i = a \/ i <= b} = a INSERT {i | i <= b}`] THEN
  ASM_SIMP_TAC[NSUM_CLAUSES; FINITE_NUMSEG_LE; NOT_SUC] THEN
  REWRITE_TAC[IN_ELIM_THM; SUC_SUB1; ARITH_RULE `~(SUC k <= k)`] THEN
  MATCH_MP_TAC(ARITH_RULE `a:num <= b ==> b - a + a = b`) THEN
  ASM_SIMP_TAC[LE_EXP; PRIME_IMP_NZ] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Now the real analog.                                                      *)
(* ------------------------------------------------------------------------- *)

let real_multiplicative = new_definition
 `real_multiplicative (f:num->real) <=>
     f(1) = &1 /\ !m n. coprime(m,n) ==> f(m * n) = f(m) * f(n)`;;

let REAL_MULTIPLICATIVE = prove
 (`real_multiplicative f <=>
        f(1) = &1 /\
        !m n. ~(m = 0) /\ ~(n = 0) /\ coprime(m,n) ==> f(m * n) = f(m) * f(n)`,
  REWRITE_TAC[real_multiplicative] THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[COPRIME_0; MULT_CLAUSES; REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  ASM_CASES_TAC `m = 0` THEN
  ASM_SIMP_TAC[COPRIME_0; MULT_CLAUSES; REAL_MUL_RID] THEN
  ASM_MESON_TAC[COPRIME_SYM; COPRIME_0; DIVIDES_ONE; MULT_CLAUSES]);;

let REAL_MULTIPLICATIVE_CONST = prove
 (`!c. real_multiplicative(\n. c) <=> c = &1`,
  GEN_TAC THEN REWRITE_TAC[real_multiplicative] THEN
  ASM_CASES_TAC `c:real = &1` THEN ASM_REWRITE_TAC[REAL_MUL_LID]);;

let REAL_MULTIPLICATIVE_DELTA = prove
 (`real_multiplicative(\n. if n = 1 then &1 else &0)`,
  REWRITE_TAC[REAL_MULTIPLICATIVE; MULT_EQ_1] THEN REAL_ARITH_TAC);;

let REAL_MULTIPLICATIVE_IGNOREZERO = prove
 (`!f g. (!n. ~(n = 0) ==> g(n) = f(n)) /\ real_multiplicative f
         ==> real_multiplicative g`,
  REPEAT GEN_TAC THEN SIMP_TAC[REAL_MULTIPLICATIVE; ARITH_EQ] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MULT_EQ_0]);;

let REAL_MULTIPLICATIVE_CONVOLUTION = prove
 (`!f g. real_multiplicative f /\ real_multiplicative g
         ==> real_multiplicative (\n. sum {d | d divides n}
                                          (\d. f(d) * g(n DIV d)))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [real_multiplicative] THEN
  REWRITE_TAC[REAL_MULTIPLICATIVE; GSYM SUM_LMUL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[DIVIDES_ONE; DIV_1; SING_GSPEC; SUM_SING; REAL_MUL_LID] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM SUM_LMUL; SUM_SUM_PRODUCT; FINITE_DIVISORS] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_EQ_GENERAL THEN
  EXISTS_TAC `\(a:num,b). a * b` THEN REWRITE_TAC[EXISTS_UNIQUE_DEF] THEN
  REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP DIVISION_DECOMP) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MULT_SYM]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a1:num`; `b1:num`; `a2:num`; `b2:num`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC COPRIME_DIVPROD THENL
     (map EXISTS_TAC [`b2:num`; `b1:num`; `a2:num`; `a1:num`]) THEN
    ASM_MESON_TAC[COPRIME_DIVISORS; DIVIDES_REFL;
                  DIVIDES_RMUL; COPRIME_SYM; MULT_SYM];
    MAP_EVERY X_GEN_TAC [`d:num`; `e:num`] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[DIVIDES_MUL2; MULT_SYM]; ALL_TAC] THEN
    MP_TAC(REWRITE_RULE[divides] (ASSUME `(d:num) divides n`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `d':num` SUBST_ALL_TAC) THEN
    MP_TAC(REWRITE_RULE[divides] (ASSUME `(e:num) divides m`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `e':num` SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
    ONCE_REWRITE_TAC[AC MULT_AC
     `(e * e') * d * d':num = (d * e) * (d' * e')`] THEN
    ASM_SIMP_TAC[DIV_MULT; MULT_EQ_0] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (NUMBER_RULE
     `coprime(a * b,c * d) ==> coprime(c,a) /\ coprime(d,b)`)) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]);;

let REAL_MULTIPLICATIVE_DIVISORSUM = prove
 (`!f. real_multiplicative f
       ==> real_multiplicative (\n. sum {d | d divides n} f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real`; `(\n. &1):num->real`]
     REAL_MULTIPLICATIVE_CONVOLUTION) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MULTIPLICATIVE_CONST; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* The Mobius function (into the reals).                                     *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let mobius = new_definition
 `mobius(n) = if ?p. prime p /\ (p EXP 2) divides n then &0
              else --(&1) pow CARD {p | prime p /\ p divides n}`;;

let MOBIUS_0 = prove
 (`mobius 0 = &0`,
  REWRITE_TAC[mobius] THEN MP_TAC(SPEC `2 EXP 2` DIVIDES_0) THEN
  MESON_TAC[PRIME_2]);;

let MOBIUS_1 = prove
 (`mobius 1 = &1`,
  REWRITE_TAC[mobius; DIVIDES_ONE; EXP_EQ_1; ARITH] THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  SUBGOAL_THEN `{p | prime p /\ p = 1} = {}`
   (fun th -> SIMP_TAC[th; CARD_CLAUSES; real_pow]) THEN SET_TAC[PRIME_1]);;

let REAL_ABS_MOBIUS = prove
 (`!n. abs(mobius n) <= &1`,
  GEN_TAC THEN REWRITE_TAC[mobius] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NEG; REAL_POW_ONE; REAL_ABS_NUM] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let MOBIUS_MULT = prove
 (`!a b. coprime(a,b) ==> mobius(a * b) = mobius a * mobius b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mobius] THEN
  ASM_CASES_TAC `?p. prime p /\ (p EXP 2) divides a` THENL
   [ASM_CASES_TAC `?p. prime p /\ p EXP 2 divides (a * b)` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_MESON_TAC[DIVIDES_RMUL];
    ALL_TAC] THEN
  ASM_CASES_TAC `?p. prime p /\ (p EXP 2) divides b` THENL
   [ASM_CASES_TAC `?p. prime p /\ p EXP 2 divides (a * b)` THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_MESON_TAC[DIVIDES_LMUL];
    ALL_TAC] THEN
  ASM_CASES_TAC `?p. prime p /\ p EXP 2 divides (a * b)` THENL
   [ASM_MESON_TAC[PRIME_DIVPROD_POW]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
  ASM_CASES_TAC `a = 0` THENL [ASM_MESON_TAC[PRIME_2; DIVIDES_0]; ALL_TAC] THEN
  ASM_CASES_TAC `b = 0` THENL [ASM_MESON_TAC[PRIME_2; DIVIDES_0]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p | p divides a * b}` THEN
    ASM_SIMP_TAC[FINITE_DIVISORS; MULT_EQ_0] THEN SET_TAC[];
    SIMP_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNION; AND_FORALL_THM] THEN
    X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `~(?p. prime p /\ p EXP 2 divides a * b)` THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `p:num`) THEN
    ASM_CASES_TAC `prime p` THEN ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN
    REWRITE_TAC[CONTRAPOS_THM; EXP_2] THEN CONV_TAC NUMBER_RULE]);;

let REAL_MULTIPLICATIVE_MOBIUS = prove
 (`real_multiplicative mobius`,
  SIMP_TAC[real_multiplicative; MOBIUS_1; MOBIUS_MULT]);;

let MOBIUS_PRIME = prove
 (`!p. prime p ==> mobius(p) = -- &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mobius] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `q:num`
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th -> MP_TAC th THEN ASSUME_TAC
     (MATCH_MP(NUMBER_RULE `q EXP 2 divides p ==> q divides p`) th)) THEN
    SUBGOAL_THEN `q:num = p` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[DIVIDES_PRIME_PRIME]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    REWRITE_TAC[ARITH_RULE `p EXP 2 <= p <=> p * p <= 1 * p`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
    SUBGOAL_THEN `{q | prime q /\ q divides p} = {p}` SUBST1_TAC THENL
     [ASM SET_TAC[DIVIDES_PRIME_PRIME]; ALL_TAC] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH; REAL_POW_1]]);;

let MOBIUS_PRIMEPOW = prove
 (`!p k. prime p ==> mobius(p EXP k) = if k = 0 then &1
                                       else if k = 1 then -- &1
                                       else &0`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[EXP; MOBIUS_1] THEN
  ASM_CASES_TAC `k = 1` THEN ASM_SIMP_TAC[EXP_1; MOBIUS_PRIME] THEN
  REWRITE_TAC[mobius] THEN
  SUBGOAL_THEN `?q. prime q /\ q EXP 2 divides p EXP k`
   (fun th -> REWRITE_TAC[th]) THEN
  EXISTS_TAC `p:num` THEN ASM_SIMP_TAC[DIVIDES_PRIME_EXP_LE] THEN
  ASM_ARITH_TAC);;

let DIVISORSUM_MOBIUS = prove
 (`!n. 1 <= n
       ==> sum {d | d divides n} (\d. mobius d) = if n = 1 then &1 else &0`,
  REWRITE_TAC[ARITH_RULE `1 <= n <=> n = 1 \/ 1 < n`] THEN
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[DIVIDES_ONE; SET_RULE `{x | x = a} = {a}`; SUM_SING; MOBIUS_1] THEN
  SIMP_TAC[ARITH_RULE `1 < n ==> ~(n = 1)`] THEN
  MATCH_MP_TAC INDUCT_COPRIME_STRONG THEN CONJ_TAC THENL
   [MP_TAC(MATCH_MP REAL_MULTIPLICATIVE_DIVISORSUM
                    REAL_MULTIPLICATIVE_MOBIUS) THEN
    SIMP_TAC[real_multiplicative; ETA_AX; REAL_MUL_LZERO];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `k:num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum {1,p} (\d. mobius d)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[SUM_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; IN_SING;
                 MOBIUS_PRIME; MOBIUS_1; REAL_ADD_RID; REAL_ADD_RINV] THEN
    ASM_MESON_TAC[PRIME_1]] THEN
  MATCH_MP_TAC SUM_SUPERSET THEN ASM_SIMP_TAC[DIVIDES_PRIMEPOW] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[EXP; LE_0];
    ASM_MESON_TAC[EXP_1; LE_1];
    ASM_SIMP_TAC[MOBIUS_PRIMEPOW] THEN ASM_MESON_TAC[EXP; EXP_1]]);;

let MOBIUS_INVERSION = prove
 (`!f g. (!n. 1 <= n ==> g(n) = sum {d | d divides n} f)
         ==> !n. 1 <= n
                 ==> f(n) = sum {d | d divides n} (\d. mobius(d) * g(n DIV d))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!d. d divides n ==> ~(n DIV d = 0)` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `d = 0` THEN
    ASM_SIMP_TAC[DIVIDES_ZERO; LE_1] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_SIMP_TAC[LE_1; NOT_LT; DIV_EQ_0];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LE_1] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `sum {d | d divides n} (\d. f(d) * (if n DIV d = 1 then &1 else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum {n} (\d. f(d) * (if n DIV d = 1 then &1 else &0))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[SUM_SING; DIV_REFL; LE_1; REAL_MUL_RID]; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
    SIMP_TAC[SUBSET; IN_SING; IN_ELIM_THM; DIVIDES_REFL] THEN
    X_GEN_TAC `d:num` THEN REWRITE_TAC[DIVIDES_DIV_MULT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; REAL_MUL_RZERO];
    ASM_SIMP_TAC[GSYM DIVISORSUM_MOBIUS; LE_1] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    ASM_SIMP_TAC[SUM_SUM_PRODUCT; FINITE_DIVISORS; LE_1; IN_ELIM_THM] THEN
    MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
    REPEAT(EXISTS_TAC `\(m:num,n:num). (n,m)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    CONJ_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_MESON_TAC[DIVIDES_DIVIDES_DIV; MULT_SYM;
                  NUMBER_RULE `(a * b) divides c ==> b divides c`]]);;
