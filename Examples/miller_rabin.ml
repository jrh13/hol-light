(* ========================================================================= *)
(* Miller-Rabin strong pseudoprimes / probable primes.                       *)
(* ========================================================================= *)

needs "Library/primitive.ml";;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Miller-Rabin compositeness witnesses and pseudoprimes (including primes). *)
(* We treat even numbers as degenerately composite to any pseudoprime base,  *)
(* except for n = 2, which is considered a pseudoprime. This seems to give   *)
(* the cleanest relationhships, though we mainly care about the odd case.    *)
(* ------------------------------------------------------------------------- *)

let miller_rabin_composite = new_definition
 `miller_rabin_composite a n <=>
        if EVEN n then ~(n = 2) else
        let e = index 2 (n - 1) in
        let k = (n - 1) DIV 2 EXP e in
        ~(a EXP k == 1) (mod n) /\
        !i. i < e ==> ~((a EXP (2 EXP i * k) == n - 1) (mod n))`;;

let miller_rabin_pseudoprime = new_definition
 `miller_rabin_pseudoprime a n <=>
        n = 2 \/
        ODD n /\
        let e = index 2 (n - 1) in
        let k = (n - 1) DIV 2 EXP e in
        (a EXP k == 1) (mod n) \/
        ?i. i < e /\ (a EXP (2 EXP i * k) == n - 1) (mod n)`;;

let NOT_MILLER_RABIN_COMPOSITE = prove
 (`!a n. ~(miller_rabin_composite a n) <=> miller_rabin_pseudoprime a n`,
  REWRITE_TAC[miller_rabin_composite; miller_rabin_pseudoprime] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 2` THEN ASM_REWRITE_TAC[ARITH] THEN
  ASM_CASES_TAC `ODD n` THEN ASM_REWRITE_TAC[GSYM NOT_ODD] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN MESON_TAC[]);;

let NOT_MILLER_RABIN_PSEUDOPRIME = prove
 (`!a n. ~(miller_rabin_pseudoprime a n) <=> miller_rabin_composite a n`,
  REWRITE_TAC[GSYM NOT_MILLER_RABIN_COMPOSITE]);;

(* ------------------------------------------------------------------------- *)
(* Primes are Miller-Rabin pseudoprimes to any coprime base.                 *)
(* An odd Miller-Rabin pseudoprime is a Fermat pseodoprime, and for an odd   *)
(* prime power the reverse is true (not more generally).                     *)
(* ------------------------------------------------------------------------- *)

let MILLER_RABIN_IMP_FERMAT_PSEUDOPRIME = prove
 (`!a q. miller_rabin_pseudoprime a q /\ ~(q = 2)
         ==> (a EXP (q - 1) == 1) (mod q)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ASM_CASES_TAC `q = 0` THEN ASM_REWRITE_TAC[SUB_0; EXP; CONG_REFL] THEN
  ASM_REWRITE_TAC[miller_rabin_pseudoprime] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o
      SPEC `2 EXP (index 2 (q - 1))` o MATCH_MP CONG_EXP_1) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONG_TRANS) THEN
    MATCH_MP_TAC EQ_IMP_CONG THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[EXP_EXP] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM DIVIDES_DIV_MULT; EXP_INDEX_DIVIDES];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONG_MINUS1]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
     `q divides (a + 1) ==> (a EXP 2 == 1) (mod q)`)) THEN
    REWRITE_TAC[EXP_EXP] THEN DISCH_THEN(MP_TAC o
      SPEC `2 EXP (index 2 (q - 1) - (i + 1))` o
      MATCH_MP CONG_EXP_1) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONG_TRANS) THEN
    MATCH_MP_TAC EQ_IMP_CONG THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[EXP_EXP] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `((e * d) * 2) * f = ((2 * e) * f) * d`] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 EXP); GSYM EXP_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < j ==> SUC i + j - (i + 1) = j`] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN
    REWRITE_TAC[GSYM DIVIDES_DIV_MULT; EXP_INDEX_DIVIDES]]);;

let MILLER_RABIN_EQ_FERMAT_PSEUDOPRIME = prove
 (`!a q. (?p k. prime p /\ ODD p /\ p EXP k = q)
         ==> (miller_rabin_pseudoprime a q <=> (a EXP (q - 1) == 1) (mod q))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
     MILLER_RABIN_IMP_FERMAT_PSEUDOPRIME) THEN
    ASM_MESON_TAC[ODD_EXP; REWRITE_CONV[ARITH] `ODD 2`];
    REWRITE_TAC[miller_rabin_pseudoprime] THEN
    REPEAT LET_TAC THEN DISCH_TAC] THEN
  DISJ2_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[ODD_EXP]; ALL_TAC] THEN
  MP_TAC(fst(EQ_IMP_RULE
   (SPEC `\i. i <= e /\ (a EXP (2 EXP i * k) == 1) (mod q)` num_WOP))) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [EXISTS_TAC `e:num` THEN REWRITE_TAC[LE_REFL] THEN
    MP_TAC(ISPECL [`q - 1`; `2`] INDEX_DECOMPOSITION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` (ASSUME_TAC o SYM o CONJUNCT1)) THEN
    UNDISCH_TAC `(q - 1) DIV 2 EXP e = k` THEN
    ASM_SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ] THEN ASM_MESON_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[EXP; MULT_CLAUSES] THEN STRIP_TAC THEN
  DISJ2_TAC THEN EXISTS_TAC `n - 1` THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (q \/ r) ==> ~(p /\ q) ==> r`) THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `j:num` MP_TAC)) THEN
  ASM_CASES_TAC `p = 2` THEN ASM_REWRITE_TAC[ARITH] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_SIMP_TAC[GSYM CONG_SQUARE_1_PRIME_POWER] THEN
  REWRITE_TAC[EXP_EXP; ARITH_RULE `(e * k) * 2 = (2 * e) * k`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> SUC(n - 1) = n`]);;

let PRIME_IMP_MILLER_RABIN_PSEUDOPRIME = prove
 (`!a p. prime p /\ coprime(a,p) ==> miller_rabin_pseudoprime a p`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p = 2` THENL
   [ASM_REWRITE_TAC[miller_rabin_pseudoprime]; STRIP_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
      MILLER_RABIN_EQ_FERMAT_PSEUDOPRIME o snd) THEN
  ASM_SIMP_TAC[FERMAT_LITTLE_PRIME] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`p:num`; `1`] THEN
  ASM_MESON_TAC[PRIME_ODD; EXP_1]);;

let PRIME_IMP_MILLER_RABIN_PSEUDOPRIME_ALT = prove
 (`!a p. prime p /\ ~(p divides a) ==> miller_rabin_pseudoprime a p`,
  ASM_MESON_TAC[PRIME_COPRIME_EQ; COPRIME_SYM;
                PRIME_IMP_MILLER_RABIN_PSEUDOPRIME]);;

let MILLER_RABIN_COMPOSITE_IMP_COMPOSITE = prove
 (`!a p. coprime(a,p) /\ miller_rabin_composite a p ==> ~(prime p)`,
  REWRITE_TAC[GSYM NOT_MILLER_RABIN_PSEUDOPRIME] THEN
  MESON_TAC[PRIME_IMP_MILLER_RABIN_PSEUDOPRIME]);;

let MILLER_RABIN_COMPOSITE_IMP_COMPOSITE_ALT = prove
 (`!a p. ~(p divides a) /\ miller_rabin_composite a p ==> ~(prime p)`,
  ASM_MESON_TAC[PRIME_COPRIME_EQ; COPRIME_SYM;
                 MILLER_RABIN_COMPOSITE_IMP_COMPOSITE]);;

(* ------------------------------------------------------------------------- *)
(* Other miscellaneous properties.                                           *)
(* ------------------------------------------------------------------------- *)

let MILLER_RABIN_PSEUDOPRIME_IMP_COPRIME = prove
 (`!a p. miller_rabin_pseudoprime a p ==> p = 2 \/ coprime(a,p)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p = 2` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[COPRIME_1] THEN
  ASM_CASES_TAC `p = 0` THENL
   [ASM_REWRITE_TAC[miller_rabin_pseudoprime; ARITH]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] MILLER_RABIN_IMP_FERMAT_PSEUDOPRIME)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
   `(a == 1) (mod n) ==> coprime(a,n)`)) THEN
  REWRITE_TAC[COPRIME_LEXP] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[NUMBER_RULE `coprime(a,1)`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MILLER_RABIN_PSEUDOPRIME_CONG = prove
 (`!a b p.
        (a == b) (mod p)
        ==> (miller_rabin_pseudoprime a p <=> miller_rabin_pseudoprime b p)`,
  REWRITE_TAC[FORALL_AND_THM; TAUT
   `p ==> (q <=> r) <=> (p ==> q ==> r) /\ (p ==> r ==> q)`]THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [CONG_SYM] THEN
  GEN_REWRITE_TAC RAND_CONV [SWAP_FORALL_THM] THEN REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `p:num`] THEN DISCH_TAC THEN
  REWRITE_TAC[miller_rabin_pseudoprime] THEN REPEAT LET_TAC THEN
  MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `ODD p` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_OR THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[]] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONG_TRANS) THEN
  ASM_SIMP_TAC[CONG_EXP]);;

let MILLER_RABIN_PSEUDOPRIME_1 = prove
 (`!p. ODD p ==> miller_rabin_pseudoprime 1 p`,
  REWRITE_TAC[miller_rabin_pseudoprime; EXP_ONE; CONG_REFL] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP_TAC[]);;

let MILLER_RABIN_PSEUDOPRIME_MOD_1 = prove
 (`!a. miller_rabin_pseudoprime a 1`,
  REWRITE_TAC[miller_rabin_pseudoprime; CONG_MOD_1] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[ARITH]);;

let MILLER_RABIN_PSEUDOPRIME_INVERSE_MOD = prove
 (`!a p. miller_rabin_pseudoprime a p
         ==> miller_rabin_pseudoprime (inverse_mod p a) p`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `p = 0` THENL
   [ASM_REWRITE_TAC[inverse_mod; miller_rabin_pseudoprime; ARITH];
    ALL_TAC] THEN
  ASM_CASES_TAC `p = 2` THENL
   [ASM_REWRITE_TAC[inverse_mod; miller_rabin_pseudoprime; ARITH];
    ALL_TAC] THEN
  ASM_CASES_TAC `coprime(a:num,p)` THENL
   [ALL_TAC; ASM_MESON_TAC[MILLER_RABIN_PSEUDOPRIME_IMP_COPRIME]] THEN
  ASM_REWRITE_TAC[miller_rabin_pseudoprime] THEN REPEAT LET_TAC THEN
  ASM_CASES_TAC `ODD p` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_OR THEN CONJ_TAC THENL
   [MATCH_MP_TAC(NUMBER_RULE
     `(x * y == 1) (mod p) ==> (x == 1) (mod p) ==> (y == 1) (mod p)`) THEN
    ASM_REWRITE_TAC[GSYM MULT_EXP] THEN
    MATCH_MP_TAC CONG_EXP_1 THEN REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN
    ASM_MESON_TAC[COPRIME_SYM];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `(a EXP 2 == 1) (mod p) /\ (x * y == 1) (mod p)
      ==> (x == a) (mod p) ==> (y == a) (mod p)`) THEN
    ASM_REWRITE_TAC[CONG_MINUS1_SQUARED] THEN
    ASM_REWRITE_TAC[GSYM MULT_EXP] THEN
    SUBST1_TAC(SYM(SPEC `2 EXP i * k` EXP_ONE)) THEN
    MATCH_MP_TAC CONG_EXP THEN REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN
    ASM_MESON_TAC[COPRIME_SYM]]);;

(* ------------------------------------------------------------------------- *)
(* Simple bound on number of k'th powers with a given residue a.             *)
(* ------------------------------------------------------------------------- *)

let BOUND_POWER_RESIDUES_MODULO_ODD_COPRIME = prove
 (`!n a k.
        ODD n /\ coprime(k,n) /\ coprime(n,a)
        ==> CARD {x | x < n /\ (x EXP k == a) (mod n)}
            <= nproduct {p | prime p /\ p divides n} (\p. gcd(k,p - 1))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[COPRIME_0] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[MESON[PRIME_1; DIVIDES_ONE]
      `~(prime p /\ p divides 1)`] THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; NPRODUCT_CLAUSES] THEN
    REWRITE_TAC[CONG_MOD_1; CARD_NUMSEG_LT; LE_REFL];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `a:num`; `k:num`]
    COUNT_ROOTS_MODULO_ODD_GEN) THEN
  REWRITE_TAC[GSYM nproduct] THEN
  ASM_SIMP_TAC[HAS_SIZE] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LE_0] THEN MATCH_MP_TAC EQ_IMP_LE THEN
  MATCH_MP_TAC NPRODUCT_EQ THEN
  X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC(NUMBER_RULE `coprime(k:num,a) ==> gcd(k,a * b) = gcd(k,b)`) THEN
  REWRITE_TAC[COPRIME_REXP] THEN DISJ1_TAC THEN
  MAP_EVERY UNDISCH_TAC [`(p:num) divides n`; `coprime(k:num,n)`] THEN
  CONV_TAC NUMBER_RULE);;

(* ------------------------------------------------------------------------- *)
(* General upper bound expression for the number of pseudoprime bases.       *)
(* ------------------------------------------------------------------------- *)

let MILLER_RABIN_PSEUDOPRIME_BOUND_GEN = prove
 (`!n s t v.
        ~(prime n) /\ 2 EXP s * t = n - 1 /\ ODD t /\
        (?p. prime p /\ p divides n /\ ~(2 EXP (v + 2) divides (p - 1)))
        ==> CARD {a | a < n /\ miller_rabin_pseudoprime a n}
            <= 2 * nproduct {p | prime p /\ p divides n}
                            (\p. 2 EXP v * gcd(t,p - 1))`,
  REPEAT GEN_TAC THEN DISJ_CASES_TAC(SPEC `n:num` EVEN_OR_ODD) THENL
   [ASM_CASES_TAC `n = 2` THEN
    ASM_REWRITE_TAC[PRIME_2; miller_rabin_pseudoprime; GSYM NOT_EVEN] THEN
    REWRITE_TAC[EMPTY_GSPEC; CARD_CLAUSES; LE_0];
    UNDISCH_TAC `ODD n` THEN REWRITE_TAC[IMP_IMP]] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ODD] THEN
  ASM_CASES_TAC `n = 2` THEN ASM_REWRITE_TAC[ARITH] THEN
  ASM_CASES_TAC `t = 0` THEN ASM_REWRITE_TAC[ODD] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  TRANS_TAC LE_TRANS
   `CARD {a | a < n /\ (a EXP (2 EXP v * t) == 1) (mod n)} +
    CARD {a | a < n /\ (a EXP (2 EXP v * t) == n - 1) (mod n)}` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
    W(MP_TAC o PART_MATCH (rand o rand) CARD_UNION o rand o snd) THEN
    ANTS_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE
       `{x | P x /\ Q x} = {x | x IN {y | P y} /\ Q x}`] THEN
      SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. ~(Q x /\ R x))
        ==> {x | P x /\ Q x} INTER {x | P x /\ R x} = {}`) THEN
      X_GEN_TAC `a:num` THEN ASM_REWRITE_TAC[CONG_MINUS1] THEN
      DISCH_THEN(MP_TAC o SPEC `p:num` o MATCH_MP (NUMBER_RULE
       `!p. (a == 1) (mod n) /\ n divides (a + 1)
            ==> p divides n ==> p divides 2`)) THEN
      ASM_SIMP_TAC[DIVIDES_PRIME_PRIME; PRIME_2] THEN
      ASM_MESON_TAC[DIVIDES_2; NOT_ODD];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    ONCE_REWRITE_TAC[SET_RULE
       `{x | P x /\ Q x} = {x | x IN {y | P y} /\ Q x}`] THEN
    SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG_LT; FINITE_UNION] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN
    X_GEN_TAC `a:num` THEN SIMP_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MILLER_RABIN_PSEUDOPRIME_IMP_COPRIME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [miller_rabin_pseudoprime]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] INDEX_UNIQUE)) THEN
    ASM_REWRITE_TAC[ARITH_EQ; DIVIDES_2; NOT_EVEN] THEN
    DISCH_THEN SUBST1_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SUBGOAL_THEN `(n - 1) DIV 2 EXP s = t` SUBST_ALL_TAC THENL
     [REWRITE_TAC[SYM(ASSUME `2 EXP s * t = n - 1`)] THEN
      SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
     [DISJ1_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
      REWRITE_TAC[GSYM EXP_EXP] THEN ASM_SIMP_TAC[CONG_EXP_1];
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `i:num <= v` MP_TAC THENL
     [ASM_CASES_TAC `p = 0` THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
      ASM_CASES_TAC `p = 1` THENL [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `p:num` o MATCH_MP (NUMBER_RULE
       `!p:num. (a == b) (mod n)
                ==> p divides n /\ (b EXP 2 == 1) (mod n)
                    ==> (a EXP 2 == 1) (mod p)`)) THEN
      ASM_REWRITE_TAC[CONG_MINUS1_SQUARED] THEN
      FIRST_ASSUM(MP_TAC o SPEC `p:num` o MATCH_MP (NUMBER_RULE
       `!p:num. (a == b) (mod n)
                ==> p divides n /\ (a == 1) (mod p)
                    ==> (b == 1) (mod p)`)) THEN
      ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN ANTS_TAC THENL
       [REWRITE_TAC[NUMBER_RULE
         `(a == 1) (mod p) <=> (a + 1 == 2) (mod p)`] THEN
        ASM_SIMP_TAC[SUB_ADD; LE_1] THEN
        ASM_SIMP_TAC[NUMBER_RULE
          `p divides n ==> ((n == m) (mod p) <=> p divides m)`] THEN
        ASM_SIMP_TAC[DIVIDES_PRIME_PRIME; PRIME_2] THEN
        ASM_MESON_TAC[DIVIDES_2; NOT_EVEN];
        ALL_TAC] THEN
      MP_TAC(NUMBER_RULE
        `p divides n /\ coprime(a,n)
         ==> coprime(a:num,p) /\ coprime(p,a)`) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`a:num`; `p:num`] FERMAT_LITTLE_PRIME) THEN
      ASM_REWRITE_TAC[IMP_IMP; EXP_EXP; GSYM CONJ_ASSOC] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ORDER_DIVIDES] THEN
      ASM_SIMP_TAC[DIVIDES_INDEX; MULT_EQ_0; EXP_EQ_0; ARITH_EQ; ORDER_EQ_0;
                   INDEX_MUL; ARITH_RULE `p - 1 = 0 <=> p = 0 \/ p = 1`] THEN
      SIMP_TAC[INDEX_PRIME; PRIME_2] THEN DISCH_THEN(MP_TAC o MATCH_MP
       (MESON[PRIME_2]
        `(!p. prime p ==> P p) /\ ~(!p. prime p ==> Q p) /\
         (!p. prime p ==> R p)
         ==> (!p. ~(p = 2) ==> (Q p <=> R p)) ==> P 2 /\ ~Q 2 /\ R 2`)) THEN
      ANTS_TAC THENL [SIMP_TAC[ADD_CLAUSES]; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `~(i <= n) /\ i <= n + 1 <=> i = n + 1`] THEN
      FIRST_X_ASSUM(MP_TAC o
        GEN_REWRITE_RULE RAND_CONV [PRIMEPOW_DIVIDES_INDEX]) THEN
      ASM_SIMP_TAC[INDEX_ZERO; DIVIDES_2; GSYM NOT_ODD; ADD_CLAUSES;
                   INDEX_EXP; INDEX_REFL; PRIME_2; ARITH_LE] THEN
      ASM_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV
       [ARITH_RULE `i:num <= v <=> i < v \/ i = v`] THEN
      MATCH_MP_TAC MONO_OR THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      REWRITE_TAC[LT_EXISTS] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
      REWRITE_TAC[ARITH_RULE `i + SUC n = SUC i + n`] THEN
      REWRITE_TAC[EXP_ADD; EXP; ARITH_RULE
       `((2 * i) * d) * t = ((i * t) * 2) * d`] THEN
      ONCE_REWRITE_TAC[GSYM EXP_EXP] THEN MATCH_MP_TAC CONG_EXP_1 THEN
      ONCE_REWRITE_TAC[GSYM EXP_EXP] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (NUMBER_RULE `(x == a) (mod n) ==> (a EXP 2 == 1) (mod n)
                     ==> (x EXP 2 == 1) (mod n)`)) THEN
      ASM_REWRITE_TAC[CONG_MINUS1_SQUARED]];
    MATCH_MP_TAC(ARITH_RULE `x <= b /\ y <= b ==> x + y <= 2 * b`) THEN
    SUBGOAL_THEN
     `!z. coprime(n,z)
          ==> CARD {a | a < n /\ (a EXP (2 EXP v * t) == z) (mod n)} <=
              nproduct {p | prime p /\ p divides n}
                       (\p. 2 EXP v * gcd(t,p - 1))`
    MP_TAC THENL
     [ALL_TAC;
      DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th) THEN
      ASM_MESON_TAC[COPRIME_MINUS1; COPRIME_1; COPRIME_SYM]] THEN
    X_GEN_TAC `z:num` THEN DISCH_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      BOUND_POWER_RESIDUES_MODULO_ODD_COPRIME o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[COPRIME_LMUL; COPRIME_LEXP; COPRIME_2] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `st = n - 1 ==> ~(n = 0) ==> n = st + 1`)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; CONV_TAC NUMBER_RULE];
      ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS) THEN
    SUBGOAL_THEN `FINITE {p | prime p /\ p divides n}` MP_TAC THENL
     [ASM_SIMP_TAC[FINITE_SPECIAL_DIVISORS];
      SPEC_TAC(`{p | prime p /\ p divides n}`,`s:num->bool`)] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC[NPRODUCT_CLAUSES; LE_REFL] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `s:num->bool`] THEN STRIP_TAC THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIVIDES_LE_IMP THEN
    REWRITE_TAC[NUMBER_RULE `gcd(a * b:num,c) divides a * gcd(b,c)`] THEN
    REWRITE_TAC[MULT_EQ_0; GCD_ZERO; EXP_EQ_0; ARITH_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* At most 1/4 of coprime numbers are pseudoprime bases, except for n = 9.   *)
(* ------------------------------------------------------------------------- *)

let MILLER_RABIN_PSEUDOPRIME_BOUND_PHI = prove
 (`!n. ODD n /\ ~prime n /\ n > 9
       ==> CARD {a | a < n /\ miller_rabin_pseudoprime a n} <= (phi n) DIV 4`,
  GEN_TAC THEN REWRITE_TAC[GT] THEN
  MAP_EVERY (fun t -> ASM_CASES_TAC t THEN ASM_REWRITE_TAC[ARITH])
   [`n = 0`; `n = 1`; `n = 2`] THEN
  STRIP_TAC THEN MP_TAC(ISPECL [`n - 1`; `2`] INDEX_DECOMPOSITION) THEN
  ABBREV_TAC `s = index 2 (n - 1)` THEN
  ASM_REWRITE_TAC[ARITH_RULE `n - 1 = 0 <=> n = 0 \/ n = 1`; ARITH_EQ] THEN
  REWRITE_TAC[DIVIDES_2; NOT_EVEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(fst(EQ_IMP_RULE(SPEC
   `\v. !p. prime p /\ p divides n ==> 2 EXP v divides p - 1` num_MAX))) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [MESON_TAC[EXP; DIVIDES_1]; ALL_TAC] THEN
    MP_TAC(SPEC `n:num` PRIME_FACTOR) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `index 2 (p - 1)` THEN X_GEN_TAC `k:num` THEN
    REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX] THEN
    ASM_REWRITE_TAC[ARITH_RULE `n - 1 = 0 <=> n = 0 \/ n = 1`; ARITH_EQ] THEN
    ASM_MESON_TAC[PRIME_0; PRIME_1];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [MATCH_MP_TAC(TAUT `~q ==> p /\ q ==> r`) THEN
    DISCH_THEN(MP_TAC o SPEC `1`) THEN
    REWRITE_TAC[ARITH; DIVIDES_2; EVEN_SUB] THEN
    ASM_MESON_TAC[DIVIDES_2; DIVIDES_TRANS; NOT_EVEN];
    X_GEN_TAC `v:num` THEN DISCH_THEN(K ALL_TAC)] THEN
  REWRITE_TAC[ADD1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `v + 2`)) THEN
  REWRITE_TAC[ARITH_RULE `~(v + 2 <= v + 1)`; NOT_FORALL_THM; NOT_IMP] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `s:num`; `t:num`; `v:num`]
    MILLER_RABIN_PSEUDOPRIME_BOUND_GEN) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS) THEN
  REWRITE_TAC[ARITH_RULE `2 * x <= y DIV 4 <=> 8 * x <= y`] THEN
  SUBGOAL_THEN `FINITE {p | prime p /\ p divides n}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_SPECIAL_DIVISORS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {p | prime p /\ p divides n} = 0 \/
    3 <= CARD {p | prime p /\ p divides n} \/
    {p | prime p /\ p divides n} HAS_SIZE 1 \/
    {p | prime p /\ p divides n} HAS_SIZE 2`
  MP_TAC THENL [ASM_REWRITE_TAC[HAS_SIZE] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN MP_TAC) THENL
   [ASM_SIMP_TAC[CARD_EQ_0] THEN MP_TAC(SPEC `n:num` PRIME_FACTOR) THEN
    ASM SET_TAC[];
    (*** The case of >= 3 prime divisors ***)
    DISCH_TAC THEN SUBST1_TAC(ARITH_RULE `8 = 2 EXP 3`) THEN TRANS_TAC LE_TRANS
     `2 EXP CARD {p | prime p /\ p divides n} *
      nproduct {p | prime p /\ p divides n} (\p. 2 EXP v * gcd(t,p - 1))` THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL; LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[GSYM NPRODUCT_CONST; FINITE_SPECIAL_DIVISORS;
                 GSYM NPRODUCT_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [PHI_EXPAND] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NPRODUCT_LE THEN
    ASM_SIMP_TAC[FINITE_SPECIAL_DIVISORS; LE_0; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p - 1`; `2`] INDEX_DECOMPOSITION) THEN
    ASM_REWRITE_TAC[ARITH_RULE `n - 1 = 0 <=> n = 0 \/ n = 1`; ARITH_EQ] THEN
    ASM_CASES_TAC `p = 0` THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
    ASM_CASES_TAC `p = 1` THENL [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
    ASM_REWRITE_TAC[DIVIDES_2; NOT_EVEN; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `r:num` THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[GCD_COPRIME_RMUL; COPRIME_LEXP; COPRIME_2] THEN
    ASM_SIMP_TAC[GCD_ONE; COPRIME_REXP; COPRIME_2] THEN
    REWRITE_TAC[MULT_CLAUSES; MULT_ASSOC; GSYM(CONJUNCT2 EXP)] THEN
    REWRITE_TAC[GSYM MULT_ASSOC] THEN GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
    REWRITE_TAC[GSYM MULT_ASSOC] THEN MATCH_MP_TAC LE_MULT2 THEN
    REWRITE_TAC[ADD1; LE_EXP; ARITH_EQ] THEN ASM_SIMP_TAC[LE_INDEX] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE `g <= r /\ r * 1 <= r * p ==> g <= r * p`) THEN
    REWRITE_TAC[GCD_LE; LE_MULT_LCANCEL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[ODD]; DISJ2_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; ARITH_EQ; EXP_EQ_0];
    (*** The case of 1 prime divisor ***)
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_TAC `p:num`) THEN
    GEN_REWRITE_TAC RAND_CONV [PHI_EXPAND] THEN
    ASM_REWRITE_TAC[NPRODUCT_SING] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (SET_RULE
     `{x | P x /\ Q x} = {p} ==> P p /\ Q p`)) THEN
    ASM_CASES_TAC `p = 0` THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
    ASM_CASES_TAC `p = 1` THENL [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE
     `8 * v * g <= p * q <=> (2 * v * g) * 4 <= q * p`] THEN
    MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL
     [REWRITE_TAC[MULT_ASSOC; GSYM(CONJUNCT2 EXP); ADD1] THEN
      MATCH_MP_TAC DIVIDES_LE_IMP THEN
      ASM_REWRITE_TAC[ARITH_RULE `p - 1 = 0 <=> p = 0 \/ p = 1`] THEN
      MATCH_MP_TAC DIVIDES_MUL THEN ASM_SIMP_TAC[GCD; COPRIME_LEXP] THEN
      DISJ1_TAC THEN MATCH_MP_TAC(NUMBER_RULE
       `coprime(a,b) ==> coprime(a,gcd(b,c))`) THEN
      ASM_REWRITE_TAC[COPRIME_2];
      ALL_TAC] THEN
    MP_TAC(SPECL [`\n:num. n`; `n:num`] MULTIPLICATIVE_EXPAND) THEN
    ASM_REWRITE_TAC[MULTIPLICATIVE_ID; NPRODUCT_SING] THEN
    SUBGOAL_THEN `3 <= p` MP_TAC THENL
     [ASM_MESON_TAC[ODD_PRIME; NOT_ODD; DIVIDES_TRANS; DIVIDES_2];
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `3 <= p <=> p = 3 \/ 4 <= p`] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THENL
     [MATCH_MP_TAC(ARITH_RULE
       `9 < n /\ (3 EXP 2 < i ==> 3 EXP 2 <= j) ==> n = i ==> 4 <= j`) THEN
      ASM_REWRITE_TAC[LT_EXP; LE_EXP] THEN ARITH_TAC;
      DISCH_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `prime`) THEN
      ASM_REWRITE_TAC[PRIME_EXP] THEN DISCH_TAC THEN
      TRANS_TAC LE_TRANS `4 EXP (index p n - 1)` THEN
      ASM_REWRITE_TAC[EXP_MONO_LE] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
      REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= n - 1 <=> ~(n = 0) /\ ~(n = 1)`] THEN
      ASM_REWRITE_TAC[INDEX_EQ_0]];
    (*** The case of 2 prime divisors ***)
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MATCH_MP_TAC(MESON[]
     `!P. (!p q. R p q ==> R q p) /\
          (!p q. P p ==> R p q) /\
          (!p q. ~P p /\ ~P q ==> R p q)
          ==> !p q. R p q`) THEN
    EXISTS_TAC `\p. 2 <= index p n \/ 2 EXP (v + 2) divides p - 1` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN CONJ_TAC THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN
    REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    (SUBGOAL_THEN `prime p /\ prime q /\ p divides n /\ q divides n`
     STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `~(p = 0) /\ ~(p = 1) /\ ~(q = 0) /\ ~(q = 1)`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[PRIME_0; PRIME_1]; ALL_TAC]) THEN
    GEN_REWRITE_TAC RAND_CONV [PHI_EXPAND] THEN
    MP_TAC(SPECL [`\n:num. n`; `n:num`] MULTIPLICATIVE_EXPAND) THEN
    ASM_REWRITE_TAC[MULTIPLICATIVE_ID] THEN
    ASM_SIMP_TAC[NPRODUCT_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
                 IN_INSERT; NOT_IN_EMPTY; MULT_CLAUSES] THEN
    DISCH_THEN(ASSUME_TAC o SYM) THENL
     [FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [REWRITE_TAC[GSYM(CONJUNCT2 EXP); ADD1; ARITH_RULE
         `8 * (e1 * g1) * (e2 * g2) <= (p * p') * (q * q') <=>
          2 * ((2 * e1) * g1) * ((2 * e2) * g2) <= p * p' * q * q'`] THEN
        MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL
         [TRANS_TAC LE_TRANS `2 EXP (index p n - 1)` THEN
          ASM_SIMP_TAC[EXP_MONO_LE; PRIME_GE_2] THEN
          GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
          REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
          ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> 1 <= n - 1`];
          ALL_TAC] THEN
        MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN
        MATCH_MP_TAC DIVIDES_LE_IMP THEN
        ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_0;
                        ARITH_RULE `p - 1 = 0 <=> p = 0 \/ p = 1`]
        THENL [ALL_TAC; MATCH_MP_TAC DIVIDES_LMUL] THEN
        MATCH_MP_TAC DIVIDES_MUL THEN ASM_SIMP_TAC[GCD; COPRIME_LEXP] THEN
        DISJ1_TAC THEN MATCH_MP_TAC(NUMBER_RULE
         `coprime(a,b) ==> coprime(a,gcd(b,c))`) THEN
        ASM_REWRITE_TAC[COPRIME_2];
        REWRITE_TAC[GSYM(CONJUNCT2 EXP); ADD1; ARITH_RULE
          `8 * (e1 * g1) * (e2 * g2) <= (p * p') * (q * q') <=>
           ((2 * 2 * e1) * g1) * ((2 * e2) * g2) <= (p * p') * (q * q')`] THEN
        MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN
        MATCH_MP_TAC DIVIDES_LE_IMP THEN
        ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; COPRIME_LEXP;
                        ARITH_RULE `p - 1 = 0 <=> p = 0 \/ p = 1`] THEN
        MATCH_MP_TAC DIVIDES_MUL THEN
        REWRITE_TAC[NUMBER_RULE `gcd(a,b) divides c * b`] THEN
        ASM_SIMP_TAC[ARITH_RULE `(v + 1) + 1 = v + 2`; DIVIDES_LMUL] THEN
        ASM_SIMP_TAC[COPRIME_LEXP] THEN DISJ1_TAC THEN
        MATCH_MP_TAC(NUMBER_RULE
         `coprime(a,b) ==> coprime(a,gcd(b,c))`) THEN
        ASM_REWRITE_TAC[COPRIME_2]];
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM])) THEN
      REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `~(2 <= n) ==> n = 0 \/ n = 1`))) THEN
      ASM_REWRITE_TAC[INDEX_EQ_0] THEN REPEAT(DISCH_THEN SUBST_ALL_TAC) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[EXP_1]) THEN
      REWRITE_TAC[SUB_REFL; EXP; MULT_CLAUSES] THEN
      MP_TAC(SPECL [`q - 1`; `2`] INDEX_DECOMPOSITION) THEN
      MP_TAC(SPECL [`p - 1`; `2`] INDEX_DECOMPOSITION) THEN
      SUBGOAL_THEN
       `index 2 (p - 1) = v + 1 /\ index 2 (q - 1) = v + 1`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [ASM_REWRITE_TAC[INDEX_UNIQUE_ALT; ARITH_EQ;
                        ARITH_RULE `p - 1 = 0 <=> p = 0 \/ p = 1`] THEN
        ASM_SIMP_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`];
        ASM_REWRITE_TAC[ARITH_RULE `p - 1 = 0 <=> p = 0 \/ p = 1`] THEN
        REWRITE_TAC[ARITH_EQ; LEFT_IMP_EXISTS_THM; DIVIDES_2; NOT_EVEN]] THEN
      X_GEN_TAC `a:num` THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
      X_GEN_TAC `b:num` THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
      ASM_SIMP_TAC[COPRIME_REXP; COPRIME_2; NUMBER_RULE
        `coprime(a,b) ==> gcd(a,b * c) = gcd(a,c)`] THEN
      REWRITE_TAC[EXP_ADD; EXP_1; ARITH_RULE
       `8 * (v * g1) * (v * g2) <= ((v * 2) * a) * (v * 2) * b <=>
        (v * v) * 2 * g1 * g2 <= (v * v) * a * b`] THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
      MATCH_MP_TAC(ARITH_RULE
       `~(a' = a /\ b' = b) /\
        (~(b' = b) ==> a' * (2 * b') <= a * b) /\
        (~(a' = a) ==> b' * (2 * a') <= b * a)
        ==> 2 * a' * b' <= a * b`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM DIVIDES_GCD_RIGHT] THEN STRIP_TAC;
        CONJ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC LE_MULT2 THEN
        ASM_REWRITE_TAC[GCD_LE] THEN
        (CONJ_TAC THENL [ASM_MESON_TAC[ODD]; ALL_TAC]) THEN
        MATCH_MP_TAC PROPERLY_DIVIDES_LE_IMP THEN
        REWRITE_TAC[GCD] THEN ASM_MESON_TAC[ODD]] THEN
      UNDISCH_TAC `~(p:num = q)` THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `m = n - 1 ==> ~(n = 0) ==> m + 1 = n`)) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `n - 1 = m ==> ~(n = 0) ==> m + 1 = n`))) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "n" THEN
      REPLICATE_TAC 2 (DISCH_THEN(SUBST1_TAC o SYM)) THEN
      REWRITE_TAC[EQ_ADD_RCANCEL] THEN MATCH_MP_TAC(NUMBER_RULE
       `a divides t /\ b divides t /\ coprime(a,v) /\ coprime(b,v)
        ==> s * t + 1 = (v * a + 1) * (v * b + 1)
            ==> v * a = v * b`) THEN
      ASM_REWRITE_TAC[COPRIME_REXP; COPRIME_2]]]);;

(* ------------------------------------------------------------------------- *)
(* Less than 1/4 of numbers are pseudoprime bases, for any odd composite n.  *)
(* ------------------------------------------------------------------------- *)

let MILLER_RABIN_PSEUDOPRIME_BOUND_LT = prove
 (`!n. ODD n /\ ~prime n /\ ~(n = 1)
       ==> 4 * CARD {a | a < n /\ miller_rabin_pseudoprime a n} < n`,
  MATCH_MP_TAC(MESON[]
   `!Q. (!n. ~Q n ==> P n) /\ (!n. Q n ==> P n)
        ==> !n. P n`) THEN
  EXISTS_TAC `\n. n < 10` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[ARITH_RULE `~(n < 10) <=> n > 9`] THEN
    REPEAT STRIP_TAC THEN TRANS_TAC LET_TRANS `n - 1` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    TRANS_TAC LE_TRANS `phi n` THEN ASM_SIMP_TAC[PHI_LIMIT_STRONG] THEN
    REWRITE_TAC[ARITH_RULE `4 * m <= n <=> m <= n DIV 4`] THEN
    ASM_SIMP_TAC[MILLER_RABIN_PSEUDOPRIME_BOUND_PHI];
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV PRIME_CONV) THEN REWRITE_TAC[]] THEN
  SUBGOAL_THEN `{a | a < 9 /\ miller_rabin_pseudoprime a 9} = {1,8}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!i. i IN s ==> R i) /\ (!i. R i ==> (P i <=> i IN s))
      ==> {i | R i /\ P i} = s`) THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[miller_rabin_pseudoprime] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `8 = 2 EXP 3`] THEN
    SIMP_TAC[INDEX_EXP; INDEX_REFL; PRIME_2] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MESON[] `(?x. P x /\ Q x) <=> ~(!x. P x ==> ~Q x)`] THEN
    CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV;
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH]]);;

let MILLER_RABIN_PSEUDOPRIME_BOUND = prove
 (`!n. ODD n /\ ~prime n /\ ~(n = 1)
       ==> CARD {a | a < n /\ miller_rabin_pseudoprime a n} <= n DIV 4`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MILLER_RABIN_PSEUDOPRIME_BOUND_LT) THEN
  ARITH_TAC);;
