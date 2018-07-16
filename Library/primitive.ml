(* ========================================================================= *)
(* Existence of primitive roots modulo certain numbers.                      *)
(* ========================================================================= *)

needs "Library/integer.ml";;
needs "Library/isum.ml";;
needs "Library/binomial.ml";;
needs "Library/pocklington.ml";;
needs "Library/multiplicative.ml";;

(* ------------------------------------------------------------------------- *)
(* Some lemmas connecting concepts in the various background theories.       *)
(* ------------------------------------------------------------------------- *)

let DIVIDES_BINOM_PRIME = prove
 (`!n p. prime p /\ 0 < n /\ n < p ==> p divides binom(p,n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(AP_TERM `(divides) p` (SPECL [`p - n:num`; `n:num`] BINOM_FACT)) THEN
  ASM_SIMP_TAC[DIVIDES_FACT_PRIME; PRIME_DIVPROD_EQ; SUB_ADD; LT_IMP_LE] THEN
  ASM_REWRITE_TAC[GSYM NOT_LT; LT_REFL] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n /\ n < p ==> p - n < p`]);;

let INT_PRIME = prove
 (`!p. int_prime(&p) <=> prime p`,
  GEN_TAC THEN REWRITE_TAC[prime; int_prime] THEN
  ONCE_REWRITE_TAC[GSYM INT_DIVIDES_LABS] THEN
  REWRITE_TAC[GSYM INT_FORALL_ABS; GSYM num_divides; INT_ABS_NUM] THEN
  REWRITE_TAC[INT_OF_NUM_GT; INT_OF_NUM_EQ] THEN ASM_CASES_TAC `p = 0` THENL
   [ASM_REWRITE_TAC[ARITH; DIVIDES_0] THEN DISCH_THEN(MP_TAC o SPEC `2`);
    AP_THM_TAC THEN AP_TERM_TAC] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Explicit formula for difference of real/integer polynomials.              *)
(* ------------------------------------------------------------------------- *)

let REAL_POLY_DIFF_EXPLICIT = prove
 (`!n a x y.
        sum(0..n) (\i. a(i) * x pow i) - sum(0..n) (\i. a(i) * y pow i) =
        (x - y) *
        sum(0..n-1) (\i. sum(i+1..n) (\j. a j * y pow (j - 1 - i)) * x pow i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG; GSYM REAL_SUB_LDISTRIB] THEN
  MP_TAC(ISPEC `n:num` LE_0) THEN SIMP_TAC[SUM_CLAUSES_LEFT; ADD_CLAUSES] THEN
  DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_LID; real_pow] THEN
  SIMP_TAC[REAL_SUB_POW] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * b * c:real = b * a * c`] THEN
  REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
  SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL; SUM_SUM_PRODUCT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
  REPEAT(EXISTS_TAC `\(a:num,b:num). (b,a)`) THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; FORALL_PAIR_THM; REAL_MUL_AC] THEN
  REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

let INT_POLY_DIFF_EXPLICIT = INT_OF_REAL_THM REAL_POLY_DIFF_EXPLICIT;;

(* ------------------------------------------------------------------------- *)
(* Lagrange's theorem on number of roots modulo a prime.                     *)
(* ------------------------------------------------------------------------- *)

let FINITE_INTSEG_RESTRICT = prove
 (`!P a b. FINITE {x:int | a <= x /\ x <= b /\ P x}`,
  SIMP_TAC[FINITE_RESTRICT; FINITE_INT_SEG; SET_RULE
   `{x | P x /\ Q x /\ R x} = {x | x IN {x | P x /\ Q x} /\ R x}`]);;

let INT_POLY_LAGRANGE = prove
 (`!p l r.
    int_prime p /\ r - l < p
    ==> !n a. ~(!i. i <= n ==> (a i == &0) (mod p))
              ==> CARD {x | l <= x /\ x <= r /\
                            (isum(0..n) (\i. a(i) * x pow i) == &0) (mod p)}
                  <= n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[INT_CONG_0_DIVIDES] THEN
  MATCH_MP_TAC num_WF THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[]
   `!a. (~(s = a) ==> CARD s <= n) /\ CARD a <= n ==> CARD s <= n`) THEN
  EXISTS_TAC `{}:int->bool` THEN REWRITE_TAC[LE_0; CARD_CLAUSES] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN
  X_GEN_TAC `c:int` THEN STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [MAP_EVERY UNDISCH_TAC
     [`~(!i:num. i <= n ==> (p:int) divides (a i))`;
      `p divides (isum (0..n) (\i. a i * c pow i))`] THEN
    ASM_SIMP_TAC[CONJUNCT1 LE; ISUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[INT_POW; LEFT_FORALL_IMP_THM; EXISTS_REFL; INT_MUL_RID] THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  ASM_CASES_TAC `p divides ((a:num->int) n)` THENL
   [ASM_SIMP_TAC[ISUM_CLAUSES_RIGHT; LE_0; LE_1] THEN
    ASM_SIMP_TAC[INTEGER_RULE
     `(p:int) divides y ==> (p divides (x + y * z) <=> p divides x)`] THEN
    MATCH_MP_TAC(ARITH_RULE `x <= n - 1 ==> x <= n`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[ARITH_RULE `i <= n <=> i <= n - 1 \/ i = n`]; ALL_TAC] THEN
  MP_TAC(GEN `x:int` (MATCH_MP
     (INTEGER_RULE
       `a - b:int = c ==> p divides b ==> (p divides a <=> p divides c)`)
     (ISPECL [`n:num`; `a:num->int`; `x:int`; `c:int`]
             INT_POLY_DIFF_EXPLICIT))) THEN
  ASM_SIMP_TAC[INT_PRIME_DIVPROD_EQ] THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_REWRITE_TAC[LEFT_OR_DISTRIB; SET_RULE
   `{x | q x \/ r x} = {x | q x} UNION {x | r x}`] THEN
  SUBGOAL_THEN
   `{x:int | l <= x /\ x <= r /\ p divides (x - c)} = {c}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `P c /\ (!x y. P x /\ P y ==> x = y)
                           ==> {x | P x} = {c}`) THEN
    ASM_REWRITE_TAC[INT_SUB_REFL; INT_DIVIDES_0] THEN
    MAP_EVERY X_GEN_TAC [`u:int`; `v:int`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `p divides (u - v:int)` MP_TAC THENL
     [ASM_MESON_TAC[INT_CONG; INT_CONG_SYM; INT_CONG_TRANS]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `{a} UNION s = a INSERT s`] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INTSEG_RESTRICT] THEN
  MATCH_MP_TAC(ARITH_RULE
   `~(n = 0) /\ x <= n - 1 ==> (if p then x else SUC x) <= n`) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
  DISCH_THEN(MP_TAC o SPEC `n - 1`) THEN
  ASM_SIMP_TAC[LE_REFL; SUB_ADD; LE_1; ISUM_SING_NUMSEG; SUB_REFL] THEN
  ASM_REWRITE_TAC[INT_POW; INT_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* Laborious instantiation to (x^d == 1) (mod p) over natural numbers.       *)
(* ------------------------------------------------------------------------- *)

let NUM_LAGRANGE_LEMMA = prove
 (`!p d. prime p /\ 1 <= d
         ==> CARD {x | x IN 1..p-1 /\ (x EXP d == 1) (mod p)} <= d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&p:int`; `&1:int`; `&(p-1):int`] INT_POLY_LAGRANGE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[INT_PRIME; INT_LT_SUB_RADD; INT_OF_NUM_ADD; INT_OF_NUM_LT] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`d:num`; `\i. if i = d then &1 else if i = 0 then -- &1 else &0:int`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `d:num`) THEN REWRITE_TAC[LE_REFL] THEN
    REWRITE_TAC[INT_CONG_0_DIVIDES; GSYM num_divides; DIVIDES_ONE] THEN
    ASM_MESON_TAC[PRIME_1];
    ALL_TAC] THEN
  REWRITE_TAC[MESON[]
   `(if p then x else y) * z:int = if p then x * z else y * z`] THEN
  SIMP_TAC[ISUM_CASES; FINITE_NUMSEG; FINITE_RESTRICT] THEN
  REWRITE_TAC[INT_POW; INT_MUL_LZERO; ISUM_0; INT_ADD_RID] THEN
  MATCH_MP_TAC(ARITH_RULE `x:num <= y ==> y <= d ==> x <= d`) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN
  ASM_SIMP_TAC[ARITH_RULE `(0 <= i /\ i <= d) /\ i = d <=> i = d`;
               ARITH_RULE `1 <= d
                           ==> (((0 <= i /\ i <= d) /\ ~(i = d)) /\ i = 0 <=>
                                i = 0)`] THEN
  REWRITE_TAC[SING_GSPEC; ISUM_SING] THEN
  REWRITE_TAC[INT_ARITH `&1 * x + -- &1 * &1:int = x - &1`] THEN
  REWRITE_TAC[INTEGER_RULE `(x - a:int == &0) (mod p) <=>
                            (x == a) (mod p)`] THEN
  MATCH_MP_TAC CARD_SUBSET_IMAGE THEN EXISTS_TAC `num_of_int` THEN
  REWRITE_TAC[FINITE_INTSEG_RESTRICT; SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN EXISTS_TAC `&n:int` THEN
  ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM; INT_OF_NUM_LE; INT_OF_NUM_POW] THEN
  ASM_REWRITE_TAC[GSYM num_congruent]);;

(* ------------------------------------------------------------------------- *)
(* Count of elements with a given order modulo a prime.                      *)
(* ------------------------------------------------------------------------- *)

let COUNT_ORDERS_MODULO_PRIME = prove
 (`!p d. prime p /\ d divides (p - 1)
         ==> CARD {x | x IN 1..p-1 /\ order p x = d} = phi(d)`,
  let lemma = prove
   (`!s f g:A->num.
          FINITE s /\ (!x. x IN s ==> f(x) <= g(x)) /\ nsum s f = nsum s g
          ==> !x. x IN s ==> f x = g x`,
    REWRITE_TAC[GSYM LE_ANTISYM] THEN MESON_TAC[NSUM_LE; NSUM_LT; NOT_LE]) in
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE
   `(!x. p x ==> q x) <=> (!x. x IN {x | p x} ==> q x)`] THEN
  MATCH_MP_TAC lemma THEN SUBGOAL_THEN `~(p - 1 = 0)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REWRITE_RULE[ETA_AX] PHI_DIVISORSUM; FINITE_DIVISORS] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[CARD_EQ_NSUM; FINITE_RESTRICT; FINITE_NUMSEG] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) NSUM_GROUP o lhs o snd) THEN
    REWRITE_TAC[NSUM_CONST_NUMSEG; FINITE_NUMSEG; ADD_SUB; MULT_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[GSYM PHI_PRIME] THEN
    MATCH_MP_TAC ORDER_DIVIDES_PHI THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
    MATCH_MP_TAC PRIME_COPRIME_LT THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC] THEN
  X_GEN_TAC `d:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  ASM_CASES_TAC `{x | x IN 1..p-1 /\ order p x = d} = {}` THEN
  ASM_REWRITE_TAC[CARD_CLAUSES; LE_0] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `a:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN REWRITE_TAC[PHI_ALT] THEN
  MATCH_MP_TAC CARD_SUBSET_IMAGE THEN EXISTS_TAC `\m. (a EXP m) MOD p` THEN
  REWRITE_TAC[PHI_FINITE_LEMMA] THEN
  SUBGOAL_THEN `1 <= d` ASSUME_TAC THENL
   [ASM_MESON_TAC[LE_1; DIVIDES_ZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `coprime(p,a)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[COPRIME_SYM] THEN
    MATCH_MP_TAC PRIME_COPRIME_LT THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN 1..p-1 /\ (x EXP d == 1) (mod p)} =
    IMAGE (\m. (a EXP m) MOD p) {m | m < d}`
  MP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_LE THEN
    SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(p - 1 = 0) ==> (x <= p - 1 <=> x < p)`] THEN
      ASM_SIMP_TAC[DIVISION; PRIME_IMP_NZ] THEN CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`] THEN
        ASM_SIMP_TAC[GSYM DIVIDES_MOD; PRIME_IMP_NZ] THEN
        ASM_MESON_TAC[PRIME_DIVEXP; PRIME_COPRIME_EQ];
        ASM_SIMP_TAC[CONG; PRIME_IMP_NZ; MOD_EXP_MOD] THEN
        REWRITE_TAC[EXP_EXP] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
        REWRITE_TAC[GSYM EXP_EXP] THEN
        SUBST1_TAC(SYM(SPEC `m:num` EXP_ONE)) THEN
        ASM_SIMP_TAC[GSYM CONG; PRIME_IMP_NZ] THEN
        MATCH_MP_TAC CONG_EXP THEN ASM_MESON_TAC[ORDER]];
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `d:num` THEN
      ASM_SIMP_TAC[NUM_LAGRANGE_LEMMA] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM CARD_NUMSEG_LT] THEN
      MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC CARD_IMAGE_INJ THEN
      ASM_SIMP_TAC[GSYM CONG; PRIME_IMP_NZ; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[ORDER_DIVIDES_EXPDIFF] THEN REWRITE_TAC[CONG_IMP_EQ]];
    MATCH_MP_TAC(SET_RULE
     `s' SUBSET s /\ (!x. x IN t /\ f x IN s' ==> x IN t')
      ==> s = IMAGE f t ==> s' SUBSET IMAGE f t'`) THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
    CONJ_TAC THENL [MESON_TAC[ORDER]; ALL_TAC] THEN
    X_GEN_TAC `m:num` THEN ABBREV_TAC `b = (a EXP m) MOD p` THEN STRIP_TAC THEN
    REWRITE_TAC[coprime; divides] THEN X_GEN_TAC `e:num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `m':num` (ASSUME_TAC o SYM))
                              (X_CHOOSE_THEN `d':num` (ASSUME_TAC o SYM))) THEN
    MP_TAC(ISPECL [`p:num`; `b:num`] ORDER_WORKS) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `d':num`)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `a /\ c /\ (~b ==> d) ==> (a /\ b ==> ~c) ==> d`) THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `1 <= d` THEN EXPAND_TAC "d" THEN
      REWRITE_TAC[ARITH_RULE `1 <= d <=> ~(d = 0)`; MULT_EQ_0] THEN
      SIMP_TAC[DE_MORGAN_THM; ARITH_RULE `0 < d <=> ~(d = 0)`];
      EXPAND_TAC "b" THEN ASM_SIMP_TAC[CONG; PRIME_IMP_NZ; MOD_EXP_MOD] THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[EXP_EXP] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `(e * m') * d':num = (e * d') * m'`] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM EXP_EXP] THEN
      SUBST1_TAC(SYM(SPEC `m':num` EXP_ONE)) THEN
      ASM_SIMP_TAC[GSYM CONG; PRIME_IMP_NZ] THEN
      MATCH_MP_TAC CONG_EXP THEN ASM_MESON_TAC[ORDER];
      EXPAND_TAC "d" THEN
      REWRITE_TAC[ARITH_RULE `~(d < e * d) <=> e * d <= 1 * d`] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN
      REWRITE_TAC[ARITH_RULE `e <= 1 <=> e = 0 \/ e = 1`] THEN
      STRIP_TAC THEN UNDISCH_TAC `e * d':num = d` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* In particular, primitive roots modulo a prime.                            *)
(* ------------------------------------------------------------------------- *)

let PRIMITIVE_ROOTS_MODULO_PRIME = prove
 (`!p. prime p ==> CARD {x | x IN 1..p-1 /\ order p x = p - 1} = phi(p - 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `p - 1`] COUNT_ORDERS_MODULO_PRIME) THEN
  ASM_REWRITE_TAC[DIVIDES_REFL]);;

let PRIMITIVE_ROOT_MODULO_PRIME = prove
 (`!p. prime p ==> ?x. x IN 1..p-1 /\ order p x = p - 1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIMITIVE_ROOTS_MODULO_PRIME) THEN
  ASM_CASES_TAC `{x | x IN 1..p-1 /\ order p x = p - 1} = {}` THENL
   [ASM_REWRITE_TAC[CARD_CLAUSES]; ASM SET_TAC[]] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC(ARITH_RULE `1 <= p ==> ~(0 = p)`) THEN
  MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Now primitive roots modulo odd prime powers.                              *)
(* ------------------------------------------------------------------------- *)

let COPRIME_1_PLUS_POWER_STEP = prove
 (`!p z k. prime p /\ coprime(z,p) /\ 3 <= p /\ 1 <= k
           ==> ?w. coprime(w,p) /\
                   (1 + z * p EXP k) EXP p = 1 + w * p EXP (k + 1)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `1 + a * b = a * b + 1`] THEN
  REWRITE_TAC[BINOMIAL_THEOREM; EXP_ONE; MULT_CLAUSES] THEN
  SIMP_TAC[NSUM_CLAUSES_LEFT; LE_0; EXP; binom; MULT_CLAUSES; ADD_CLAUSES] THEN
  SUBGOAL_THEN `1 <= p` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[NSUM_CLAUSES_LEFT; BINOM_1; EXP_1; ARITH] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(p EXP (k + 2)) divides (nsum(2..p) (\i. binom(p,i) * (z * p EXP k) EXP i))`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:num` THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `z + p * d:num` THEN
    ASM_REWRITE_TAC[NUMBER_RULE
     `coprime(z + p * d:num,p) <=> coprime(z,p)`] THEN
    REWRITE_TAC[EXP_ADD] THEN ARITH_TAC] THEN
  MATCH_MP_TAC NSUM_CLOSED THEN
  REWRITE_TAC[DIVIDES_0; DIVIDES_ADD; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[MULT_EXP] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `a * b * c:num = b * c * a`] THEN
  REWRITE_TAC[EXP_EXP] THEN
  MATCH_MP_TAC DIVIDES_LMUL THEN ASM_CASES_TAC `j:num = p` THENL
   [MATCH_MP_TAC DIVIDES_RMUL THEN
    ASM_SIMP_TAC[DIVIDES_EXP_LE; ARITH_RULE `3 <= p ==> 2 <= p`] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k * 3` THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[LE_MULT_LCANCEL]];
    ONCE_REWRITE_TAC[MULT_SYM] THEN
    REWRITE_TAC[EXP; ARITH_RULE `k + 2 = SUC(k + 1)`] THEN
    MATCH_MP_TAC DIVIDES_MUL2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIVIDES_BINOM_PRIME THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ASM_SIMP_TAC[DIVIDES_EXP_LE; ARITH_RULE `3 <= p ==> 2 <= p`] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k * 2` THEN CONJ_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[LE_MULT_LCANCEL]]]]);;

let COPRIME_1_PLUS_POWER = prove
 (`!p z k. prime p /\ coprime(z,p) /\ 3 <= p
           ==> ?w. coprime(w,p) /\
                   (1 + z * p) EXP (p EXP k) = 1 + w * p EXP (k + 1)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; EXP_1; EXP] THENL [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[MULT_SYM] EXP_EXP)] THEN
  DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN STRIP_ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p:num`; `w:num`; `k + 1`] COPRIME_1_PLUS_POWER_STEP) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1`] THEN
  REWRITE_TAC[EXP_ADD; EXP_1; MULT_AC]);;

let PRIMITIVE_ROOT_MODULO_PRIMEPOWS = prove
 (`!p. prime p /\ 3 <= p
       ==> ?g. !j. 1 <= j ==> order(p EXP j) g = phi(p EXP j)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIMITIVE_ROOT_MODULO_PRIME) THEN
  REWRITE_TAC[IN_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p:num`; `g:num`] ORDER) THEN
  ASM_SIMP_TAC[CONG_TO_1; EXP_EQ_0; LE_1] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?x. coprime(p,y + (p - 1) * g EXP (p - 2) * x)` CHOOSE_TAC THENL
   [MP_TAC(ISPECL [`(&p - &1:int) * &g pow (p - 2)`; `&1 - &y:int`; `&p:int`]
                  INT_CONG_SOLVE_POS) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INT_COPRIME_LMUL; INT_COPRIME_LPOW] THEN
      REWRITE_TAC[INTEGER_RULE `coprime(p - &1,p)`; GSYM num_coprime] THEN
      ASM_SIMP_TAC[INT_OF_NUM_EQ; ARITH_RULE `3 <= p ==> ~(p = 0)`] THEN
      DISJ1_TAC THEN MATCH_MP_TAC PRIME_COPRIME_LT THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      REWRITE_TAC[GSYM INT_EXISTS_POS] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
       `(x:int == &1 - y) (mod n) ==> coprime(n,y + x)`)) THEN
      ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_POW; INT_OF_NUM_MUL;
                   INT_OF_NUM_ADD; GSYM num_coprime;
                    ARITH_RULE `3 <= p ==> 1 <= p`] THEN
      REWRITE_TAC[MULT_ASSOC]];
    ALL_TAC] THEN
  EXISTS_TAC `g + p * x:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  STRIP_ASSUME_TAC(ISPECL [`p EXP j`; `g + p * x:num`] ORDER_WORKS) THEN
  MP_TAC(SPECL [`p:num`; `g + p * x:num`; `order (p EXP j) (g + p * x)`]
      ORDER_DIVIDES) THEN
  SUBGOAL_THEN `order p (g + p * x) = p - 1` SUBST1_TAC THENL
   [ASM_MESON_TAC[ORDER_CONG; NUMBER_RULE `(g:num == g + p * x) (mod p)`];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC(NUMBER_RULE
     `!y. (a == 1) (mod y) /\ x divides y ==> (a == 1) (mod x)`) THEN
    EXISTS_TAC `p EXP j` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[DIVIDES_REFL; DIVIDES_REXP; LE_1];
    REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `d:num` THEN
    DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)] THEN
  MP_TAC(ISPECL [`g + p * x:num`; `p EXP j`] ORDER_DIVIDES_PHI) THEN
  ASM_SIMP_TAC[PHI_PRIMEPOW; LE_1; COPRIME_LEXP] THEN ANTS_TAC THENL
   [REWRITE_TAC[NUMBER_RULE `coprime(p,g + p * x) <=> coprime(g,p)`] THEN
    MATCH_MP_TAC PRIME_COPRIME_LT THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p EXP j - p EXP (j - 1) = (p - 1) * p EXP (j - 1)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `1 <= j` THEN SPEC_TAC(`j:num`,`j:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[ARITH; SUC_SUB1] THEN
    REWRITE_TAC[EXP; RIGHT_SUB_DISTRIB] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
   `(a * x:num) divides (a * y) ==> ~(a = 0) ==> x divides y`)) THEN
  ASM_SIMP_TAC[DIVIDES_PRIMEPOW; ARITH_RULE `3 <= p ==> ~(p - 1 = 0)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `?z. (g + p * x) EXP (p - 1) = 1 + z * p /\ coprime(z,p)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BINOMIAL_THEOREM] THEN
    ASM_SIMP_TAC[NSUM_CLAUSES_RIGHT; LE_0; ARITH_RULE
     `3 <= p ==> 0 < p - 1`] THEN
    REWRITE_TAC[BINOM_REFL; SUB_REFL; EXP; MULT_CLAUSES] THEN
    EXISTS_TAC
     `y + nsum(0..p-2) (\k. binom(p - 1,k) * g EXP k *
                            p EXP (p - 2 - k) * x EXP (p - 1 - k))` THEN
    REWRITE_TAC[ARITH_RULE `n - 1 - 1 = n - 2`] THEN
    SIMP_TAC[ARITH_RULE `s + 1 + y * p = 1 + (y + t) * p <=> s = p * t`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM NSUM_LMUL] THEN MATCH_MP_TAC NSUM_EQ THEN
      X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      SIMP_TAC[ARITH_RULE `p * b * g * pp * x:num = b * g * (p * pp) * x`] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MULT_EXP] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[NSUM_CLAUSES_RIGHT; LE_0; ARITH_RULE
     `3 <= p ==> 0 < p - 2`] THEN
    REWRITE_TAC[BINOM_REFL; SUB_REFL; EXP; MULT_CLAUSES] THEN
    ASM_SIMP_TAC[EXP_1; ARITH_RULE `3 <= p ==> p - 1 - (p - 2) = 1`] THEN
    SUBGOAL_THEN `binom(p - 1,p - 2) = p - 1` SUBST1_TAC THENL
     [SUBGOAL_THEN `p - 1 = SUC(p - 2)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[BINOM_PENULT]];
      ALL_TAC] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `coprime(p:num,y + x) /\ p divides z ==> coprime(y + z + x,p)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NSUM_CLOSED THEN
    REWRITE_TAC[DIVIDES_0; DIVIDES_ADD; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REPLICATE_TAC 2 (MATCH_MP_TAC DIVIDES_LMUL) THEN
    MATCH_MP_TAC DIVIDES_RMUL THEN MATCH_MP_TAC DIVIDES_REXP THEN
    REWRITE_TAC[DIVIDES_REFL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?w. (g + p * x) EXP ((p - 1) * p EXP k) = 1 + p EXP (k + 1) * w /\
        coprime(w,p)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM EXP_EXP] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    GEN_REWRITE_TAC (BINDER_CONV o funpow 3 RAND_CONV) [MULT_SYM] THEN
    MATCH_MP_TAC COPRIME_1_PLUS_POWER THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC
     `((g + p * x) EXP ((p - 1) * p EXP k) == 1) (mod (p EXP j))` THEN
    ASM_REWRITE_TAC[NUMBER_RULE `(1 + x == 1) (mod n) <=> n divides x`] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`p:num`; `j:num`; `w:num`; `p EXP (k + 1)`]
       COPRIME_EXP_DIVPROD) THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[DIVIDES_EXP_LE; ARITH_RULE `3 <= p ==> 2 <= p`] THEN
    UNDISCH_TAC `k <= j - 1` THEN ARITH_TAC]);;

let PRIMITIVE_ROOT_MODULO_PRIMEPOW = prove
 (`!p k. prime p /\ 3 <= p /\ 1 <= k
         ==> ?x. x IN 1..(p EXP k - 1) /\ order (p EXP k) x = phi(p EXP k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `p:num` PRIMITIVE_ROOT_MODULO_PRIMEPOWS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `x:num` THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `x MOD (p EXP k)` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_NUMSEG; ARITH_RULE `1 <= x <=> ~(x = 0)`] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`p EXP k`; `x:num`] DIVIDES_MOD) THEN
      ASM_SIMP_TAC[EXP_EQ_0; ARITH_RULE `3 <= p ==> ~(p = 0)`] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`p EXP k`; `x:num`] ORDER) THEN
      DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
       `(x == 1) (mod p) ==> p divides x ==> p divides 1`)) THEN
      ASM_SIMP_TAC[EXP_EQ_1; DIVIDES_ONE; LE_1] THEN
      ASM_SIMP_TAC[ARITH_RULE `3 <= p ==> ~(p = 1)`] THEN
      MATCH_MP_TAC DIVIDES_REXP THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ARITH_RULE `1 <= p ==> ~(p = 0)`) THEN
      MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN
      MATCH_MP_TAC(ARITH_RULE `~(p = 0) ==> 1 <= p`) THEN
      ASM_SIMP_TAC[EXP_EQ_0] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC(ARITH_RULE `a < b ==> a <= b - 1`) THEN
      MP_TAC(ISPECL [`x:num`; `p EXP k`] DIVISION) THEN
      ASM_SIMP_TAC[EXP_EQ_0; ARITH_RULE `3 <= p ==> ~(p = 0)`]];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `order (p EXP k) x` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC ORDER_CONG THEN REWRITE_TAC[CONG_MOD]]);;

(* ------------------------------------------------------------------------- *)
(* Double prime powers and the other remaining positive cases 2 and 4.       *)
(* ------------------------------------------------------------------------- *)

let PRIMITIVE_ROOT_MODULO_2 = prove
 (`?x. x IN 1..1 /\ order 2 x = phi(2)`,
  EXISTS_TAC `1` THEN REWRITE_TAC[IN_NUMSEG; ARITH] THEN
  SIMP_TAC[PHI_PRIME; PRIME_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC ORDER_UNIQUE THEN
  REWRITE_TAC[ARITH_RULE `~(0 < m /\ m < 1)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV CONG_CONV) THEN
  REWRITE_TAC[]);;

let PRIMITIVE_ROOT_MODULO_4 = prove
 (`?x. x IN 1..3 /\ order 4 x = phi(4)`,
  EXISTS_TAC `3` THEN REWRITE_TAC[IN_NUMSEG; ARITH] THEN
  SUBST1_TAC(ARITH_RULE `4 = 2 EXP 2`) THEN
  SIMP_TAC[PHI_PRIMEPOW; PRIME_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC ORDER_UNIQUE THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; ARITH_RULE `0 < m /\ m < 2 <=> m = 1`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV CONG_CONV) THEN
  REWRITE_TAC[]);;

let PRIMITIVE_ROOT_DOUBLE_LEMMA = prove
 (`!n a. ODD n /\ ODD a /\ order n a = phi n
         ==> order (2 * n) a = phi(2 * n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ORDER_UNIQUE THEN
  ASM_SIMP_TAC[CONG_CHINESE_EQ; COPRIME_2; PHI_MULTIPLICATIVE] THEN
  REWRITE_TAC[PHI_2; MULT_CLAUSES] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[ODD; LE_1; PHI_LOWERBOUND_1_STRONG];
    ASM_REWRITE_TAC[GSYM ODD_MOD_2; ODD_EXP];
    ASM_MESON_TAC[ORDER_WORKS];
    ASM_MESON_TAC[ORDER_WORKS]]);;

let PRIMITIVE_ROOT_MODULO_DOUBLE_PRIMEPOW = prove
 (`!p k. prime p /\ 3 <= p /\ 1 <= k
         ==> ?x. x IN 1..(2 * p EXP k - 1) /\
                 order (2 * p EXP k) x = phi(2 * p EXP k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `p:num` PRIME_ODD) THEN
  ASM_SIMP_TAC[ARITH_RULE `3 <= p ==> ~(p = 2)`] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIMITIVE_ROOT_MODULO_PRIMEPOW) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num` MP_TAC) THEN REWRITE_TAC[IN_NUMSEG] THEN
  STRIP_TAC THEN DISJ_CASES_TAC (SPEC `g:num` EVEN_OR_ODD) THENL
   [EXISTS_TAC `g + p EXP k` THEN CONJ_TAC THENL
     [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(ARITH_RULE
       `g <= x - 1 /\ p EXP 1 <= x ==> g + p <= 2 * x - 1`) THEN
      ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
      ALL_TAC];
    EXISTS_TAC `g:num` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]] THEN
  MATCH_MP_TAC PRIMITIVE_ROOT_DOUBLE_LEMMA THEN
  ASM_REWRITE_TAC[ODD_ADD; ODD_EXP; NOT_ODD] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC ORDER_CONG THEN
  CONV_TAC NUMBER_RULE);;

(* ------------------------------------------------------------------------- *)
(* A couple of degenerate case not usually considered.                       *)
(* ------------------------------------------------------------------------- *)

let PRIMITIVE_ROOT_MODULO_0 = prove
 (`(?x. order 0 x = phi(0))`,
  EXISTS_TAC `2` THEN REWRITE_TAC[PHI_0; ORDER_EQ_0; COPRIME_2; ODD]);;

let PRIMITIVE_ROOT_MODULO_1 = prove
 (`?x. order 1 x = phi(1)`,
  EXISTS_TAC `1` THEN REWRITE_TAC[PHI_1] THEN MATCH_MP_TAC ORDER_UNIQUE THEN
  REWRITE_TAC[ARITH_RULE `0 < m /\ m < 1 <=> F`; EXP_1; CONG_REFL] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The negative results.                                                     *)
(* ------------------------------------------------------------------------- *)

let CONG_TO_1_POW2 = prove
 (`!k x. ODD x /\ 1 <= k ==> (x EXP (2 EXP k) == 1) (mod (2 EXP (k + 2)))`,
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; EXP] THEN
  CONV_TAC NUM_REDUCE_CONV THEN GEN_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[CONG_TO_1] THEN DISJ2_TAC THEN
    REWRITE_TAC[GSYM EVEN_EXISTS; ARITH_RULE
     `SUC(2 * m) EXP 2 = 1 + q * 8 <=> m * (m + 1) = 2 * q`] THEN
    REWRITE_TAC[EVEN_MULT; EVEN_ADD; ARITH] THEN CONV_TAC TAUT;
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] EXP_MULT; LE_1] THEN
    REWRITE_TAC[CONG_TO_1; EXP_EQ_1; ADD_EQ_0; MULT_EQ_1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
    REWRITE_TAC[EQ_MULT_LCANCEL; EXP_EQ_0; ARITH; GSYM EVEN_EXISTS; ARITH_RULE
     `(1 + m * n) EXP 2 = 1 + q * 2 * n <=>
      n * m * (2 + m * n) = n * 2 * q`] THEN
    REWRITE_TAC[EVEN_MULT; EVEN_ADD; EVEN_EXP; ARITH] THEN ARITH_TAC]);;

let NO_PRIMITIVE_ROOT_MODULO_POW2 = prove
 (`!k. 3 <= k ==> ~(?x. order (2 EXP k) x = phi(2 EXP k))`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(SPEC `x:num` EVEN_OR_ODD) THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `a = b ==> 1 <= b /\ a = 0 ==> F`)) THEN
    ASM_SIMP_TAC[ORDER_EQ_0; PHI_LOWERBOUND_1_STRONG; LE_1; EXP_EQ_0; ARITH;
                 COPRIME_LEXP; COPRIME_2; DE_MORGAN_THM; NOT_ODD] THEN
    ASM_ARITH_TAC;
    MP_TAC(CONJUNCT2(ISPECL [`2 EXP k`; `x:num`] ORDER_WORKS)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `2 EXP (k - 2)`) THEN
    ASM_SIMP_TAC[PHI_PRIMEPOW; PRIME_2; ARITH_RULE `3 <= k ==> ~(k = 0)`] THEN
    ABBREV_TAC `j = k - 2` THEN
    SUBGOAL_THEN `k - 1 = j + 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k = j + 2` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `1 <= j` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[CONG_TO_1_POW2; ARITH_RULE `0 < x <=> ~(x = 0)`] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH] THEN
    MATCH_MP_TAC(ARITH_RULE `a + b:num < c ==> a < c - b`) THEN
    REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `x + x * 2 < x * 4 <=> ~(x = 0)`] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH]]);;

let NO_PRIMITIVE_ROOT_MODULO_COMPOSITE = prove
 (`!a b. 3 <= a /\ 3 <= b /\ coprime(a,b)
         ==> ~(?x. order (a * b) x = phi(a * b))`,
  SIMP_TAC[PHI_MULTIPLICATIVE] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a * b:num`; `x:num`] ORDER_WORKS) THEN
  ASM_SIMP_TAC[CONG_CHINESE_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(phi a * phi b) DIV 2`) THEN
  REWRITE_TAC[ARITH_RULE `0 < a DIV 2 /\ a DIV 2 < a <=> 2 <= a`; NOT_IMP] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `2 * 2 <= x ==> 2 <= x`) THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC[PHI_LOWERBOUND_2];
    SUBGOAL_THEN `EVEN(phi b)` MP_TAC THENL
     [ASM_SIMP_TAC[EVEN_PHI]; SIMP_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM]] THEN
    REWRITE_TAC[ARITH_RULE `(a * 2 * b) DIV 2 = a * b`];
    SUBGOAL_THEN `EVEN(phi a)` MP_TAC THENL
     [ASM_SIMP_TAC[EVEN_PHI]; SIMP_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM]] THEN
    REWRITE_TAC[ARITH_RULE `((2 * a) * b) DIV 2 = b * a`]] THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[GSYM EXP_EXP] THEN SUBST1_TAC(SYM(SPEC `m:num` EXP_ONE)) THEN
  MATCH_MP_TAC CONG_EXP THEN MATCH_MP_TAC FERMAT_LITTLE THEN
  MP_TAC(ISPECL [`a * b:num`; `x:num`] ORDER_EQ_0) THEN
  ASM_SIMP_TAC[MULT_EQ_0; LE_1; PHI_LOWERBOUND_1_STRONG;
               ARITH_RULE `3 <= p ==> 1 <= p`] THEN
  CONV_TAC NUMBER_RULE);;

(* ------------------------------------------------------------------------- *)
(* Equivalences, one with some degenerate cases, one more conventional.      *)
(* ------------------------------------------------------------------------- *)

let PRIMITIVE_ROOT_EXISTS = prove
 (`!n. (?x. order n x = phi n) <=>
       n = 0 \/ n = 2 \/ n = 4 \/
       ?p k. prime p /\ 3 <= p /\ (n = p EXP k \/ n = 2 * p EXP k)`,
  GEN_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[PRIMITIVE_ROOT_MODULO_0] THEN
  ASM_CASES_TAC `n = 2` THENL
   [ASM_MESON_TAC[PRIMITIVE_ROOT_MODULO_2]; ALL_TAC] THEN
  ASM_CASES_TAC `n = 4` THENL
   [ASM_MESON_TAC[PRIMITIVE_ROOT_MODULO_4]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[PRIMITIVE_ROOT_MODULO_1] THEN
    MAP_EVERY EXISTS_TAC [`3`; `0`] THEN
    CONV_TAC(ONCE_DEPTH_CONV PRIME_CONV) THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  EQ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `k:num`] THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[EXP; MULT_CLAUSES] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[LE_1; PRIMITIVE_ROOT_MODULO_PRIMEPOW;
                  PRIMITIVE_ROOT_MODULO_DOUBLE_PRIMEPOW]] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `n:num` PRIMEPOW_FACTOR) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `k:num`; `m:num`] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  ASM_CASES_TAC `m = 1` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p:num`; `k:num`]) THEN
    ASM_SIMP_TAC[PRIME_GE_2; ARITH_RULE
     `2 <= p ==> (~(3 <= p) <=> p = 2)`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_CASES_TAC `3 <= k` THENL
     [ASM_MESON_TAC[NO_PRIMITIVE_ROOT_MODULO_POW2]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
      `~(3 <= k) ==> 1 <= k ==> k = 1 \/ k = 2`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_CASES_TAC `m = 2` THENL
   [ASM_REWRITE_TAC[COPRIME_2] THEN
    ASM_CASES_TAC `p = 2` THEN ASM_REWRITE_TAC[ARITH] THEN
    STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    SUBGOAL_THEN `3 <= p` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[MULT_SYM];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k = 1` THENL
   [UNDISCH_THEN `k = 1` SUBST_ALL_TAC;
    MP_TAC(SPECL [`p EXP k`; `m:num`] NO_PRIMITIVE_ROOT_MODULO_COMPOSITE) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[COPRIME_LEXP] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE `2 EXP 2 <= x ==> 3 <= x`) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p EXP 2` THEN
    ASM_REWRITE_TAC[EXP_MONO_LE; LE_EXP] THEN
    ASM_SIMP_TAC[PRIME_GE_2; PRIME_IMP_NZ] THEN ASM_ARITH_TAC] THEN
  ASM_CASES_TAC `p = 2` THENL
   [UNDISCH_THEN `p = 2` SUBST_ALL_TAC;
    MP_TAC(SPECL [`p EXP 1`; `m:num`] NO_PRIMITIVE_ROOT_MODULO_COMPOSITE) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[COPRIME_LEXP] THEN REWRITE_TAC[EXP_1] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ASM_ARITH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EXP_1]) THEN REWRITE_TAC[EXP_1] THEN
  MP_TAC(ISPEC `m:num` PRIMEPOW_FACTOR) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `j:num`; `r:num`] THEN
  ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  STRIP_TAC THEN UNDISCH_TAC `coprime(2,m)` THEN
  ASM_SIMP_TAC[COPRIME_RMUL; COPRIME_REXP; LE_1] THEN
  REWRITE_TAC[COPRIME_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `3 <= q` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(p = 2) /\ 2 <= p ==> 3 <= p`) THEN
    ASM_SIMP_TAC[PRIME_GE_2] THEN DISCH_TAC THEN
    UNDISCH_TAC `ODD q` THEN ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`q:num`; `j:num`]) THEN
  ASM_CASES_TAC `r = 1` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`2 * r`; `q EXP j`] NO_PRIMITIVE_ROOT_MODULO_COMPOSITE) THEN
  REWRITE_TAC[COPRIME_LMUL; COPRIME_REXP] THEN ASM_REWRITE_TAC[COPRIME_2] THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_AC; NOT_EXISTS_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `3 <= r * 2 <=> ~(r = 0 \/ r = 1)`] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `q EXP 1` THEN
  ASM_REWRITE_TAC[LE_EXP; ARITH; COND_ID] THEN ASM_REWRITE_TAC[EXP_1]);;

let PRIMITIVE_ROOT_EXISTS_NONTRIVIAL = prove
 (`!n. (?x. x IN 1..n-1 /\ order n x = phi n) <=>
       n = 2 \/ n = 4 \/
       ?p k. prime p /\ 3 <= p /\ 1 <= k /\ (n = p EXP k \/ n = 2 * p EXP k)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[IN_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC(TAUT `~a /\ ~b ==> (a <=> b)`) THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    REWRITE_TAC[MULT_EQ_0; EXP_EQ_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[IN_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC(TAUT `~a /\ ~b ==> (a <=> b)`) THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    REWRITE_TAC[MULT_EQ_1; EXP_EQ_1] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `?x. order n x = phi n` THEN CONJ_TAC THENL
   [EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:num`) THEN EXISTS_TAC `x MOD n` THEN
    ASM_SIMP_TAC[IN_NUMSEG; DIVISION; ARITH_RULE
     `~(n = 0) /\ ~(n = 1) ==> (x <= n - 1 <=> x < n)`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`] THEN
      ASM_SIMP_TAC[GSYM DIVIDES_MOD] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`n:num`; `x:num`] ORDER_EQ_0) THEN
      ASM_SIMP_TAC[LE_1; PHI_LOWERBOUND_1_STRONG] THEN
      REWRITE_TAC[coprime] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
      ASM_REWRITE_TAC[DIVIDES_REFL];
      FIRST_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC ORDER_CONG THEN
      ASM_SIMP_TAC[CONG_MOD]];
    ASM_REWRITE_TAC[PRIMITIVE_ROOT_EXISTS] THEN
    ASM_CASES_TAC `n = 2` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `n = 4` THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:num` THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
    CONV_TAC(BINOP_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
    ASM_CASES_TAC `k = 0` THEN ASM_SIMP_TAC[LE_1] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC]);;
