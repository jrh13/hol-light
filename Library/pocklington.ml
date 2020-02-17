(* ========================================================================= *)
(* HOL primality proving via Pocklington-optimized  Pratt certificates.      *)
(* ========================================================================= *)

needs "Library/iter.ml";;
needs "Library/prime.ml";;

prioritize_num();;

let num_0 = Int 0;;
let num_1 = Int 1;;
let num_2 = Int 2;;

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
 (`!p. prime p <=> ~(p = 0) /\ ~(p = 1) /\ !m. 0 < m /\ m < p ==> coprime(p,m)`,
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

let CONG_MOD_2 = prove
 (`!a b. (a == b) (mod 2) <=> (EVEN a <=> EVEN b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONG; MOD_2_CASES] THEN
  ASM_CASES_TAC `EVEN a` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `EVEN b` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CONG_MOD_2_ALT = prove
 (`!a b. (a == b) (mod 2) <=> (ODD a <=> ODD b)`,
  REWRITE_TAC[CONG_MOD_2; GSYM NOT_ODD] THEN MESON_TAC[]);;

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

let CONG_MINUS1 = prove
 (`!a b n. (a == n - 1) (mod n) <=> n = 0 /\ a = 0 \/ n divides (a + 1)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[SUB_0; CONG_MOD_0; DIVIDES_ZERO] THEN ARITH_TAC;
    ONCE_REWRITE_TAC[NUMBER_RULE
     `(a == b) (mod n) <=> (a + 1 == b + 1) (mod n)`] THEN
    ASM_SIMP_TAC[SUB_ADD; LE_1] THEN CONV_TAC NUMBER_RULE]);;

let CONG_MINUS1_SQUARED = prove
 (`!p. ((p - 1) EXP 2 == 1) (mod p) <=> ~(p = 0)`,
  GEN_TAC THEN ASM_CASES_TAC `p = 0` THEN
  ASM_REWRITE_TAC[CONG_MOD_0; ARITH] THEN
  ONCE_REWRITE_TAC[NUMBER_RULE
   `(n EXP 2 == m) (mod p) <=> ((n + 1) EXP 2 == m + 2 * n + 1) (mod p)`] THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1; NUMBER_RULE
   `(p EXP 2 == 1 + 2 * n + 1) (mod p) <=> p divides (2 * (n + 1))`] THEN
  CONV_TAC NUMBER_RULE);;

let CONG_CASES = prove
 (`!x y n. (x == y) (mod n) <=> (?q. x = q * n + y) \/ (?q. y = q * n + x)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[] THEN NUMBER_TAC] THEN
  REWRITE_TAC[cong; nat_mod; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q1:num`; `q2:num`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP(ARITH_RULE
   `x + a = y + b ==> x = (b - a) + y \/ y = (a - b) + x`)) THEN
  REWRITE_TAC[GSYM LEFT_SUB_DISTRIB] THEN MESON_TAC[MULT_SYM]);;

let CONG_MULT_LCANCEL = prove
 (`!a n x y. coprime(a,n) /\ (a * x == a * y) (mod n) ==> (x == y) (mod n)`,
  NUMBER_TAC);;

let CONG_MULT_RCANCEL = prove
 (`!a n x y. coprime(a,n) /\ (x * a == y * a) (mod n) ==> (x == y) (mod n)`,
  NUMBER_TAC);;

let CONG_REFL = prove
 (`!x n. (x == x) (mod n)`,
  NUMBER_TAC);;

let EQ_IMP_CONG = prove
 (`!a b n. a = b ==> (a == b) (mod n)`,
  SIMP_TAC[CONG_REFL]);;

let CONG_SYM = prove
 (`!x y n. (x == y) (mod n) <=> (y == x) (mod n)`,
  NUMBER_TAC);;

let CONG_TRANS = prove
 (`!x y z n. (x == y) (mod n) /\ (y == z) (mod n) ==> (x == z) (mod n)`,
  NUMBER_TAC);;

let CONG_ADD = prove
 (`!x x' y y'.
     (x == x') (mod n) /\ (y == y') (mod n) ==> (x + y == x' + y') (mod n)`,
  NUMBER_TAC);;

let CONG_MULT = prove
 (`!x x' y y'.
     (x == x') (mod n) /\ (y == y') (mod n) ==> (x * y == x' * y') (mod n)`,
  NUMBER_TAC);;

let CONG_MULT_1 = prove
 (`!n x y. (x == 1) (mod n) /\ (y == 1) (mod n) ==> (x * y == 1) (mod n)`,
  NUMBER_TAC);;

let CONG_EXP = prove
 (`!n k x y. (x == y) (mod n) ==> (x EXP k == y EXP k) (mod n)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[CONG_MULT; EXP; CONG_REFL]);;

let CONG_EXP_1 = prove
 (`!x n k. (x == 1) (mod n) ==> (x EXP k == 1) (mod n)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP CONG_EXP) THEN
  REWRITE_TAC[EXP_ONE]);;

let CONG_SUB = prove
 (`!x x' y y'.
     (x == x') (mod n) /\ (y == y') (mod n) /\ y <= x /\ y' <= x'
     ==> (x - y == x' - y') (mod n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cong; nat_mod] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
   `(x + a = x' + a') /\ (y + b = y' + b') /\ y <= x /\ y' <= x'
    ==> ((x - y) + (a + b') = (x' - y') + (a' + b))`)) THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN MESON_TAC[]);;

let CONG_MULT_LCANCEL_EQ = prove
 (`!a n x y. coprime(a,n) ==> ((a * x == a * y) (mod n) <=> (x == y) (mod n))`,
  NUMBER_TAC);;

let CONG_MULT_RCANCEL_EQ = prove
 (`!a n x y. coprime(a,n) ==> ((x * a == y * a) (mod n) <=> (x == y) (mod n))`,
  NUMBER_TAC);;

let CONG_ADD_LCANCEL_EQ = prove
 (`!a n x y. (a + x == a + y) (mod n) <=> (x == y) (mod n)`,
  NUMBER_TAC);;

let CONG_ADD_RCANCEL_EQ = prove
 (`!a n x y. (x + a == y + a) (mod n) <=> (x == y) (mod n)`,
  NUMBER_TAC);;

let CONG_ADD_RCANCEL = prove
 (`!a n x y. (x + a == y + a) (mod n) ==> (x == y) (mod n)`,
  NUMBER_TAC);;

let CONG_ADD_LCANCEL = prove
 (`!a n x y. (a + x == a + y) (mod n) ==> (x == y) (mod n)`,
  NUMBER_TAC);;

let CONG_ADD_LCANCEL_EQ_0 = prove
 (`!a n x y. (a + x == a) (mod n) <=> (x == 0) (mod n)`,
  NUMBER_TAC);;

let CONG_ADD_RCANCEL_EQ_0 = prove
 (`!a n x y. (x + a == a) (mod n) <=> (x == 0) (mod n)`,
  NUMBER_TAC);;

let CONG_IMP_EQ = prove
 (`!x y n. x < n /\ y < n /\ (x == y) (mod n) ==> x = y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[LT] THEN
  ASM_MESON_TAC[CONG; MOD_LT]);;

let CONG_DIVIDES_MODULUS = prove
 (`!x y m n. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`,
  NUMBER_TAC);;

let CONG_0_DIVIDES = prove
 (`!n x. (x == 0) (mod n) <=> n divides x`,
  NUMBER_TAC);;

let CONG_1_DIVIDES = prove
 (`!n x. (x == 1) (mod n) ==> n divides (x - 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides; cong; nat_mod] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
   `(x + q1 = 1 + q2) ==> ~(x = 0) ==> (x - 1 = q2 - q1)`)) THEN
  ASM_CASES_TAC `x = 0` THEN
  ASM_REWRITE_TAC[ARITH; GSYM LEFT_SUB_DISTRIB] THEN
  ASM_MESON_TAC[MULT_CLAUSES]);;

let CONG_1_DIVIDES_EQ = prove
 (`!n x. (x == 1) (mod n) <=> (x = 0 ==> n = 1) /\ n divides (x - 1)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[NUMBER_RULE `(0 == a) (mod n) <=> n divides a`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIVIDES_ONE; DIVIDES_0];
    ONCE_REWRITE_TAC[CONG_SYM] THEN ONCE_REWRITE_TAC[CONG_SUB_CASES] THEN
    ASM_SIMP_TAC[LE_1] THEN CONV_TAC NUMBER_RULE]);;

let CONG_DIVIDES = prove
 (`!x y n. (x == y) (mod n) ==> (n divides x <=> n divides y)`,
  NUMBER_TAC);;

let CONG_COPRIME = prove
 (`!x y n. (x == y) (mod n) ==> (coprime(n,x) <=> coprime(n,y))`,
  NUMBER_TAC);;

let CONG_GCD_RIGHT = prove
 (`!x y n. (x == y) (mod n) ==> gcd(n,x) = gcd(n,y)`,
  NUMBER_TAC);;

let CONG_GCD_LEFT = prove
 (`!x y n. (x == y) (mod n) ==> gcd(x,n) = gcd(y,n)`,
  NUMBER_TAC);;

let CONG_MOD = prove
 (`!a n. (a MOD n == a) (mod n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[CONG_REFL; MOD_ZERO] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION) THEN
  DISCH_THEN(MP_TAC o SPEC `a:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[cong; nat_mod] THEN
  MAP_EVERY EXISTS_TAC [`a DIV n`; `0`] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; ADD_AC; MULT_AC]);;

let MOD_MULT_CONG = prove
 (`!a b x y. ((x MOD (a * b) == y) (mod a) <=> (x == y) (mod a))`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `(x MOD (a * b) == x) (mod a)`
   (fun th -> MESON_TAC[th; CONG_TRANS; CONG_SYM]) THEN
  MATCH_MP_TAC CONG_DIVIDES_MODULUS THEN EXISTS_TAC `a * b` THEN
  ASM_SIMP_TAC[CONG_MOD; MULT_EQ_0; DIVIDES_RMUL; DIVIDES_REFL]);;

let CONG_MOD_MULT = prove
 (`!x y m n. (x == y) (mod n) /\ m divides n ==> (x == y) (mod m)`,
  NUMBER_TAC);;

let CONG_MOD_LT = prove
 (`!y. y < n ==> (x MOD n = y <=> (x == y) (mod n))`,
  MESON_TAC[MOD_LT; CONG; LT]);;

let MOD_UNIQUE = prove
 (`!m n p. m MOD n = p <=> ((n = 0 /\ m = p) \/ p < n) /\ (m == p) (mod n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[CONG_MOD_0; LT] THENL
   [ASM_MESON_TAC[DIVISION_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[CONG] THEN ASM_MESON_TAC[DIVISION; MOD_LT]);;

let CONG_DIV = prove
 (`!m n a b.
        ~(m = 0) /\ (a == m * b) (mod (m * n)) ==> (a DIV m == b) (mod n)`,
  MESON_TAC[CONG_DIV2; DIV_MULT]);;

let CONG_SQUARE_1_PRIME_POWER = prove
 (`!p k x.
        prime p /\ ~(p = 2)
        ==> ((x EXP 2 == 1) (mod (p EXP k)) <=>
             (x == 1) (mod (p EXP k)) \/ (x == p EXP k - 1) (mod (p EXP k)))`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[EXP; CONG_MOD_1] THEN
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[PRIME_0] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[PRIME_1] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[CONG_MINUS1; CONG_1_DIVIDES_EQ] THEN
  ASM_REWRITE_TAC[EXP_EQ_0; EXP_EQ_1] THEN
  ASM_CASES_TAC `x = 0` THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; DIVIDES_ONE; EXP_EQ_1; ARITH] THEN
  SUBGOAL_THEN `x EXP 2 - 1 = (x - 1) * (x + 1)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_MUL] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; EXP_EQ_0; LE_1] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_POW] THEN
    INT_ARITH_TAC;
    MATCH_MP_TAC PRIME_DIVPROD_POW_GEN_EQ THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GCD_SYM] THEN REWRITE_TAC[DIVIDES_GCD] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_SUB) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(x = 0) ==> (x + 1) - (x - 1) = 2`] THEN
    ASM_SIMP_TAC[DIVIDES_PRIME_PRIME; PRIME_2]]);;

(* ------------------------------------------------------------------------- *)
(* Some things when we know more about the order.                            *)
(* ------------------------------------------------------------------------- *)

let CONG_LT = prove
 (`!x y n. y < n ==> ((x == y) (mod n) <=> ?d. x = d * n + y)`,
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LT;
              GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
  REWRITE_TAC[num_congruent; int_congruent] THEN
  REWRITE_TAC[INT_ARITH `x = m * n + y <=> x - y:int = n * m`] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_TAC `d:int`) THEN
  DISJ_CASES_TAC(SPEC `d:int` INT_IMAGE) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (INT_ARITH
   `x - y:int = n * --m ==> y = x + n * m`)) THEN
  POP_ASSUM MP_TAC THEN DISJ_CASES_TAC(ARITH_RULE `m = 0 \/ 1 <= m`) THEN
  ASM_REWRITE_TAC[INT_MUL_RZERO; INT_ARITH `x - (x + a):int = --a`] THENL
   [STRIP_TAC THEN EXISTS_TAC `0` THEN INT_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC) THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_MUL; INT_OF_NUM_LT] THEN
    ARITH_TAC]);;

let CONG_LE = prove
 (`!x y n. y <= x ==> ((x == y) (mod n) <=> ?q. x = q * n + y)`,
  ONCE_REWRITE_TAC[CONG_SYM] THEN ONCE_REWRITE_TAC[CONG_SUB_CASES] THEN
  SIMP_TAC[ARITH_RULE `y <= x ==> (x = a + y <=> x - y = a)`] THEN
  REWRITE_TAC[CONG_0; divides] THEN MESON_TAC[MULT_SYM]);;

let CONG_TO_1 = prove
 (`!a n. (a == 1) (mod n) <=> a = 0 /\ n = 1 \/ ?m. a = 1 + m * n`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[CONG_MOD_1] THENL
   [MESON_TAC[ARITH_RULE `n = 0 \/ n = 1 + (n - 1) * 1`]; ALL_TAC] THEN
  DISJ_CASES_TAC(ARITH_RULE `a = 0 \/ ~(a = 0) /\ 1 <= a`) THEN
  ASM_SIMP_TAC[CONG_LE] THENL [ALL_TAC; MESON_TAC[ADD_SYM; MULT_SYM]] THEN
  ASM_MESON_TAC[CONG_SYM; CONG_0; DIVIDES_ONE; ARITH_RULE `~(0 = 1 + a)`]);;

(* ------------------------------------------------------------------------- *)
(* In particular two common cases.                                           *)
(* ------------------------------------------------------------------------- *)

let EVEN_MOD_2 = prove
 (`EVEN n <=> (n == 0) (mod 2)`,
  SIMP_TAC[EVEN_EXISTS; CONG_LT; ARITH; ADD_CLAUSES; MULT_AC]);;

let ODD_MOD_2 = prove
 (`ODD n <=> (n == 1) (mod 2)`,
  SIMP_TAC[ODD_EXISTS; CONG_LT; ARITH; ADD_CLAUSES; ADD1; MULT_AC]);;

(* ------------------------------------------------------------------------- *)
(* Conversion to evaluate congruences.                                       *)
(* ------------------------------------------------------------------------- *)

let CONG_CONV =
  let pth = prove
   (`(x == y) (mod n) <=>
     if x <= y then n divides (y - x) else n divides (x - y)`,
    ONCE_REWRITE_TAC[CONG_SUB_CASES] THEN REWRITE_TAC[CONG_0_DIVIDES]) in
  GEN_REWRITE_CONV I [pth] THENC
  RATOR_CONV(LAND_CONV NUM_LE_CONV) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES] THENC
  RAND_CONV NUM_SUB_CONV THENC
  DIVIDES_CONV;;

(* ------------------------------------------------------------------------- *)
(* Some basic theorems about solving congruences.                            *)
(* ------------------------------------------------------------------------- *)

let CONG_SOLVE_EQ = prove
 (`!n a b. (?x. (a * x == b) (mod n)) <=> gcd(a,n) divides b`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [NUMBER_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; GCD_0]
  THENL [NUMBER_TAC; REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `c:num` THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP BEZOUT_GCD_STRONG) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
  EXISTS_TAC `c * x:num` THEN POP_ASSUM MP_TAC THEN CONV_TAC NUMBER_RULE);;

let CONG_SOLVE_LT_EQ = prove
 (`!n a b. (?x. x < n /\ (a * x == b) (mod n)) <=>
           ~(n = 0) /\ gcd(a,n) divides b`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[CONJUNCT1 LT] THEN REWRITE_TAC[GSYM CONG_SOLVE_EQ] THEN
  MATCH_MP_TAC(MESON[DIVISION]
   `~(n = 0) /\ (!y. P y ==> P(y MOD n))
    ==> ((?y. y < n /\ P y) <=> (?y. P y))`) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:num` THEN MATCH_MP_TAC(NUMBER_RULE
   `(x == y) (mod n) ==> (a * x == b) (mod n) ==> (a * y == b) (mod n)`) THEN
  ASM_SIMP_TAC[CONG_RMOD; CONG_REFL]);;

let CONG_SOLVE = prove
 (`!a b n. coprime(a,n) ==> ?x. (a * x == b) (mod n)`,
  REWRITE_TAC[CONG_SOLVE_EQ] THEN CONV_TAC NUMBER_RULE);;

let CONG_SOLVE_UNIQUE = prove
 (`!a b n. coprime(a,n) /\ ~(n = 0) ==> ?!x. x < n /\ (a * x == b) (mod n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXISTS_UNIQUE] THEN
  MP_TAC(SPECL [`a:num`; `b:num`; `n:num`] CONG_SOLVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `x:num`) THEN
  EXISTS_TAC `x MOD n` THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[DIVISION] THEN MATCH_MP_TAC CONG_TRANS THEN
    EXISTS_TAC `a * x:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC[CONG_REFL] THEN
    ASM_SIMP_TAC[CONG; MOD_MOD_REFL];
    ALL_TAC] THEN
  STRIP_TAC THEN X_GEN_TAC `y:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `y MOD n` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM CONG] THEN MATCH_MP_TAC CONG_MULT_LCANCEL THEN
  EXISTS_TAC `a:num` THEN ASM_MESON_TAC[CONG_TRANS; CONG_SYM]);;

let CONG_SOLVE_UNIQUE_NONTRIVIAL = prove
 (`!a p x. prime p /\ coprime(p,a) /\ 0 < x /\ x < p
           ==> ?!y. 0 < y /\ y < p /\ (x * y == a) (mod p)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[PRIME_0] THEN
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `1 < p` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 < p <=> ~(p = 0) /\ ~(p = 1)`] THEN
    ASM_MESON_TAC[PRIME_1];
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:num`; `a:num`; `p:num`] CONG_SOLVE_UNIQUE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[PRIME_0]] THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN
    MP_TAC(SPECL [`x:num`; `p:num`] PRIME_COPRIME) THEN
    ASM_CASES_TAC `x = 1` THEN ASM_REWRITE_TAC[COPRIME_1] THEN
    ASM_MESON_TAC[COPRIME_SYM; NOT_LT; DIVIDES_LE; LT_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `r:num` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `0 < r <=> ~(r = 0)`] THEN
  ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(p = 0) ==> 0 < p`] THEN
  ONCE_REWRITE_TAC[CONG_SYM] THEN REWRITE_TAC[CONG_0] THEN
  ASM_MESON_TAC[DIVIDES_REFL; PRIME_1; coprime]);;

let CONG_UNIQUE_INVERSE_PRIME = prove
 (`!p x. prime p /\ 0 < x /\ x < p
         ==> ?!y. 0 < y /\ y < p /\ (x * y == 1) (mod p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_SOLVE_UNIQUE_NONTRIVIAL THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[COPRIME_1; COPRIME_SYM]);;

let COUNT_CONG_SOLVE_SIMPLE = prove
 (`!m n b. {x | x < m * n /\ (x == b) (mod n)} HAS_SIZE
           (if n = 0 then 0 else m)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; LT; HAS_SIZE_0; EMPTY_GSPEC] THEN
  SUBGOAL_THEN
   `{x | x < m * n /\ (x == b) (mod n)} =
    IMAGE (\i. i * n + b MOD n) {i | i < m}`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:num` THEN REWRITE_TAC[CONG] THEN
      DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN EXISTS_TAC `x DIV n` THEN
      ASM_SIMP_TAC[RDIV_LT_EQ; DIVISION_SIMP] THEN ASM_MESON_TAC[MULT_SYM];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      REWRITE_TAC[CONG_LMOD; CONG_REFL; NUMBER_RULE
       `(x * n + c:num == b) (mod n) <=> (c == b) (mod n)`] THEN
      MATCH_MP_TAC(ARITH_RULE
       `b < n /\ (i + 1) * n <= m * n ==> i * n + b < m * n`) THEN
      ASM_REWRITE_TAC[MOD_LT_EQ; LE_MULT_RCANCEL] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    REWRITE_TAC[IN_ELIM_THM; HAS_SIZE_NUMSEG_LT] THEN
    ASM_SIMP_TAC[EQ_ADD_RCANCEL; EQ_MULT_RCANCEL]]);;

let COUNT_CONG_SOLVE_GEN = prove
 (`!m n a b.
        {x | x < m * n /\ (a * x == b) (mod n)} HAS_SIZE
        (if ~(n = 0) /\ gcd(n,a) divides b then m * gcd(n,a) else 0)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`m = 0`; `n = 0`] THEN
  ASM_REWRITE_TAC[LT; EMPTY_GSPEC; HAS_SIZE_0; MULT_CLAUSES; COND_ID] THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[HAS_SIZE_0; SET_RULE `{x | P x} = {} <=> ~(?x. P x)`] THEN
    ASM_MESON_TAC[CONG_SOLVE_EQ; GCD_SYM]] THEN
  MP_TAC(SPECL [`n:num`; `a:num`; `b:num`] CONG_SOLVE_EQ) THEN
  DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[GCD_SYM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:num` MP_TAC) THEN REWRITE_TAC[CONG] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) THEN REWRITE_TAC[GSYM CONG] THEN
  MP_TAC(NUMBER_RULE `gcd(n:num,a) divides n`) THEN
  REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:num` THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `!x:num. (a * x == a * z) (mod n) <=> (x == z) (mod d)`
   (fun th -> REWRITE_TAC[th])
  THENL [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC NUMBER_RULE; ALL_TAC] THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[MULT_ASSOC; HAS_SIZE] THEN
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] COUNT_CONG_SOLVE_SIMPLE] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MULT_CLAUSES]);;

let COUNT_CONG_SOLVE = prove
 (`!n a b. {x | x < n /\ (a * x == b) (mod n)} HAS_SIZE
           (if ~(n = 0) /\ gcd(n,a) divides b then gcd(n,a) else 0)`,
  MP_TAC(SPEC `1` COUNT_CONG_SOLVE_GEN) THEN
  REWRITE_TAC[MULT_CLAUSES; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Forms of the Chinese remainder theorem.                                   *)
(* ------------------------------------------------------------------------- *)

let CONG_CHINESE = prove
 (`coprime(a,b) /\ (x == y) (mod a) /\ (x == y) (mod b)
   ==> (x == y) (mod (a * b))`,
  ONCE_REWRITE_TAC[CONG_SUB_CASES] THEN MESON_TAC[CONG_0; DIVIDES_MUL]);;

let CHINESE_REMAINDER_UNIQUE = prove
 (`!a b m n.
        coprime(a,b) /\ ~(a = 0) /\ ~(b = 0)
        ==> ?!x. x < a * b /\ (x == m) (mod a) /\ (x == n) (mod b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`a:num`; `b:num`; `m:num`; `n:num`] CHINESE_REMAINDER) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `q1:num`; `q2:num`] THEN
    DISCH_TAC THEN EXISTS_TAC `x MOD (a * b)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[DIVISION; MULT_EQ_0]; ALL_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o CONJUNCT1);
      FIRST_X_ASSUM(SUBST1_TAC o CONJUNCT2)] THEN
    ASM_SIMP_TAC[MOD_MULT_CONG] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    REWRITE_TAC[cong; nat_mod; GSYM ADD_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
    MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN
    EXISTS_TAC `a * b` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONG_CHINESE; CONG_SYM; CONG_TRANS]]);;

let CHINESE_REMAINDER_COPRIME_UNIQUE = prove
 (`!a b m n.
        coprime(a,b) /\ ~(a = 0) /\ ~(b = 0) /\ coprime(m,a) /\ coprime(n,b)
        ==> ?!x. coprime(x,a * b) /\ x < a * b /\
                 (x == m) (mod a) /\ (x == n) (mod b)`,
  REPEAT STRIP_TAC THEN MP_TAC
   (SPECL [`a:num`; `b:num`; `m:num`; `n:num`] CHINESE_REMAINDER_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
   `(!x. P(x) ==> Q(x)) ==> (?!x. P x) ==> ?!x. Q(x) /\ P(x)`) THEN
  ASM_SIMP_TAC[CHINESE_REMAINDER_UNIQUE] THEN
  ASM_MESON_TAC[CONG_COPRIME; COPRIME_SYM; COPRIME_MUL]);;

let CHINESE_REMAINDER_USUAL = prove
 (`!a b u v:num. coprime(a,b) ==> ?x. (x == u) (mod a) /\ (x == v) (mod b)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = 0` THEN
  ASM_SIMP_TAC[CONG_MOD_1; COPRIME_0; CONG_MOD_0; EXISTS_REFL] THEN
  ASM_CASES_TAC `b = 0` THEN
  ASM_SIMP_TAC[CONG_MOD_1; COPRIME_0; CONG_MOD_0; EXISTS_REFL] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`a:num`; `b:num`; `u:num`; `v:num`] CHINESE_REMAINDER) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN SIMP_TAC[] THEN CONV_TAC NUMBER_RULE);;

let CONG_CHINESE_EQ = prove
 (`!a b x y.
     coprime(a,b)
     ==> ((x == y) (mod (a * b)) <=> (x == y) (mod a) /\ (x == y) (mod b))`,
  NUMBER_TAC);;

let CHINESE_REMAINDER_COUNT = prove
 (`!P Q R a b k m n.
        coprime(a,b) /\
        (!x. x < a * b ==> (R x <=> P (x MOD a) /\ Q (x MOD b))) /\
        {x | x < a /\ P x} HAS_SIZE m /\ {x | x < b /\ Q x} HAS_SIZE n
        ==> {x | x < a * b /\ R x} HAS_SIZE (m * n)`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_SIZE_CROSS) THEN
  ASM_CASES_TAC `a = 0` THENL
   [ASM_REWRITE_TAC[LT; EMPTY_GSPEC; CROSS_EMPTY; MULT_CLAUSES;
                    HAS_SIZE; CARD_CLAUSES; FINITE_EMPTY];
    ALL_TAC] THEN
  ASM_CASES_TAC `b = 0` THENL
   [ASM_REWRITE_TAC[LT; EMPTY_GSPEC; CROSS_EMPTY; MULT_CLAUSES;
                    HAS_SIZE; CARD_CLAUSES; FINITE_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:num`; `b:num`] CHINESE_REMAINDER_UNIQUE) THEN
  ASM_REWRITE_TAC[UNIQUE_SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `f:num->num->num` o EXISTENCE) THEN
  MATCH_MP_TAC(MESON[HAS_SIZE_IMAGE_INJ_EQ]
   `!f. (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        IMAGE f s = t
        ==> s HAS_SIZE p ==> t HAS_SIZE p`) THEN
  EXISTS_TAC `\(m,n). (f:num->num->num) m n` THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM] THEN
  REWRITE_TAC[EXISTS_PAIR_THM; IN_IMAGE; IN_CROSS] THEN
  REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[CONG_IMP_EQ; CONG_SYM; CONG_TRANS];
    RULE_ASSUM_TAC(REWRITE_RULE[CONG]) THEN ASM_SIMP_TAC[MOD_LT];
    X_GEN_TAC `x:num` THEN ASM_SIMP_TAC[IMP_CONJ] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`x MOD a`; `x MOD b`] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[MOD_LT; MOD_LT_EQ]] THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `a * b:num` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[NUMBER_RULE
     `coprime(a,b)
       ==> ((x == y) (mod (a * b)) <=>
            (x == y) (mod a) /\ (x == y) (mod b))`] THEN
     ASM_MESON_TAC[MOD_LT; MOD_LT_EQ; CONG]]);;

let CHINESE_REMAINDER_COPRIME_COUNT = prove
 (`!P Q R a b k m n.
        coprime(a,b) /\
        (!x. x < a * b ==> (R x <=> P (x MOD a) /\ Q (x MOD b))) /\
        {x | x < a /\ coprime(a,x) /\ P x} HAS_SIZE m /\
        {x | x < b /\ coprime(b,x) /\ Q x} HAS_SIZE n
        ==> {x | x < a * b /\ coprime(a * b,x) /\ R x} HAS_SIZE (m * n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CHINESE_REMAINDER_COUNT THEN
  EXISTS_TAC `\x:num. coprime(a,x) /\ P x` THEN
  EXISTS_TAC `\x:num. coprime(b,x) /\ Q x` THEN
  ASM_SIMP_TAC[COPRIME_RMOD; NUMBER_RULE
   `coprime(a:num,b)
    ==> (coprime(a * b,x) <=> coprime(a,x) /\ coprime(b,x))`] THEN
  MESON_TAC[]);;

let COUNT_ROOTS_MODULO_COPRIME = prove
 (`!a b k m n.
        coprime(a,b) /\
        {x | x < a /\ (x EXP k == 1) (mod a)} HAS_SIZE m /\
        {x | x < b /\ (x EXP k == 1) (mod b)} HAS_SIZE n
        ==> {x | x < a * b /\ (x EXP k == 1) (mod (a * b))} HAS_SIZE (m * n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CHINESE_REMAINDER_COUNT THEN
  EXISTS_TAC `\x. (x EXP k == 1) (mod a)` THEN
  EXISTS_TAC `\x. (x EXP k == 1) (mod b)` THEN
  ASM_SIMP_TAC[NUMBER_RULE
   `coprime(a,b)
       ==> ((x == y) (mod (a * b)) <=>
            (x == y) (mod a) /\ (x == y) (mod b))`] THEN
  REWRITE_TAC[CONG; MOD_EXP_MOD]);;

(* ------------------------------------------------------------------------- *)
(* A "multiplicative inverse (or nearest equivalent) modulo n" function.     *)
(* ------------------------------------------------------------------------- *)

let inverse_mod = new_definition
 `inverse_mod n x =
    if n <= 1 then 1
    else @y. y < n /\ (x * y == gcd(n,x)) (mod n)`;;

let INVERSE_MOD_BOUND,INVERSE_MOD_RMUL_GEN = (CONJ_PAIR o prove)
 (`(!n x. inverse_mod n x < n <=> 2 <= n) /\
   (!n x. (x * inverse_mod n x == gcd(n,x)) (mod n))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REWRITE_TAC[inverse_mod] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `x:num`] THEN ASM_CASES_TAC `n <= 1` THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
     `n <= 1 ==> n = 0 \/ n = 1`)) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[CONG_MOD_0; CONG_MOD_1; GCD_0; MULT_CLAUSES];
    ASM_REWRITE_TAC[ARITH_RULE `2 <= n <=> ~(n <= 1)`] THEN
    CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[CONG_SOLVE_LT_EQ] THEN
    REWRITE_TAC[GCD_SYM; DIVIDES_REFL] THEN ASM_ARITH_TAC]);;

let INVERSE_MOD_LMUL_GEN = prove
 (`!n x. (inverse_mod n x * x == gcd(n,x)) (mod n)`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[INVERSE_MOD_RMUL_GEN]);;

let INVERSE_MOD_RMUL_EQ = prove
 (`!n x. (x * inverse_mod n x == 1) (mod n) <=> coprime(n,x)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [NUMBER_TAC; ALL_TAC] THEN
  REWRITE_TAC[COPRIME_GCD] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_GEN]);;

let INVERSE_MOD_LMUL_EQ = prove
 (`!n x. (inverse_mod n x * x == 1) (mod n) <=> coprime(n,x)`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[INVERSE_MOD_RMUL_EQ]);;

let INVERSE_MOD_LMUL = prove
 (`!n x. coprime(n,x) ==> (inverse_mod n x * x == 1) (mod n)`,
  REWRITE_TAC[INVERSE_MOD_LMUL_EQ]);;

let INVERSE_MOD_RMUL = prove
 (`!n x. coprime(n,x) ==> (x * inverse_mod n x == 1) (mod n)`,
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ]);;

let INVERSE_MOD_UNIQUE = prove
 (`!n a x.
        (a * x == 1) (mod n) /\ x <= n /\ ~(n = 1 /\ x = 0)
        ==> inverse_mod n a = x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[CONG_MOD_0; MULT_EQ_1] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `x:num = n` THENL
   [ASM_REWRITE_TAC[NUMBER_RULE `(a * n == z) (mod n) <=> n divides z`] THEN
    REWRITE_TAC[DIVIDES_ONE] THEN SIMP_TAC[inverse_mod; LE_REFL];
    REPEAT STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `~(n = 1 /\ x = 0) ==> ~(x = n) /\ x <= n ==> ~(n = 1)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[INVERSE_MOD_BOUND] THEN
  REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC(NUMBER_RULE
   `(a * x == 1) (mod n) /\ (a * y == 1) (mod n) ==> (x == y) (mod n)`) THEN
  ASM_REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN
  UNDISCH_TAC `(a * x == 1) (mod n)` THEN CONV_TAC NUMBER_RULE);;

let INVERSE_MOD_CONG = prove
 (`!n x y. (x == y) (mod n) ==> inverse_mod n x = inverse_mod n y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inverse_mod] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP CONG_GCD_RIGHT) THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `(x:num == y) (mod n)` THEN CONV_TAC NUMBER_RULE);;

let INVERSE_MOD_INVERSE_MOD_CONG = prove
 (`!n x. coprime(n,x) ==> (inverse_mod n (inverse_mod n x) == x) (mod n)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(NUMBER_RULE
   `!x'. (x * x' == 1) (mod n) /\ (x' * x'' == 1) (mod n)
         ==> (x'' == x) (mod n)`) THEN
  EXISTS_TAC `inverse_mod n x` THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[INVERSE_MOD_RMUL_EQ];
    GEN_REWRITE_TAC RAND_CONV [INVERSE_MOD_RMUL_EQ] THEN
    CONV_TAC NUMBER_RULE]);;

let INVERSE_MOD_INVERSE_MOD = prove
 (`!n x. coprime(n,x) /\ 1 <= x /\ x <= n
         ==> inverse_mod n (inverse_mod n x) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INVERSE_MOD_UNIQUE THEN
  ASM_SIMP_TAC[INVERSE_MOD_LMUL_EQ; LE_1]);;

let INVERSE_MOD_NONZERO_ALT = prove
 (`!n a. ~(n divides a) ==> ~(inverse_mod n a = 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `a:num`] INVERSE_MOD_RMUL_GEN) THEN
  ASM_REWRITE_TAC[NUMBER_RULE `(a * 0 == b) (mod n) <=> n divides b`] THEN
  SIMP_TAC[DIVIDES_GCD]);;

let INVERSE_MOD_NONZERO = prove
 (`!n a. coprime(n,a) ==> ~(inverse_mod n a = 0)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[inverse_mod; ARITH];
    DISCH_TAC THEN MATCH_MP_TAC INVERSE_MOD_NONZERO_ALT THEN
    ASM_SIMP_TAC[DIVIDES_ONE; NUMBER_RULE
     `coprime(n,a) ==> (n divides a <=> n divides 1)`]]);;

let INVERSE_MOD_BOUND_LE = prove
 (`!n a. inverse_mod n a <= n <=> ~(n = 0)`,
  GEN_TAC THEN REWRITE_TAC[LE_LT; INVERSE_MOD_BOUND] THEN
  REWRITE_TAC[inverse_mod] THEN ARITH_TAC);;

let INVERSE_MOD_INVERSION = prove
 (`!m n. coprime(m,n)
         ==> m * inverse_mod n m + n * inverse_mod m n = m * n + 1`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [ASM_SIMP_TAC[COPRIME_0; inverse_mod; MULT_CLAUSES; ADD_CLAUSES; ARITH];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[COPRIME_0; inverse_mod; MULT_CLAUSES; ADD_CLAUSES; ARITH];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(m * inverse_mod n m + n * inverse_mod m n == 1) (mod (m * n))`
  MP_TAC THENL
   [MATCH_MP_TAC CONG_CHINESE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NUMBER_RULE `(m * x + a == 1) (mod m) <=> (a == 1) (mod m)`;
                NUMBER_RULE `(a + m * x == 1) (mod m) <=> (a == 1) (mod m)`;
                INVERSE_MOD_RMUL_EQ; INVERSE_MOD_LMUL_EQ] THEN
    ASM_MESON_TAC[COPRIME_SYM];
    REWRITE_TAC[CONG_TO_1; ADD_EQ_0; MULT_EQ_0; MULT_EQ_1]] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[inverse_mod; ARITH] THEN
    ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[inverse_mod; ARITH];
    DISCH_THEN(X_CHOOSE_THEN `q:num` MP_TAC)] THEN
  ASM_CASES_TAC `q = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; MULT_EQ_0; MULT_EQ_1;
      ARITH_RULE `a + b = 1 <=> a = 0 /\ b = 1 \/ a = 1 /\ b = 0`] THEN
    MAP_EVERY ASM_CASES_TAC [`m = 1`; `n = 1`] THEN
    ASM_REWRITE_TAC[COPRIME_0; inverse_mod; ARITH];
    ALL_TAC] THEN
  ASM_CASES_TAC `q = 1` THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE
   `m * x <= m * n /\ n * y <= n * m /\ 2 * m * n <= q * m * n
    ==> m * x + n * y = 1 + q * m * n ==> u:num = v`) THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL; INVERSE_MOD_BOUND_LE] THEN
  REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC);;

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

let PHI_FINITE_LEMMA = prove
 (`!P n. FINITE {m | coprime(m,n) /\ m < n}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..n` THEN
  REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC);;

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

let PHI_EQ_0 = prove
 (`!n. phi n = 0 <=> n = 0`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[PHI_0] THEN
  MP_TAC(SPEC `n:num` PHI_LOWERBOUND_1_STRONG) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Value on primes and prime powers.                                         *)
(* ------------------------------------------------------------------------- *)

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

let PHI_PRIMEPOW_SUC = prove
 (`!p k. prime(p) ==> phi(p EXP (k + 1)) = p EXP (k + 1) - p EXP k`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[PHI_ALT;  COPRIME_PRIMEPOW; ADD_EQ_0; ARITH] THEN
  REWRITE_TAC[SET_RULE
   `{n | ~(P n) /\ Q n} = {n | Q n} DIFF {n | P n /\ Q n}`] THEN
  SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM; CARD_DIFF] THEN
  REWRITE_TAC[CARD_NUMSEG_LT] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `{m | p divides m /\ m < p EXP (k + 1)} =
                IMAGE (\x. p * x) {m | m < p EXP k}`
   (fun th -> ASM_SIMP_TAC[th; CARD_IMAGE_INJ; EQ_MULT_LCANCEL; PRIME_IMP_NZ;
                           FINITE_NUMSEG_LT; CARD_NUMSEG_LT]) THEN
  REWRITE_TAC[EXTENSION; TAUT `(a <=> b) <=> (a ==> b) /\ (b ==> a)`;
              FORALL_AND_THM; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[IN_ELIM_THM; GSYM ADD1; EXP; LT_MULT_LCANCEL; PRIME_IMP_NZ] THEN
  CONJ_TAC THENL [ALL_TAC; NUMBER_TAC] THEN
  X_GEN_TAC `x:num` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `n:num` THEN
  UNDISCH_TAC `p * n < p * p EXP k` THEN
  ASM_SIMP_TAC[LT_MULT_LCANCEL; PRIME_IMP_NZ]);;

let PHI_PRIMEPOW = prove
 (`!p k. prime p
         ==> phi(p EXP k) = if k = 0 then 1 else p EXP k - p EXP (k - 1)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; CONJUNCT1 EXP; PHI_1] THEN
  ASM_SIMP_TAC[ADD1; PHI_PRIMEPOW_SUC; ADD_SUB]);;

let PHI_PRIMEPOW_ALT = prove
 (`!p k. prime p
         ==> phi(p EXP k) = if k = 0 then 1 else p EXP (k - 1) * (p - 1)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[PHI_PRIMEPOW] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[RIGHT_SUB_DISTRIB] THEN
  REWRITE_TAC[MULT_CLAUSES; GSYM(CONJUNCT2 EXP)] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> SUC(k - 1) = k`]);;

let PHI_2 = prove
 (`phi 2 = 1`,
  SIMP_TAC[PHI_PRIME; PRIME_2] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Multiplicativity property.                                                *)
(* ------------------------------------------------------------------------- *)

let PHI_MULTIPLICATIVE = prove
 (`!a b. coprime(a,b) ==> phi(a * b) = phi(a) * phi(b)`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`a = 0`; `b = 0`] THEN
  ASM_REWRITE_TAC[PHI_0; MULT_CLAUSES] THEN
  SIMP_TAC[PHI_ALT; GSYM CARD_PRODUCT; PHI_FINITE_LEMMA] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN
  EXISTS_TAC `\p. p MOD a,p MOD b` THEN
  REWRITE_TAC[PHI_FINITE_LEMMA; IN_ELIM_PAIR_THM] THEN
  ASM_SIMP_TAC[IN_ELIM_THM; COPRIME_LMOD; DIVISION] THEN CONJ_TAC THENL
   [MESON_TAC[COPRIME_LMUL2; COPRIME_RMUL2]; ALL_TAC] THEN
  X_GEN_TAC `pp:num#num` THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC] THEN MP_TAC(SPECL
   [`a:num`; `b:num`; `m:num`; `n:num`] CHINESE_REMAINDER_COPRIME_UNIQUE) THEN
  ASM_SIMP_TAC[CONG; MOD_LT]);;

(* ------------------------------------------------------------------------- *)
(* Even-ness of phi for most arguments.                                      *)
(* ------------------------------------------------------------------------- *)

let EVEN_PHI = prove
 (`!n. 3 <= n ==> EVEN(phi n)`,
  REWRITE_TAC[ARITH_RULE `3 <= n <=> 1 < n /\ ~(n = 2)`; IMP_CONJ] THEN
  MATCH_MP_TAC INDUCT_COPRIME_STRONG THEN
  SIMP_TAC[PHI_PRIMEPOW; PHI_MULTIPLICATIVE; EVEN_MULT; EVEN_SUB] THEN
  CONJ_TAC THENL [MESON_TAC[COPRIME_REFL; ARITH_RULE `~(2 = 1)`]; ALL_TAC] THEN
  REWRITE_TAC[EVEN_EXP] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP PRIME_ODD) THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[GSYM NOT_ODD]]);;

let EVEN_PHI_EQ = prove
 (`!n. EVEN(phi n) <=> n = 0 \/ 3 <= n`,
  GEN_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[ARITH_RULE `~(n = 0 \/ 3 <= n) <=> n = 1 \/ n = 2`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[PHI_1; PHI_2] THEN CONV_TAC NUM_REDUCE_CONV;
    STRIP_TAC THEN ASM_SIMP_TAC[PHI_0; EVEN_PHI; EVEN]]);;

let ODD_PHI_EQ = prove
 (`!n. ODD(phi n) <=> n = 1 \/ n = 2`,
  REWRITE_TAC[GSYM NOT_EVEN; EVEN_PHI_EQ] THEN ARITH_TAC);;

let PHI_EQ_PRIME = prove
 (`!p. phi p = p - 1 <=> p = 0 \/ prime p`,
  GEN_TAC THEN ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[PHI_0; ARITH] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[PHI_1; PRIME_1; ARITH] THEN
  EQ_TAC THEN REWRITE_TAC[PHI_PRIME] THEN
  SUBGOAL_THEN `1 < p` MP_TAC THENL
   [ASM_ARITH_TAC; POP_ASSUM_LIST(K ALL_TAC)] THEN
  SPEC_TAC(`p:num`,`n:num`) THEN
  MATCH_MP_TAC INDUCT_COPRIME_STRONG THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[PHI_MULTIPLICATIVE] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    MATCH_MP_TAC(ARITH_RULE
     `~(m = 0 /\ n = 0) /\ (m + 1) * (n + 1) <= k ==> ~(m * n = k - 1)`) THEN
    ASM_SIMP_TAC[PHI_EQ_0; ARITH_RULE `1 < n ==> ~(n = 0)`] THEN
    MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
     `~(n = 0) /\ m <= n - 1 ==> m + 1 <= n`) THEN
    (CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC PHI_LIMIT_STRONG]) THEN
    ASM_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`p:num`; `k:num`] THEN
    SIMP_TAC[PHI_PRIMEPOW; PRIME_EXP] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `p EXP k - p EXP k1 = p EXP k - 1
      ==> ~(p EXP k = 0) /\ p EXP k1 <= p EXP k ==> p EXP k1 = 1`)) THEN
    REWRITE_TAC[EXP_EQ_0; LE_EXP; EXP_EQ_1; ARITH_RULE `k - 1 <= k`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `k - 1 = 0 <=> k = 0 \/ k = 1`] THEN
    ASM_MESON_TAC[PRIME_0; PRIME_1]]);;

let PHI_LIMIT_COMPOSITE = prove
 (`!n. ~prime n /\ ~(n = 0) /\ ~(n = 1) ==> phi n < n - 1`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LT_LE; PHI_LIMIT_STRONG; PHI_EQ_PRIME]);;

(* ------------------------------------------------------------------------- *)
(* Some iteration theorems.                                                  *)
(* ------------------------------------------------------------------------- *)

let NPRODUCT_MOD = prove
 (`!s a:A->num n.
        FINITE s /\ ~(n = 0)
        ==> (iterate (*) s (\m. a(m) MOD n) == iterate (*) s a) (mod n)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `\x y. (x == y) (mod n)`
   (MATCH_MP ITERATE_RELATED MONOIDAL_MUL)) THEN
  SIMP_TAC[NEUTRAL_MUL; CONG_MULT; CONG_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[CONG_MOD]);;

let NPRODUCT_CMUL = prove
 (`!s a c n.
        FINITE s
        ==> iterate (*) s (\m. c * a(m)) = c EXP (CARD s) * iterate (*) s a`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[ITERATE_CLAUSES; MONOIDAL_MUL; NEUTRAL_MUL; CARD_CLAUSES;
               EXP; MULT_CLAUSES] THEN
  REWRITE_TAC[MULT_AC]);;

let COPRIME_NPRODUCT = prove
 (`!s n. FINITE s /\ (!x. x IN s ==> coprime(n,a(x)))
         ==> coprime(n,iterate (*) s a)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[ITERATE_CLAUSES; MONOIDAL_MUL; NEUTRAL_MUL;
           IN_INSERT; COPRIME_MUL; COPRIME_1]);;

let ITERATE_OVER_COPRIME = prove
 (`!op f n k.
        monoidal(op) /\ coprime(k,n) /\
        (!x y. (x == y) (mod n) ==> f x = f y)
        ==> iterate op {d | coprime(d,n) /\ d < n} (\m. f(k * m)) =
            iterate op {d | coprime(d,n) /\ d < n} f`,
  let lemma = prove
   (`~(n = 0) ==> ((a * x MOD n == b) (mod n) <=> (a * x == b) (mod n))`,
    MESON_TAC[CONG_REFL; CONG_SYM; CONG_TRANS; CONG_MULT; CONG_MOD]) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[LT; SET_RULE `{x | F} = {}`; ITERATE_CLAUSES]; ALL_TAC] THEN
  STRIP_TAC THEN SUBGOAL_THEN `?m. (k * m == 1) (mod n)` CHOOSE_TAC THENL
   [ASM_MESON_TAC[CONG_SOLVE; MULT_SYM; CONG_SYM]; ALL_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ_GENERAL_INVERSES) THEN
  MAP_EVERY EXISTS_TAC [`\x. (k * x) MOD n`; `\x. (m * x) MOD n`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_SIMP_TAC[COPRIME_LMOD; CONG_MOD_LT; CONG_LMOD; DIVISION; lemma;
               COPRIME_LMUL] THEN
  REPEAT STRIP_TAC THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[CONG_LMOD]) THEN
  UNDISCH_TAC `(k * m == 1) (mod n)` THEN CONV_TAC NUMBER_RULE);;

let ITERATE_ITERATE_DIVISORS = prove
 (`!op:A->A->A f x.
        monoidal op
        ==> iterate op (1..x) (\n. iterate op {d | d divides n} (f n)) =
            iterate op (1..x)
                       (\n. iterate op (1..(x DIV n)) (\k. f (k * n) n))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ITERATE_ITERATE_PRODUCT; FINITE_NUMSEG; FINITE_DIVISORS;
               IN_NUMSEG; LE_1] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
      ITERATE_EQ_GENERAL_INVERSES) THEN
  MAP_EVERY EXISTS_TAC [`\(n,d). d,n DIV d`; `\(n:num,k). n * k,n`] THEN
  ASM_SIMP_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; PAIR_EQ] THEN CONJ_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `n:num` THENL
   [X_GEN_TAC `k:num` THEN SIMP_TAC[DIV_MULT; LE_1; GSYM LE_RDIV_EQ] THEN
    SIMP_TAC[MULT_EQ_0; ARITH_RULE `1 <= x <=> ~(x = 0)`] THEN
    DISCH_THEN(K ALL_TAC) THEN NUMBER_TAC;
    X_GEN_TAC `d:num` THEN ASM_CASES_TAC `d = 0` THEN
    ASM_REWRITE_TAC[DIVIDES_ZERO] THENL [ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[DIV_MONO] THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[DIVIDES_DIV_MULT; MULT_SYM]] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `1 <= x <=> ~(x = 0)`] THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Fermat's Little theorem / Fermat-Euler theorem.                           *)
(* ------------------------------------------------------------------------- *)

let FERMAT_LITTLE = prove
 (`!a n. coprime(a,n) ==> (a EXP (phi n) == 1) (mod n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[COPRIME_0; PHI_0; CONG_MOD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN MATCH_MP_TAC CONG_MULT_LCANCEL THEN
  EXISTS_TAC `iterate (*) {m | coprime (m,n) /\ m < n} (\m. m)` THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[PHI_ALT; MULT_CLAUSES] THEN
  SIMP_TAC[IN_ELIM_THM; ONCE_REWRITE_RULE[COPRIME_SYM] COPRIME_NPRODUCT;
           PHI_FINITE_LEMMA; GSYM NPRODUCT_CMUL] THEN
  ONCE_REWRITE_TAC[CONG_SYM] THEN MATCH_MP_TAC CONG_TRANS THEN
  EXISTS_TAC `iterate (*) {m | coprime(m,n) /\ m < n} (\m. (a * m) MOD n)` THEN
  ASM_SIMP_TAC[NPRODUCT_MOD; PHI_FINITE_LEMMA] THEN
  MP_TAC(ISPECL [`( * ):num->num->num`; `\x. x MOD n`; `n:num`; `a:num`]
                ITERATE_OVER_COPRIME) THEN
  ASM_SIMP_TAC[MONOIDAL_MUL; GSYM CONG] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[CONG_SYM] THEN
  MATCH_MP_TAC NPRODUCT_MOD THEN ASM_SIMP_TAC[PHI_FINITE_LEMMA]);;

let FERMAT_LITTLE_PRIME = prove
 (`!a p. prime p /\ coprime(a,p) ==> (a EXP (p - 1) == 1) (mod p)`,
  MESON_TAC[FERMAT_LITTLE; PHI_PRIME_EQ]);;

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
(* Definition of the order of a number mod n (always 0 in non-coprime case). *)
(* ------------------------------------------------------------------------- *)

let order = new_definition
 `order n a = @d. !k. (a EXP k == 1) (mod n) <=> d divides k`;;

let EXP_ITER = prove
 (`!x n. x EXP n = ITER n (\y. x * y) (1)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; EXP]);;

let ORDER_DIVIDES = prove
 (`!n a d. (a EXP d == 1) (mod n) <=> order(n) a divides d`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[order] THEN CONV_TAC SELECT_CONV THEN
  MP_TAC(ISPECL [`\x y:num. (x == y) (mod n)`; `\x:num. a * x`; `1`]
        ORDER_EXISTENCE_ITER) THEN
  REWRITE_TAC[GSYM EXP_ITER] THEN DISCH_THEN MATCH_MP_TAC THEN
  NUMBER_TAC);;

let ORDER = prove
 (`!n a. (a EXP (order(n) a) == 1) (mod n)`,
  REWRITE_TAC[ORDER_DIVIDES; DIVIDES_REFL]);;

let ORDER_UNIQUE_ALT = prove
 (`!n a d. order n a = d <=> !k. (a EXP k == 1) (mod n) <=> d divides k`,
  REWRITE_TAC[ORDER_DIVIDES; GSYM DIVIDES_ANTISYM] THEN
  MESON_TAC[DIVIDES_REFL; DIVIDES_TRANS]);;

let ORDER_MINIMAL = prove
 (`!n a m. 0 < m /\ m < order(n) a ==> ~((a EXP m == 1) (mod n))`,
  REWRITE_TAC[ORDER_DIVIDES] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC);;

let ORDER_WORKS = prove
 (`!n a. (a EXP (order(n) a) == 1) (mod n) /\
         !m. 0 < m /\ m < order(n) a ==> ~((a EXP m == 1) (mod n))`,
  MESON_TAC[ORDER; ORDER_MINIMAL]);;

let ORDER_1 = prove
 (`!n. order n 1 = 1`,
  REWRITE_TAC[GSYM DIVIDES_ONE; GSYM ORDER_DIVIDES; EXP_1; CONG_REFL]);;

let ORDER_EQ_0 = prove
 (`!n a. order(n) a = 0 <=> ~coprime(n,a)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [ONCE_REWRITE_TAC[COPRIME_SYM] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FERMAT_LITTLE) THEN
    ASM_REWRITE_TAC[ORDER_DIVIDES; DIVIDES_ZERO; PHI_EQ_0] THEN
    ASM_MESON_TAC[COPRIME_0; ORDER_1; ARITH_RULE `~(1 = 0)`];
    MP_TAC(SPECL [`n:num`; `a:num`] ORDER) THEN
    SPEC_TAC(`order n a`,`m:num`) THEN INDUCT_TAC THEN REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (TAUT
     `~p ==> (q ==> p) ==> q ==> r`)) THEN
    REWRITE_TAC[EXP] THEN CONV_TAC NUMBER_RULE]);;

let ORDER_CONG = prove
 (`!n a b. (a == b) (mod n) ==> order n a = order n b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[order] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_MESON_TAC[CONG_EXP; CONG_REFL; CONG_SYM; CONG_TRANS]);;

let ORDER_MOD = prove
 (`!p n. order p (n MOD p) = order p n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC ORDER_CONG THEN
  REWRITE_TAC[CONG_LMOD; CONG_REFL]);;

let COPRIME_ORDER = prove
 (`!n a. coprime(n,a)
         ==> order(n) a > 0 /\
            (a EXP (order(n) a) == 1) (mod n) /\
            !m. 0 < m /\ m < order(n) a ==> ~((a EXP m == 1) (mod n))`,
  SIMP_TAC[ARITH_RULE `n > 0 <=> ~(n = 0)`; ORDER_EQ_0] THEN
  MESON_TAC[ORDER; ORDER_MINIMAL]);;

let ORDER_DIVIDES_PHI = prove
 (`!a n. coprime(n,a) ==> (order n a) divides (phi n)`,
  MESON_TAC[ORDER_DIVIDES; FERMAT_LITTLE; COPRIME_SYM]);;

let ORDER_LE_PHI = prove
 (`!n. ~(n = 0) ==> order n a <= phi n`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `order n a = 0` THEN ASM_REWRITE_TAC[LE_0] THEN
  MATCH_MP_TAC DIVIDES_LE_IMP THEN ASM_REWRITE_TAC[PHI_EQ_0] THEN
  MATCH_MP_TAC ORDER_DIVIDES_PHI THEN
  ASM_MESON_TAC[ORDER_EQ_0]);;

let ORDER_DIVIDES_EXPDIFF = prove
 (`!a n d e. coprime(n,a)
             ==> ((a EXP d == a EXP e) (mod n) <=> (d == e) (mod (order n a)))`,
  SUBGOAL_THEN
   `!a n d e. coprime(n,a) /\ e <= d
              ==> ((a EXP d == a EXP e) (mod n) <=> (d == e) (mod (order n a)))`
   (fun th -> MESON_TAC[th; LE_CASES; CONG_SYM]) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` SUBST1_TAC) THEN
  SUBST1_TAC(ARITH_RULE `e = e + 0`) THEN
  REWRITE_TAC[ARITH_RULE `(e + 0) + c = e + c`] THEN
  REWRITE_TAC[EXP_ADD] THEN
  ASM_SIMP_TAC[CONG_ADD_LCANCEL_EQ; COPRIME_EXP;
    ONCE_REWRITE_RULE[COPRIME_SYM] CONG_MULT_LCANCEL_EQ] THEN
  REWRITE_TAC[EXP; CONG_0_DIVIDES; ORDER_DIVIDES]);;

let ORDER_UNIQUE = prove
 (`!n a k. 0 < k /\
           (a EXP k == 1) (mod n) /\
           (!m. 0 < m /\ m < k ==> ~(a EXP m == 1) (mod n))
           ==> order n a = k`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `order n a`) THEN
  MP_TAC(ISPECL [`n:num`; `a:num`] ORDER_WORKS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `k:num`)) THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `order n a = 0` THEN
  ASM_REWRITE_TAC[] THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [ORDER_EQ_0]) THEN
  MP_TAC(ISPECL [`n:num`; `a:num`; `k:num`] COPRIME_REXP) THEN
  ASM_SIMP_TAC[LE_1; LT] THEN
  UNDISCH_TAC `(a EXP k == 1) (mod n)` THEN CONV_TAC NUMBER_RULE);;

let ORDER_MUL_LCM = prove
 (`!m n a. coprime(m,n) ==> order (m * n) a = lcm(order m a,order n a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ORDER_UNIQUE_ALT] THEN
  ASM_SIMP_TAC[NUMBER_RULE
   `coprime(m,n)
    ==> ((x == y) (mod (m * n)) <=>
         (x == y) (mod m) /\ (x == y) (mod n))`] THEN
  REWRITE_TAC[ORDER_DIVIDES; LCM_DIVIDES]);;

let ORDER_EXP_GEN = prove
 (`!p a k. order p (a EXP k) =
           if k = 0 then 1 else order p a DIV gcd(order p a,k)`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ORDER_1; EXP] THEN
  ASM_CASES_TAC `order p a = 0` THENL
   [ASM_REWRITE_TAC[DIV_0; ORDER_EQ_0; COPRIME_REXP] THEN
    ASM_REWRITE_TAC[GSYM ORDER_EQ_0];
    ALL_TAC] THEN
  REWRITE_TAC[ORDER_UNIQUE_ALT; EXP_EXP] THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[ORDER_DIVIDES] THEN
  MP_TAC(NUMBER_RULE `gcd(order p a,k) divides order p a`) THEN
  GEN_REWRITE_TAC LAND_CONV [divides] THEN
  ABBREV_TAC `d = gcd(order p a,k)` THEN
  ASM_CASES_TAC `d = 0` THENL [ASM_MESON_TAC[GCD_ZERO]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `e:num`) THEN ASM_SIMP_TAC[DIV_MULT] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC NUMBER_RULE);;

let ORDER_EXP = prove
 (`!p a k. ~(k = 0) /\ k divides order p a
           ==> order p (a EXP k) = order p a DIV k`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ORDER_EXP_GEN] THEN
  AP_TERM_TAC THEN ASM_REWRITE_TAC[GSYM DIVIDES_GCD_RIGHT]);;

let ORDER_INVERSE_MOD = prove
 (`!n a. coprime(n,a) ==> order n (inverse_mod n a) = order n a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[order] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `d:num` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod n) ==> ((a == 1) (mod n) <=> (b == 1) (mod n))`) THEN
  REWRITE_TAC[GSYM MULT_EXP] THEN MATCH_MP_TAC CONG_EXP_1 THEN
  ASM_REWRITE_TAC[INVERSE_MOD_LMUL_EQ]);;

let ORDER_MUL_DIVIDES = prove
 (`!p a b. order p (a * b) divides order p a * order p b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ORDER_DIVIDES] THEN
  REWRITE_TAC[MULT_EXP] THEN MATCH_MP_TAC CONG_MULT_1 THEN
  REWRITE_TAC[ORDER_DIVIDES] THEN NUMBER_TAC);;

let ORDER_MUL_EQ = prove
 (`!p a b. coprime(order p a,order p b)
           ==> order p (a * b) = order p a * order p b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN
  ASM_SIMP_TAC[ORDER_MUL_DIVIDES] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `(a:num) divides (b * c) /\ b divides (a * c) /\ coprime(a,b)
    ==> (a * b) divides c`) THEN
  ASM_REWRITE_TAC[GSYM ORDER_DIVIDES] THEN CONJ_TAC THEN
  MATCH_MP_TAC CONG_TRANS THENL
   [EXISTS_TAC `(a * b) EXP (order p b * order p (a * b))`;
    EXISTS_TAC `(a * b) EXP (order p a * order p (a * b))`] THEN
  (CONJ_TAC THENL
    [ALL_TAC;
     GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o RAND_CONV) [MULT_SYM] THEN
     REWRITE_TAC[GSYM EXP_EXP] THEN MATCH_MP_TAC CONG_EXP_1 THEN
     REWRITE_TAC[ORDER_WORKS]]) THEN
  REWRITE_TAC[GSYM EXP_EXP] THEN MATCH_MP_TAC CONG_EXP THEN
  REWRITE_TAC[MULT_EXP] THENL
   [MATCH_MP_TAC(NUMBER_RULE `(b == 1) (mod n) ==> (a == a * b) (mod n)`);
    MATCH_MP_TAC(NUMBER_RULE `(a == 1) (mod n) ==> (b == a * b) (mod n)`)] THEN
  REWRITE_TAC[ORDER_WORKS]);;

let ORDER_LCM_EXISTS = prove
 (`!p a b. ?c. order p c = lcm(order p a,order p b)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `order p a = 0` THENL
   [ASM_MESON_TAC[LCM_0]; ALL_TAC] THEN
  ASM_CASES_TAC `order p b = 0` THENL
   [ASM_MESON_TAC[LCM_0]; ALL_TAC] THEN
  MP_TAC(SPECL [`order p a`; `order p b`]
        LCM_COPRIME_DECOMP) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
  REWRITE_TAC[divides; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m':num` THEN DISCH_TAC THEN
  X_GEN_TAC `n':num` THEN DISCH_TAC THEN DISCH_TAC THEN
  DISCH_THEN(fun th -> SUBST1_TAC(SYM th) THEN ASSUME_TAC(SYM th)) THEN
  EXISTS_TAC `a EXP m' * b EXP n'` THEN
  SUBGOAL_THEN
   `order p (a EXP m') = m /\ order p (b EXP n') = n`
   (fun th -> ASM_SIMP_TAC[th; ORDER_MUL_EQ]) THEN
  ASM_SIMP_TAC[ORDER_EXP_GEN] THEN CONJ_TAC THEN
  (COND_CASES_TAC THENL [ASM_MESON_TAC[MULT_CLAUSES]; ALL_TAC]) THEN
  REWRITE_TAC[NUMBER_RULE `gcd(a * b:num,a) = a /\ gcd(a * b,b) = b`] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT]);;

let ORDER_DIVIDES_MAXIMAL = prove
 (`!p. ~(p = 1)
       ==> ?n. coprime(p,n) /\
               !m. coprime(p,m) ==> order p m divides order p n`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p = 0` THEN
  ASM_SIMP_TAC[COPRIME_0; DIVIDES_REFL; UNWIND_THM2] THEN
  MP_TAC(fst(EQ_IMP_RULE(ISPEC `IMAGE (order p) {k | k < p}` num_MAX))) THEN
  REWRITE_TAC[MESON[IN] `IMAGE f s x <=> x IN IMAGE f s`] THEN
  SIMP_TAC[GSYM num_FINITE; FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[MEMBER_NOT_EMPTY; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LE_1]; ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
   `a <= b ==> ~(a = 0) ==> ~(b = 0)`)) THEN
  REWRITE_TAC[ORDER_EQ_0; COPRIME_1] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`p:num`; `m:num`; `n:num`] ORDER_LCM_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q MOD p`) THEN
  ASM_REWRITE_TAC[ORDER_MOD; MOD_LT_EQ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
   `a:num <= b ==> b <= a ==> a = b`)) THEN
  ASM_REWRITE_TAC[LE_LCM; GSYM DIVIDES_LCM_RIGHT; ORDER_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Properties of primitive roots (when they exist).                          *)
(* ------------------------------------------------------------------------- *)

let PRIMITIVE_ROOT_IMP_COPRIME = prove
 (`!n g. order n g = phi n ==> n = 0 \/ coprime(n,g)`,
  MESON_TAC[ORDER_EQ_0; PHI_EQ_0]);;

let PRIMITIVE_ROOT_IMP_PRIME = prove
 (`!p g. order p g = p - 1 ==> p = 0 \/ prime p`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p = 0` THENL
   [ASM_REWRITE_TAC[]; REWRITE_TAC[GSYM PHI_EQ_PRIME]] THEN
  ASM_CASES_TAC `p = 1` THEN
  ASM_REWRITE_TAC[SUB_REFL; ORDER_EQ_0; COPRIME_1] THEN
  MATCH_MP_TAC(ARITH_RULE
   `h <= p - 1 /\ g <= h ==> g = p - 1 ==> h = p - 1`) THEN
  ASM_SIMP_TAC[PHI_LIMIT_STRONG; ORDER_LE_PHI]);;

let PRIMITIVE_ROOT_IMAGE = prove
 (`!n g. order n g = phi n
         ==> IMAGE (\i. (g EXP i) MOD n) {i | i < phi n} =
             {a | coprime(a,n) /\ a < n}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[PHI_0; CONJUNCT1 LT; EMPTY_GSPEC; IMAGE_CLAUSES] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `coprime(n:num,g)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORDER_EQ_0; PHI_EQ_0];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[COPRIME_LMOD; COPRIME_LEXP; MOD_LT_EQ] THEN
    ASM_MESON_TAC[COPRIME_SYM];
    DISCH_TAC] THEN
  REWRITE_TAC[SET_RULE
   `t SUBSET IMAGE f s <=> !y. y IN t ==> ?x. x IN s /\ f x = y`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SURJECTIVE_IFF_INJECTIVE_GEN o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; GSYM PHI_ALT; CARD_NUMSEG_LT] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i < n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[IN_ELIM_THM; GSYM CONG; ORDER_DIVIDES_EXPDIFF] THEN
  MESON_TAC[CONG_IMP_EQ]);;

let PRIMITIVE_ROOT_IMAGE_PRIME = prove
 (`!p g. order p g = p - 1
         ==> IMAGE (\i. (g EXP i) MOD p) {i | i < p - 1} =
             {a | 0 < a /\ a < p}`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p = 0` THEN
  ASM_REWRITE_TAC[ARITH; CONJUNCT1 LT; EMPTY_GSPEC; IMAGE_CLAUSES] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIMITIVE_ROOT_IMP_PRIME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`p:num`; `g:num`] PRIMITIVE_ROOT_IMAGE) THEN
  ASM_SIMP_TAC[PHI_PRIME] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `a:num` THEN
  ASM_CASES_TAC `a:num < p` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ] THEN
  ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[LT_REFL; DIVIDES_0] THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < a <=> ~(a = 0)`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE_STRONG) THEN
  ASM_ARITH_TAC);;

let PRIMITIVE_ROOT_SURJECTIVE = prove
 (`!n g a. ~(n = 0) /\ order n g = phi n /\ coprime(a,n)
           ==> ?m. m < phi n /\ (a == g EXP m) (mod n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIMITIVE_ROOT_IMAGE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `IMAGE f s = t ==> !y. y IN t ==> ?x. x IN s /\ f x = y`)) THEN
  DISCH_THEN(MP_TAC o SPEC `a MOD n`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; COPRIME_LMOD; MOD_LT_EQ] THEN
  MESON_TAC[CONG]);;

let PRIMITIVE_ROOT_SURJECTIVE_ALT = prove
 (`!n g a. order n g = phi n /\ coprime(a,n)
           ==> ?m. (a == g EXP m) (mod n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ALL_TAC; ASM_MESON_TAC[PRIMITIVE_ROOT_SURJECTIVE]] THEN
  ASM_SIMP_TAC[COPRIME_0; CONG_MOD_0] THEN MESON_TAC[EXP]);;

let PRIMITIVE_ROOT_SURJECTIVE_PRIME = prove
 (`!p g a. ~(p = 0) /\ order p g = p - 1 /\ coprime(a,p)
           ==> ?m. m < p - 1 /\ (a == g EXP m) (mod p)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIMITIVE_ROOT_IMAGE_PRIME) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `IMAGE f s = t ==> !y. y IN t ==> ?x. x IN s /\ f x = y`)) THEN
  DISCH_THEN(MP_TAC o SPEC `a MOD p`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; COPRIME_LMOD; MOD_LT_EQ] THEN
  REWRITE_TAC[CONG; ARITH_RULE `0 < n <=> ~(n = 0)`; GSYM DIVIDES_MOD] THEN
  ASM_MESON_TAC[PRIME_COPRIME_EQ; COPRIME_SYM; PRIMITIVE_ROOT_IMP_PRIME]);;

let PRIMITIVE_ROOT_SURJECTIVE_PRIME_ALT = prove
 (`!p g a. order p g = p - 1 /\ coprime(a,p)
           ==> ?m. (a == g EXP m) (mod p)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p = 0` THENL
   [ALL_TAC; ASM_MESON_TAC[PRIMITIVE_ROOT_SURJECTIVE_PRIME]] THEN
  ASM_SIMP_TAC[COPRIME_0; CONG_MOD_0] THEN MESON_TAC[EXP]);;

(* ------------------------------------------------------------------------- *)
(* Another trivial primality characterization.                               *)
(* ------------------------------------------------------------------------- *)

let PRIME_PRIME_FACTOR = prove
 (`!n. prime n <=> ~(n = 1) /\ !p. prime p /\ p divides n ==> (p = n)`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [prime] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [MESON_TAC[PRIME_1]; ALL_TAC] THEN
  STRIP_TAC THEN X_GEN_TAC `d:num` THEN
  ASM_CASES_TAC `d = 1` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC o
    MATCH_MP PRIME_FACTOR) THEN
  ASM_MESON_TAC[DIVIDES_TRANS; DIVIDES_ANTISYM]);;

let PRIME_DIVISOR_SQRT = prove
 (`!n. prime(n) <=> ~(n = 1) /\ !d. d divides n /\ d EXP 2 <= n ==> (d = 1)`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [prime] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_SIMP_TAC[DIVIDES_ONE] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[DIVIDES_0; LE; EXP_EQ_0; ARITH_EQ] THEN
    MATCH_MP_TAC(TAUT `~a /\ ~b ==> (a <=> b)`) THEN CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o SPEC `2`) THEN REWRITE_TAC[ARITH];
      DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[ARITH]];
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `d:num` THEN STRIP_TAC THENL
   [ASM_CASES_TAC `d = n:num` THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    UNDISCH_TAC `d EXP 2 <= n` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXP_2; ARITH_RULE `~(n * n <= n) <=> n * 1 < n * n`] THEN
    ASM_REWRITE_TAC[LT_MULT_LCANCEL] THEN
    MAP_EVERY UNDISCH_TAC [`~(n = 0)`; `~(n = 1)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `d divides n` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `d EXP 2 <= d * e \/ e EXP 2 <= d * e` MP_TAC THENL
   [REWRITE_TAC[EXP_2; LE_MULT_LCANCEL; LE_MULT_RCANCEL] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `d:num`);
    FIRST_X_ASSUM(MP_TAC o SPEC `e:num`)] THEN
  ASM_SIMP_TAC[DIVIDES_RMUL; DIVIDES_LMUL; DIVIDES_REFL; MULT_CLAUSES]);;

let PRIME_PRIME_FACTOR_SQRT = prove
 (`!n. prime n <=>
       ~(n = 0) /\ ~(n = 1) /\ ~(?p. prime p /\ p divides n /\ p EXP 2 <= n)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[PRIME_1] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[PRIME_0] THEN
  GEN_REWRITE_TAC LAND_CONV [PRIME_DIVISOR_SQRT] THEN
  EQ_TAC THENL [MESON_TAC[PRIME_1]; ALL_TAC] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `d = 1` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[DIVIDES_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `d EXP 2` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[num_CONV `2`; EXP_MONO_LE_SUC] THEN
  ASM_MESON_TAC[DIVIDES_LE; DIVIDES_ZERO]);;

(* ------------------------------------------------------------------------- *)
(* Pocklington theorem.                                                      *)
(* ------------------------------------------------------------------------- *)

let POCKLINGTON_LEMMA = prove
 (`!a n q r.
        2 <= n /\ (n - 1 = q * r) /\
        (a EXP (n - 1) == 1) (mod n) /\
        (!p. prime(p) /\ p divides q
             ==> coprime(a EXP ((n - 1) DIV p) - 1,n))
        ==> !p. prime p /\ p divides n ==> (p == 1) (mod q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `order p (a EXP r) = q` ASSUME_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `coprime(a EXP r,p)` (MP_TAC o MATCH_MP FERMAT_LITTLE) THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[ORDER_DIVIDES] THEN
      SUBGOAL_THEN `phi p = p - 1` SUBST1_TAC THENL
       [ASM_MESON_TAC[PHI_PRIME_EQ]; ALL_TAC] THEN
      REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `d:num` THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `(p - 1 = q * d) ==> ~(p = 0) ==> (p + q * 0 = 1 + q * d)`)) THEN
      REWRITE_TAC[nat_mod; cong] THEN ASM_MESON_TAC[PRIME_0]] THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_EXP THEN
    UNDISCH_TAC `(a EXP (n - 1) == 1) (mod n)` THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[coprime; NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `d = p:num` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[prime]; ALL_TAC] THEN
    SUBGOAL_THEN `p divides (a EXP (n - 1))` ASSUME_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
       `2 <= n ==> (n - 1 = SUC(n - 2))`)) THEN
      REWRITE_TAC[EXP] THEN ASM_SIMP_TAC[DIVIDES_RMUL];
      ALL_TAC] THEN
    REWRITE_TAC[cong; nat_mod] THEN
    SUBGOAL_THEN `~(p divides 1)` MP_TAC THENL
     [ASM_MESON_TAC[DIVIDES_ONE; PRIME_1]; ALL_TAC] THEN
    ASM_MESON_TAC[DIVIDES_RMUL; DIVIDES_ADD; DIVIDES_ADD_REVL]] THEN
  SUBGOAL_THEN `(order p (a EXP r)) divides q` MP_TAC THENL
   [REWRITE_TAC[GSYM ORDER_DIVIDES; EXP_EXP] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN
    UNDISCH_TAC `(a EXP (n - 1) == 1) (mod n)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p divides n` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:num` SUBST_ALL_TAC) THEN
    REWRITE_TAC[cong; nat_mod] THEN MESON_TAC[MULT_AC];
    ALL_TAC] THEN
  REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `d:num` THEN
  ASM_CASES_TAC `d = 1` THEN ASM_SIMP_TAC[MULT_CLAUSES] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  DISCH_THEN(X_CHOOSE_THEN `P:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `P divides q` ASSUME_TAC THENL
   [ASM_MESON_TAC[DIVIDES_LMUL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `P:num`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN
  UNDISCH_TAC `P divides q` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN
  SUBGOAL_THEN `~(P = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT] THEN
  UNDISCH_TAC `P divides d` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num` SUBST_ALL_TAC) THEN
  UNDISCH_TAC `order p (a EXP r) * P * t = P * s` THEN
  ONCE_REWRITE_TAC[ARITH_RULE
   `(a * p * b = p * c) <=> (p * a * b = p * c)`] THEN
  REWRITE_TAC[EQ_MULT_LCANCEL] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[coprime] THEN
  DISCH_THEN(MP_TAC o SPEC `p:num`) THEN REWRITE_TAC[NOT_IMP] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[PRIME_1]] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[AC MULT_AC `(d * t) * r = r * d * t`] THEN
  REWRITE_TAC[EXP_MULT] THEN
  MATCH_MP_TAC CONG_1_DIVIDES THEN
  MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `1 EXP t` THEN
  SIMP_TAC[CONG_EXP; ORDER] THEN REWRITE_TAC[EXP_ONE; CONG_REFL]);;

let POCKLINGTON = prove
 (`!a n q r.
        2 <= n /\ (n - 1 = q * r) /\ n <= q EXP 2 /\
        (a EXP (n - 1) == 1) (mod n) /\
        (!p. prime(p) /\ p divides q
             ==> coprime(a EXP ((n - 1) DIV p) - 1,n))
        ==> prime(n)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[PRIME_PRIME_FACTOR_SQRT] THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> ~(n = 0) /\ ~(n = 1)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`a:num`; `n:num`; `q:num`; `r:num`] POCKLINGTON_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `p:num`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p EXP 2 <= q EXP 2` MP_TAC THENL
   [ASM_MESON_TAC[LE_TRANS]; ALL_TAC] THEN
  REWRITE_TAC[num_CONV `2`; EXP_MONO_LE_SUC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONG_1_DIVIDES) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Variant for application, to separate the exponentiation.                  *)
(* ------------------------------------------------------------------------- *)

let POCKLINGTON_ALT = prove
 (`!a n q r.
        2 <= n /\ (n - 1 = q * r) /\ n <= q EXP 2 /\
        (a EXP (n - 1) == 1) (mod n) /\
        (!p. prime(p) /\ p divides q
             ==> ?b. (a EXP ((n - 1) DIV p) == b) (mod n) /\
                     coprime(b - 1,n))
        ==> prime(n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POCKLINGTON THEN
  MAP_EVERY EXISTS_TAC [`a:num`; `q:num`; `r:num`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(a EXP ((q * r) DIV p) - 1 == b - 1) (mod n)`
   (fun th -> ASM_MESON_TAC[CONG_COPRIME; COPRIME_SYM; th]) THEN
  MATCH_MP_TAC CONG_SUB THEN ASM_REWRITE_TAC[CONG_REFL] THEN
  REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
  SUBGOAL_THEN `~(a = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(a EXP (n - 1) == 1) (mod n)` THEN
    SIMP_TAC[ARITH_RULE `2 <= n ==> (n - 1 = SUC(n - 2))`;
             ASSUME `a = 0`; ASSUME `2 <= n`] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP] THEN
    ONCE_REWRITE_TAC[CONG_SYM] THEN
    REWRITE_TAC[CONG_0_DIVIDES; DIVIDES_ONE] THEN
    UNDISCH_TAC `2 <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(a EXP ((q * r) DIV p) == b) (mod n)` THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONG_0_DIVIDES] THEN
  SUBGOAL_THEN `~(n divides (a EXP (n - 1)))` MP_TAC THENL
   [ASM_MESON_TAC[CONG_DIVIDES; DIVIDES_ONE; ARITH_RULE `~(2 <= 1)`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[CONTRAPOS_THM] THEN UNDISCH_TAC `p divides q` THEN
  GEN_REWRITE_TAC LAND_CONV [divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EXP_MULT] THEN
  SUBGOAL_THEN `p = SUC(p - 1)` SUBST1_TAC THENL
   [UNDISCH_TAC `~(p = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXP; DIVIDES_RMUL]);;

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
(* Variant of Pocklington theorem.                                           *)
(* ------------------------------------------------------------------------- *)

let POCKLINGTON_PRIMEFACT = prove
 (`2 <= n /\ (q * r = n - 1) /\ n <= q * q
   ==> ((a EXP r) MOD n = b)
       ==> (ITLIST (*) ps 1 = q)
           ==> ((b EXP q) MOD n = 1)
               ==> ALL (\p. prime p /\
                            coprime((b EXP (q DIV p)) MOD n - 1,n)) ps
                   ==> prime n`,
  DISCH_THEN(fun th -> DISCH_THEN(SUBST1_TAC o SYM) THEN MP_TAC th) THEN
  SIMP_TAC[MOD_EXP_MOD; ARITH_RULE `2 <= n ==> ~(n = 0)`] THEN
  SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] EXP_EXP] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POCKLINGTON THEN
  MAP_EVERY EXISTS_TAC [`a:num`; `q:num`; `r:num`] THEN
  ASM_REWRITE_TAC[EXP_2] THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`a EXP (n - 1)`; `n:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> ~(n = 0)`] THEN
    STRIP_TAC THEN ABBREV_TAC `Q = a EXP (n - 1) DIV n` THEN
    ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[cong; nat_mod] THEN
    MAP_EVERY EXISTS_TAC [`0`; `Q:num`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `primefact ps q` MP_TAC THENL
   [ASM_REWRITE_TAC[PRIMEFACT_VARIANT] THEN MATCH_MP_TAC ALL_IMP THEN
    EXISTS_TAC `\p. prime p /\ coprime(a EXP (q DIV p * r) MOD n - 1,n)` THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP PRIMAFACT_CONTAINS) THEN
  X_GEN_TAC `p:num` THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> a /\ b ==> c`) THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  SUBGOAL_THEN `q DIV p * r = (n - 1) DIV p` SUBST1_TAC THENL
   [UNDISCH_TAC `p divides q` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THEN
    UNDISCH_THEN `(p * d) * r = n - 1` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[DIV_MULT; GSYM MULT_ASSOC];
    ALL_TAC] THEN
  MATCH_MP_TAC CONG_COPRIME THEN MATCH_MP_TAC CONG_SUB THEN
  ASM_SIMP_TAC[CONG_MOD; ARITH_RULE `2 <= n ==> ~(n = 0)`; CONG_REFL] THEN
  MATCH_MP_TAC(ARITH_RULE `a <= b /\ ~(a = 0) ==> 1 <= a /\ 1 <= b`) THEN
  ASM_SIMP_TAC[MOD_LE; ARITH_RULE `2 <= n ==> ~(n = 0)`] THEN
  ASM_SIMP_TAC[MOD_EQ_0; ARITH_RULE `2 <= n ==> ~(n = 0)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` MP_TAC) THEN
  DISCH_THEN(MP_TAC o C AP_THM `p:num` o AP_TERM `(EXP)`) THEN
  REWRITE_TAC[EXP_EXP] THEN
  SUBGOAL_THEN `(n - 1) DIV p * p = n - 1` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `q * r = n - 1`)) THEN
    UNDISCH_TAC `p divides q` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
    REWRITE_TAC[GSYM MULT_ASSOC] THEN
    ASM_MESON_TAC[DIV_MULT; MULT_AC; PRIME_0];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `n:num` o AP_TERM `(MOD)`) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `~(p = 0) ==> (p = SUC(p - 1))`)) THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[EXP; GSYM MULT_ASSOC] THEN
  ASM_SIMP_TAC[MOD_MULT; ARITH_RULE `2 <= n ==> ~(n = 0)`] THEN
  REWRITE_TAC[ARITH_EQ]);;

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
(* Also just use a stupid algorithm for small enough numbers or if PARI/GP   *)
(* is not installed. I should really write a better factoring algorithm.     *)
(* ------------------------------------------------------------------------- *)

let PARI_THRESHOLD = pow2 25;;

let multifactor =
  let rec findfactor m n =
    if mod_num n m =/ num_0 then m
    else if m */ m >/ n then n
    else findfactor (m +/ num_1) n in
  let rec stupidfactor n =
    let p = findfactor num_2 n in
    if p =/ n then [n] else p::(stupidfactor(quo_num n p)) in
  let rec multilist l =
    if l = [] then [] else
    let (x,n) = hd l in
    replicate x (Num.int_of_num n) @ multilist (tl l) in
  fun n -> try if n </ PARI_THRESHOLD then failwith ""
               else multilist (factor n)
           with Failure _ -> sort (</) (stupidfactor n);;

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
(* Relatively efficient evaluation of "(a EXP k) MOD n".                     *)
(* ------------------------------------------------------------------------- *)

let EXP_MOD_CONV =
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
  fun tm ->
    let ntm = rand tm in
    let th1 = INST [ntm,n_tm] pth in
    let th2 = EQF_ELIM(NUM_EQ_CONV(rand(lhand(concl th1)))) in
    let th_base,th_steps = CONJ_PAIR(MP th1 th2) in
    let conv_base = GEN_REWRITE_CONV I [th_base]
    and conv_step = GEN_REWRITE_CONV I [th_steps] in
    let rec conv tm =
      try conv_base tm with Failure _ ->
      (conv_step THENC
       RAND_CONV conv THENC
       let_CONV THENC
       NUM_REDUCE_CONV) tm in
    conv tm;;

(* ------------------------------------------------------------------------- *)
(* HOL checking of primality certificate, using Pocklington shortcut.        *)
(* ------------------------------------------------------------------------- *)

let prime_theorem_cache = ref [];;

let rec lookup_under_num n l =
  if l = [] then failwith "lookup_under_num" else
  let h = hd l in
  if fst h =/ n then snd h
  else lookup_under_num n (tl l);;

let rec split_factors q qs ps n =
  if q */ q >=/ n then rev qs,ps
  else split_factors (q */ hd ps) (hd ps :: qs) (tl ps) n;;

let check_certificate =
  let n_tm = `n:num`
  and a_tm = `a:num`
  and q_tm = `q:num`
  and r_tm = `r:num`
  and b_tm = `b:num`
  and ps_tm = `ps:num list`
  and conv_itlist =
   GEN_REWRITE_CONV TOP_DEPTH_CONV [ITLIST] THENC NUM_REDUCE_CONV
  and conv_all =
   GEN_REWRITE_CONV TOP_DEPTH_CONV
    [ALL; BETA_THM; TAUT `a /\ T <=> a`] THENC
   GEN_REWRITE_CONV DEPTH_CONV
    [TAUT `(a /\ a /\ b <=> a /\ b) /\ (a /\ a <=> a)`]
  and subarith_conv =
    let gconv_net = itlist (uncurry net_of_conv)
      [`a - b`,NUM_SUB_CONV;
       `a DIV b`,NUM_DIV_CONV;
       `(a EXP b) MOD c`,EXP_MOD_CONV;
       `coprime(a,b)`,COPRIME_CONV;
       `p /\ T`,REWR_CONV(TAUT `p /\ T <=> p`);
       `T /\ p`,REWR_CONV(TAUT `T /\ p <=> p`)]
      empty_net  in
    DEPTH_CONV(REWRITES_CONV gconv_net) in
  let rec check_certificate cert =
    match cert with
      Prime_2 ->
          PRIME_2
    | Primroot_and_factors((n,ps),a,ncerts) ->
          try lookup_under_num n (!prime_theorem_cache) with Failure _ ->
          let qs,rs = split_factors num_1 [] (rev ps) n in
          let q = itlist ( */ ) qs num_1
          and r = itlist ( */ ) rs num_1 in
          let th1 = INST [mk_numeral n,n_tm;
                          mk_flist (map mk_numeral qs),ps_tm;
                          mk_numeral q,q_tm;
                          mk_numeral r,r_tm;
                          mk_numeral a,a_tm]
                         POCKLINGTON_PRIMEFACT in
          let th2 = MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1)))) in
          let tha = EXP_MOD_CONV(lhand(lhand(concl th2))) in
          let thb = MP (INST [rand(concl tha),b_tm] th2) tha in
          let th3 = MP thb (EQT_ELIM(conv_itlist (lhand(concl thb)))) in
          let th4 = MP th3 (EXP_MOD_CONV (lhand(lhand(concl th3)))) in
          let th5 = conv_all(lhand(concl th4)) in
          let th6 = TRANS th5 (subarith_conv(rand(concl th5))) in
          let th7 = IMP_TRANS (snd(EQ_IMP_RULE th6)) th4 in
          let ants = conjuncts(lhand(concl th7)) in
          let certs =
            map (fun t -> lookup_under_num (dest_numeral(rand t)) ncerts)
                ants in
          let ths = map check_certificate certs in
          let fth = MP th7 (end_itlist CONJ ths) in
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
    if p =/ num_0 then EQF_INTRO PRIME_0
    else if p =/ num_1 then EQF_INTRO PRIME_1 else
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
(* Another lemma.                                                            *)
(* ------------------------------------------------------------------------- *)

let PRIME_POWER_EXISTS = prove
 (`!q. prime q
       ==> ((?i. n = q EXP i) <=>
            (!p. prime p /\ p divides n ==> p = q))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[IMP_CONJ; PRIME_DIVEXP_EQ; DIVIDES_PRIME_PRIME] THEN
  ASM_CASES_TAC `n = 0` THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th)) THEN
    ASM_REWRITE_TAC[PRIME_2; PRIME_CONV `prime 3`; DIVIDES_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[EXP]; ALL_TAC] THEN
  MP_TAC(ISPEC `n:num` PRIMEPOW_FACTOR) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` MP_TAC) THEN
  ASM_CASES_TAC `p:num = q` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM);
    ASM_MESON_TAC[DIVIDES_REXP; LE_1; DIVIDES_RMUL; DIVIDES_REFL]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC(NUM_RING `m = 1 ==> x * m = x`) THEN
  MATCH_MP_TAC(ARITH_RULE `~(m = 0) /\ ~(2 <= m) ==> m = 1`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[COPRIME_0; PRIME_1]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP PRIMEPOW_FACTOR) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[DIVIDES_LMUL; DIVIDES_RMUL; DIVIDES_REXP; LE_1; DIVIDES_REFL];
    DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COPRIME_RMUL]) THEN
    ASM_SIMP_TAC[COPRIME_REXP; LE_1; COPRIME_REFL] THEN
    ASM_MESON_TAC[PRIME_1]]);;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

map (time PRIME_TEST o mk_small_numeral) (0--50);;

time PRIME_TEST `65535`;;

time PRIME_TEST `65536`;;

time PRIME_TEST `65537`;;

time PROVE_PRIMEFACT (Int 222);;

time PROVE_PRIMEFACT (Int 151);;

(* ------------------------------------------------------------------------- *)
(* The "Landau trick" in Erdos's proof of Chebyshev-Bertrand theorem.        *)
(* ------------------------------------------------------------------------- *)

map (time PRIME_TEST o mk_small_numeral)
  [3; 5; 7; 13; 23; 43; 83; 163; 317; 631; 1259; 2503; 4001];;
