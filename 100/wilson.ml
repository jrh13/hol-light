(* ========================================================================= *)
(* Wilson's theorem.                                                         *)
(* ========================================================================= *)

needs "Library/prime.ml";;
needs "Library/pocklington.ml";;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Factorial in terms of products.                                           *)
(* ------------------------------------------------------------------------- *)

let FACT_NPRODUCT = prove
 (`!n. FACT(n) = nproduct(1..n) (\i. i)`,
  INDUCT_TAC THEN
  REWRITE_TAC[FACT; NUMSEG_CLAUSES; ARITH; NPRODUCT_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= SUC n`; NPRODUCT_CLAUSES; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

let FACT_NPRODUCT_ALT = prove
 (`!n. FACT(n) = nproduct(2..n) (\i. i)`,
  GEN_TAC THEN REWRITE_TAC[FACT_NPRODUCT] THEN
  DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 1 <= n`) THEN
  ASM_REWRITE_TAC[num_CONV `1`; NUMSEG_CLAUSES] THEN
  REWRITE_TAC[ARITH; NPRODUCT_CLAUSES; FACT] THEN
  ASM_SIMP_TAC[GSYM NUMSEG_LREC] THEN
  SIMP_TAC[NPRODUCT_CLAUSES; FINITE_NUMSEG; IN_NUMSEG; MULT_CLAUSES] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* General "pairing up" theorem for products.                                *)
(* ------------------------------------------------------------------------- *)

let NPRODUCT_PAIRUP_INDUCT = prove
 (`!f r n s. FINITE s /\ CARD s = n /\
             (!x:A. x IN s ==> ?!y. y IN s /\ ~(y = x) /\
                                    (f(x) * f(y) == 1) (mod r))
             ==> (nproduct s f == 1) (mod r)`,
  GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:A->bool` THEN ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_REWRITE_TAC[NPRODUCT_CLAUSES; CONG_REFL] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL [ASM_MESON_TAC[CARD_EQ_0]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:A` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `n - 2`) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - 2 < n`] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[ASSUME `(a:A) IN s`] THEN
  REWRITE_TAC[EXISTS_UNIQUE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `(s DELETE a) DELETE (b:A)`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_DELETE] THEN
    SIMP_TAC[FINITE_DELETE; ASSUME `FINITE(s:A->bool)`; CARD_DELETE] THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:A) IN s`)) THEN
    REWRITE_TAC[EXISTS_UNIQUE] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[MULT_SYM]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(b:A) IN s`)) THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`a:A`; `x:A`] o CONJUNCT2) THEN
    ASM_MESON_TAC[MULT_SYM];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `s = (a:A) INSERT (b INSERT (s DELETE a DELETE b))`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[NPRODUCT_CLAUSES; FINITE_INSERT; FINITE_DELETE;
           ASSUME `FINITE(s:A->bool)`] THEN
  ASM_REWRITE_TAC[IN_INSERT; IN_DELETE; MULT_CLAUSES] THEN
  REWRITE_TAC[MULT_ASSOC] THEN
  ONCE_REWRITE_TAC[SYM(NUM_REDUCE_CONV `1 * 1`)] THEN
  MATCH_MP_TAC CONG_MULT THEN ASM_REWRITE_TAC[]);;

let NPRODUCT_PAIRUP = prove
 (`!f r s. FINITE s /\
           (!x:A. x IN s ==> ?!y. y IN s /\ ~(y = x) /\
                                  (f(x) * f(y) == 1) (mod r))
           ==> (nproduct s f == 1) (mod r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NPRODUCT_PAIRUP_INDUCT THEN
  EXISTS_TAC `CARD(s:A->bool)` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence Wilson's theorem.                                                   *)
(* ------------------------------------------------------------------------- *)

let WILSON = prove
 (`!p. prime(p) ==> (FACT(p - 1) == p - 1) (mod p)`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `p = 0` THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  ASM_CASES_TAC `p = 1` THENL [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  ASM_CASES_TAC `p = 2` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[CONG_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `FACT(p - 1) = FACT(p - 2) * (p - 1)` SUBST1_TAC THENL
   [SUBGOAL_THEN `p - 1 = SUC(p - 2)`
     (fun th -> REWRITE_TAC[th; FACT; MULT_AC]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = 1 * x`] THEN
  MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC[CONG_REFL] THEN
  REWRITE_TAC[FACT_NPRODUCT_ALT] THEN MATCH_MP_TAC NPRODUCT_PAIRUP THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `x:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `x:num`] CONG_UNIQUE_INVERSE_PRIME) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [MATCH_MP_TAC MONO_EXISTS;
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC] THEN
  X_GEN_TAC `y:num` THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `y = 1` THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 <= y <=> 0 < y /\ ~(y = 1)`] THEN
    UNDISCH_TAC `(x * y == 1) (mod p)` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_SIMP_TAC[CONG; MOD_LT; ARITH_RULE `x <= p - 2 /\ ~(p = 0) ==> x < p`;
                 ARITH_RULE `~(p = 0) /\ ~(p = 1) ==> 1 < p`] THEN
    UNDISCH_TAC `2 <= x` THEN ARITH_TAC;
    MATCH_MP_TAC(ARITH_RULE `y < p /\ ~(y = p - 1) ==> y <= p - 2`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `(x * y == 1) (mod p)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN SUBGOAL_THEN `(x + 1 == 0) (mod p)` MP_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[CONG_0] THEN DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
      MAP_EVERY UNDISCH_TAC [`2 <= x`; `x <= p - 2`] THEN ARITH_TAC] THEN
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `x * p:num` THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[CONG_0] THEN MESON_TAC[divides; MULT_SYM]] THEN
    SUBGOAL_THEN `x * p = x + x * (p - 1)` SUBST1_TAC THENL
     [REWRITE_TAC[LEFT_SUB_DISTRIB; MULT_CLAUSES] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC(GSYM SUB_ADD) THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = x * 1`] THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
      UNDISCH_TAC `~(p = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONG_SYM] THEN MATCH_MP_TAC CONG_ADD THEN
    ASM_REWRITE_TAC[CONG_REFL];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `((x + 1) * (x - 1) == 0) (mod p)` MP_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[CONG_0] THEN
      DISCH_THEN(MP_TAC o CONJ (ASSUME `prime p`)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP PRIME_DIVPROD) THEN
      DISCH_THEN(DISJ_CASES_THEN (MP_TAC o MATCH_MP DIVIDES_LE)) THEN
      MAP_EVERY UNDISCH_TAC
        [`2 <= x`; `x <= p - 2`; `~(p = 1)`; `~(p = 0)`] THEN
      ARITH_TAC] THEN
    ONCE_REWRITE_TAC[GSYM(SPEC `1` CONG_ADD_LCANCEL_EQ)] THEN
    SUBGOAL_THEN `1 + (x + 1) * (x - 1) = x * x`
     (fun th -> ASM_REWRITE_TAC[th; ARITH]) THEN
    REWRITE_TAC[LEFT_SUB_DISTRIB] THEN
    MATCH_MP_TAC(ARITH_RULE
     `(x + 1) * 1 <= (x + 1) * x
      ==> 1 + (x + 1) * x - (x + 1) * 1 = x * x`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `2 <= x` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* And in fact we have a converse.                                           *)
(* ------------------------------------------------------------------------- *)

let WILSON_EQ = prove
 (`!p. ~(p = 1) ==> (prime p <=> (FACT(p - 1) == p - 1) (mod p))`,
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN EQ_TAC THEN SIMP_TAC[WILSON] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[CONG_MOD_0] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[LE_LT] THEN ASM_CASES_TAC `n:num = p` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE `x < y ==> x <= y - 1`)) THEN
  ASM_SIMP_TAC[GSYM DIVIDES_FACT_PRIME] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  SUBGOAL_THEN `p divides FACT(n - 1) <=> p divides (n - 1)` SUBST1_TAC THENL
   [MATCH_MP_TAC CONG_DIVIDES THEN
    MATCH_MP_TAC CONG_DIVIDES_MODULUS THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN SUBGOAL_THEN `p divides 1` MP_TAC THENL
   [MATCH_MP_TAC DIVIDES_ADD_REVR THEN EXISTS_TAC `n - 1` THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - 1 + 1 = n`];
    REWRITE_TAC[DIVIDES_ONE] THEN ASM_MESON_TAC[PRIME_1]]);;
