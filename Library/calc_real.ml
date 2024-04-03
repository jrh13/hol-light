(* ========================================================================= *)
(* Calculation with real numbers (Boehm-style but by inference).             *)
(* ========================================================================= *)

needs "Library/transc.ml";;

let REAL_SUB_SUM0 = prove
 (`!x y m. sum(0,m) x - sum(0,m) y = sum(0,m) (\i. x i - y i)`,
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sum] THEN
  REAL_ARITH_TAC);;

let REAL_MUL_RSUM0 = prove
 (`!m c x. c * sum(0,m) x = sum(0,m) (\i. c * x(i))`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[sum; REAL_MUL_RZERO; REAL_ADD_LDISTRIB]);;

let REAL_ABS_LEMMA = prove
 (`!a b n. (&a pow n) * abs b = abs((&a pow n) * b)`,
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM]);;

let REAL_ABS_LEMMA1 = prove
 (`!a b. &a * abs b = abs(&a * b)`,
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM]);;

let REAL_ABS_TRIANGLE_LEMMA = prove
 (`!u x y z. abs(x - y) + abs(z - x) < u ==> abs(z - y) < u`,
  REAL_ARITH_TAC);;
let REAL_MONO_POW2 = prove
 (`!m n. m <= n ==> &2 pow m <= &2 pow n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; real_pow; REAL_LE_REFL] THEN
  POP_ASSUM MP_TAC THEN MP_TAC(SPEC `m:num` REAL_LT_POW2) THEN
  REAL_ARITH_TAC);;

let REAL_LE_SUC_POW2 = prove
 (`!m. &2 pow m + &1 <= &2 pow (SUC m)`,
  GEN_TAC THEN REWRITE_TAC[real_pow; REAL_MUL_2; REAL_LE_LADD; REAL_LE_POW2]);;

let REAL_OPPSIGN_LEMMA = prove
 (`!x y. (x * y < &0) <=> (x < &0 /\ &0 < y) \/ (&0 < x /\ y < &0)`,
  REPEAT GEN_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPEC `x:real` REAL_LT_NEGTOTAL) THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPEC `y:real` REAL_LT_NEGTOTAL) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LT_REFL] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP REAL_LT_MUL th) THEN MP_TAC th) THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  REAL_ARITH_TAC);;

let REAL_OPPSIGN = prove
 (`(&0 < x ==> &0 <= y) /\ (x < &0 ==> y <= &0) <=> &0 <= x * y`,
  REWRITE_TAC[GSYM REAL_NOT_LT; REAL_OPPSIGN_LEMMA] THEN
  REAL_ARITH_TAC);;

let REAL_NDIV_LEMMA1a = prove
 (`!a m n. &2 * abs(&2 pow m * &a - &2 pow (m + n)) <= &2 pow m
           ==> (&a = &2 pow n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_ADD; GSYM REAL_SUB_LDISTRIB] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM] THEN
  REWRITE_TAC[REAL_OF_NUM_POW] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
    (SPECL [`a:num`; `2 EXP n`] LT_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
  POP_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o REWRITE_RULE[LT_EXISTS]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ARITH `((a + b) - a = b) /\ (a - (a + b) = --b)`] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_NOT_LE; REAL_ABS_NUM] THEN
  REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_MUL_2; REAL_ADD_LDISTRIB; REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_ADD_ASSOC; REAL_LT_ADDL] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&(2 EXP m)` THEN
  REWRITE_TAC[REAL_LT_POW2; GSYM REAL_OF_NUM_POW] THEN
  ONCE_REWRITE_TAC[AC REAL_ADD_AC `(a + b) + c = b + (a + c)`] THEN
  REWRITE_TAC[GSYM REAL_MUL_2; REAL_LE_ADDR] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_LT_POW2]);;

let REAL_NDIV_LEMMA1b = prove
 (`!a m n. ~(&2 * abs(-- (&2 pow m * &a) - &2 pow (m + n)) <= &2 pow m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sub; GSYM REAL_NEG_ADD] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_POW_ADD] THEN
  REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_ADD_LDISTRIB] THEN
  SUBGOAL_THEN `&0 <= &a + &2 pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS];
    REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NUM] THEN
    ASM_REWRITE_TAC[real_abs; REAL_NOT_LE] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `(&2 * &2 pow m) * &1` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_RID; REAL_MUL_2] THEN
      REWRITE_TAC[REAL_LT_ADDR; REAL_LT_POW2];
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow n` THEN
        REWRITE_TAC[REAL_LE_POW2; REAL_LE_ADDL; REAL_POS]]]]);;

let REAL_NDIV_LEMMA2 = prove
 (`!a b m n. (?k. (b = &k) \/ (b = --(&k))) /\
             (abs(a) = &2 pow m) /\
             &2 * abs(a * b - &2 pow (m + n)) <= abs(a)
             ==> (a * b = &2 pow (m + n))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISJ_CASES_THEN SUBST1_TAC (REAL_ARITH `(a = abs a) \/ (a = --(abs a))`) THEN
  ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_POW; REAL_ABS_NUM; REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_NDIV_LEMMA1b] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_NDIV_LEMMA1a) THEN
  REWRITE_TAC[REAL_POW_ADD]);;

let REAL_NDIV_LEMMA3 = prove
 (`!a b m n. m <= n /\
             (?k. (b = &k) \/ (b = --(&k))) /\
             (abs(a) = &2 pow m) /\
             &2 * abs(a * b - &2 pow n) <= abs(a)
             ==> (a * b = &2 pow n)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  POP_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[REAL_NDIV_LEMMA2]);;

(* ------------------------------------------------------------------------- *)
(* Surely there is already an efficient way to do this...                    *)
(* ------------------------------------------------------------------------- *)

let log2 =                              (*** least p >= 0 with x <= 2^p ***)
  let rec log2 x y =
    if x </ Num.num_of_int 1 then y
    else log2 (quo_num x (Num.num_of_int 2)) (y +/ Num.num_of_int 1) in
  fun x -> log2 (x -/ Num.num_of_int 1) (Num.num_of_int 0);;

(* ------------------------------------------------------------------------- *)
(* Theorems justifying the steps.                                            *)
(* ------------------------------------------------------------------------- *)

let REALCALC_DOWNGRADE = prove
 (`(SUC d0 = d) ==>
   (n + d = n0) ==>
   abs(a - &2 pow n0 * x) < &1 ==>
   abs((&2 pow d) * b - a) <= &2 pow d0 ==>
   abs(b - &2 pow n * x) < &1`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&2 pow (SUC d0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ABS_LEMMA; REAL_MUL_RID; REAL_SUB_LDISTRIB] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&2 pow d0 + &2 pow d0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_ABS_TRIANGLE_LEMMA THEN EXISTS_TAC `a:real` THEN
      MATCH_MP_TAC REAL_LTE_ADD2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
      SPEC_TAC(`d0:num`,`d0:num`) THEN INDUCT_TAC THEN
      REWRITE_TAC[real_pow; REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + &1` THEN
      REWRITE_TAC[REAL_MUL_2] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[real_pow; GSYM REAL_MUL_2; REAL_LE_REFL]]]);;

let REALCALC_INT = prove
 (`abs((&2 pow n) * a - (&2 pow n) * a) < &1`,
  REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_LT_01]);;

let REALCALC_NEG = prove
 (`abs(a - (&2 pow n) * x) < &1
   ==> abs(--a - (&2 pow n) * --x) < &1`,
  REWRITE_TAC[real_sub; GSYM REAL_NEG_ADD] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_MUL_RNEG]);;

let REALCALC_ABS = prove
 (`abs(a - &2 pow n * x) < &1
   ==> abs(abs(a) - &2 pow n * abs(x)) < &1`,
  DISCH_TAC THEN REWRITE_TAC[REAL_ABS_LEMMA] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs(a - (&2 pow n) * x)` THEN
  ASM_REWRITE_TAC[REAL_ABS_SUB_ABS]);;

let REALCALC_INV_LEMMA = prove
 (`(?m. (b = &m) \/ (b = --(&m))) /\
   (?m. (a = &m) \/ (a = --(&m))) /\
   SUC(n + k) <= (2 * e) /\
   &2 pow e <= abs(a) /\
   abs(a - &2 pow k * x) < &1 /\
   &2 * abs(a * b - &2 pow (n + k)) <= abs(a)
   ==> abs(b - &2 pow n * inv(x)) < &1`,
  let lemma1 = REAL_ARITH
   `!x y z b. &2 * abs(x - y) <= b /\ &2 * abs(y - z) < b
              ==> &2 * abs(x - z) < &2 * b` in
  let lemma2 = REAL_ARITH
   `!x y z. x + &1 <= abs(z) /\ abs(z - y) < &1 ==> x <= abs(y)` in
  let lemma3 = REAL_ARITH
    `(abs(x) <= &1 /\ &0 < abs(y) /\ abs(y) < &1) /\
     (&0 < x ==> &0 <= y) /\ (x < &0 ==> y <= &0)
      ==> abs(x - y) < &1` in
  let lemma4 = REAL_ARITH
    `!a b c. c <= abs(a) + abs(b) /\ abs(a - b) < c ==>
             (&0 < a ==> &0 <= b) /\ (a < &0 ==> b <= &0)` in
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(a = &0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&2 pow e <= abs(&0)` THEN
    REWRITE_TAC[REAL_ABS_0; GSYM REAL_NOT_LT; REAL_LT_POW2]; ALL_TAC] THEN
  SUBGOAL_THEN `~(x = &0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `abs(a - &2 pow k * &0) < &1` THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_NOT_LT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow e` THEN
    ASM_REWRITE_TAC[REAL_LE_POW2]; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 pow e + &1 <= abs(a)) \/ (&2 pow e = abs(a))` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW] THEN
    FIRST_ASSUM(CHOOSE_THEN(DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_NEG; REAL_ABS_NUM]) THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_EQ] THEN
    REWRITE_TAC[GSYM ADD1; LE_SUC_LT; GSYM LE_LT] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW];
    UNDISCH_TAC `&2 pow e <= abs(a)` THEN DISCH_THEN(K ALL_TAC)] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_TAC THEN MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
    EXISTS_TAC `&2 * abs(a)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[GSYM REAL_ABS_NZ] THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_ABS_MUL] THEN
      REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_MUL_RID] THEN
      MATCH_MP_TAC lemma1 THEN EXISTS_TAC `&2 pow (n + k)` THEN
      ASM_REWRITE_TAC[]] THEN
    GEN_REWRITE_TAC (LAND_CONV o funpow 3 RAND_CONV) [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_POW_ADD; GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN
    EXISTS_TAC `abs(x)` THEN ASM_REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&2 * abs(&2 pow n) * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_POW_EQ_0] THEN
        CONV_TAC(RAND_CONV(LAND_CONV REAL_INT_EQ_CONV)) THEN REWRITE_TAC[];
        REWRITE_TAC[REAL_SUB_RDISTRIB] THEN
        ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
        REWRITE_TAC[REAL_MUL_ASSOC] THEN
        FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_MUL_RINV th]) THEN
        ASM_REWRITE_TAC[REAL_MUL_LID]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&2 pow k` THEN
    REWRITE_TAC[REAL_LT_POW2; REAL_MUL_RID; REAL_ABS_LEMMA] THEN
    ONCE_REWRITE_TAC
     [AC REAL_MUL_AC `a * b * c = (a * c) * b`] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 pow e * &2 pow e` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC
       [AC REAL_MUL_AC `(a * b) * c = c * b * a`] THEN
      REWRITE_TAC[GSYM REAL_POW_ADD; GSYM(CONJUNCT2 real_pow)] THEN
      MATCH_MP_TAC REAL_MONO_POW2 THEN ASM_REWRITE_TAC[GSYM MULT_2];
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_LT_POW2];
        REWRITE_TAC[REAL_ABS_LEMMA] THEN MATCH_MP_TAC lemma2 THEN
        EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_LT_POW2];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow e + &1` THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];

    DISCH_TAC THEN
    DISJ_CASES_TAC (SPECL [`e:num`; `n + k:num`] LET_CASES) THENL
     [SUBGOAL_THEN `a * b = &2 pow (n + k)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_NDIV_LEMMA3 THEN
        EXISTS_TAC `e:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `abs(a)` THEN
      ASM_REWRITE_TAC[GSYM REAL_ABS_NZ; GSYM REAL_ABS_MUL] THEN
      ASM_REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
      ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c = b * a * c`] THEN
      REWRITE_TAC[REAL_POW_ADD; GSYM REAL_SUB_LDISTRIB] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC `abs(x)` THEN
      ASM_REWRITE_TAC[GSYM REAL_ABS_NZ; GSYM REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_ABS_MUL] THEN
      REWRITE_TAC[REAL_SUB_RDISTRIB; GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC[MATCH_MP REAL_MUL_LINV (ASSUME `~(x = &0)`)] THEN
      ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&2 pow n * &1` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NUM] THEN
        MATCH_MP_TAC REAL_LT_LMUL THEN
        ASM_REWRITE_TAC[REAL_LT_POW2; REAL_MUL_RID];
        MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `&2 pow (SUC k)` THEN
        REWRITE_TAC[REAL_MUL_RID; REAL_LT_POW2]] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 pow (2 * e)` THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_POW_ADD; ADD_CLAUSES] THEN
        MATCH_MP_TAC REAL_MONO_POW2 THEN ASM_REWRITE_TAC[];
        SUBST1_TAC(SYM(ASSUME `&2 pow e = abs(a)`)) THEN
        REWRITE_TAC[MULT_2; REAL_POW_ADD; GSYM REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[MATCH_MP REAL_LT_IMP_LE (SPEC_ALL REAL_LT_POW2)]] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[real_pow] THEN
      SUBGOAL_THEN `?d. e = SUC d` (CHOOSE_THEN SUBST_ALL_TAC) THENL
       [UNDISCH_TAC `SUC (n + k) <= (2 * e)` THEN
        SPEC_TAC(`e:num`,`e:num`) THEN INDUCT_TAC THEN
        REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE; NOT_SUC] THEN
        REWRITE_TAC[SUC_INJ; GSYM EXISTS_REFL];
        REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&2 pow (SUC d) - &1` THEN
        REWRITE_TAC[REAL_LE_SUB_RADD; REAL_LE_SUB_LADD] THEN
        REWRITE_TAC[REAL_LE_SUC_POW2] THEN
        SUBGOAL_THEN `abs(abs a - &2 pow k * abs(x)) < &1` MP_TAC THENL
         [REWRITE_TAC[REAL_ABS_LEMMA] THEN
          MATCH_MP_TAC(REAL_LET_IMP REAL_ABS_SUB_ABS) THEN
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];

      SUBGOAL_THEN `abs(b) <= &1 /\ &0 <= a * b` STRIP_ASSUME_TAC THENL
       [ASM_CASES_TAC `b = &0` THEN
        ASM_REWRITE_TAC[REAL_ABS_0; REAL_MUL_RZERO; REAL_POS] THEN
        SUBGOAL_THEN `abs(a) <= abs(a * b)` ASSUME_TAC THENL
         [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
          REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          REWRITE_TAC[REAL_ABS_POS] THEN
          SUBGOAL_THEN `?q. abs(b) = &q` CHOOSE_TAC THENL
           [UNDISCH_TAC `?m. (b = &m) \/ (b = --(&m))` THEN
            DISCH_THEN(X_CHOOSE_THEN `p:num` DISJ_CASES_TAC) THEN
            EXISTS_TAC `p:num` THEN
            ASM_REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM];
            UNDISCH_TAC `~(b = &0)` THEN ASM_REWRITE_TAC[REAL_ABS_NZ] THEN
            REWRITE_TAC[REAL_ABS_NUM; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
            REWRITE_TAC[SYM(REWRITE_CONV[ARITH_SUC] `SUC 0`)] THEN
            REWRITE_TAC[LE_SUC_LT]];
          ALL_TAC] THEN
        SUBGOAL_THEN `abs(a * b) <= abs(a) /\ &0 <= a * b` ASSUME_TAC THENL
         [MP_TAC(SPEC `(n:num) + k` REAL_LT_POW2) THEN
          UNDISCH_TAC `&2 * abs(a * b - &2 pow (n + k)) <= abs a` THEN
          UNDISCH_TAC `abs(a) <= abs(a * b)` THEN
          SUBGOAL_THEN `~(a * b = &0)` MP_TAC THENL
           [ASM_REWRITE_TAC[REAL_ENTIRE]; ALL_TAC] THEN
          SUBGOAL_THEN `&2 * &2 pow (n + k) <= abs(a)` MP_TAC THENL
           [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
            FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
            MATCH_MP_TAC REAL_MONO_POW2 THEN ASM_REWRITE_TAC[LE_SUC_LT];
            REAL_ARITH_TAC];
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
          EXISTS_TAC `abs(a)` THEN ASM_REWRITE_TAC
            [GSYM REAL_ABS_NZ; GSYM REAL_ABS_MUL; REAL_MUL_RID]];
        ALL_TAC] THEN
      MATCH_MP_TAC lemma3 THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_ENTIRE; REAL_INV_EQ_0] THEN
          MATCH_MP_TAC REAL_LT_IMP_NZ THEN REWRITE_TAC[REAL_LT_POW2];
          MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `abs(x)` THEN
          ASM_REWRITE_TAC[GSYM REAL_ABS_NZ; GSYM REAL_ABS_MUL] THEN
          ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c = b * c * a`] THEN
          SUBGOAL_THEN `inv(x) * x = &1` SUBST1_TAC THENL
           [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[];
            REWRITE_TAC[REAL_MUL_RID] THEN
            MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&2 pow k` THEN
            REWRITE_TAC[REAL_LT_POW2; REAL_ABS_LEMMA] THEN
            MATCH_MP_TAC REAL_LET_TRANS THEN
            EXISTS_TAC `&2 pow (SUC(n + k)) - &1` THEN
            REWRITE_TAC[REAL_LT_SUB_RADD; REAL_LE_SUB_LADD] THEN
            ONCE_REWRITE_TAC[ADD_SYM] THEN
            REWRITE_TAC[GSYM REAL_POW_ADD] THEN
            ONCE_REWRITE_TAC[ADD_SYM] THEN
            REWRITE_TAC[REAL_LE_SUC_POW2; REAL_ABS_POW; REAL_ABS_NUM] THEN
            MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 pow e` THEN
            CONJ_TAC THENL
             [MATCH_MP_TAC REAL_MONO_POW2 THEN
              ASM_REWRITE_TAC[LE_SUC_LT];
              UNDISCH_TAC `abs(a - &2 pow k * x) < &1` THEN
              ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]];
        SUBGOAL_THEN `&0 <= b * (&2 pow n * inv x)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
          EXISTS_TAC `a * a` THEN ASM_REWRITE_TAC[REAL_LT_SQUARE] THEN
          REWRITE_TAC[REAL_MUL_RZERO] THEN
          ONCE_REWRITE_TAC[AC REAL_MUL_AC
            `(a * b) * c * d = (a * c) * (b * d)`] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
          EXISTS_TAC `x * x` THEN ASM_REWRITE_TAC[REAL_LT_SQUARE] THEN
          REWRITE_TAC[REAL_MUL_RZERO] THEN
          ONCE_REWRITE_TAC[AC REAL_MUL_AC
           `(a * b) * c * d * e = d * (e * a) * c * b`] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN
          REWRITE_TAC[MATCH_MP REAL_LT_IMP_LE (SPEC_ALL REAL_LT_POW2)] THEN
          FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
            [MATCH_MP REAL_MUL_LINV th]) THEN
          MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&2 pow k` THEN
          REWRITE_TAC[REAL_LT_POW2; REAL_MUL_RZERO; REAL_MUL_LID] THEN
          ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c = b * (a * c)`] THEN
          ONCE_REWRITE_TAC[GSYM REAL_OPPSIGN] THEN
          MATCH_MP_TAC lemma4 THEN EXISTS_TAC `&1` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `abs(a)` THEN CONJ_TAC THENL
           [UNDISCH_TAC `?m. (a = &m) \/ (a = -- (&m))` THEN
            DISCH_THEN(CHOOSE_THEN(DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
            ASM_REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM] THEN
            REWRITE_TAC[REAL_OF_NUM_LE] THEN
            REWRITE_TAC[SYM(REWRITE_CONV[ARITH_SUC] `SUC 0`)] THEN
            REWRITE_TAC[LE_SUC_LT] THEN RULE_ASSUM_TAC
             (REWRITE_RULE[REAL_ARITH `(--x = &0) = (x = &0)`]) THEN
            UNDISCH_TAC `~(&m = &0)` THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
            CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[NOT_LT; LE];
            REWRITE_TAC[REAL_LE_ADDR; REAL_ABS_POS]];
          REWRITE_TAC[REAL_OPPSIGN]]]]]);;

let REALCALC_INV = prove
 (`abs(a - &2 pow k * x) < &1 ==>
   (?m. (a = &m) \/ (a = --(&m))) ==>
   (?m. (b = &m) \/ (b = --(&m))) ==>
   SUC(n + k) <= (2 * e) ==>
   &2 pow e <= abs(a) ==>
   &2 * abs(a * b - &2 pow (n + k)) <= abs(a)
   ==> abs(b - &2 pow n * inv(x)) < &1`,
  REPEAT DISCH_TAC THEN MATCH_MP_TAC REALCALC_INV_LEMMA THEN
  ASM_REWRITE_TAC[]);;

let REALCALC_ADD = prove
 (`(n + 2 = n') ==>
   abs(a - &2 pow n' * x) < &1 ==>
   abs(b - &2 pow n' * y) < &1 ==>
   abs(&4 * c - (a + b)) <= &2
   ==> abs(c - &2 pow n * (x + y)) < &1`,
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
  EXISTS_TAC `&2 pow 2` THEN
  CONV_TAC(LAND_CONV REAL_INT_REDUCE_CONV) THEN
  REWRITE_TAC[REAL_ABS_LEMMA; REAL_SUB_LDISTRIB; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  SUBST1_TAC(REAL_INT_REDUCE_CONV `&2 pow 2`) THEN
  MATCH_MP_TAC REAL_ABS_TRIANGLE_LEMMA THEN
  EXISTS_TAC `a + b` THEN
  GEN_REWRITE_TAC RAND_CONV [SYM(REAL_INT_REDUCE_CONV `&2 + &2`)] THEN
  MATCH_MP_TAC REAL_LTE_ADD2 THEN ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC
   [REAL_ARITH `(x + y) - a * (u + v) = (x - a * u) + (y - a * v)`] THEN
  GEN_REWRITE_TAC RAND_CONV [SYM(REAL_INT_REDUCE_CONV `&1 + &1`)] THEN
  MATCH_MP_TAC(REAL_LET_IMP REAL_ABS_TRIANGLE) THEN
  MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]);;

let REALCALC_MUL = prove
 (`abs(a - &2 pow k * x) < &1 ==>
   abs(b - &2 pow l * y) < &1 ==>
   (n + m = k + l) ==>
   &2 * (abs(a) + abs(b) + &1) <= &2 pow m ==>
   &2 * abs(&2 pow m * c - a * b) <= &2 pow m
   ==> abs(c - &2 pow n * (x * y)) < &1`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&2 pow m` THEN
  REWRITE_TAC[REAL_LT_POW2; REAL_ABS_LEMMA; REAL_SUB_LDISTRIB] THEN
  MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&2` THEN
  CONV_TAC(LAND_CONV (EQT_INTRO o REAL_ARITH)) THEN
  REWRITE_TAC[REAL_MUL_RID] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_2] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&2 * abs(&2 pow m * c - a * b) +
              &2 * abs(a * b - &2 pow m * &2 pow n * x * y)` THEN
  CONV_TAC(LAND_CONV (EQT_INTRO o REAL_ARITH)) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_ADD2 THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_POW_ADD] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `((a * b) * c) * d = (a * c) * (b * d)`] THEN
  SUBGOAL_THEN `?d. abs(d) < &1 /\ (&2 pow k * x = a + d)` MP_TAC THENL
   [EXISTS_TAC `&2 pow k * x - a` THEN
    UNDISCH_TAC `abs(a - &2 pow k * x) < &1` THEN REAL_ARITH_TAC;
    DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))] THEN
  SUBGOAL_THEN `?e. abs(e) < &1 /\ (&2 pow l * y = b + e)` MP_TAC THENL
   [EXISTS_TAC `&2 pow l * y - b` THEN
    UNDISCH_TAC `abs(b - &2 pow l * y) < &1` THEN REAL_ARITH_TAC;
    DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `&2 * (abs(a) * &1 + abs(b) * &1 + &1 * &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN
    CONV_TAC(LAND_CONV (EQT_INTRO o REAL_ARITH)) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs(a) * abs(e) + abs(b) * abs(d) + abs(d) * abs(e)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_ADD2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LET_ADD2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
          MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]]]];
    ASM_REWRITE_TAC[REAL_MUL_RID]]);;

(* ------------------------------------------------------------------------- *)
(* Square root.                                                              *)
(* ------------------------------------------------------------------------- *)

let REALCALC_SQRT = prove
 (`abs(a - &2 pow n * x) < &1
       ==> &1 <= x
           ==> abs(b pow 2 - &2 pow n * a) <= b
               ==> abs(b - &2 pow n * sqrt(x)) < &1`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
  EXISTS_TAC `abs(b + &2 pow n * sqrt(x))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `!z. abs(z) <= b /\ &0 < c ==> &0 < abs(b + c)`) THEN
    EXISTS_TAC `b pow 2 - &2 pow n * a` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH; REAL_LT_MUL;
                 SQRT_POS_LT; REAL_ARITH `&1 <= x ==> &0 < x`]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_MUL_RID] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
    `(a + b) * (a - b) = a * a - b * b`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!c d. abs(b - c) <= d /\ abs(c - a) < e - d
          ==> abs(b - a) < e`) THEN
  MAP_EVERY EXISTS_TAC [`&2 pow n * a`; `b:real`] THEN
  ASM_REWRITE_TAC[GSYM REAL_POW_2] THEN
  REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
  MATCH_MP_TAC(REAL_ARITH `a < c ==> a < abs(b + c) - b`) THEN
  REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN
  SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1` THEN
  ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; GSYM POW_2; SQRT_POW_2;
               REAL_ARITH `&1 <= x ==> &0 <= x`] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP(REAL_ARITH `&1 <= x ==> &0 <= x`)) THEN
  UNDISCH_TAC `&1 <= x` THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `x = sqrt(x) pow 2` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[SQRT_POW2];
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[POW_2] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
    ASM_SIMP_TAC[SQRT_POS_LE]]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas common to all the Taylor series error analyses.                    *)
(* ------------------------------------------------------------------------- *)

let STEP_LEMMA1 = prove
 (`!a b c d x y.
        abs(a - c) <= x /\ abs(b - d) <= y
        ==> abs(a * b - c * d) <= abs(c) * y + abs(d) * x + x * y`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `u = a - c` THEN ABBREV_TAC `v = b - d` THEN
  SUBGOAL_THEN `a = c + u` SUBST1_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `b = d + v` SUBST1_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN SUBST1_TAC
   (REAL_ARITH `(c + u) * (d + v) - c * d = c * v + d * u + u * v`) THEN
  REPEAT(MATCH_MP_TAC (REAL_LE_IMP REAL_ABS_TRIANGLE) THEN
         MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC) THEN
  REWRITE_TAC[REAL_ABS_MUL] THENL
   [MATCH_MP_TAC REAL_LE_LMUL;
    MATCH_MP_TAC REAL_LE_LMUL;
    MATCH_MP_TAC REAL_LE_MUL2] THEN
  ASM_REWRITE_TAC[REAL_ABS_POS]);;

let STEP_LEMMA2 = prove
 (`!n s t u x y k l a d.
        &0 < a /\
        &0 < d /\
        abs(s - &2 pow n * x) <= k /\
        abs(t - &2 pow n * y) <= l /\
        &2 * abs(u * &2 pow n * d - a * s * t) <= &2 pow n * d
        ==> abs(u - &2 pow n * (a / d) * (x * y)) <=
            (a / d) * (abs(x) + k / (&2 pow n)) * l +
            ((a / d) * k * abs(y) + &1 / &2)`,
   REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   ONCE_REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN
    (CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP STEP_LEMMA1) ASSUME_TAC) THEN
   SUBGOAL_THEN `&0 < &2 * &2 pow n * d` ASSUME_TAC THENL
    [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
     ASM_REWRITE_TAC[REAL_LT_POW2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
   EXISTS_TAC `&2 * &2 pow n * d` THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[real_div; REAL_ADD_LDISTRIB; REAL_ADD_RDISTRIB] THEN
   SUBGOAL_THEN
     `!z. (&2 * &2 pow n * d) * abs(z) = abs((&2 * &2 pow n * d) * z)`
   (fun th -> REWRITE_TAC[th])
   THENL
    [GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN AP_THM_TAC THEN
     AP_TERM_TAC THEN UNDISCH_TAC `&0 < &2 * &2 pow n * d` THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
   (MATCH_MP_TAC o GEN_ALL o REAL_ARITH)
     `abs(a - b) + abs(b - c) <= d ==> abs(a - c) <= d` THEN
   EXISTS_TAC `&2 * a * s * t` THEN
   REWRITE_TAC[GSYM REAL_MUL_ASSOC; REAL_ADD_ASSOC] THEN
   GEN_REWRITE_TAC RAND_CONV [REAL_ADD_SYM] THEN
   SUBGOAL_THEN `(inv(&2) * &2 = &1) /\
                 (inv(&2 pow n) * &2 pow n = &1) /\
                 (inv(d) * d = &1)`
   STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
     REWRITE_TAC[REAL_POW_EQ_0] THEN
     UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
    [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
     ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_RID] THEN
     REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_ABS_LEMMA1] THEN
     REWRITE_TAC[REAL_MUL_ASSOC] THEN
     GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV o LAND_CONV)
        [REAL_MUL_SYM] THEN ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC];

     REWRITE_TAC(map (GSYM o SPEC `&2`)
       [REAL_SUB_LDISTRIB; REAL_ADD_LDISTRIB]) THEN
     REWRITE_TAC[GSYM REAL_ABS_LEMMA1] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
     CONV_TAC(LAND_CONV (EQT_INTRO o REAL_ARITH)) THEN REWRITE_TAC[] THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
      [AC REAL_MUL_AC
        `a * b * c * d * e * f * g = d * (a * f) * (c * g) * (e * b)`] THEN
     GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV)
      [AC REAL_MUL_AC
        `a * b * c * d * e * f = c * (a * e) * f * (d * b)`] THEN
     GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
      [AC REAL_MUL_AC
        `a * b * c * d * e * f * g = c * (e * g) * (f * a) * (d * b)`] THEN
     GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
      [AC REAL_MUL_AC
        `a * b * c * d * e * f = c * (a * f) * e * (d * b)`] THEN
     GEN_REWRITE_TAC RAND_CONV
      [AC REAL_ADD_AC `(a + b) + c = a + c + b`] THEN
     ASM_REWRITE_TAC[REAL_MUL_RID] THEN
     REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; GSYM REAL_SUB_LDISTRIB] THEN
     REWRITE_TAC[REAL_ABS_MUL] THEN
     SUBGOAL_THEN `abs(a) = a` SUBST1_TAC THENL
      [UNDISCH_TAC `&0 < a` THEN REAL_ARITH_TAC;
       MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_LEMMA] THEN
       MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Now specific instances.                                                   *)
(* ------------------------------------------------------------------------- *)

let STEP_EXP = prove
 (`abs(x) <= &1 /\
   abs(s - &2 pow n * x) <= &1 /\
   abs(t - &2 pow n * (x pow i / &(FACT i))) <= k /\
   &2 * abs(u * &2 pow n * &(SUC i) - s * t) <= &2 pow n * &(SUC i)
   ==> abs(u - &2 pow n * (x pow (SUC i)) / &(FACT(SUC i))) <=
            (&2 / &(SUC i)) * k + &1 / &(FACT(SUC i)) + &1 / &2`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `s:real`; `t:real`; `u:real`;
                `x:real`; `x pow i / &(FACT i)`;
                `&1`; `k:real`; `&1`; `&(SUC i)`] STEP_LEMMA2) THEN
  ASM_REWRITE_TAC[REAL_LT_01; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_OF_NUM_LT; LT_0] THEN
  REWRITE_TAC[FACT; real_div; GSYM REAL_OF_NUM_MUL; real_pow] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_INV_MUL] THEN
  MATCH_MP_TAC(REAL_ARITH `(a = b) /\ c <= d ==> a <= c ==> b <= d`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_AC];
    REWRITE_TAC[REAL_ADD_ASSOC; REAL_LE_RADD] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_OF_NUM_LE; LE_0];
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `&2 = &1 + &1`] THEN
          MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC[REAL_LE_POW2];
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `abs(t - &2 pow n * (x pow i / &(FACT i)))` THEN
          ASM_REWRITE_TAC[REAL_ABS_POS]];
        REWRITE_TAC[REAL_ABS_MUL] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
        CONJ_TAC THENL
         [REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
          ASM_REWRITE_TAC[REAL_ABS_POS];
          MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> abs(a) <= a`) THEN
          MATCH_MP_TAC REAL_LE_INV THEN
          REWRITE_TAC[REAL_OF_NUM_LE; LE_0]]]]]);;

let STEP_SIN = prove
 (`abs(x) <= &1 /\
   abs(s - &2 pow n * --(x pow 2)) <= &1 /\
   abs(t - &2 pow n *
           x pow (2 * i + 1) / &(FACT (2 * i + 1)))
   <= &1 /\
   &2 * abs(u * &2 pow n * &(2 * i + 2) * &(2 * i + 3)
            - s * t)
   <= &2 pow n * &(2 * i + 2) * &(2 * i + 3)
   ==> abs(u - &2 pow n *
               --(x pow (2 * (SUC i) + 1)) /
               &(FACT (2 * (SUC i) + 1))) <= &1`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `s:real`; `t:real`; `u:real`;
                `--(x pow 2)`;
                `x pow (2 * i + 1) /
                 &(FACT(2 * i + 1))`;
                `&1`; `&1`; `&1`;
                `&(2 * i + 2) * &(2 * i + 3)`]
         STEP_LEMMA2) THEN
  ASM_REWRITE_TAC[REAL_LT_01; REAL_MUL_LID] THEN W(C SUBGOAL_THEN
  (fun th -> REWRITE_TAC[th]) o funpow 2 (fst o dest_imp) o snd) THENL
   [REWRITE_TAC(map num_CONV [`3`; `2`; `1`]) THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; LT_0]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(a = b) /\ c <= d ==> a <= c ==> b <= d`) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN SUBGOAL_THEN
      `2 * (SUC i) + 1 = SUC(SUC(2 * i + 1))`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [GSYM REAL_OF_NUM_EQ] THEN
      REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[real_pow; FACT] THEN
      REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
      REWRITE_TAC[ARITH] THEN
      REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_OF_NUM_MUL;
                  GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RNEG; REAL_MUL_LNEG] THEN
      REWRITE_TAC[REAL_POW_2; REAL_MUL_AC]];
    GEN_REWRITE_TAC RAND_CONV
     [SYM(REAL_RAT_REDUCE_CONV `&1 / &3 + &1 / &6 + &1 / &2`)] THEN
    REWRITE_TAC[REAL_ADD_ASSOC; REAL_LE_RADD] THEN
    SUBGOAL_THEN `&1 / (&(2 * i + 2) * &(2 * i + 3))
                  <= &1 / &6` ASSUME_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      CONV_TAC(LAND_CONV (EQT_INTRO o REAL_ARITH)) THEN REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `&6 = &2 * &3`] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC LE_MULT2 THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[LE_ADD]; ALL_TAC] THEN
    REWRITE_TAC[SYM(REAL_RAT_REDUCE_CONV `&1 / &6 * &2`)] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_POS];
      MATCH_MP_TAC REAL_LE_ADD THEN
      REWRITE_TAC[REAL_MUL_RID; REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN
      REWRITE_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ; REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_LT_POW2];
      REWRITE_TAC[REAL_MUL_RID]] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `&2 = &1 + &1`] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_POW] THEN
        MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS];
        REWRITE_TAC[real_div; REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC[REAL_LE_POW2]];
      REWRITE_TAC[real_div; REAL_ABS_MUL] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
        ASM_REWRITE_TAC[REAL_ABS_POS];
        REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM] THEN
        MATCH_MP_TAC REAL_INV_LE_1 THEN
        REWRITE_TAC[REAL_OF_NUM_LE; FACT_LE]]]]);;

let STEP_COS = prove
 (`abs(x) <= &1 /\
   abs(s - &2 pow n * --(x pow 2)) <= &1 /\
   abs(t - &2 pow n *
           x pow (2 * i) / &(FACT (2 * i)))
   <= k /\
   &2 * abs(u * &2 pow n * &(2 * i + 1) * &(2 * i + 2)
            - s * t)
   <= &2 pow n * &(2 * i + 1) * &(2 * i + 2)
   ==> abs(u - &2 pow n *
               --(x pow (2 * (SUC i))) /
               &(FACT (2 * (SUC i))))
       <= (&2 * inv(&(2 * i + 1) * &(2 * i + 2))) * k
          + inv(&(FACT(2 * i + 2))) + &1 / &2`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `s:real`; `t:real`; `u:real`;
                `--(x pow 2)`;
                `x pow (2 * i) /
                 &(FACT(2 * i))`;
                `&1`; `k:real`; `&1`;
                `&(2 * i + 1) * &(2 * i + 2)`]
         STEP_LEMMA2) THEN
  ASM_REWRITE_TAC[REAL_LT_01; REAL_MUL_LID] THEN W(C SUBGOAL_THEN
  (fun th -> REWRITE_TAC[th]) o funpow 2 (fst o dest_imp) o snd) THENL
   [REWRITE_TAC(map num_CONV [`3`; `2`; `1`]) THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; LT_0]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(a = b) /\ c <= d ==> a <= c ==> b <= d`) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN SUBGOAL_THEN
      `2 * (SUC i) = SUC(SUC(2 * i))`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [GSYM REAL_OF_NUM_EQ] THEN
      REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[real_pow; FACT] THEN
      REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
      REWRITE_TAC[ARITH] THEN
      REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_OF_NUM_MUL;
                  GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RNEG; REAL_MUL_LNEG] THEN
      REWRITE_TAC[REAL_POW_2; REAL_MUL_AC]];

    REWRITE_TAC[REAL_ADD_ASSOC; REAL_LE_RADD] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_LID] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_SYM] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV THEN
          REWRITE_TAC[REAL_OF_NUM_MUL; REAL_POS];
          GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `&2 = &1 + &1`] THEN
          MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
           [REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_POW] THEN
            MATCH_MP_TAC REAL_POW_1_LE THEN
            ASM_REWRITE_TAC[REAL_ABS_POS];
            MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC[REAL_LE_POW2]]];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
         `abs(t - &2 pow n * x pow (2 * i) / &(FACT (2 * i)))` THEN
        ASM_REWRITE_TAC[REAL_ABS_POS]];
      REWRITE_TAC[real_div; REAL_MUL_LID; REAL_INV_MUL; REAL_ABS_MUL] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      ONCE_REWRITE_TAC[AC REAL_MUL_AC
        `(a * b) * c * d = (d * a * b) * c`] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REPEAT CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        REWRITE_TAC[REAL_POS; REAL_ABS_POS; REAL_LE_INV_EQ];
        REWRITE_TAC[REAL_ABS_INV] THEN
        REWRITE_TAC[GSYM REAL_INV_MUL; REAL_ABS_NUM] THEN
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
        REWRITE_TAC[num_CONV `2`; num_CONV `1`; ADD_CLAUSES] THEN
        REWRITE_TAC[SYM(num_CONV `2`); SYM(num_CONV `1`)] THEN
        REWRITE_TAC[FACT; REAL_OF_NUM_MUL] THEN
        REWRITE_TAC[MULT_AC];
        REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
        ASM_REWRITE_TAC[REAL_ABS_POS]]]]);;

let STEP_LN = prove
 (`2 <= n /\
   abs(x) <= &1 / &2 /\
   abs(s - &2 pow n * --x) <= &1 /\
   abs(t - &2 pow n * -- ((--x) pow (SUC i) / &(SUC i))) <= &3 /\
   &2 * abs(u * &2 pow n * &(SUC(SUC i)) - &(SUC i) * s * t)
   <= &2 pow n * &(SUC(SUC i))
   ==> abs(u - &2 pow n * -- ((--x) pow (SUC(SUC i)) / &(SUC(SUC i)))) <= &3`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `s:real`; `t:real`; `u:real`;
                `--x`;
                `-- (--x pow (SUC i) / &(SUC i))`;
                `&1`; `&3`;
                `&(SUC i)`;
                `&(SUC(SUC i))`]
         STEP_LEMMA2) THEN
  ASM_REWRITE_TAC[REAL_LT_01; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_OF_NUM_LT; LT_0] THEN
  MATCH_MP_TAC(REAL_ARITH `(a = b) /\ c <= d ==> a <= c ==> b <= d`) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_pow; real_div; REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    SUBGOAL_THEN `inv(&(SUC i)) * &(SUC i) = &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN
      REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC];
      ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_MUL_AC]];
    GEN_REWRITE_TAC RAND_CONV [SYM(REAL_RAT_REDUCE_CONV
      `(&1 / &2 + &1 / &4) * &3 + &1 / &4 + &1 / &2`)] THEN
    REWRITE_TAC[REAL_ADD_ASSOC; REAL_LE_RADD] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONV_TAC(RAND_CONV (EQT_INTRO o REAL_ARITH)) THEN REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
        EXISTS_TAC `&(SUC(SUC i))` THEN
        REWRITE_TAC[REAL_MUL_LZERO; REAL_OF_NUM_LT; LT_0] THEN
        REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC(REAL_ARITH `(x = &1) ==> &0 <= x`) THEN
        MATCH_MP_TAC REAL_MUL_LINV THEN
        REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC];
        MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
        EXISTS_TAC `&(SUC(SUC i))` THEN
        REWRITE_TAC[REAL_OF_NUM_LT; LT_0] THEN
        REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_MUL_ASSOC] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
        REWRITE_TAC[REAL_OF_NUM_LE; LE] THEN
        MATCH_MP_TAC(REAL_ARITH `(x = &1) ==> &0 <= x /\ x <= &1`) THEN
        MATCH_MP_TAC REAL_MUL_LINV THEN
        REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC];
        MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_ABS_POS] THEN
        REWRITE_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_LT_POW2];
        MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[REAL_ABS_NEG] THEN
        REWRITE_TAC[real_div; REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN
        CONV_TAC(LAND_CONV (EQT_INTRO o REAL_ARITH)) THEN REWRITE_TAC[] THEN
        SUBST1_TAC(SYM(REAL_INT_REDUCE_CONV `&2 pow 2`)) THEN
        MATCH_MP_TAC REAL_MONO_POW2 THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[real_div; REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_INV] THEN
      REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NEG; REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_ABS_NUM] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
      SUBGOAL_THEN `inv(&(SUC i)) * &(SUC i) = &1` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC];
        GEN_REWRITE_TAC RAND_CONV
         [EQT_ELIM(REAL_RAT_REDUCE_CONV `inv(&4) = inv(&2) * inv(&2)`)] THEN
        ASM_REWRITE_TAC[REAL_MUL_RID; GSYM REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC
          [REAL_POS; REAL_ABS_POS; REAL_LE_INV_EQ; GSYM REAL_ABS_POW] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_POS] THEN
          REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN
          MP_TAC(SPEC `i:num` REAL_POS) THEN REAL_ARITH_TAC;
          REWRITE_TAC[real_pow; REAL_ABS_POW] THEN
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LE_MUL2 THEN
          REWRITE_TAC[REAL_LE_INV_EQ; REAL_ABS_POS] THEN
          REPEAT CONJ_TAC THENL
           [CONV_TAC(RAND_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
            MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS];
            MATCH_MP_TAC REAL_POW_1_LE THEN REWRITE_TAC[REAL_ABS_POS] THEN
            MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &2` THEN
            ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV]]]]]);;

(* ------------------------------------------------------------------------- *)
(* Expand the "!k. SUC k < r ==> P k" term for given numeral r.              *)
(* ------------------------------------------------------------------------- *)

let EXPAND_RANGE_CONV =
  let pth0 = prove
   (`(!k. SUC k < 0 ==> P k) <=> T`,
    REWRITE_TAC[LT])
  and pth1 = prove
   (`(!k. k < (SUC m) ==> P k) <=>
     (!k. k < m ==> P k) /\ P m`,
    REWRITE_TAC[LT] THEN MESON_TAC[])
  and pth2 = prove
   (`(!k. k < 0 ==> P k) <=> T`,
    REWRITE_TAC[LT]) in
  let triv_conv = GEN_REWRITE_CONV I [pth0]
  and trivial_conv = GEN_REWRITE_CONV I [pth2]
  and nontrivial_conv = GEN_REWRITE_CONV I [pth1] in
  let s_tm = `s:real`
  and m_tm = `m:num`
  and n_tm = `n:num` in
  let rec expand_conv tm =
    try trivial_conv tm
    with Failure _ ->
        let mth = num_CONV(rand(lhand(body(rand tm)))) in
        let th1 = BINDER_CONV(LAND_CONV(RAND_CONV(K mth))) tm in
        let th2 = TRANS th1 (nontrivial_conv (rand(concl th1))) in
        let th3 = COMB2_CONV (RAND_CONV expand_conv) (SUBS_CONV[SYM mth])
                             (rand(concl th2)) in
        TRANS th2 th3 in
  let hack_conv =
    triv_conv ORELSEC
    (BINDER_CONV (LAND_CONV
       ((RAND_CONV num_CONV) THENC REWR_CONV LT_SUC)) THENC
     expand_conv) in
  hack_conv;;

(* ------------------------------------------------------------------------- *)
(* Lemmas leading to iterative versions.                                     *)
(* ------------------------------------------------------------------------- *)

let STEP_EXP_THM = prove
 (`abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   abs(t(i) - &2 pow n * (x pow i / &(FACT i))) <= k ==>
   &2 * abs(t(SUC i) * &2 pow n * &(SUC i) - s * t(i)) <= &2 pow n * &(SUC i)
   ==> abs(t(SUC i) - &2 pow n * (x pow (SUC i)) / &(FACT(SUC i))) <=
            (&2 / &(SUC i)) * k + &1 / &(FACT(SUC i)) + &1 / &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(GEN_ALL STEP_EXP) THEN
  MAP_EVERY EXISTS_TAC [`s:real`; `t(i:num):real`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  ASM_REWRITE_TAC[]);;

let STEP_EXP_RULE th =
  let th1 = MATCH_MP STEP_EXP_THM th in
  let th2 = UNDISCH(PURE_REWRITE_RULE[ARITH_SUC] th1) in
  let th3 = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV NUM_FACT_CONV)) th2 in
  let th4 = CONV_RULE(RAND_CONV REAL_RAT_REDUCE_CONV) th3 in
  let th5 = ASSUME(find is_conj (hyp th)) in
  let th6a,th6b = (I F_F CONJUNCT1) (CONJ_PAIR th5) in
  CONJ th6a (CONJ th6b th4);;

let STEP_EXP_0 = (UNDISCH o prove)
 (`abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   (t(0) = &2 pow n) ==>
   abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   abs(t(0) - &2 pow n * (x pow 0 / &(FACT 0))) <= &0`,
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_pow; FACT; real_div; REAL_INV_1; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_LE_REFL]);;

let STEP_EXP_1 = STEP_EXP_RULE STEP_EXP_0;;     (* e(1) = 3/2           *)
let STEP_EXP_2 = STEP_EXP_RULE STEP_EXP_1;;     (* e(2) = 5/2           *)
let STEP_EXP_3 = STEP_EXP_RULE STEP_EXP_2;;     (* e(3) = 7/3           *)
let STEP_EXP_4 = STEP_EXP_RULE STEP_EXP_3;;     (* e(4) = 41/24         *)
let STEP_EXP_5 = STEP_EXP_RULE STEP_EXP_4;;     (* e(5) = 143/120       *)

let STEP_EXP_4_PLUS = prove
 (`4 <= m /\
   abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   (t(0) = &2 pow n) /\
   (!k. SUC k < SUC m ==>
                &2 * abs(t(SUC k) * &2 pow n * &(SUC k) - s * t(k))
                <= &2 pow n * &(SUC k))
   ==> abs(t m - &2 pow n * x pow m / &(FACT m)) <= &2`,
  let lemma = prove
   (`(!k. k < (SUC m) ==> P k) <=>
     (!k. k < m ==> P k) /\ P m`,
    REWRITE_TAC[LT] THEN MESON_TAC[]) in
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  POP_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[LT_SUC] THEN SPEC_TAC(`d:num`,`d:num`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN
    SUBST1_TAC(TOP_DEPTH_CONV num_CONV `4`) THEN
    REWRITE_TAC[lemma] THEN REWRITE_TAC[ARITH_SUC] THEN
    REWRITE_TAC[LT] THEN STRIP_TAC THEN
    MP_TAC (DISCH_ALL STEP_EXP_4) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[ADD_CLAUSES; lemma] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 / &(SUC(4 + d)) * &2 +
                &1 / &(FACT(SUC(4 + d))) + &1 / &2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(GEN_ALL STEP_EXP) THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `s:real` THEN EXISTS_TAC `t(4 + d):real` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      GEN_REWRITE_TAC RAND_CONV
        [SYM(REAL_RAT_REDUCE_CONV `&3 / &2 + &1 / &2`)] THEN
      REWRITE_TAC[REAL_LE_RADD; REAL_ADD_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 / &5 + &1 / &120` THEN
      CONV_TAC(RAND_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
        REWRITE_TAC[REAL_ARITH `&2 * &2 = &4`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_ARITH `&0 <= &4`] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN
        MP_TAC(SPEC `d':num` REAL_POS) THEN REAL_ARITH_TAC;
        REWRITE_TAC[real_div; REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN
        CONV_TAC(LAND_CONV (EQT_INTRO o REAL_ARITH)) THEN REWRITE_TAC[] THEN
        SUBST1_TAC(SYM(NUM_FACT_CONV `FACT 5`)) THEN
        REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC FACT_MONO THEN
        REWRITE_TAC[num_CONV `5`; LE_SUC; LE_ADD]]]]);;

let STEPS_EXP_0 = prove
 (`abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   (t(0) = &2 pow n) /\
   (!k. SUC k < 0 ==>
                &2 * abs(t(SUC k) * &2 pow n * &(SUC k) - s * t(k))
                <= &2 pow n * &(SUC k))
   ==> abs(sum(0,0) t -
           &2 pow n * sum(0,0) (\i. x pow i / &(FACT i))) <= &2 * &0`,
  STRIP_TAC THEN ASM_REWRITE_TAC[sum] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ABS_0; REAL_SUB_REFL; REAL_LE_REFL]);;

let STEPS_EXP_1 = prove
 (`abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   (t(0) = &2 pow n) /\
   (!k. SUC k < 1 ==>
                &2 * abs(t(SUC k) * &2 pow n * &(SUC k) - s * t(k))
                <= &2 pow n * &(SUC k))
   ==> abs(sum(0,1) t - &2 pow n * sum(0,1)(\i. x pow i / &(FACT i)))
         <= &2 * &1`,
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_RANGE_CONV) THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN
  CONV_TAC(RAND_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  MP_TAC (DISCH_ALL STEP_EXP_0) THEN ASM_REWRITE_TAC[]);;

let STEPS_EXP_2 = prove
 (`abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   (t(0) = &2 pow n) /\
   (!k. SUC k < 2 ==>
                &2 * abs(t(SUC k) * &2 pow n * &(SUC k) - s * t(k))
                <= &2 pow n * &(SUC k))
   ==> abs(sum(0,2) t - &2 pow n * sum(0,2) (\i. x pow i / &(FACT i)))
       <= &2 * &2`,
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_RANGE_CONV) THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[REAL_ARITH `(a + b) - (c + d) = (a - c) + (b - d)`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0 + &3 / &2` THEN
  CONV_TAC(RAND_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_LE_IMP(REAL_ARITH `abs(a + b) <= abs(a) + abs(b)`)) THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MP_TAC (DISCH_ALL STEP_EXP_0) THEN ASM_REWRITE_TAC[];
    MP_TAC (DISCH_ALL STEP_EXP_1) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES]]);;

let STEPS_EXP_3 = prove
 (`abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   (t(0) = &2 pow n) /\
   (!k. SUC k < 3 ==>
                &2 * abs(t(SUC k) * &2 pow n * &(SUC k) - s * t(k))
                <= &2 pow n * &(SUC k))
   ==> abs(sum(0,3) t - &2 pow n * sum(0,3) (\i. x pow i / &(FACT i)))
       <= &2 * &3`,
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_RANGE_CONV) THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[REAL_ARITH `(a + b) - (c + d) = (a - c) + (b - d)`] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0 + &3 / &2 + &5 / &2` THEN
  CONV_TAC(RAND_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  REPEAT
   (MATCH_MP_TAC(REAL_LE_IMP(REAL_ARITH `abs(a + b) <= abs(a) + abs(b)`)) THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC)
  THENL
   [MP_TAC (DISCH_ALL STEP_EXP_0) THEN ASM_REWRITE_TAC[];
    MP_TAC (DISCH_ALL STEP_EXP_1) THEN ASM_REWRITE_TAC[ADD_CLAUSES];
    MP_TAC (DISCH_ALL STEP_EXP_2) THEN ASM_REWRITE_TAC[ADD_CLAUSES]]);;

let STEPS_EXP_4 = prove
 (`abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   (t(0) = &2 pow n) /\
   (!k. SUC k < 4 ==>
                &2 * abs(t(SUC k) * &2 pow n * &(SUC k) - s * t(k))
                <= &2 pow n * &(SUC k))
   ==> abs(sum(0,4) t - &2 pow n * sum(0,4) (\i. x pow i / &(FACT i)))
       <= &2 * &4`,
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_RANGE_CONV) THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[REAL_ARITH `(a + b) - (c + d) = (a - c) + (b - d)`] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&0 + &3 / &2 + &5 / &2 + &7 / &3` THEN
  CONV_TAC(RAND_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  REPEAT
   (MATCH_MP_TAC(REAL_LE_IMP(REAL_ARITH `abs(a + b) <= abs(a) + abs(b)`)) THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC)
  THENL
   [MP_TAC (DISCH_ALL STEP_EXP_0) THEN ASM_REWRITE_TAC[];
    MP_TAC (DISCH_ALL STEP_EXP_1) THEN ASM_REWRITE_TAC[ADD_CLAUSES];
    MP_TAC (DISCH_ALL STEP_EXP_2) THEN ASM_REWRITE_TAC[ADD_CLAUSES];
    MP_TAC (DISCH_ALL STEP_EXP_3) THEN ASM_REWRITE_TAC[ADD_CLAUSES]]);;

(* ------------------------------------------------------------------------- *)
(* Iterated versions.                                                        *)
(* ------------------------------------------------------------------------- *)

let STEPS_EXP_LEMMA = prove
 (`(!k. P(SUC k) ==> P(k)) /\
   (P(0) ==> (abs(sum(0,0) z) <= &2 * &0)) /\
   (P(1) ==> (abs(sum(0,1) z) <= &2 * &1)) /\
   (P(2) ==> (abs(sum(0,2) z) <= &2 * &2)) /\
   (P(3) ==> (abs(sum(0,3) z) <= &2 * &3)) /\
   (P(4) ==> (abs(sum(0,4) z) <= &2 * &4)) /\
   (!m. 4 <= m /\ P(SUC m) ==> (abs(z m) <= &2))
   ==> !m. P(m) ==> (abs(sum(0,m) z) <= &2 * &m)`,
  STRIP_TAC THEN SUBGOAL_THEN
    `!d. P(d + 4) ==>
         abs(sum(0,d + 4) z) <= &2 * &(d + 4)`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_TAC THEN REWRITE_TAC[sum; ADD1] THEN
    ONCE_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    MATCH_MP_TAC(REAL_LE_IMP(REAL_ARITH `abs(a + b) <= abs(a) + abs(b)`)) THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_MUL_RID] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[ADD_CLAUSES] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[LE_ADD]];
    GEN_TAC THEN
    DISJ_CASES_THEN MP_TAC (SPECL [`4`; `m:num`] LE_CASES) THENL
     [DISCH_THEN(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[];
      SUBST1_TAC(TOP_DEPTH_CONV num_CONV `4`) THEN
      REWRITE_TAC[LE] THEN REWRITE_TAC[ARITH_SUC] THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
      ASM_REWRITE_TAC[]]]);;

let STEPS_EXP = prove
 (`abs(x) <= &1 /\
   abs(s - &2 pow n * x) < &1 /\
   (t(0) = &2 pow n) /\
   (!k. SUC k < m ==>
                &2 * abs(t(SUC k) * &2 pow n * &(SUC k) - s * t(k))
                <= &2 pow n * &(SUC k))
   ==> abs(sum(0,m) t - &2 pow n * sum(0,m) (\i. x pow i / &(FACT i)))
       <= &2 * &m`,
  REWRITE_TAC[REAL_MUL_RSUM0; REAL_SUB_SUM0] THEN
  SPEC_TAC(`m:num`,`m:num`) THEN MATCH_MP_TAC STEPS_EXP_LEMMA THEN
  REWRITE_TAC[GSYM REAL_SUB_SUM0; GSYM REAL_MUL_RSUM0] THEN
  REWRITE_TAC[STEPS_EXP_0; STEPS_EXP_1; STEPS_EXP_2; STEPS_EXP_3] THEN
  REWRITE_TAC[STEPS_EXP_4; STEP_EXP_4_PLUS] THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `k:num` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LT]);;

let STEPS_LN = prove
 (`2 <= n /\
   abs(x) <= &1 / &2 /\
   abs(s - &2 pow n * --x) < &1 /\
   (t(0) = --s) /\
   (!k. SUC k < m ==>
                &2 * abs(t(SUC k) * &2 pow n * &(SUC(SUC k))
                         - &(SUC k) * s * t(k))
                <= &2 pow n * &(SUC(SUC k)))
   ==> abs(sum(0,m) t - &2 pow n * sum(0,m)
                (\i. (--(&1)) pow i * x pow (SUC i) / &(SUC i))) <= &3 * &m`,
  REWRITE_TAC[REAL_MUL_RSUM0; REAL_SUB_SUM0] THEN
  STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC (REAL_LE_IMP SUM_ABS_LE) THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[ADD_CLAUSES; LE_0] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[real_pow; ARITH; REAL_DIV_1; REAL_MUL_LID; REAL_MUL_RID] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `-- a - b * c = --(a - b * --c)`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN
    ASM_SIMP_TAC[REAL_ABS_NEG; REAL_LT_IMP_LE; REAL_OF_NUM_LE; ARITH];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  SUBGOAL_THEN `p:num < m` (ANTE_RES_THEN MP_TAC) THENL
   [UNDISCH_TAC `SUC p < m` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `!y. abs(x - y) + abs(y - z) <= e ==> abs(x - z) <= e`) THEN
  EXISTS_TAC `&(SUC p) * s * t p / (&2 pow n * &(SUC(SUC p)))` THEN
  ONCE_REWRITE_TAC [SYM(REAL_RAT_REDUCE_CONV `&1 / &2 + &5 / &2`)] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
    EXISTS_TAC `&2 pow n * &(SUC(SUC p))` THEN
    SUBGOAL_THEN `&0 < &2 pow n * &(SUC(SUC p))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN
      SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; LT_0; ARITH]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!x y. &0 < y ==> (abs(x) * y = abs(x * y))`
     (fun th -> ASM_SIMP_TAC[th]) THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
      AP_TERM_TAC THEN ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&2` THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_SUB_RDISTRIB] THEN
    SUBGOAL_THEN `!a b c d. &0 < a ==> ((b * c * d / a) * a = b * c * d)`
     (fun th -> ASM_SIMP_TAC[th]) THEN
    SIMP_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RID;
             REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!y. abs(x - y) + abs(y - z) <= e ==> abs(x - z) <= e`) THEN
  EXISTS_TAC `--(&1) pow p * s * x pow (SUC p) / &(SUC(SUC p))` THEN
  ONCE_REWRITE_TAC [SYM(REAL_RAT_REDUCE_CONV `&9 / &4 + &1 / &4`)] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [SUBGOAL_THEN `--(&1) pow p * s * x pow (SUC p) / &(SUC(SUC p)) =
                  &(SUC p) * s *
                  (&2 pow n * --(&1) pow p * x pow SUC p / &(SUC p)) /
                  (&2 pow n * &(SUC (SUC p)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_INV_MUL] THEN
      ONCE_REWRITE_TAC[AC REAL_MUL_AC
       `a * b * c * d * e * f * g * h =
        d * b * e * h * (g * c) * (f * a)`] THEN
      SIMP_TAC[REAL_MUL_LINV; REAL_POW_EQ_0; REAL_OF_NUM_EQ;
               ARITH; NOT_SUC] THEN
      REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC; GSYM REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c * d = (a * b * d) * c`] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o REDEPTH_CONV)
                    [GSYM REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs (&(SUC p) * s * inv (&2 pow n * &(SUC (SUC p)))) * &3` THEN
    ASM_SIMP_TAC[REAL_LE_LMUL; REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_INV; REAL_ABS_POW] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c * d * e =
                                     (d * a) * (b * c) * e`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&1) * &3 / &4 * &3` THEN
    CONV_TAC(RAND_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_OF_NUM_LE; ARITH] THEN
    ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_POS;
             REAL_POW_LE; REAL_ABS_POS] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
      EXISTS_TAC `&(SUC(SUC p))` THEN
      SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_OF_NUM_EQ; NOT_SUC] THEN
      REWRITE_TAC[REAL_INV_1; REAL_MUL_LID; REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
      EXISTS_TAC `&2 pow n` THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      SIMP_TAC[REAL_MUL_LINV; REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH; REAL_MUL_RID] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!y. abs(x - y) < &1 /\ abs(y) <= d - &1 ==> abs(x) <= d`) THEN
      EXISTS_TAC `&2 pow n * --x` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `inv(&2 pow n)` THEN
      SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_POW; REAL_ABS_NUM] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
      SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_POW_EQ_0; REAL_OF_NUM_EQ;
               ARITH_EQ] THEN
      REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&1 / &2` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_div; REAL_SUB_RDISTRIB; GSYM REAL_MUL_ASSOC] THEN
      SIMP_TAC[REAL_MUL_RINV; REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_LE_SUB_LADD] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
      REWRITE_TAC[GSYM REAL_LE_SUB_LADD] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
      SUBST1_TAC(SYM(REAL_INT_REDUCE_CONV `&2 pow 2`)) THEN
      MATCH_MP_TAC REAL_POW_MONO THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `--(&1) pow p * s * x pow (SUC p) / &(SUC(SUC p)) -
    &2 pow n * --(&1) pow (SUC p) * x pow (SUC(SUC p)) / &(SUC(SUC p)) =
    (--(&1) pow p * x pow (SUC p) / &(SUC(SUC p))) *
    (s - &2 pow n * --x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_pow; real_div; GSYM REAL_OF_NUM_SUC] THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB; GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_NEG_NEG; REAL_MUL_AC]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs (-- (&1) pow p * x pow SUC p / &(SUC (SUC p))) * &1` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL; REAL_ABS_POS; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_MUL_RID; real_div; REAL_ABS_MUL; REAL_ABS_POW;
              REAL_ABS_NEG; REAL_ABS_NUM; REAL_ABS_INV] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2) pow 1 * inv(&2)` THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  SIMP_TAC[REAL_ABS_POS; REAL_POW_LE;
           REAL_LE_INV_EQ; LE_0; REAL_OF_NUM_LE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2) pow (SUC p)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      REWRITE_TAC[REAL_POW_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN
      REWRITE_TAC[REAL_OF_NUM_LE; ARITH] THEN ARITH_TAC];
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; ARITH; REAL_OF_NUM_LE] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Special version of Taylor series for exponential in limited range.        *)
(* ------------------------------------------------------------------------- *)

let MCLAURIN_EXP_LE1 = prove
 (`!x n. abs(x) <= &1
         ==> ?t. abs(t) <= &1 /\
             (exp(x) = sum(0,n) (\m. x pow m / &(FACT m)) +
                       (exp(t) / &(FACT n)) * x pow n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `n:num`] MCLAURIN_EXP_LE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(x)` THEN
  ASM_REWRITE_TAC[]);;

let REAL_EXP_15 = prove
 (`exp(&1) < &5`,
  SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `inv(&2) + inv(&2)`)) THEN
  REWRITE_TAC[REAL_EXP_ADD] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(&1 + &2 * inv(&2)) * (&1 + &2 * inv(&2))` THEN
  CONV_TAC(RAND_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[REAL_EXP_POS_LE] THEN
  MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let TAYLOR_EXP_WEAK = prove
 (`abs(x) <= &1 ==>
   abs(exp(x) - sum(0,m) (\i. x pow i / &(FACT i))) < &5 * inv(&(FACT m))`,
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `m:num` o MATCH_MP MCLAURIN_EXP_LE1) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[REAL_ARITH `abs((x + y) - x) = abs(y)`] THEN
  REWRITE_TAC[real_div; REAL_ABS_MUL; GSYM REAL_MUL_ASSOC] THEN
  ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THENL
     [REWRITE_TAC[real_pow; FACT; ABS_N; REAL_INV_1; REAL_MUL_RID] THEN
      ASM_REWRITE_TAC[real_abs; REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `exp(&1)` THEN REWRITE_TAC[REAL_EXP_15] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      UNDISCH_TAC `abs(t) <= &1` THEN REAL_ARITH_TAC;
      REWRITE_TAC[POW_0; REAL_ABS_0; REAL_MUL_RZERO] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC REAL_INV_POS THEN
      REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT]];
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&5 * abs(inv(&(FACT m))) * abs(x pow m)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(exp(&1))` THEN
        ASM_REWRITE_TAC[real_abs; REAL_EXP_POS_LE; REAL_EXP_MONO_LE;
                       REAL_EXP_15] THEN
        UNDISCH_TAC `abs(t) <= &1` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_REWRITE_TAC[GSYM ABS_NZ; REAL_POW_EQ_0] THEN
        REWRITE_TAC[REAL_INV_EQ_0; REAL_OF_NUM_EQ] THEN
        MP_TAC(SPEC `m:num` FACT_LT) THEN ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LE; ARITH] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ABS_INV; ABS_N; REAL_LE_REFL] THEN
      REWRITE_TAC[REAL_ABS_POW] THEN
      MATCH_MP_TAC REAL_POW_1_LE THEN
      ASM_REWRITE_TAC[REAL_ABS_POS]]]);;

let REAL_EXP_13 = prove
 (`exp(&1) < &3`,
  MP_TAC(INST [`&1`,`x:real`; `5`,`m:num`] TAYLOR_EXP_WEAK) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_FACT_CONV) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH
   `b + e <= c ==> abs(a - b) < e ==> a < c`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let TAYLOR_EXP = prove
 (`abs(x) <= &1 ==>
   abs(exp(x) - sum(0,m) (\i. x pow i / &(FACT i))) < &3 * inv(&(FACT m))`,
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `m:num` o MATCH_MP MCLAURIN_EXP_LE1) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[REAL_ARITH `abs((x + y) - x) = abs(y)`] THEN
  REWRITE_TAC[real_div; REAL_ABS_MUL; GSYM REAL_MUL_ASSOC] THEN
  ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THENL
     [REWRITE_TAC[real_pow; FACT; ABS_N; REAL_INV_1; REAL_MUL_RID] THEN
      ASM_REWRITE_TAC[real_abs; REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `exp(&1)` THEN REWRITE_TAC[REAL_EXP_13] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      UNDISCH_TAC `abs(t) <= &1` THEN REAL_ARITH_TAC;
      REWRITE_TAC[POW_0; REAL_ABS_0; REAL_MUL_RZERO] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC REAL_INV_POS THEN
      REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT]];
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&3 * abs(inv(&(FACT m))) * abs(x pow m)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL_IMP THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(exp(&1))` THEN
        ASM_REWRITE_TAC[real_abs; REAL_EXP_POS_LE; REAL_EXP_MONO_LE;
                        REAL_EXP_13] THEN
        UNDISCH_TAC `abs(t) <= &1` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_REWRITE_TAC[GSYM ABS_NZ; REAL_POW_EQ_0] THEN
        REWRITE_TAC[REAL_INV_EQ_0; REAL_OF_NUM_EQ] THEN
        MP_TAC(SPEC `m:num` FACT_LT) THEN ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LE; ARITH] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ABS_INV; ABS_N; REAL_LE_REFL] THEN
      REWRITE_TAC[REAL_ABS_POW] THEN
      MATCH_MP_TAC REAL_POW_1_LE THEN
      ASM_REWRITE_TAC[REAL_ABS_POS]]]);;

let TAYLOR_LN = prove
 (`&0 <= x /\ x <= inv(&2 pow k) ==>
   abs(ln(&1 + x) - sum(0,m) (\i. --(&1) pow i * x pow SUC i / &(SUC i)))
   < inv(&2 pow (k * SUC m) * &(SUC m))`,
  let lemma = INST [`1`,`k:num`] (SYM(SPEC_ALL SUM_REINDEX)) in
  STRIP_TAC THEN
  UNDISCH_TAC `&0 <= x` THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THENL
   [ALL_TAC;
    REWRITE_TAC[real_pow; REAL_MUL_LZERO; REAL_MUL_RZERO; real_div] THEN
    REWRITE_TAC[SUM_0; REAL_ADD_RID; REAL_SUB_LZERO; LN_1] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_0] THEN
    SIMP_TAC[REAL_LT_INV_EQ; REAL_LT_MUL; REAL_POW_LT; REAL_OF_NUM_LT;
             LT_0; ARITH]] THEN
  SUBGOAL_THEN `!i. --(&1) pow i = --(&1) pow (SUC(SUC i))`
   (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[real_pow; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    REWRITE_TAC[REAL_MUL_LID]; ALL_TAC] THEN
  REWRITE_TAC[ADD1; lemma] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  ONCE_REWRITE_TAC[SUM_DIFF] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
  REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO] THEN
  REWRITE_TAC[GSYM ADD1] THEN
  MP_TAC(SPECL [`x:real`; `SUC m`] MCLAURIN_LN_POS) THEN
  ASM_REWRITE_TAC[LT_0] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[GSYM ADD1] THEN
  REWRITE_TAC[GSYM real_div] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_ARITH `(a + b) - a = b`] THEN
  REWRITE_TAC[real_div; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_POW] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_POW_ONE] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
   `inv (&2 pow (k * SUC m)) * inv (&(SUC m)) * inv(abs(&1 + t) pow SUC m)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_POS; REAL_ABS_POS;
             REAL_POW_LE] THEN
    REWRITE_TAC[GSYM REAL_POW_INV] THEN
    REWRITE_TAC[GSYM REAL_POW_POW] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_SIMP_TAC[REAL_POW_INV; real_abs; REAL_LT_IMP_LE];
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
    SIMP_TAC[REAL_LT_MUL; REAL_LT_INV_EQ; REAL_OF_NUM_LT; LT_0; REAL_POW_LT;
             ARITH] THEN
    REWRITE_TAC[GSYM REAL_POW_INV; GSYM REAL_ABS_INV] THEN
    SUBGOAL_THEN `abs(inv(&1 + t)) < &1` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_INV] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_1] THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN
      UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
      SUBST1_TAC(SYM(SPEC `SUC m` REAL_POW_ONE)) THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN
      ASM_REWRITE_TAC[REAL_POW_ONE; NOT_SUC; REAL_ABS_POS]]]);;

(* ------------------------------------------------------------------------- *)
(* Leading from the summation to the actual function.                        *)
(* ------------------------------------------------------------------------- *)

let APPROX_LEMMA1 = prove
 (`abs(f(x:real) - sum(0,m) (\i. P i x)) < inv(&2 pow (n + 2)) /\
   abs(u - &2 pow (n + e + 2) * sum(0,m) (\i. P i x)) <= &k * &m /\
   &k * &m <= &2 pow e /\
   abs(s * &2 pow (e + 2) - u) <= &2 pow (e + 1)
   ==> abs(s - &2 pow n * f(x)) < &1`,
  STRIP_TAC THEN MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
  EXISTS_TAC `&2 pow (n + e + 2)` THEN
  REWRITE_TAC[REAL_LT_POW2] THEN
  REWRITE_TAC[REAL_ABS_LEMMA; REAL_SUB_LDISTRIB; REAL_MUL_RID] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN (MATCH_MP_TAC o GEN_ALL)
   (REAL_ARITH `abs(a - b) + abs(b - c) < d ==> abs(a - c) < d`) THEN
  EXISTS_TAC `&2 pow n * u` THEN
  CONV_TAC(funpow 4 RAND_CONV num_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES; real_pow; REAL_MUL_2] THEN
  MATCH_MP_TAC REAL_LET_ADD2 THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_POW_ADD] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[GSYM REAL_ABS_LEMMA] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_LT_POW2];
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_SUB_LDISTRIB] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_POW_ADD] THEN
    REWRITE_TAC[GSYM REAL_ABS_LEMMA] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN REWRITE_TAC[REAL_LT_POW2] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN (MATCH_MP_TAC o GEN_ALL)
      (REAL_ARITH `abs(a - b) + abs(b - c) < d ==> abs(a - c) < d`) THEN
    EXISTS_TAC
      `&2 pow (n + e + 2) * sum(0,m) (\i. P i (x:real))` THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_POW_ADD] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_POW_1; REAL_MUL_2] THEN
    MATCH_MP_TAC REAL_LET_ADD2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&k * &m` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_ABS_LEMMA] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
      ONCE_REWRITE_TAC[REAL_POW_ADD] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN
      REWRITE_TAC[REAL_LT_POW2] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
      EXISTS_TAC `inv(&2 pow (n + 2))` THEN
      REWRITE_TAC[REAL_LT_INV_EQ; REAL_LT_POW2] THEN
      REWRITE_TAC[REAL_MUL_RID; REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
      SUBGOAL_THEN `inv(&2 pow (n + 2)) * &2 pow (n + 2) = &1`
      (fun th -> ASM_REWRITE_TAC[th; REAL_MUL_LID]) THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[REAL_POW_EQ_0] THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN DISJ1_TAC THEN REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Approximation theorems.                                                   *)
(* ------------------------------------------------------------------------- *)

let APPROX_EXP = prove
 (`(n + e + 2 = p) /\
   &3 * &2 pow (n + 2) <= &(FACT m) /\
   &2 * &m <= &2 pow e /\
   abs(x) <= &1 /\
   abs(s - &2 pow p * x) < &1 /\
   (t(0) = &2 pow p) /\
   (!k. SUC k < m ==>
                &2 * abs(t(SUC k) * &2 pow p * &(SUC k) - s * t(k))
                <= &2 pow p * &(SUC k)) /\
   abs(u * &2 pow (e + 2) - sum(0,m) t) <= &2 pow (e + 1)
   ==> abs(u - &2 pow n * exp(x)) < &1`,
  STRIP_TAC THEN MATCH_MP_TAC(GEN_ALL APPROX_LEMMA1) THEN
  MAP_EVERY EXISTS_TAC
   [`\i x. x pow i / &(FACT i)`; `2`; `m:num`; `sum(0,m) t`; `e:num`] THEN
  ASM_REWRITE_TAC[BETA_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&3 * inv(&(FACT m))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TAYLOR_EXP THEN ASM_REWRITE_TAC[];
      SUBST1_TAC(SYM(SPEC `&3` REAL_INV_INV)) THEN
      REWRITE_TAC[GSYM REAL_INV_MUL] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_LT_POW2] THEN
      MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&3` THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      REWRITE_TAC[MATCH_MP REAL_MUL_RINV (REAL_ARITH `~(&3 = &0)`)] THEN
      ASM_REWRITE_TAC[REAL_MUL_LID] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC STEPS_EXP THEN ASM_REWRITE_TAC[]]);;

let APPROX_LN = prove
 (`~(k = 0) /\
   (n + e + 2 = p) /\
   &2 pow (n + 2) <= &2 pow (k * SUC m) * &(SUC m) /\
   &3 * &m <= &2 pow e /\
   (&0 <= x /\ x <= inv(&2 pow k)) /\
   abs(s - &2 pow p * --x) < &1 /\
   (t(0) = --s) /\
   (!k. SUC k < m ==>
                &2 * abs(t(SUC k) * &2 pow p * &(SUC(SUC k)) -
                         &(SUC k) * s * t(k))
                <= &2 pow p * &(SUC(SUC k))) /\
   abs(u * &2 pow (e + 2) - sum(0,m) t) <= &2 pow (e + 1)
   ==> abs(u - &2 pow n * ln(&1 + x)) < &1`,
  STRIP_TAC THEN
  (MATCH_MP_TAC o GEN_ALL o BETA_RULE)
    (INST [`\x. ln(&1 + x):real`,`f:real->real`] APPROX_LEMMA1) THEN
  MAP_EVERY EXISTS_TAC
   [`\i x. (--(&1)) pow i * x pow (SUC i) / &(SUC i)`;
    `3`; `m:num`; `sum(0,m) t`; `e:num`] THEN
  ASM_REWRITE_TAC[BETA_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `inv(&2 pow (k * SUC m) * &(SUC m))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC TAYLOR_LN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_LT_POW2]];
    MATCH_MP_TAC STEPS_LN THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `2 <= (n + e + 2)` MP_TAC THENL
     [REWRITE_TAC[ADD_ASSOC] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[LE_ADD];
      SUBGOAL_THEN `abs(x) <= &1 / &2` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[real_abs] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(&2 pow k)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_LT_POW2] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN
      REWRITE_TAC[REAL_OF_NUM_LE; ARITH] THEN
      UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Eliminate trivial definitions.                                            *)
(* ------------------------------------------------------------------------- *)

let ELIMINATE_DEF =
  let x_tm = `x:num`
  and a_tm = `&0`
  and sconv = REWRITE_CONV[ARITH] in
  fun tdefs th ->
  if tdefs = [] then th else
  let ctm =
    itlist (fun tm acc ->
              let l,r = (rand F_F I) (dest_eq tm) in
              mk_cond(mk_eq(x_tm,l),r,acc)) tdefs a_tm in
  let atm = mk_abs(x_tm,ctm) in
  let ttm = rator(lhs(hd tdefs)) in
  let tth = ASSUME(mk_eq(ttm,atm)) in
  let ths = map
    (EQT_ELIM o CONV_RULE(RAND_CONV sconv) o SUBS_CONV[tth]) tdefs in
  let dth = PROVE_HYP (end_itlist CONJ ths) th in
  MP (INST [atm,ttm] (DISCH_ALL dth)) (REFL atm);;

(* ------------------------------------------------------------------------- *)
(* Overall conversion.                                                       *)
(* ------------------------------------------------------------------------- *)

let realcalc_cache = ref [];;

let REALCALC_CONV,thm_eval,raw_eval,thm_wrap =
  let a_tm = `a:real` and n_tm = `n:num` and n'_tm = `n':num`

  and m_tm = `m:num`

  and b_tm = `b:real` and e_tm = `e:num`
  and c_tm = `c:real`

  and neg_tm = `(--)`
  and abs_tm = `abs`
  and inv_tm = `inv`
  and sqrt_tm = `sqrt`
  and add_tm = `(+)`
  and mul_tm = `(*)`
  and sub_tm = `(-)`
  and exp_tm = `exp:real->real`
  and ln_tm = `ln:real->real`
  and add1_tm = `(+) (&1)`
  and pow2_tm = `(pow) (&2)`
  and one_tm = `&1`
  and lt_tm = `(<)` in

  let INTEGER_PROVE =
    EQT_ELIM o REWRITE_CONV[REAL_EQ_NEG2; GSYM EXISTS_REFL;
                            EXISTS_OR_THM; REAL_OF_NUM_EQ] in

  let ndiv x y =
    let q = quo_num x y in
    let r = x -/ (q */ y) in
    if le_num (abs_num(Num.num_of_int 2 */ r)) (abs_num y) then q
    else if le_num (abs_num(Num.num_of_int 2 */ (r -/ y))) (abs_num y) then q +/ Num.num_of_int 1
    else if le_num (abs_num(Num.num_of_int 2 */ (r +/ y))) (abs_num y) then q -/ Num.num_of_int 1
    else let s = (string_of_num x)^" and "^(string_of_num y) in
         failwith ("ndiv: "^s) in

  let raw_wrap (f:num->num) = (ref(Num.num_of_int(-1),Num.num_of_int 0),f) in

  let raw_eval(r,(f:num->num)) n =
    let (n0,y0) = !r in
    if le_num n n0 then ndiv y0 (power_num (Num.num_of_int 2) (n0 -/ n))
    else let y = f n in (r := (n,y); y) in

  let thm_eval =
    let SUC_tm = `SUC`
    and mk_add = mk_binop `(+):num->num->num` in
    fun (r,(f:num->thm)) n ->
      let (n0,y0th) = !r in
      if le_num n n0 then
        if n =/ n0 then y0th else
          let th1 = NUM_SUC_CONV
            (mk_comb(SUC_tm,mk_numeral(n0 -/ (n +/ Num.num_of_int 1)))) in
          let th2 = MATCH_MP REALCALC_DOWNGRADE th1 in
          let th3 = NUM_ADD_CONV(mk_add(mk_numeral(n)) (mk_numeral(n0 -/ n))) in
          let th4 = MATCH_MP th2 th3 in
          let th5 = MATCH_MP th4 y0th in
          let tm5 = fst(dest_imp(concl th5)) in
          let tm5a,tm5b = dest_comb tm5 in
          let th6 = REAL_INT_POW_CONV tm5b in
          let tm5c = rand(rand tm5a) in
          let tm5d,tm5e = dest_comb tm5c in
          let tm5f,tm5g = dest_comb(rand tm5d) in
          let tm5h = rand(rand tm5f) in
          let bin = mk_realintconst
           (ndiv (dest_realintconst tm5e) (power_num (Num.num_of_int 2) (dest_numeral tm5h))) in
          let th7 = AP_TERM (rator(rand tm5f)) th1 in
          let th8 = GEN_REWRITE_RULE LAND_CONV [CONJUNCT2 real_pow] th7 in
          let th9 = SYM(GEN_REWRITE_RULE (LAND_CONV o RAND_CONV) [th6] th8) in
          let th10 = TRANS th9 (REAL_INT_MUL_CONV (rand(concl th9))) in
          let th11 = AP_THM (AP_TERM (rator tm5f) th10) bin in
          let th12 = TRANS th11 (REAL_INT_MUL_CONV (rand(concl th11))) in
          let th13 = AP_THM (AP_TERM (rator tm5d) th12) tm5e in
          let th14 = TRANS th13 (REAL_INT_SUB_CONV (rand(concl th13))) in
          let th15 = AP_TERM (rator(rand tm5a)) th14 in
          let th16 = TRANS th15 (REAL_INT_ABS_CONV (rand(concl th15))) in
          let th17 = MK_COMB(AP_TERM (rator tm5a) th16,th6) in
          let th18 = TRANS th17 (REAL_INT_LE_CONV (rand(concl th17))) in
          MATCH_MP th5 (EQT_ELIM th18)
      else let yth = f n in (r := (n,yth); yth) in

  let thm_wrap (f:num->thm) = (ref(Num.num_of_int(-1),TRUTH),f) in

  let find_msd =
    let rec find_msd n f =
      if Num.num_of_int 1 </ abs_num(raw_eval f n) then n
      else find_msd (n +/ Num.num_of_int 1) f in
    find_msd (Num.num_of_int 0) in

  let find_acc =
    let rec find_msd n f =
      if Num.num_of_int 32 </ abs_num(raw_eval f n) then n
      else find_msd (n +/ Num.num_of_int 1) f in
    find_msd (Num.num_of_int 0) in

  let find_ubound f =
    let k = find_acc f in
    let a = abs_num(raw_eval f k) in
    k -/ log2 (a +/ Num.num_of_int 1) in

  let REALCALC_EXP_CONV =
    let t_tm = `t:num->real`
    and n_tm = `n:num`
    and m_tm = `m:num`
    and e_tm = `e:num`
    and p_tm = `p:num`
    and s_tm = `s:real`
    and u_tm = `u:real`
    and x_tm = `x:real` in
    let rec calculate_m acc i r =
      if acc >=/ r then i else
      let i' = i +/ Num.num_of_int 1 in
      calculate_m (i' */ acc) i' r in
    let calculate_exp_sequence =
      let rec calculate_exp_sequence p2 s i =
        if i </ Num.num_of_int 0 then []
        else if i =/ Num.num_of_int 0 then [p2] else
        let acc = calculate_exp_sequence p2 s (i -/ Num.num_of_int 1) in
        let t = hd acc in
        let t' = ndiv (s */ t) (p2 */ i) in
        t'::acc in
      fun p s m -> let p2 = power_num (Num.num_of_int 2) p in
                   rev(calculate_exp_sequence p2 s (m -/ Num.num_of_int 1)) in
    let pth = prove
     (`abs(x) <= &1 ==>
       abs(s - &2 pow p * x) < &1 ==>
       (n + e + 2 = p) /\
       &3 * &2 pow (n + 2) <= &(FACT m) /\
       &2 * &m <= &2 pow e /\
       (t(0) = &2 pow p) /\
       (!k. SUC k < m ==>
                    &2 * abs(t(SUC k) * &2 pow p * &(SUC k) - s * t(k))
                    <= &2 pow p * &(SUC k)) /\
       abs(u * &2 pow (e + 2) - sum(0,m) t) <= &2 pow (e + 1)
       ==> abs(u - &2 pow n * exp(x)) < &1`,
      REPEAT STRIP_TAC THEN MATCH_MP_TAC APPROX_EXP THEN
      ASM_REWRITE_TAC[]) in
    let LEFT_ZERO_RULE =
      ONCE_REWRITE_RULE[prove(`0 + n = n`,REWRITE_TAC[ADD_CLAUSES])] in
    fun (fn1,fn2) ->
      let raw_fn n =
        let m = calculate_m (Num.num_of_int 1) (Num.num_of_int 0)
                  (Num.num_of_int 3 */ (power_num (Num.num_of_int 2) (n +/ Num.num_of_int 2))) in
        let e = log2 (Num.num_of_int 2 */ m) in
        let p = n +/ e +/ Num.num_of_int 2 in
        let s = raw_eval fn1 p in
        let seq = calculate_exp_sequence p s m in
        let u0 = itlist (+/) seq (Num.num_of_int 0) in
        ndiv u0 (power_num (Num.num_of_int 2) (e +/ Num.num_of_int 2))
      and thm_fn n =
        let m = calculate_m (Num.num_of_int 1) (Num.num_of_int 0)
                  (Num.num_of_int 3 */ (power_num (Num.num_of_int 2) (n +/ Num.num_of_int 2))) in
        let e = log2 (Num.num_of_int 2 */ m) in
        let p = n +/ e +/ Num.num_of_int 2 in
        let sth = thm_eval fn2 p in
        let tm1 = rand(lhand(concl sth)) in
        let s_num = lhand tm1 in
        let x_num = rand(rand tm1) in
        let s = dest_realintconst s_num in
        let seq = calculate_exp_sequence p s m in
        let u0 = itlist (+/) seq (Num.num_of_int 0) in
        let u = ndiv u0 (power_num (Num.num_of_int 2) (e +/ Num.num_of_int 2)) in
        let m_num = mk_numeral m
        and n_num = mk_numeral n
        and e_num = mk_numeral e
        and p_num = mk_numeral p
        and u_num = mk_realintconst u in
        let tdefs = map2 (fun a b -> mk_eq(mk_comb(t_tm,mk_small_numeral a),
                             mk_realintconst b)) (0--(length seq - 1)) seq in
        let p2th = REAL_INT_POW_CONV (mk_comb(pow2_tm,p_num)) in
        let th0 = INST [m_num,m_tm; n_num,n_tm; e_num,e_tm;
                        x_num,x_tm; p_num,p_tm; s_num,s_tm; u_num,u_tm] pth in
        let th0' = MP th0 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th0)))) in
        let th1 = MP th0' sth in
        let th2 = CONV_RULE (ONCE_DEPTH_CONV EXPAND_RANGE_CONV) th1 in
        let th3 = LEFT_ZERO_RULE
         (CONV_RULE (ONCE_DEPTH_CONV REAL_SUM_CONV) th2) in
        let ths = try CONJUNCTS(ASSUME(list_mk_conj tdefs))
                  with Failure _ -> [] in
        let th4 = SUBS (p2th::ths) th3 in
        let th5 = CONV_RULE (LAND_CONV
          (DEPTH_CONV NUM_ADD_CONV THENC
           ONCE_DEPTH_CONV NUM_FACT_CONV THENC
           REAL_INT_REDUCE_CONV)) th4 in
        MP (ELIMINATE_DEF tdefs th5) TRUTH in
     raw_wrap raw_fn,thm_wrap thm_fn in

  let REALCALC_LN_CONV =
    let t_tm = `t:num->real`
    and n_tm = `n:num`
    and m_tm = `m:num`
    and e_tm = `e:num`
    and p_tm = `p:num`
    and s_tm = `s:real`
    and u_tm = `u:real`
    and k_tm = `k:num`
    and x_tm = `x:real` in
    let rec calculate_m acc k2 m r =
      if acc */ (m +/ Num.num_of_int 1) >=/ r then m else
      calculate_m (k2 */ acc) k2 (m +/ Num.num_of_int 1) r in
    let calculate_ln_sequence =
      let rec calculate_ln_sequence p2 s i =
        if i </ Num.num_of_int 0 then []
        else if i =/ Num.num_of_int 0 then [s] else
        let acc = calculate_ln_sequence p2 s (i -/ Num.num_of_int 1) in
        let t = hd acc in
        let t' = ndiv (Num.num_of_int(-1) */ s */ t */ i) (p2 */ (i +/ Num.num_of_int 1)) in
        t'::acc in
      fun p s m -> let p2 = power_num (Num.num_of_int 2) p in
                   rev(calculate_ln_sequence p2 s (m -/ Num.num_of_int 1)) in
    let pth = prove
     (`&0 <= x /\ x <= inv(&2 pow k) ==>
       abs(s - &2 pow p * x) < &1 ==>
       ~(k = 0) /\
       (n + e + 2 = p) /\
       &2 pow (n + 2) <= &2 pow (k * SUC m) * &(SUC m) /\
       &3 * &m <= &2 pow e /\
       (t(0) = s) /\
       (!k. SUC k < m ==>
                    &2 * abs(t(SUC k) * &2 pow p * &(SUC(SUC k)) -
                             &(SUC k) * --s * t(k))
                    <= &2 pow p * &(SUC(SUC k))) /\
       abs(u * &2 pow (e + 2) - sum(0,m) t) <= &2 pow (e + 1)
       ==> abs(u - &2 pow n * ln(&1 + x)) < &1`,
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(INST [`--s`,`s:real`] APPROX_LN) THEN
      ASM_REWRITE_TAC[REAL_NEG_NEG] THEN
      REWRITE_TAC[REAL_MUL_RNEG] THEN
      REWRITE_TAC[REAL_ARITH `abs(--a - --b) = abs(a - b)`] THEN
      ASM_REWRITE_TAC[]) in
    let LEFT_ZERO_RULE =
      ONCE_REWRITE_RULE[prove(`0 + n = n`,REWRITE_TAC[ADD_CLAUSES])] in
    let pow2_tm = `(pow) (&2)` in
    let default_tdefs = [`t 0 = &0`] in
    fun (fn1,fn2) ->
      let raw_fn n =
        let k = find_ubound fn1 in
        if k </ Num.num_of_int 1 then failwith "ln of number not provably <= 1/2" else
        let k2 = power_num (Num.num_of_int 2) k in
        let m = calculate_m k2 k2 (Num.num_of_int 0) (power_num (Num.num_of_int 2) (n +/ Num.num_of_int 2)) in
        let e = log2 (Num.num_of_int 3 */ m) in
        let p = n +/ e +/ Num.num_of_int 2 in
        let s = raw_eval fn1 p in
        let seq = calculate_ln_sequence p s m in
        let u0 = itlist (+/) seq (Num.num_of_int 0) in
        ndiv u0 (power_num (Num.num_of_int 2) (e +/ Num.num_of_int 2))
      and thm_fn n =
        let k = find_ubound fn1 in
        if k </ Num.num_of_int 1 then failwith "ln of number not provably <= 1/2" else
        let k2 = power_num (Num.num_of_int 2) k in
        let m = calculate_m k2 k2 (Num.num_of_int 0) (power_num (Num.num_of_int 2) (n +/ Num.num_of_int 2)) in
        let e = log2 (Num.num_of_int 3 */ m) in
        let p = n +/ e +/ Num.num_of_int 2 in
        let sth = thm_eval fn2 p in
        let tm1 = rand(lhand(concl sth)) in
        let s_num = lhand tm1 in
        let x_num = rand(rand tm1) in
        let s = dest_realintconst s_num in
        let seq = calculate_ln_sequence p s m in
        let u0 = itlist (+/) seq (Num.num_of_int 0) in
        let u = ndiv u0 (power_num (Num.num_of_int 2) (e +/ Num.num_of_int 2)) in
        let m_num = mk_numeral m
        and n_num = mk_numeral n
        and e_num = mk_numeral e
        and p_num = mk_numeral p
        and k_num = mk_numeral k
        and u_num = mk_realintconst u in
        let tdefs0 = map2 (fun a b -> mk_eq(mk_comb(t_tm,mk_small_numeral a),
                             mk_realintconst b)) (0--(length seq - 1)) seq in
        let tdefs = if tdefs0 = [] then default_tdefs else tdefs0 in
        let p2th = REAL_INT_POW_CONV (mk_comb(pow2_tm,p_num)) in
        let th0 = INST [m_num,m_tm; n_num,n_tm; e_num,e_tm; k_num,k_tm;
                        x_num,x_tm; p_num,p_tm; s_num,s_tm; u_num,u_tm] pth in
        let th0' = MP th0 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th0)))) in
        let th1 = MP th0' sth in
        let th2 = CONV_RULE (ONCE_DEPTH_CONV EXPAND_RANGE_CONV) th1 in
        let th3 = LEFT_ZERO_RULE
                   (CONV_RULE (ONCE_DEPTH_CONV REAL_SUM_CONV) th2) in
        let ths = try CONJUNCTS(ASSUME(list_mk_conj tdefs))
                  with Failure _ -> [] in
        let th4 = SUBS (p2th::ths) th3 in
        let th5 = CONV_RULE (LAND_CONV
          (NUM_REDUCE_CONV THENC
           REAL_INT_REDUCE_CONV)) th4 in
        MP (ELIMINATE_DEF tdefs th5) TRUTH in
     raw_wrap raw_fn,thm_wrap thm_fn in

  let REALCALC_SQRT_CONV =
    let num_sqrt =
      let rec isolate_sqrt (a,b) y =
      if abs_num(a -/ b) <=/ Num.num_of_int 1 then
        if abs_num(a */ a -/ y) <=/ a then a else b
      else
        let c = quo_num (a +/ b) (Num.num_of_int 2) in
        if c */ c <=/ y then isolate_sqrt (c,b) y
        else isolate_sqrt (a,c) y in
      fun n -> isolate_sqrt (Num.num_of_int 0,n) n in
    let MATCH_pth = MATCH_MP REALCALC_SQRT in
    let b_tm = `b:real` in
    let PROVE_1_LE_SQRT =
      let pth = prove
       (`&1 <= x ==> &1 <= sqrt(x)`,
        DISCH_THEN(fun th ->
          ASSUME_TAC(MATCH_MP (REAL_ARITH `&1 <= x ==> &0 <= x`) th) THEN
          MP_TAC th) THEN
        CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[REAL_NOT_LE] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `x = sqrt(x) pow 2` SUBST1_TAC THENL
         [CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[SQRT_POW2];
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          REWRITE_TAC[POW_2] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
          ASM_SIMP_TAC[SQRT_POS_LE]]) in
      let tac = REPEAT(MATCH_MP_TAC pth) THEN CONV_TAC REAL_RAT_LE_CONV in
      fun tm -> try prove(tm,tac)
                with Failure _ -> failwith "Need root body >= &1" in
    fun (fn1,fn2) ->
      let raw_fn n =
        num_sqrt(power_num (Num.num_of_int 2) n */ raw_eval fn1 n)
      and thm_fn n =
        let th1 = MATCH_pth(thm_eval fn2 n) in
        let th2 = MP th1 (PROVE_1_LE_SQRT(lhand(concl th1))) in
        let th3 = CONV_RULE(funpow 2 LAND_CONV
          (funpow 2 RAND_CONV REAL_RAT_REDUCE_CONV)) th2 in
        let k = dest_realintconst(rand(rand(lhand(lhand(concl th3))))) in
        let th4 = INST [mk_realintconst(num_sqrt k),b_tm] th3 in
        MP th4 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th4)))) in
     raw_wrap raw_fn,thm_wrap thm_fn in

  let rec REALCALC_CONV tm =
    try assoc tm (!realcalc_cache) with Failure _ ->
    if is_ratconst tm then
      let x = rat_of_term tm in
      let raw_fn acc =
        floor_num ((power_num (Num.num_of_int 2) acc) */ x)
      and thm_fn acc =
        let a = floor_num ((power_num (Num.num_of_int 2) acc) */ x) in
        let atm = mk_realintconst a in
        let rtm = mk_comb(mk_comb(mul_tm,mk_comb(pow2_tm,mk_numeral acc)),tm) in
        let btm = mk_comb(abs_tm,mk_comb(mk_comb(sub_tm,atm),rtm)) in
        let ftm = mk_comb(mk_comb(lt_tm,btm),one_tm) in
        EQT_ELIM(REAL_RAT_REDUCE_CONV ftm) in
      raw_wrap raw_fn,thm_wrap thm_fn else
    let lop,r = dest_comb tm in
    if lop = neg_tm then
      let rfn,tfn = REALCALC_CONV r in
      let raw_fn acc =
        minus_num (raw_eval rfn acc)
      and thm_fn acc =
        let th1 = thm_eval tfn acc in
        let th2 = MATCH_MP REALCALC_NEG th1 in
        try EQ_MP (LAND_CONV(RAND_CONV(LAND_CONV REAL_INT_NEG_CONV)) (concl th2))
                  th2
        with Failure _ -> th2 in
      raw_wrap raw_fn,thm_wrap thm_fn
    else if lop = abs_tm then
      let rfn,tfn = REALCALC_CONV r in
      let raw_fn acc =
        abs_num (raw_eval rfn acc)
      and thm_fn acc =
        let th1 = thm_eval tfn acc in
        let th2 = MATCH_MP REALCALC_ABS th1 in
        CONV_RULE (LAND_CONV(RAND_CONV(LAND_CONV REAL_INT_ABS_CONV))) th2 in
      raw_wrap raw_fn,thm_wrap thm_fn
    else if lop = sqrt_tm then
      REALCALC_SQRT_CONV(REALCALC_CONV r)
    else if lop = inv_tm then
      let rfn,tfn = REALCALC_CONV r in
      let x0 = raw_eval rfn (Num.num_of_int 0) in
      let ax0 = abs_num x0 in
      let r = log2(ax0) -/ Num.num_of_int 1 in
      let get_ek(acc) =
        if r < Num.num_of_int 0 then
          let p = find_msd rfn in
          let e = acc +/ p +/ Num.num_of_int 1 in
          let k = e +/ p in e,k
        else
          let k = let k0 = acc +/ Num.num_of_int 1 -/ (Num.num_of_int 2 */ r) in
                  if k0 </ Num.num_of_int 0 then Num.num_of_int 0 else k0 in
          let e = r +/ k in e,k in
      let raw_fn acc =
        let _,k = get_ek(acc) in
        let nk2 = power_num (Num.num_of_int 2) (acc +/ k) in
        ndiv nk2 (raw_eval rfn k) in
      let thm_fn acc =
        let e,k = get_ek(acc) in
        let nk2 = power_num (Num.num_of_int 2) (acc +/ k) in
        let th1 = thm_eval tfn k in
        let atm = lhand(rand(lhand(concl th1))) in
        let a = dest_realintconst atm in
        let b = ndiv nk2 a in
        let btm = mk_realintconst b in
        let etm = mk_numeral e in
        let ntm = mk_numeral acc in
        let th2 = MATCH_MP REALCALC_INV th1 in
        let th3 = INST [btm,b_tm; etm,e_tm; ntm,n_tm] th2 in
        let th4 = MP th3 (INTEGER_PROVE(lhand(concl th3))) in
        let th5 = MP th4 (INTEGER_PROVE(lhand(concl th4))) in
        let th6 = MP th5 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th5)))) in
        let th7 = MP th6 (EQT_ELIM(REAL_INT_REDUCE_CONV(lhand(concl th6)))) in
        MP th7
         (EQT_ELIM(((LAND_CONV (funpow 4 RAND_CONV NUM_ADD_CONV) THENC
                    REAL_INT_REDUCE_CONV) (lhand(concl th7))))) in
      raw_wrap raw_fn,thm_wrap thm_fn
    else if lop = exp_tm then
      let rfn,tfn = REALCALC_CONV r in
      REALCALC_EXP_CONV (rfn,tfn)
    else if lop = ln_tm then
      let r1,r2 = dest_comb r in
      if r1 = add1_tm then
        let rfn,tfn = REALCALC_CONV r2 in
        REALCALC_LN_CONV (rfn,tfn)
      else
        failwith "Can only do logs like ln(&1 + x) for small rational x" else
    let op,l = dest_comb lop in
    if op = add_tm then
      let rfn1,tfn1 = REALCALC_CONV l
      and rfn2,tfn2 = REALCALC_CONV r in
      let raw_fn acc =
        let acc' = acc +/ Num.num_of_int 2 in
        ndiv (raw_eval rfn1 acc' +/ raw_eval rfn2 acc') (Num.num_of_int 4)
      and thm_fn acc =
        let acc' = acc +/ Num.num_of_int 2 in
        let th1 = INST [mk_numeral acc,n_tm] REALCALC_ADD in
        let th2 = MATCH_MP th1 (NUM_ADD_CONV (lhand(lhand(concl th1)))) in
        let th3 = thm_eval tfn1 acc' in
        let th4 = MATCH_MP th2 th3 in
        let th5 = thm_eval tfn2 acc' in
        let th6 = MATCH_MP th4 th5 in
        let n1 = dest_realintconst(lhand(rand(lhand(concl th3))))
        and n2 = dest_realintconst(lhand(rand(lhand(concl th5)))) in
        let ci = mk_realintconst(ndiv (n1 +/ n2) (Num.num_of_int 4)) in
        let th7 = INST [ci,c_tm] th6 in
        let th8 = EQT_ELIM(REAL_INT_REDUCE_CONV(lhand(concl th7))) in
        MP th7 th8 in
      raw_wrap raw_fn,thm_wrap thm_fn
    else if op = mul_tm then
      let rfn1,tfn1 = REALCALC_CONV l
      and rfn2,tfn2 = REALCALC_CONV r in
      let get_kl(acc) =
        let n' = acc +/ Num.num_of_int 2 in
        let r = quo_num n' (Num.num_of_int 2) in
        let s = n' -/ r in
        let p = log2(abs_num(raw_eval rfn1 r))
        and q = log2(abs_num(raw_eval rfn2 s)) in
        let k = q +/ r +/ Num.num_of_int 1
        and l = p +/ s +/ Num.num_of_int 1 in
        if p =/ Num.num_of_int 0 && q = Num.num_of_int 0 then
          if k </ l then k +/ Num.num_of_int 1,l else k,l +/ Num.num_of_int 1
        else k,l in
      let raw_fn acc =
        let k,l = get_kl acc in
        let m = (k +/ l) -/ acc in
        ndiv (raw_eval rfn1 k */ raw_eval rfn2 l) (power_num (Num.num_of_int 2) m) in
      let thm_fn acc =
        let k,l = get_kl acc in
        let m = (k +/ l) -/ acc in
        let th1a = thm_eval tfn1 k
        and th1b = thm_eval tfn2 l in
        let a = dest_realintconst(lhand(rand(lhand(concl th1a))))
        and b = dest_realintconst(lhand(rand(lhand(concl th1b)))) in
        let c = ndiv (a */ b) (power_num (Num.num_of_int 2) m) in
        let ntm = mk_numeral acc
        and mtm = mk_numeral m
        and ctm = mk_realintconst c in
        let th1 = MATCH_MP REALCALC_MUL th1a in
        let th2 = MATCH_MP th1 th1b in
        let th3 = INST [ntm,n_tm; mtm,m_tm; ctm,c_tm] th2 in
        let th4 = MP th3 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th3)))) in
        let th5 = MP th4 (EQT_ELIM(REAL_INT_REDUCE_CONV(lhand(concl th4)))) in
        MP th5 (EQT_ELIM(REAL_INT_REDUCE_CONV(lhand(concl th5)))) in
      raw_wrap raw_fn,thm_wrap thm_fn
    else failwith "No other operators work yet, sorry!" in
  REALCALC_CONV,thm_eval,raw_eval,thm_wrap;;

(* ------------------------------------------------------------------------- *)
(* Apply some conversion before doing approximation.                         *)
(* ------------------------------------------------------------------------- *)

let REALCALC_PRECONV conv tm =
  let th = conv tm in
  let rfn,tfn = REALCALC_CONV (rand(concl th)) in
  rfn,
  thm_wrap(fun n ->
        let th1 = thm_eval tfn n in
        GEN_REWRITE_RULE (LAND_CONV o funpow 3 RAND_CONV) [SYM th] th1);;

(* ------------------------------------------------------------------------- *)
(* Calculate ordering relation between two expressions.                      *)
(* ------------------------------------------------------------------------- *)

let REALCALC_LT = prove
 (`abs(a - &2 pow n * x) < &1 /\ abs(b - &2 pow n * y) < &1
   ==> &2 <= abs(a - b) ==> (x < y <=> a < b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `&2 pow n * x < &2 pow n * y` THEN CONJ_TAC THENL
   [SIMP_TAC[REAL_LT_LMUL_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH];
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC]);;

let REALCALC_LE = prove
 (`abs(a - &2 pow n * x) < &1 /\ abs(b - &2 pow n * y) < &1
   ==> &2 <= abs(a - b) ==> (x <= y <=> a <= b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `&2 pow n * x <= &2 pow n * y` THEN CONJ_TAC THENL
   [SIMP_TAC[REAL_LE_LMUL_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH];
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC]);;

let REALCALC_GT = prove
 (`abs(a - &2 pow n * x) < &1 /\ abs(b - &2 pow n * y) < &1
   ==> &2 <= abs(a - b) ==> (x > y <=> a > b)`,
  ONCE_REWRITE_TAC[CONJ_SYM; REAL_ABS_SUB] THEN
  REWRITE_TAC[real_gt; REALCALC_LT]);;

let REALCALC_GE = prove
 (`abs(a - &2 pow n * x) < &1 /\ abs(b - &2 pow n * y) < &1
   ==> &2 <= abs(a - b) ==> (x >= y <=> a >= b)`,
  ONCE_REWRITE_TAC[CONJ_SYM; REAL_ABS_SUB] THEN
  REWRITE_TAC[real_ge; REALCALC_LE]);;

let REALCALC_EQ = prove
 (`abs(a - &2 pow n * x) < &1 /\ abs(b - &2 pow n * y) < &1
   ==> &2 <= abs(a - b) ==> ((x = y) <=> F)`,
  ASM_CASES_TAC `x:real = y` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let realcalc_rel_conv =
  let pops =
   [`(<)`,(</); `(<=)`,(<=/);
    `(>)`,(>/); `(>=)`,(>=/);
    `(=):real->real->bool`,(=/)] in
  let rec find_n rfn1 rfn2 n =
    if n >/ Num.num_of_int 1000 then
       failwith "realcalc_rel_conv: too close to discriminate" else
    if abs_num(raw_eval rfn1 n -/ raw_eval rfn2 n) >=/ Num.num_of_int 4 then n
    else find_n rfn1 rfn2 (n +/ Num.num_of_int 1) in
  fun tm ->
    let lop,r = dest_comb tm in
    let op,l = dest_comb lop in
    let pop =
      try assoc op pops
      with Failure _ -> failwith "realcalc_rel_conv: unknown operator" in
    let rfn1,tfn1 = REALCALC_CONV l
    and rfn2,tfn2 = REALCALC_CONV r in
    let n = find_n rfn1 rfn2 (Num.num_of_int 1) in
    pop (raw_eval rfn1 n) (raw_eval rfn2 n);;

let REALCALC_REL_CONV =
  let pths =
   [`(<)`,REALCALC_LT; `(<=)`,REALCALC_LE;
    `(>)`,REALCALC_GT; `(>=)`,REALCALC_GE;
    `(=):real->real->bool`,REALCALC_EQ] in
  let rec find_n rfn1 rfn2 n =
    if n >/ Num.num_of_int 1000 then
       failwith "realcalc_rel_conv: too close to discriminate" else
    if abs_num(raw_eval rfn1 n -/ raw_eval rfn2 n) >=/ Num.num_of_int 4 then n
    else find_n rfn1 rfn2 (n +/ Num.num_of_int 1) in
  fun tm ->
    let lop,r = dest_comb tm in
    let op,l = dest_comb lop in
    let pth = try assoc op pths
    with Failure _ -> failwith "realcalc_rel_conv: unknown operator" in
    let rfn1,tfn1 = REALCALC_CONV l
    and rfn2,tfn2 = REALCALC_CONV r in
    let n = find_n rfn1 rfn2 (Num.num_of_int 1) in
    let th1 = thm_eval tfn1 n
    and th2 = thm_eval tfn2 n in
    let th3 = MATCH_MP pth (CONJ th1 th2) in
    let th4 = MP th3 (EQT_ELIM(REAL_INT_REDUCE_CONV(lhand(concl th3)))) in
    CONV_RULE(RAND_CONV REAL_RAT_REDUCE_CONV) th4;;
