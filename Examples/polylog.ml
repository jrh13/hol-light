(* ========================================================================= *)
(* Pi series in Bailey/Borwein/Plouffe "polylogarithmic constants" paper.    *)
(* ========================================================================= *)

needs "Library/transc.ml";;

let FACTOR_1X4_LEMMA = prove
 (`!x. (x * x + x * sqrt (&2) + &1) * (x * x - x * sqrt (&2) + &1) =
       &1 + x pow 4`,
  REWRITE_TAC[REAL_ARITH
   `(a + b + c) * (a - b + c) = &2 * a * c + a * a - b * b + c * c`] THEN
  REWRITE_TAC[REAL_ARITH
   `&2 * (x * x) * &1 + a - (x * s) * x * s + &1 * &1 =
   (&2 - s * s) * x * x + (&1 + a)`] THEN
  SIMP_TAC[REWRITE_RULE[REAL_POW_2] SQRT_POW_2; REAL_POS] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_LID] THEN
  SUBST1_TAC(SYM(NUM_REDUCE_CONV `SUC(SUC(SUC(SUC 0)))`)) THEN
  REWRITE_TAC[real_pow; REAL_MUL_ASSOC; REAL_MUL_RID]);;

let MAGIC_DERIVATIVE = prove
 (`!x. abs(x) < &1
       ==> ((\x. ln((x - &1) pow 2) +
                 ln((x + &1) pow 2) +
                 ln((x pow 2 + x * sqrt(&2) + &1) /
                    (x pow 2 - x * sqrt(&2) + &1)) +
                 &2 * atn(x * sqrt(&2) + &1) +
                 &2 * atn(x * sqrt(&2) - &1) +
                 &2 * atn(x pow 2) -
                 ln(x pow 4 + &1))
            diffl ((&4 * sqrt(&2) -
                    &8 * x pow 3 -
                    &4 * sqrt(&2) * x pow 4 -
                    &8 * x pow 5) / (&1 - x pow 8)))(x)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o SPEC `x:real` o DIFF_CONV o lhand o rator o snd) THEN
  REWRITE_TAC[IMP_IMP] THEN
  MATCH_MP_TAC(TAUT
   `a /\ (a ==> (b <=> c)) ==> (a ==> b) ==> c`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC(TAUT
     `a /\ (a ==> c) /\ (a /\ c ==> b) /\ d /\ e
      ==> e /\ d /\ b /\ a /\ c`) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
      SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 + 2`)) THEN
      REWRITE_TAC[REAL_POW_ADD; REAL_LE_SQUARE];
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_ADD_SYM] THEN
      ONCE_REWRITE_TAC[GSYM FACTOR_1X4_LEMMA] THEN
      DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_NZ) THEN
      SIMP_TAC[REAL_POW_2; REAL_ENTIRE; DE_MORGAN_THM];
      STRIP_TAC THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `inv((x pow 2 - x * sqrt (&2) + &1) *
                      (x pow 2 - x * sqrt (&2) + &1)) *
                  ((x pow 2 - x * sqrt (&2) + &1) *
                   (x pow 2 - x * sqrt (&2) + &1)) *
                  (x pow 2 + x * sqrt (&2) + &1) /
                  (x pow 2 - x * sqrt (&2) + &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_LT_INV_EQ; GSYM REAL_POW_2] THEN
          ASM_REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`;
                          REAL_POW_EQ_0] THEN
          REWRITE_TAC[REAL_LE_SQUARE; REAL_POW_2]; ALL_TAC] THEN
        ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_DIV_LMUL] THEN
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        REWRITE_TAC[REAL_POW_2; FACTOR_1X4_LEMMA] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
        SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 + 2`)) THEN
        REWRITE_TAC[REAL_POW_ADD; REAL_LE_SQUARE];
        ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_ENTIRE; DE_MORGAN_THM] THEN
      REWRITE_TAC[REAL_LE_REFL; REAL_MUL_LID];
      REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
      REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE; REAL_ENTIRE] THEN
      UNDISCH_TAC `abs(x) < &1` THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
      REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE; REAL_ENTIRE] THEN
      UNDISCH_TAC `abs(x) < &1` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_MUL_LID; REAL_MUL_RID;
              REAL_SUB_RZERO; REAL_SUB_LZERO; REAL_SUB_REFL;
              REAL_ADD_LID; REAL_ADD_RID] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_POW_1] THEN
  REWRITE_TAC[REAL_ARITH
   `(a + b) * (x - y + z) - (a - b) * (x + y + z) =
    &2 * (b * x + b * z - a * y)`] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ARITH
   `s * x * x + s - (&2 * x) * x * s = s * (&1 - x * x)`] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV; GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[AC REAL_MUL_AC
   `a * b * c * d * e * inv(a) * f =
    (a * inv a) * b * c * d * e * f`] THEN
  REWRITE_TAC[REAL_ARITH
   `&1 + (x * s + &1) * (x * s + &1) =
    &2 + &2 * x * s + (s * s) * x * x`] THEN
  REWRITE_TAC[REAL_ARITH
   `&1 + (x * s - &1) * (x * s - &1) =
    &2 + &2 * x * --s + (s * s) * x * x`] THEN
  SIMP_TAC[REWRITE_RULE[REAL_POW_2] SQRT_POW_2; REAL_POS] THEN
  REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[REAL_ARITH `&2 + &2 * x = &2 * (&1 + x)`] THEN
  REWRITE_TAC[REAL_MUL_LNEG] THEN
  REWRITE_TAC[REAL_ARITH
   `&1 + x * (a + b) = (&1 + x * a) + x * b`] THEN
  REWRITE_TAC[REAL_MUL_RNEG] THEN REWRITE_TAC[GSYM real_sub] THEN
  REWRITE_TAC[REAL_ARITH `(&1 + x * a) + x * x = x * x + x * a + &1`] THEN
  REWRITE_TAC[REAL_ARITH `(&1 - x * a) + x * x = x * x - x * a + &1`] THEN
  REWRITE_TAC[REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_ARITH `inv(x) * y * z * x = (x * inv(x)) * y * z`] THEN
  SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; ARITH_EQ; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_ARITH
    `p' * n * &2 * s2 * aa * n' * n' =
     (n' * n) * (p' * n') * &2 * s2 * aa`] THEN
  MP_TAC(SPEC `x pow 2` REAL_LE_SQUARE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `&0 <= x ==> ~(&1 + x = &0)`)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_POW_2] THEN
  REWRITE_TAC[REAL_POW_POW; ARITH] THEN
  REWRITE_TAC[GSYM FACTOR_1X4_LEMMA; REAL_ENTIRE; DE_MORGAN_THM] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_LID] THEN
  SUBGOAL_THEN
   `!other. inv(x * x + x * sqrt (&2) + &1) * sqrt (&2) +
            inv(x * x - x * sqrt (&2) + &1) * sqrt (&2) + other =
            other + &2 * sqrt(&2) * (&1 + x * x) *
                    inv(x * x + x * sqrt (&2) + &1) *
                    inv(x * x - x * sqrt (&2) + &1)`
   (fun th -> ONCE_REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN
    MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN
    EXISTS_TAC `(x * x + x * sqrt (&2) + &1) *
                (x * x - x * sqrt (&2) + &1)` THEN
    MATCH_MP_TAC(TAUT `~a /\ (~a ==> b) ==> ~a /\ b`) THEN CONJ_TAC THENL
     [REWRITE_TAC[FACTOR_1X4_LEMMA] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> ~(&1 + x = &0)`) THEN
      SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 + 2`)) THEN
      REWRITE_TAC[REAL_POW_ADD; REAL_LE_SQUARE]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH
     `(x * y) * (a + b + c) = (x * a) * y + (y * b) * x + x * y * c`] THEN
    ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV] THEN
    REWRITE_TAC[REAL_ARITH
     `(a + b + x * other = x * (other + c)) <=> (a + b = x * c)`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC
     `p * n * x * y * z * p' * n' =
      (p * p') * (n * n') * x * y * z`] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LID; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ARITH
     `a * (x - y + z) + a * (x + y + z) = &2 * a * (x + z)`] THEN
    REWRITE_TAC[REAL_ADD_AC]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL; FACTOR_1X4_LEMMA] THEN
  SUBGOAL_THEN `~(x + &1 = &0) /\ ~(x - &1 = &0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `&0 < (x + &1) pow 2`;
      UNDISCH_TAC `&0 < (x - &1) pow 2`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_NZ) THEN
    SIMP_TAC[REAL_POW_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_ARITH
   `i4 * &2 * s * (&1 - x2) + other + &2 * s * (&1 + x2) * i4 =
    &4 * s * i4 + other`] THEN
  MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC `&1 - x pow 8` THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x < &1 ==> ~(&1 - x = &0)`) THEN
    SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 * 4`)) THEN
    SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `&1 pow 4`)) THEN
    REWRITE_TAC[GSYM REAL_POW_POW] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    REWRITE_TAC[ARITH_EQ; REAL_POW_2; REAL_LE_SQUARE] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `&1 pow 2`)) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; ARITH_EQ]; ALL_TAC] THEN
  SIMP_TAC[GSYM real_div; REAL_DIV_LMUL] THEN
  SUBGOAL_THEN `!x. &1 - x pow 8 = (&1 + x pow 4) * (&1 - x pow 4)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [SUBST1_TAC(SYM(NUM_REDUCE_CONV `4 * 2`)) THEN
    REWRITE_TAC[GSYM REAL_POW_POW] THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_POW_2; GSYM(CONJUNCT2 real_pow)] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBST1_TAC(SPECL [`x pow 4`; `&1`] REAL_ADD_SYM) THEN
  REWRITE_TAC[real_div; REAL_ARITH
   `a + b + c1 * c2 * x + x * d - x * e =
    (a + b) + x * (c1 * c2 + d - e)`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(p * m) * (x + inv(p) * y) = m * x * p + (p * inv(p)) * m * y`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LID] THEN
  UNDISCH_TAC `~(&1 - x pow 4 = &0)` THEN
  SUBGOAL_THEN `!x. &1 - x pow 4 = (&1 + x pow 2) * (&1 - x pow 2)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 * 2`)) THEN
    REWRITE_TAC[GSYM REAL_POW_POW] THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN STRIP_TAC THEN
  UNDISCH_TAC `~(&1 - x pow 2 = &0)` THEN
  SUBGOAL_THEN `!x. &1 - x pow 2 = (&1 + x) * (&1 - x)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(x12 * (p1 + p2) * (m1 - m2)) * (m' * &2 + p' * &2) * other =
    --(&2) * x12 * other *
    ((p2 + p1) * (m2 - m1) * m' + (m2 - m1) * (p2 + p1) * p')`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV] THEN
  CONV_TAC(TOP_DEPTH_CONV num_CONV) THEN
  REWRITE_TAC[real_pow] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let POLYLOG_CONVERGES = prove
 (`!a b x. ~(a = 0) /\ ~(b = 0) /\ abs(x) < &1
           ==> summable (\n. x pow (a * n + b) / &(a * n + b))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC `\n. abs(x) pow (a * n + b)` THEN CONJ_TAC THENL
   [EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_DIV; GSYM REAL_ABS_POW; REAL_ABS_NUM] THEN
    REWRITE_TAC[real_div] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[REAL_INV_LE_1; REAL_OF_NUM_LE;
                 ARITH_RULE `~(b = 0) ==> 1 <= a + b`];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[REAL_POW_ADD; GSYM REAL_POW_POW] THEN
  REWRITE_TAC[summable] THEN
  EXISTS_TAC `abs(x) pow b * inv(&1 - abs(x) pow a)` THEN
  MATCH_MP_TAC SER_CMUL THEN
  MATCH_MP_TAC GP THEN
  REWRITE_TAC[REAL_ABS_POW; REAL_ABS_ABS] THEN
  SUBST1_TAC(SYM(SPEC `a:num` REAL_POW_ONE)) THEN
  MATCH_MP_TAC REAL_POW_LT2 THEN
  ASM_REWRITE_TAC[REAL_ABS_POS]);;

let POLYLOG_DERIVATIVE = prove
 (`!a b x. ~(a = 0) /\ ~(b = 0) /\ abs(x) < &1
           ==> ((\x. suminf (\n. x pow (a * n + b) / &(a * n + b))) diffl
               (x pow (b - 1) / (&1 - x pow a)))(x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(x pow a) < &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_POW] THEN
    SUBST1_TAC(SYM(SPEC `a:num` REAL_POW_ONE)) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  MP_TAC(SPEC `x pow a` GP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\x. suminf (\n. inv(&(a * n + b)) * x pow n)) diffl
     (suminf (\n. diffs (\n. inv(&(a * n + b))) n * (x pow a) pow n)))(x pow a)`
  MP_TAC THENL
   [MATCH_MP_TAC TERMDIFF_STRONG THEN
    EXISTS_TAC `(abs(x pow a) + &1) / &2` THEN
    ABBREV_TAC `k = (abs(x pow a) + &1) / &2` THEN
    SUBGOAL_THEN `abs(x pow a) < abs(k) /\ abs(k) < &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "k" THEN
      SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_LT_RDIV_EQ;
             REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
      UNDISCH_TAC `abs(x pow a) < &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SER_COMPAR THEN
    EXISTS_TAC `\n. abs(k) pow n` THEN CONJ_TAC THENL
     [EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[GSYM real_div; REAL_ABS_DIV;
                  GSYM REAL_ABS_POW; REAL_ABS_NUM] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                   ARITH_RULE `~(b = 0) ==> 0 < a + b`] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LE;
                   ARITH_RULE `~(b = 0) ==> 1 <= a + b`]; ALL_TAC] THEN
    REWRITE_TAC[summable] THEN EXISTS_TAC `inv(&1 - abs k)` THEN
    ASM_SIMP_TAC[GP; REAL_ABS_ABS]; ALL_TAC] THEN
  REWRITE_TAC[diffs] THEN
  MP_TAC(SPECL [`a:num`; `x:real`] DIFF_POW) THEN
  REWRITE_TAC[TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_CHAIN) THEN
  REWRITE_TAC[] THEN
  MP_TAC(SPECL [`b:num`; `x:real`] DIFF_POW) THEN
  REWRITE_TAC[TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_MUL) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `summable (\n. &(SUC n) / &(a * SUC n + b) * (x pow a) pow (SUC n - 1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUC_SUB1] THEN MATCH_MP_TAC SER_COMPAR THEN
    EXISTS_TAC `\n. abs(x pow a) pow n` THEN CONJ_TAC THENL
     [EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
      REWRITE_TAC[GSYM REAL_ABS_POW] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_ABS_DIV; REAL_ABS_NUM;
                   ARITH_RULE `~(b = 0) ==> 0 < a + b /\ 1 <= a + b`;
                   REAL_MUL_LID; REAL_LE_LDIV_EQ] THEN
      MATCH_MP_TAC(ARITH_RULE `1 * n <= b ==> n <= b + c`) THEN
      ASM_SIMP_TAC[LE_MULT_RCANCEL; ARITH_RULE `1 <= n <=> ~(n = 0)`];
      ALL_TAC] THEN
    REWRITE_TAC[summable] THEN EXISTS_TAC `inv(&1 - abs(x pow a))` THEN
    ASM_SIMP_TAC[GP; REAL_ABS_ABS]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o
              MATCH_MP(SPECL [`f:num->real`; `1`] SER_OFFSET_REV) o
              REWRITE_RULE[ADD1]) THEN
  REWRITE_TAC[SUM_1] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID] THEN
  REWRITE_TAC[GSYM real_div] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV(ALPHA_CONV `n:num`))) THEN
  REWRITE_TAC[ADD_SUB] THEN REWRITE_TAC[ADD1] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_CMUL) THEN
  DISCH_THEN(MP_TAC o SPEC `&a * x pow (a - 1) * x pow b`) THEN
  SUBGOAL_THEN
   `summable (\n. inv(&(a * n + b)) * x pow a pow n)`
  MP_TAC THENL
   [MATCH_MP_TAC SER_COMPAR THEN
    EXISTS_TAC `\n. abs(x pow a) pow n` THEN CONJ_TAC THENL
     [EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_ABS_POW; REAL_ABS_NUM] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM] THEN
      ASM_SIMP_TAC[REAL_INV_LE_1; REAL_OF_NUM_LE;
                   ARITH_RULE `~(b = 0) ==> 1 <= a + b`];
      ALL_TAC] THEN
    REWRITE_TAC[summable] THEN
    EXISTS_TAC `inv(&1 - abs(x pow a))` THEN
    ASM_SIMP_TAC[GP; REAL_ABS_ABS]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_CMUL) THEN
  DISCH_THEN(MP_TAC o SPEC `&b * x pow (b - 1)`) THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_ADD) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!n. (&a * x pow (a - 1) * x pow b) *
        &n / &(a * n + b) * x pow a pow (n - 1) +
        (&b * x pow (b - 1)) * inv(&(a * n + b)) * x pow a pow n =
        x pow (a * n + b - 1)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n = 0` THENL
     [ASM_REWRITE_TAC[SUB_0; real_pow; MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
      REWRITE_TAC[REAL_ADD_LID; GSYM REAL_MUL_ASSOC; REAL_MUL_RID] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_DIV_LMUL; REAL_OF_NUM_EQ]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_ADD; GSYM REAL_POW_POW] THEN
    SUBGOAL_THEN `(x pow a) pow n = x pow a * (x pow a) pow (n - 1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
      AP_TERM_TAC THEN UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_POW] THEN
    SUBGOAL_THEN `x pow a = x * x pow (a - 1)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
      AP_TERM_TAC THEN UNDISCH_TAC `~(a = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `x pow b = x * x pow (b - 1)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
      AP_TERM_TAC THEN UNDISCH_TAC `~(b = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_ARITH
     `a * xa1 * x * xb1 * n * i * xan1 + b * xb1 * i * x * xa1 * xan1 =
      x * xa1 * xan1 * xb1 * (a * n + b) * i`] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_OF_NUM_MUL; REAL_OF_NUM_ADD] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_MUL_RID; REAL_OF_NUM_EQ;
                 ARITH_RULE `~(b = 0) ==> ~(a + b = 0)`];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_UNIQ) THEN
  SUBGOAL_THEN
   `x pow (b - 1) / (&1 - x pow a) = suminf (\n. x pow (a * n + b - 1))`
  (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC SUM_UNIQ THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN
    REWRITE_TAC[REAL_POW_ADD; real_div] THEN
    MATCH_MP_TAC SER_CMUL THEN
    ASM_SIMP_TAC[GSYM REAL_POW_POW; GP]; ALL_TAC] THEN
  SIMP_TAC[REAL_MUL_AC] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[diffl] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
               LIM_TRANSFORM) THEN
  REWRITE_TAC[LIM] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `&1 - abs(x)` THEN
  ASM_REWRITE_TAC[REAL_SUB_LT; REAL_SUB_RZERO] THEN
  X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `(a = a') /\ &0 < b ==> abs(a - a') < b`) THEN
  ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `abs(x + h) < &1` ASSUME_TAC THENL
   [UNDISCH_TAC `abs(h) < &1 - abs(x)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. abs(z) < &1
        ==> (suminf (\n. z pow (a * n + b) / &(a * n + b)) =
             z pow b * suminf (\n. inv (&(a * n + b)) * z pow a pow n))`
   (fun th -> ASM_SIMP_TAC[th]) THEN
  X_GEN_TAC `z:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC(GSYM SUM_UNIQ) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[REAL_POW_ADD; real_div; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC SER_CMUL THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_POW_POW] THEN
  MATCH_MP_TAC SUMMABLE_SUM THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC `\n. abs(z pow a) pow n` THEN CONJ_TAC THENL
   [EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_ABS_POW; REAL_ABS_NUM] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_INV_LE_1; REAL_OF_NUM_LE;
                 ARITH_RULE `~(b = 0) ==> 1 <= a + b`];
    ALL_TAC] THEN
  REWRITE_TAC[summable] THEN
  EXISTS_TAC `inv(&1 - abs(z pow a))` THEN
  MATCH_MP_TAC GP THEN REWRITE_TAC[REAL_ABS_ABS; REAL_ABS_POW] THEN
  SUBST1_TAC(SYM(SPEC `a:num` REAL_POW_ONE)) THEN
  MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

let POLYLOG_THM = prove
 (`(\n. inv(&16 pow n) * (&4 / &(8 * n + 1) -
                          &2 / &(8 * n + 4) -
                          &1 / &(8 * n + 5) -
                          &1 / &(8 * n + 6)))
   sums pi`,
  SUBGOAL_THEN
   `!x. abs(x) < &1
        ==> ((\x. suminf (\n. &4 * sqrt(&2) * x pow (8 * n + 1) / &(8 * n + 1) -
                              &8 * x pow (8 * n + 4) / &(8 * n + 4) -
                              &4 * sqrt(&2) * x pow (8 * n + 5) / &(8 * n + 5) -
                              &8 * x pow (8 * n + 6) / &(8 * n + 6)))
             diffl
              (&4 * sqrt(&2) -
               &8 * x pow 3 -
               &4 * sqrt(&2) * x pow 4 -
               &8 * x pow 5) / (&1 - x pow 8))(x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`8`; `1`; `x:real`] POLYLOG_DERIVATIVE) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[real_pow] THEN
    DISCH_THEN(MP_TAC o SPEC `&4 * sqrt(&2)` o MATCH_MP DIFF_CMUL) THEN
    MP_TAC(SPECL [`8`; `4`; `x:real`] POLYLOG_DERIVATIVE) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `&8` o MATCH_MP DIFF_CMUL) THEN
    MP_TAC(SPECL [`8`; `5`; `x:real`] POLYLOG_DERIVATIVE) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `&4 * sqrt(&2)` o MATCH_MP DIFF_CMUL) THEN
    MP_TAC(SPECL [`8`; `6`; `x:real`] POLYLOG_DERIVATIVE) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `&8` o MATCH_MP DIFF_CMUL) THEN
    REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_ADD) THEN
    ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_ADD) THEN
    ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_SUB) THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC; GSYM REAL_ADD_RDISTRIB;
                GSYM REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[REAL_ARITH `a - (b + c + d) = a - b - c - d`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_RID] THEN
    REWRITE_TAC[diffl] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
                 LIM_TRANSFORM) THEN
    REWRITE_TAC[LIM] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    EXISTS_TAC `&1 - abs(x)` THEN
    ASM_REWRITE_TAC[REAL_SUB_LT; REAL_SUB_RZERO] THEN
    X_GEN_TAC `h:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `(a = a') /\ &0 < b ==> abs(a - a') < b`) THEN
    ASM_REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `abs(x + h) < &1` ASSUME_TAC THENL
     [UNDISCH_TAC `abs(h) < &1 - abs(x)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `!z. abs(z) < &1
          ==> (suminf
                  (\n. (&4 * sqrt (&2)) * z pow (8 * n + 1) / &(8 * n + 1) -
                       &8 * z pow (8 * n + 4) / &(8 * n + 4) -
                       (&4 * sqrt (&2)) * z pow (8 * n + 5) / &(8 * n + 5) -
                       &8 * z pow (8 * n + 6) / &(8 * n + 6)) =
            (&4 * sqrt (&2)) * suminf (\n. z pow (8 * n + 1) / &(8 * n + 1)) -
             &8 * suminf (\n. z pow (8 * n + 4) / &(8 * n + 4)) -
             (&4 * sqrt (&2)) * suminf (\n. z pow (8 * n + 5) / &(8 * n + 5)) -
             &8 * suminf (\n. z pow (8 * n + 6) / &(8 * n + 6)))`
     (fun th -> ASM_SIMP_TAC[th]) THEN
    X_GEN_TAC `z:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC(GSYM SUM_UNIQ) THEN
    REPEAT(MATCH_MP_TAC SER_SUB THEN CONJ_TAC) THEN
    MATCH_MP_TAC SER_CMUL THEN
    MATCH_MP_TAC SUMMABLE_SUM THEN
    MATCH_MP_TAC POLYLOG_CONVERGES THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(SPEC
   `\x. suminf (\n. &4 * sqrt (&2) * x pow (8 * n + 1) / &(8 * n + 1) -
                    &8 * x pow (8 * n + 4) / &(8 * n + 4) -
                    &4 * sqrt (&2) * x pow (8 * n + 5) / &(8 * n + 5) -
                    &8 * x pow (8 * n + 6) / &(8 * n + 6)) -
        (ln ((x - &1) pow 2) +
         ln((x + &1) pow 2) +
         ln((x pow 2 + x * sqrt (&2) + &1) /
            (x pow 2 - x * sqrt (&2) + &1)) +
         &2 * atn (x * sqrt (&2) + &1) +
         &2 * atn (x * sqrt (&2) - &1) +
         &2 * atn (x pow 2) - ln (x pow 4 + &1))` DIFF_ISCONST_END_SIMPLE) THEN
  DISCH_THEN(MP_TAC o SPECL [`&0`; `inv(sqrt(&2))`]) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_LT_INV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs(x) < &1` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `!a. &0 <= x /\ x <= a /\ a < &1 ==> abs(x) < &1`) THEN
      EXISTS_TAC `inv(sqrt(&2))` THEN ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `inv(&1)`)) THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN REWRITE_TAC[REAL_LT_01] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `sqrt((&5 / &4) pow 2)` THEN CONJ_TAC THENL
       [SIMP_TAC[POW_2_SQRT; REAL_LE_DIV; REAL_POS] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP MAGIC_DERIVATIVE th) THEN
                         ANTE_RES_THEN MP_TAC th) THEN
    ONCE_REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_SUB) THEN
    REWRITE_TAC[REAL_SUB_REFL]; ALL_TAC] THEN
  SIMP_TAC[snd(EQ_IMP_RULE(SPEC_ALL REAL_POW_EQ_0));
           ARITH_RULE `~(b = 0) ==> ~(a + b = 0)`;
           ARITH_EQ] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  REWRITE_TAC[GSYM real_div; REAL_ADD_LID; REAL_ADD_RID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_DIV_1; LN_1; ATN_1; ATN_NEG; ATN_0] THEN
  REWRITE_TAC[REAL_ARITH `a * b + a * --b + c = c`] THEN
  SUBGOAL_THEN `suminf (\n. &0) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM SUM_UNIQ) THEN
    MP_TAC(SPECL [`\n:num. &0`; `0`] SER_0) THEN REWRITE_TAC[sum];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_SUB_REFL] THEN
  SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LT_INV_EQ;
           SQRT_POS_LT; REAL_OF_NUM_LT; ARITH_LE; ARITH_LT] THEN
  SUBGOAL_THEN `inv(sqrt(&2)) pow 4 = inv(sqrt(&2)) pow 2 pow 2`
  SUBST1_TAC THENL [REWRITE_TAC[REAL_POW_POW; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(&2)) pow 2 = &1 / &2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_INV; real_div; REAL_MUL_LID] THEN AP_TERM_TAC THEN
    SIMP_TAC[SQRT_POW_2; REAL_POS]; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN
   `!other. ln((inv (sqrt (&2)) - &1) pow 2) +
            ln((inv (sqrt (&2)) + &1) pow 2) + other =
            ln(&1 / &4) + other`
   (fun th -> ONCE_REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_ADD_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `&0 < (inv(sqrt(&2)) - &1) pow 2 /\
                  &0 < (inv(sqrt (&2)) + &1) pow 2`
     (fun th -> SIMP_TAC[GSYM LN_MUL; th])
    THENL
     [REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
      REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE; REAL_ENTIRE] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 < x /\ x < &1 ==> ~(x - &1 = &0) /\ ~(x + &1 = &0)`) THEN
      SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT; REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `sqrt((&4 / &5) pow 2)` THEN CONJ_TAC THENL
       [ALL_TAC;
        SIMP_TAC[POW_2_SQRT; REAL_LE_DIV; REAL_POS] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV] THEN
      SIMP_TAC[GSYM SQRT_INV; REAL_POS] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_POW_MUL] THEN
    REWRITE_TAC[REAL_ARITH `(x - &1) * (x + &1) = x * x - &1`] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN
    SUBGOAL_THEN `inv(sqrt(&2)) pow 2 = &1 / &2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_INV; real_div; REAL_MUL_LID] THEN AP_TERM_TAC THEN
      SIMP_TAC[SQRT_POW_2; REAL_POS]; ALL_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[ATN_0; REAL_MUL_RZERO; REAL_ADD_LID] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `l1 + l2 + a + y - l3 = (l1 + l2 - l3) + a + y`] THEN
  SIMP_TAC[GSYM LN_DIV; GSYM LN_MUL; REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT;
           ARITH_LE; ARITH_LT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LN_1; REAL_ADD_LID] THEN
  REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[REAL_POW_ADD; real_div; REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN `!n. inv(sqrt (&2)) pow (8 * n) = inv(&16 pow n)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 * 4`)) THEN
    REWRITE_TAC[GSYM REAL_POW_POW] THEN
    SUBGOAL_THEN `inv(sqrt(&2)) pow 2 = &1 / &2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_INV; real_div; REAL_MUL_LID] THEN AP_TERM_TAC THEN
      SIMP_TAC[SQRT_POW_2; REAL_POS]; ALL_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[GSYM REAL_POW_INV] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN
  SUBGOAL_THEN `!x. x pow 5 = x * x pow 4` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow); ARITH]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_1] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `a * s * i * b - c - d * s * (i * e) * f - g =
    (s * i) * a * b - c - (s * i) * d * e * f - g`] THEN
  SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; SQRT_POS_LT; REAL_OF_NUM_LT;
           ARITH_LT; ARITH_LE] THEN
  SUBGOAL_THEN `!x. x pow 6 = (x pow 2) pow 3`
    (fun th -> REWRITE_TAC[th])
  THENL [REWRITE_TAC[REAL_POW_POW; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x pow 4 = (x pow 2) pow 2`
    (fun th -> REWRITE_TAC[th])
  THENL [REWRITE_TAC[REAL_POW_POW; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(&2)) pow 2 = &1 / &2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_INV; real_div; REAL_MUL_LID] THEN AP_TERM_TAC THEN
    SIMP_TAC[SQRT_POW_2; REAL_POS]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[REAL_INV_MUL] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c = b * a * c`] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
  REWRITE_TAC[GSYM real_div] THEN
  REWRITE_TAC[REAL_SUB_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `summable
      (\n. inv (&16 pow n) *
           (&4 / &(8 * n + 1) -
            &2 / &(8 * n + 4) -
            &1 / &(8 * n + 5) -
            &1 / &(8 * n + 6)))`
  MP_TAC THENL
   [MATCH_MP_TAC SER_COMPAR THEN
    EXISTS_TAC `\n. &8 / &16 pow n` THEN CONJ_TAC THENL
     [EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_ABS_POW; REAL_ABS_NUM] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NUM; REAL_LE_REFL] THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs(v) <= &1 /\ abs(w) <= &1 /\ abs(x) <= &1 /\ abs(y) <= &1
        ==> abs(&4 * v - &2 * w - &1 * x - &1 * y) <= &8`) THEN
      REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM] THEN
      SUBST1_TAC(SYM REAL_INV_1) THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[summable] THEN EXISTS_TAC `&8 / (&1 - inv(&16))` THEN
    REWRITE_TAC[real_div; GSYM REAL_POW_INV] THEN
    MATCH_MP_TAC SER_CMUL THEN
    MATCH_MP_TAC GP THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_SUM) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_EQ_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  MP_TAC(SPEC `atn(&1 / &2)` TAN_COT) THEN
  REWRITE_TAC[ATN_TAN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(MP_TAC o AP_TERM `atn`) THEN REWRITE_TAC[REAL_DIV_1] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(a = d - c) ==> (a = b) ==> (b + c = d)`) THEN
  MATCH_MP_TAC TAN_ATN THEN REWRITE_TAC[PI2_PI4] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 < x /\ x < p4
    ==> --(&2 * p4) < &2 * p4 - x /\ &2 * p4 - x < &2 * p4`) THEN
  CONJ_TAC THENL
   [SUBST1_TAC(SYM ATN_0) THEN MATCH_MP_TAC ATN_MONO_LT THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC ATN_LT_PI4_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;
