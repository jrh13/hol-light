(* ========================================================================= *)
(* #26: Leibniz's series for pi                                              *)
(* ========================================================================= *)

needs "Library/transc.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Summability of alternating series.                                        *)
(* ------------------------------------------------------------------------- *)

let ALTERNATING_SUM_BOUNDS = prove
 (`!a. (!n. a(2 * n + 1) <= &0 /\ &0 <= a(2 * n)) /\
       (!n. abs(a(n + 1)) <= abs(a(n)))
       ==> !m n. (EVEN m ==> &0 <= sum(m,n) a /\ sum(m,n) a <= a(m)) /\
                 (ODD m ==> a(m) <= sum(m,n) a /\ sum(m,n) a <= &0)`,
  GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN REWRITE_TAC[ODD; EVEN] THENL
   [SIMP_TAC[sum; ODD_EXISTS; EVEN_EXISTS; LEFT_IMP_EXISTS_THM; ADD1] THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN
  REWRITE_TAC[ARITH_RULE `SUC n = 1 + n`; GSYM SUM_SPLIT] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_conj o concl) o SPEC `SUC m`) THEN
  REWRITE_TAC[ODD; EVEN; SUM_1] THEN REWRITE_TAC[ADD1; GSYM NOT_EVEN] THEN
  UNDISCH_THEN `!n. abs(a(n + 1)) <= abs(a n)` (MP_TAC o SPEC `m:num`) THEN
  ASM_CASES_TAC `EVEN m` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EVEN]) THEN
    REWRITE_TAC[ODD_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST_ALL_TAC) THEN
    REWRITE_TAC[ADD1] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN REAL_ARITH_TAC]);;

let ALTERNATING_SUM_BOUND = prove
 (`!a. (!n. a(2 * n + 1) <= &0 /\ &0 <= a(2 * n)) /\
       (!n. abs(a(n + 1)) <= abs(a(n)))
       ==> !m n. abs(sum(m,n) a) <= abs(a m)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ALTERNATING_SUM_BOUNDS) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  REWRITE_TAC[GSYM NOT_EVEN] THEN ASM_CASES_TAC `EVEN m` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let SUMMABLE_ALTERNATING = prove
 (`!v. (!n. a(2 * n + 1) <= &0 /\ &0 <= a(2 * n)) /\
       (!n. abs(a(n + 1)) <= abs(a(n))) /\ a tends_num_real &0
       ==> summable a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SER_CAUCHY] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o GEN_REWRITE_RULE I [SEQ]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  ASM_MESON_TAC[ALTERNATING_SUM_BOUND; REAL_LET_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Another version of the atan series.                                       *)
(* ------------------------------------------------------------------------- *)

let REAL_ATN_POWSER_ALT = prove
 (`!x. abs(x) < &1
       ==> (\n. (-- &1) pow n / &(2 * n + 1) * x pow (2 * n + 1))
           sums (atn x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_ATN_POWSER) THEN
  FIRST_ASSUM(MP_TAC o C CONJ (ARITH_RULE `0 < 2`) o
              MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_GROUP) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP SUM_UNIQ) THEN
  REWRITE_TAC[SUM_2; EVEN_MULT; EVEN_ADD; ARITH_EVEN; ADD_SUB] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `n * 2 = 2 * n`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ; REAL_MUL_LZERO; REAL_ADD_LID]);;

(* ------------------------------------------------------------------------- *)
(* Summability of the same series for x = 1.                                 *)
(* ------------------------------------------------------------------------- *)

let SUMMABLE_LEIBNIZ = prove
 (`summable (\n. (-- &1) pow n / &(2 * n + 1))`,
  MATCH_MP_TAC SUMMABLE_ALTERNATING THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD; REAL_POW_MUL; GSYM REAL_POW_POW] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_ONE; real_div; REAL_MUL_LID; REAL_MUL_LNEG] THEN
    REWRITE_TAC[REAL_LE_LNEG; REAL_ADD_RID; REAL_LE_INV_EQ; REAL_POS];
    GEN_TAC THEN REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NEG] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_POW_ONE; real_div; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC;
    REWRITE_TAC[SEQ; REAL_SUB_RZERO; REAL_ABS_DIV; REAL_ABS_POW] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_POW_ONE] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH_RULE `0 < n + 1`] THEN
    GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `&1` o MATCH_MP REAL_ARCH) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[GE] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `&1 < x * e ==> e * x <= y ==> &1 < y`)) THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The tricky sum-bounding lemma.                                            *)
(* ------------------------------------------------------------------------- *)

let SUM_DIFFERENCES = prove
 (`!a m n. m <= n + 1 ==> sum(m..n) (\i. a(i) - a(i+1)) = a(m) - a(n + 1)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `m <= 0 + 1 <=> m = 0 \/ m = 1`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[SUM_SING_NUMSEG] THEN
    ASM_SIMP_TAC[SUM_TRIV_NUMSEG; ARITH; REAL_SUB_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `m <= SUC n + 1 <=> m <= n + 1 \/ m = SUC n + 1`] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_TRIV_NUMSEG; ARITH_RULE `n < n + 1`; REAL_SUB_REFL] THEN
  ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG;
    ARITH_RULE `m <= n + 1 ==> m <= SUC n /\ m <= SUC n + 1`] THEN
  REWRITE_TAC[ADD1] THEN REAL_ARITH_TAC);;

let SUM_REARRANGE_LEMMA = prove
 (`!a v m n.
        m <= n + 1
        ==> sum(m..n+1) (\i. a i * v i) =
            sum(m..n) (\k. sum(m..k) a * (v(k) - v(k+1))) +
            sum(m..n+1) a * v(n+1)`,
  REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; num_CONV `1`; ADD_CLAUSES] THEN
    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; SUM_CLAUSES_NUMSEG] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_CASES_TAC `m = SUC(n + 1)` THENL
   [ASM_REWRITE_TAC[LE_SUC; ARITH_RULE `~(n + 1 <= n)`] THEN
    ASM_SIMP_TAC[SUM_TRIV_NUMSEG; ARITH_RULE
     `n < SUC n /\ n < SUC(n + 1)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ARITH_RULE
   `m <= SUC n <=> m <= SUC(n + 1) /\ ~(m = SUC(n + 1))`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC; REAL_EQ_ADD_LCANCEL] THEN
  REWRITE_TAC[REAL_ADD_ASSOC; REAL_ADD_RDISTRIB; REAL_EQ_ADD_RCANCEL] THEN
  REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `m <= SUC(n + 1) /\ ~(m = SUC(n + 1)) ==> m <= SUC n`] THEN
  REWRITE_TAC[REAL_ARITH
   `(s1 * (v - w) + x) + (s2 + y) * w =
    (x + y * w) + (v - w) * s1 + w * s2`] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[REAL_ADD_LDISTRIB; GSYM SUM_CMUL; GSYM SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[REAL_SUB_ADD; REAL_SUB_RDISTRIB] THEN REAL_ARITH_TAC);;

let SUM_BOUNDS_LEMMA = prove
 (`!a v l u m n.
        m <= n /\
        (!i. m <= i /\ i <= n ==> &0 <= v(i) /\ v(i+1) <= v(i)) /\
        (!k. m <= k /\ k <= n ==> l <= sum(m..k) a /\ sum(m..k) a <= u)
        ==> l * v(m) <= sum(m..n) (\i. a(i) * v(i)) /\
            sum(m..n) (\i. a(i) * v(i)) <= u * v(m)`,
  REPLICATE_TAC 5 GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LE; SUM_CLAUSES_NUMSEG] THEN
    SIMP_TAC[ARITH_RULE `m <= i /\ i = 0 <=> m = 0 /\ i = 0`] THEN
    REWRITE_TAC[LEFT_FORALL_IMP_THM; RIGHT_EXISTS_AND_THM; EXISTS_REFL] THEN
    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[SUM_SING_NUMSEG] THEN
    SIMP_TAC[REAL_LE_RMUL];
    POP_ASSUM(K ALL_TAC) THEN REWRITE_TAC[ADD1]] THEN
  SIMP_TAC[SUM_REARRANGE_LEMMA] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(m..n) (\k. l * (v(k) - v(k + 1))) + l * v(n+1)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[SUM_LMUL; SUM_DIFFERENCES] THEN REAL_ARITH_TAC;
      ALL_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(m..n) (\k. u * (v(k) - v(k + 1))) + u * v(n+1)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[SUM_LMUL; SUM_DIFFERENCES] THEN REAL_ARITH_TAC]] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_SIMP_TAC[REAL_LE_RMUL; LE_REFL] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_SUB_LE; ARITH_RULE `k <= n ==> k <= n + 1`]);;

let SUM_BOUND_LEMMA = prove
 (`!a v b m n.
        m <= n /\
        (!i. m <= i /\ i <= n ==> &0 <= v(i) /\ v(i+1) <= v(i)) /\
        (!k. m <= k /\ k <= n ==> abs(sum(m..k) a) <= b)
        ==> abs(sum(m..n) (\i. a(i) * v(i))) <= b * abs(v m)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `--b * k <= a /\ a <= b * k ==> abs(a) <= b * k`) THEN
  ASM_SIMP_TAC[LE_REFL; real_abs] THEN
  MATCH_MP_TAC SUM_BOUNDS_LEMMA THEN
  ASM_REWRITE_TAC[REAL_BOUNDS_LE]);;

(* ------------------------------------------------------------------------- *)
(* Hence the final theorem.                                                  *)
(* ------------------------------------------------------------------------- *)

let LEIBNIZ_PI = prove
 (`(\n. (-- &1) pow n / &(2 * n + 1)) sums (pi / &4)`,
  REWRITE_TAC[GSYM ATN_1] THEN
  ASSUME_TAC(MATCH_MP SUMMABLE_SUM SUMMABLE_LEIBNIZ) THEN
  ABBREV_TAC `s = suminf(\n. (-- &1) pow n / &(2 * n + 1))` THEN
  SUBGOAL_THEN `s = atn(&1)` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 < abs(x - y)) ==> x = y`) THEN
  ABBREV_TAC `e = abs(s - atn(&1))` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  REWRITE_TAC[SER_CAUCHY] THEN DISCH_THEN(MP_TAC o SPEC `e / &7`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(\x. sum(0,N) (\n. (-- &1) pow n / &(2 * n + 1) * x pow (2 * n + 1)))
    contl (&1)`
  MP_TAC THENL
   [MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC
     `sum(0,N) (\n. (-- &1) pow n * &1 pow (2 * n))` THEN
    MATCH_MP_TAC DIFF_SUM THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC DIFF_CMUL THEN
    MP_TAC(SPECL [`2 * k + 1`; `&1`] DIFF_POW) THEN
    DISCH_THEN(MP_TAC o SPEC `inv(&(2 * k + 1))` o MATCH_MP DIFF_CMUL) THEN
    MATCH_MP_TAC(TAUT `a = b ==> a ==> b`) THEN
    REWRITE_TAC[ADD_SUB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[REAL_POW_ONE] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `atn contl (&1)` MP_TAC THENL
   [MESON_TAC[DIFF_CONT; DIFF_ATN]; ALL_TAC] THEN
  REWRITE_TAC[CONTL_LIM; LIM] THEN
  REWRITE_TAC[TAUT `a ==> ~b <=> ~(a /\ b)`; AND_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &6`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; GSYM SUM_SUB] THEN
  ONCE_REWRITE_TAC[GSYM REAL_ABS_NEG] THEN
  REWRITE_TAC[GSYM SUM_NEG; REAL_NEG_SUB; GSYM REAL_MUL_RNEG] THEN
  REWRITE_TAC[REAL_POW_ONE; GSYM REAL_SUB_LDISTRIB] THEN DISCH_THEN
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC)
                    (X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `x = &1 - min (min (d1 / &2) (d2 / &2)) (&1 / &2)` THEN
  REPEAT(FIRST_X_ASSUM (MP_TAC o SPEC `x:real`) THEN ANTS_TAC THENL
          [ASM_REAL_ARITH_TAC; DISCH_TAC]) THEN
  SUBGOAL_THEN `&0 < x /\ x < &1 /\ abs x < &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP REAL_ATN_POWSER_ALT) THEN
  REWRITE_TAC[sums; SEQ] THEN DISCH_THEN(MP_TAC o SPEC `e / &6`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [sums]) THEN
  REWRITE_TAC[SEQ] THEN DISCH_THEN(MP_TAC o SPEC `e / &6`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `N + N1 + N2:num`) THEN
         ANTS_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `abs(sum(N,N1+N2) (\n. -- &1 pow n / &(2 * n + 1) * x pow (2 * n + 1)))
     < e / &6`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `N1 + N2 = 0` THENL
     [ASM_SIMP_TAC[sum; REAL_LT_DIV; REAL_OF_NUM_LT; REAL_ABS_NUM; ARITH];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= e / &7 /\ &0 < e ==> x < e / &6`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `e / &7 * abs(x pow (2 * N + 1))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
      REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_POW_1_LE THEN
      MAP_EVERY UNDISCH_TAC [`&0 < x`; `x < &1`] THEN REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC[PSUM_SUM_NUMSEG] THEN MATCH_MP_TAC SUM_BOUND_LEMMA THEN
    CONJ_TAC THENL [UNDISCH_TAC `~(N1 + N2 = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LT];
      REWRITE_TAC[ARITH_RULE `2 * (m + 1) + 1 = (2 * m + 1) + 2`] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_POW_ADD] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_POW_1_LE; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `(k - N:num) + 1`]) THEN
      SIMP_TAC[PSUM_SUM_NUMSEG; ADD_EQ_0; ARITH_EQ] THEN
      ASM_SIMP_TAC[ARITH_RULE `N <= k ==> (N + (k - N) + 1) - 1 = k`] THEN
      REWRITE_TAC[GE; LE_REFL; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `N1 + N2:num`]) THEN
  REWRITE_TAC[GE; LE_REFL] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `abs((slo + shi) - s) < e / &6
    ==> ~(abs(slo - s) < e / &3) ==> ~(abs(shi) < e / &7)`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_SUB_LDISTRIB; SUM_SUB; REAL_MUL_RID]) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `abs(s1 - sx) < e / &6
    ==> ~(abs(sx - s) < e / &2) ==> ~(abs(s1 - s) < e / &3)`)) THEN
  ASM_REAL_ARITH_TAC);;
