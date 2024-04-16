(* ========================================================================= *)
(* Derivation of Machin's formula and other similar ones.                    *)
(* ========================================================================= *)

needs "Library/transc.ml";;

let REAL_LE_1_POW2 = prove
 (`!n. &1 <= &2 pow n`,
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> 0 < n`;
              EXP_LT_0; ARITH]);;

let REAL_LT_1_POW2 = prove
 (`!n. &1 < &2 pow n <=> ~(n = 0)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `&2 pow 0`)) THEN
  MATCH_MP_TAC REAL_POW_MONO_LT THEN
  REWRITE_TAC[REAL_OF_NUM_LT] THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;

let REAL_POW2_CLAUSES = prove
 (`(!n. &0 <= &2 pow n) /\
   (!n. &0 < &2 pow n) /\
   (!n. &0 <= inv(&2 pow n)) /\
   (!n. &0 < inv(&2 pow n)) /\
   (!n. inv(&2 pow n) <= &1) /\
   (!n. &1 - inv(&2 pow n) <= &1) /\
   (!n. &1 <= &2 pow n) /\
   (!n. &1 < &2 pow n <=> ~(n = 0)) /\
   (!n. &0 <= &1 - inv(&2 pow n)) /\
   (!n. &0 <= &2 pow n - &1) /\
   (!n. &0 < &1 - inv(&2 pow n) <=> ~(n = 0))`,
  SIMP_TAC[REAL_LE_1_POW2; REAL_LT_1_POW2; REAL_SUB_LE; REAL_SUB_LT;
           REAL_INV_LE_1] THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_INV_EQ; REAL_POW_LT; REAL_POW_LE;
           REAL_OF_NUM_LE; REAL_OF_NUM_LT; ARITH;
           REAL_ARITH `&1 - x <= &1 <=> &0 <= x`] THEN
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&2 pow 1)` THEN
  ASM_SIMP_TAC[REAL_LE_INV2; REAL_POW_MONO; REAL_POW_LT; REAL_OF_NUM_LT; ARITH;
               REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let REAL_POW2_THM = prove
 (`&0 < &2 pow n /\
   &1 <= &2 pow n /\
   (&1 < &2 pow n <=> ~(n = 0)) /\
   (&2 pow m <= &2 pow n <=> m <= n) /\
   (&2 pow m < &2 pow n <=> m < n) /\
   (inv(&2 pow m) <= inv(&2 pow n) <=> n <= m) /\
   (inv(&2 pow m) < inv(&2 pow n) <=> n < m)`,
  REWRITE_TAC[REAL_POW2_CLAUSES] THEN
  SUBGOAL_THEN `!m n. &2 pow m <= &2 pow n <=> m <= n` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EQ_TAC THEN
    SIMP_TAC[REAL_POW_MONO; REAL_OF_NUM_LE; ARITH] THEN
    CONV_TAC CONTRAPOS_CONV THEN
    SIMP_TAC[REAL_NOT_LE; REAL_NOT_LT; REAL_POW_MONO_LT; REAL_OF_NUM_LT;
             NOT_LE; ARITH]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN REWRITE_TAC[GSYM NOT_LE] THEN
  SUBGOAL_THEN `!m n. inv(&2 pow m) <= inv(&2 pow n) <=> &2 pow n <= &2 pow m`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[REAL_LE_INV2; REAL_POW2_CLAUSES] THEN
  CONV_TAC CONTRAPOS_CONV THEN
  SIMP_TAC[REAL_NOT_LE; REAL_LT_INV2; REAL_POW2_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Compound errors given bounds in assumptions.                              *)
(* ------------------------------------------------------------------------- *)

let BOUND_SUMPROD_RULE =
  let pth_add = REAL_ARITH
    `abs(x1) <= b1 /\ abs(x2) <= b2 ==> abs(x1 + x2) <= b1 + b2`
  and pth_sub = REAL_ARITH
    `abs(x1) <= b1 /\ abs(x2) <= b2 ==> abs(x1 - x2) <= b1 + b2`
  and pth_mul = prove
   (`abs(x1) <= b1 /\ abs(x2) <= b2 ==> abs(x1 * x2) <= b1 * b2`,
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SIMP_TAC[REAL_LE_MUL2; REAL_ABS_POS])
  and pth_neg = REAL_ARITH
    `abs(x1) <= b1 ==> abs(--x1) <= b1`
  and pth_pow = prove
   (`abs(x) <= b1 ==> abs(x pow n) <= b1 pow n`,
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS])
  and pth_abs = REAL_ARITH `abs(x) <= b ==> abs(abs(x)) <= b`
  and pth_triv = REAL_ARITH `abs(x) <= abs(x)`
  and n_tm = `n:num` in
  let rec BOUND_SUMPROD_RULE (asl,w) =
    let tm = rator w in
    try tryfind (fun (_,th) -> if rator(concl th) = tm then th
                               else fail()) asl
    with Failure _ -> try
        let pth,th = tryfind
          (fun pth -> pth,PART_MATCH (rator o rand) pth tm)
          [pth_neg; pth_abs] in
        let th1 = BOUND_SUMPROD_RULE (asl,lhand(concl th)) in
        MATCH_MP pth th1
    with Failure _ -> try
        let pth = INST [funpow 3 rand tm,n_tm] pth_pow in
        let th = PART_MATCH (rator o rand) pth tm in
        let th1 = BOUND_SUMPROD_RULE (asl,lhand(concl th)) in
        MATCH_MP (INST [funpow 3 rand tm,n_tm] pth_pow) th1
    with Failure _ -> try
        let pth,th = tryfind
          (fun pth -> pth,PART_MATCH (rator o rand) pth tm)
          [pth_add; pth_sub; pth_mul] in
        let trm = lhand(concl th) in
        let th1 = BOUND_SUMPROD_RULE (asl,lhand trm)
        and th2 = BOUND_SUMPROD_RULE (asl,rand trm) in
        MATCH_MP pth (CONJ th1 th2)
    with Failure _ ->
        PART_MATCH rator pth_triv tm in
  BOUND_SUMPROD_RULE;;

let BOUND_SUMPROD_TAC =
  let tac =
    let pth =
      REAL_ARITH `x <= a ==> (!b. a <= b ==> x <= b) /\
                             (!b. a < b ==> x < b)` in
    fun th ->
      let th1,th2 = CONJ_PAIR(MATCH_MP pth th) in
      MATCH_MP_TAC th1 ORELSE MATCH_MP_TAC th2
  and le_tm = `(<=):real->real->bool` in
  fun (asl,w as gl) ->
    let l,r = dest_comb w in
    let gv = genvar(type_of r) in
    let tm = mk_comb(mk_comb(le_tm,rand l),gv) in
    let th = BOUND_SUMPROD_RULE(asl,tm) in
    tac th gl;;

(* ------------------------------------------------------------------------- *)
(* Power series for atn.                                                     *)
(* ------------------------------------------------------------------------- *)

let REAL_ATN_POWSER_SUMMABLE = prove
 (`!x. abs(x) < &1
       ==> summable (\n. (if EVEN n then &0
                          else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC `\n. abs(x) pow n` THEN CONJ_TAC THENL
   [EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN
    SIMP_TAC[REAL_POW_LE; REAL_MUL_LZERO; REAL_ABS_POS; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NEG; REAL_ABS_POW] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_LID] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    MATCH_MP_TAC REAL_LE_LDIV THEN
    CONJ_TAC THENL [ASM_MESON_TAC[REAL_OF_NUM_LT; EVEN; LT_NZ]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    SIMP_TAC[REAL_POW_LE; REAL_ABS_POS] THEN
    ASM_MESON_TAC[REAL_OF_NUM_LE; EVEN; ARITH_RULE `1 <= n <=> ~(n = 0)`];
    ALL_TAC] THEN
  REWRITE_TAC[summable] THEN EXISTS_TAC `inv(&1 - abs x)` THEN
  MATCH_MP_TAC GP THEN ASM_REWRITE_TAC[REAL_ABS_ABS]);;

let REAL_ATN_POWSER_DIFFS_SUMMABLE = prove
 (`!x. abs(x) < &1
       ==> summable (\n. diffs (\n. (if EVEN n then &0
                                     else --(&1) pow ((n - 1) DIV 2) / &n)) n *
                         x pow n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[diffs] THEN
  MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC `\n. abs(x) pow n` THEN CONJ_TAC THENL
   [EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN
    SIMP_TAC[REAL_POW_LE; REAL_MUL_LZERO; REAL_MUL_RZERO;
             REAL_ABS_POS; REAL_ABS_NUM] THEN
    SIMP_TAC[REAL_MUL_ASSOC; REAL_DIV_LMUL; REAL_OF_NUM_EQ; NOT_SUC] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NEG; REAL_ABS_POW] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[summable] THEN EXISTS_TAC `inv(&1 - abs x)` THEN
  MATCH_MP_TAC GP THEN ASM_REWRITE_TAC[REAL_ABS_ABS]);;

let REAL_ATN_POWSER_DIFFS_SUM = prove
 (`!x. abs(x) < &1
       ==> (\n. diffs (\n. (if EVEN n then &0
                            else --(&1) pow ((n - 1) DIV 2) / &n)) n * x pow n)
           sums (inv(&1 + x pow 2))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_ATN_POWSER_DIFFS_SUMMABLE) THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SUMMABLE_SUM th) THEN
                       MP_TAC(MATCH_MP SER_PAIR th)) THEN
  SUBGOAL_THEN
   `(\n. sum (2 * n,2) (\n. diffs
      (\n. (if EVEN n then &0
            else --(&1) pow ((n - 1) DIV 2) / &n)) n * x pow n)) =
    (\n. --(x pow 2) pow n)`
  SUBST1_TAC THENL
   [ABS_TAC THEN
    CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV(TOP_DEPTH_CONV num_CONV)))) THEN
    REWRITE_TAC[sum; diffs; ADD_CLAUSES; EVEN_MULT; ARITH_EVEN; EVEN] THEN
    REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID; REAL_MUL_LZERO;
                REAL_MUL_RZERO] THEN
    SIMP_TAC[ARITH_RULE `SUC n - 1 = n`; DIV_MULT; ARITH_EQ] THEN
    SIMP_TAC[REAL_MUL_ASSOC; REAL_DIV_LMUL; REAL_OF_NUM_EQ; NOT_SUC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW_POW] THEN
    REWRITE_TAC[GSYM REAL_POW_MUL] THEN
    REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `(\n. --(x pow 2) pow n) sums inv (&1 + x pow 2)` MP_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `&1 + x = &1 - (--x)`] THEN
    MATCH_MP_TAC GP THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_POW] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_POW_2; REAL_LT_MUL2; REAL_ABS_POS]; ALL_TAC] THEN
  MESON_TAC[SUM_UNIQ]);;

let REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE = prove
 (`!x. abs(x) < &1
       ==> summable
             (\n. diffs (diffs
                 (\n. (if EVEN n then &0
                       else --(&1) pow ((n - 1) DIV 2) / &n))) n * x pow n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[diffs] THEN
  MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC `\n. &(SUC n) * abs(x) pow n` THEN CONJ_TAC THENL
   [EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_ABS_MUL; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    COND_CASES_TAC THEN
    SIMP_TAC[REAL_POW_LE; REAL_MUL_LZERO; REAL_MUL_RZERO;
             REAL_ABS_POS; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_MUL_ASSOC] THEN
    SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; NOT_SUC] THEN
    REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NEG; REAL_POW_ONE; REAL_MUL_LID;
                REAL_ABS_NUM; REAL_LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC SER_RATIO THEN
  SUBGOAL_THEN `?c. abs(x) < c /\ c < &1` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(&1 + abs(x)) / &2` THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    UNDISCH_TAC `abs(x) < &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?N. !n. n >= N ==> &(SUC(SUC n)) * abs(x) <= &(SUC n) * c`
  STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `N:num` THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[real_pow; REAL_ABS_MUL; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_ABS_ABS] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN ASM_SIMP_TAC[]] THEN
  ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_RZERO] THEN
    EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN UNDISCH_TAC `abs(x) < c` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; GSYM REAL_ABS_NZ] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM real_div] THEN
  REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x + &1 <= y <=> &1 <= y - x * &1`] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
  SUBGOAL_THEN `?N. &1 <= &N * (c / abs x - &1)` STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `N:num` THEN REWRITE_TAC[GE] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `&1 <= x ==> x <= y ==> &1 <= y`)) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_ARITH `a <= b ==> a <= b + &1`;
                 REAL_OF_NUM_LE; REAL_LE_RADD] THEN
    REWRITE_TAC[REAL_LE_SUB_LADD; REAL_ADD_LID] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; GSYM REAL_ABS_NZ; REAL_MUL_LID;
                 REAL_LT_IMP_LE]] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_LT_SUB_LADD; REAL_ADD_LID;
               REAL_LT_RDIV_EQ; GSYM REAL_ABS_NZ; REAL_MUL_LID;
               REAL_ARCH_SIMPLE]);;

let REAL_ATN_POWSER_DIFFL = prove
 (`!x. abs(x) < &1
       ==> ((\x. suminf (\n. (if EVEN n then &0
                              else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n))
            diffl (inv(&1 + x pow 2))) x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_ATN_POWSER_DIFFS_SUM) THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP SUM_UNIQ) THEN
  MATCH_MP_TAC TERMDIFF THEN
  SUBGOAL_THEN `?K. abs(x) < abs(K) /\ abs(K) < &1` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(&1 + abs(x)) / &2` THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ABS_DIV; REAL_ABS_NUM;
             REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    UNDISCH_TAC `abs(x) < &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ATN_POWSER_SUMMABLE; REAL_ATN_POWSER_DIFFS_SUMMABLE;
               REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE]);;

let REAL_ATN_POWSER = prove
 (`!x. abs(x) < &1
       ==> (\n. (if EVEN n then &0
                 else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n)
           sums (atn x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_ATN_POWSER_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
  SUBGOAL_THEN
   `suminf (\n. (if EVEN n then &0
                 else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n) = atn(x)`
   (fun th -> REWRITE_TAC[th]) THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a = b) <=> (a - b = &0)`] THEN
  SUBGOAL_THEN
   `suminf (\n. (if EVEN n then &0
                 else --(&1) pow ((n - 1) DIV 2) / &n) * &0 pow n) -
    atn(&0) = &0`
  MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `(a = &0) /\ (b = &0) ==> (a - b = &0)`) THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNIQ THEN
      MP_TAC(SPEC `&0` GP) THEN
      REWRITE_TAC[REAL_ABS_NUM; REAL_OF_NUM_LT; ARITH] THEN
      DISCH_THEN(MP_TAC o SPEC `&0` o MATCH_MP SER_CMUL) THEN
      REWRITE_TAC[REAL_MUL_LZERO] THEN
      MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
      CONV_TAC SYM_CONV THEN
      REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0] THEN ASM_MESON_TAC[EVEN];
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM TAN_0] THEN
      MATCH_MP_TAC TAN_ATN THEN
      SIMP_TAC[PI2_BOUNDS; REAL_ARITH `&0 < x ==> --x < &0`]];
    ALL_TAC] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  MP_TAC(SPEC `\x. suminf (\n. (if EVEN n then &0

                       else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n) -
          atn x` DIFF_ISCONST_END_SIMPLE) THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
    `~(x = &0) ==> &0 < x \/ x < &0`))
  THENL
   [DISCH_THEN(MP_TAC o SPECL [`&0`; `x:real`]);
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real`; `&0`])] THEN
  (REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `u:real` THEN REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `abs(u) < &1` (MP_TAC o MATCH_MP REAL_ATN_POWSER_DIFFL) THENL
    [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
   DISCH_THEN(MP_TAC o C CONJ (SPEC `u:real` DIFF_ATN)) THEN
   DISCH_THEN(MP_TAC o MATCH_MP DIFF_SUB) THEN
   REWRITE_TAC[REAL_SUB_REFL]));;

(* ------------------------------------------------------------------------- *)
(* A more Taylor-like version with a simply bounded remainder term.          *)
(* ------------------------------------------------------------------------- *)

let MCLAURIN_ATN_SIMPLE = prove
 (`!x n k. abs(x) <= inv(&2 pow k) /\ ~(k = 0)
           ==> abs(atn x -
                   sum(0,n) (\m. (if EVEN m then &0
                                  else --(&1) pow ((m - 1) DIV 2) / &m) *
                                  x pow m))
               <= &2 * abs(x) pow n`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `abs(x) < &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&2 pow k)` THEN
    ASM_REWRITE_TAC[REAL_ARITH `a < &1 <=> &0 < &1 - a`; REAL_POW2_CLAUSES];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_ATN_POWSER) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(SYM(MATCH_MP SUM_UNIQ th)) THEN
                       MP_TAC(MATCH_MP SUM_SUMMABLE th)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_OFFSET) THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_UNIQ) THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(r) <= e ==> (f - s = r) ==> abs(f - s) <= e`) THEN
  SUBGOAL_THEN
   `(\m. abs(x) pow (m + n)) sums (abs(x) pow n) * inv(&1 - abs(x))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP GP o MATCH_MP (REAL_ARITH
      `abs(x) < &1 ==> abs(abs x) < &1`)) THEN
    DISCH_THEN(MP_TAC o SPEC `abs(x) pow n` o MATCH_MP SER_CMUL) THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[GSYM REAL_POW_ADD];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `suminf (\m. abs(x) pow (m + n))` THEN CONJ_TAC THENL
   [ALL_TAC;
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP SUM_UNIQ) THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_ABS_POS; REAL_POW_LE] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a <= &1 - b <=> b <= &1 - a`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 pow k)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    ASM_SIMP_TAC[REAL_POW_MONO; REAL_OF_NUM_LE; ARITH;
                 ARITH_RULE `~(k = 0) ==> 1 <= k`]] THEN
  SUBGOAL_THEN
   `!m. abs((if EVEN (m + n) then &0
             else --(&1) pow (((m + n) - 1) DIV 2) / &(m + n)) *
             x pow (m + n))
        <= abs(x) pow (m + n)`
  ASSUME_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN
    SIMP_TAC[REAL_MUL_LZERO; REAL_ABS_NUM; REAL_POW_LE; REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NEG] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_LID] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[REAL_POW_LE; REAL_ABS_POS] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_1] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    ASM_MESON_TAC[EVEN]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `suminf (\m. abs((if EVEN (m + n) then &0
                     else --(&1) pow (((m + n) - 1) DIV 2) / &(m + n)) *
                    x pow (m + n)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SER_ABS THEN MATCH_MP_TAC SER_COMPARA THEN
    EXISTS_TAC `\m. abs(x) pow (m + n)` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUM_SUMMABLE]; ALL_TAC] THEN
  MATCH_MP_TAC SER_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SER_COMPARA THEN
    EXISTS_TAC `\m. abs(x) pow (m + n)` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[SUM_SUMMABLE]);;

let MCLAURIN_ATN_APPROX = prove
 (`!x n k. abs(x) <= inv(&2 pow k) /\ ~(k = 0)
           ==> abs(atn x -
                   sum(0,n) (\m. (if EVEN m then &0
                                  else --(&1) pow ((m - 1) DIV 2) / &m) *
                                  x pow m))
               <= inv(&2 pow (n * k - 1))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[sum; REAL_SUB_RZERO; MULT_CLAUSES; SUB_0] THEN
    MP_TAC(SPECL [`x:real`; `2`; `k:num`] MCLAURIN_ATN_SIMPLE) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(y) + d <= e ==> abs(x - y) <= d ==> abs(x) <= e`) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
    REWRITE_TAC[real_pow; REAL_POW_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_INV_1; REAL_ADD_LID] THEN
    SUBGOAL_THEN `abs(x) <= inv(&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 pow k)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      ASM_SIMP_TAC[REAL_POW_MONO; REAL_OF_NUM_LE; ARITH;
                   ARITH_RULE `~(k = 0) ==> 1 <= k`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&2) + &2 * inv(&2) pow 2` THEN
    CONV_TAC(RAND_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[REAL_POW_1] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_OF_NUM_LT; ARITH;
                 REAL_POW_LE2; REAL_OF_NUM_LE; REAL_ABS_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * abs(x) pow n` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MCLAURIN_ATN_SIMPLE THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_SUB; REAL_OF_NUM_EQ; ARITH_EQ;
               ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0] THEN
  REWRITE_TAC[REAL_INV_DIV; REAL_POW_1] THEN REWRITE_TAC[real_div] THEN
  SIMP_TAC[REAL_LE_LMUL_EQ; REAL_OF_NUM_LT; ARITH] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM REAL_POW_POW] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW_INV] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_REWRITE_TAC[REAL_ABS_POS]);;

(* ------------------------------------------------------------------------- *)
(* Rules to return approximations to atn(x) good to 2^-p given |x| <= 2^-k.  *)
(* ------------------------------------------------------------------------- *)

let mclaurin_atn_rule,MCLAURIN_ATN_RULE =
  let x_tm = `x:real`
  and n_tm = `n:num`
  and k_tm = `k:num`
  and inv_tm = `inv`
  and le_tm = `(<=):real->real->bool`
  and pow2_tm = `(pow) (&2)` in
  let pth = SPECL [x_tm; n_tm; k_tm] MCLAURIN_ATN_APPROX
  and CLEAN_RULE = REWRITE_RULE[real_pow]
  and MATCH_REAL_LE_TRANS = MATCH_MP REAL_LE_TRANS
  and num_0 = num 0
  and num_1 = num 1 in
  let mclaurin_atn_rule k0 p0 =
    if k0 = 0 then failwith "mclaurin_atn_rule: must have |x| <= 1/2" else
    let k = num k0
    and p = num p0 in
    let n = Num.int_of_num(ceiling_num ((p +/ k) // k)) in
    let ns = if n mod 2 = 0 then 0--(n - 1) else 0--(n - 2) in
    map (fun m -> if m mod 2 = 0 then num_0 else
                  (if (m - 1) mod 4 = 0 then I else minus_num)
                  (num_1 // num m)) ns
  and MCLAURIN_ATN_RULE k0 p0 =
    if k0 = 0 then failwith "MCLAURIN_ATN_RULE: must have |x| <= 1/2" else
    let k = num k0
    and p = num p0 in
    let n = ceiling_num ((p +/ k) // k) in
    let th1 = INST [mk_numeral k,k_tm; mk_numeral n,n_tm] pth in
    let th2 = ASSUME (lhand(lhand(concl th1)))
    and th3 = EQF_ELIM(NUM_REDUCE_CONV(rand(rand(lhand(concl th1))))) in
    let th4 = MP th1 (CONJ th2 th3) in
    let th5 = CONV_RULE(ONCE_DEPTH_CONV REAL_HORNER_SUM_CONV) th4 in
    let th6 = CLEAN_RULE th5 in
    let th7 = CONV_RULE (NUM_REDUCE_CONV THENC LAND_CONV REAL_RAT_REDUCE_CONV)
                        (BETA_RULE th6) in
    let tm1 = mk_comb(inv_tm,mk_comb(pow2_tm,mk_numeral p)) in
    let tm2 = mk_comb(mk_comb(le_tm,rand(concl th7)),tm1) in
    let th8 = EQT_ELIM((NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) tm2) in
    let th9 = MATCH_REAL_LE_TRANS (CONJ th7 th8) in
    GEN x_tm (DISCH_ALL th9) in
  mclaurin_atn_rule,MCLAURIN_ATN_RULE;;

(* ------------------------------------------------------------------------- *)
(* Lemmas for Machin-type formulas.                                          *)
(* ------------------------------------------------------------------------- *)

let TAN_ADD_ATN_SIDECOND = prove
 (`!x y. ~(x * y = &1) ==> ~(cos(atn x + atn y) = &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[COS_ADD; REAL_ARITH `(a - b = &0) <=> (a = b)`] THEN
  DISCH_THEN(MP_TAC o AP_TERM `(*) (inv(cos(atn x)))`) THEN
  SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; COS_ATN_NZ; REAL_MUL_LID] THEN
  DISCH_THEN(MP_TAC o AP_TERM `(*) (inv(cos(atn y)))`) THEN
  SIMP_TAC[REAL_MUL_LINV; COS_ATN_NZ; REAL_MUL_LID; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c * d = (c * b) * (d * a)`] THEN
  ASM_REWRITE_TAC[GSYM tan; GSYM real_div; ATN_TAN]);;

let ATN_ADD = prove
 (`!x y. ~(x * y = &1) /\
         abs(atn x + atn y) < pi / &2
         ==> (atn(x) + atn(y) = atn((x + y) / (&1 - x * y)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `tan(atn(x) + atn(y)) = (x + y) / (&1 - x * y)` MP_TAC THENL
   [ASM_SIMP_TAC[ATN_TAN; TAN_ADD; COS_ATN_NZ; TAN_ADD_ATN_SIDECOND];
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    ASM_SIMP_TAC[TAN_ATN; REAL_ARITH `abs(x) < e ==> --e < x /\ x < e`]]);;

let ATN_ADD_SMALL_LEMMA_POS = prove
 (`!x y. &0 < y /\ x * y < &1
         ==> atn(x) + atn(y) < pi / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_LT_SUB_LADD] THEN
  SUBGOAL_THEN `pi / &2 - atn y = atn(tan(pi / &2 - atn y))` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC TAN_ATN THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 < x /\ x < a ==> --a < a - x /\ a - x < a`) THEN
    REWRITE_TAC[ATN_BOUNDS] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM ATN_0] THEN
    ASM_SIMP_TAC[ATN_MONO_LT];
    MATCH_MP_TAC ATN_MONO_LT THEN REWRITE_TAC[TAN_COT; ATN_TAN] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_RDIV_EQ; REAL_LT_IMP_NZ]]);;

let ATN_ADD_SMALL_LEMMA = prove
 (`!x y. abs(x * y) < &1 ==> abs(atn(x) + atn(y)) < pi / &2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `--a < x /\ x < a /\ --a < y /\ y < a /\
    (&0 < y ==> x + y < a) /\
    (&0 < --y ==> --x + --y < a)
    ==> abs(x + y) < a`) THEN
  REWRITE_TAC[ATN_BOUNDS] THEN CONJ_TAC THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM ATN_NEG] THEN
  MATCH_MP_TAC ATN_ADD_SMALL_LEMMA_POS THEN
  ASM_SIMP_TAC[REAL_ARITH `abs(x) < &1 ==> x < &1`;
               REAL_ARITH `--x * -- y = x * y`] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `&0 < y ==> (z <= &0 ==> y <= &0) ==> &0 < z`)) THEN
  MATCH_MP_TAC(REAL_ARITH
   `(y < &0 ==> z < &0) /\ ((y = &0) ==> (z = &0))
    ==> y <= &0 ==> z <= &0`) THEN
  SIMP_TAC[ATN_0; GSYM ATN_NEG] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM ATN_0] THEN
  SIMP_TAC[ATN_MONO_LT]);;

let ATN_ADD_SMALL = prove
 (`!x y. abs(x * y) < &1
         ==> (atn(x) + atn(y) = atn((x + y) / (&1 - x * y)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ATN_ADD THEN
  ASM_SIMP_TAC[ATN_ADD_SMALL_LEMMA] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let ATN_ADD_CONV =
  let match_fn = PART_MATCH (lhand o rand) ATN_ADD_SMALL in
  let overall_fn =
    C MP TRUTH o
    CONV_RULE
       (COMB2_CONV REAL_RAT_REDUCE_CONV
         (RAND_CONV REAL_RAT_REDUCE_CONV)) o
    match_fn in
  fun tm -> if is_ratconst(rand(rand tm)) &&
               is_ratconst(rand(lhand tm))
            then overall_fn tm
            else failwith "ATN_ADD_CONV: Atn of nonconstant";;

let ATN_CMUL_CONV =
  let pth_base = prove
   (`(&0 * atn(x) = &0) /\
     (&1 * atn(x) = atn(x))`,
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID])
  and pth_0,pth_1 = (CONJ_PAIR o prove)
   (`(&(NUMERAL(BIT0 n)) * atn(x) =
      &(NUMERAL n) * atn(x) + &(NUMERAL n) * atn(x)) /\
     (&(NUMERAL(BIT1 n)) * atn(x) =
      atn(x) + &(NUMERAL n) * atn(x) + &(NUMERAL n) * atn(x))`,
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
    REWRITE_TAC[NUMERAL; BIT0; BIT1] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_SUC] THEN
    REAL_ARITH_TAC) in
  let rewr_base = GEN_REWRITE_CONV I [pth_base]
  and rewr_0 = GEN_REWRITE_CONV I [pth_0]
  and rewr_1 = GEN_REWRITE_CONV I [pth_1] in
  let rec ATN_CMUL_CONV tm =
    if not (is_ratconst(rand(rand tm))) then failwith "ATN_CMUL_CONV" else
    try rewr_base tm with Failure _ ->
    try let th1 = rewr_0 tm in
        let tm1 = rand(concl th1) in
        let th2 = ATN_CMUL_CONV(rand tm1) in
        let th3 = MK_COMB(AP_TERM (rator(rator tm1)) th2,th2) in
        let th4 = TRANS th3 (ATN_ADD_CONV(rand(concl th3))) in
        TRANS th1 th4
    with Failure _ ->
        let th1 = rewr_1 tm in
        let tm1 = rand(rand(concl th1)) in
        let th2 = ATN_CMUL_CONV(rand tm1) in
        let th3 = MK_COMB(AP_TERM (rator(rator tm1)) th2,th2) in
        let th4 = TRANS th3 (ATN_ADD_CONV(rand(concl th3))) in
        let th5 = AP_TERM (rator(rand(concl th1))) th4 in
        let th6 = TRANS th5 (ATN_ADD_CONV(rand(concl th5))) in
        TRANS th1 th6 in
  ATN_CMUL_CONV;;

let ATN_SUB_CONV =
  let pth = prove
   (`(atn(x) - atn(y) = atn(x) + atn(--y))`,
    REWRITE_TAC[real_sub; ATN_NEG]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(RAND_CONV REAL_RAT_NEG_CONV) THENC
  ATN_ADD_CONV;;

let MACHIN_CONV =
  DEPTH_CONV(ATN_ADD_CONV ORELSEC ATN_SUB_CONV ORELSEC ATN_CMUL_CONV);;

let MACHIN_RULE tm = SYM(TRANS (MACHIN_CONV tm) ATN_1);;

let MACHIN_1 = time MACHIN_RULE `&4 * atn(&1 / &5) - atn(&1 / &239)`;;
let MACHIN_2 = time MACHIN_RULE `atn(&1 / &2) + atn(&1 / &3)`;;
let MACHIN_3 = time MACHIN_RULE `&2 * atn(&1 / &2) - atn(&1 / &7)`;;
let MACHIN_4 = time MACHIN_RULE `&2 * atn(&1 / &3) + atn(&1 / &7)`;;

let EULER = time MACHIN_RULE `&5 * atn(&1 / &7) + &2 * atn (&3 / &79)`;;

let GAUSS_MACHIN = time MACHIN_RULE
  `&12 * atn(&1 / &18) + &8 * atn (&1 / &57) - &5 * atn(&1 / &239)`;;

let STRASSNITZKY_MACHIN = time MACHIN_RULE
  `atn(&1 / &2) + atn (&1 / &5) + atn(&1 / &8)`;;

let MACHINLIKE_1 = time MACHIN_RULE
  `&6 * atn(&1 / &8) + &2 * atn(&1 / &57) + atn(&1 / &239)`;;
let MACHINLIKE_2 = time MACHIN_RULE
  `&4 * atn(&1 / &5) - &1 * atn(&1 / &70) + atn(&1 / &99)`;;
let MACHINLIKE_3 = time MACHIN_RULE
  `&1 * atn(&1 / &2) + &1 * atn(&1 / &5) + atn(&1 / &8)`;;
let MACHINLIKE_4 = time MACHIN_RULE
  `&8 * atn(&1 / &10) - &1 * atn(&1 / &239) - &4 * atn(&1 / &515)`;;
let MACHINLIKE_5 = time MACHIN_RULE
  `&5 * atn(&1 / &7) + &4 * atn(&1 / &53) + &2 * atn(&1 / &4443)`;;

(***** Hopefully this one would work, but it takes a long time

let HWANG_MACHIN = time MACHIN_RULE
  `&183 * atn(&1 / &239) + &32 * atn(&1 / &1023) -
   &68 * atn(&1 / &5832) + &12 * atn(&1 / &110443) -
   &12 * atn(&1 / &4841182) - &100 * atn(&1 / &6826318)`;;

 *****)

(* ------------------------------------------------------------------------- *)
(* Approximate the arctan of a rational number.                              *)
(* ------------------------------------------------------------------------- *)

let rec POLY l x =
  if l = [] then num_0
  else hd l +/ (x */ POLY (tl l) x);;

let atn_approx_conv,ATN_APPROX_CONV =
  let atn_tm = `atn`
  and num_0 = num 0
  and num_1 = num 1
  and num_2 = num 2 in
  let rec log_2 x = if x <=/ num_1 then log_2 (num_2 */ x) -/ num_1
       else if x >/ num_2 then log_2 (x // num_2) +/ num_1
                      else num_1 in
  let pth = prove
   (`!p. abs(atn(&0) - &0) <= inv(&2 pow p)`,
    SIMP_TAC[ATN_0; REAL_SUB_REFL; REAL_ABS_NUM; REAL_LE_INV_EQ;
             REAL_POW_LE; REAL_POS]) in
  let atn_approx_conv p r =
    if r =/ num_0 then num_0 else
    let k = Num.int_of_num(minus_num(log_2(abs_num r))) in
    if k < 1 then failwith "atn_approx_conv: argument too big" else
    let rats = mclaurin_atn_rule k p in
    POLY rats r
  and ATN_APPROX_CONV p tm =
    let atm,rtm = dest_comb tm in
    if atm <> atn_tm then failwith "ATN_APPROX_CONV" else
    let r = rat_of_term rtm in
    if r =/ num_0 then SPEC (mk_small_numeral p) pth else
    let k = Num.int_of_num(minus_num(log_2(abs_num r))) in
    if k < 1 then failwith "ATN_APPROX_CONV: argument too big" else
    let th1 = MCLAURIN_ATN_RULE k p in
    let th2 = SPEC rtm th1 in
    let th3 = MP th2 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th2)))) in
    CONV_RULE(LAND_CONV(RAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV))) th3 in
  atn_approx_conv,ATN_APPROX_CONV;;

(* ------------------------------------------------------------------------- *)
(* Approximate pi using this and a Machin-type formula.                      *)
(* ------------------------------------------------------------------------- *)

let pi_approx_rule,PI_APPROX_RULE =
  let const_1_8 = num 1 // num 8
  and const_1_57 = num 1 // num 57
  and const_1_239 = num 1 // num 239
  and const_24 = num 24
  and const_8 = num 8
  and const_4 = num 4
  and tm_1_8 = `atn(&1 / &8)`
  and tm_1_57 = `atn(&1 / &57)`
  and tm_1_239 = `atn(&1 / &239)`
  and q1_tm = `q1:num`
  and q2_tm = `q2:num`
  and p_tm = `p:num` in
  let pth = prove
   (`(q1 = p + 5) /\
     (q2 = p + 6) /\
     abs(atn(&1 / &8) - a1) <= inv(&2 pow q1) /\
     abs(atn(&1 / &57) - a2) <= inv(&2 pow q2) /\
     abs(atn(&1 / &239) - a3) <= inv(&2 pow q2)
     ==> abs(pi - (&24 * a1 + &8 * a2 + &4 * a3)) <= inv(&2 pow p)`,
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `abs(inv(&2 pow 2))` THEN
    SIMP_TAC[REAL_POW2_CLAUSES; REAL_ARITH `&0 < x ==> &0 < abs(x)`] THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL] THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NUM] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL; GSYM REAL_POW_ADD] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_ADD_LDISTRIB; REAL_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM real_div; MACHINLIKE_1] THEN
    REWRITE_TAC[REAL_ARITH `(x1 + x2 + x3) - (y1 + y2 + y3) =
                            (x1 - y1) + (x2 - y2) + (x3 - y3)`] THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN BOUND_SUMPROD_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
    SIMP_TAC[GSYM REAL_ADD_RDISTRIB; REAL_LE_RMUL_EQ; REAL_POW2_CLAUSES] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV) in
  let pi_approx_rule p =
    let q1 = p + 5
    and q2 = p + 6 in
    let a1 = atn_approx_conv q1 const_1_8
    and a2 = atn_approx_conv q2 const_1_57
    and a3 = atn_approx_conv q2 const_1_239 in
    const_24 */ a1 +/ const_8 */ a2 +/ const_4 */ a3
  and PI_APPROX_RULE p =
    let q1 = p + 5
    and q2 = p + 6 in
    let th1 = ATN_APPROX_CONV q1 tm_1_8
    and th2 = ATN_APPROX_CONV q2 tm_1_57
    and th3 = ATN_APPROX_CONV q2 tm_1_239 in
    let th4 = INST [mk_small_numeral p,p_tm;
                    mk_small_numeral q1,q1_tm;
                    mk_small_numeral q2,q2_tm] pth in
    let th5 = EQT_ELIM(NUM_REDUCE_CONV(lhand(lhand(concl th4))))
    and th6 = EQT_ELIM(NUM_REDUCE_CONV(lhand(rand(lhand(concl th4))))) in
    let th7 = MATCH_MP th4 (end_itlist CONJ [th5; th6; th1; th2; th3]) in
    CONV_RULE(LAND_CONV(RAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV))) th7 in
  pi_approx_rule,PI_APPROX_RULE;;

(* ------------------------------------------------------------------------- *)
(* A version that yields a fraction with power of two denominator.           *)
(* ------------------------------------------------------------------------- *)

let pi_approx_binary_rule,PI_APPROX_BINARY_RULE =
  let pth = prove
   (`abs(x - r) <= inv(&2 pow (SUC p))
     ==> !a. abs(&2 pow p * r - a) <= inv(&2)
             ==> abs(x - a / &2 pow p) <= inv(&2 pow p)`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
      `abs(x - r) <= q ==> abs(r - r') <= p - q ==> abs(x - r') <= p`)) THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `abs(&2 pow p)` THEN
    SIMP_TAC[REAL_ARITH `&0 < x ==> &0 < abs(x)`; REAL_POW2_THM] THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_SUB_LDISTRIB] THEN
    SIMP_TAC[REAL_ABS_POW; REAL_ABS_NUM; GSYM real_div;
             REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_POW2_CLAUSES;
             REAL_DIV_POW2; REAL_OF_NUM_EQ; ARITH_EQ;
             LE_REFL; ARITH_RULE `~(SUC p <= p)`;
             ARITH_RULE `SUC p - p = 1`; SUB_REFL] THEN
    UNDISCH_TAC `abs (&2 pow p * r - a) <= inv (&2)` THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV)
  and num_2 = num 2 in
  let pi_approx_binary_rule p =
    let ppow = power_num num_2 (num p) in
    let r = pi_approx_rule (p + 1) in
    let a = round_num (ppow */ r) in
    a // ppow
  and PI_APPROX_BINARY_RULE p =
    let ppow = power_num num_2 (num p) in
    let th1 = PI_APPROX_RULE (p + 1) in
    let th2 = CONV_RULE(funpow 3 RAND_CONV num_CONV) th1 in
    let r = rat_of_term(rand(rand(lhand(concl th2)))) in
    let th3 = SPEC (mk_realintconst(round_num(ppow */ r))) (MATCH_MP pth th2) in
    let th4 = MP th3 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th3)))) in
    CONV_RULE(LAND_CONV(RAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV))) th4 in
  pi_approx_binary_rule,PI_APPROX_BINARY_RULE;;

(* ------------------------------------------------------------------------- *)
(* Rule to expand atn(r) for rational r into more easily calculable bits.    *)
(* ------------------------------------------------------------------------- *)

let ATN_EXPAND_CONV =
  let num_0 = num 0
  and num_1 = num 1
  and num_2 = num 2
  and eighth = num 1 // num 8
  and atn_tm = `atn`
  and eighth_tm = `&1 / &8`
  and mk_mul = mk_binop `(*)`
  and mk_add = mk_binop `(+)`
  and amp_tm = `&` in
  let home_in =
    let rec homein n x =
      let x' = (x -/ eighth) // (num_1 +/ x */ eighth) in
      if x' </ num_0 then
        if abs_num(x') </ abs_num(x) then (x',n+1) else (x,n)
      else homein (n + 1) x' in
    homein 0 in
  fun tm ->
    let ltm,rtm = dest_comb tm in
    if ltm <> atn_tm then failwith "ATN_EXPAND_CONV" else
    let r = rat_of_term rtm in
    let (x,n) = home_in r in
    let xtm = mk_add (mk_mul (mk_comb(amp_tm,mk_small_numeral n))
                             (mk_comb(atn_tm,eighth_tm)))
                     (mk_comb(atn_tm,term_of_rat x)) in
    SYM(MACHIN_CONV xtm);;
