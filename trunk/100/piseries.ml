(* ========================================================================= *)
(* Taylor series for tan and cot, via partial fractions expansion of cot.    *)
(* ========================================================================= *)

needs "Library/analysis.ml";;
needs "Library/transc.ml";;
needs "Library/floor.ml";;
needs "Library/poly.ml";;
needs "Examples/machin.ml";;
needs "Library/iter.ml";;

(* ------------------------------------------------------------------------- *)
(* Compatibility stuff for some old proofs.                                  *)
(* ------------------------------------------------------------------------- *)

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

let REAL_INTEGER_CLOSURES = prove
 (`(!n. ?p. abs(&n) = &p) /\
   (!x y. (?m. abs(x) = &m) /\ (?n. abs(y) = &n) ==> ?p. abs(x + y) = &p) /\
   (!x y. (?m. abs(x) = &m) /\ (?n. abs(y) = &n) ==> ?p. abs(x - y) = &p) /\
   (!x y. (?m. abs(x) = &m) /\ (?n. abs(y) = &n) ==> ?p. abs(x * y) = &p) /\
   (!x r. (?n. abs(x) = &n) ==> ?p. abs(x pow r) = &p) /\
   (!x. (?n. abs(x) = &n) ==> ?p. abs(--x) = &p) /\
   (!x. (?n. abs(x) = &n) ==> ?p. abs(abs x) = &p)`,
  REWRITE_TAC[GSYM integer; INTEGER_CLOSED]);;

let PI_APPROX_25_BITS = time PI_APPROX_BINARY_RULE 25;;

(* ------------------------------------------------------------------------- *)
(* Convert a polynomial into a "canonical" list-based form.                  *)
(* ------------------------------------------------------------------------- *)

let POLYMERIZE_CONV =
  let pth = prove
   (`a = poly [a] x`,
    REWRITE_TAC[poly; REAL_MUL_RZERO; REAL_ADD_RID])
  and qth = prove
   (`x * poly p x = poly (CONS (&0) p) x`,
    REWRITE_TAC[poly; REAL_ADD_LID]) in
  let conv_base = GEN_REWRITE_CONV I [pth]
  and conv_zero = GEN_REWRITE_CONV I [qth]
  and conv_step = GEN_REWRITE_CONV I [GSYM(CONJUNCT2 poly)] in
  let is_add = is_binop `(+):real->real->real`
  and is_mul = is_binop `(*):real->real->real` in
  let rec conv tm =
    if is_add tm then
      let l,r = dest_comb tm in
      let r1,r2 = dest_comb r in
      let th1 = AP_TERM l (AP_TERM r1 (conv r2)) in
      TRANS th1 (conv_step(rand(concl th1)))
    else if is_mul tm then
      let th1 = AP_TERM (rator tm) (conv (rand tm)) in
      TRANS th1 (conv_zero(rand(concl th1)))
    else conv_base tm in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Basic definition of cotangent.                                            *)
(* ------------------------------------------------------------------------- *)

let cot = new_definition
  `cot x = cos x / sin x`;;

let COT_TAN = prove
 (`cot(x) = inv(tan(x))`,
  REWRITE_TAC[cot; tan; REAL_INV_DIV]);;

(* ------------------------------------------------------------------------- *)
(* We need to reverse sums to prove the grisly lemma below.                  *)
(* ------------------------------------------------------------------------- *)

let SUM_PERMUTE_0 = prove
 (`!n p. (!y. y < n ==> ?!x. x < n /\ (p(x) = y))
        ==> !f. sum(0,n)(\n. f(p n)) = sum(0,n) f`,
  INDUCT_TAC THEN GEN_TAC THEN TRY(REWRITE_TAC[sum] THEN NO_TAC) THEN
  DISCH_TAC THEN GEN_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[LESS_SUC_REFL] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC RAND_CONV [sum] THEN REWRITE_TAC[ADD_CLAUSES] THEN
  ABBREV_TAC `q:num->num = \r. if r < k then p(r) else p(SUC r)` THEN
  SUBGOAL_THEN `!y:num. y < n ==> ?!x. x < n /\ (q x = y)` MP_TAC THENL
   [X_GEN_TAC `y:num` THEN DISCH_TAC THEN (MP_TAC o ASSUME)
      `!y. y < (SUC n) ==> ?!x. x < (SUC n) /\ (p x = y)` THEN
    DISCH_THEN(MP_TAC o SPEC `y:num`) THEN
    W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
     [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[LESS_SUC_REFL];
      DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o C MP th))] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    CONJ_TAC THENL
     [DISJ_CASES_TAC(SPECL [`x:num`; `k:num`] LTE_CASES) THENL
       [EXISTS_TAC `x:num` THEN EXPAND_TAC "q" THEN BETA_TAC THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC `&k` THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
        UNDISCH_TAC `k < (SUC n)` THEN
        REWRITE_TAC[GSYM LT_SUC_LE; LE_ADD2];
        MP_TAC(ASSUME `k <= x:num`) THEN REWRITE_TAC[LE_LT] THEN
        DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL
         [EXISTS_TAC `x - 1` THEN EXPAND_TAC "q" THEN BETA_TAC THEN
          UNDISCH_TAC `k < x:num` THEN
          DISCH_THEN(X_CHOOSE_THEN `d:num` MP_TAC o MATCH_MP LESS_ADD_1) THEN
          REWRITE_TAC[GSYM ADD1; ADD_CLAUSES] THEN
          DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[LT_SUC]) THEN
          ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
          UNDISCH_TAC `(k + d) < k:num` THEN
          REWRITE_TAC[GSYM LE_SUC_LT] THEN CONV_TAC CONTRAPOS_CONV THEN
          REWRITE_TAC[GSYM NOT_LT; REWRITE_RULE[ADD_CLAUSES] LESS_ADD_SUC];
          SUBST_ALL_TAC(ASSUME `(p:num->num) x = n`) THEN
          UNDISCH_TAC `y < n:num` THEN ASM_REWRITE_TAC[LT_REFL]]];
      SUBGOAL_THEN `!z. q z :num = p(if z < k then z else SUC z)` MP_TAC THENL
       [GEN_TAC THEN EXPAND_TAC "q" THEN BETA_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC[];
        DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
      MAP_EVERY X_GEN_TAC [`x1:num`; `x2:num`] THEN STRIP_TAC THEN
      UNDISCH_TAC `!y. y < (SUC n) ==>
                          ?!x. x < (SUC n) /\ (p x = y)` THEN
      DISCH_THEN(MP_TAC o SPEC `y:num`) THEN
      REWRITE_TAC[MATCH_MP LESS_SUC (ASSUME `y < n:num`)] THEN
      CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
      DISCH_THEN(MP_TAC o SPECL [`if x1 < k then x1 else SUC x1`;
        `if x2 < k then x2 else SUC x2`] o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
       [CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LT_SUC] THEN
        MATCH_MP_TAC LESS_SUC THEN ASM_REWRITE_TAC[];
        DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o C MATCH_MP th)) THEN
        REPEAT COND_CASES_TAC THEN REWRITE_TAC[SUC_INJ] THENL
         [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(x2 < k:num)` THEN
          CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
          REWRITE_TAC[] THEN MATCH_MP_TAC LT_TRANS THEN
          EXISTS_TAC `SUC x2` THEN ASM_REWRITE_TAC[LESS_SUC_REFL];
          DISCH_THEN(SUBST_ALL_TAC o SYM) THEN UNDISCH_TAC `~(x1  < k:num)` THEN
          CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
          REWRITE_TAC[] THEN MATCH_MP_TAC LT_TRANS THEN
          EXISTS_TAC `SUC x1` THEN ASM_REWRITE_TAC[LESS_SUC_REFL]]]];
    DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
      [GSYM th]) THEN BETA_TAC THEN
    UNDISCH_TAC `k < (SUC n)` THEN
    REWRITE_TAC[LE_SUC; LT_SUC_LE; LE_ADD2] THEN
    DISCH_THEN(X_CHOOSE_TAC `d:num` o MATCH_MP LESS_EQUAL_ADD) THEN
    GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o ONCE_DEPTH_CONV)
      [ASSUME `n = k + d:num`] THEN REWRITE_TAC[GSYM SUM_TWO] THEN
    GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV)
      [ASSUME `n = k + d:num`] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (GSYM ADD_SUC)] THEN
    REWRITE_TAC[GSYM SUM_TWO; sum; ADD_CLAUSES] THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN BINOP_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN
      REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
      BETA_TAC THEN EXPAND_TAC "q" THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC RAND_CONV [REAL_ADD_SYM] THEN
      REWRITE_TAC[ASSUME `(p:num->num) k = n`; REAL_EQ_LADD] THEN
      REWRITE_TAC[ADD1; SUM_REINDEX] THEN BETA_TAC THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN BETA_TAC THEN
      REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
      EXPAND_TAC "q" THEN BETA_TAC THEN ASM_REWRITE_TAC[ADD1]]]);;

let SUM_REVERSE_0 = prove
 (`!n f. sum(0,n) f = sum(0,n) (\k. f((n - 1) - k))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `\x. (n - 1) - x`] SUM_PERMUTE_0) THEN
  REWRITE_TAC[] THEN
  W(C SUBGOAL_THEN (fun th -> SIMP_TAC[th]) o funpow 2 lhand o snd) THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  DISCH_TAC THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  EXISTS_TAC `n - 1 - m` THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let SUM_REVERSE = prove
 (`!n m f. sum(m,n) f = sum(m,n) (\k. f(((n + 2 * m) - 1) - k))`,
  REPEAT GEN_TAC THEN SUBST1_TAC(ARITH_RULE `m = 0 + m`) THEN
  REWRITE_TAC[SUM_REINDEX] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_REVERSE_0] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN
  GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES; LE_0] THEN
  DISCH_THEN(fun th -> AP_TERM_TAC THEN MP_TAC th) THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Following is lifted from fsincos taylor series.                           *)
(* ------------------------------------------------------------------------- *)

let MCLAURIN_SIN = prove
 (`!x n. abs(sin x -
             sum(0,n) (\m. (if EVEN m then &0
                            else -- &1 pow ((m - 1) DIV 2) / &(FACT m)) *
                            x pow m))
         <= inv(&(FACT n)) * abs(x) pow n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`sin`; `\n x. if n MOD 4 = 0 then sin(x)
                              else if n MOD 4 = 1 then cos(x)
                              else if n MOD 4 = 2 then --sin(x)
                              else --cos(x)`] MCLAURIN_ALL_LE) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [CONJ_TAC THENL
     [SIMP_TAC[MOD_0; ARITH_EQ; EQT_INTRO(SPEC_ALL ETA_AX)]; ALL_TAC] THEN
    X_GEN_TAC `m:num` THEN X_GEN_TAC `y:real` THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`m:num`; `4`] DIVISION) THEN
    REWRITE_TAC[ARITH_EQ] THEN ABBREV_TAC `d = m MOD 4` THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
    REWRITE_TAC[ADD1; GSYM ADD_ASSOC; MOD_MULT_ADD] THEN
    SPEC_TAC(`d:num`,`d:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    W(MP_TAC o DIFF_CONV o lhand o rator o snd) THEN
    SIMP_TAC[REAL_MUL_RID; REAL_NEG_NEG]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real`; `n:num`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  MATCH_MP_TAC(REAL_ARITH
    `(x = y) /\ abs(u) <= v ==> abs((x + u) - y) <= v`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[SIN_0; COS_0; REAL_NEG_0] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`r:num`; `4`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC
      (RAND_CONV o ONCE_DEPTH_CONV) [th] THEN
      MP_TAC(SYM th)) THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN
    UNDISCH_TAC `r MOD 4 < 4` THEN
    SPEC_TAC(`r MOD 4`,`d:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
    SIMP_TAC[ARITH_RULE `(x + 1) - 1 = x`;
             ARITH_RULE `(x + 3) - 1 = x + 2`;
             ARITH_RULE `x * 4 + 2 = 2 * (2 * x + 1)`;
             ARITH_RULE `x * 4 = 2 * 2 * x`] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
    REWRITE_TAC[REAL_POW_NEG; EVEN_ADD; EVEN_MULT; ARITH_EVEN; REAL_POW_ONE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_INV_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div; REAL_ABS_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[REAL_ABS_NEG; SIN_BOUND; COS_BOUND];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_POW; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The formulas marked with a star on p. 205 of Knopp's book.                *)
(* ------------------------------------------------------------------------- *)

let COT_HALF_TAN = prove
 (`~(integer x)
   ==> (cot(pi * x) = &1 / &2 * (cot(pi * x / &2) - tan(pi * x / &2)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
  REWRITE_TAC[cot; tan] THEN
  REWRITE_TAC[REAL_MUL_RID] THEN
  SUBGOAL_THEN `pi * x = &2 * pi * x / &2`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL
   [ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c = (a * c) * b`] THEN
    SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  ABBREV_TAC `y = pi * x / &2` THEN
  REWRITE_TAC[COS_DOUBLE; SIN_DOUBLE] THEN
  SUBGOAL_THEN `~(sin y = &0) /\ ~(cos y = &0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[SIN_ZERO; COS_ZERO; real_div] THEN
    CONJ_TAC THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b * c = d) <=> (b * a * c = d)`] THEN
    SIMP_TAC[GSYM REAL_MUL_LNEG; REAL_EQ_MUL_RCANCEL; REAL_ENTIRE;
             REAL_INV_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ; REAL_LT_IMP_NZ;
             PI_POS] THEN
    REWRITE_TAC[OR_EXISTS_THM] THEN
    REWRITE_TAC[TAUT `a /\ b \/ a /\ c <=> a /\ (b \/ c)`] THEN
    DISCH_THEN(CHOOSE_THEN(DISJ_CASES_THEN (MP_TAC o AP_TERM `abs`) o
      CONJUNCT2)) THEN
    UNDISCH_TAC `~(integer x)` THEN
    SIMP_TAC[integer; REAL_ABS_NEG; REAL_ABS_NUM; NOT_EXISTS_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC `&2 * sin y * cos y` THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
    `(h * (c * s' - s * c')) * t * s * c =
     (t * h) * (c * c * s * s' - s * s * c * c')`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_LID; REAL_POW_2]);;

let COT_HALF_POS = prove
 (`~(integer x)
   ==> (cot(pi * x) = &1 / &2 * (cot(pi * x / &2) + cot(pi * (x + &1) / &2)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
  REWRITE_TAC[cot; COS_ADD; SIN_ADD; COS_PI2; SIN_PI2] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_SUB_LZERO] THEN
  REWRITE_TAC[REAL_MUL_RID] THEN
  SUBGOAL_THEN `pi * x = &2 * pi * x / &2`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL
   [ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c = (a * c) * b`] THEN
    SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  ABBREV_TAC `y = pi * x / &2` THEN
  REWRITE_TAC[COS_DOUBLE; SIN_DOUBLE] THEN
  SUBGOAL_THEN `~(sin y = &0) /\ ~(cos y = &0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[SIN_ZERO; COS_ZERO; real_div] THEN
    CONJ_TAC THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b * c = d) <=> (b * a * c = d)`] THEN
    SIMP_TAC[GSYM REAL_MUL_LNEG; REAL_EQ_MUL_RCANCEL; REAL_ENTIRE;
             REAL_INV_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ; REAL_LT_IMP_NZ;
             PI_POS] THEN
    REWRITE_TAC[OR_EXISTS_THM] THEN
    REWRITE_TAC[TAUT `a /\ b \/ a /\ c <=> a /\ (b \/ c)`] THEN
    DISCH_THEN(CHOOSE_THEN(DISJ_CASES_THEN (MP_TAC o AP_TERM `abs`) o
      CONJUNCT2)) THEN
    UNDISCH_TAC `~(integer x)` THEN
    SIMP_TAC[integer; REAL_ABS_NEG; REAL_ABS_NUM; NOT_EXISTS_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC `&2 * sin y * cos y` THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
    `(h * c * s' + h * --s * c') * t * s * c =
     (t * h) * (c * c * s * s' - s * s * c * c')`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_LID; REAL_POW_2]);;

let COT_HALF_NEG = prove
 (`~(integer x)
   ==> (cot(pi * x) = &1 / &2 * (cot(pi * x / &2) + cot(pi * (x - &1) / &2)))`,
  STRIP_TAC THEN ASM_SIMP_TAC[COT_HALF_POS] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBST1_TAC(REAL_ARITH `x + &1 = (x - &1) + &2`) THEN
  ABBREV_TAC `y = x - &1` THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; REAL_ADD_LDISTRIB] THEN
  SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[cot; SIN_ADD; COS_ADD; SIN_PI; COS_PI] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_SUB_RZERO] THEN
  REWRITE_TAC[real_div; REAL_MUL_RNEG; REAL_MUL_LNEG; REAL_INV_NEG] THEN
  REWRITE_TAC[REAL_NEG_NEG; REAL_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* By induction, the formula marked with the dagger.                         *)
(* ------------------------------------------------------------------------- *)

let COT_HALF_MULTIPLE = prove
 (`~(integer x)
   ==> !n. cot(pi * x) =
           sum(0,2 EXP n)
             (\k. cot(pi * (x + &k) / &2 pow n) +
                  cot(pi * (x - &k) / &2 pow n)) / &2 pow (n + 1)`,
  DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[EXP; real_pow; REAL_DIV_1; ADD_CLAUSES; REAL_POW_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
    REWRITE_TAC[real_div; REAL_ADD_RID; REAL_SUB_RZERO; GSYM REAL_MUL_2] THEN
    REWRITE_TAC[AC REAL_MUL_AC `(a * b) * c = b * a * c`] THEN
    SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID; REAL_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `sum(0,2 EXP n)
       (\k. &1 / &2 * (cot (pi * (x + &k) / &2 pow n / &2) +
                       cot (pi * ((x + &k) / &2 pow n + &1) / &2)) +
            &1 / &2 * (cot (pi * (x - &k) / &2 pow n / &2) +
                       cot (pi * ((x - &k) / &2 pow n - &1) / &2))) /
    &2 pow (n + 1)` THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `k:num` THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[] THEN BINOP_TAC THENL
     [MATCH_MP_TAC COT_HALF_POS THEN
      UNDISCH_TAC `~(integer x)` THEN
      REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
      SUBGOAL_THEN `x = &2 pow n * (x + &k) / &2 pow n - &k`
        (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
      THENL
       [SIMP_TAC[REAL_DIV_LMUL; REAL_POW2_CLAUSES; REAL_LT_IMP_NZ] THEN
        REAL_ARITH_TAC;
        SIMP_TAC[integer; REAL_INTEGER_CLOSURES]];
      MATCH_MP_TAC COT_HALF_NEG THEN
      UNDISCH_TAC `~(integer x)` THEN
      REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
      SUBGOAL_THEN `x = &2 pow n * (x - &k) / &2 pow n + &k`
        (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
      THENL
       [SIMP_TAC[REAL_DIV_LMUL; REAL_POW2_CLAUSES; REAL_LT_IMP_NZ] THEN
        REAL_ARITH_TAC;
        SIMP_TAC[integer; REAL_INTEGER_CLOSURES]]]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; SUM_CMUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
  ONCE_REWRITE_TAC[real_div] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  BINOP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[real_pow; REAL_POW_ADD; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  SUBGOAL_THEN `!k. (x + &k) / &2 pow n + &1 = (x + &(2 EXP n + k)) / &2 pow n`
   (fun th -> ONCE_REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN
    EXISTS_TAC `&2 pow n` THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_POW2_CLAUSES;
                 REAL_ADD_LDISTRIB] THEN
    REWRITE_TAC[REAL_MUL_RID; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
    REWRITE_TAC[REAL_ADD_AC]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. (x - &k) / &2 pow n - &1 = (x - &(2 EXP n + k)) / &2 pow n`
   (fun th -> ONCE_REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN
    EXISTS_TAC `&2 pow n` THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_POW2_CLAUSES;
                 REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[REAL_MUL_RID; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXP; MULT_2;
              GSYM(ONCE_REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_OFFSET)] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM(CONJUNCT2 real_pow))] THEN
  REWRITE_TAC[SUM_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV (ALPHA_CONV `j:num`)) THEN
  REWRITE_TAC[REAL_ADD_AC; ADD_AC]);;

let COT_HALF_KNOPP = prove
 (`~(integer x)
   ==> !n. cot(pi * x) =
           cot(pi * x / &2 pow n) / &2 pow n +
           sum(1,2 EXP n - 1)
             (\k. cot(pi * (x + &k) / &2 pow (n + 1)) +
                  cot(pi * (x - &k) / &2 pow (n + 1))) / &2 pow (n + 1)`,
  DISCH_TAC THEN GEN_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SPEC `n:num` o MATCH_MP COT_HALF_MULTIPLE) THEN
  SUBGOAL_THEN `!f. sum(0,2 EXP n) f = f 0 + sum(1,2 EXP n - 1) f`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL
   [GEN_TAC THEN SUBGOAL_THEN `2 EXP n = 1 + (2 EXP n - 1)`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
    THENL
     [SIMP_TAC[ARITH_RULE `~(x = 0) ==> (1 + (x - 1) = x)`;
               EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
    REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_DIFF)] THEN
    REWRITE_TAC[SUM_1; REAL_ADD_AC]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID; REAL_SUB_RZERO; GSYM REAL_MUL_2] THEN
  GEN_REWRITE_TAC LAND_CONV [real_div] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `(&2 * cot (pi * x / &2 pow n)) / &2 pow (n + 1) +
    sum(1,2 EXP n - 1)
       (\k. &1 / &2 * (cot (pi * (x + &k) / &2 pow n / &2) +
                       cot (pi * ((x + &k) / &2 pow n - &1) / &2)) +
            &1 / &2 * (cot (pi * (x - &k) / &2 pow n / &2) +
                       cot (pi * ((x - &k) / &2 pow n + &1) / &2))) /
    &2 pow (n + 1)` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `k:num` THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[] THEN BINOP_TAC THENL
     [MATCH_MP_TAC COT_HALF_NEG THEN
      UNDISCH_TAC `~(integer x)` THEN
      REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
      SUBGOAL_THEN `x = &2 pow n * (x + &k) / &2 pow n - &k`
        (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
      THENL
       [SIMP_TAC[REAL_DIV_LMUL; REAL_POW2_CLAUSES; REAL_LT_IMP_NZ] THEN
        REAL_ARITH_TAC;
        SIMP_TAC[integer; REAL_INTEGER_CLOSURES]];
      MATCH_MP_TAC COT_HALF_POS THEN
      UNDISCH_TAC `~(integer x)` THEN
      REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
      SUBGOAL_THEN `x = &2 pow n * (x - &k) / &2 pow n + &k`
        (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
      THENL
       [SIMP_TAC[REAL_DIV_LMUL; REAL_POW2_CLAUSES; REAL_LT_IMP_NZ] THEN
        REAL_ARITH_TAC;
        SIMP_TAC[integer; REAL_INTEGER_CLOSURES]]]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; SUM_CMUL] THEN
  ONCE_REWRITE_TAC[AC REAL_ADD_AC
   `(a + b) + (c + d) = (a + c) + (b + d)`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SUM_ADD] THEN
  GEN_REWRITE_TAC (funpow 2 (LAND_CONV o RAND_CONV) o RAND_CONV)
    [SUM_REVERSE] THEN
  SUBGOAL_THEN `(2 EXP n - 1 + 2 * 1) - 1 = 2 EXP n` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(2 EXP n = 0)` MP_TAC THENL
     [REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
      SPEC_TAC(`2 EXP n`,`m:num`) THEN ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_ADD] THEN
  BINOP_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN
    REWRITE_TAC[real_div; REAL_POW_ADD; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM SUM_CMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[LE_0; ADD_CLAUSES] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [real_div] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
  SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(a = e) /\ (d = e) /\ (b = f) /\ (c = f)
    ==> ((a + b) + (c + d) = (e + f) * &2)`) THEN
  UNDISCH_TAC `k < 2 EXP n - 1 + 1` THEN
  SIMP_TAC[ARITH_RULE `~(p = 0) ==> (k < p - 1 + 1 <=> k < p)`;
           EXP_EQ_0; ARITH_EQ] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!x. (x / &2 pow n + &1 = (x + &2 pow n) / &2 pow n) /\
                    (x / &2 pow n - &1 = (x - &2 pow n) / &2 pow n)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_POW2_CLAUSES; REAL_ADD_RDISTRIB;
             REAL_SUB_RDISTRIB; REAL_MUL_LID; REAL_DIV_RMUL;
             REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x / &2 pow n / &2 = x / &2 pow (n + 1)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[REAL_POW_ADD; real_div; REAL_POW_1; REAL_INV_MUL;
                GSYM REAL_MUL_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[LT_IMP_LE; GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_POW] THEN
  CONJ_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bounds on the terms in this series.                                       *)
(* ------------------------------------------------------------------------- *)

let SIN_SUMDIFF_LEMMA = prove
 (`!x y. sin(x + y) * sin(x - y) = (sin x + sin y) * (sin x - sin y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH
   `(x + y) * (x - y) = x * x - y * y`] THEN
  REWRITE_TAC[SIN_ADD; real_sub; SIN_NEG; COS_NEG] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC; GSYM REAL_MUL_ASSOC;
              REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_ARITH
   `(a = sx * sx + --(sy * sy)) <=> (a + sy * sy + --(sx * sx) = &0)`] THEN
  REWRITE_TAC[REAL_ARITH
   `a + --(sx * cy * cx * sy) + cx * sy * sx * cy + b = a + b`] THEN
  REWRITE_TAC[REAL_ARITH
   `(sx * cy * sx * cy + --(cx * sy * cx * sy)) + sy * sy + --(sx * sx) =
    (sy * sy + (sx * sx + cx * cx) * (cy * cy)) -
    (sx * sx + (sy * sy + cy * cy) * (cx * cx))`] THEN
  REWRITE_TAC[REWRITE_RULE[REAL_POW_2] SIN_CIRCLE; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_SUB_REFL]);;

let SIN_ZERO_LEMMA = prove
 (`!x. (sin(pi * x) = &0) <=> integer(x)`,
  REWRITE_TAC[integer; SIN_ZERO; EVEN_EXISTS] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b <=> ~(a ==> ~b)`] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `(a * b) * c * d = c * b * a * d`] THEN
  SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; ARITH_EQ; REAL_MUL_RID] THEN
  REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN
  SIMP_TAC[GSYM REAL_ADD_LDISTRIB; GSYM REAL_SUB_LDISTRIB;
           REAL_EQ_MUL_LCANCEL; PI_POS; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[NOT_IMP; NOT_FORALL_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
  REWRITE_TAC[REAL_MUL_RNEG; OR_EXISTS_THM] THEN
  REWRITE_TAC[REAL_ARITH
     `(abs(x) = a) <=> &0 <= a /\ ((x = a) \/ (x = --a))`] THEN
  REWRITE_TAC[REAL_POS]);;

let NOT_INTEGER_LEMMA = prove
 (`~(x = &0) /\ abs(x) < &1 ==> ~(integer x)`,
  ONCE_REWRITE_TAC[GSYM REAL_ABS_ZERO] THEN
  CONV_TAC CONTRAPOS_CONV THEN SIMP_TAC[integer; LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; REAL_OF_NUM_LT] THEN
  ARITH_TAC);;

let NOT_INTEGER_DIV_POW2 = prove
 (`~(integer x) ==> ~(integer(x / &2 pow n))`,
  REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
  SUBGOAL_THEN `x = &2 pow n * x / &2 pow n`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
  THENL
   [SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_POW2_CLAUSES];
    SIMP_TAC[integer; REAL_INTEGER_CLOSURES]]);;

let SIN_ABS_LEMMA = prove
 (`!x. abs(x) < pi ==> (abs(sin x) = sin(abs x))`,
  GEN_TAC THEN ASM_CASES_TAC `x = &0` THEN
  ASM_REWRITE_TAC[SIN_0; REAL_ABS_NUM] THEN
  REWRITE_TAC[real_abs] THEN ASM_CASES_TAC `&0 <= x` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `&0 < sin x`
     (fun th -> ASM_SIMP_TAC[th; REAL_LT_IMP_LE]) THEN
    MATCH_MP_TAC SIN_POS_PI THEN ASM_REWRITE_TAC[real_abs] THEN
    ASM_REWRITE_TAC[REAL_LT_LE];
    SUBGOAL_THEN `&0 < --(sin x)`
     (fun th -> SIMP_TAC[th; SIN_NEG;
                         REAL_ARITH `&0 < --x ==> ~(&0 <= x)`]) THEN
    REWRITE_TAC[GSYM SIN_NEG] THEN MATCH_MP_TAC SIN_POS_PI THEN
    ASM_SIMP_TAC[REAL_ARITH `~(x = &0) /\ ~(&0 <= x) ==> &0 < --x`]]);;

let SIN_EQ_LEMMA = prove
 (`!x y. &0 <= x /\ x < pi / &2 /\ &0 <= y /\ y < pi / &2
         ==> ((sin x = sin y) <=> (x = y))`,
  SUBGOAL_THEN
   `!x y. &0 <= x /\ x < pi / &2 /\ &0 <= y /\ y < pi / &2 /\ x < y
          ==> sin x < sin y`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
    CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC[REAL_ARITH `~(x = y) <=> x < y \/ y < x`] THEN
    ASM_MESON_TAC[]] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`sin`; `cos`; `x:real`; `y:real`] MVT_ALT) THEN
  ASM_REWRITE_TAC[DIFF_SIN; REAL_EQ_SUB_RADD] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[REAL_ARITH `x < a + x <=> &0 < a`] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  MATCH_MP_TAC COS_POS_PI2 THEN
  ASM_MESON_TAC[REAL_LET_TRANS; REAL_LT_TRANS]);;

let KNOPP_TERM_EQUIVALENT = prove
 (`~(integer x) /\ k < 2 EXP n
   ==> ((cot(pi * (x + &k) / &2 pow (n + 1)) +
         cot(pi * (x - &k) / &2 pow (n + 1))) / &2 pow (n + 1) =
        cot(pi * x / &2 pow (n + 1)) / &2 pow n /
        (&1 - sin(pi * &k / &2 pow (n + 1)) pow 2 /
              sin(pi * x / &2 pow (n + 1)) pow 2))`,
  let lemma = prove
   (`~(x = &0) /\ (x * a = b) ==> (a = b / x)`,
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC `x:real` THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL]) in
  REPEAT STRIP_TAC THEN SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_POW2_CLAUSES] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_POW_ADD] THEN
  REWRITE_TAC[REAL_POW_1; real_div] THEN
  GEN_REWRITE_TAC RAND_CONV [AC REAL_MUL_AC
   `((a * b') * c) * b * &2 = (&2 * a) * c * b * b'`] THEN
  SIMP_TAC[REAL_MUL_RINV; REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[real_div; REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB;
              REAL_ADD_RDISTRIB; REAL_SUB_RDISTRIB] THEN
  REWRITE_TAC[REAL_MUL_RID; GSYM real_div] THEN
  ABBREV_TAC `a = pi * x / &2 pow (n + 1)` THEN
  ABBREV_TAC `b = pi * &k / &2 pow (n + 1)` THEN
  SUBGOAL_THEN
   `~(sin(a + b) = &0) /\
    ~(sin a = &0) /\
    ~(sin(a - b) = &0) /\
    ~(&1 - sin(b) pow 2 / sin(a) pow 2 = &0)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT
      `(a /\ b /\ c) /\ (b ==> d) ==> a /\ b /\ c /\ d`) THEN
    CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
      REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; GSYM REAL_SUB_LDISTRIB] THEN
      REWRITE_TAC[SIN_ZERO_LEMMA] THEN REWRITE_TAC[real_div] THEN
      REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
      REWRITE_TAC[GSYM real_div] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC NOT_INTEGER_DIV_POW2 THEN
      ASM_REWRITE_TAC[] THENL
       [UNDISCH_TAC `~(integer x)` THEN
        REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
        SUBGOAL_THEN `x = (x + &k) - &k`
         (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
        THENL
         [REAL_ARITH_TAC; SIMP_TAC[integer; REAL_INTEGER_CLOSURES]];
        UNDISCH_TAC `~(integer x)` THEN
        REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
        SUBGOAL_THEN `x = (x - &k) + &k`
         (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
        THENL
         [REAL_ARITH_TAC; SIMP_TAC[integer; REAL_INTEGER_CLOSURES]]];
      ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[REAL_SUB_0] THEN
    DISCH_THEN(MP_TAC o AP_TERM `( * ) (sin(a) pow 2)`) THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_POW_EQ_0; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `(a * a = b * b) <=> ((a + b) * (a - b) = &0)`] THEN
    REWRITE_TAC[GSYM SIN_SUMDIFF_LEMMA] THEN
    REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; GSYM REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[SIN_ZERO_LEMMA] THEN
    REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[GSYM real_div] THEN CONJ_TAC THEN
    MATCH_MP_TAC NOT_INTEGER_DIV_POW2 THENL
     [UNDISCH_TAC `~(integer x)` THEN
      REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
      SUBGOAL_THEN `x = (x + &k) - &k`
       (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
      THENL
       [REAL_ARITH_TAC; SIMP_TAC[integer; REAL_INTEGER_CLOSURES]];
      UNDISCH_TAC `~(integer x)` THEN
      REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
      SUBGOAL_THEN `x = (x - &k) + &k`
       (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
      THENL
       [REAL_ARITH_TAC; SIMP_TAC[integer; REAL_INTEGER_CLOSURES]]];
    ALL_TAC] THEN
  REWRITE_TAC[cot; TAN_ADD; real_sub] THEN REWRITE_TAC[GSYM real_sub] THEN
  MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC `sin(a + b)` THEN
  ASM_SIMP_TAC[REAL_ADD_LDISTRIB; REAL_DIV_LMUL] THEN
  MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC `sin(a - b)` THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `a * (b + c * d) = a * b + c * a * d`] THEN
  ASM_SIMP_TAC[REAL_ADD_LDISTRIB; REAL_DIV_LMUL] THEN
  MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN
  EXISTS_TAC `&1 - sin(b) pow 2 / sin(a) pow 2` THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `a * b * c * da = b * c * a * da`] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL] THEN
  MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC `sin(a) pow 2` THEN
  ASM_REWRITE_TAC[REAL_POW_2; REAL_ENTIRE] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `((sa * sa) * (&1 - sb2 * sa' * sa') * others =
     (sa * sa) * v * w * x * y * sa') =
    (others * (sa * sa - sb2 * (sa * sa') * (sa * sa')) =
     sa * v * w * x * y * sa * sa')`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LID; REAL_MUL_RID] THEN
  SUBGOAL_THEN `sin(a - b) * cos(a + b) + sin(a + b) * cos(a - b) =
                sin(&2 * a)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM SIN_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SIN_DOUBLE] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ARITH
   `sa * samb * sapb * &2 * ca = (&2 * sa * ca) * samb * sapb`] THEN
  AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[SIN_SUMDIFF_LEMMA] THEN REAL_ARITH_TAC);;

let SIN_LINEAR_ABOVE = prove
 (`!x. abs(x) < &1 ==> abs(sin x) <= &2 * abs(x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `2`] MCLAURIN_SIN) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
  REWRITE_TAC[real_pow; REAL_POW_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_DIV_1; REAL_MUL_LID; REAL_POW_1; REAL_ADD_LID] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(a) <= abs(x) ==> abs(s - x) <= a ==> abs(s) <= &2 * abs(x)`) THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC; REAL_ABS_MUL] THEN
  REWRITE_TAC[REAL_ABS_ABS] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &2 * &1` THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let SIN_LINEAR_BELOW = prove
 (`!x. abs(x) < &2 ==> abs(sin x) >= abs(x) / &3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `3`] MCLAURIN_SIN) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
  REWRITE_TAC[real_pow; REAL_POW_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_DIV_1; REAL_MUL_LID; REAL_POW_1; REAL_ADD_LID] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
  SIMP_TAC[real_ge; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&3 * abs(a) <= &2 * abs(x)
    ==> abs(s - x) <= a ==> abs(x) <= abs(s) * &3`) THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_ABS; REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV num_CONV))) THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE]);;

let KNOPP_TERM_BOUND_LEMMA = prove
 (`~(integer x) /\ k < 2 EXP n /\ &6 * abs(x) < &k
   ==> abs(a / (&1 - sin(pi * &k / &2 pow (n + 1)) pow 2 /
                     sin(pi * x / &2 pow (n + 1)) pow 2))
       <= abs(a) / ((&k / (&6 * x)) pow 2 - &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(x = &0)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(integer x)` THEN
    REWRITE_TAC[TAUT `(~b ==> ~a) <=> (a ==> b)`] THEN
    SIMP_TAC[integer; REAL_ABS_NUM; REAL_OF_NUM_EQ; GSYM EXISTS_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN
  ONCE_REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_SUB_LT] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_MUL; REAL_ABS_NUM] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN
    REWRITE_TAC[REAL_OF_NUM_LE; ARITH] THEN
    UNDISCH_TAC `&6 * abs(x) < &k` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC(TAUT `(b <=> a) ==> a ==> b`) THEN
    MATCH_MP_TAC REAL_LT_RDIV_EQ THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH; GSYM REAL_ABS_NZ];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= x /\ x <= y ==> x - &1 <= abs(&1 - y)`) THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_POW_DIV] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(abs(pi * &k / &2 pow (n + 1)) / &3) *
              inv(&2 * abs(pi * x / &2 pow (n + 1)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_INV_MUL] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC
     `p * k * q' * k1 * k2 * p' * x' * q =
      k * (k1 * k2) * x' * (p * p') * (q * q')`] THEN
    SIMP_TAC[REAL_INV_INV; REAL_MUL_RINV; REAL_ABS_ZERO;
             REAL_LT_IMP_NZ; REAL_POW2_CLAUSES; PI_POS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_LE_REFL]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ABS_DIV] THEN
  GEN_REWRITE_TAC RAND_CONV [real_div] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_DIV; REAL_LE_MUL;
           REAL_ABS_POS; REAL_POS] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM real_ge] THEN MATCH_MP_TAC SIN_LINEAR_BELOW THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    SIMP_TAC[REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NUM;
             REAL_LT_LDIV_EQ; REAL_POW2_CLAUSES] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    SIMP_TAC[real_abs; REAL_LT_IMP_LE; PI_POS] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `pi * &2 pow n` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_LMUL_EQ; PI_POS; REAL_OF_NUM_POW; REAL_OF_NUM_LT];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_MUL_ASSOC] THEN
    SIMP_TAC[REAL_LE_RMUL_EQ; REAL_POW2_CLAUSES] THEN
    MATCH_MP_TAC(C MATCH_MP PI_APPROX_25_BITS (REAL_ARITH
     `abs(p - y) <= e ==> y + e <= a ==> p <= a`)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[GSYM REAL_ABS_NZ; SIN_ZERO_LEMMA] THEN
    ASM_SIMP_TAC[NOT_INTEGER_DIV_POW2] THEN
    MATCH_MP_TAC SIN_LINEAR_ABOVE THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    SIMP_TAC[REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NUM;
             REAL_LT_LDIV_EQ; REAL_POW2_CLAUSES] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `abs(&6)` THEN
    CONV_TAC (LAND_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `abs(&k * pi)` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN
      ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
      SIMP_TAC[PI_POS; REAL_ARITH `&0 < x ==> &0 < abs x`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(&2 pow n * pi)` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ABS_NUM; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
      ASM_SIMP_TAC[LT_IMP_LE]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_ABS_POW; REAL_ABS_NUM;
                REAL_ABS_MUL; GSYM REAL_MUL_ASSOC] THEN
    SIMP_TAC[REAL_LE_LMUL_EQ; REAL_POW2_CLAUSES] THEN
    MATCH_MP_TAC(C MATCH_MP PI_APPROX_25_BITS (REAL_ARITH
     `abs(p - y) <= e ==> abs y + e <= a ==> abs p <= a`)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let KNOPP_TERM_BOUND = prove
 (`~(integer x) /\ k < 2 EXP n /\ &6 * abs(x) < &k
   ==> abs((cot(pi * (x + &k) / &2 pow (n + 1)) +
            cot(pi * (x - &k) / &2 pow (n + 1))) / &2 pow (n + 1))
       <= abs(cot(pi * x / &2 pow (n + 1)) / &2 pow n) *
          (&36 * x pow 2) / (&k pow 2 - &36 * x pow 2)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[KNOPP_TERM_EQUIVALENT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(cot(pi * x / &2 pow (n + 1)) / &2 pow n) /
              ((&k / (&6 * x)) pow 2 - &1)` THEN
  ASM_SIMP_TAC[KNOPP_TERM_BOUND_LEMMA] THEN
  GEN_REWRITE_TAC LAND_CONV [real_div] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_DIV] THEN AP_TERM_TAC THEN
  SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `&6 pow 2`)) THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN REWRITE_TAC[REAL_POW_DIV] THEN
  SUBGOAL_THEN `&0 < (&6 * x) pow 2`
   (fun th -> SIMP_TAC[th; REAL_EQ_RDIV_EQ; REAL_SUB_RDISTRIB;
                       REAL_MUL_LID; REAL_DIV_RMUL; REAL_LT_IMP_NZ]) THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT THEN
  REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  UNDISCH_TAC `~(integer x)` THEN
  REWRITE_TAC[TAUT `(~b ==> ~a) <=> (a ==> b)`] THEN
  SIMP_TAC[integer; REAL_ABS_NUM; REAL_OF_NUM_EQ; GSYM EXISTS_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Show that the series we're looking at do in fact converge...              *)
(* ------------------------------------------------------------------------- *)

let SUMMABLE_INVERSE_SQUARES_LEMMA = prove
 (`(\n. inv(&(n + 1) * &(n + 2))) sums &1`,
  REWRITE_TAC[sums] THEN
  SUBGOAL_THEN
   `!n. sum(0,n) (\m. inv(&(m + 1) * &(m + 2))) = &1 - inv(&(n + 1))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [INDUCT_TAC THEN REWRITE_TAC[sum] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[REAL_ARITH `(&1 - a + b = &1 - c) <=> (b + c = a)`] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_LINV_UNIQ THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_INV_MUL; REAL_MUL_ASSOC; REAL_ADD_LDISTRIB] THEN
    SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; ARITH_RULE `~(n + 1 = 0)`] THEN
    REWRITE_TAC[REAL_MUL_LID; ARITH_RULE `SUC(n + 1) = n + 2`] THEN
    MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC `&(n + 2)` THEN
    SIMP_TAC[REAL_ADD_RDISTRIB; real_div; GSYM REAL_MUL_ASSOC; REAL_OF_NUM_EQ;
             REAL_MUL_LINV; ARITH_RULE `~(n + 2 = 0)`; REAL_MUL_LID;
             REAL_MUL_RID] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_RZERO] THEN
  MATCH_MP_TAC SEQ_SUB THEN REWRITE_TAC[SEQ_CONST] THEN
  MATCH_MP_TAC SEQ_INV0 THEN X_GEN_TAC `x:real` THEN
  X_CHOOSE_TAC `N:num` (SPEC `x:real` REAL_ARCH_SIMPLE) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[real_gt; GE] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&N` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LT; ARITH_RULE `a < b + 1 <=> a <= b`]);;

let SUMMABLE_INVERSE_SQUARES = prove
 (`summable (\n. inv(&n pow 2))`,
  MATCH_MP_TAC SUM_SUMMABLE THEN
  EXISTS_TAC `sum(0,2) (\n. inv(&n pow 2)) +
              suminf (\n. inv(&(n + 2) pow 2))` THEN
  MATCH_MP_TAC SER_OFFSET_REV THEN
  MATCH_MP_TAC SER_ACONV THEN MATCH_MP_TAC SER_COMPARA THEN
  EXISTS_TAC `\n. inv(&(n + 1) * &(n + 2))` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_SUMMABLE THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[SUMMABLE_INVERSE_SQUARES_LEMMA]] THEN
  EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[REAL_POW_2; REAL_INV_MUL; REAL_ABS_INV; REAL_ABS_NUM;
              REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC);;

let SUMMABLE_INVERSE_POWERS = prove
 (`!m. 2 <= m ==> summable (\n. inv(&(n + 1) pow m))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC `\m. inv (&(m + 1) pow 2)` THEN CONJ_TAC THENL
   [EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH_RULE `0 < n + 1`] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ARITH_TAC;
    REWRITE_TAC[summable] THEN
    EXISTS_TAC
     `suminf (\m. inv (&m pow 2)) - sum(0,1) (\m. inv (&m pow 2))` THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] SER_OFFSET) THEN
    REWRITE_TAC[SUMMABLE_INVERSE_SQUARES]]);;

let COT_TYPE_SERIES_CONVERGES = prove
 (`!x. ~(integer x) ==> summable (\n. inv(&n pow 2 - x))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SER_ACONV THEN MATCH_MP_TAC SER_COMPARA THEN
  EXISTS_TAC `\n. &2 / &n pow 2` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_SUMMABLE THEN
    EXISTS_TAC `&2 * suminf (\n. inv(&n pow 2))` THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC SER_CMUL THEN
    MATCH_MP_TAC SUMMABLE_SUM THEN
    REWRITE_TAC[SUMMABLE_INVERSE_SQUARES]] THEN
  MP_TAC(SPEC `&2 * abs x + &1` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[GE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &n pow 2`
   (fun th -> SIMP_TAC[th; REAL_LE_RDIV_EQ])
  THENL
   [MATCH_MP_TAC REAL_POW_LT THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&N` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `&2 * abs x + &1 <= &N` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_ABS_INV] THEN
  REWRITE_TAC[GSYM real_div] THEN
  SUBGOAL_THEN `&0 < abs(&n pow 2 - x)`
   (fun th -> SIMP_TAC[REAL_LE_LDIV_EQ; th])
  THENL
   [REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
    UNDISCH_TAC `~(integer x)` THEN
    REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
    DISCH_TAC THEN
    SUBST1_TAC(REAL_ARITH `x = &n pow 2 - (&n pow 2 - x)`) THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    SIMP_TAC[integer; REAL_INTEGER_CLOSURES]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&2 * abs(x) + &1 <= a ==> a <= &2 * abs(a - x)`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N pow 2` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; EXP_2; LE_SQUARE_REFL];
    ASM_SIMP_TAC[REAL_POW_LE2; REAL_OF_NUM_LE; LE_0]]);;

(* ------------------------------------------------------------------------- *)
(* Now the rather tricky limiting argument gives the result.                 *)
(* ------------------------------------------------------------------------- *)

let SIN_X_RANGE = prove
 (`!x. abs(sin(x) - x) <= abs(x) pow 2 / &2`,
  GEN_TAC THEN
  MP_TAC(SPECL [`x:real`; `2`] MCLAURIN_SIN) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
  REWRITE_TAC[ARITH; REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_DIV_1; REAL_POW_1; REAL_MUL_LID] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN REWRITE_TAC[REAL_MUL_AC]);;

let SIN_X_X_RANGE = prove
 (`!x. ~(x = &0) ==> abs(sin(x) / x - &1) <= abs(x) / &2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `abs(x)` THEN
  ASM_REWRITE_TAC[GSYM REAL_ABS_MUL; GSYM REAL_ABS_NZ] THEN
  ASM_SIMP_TAC[REAL_SUB_LDISTRIB; REAL_DIV_LMUL] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC; REAL_MUL_RID] THEN
  REWRITE_TAC[GSYM REAL_POW_2; SIN_X_RANGE; GSYM real_div]);;

let SIN_X_LIMIT = prove
 (`((\x. sin(x) / x) tends_real_real &1)(&0)`,
  REWRITE_TAC[LIM] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN EXISTS_TAC `e:real` THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(x) / &2` THEN
  ASM_SIMP_TAC[SIN_X_X_RANGE; REAL_ABS_NZ] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  UNDISCH_TAC `abs(x) < e` THEN REAL_ARITH_TAC);;

let COT_X_LIMIT = prove
 (`((\x. x * cot(x)) tends_real_real &1)(&0)`,
  SUBGOAL_THEN `(cos tends_real_real &1)(&0)` MP_TAC THENL
   [MP_TAC(SPEC `&0` DIFF_COS) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_CONT) THEN
    REWRITE_TAC[contl; REAL_ADD_LID; COS_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C CONJ SIN_X_LIMIT) THEN
  DISCH_THEN(MP_TAC o C CONJ (REAL_ARITH `~(&1 = &0)`)) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_DIV) THEN
  REWRITE_TAC[REAL_DIV_1; cot] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_AC; REAL_INV_INV]);;

let COT_LIMIT_LEMMA = prove
 (`!x. ~(x = &0)
       ==> (\n. (x / &2 pow n) * cot(x / &2 pow n)) tends_num_real &1`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SEQ] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC COT_X_LIMIT THEN REWRITE_TAC[LIM] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
  X_CHOOSE_TAC `N:num` (SPEC `abs(x) / d` REAL_ARCH_POW2) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN
  DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_POW2_CLAUSES; REAL_LT_DIV; GSYM REAL_ABS_NZ] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_POW2_CLAUSES] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&2 pow N` THEN
  ASM_REWRITE_TAC[REAL_POW2_THM]);;

let COT_LIMIT_LEMMA1 = prove
 (`~(x = &0)
   ==> (\n. (pi / &2 pow (n + 1)) * cot(pi * x / &2 pow (n + 1)))
       tends_num_real (inv(x))`,
  DISCH_TAC THEN
  MP_TAC(SPEC `pi * x * inv(&2)` COT_LIMIT_LEMMA) THEN
  ASM_SIMP_TAC[REAL_ENTIRE; REAL_LT_IMP_NZ; PI_POS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
   `p * x * a * b * c = x * (p * (a * b)) * c`] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
  REWRITE_TAC[ADD1; GSYM real_div] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [GSYM REAL_MUL_LID] THEN
  FIRST_ASSUM(SUBST1_TAC o GSYM o MATCH_MP REAL_MUL_LINV) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC SEQ_MUL THEN REWRITE_TAC[SEQ_CONST] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `x * p * q * c = x * (p * q) * c`] THEN
  ASM_REWRITE_TAC[GSYM real_div]);;

let COT_X_BOUND_LEMMA_POS = prove
 (`?M. !x. &0 < x /\ abs(x) <= &1 ==> abs(x * cot(x)) <= M`,
  MP_TAC COT_X_LIMIT THEN REWRITE_TAC[LIM] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`\x. x * cot(x)`; `d:real`; `&1`] CONT_BOUNDED_ABS) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC CONT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CONT THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[DIFF_X]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
    REWRITE_TAC[cot] THEN MATCH_MP_TAC CONT_DIV THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CONT THEN
      EXISTS_TAC `--(sin x)` THEN REWRITE_TAC[DIFF_COS];
      MATCH_MP_TAC DIFF_CONT THEN
      EXISTS_TAC `cos x` THEN REWRITE_TAC[DIFF_SIN];
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
      SUBGOAL_THEN `&1 < pi`
       (fun th -> ASM_MESON_TAC[th; REAL_LET_TRANS; REAL_LTE_TRANS]) THEN
      MP_TAC PI_APPROX_25_BITS THEN
      MATCH_MP_TAC(REAL_ARITH
       `&1 + e < a ==> abs(p - a) <= e ==> &1 < p`) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN EXISTS_TAC `abs M + &2` THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  DISJ_CASES_TAC(SPECL [`abs x`; `d:real`] REAL_LTE_TOTAL) THENL
   [MATCH_MP_TAC(REAL_ARITH `abs(x - &1) < &1 ==> abs(x) <= abs(m) + &2`) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> &0 < abs(x)`];
    MATCH_MP_TAC(REAL_ARITH `x <= m ==> x <= abs(m) + &2`) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 < x`; `abs(x) <= &1`; `d <= abs(x)`] THEN
    REAL_ARITH_TAC]);;

let COT_X_BOUND_LEMMA = prove
 (`?M. !x. ~(x = &0) /\ abs(x) <= &1 ==> abs(x * cot(x)) <= M`,
  X_CHOOSE_TAC `M:real` COT_X_BOUND_LEMMA_POS THEN
  EXISTS_TAC `M:real` THEN X_GEN_TAC `x:real` THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `~(x = &0) ==> &0 < x \/ &0 < --x`)) THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `x * cot(x) = --x * cot(--x)` SUBST1_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[REAL_ABS_NEG]] THEN
  REWRITE_TAC[cot; SIN_NEG; COS_NEG; real_div; REAL_INV_NEG;
              REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG]);;

let COT_PARTIAL_FRACTIONS = prove
 (`~(integer x)
   ==> (\n. (&2 * x pow 2) / (x pow 2 - &n pow 2)) sums
       ((pi * x) * cot(pi * x) + &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(x = &0)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(integer x)` THEN
    REWRITE_TAC[TAUT `(~b ==> ~a) <=> (a ==> b)`] THEN
    SIMP_TAC[integer; REAL_ABS_NUM; REAL_OF_NUM_EQ; GSYM EXISTS_REFL];
    ALL_TAC] THEN
  ABBREV_TAC
   `A = \n k. (pi * x / &2 pow n) * cot(pi * x / &2 pow n) +
              (pi * x / &2 pow (n + 1)) *
              sum(1,k) (\m. cot (pi * (x + &m) / &2 pow (n + 1)) +
                            cot (pi * (x - &m) / &2 pow (n + 1)))` THEN
  ABBREV_TAC
   `B = \n k. (pi * x / &2 pow (n + 1)) *
              sum(k + 1,2 EXP n - 1 - k)
                 (\m. cot(pi * (x + &m) / &2 pow (n + 1)) +
                      cot(pi * (x - &m) / &2 pow (n + 1)))` THEN
  SUBGOAL_THEN `!n. ~(x - &n = &0)` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN UNDISCH_TAC `~(integer x)` THEN
    REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `x = (x - &n) + &n` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_SIMP_TAC[integer; REAL_INTEGER_CLOSURES]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~(x + &n = &0)` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN UNDISCH_TAC `~(integer x)` THEN
    REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `x = (x + &n) - &n` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_SIMP_TAC[integer; REAL_INTEGER_CLOSURES]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~(x pow 2 - &n pow 2 = &0)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a * a - b * b = (a + b) * (a - b)`] THEN
    ASM_REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (&2 * x) / (x pow 2 - &n pow 2) = inv(x + &n) + inv(x - &n)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN
    EXISTS_TAC `x pow 2 - &n pow 2` THEN ASM_SIMP_TAC[REAL_DIV_LMUL] THEN
    REWRITE_TAC[REAL_POW_2; REAL_ADD_LDISTRIB] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a * a - b * b = (a + b) * (a - b)`] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `(p * m) * p' + (p * m) * m' = m * p * p' + p * m * m'`] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. (\n. A n k) tends_num_real
                    (&1 + sum(1,k) (\n. (&2 * x pow 2) / (x pow 2 - &n pow 2)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "A" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SEQ_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC COT_LIMIT_LEMMA THEN
      ASM_SIMP_TAC[REAL_ENTIRE; PI_POS; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_CMUL] THEN MATCH_MP_TAC SEQ_SUM THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_POW_2; real_div] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(&2 * x * x) * d = x * (&2 * x) * d`] THEN
    REWRITE_TAC[GSYM REAL_POW_2; GSYM real_div] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    MATCH_MP_TAC SEQ_ADD THEN
    REWRITE_TAC[real_div] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(p * x * d) * cc = x * (p * d) * cc`] THEN
    CONJ_TAC THEN MATCH_MP_TAC SEQ_MUL THEN REWRITE_TAC[SEQ_CONST] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[COT_LIMIT_LEMMA1]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k n. &6 * abs(x) < &k
          ==> abs(B n k)
              <= abs((pi * x / &2 pow (n + 1)) *
                     cot(pi * x / &2 pow (n + 1))) *
                 sum(k + 1,2 EXP n - 1 - k)
                    (\m. (&72 * x pow 2) / (&m pow 2 - &36 * x pow 2))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[GSYM SUM_CMUL] THEN
    W(fun (asl,w) -> MP_TAC(PART_MATCH lhand SUM_ABS_LE (lhand w))) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN
    REWRITE_TAC[ARITH_RULE
     `k + 1 <= r /\ r < (p - 1 - k) + k + 1 <=> k < r /\ r < p`] THEN
    STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
    EXISTS_TAC `abs(inv(&2 pow (n + 1)))` THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REWRITE_TAC[GSYM real_div] THEN
    SIMP_TAC[REAL_ARITH `&0 < x ==> &0 < abs(x)`; REAL_LT_INV_EQ;
             REAL_POW2_CLAUSES] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `abs(cot (pi * x / &2 pow (n + 1)) / &2 pow n) *
      (&36 * x pow 2) / (&r pow 2 - &36 * x pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC KNOPP_TERM_BOUND THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC `&k` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_POW_ADD;
                REAL_ABS_MUL; REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    GEN_REWRITE_TAC RAND_CONV
     [AC REAL_MUL_AC `a * b * c * d * e = b * c * d * a * e`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?N. !n k:num. N <= k /\ pi * abs(x) <= &2 pow (n + 1)
                          ==> abs(B n k) < e`
  ASSUME_TAC THENL
   [X_CHOOSE_TAC `Bd:real` COT_X_BOUND_LEMMA THEN
    SUBGOAL_THEN
     `!k n. &9 * abs x < &k
            ==> abs(sum(k + 1,2 EXP n - 1 - k)
                       (\m. (&72 * x pow 2) / (&m pow 2 - &36 * x pow 2)))
                <= &144 * x pow 2 / &k`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; SUM_CMUL] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_POW; REAL_POW2_ABS] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `&144 * x * y = &72 * x * &2 * y`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_LE_SQUARE; REAL_POW_2] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * sum(k + 1,2 EXP n - 1 - k) (\m. inv(&m * &m))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM SUM_CMUL] THEN
        W(fun (asl,w) -> MP_TAC(PART_MATCH lhand SUM_ABS_LE (lhand w))) THEN
        MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
        MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
        REWRITE_TAC[] THEN
        SUBGOAL_THEN `&0 < &r * &r - &36 * x * x` ASSUME_TAC THENL
         [REWRITE_TAC[GSYM REAL_POW_2] THEN
          ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
          REWRITE_TAC[REAL_POW_2] THEN
          REWRITE_TAC[REAL_ARITH
           `&0 < r * r - &36 * x * x <=> (&6 * x) * (&6 * x) < r * r`] THEN
          MATCH_MP_TAC REAL_LT_MUL2 THEN
          SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_ABS_POS] THEN
          MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&k` THEN
          ASM_REWRITE_TAC[REAL_ABS_NUM] THEN
          REWRITE_TAC[REAL_OF_NUM_LE] THEN
          ASM_SIMP_TAC[REAL_ARITH `&9 * abs(x) < a ==> &6 * abs(x) < a`] THEN
          UNDISCH_TAC `k + 1 <= r` THEN ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE; REAL_LE_INV_EQ] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
        REWRITE_TAC[real_div] THEN
        ONCE_REWRITE_TAC[AC REAL_MUL_AC `(a * b) * c = (a * c) * b`] THEN
        REWRITE_TAC[GSYM real_div] THEN
        SUBGOAL_THEN `&0 < &r` ASSUME_TAC THENL
         [UNDISCH_TAC `k + 1 <= r` THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
          ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL] THEN
        REWRITE_TAC[REAL_ARITH `&1 * x <= &2 * (x - y) <=> &2 * y <= x`] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= x /\ &81 * x <= y ==> &2 * &36 * x <= y`) THEN
        REWRITE_TAC[REAL_LE_SQUARE] THEN
        REWRITE_TAC[REAL_ARITH `&81 * x * x = (&9 * x) * (&9 * x)`] THEN
        REWRITE_TAC[GSYM REAL_POW_2] THEN
        ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
        REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&k` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        UNDISCH_TAC `k + 1 <= r` THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      REWRITE_TAC[SUM_REINDEX] THEN
      SUBGOAL_THEN `?d. k = 1 + d` (CHOOSE_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[GSYM LE_EXISTS] THEN
        MATCH_MP_TAC(ARITH_RULE `0 < k ==> 1 <= k`) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
        UNDISCH_TAC `&9 * abs(x) < &k` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SPEC_TAC(`2 EXP n - 1 - (1 + d)`,`n:num`) THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN GEN_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [ADD_SYM] THEN
      REWRITE_TAC[SUM_REINDEX] THEN
      REWRITE_TAC[ARITH_RULE `(r + 1) + 1 = r + 2`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(d,n) (\r. inv(&(r + 1) * &(r + 2)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE THEN REPEAT STRIP_TAC THEN
        SIMP_TAC[REAL_LE_RMUL_EQ; REAL_LT_INV_EQ; REAL_OF_NUM_LT;
                 REAL_INV_MUL; ARITH_RULE `0 < n + 2`] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!n. sum(d,n) (\r. inv (&(r + 1) * &(r + 2))) =
            inv(&(d + 1)) - inv(&(d + n + 1))`
       (fun th -> REWRITE_TAC[th])
      THENL
       [INDUCT_TAC THEN REWRITE_TAC[sum; ADD_CLAUSES; REAL_SUB_REFL] THEN
        ASM_REWRITE_TAC[REAL_ARITH
         `((a - x) + y = a - z) <=> (y + z = x)`] THEN
        REWRITE_TAC[GSYM ADD_ASSOC; REAL_INV_MUL;
          ARITH_RULE `SUC(d + n + 1) = d + n + 2`] THEN
        MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN
        EXISTS_TAC `&(d + n + 1) * &(d + n + 2)` THEN
        REWRITE_TAC[REAL_ARITH
         `(dn1' * dn2' + dn2') * (dn1 * dn2) =
          (dn1 * dn1' + dn1) * (dn2 * dn2')`] THEN
        SIMP_TAC[REAL_ENTIRE; REAL_MUL_RINV; REAL_OF_NUM_EQ;
                 ARITH_RULE `~(d + n + 1 = 0) /\ ~(d + n + 2 = 0)`] THEN
        SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV;
                 REAL_OF_NUM_EQ; ARITH_RULE `~(d + n + 1 = 0)`] THEN
        REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
        ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ADD_AC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x - y <= x`) THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]; ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?N. &9 * abs(x) + &1 <= &N /\
          (Bd * &144 * x pow 2) / e + &1 <= &N`
     (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC)
    THENL
     [X_CHOOSE_TAC `N1:num` (SPEC `&9 * abs(x) + &1` REAL_ARCH_SIMPLE) THEN
      X_CHOOSE_TAC `N2:num`
       (SPEC `(Bd * &144 * x pow 2) / e + &1` REAL_ARCH_SIMPLE) THEN
      EXISTS_TAC `N1 + N2:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      ASM_MESON_TAC[REAL_POS;
                    REAL_ARITH `a <= m /\ b <= n /\ &0 <= m /\ &0 <= n
                                ==> a <= m + n /\ b <= m + n`];
      ALL_TAC] THEN
    EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `k:num`] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC
     `abs((pi * x / &2 pow (n + 1)) * cot (pi * x / &2 pow (n + 1))) *
          sum(k + 1,2 EXP n - 1 - k)
              (\m. (&72 * x pow 2) / (&m pow 2 - &36 * x pow 2))` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `&N` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      UNDISCH_TAC `&9 * abs x + &1 <= &N` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `Bd * &144 * x pow 2 / &k` THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      REWRITE_TAC[GSYM real_div] THEN
      SUBGOAL_THEN `&0 < &k` (fun th -> SIMP_TAC[REAL_LT_LDIV_EQ; th]) THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&N` THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
        UNDISCH_TAC `&9 * abs x + &1 <= &N` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ] THEN
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&N` THEN
      ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC; REAL_OF_NUM_LE] THEN
      ASM_SIMP_TAC[REAL_ARITH `x + &1 <= y ==> x < y`]] THEN
    MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
    ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ABS_ABS] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[real_div; REAL_ENTIRE; REAL_LT_IMP_NZ; REAL_POW2_CLAUSES;
                   REAL_MUL_ASSOC; REAL_LT_INV_EQ; PI_POS] THEN
      SIMP_TAC[GSYM real_div; REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NUM] THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW2_CLAUSES; REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      SIMP_TAC[real_abs; REAL_LT_IMP_LE; PI_POS] THEN
      ASM_REWRITE_TAC[GSYM real_abs]; ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&N:real` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `&9 * abs x + &1 <= &N` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n k. k < 2 EXP n
          ==> ((pi * x) *
               (cot (pi * x / &2 pow n) / &2 pow n +
                sum (1,2 EXP n - 1)
                    (\k. cot(pi * (x + &k) / &2 pow (n + 1)) +
                         cot(pi * (x - &k) / &2 pow (n + 1))) /
                &2 pow (n + 1)) = A n k + B n k)`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    REWRITE_TAC[GSYM REAL_ADD_ASSOC; GSYM REAL_ADD_LDISTRIB] THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV o funpow 3 LAND_CONV)
      [ARITH_RULE `x = 0 + x`] THEN
    REWRITE_TAC[SUM_REINDEX] THEN
    ONCE_REWRITE_TAC
     [REWRITE_RULE[REAL_ARITH `(a = b - c) <=> (c + a = b)`] SUM_DIFF] THEN
    ASM_SIMP_TAC[ARITH_RULE `n < p ==> (n + p - 1 - n = p - 1)`] THEN
    GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV o funpow 3 LAND_CONV)
     [ARITH_RULE `x = 0 + x`] THEN
    REWRITE_TAC[SUM_REINDEX] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; GSYM REAL_ADD_LDISTRIB] THEN
    REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COT_HALF_KNOPP) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN DISCH_TAC THEN
  REWRITE_TAC[sums; SEQ] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  UNDISCH_TAC
   `!e. &0 < e
        ==> ?N. !n k:num. N <= k /\ pi * abs(x) <= &2 pow (n + 1)
                          ==> abs (B n k) < e` THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N1 + 1` THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[GE] THEN DISCH_TAC THEN
  UNDISCH_TAC
   `!k. (\n. A n k) tends_num_real
           &1 + sum (1,k) (\n. (&2 * x pow 2) / (x pow 2 - &n pow 2))` THEN
  DISCH_THEN(MP_TAC o SPEC `n - 1`) THEN REWRITE_TAC[SEQ] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN REWRITE_TAC[GE] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?m. n - 1 < 2 EXP m /\ N2 <= m /\ pi * abs(x) <= &2 pow (m + 1)`
  MP_TAC THENL
   [SUBGOAL_THEN `?m. &(n - 1) + &1 <= &m /\ &N2 <= &m /\ pi * abs(x) <= &m`
    MP_TAC THENL
     [X_CHOOSE_TAC `m1:num` (SPEC `&(n - 1) + &1` REAL_ARCH_SIMPLE) THEN
      X_CHOOSE_TAC `m2:num` (SPEC `&N2` REAL_ARCH_SIMPLE) THEN
      X_CHOOSE_TAC `m3:num` (SPEC `pi * abs(x)` REAL_ARCH_SIMPLE) THEN
      EXISTS_TAC `m1 + m2 + m3:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      MATCH_MP_TAC(REAL_ARITH
       `x <= a /\ y <= b /\ z <= c /\ &0 <= a /\ &0 <= b /\ &0 <= c
        ==> x <= a + b + c /\ y <= a + b + c /\ z <= a + b + c`) THEN
      ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN
    MATCH_MP_TAC(REAL_ARITH
     `m <= m2 /\ m2 <= m22
      ==> x1 + &1 <= m /\ x2 <= m /\ x3 <= m
          ==> x1 < m2 /\ x2 <= m /\ x3 <= m22`) THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
    REWRITE_TAC[REAL_ARITH `x <= x * &2 <=> &0 <= x`] THEN
    REWRITE_TAC[REAL_POW2_CLAUSES] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_POW] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    SPEC_TAC(`m:num`,`n:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[EXP; ARITH] THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `SUC(2 EXP n)` THEN
    ASM_REWRITE_TAC[LT_SUC] THEN REWRITE_TAC[MULT_2; ADD1; LE_ADD_LCANCEL] THEN
    REWRITE_TAC[num_CONV `1`; LE_SUC_LT; EXP_LT_0; ARITH_EQ]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e / &2 + e / &2` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[REAL_LE_REFL; GSYM REAL_MUL_2; REAL_DIV_LMUL;
             REAL_OF_NUM_EQ; ARITH_EQ]] THEN
  UNDISCH_TAC
   `!n k. k < 2 EXP n ==> ((pi * x) * cot (pi * x) = A n k + B n k)` THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num`; `n - 1`]) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(b) < e /\ abs((s - &1) - a) < e
    ==> abs(s - ((a + b) + &1)) < e + e`) THEN
  CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `N1 + 1 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (0,n) (\r. (&2 * x pow 2) / (x pow 2 - &r pow 2)) - &1 =
    &1 + sum(1,n-1) (\r. (&2 * x pow 2) / (x pow 2 - &r pow 2))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `n = 1 + (n - 1)`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
    THENL
     [UNDISCH_TAC `N1 + 1 <= n` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM(REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_DIFF)] THEN
    MATCH_MP_TAC(REAL_ARITH `(a = &2) ==> ((x + a) - &1 = &1 + x)`) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
    REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN REWRITE_TAC[real_div] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_DIV_REFL; REAL_POW_EQ_0] THEN
    REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Expansion of each term as a power series.                                 *)
(* ------------------------------------------------------------------------- *)

let COT_PARTIAL_FRACTIONS_SUBTERM = prove
 (`abs(x) < &n
   ==> (\k. --(&2) * (x pow 2 / &n pow 2) pow (k + 1))
       sums ((&2 * x pow 2) / (x pow 2 - &n pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [UNDISCH_TAC `abs(x) < &n` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\k. (x pow 2 / &n pow 2) pow k) sums
    inv(&1 - (x pow 2 / &n pow 2))`
  MP_TAC THENL
   [MATCH_MP_TAC GP THEN
    REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_POW_LT; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_POW_LT2; REAL_ABS_POS; ARITH_EQ]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o
    SPEC `--(&2) * (x pow 2 / &n pow 2)` o MATCH_MP SER_CMUL) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM(CONJUNCT2 real_pow)] THEN
    REWRITE_TAC[ADD1]; ALL_TAC] THEN
  REWRITE_TAC[real_div; GSYM REAL_INV_MUL;
              GSYM REAL_MUL_ASSOC; REAL_MUL_LNEG] THEN
  REWRITE_TAC[GSYM REAL_MUL_RNEG; GSYM REAL_INV_NEG] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_NEG_SUB; REAL_SUB_LDISTRIB; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_DIV_LMUL; REAL_POW_LT; REAL_LT_IMP_NZ]);;

(* ------------------------------------------------------------------------- *)
(* General theorem about swapping a double series of positive terms.         *)
(* ------------------------------------------------------------------------- *)

let SEQ_LE_CONST = prove
 (`!a x l N. (!n. n >= N ==> x(n) <= a) /\ x tends_num_real l ==> l <= a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SEQ_LE THEN
  MAP_EVERY EXISTS_TAC [`x:num->real`; `\n:num. a:real`] THEN
  ASM_REWRITE_TAC[SEQ_CONST] THEN ASM_MESON_TAC[]);;

let SEQ_GE_CONST = prove
 (`!a x l N. (!n. n >= N ==> a <= x(n)) /\ x tends_num_real l ==> a <= l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SEQ_LE THEN
  MAP_EVERY EXISTS_TAC [`\n:num. a:real`; `x:num->real`] THEN
  ASM_REWRITE_TAC[SEQ_CONST] THEN ASM_MESON_TAC[]);;

let SUM_SWAP_0 = prove
 (`!m n. sum(0,m) (\i. sum(0,n) (\j. a i j)) =
         sum(0,n) (\j. sum(0,m) (\i. a i j))`,
  INDUCT_TAC THEN
  ASM_SIMP_TAC[sum; SUM_CONST; REAL_MUL_RZERO; SUM_ADD]);;

let SUM_SWAP = prove
 (`!m1 m2 n1 n2.
        sum(m1,m2) (\i. sum(n1,n2) (\j. a i j)) =
        sum(n1,n2) (\j. sum(m1,m2) (\i. a i j))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV)
    [ARITH_RULE `m = 0 + m`] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV)
    [ARITH_RULE `m = 0 + m`] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINDER_CONV o LAND_CONV o LAND_CONV)
    [ARITH_RULE `m = 0 + m`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o BINDER_CONV o LAND_CONV o LAND_CONV)
    [ARITH_RULE `m = 0 + m`] THEN
  REWRITE_TAC[SUM_REINDEX; SUM_SWAP_0]);;

let SER_SWAPDOUBLE_POS = prove
 (`!z a l. (!m n. &0 <= a m n) /\ (!m. (a m) sums (z m)) /\ z sums l
           ==> ?s. (!n. (\m. a m n) sums (s n)) /\ s sums l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!m:num n. sum(0,n) (a m) <= z m` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SEQ_GE_CONST THEN
    EXISTS_TAC `\n. sum(0,n) (a(m:num))` THEN
    ASM_REWRITE_TAC[GSYM sums] THEN
    EXISTS_TAC `n:num` THEN X_GEN_TAC `p:num` THEN
    SIMP_TAC[GE; LEFT_IMP_EXISTS_THM; LE_EXISTS] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
    ASM_SIMP_TAC[GSYM SUM_DIFF; SUM_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `!m:num. &0 <= z m` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0,n) (a(m:num))` THEN
    ASM_SIMP_TAC[SUM_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. sum(0,n) z <= l` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SEQ_GE_CONST THEN
    EXISTS_TAC `\n. sum(0,n) z` THEN
    ASM_REWRITE_TAC[GSYM sums] THEN
    EXISTS_TAC `n:num` THEN X_GEN_TAC `p:num` THEN
    SIMP_TAC[GE; LEFT_IMP_EXISTS_THM; LE_EXISTS] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
    ASM_SIMP_TAC[GSYM SUM_DIFF; SUM_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= l` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0,n) z` THEN
    ASM_SIMP_TAC[SUM_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?M N. !m n. M <= m /\ N <= n ==>
                        l - e <= sum(0,m) (\i. sum(0,n) (\j. a i j)) /\
                        sum(0,m) (\i. sum(0,n) (\j. a i j)) <= l`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN UNDISCH_TAC `z sums l` THEN
    REWRITE_TAC[sums; SEQ] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; GE; REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
    SUBGOAL_THEN
     `?N. !m n. m < M /\ n >= N
                ==> abs(sum (0,n) (a m) - z m) < e / (&2 * &(M + 1))`
    MP_TAC THENL
     [SUBGOAL_THEN `&0 < e / (&2 * &(M + 1))` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; REAL_LT_MUL; ARITH;
                     ARITH_RULE `0 < n + 1`]; ALL_TAC] THEN
      SPEC_TAC(`e / (&2 * &(M + 1))`,`d:real`) THEN
      SPEC_TAC(`M:num`,`n:num`) THEN
      GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
      REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
      GEN_TAC THEN DISCH_TAC THEN
      INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN
      UNDISCH_TAC `!m:num. (a m) sums (z m)` THEN
      DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
      REWRITE_TAC[sums; SEQ] THEN
      DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
      FIRST_X_ASSUM(X_CHOOSE_TAC `N1:num`) THEN
      EXISTS_TAC `N0 + N1:num` THEN
      X_GEN_TAC `m:num` THEN X_GEN_TAC `p:num` THEN
      REWRITE_TAC[LT] THEN
      ASM_MESON_TAC[ARITH_RULE `a >= m + n ==> a >= m /\ a >= n:num`];
      ALL_TAC] THEN
    REWRITE_TAC[GE] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    MAP_EVERY EXISTS_TAC [`M:num`; `N:num`] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `!s0. s0 <= s /\ s <= l /\ abs(s0 - l) < e
           ==> l - e <= s /\ s <= l`) THEN
    EXISTS_TAC `sum(0,M) (\i. sum (0,n) (\j. a i j))` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `M <= m:num` THEN
      SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
      ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
      REWRITE_TAC[GSYM SUM_DIFF] THEN ASM_SIMP_TAC[SUM_POS]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum (0,m) z` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUM_LE THEN
      CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e / &2 + e / &2` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      SIMP_TAC[REAL_LE_REFL; GSYM REAL_MUL_2; REAL_DIV_LMUL;
               REAL_OF_NUM_EQ; ARITH_EQ]] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!z. abs(x - z) <= e /\ abs(z - y) < e ==> abs(x - y) < e + e`) THEN
    EXISTS_TAC `sum(0,M) z` THEN ASM_SIMP_TAC[LE_REFL] THEN
    REWRITE_TAC[GSYM SUM_SUB] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&M * e / (&2 * &(M + 1))` THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[real_div; REAL_INV_MUL] THEN
      ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c * d = (b * c) * a * d`] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_INV_EQ; REAL_POS] THEN
      SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
               ARITH_RULE `0 < n + 1`] THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE; LE_ADD]] THEN
    W(fun (asl,w) -> MP_TAC(PART_MATCH lhand SUM_ABS_LE (lhand w))) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0,M) (\n. e / (&2 * &(M + 1)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
      ASM_SIMP_TAC[ADD_CLAUSES; REAL_LT_IMP_LE];
      REWRITE_TAC[SUM_CONST; REAL_LE_REFL]]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. sum(0,m) (\i. (a:num->num->real) i n) <= l`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0,M+m) (\i. sum(0,N+n+1) (\j. a i j))` THEN
    ASM_SIMP_TAC[LE_ADD] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    ONCE_REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_DIFF)] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y /\ &0 <= z ==> x <= z + y`) THEN
    ASM_SIMP_TAC[SUM_POS] THEN MATCH_MP_TAC SUM_LE THEN
    X_GEN_TAC `r:num` THEN DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_DIFF)] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y /\ &0 <= z ==> x <= y + z`) THEN
    ASM_SIMP_TAC[SUM_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(n,1) (\j. a (r:num) j)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_1; REAL_LE_REFL]; ALL_TAC] THEN
    SUBST1_TAC(ARITH_RULE `n = 0 + n`) THEN REWRITE_TAC[SUM_REINDEX] THEN
    ONCE_REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_DIFF)] THEN
    ASM_SIMP_TAC[SUM_POS; REAL_LE_ADDL]; ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. ?s. (\m. a m n) sums s` MP_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[sums; GSYM convergent] THEN
    MATCH_MP_TAC SEQ_BCONV THEN CONJ_TAC THENL
     [MATCH_MP_TAC SEQ_BOUNDED_2 THEN
      MAP_EVERY EXISTS_TAC [`&0`; `l:real`] THEN ASM_SIMP_TAC[SUM_POS];
      REWRITE_TAC[mono] THEN DISJ1_TAC THEN
      SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
      REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_DIFF)] THEN
      ASM_SIMP_TAC[SUM_POS; REAL_LE_ADDL]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `s:num->real` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?N. !n. N <= n
                    ==> l - e <= sum (0,n) s /\ sum(0,n) s <= l`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN
    ONCE_REWRITE_TAC[SUM_SWAP_0] THEN DISCH_TAC THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `!s0. l - e <= s0 /\ s0 <= s ==> l - e <= s`) THEN
      EXISTS_TAC `sum (0,n) (\j. sum (0,M) (\i. a i j))` THEN
      ASM_SIMP_TAC[LE_REFL] THEN MATCH_MP_TAC SUM_LE THEN
      X_GEN_TAC `r:num` THEN DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SEQ_GE_CONST THEN
      EXISTS_TAC `\m. sum(0,m) (\m. a m (r:num))` THEN
      EXISTS_TAC `M:num` THEN ASM_REWRITE_TAC[GSYM sums] THEN
      SIMP_TAC[GE; LEFT_IMP_EXISTS_THM; LE_EXISTS] THEN
      ONCE_REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_DIFF)] THEN
      ASM_SIMP_TAC[SUM_POS; REAL_LE_ADDL]; ALL_TAC] THEN
    MATCH_MP_TAC SEQ_LE_CONST THEN
    EXISTS_TAC `\m. sum (0,n) (\j. sum (0,m) (\i. a i j))` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `0` THEN CONJ_TAC THENL
     [X_GEN_TAC `m:num` THEN DISCH_THEN(K ALL_TAC) THEN
      ONCE_REWRITE_TAC[SUM_SWAP_0] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0,m) z` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SEQ_SUM THEN X_GEN_TAC `m:num` THEN
    ASM_REWRITE_TAC[GSYM sums]; ALL_TAC] THEN
  REWRITE_TAC[sums; SEQ] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  UNDISCH_TAC
   `!e. &0 < e
        ==> (?N. !n. N <= n ==> l - e <= sum (0,n) s /\ sum (0,n) s <= l)` THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[GE] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> b ==> c) ==> (a ==> b) ==> (a ==> c)`) THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `d < e ==> l - d <= x /\ x <= l ==> abs(x - l) < e`) THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hence we get a power series for cot with nice convergence property.       *)
(* ------------------------------------------------------------------------- *)

let COT_PARTIAL_FRACTIONS_FROM1 = prove
 (`~integer x
    ==> (\n. (&2 * x pow 2) / (x pow 2 - &(n + 1) pow 2)) sums
        (pi * x) * cot (pi * x) - &1`,
  DISCH_TAC THEN
  SUBGOAL_THEN `~(x = &0)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(integer x)` THEN
    REWRITE_TAC[TAUT `(~b ==> ~a) <=> (a ==> b)`] THEN
    SIMP_TAC[integer; REAL_ABS_NUM; REAL_OF_NUM_EQ; GSYM EXISTS_REFL];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COT_PARTIAL_FRACTIONS) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP SER_OFFSET) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP SUM_UNIQ) THEN
  MATCH_MP_TAC EQ_IMP THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN REWRITE_TAC[SUM_1] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `(a * b * b) * c = a * (b * b) * c`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_ENTIRE; REAL_MUL_RID] THEN
  REAL_ARITH_TAC);;

let COT_ALT_POWSER = prove
 (`!x. &0 < abs(x) /\ abs(x) < &1
       ==> ?s. (!n. (\m. &2 * (x pow 2 / &(m + 1) pow 2) pow (n + 1))
                    sums s n) /\
               s sums --((pi * x) * cot(pi * x) - &1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SER_SWAPDOUBLE_POS THEN
  EXISTS_TAC `\n. (--(&2) * x pow 2) / (x pow 2 - &(n + 1) pow 2)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[REAL_POS; REAL_POW_LE; REAL_LE_MUL;
             REAL_POW_2; REAL_LE_DIV; REAL_LE_SQUARE];
    X_GEN_TAC `m:num` THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o LAND_CONV)
     [GSYM REAL_NEG_NEG] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN
    MATCH_MP_TAC SER_NEG THEN
    REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
    REWRITE_TAC[GSYM real_div] THEN
    MATCH_MP_TAC COT_PARTIAL_FRACTIONS_SUBTERM THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN
    MATCH_MP_TAC SER_NEG THEN
    REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
    REWRITE_TAC[GSYM real_div] THEN
    MATCH_MP_TAC COT_PARTIAL_FRACTIONS_FROM1 THEN
    UNDISCH_TAC `&0 < abs x` THEN UNDISCH_TAC `abs x < &1` THEN
    ONCE_REWRITE_TAC[TAUT `a ==> b ==> ~c <=> c ==> ~(a /\ b)`] THEN
    SIMP_TAC[integer; LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* General unpairing result.                                                 *)
(* ------------------------------------------------------------------------- *)

let SER_INSERTZEROS = prove
 (`(\n. c(2 * n)) sums l
   ==> (\n. if ODD n then &0 else c(n)) sums l`,
  REWRITE_TAC[sums; SEQ; GE] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `2 * N` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  DISJ_CASES_THEN MP_TAC (SPEC `n:num` EVEN_OR_ODD) THENL
   [REWRITE_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `m:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] (GSYM SUM_GROUP)] THEN
    REWRITE_TAC[SUM_2; ODD_ADD; ODD_MULT; ARITH_ODD; REAL_ADD_RID] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `2 * N <= 2 * m` THEN ARITH_TAC;
    REWRITE_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `m:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[GSYM ODD_EXISTS] THEN REWRITE_TAC[sum] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] (GSYM SUM_GROUP)] THEN
    REWRITE_TAC[SUM_2; ODD_ADD; ODD_MULT; ARITH_ODD; REAL_ADD_RID] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `0 + 2 * m = 2 * (0 + m)`] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 sum)] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `2 * N <= SUC(2 * m)` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Mangle this into a standard power series.                                 *)
(* ------------------------------------------------------------------------- *)

let COT_POWSER_SQUARED_FORM = prove
 (`!x. &0 < abs(x) /\ abs(x) < pi
       ==> (\n. &2 * (x / pi) pow (2 * (n + 1)) *
                suminf (\m. inv (&(m + 1) pow (2 * (n + 1)))))
           sums --(x * cot x - &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x / pi` COT_ALT_POWSER) THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN
  SIMP_TAC[real_abs; REAL_LT_IMP_LE; PI_POS] THEN
  REWRITE_TAC[GSYM real_abs] THEN
  SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ; PI_POS] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
  SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; PI_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `s sums --(x * cot(x) - &1)` THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SER_CMUL o SPEC `n:num`) THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&2 * (x / pi) pow (2 * (n + 1)))`) THEN
  REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ABS_CONV o
                   RAND_CONV o ONCE_DEPTH_CONV)
      [REAL_POW_DIV] THEN
  REWRITE_TAC[REAL_POW_POW] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ABS_CONV o
                   RAND_CONV o ONCE_DEPTH_CONV)
      [real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `a * &2 * b * c = c * ((&2 * b) * a)`] THEN
  SUBGOAL_THEN
   `~(&2 * (x / pi) pow (2 * (n + 1)) = &0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH_EQ; REAL_POW_EQ_0] THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN DISJ1_TAC THEN
    REWRITE_TAC[real_div; REAL_ENTIRE; REAL_INV_EQ_0] THEN
    ASM_SIMP_TAC[PI_POS; REAL_LT_IMP_NZ;
                 snd(EQ_IMP_RULE(SPEC_ALL REAL_ABS_NZ))];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_UNIQ) THEN
  DISCH_THEN(MP_TAC o AP_TERM `( * ) (&2 * (x / pi) pow (2 * (n + 1)))`) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
   [AC REAL_MUL_AC `a * b * c = (a * b) * c`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC]);;

let COT_POWSER_SQUAREDAGAIN = prove
 (`!x. &0 < abs(x) /\ abs(x) < pi
       ==> (\n. (if n = 0 then &1
                 else --(&2) *
                      suminf (\m. inv (&(m + 1) pow (2 * n))) /
                      pi pow (2 * n)) *
                x pow (2 * n))
           sums (x * cot(x))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COT_POWSER_SQUARED_FORM) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\n. if n = 0 then &1 else
         --(&2 * (x / pi) pow (2 * n) *
                 suminf (\m. inv (&(m + 1) pow (2 * n)))))
    sums (sum(0,1) (\n. if n = 0 then &1 else
                        --(&2 * (x / pi) pow (2 * n) *
                           suminf (\m. inv (&(m + 1) pow (2 * n))))) +
          suminf (\n. if n + 1 = 0 then &1 else
                        --(&2 * (x / pi) pow (2 * (n + 1)) *
                           suminf (\m. inv (&(m + 1) pow (2 * (n + 1)))))))`
  MP_TAC THENL
   [MATCH_MP_TAC SER_OFFSET_REV THEN
    REWRITE_TAC[ARITH_RULE `~(n + 1 = 0)`] THEN
    REWRITE_TAC[summable] THEN
    EXISTS_TAC `x * cot(x) - &1` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUM_1; ARITH_RULE `~(n + 1 = 0)`] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP SUM_UNIQ) THEN
  REWRITE_TAC[REAL_ARITH `&1 + x - &1 = x`] THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; real_pow; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_POW_DIV; REAL_MUL_LNEG] THEN AP_TERM_TAC THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let COT_X_POWSER = prove
 (`!x. &0 < abs(x) /\ abs(x) < pi
       ==> (\n. (if n = 0 then &1 else if ODD n then &0 else
                 --(&2) * suminf (\m. inv (&(m + 1) pow n)) / pi pow n) *
                x pow n)
           sums (x * cot(x))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COT_POWSER_SQUAREDAGAIN) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [ARITH_RULE `(n = 0) <=> (2 * n = 0)`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_INSERTZEROS) THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ARITH] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO]);;

(* ------------------------------------------------------------------------- *)
(* Hence use the double-angle formula to get a series for tangent.           *)
(* ------------------------------------------------------------------------- *)

let TAN_COT_DOUBLE = prove
 (`!x. &0 < abs(x) /\ abs(x) < pi / &2
        ==> (tan(x) = cot(x) - &2 * cot(&2 * x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(sin x = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[SIN_ZERO] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    REWRITE_TAC[OR_EXISTS_THM] THEN
    REWRITE_TAC[TAUT `a /\ b \/ a /\ c <=> a /\ (b \/ c)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `(x = a) \/ (x = --a) ==> &0 <= a ==> (abs(x) = a)`)) THEN
    SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LT_IMP_LE; PI_POS; REAL_POS] THEN
    DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
    ASM_CASES_TAC `m = 0` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; REAL_MUL_LZERO; REAL_LT_REFL] THEN
    DISJ1_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_ARITH `x = &1 * x`] THEN
    SIMP_TAC[REAL_LT_RMUL_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; PI_POS] THEN
    UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(cos x = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[COS_ZERO] THEN
    MAP_EVERY UNDISCH_TAC [`abs x < pi / &2`; `&0 < abs x`] THEN
    REWRITE_TAC[IMP_IMP] THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    REWRITE_TAC[OR_EXISTS_THM; NOT_EVEN] THEN
    REWRITE_TAC[TAUT `a /\ b \/ a /\ c <=> a /\ (b \/ c)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `(x = a) \/ (x = --a) ==> &0 <= a ==> (abs(x) = a)`)) THEN
    SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LT_IMP_LE; PI_POS; REAL_POS] THEN
    DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
    DISJ2_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_ARITH `x = &1 * x`] THEN
    SIMP_TAC[REAL_LT_RMUL_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; PI_POS] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(sin(&2 * x) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[SIN_ZERO] THEN
    MAP_EVERY UNDISCH_TAC [`abs x < pi / &2`; `&0 < abs x`] THEN
    REWRITE_TAC[IMP_IMP] THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    REWRITE_TAC[OR_EXISTS_THM] THEN
    REWRITE_TAC[TAUT `a /\ b \/ a /\ c <=> a /\ (b \/ c)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `(x = a) \/ (x = --a) ==> &0 <= a ==> (abs(x) = a)`)) THEN
    SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LT_IMP_LE; PI_POS; REAL_POS] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_EQ_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
    ASM_CASES_TAC `m = 0` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; REAL_MUL_LZERO; REAL_LT_REFL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISJ2_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC `(a * b) * c = b * a * c`] THEN
    SIMP_TAC[REAL_LT_DIV2_EQ; REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH;
             REAL_OF_NUM_LT] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_ARITH `x = &1 * x`] THEN
    SIMP_TAC[REAL_LT_RMUL_EQ; PI_POS; REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[tan; cot] THEN
  MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN
  EXISTS_TAC `sin(&2 * x)` THEN ASM_REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(d * e - &2 * f * g) * h = h * d * e - &2 * f * (h * g)`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC `sin(x)` THEN
  ASM_SIMP_TAC[REAL_SUB_RDISTRIB; GSYM REAL_MUL_ASSOC;
               REAL_MUL_LINV; REAL_MUL_RID] THEN
  GEN_REWRITE_TAC LAND_CONV
   [AC REAL_MUL_AC `a * b * c * d = a * c * d * b`] THEN
  MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC `cos(x)` THEN
  ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RID] THEN
  REWRITE_TAC[SIN_DOUBLE; COS_DOUBLE; REAL_POW_2] THEN
  REWRITE_TAC[REAL_ARITH
   `((&2 * s * c) * c - &2 * (c * c - s * s) * s) * c =
    &2 * c * s * s * s`] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let TAN_POWSER_WEAK = prove
 (`!x. &0 < abs(x) /\ abs(x) < pi / &2
       ==> (\n. (if EVEN n then &0 else
                 &2 * (&2 pow (n + 1) - &1) *
                 suminf (\m. inv (&(m + 1) pow (n + 1))) / pi pow (n + 1)) *
                x pow n)
           sums (tan x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real` COT_X_POWSER) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `pi / &2` THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(x)` o MATCH_MP SER_CMUL) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_ABS_NZ; REAL_MUL_LID] THEN
  MP_TAC(SPEC `&2 * x` COT_X_POWSER) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ABS_NUM;
                 REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(x)` o MATCH_MP SER_CMUL) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
   [AC REAL_MUL_AC `a * (b * c) * d = (a * c) * b * d`] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_ABS_NZ; REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_SUB) THEN
  ASM_SIMP_TAC[GSYM TAN_COT_DOUBLE] THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(ASSUME_TAC o SYM o MATCH_MP SUM_UNIQ) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP SER_OFFSET) THEN
  ASM_REWRITE_TAC[SUM_1] THEN
  REWRITE_TAC[real_pow; REAL_MUL_RID; REAL_SUB_REFL; REAL_SUB_RZERO] THEN
  REWRITE_TAC[ODD_ADD; ARITH_ODD; ADD_EQ_0; ARITH_EQ] THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[NOT_ODD] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_SUB_REFL] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_POW_MUL; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `x' * m2 * s * xp * x - x' * m2 * s * pn * t * xp * x =
    (x' * x) * --m2 * (t * pn - &1) * s * xp`] THEN
  ASM_SIMP_TAC[REAL_NEG_NEG; REAL_MUL_LINV; REAL_ABS_NZ; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let TAN_POWSER = prove
 (`!x. abs(x) < pi / &2
       ==> (\n. (if EVEN n then &0 else
                 &2 * (&2 pow (n + 1) - &1) *
                 suminf (\m. inv (&(m + 1) pow (n + 1))) / pi pow (n + 1)) *
                x pow n)
           sums (tan x)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `&0 < abs(x)` THEN ASM_SIMP_TAC[TAN_POWSER_WEAK] THEN
  DISCH_THEN(K ALL_TAC) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[TAN_0] THEN
  W(fun (asl,w) -> MP_TAC(SPECL [lhand w; `0`] SER_0)) THEN
  REWRITE_TAC[sum] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `EVEN n` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  UNDISCH_TAC `~(EVEN n)` THEN
  REWRITE_TAC[NOT_EVEN; ODD_EXISTS; real_pow; LEFT_IMP_EXISTS_THM] THEN
  SIMP_TAC[real_pow; REAL_MUL_LZERO; REAL_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Add polynomials to differentiator's known functions, for next proofs.     *)
(* ------------------------------------------------------------------------- *)

let th = prove
 (`(f diffl l)(x) ==>
    ((\x. poly p (f x)) diffl (l * poly (poly_diff p) (f x)))(x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MP_TAC(SPECL [`\x. poly p x`; `f:real->real`;
                `poly (poly_diff p) (f(x:real))`;
                `l:real`; `x:real`] DIFF_CHAIN) THEN
  ASM_REWRITE_TAC[POLY_DIFF]) in
add_to_diff_net th;;

(* ------------------------------------------------------------------------- *)
(* Main recurrence relation.                                                 *)
(* ------------------------------------------------------------------------- *)

let DIFF_CHAIN_TAN = prove
 (`~(cos x = &0)
   ==> ((\x. poly p (tan x)) diffl
        (poly ([&1; &0; &1] ** poly_diff p) (tan x))) (x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tan] THEN
  W(MP_TAC o SPEC `x:real` o DIFF_CONV o lhand o rator o snd) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[POLY_MUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[poly; REAL_MUL_RID; REAL_MUL_RZERO; REAL_ADD_RID;
              REAL_ADD_LID] THEN
  REWRITE_TAC[REAL_ARITH `a - --s * s = (s * s + a)`] THEN
  REWRITE_TAC[GSYM REAL_POW_2; SIN_CIRCLE] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_POW2_ABS] THEN
  ASM_SIMP_TAC[REAL_POW_LT; GSYM REAL_ABS_NZ; REAL_EQ_LDIV_EQ] THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM REAL_POW_MUL] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[SIN_CIRCLE]);;

(* ------------------------------------------------------------------------- *)
(* Define tangent polynomials and tangent numbers on this pattern.           *)
(* ------------------------------------------------------------------------- *)

let tanpoly = new_recursive_definition num_RECURSION
  `(tanpoly 0 = [&0; &1]) /\
   (!n. tanpoly (SUC n) = [&1; &0; &1] ** poly_diff(tanpoly n))`;;

let TANPOLYS_RULE =
  let pth1,pth2 = CONJ_PAIR tanpoly in
  let base = [pth1]
  and rule = GEN_REWRITE_RULE LAND_CONV [GSYM pth2] in
  let poly_diff_tm = `poly_diff`
  and poly_mul_tm = `( ** ) [&1; &0; &1]` in
  let rec tanpolys n =
    if n < 0 then []
    else if n = 0 then base else
    let thl = tanpolys (n - 1) in
    let th1 = AP_TERM poly_diff_tm (hd thl) in
    let th2 = TRANS th1 (POLY_DIFF_CONV (rand(concl th1))) in
    let th3 = AP_TERM poly_mul_tm th2 in
    let th4 = TRANS th3 (POLY_MUL_CONV (rand(concl th3))) in
    let th5 = rule th4 in
    let th6 = CONV_RULE (LAND_CONV(RAND_CONV NUM_SUC_CONV)) th5 in
    th6::thl in
  rev o tanpolys;;

let TANPOLY_CONV =
  let tanpoly_tm = `tanpoly` in
  fun tm ->
    let l,r = dest_comb tm in
    if l <> tanpoly_tm then failwith "TANPOLY_CONV"
    else last(TANPOLYS_RULE(dest_small_numeral r));;

let tannumber = new_definition
  `tannumber n = poly (tanpoly n) (&0)`;;

let TANNUMBERS_RULE,TANNUMBER_CONV =
  let POLY_0_THM = prove
   (`(poly [] (&0) = &0) /\
     (poly (CONS h t) (&0) = h)`,
    REWRITE_TAC[poly; REAL_MUL_LZERO; REAL_ADD_RID]) in
  let poly_tm = `poly`
  and zero_tm = `&0`
  and tannumber_tm = `tannumber`
  and depoly_conv = GEN_REWRITE_CONV I [POLY_0_THM]
  and tannumber_rule = GEN_REWRITE_RULE LAND_CONV [GSYM tannumber] in
  let process th =
    let th1 = AP_THM (AP_TERM poly_tm th) zero_tm in
    let th2 = TRANS th1 (depoly_conv (rand(concl th1))) in
    let th3 = tannumber_rule th2 in
    th3 in
  let TANNUMBERS_RULE = map process o TANPOLYS_RULE
  and TANNUMBER_CONV tm =
    let l,r = dest_comb tm in
    if l <> tannumber_tm then failwith "TANNUMBER_CONV" else
    process(last(TANPOLYS_RULE(dest_small_numeral r))) in
  TANNUMBERS_RULE,TANNUMBER_CONV;;

(* ------------------------------------------------------------------------- *)
(* Chaining rules using the tangent polynomials.                             *)
(* ------------------------------------------------------------------------- *)

let DIFF_CHAIN_TAN_TANPOLYS = prove
 (`~(cos x = &0)
   ==> ((\x. poly (tanpoly n) (tan x)) diffl
        (poly (tanpoly(SUC n)) (tan x))) (x)`,
  REWRITE_TAC[tanpoly; DIFF_CHAIN_TAN]);;

let th = prove
 (`(f diffl l)(x) /\ ~(cos(f x) = &0)
   ==> ((\x. poly (tanpoly n) (tan(f x))) diffl
        (l * poly (tanpoly(SUC n)) (tan(f x))))(x)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MP_TAC(SPECL [`\x. poly (tanpoly n) (tan x)`; `f:real->real`;
                `poly (tanpoly(SUC n)) (tan(f(x:real)))`;
                `l:real`; `x:real`] DIFF_CHAIN) THEN
  ASM_SIMP_TAC[DIFF_CHAIN_TAN_TANPOLYS]) in
add_to_diff_net th;;

(* ------------------------------------------------------------------------- *)
(* Hence rewrite coefficients of tan and cot series in terms of tannumbers.  *)
(* ------------------------------------------------------------------------- *)

let TERMDIFF_ALT = prove
 (`!f f' c k.
        (!x. abs(x) < k ==> (\n. c(n) * x pow n) sums f(x))
        ==> (!x. abs(x) < k ==> (f diffl f'(x))(x))
            ==> (!x. abs(x) < k ==> (\n. (diffs c)(n) * x pow n) sums f'(x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `summable (\n. diffs c n * x pow n) /\
    (f'(x) = suminf (\n. diffs c n * x pow n))`
  MP_TAC THENL
   [ALL_TAC; SIMP_TAC[SUMMABLE_SUM]] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `abs(x) < k` THEN SPEC_TAC(`x:real`,`x:real`) THEN
    MATCH_MP_TAC TERMDIFF_CONVERGES THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[summable] THEN
    EXISTS_TAC `(f:real->real) x` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  MATCH_MP_TAC DIFF_LCONST THEN
  EXISTS_TAC `\x. f x - suminf (\n. c(n) * x pow n)` THEN
  EXISTS_TAC `x:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIFF_SUB THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC TERMDIFF_STRONG THEN
    EXISTS_TAC `(abs(x) + k) / &2` THEN CONJ_TAC THENL
     [REWRITE_TAC[summable] THEN
      EXISTS_TAC `(f:real->real)((abs(x) + k) / &2)` THEN
      FIRST_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_LT_LDIV_EQ;
             REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    UNDISCH_TAC `abs(x) < k` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `k - abs(x)` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  X_GEN_TAC `y:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `(a = b) /\ (c = d) ==> (a - b = c - d)`) THEN
  CONJ_TAC THEN MATCH_MP_TAC SUM_UNIQ THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `abs(x - y) < k - abs(x)` THEN REAL_ARITH_TAC);;

let TAN_DERIV_POWSER = prove
 (`!n x. abs(x) < pi / &2
         ==> (\m. ITER n diffs
                   (\i. if EVEN i
                        then &0
                        else &2 *
                             (&2 pow (i + 1) - &1) *
                             suminf (\m. inv (&(m + 1) pow (i + 1))) /
                             pi pow (i + 1)) m *
                  x pow m)
             sums (poly (tanpoly n) (tan x))`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[ITER; tanpoly; poly] THEN
    REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID; REAL_MUL_RZERO; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[TAN_POWSER]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP TERMDIFF_ALT) THEN
  REWRITE_TAC[ITER] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC DIFF_CHAIN_TAN_TANPOLYS THEN
  REWRITE_TAC[COS_ZERO] THEN
  UNDISCH_TAC `abs x < pi / &2` THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
  REWRITE_TAC[OR_EXISTS_THM; NOT_EVEN] THEN
  REWRITE_TAC[TAUT `a /\ b \/ a /\ c <=> a /\ (b \/ c)`] THEN
  DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `(x = a) \/ (x = --a) ==> &0 <= a ==> (abs(x) = a)`)) THEN
  SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LT_IMP_LE; PI_POS; REAL_POS] THEN
  DISCH_THEN(K ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_ARITH `x = &1 * x`] THEN
  SIMP_TAC[REAL_LT_RMUL_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; PI_POS] THEN
  ARITH_TAC);;

let ITER_DIFFS_LEMMA = prove
 (`!n c. ITER n diffs c 0 = &(FACT n) * c(n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER_ALT; diffs; FACT; REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_MUL_AC]);;

let TANNUMBER_HARMONICSUMS = prove
 (`!n. ODD n
       ==> (&2 * (&2 pow (n + 1) - &1) * &(FACT n) *
            suminf (\m. inv (&(m + 1) pow (n + 1))) / pi pow (n + 1) =
            tannumber n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `&0`] TAN_DERIV_POWSER) THEN
  SIMP_TAC[REAL_ABS_NUM; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; PI_POS] THEN
  REWRITE_TAC[TAN_0; GSYM tannumber] THEN
  MP_TAC(SPECL
   [`\m. ITER n diffs
      (\i. if EVEN i
           then &0
           else &2 *
                (&2 pow (i + 1) - &1) *
                suminf (\m. inv (&(m + 1) pow (i + 1))) / pi pow (i + 1))
      m *
      &0 pow m`;
    `1`] SER_0) THEN
  REWRITE_TAC[SUM_1] THEN
  SIMP_TAC[snd(EQ_IMP_RULE(SPEC_ALL REAL_POW_EQ_0));
           ARITH_RULE `1 <= n ==> ~(n = 0)`] THEN
  REWRITE_TAC[REAL_MUL_RZERO; real_pow] THEN
  ONCE_REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_UNIQ) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ITER_DIFFS_LEMMA; REAL_MUL_RID] THEN
  ASM_REWRITE_TAC[GSYM NOT_ODD] THEN REWRITE_TAC[REAL_MUL_AC]);;

let HARMONICSUMS_TANNUMBER = prove
 (`!n. EVEN n /\ ~(n = 0)
       ==> (suminf (\m. inv (&(m + 1) pow n)) / pi pow n =
            tannumber(n - 1) / (&2 * &(FACT(n - 1)) * (&2 pow n - &1)))`,
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; EVEN; NOT_EVEN] THEN
  REWRITE_TAC[SUC_SUB1] THEN SIMP_TAC[GSYM TANNUMBER_HARMONICSUMS] THEN
  REWRITE_TAC[ADD1] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c * d = (a * c * b) * d`] THEN
  REWRITE_TAC[real_div] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `(a * b * c) * d = a * (b * c) * d`] THEN
  REWRITE_TAC[GSYM real_div] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_DIV_LMUL THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
  MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT] THEN
  REWRITE_TAC[REAL_SUB_LT] THEN
  REWRITE_TAC[REAL_POW2_CLAUSES; ADD_EQ_0; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* For uniformity, show that even tannumbers are zero.                       *)
(* ------------------------------------------------------------------------- *)

let ODD_POLY_DIFF = prove
 (`(!x. poly p (--x) = poly p x)
   ==> (!x. poly (poly_diff p) (--x) = --(poly(poly_diff p) x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFF_UNIQ THEN
  EXISTS_TAC `\x. poly p (--x)` THEN EXISTS_TAC `--x` THEN CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o HALF_MK_ABS o GSYM) THEN
    REWRITE_TAC[CONV_RULE(ONCE_DEPTH_CONV ETA_CONV) POLY_DIFF];
    MP_TAC(SPECL [`\x. poly p x`; `\x. --x`; `poly (poly_diff p) x`;
                  `--(&1)`; `--x`]
           DIFF_CHAIN) THEN
    REWRITE_TAC[POLY_DIFF; REAL_MUL_RNEG; REAL_MUL_RID; REAL_NEG_NEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    W(MP_TAC o SPEC `--x` o DIFF_CONV o lhand o rator o snd) THEN
    REWRITE_TAC[]]);;

let EVEN_POLY_DIFF = prove
 (`(!x. poly p (--x) = --(poly p x))
   ==> (!x. poly (poly_diff p) (--x) = poly(poly_diff p) x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFF_UNIQ THEN
  EXISTS_TAC `\x. poly p x` THEN EXISTS_TAC `--x` THEN
  REWRITE_TAC[POLY_DIFF] THEN
  FIRST_ASSUM(MP_TAC o
    ONCE_REWRITE_RULE[REAL_ARITH `(a = --b) <=> (--a = b)`]) THEN
  DISCH_THEN(SUBST1_TAC o HALF_MK_ABS o GSYM) THEN
  REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_NEG_NEG] THEN
  MATCH_MP_TAC DIFF_NEG THEN
  MP_TAC(SPECL [`\x. poly p x`; `\x. --x`; `poly (poly_diff p) x`;
                  `--(&1)`; `--x`]
           DIFF_CHAIN) THEN
  REWRITE_TAC[POLY_DIFF; REAL_MUL_RNEG; REAL_MUL_RID; REAL_NEG_NEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  W(MP_TAC o SPEC `--x` o DIFF_CONV o lhand o rator o snd) THEN
  REWRITE_TAC[]);;

let TANPOLY_ODD_EVEN = prove
 (`!n x. (poly (tanpoly n) (--x) =
          if EVEN n then --(poly (tanpoly n) x) else poly (tanpoly n) x)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[EVEN; tanpoly] THEN
    CONV_TAC(ONCE_DEPTH_CONV POLY_DIFF_CONV) THEN
    REWRITE_TAC[poly] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[EVEN] THEN
  ASM_CASES_TAC `EVEN n` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[tanpoly; POLY_MUL; ODD_POLY_DIFF; EVEN_POLY_DIFF] THEN
  REWRITE_TAC[REAL_MUL_RNEG] THEN TRY AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[poly] THEN REAL_ARITH_TAC);;

let TANNUMBER_EVEN = prove
 (`!n. EVEN n ==> (tannumber n = &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tannumber] THEN
  MATCH_MP_TAC(REAL_ARITH `(x = --x) ==> (x = &0)`) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_NEG_0] THEN
  ASM_SIMP_TAC[TANPOLY_ODD_EVEN]);;

(* ------------------------------------------------------------------------- *)
(* Hence get tidy series.                                                    *)
(* ------------------------------------------------------------------------- *)

let TAYLOR_TAN_CONVERGES = prove
 (`!x. abs(x) < pi / &2
       ==> (\n. tannumber n / &(FACT n) * x pow n) sums (tan x)`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP TAN_POWSER) THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[real_div; TANNUMBER_EVEN; REAL_MUL_LZERO; REAL_MUL_RZERO];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HARMONICSUMS_TANNUMBER; EVEN_ADD; ARITH; ADD_EQ_0] THEN
  REWRITE_TAC[ADD_SUB; real_div; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
   `a * b * c * a' * d * b' * e = (c * d * e) * ((a * a') * (b * b'))`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN AP_TERM_TAC THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_MUL_RINV THEN
  SIMP_TAC[REAL_ARITH `&1 < x ==> ~(x - &1 = &0)`;
           REAL_POW2_CLAUSES; ADD_EQ_0; ARITH_EQ]);;

let TAYLOR_X_COT_CONVERGES = prove
 (`!x. &0 < abs(x) /\ abs(x) < pi
       ==> (\n. (if n = 0 then &1 else
                 tannumber (n - 1) / ((&1 - &2 pow n) * &(FACT(n - 1)))) *
                x pow n)
           sums (x * cot(x))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP COT_X_POWSER) THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `ODD n` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `tannumber(n - 1) = &0`
     (fun th -> SIMP_TAC[th; real_div; REAL_MUL_LZERO; REAL_MUL_RZERO]) THEN
    MATCH_MP_TAC TANNUMBER_EVEN THEN
    UNDISCH_TAC `ODD n` THEN
    SUBGOAL_THEN `n = SUC(n - 1)` MP_TAC THENL
     [UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[ODD; NOT_ODD]; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[HARMONICSUMS_TANNUMBER; GSYM NOT_ODD] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `--(&2) * x * y * z * a = (&2 * y) * x * --a * z`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM REAL_INV_NEG; REAL_NEG_SUB; REAL_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Get a simple bound on the tannumbers.                                     *)
(* ------------------------------------------------------------------------- *)

let TANNUMBER_BOUND = prove
 (`!n. abs(tannumber n) <= &4 * &(FACT n) * (&2 / pi) pow (n + 1)`,
  GEN_TAC THEN DISJ_CASES_TAC(SPEC `n:num` EVEN_OR_ODD) THEN
  ASM_SIMP_TAC[TANNUMBER_EVEN; GSYM TANNUMBER_HARMONICSUMS] THEN
  (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
    [REAL_ABS_NUM; REAL_LE_MUL; REAL_POW_LE; REAL_POS; REAL_LE_DIV;
     PI_POS; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
   `a * b * c * d * e = (a * d) * c * b * e`] THEN
  ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_ARITH `&2 * x <= &4 <=> x <= &2`] THEN
    MP_TAC(SPEC `\m. inv (&(m + 1) pow (n + 1))` SER_ABS) THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM; REAL_ABS_POW] THEN
    W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
     [MATCH_MP_TAC SUMMABLE_INVERSE_POWERS THEN
      UNDISCH_TAC `ODD n` THEN
      SIMP_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM] THEN
      REPEAT STRIP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `suminf (\m. inv(&(m + 1) pow 2))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SER_LE THEN REPEAT CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH_RULE `0 < n + 1`] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        UNDISCH_TAC `ODD n` THEN
        SIMP_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM] THEN
        REPEAT STRIP_TAC THEN ARITH_TAC;
        MATCH_MP_TAC SUMMABLE_INVERSE_POWERS THEN
        UNDISCH_TAC `ODD n` THEN
        SIMP_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM] THEN
        REPEAT STRIP_TAC THEN ARITH_TAC;
        MATCH_MP_TAC SUMMABLE_INVERSE_POWERS THEN REWRITE_TAC[LE_REFL]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0,1) (\n. inv(&(n + 1) pow 2)) +
                suminf (\n. inv(&((n + 1) + 1) pow 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `(y = x) ==> x <= y`) THEN
      MATCH_MP_TAC SUM_UNIQ THEN
      MATCH_MP_TAC SER_OFFSET_REV THEN
      REWRITE_TAC[summable] THEN
      EXISTS_TAC
       `suminf (\n. inv(&(n + 1) pow 2)) -
       sum(0,1) (\n. inv(&(n + 1) pow 2))` THEN
      MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] SER_OFFSET) THEN
      MATCH_MP_TAC SUMMABLE_INVERSE_POWERS THEN REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_1; ADD_CLAUSES] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `&1 + x <= &2 <=> x <= &1`] THEN
    SUBST1_TAC(MATCH_MP SUM_UNIQ SUMMABLE_INVERSE_SQUARES_LEMMA) THEN
    MATCH_MP_TAC SER_LE THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `m:num` THEN REWRITE_TAC[REAL_POW_2] THEN
      REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`] THEN
      REWRITE_TAC[REAL_POW_2; REAL_INV_MUL; REAL_ABS_INV; REAL_ABS_NUM;
                  REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC;
      REWRITE_TAC[summable] THEN
      EXISTS_TAC
       `suminf (\n. inv(&(n + 1) pow 2)) -
       sum(0,1) (\n. inv(&(n + 1) pow 2))` THEN
      MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] SER_OFFSET) THEN
      MATCH_MP_TAC SUMMABLE_INVERSE_POWERS THEN REWRITE_TAC[LE_REFL];
      REWRITE_TAC[summable] THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[SUMMABLE_INVERSE_SQUARES_LEMMA]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN REWRITE_TAC[REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN
  ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW] THEN
  SIMP_TAC[real_abs; PI_POS; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[GSYM real_abs] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LT; REAL_LT_IMP_LE; PI_POS] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&1 <= x ==> abs(x - &1) <= x`) THEN
  REWRITE_TAC[REAL_POW2_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Also get some harmonic sums.                                              *)
(* ------------------------------------------------------------------------- *)

let HARMONIC_SUMS = prove
 (`!n. (\m. inv (&(m + 1) pow (2 * (n + 1))))
       sums (pi pow (2 * (n + 1)) *
             tannumber(2 * n + 1) /
             (&2 * (&2 pow (2 * (n + 1)) - &1) * &(FACT(2 * n + 1))))`,
  GEN_TAC THEN
  SUBGOAL_THEN `summable (\m. inv (&(m + 1) pow (2 * (n + 1))))` MP_TAC THENL
   [MATCH_MP_TAC SUMMABLE_INVERSE_POWERS THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_EQ_LDIV_EQ; REAL_POW_LT; PI_POS] THEN
  REWRITE_TAC[ARITH_RULE `2 * n + 1 = 2 * (n + 1) - 1`] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c = a * c * b`] THEN
  MATCH_MP_TAC HARMONICSUMS_TANNUMBER THEN
  REWRITE_TAC[MULT_EQ_0; ADD_EQ_0; ARITH; EVEN_MULT]);;

let mk_harmonic =
  let pth = prove
   (`x * &1 / n = x / n`,
    REWRITE_TAC[real_div; REAL_MUL_LID]) in
  let final_RULE = CONV_RULE(TRY_CONV(GEN_REWRITE_CONV RAND_CONV [pth])) in
  fun n ->
    let th1 = SPEC(mk_small_numeral((n-1)/2)) HARMONIC_SUMS in
    let th2 = CONV_RULE NUM_REDUCE_CONV th1 in
    let th3 = CONV_RULE(ONCE_DEPTH_CONV TANNUMBER_CONV) th2 in
    let th4 = CONV_RULE REAL_RAT_REDUCE_CONV th3 in
    final_RULE th4;;

(* ------------------------------------------------------------------------- *)
(* A little test.                                                            *)
(* ------------------------------------------------------------------------- *)

map (fun n -> time mk_harmonic (2 * n)) (0--8);;

(* ------------------------------------------------------------------------- *)
(* Isolate the most famous special case.                                     *)
(* ------------------------------------------------------------------------- *)

let EULER_HARMONIC_SUM = mk_harmonic 2;;

(* ------------------------------------------------------------------------- *)
(* Canonical Taylor series for tan and cot with truncation bounds.           *)
(* ------------------------------------------------------------------------- *)

let TAYLOR_TAN_BOUND_GENERAL = prove
 (`!x n. abs(x) <= &1
         ==> abs(tan x - sum (0,n) (\m. tannumber m / &(FACT m) * x pow m))
             <= &12 * (&2 / &3) pow (n + 1) * abs(x) pow n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(x) < pi / &2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e < a ==> abs(p - a) <= e ==> b < p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP TAYLOR_TAN_CONVERGES) THEN
  DISCH_THEN(fun th ->
    ASSUME_TAC th THEN MP_TAC(MATCH_MP SUM_SUMMABLE th)) THEN
  DISCH_THEN(MP_TAC o SPEC `n:num` o MATCH_MP SER_OFFSET) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP SUM_UNIQ) THEN
  REWRITE_TAC[sums] THEN DISCH_THEN(MP_TAC o MATCH_MP SEQ_ABS_IMP) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC SEQ_LE_CONST THEN
  EXISTS_TAC `\r. abs(sum(0,r) (\m. (tannumber(m + n) / &(FACT(m + n))) *
                                    x pow (m + n)))` THEN
  EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN(K ALL_TAC) THEN
  W(MP_TAC o PART_MATCH lhand SUM_ABS_LE o lhand o snd) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(0,m) (\r. &4 * (&2 / pi) pow (r + n + 1) * abs(x pow (r + n)))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN
    X_GEN_TAC `r:num` THEN REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM;
             REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; FACT_LT] THEN
    MP_TAC(SPEC `r + n:num` TANNUMBER_BOUND) THEN
    REWRITE_TAC[REAL_MUL_AC; GSYM ADD_ASSOC]; ALL_TAC] THEN
  REWRITE_TAC[GSYM ADD1; ADD_CLAUSES] THEN
  REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_ABS_POW; GSYM REAL_POW_MUL] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[SUM_CMUL] THEN
  SUBGOAL_THEN `&2 / pi * abs(x) < &2 / &3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 / pi * &1` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE;
                   PI_POS];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; PI_POS] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e < a ==> abs(p - a) <= e ==> b < p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `~(&2 / pi * abs(x) = &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `&2 / pi * abs x < &2 / &3` THEN
    ONCE_REWRITE_TAC[TAUT `a ==> ~b <=> b ==> ~a`] THEN
    SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [AC REAL_MUL_AC `(a * b) * c = (a * c) * b`] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
  ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_POW_MUL; GSYM REAL_ABS_POW;
                REAL_ABS_MUL; REAL_ABS_ABS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ABS_MUL; real_div; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e <= a ==> abs(p - a) <= e ==> b <= abs p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_ARITH
   `&4 * x * y <= &12 * z <=> x * y <= z * &3`] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; real_div; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e <= a ==> abs(p - a) <= e ==> b <= abs p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  ASM_SIMP_TAC[GP_FINITE] THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  REWRITE_TAC[real_div; GSYM REAL_ABS_INV] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  REWRITE_TAC[GSYM real_div] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ x <= &1 ==> abs(&1 - x) <= &1`) THEN
    (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
       [REAL_POW_LE; REAL_LE_DIV; REAL_LE_MUL; REAL_POS;
        REAL_ABS_POS; PI_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN
    (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
       [REAL_POW_LE; REAL_LE_DIV; REAL_LE_MUL; REAL_POS;
        REAL_ABS_POS; PI_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 / pi * &1` THEN
    ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LE_DIV; REAL_POS;
                 REAL_LT_IMP_LE; PI_POS] THEN
    SIMP_TAC[REAL_MUL_RID; REAL_LE_LDIV_EQ; PI_POS] THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e <= a ==> abs(p - a) <= e ==> b <= &1 * p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_INV] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH
   `x <= (&1 - a) * &1 ==> a <= abs(&1 - x)`) THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE; PI_POS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
  MP_TAC PI_APPROX_25_BITS THEN
  MATCH_MP_TAC(REAL_ARITH
   `b + e <= a ==> abs(p - a) <= e ==> b <= p`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let TAYLOR_TAN_BOUND = prove
 (`!x n k. abs(x) <= inv(&2 pow k)
           ==> abs(tan x -
                   sum (0,n) (\m. tannumber(m) / &(FACT(m)) * x pow m))
               <= &12 * (&2 / &3) pow (n + 1) * inv(&2 pow (k * n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&12 * (&2 / &3) pow (n + 1) * abs(x) pow n` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TAYLOR_TAN_BOUND_GENERAL THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 pow k)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `inv(&2 pow 0)`)) THEN
    REWRITE_TAC[REAL_POW2_THM; LE_0];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_LE_DIV; REAL_POS] THEN
    REWRITE_TAC[GSYM REAL_POW_POW] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW_INV] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]]);;

let TAYLOR_TANX_BOUND = prove
 (`!x n k. abs(x) <= inv(&2 pow k) /\ ~(x = &0)
           ==> abs(tan x / x -
                   sum (0,n) (\m. tannumber(m+1) / &(FACT(m+1)) * x pow m))
               <= &12 * (&2 / &3) pow (n + 2) * inv(&2 pow (k * n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `abs(x)` THEN
  ASM_SIMP_TAC[GSYM REAL_ABS_NZ] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_SUB_RDISTRIB] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM SUM_CMUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [AC REAL_MUL_AC `a * b * c = b * (a * c)`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
  REWRITE_TAC[ADD1; SPECL [`f:num->real`; `n:num`; `1`] SUM_OFFSET] THEN
  REWRITE_TAC[SUM_1] THEN
  CONV_TAC(ONCE_DEPTH_CONV TANNUMBER_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[real_pow] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&12 * (&2 / &3) pow ((n + 1) + 1) * abs(x) pow (n + 1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TAYLOR_TAN_BOUND_GENERAL THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 pow k)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `inv(&2 pow 0)`)) THEN
    REWRITE_TAC[REAL_POW2_THM; LE_0]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`] THEN
  REWRITE_TAC[GSYM ADD1; real_pow] THEN
  GEN_REWRITE_TAC RAND_CONV [AC REAL_MUL_AC
   `(a * b * c) * d = (a * b * d) * c`] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
    [REAL_LE_MUL; REAL_POW_LE; REAL_ABS_POS; REAL_LE_DIV; REAL_POS] THEN
  REWRITE_TAC[GSYM REAL_POW_POW] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW_INV] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

let TAYLOR_TANX_SQRT_BOUND = prove
 (`!x n k. abs(x) <= inv(&2 pow k) /\ &0 < x
           ==> abs(tan (sqrt x) / sqrt(x) -
                   sum(0,n) (\m. tannumber(2 * m + 1) / &(FACT(2 * m + 1)) *
                                 x pow m))
               <= &12 * (&2 / &3) pow (2 * n + 2) *
                  inv(&2 pow (k DIV 2 * 2 * n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`sqrt x`; `2 * n`; `k DIV 2`] TAYLOR_TANX_BOUND) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_IMP_NZ; DIV_EQ_0; ARITH_EQ; NOT_LT] THEN
    SUBGOAL_THEN `&2 pow (k DIV 2) = sqrt(&2 pow (2 * (k DIV 2)))`
    SUBST1_TAC THENL
     [SIMP_TAC[SQRT_EVEN_POW2; EVEN_MULT; ARITH_EVEN; DIV_MULT; ARITH_EQ];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM SQRT_INV; REAL_LT_IMP_LE; REAL_POW2_CLAUSES] THEN
    ASM_SIMP_TAC[real_abs; SQRT_POS_LT; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 pow k)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN SIMP_TAC[REAL_POW2_CLAUSES] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN
    REWRITE_TAC[REAL_OF_NUM_LE; ARITH] THEN
    MESON_TAC[LE_ADD; DIVISION; NUM_EQ_CONV `2 = 0`; MULT_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM SUM_GROUP] THEN
  SIMP_TAC[SUM_2; TANNUMBER_EVEN; ARITH_EVEN; EVEN_ADD; EVEN_MULT] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_POW; SQRT_POW_2; REAL_LT_IMP_LE]);;

let TAYLOR_COT_BOUND_GENERAL = prove
 (`!x n. abs(x) <= &1 /\ ~(x = &0)
         ==> abs((&1 / x - cot x) -
                 sum (0,n) (\m. (tannumber m /
                                 ((&2 pow (m+1) - &1) * &(FACT(m)))) *
                                x pow m))
             <= &4 * (abs(x) / &3) pow n`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `abs(x)` THEN
  ASM_SIMP_TAC[GSYM REAL_ABS_NZ] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_SUB_LDISTRIB] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL] THEN REWRITE_TAC[GSYM SUM_CMUL] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `x * a * y = a * x * y`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN REWRITE_TAC[ADD1] THEN
  REWRITE_TAC[SUM_1; REAL_MUL_LZERO; REAL_SUB_RZERO; real_pow] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  SUBGOAL_THEN `abs(x) < pi` MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e < a ==> abs(p - a) <= e ==> b < p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ABS_NZ]) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP TAYLOR_X_COT_CONVERGES) THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(ASSUME_TAC o SYM o MATCH_MP SUM_UNIQ) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP SER_OFFSET) THEN
  ASM_REWRITE_TAC[SUM_1; ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN
  REWRITE_TAC[REAL_NEG_SUB] THEN
  ONCE_REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN
  REWRITE_TAC[GSYM REAL_INV_NEG] THEN
  REWRITE_TAC[GSYM real_div] THEN
  ONCE_REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
  REWRITE_TAC[REAL_NEG_SUB] THEN REWRITE_TAC[ADD_SUB] THEN
  DISCH_THEN(fun th ->
    ASSUME_TAC th THEN MP_TAC(MATCH_MP SUM_SUMMABLE th)) THEN
  DISCH_THEN(MP_TAC o SPEC `n:num` o MATCH_MP SER_OFFSET) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP SUM_UNIQ) THEN
  REWRITE_TAC[sums] THEN DISCH_THEN(MP_TAC o MATCH_MP SEQ_ABS_IMP) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC SEQ_LE_CONST THEN
  FIRST_ASSUM(fun th ->
   EXISTS_TAC(lhand(concl th)) THEN EXISTS_TAC `0` THEN
   CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC th]) THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH lhand SUM_ABS_LE o lhand o snd) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(0,m) (\r. &4 *
                  (&2 / pi) pow (r + n + 1) / (&2 pow (r + n + 1) - &1) *
                  abs(x pow (r + n + 1)))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN
    X_GEN_TAC `r:num` THEN REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [AC REAL_MUL_AC `a * b * c = (c * a) * b`] THEN
    REWRITE_TAC[REAL_MUL_ASSOC; real_abs; REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_POW2_CLAUSES] THEN REWRITE_TAC[GSYM real_abs] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_SUB_LE; REAL_POW2_CLAUSES] THEN
    SIMP_TAC[GSYM real_div; REAL_ABS_DIV; REAL_ABS_NUM;
             REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; FACT_LT] THEN
    MP_TAC(SPEC `r + n:num` TANNUMBER_BOUND) THEN
    REWRITE_TAC[REAL_MUL_AC; GSYM ADD_ASSOC]; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [AC REAL_MUL_AC `a * (b * c) * d = a * c * (b * d)`] THEN
  REWRITE_TAC[REAL_ABS_POW; GSYM REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(0,m) (\r. &8 * inv(&2 pow (r + n + 1)) *
                       ((&2 * inv pi) * abs x) pow (r + n + 1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&4 * x <= &8 * y <=> x <= &2 * y`] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
      [REAL_POW_LE; REAL_LE_MUL; REAL_ABS_POS; REAL_POS;
       REAL_LT_IMP_LE; PI_POS; REAL_LE_INV_EQ] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM REAL_INV_INV] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    SIMP_TAC[REAL_LT_MUL; REAL_LT_INV_EQ; REAL_OF_NUM_LT;
             ARITH; REAL_POW_LT] THEN
    REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; real_pow] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `&1 * x <= &2 * x - &1 <=> &1 <= x`] THEN
    REWRITE_TAC[REAL_POW2_CLAUSES]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_POW_INV; GSYM REAL_POW_MUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_ARITH `(&1 * x) * y = y * x`] THEN
  REWRITE_TAC[GSYM real_div] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_POW_ADD] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [AC REAL_MUL_AC `a * b * c = (a * c) * b`] THEN
  REWRITE_TAC[SUM_CMUL] THEN
  SUBGOAL_THEN
   `(&4 * abs x) * (abs x * &1 / &3) pow n =
    &12 * (abs x / &3) pow (n + 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_POW_MUL; GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV
     [AC REAL_MUL_AC `a * b * c * d * e = (a * e) * d * b * c`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `&8 * &3 / &2`)) THEN
  GEN_REWRITE_TAC RAND_CONV [AC REAL_MUL_AC
   `(a * b) * c = (a * c) * b`] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
  ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[real_div; REAL_ABS_MUL; REAL_ABS_ABS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ABS_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e <= a ==> abs(p - a) <= e ==> b <= abs p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `abs(x) / pi < &1 / &3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&1 / pi` THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; PI_POS] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e < a ==> abs(p - a) <= e ==> b < p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `~(abs(x) / pi = &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `abs x / pi < &1 / &3` THEN
    ONCE_REWRITE_TAC[TAUT `a ==> ~b <=> b ==> ~a`] THEN
    SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  ASM_SIMP_TAC[GP_FINITE] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x - &1 = --(&1 - x)`] THEN
  REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ x <= &1 ==> abs(&1 - x) <= &1`) THEN
    SIMP_TAC[REAL_POW_LE; REAL_LE_MUL; REAL_LE_INV_EQ; REAL_ABS_POS;
             REAL_LT_IMP_LE; PI_POS] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN
    SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; REAL_LE_INV_EQ;
             REAL_LT_IMP_LE; PI_POS] THEN
    SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; PI_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e <= a ==> abs(p - a) <= e ==> b <= &1 * p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
  REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM real_div] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < a ==> b <= &1 - a ==> b <= abs(&1 - x)`)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let TAYLOR_COT_BOUND = prove
 (`!x n k. abs(x) <= inv(&2 pow k) /\ ~(x = &0)
           ==> abs((&1 / x - cot x) -
                   sum (0,n) (\m. (tannumber m /
                                   ((&2 pow (m+1) - &1) * &(FACT(m)))) *
                                  x pow m))
               <= &4 / &3 pow n * inv(&2 pow (k * n))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(x) <= &1 /\ ~(x = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&2 pow k)` THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `inv(&2 pow 0)`)) THEN
    REWRITE_TAC[REAL_POW2_THM; LE_0]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num` o MATCH_MP TAYLOR_COT_BOUND_GENERAL) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[real_div; REAL_POW_MUL; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  REWRITE_TAC[GSYM REAL_POW_INV; GSYM REAL_POW_POW] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_POS; REAL_ABS_POS] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[real_div; REAL_MUL_LID; REAL_POW_INV]);;

let TAYLOR_COTX_BOUND = prove
 (`!x n k. abs(x) <= inv(&2 pow k) /\ ~(x = &0)
           ==> abs((&1 / x - cot x) / x -
                   sum (0,n) (\m. (tannumber(m+1) /
                                   ((&2 pow (m+2) - &1) * &(FACT(m+1)))) *
                                  x pow m))
               <= (&4 / &3) / &3 pow n * inv(&2 pow (k * n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `abs(x)` THEN
  ASM_SIMP_TAC[GSYM REAL_ABS_NZ] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_SUB_RDISTRIB] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM SUM_CMUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [AC REAL_MUL_AC `a * b * c = b * (a * c)`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
  REWRITE_TAC[ARITH_RULE `n + 2 = (n + 1) + 1`] THEN
  REWRITE_TAC[ADD1; SPECL [`f:num->real`; `n:num`; `1`] SUM_OFFSET] THEN
  REWRITE_TAC[SUM_1] THEN
  CONV_TAC(ONCE_DEPTH_CONV TANNUMBER_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[real_pow] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  REWRITE_TAC[GSYM REAL_SUB_RDISTRIB] THEN
  SUBGOAL_THEN `abs(x) <= &1 /\ ~(x = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&2 pow k)` THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `inv(&2 pow 0)`)) THEN
    REWRITE_TAC[REAL_POW2_THM; LE_0]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n + 1` o MATCH_MP TAYLOR_COT_BOUND_GENERAL) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c * d = ((a * d) * b) * c`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_POW_MUL; GSYM REAL_INV_MUL] THEN
  REWRITE_TAC[GSYM REAL_POW_POW; GSYM REAL_POW_MUL] THEN
  REWRITE_TAC[REAL_INV_MUL; REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM REAL_POW_INV] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; REAL_LE_DIV; REAL_POS] THEN
  REWRITE_TAC[REAL_INV_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let TAYLOR_COTXX_BOUND = prove
 (`!x n k. abs(x) <= inv(&2 pow k) /\ ~(x = &0)
           ==> abs((&1 - x * cot(x)) -
                   sum(0,n) (\m. (tannumber (m-1) /
                                  ((&2 pow m - &1) * &(FACT(m-1)))) *
                                 x pow m))
               <= &12 / &3 pow n * inv(&2 pow (k * n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `abs(inv x)` THEN
  ASM_SIMP_TAC[GSYM REAL_ABS_NZ; REAL_INV_EQ_0] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_SUB_RDISTRIB] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
   [AC REAL_MUL_AC `(a * b) * c = b * a * c`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID] THEN
  REWRITE_TAC[GSYM real_div] THEN
  REWRITE_TAC[GSYM REAL_SUB_RDISTRIB] THEN
  SUBGOAL_THEN `abs(x) <= &1 /\ ~(x = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&2 pow k)` THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `inv(&2 pow 0)`)) THEN
    REWRITE_TAC[REAL_POW2_THM; LE_0]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n - 1` o MATCH_MP TAYLOR_COT_BOUND_GENERAL) THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[sum] THEN
    REWRITE_TAC[real_pow; real_div; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    REWRITE_TAC[GSYM real_div] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC; MULT_CLAUSES; REAL_INV_MUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_DIV] THEN
    REWRITE_TAC[REAL_ABS_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&2 pow k)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&2 pow 0)` THEN
    REWRITE_TAC[REAL_POW2_THM; LE_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `n = (n - 1) + 1` MP_TAC THENL
   [UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC
   (RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
  REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_OFFSET)] THEN
  REWRITE_TAC[SUB_0; ADD_SUB; SUM_1] THEN
  SIMP_TAC[TANNUMBER_EVEN; EVEN] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV)
        [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM SUM_CMUL] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
        [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(s1 = s2) /\ a <= b ==> s1 <= a ==> s2 <= b`) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_MUL_RID] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; GSYM REAL_MUL_ASSOC] THEN
    REPEAT AP_TERM_TAC THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_INV_MUL; REAL_MUL_ASSOC; real_div] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
  REWRITE_TAC[REAL_ABS_INV; GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; GSYM REAL_ABS_NZ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
  REWRITE_TAC[GSYM REAL_POW_POW] THEN
  REWRITE_TAC[GSYM REAL_POW_INV] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD1] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_REWRITE_TAC[REAL_ABS_POS; REAL_POW_INV]);;

let TAYLOR_COTXX_SQRT_BOUND = prove
 (`!x n k. abs(x) <= inv(&2 pow k) /\ &0 < x
           ==> abs((&1 - sqrt(x) * cot(sqrt(x))) -
                   sum(0,n) (\m. (tannumber (2*m-1) /
                                  ((&2 pow (2*m) - &1) * &(FACT(2*m-1)))) *
                                 x pow m))
               <= &12 / &3 pow (2 * n) * inv(&2 pow (k DIV 2 * 2 * n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`sqrt x`; `2 * n`; `k DIV 2`] TAYLOR_COTXX_BOUND) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_IMP_NZ; DIV_EQ_0; ARITH_EQ; NOT_LT] THEN
    SUBGOAL_THEN `&2 pow (k DIV 2) = sqrt(&2 pow (2 * (k DIV 2)))`
    SUBST1_TAC THENL
     [SIMP_TAC[SQRT_EVEN_POW2; EVEN_MULT; ARITH_EVEN; DIV_MULT; ARITH_EQ];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM SQRT_INV; REAL_LT_IMP_LE; REAL_POW2_CLAUSES] THEN
    ASM_SIMP_TAC[real_abs; SQRT_POS_LT; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 pow k)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN SIMP_TAC[REAL_POW2_CLAUSES] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN
    REWRITE_TAC[REAL_OF_NUM_LE; ARITH] THEN
    MESON_TAC[LE_ADD; DIVISION; NUM_EQ_CONV `2 = 0`; MULT_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM SUM_GROUP] THEN
  SUBGOAL_THEN `!n. EVEN(((n * 2) + 1) - 1)` ASSUME_TAC THENL
   [INDUCT_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; SUC_SUB1; SUB_0;
                MULT_CLAUSES; SUB_REFL; ADD_SUB] THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_2; TANNUMBER_EVEN; ARITH_EVEN; EVEN_ADD; EVEN_MULT] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_POW; SQRT_POW_2; REAL_LT_IMP_LE]);;
