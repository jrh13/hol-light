(* ========================================================================= *)
(* Bernoulli numbers and polynomials; sum of kth powers.                     *)
(* ========================================================================= *)

needs "Library/binomial.ml";;
needs "Library/analysis.ml";;
needs "Library/transc.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* A couple of basic lemmas about new-style sums.                            *)
(* ------------------------------------------------------------------------- *)

let SUM_DIFFS = prove
 (`!a m n. m <= n + 1 ==> sum(m..n) (\i. a(i + 1) - a(i)) = a(n + 1) - a(m)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG] THENL
   [REWRITE_TAC[ARITH_RULE `m <= 0 + 1 <=> m = 0 \/ m = 1`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH; ADD_CLAUSES; REAL_SUB_REFL];
    SIMP_TAC[ARITH_RULE `m <= SUC n + 1 <=> m <= n + 1 \/ m = SUC n + 1`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[ADD1] THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; ARITH_RULE `~((n + 1) + 1 <= n + 1)`] THEN
    MATCH_MP_TAC SUM_TRIV_NUMSEG THEN ARITH_TAC]);;

let DIFF_SUM = prove
 (`!f f' a b.
        (!k. a <= k /\ k <= b ==> ((\x. f x k) diffl f'(k)) x)
        ==> ((\x. sum(a..b) (f x)) diffl (sum(a..b) f')) x`,
  REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[ARITH; DIFF_CONST; SUM_TRIV_NUMSEG;
               ARITH_RULE `~(a <= SUC b) ==> b < a`] THEN
  DISCH_TAC THEN MATCH_MP_TAC DIFF_ADD THEN
  ASM_SIMP_TAC[LE_REFL; ARITH_RULE `k <= b ==> k <= SUC b`]);;

(* ------------------------------------------------------------------------- *)
(* Bernoulli numbers.                                                        *)
(* ------------------------------------------------------------------------- *)

let bernoulli = define
 `(bernoulli 0 = &1) /\
  (!n. bernoulli(SUC n) =
       --sum(0..n) (\j. &(binom(n + 2,j)) * bernoulli j) / (&n + &2))`;;

(* ------------------------------------------------------------------------- *)
(* A slightly tidier-looking form of the recurrence.                         *)
(* ------------------------------------------------------------------------- *)

let BERNOULLI = prove
 (`!n. sum(0..n) (\j. &(binom(n + 1,j)) * bernoulli j) =
       if n = 0 then &1 else &0`,
  INDUCT_TAC THEN
  REWRITE_TAC[bernoulli; SUM_CLAUSES_NUMSEG; GSYM ADD1; ADD_CLAUSES; binom;
              REAL_MUL_LID; LE_0; NOT_SUC] THEN
  SIMP_TAC[BINOM_LT; ARITH_RULE `n < SUC n`; BINOM_REFL; REAL_ADD_LID] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC n) = n + 2`] THEN
  MATCH_MP_TAC(REAL_FIELD `x = &n + &2 ==> s + x * --s / (&n + &2) = &0`) THEN
  REWRITE_TAC[ADD1; BINOM_TOP_STEP_REAL; ARITH_RULE `~(n = n + 1)`] THEN
  REWRITE_TAC[BINOM_REFL] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bernoulli polynomials.                                                    *)
(* ------------------------------------------------------------------------- *)

let bernpoly = new_definition
 `bernpoly n x = sum(0..n) (\k. &(binom(n,k)) * bernoulli k * x pow (n - k))`;;

(* ------------------------------------------------------------------------- *)
(* The key derivative recurrence.                                            *)
(* ------------------------------------------------------------------------- *)

let DIFF_BERNPOLY = prove
 (`!n x. ((bernpoly (SUC n)) diffl (&(SUC n) * bernpoly n x)) x`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[bernpoly; SUM_CLAUSES_NUMSEG; LE_0] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
  MATCH_MP_TAC DIFF_ADD THEN REWRITE_TAC[SUB_REFL; real_pow; DIFF_CONST] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC DIFF_SUM THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[ADD1; BINOM_TOP_STEP_REAL] THEN
  DIFF_TAC THEN ASM_SIMP_TAC[ARITH_RULE `k <= n ==> ~(k = n + 1)`] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= n ==> (n + 1) - k - 1 = n - k`] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `k <= n ==> k <= n + 1`] THEN
  UNDISCH_TAC `k <= n:num` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_LE] THEN
  ABBREV_TAC `z = x pow (n - k)` THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Hence the key stepping recurrence.                                        *)
(* ------------------------------------------------------------------------- *)

let INTEGRALS_EQ = prove
 (`!f g. (!x. ((\x. f(x) - g(x)) diffl &0) x) /\ f(&0) = g(&0)
         ==> !x. f(x) = g(x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\x:real. f(x) - g(x)`; `x:real`; `&0`] DIFF_ISCONST_ALL) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RECURRENCE_BERNPOLY = prove
 (`!n x. bernpoly n (x + &1) - bernpoly n x = &n * x pow (n - 1)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[bernpoly; SUM_SING_NUMSEG; REAL_SUB_REFL; SUB_REFL;
                real_pow; REAL_MUL_LZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRALS_EQ THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
    DISCH_THEN(MP_TAC o AP_TERM `(*) (&(SUC n))`) THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
    REPEAT(MATCH_MP_TAC DIFF_SUB THEN CONJ_TAC) THEN
    SIMP_TAC[SUC_SUB1; DIFF_CMUL; DIFF_POW; DIFF_BERNPOLY; ETA_AX] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC DIFF_CHAIN THEN REWRITE_TAC[DIFF_BERNPOLY] THEN
    DIFF_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[bernpoly; GSYM SUM_SUB_NUMSEG] THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_POW_ONE; GSYM REAL_SUB_LDISTRIB] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; SUB_REFL; real_pow] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  SIMP_TAC[ARITH_RULE `i <= n ==> SUC n - i = SUC(n - i)`] THEN
  REWRITE_TAC[real_pow; REAL_MUL_LZERO; REAL_SUB_RZERO; REAL_MUL_RID] THEN
  REWRITE_TAC[BERNOULLI; ADD1] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH; real_pow; REAL_MUL_LID] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0] THEN
  ASM_REWRITE_TAC[ADD_SUB]);;

(* ------------------------------------------------------------------------- *)
(* Hence we get the main result.                                             *)
(* ------------------------------------------------------------------------- *)

let SUM_OF_POWERS = prove
 (`!n. sum(0..n) (\k. &k pow m) =
        (bernpoly(SUC m) (&n + &1) - bernpoly(SUC m) (&0)) / (&m + &1)`,
  GEN_TAC THEN ASM_SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  ONCE_REWRITE_TAC[GSYM REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `sum(0..n) (\i. bernpoly (SUC m) (&(i + 1)) - bernpoly (SUC m) (&i))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[RECURRENCE_BERNPOLY; GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; SUC_SUB1];
    SIMP_TAC[SUM_DIFFS; LE_0] THEN REWRITE_TAC[REAL_OF_NUM_ADD]]);;

(* ------------------------------------------------------------------------- *)
(* Now explicit computations of the various terms on specific instances.     *)
(* ------------------------------------------------------------------------- *)

let SUM_CONV =
  let pth = prove
   (`sum(0..0) f = f 0 /\ sum(0..SUC n) f = sum(0..n) f + f(SUC n)`,
    SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0]) in
  let econv_0 = GEN_REWRITE_CONV I [CONJUNCT1 pth]
  and econv_1 = GEN_REWRITE_CONV I [CONJUNCT2 pth] in
  let rec sconv tm =
    (econv_0 ORELSEC
     (LAND_CONV(RAND_CONV num_CONV) THENC econv_1 THENC
      COMB2_CONV (RAND_CONV sconv) (RAND_CONV NUM_SUC_CONV))) tm in
  sconv;;

let BINOM_CONV =
  let pth = prove
   (`a * b * x = FACT c ==> x = (FACT c) DIV (a * b)`,
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN ARITH_TAC;
      POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      SIMP_TAC[LT_NZ; MULT_ASSOC; MULT_CLAUSES] THEN
      MESON_TAC[LT_NZ; FACT_LT]]) in
  let match_pth = MATCH_MP pth
  and binom_tm = `binom` in
  fun tm ->
    let bop,lr = dest_comb tm in
    if bop <> binom_tm then failwith "BINOM_CONV" else
    let l,r = dest_pair lr in
    let n = dest_numeral l and k = dest_numeral r in
    if n </ k then
      let th = SPECL [l;r] BINOM_LT in
      MP th (EQT_ELIM(NUM_LT_CONV(lhand(concl th))))
    else
      let d = n -/ k in
      let th1 = match_pth(SPECL [mk_numeral d; r] BINOM_FACT) in
      CONV_RULE NUM_REDUCE_CONV th1;;

let BERNOULLIS =
  let th_0,th_1 = CONJ_PAIR bernoulli
  and b_tm = `bernoulli` in
  let conv_1 = GEN_REWRITE_CONV I [th_1] in
  let rec bconv n =
    if n <= 0 then [th_0] else
    let bths = bconv (n - 1)
    and tm = mk_comb(b_tm,mk_small_numeral n) in
    (RAND_CONV num_CONV THENC conv_1 THENC
     LAND_CONV(RAND_CONV SUM_CONV) THENC
     ONCE_DEPTH_CONV BETA_CONV THENC
     DEPTH_CONV(NUM_RED_CONV ORELSEC BINOM_CONV) THENC
     GEN_REWRITE_CONV ONCE_DEPTH_CONV bths THENC
     REAL_RAT_REDUCE_CONV) tm :: bths in
  bconv;;

let BERNOULLI_CONV =
  let b_tm = `bernoulli` in
  fun tm -> let op,n = dest_comb tm in
            if op <> b_tm || not(is_numeral n) then failwith "BERNOULLI_CONV"
            else hd(BERNOULLIS(dest_small_numeral n));;

let BERNPOLY_CONV =
  let conv_1 =
    REWR_CONV bernpoly THENC SUM_CONV THENC
    TOP_DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV
  and conv_3 =
    ONCE_DEPTH_CONV BINOM_CONV THENC REAL_POLY_CONV in
  fun tm ->
    let n = dest_small_numeral(lhand tm) in
    let conv_2 = GEN_REWRITE_CONV ONCE_DEPTH_CONV (BERNOULLIS n) in
    (conv_1 THENC conv_2 THENC conv_3) tm;;

let SOP_CONV =
  let pth = prove
   (`sum(0..n) (\k. &k pow m) =
        (\p. (p(&n + &1) - p(&0)) / (&m + &1))
        (\x. bernpoly (SUC m) x)`,
    REWRITE_TAC[SUM_OF_POWERS]) in
  let conv_0 = REWR_CONV pth in
  REWR_CONV pth THENC
  RAND_CONV(ABS_CONV(LAND_CONV NUM_SUC_CONV THENC BERNPOLY_CONV)) THENC
  TOP_DEPTH_CONV BETA_CONV THENC
  REAL_POLY_CONV;;

let SOP_NUM_CONV =
  let pth = prove
   (`sum(0..n) (\k. &k pow p) = &m ==> nsum(0..n) (\k. k EXP p) = m`,
    REWRITE_TAC[REAL_OF_NUM_POW; GSYM REAL_OF_NUM_SUM_NUMSEG;
                REAL_OF_NUM_EQ]) in
  let rule_1 = PART_MATCH (lhs o rand) pth in
  fun tm ->
    let th1 = rule_1 tm in
    let th2 = SOP_CONV(lhs(lhand(concl th1))) in
    MATCH_MP th1 th2;;

(* ------------------------------------------------------------------------- *)
(* The example Bernoulli bragged about.                                      *)
(* ------------------------------------------------------------------------- *)

time SOP_NUM_CONV `nsum(0..1000) (\k. k EXP 10)`;;

(* ------------------------------------------------------------------------- *)
(* The general formulas for moderate powers.                                 *)
(* ------------------------------------------------------------------------- *)

time SOP_CONV `sum(0..n) (\k. &k pow 0)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 1)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 2)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 3)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 4)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 5)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 6)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 7)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 8)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 9)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 10)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 11)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 12)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 13)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 14)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 15)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 16)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 17)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 18)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 19)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 20)`;;
time SOP_CONV `sum(0..n) (\k. &k pow 21)`;;
