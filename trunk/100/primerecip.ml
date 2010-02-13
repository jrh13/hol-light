(* ========================================================================= *)
(* Divergence of prime reciprocal series.                                    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Now load other stuff needed.                                              *)
(* ------------------------------------------------------------------------- *)

needs "100/bertrand.ml";;
needs "100/divharmonic.ml";;

(* ------------------------------------------------------------------------- *)
(* Variant of induction.                                                     *)
(* ------------------------------------------------------------------------- *)

let INDUCTION_FROM_1 = prove
 (`!P. P 0 /\ P 1 /\ (!n. 1 <= n /\ P n ==> P(SUC n)) ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[num_CONV `1`; ARITH_RULE `n = 0 \/ 1 <= n`]);;

(* ------------------------------------------------------------------------- *)
(* Evaluate sums over explicit intervals.                                    *)
(* ------------------------------------------------------------------------- *)

let SUM_CONV =
  let pth = prove
   (`sum(1..1) f = f 1 /\ sum(1..SUC n) f = sum(1..n) f + f(SUC n)`,
    SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0;
             ARITH_RULE `1 <= SUC n`; SUM_SING_NUMSEG]) in
  let econv_0 = GEN_REWRITE_CONV I [CONJUNCT1 pth]
  and econv_1 = GEN_REWRITE_CONV I [CONJUNCT2 pth] in
  let rec sconv tm =
    (econv_0 ORELSEC
     (LAND_CONV(RAND_CONV num_CONV) THENC econv_1 THENC
      COMB2_CONV (RAND_CONV sconv) (RAND_CONV NUM_SUC_CONV))) tm in
  sconv;;

(* ------------------------------------------------------------------------- *)
(* Lower bound relative to harmonic series.                                  *)
(* ------------------------------------------------------------------------- *)

let PRIMERECIP_HARMONIC_LBOUND = prove
 (`!n. (&3 / (&16 * ln(&32))) * sum(1..n) (\i. &1 / &i) <=
       sum(1..32 EXP n) (\i. if prime(i) then &1 / &i else &0)`,
  MATCH_MP_TAC INDUCTION_FROM_1 THEN CONJ_TAC THENL
   [SIMP_TAC[SUM_TRIV_NUMSEG; ARITH; SUM_SING_NUMSEG; REAL_MUL_RZERO] THEN
    REWRITE_TAC[PRIME_1; REAL_LE_REFL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH; SUM_SING_NUMSEG] THEN
    CONV_TAC(RAND_CONV SUM_CONV) THEN REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV PRIME_CONV) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[SYM(REAL_RAT_REDUCE_CONV `&2 pow 5`)] THEN
    SIMP_TAC[LN_POW; REAL_OF_NUM_LT; ARITH; real_div; REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_RID] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_DIV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[LN_2_COMPOSITION; real_div; real_sub] THEN
    CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH
   `b - a <= s2 - s1 ==> a <= s1 ==> b <= s2`) THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; REAL_ADD_SUB; ARITH_RULE `1 <= SUC n`] THEN
  MP_TAC(SPEC `32 EXP n` PII_UBOUND_5) THEN ANTS_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `32 EXP 1` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  MP_TAC(SPEC `32 EXP (SUC n)` PII_LBOUND) THEN ANTS_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `32 EXP 1` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN REWRITE_TAC[ARITH] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP(REAL_ARITH
   `a <= s1 /\ s2 <= b ==> a - b <= s1 - s2`)) THEN
  SIMP_TAC[pii; PSUM_SUM_NUMSEG; EXP_EQ_0; ARITH; ADD_SUB2] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN
  REWRITE_TAC[EXP; ARITH_RULE `32 * n = n + 31 * n`] THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`; REAL_ADD_SUB] THEN
  REWRITE_TAC[ARITH_RULE `n + 31 * n = 32 * n`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `inv(&32 pow (SUC n)) *
    sum(32 EXP n + 1 .. 32 EXP SUC n) (\i. if prime i then &1 else &0)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_MUL_RZERO] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `32 EXP n + 1 <= i` THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    SIMP_TAC[ARITH_RULE `~(0 < i) <=> i = 0`] THEN
    REWRITE_TAC[LE; ARITH; ADD_EQ_0]] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM real_div; REAL_POW_LT; REAL_LE_RDIV_EQ;
           REAL_OF_NUM_LT; ARITH] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
    `a <= x ==> b <= a ==> b <= x`)) THEN
  SIMP_TAC[LN_POW; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_pow; GSYM REAL_OF_NUM_SUC] THEN
  REWRITE_TAC[REAL_FIELD
   `&1 / &2 * (&32 * n32) / (n1 * l) - &5 * n32 / (n * l) =
    (n32 / l) * (&16 / n1 - &5 / n)`] THEN
  REWRITE_TAC[REAL_FIELD
   `(&3 / (&16 * l) * i) * &32 * n32 = (n32 / l) * (&6 * i)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; LN_POS; REAL_OF_NUM_LE; ARITH] THEN
  REWRITE_TAC[real_div; REAL_ARITH
   `&6 * &1 * n1 <= &16 * n1 - &5 * n <=> n <= inv(inv(&2)) * n1`] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hence an overall lower bound.                                             *)
(* ------------------------------------------------------------------------- *)

let PRIMERECIP_LBOUND = prove
 (`!n. &3 / (&32 * ln(&32)) * &n
       <= sum (1 .. 32 EXP (2 EXP n)) (\i. if prime i then &1 / &i else &0)`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&3 / (&16 * ln(&32)) * sum (1 .. 2 EXP n) (\i. &1 / &i)` THEN
  REWRITE_TAC[PRIMERECIP_HARMONIC_LBOUND] THEN
  REWRITE_TAC[REAL_FIELD
   `&3 / (&32 * ln(&32)) * &n = &3 / (&16 * ln(&32)) * (&n / &2)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REWRITE_RULE[real_ge] HARMONIC_LEMMA] THEN
  SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; LN_POS; REAL_OF_NUM_LE; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* General lemma.                                                            *)
(* ------------------------------------------------------------------------- *)

let UNBOUNDED_DIVERGENT = prove
 (`!s. (!k. ?N. !n. n >= N ==> sum(1..n) s >= k)
       ==> ~(convergent(\n. sum(1..n) s))`,
  REWRITE_TAC[convergent; SEQ] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN
  REWRITE_TAC[REAL_LT_01] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l + &1`) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `M:num` THEN
  DISCH_THEN(MP_TAC o SPEC `M + N:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `M + N:num`) THEN
  REWRITE_TAC[LE_ADD; ONCE_REWRITE_RULE[ADD_SYM] LE_ADD; GE] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hence divergence.                                                         *)
(* ------------------------------------------------------------------------- *)

let PRIMERECIP_DIVERGES_NUMSEG = prove
 (`~(convergent (\n. sum (1..n) (\i. if prime i then &1 / &i else &0)))`,
  MATCH_MP_TAC UNBOUNDED_DIVERGENT THEN X_GEN_TAC `k:real` THEN
  MP_TAC(SPEC `&3 / (&32 * ln(&32))` REAL_ARCH) THEN
  SIMP_TAC[REAL_LT_DIV; LN_POS_LT; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(MP_TAC o SPEC `k:real`) THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `32 EXP (2 EXP N)` THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[GE; real_ge] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&N * &3 / (&32 * ln (&32))` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `sum(1 .. 32 EXP (2 EXP N)) (\i. if prime i then &1 / &i else &0)` THEN
  REWRITE_TAC[PRIMERECIP_LBOUND] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`; REAL_LE_ADDR] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN SIMP_TAC[REAL_LE_DIV; REAL_POS]);;

(* ------------------------------------------------------------------------- *)
(* A perhaps more intuitive formulation.                                     *)
(* ------------------------------------------------------------------------- *)

let PRIMERECIP_DIVERGES = prove
 (`~(convergent (\n. sum {p | prime p /\ p <= n} (\p. &1 / &p)))`,
  MP_TAC PRIMERECIP_DIVERGES_NUMSEG THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> ~a ==> ~b`) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [SUBGOAL_THEN `{p | prime p /\ p <= 0} = {}`
     (fun th -> SIMP_TAC[SUM_CLAUSES; SUM_TRIV_NUMSEG; th; ARITH]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; LE] THEN
    MESON_TAC[PRIME_0];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  SUBGOAL_THEN
   `{p | prime p /\ p <= SUC n} =
        if prime(SUC n) then (SUC n) INSERT {p | prime p /\ p <= n}
        else {p | prime p /\ p <= n}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN
    GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; LE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ADD_RID] THEN
  SUBGOAL_THEN `FINITE {p | prime p /\ p <= n}`
   (fun th -> SIMP_TAC[SUM_CLAUSES; th])
  THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..n` THEN
    SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; IN_ELIM_THM; SUBSET] THEN
    MESON_TAC[PRIME_0; ARITH_RULE `1 <= i <=> ~(i = 0)`];
    REWRITE_TAC[IN_ELIM_THM; ARITH_RULE `~(SUC n <= n)`; REAL_ADD_AC]]);;
