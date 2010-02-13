(* ========================================================================= *)
(* Binomial coefficients and the binomial theorem.                           *)
(* ========================================================================= *)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Binomial coefficients.                                                    *)
(* ------------------------------------------------------------------------- *)

let binom = define
  `(!n. binom(n,0) = 1) /\
   (!k. binom(0,SUC(k)) = 0) /\
   (!n k. binom(SUC(n),SUC(k)) = binom(n,SUC(k)) + binom(n,k))`;;

let BINOM_LT = prove
 (`!n k. n < k ==> (binom(n,k) = 0)`,
  INDUCT_TAC THEN INDUCT_TAC THEN REWRITE_TAC[binom; ARITH; LT_SUC; LT] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < k ==> n < SUC(k)`; ARITH]);;

let BINOM_REFL = prove
 (`!n. binom(n,n) = 1`,
  INDUCT_TAC THEN ASM_SIMP_TAC[binom; BINOM_LT; LT; ARITH]);;

let BINOM_1 = prove                
 (`!n. binom(n,1) = n`,
  REWRITE_TAC[num_CONV `1`] THEN                                         
  INDUCT_TAC THEN ASM_REWRITE_TAC[binom] THEN ARITH_TAC);;

let BINOM_FACT = prove
 (`!n k. FACT n * FACT k * binom(n+k,k) = FACT(n + k)`,
  INDUCT_TAC THEN REWRITE_TAC[FACT; ADD_CLAUSES; MULT_CLAUSES; BINOM_REFL] THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; FACT; MULT_CLAUSES; binom] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; FACT; binom] THEN CONV_TAC NUM_RING);;

let BINOM_EQ_0 = prove
 (`!n k. binom(n,k) = 0 <=> n < k`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[BINOM_LT]] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_LT; LE_EXISTS] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  DISCH_TAC THEN MP_TAC(SYM(SPECL [`d:num`; `k:num`] BINOM_FACT)) THEN
  ASM_REWRITE_TAC[GSYM LT_NZ; MULT_CLAUSES; FACT_LT]);;

let BINOM_PENULT = prove
 (`!n. binom(SUC n,n) = SUC n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC [binom; ONE; BINOM_REFL] THEN
  SUBGOAL_THEN `binom(n,SUC n)=0` SUBST1_TAC THENL
   [REWRITE_TAC [BINOM_EQ_0; LT]; REWRITE_TAC [ADD; ADD_0; ADD_SUC; SUC_INJ]]);;

(* ------------------------------------------------------------------------- *)
(* More potentially useful lemmas.                                           *)
(* ------------------------------------------------------------------------- *)

let BINOM_TOP_STEP = prove
 (`!n k. ((n + 1) - k) * binom(n + 1,k) = (n + 1) * binom(n,k)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n < k:num` THENL
   [FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP
     (ARITH_RULE `n < k ==> n + 1 = k \/ n + 1 < k`)) THEN
    ASM_SIMP_TAC[BINOM_LT; SUB_REFL; MULT_CLAUSES];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_LT; LE_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  REWRITE_TAC[GSYM ADD_ASSOC; ADD_SUB; ADD_SUB2] THEN
  MP_TAC(SPECL [`d + 1`; `k:num`] BINOM_FACT) THEN
  MP_TAC(SPECL [`d:num`; `k:num`] BINOM_FACT) THEN
  REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; FACT; ADD_AC] THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t FACT_LT)) [`d:num`; `k:num`] THEN
  REWRITE_TAC[LT_NZ] THEN CONV_TAC NUM_RING);;

let BINOM_BOTTOM_STEP = prove
 (`!n k. (k + 1) * binom(n,k + 1) = (n - k) * binom(n,k)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n < k + 1` THENL
   [FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP
     (ARITH_RULE `n < k + 1 ==> n = k \/ n < k`)) THEN
    ASM_SIMP_TAC[BINOM_LT; SUB_REFL; MULT_CLAUSES];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_LT; LE_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  REWRITE_TAC[GSYM ADD_ASSOC; ADD_SUB; ADD_SUB2] THEN
  MP_TAC(SPECL [`d + 1`; `k:num`] BINOM_FACT) THEN
  MP_TAC(SPECL [`d:num`; `k + 1`] BINOM_FACT) THEN
  REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; FACT; ADD_AC] THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t FACT_LT)) [`d:num`; `k:num`] THEN
  REWRITE_TAC[LT_NZ] THEN CONV_TAC NUM_RING);;

(* ------------------------------------------------------------------------- *)
(* Binomial expansion.                                                       *)
(* ------------------------------------------------------------------------- *)

let BINOMIAL_THEOREM = prove
 (`!n x y.
      (x + y) EXP n = nsum(0..n) (\k. binom(n,k) * x EXP k * y EXP (n - k))`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[EXP] THEN
  REWRITE_TAC[NSUM_SING_NUMSEG; binom; SUB_REFL; EXP; MULT_CLAUSES] THEN
  SIMP_TAC[NSUM_CLAUSES_LEFT; ADD1; ARITH_RULE `0 <= n + 1`; NSUM_OFFSET] THEN
  ASM_REWRITE_TAC[EXP; binom; GSYM ADD1; GSYM NSUM_LMUL] THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; NSUM_ADD_NUMSEG; MULT_CLAUSES; SUB_0] THEN
  MATCH_MP_TAC(ARITH_RULE `a = e /\ b = c + d ==> a + b = c + d + e`) THEN
  CONJ_TAC THENL [REWRITE_TAC[MULT_AC; SUB_SUC]; REWRITE_TAC[GSYM EXP]] THEN
  SIMP_TAC[ADD1; SYM(REWRITE_CONV[NSUM_OFFSET]`nsum(m+1..n+1) (\i. f i)`)] THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG; GSYM ADD1; LE_SUC; LE_0] THEN
  SIMP_TAC[NSUM_CLAUSES_LEFT; LE_0] THEN
  SIMP_TAC[BINOM_LT; LT; MULT_CLAUSES; ADD_CLAUSES; SUB_0; EXP; binom] THEN
  SIMP_TAC[ARITH; ARITH_RULE `k <= n ==> SUC n - k = SUC(n - k)`; EXP] THEN
  REWRITE_TAC[MULT_AC]);;

(* ------------------------------------------------------------------------- *)
(* Same thing for the reals.                                                 *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let REAL_BINOMIAL_THEOREM = prove
 (`!n x y.
     (x + y) pow n = sum(0..n) (\k. &(binom(n,k)) * x pow k * y pow (n - k))`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[real_pow] THEN
  REWRITE_TAC[SUM_SING_NUMSEG; binom; SUB_REFL; real_pow; REAL_MUL_LID] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; ADD1; ARITH_RULE `0 <= n + 1`; SUM_OFFSET] THEN
  ASM_REWRITE_TAC[real_pow; binom; GSYM ADD1; GSYM SUM_LMUL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; SUM_ADD_NUMSEG; REAL_MUL_LID; SUB_0] THEN
  MATCH_MP_TAC(ARITH_RULE `a = e /\ b = c + d ==> a + b = c + d + e`) THEN
  CONJ_TAC THENL [SIMP_TAC[REAL_MUL_AC; SUB_SUC]; SIMP_TAC[GSYM real_pow]] THEN
  SIMP_TAC[ADD1; SYM(REWRITE_CONV[SUM_OFFSET]`sum(m+1..n+1) (\i. f i)`)] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; GSYM ADD1; LE_SUC; LE_0] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; BINOM_LT; LT; REAL_MUL_LID; SUB_0; real_pow;
           binom; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  SIMP_TAC[ARITH; ARITH_RULE `k <= n ==> SUC n - k = SUC(n - k)`; real_pow] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* More direct stepping theorems over the reals.                             *)
(* ------------------------------------------------------------------------- *)

let BINOM_TOP_STEP_REAL = prove
 (`!n k. &(binom(n + 1,k)) =
           if k = n + 1 then &1
           else (&n + &1) / (&n + &1 - &k) * &(binom(n,k))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[BINOM_REFL] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
   `~(k = n + 1) ==> n < k /\ n + 1 < k \/ k <= n /\ k <= n + 1`)) THEN
  ASM_SIMP_TAC[BINOM_LT; REAL_MUL_RZERO] THEN
  MP_TAC(SPECL [`n:num`; `k:num`] BINOM_TOP_STEP) THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD;
               GSYM REAL_OF_NUM_SUB] THEN
  UNDISCH_TAC `k <= n:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  CONV_TAC REAL_FIELD);;

let BINOM_BOTTOM_STEP_REAL = prove
 (`!n k. &(binom(n,k+1)) = (&n - &k) / (&k + &1) * &(binom(n,k))`,
  REPEAT GEN_TAC THEN DISJ_CASES_TAC(ARITH_RULE `n:num < k \/ k <= n`) THENL
   [ASM_SIMP_TAC[BINOM_LT; ARITH_RULE `n < k ==> n < k + 1`; REAL_MUL_RZERO];
    MP_TAC(SPECL [`n:num`; `k:num`] BINOM_BOTTOM_STEP) THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL;
                 GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_SUB] THEN
    CONV_TAC REAL_FIELD]);;

let REAL_OF_NUM_BINOM = prove
 (`!n k. &(binom(n,k)) =
             if k <= n then &(FACT n) / (&(FACT(n - k)) * &(FACT k))
             else &0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[BINOM_LT; GSYM NOT_LE] THEN
  SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT; FACT_LT] THEN
  FIRST_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[ADD_SUB2] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[GSYM BINOM_FACT] THEN REWRITE_TAC[REAL_OF_NUM_MUL; MULT_AC]);;

(* ------------------------------------------------------------------------- *)
(* Some additional theorems for stepping both arguments together.            *)
(* ------------------------------------------------------------------------- *)

let BINOM_BOTH_STEP_REAL = prove
 (`!p k. &(binom(p + 1,k + 1)) = (&p + &1) / (&k + &1) * &(binom(p,k))`,
  REWRITE_TAC[BINOM_TOP_STEP_REAL; BINOM_BOTTOM_STEP_REAL] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[EQ_ADD_RCANCEL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BINOM_REFL] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_EQ] THEN
  CONV_TAC REAL_FIELD);;

let BINOM_BOTH_STEP = prove
 (`!p k. (k + 1) * binom(p + 1,k + 1) = (p + 1) * binom(p,k)`,
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[BINOM_BOTH_STEP_REAL; GSYM REAL_OF_NUM_ADD] THEN
  CONV_TAC REAL_FIELD);;

let BINOM_BOTH_STEP_DOWN = prove
 (`!p k. (k = 0 ==> p = 0) ==> k * binom(p,k) = p * binom(p - 1,k - 1)`,
  REPEAT INDUCT_TAC THEN
  SIMP_TAC[BINOM_LT; LT_0; LT_REFL; ARITH] THEN
  REWRITE_TAC[SUC_SUB1; ADD1; BINOM_BOTH_STEP] THEN
  REWRITE_TAC[MULT_CLAUSES]);;

let BINOM = prove
 (`!n k. binom(n,k) =
            if k <= n then FACT(n) DIV (FACT(n - k) * FACT(k))
            else 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[BINOM_EQ_0; GSYM NOT_LE] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
  SIMP_TAC[LT_MULT; FACT_LT; ADD_CLAUSES] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[GSYM BINOM_FACT; ADD_SUB] THEN REWRITE_TAC[MULT_AC]);;

(* ------------------------------------------------------------------------- *)
(* Numerical computation of binom.                                           *)
(* ------------------------------------------------------------------------- *)

let NUM_BINOM_CONV =
  let pth_step = prove
   (`binom(n,k) = y
     ==> k <= n
         ==> (SUC n) * y = ((n + 1) - k) * x ==> binom(SUC n,k) = x`,
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ADD1; GSYM BINOM_TOP_STEP; EQ_MULT_LCANCEL; SUB_EQ_0] THEN
    ARITH_TAC)
  and pth_0 = prove
   (`n < k ==> binom(n,k) = 0`,
    REWRITE_TAC[BINOM_LT])
  and pth_1 = prove
   (`binom(n,n) = 1`,
    REWRITE_TAC[BINOM_REFL])
  and k_tm = `k:num` and n_tm = `n:num`
  and x_tm = `x:num` and y_tm = `y:num`
  and binom_tm = `binom` in
  let rec BINOM_RULE(n,k) =
    if n </ k then
      let th = INST [mk_numeral n,n_tm; mk_numeral k,k_tm] pth_0 in
      MP_CONV NUM_LT_CONV th
    else if n =/ k then
      INST [mk_numeral n,n_tm] pth_1
    else
      let th1 = BINOM_RULE(n -/ Int 1,k) in
      let y = dest_numeral(rand(concl th1)) in
      let x = (n // (n -/ k)) */ y in
      let th2 = INST [mk_numeral(n -/ Int 1),n_tm; mk_numeral k,k_tm;
                      mk_numeral x,x_tm; mk_numeral y,y_tm] pth_step in
      let th3 = MP_CONV NUM_REDUCE_CONV (MP_CONV NUM_LE_CONV (MP th2 th1)) in
      CONV_RULE (LAND_CONV(RAND_CONV(LAND_CONV NUM_SUC_CONV))) th3 in
  fun tm ->
    let bop,nkp = dest_comb tm in
    if bop <> binom_tm then failwith "NUM_BINOM_CONV" else
    let nt,kt = dest_pair nkp in
    BINOM_RULE(dest_numeral nt,dest_numeral kt);;
