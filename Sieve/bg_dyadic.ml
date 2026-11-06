(* ========================================================================= *)
(* Bounded gaps between primes, part 4: the dyadic weight and the constants. *)
(*                                                                           *)
(* * The weight maynard_gdy J l0 r = sum_{j = 1..J} 2^-j [r < maynard_dyx l0 *)
(*   j], with maynard_dyx l0 j = exp((2^j - 1) l0).  MAYNARD_GDY_SUM and     *)
(*   MAYNARD_GDY_SQ_SUM reduce Lambda, Gamma and M1 to recip_phi_sum at the  *)
(*   thresholds maynard_dyx l0 j; DY_SUM1 (<= 1), DY_SUM2 (<= 3) and DY_SUM3 *)
(*   (<= 3 J) bound the numerical sums.                                      *)
(* * With c0 = prod_{p <= D0} (1 - 1/p) and W = prod_{p <= D0} p:            *)
(*   LAMBDA_DY_LOWER (c0 l0 (J - 1) <= Lambda), GAMMA_DY_UPPER,              *)
(*   GAMMA_DY_LOWER (c0 l0 / 4 <= Gamma) and M1_DY_UPPER.                    *)
(* * TITCHMARSH_K_LE_3: the Titchmarsh constant                              *)
(*   lim prod_{p <= n} (1 + 1/(p (p - 1))) is at most 3.                     *)
(* * RANKIN_COL_SET (Rankin's trick for the colourings with support product  *)
(*   < R), BV_DISC_TRIVIAL (bv_disc x d b <= 3 x / phi(d) for d <= x),       *)
(*   MERTENS_P_UPPER (prod_{D0 < p < R} (1 + 1/(p - 1)) <= c0 M2 log R) and  *)
(*   ETA_BOUND (eta <= 2 / D0).                                              *)
(* ========================================================================= *)

needs "Sieve/bg_weights.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The dyadic weight.                                                        *)
(* ------------------------------------------------------------------------- *)

let maynard_dyx = new_definition
 `maynard_dyx l0 j = exp((&2 pow j - &1) * l0)`;;

let maynard_gdy = new_definition
 `maynard_gdy J l0 r = sum (1..J) (\j. inv(&2 pow j) *
                               (if &r < maynard_dyx l0 j then &1 else &0))`;;

let MAYNARD_DYX_POS = prove
 (`!l0 j. &0 < maynard_dyx l0 j`,
  REWRITE_TAC[maynard_dyx; REAL_EXP_POS_LT]);;

let LOG_MAYNARD_DYX = prove
 (`!l0 j. log(maynard_dyx l0 j) = (&2 pow j - &1) * l0`,
  REWRITE_TAC[maynard_dyx; LOG_EXP]);;

let MAYNARD_DYX_MONO = prove
 (`!l0 i j. &0 <= l0 /\ i <= j ==> maynard_dyx l0 i <= maynard_dyx l0 j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[maynard_dyx; REAL_EXP_MONO_LE] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> a - &1 <= b - &1`) THEN
  MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MAYNARD_DYX_GE_1 = prove
 (`!l0 j. &0 <= l0 ==> &1 <= maynard_dyx l0 j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[maynard_dyx] THEN
  MATCH_MP_TAC(REAL_ARITH `!t. &0 <= t /\ &1 + t <= e ==> &1 <= e`) THEN
  EXISTS_TAC `(&2 pow j - &1) * l0` THEN REWRITE_TAC[REAL_EXP_LE_X] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_SUB_LE; REAL_LE_POW2]);;

let MAYNARD_DYX_GT_1 = prove
 (`!l0 j. &0 < l0 /\ 1 <= j ==> &1 < maynard_dyx l0 j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[maynard_dyx] THEN
  MATCH_MP_TAC REAL_EXP_LT_1 THEN MATCH_MP_TAC REAL_LT_MUL THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_POW_LT_1 THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC]);;

let MAYNARD_GDY_POS = prove
 (`!J l0 r. &0 <= maynard_gdy J l0 r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[maynard_gdy] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
  COND_CASES_TAC THEN REAL_ARITH_TAC);;

let MAYNARD_GDY_MONO = prove
 (`!J l0 r s. r <= s ==> maynard_gdy J l0 s <= maynard_gdy J l0 r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[maynard_gdy] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
  SUBGOAL_THEN `&r <= &s` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let MAYNARD_GDY_ZERO = prove
 (`!J l0 r. &0 <= l0 /\ maynard_dyx l0 J <= &r ==> maynard_gdy J l0 r = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[maynard_gdy] THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `maynard_dyx l0 j <= maynard_dyx l0 J` MP_TAC THENL
   [MATCH_MP_TAC MAYNARD_DYX_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let DY_GEOM = prove
 (`!J. sum (1..J) (\j. inv(&2 pow j)) = &1 - inv(&2 pow J)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    REWRITE_TAC[real_pow] THEN
    SUBGOAL_THEN `~(&2 pow J = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ];
      CONV_TAC REAL_FIELD]]);;

let MAYNARD_GDY_LE_1 = prove
 (`!J l0 r. maynard_gdy J l0 r <= &1`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (1..J) (\j. inv(&2 pow j))` THEN CONJ_TAC THENL
   [REWRITE_TAC[maynard_gdy] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[DY_GEOM] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 - x <= &1`) THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS]]);;

let SUM_POWERSET_FILTER = prove
 (`!P (Q:(num->bool)->bool) (f:(num->bool)->real).
     sum {A | A SUBSET P /\ Q A} f =
     sum {A | A SUBSET P} (\A. if Q A then f A else &0)`,
  REWRITE_TAC[GSYM SUM_RESTRICT_SET; IN_ELIM_THM]);;

let MAYNARD_GDY_SUM = prove
 (`!J l0 P (f:(num->bool)->real).
     FINITE P
     ==> sum {A | A SUBSET P}
           (\A. maynard_gdy J l0 (nproduct A (\p. p)) * f A) =
         sum (1..J) (\j. inv(&2 pow j) *
                         sum {A | A SUBSET P /\
                                  &(nproduct A (\p. p)) <
                                  maynard_dyx l0 j} f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[maynard_gdy; GSYM SUM_RMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_POWERSET; FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[SUM_POWERSET_FILTER; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `A:num->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REAL_ARITH_TAC);;

let IND_MIN = prove
 (`!l0 r i j.
     &0 <= l0
     ==> (if &r < maynard_dyx l0 i then &1 else &0) *
         (if &r < maynard_dyx l0 j then &1 else &0) =
         (if &r < maynard_dyx l0 (MIN i j) then &1 else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MIN] THEN
  ASM_CASES_TAC `i:num <= j` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `maynard_dyx l0 i <= maynard_dyx l0 j` MP_TAC THENL
     [MATCH_MP_TAC MAYNARD_DYX_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC];
    SUBGOAL_THEN `maynard_dyx l0 j <= maynard_dyx l0 i` MP_TAC THENL
     [MATCH_MP_TAC MAYNARD_DYX_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC]] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let MAYNARD_GDY_SQ = prove
 (`!J l0 r.
     &0 <= l0
     ==> maynard_gdy J l0 r pow 2 =
         sum (1..J) (\i. sum (1..J) (\j. inv(&2 pow i) * inv(&2 pow j) *
                           (if &r <
                            maynard_dyx l0 (MIN i j) then &1 else &0)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_2; maynard_gdy] THEN
  SIMP_TAC[REAL_MUL_SUM; FINITE_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN
    STRIP_TAC THEN
  REWRITE_TAC[] THEN ASM_SIMP_TAC[GSYM IND_MIN] THEN REAL_ARITH_TAC);;

let MAYNARD_GDY_SQ_SUM = prove
 (`!J l0 P (f:(num->bool)->real).
     FINITE P /\ &0 <= l0
     ==> sum {A | A SUBSET P}
             (\A. maynard_gdy J l0 (nproduct A (\p. p)) pow 2 * f A) =
         sum (1..J) (\i. sum (1..J) (\j. inv(&2 pow i) * inv(&2 pow j) *
           sum {A | A SUBSET P /\
                &(nproduct A (\p. p)) < maynard_dyx l0 (MIN i j)}
               f))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MAYNARD_GDY_SQ; GSYM SUM_RMUL; FINITE_NUMSEG] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_POWERSET; FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_POWERSET; FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[SUM_POWERSET_FILTER; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `A:num->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Numerical sums.                                                           *)
(* ------------------------------------------------------------------------- *)

let POW2_NZ = prove
 (`!n. ~(&2 pow n = &0)`,
  REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ]);;

let DY_LAMBDA_NUM = prove
 (`!J. &J - &1 <= sum (1..J) (\j. inv(&2 pow j) * (&2 pow j - &1))`,
  GEN_TAC THEN
  SUBGOAL_THEN `sum (1..J) (\j. inv(&2 pow j) * (&2 pow j - &1)) =
                sum (1..J) (\j. &1 - inv(&2 pow j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MP_TAC(SPEC `j:num` POW2_NZ) THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; SUM_CONST_NUMSEG; DY_GEOM; ADD_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &J - &1 <= &J * &1 - (&1 - x)`) THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS]);;

let DY_SUM1 = prove
 (`!J. sum (1..J) (\i. sum (1..J) (\j. inv(&2 pow i) * inv(&2 pow j)))
       <= &1`,
  GEN_TAC THEN SIMP_TAC[GSYM REAL_MUL_SUM; FINITE_NUMSEG; DY_GEOM] THEN
  SUBGOAL_THEN `&0 <= inv(&2 pow J) /\ inv(&2 pow J) <= &1` MP_TAC THENL
   [SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC[REAL_LE_POW2];
    ALL_TAC] THEN
  SPEC_TAC(`inv(&2 pow J)`,`t:real`) THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x * x <= &1 * &1 ==> x * x <= &1`) THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC);;

let DY_SUM2_EQ = prove
 (`!J. sum (1..J) (\i. sum (1..J) (\j. inv(&2 pow i) * inv(&2 pow j) *
                                      &2 pow (MIN i j))) =
       &3 - (&2 * &J + &3) * inv(&2 pow J)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sum (1..J) (\i. inv(&2 pow i) * inv(&2 pow SUC J) *
                    &2 pow (MIN i (SUC J))) = &J * inv(&2 pow SUC J) /\
    sum (1..J) (\j. inv(&2 pow SUC J) * inv(&2 pow j) *
                    &2 pow (MIN (SUC J) j)) = &J * inv(&2 pow SUC J)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum (1..J) (\i. inv(&2 pow SUC J))`
    THEN (CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB]])
    THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `i <= J ==> MIN i (SUC J) = i /\
                                       MIN (SUC J) i = i`] THEN
    MP_TAC(SPEC `i:num` POW2_NZ) THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[MIN; LE_REFL; real_pow; GSYM REAL_OF_NUM_SUC] THEN
  MP_TAC(SPEC `J:num` POW2_NZ) THEN CONV_TAC REAL_FIELD);;

let DY_SUM2 = prove
 (`!J. sum (1..J) (\i. sum (1..J) (\j. inv(&2 pow i) * inv(&2 pow j) *
                                      &2 pow (MIN i j))) <= &3`,
  GEN_TAC THEN REWRITE_TAC[DY_SUM2_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &3 - x <= &3`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 * x + &3`) THEN
  REWRITE_TAC[REAL_POS]);;

let DY_GEOM2 = prove
 (`!J. sum (1..J) (\i. &2 pow i) = &2 pow (SUC J) - &2`,
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; real_pow] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC]);;

let DY_SUM3_EQ = prove
 (`!J. sum (1..J) (\i. sum (1..J) (\j. inv(&2 pow i) * inv(&2 pow j) *
                                      (&2 pow (MIN i j)) pow 2)) =
       &3 * &J - &4 + &4 * inv(&2 pow J)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sum (1..J) (\i. inv(&2 pow i) * inv(&2 pow SUC J) *
                    (&2 pow (MIN i (SUC J))) pow 2) =
    inv(&2 pow SUC J) * sum (1..J) (\i. &2 pow i) /\
    sum (1..J) (\j. inv(&2 pow SUC J) * inv(&2 pow j) *
                    (&2 pow (MIN (SUC J) j)) pow 2) =
    inv(&2 pow SUC J) * sum (1..J) (\i. &2 pow i)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN CONJ_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `i <= J ==> MIN i (SUC J) = i /\
                                       MIN (SUC J) i = i`] THEN
    MP_TAC(SPEC `i:num` POW2_NZ) THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[DY_GEOM2; MIN; LE_REFL; real_pow; GSYM REAL_OF_NUM_SUC] THEN
  MP_TAC(SPEC `J:num` POW2_NZ) THEN CONV_TAC REAL_FIELD);;

let DY_SUM3 = prove
 (`!J. sum (1..J) (\i. sum (1..J) (\j. inv(&2 pow i) * inv(&2 pow j) *
                                      (&2 pow (MIN i j)) pow 2)) <= &3 * &J`,
  GEN_TAC THEN REWRITE_TAC[DY_SUM3_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> &3 * &J - &4 + &4 * x <= &3 * &J`) THEN
  MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC[REAL_LE_POW2]);;

(* ------------------------------------------------------------------------- *)
(* Lambda, Gamma and M1 for the dyadic weight.                               *)
(* ------------------------------------------------------------------------- *)

let MERTENS_C0_POS = prove
 (`!D0. &0 <= product {p | prime p /\ p <= D0} (\p. &1 - inv(&p))`,
  GEN_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
  REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_LE; PRIME_GE_2]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> &0 <= &1 - x`) THEN
  MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC);;

let LAMBDA_DY_LOWER = prove
 (`!J l0 D0 P.
     FINITE P /\ (!p. p IN P ==> prime p) /\
     (!p. prime p /\ D0 < p /\ &p < maynard_dyx l0 J ==> p IN P) /\ &0 <= l0
     ==> product {p | prime p /\ p <= D0} (\p. &1 - inv(&p)) * l0 * (&J - &1)
         <= sum {A | A SUBSET P}
                (\A. maynard_gdy J l0 (nproduct A (\p. p)) *
                     product A (\p. inv(&p - &1)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MAYNARD_GDY_SUM] THEN
  REWRITE_TAC[GSYM recip_phi_sum] THEN
  ABBREV_TAC `c0 = product {p | prime p /\ p <= D0} (\p. &1 - inv(&p))` THEN
  SUBGOAL_THEN `&0 <= c0` ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN REWRITE_TAC[MERTENS_C0_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (1..J) (\j. inv(&2 pow j) * (c0 * ((&2 pow j - &1) * l0)))`
  THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `sum (1..J) (\j. inv(&2 pow j) * (c0 * ((&2 pow j - &1) * l0))) =
      (c0 * l0) * sum (1..J) (\j. inv(&2 pow j) * (&2 pow j - &1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[DY_LAMBDA_NUM];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
  REWRITE_TAC[GSYM LOG_MAYNARD_DYX] THEN EXPAND_TAC "c0" THEN
  MATCH_MP_TAC RECIP_PHI_SUM_LOWER THEN ASM_SIMP_TAC[MAYNARD_DYX_GE_1] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `maynard_dyx l0 j` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MAYNARD_DYX_MONO THEN ASM_REWRITE_TAC[]);;

let DYW_FACTS = prove
 (`!D0. &1 <= &(nproduct {p | prime p /\ p <= D0} (\p. p)) /\
        &0 <= log(&(nproduct {p | prime p /\ p <= D0} (\p. p)))`,
  GEN_TAC THEN MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> 0 < n`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN REWRITE_TAC[FINITE_ATMOST;
     IN_ELIM_THM] THEN
    MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    DISCH_TAC THEN MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]]);;

let SUM_SUM_LINEAR = prove
 (`!m n p q c d (f:num->num->real) g.
     sum (m..n) (\i. sum (p..q) (\j. c * f i j + d * g i j)) =
     c * sum (m..n) (\i. sum (p..q) (\j. f i j)) +
     d * sum (m..n) (\i. sum (p..q) (\j. g i j))`,
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL]);;

let GAMMA_DY_UPPER = prove
 (`!Kt J l0 D0 P.
     ((\n. product {p | prime p /\ p <= n}
                   (\p. &1 + inv(&p * (&p - &1)))) ---> Kt) sequentially /\
     FINITE P /\ (!p. p IN P ==> prime p /\ D0 < p) /\ &0 <= l0
     ==> sum {A | A SUBSET P}
             (\A. maynard_gdy J l0 (nproduct A (\p. p)) pow 2 *
                  product A (\p. inv(&p - &1))) *
         product {p | prime p /\ p <= D0} (\p. &1 + inv(&p - &1))
         <= Kt * ((&1 + log(&(nproduct {p | prime p /\ p <= D0} (\p. p)))) +
                 &3 * l0)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MAYNARD_GDY_SQ_SUM] THEN
  REWRITE_TAC[GSYM recip_phi_sum; GSYM SUM_RMUL] THEN
  MP_TAC(SPEC `D0:num` DYW_FACTS) THEN
  ABBREV_TAC `W = nproduct {p | prime p /\ p <= D0} (\p. p)` THEN
  ABBREV_TAC `c1 = product {p | prime p /\ p <= D0} (\p. &1 + inv(&p - &1))`
  THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= Kt` ASSUME_TAC THENL
   [ASM_MESON_TAC[TITCHMARSH_K_GE_1]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (1..J) (\i. sum (1..J) (\j.
      (Kt * (&1 + log(&W))) * (inv(&2 pow i) * inv(&2 pow j)) +
      (Kt * l0) * (inv(&2 pow i) * inv(&2 pow j) * &2 pow (MIN i j))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= inv(&2 pow i) * inv(&2 pow j)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (inv(&2 pow i) * inv(&2 pow j)) * Kt * l0`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
             [`Kt:real`; `D0:num`; `P:num->bool`; `maynard_dyx l0 (MIN i j)`]
           RECIP_PHI_SUM_UPPER) THEN
    ASM_SIMP_TAC[MAYNARD_DYX_GE_1] THEN
    ASM_SIMP_TAC[LOG_MUL; MAYNARD_DYX_POS; REAL_ARITH `&1 <= x ==> &0 < x`;
                 LOG_MAYNARD_DYX] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o
      CONJ (ASSUME `&0 <= inv(&2 pow i) * inv(&2 pow j)`)) THEN
    UNDISCH_TAC `&0 <= (inv(&2 pow i) * inv(&2 pow j)) * Kt * l0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_SUM_LINEAR] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(Kt * a) * s1 <= (Kt * a) * &1 /\ (Kt * l) * s2 <= (Kt * l) * &3
    ==> (Kt * a) * s1 + (Kt * l) * s2 <= Kt * (a + &3 * l)`) THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[DY_SUM1; DY_SUM2] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

let MERTENS_C1_POS = prove
 (`!D0. &0 <= product {p | prime p /\ p <= D0} (\p. &1 + inv(&p - &1))`,
  GEN_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
  REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_LE; PRIME_GE_2]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
  REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC);;

let RECIP_PHI_SUM_LOG_BOUND = prove
 (`!P x. FINITE P /\ (!p. p IN P ==> 2 <= p) /\ &0 < x
         ==> sum {t | t SUBSET P /\ &(nproduct t (\p. p)) < x}
                 (\t. product t (\p. inv(&p - &1)) *
                      log(&(nproduct t (\p. p))))
             <= log x * recip_phi_sum P x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[recip_phi_sum; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
     EXISTS_TAC `{t:num->bool | t SUBSET P}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    SUBGOAL_THEN `2 <= p` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN MATCH_MP_TAC NPRODUCT_POS_LT THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `2 <= p` MP_TAC THENL [ASM SET_TAC[]; ARITH_TAC]]);;

let GAMMA_DY_LOWER = prove
 (`!J l0 D0 P.
     FINITE P /\ (!p. p IN P ==> prime p) /\
     (!p. prime p /\ D0 < p /\ &p < maynard_dyx l0 1 ==> p IN P) /\
     &0 <= l0 /\ 1 <= J
     ==> product {p | prime p /\ p <= D0} (\p. &1 - inv(&p)) * l0 / &4
         <= sum {A | A SUBSET P}
                (\A. maynard_gdy J l0 (nproduct A (\p. p)) pow 2 *
                     product A (\p. inv(&p - &1)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MAYNARD_GDY_SQ_SUM] THEN
    REWRITE_TAC[GSYM recip_phi_sum] THEN
  ABBREV_TAC `c0 = product {p | prime p /\ p <= D0} (\p. &1 - inv(&p))` THEN
  SUBGOAL_THEN `!x. &0 <= recip_phi_sum P x` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RECIP_PHI_SUM_POS THEN ASM_MESON_TAC[PRIME_GE_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j. &0 <= inv(&2 pow i) * inv(&2 pow j) *
                            recip_phi_sum P (maynard_dyx l0 (MIN i j))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (1..J) (\j. inv(&2 pow 1) * inv(&2 pow j) *
                              recip_phi_sum P (maynard_dyx l0 (MIN 1 j)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(BETA_RULE(ISPECL
     [`1..J`; `\i. sum (1..J) (\j. inv(&2 pow i) * inv(&2 pow j) *
                                  recip_phi_sum P
                                    (maynard_dyx l0 (MIN i j)))`; `1`]
     ELEMENT_LE_SUM)) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_REFL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `inv(&2 pow 1) * inv(&2 pow 1) *
     recip_phi_sum P (maynard_dyx l0 (MIN 1 1))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(BETA_RULE(ISPECL
     [`1..J`;
      `\j. inv(&2 pow 1) * inv(&2 pow j) *
           recip_phi_sum P (maynard_dyx l0 (MIN 1 j))`;
      `1`] ELEMENT_LE_SUM)) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_REFL]] THEN
  REWRITE_TAC[ARITH_RULE `MIN 1 1 = 1`] THEN
  MP_TAC(ISPECL [`D0:num`; `P:num->bool`; `maynard_dyx l0 1`]
           RECIP_PHI_SUM_LOWER) THEN
  ASM_SIMP_TAC[MAYNARD_DYX_GE_1; LOG_MAYNARD_DYX] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let M1_DY_UPPER = prove
 (`!Kt J l0 D0 P.
     ((\n. product {p | prime p /\ p <= n}
                   (\p. &1 + inv(&p * (&p - &1)))) ---> Kt) sequentially /\
     FINITE P /\ (!p. p IN P ==> prime p /\ D0 < p) /\ &0 <= l0
     ==> sum {A | A SUBSET P}
             (\A. (maynard_gdy J l0 (nproduct A (\p. p)) pow 2 *
                   product A (\p. inv(&p - &1))) *
                  log(&(nproduct A (\p. p)))) *
         product {p | prime p /\ p <= D0} (\p. &1 + inv(&p - &1))
         <= Kt * l0 *
            (&3 * (&1 + log(&(nproduct {p | prime p /\ p <= D0} (\p. p)))) +
             &3 * &J * l0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MAYNARD_GDY_SQ_SUM] THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
  MP_TAC(SPEC `D0:num` DYW_FACTS) THEN
    MP_TAC(SPEC `D0:num` MERTENS_C1_POS) THEN
  ABBREV_TAC `W = nproduct {p | prime p /\ p <= D0} (\p. p)` THEN
  ABBREV_TAC `c1 = product {p | prime p /\ p <= D0} (\p. &1 + inv(&p - &1))`
  THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= Kt` ASSUME_TAC THENL
   [ASM_MESON_TAC[TITCHMARSH_K_GE_1]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (1..J) (\i. sum (1..J) (\j.
      (Kt * l0 * (&1 + log(&W))) *
      (inv(&2 pow i) * inv(&2 pow j) * &2 pow (MIN i j)) +
      (Kt * l0 * l0) *
      (inv(&2 pow i) * inv(&2 pow j) * (&2 pow (MIN i j)) pow 2)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUM_SUM_LINEAR] THEN
    MATCH_MP_TAC(REAL_ARITH
     `(Kt * l * a) * s1 <= (Kt * l * a) * &3 /\
      (Kt * l * l) * s2 <= (Kt * l * l) * (&3 * &J)
      ==> (Kt * l * a) * s1 + (Kt * l * l) * s2 <=
          Kt * l * (&3 * a + &3 * &J * l)`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[DY_SUM2; DY_SUM3] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`P:num->bool`; `maynard_dyx l0 (MIN i j)`]
           RECIP_PHI_SUM_LOG_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MAYNARD_DYX_POS] THEN ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
  MP_TAC(ISPECL
           [`Kt:real`; `D0:num`; `P:num->bool`; `maynard_dyx l0 (MIN i j)`]
         RECIP_PHI_SUM_UPPER) THEN
  ASM_SIMP_TAC[MAYNARD_DYX_GE_1] THEN
  ASM_SIMP_TAC[LOG_MUL; MAYNARD_DYX_POS; REAL_ARITH `&1 <= x ==> &0 < x`;
               LOG_MAYNARD_DYX] THEN
  SUBGOAL_THEN `&0 <= recip_phi_sum P (maynard_dyx l0 (MIN i j))` MP_TAC THENL
   [MATCH_MP_TAC RECIP_PHI_SUM_POS THEN
    ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
  MP_TAC(SPEC `MIN i j` REAL_LE_POW2) THEN
  SUBGOAL_THEN `&0 <= inv(&2 pow i) /\ &0 <= inv(&2 pow j)` MP_TAC THENL
   [SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS]; ALL_TAC] THEN
  ABBREV_TAC
   `s = sum
      {A | A SUBSET P /\ &(nproduct A (\p. p)) < maynard_dyx l0 (MIN i j)}
            (\A. product A (\p. inv(&p - &1)) * log(&(nproduct A (\p. p))))`
  THEN
  ABBREV_TAC `r = recip_phi_sum P (maynard_dyx l0 (MIN i j))` THEN
  ABBREV_TAC `t = &2 pow (MIN i j)` THEN
  ABBREV_TAC `u1 = inv(&2 pow i)` THEN ABBREV_TAC `u2 = inv(&2 pow j)` THEN
  ABBREV_TAC `lw = log(&W)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(u1 * u2 * c1) * s <= (u1 * u2 * c1) * ((t - &1) * l0 * r)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(u1 * u2 * (t - &1) * l0) * (r * c1) <=
    (u1 * u2 * (t - &1) * l0) * (Kt * (&1 + lw + (t - &1) * l0))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u1 * u2 * Kt * l0 * (&1 + lw) /\
                &0 <= u1 * u2 * Kt * l0 * l0 * (&2 * t - &1)`
  MP_TAC THENL
   [CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Titchmarsh constant is at most 3.                                     *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_BERNOULLI = prove
 (`!(u:A->real) s B.
     FINITE s /\ (!x. x IN s ==> &0 <= u x)
     ==> product s (\x. &1 + &B * u x) <= product s (\x. &1 + u x) pow B`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM PRODUCT_POW_REAL] THEN
  MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (u:A->real) x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_LBOUND] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]);;

let SUM_TELESCOPE_INV = prove
 (`!a b. 2 <= a
         ==> sum (a..b) (\m. inv(&m * (&m - &1))) <= inv(&a - &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum (a..b) (\m. inv(&m * (&m - &1))) =
    sum (a..b) (\m. inv(&m - &1) - inv(&(m + 1) - &1))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN `&2 <= &m` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_DIFFS] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x - y <= x`) THEN
    REWRITE_TAC[REAL_LE_INV_EQ; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_LE_INV_EQ] THEN
    SUBGOAL_THEN `&2 <= &a` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; REAL_ARITH_TAC]]);;

let TITCHMARSH_K_LE_3 = prove
 (`!Kt. ((\n. product {p | prime p /\ p <= n}
                     (\p. &1 + inv(&p * (&p - &1)))) ---> Kt) sequentially
       ==> Kt <= &3`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\n. product {p | prime p /\ p <= n}
                          (\p. &1 + inv(&p * (&p - &1)))` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(sum {p | prime p /\ p <= n} (\p. inv(&p * (&p - &1))))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[REAL_EXP_SUM; FINITE_ATMOST] THEN MATCH_MP_TAC PRODUCT_LE THEN
    REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    STRIP_TAC THEN REWRITE_TAC[REAL_EXP_LE_X] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS; REAL_SUB_LE; REAL_OF_NUM_LE] THEN
    ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (2..n) (\m. inv(&m * (&m - &1)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
        MESON_TAC[PRIME_GE_2];
        ALL_TAC] THEN
      X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_DIFF; IN_NUMSEG] THEN
      STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_POS; REAL_SUB_LE; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MP_TAC(SPECL [`2`; `n:num`] SUM_TELESCOPE_INV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[]];
    MP_TAC E_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Rankin's trick; the trivial discrepancy bound.                            *)
(* ------------------------------------------------------------------------- *)

let RANKIN_COL_SET = prove
 (`!k P R B.
     FINITE P /\ (!p. p IN P ==> 1 <= p) /\ &0 <= B /\ &0 < R
     ==> sum {c | c IN col_set k P /\ &(nproduct (col_supp c) (\p. p)) < R}
             (\c. B pow CARD(col_supp c))
         <= R * product P (\p. &1 + &k * (B / &p))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `P:num->bool`;
   `\p:num. B / &p`] COL_SET_SUM_SUPP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  SUBGOAL_THEN `FINITE(col_set k P)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_COL_SET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c IN col_set k P ==> FINITE(col_supp c) /\ col_supp c SUBSET P`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `col_supp c SUBSET P` ASSUME_TAC THENL
     [UNDISCH_TAC `(c:num->num) IN col_set k P` THEN
      REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      ASM_MESON_TAC[FINITE_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c IN col_set k P ==> &0 <= product (col_supp c) (\p. B / &p)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {c | c IN col_set k P /\ &(nproduct (col_supp c) (\p. p)) < R}
        (\c. R * product (col_supp c) (\p. B / &p))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
  X_GEN_TAC `c:num->num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:num->num` o check (fun th ->
    can (find_term ((=) `FINITE:(num->bool)->bool`)) (concl th) &&
    is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `&(nproduct (col_supp c) (\p:num. p)) < R` THEN
  ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT; PRODUCT_DIV; GSYM PRODUCT_CONST] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < product (col_supp c) real_of_num` ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    SUBGOAL_THEN `1 <= p` MP_TAC THENL [ASM SET_TAC[]; ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= product (col_supp c) (\x:num. B)` ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let BV_DISC_TRIVIAL = prove
 (`!x d b. 1 <= d /\ d <= x ==> bv_disc x d b <= &3 * &x / &(phi d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bv_disc] THEN
  SUBGOAL_THEN `&1 <= &(phi d) /\ &(phi d) <= &d` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_LE; PHI_LOWERBOUND_1_STRONG; PHI_LIMIT];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(pi_ap x d b) <= &x / &d + &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(x DIV d) + &1` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + &1 <= b + &1`) THEN
      MP_TAC(SPECL [`x:num`; `d:num`] REAL_DIV_BOUNDS) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; pi_ap] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD {n | n IN 1..x /\ n MOD d = b MOD d}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
        X_GEN_TAC `p:num` THEN STRIP_TAC THEN
        ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`; CONG;
                      ARITH_RULE `1 <= d ==> ~(d = 0)`];
        MATCH_MP_TAC FINITE_RESTRICT THEN REWRITE_TAC[FINITE_NUMSEG]];
      MP_TAC(SPECL [`d:num`; `b MOD d`; `x:num`] CARD_RESIDUE_CLASS) THEN
      ASM_SIMP_TAC[DIVISION; ARITH_RULE `1 <= d ==> ~(d = 0)`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(pi_upto x) <= &x` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; pi_upto] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(1..x)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
      MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
      REWRITE_TAC[CARD_NUMSEG_1; LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&x / &d <= &x / &(phi d) /\ &1 <= &x / &(phi d) /\
                &(pi_upto x) / &(phi d) <= &x / &(phi d)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= &x /\ &1 <= &d` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV_DENOM; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&d` THEN
      ASM_REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE];
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&1 <= x ==> &0 < x`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &(pi_upto x) / &(phi d)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  MP_TAC(SPEC `pi_ap x d b` REAL_POS) THEN
  REWRITE_TAC[real_div] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A Mertens-type product bound; eta.                                        *)
(* ------------------------------------------------------------------------- *)

let MERTENS_P_UPPER = prove
 (`?M2. &0 < M2 /\
        !D0 R. 2 <= D0 /\ &D0 < R
               ==> product {p | prime p /\ D0 < p /\ &p < R}
                           (\p. &1 + inv(&p - &1))
                   <= product {p | prime p /\ p <= D0} (\p. &1 - inv(&p)) *
                      M2 * log R`,
  X_CHOOSE_TAC `Cm:real` MERTENS_PRODUCT_LOG THEN
  EXISTS_TAC `exp(Cm / log(&2)) / log(&2)` THEN
  SUBGOAL_THEN `&0 < log(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&D0` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&2`; `R:real`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ABBREV_TAC `Q = {p | prime p /\ &2 <= &p /\ &p < R}` THEN
  ABBREV_TAC `Wq = {p | prime p /\ p <= D0}` THEN
  ABBREV_TAC `P = {p | prime p /\ D0 < p /\ &p < R}` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `FINITE(Wq:num->bool) /\ FINITE(P:num->bool) /\
                Q = Wq UNION P /\ DISJOINT Wq P`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Q"; "Wq"; "P"] THEN REWRITE_TAC[FINITE_ATMOST] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(SPEC `R:real` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p:num | p < n}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM_MESON_TAC[REAL_LTE_TRANS];
      REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
      X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN
        ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `2 <= p` ASSUME_TAC THENL
       [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_CASES_TAC `p:num <= D0` THEN ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&D0` THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE];
        ASM_ARITH_TAC];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
       NOT_IN_EMPTY] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN Q ==> &2 <= &p` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(sum Q (\p. --log(&1 - inv(&p)))) =
    product Q (\p. &1 + inv(&p - &1))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_EXP_SUM; FINITE_UNION] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_EXP_NEG] THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &1 - inv(&p)` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x < &1 ==> &0 < &1 - x`) THEN
      MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[EXP_LOG] THEN UNDISCH_TAC `&2 <= &p` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product Q (\p. &1 + inv(&p - &1)) =
    product Wq (\p. &1 + inv(&p - &1)) * product P (\p. &1 + inv(&p - &1))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[PRODUCT_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN
   `product Wq (\p. &1 - inv(&p)) * product Wq (\p. &1 + inv(&p - &1)) = &1`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM PRODUCT_MUL] THEN
    MATCH_MP_TAC PRODUCT_EQ_1 THEN X_GEN_TAC `p:num` THEN
    EXPAND_TAC "Wq" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [ASM_MESON_TAC[PRIME_GE_2; REAL_OF_NUM_LE]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product P (\p. &1 + inv(&p - &1)) =
    product Wq (\p. &1 - inv(&p)) * exp(sum Q (\p. --log(&1 - inv(&p))))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `product Wq (\p. &1 - inv(&p)) *
                 product Wq (\p. &1 + inv(&p - &1)) = &1` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [EXPAND_TAC "Wq" THEN REWRITE_TAC[MERTENS_C0_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(log(log R) - log(log(&2)) + Cm / log(&2))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log R` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_ADD; REAL_EXP_SUB] THEN
  ASM_SIMP_TAC[EXP_LOG] THEN
  REWRITE_TAC[real_div; REAL_MUL_AC; REAL_LE_REFL]);;

let ETA_BOUND = prove
 (`!D0 R. 2 <= D0
          ==> sum {p | prime p /\ D0 < p /\ &p < R} (\p. inv(&p - &1) pow 2)
              <= &2 / &D0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `R:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (D0 + 1..n) (\m. inv(&m - &1) pow 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN X_GEN_TAC `p:num` THEN
      STRIP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * sum (D0 + 1..n) (\m. inv(&m * (&m - &1)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&3 <= &m` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`&m:real`,`y:real`) THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `inv(y - &1) pow 2 = inv((y - &1) pow 2) /\
                  &2 * inv(y * (y - &1)) = inv((y * (y - &1)) / &2)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[REAL_POW_INV] THEN
      UNDISCH_TAC `&3 <= y` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      REWRITE_TAC[REAL_POW_2] THEN
      SUBGOAL_THEN `&0 <= (y - &1) * (y - &3)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`D0 + 1`; `n:num`] SUM_TELESCOPE_INV) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(x + &1) - &1 = x`] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  REAL_ARITH_TAC);;
