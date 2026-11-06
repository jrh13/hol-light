(* ========================================================================= *)
(* A density estimate for the W-tricked primes in a fixed residue class.     *)
(*                                                                           *)
(* GT_DENSITY: for each w, the sum of (phi(W)/W) log(W n + 1) over n < h     *)
(* with W n + 1 prime is at least h/2 for all large h, where W = gtW w.      *)
(* This uses THETA_AP_UNIFORM, from Siegel-Walfisz.  The dense-subset        *)
(* Green-Tao proof in gt_green_tao.ml obtains its density by the prime       *)
(* number theorem and residue pigeonholing; this is a separate corollary.    *)
(* ========================================================================= *)

needs "Sieve/gt_majorant.ml";;
needs "Sieve/sw_theta.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The density of the W-tricked primes.                                      *)
(* ------------------------------------------------------------------------- *)

let THETA_W_SUM = prove
 (`!W h. 1 <= W
         ==> sum {n | n < h} (\n. if prime(W * n + 1) then log(&(W * n + 1))
                                 else &0) =
             sum {p | prime p /\ p <= W * h /\ (p == 1) (mod W)}
               (\p. log(&p))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SUBGOAL_THEN
   `{p | prime p /\ p <= W * h /\ (p == 1) (mod W)} =
    IMAGE (\n. W * n + 1) {n | n IN {n | n < h} /\ prime(W * n + 1)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN MP_TAC(SPECL [`W:num`; `p:num`] CONG_1_DIVIDES) THEN
      ASM_REWRITE_TAC[divides] THEN
      DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
      SUBGOAL_THEN `p = W * n + 1` ASSUME_TAC THENL
       [MP_TAC(SPEC `p:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
      UNDISCH_TAC `W * n + 1 <= W * h` THEN REWRITE_TAC[NOT_LE] THEN
      MATCH_MP_TAC(ARITH_RULE `(a:num) <= b ==> a < b + 1`) THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL];
      DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(W:num) * (n + 1)` THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
        CONV_TAC NUMBER_RULE]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `(W:num) * x + 1 = W * y + 1` THEN
    REWRITE_TAC[EQ_ADD_RCANCEL; EQ_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let GT_DENSITY = prove
 (`!W. 1 <= W
       ==> ?h0. !h. h0 <= h
                ==> &h / &2 <=
                    sum {n | n < h}
                        (\n. if prime(W * n + 1)
                             then &(phi W) / &W * log(&(W * n + 1))
                             else &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`1`; `1`] THETA_AP_UNIFORM) THEN REWRITE_TAC[REAL_POW_1] THEN
  DISCH_THEN(X_CHOOSE_TAC `Cb:real`) THEN
  MP_TAC(SPEC `exp(&W + &2 * abs Cb * &W) + &2` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `h0:num`) THEN EXISTS_TAC `h0:num` THEN
  X_GEN_TAC `h:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= &(phi W) /\ &(phi W) <= &W /\ &1 <= &W`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; PHI_LIMIT] THEN
    ASM_SIMP_TAC[PHI_LOWERBOUND_1_STRONG];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= abs Cb * &W` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(&W + &2 * abs Cb * &W) + &2 <= &W * &h` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&h0` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `h:num` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `(h:num) = 1 * h`] THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= &W * &h /\ &W + &2 * abs Cb * &W <= log(&W * &h)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `&W + &2 * abs Cb * &W` REAL_EXP_POS_LT) THEN
      ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&W * &h) /\ abs Cb * &W <= log(&W * &h) / &2`
  STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (if prime(W * n + 1) then &(phi W) / &W * log(&(W * n + 1)) else &0) =
        &(phi W) / &W *
        (if prime(W * n + 1) then log(&(W * n + 1)) else &0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO]; ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN ASM_SIMP_TAC[THETA_W_SUM] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&W * &h:real`; `W:num`; `1`; `(W:num) * h`] o
    check (fun th -> is_forall(concl th))) THEN
  REWRITE_TAC[COPRIME_1; GSYM REAL_OF_NUM_MUL; REAL_LE_REFL] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `th = sum {p | prime p /\ p <= W * h /\ (p == 1) (mod W)}
                       (\p. log(&p))` THEN
  ABBREV_TAC `L = log(&W * &h)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&W * &h) / &(phi W) - abs Cb * (&W * &h) / L <= th`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `!a b c. abs(th - a) <= c /\ c <= b ==> a - b <= th`) THEN
    EXISTS_TAC `Cb * (&W * &h) / L` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_POS] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(phi W) / &W *
              ((&W * &h) / &(phi W) - abs Cb * (&W * &h) / L)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN
   `&(phi W) / &W * ((&W * &h) / &(phi W) - abs Cb * (&W * &h) / L) =
    &h - (abs Cb * &(phi W)) * &h / L`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&1 <= &(phi W)`; `&1 <= &W`; `&0 < L`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= h / &2 ==> h / &2 <= h - x`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(L / &2) * (&h / L)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs Cb * &W` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < L` THEN
    CONV_TAC REAL_FIELD]);;
