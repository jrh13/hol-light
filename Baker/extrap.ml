(* ========================================================================= *)
(* The extrapolation argument: Baker Lemmas 6 and 7, analytic part.          *)
(*                                                                           *)
(* Purpose: for an abstract family f m of entire functions indexed by        *)
(* multi-indices m and closed under differentiation with coefficients,       *)
(* D (f m) = sum_{i<n} c m i f (m + e_i) + c0 m f m with coefficients of     *)
(* norm sum at most N (Baker, Transcendental Number Theory, Ch. 3;           *)
(* Sharpening I, Lemmas 7 and 8): bounds for the derivatives from bounds for *)
(* the family; the interpolation bound for the nodes 1..R of multiplicity S  *)
(* + 1 with explicit constants (from INTERPOLATION_RESIDUE_BOUND); one       *)
(* extrapolation step, from the nodes 1..R to the points l with R < l <= R   *)
(* prime, and the induction over a sequence of steps (Lemma 6); and the      *)
(* bound at the rational points l / k from smallness at the nodes 1..X       *)
(* (Lemma 7, analytic part). The family of Baker is the case c = 1, c0 = 0,  *)
(* N = n.                                                                    *)
(*                                                                           *)
(* Main results: EXTRAPOLATION_STEP_COEFF, EXTRAPOLATION_INDUCTION_COEFF     *)
(*   (Lemma 6 with coefficients), RATIONAL_EXTRAPOLATION_COEFF_GEN (Lemma 7  *)
(*   with coefficients, analytic part; also at l = 0) and its case           *)
(*   RATIONAL_EXTRAPOLATION_COEFF; DERIVATIVE_FAMILY_BOUND_COEFF; the cases  *)
(*   of Baker EXTRAPOLATION_INDUCTION and RATIONAL_EXTRAPOLATION;            *)
(*   RATIONAL_EXTRAPOLATION_ALL, INTEGER_NODES_INTERPOLATION_BOUND,          *)
(*   HIGHER_COMPLEX_DERIVATIVE_VSUM, HIGHER_COMPLEX_DERIVATIVE_LINCOMB,      *)
(*   NSUM_INCREMENT.                                                         *)
(*                                                                           *)
(* Uses: Baker/lemmas.ml (REAL_ABS_SUB_NUM_GE_1, REAL_LE_1_MUL),             *)
(*   Baker/delta.ml (BINOM_LE_EXP, NPRODUCT_SHIFT_BINOM,                     *)
(*   HIGHER_COMPLEX_DERIVATIVE_LMUL), Baker/residue.ml                       *)
(*   (INTERPOLATION_RESIDUE_BOUND).                                          *)
(* ========================================================================= *)

needs "Baker/residue.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Higher derivatives of a family closed under differentiation with          *)
(* coefficients: D f_m = sum_i c_m,i f_(m+e_i) + c0_m f_m.                   *)
(* ------------------------------------------------------------------------- *)

let HIGHER_COMPLEX_DERIVATIVE_VSUM = prove
 (`!(f:A->complex->complex) s t n z.
        FINITE t /\ open s /\ (!i. i IN t ==> f i holomorphic_on s) /\ z IN s
        ==> higher_complex_derivative n (\w. vsum t (\i. f i w)) z =
            vsum t (\i. higher_complex_derivative n (f i) z)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[VSUM_CLAUSES] THEN
    REWRITE_TAC[COMPLEX_VEC_0; HIGHER_COMPLEX_DERIVATIVE_CONST; COND_ID];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  DISCH_TAC THEN REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[VSUM_CLAUSES] THEN
  MP_TAC(ISPECL [`(f:A->complex->complex) a`;
                 `\w. vsum t (\i. (f:A->complex->complex) i w)`;
                 `s:complex->bool`; `n:num`; `z:complex`]
         HIGHER_COMPLEX_DERIVATIVE_ADD) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_VSUM THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[]]);;

let HIGHER_COMPLEX_DERIVATIVE_LINCOMB = prove
 (`!(g:A->complex->complex) h a b s j z.
        FINITE s /\ (!i. i IN s ==> g i holomorphic_on (:complex)) /\
        h holomorphic_on (:complex)
        ==> higher_complex_derivative j
             (\w. vsum s (\i. a i * g i w) + b * h w) z =
            vsum s (\i. a i * higher_complex_derivative j (g i) z) +
            b * higher_complex_derivative j h z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\w. vsum s (\i. (a:A->complex) i * (g:A->complex->complex) i w)`;
    `\w. (b:complex) * (h:complex->complex) w`;
    `(:complex)`; `j:num`; `z:complex`] HIGHER_COMPLEX_DERIVATIVE_ADD) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_VSUM THEN
      ASM_SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_CONST; ETA_AX];
      MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
      ASM_REWRITE_TAC[HOLOMORPHIC_ON_CONST; ETA_AX]];
    DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THENL
   [MP_TAC(ISPECL
     [`\i w. (a:A->complex) i * (g:A->complex->complex) i w`;
      `(:complex)`; `s:A->bool`; `j:num`; `z:complex`]
     HIGHER_COMPLEX_DERIVATIVE_VSUM) THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_CONST;
                 ETA_AX] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `i:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_LMUL THEN
    EXISTS_TAC `(:complex)` THEN ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV];
    MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_LMUL THEN
    EXISTS_TAC `(:complex)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]]);;

let NSUM_INCREMENT = prove
 (`!s (m:num->num) i. FINITE s /\ i IN s
           ==> nsum s (\r. if r = i then m r + 1 else m r) = nsum s m + 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. if r = i then (m:num->num) r + 1 else m r`;
                 `s:num->bool`; `i:num`] NSUM_DELETE) THEN
  MP_TAC(ISPECL [`m:num->num`; `s:num->bool`; `i:num`] NSUM_DELETE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC(ARITH_RULE `!a x y. x = y ==> (a + 1) + x = (a + y) + 1`) THEN
  MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC[IN_DELETE]);;

let DERIVATIVE_FAMILY_BOUND_COEFF = prove
 (`!f (c:(num->num)->num->complex) (c0:(num->num)->complex) n S N eps z.
     1 <= n /\ (!m. f m holomorphic_on (:complex)) /\
     (!m. complex_derivative (f m) =
          \w. vsum(0..n-1)
                (\i. c m i * f (\r. if r = i then m r + 1 else m r) w) +
              c0 m * f m w) /\
     (!m. nsum(0..n-1) m < S
          ==> sum(0..n-1) (\i. norm(c m i)) + norm(c0 m) <= &N) /\
     (!m. nsum(0..n-1) m <= S ==> norm(f m z) <= eps)
     ==> !j m. nsum(0..n-1) m + j <= S
               ==> norm(higher_complex_derivative j (f m) z) <=
                   &N pow j * eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= eps` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `\r:num. 0`) THEN
    REWRITE_TAC[NSUM_0; LE_0] THEN
    MESON_TAC[NORM_POS_LE; REAL_LE_TRANS];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [ASM_SIMP_TAC[higher_complex_derivative; ADD_CLAUSES; real_pow;
                 REAL_MUL_LID];
    ALL_TAC] THEN
  X_GEN_TAC `m:num->num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[higher_complex_derivative_alt] THEN
  MP_TAC(ISPECL
   [`\i. (f:(num->num)->complex->complex)
           (\r. if r = i then m r + 1 else m r)`;
    `(f:(num->num)->complex->complex) m`;
    `(c:(num->num)->num->complex) m`; `(c0:(num->num)->complex) m`;
    `0..n-1`; `j:num`; `z:complex`] HIGHER_COMPLEX_DERIVATIVE_LINCOMB) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `nsum(0..n-1) m < S` (ANTE_RES_THEN ASSUME_TAC) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `(sum(0..n-1) (\i. norm((c:(num->num)->num->complex) m i)) +
     norm((c0:(num->num)->complex) m)) * (&N pow j * eps)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(x:complex) <= a /\ norm(y:complex) <= b
      ==> norm(x + y) <= a + b`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`0..n-1`; `m:num->num`; `i:num`] NSUM_INCREMENT) THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[COMPLEX_NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    REWRITE_TAC[real_pow; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE;
                                                REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS]]);;

(* ------------------------------------------------------------------------- *)
(* Elementary estimates: partial sums of the exponential series, a           *)
(* factorial bound replacing W^(R S) by 16^W, and the product of the         *)
(* distances between integer nodes.                                          *)
(* ------------------------------------------------------------------------- *)

let REAL_EXP_PARTIAL_SUM_LE = prove
 (`!x:real n. &0 <= x ==> sum(0..n) (\j. x pow j / &(FACT j)) <= exp x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[exp; RE_DEF] THEN
  MATCH_MP_TAC(MATCH_MP
   (ONCE_REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> b ==> a /\ c ==> d`]
        LIM_COMPONENT_LBOUND)
   (REWRITE_RULE[sums] (SPEC `Cx x` CEXP_CONVERGES))) THEN
  SIMP_TAC[DIMINDEX_2; ARITH; TRIVIAL_LIMIT_SEQUENTIALLY;
           VSUM_COMPONENT; EVENTUALLY_SEQUENTIALLY; FROM_0; INTER_UNIV] THEN
  REWRITE_TAC[GSYM CX_DIV; GSYM RE_DEF; RE_CX; GSYM CX_POW] THEN
  EXISTS_TAC `n:num` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; SUBSET_NUMSEG; LE_REFL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_POS]);;

let NPRODUCT_SHIFT_DELETE_BOUND = prove
 (`!W R r. 1 <= r /\ r <= R /\ R <= W
           ==> nproduct(1..R) (\b. W + b) * 2 EXP (R - 1) <=
               W * 16 EXP W * FACT(r - 1) * FACT(R - r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= R` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NPRODUCT_SHIFT_BINOM] THEN
  SUBGOAL_THEN `FACT R = R * FACT(r - 1) * FACT(R - r) * binom(R - 1,R - r)`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`r - 1`; `R - r`] BINOM_FACT) THEN
    SUBGOAL_THEN `(r - 1) + (R - r) = R - 1` SUBST1_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(SPEC `R - 1` (CONJUNCT2 FACT)) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= R ==> SUC(R - 1) = R`];
    ALL_TAC] THEN
  TRANS_TAC LE_TRANS
   `((R * FACT(r - 1) * FACT(R - r) * 2 EXP (R - 1)) * 2 EXP (W + R)) *
    2 EXP (R - 1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL] THEN
    MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[BINOM_LE_EXP] THEN
    REPEAT(MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL]) THEN
    REWRITE_TAC[BINOM_LE_EXP];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (R - 1) * 2 EXP (W + R) * 2 EXP (R - 1) <= 16 EXP W`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD; SYM(NUM_REDUCE_CONV `2 EXP 4`);
                GSYM EXP_MULT] THEN
    REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC LE_TRANS
   `(2 EXP (R - 1) * 2 EXP (W + R) * 2 EXP (R - 1)) *
    R * FACT(r - 1) * FACT(R - r)` THEN
  CONJ_TAC THENL [REWRITE_TAC[MULT_AC; LE_REFL]; ALL_TAC] THEN
  TRANS_TAC LE_TRANS `16 EXP W * W * FACT(r - 1) * FACT(R - r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL];
    REWRITE_TAC[MULT_AC; LE_REFL]]);;

let PRODUCT_ABS_DIFF_LEFT = prove
 (`!r. product(1..r-1) (\b. abs(&r - &b)) = &(FACT(r - 1))`,
  GEN_TAC THEN
  SUBGOAL_THEN `1..r-1 = IMAGE (\c. r - c) (1..r-1)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [th])
  THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_NUMSEG] THEN X_GEN_TAC `x:num` THEN
    EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `r - x:num` THEN ASM_ARITH_TAC;
      STRIP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) PRODUCT_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[GSYM NPRODUCT_FACT; REAL_OF_NUM_NPRODUCT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `c <= r` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  REWRITE_TAC[REAL_ARITH `x - (x - y) = y:real`; REAL_ABS_NUM]);;

let PRODUCT_ABS_DIFF_RIGHT = prove
 (`!r k. product(r+1..r+k) (\b. abs(&r - &b)) = &(FACT k)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [SUBGOAL_THEN `r+1..r+0 = {}` SUBST1_TAC THENL
     [REWRITE_TAC[NUMSEG_EMPTY] THEN ARITH_TAC;
      REWRITE_TAC[PRODUCT_CLAUSES; FACT]];
    ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; PRODUCT_CLAUSES_NUMSEG;
              ARITH_RULE `r + 1 <= SUC(r + k)`] THEN
  ASM_REWRITE_TAC[FACT; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ARITH `x - ((x + y) + &1) = --(y + &1)`; REAL_ABS_NEG] THEN
  REWRITE_TAC[REAL_ARITH `abs(&k + &1) = &k + &1`] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

let PRODUCT_ABS_DIFF_DELETE = prove
 (`!r R. 1 <= r /\ r <= R
         ==> product((1..R) DELETE r) (\b. abs(&r - &b)) =
             &(FACT(r - 1)) * &(FACT(R - r))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(1..R) DELETE r = (1..r-1) UNION (r+1..r+(R-r))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DELETE; IN_UNION; IN_NUMSEG] THEN
    X_GEN_TAC `x:num` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) PRODUCT_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG; DISJOINT_NUMSEG] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[PRODUCT_ABS_DIFF_LEFT; PRODUCT_ABS_DIFF_RIGHT]);;

let REAL_POW_RATIO_INV_LE = prove
 (`!x y c e k.
        &0 <= x /\ x <= c * y /\ &0 < y /\ &0 < e
        ==> x pow k * inv(inv e * y pow k) <= e * c pow k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < y pow k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `(c * y) pow k * inv(inv e * y pow k)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ]];
    REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `&0 < y pow k` THEN UNDISCH_TAC `&0 < e` THEN
    CONV_TAC REAL_FIELD]);;


(* ------------------------------------------------------------------------- *)
(* Interpolation bound for a finite set s of nodes of multiplicity S + 1     *)
(* with mutual distances at least 2 d: the big circle |z| = rho, small       *)
(* circles of radius d around the nodes, Taylor coefficients bounded by      *)
(* n^j eps / j!.                                                             *)
(* ------------------------------------------------------------------------- *)

let CIRCLE_NODES_LOWER_BOUND = prove
 (`!s w z t rho.
        FINITE s /\ norm w <= rho / &2 /\
        (!a. a IN s ==> norm a <= rho / &2) /\ norm z = rho
        ==> (rho / &2) * (rho / &2) pow (CARD s * (t + 1)) <=
            norm((z - w) * cproduct s (\a. (z - a) pow (t + 1)))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[COMPLEX_NORM_MUL; NORM_CPRODUCT; COMPLEX_NORM_POW] THEN
  SUBGOAL_THEN `&0 <= rho / &2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `w:complex` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(rho / &2) pow (CARD s * (t + 1)) =
    product s (\a:complex. (rho / &2) pow (t + 1))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[PRODUCT_CONST; REAL_POW_POW] THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`norm(w:complex) <= rho / &2`;
                           `norm(z:complex) = rho`] THEN
    CONV_TAC NORM_ARITH;
    MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[REAL_POW_LE];
    MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `a:complex` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_POW_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:complex`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `norm(z:complex) = rho` THEN CONV_TAC NORM_ARITH]);;

let SMALL_CIRCLE_NODES_UPPER_BOUND = prove
 (`!s w a z d t.
        FINITE s /\ a IN s /\ &0 < d /\ &2 * d <= norm(w - a) /\
        (!b. b IN s /\ ~(b = a) ==> &2 * d <= norm(a - b)) /\
        norm(z - a) = d
        ==> norm(inv((z - w) *
                     cproduct (s DELETE a) (\b. (z - b) pow (t + 1)))) <=
            inv(d * product (s DELETE a) (\b. norm(a - b) / &2) pow (t + 1))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CPRODUCT_POW; FINITE_DELETE] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_INV; COMPLEX_NORM_MUL; FINITE_DELETE;
               COMPLEX_NORM_POW; NORM_CPRODUCT] THEN
  SUBGOAL_THEN
   `&0 < product (s DELETE a) (\b:complex. norm(a - b) / &2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
    X_GEN_TAC `b:complex` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `b:complex`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&2 * d <= norm(w - a:complex)`;
                           `norm(z - a:complex) = d`] THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
  X_GEN_TAC `b:complex` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:complex`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `a - b:complex` NORM_POS_LE) THEN
  UNDISCH_TAC `norm(z - a:complex) = d` THEN CONV_TAC NORM_ARITH);;

let TAYLOR_COEFF_SUM_BOUND = prove
 (`!g n S eps u d.
        &0 <= eps /\ &0 <= u /\ &0 < d /\ d <= &1 /\
        (!j. j <= S ==> g j <= &n pow j * eps)
        ==> sum(0..S) (\j. g j / &(FACT j) * u / d pow (S - j)) <=
            eps * u * inv(d) pow S * exp(&n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= inv d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(0..S) (\j. &n pow j / &(FACT j) * eps * u * inv(d) pow S)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &(FACT j)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT]; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `(&n pow j * eps) * (inv(&(FACT j)) * u) * inv(d) pow (S - j)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_div; REAL_POW_INV; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `(a * e) * (f * u) * p:real = (a * f * e * u) * p`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LE; REAL_POS; REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ALL_TAC]) THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_RMUL] THEN
  GEN_REWRITE_TAC RAND_CONV
   [REAL_ARITH `a * b * c * d:real = d * a * b * c`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_EXP_PARTIAL_SUM_LE; REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC);;

let INTERPOLATION_NODES_BOUND = prove
 (`!f s S w rho d M eps n.
     f holomorphic_on (:complex) /\ FINITE s /\ &0 < rho /\
     norm w <= rho / &2 /\ (!a. a IN s ==> norm a <= rho / &2) /\
     &0 < d /\ d <= &1 /\
     (!a. a IN s ==> &2 * d <= norm(w - a)) /\
     (!a b. a IN s /\ b IN s /\ ~(b = a) ==> &2 * d <= norm(a - b)) /\
     (!z. norm z = rho ==> norm(f z) <= M) /\
     &0 <= eps /\
     (!a j. a IN s /\ j <= S
            ==> norm(higher_complex_derivative j f a) <= &n pow j * eps)
     ==> norm(f w) <=
         norm(cproduct s (\a. (w - a) pow (S + 1))) *
         rho * M / ((rho / &2) * (rho / &2) pow (CARD s * (S + 1))) +
         eps * inv(d) pow S * exp(&n) *
         sum s (\a. norm(cproduct s (\b. (w - b) pow (S + 1))) *
                    inv(d * product (s DELETE a) (\b. norm(a - b) / &2)
                            pow (S + 1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~((w:complex) IN s)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `!a:complex. a IN s ==> &2 * d <= norm(w - a)` THEN
    DISCH_THEN(MP_TAC o SPEC `w:complex`) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:complex. a IN s ==> &0 <= inv(d * product (s DELETE a)
                                  (\b. norm(a - b) / &2) pow (S + 1))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
    ASM_SIMP_TAC[FINITE_DELETE; REAL_LE_DIV; NORM_POS_LE; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`f:complex->complex`; `s:complex->bool`; `S:num`; `w:complex`;
    `Cx(&0)`; `rho:real`; `d:real`; `M:real`;
    `(rho / &2) * (rho / &2) pow (CARD(s:complex->bool) * (S + 1))`;
    `\a:complex. inv(d * product (s DELETE a) (\b. norm(a - b) / &2)
                         pow (S + 1))`]
   INTERPOLATION_RESIDUE_BOUND) THEN
  REWRITE_TAC[COMPLEX_SUB_RZERO] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `a:complex` THEN DISCH_TAC THEN
      UNDISCH_TAC `!a:complex. a IN s ==> norm a <= rho / &2` THEN
      DISCH_THEN(MP_TAC o SPEC `a:complex`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `a:complex` THEN DISCH_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `!a:complex. a IN s ==> &2 * d <= norm(w - a)` THEN
        DISCH_THEN(MP_TAC o SPEC `a:complex`) THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `b:complex` THEN STRIP_TAC THEN
        UNDISCH_TAC `!a b:complex. a IN s /\ b IN s /\ ~(b = a)
                                   ==> &2 * d <= norm(a - b)` THEN
        DISCH_THEN(MP_TAC o SPECL [`a:complex`; `b:complex`]) THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`a:complex`; `b:complex`] NORM_SUB) THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_ARITH `&0 < x ==> &0 < x / &2`];
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC CIRCLE_NODES_LOWER_BOUND THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`a:complex`; `z:complex`] THEN STRIP_TAC THEN
      MATCH_MP_TAC SMALL_CIRCLE_NODES_UPPER_BOUND THEN ASM_SIMP_TAC[] THEN
      X_GEN_TAC `b:complex` THEN STRIP_TAC THEN
      UNDISCH_TAC `!a b:complex. a IN s /\ b IN s /\ ~(b = a)
                                 ==> &2 * d <= norm(a - b)` THEN
      DISCH_THEN(MP_TAC o SPECL [`a:complex`; `b:complex`]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `P = norm(cproduct s (\a:complex. (w - a) pow (S + 1)))` THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z:real`) THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  REWRITE_TAC[REAL_LE_REFL] THEN REWRITE_TAC[SUM_LMUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `e * i * x * p * u:real = p * e * i * x * u`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:complex` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `e * i * x * u:real = e * u * i * x`] THEN
  MATCH_MP_TAC TAYLOR_COEFF_SUM_BOUND THEN ASM_SIMP_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Integer nodes 1..R: prod_{b <> r} |r - b| = (r - 1)! (R - r)!, hence      *)
(* prod_b |w - b| <= W 16^W prod_{b <> r} |r - b| / 2 for |w| <= W, R <= W;  *)
(* this gives the interpolation bound with explicit constants.               *)
(* ------------------------------------------------------------------------- *)

let INTEGER_NODES_PRODUCT_RATIO = prove
 (`!w R r W.
        1 <= r /\ r <= R /\ R <= W /\ norm w <= &W
        ==> product(1..R) (\b. norm(w - Cx(&b))) <=
            (&W * &16 pow W) *
            product((1..R) DELETE r) (\b. abs(&r - &b) / &2)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[PRODUCT_DIV; FINITE_DELETE; FINITE_NUMSEG; PRODUCT_CONST] THEN
  ASM_SIMP_TAC[PRODUCT_ABS_DIFF_DELETE; CARD_DELETE; FINITE_NUMSEG;
               IN_NUMSEG; CARD_NUMSEG_1] THEN
  TRANS_TAC REAL_LE_TRANS `product(1..R) (\b. &W + &b)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    REWRITE_TAC[NORM_POS_LE] THEN
    MP_TAC(NORM_ARITH `norm(w - Cx(&b)) <= norm w + norm(Cx(&b))`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_NPRODUCT; FINITE_NUMSEG] THEN
  MP_TAC(SPECL [`W:num`; `R:num`; `r:num`] NPRODUCT_SHIFT_DELETE_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW] THEN
  MP_TAC(SPECL [`&2:real`; `R - 1`] REAL_POW_LT) THEN
  REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
  SPEC_TAC(`&2 pow (R - 1)`, `y:real`) THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_binary "real_le" o concl)) THEN
  REWRITE_TAC[REAL_MUL_ASSOC]);;

let INTERPOLATION_MAIN_TERM_BOUND = prove
 (`!x rho M W R S.
        &0 <= x /\ x <= (&2 * &W) pow R /\ &0 <= M /\ &0 < rho
        ==> x pow (S + 1) * rho * M /
            ((rho / &2) * (rho / &2) pow (R * (S + 1))) <=
            &2 * M * (&4 * &W / rho) pow (R * (S + 1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x pow (S + 1) <= (&2 * &W) pow (R * (S + 1))` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&4 * &W / rho) pow (R * (S + 1)) =
    (&2 * &W) pow (R * (S + 1)) / (rho / &2) pow (R * (S + 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_DIV] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(SPECL [`rho / &2`; `R * (S + 1)`] REAL_POW_LT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`(rho / &2) pow (R * (S + 1))`, `A:real`) THEN
  SPEC_TAC(`(&2 * &W) pow (R * (S + 1))`, `B:real`) THEN
  SPEC_TAC(`x pow (S + 1)`, `X:real`) THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `X * rho * M / (rho / &2 * A) = (&2 * M * X) / A /\
                &2 * M * B / A = (&2 * M * B) / A`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `&0 < A` THEN UNDISCH_TAC `&0 < rho` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REAL_ARITH_TAC);;

let NORM_CPRODUCT_INTEGER_NODES = prove
 (`!w R S. norm(cproduct (IMAGE (\r. Cx(&r)) (1..R)) (\a. (w - a) pow S)) =
           product(1..R) (\b. norm(w - Cx(&b))) pow S`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CPRODUCT_POW; FINITE_IMAGE; FINITE_NUMSEG] THEN
  SIMP_TAC[COMPLEX_NORM_POW; NORM_CPRODUCT; FINITE_IMAGE; FINITE_NUMSEG] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) PRODUCT_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [SIMP_TAC[CX_INJ; REAL_OF_NUM_EQ]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF]);;

let PRODUCT_INTEGER_NODES_DELETE = prove
 (`!R r. product (IMAGE (\x. Cx(&x)) (1..R) DELETE Cx(&r))
                 (\b. norm(Cx(&r) - b) / &2) =
         product ((1..R) DELETE r) (\b. abs(&r - &b) / &2)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\x. Cx(&x)`; `1..R`; `r:num`] IMAGE_DELETE_INJ) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [SIMP_TAC[CX_INJ; REAL_OF_NUM_EQ]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) PRODUCT_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [SIMP_TAC[CX_INJ; REAL_OF_NUM_EQ]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN
  REWRITE_TAC[o_THM; GSYM CX_SUB; COMPLEX_NORM_CX]);;

let INTEGER_NODES_INTERPOLATION_BOUND = prove
 (`!f n R S q W w rho M eps.
     f holomorphic_on (:complex) /\ 1 <= R /\ R <= W /\ 1 <= q /\
     norm w <= &W /\
     (!r. 1 <= r /\ r <= R ==> inv(&q) <= norm(w - Cx(&r))) /\
     &4 * &W <= rho /\
     (!z. norm z = rho ==> norm(f z) <= M) /\
     (!r j. 1 <= r /\ r <= R /\ j <= S
            ==> norm(higher_complex_derivative j f (Cx(&r))) <=
                &n pow j * eps)
     ==> norm(f w) <=
         &2 * M * (&4 * &W / rho) pow (R * (S + 1)) +
         eps * &2 * &q * &R * (&2 * &q) pow S * exp(&n) *
         (&W * &16 pow W) pow (S + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &W /\ &1 <= &q /\ &R <= &W` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(f:complex->complex)(Cx rho)` NORM_POS_LE) THEN
    SUBGOAL_THEN `norm((f:complex->complex)(Cx rho)) <= M` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= eps` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`1`; `0`]) THEN
    REWRITE_TAC[LE_REFL; LE_0; real_pow; REAL_MUL_LID] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `higher_complex_derivative 0 (f:complex->complex) (Cx(&1))`
                 NORM_POS_LE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * inv(&2 * &q) = inv(&q)` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 <= &q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(IMAGE (\r. Cx(&r)) (1..R))` ASSUME_TAC THENL
   [SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(w:complex) <= rho / &2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!a. a IN IMAGE (\r. Cx(&r)) (1..R) ==> norm a <= rho / &2`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&r <= &R` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&2 * &q) /\ inv(&2 * &q) <= &1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a IN IMAGE (\r. Cx(&r)) (1..R) ==> &2 * inv(&2 * &q) <= norm(w - a)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. a IN IMAGE (\r. Cx(&r)) (1..R) /\ b IN IMAGE (\r. Cx(&r)) (1..R) /\
          ~(b = a) ==> &2 * inv(&2 * &q) <= norm(a - b)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN X_GEN_TAC `y:num` THEN DISCH_TAC THEN
    REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC REAL_LE_TRANS `&1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_ABS_SUB_NUM_GE_1 THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a j. a IN IMAGE (\r. Cx(&r)) (1..R) /\ j <= S
          ==> norm(higher_complex_derivative j f a) <= &n pow j * eps`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`f:complex->complex`; `IMAGE (\r. Cx(&r)) (1..R)`; `S:num`; `w:complex`;
    `rho:real`; `inv(&2 * &q)`; `M:real`; `eps:real`; `n:num`]
   INTERPOLATION_NODES_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= a' /\ b <= b' ==> x <= a + b ==> x <= a' + b':real`) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `CARD(IMAGE (\r. Cx(&r)) (1..R)) = R` SUBST1_TAC THENL
     [SIMP_TAC[CARD_IMAGE_INJ; CX_INJ; REAL_OF_NUM_EQ; FINITE_NUMSEG;
               CARD_NUMSEG_1];
      ALL_TAC] THEN
    REWRITE_TAC[NORM_CPRODUCT_INTEGER_NODES] THEN
    MATCH_MP_TAC INTERPOLATION_MAIN_TERM_BOUND THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN REWRITE_TAC[NORM_POS_LE];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `product(1..R) (\b. &2 * &W)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
      REWRITE_TAC[NORM_POS_LE] THEN
      MP_TAC(NORM_ARITH `norm(w - Cx(&b)) <= norm w + norm(Cx(&b))`) THEN
      REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
      SUBGOAL_THEN `&b <= &W` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
      REWRITE_TAC[PRODUCT_CONST_NUMSEG_1; REAL_LE_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_INV_INV] THEN
  SIMP_TAC[SUM_IMAGE; CX_INJ; REAL_OF_NUM_EQ] THEN
  REWRITE_TAC[o_DEF; NORM_CPRODUCT_INTEGER_NODES;
              PRODUCT_INTEGER_NODES_DELETE] THEN
  TRANS_TAC REAL_LE_TRANS
   `eps * (&2 * &q) pow S * exp(&n) *
    sum(1..R) (\r. (&2 * &q) * (&W * &16 pow W) pow (S + 1))` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LE; REAL_EXP_POS_LE; REAL_LE_MUL; REAL_POS];
      ALL_TAC]) THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_RATIO_INV_LE THEN
    ASM_SIMP_TAC[INTEGER_NODES_PRODUCT_RATIO] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC PRODUCT_POS_LT THEN
      REWRITE_TAC[FINITE_DELETE; FINITE_NUMSEG; IN_DELETE] THEN
      X_GEN_TAC `b:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 < x / &2`) THEN
      MATCH_MP_TAC REAL_ABS_SUB_NUM_GE_1 THEN ASM_MESON_TAC[];
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(R + 1) - 1 = R`] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Baker Lemma 6: one extrapolation step (nodes 1..R, derivatives of order   *)
(* up to S from smallness for |m| <= 2 S, new points l with R < l up to the  *)
(* bound R prime) and the induction over a sequence of such steps; first     *)
(* with coefficients (Sharpening I), then the case c = 1, c0 = 0 of Baker.   *)
(* ------------------------------------------------------------------------- *)

let EXTRAPOLATION_STEP_COEFF = prove
 (`!f (c:(num->num)->num->complex) (c0:(num->num)->complex)
    n R R' S rho M V eps N.
     1 <= n /\
     (!m. f m holomorphic_on (:complex)) /\
     (!m. complex_derivative (f m) =
          \z. vsum(0..n-1)
                (\i. c m i * f (\r. if r = i then m r + 1 else m r) z) +
              c0 m * f m z) /\
     (!m. nsum(0..n-1) m < 2 * S
          ==> sum(0..n-1) (\i. norm(c m i)) + norm(c0 m) <= &N) /\
     1 <= R /\ R <= R' /\ &4 * &R' <= rho /\
     (!m r. nsum(0..n-1) m <= 2 * S /\ 1 <= r /\ r <= R
            ==> norm(f m (Cx(&r))) <= eps) /\
     (!m z. nsum(0..n-1) m <= S /\ norm z = rho ==> norm(f m z) <= M) /\
     (!m l. nsum(0..n-1) m <= S /\ R < l /\ l <= R'
            ==> norm(f m (Cx(&l))) <= eps \/ V < norm(f m (Cx(&l)))) /\
     &2 * M * (&4 * &R' / rho) pow (R * (S + 1)) +
     eps * &2 * &R * &2 pow S * exp(&N) * (&R' * &16 pow R') pow (S + 1)
     <= V
     ==> !m l. nsum(0..n-1) m <= S /\ R < l /\ l <= R'
               ==> norm(f m (Cx(&l))) <= eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`m:num->num`; `l:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(V < norm((f:(num->num)->complex->complex) m (Cx(&l))))`
  MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[REAL_NOT_LT] THEN
  TRANS_TAC REAL_LE_TRANS
   `&2 * M * (&4 * &R' / rho) pow (R * (S + 1)) +
    eps * &2 * &R * &2 pow S * exp(&N) * (&R' * &16 pow R') pow (S + 1)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(f:(num->num)->complex->complex) m`; `N:num`; `R:num`;
                 `S:num`; `1`; `R':num`; `Cx(&l)`; `rho:real`; `M:real`;
                 `eps:real`] INTEGER_NODES_INTERPOLATION_BOUND) THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[LE_REFL; COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_OF_NUM_LE;
                  REAL_INV_1] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC REAL_ABS_SUB_NUM_GE_1 THEN ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`r:num`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:(num->num)->complex->complex`;
                   `c:(num->num)->num->complex`; `c0:(num->num)->complex`;
                   `n:num`; `2 * S`; `N:num`; `eps:real`; `Cx(&r)`]
                  DERIVATIVE_FAMILY_BOUND_COEFF) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let EXTRAPOLATION_INDUCTION_COEFF = prove
 (`!f (c:(num->num)->num->complex) (c0:(num->num)->complex)
    n R S rho M V eps J N.
     1 <= n /\
     (!m. f m holomorphic_on (:complex)) /\
     (!m. complex_derivative (f m) =
          \z. vsum(0..n-1)
                (\i. c m i * f (\r. if r = i then m r + 1 else m r) z) +
              c0 m * f m z) /\
     (!m. nsum(0..n-1) m < S 0
          ==> sum(0..n-1) (\i. norm(c m i)) + norm(c0 m) <= &N) /\
     1 <= R 0 /\
     (!K. K < J
          ==> R K <= R(K + 1) /\ 2 * S(K + 1) <= S K /\
              &4 * &(R(K + 1)) <= rho K /\
              (!m z. nsum(0..n-1) m <= S(K + 1) /\ norm z = rho K
                     ==> norm(f m z) <= M K) /\
              (!m l. nsum(0..n-1) m <= S(K + 1) /\ R K < l /\ l <= R(K + 1)
                     ==> norm(f m (Cx(&l))) <= eps \/
                         V K < norm(f m (Cx(&l)))) /\
              &2 * M K * (&4 * &(R(K + 1)) / rho K)
                         pow (R K * (S(K + 1) + 1)) +
              eps * &2 * &(R K) * &2 pow (S(K + 1)) * exp(&N) *
              (&(R(K + 1)) * &16 pow (R(K + 1))) pow (S(K + 1) + 1)
              <= V K) /\
     (!m l. nsum(0..n-1) m <= S 0 /\ 1 <= l /\ l <= R 0
            ==> norm(f m (Cx(&l))) <= eps)
     ==> !m l. nsum(0..n-1) m <= S J /\ 1 <= l /\ l <= R J
               ==> norm(f m (Cx(&l))) <= eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!K. K <= J
        ==> 1 <= R K /\ (S:num->num) K <= S 0 /\
            !m l. nsum(0..n-1) m <= S K /\ 1 <= l /\ l <= R K
                  ==> norm((f:(num->num)->complex->complex) m (Cx(&l))) <=
                      eps`
   (fun th -> MESON_TAC[th; LE_REFL]) THEN
  INDUCT_TAC THENL [ASM_REWRITE_TAC[LE_0; LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[ADD1] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `K:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:(num->num)->complex->complex`;
                 `c:(num->num)->num->complex`; `c0:(num->num)->complex`;
                 `n:num`; `(R:num->num) K`; `(R:num->num)(K + 1)`;
                 `(S:num->num)(K + 1)`; `(rho:num->real) K`;
                 `(M:num->real) K`; `(V:num->real) K`; `eps:real`; `N:num`]
                EXTRAPOLATION_STEP_COEFF) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num->num`; `l:num`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `l <= (R:num->num) K` THENL
   [SUBGOAL_THEN `nsum(0..n-1) m <= (S:num->num) K` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_MESON_TAC[]];
    SUBGOAL_THEN `(R:num->num) K < l` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_MESON_TAC[]]]);;

let EXTRAPOLATION_INDUCTION = prove
 (`!f n R S rho M V eps J.
     1 <= n /\
     (!m. f m holomorphic_on (:complex)) /\
     (!m. complex_derivative (f m) =
          \z. vsum(0..n-1) (\i. f (\r. if r = i then m r + 1 else m r) z)) /\
     1 <= R 0 /\
     (!K. K < J
          ==> R K <= R(K + 1) /\ 2 * S(K + 1) <= S K /\
              &4 * &(R(K + 1)) <= rho K /\
              (!m z. nsum(0..n-1) m <= S(K + 1) /\ norm z = rho K
                     ==> norm(f m z) <= M K) /\
              (!m l. nsum(0..n-1) m <= S(K + 1) /\ R K < l /\ l <= R(K + 1)
                     ==> norm(f m (Cx(&l))) <= eps \/
                         V K < norm(f m (Cx(&l)))) /\
              &2 * M K * (&4 * &(R(K + 1)) / rho K)
                         pow (R K * (S(K + 1) + 1)) +
              eps * &2 * &(R K) * &2 pow (S(K + 1)) * exp(&n) *
              (&(R(K + 1)) * &16 pow (R(K + 1))) pow (S(K + 1) + 1)
              <= V K) /\
     (!m l. nsum(0..n-1) m <= S 0 /\ 1 <= l /\ l <= R 0
            ==> norm(f m (Cx(&l))) <= eps)
     ==> !m l. nsum(0..n-1) m <= S J /\ 1 <= l /\ l <= R J
               ==> norm(f m (Cx(&l))) <= eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:(num->num)->complex->complex`;
                 `\(m:num->num) (i:num). Cx(&1)`; `\m:num->num. Cx(&0)`;
                 `n:num`; `R:num->num`; `S:num->num`; `rho:num->real`;
                 `M:num->real`; `V:num->real`; `eps:real`; `J:num`; `n:num`]
    EXTRAPOLATION_INDUCTION_COEFF) THEN
  REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; SUM_CONST_NUMSEG; REAL_ADD_RID;
              REAL_MUL_RID; REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `1 <= n` THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Baker Lemma 7, analytic part: the member f m0 at the rational points      *)
(* l / k, 0 <= l <= k X, from smallness at the nodes 1..X; with              *)
(* coefficients, then the case c = 1, c0 = 0, m0 = 0 of Baker.               *)
(* ------------------------------------------------------------------------- *)

let RATIONAL_EXTRAPOLATION_COEFF_GEN = prove
 (`!f (c:(num->num)->num->complex) (c0:(num->num)->complex)
    n X Y m0 q l rho M eps N.
     1 <= n /\
     (!m. f m holomorphic_on (:complex)) /\
     (!m. complex_derivative (f m) =
          \z. vsum(0..n-1)
                (\i. c m i * f (\r. if r = i then m r + 1 else m r) z) +
              c0 m * f m z) /\
     (!m. nsum(0..n-1) m < nsum(0..n-1) m0 + Y
          ==> sum(0..n-1) (\i. norm(c m i)) + norm(c0 m) <= &N) /\
     1 <= X /\ 1 <= q /\ l <= q * X /\ (~(q divides l) \/ l = 0) /\
     &4 * &X <= rho /\
     (!z. norm z = rho ==> norm(f m0 z) <= M) /\
     (!m r. nsum(0..n-1) m <= nsum(0..n-1) m0 + Y /\ 1 <= r /\ r <= X
            ==> norm(f m (Cx(&r))) <= eps)
     ==> norm(f m0 (Cx(&l) / Cx(&q))) <=
         &2 * M * (&4 * &X / rho) pow (X * (Y + 1)) +
         eps * &2 * &q * &X * (&2 * &q) pow Y * exp(&N) *
         (&X * &16 pow X) pow (Y + 1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < &q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx(&q) = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC INTEGER_NODES_INTERPOLATION_BOUND THEN
  ASM_REWRITE_TAC[LE_REFL] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(l = q * r)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
      REWRITE_TAC[NUMBER_RULE `q divides q * r`; MULT_EQ_0] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `Cx(&l) / Cx(&q) - Cx(&r) = Cx((&l - &(q * r)) / &q)`
    SUBST1_TAC THENL
     [REWRITE_TAC[CX_DIV; CX_SUB; GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
      UNDISCH_TAC `~(Cx(&q) = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_DIV; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
    MATCH_MP_TAC REAL_ABS_SUB_NUM_GE_1 THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`r:num`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:(num->num)->complex->complex`;
                   `c:(num->num)->num->complex`; `c0:(num->num)->complex`;
                   `n:num`; `nsum(0..n-1) (m0:num->num) + Y`; `N:num`;
                   `eps:real`; `Cx(&r)`] DERIVATIVE_FAMILY_BOUND_COEFF) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let RATIONAL_EXTRAPOLATION_COEFF = prove
 (`!f (c:(num->num)->num->complex) (c0:(num->num)->complex)
    n X Y m0 q l rho M eps N.
     1 <= n /\
     (!m. f m holomorphic_on (:complex)) /\
     (!m. complex_derivative (f m) =
          \z. vsum(0..n-1)
                (\i. c m i * f (\r. if r = i then m r + 1 else m r) z) +
              c0 m * f m z) /\
     (!m. nsum(0..n-1) m < nsum(0..n-1) m0 + Y
          ==> sum(0..n-1) (\i. norm(c m i)) + norm(c0 m) <= &N) /\
     1 <= X /\ 1 <= q /\ l <= q * X /\ ~(q divides l) /\ &4 * &X <= rho /\
     (!z. norm z = rho ==> norm(f m0 z) <= M) /\
     (!m r. nsum(0..n-1) m <= nsum(0..n-1) m0 + Y /\ 1 <= r /\ r <= X
            ==> norm(f m (Cx(&r))) <= eps)
     ==> norm(f m0 (Cx(&l) / Cx(&q))) <=
         &2 * M * (&4 * &X / rho) pow (X * (Y + 1)) +
         eps * &2 * &q * &X * (&2 * &q) pow Y * exp(&N) *
         (&X * &16 pow X) pow (Y + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(SPECL
   [`f:(num->num)->complex->complex`; `c:(num->num)->num->complex`;
    `c0:(num->num)->complex`; `n:num`; `X:num`; `Y:num`; `m0:num->num`;
    `q:num`; `l:num`; `rho:real`; `M:real`; `eps:real`; `N:num`]
   RATIONAL_EXTRAPOLATION_COEFF_GEN) THEN
  ASM_REWRITE_TAC[]);;

let RATIONAL_EXTRAPOLATION = prove
 (`!f n X Y k l rho M eps.
     1 <= n /\
     (!m. f m holomorphic_on (:complex)) /\
     (!m. complex_derivative (f m) =
          \z. vsum(0..n-1) (\i. f (\r. if r = i then m r + 1 else m r) z)) /\
     1 <= X /\ 1 <= k /\ l <= k * X /\ (~(k divides l) \/ l = 0) /\
     &4 * &X <= rho /\
     (!z. norm z = rho ==> norm(f (\r. 0) z) <= M) /\
     (!m r. nsum(0..n-1) m <= Y /\ 1 <= r /\ r <= X
            ==> norm(f m (Cx(&r))) <= eps)
     ==> norm(f (\r. 0) (Cx(&l) / Cx(&k))) <=
         &2 * M * (&4 * &X / rho) pow (X * (Y + 1)) +
         eps * &2 * &k * &X * (&2 * &k) pow Y * exp(&n) *
         (&X * &16 pow X) pow (Y + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:(num->num)->complex->complex`;
                 `\(m:num->num) (i:num). Cx(&1)`; `\m:num->num. Cx(&0)`;
                 `n:num`; `X:num`; `Y:num`; `\r:num. 0`; `k:num`; `l:num`;
                 `rho:real`; `M:real`; `eps:real`; `n:num`]
    RATIONAL_EXTRAPOLATION_COEFF_GEN) THEN
  REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID;
              NSUM_0; ADD_CLAUSES] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; SUM_CONST_NUMSEG; REAL_ADD_RID;
              REAL_MUL_RID; REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `1 <= n` THEN ARITH_TAC);;

let RATIONAL_EXTRAPOLATION_NODE = prove
 (`!f:(num->num)->complex->complex n X Y k l eps.
     1 <= k /\ k divides l /\ ~(l = 0) /\ l <= k * X /\
     (!m r. nsum(0..n-1) m <= Y /\ 1 <= r /\ r <= X
            ==> norm(f m (Cx(&r))) <= eps)
     ==> norm(f (\r. 0) (Cx(&l) / Cx(&k))) <= eps`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `x:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `Cx(&(k * x)) / Cx(&k) = Cx(&x)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
    SUBGOAL_THEN `~(Cx(&k) = Cx(&0))` MP_TAC THENL
     [REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
      CONV_TAC COMPLEX_FIELD];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[NSUM_0; LE_0] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; LE_MULT_LCANCEL; DE_MORGAN_THM]) THEN
  ASM_ARITH_TAC);;

let RATIONAL_EXTRAPOLATION_ALL = prove
 (`!f n X Y k l rho M eps.
     1 <= n /\
     (!m. f m holomorphic_on (:complex)) /\
     (!m. complex_derivative (f m) =
          \z. vsum(0..n-1) (\i. f (\r. if r = i then m r + 1 else m r) z)) /\
     1 <= X /\ 1 <= k /\ l <= k * X /\ &4 * &X <= rho /\
     (!z. norm z = rho ==> norm(f (\r. 0) z) <= M) /\
     (!m r. nsum(0..n-1) m <= Y /\ 1 <= r /\ r <= X
            ==> norm(f m (Cx(&r))) <= eps)
     ==> norm(f (\r. 0) (Cx(&l) / Cx(&k))) <=
         &2 * M * (&4 * &X / rho) pow (X * (Y + 1)) +
         eps * &2 * &k * &X * (&2 * &k) pow Y * exp(&n) *
         (&X * &16 pow X) pow (Y + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `~(k divides l) \/ l = 0` THENL
   [MATCH_MP_TAC RATIONAL_EXTRAPOLATION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
  TRANS_TAC REAL_LE_TRANS `eps:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RATIONAL_EXTRAPOLATION_NODE THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `X:num`; `Y:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &k /\ &1 <= &X` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= rho` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(f:(num->num)->complex->complex) (\r. 0) (Cx rho)`
                 NORM_POS_LE) THEN
    SUBGOAL_THEN `norm((f:(num->num)->complex->complex) (\r. 0) (Cx rho)) <= M`
    MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= eps` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(f:(num->num)->complex->complex) (\r. 0) (Cx(&1))`
                 NORM_POS_LE) THEN
    SUBGOAL_THEN
     `norm((f:(num->num)->complex->complex) (\r. 0) (Cx(&1))) <= eps`
    MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[NSUM_0; LE_0; LE_REFL];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ e <= b ==> e <= a + b:real`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
  TRY(MATCH_MP_TAC REAL_POW_LE_1) THEN
  TRY(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
  TRY(MATCH_MP_TAC REAL_POW_LE_1) THEN
  ASM_REWRITE_TAC[] THEN TRY(CONV_TAC REAL_RAT_REDUCE_CONV) THEN
  MP_TAC(SPEC `&n` REAL_EXP_LE_X) THEN MP_TAC(SPEC `n:num` REAL_POS) THEN
  REAL_ARITH_TAC);;
