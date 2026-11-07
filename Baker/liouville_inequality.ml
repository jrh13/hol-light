(* ========================================================================= *)
(* Liouville inequality for integer polynomials in algebraic numbers.        *)
(*                                                                           *)
(* Purpose: a nonzero integer polynomial expression g theta in numbers       *)
(* theta r, each a root of an explicit integer polynomial a r of degree d r  *)
(* with coefficients bounded by h r, is bounded below explicitly in terms of *)
(* D = prod_r d r, the size of g and the h r. The roots of a r multiplied by *)
(* its leading coefficient are the roots of a monic integer polynomial, so   *)
(* their power sums are integers (INTEGER_POLY_ROOTS_SCALED); clearing the   *)
(* denominators (INTPOLY_SCALE) reduces the claim to                         *)
(* INTPOLY_LIOUVILLE_MONIC. Also the root bound norm z <= 1 + d h.           *)
(*                                                                           *)
(* Main results: INTPOLY_LIOUVILLE (the Liouville inequality),               *)
(*   INTEGER_POLY_ROOT_BOUND, INTEGER_POLY_ROOTS_SCALED, INTPOLY_SCALE.      *)
(*                                                                           *)
(* Uses: Baker/prelim.ml (complex integers), Baker/algebraic.ml              *)
(*   (COMPLEX_POLYFUN_FACTOR, NEWTON_INTEGER_POWER_SUMS), Baker/intpoly.ml   *)
(*   (intpoly, INTPOLY_LIOUVILLE_MONIC).                                     *)
(* ========================================================================= *)

needs "Baker/intpoly.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Roots of an integer polynomial, scaled by the leading coefficient, are    *)
(* the roots of a monic integer polynomial, so their power sums are integers.*)
(* ------------------------------------------------------------------------- *)

let INTEGER_POLY_ROOTS_SCALED = prove
 (`!a d. (!j. integer(a j)) /\ ~(a d = &0)
         ==> ?rho. (!x. vsum(0..d) (\j. Cx(a j) * x pow j) =
                        Cx(a d) * cproduct(1..d) (\i. x - rho i)) /\
                   (!k. complex_integer
                          (vsum(1..d) (\i. (Cx(a d) * rho i) pow k)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:num`; `\j. Cx((a:num->real) j)`]
    COMPLEX_POLYFUN_FACTOR) THEN
  ASM_REWRITE_TAC[CX_INJ] THEN
  DISCH_THEN(X_CHOOSE_TAC `rho:num->complex`) THEN
  EXISTS_TAC `rho:num->complex` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`1..d`; `\i. Cx((a:num->real) d) * (rho:num->complex) i`;
                 `\j. if j = d then Cx(&1)
                      else Cx((a:num->real) j) * Cx(a d) pow (d - 1 - j)`]
        NEWTON_INTEGER_POWER_SUMS) THEN
  REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[COMPLEX_INTEGER_CX_NUM; COMPLEX_INTEGER_MUL;
                 COMPLEX_INTEGER_POW; COMPLEX_INTEGER_CX]] THEN
  X_GEN_TAC `x:complex` THEN ASM_CASES_TAC `d = 0` THENL
   [ASM_REWRITE_TAC[CPRODUCT_CLAUSES_NUMSEG; ARITH; VSUM_SING_NUMSEG;
                    complex_pow; COMPLEX_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Cx((a:num->real) d) pow d = Cx(a d) * Cx(a d) pow (d - 1)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM(CONJUNCT2 complex_pow);
                 ARITH_RULE `~(d = 0) ==> SUC(d - 1) = d`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cproduct(1..d) (\i. x - Cx((a:num->real) d) * (rho:num->complex) i) =
    Cx(a d) pow d * cproduct(1..d) (\i. x / Cx(a d) - rho i)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `Cx((a:num->real) d) pow d = cproduct(1..d) (\i. Cx(a d))`
    SUBST1_TAC THENL
     [REWRITE_TAC[CPRODUCT_CONST_NUMSEG] THEN AP_TERM_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[GSYM CPRODUCT_MUL; FINITE_NUMSEG] THEN
      MATCH_MP_TAC CPRODUCT_EQ THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `~((a:num->real) d = &0)` THEN REWRITE_TAC[GSYM CX_INJ] THEN
    CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `(a * b) * c:complex = b * a * c`] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(SPEC `x / Cx((a:num->real) d)` th)]) THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[COMPLEX_POW_DIV] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(COMPLEX_FIELD
     `~(a = Cx(&0)) /\ ~(p = Cx(&0))
      ==> p * a * (y / (a * p)) = Cx(&1) * y`) THEN
    ASM_REWRITE_TAC[COMPLEX_POW_EQ_0; CX_INJ];
    SUBGOAL_THEN
     `Cx((a:num->real) d) pow (d - 1) =
      Cx(a d) pow (d - 1 - j) * Cx(a d) pow j`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM COMPLEX_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_POW_DIV] THEN
    MATCH_MP_TAC(COMPLEX_FIELD
     `~(p = Cx(&0)) ==> (q * p) * c * (y / p) = (c * q) * y`) THEN
    ASM_REWRITE_TAC[COMPLEX_POW_EQ_0; CX_INJ]]);;

let INTEGER_POLY_ROOT_BOUND = prove
 (`!a d h z.
        (!j. integer(a j)) /\ ~(a d = &0) /\ (!j. abs(a j) <= h) /\
        vsum(0..d) (\j. Cx(a j) * z pow j) = Cx(&0)
        ==> norm z <= &1 + &d * h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= h` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS]; ALL_TAC] THEN
  ASM_CASES_TAC `norm(z:complex) <= &1` THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= &1 /\ &0 <= y ==> x <= &1 + y`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  ASM_CASES_TAC `d = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `vsum (0..0) (\j. Cx(a j) * z pow j) = Cx(&0)` THEN
    ASM_REWRITE_TAC[VSUM_SING_NUMSEG; complex_pow; COMPLEX_MUL_RID; CX_INJ];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z:complex) pow d <= &d * h * norm z pow (d - 1)`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `norm(Cx(a d) * (z:complex) pow d)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_POW] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; NORM_POS_LE; REAL_ABS_INTEGER_LEMMA];
      ALL_TAC] THEN
    UNDISCH_TAC `vsum (0..d) (\j. Cx(a j) * z pow j) = Cx(&0)` THEN
    SUBGOAL_THEN `0 < d /\ 0 <= d`
     (fun th -> REWRITE_TAC[MATCH_MP VSUM_CLAUSES_RIGHT th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_RING `s + p:complex = Cx(&0) <=> p = --s`] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NORM_NEG] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum(0..d-1) (\j. h * norm(z:complex) pow (d - 1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_POW] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_ABS_POS; REAL_POW_LE; NORM_POS_LE] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[SUM_CONST_NUMSEG] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(d = 0) ==> (d - 1 + 1) - 0 = d`] THEN
      REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z:complex) pow d = norm z * norm z pow (d - 1)`
  SUBST_ALL_TAC THENL
   [ASM_SIMP_TAC[GSYM(CONJUNCT2 real_pow);
                 ARITH_RULE `~(d = 0) ==> SUC(d - 1) = d`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(z:complex) pow (d - 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [REAL_MUL_ASSOC]) THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Clearing denominators: substituting x r / a r into an integer polynomial  *)
(* and multiplying by prod_r a r pow n r gives an integer polynomial.        *)
(* ------------------------------------------------------------------------- *)

let INTPOLY_SCALE = prove
 (`!v n b g (a:num->real).
        FINITE v /\ intpoly v n b g /\
        (!r. r IN v ==> integer(a r) /\ ~(a r = &0))
        ==> intpoly v n (b * product v (\r. abs(a r) pow n r))
              (\y. Cx(product v (\r. a r pow n r)) * g(\r. y r / Cx(a r)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[intpoly] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`s:num->bool`;
    `\k. (c:num->real) k *
         product v (\r. (a:num->real) r pow (n r - (e:num->num->num) k r))`;
    `e:num->num->num`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC(el 3 (CONJUNCTS INTEGER_CLOSED)) THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC INTEGER_PRODUCT THEN
    ASM_SIMP_TAC[INTEGER_CLOSED];
    TRANS_TAC REAL_LE_TRANS
     `sum s (\k. abs((c:num->real) k) *
                 product v (\r. abs((a:num->real) r) pow n r))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_SIMP_TAC[GSYM PRODUCT_ABS; REAL_ABS_POW] THEN
      MATCH_MP_TAC PRODUCT_LE THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_ABS_POS] THEN
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_POW_MONO THEN
      ASM_SIMP_TAC[REAL_ABS_INTEGER_LEMMA] THEN ARITH_TAC;
      ASM_SIMP_TAC[SUM_RMUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_ABS_POS]];
    X_GEN_TAC `x:num->complex` THEN ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[CX_MUL; CX_PRODUCT; CX_POW] THEN
    MATCH_MP_TAC(COMPLEX_RING
     `p * q = s * t ==> p * w * q = (w * s) * t:complex`) THEN
    ASM_SIMP_TAC[GSYM CPRODUCT_MUL] THEN MATCH_MP_TAC CPRODUCT_EQ THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `Cx((a:num->real) r) pow n r =
      Cx(a r) pow (n r - (e:num->num->num) k r) * Cx(a r) pow e k r`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM COMPLEX_POW_ADD] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(GSYM SUB_ADD) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_POW_DIV] THEN
    MATCH_MP_TAC(COMPLEX_FIELD
     `~(q = Cx(&0)) ==> (p * q) * (y / q) = p * y`) THEN
    ASM_SIMP_TAC[COMPLEX_POW_EQ_0; CX_INJ]]);;

let LIOUVILLE_INEQ_LEMMA = prove
 (`!f m1 m2 p1 p2 y k.
        &1 <= f /\ &1 <= m1 /\ m1 <= m2 /\ &0 < p1 /\ p1 <= p2 /\
        inv(f * m1 pow k) <= p1 * y
        ==> inv(f * m2 pow k * p2) <= y`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `inv(f * m1 pow k) / p1` THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    SUBGOAL_THEN `&0 < m1 pow k` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The general Liouville inequality: a nonzero integer polynomial expression *)
(* in roots of integer polynomials is bounded below explicitly.              *)
(* ------------------------------------------------------------------------- *)

let INTPOLY_LIOUVILLE = prove
 (`!v n b g (theta:num->complex) (a:num->num->real) d h.
        FINITE v /\ intpoly v n b g /\
        (!r. r IN v
             ==> (!j. integer(a r j) /\ abs(a r j) <= h r) /\
                 ~(a r (d r) = &0) /\
                 vsum(0..d r) (\j. Cx(a r j) * theta r pow j) = Cx(&0)) /\
        ~(g theta = Cx(&0))
        ==> inv(&(FACT(nproduct v d)) *
                (max (&1) (b * product v (\r. h r pow n r) *
                           product v (\r. (h r * (&1 + &(d r) * h r)) pow n r)))
                pow (nproduct v d - 1) *
                product v (\r. h r pow n r))
            <= norm(g theta)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?rho. !r. r IN v
              ==> (!x. vsum(0..d r)
                         (\j. Cx((a:num->num->real) r j) * x pow j) =
                       Cx(a r (d r)) * cproduct(1..d r) (\i. x - rho r i)) /\
                  (!k. complex_integer
                        (vsum(1..d r) (\i. (Cx(a r (d r)) * rho r i) pow k)))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RIGHT_EXISTS_IMP_THM; GSYM SKOLEM_THM] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC INTEGER_POLY_ROOTS_SCALED THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?t. !r. r IN v
            ==> t r IN 1..d r /\ (rho:num->num->complex) r (t r) = theta r`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RIGHT_EXISTS_IMP_THM; GSYM SKOLEM_THM] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `(theta:num->complex) r` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ] THEN
    DISCH_THEN(MP_TAC o SYM) THEN ASM_REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ] THEN
    SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG; COMPLEX_SUB_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `A = \r. (a:num->num->real) r (d r)` THEN
  SUBGOAL_THEN
   `!r. r IN v
        ==> integer((A:num->real) r) /\ ~(A r = &0) /\
            abs(A r) <= h r /\ &1 <= h r`
  ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[REAL_ABS_INTEGER_LEMMA; REAL_LE_TRANS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:num->bool`; `n:num->num`; `b:real`;
                 `g:(num->complex)->complex`; `A:num->real`] INTPOLY_SCALE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`v:num->bool`; `n:num->num`;
    `b * product v (\r. abs((A:num->real) r) pow n r)`;
    `\y. Cx(product v (\r. (A:num->real) r pow n r)) *
         (g:(num->complex)->complex)(\r. y r / Cx(A r))`;
    `d:num->num`; `\r i. Cx((A:num->real) r) * (rho:num->num->complex) r i`;
    `RESTRICTION v (t:num->num)`;
    `\r. (h:num->real) r * (&1 + &(d r) * h r)`]
   INTPOLY_LIOUVILLE_MONIC) THEN
  SUBGOAL_THEN
   `(g:(num->complex)->complex)
      (\r. (Cx((A:num->real) r) * (rho:num->num->complex) r
              (RESTRICTION v t r)) / Cx(A r)) =
    g theta`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTPOLY_EQ_ON THEN
    MAP_EVERY EXISTS_TAC [`v:num->bool`; `n:num->num`; `b:real`] THEN
    ASM_REWRITE_TAC[RESTRICTION] THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(COMPLEX_FIELD
     `~(p = Cx(&0)) /\ y = z ==> (p * y) / p = z`) THEN
    ASM_SIMP_TAC[CX_INJ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "A" THEN ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`r:num`; `i:num`] THEN STRIP_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_SIMP_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
      MATCH_MP_TAC INTEGER_POLY_ROOT_BOUND THEN
      EXISTS_TAC `(a:num->num->real) r` THEN ASM_SIMP_TAC[] THEN
      ASM_SIMP_TAC[COMPLEX_ENTIRE; CPRODUCT_EQ_0; FINITE_NUMSEG] THEN
      DISJ2_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[COMPLEX_SUB_REFL];
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_MESON_TAC[REAL_POS; REAL_ARITH `&1 <= h ==> &0 <= h`];
      REWRITE_TAC[RESTRICTION_IN_CARTESIAN_PRODUCT] THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ] THEN
      ASM_SIMP_TAC[PRODUCT_EQ_0; REAL_POW_EQ_0] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  ASM_SIMP_TAC[GSYM PRODUCT_ABS; REAL_ABS_POW] THEN DISCH_TAC THEN
  MATCH_MP_TAC LIOUVILLE_INEQ_LEMMA THEN
  EXISTS_TAC
   `max (&1) ((b * product v (\r. abs((A:num->real) r) pow n r)) *
              product v (\r. ((h:num->real) r * (&1 + &(d r) *
                h r)) pow n r))` THEN
  EXISTS_TAC `product v (\r. abs((A:num->real) r) pow n r)` THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE; FACT_LT; ARITH_RULE `1 <= n <=> 0 < n`;
                  REAL_ARITH `&1 <= max (&1) x`] THEN
  SUBGOAL_THEN
   `product v (\r. abs((A:num->real) r) pow n r) <=
    product v (\r. (h:num->real) r pow n r)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_ABS_POS] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= y ==> max (&1) x <= max (&1) y`) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_MESON_TAC[INTPOLY_BOUND_POS]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_ARITH `&1 <= h ==> &0 <= h`];
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_MESON_TAC[REAL_POS; REAL_ARITH `&1 <= h ==> &0 <= h`]];
    MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_SIMP_TAC[GSYM REAL_ABS_NZ]]);;
