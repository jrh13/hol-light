(* ========================================================================= *)
(* Sharpening I: the auxiliary function.                                     *)
(*                                                                           *)
(* Purpose: the analytic layer of the auxiliary function of Baker,           *)
(* Sharpening I, sec. 3 (Acta Arith. 21, 1972), with complex coefficients    *)
(* bb r, r = 1..n (integer coefficients b r are the case bb r = Cx(b r), the *)
(* algebraic coefficients of Baker 1973 the general case), for any complex   *)
(* numbers lg r (the arithmetic of the alphas and the betas is in            *)
(* Baker/sharp_arith.ml). For lambda = (a,b,mu), a < h, b <= L0,             *)
(* mu r <= Lv r (r = 1..n),                                                  *)
(*   x_r = bb n mu_r - bb r mu_n,  omega = sum_(r<n) (x_r / bb n) lg r,      *)
(*   term_m(z) = p(lambda) [D^(m 0) B_ab](z) / (m 0)!                        *)
(*               prod_(r<n) Delta(x_r; m r) cexp(z omega)                    *)
(* (sharp_term, sharp_aux of Baker/sharp_defs.ml) and the counterpart        *)
(* sharp_alg with cexp(z sum_(r<=n) mu_r lg r). Results: the index set;      *)
(* omega in terms of Lambda = sum_r bb r lg r; holomorphy and the derivative *)
(* relation D f_m = sum_(i<n) c_m,i f_(m+e_i) + c0_m f_m (from               *)
(* x Delta(x;m) = (m+1) (Delta(x;m+1) - Delta(x;m)) at the complex nodes     *)
(* x_r); the coefficient bound (for &1 <= norm(bb n)); the size of the Delta *)
(* products, of the auxiliary function and of its approximation by the       *)
(* counterpart, also in the form of the size functions sharp_ubd and         *)
(* sharp_errb (pure real functions of the analytic size bound B); the omega  *)
(* bounds of the numeric layer.                                              *)
(*                                                                           *)
(* Main results: CARD_SHARP_INDEX, SHARP_OMEGA_EQ, SHARP_AUX_HOLOMORPHIC,    *)
(*   SHARP_AUX_DERIVATIVE, SHARP_COEFF_BOUND, SHARP_CPRODUCT_DELTA_BOUND,    *)
(*   SHARP_AUX_BOUND, SHARP_AUX_ALG_APPROX, SHARP_AUX_UBD, SHARP_AUX_ERRB,   *)
(*   SHARP_OMEGA_BOUNDS; helpers FINITE_SHARP_INDEX, IN_SHARP_INDEX,         *)
(*   SHARP_INDEX_MU_LE, CPRODUCT_FELDMAN_DELTA_SHIFT, SHARP_OMEGA_CPRODUCT,  *)
(*   HAS_COMPLEX_DERIVATIVE_FELDMAN_BASIS_DIV_FACT,                          *)
(*   HAS_COMPLEX_DERIVATIVE_SHARP_SHAPE, SHARP_TERM_HAS_DERIVATIVE,          *)
(*   SHARP_AUX_HAS_DERIVATIVE, SHARP_COEFF_TERM_BOUND, REAL_LE_MUL4,         *)
(*   SHARP_X_BOUND, NORM_CEXP_MUL_SUB_LE, SHARP_TERM_BOUND,                  *)
(*   SHARP_TERM_ALGTERM_BOUND.                                               *)
(*                                                                           *)
(* Uses: Baker/sharp_defs.ml (sharp_index, sharp_x, sharp_omega, sharp_term, *)
(*   sharp_aux, sharp_algterm, sharp_alg, sharp_coeff, sharp_coeff0,         *)
(*   sharp_ubd, sharp_errb, sharp_lv), Baker/sharp_poly.ml                   *)
(*   (FELDMAN_DELTA_MUL_SHIFT, FELDMAN_DELTA_SIZE), Baker/delta.ml           *)
(*   (feldman_delta, feldman_basis, HOLOMORPHIC_ON_FELDMAN_BASIS,            *)
(*   FELDMAN_BASIS_DERIV_BOUND_UNIFORM), Baker/auxiliary.ml (NORM_CEXP_LE),  *)
(*   Baker/intpoly.ml (CARD_CARTESIAN_PRODUCT), sets.ml                      *)
(*   (FINITE_CARTESIAN_PRODUCT_FINITE), Baker/algebraic.ml                   *)
(*   (CPRODUCT_DELETE),                                                      *)
(*   Library/products.ml (REAL_POW_NSUM), Multivariate/transcendentals.ml    *)
(*   (CEXP_LIPSCHITZ_BOUNDED).                                               *)
(* ========================================================================= *)

needs "Baker/sharp_poly.ml";;
needs "Baker/sharp_defs.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The index set.                                                            *)
(* ------------------------------------------------------------------------- *)

let FINITE_SHARP_INDEX = prove
 (`!h L0 Lv n. FINITE(sharp_index h L0 Lv n)`,
  REWRITE_TAC[sharp_index] THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FINITE_NUMSEG_LT;
           FINITE_CARTESIAN_PRODUCT_FINITE]);;

let CARD_SHARP_INDEX = prove
 (`!h L0 Lv n.
        CARD(sharp_index h L0 Lv n) =
        h * (L0 + 1) * nproduct(1..n) (\r. Lv r + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sharp_index] THEN
  SIMP_TAC[CARD_CROSS; FINITE_CROSS; FINITE_NUMSEG; FINITE_NUMSEG_LT;
           FINITE_CARTESIAN_PRODUCT_FINITE; CARD_NUMSEG_LT; CARD_NUMSEG] THEN
  SIMP_TAC[CARD_CARTESIAN_PRODUCT; FINITE_NUMSEG; CARD_NUMSEG; SUB_0]);;

let IN_SHARP_INDEX = prove
 (`!h L0 Lv n a b mu.
        (a,b,mu) IN sharp_index h L0 Lv n <=>
        a < h /\ b <= L0 /\ mu IN cartesian_product (1..n) (\r. 0..Lv r)`,
  REWRITE_TAC[sharp_index; IN_CROSS; IN_ELIM_THM; IN_NUMSEG; LE_0]);;

let SHARP_INDEX_MU_LE = prove
 (`!n Lv mu r.
        mu IN cartesian_product (1..n) (\r. 0..Lv r) /\ r IN 1..n
        ==> mu r <= Lv r`,
  REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_NUMSEG] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* omega = sum_(r<=n) mu_r lg_r - (mu_n / bb n) sum_(r<=n) bb r lg_r.        *)
(* ------------------------------------------------------------------------- *)

let SHARP_OMEGA_EQ = prove
 (`!n (bb:num->complex) (lg:num->complex) mu.
     1 <= n /\ ~(bb n = Cx(&0))
     ==> sharp_omega n bb lg mu =
         vsum(1..n) (\r. Cx(&(mu r)) * lg r) -
         (Cx(&(mu n)) / bb n) * vsum(1..n) (\r. bb r * lg r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sharp_omega; sharp_x] THEN
  SUBGOAL_THEN `0 < n /\ 1 <= n` (fun th ->
    REWRITE_TAC[MATCH_MP VSUM_CLAUSES_RIGHT th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(1..n-1) (\r. (((bb:num->complex) n * Cx(&(mu r)) -
                        bb r * Cx(&(mu n))) / bb n) * (lg:num->complex) r) =
    vsum(1..n-1) (\r. Cx(&(mu r)) * lg r) -
    (Cx(&(mu n)) / bb n) * vsum(1..n-1) (\r. bb r * lg r)`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_SUB; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `~((bb:num->complex) n = Cx(&0))` THEN
    CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  UNDISCH_TAC `~((bb:num->complex) n = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Holomorphy and the derivative relation. The key step is                   *)
(* omega prod_r Delta(x_r;m_r) = sum_i c_i (prod_(m+e_i) - prod_m), from     *)
(* x Delta(x;m) = (m+1) (Delta(x;m+1) - Delta(x;m)) at the complex nodes     *)
(* x_r (CPRODUCT_FELDMAN_DELTA_SHIFT).                                       *)
(* ------------------------------------------------------------------------- *)

let CPRODUCT_FELDMAN_DELTA_SHIFT = prove
 (`!s (x:num->complex) (m:num->num) i.
        FINITE s /\ i IN s
        ==> x i * cproduct s (\r. feldman_delta (m r) (x r)) =
            Cx(&(m i + 1)) *
            (cproduct s (\r. feldman_delta (if r = i then m r + 1 else m r)
                                           (x r)) -
             cproduct s (\r. feldman_delta (m r) (x r)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. feldman_delta (if r = i then m r + 1 else m r)
                                    ((x:num->complex) r)`;
                 `s:num->bool`; `i:num`] CPRODUCT_DELETE) THEN
  MP_TAC(ISPECL [`\r. feldman_delta ((m:num->num) r) ((x:num->complex) r)`;
                 `s:num->bool`; `i:num`] CPRODUCT_DELETE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN
   `cproduct (s DELETE i)
     (\r. feldman_delta (if r = i then m r + 1 else m r)
                        ((x:num->complex) r)) =
    cproduct (s DELETE i) (\r. feldman_delta (m r) (x r))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CPRODUCT_EQ THEN SIMP_TAC[IN_DELETE]; ALL_TAC] THEN
  MP_TAC(SPECL [`(m:num->num) i`; `(x:num->complex) i`]
         FELDMAN_DELTA_MUL_SHIFT) THEN
  CONV_TAC COMPLEX_RING);;

let SHARP_OMEGA_CPRODUCT = prove
 (`!n (bb:num->complex) (lg:num->complex) m mu.
     sharp_omega n bb lg mu *
     cproduct(1..n-1) (\r. feldman_delta (m r) (sharp_x n bb mu r)) =
     vsum(1..n-1)
      (\i. (Cx(&(m i + 1)) * lg i / bb n) *
           cproduct(1..n-1)
            (\r. feldman_delta (if r = i then m r + 1 else m r)
                               (sharp_x n bb mu r))) +
     sharp_coeff0 n bb lg m *
     cproduct(1..n-1) (\r. feldman_delta (m r) (sharp_x n bb mu r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sharp_omega; sharp_coeff0] THEN
  ABBREV_TAC
   `Q = cproduct(1..n-1)
         (\r. feldman_delta ((m:num->num) r)
                            (sharp_x n (bb:num->complex) mu r))` THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG; GSYM complex_sub] THEN
  REWRITE_TAC[GSYM(MATCH_MP VSUM_COMPLEX_RMUL (SPEC_ALL FINITE_NUMSEG));
              GSYM(MATCH_MP VSUM_SUB (SPEC_ALL FINITE_NUMSEG))] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`1..n-1`; `sharp_x n (bb:num->complex) mu`;
                 `m:num->num`; `i:num`] CPRODUCT_FELDMAN_DELTA_SHIFT) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING);;

let HAS_COMPLEX_DERIVATIVE_FELDMAN_BASIS_DIV_FACT = prove
 (`!h a b k z.
        ((\z. higher_complex_derivative k (feldman_basis h a b) z /
              Cx(&(FACT k))) has_complex_derivative
         (Cx(&(k + 1)) *
          (higher_complex_derivative (k + 1) (feldman_basis h a b) z /
           Cx(&(FACT(k + 1)))))) (at z)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`feldman_basis h a b`; `(:complex)`; `z:complex`; `k:num`]
         HAS_COMPLEX_DERIVATIVE_HIGHER_COMPLEX_DERIVATIVE) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV; HOLOMORPHIC_ON_FELDMAN_BASIS] THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(&(FACT k))` o
             MATCH_MP HAS_COMPLEX_DERIVATIVE_CDIV_AT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM ADD1; FACT; GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
  MP_TAC(SPEC `k:num` FACT_NZ) THEN MP_TAC(SPEC `k:num` NOT_SUC) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM CX_INJ] THEN
  CONV_TAC COMPLEX_FIELD);;

let HAS_COMPLEX_DERIVATIVE_SHARP_SHAPE = prove
 (`!f f' c q w z.
        (f has_complex_derivative f') (at z)
        ==> ((\z. c * f z * q * cexp(z * w)) has_complex_derivative
             (c * f' * q * cexp(z * w) + c * f z * (w * q) * cexp(z * w)))
            (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\z. q * cexp(z * w)) has_complex_derivative (q * (w * cexp(z * w))))
    (at z)`
  ASSUME_TAC THENL
   [COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_MUL_AT o
    CONJ (ASSUME
     `((f:complex->complex) has_complex_derivative f') (at z)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `c:complex` o
             MATCH_MP HAS_COMPLEX_DERIVATIVE_LMUL_AT) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC COMPLEX_RING);;

let SHARP_TERM_HAS_DERIVATIVE = prove
 (`!n h p bb lg m a b mu z.
        ((\z. sharp_term n h p bb lg m (a,b,mu) z) has_complex_derivative
         (vsum(0..n-1) (\i. sharp_coeff n bb lg m i *
                            sharp_term n h p bb lg
                              (\r. if r = i then m r + 1 else m r)
                              (a,b,mu) z) +
          sharp_coeff0 n bb lg m * sharp_term n h p bb lg m (a,b,mu) z))
        (at z)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `0 <= n - 1`
   (fun th -> REWRITE_TAC[MATCH_MP VSUM_CLAUSES_LEFT th]) THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN
   `vsum(1..n-1) (\i. sharp_coeff n bb lg m i *
                      sharp_term n h p bb lg
                        (\r. if r = i then m r + 1 else m r) (a,b,mu) z) =
    (Cx(p(a,b,mu)) *
     (higher_complex_derivative (m 0) (feldman_basis h a b) z /
      Cx(&(FACT(m 0)))) *
     cexp(z * sharp_omega n bb lg mu)) *
    vsum(1..n-1)
     (\i. (Cx(&(m i + 1)) * lg i / bb n) *
          cproduct(1..n-1)
           (\r. feldman_delta (if r = i then m r + 1 else m r)
                              (sharp_x n bb mu r)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM(MATCH_MP VSUM_COMPLEX_LMUL (SPEC_ALL FINITE_NUMSEG))] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(i = 0) /\ ~(0 = i)`
     (fun th -> REWRITE_TAC[th; sharp_coeff; sharp_term]) THENL
     [ASM_ARITH_TAC; REWRITE_TAC[COMPLEX_MUL_AC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sharp_coeff n bb lg m 0 *
    sharp_term n h p bb lg (\r. if r = 0 then m r + 1 else m r) (a,b,mu) z =
    Cx(p(a,b,mu)) *
    (Cx(&(m 0 + 1)) *
     (higher_complex_derivative (m 0 + 1) (feldman_basis h a b) z /
      Cx(&(FACT(m 0 + 1))))) *
    cproduct(1..n-1) (\r. feldman_delta (m r) (sharp_x n bb mu r)) *
    cexp(z * sharp_omega n bb lg mu)`
  SUBST1_TAC THENL
   [REWRITE_TAC[sharp_coeff; sharp_term] THEN
    SUBGOAL_THEN
     `cproduct(1..n-1) (\r. feldman_delta (if r = 0 then m r + 1 else m r)
                                          (sharp_x n bb mu r)) =
      cproduct(1..n-1) (\r. feldman_delta (m r) (sharp_x n bb mu r))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CPRODUCT_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ARITH_RULE `1 <= r ==> ~(r = 0)`];
      REWRITE_TAC[COMPLEX_MUL_AC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. higher_complex_derivative ((m:num->num) 0) (feldman_basis h a b) z /
         Cx(&(FACT(m 0)))`;
    `Cx(&((m:num->num) 0 + 1)) *
     (higher_complex_derivative (m 0 + 1) (feldman_basis h a b) z /
      Cx(&(FACT(m 0 + 1))))`;
    `Cx((p:num#num#(num->num)->real)(a,b,mu))`;
    `cproduct(1..n-1)
      (\r. feldman_delta ((m:num->num) r)
                         (sharp_x n (bb:num->complex) mu r))`;
    `sharp_omega n (bb:num->complex) (lg:num->complex) mu`; `z:complex`]
   HAS_COMPLEX_DERIVATIVE_SHARP_SHAPE) THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_FELDMAN_BASIS_DIV_FACT] THEN
  REWRITE_TAC[sharp_term; SHARP_OMEGA_CPRODUCT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC COMPLEX_RING);;

let SHARP_AUX_HAS_DERIVATIVE = prove
 (`!n h L0 Lv p bb lg m z.
        (sharp_aux n h L0 Lv p bb lg m has_complex_derivative
         (vsum(0..n-1) (\i. sharp_coeff n bb lg m i *
                            sharp_aux n h L0 Lv p bb lg
                              (\r. if r = i then m r + 1 else m r) z) +
          sharp_coeff0 n bb lg m * sharp_aux n h L0 Lv p bb lg m z))
        (at z)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `sharp_aux n h L0 Lv p bb lg m =
    \z. vsum (sharp_index h L0 Lv n) (\x. sharp_term n h p bb lg m x z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; sharp_aux]; ALL_TAC] THEN
  REWRITE_TAC[sharp_aux] THEN
  REWRITE_TAC[GSYM(MATCH_MP VSUM_COMPLEX_LMUL
                     (SPEC_ALL FINITE_SHARP_INDEX))] THEN
  MP_TAC(ISPECL
   [`\i x. sharp_coeff n bb lg m i *
           sharp_term n h p bb lg (\r. if r = i then m r + 1 else m r) x z`;
    `0..n-1`; `sharp_index h L0 Lv n`] VSUM_SWAP) THEN
  REWRITE_TAC[FINITE_NUMSEG; FINITE_SHARP_INDEX] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM(MATCH_MP VSUM_ADD (SPEC_ALL FINITE_SHARP_INDEX))] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_VSUM THEN
  REWRITE_TAC[FINITE_SHARP_INDEX; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `mu:num->num`] THEN DISCH_TAC THEN
  REWRITE_TAC[SHARP_TERM_HAS_DERIVATIVE]);;

let SHARP_AUX_HOLOMORPHIC = prove
 (`!n h L0 Lv p bb lg m.
        sharp_aux n h L0 Lv p bb lg m holomorphic_on (:complex)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[holomorphic_on] THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  EXISTS_TAC
   `vsum(0..n-1) (\i. sharp_coeff n bb lg m i *
                      sharp_aux n h L0 Lv p bb lg
                        (\r. if r = i then m r + 1 else m r) z) +
    sharp_coeff0 n bb lg m * sharp_aux n h L0 Lv p bb lg m z` THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
  REWRITE_TAC[SHARP_AUX_HAS_DERIVATIVE]);;

let SHARP_AUX_DERIVATIVE = prove
 (`!n h L0 Lv p bb lg m.
     1 <= n
     ==> complex_derivative (sharp_aux n h L0 Lv p bb lg m) =
         \z. vsum(0..n-1) (\i. sharp_coeff n bb lg m i *
                              sharp_aux n h L0 Lv p bb lg
                                (\r. if r = i then m r + 1 else m r) z) +
             sharp_coeff0 n bb lg m * sharp_aux n h L0 Lv p bb lg m z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:complex` THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  REWRITE_TAC[SHARP_AUX_HAS_DERIVATIVE]);;

(* ------------------------------------------------------------------------- *)
(* The coefficients: sum_i |c_m,i| + |c0_m| <= S Nl when |m| < S and         *)
(* &1 <= norm(bb n).                                                         *)
(* ------------------------------------------------------------------------- *)

let SHARP_COEFF_TERM_BOUND = prove
 (`!n (bb:num->complex) (lg:num->complex) (m:num->num) i S.
     &1 <= norm(bb n) /\ m i + 1 <= S
     ==> norm(Cx(&(m i + 1)) * lg i / bb n) <= &S * norm(lg i)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; COMPLEX_NORM_CX;
              REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
  SUBGOAL_THEN `&0 < norm((bb:num->complex) n)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_LE_LDIV_EQ] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]);;

let SHARP_COEFF_BOUND = prove
 (`!n (bb:num->complex) (lg:num->complex) m S Nl.
     1 <= n /\ &1 <= norm(bb n) /\
     &1 + &2 * sum(1..n-1) (\i. norm(lg i)) <= &Nl /\
     nsum(0..n-1) m < S
     ==> sum(0..n-1) (\i. norm(sharp_coeff n bb lg m i)) +
         norm(sharp_coeff0 n bb lg m) <= &(S * Nl)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i <= n - 1 ==> (m:num->num) i + 1 <= S` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`m:num->num`; `nsum(0..n-1) m`; `0..n-1`]
           NSUM_POS_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG; LE_REFL] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[IN_NUMSEG; LE_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(sharp_coeff n bb lg m 0) <= &S` ASSUME_TAC THENL
   [REWRITE_TAC[sharp_coeff; COMPLEX_NORM_CX; REAL_ABS_NUM;
                REAL_OF_NUM_LE] THEN
    FIRST_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN 1..n-1
        ==> norm(Cx(&((m:num->num) i + 1)) * lg i / bb n) <=
            &S * norm((lg:num->complex) i)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SHARP_COEFF_TERM_BOUND THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n-1) (\i. norm(sharp_coeff n bb lg m i)) <=
    &S * sum(1..n-1) (\i. norm((lg:num->complex) i))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(i = 0)` (fun th -> REWRITE_TAC[th; sharp_coeff]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(sharp_coeff0 n bb lg m) <=
    &S * sum(1..n-1) (\i. norm((lg:num->complex) i))`
  ASSUME_TAC THENL
   [REWRITE_TAC[sharp_coeff0; NORM_NEG; GSYM SUM_LMUL] THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `0 <= n - 1`
   (fun th -> REWRITE_TAC[MATCH_MP SUM_CLAUSES_LEFT th]) THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; GSYM REAL_OF_NUM_MUL] THEN
  TRANS_TAC REAL_LE_TRANS
   `&S * (&1 + &2 * sum(1..n-1) (\i. norm((lg:num->complex) i)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `x0 <= s /\ x1 <= s * l /\ x2 <= s * l
      ==> (x0 + x1) + x2 <= s * (&1 + &2 * l):real`) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]]);;

(* ------------------------------------------------------------------------- *)
(* Size of the terms: |x_r| <= 2 B L gives |Delta(x_r;m_r)| <=               *)
(* (4B+2)^(m_r) 2^L, the Feldman basis part is <= 2^((L0+2)(N+h)) and        *)
(* |cexp(z omega)| <= exp(|z| T0). For the counterpart the exponential       *)
(* factor becomes |cexp(z w) - cexp(z v)| <= |z| d0 exp(|z| (T0 + d0))       *)
(* when |w| <= T0 and |w - v| <= d0 (NORM_CEXP_MUL_SUB_LE).                  *)
(* ------------------------------------------------------------------------- *)

let REAL_LE_MUL4 = prove
 (`!a b c d a' b' c' d':real.
     &0 <= a /\ a <= a' /\ &0 <= b /\ b <= b' /\
     &0 <= c /\ c <= c' /\ &0 <= d /\ d <= d'
     ==> a * b * c * d <= a' * b' * c' * d'`,
  REPEAT STRIP_TAC THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LE_MUL]));;

let SHARP_X_BOUND = prove
 (`!n (bb:num->complex) (mu:num->num) r B L.
        norm(bb n) <= B /\ norm(bb r) <= B /\ mu n <= L /\ mu r <= L
        ==> norm(sharp_x n bb mu r) <= &2 * B * &L`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sharp_x] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x:complex) <= c /\ norm(y:complex) <= c
    ==> norm(x - y) <= &2 * c`) THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[NORM_POS_LE; REAL_POS; REAL_OF_NUM_LE]);;

let SHARP_CPRODUCT_DELTA_BOUND = prove
 (`!n (bb:num->complex) (mu:num->num) (m:num->num) B L.
     1 <= n /\ &0 <= B /\
     (!r. r IN 1..n ==> norm(bb r) <= B /\ mu r <= L)
     ==> norm(cproduct(1..n-1)
               (\r. feldman_delta (m r) (sharp_x n bb mu r))) <=
         (&4 * B + &2) pow (nsum(1..n-1) m) * &2 pow ((n - 1) * L)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[NORM_CPRODUCT; FINITE_NUMSEG] THEN
  TRANS_TAC REAL_LE_TRANS
   `product(1..n-1) (\r. (&4 * B + &2) pow ((m:num->num) r) * &2 pow L)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC FELDMAN_DELTA_SIZE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SHARP_X_BOUND THEN
    SUBGOAL_THEN `n IN 1..n /\ r IN 1..n` MP_TAC THENL
     [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC; ASM_MESON_TAC[]];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SIMP_TAC[PRODUCT_MUL; FINITE_NUMSEG; GSYM REAL_POW_NSUM;
             PRODUCT_CONST_NUMSEG_1; REAL_POW_POW] THEN
    REWRITE_TAC[MULT_SYM]]);;

let NORM_CEXP_MUL_SUB_LE = prove
 (`!z w w' T0 d0.
        norm w <= T0 /\ norm(w - w') <= d0
        ==> norm(cexp(z * w) - cexp(z * w')) <=
            norm z * d0 * exp(norm z * (T0 + d0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`norm(z:complex) * (T0 + d0)`; `z * w:complex`;
                 `z * w':complex`] CEXP_LIPSCHITZ_BOUNDED) THEN
  REWRITE_TAC[GSYM COMPLEX_SUB_LDISTRIB; COMPLEX_NORM_MUL] THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN NORM_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c:real`) THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `e * z * d:real = z * d * e`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]]);;

let SHARP_TERM_BOUND = prove
 (`!n h L0 L p bb lg m a b mu z P B T0 N.
     1 <= n /\ &0 <= B /\ a < h /\ b <= L0 /\ abs(p(a,b,mu)) <= P /\
     (!r. r IN 1..n ==> norm(bb r) <= B /\ mu r <= L) /\
     norm(sharp_omega n bb lg mu) <= T0 /\ norm z + &1 <= &N
     ==> norm(sharp_term n h p bb lg m (a,b,mu) z) <=
         P * &2 pow ((L0 + 2) * (N + h)) *
         (&4 * B + &2) pow (nsum(1..n-1) m) * &2 pow ((n - 1) * L) *
         exp(norm z * T0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sharp_term] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL4 THEN
  ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FELDMAN_BASIS_DERIV_BOUND_UNIFORM THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SHARP_CPRODUCT_DELTA_BOUND THEN ASM_REWRITE_TAC[];
    TRANS_TAC REAL_LE_TRANS `exp(norm(z * sharp_omega n bb lg mu))` THEN
    REWRITE_TAC[NORM_CEXP_LE; REAL_EXP_MONO_LE; COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]]);;

let SHARP_TERM_ALGTERM_BOUND = prove
 (`!n h L0 L p bb lg m a b mu z P B T0 N d0.
     1 <= n /\ &0 <= B /\ a < h /\ b <= L0 /\ abs(p(a,b,mu)) <= P /\
     (!r. r IN 1..n ==> norm(bb r) <= B /\ mu r <= L) /\
     norm(sharp_omega n bb lg mu) <= T0 /\
     norm(sharp_omega n bb lg mu - vsum(1..n) (\r. Cx(&(mu r)) * lg r))
     <= d0 /\
     norm z + &1 <= &N
     ==> norm(sharp_term n h p bb lg m (a,b,mu) z -
              sharp_algterm n h p bb lg m (a,b,mu) z) <=
         P * &2 pow ((L0 + 2) * (N + h)) *
         (&4 * B + &2) pow (nsum(1..n-1) m) * &2 pow ((n - 1) * L) *
         (norm z * d0 * exp(norm z * (T0 + d0)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sharp_term; sharp_algterm] THEN
  REWRITE_TAC[COMPLEX_RING
   `p1 * p2 * p3 * x1 - p1 * p2 * p3 * x2:complex =
    p1 * p2 * p3 * (x1 - x2)`] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL4 THEN
  ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FELDMAN_BASIS_DERIV_BOUND_UNIFORM THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SHARP_CPRODUCT_DELTA_BOUND THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC NORM_CEXP_MUL_SUB_LE THEN ASM_REWRITE_TAC[]]);;

let SHARP_AUX_BOUND = prove
 (`!n h L0 Lv L p bb lg m z P B T0 N.
     1 <= n /\ &1 <= B /\
     (!x. x IN sharp_index h L0 Lv n ==> abs(p x) <= P) /\
     (!r. r IN 1..n ==> norm(bb r) <= B /\ Lv r <= L) /\
     (!mu. mu IN cartesian_product (1..n) (\r. 0..Lv r)
           ==> norm(sharp_omega n bb lg mu) <= T0) /\
     norm z + &1 <= &N
     ==> norm(sharp_aux n h L0 Lv p bb lg m z) <=
         &(CARD(sharp_index h L0 Lv n)) * P * &2 pow ((L0 + 2) * (N + h)) *
         (&4 * B + &2) pow (nsum(1..n-1) m) * &2 pow ((n - 1) * L) *
         exp(norm z * T0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sharp_aux] THEN
  MATCH_MP_TAC VSUM_NORM_BOUND THEN REWRITE_TAC[FINITE_SHARP_INDEX] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `mu:num->num`] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IN_SHARP_INDEX]) THEN
  MATCH_MP_TAC SHARP_TERM_BOUND THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ASM_REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ASM_MESON_TAC[SHARP_INDEX_MU_LE; LE_TRANS];
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

let SHARP_AUX_ALG_APPROX = prove
 (`!n h L0 Lv L p bb lg m z P B T0 N d0.
     1 <= n /\ &1 <= B /\
     (!x. x IN sharp_index h L0 Lv n ==> abs(p x) <= P) /\
     (!r. r IN 1..n ==> norm(bb r) <= B /\ Lv r <= L) /\
     (!mu. mu IN cartesian_product (1..n) (\r. 0..Lv r)
           ==> norm(sharp_omega n bb lg mu) <= T0 /\
               norm(sharp_omega n bb lg mu -
                    vsum(1..n) (\r. Cx(&(mu r)) * lg r)) <= d0) /\
     norm z + &1 <= &N
     ==> norm(sharp_aux n h L0 Lv p bb lg m z -
              sharp_alg n h L0 Lv p bb lg m z) <=
         &(CARD(sharp_index h L0 Lv n)) * P * &2 pow ((L0 + 2) * (N + h)) *
         (&4 * B + &2) pow (nsum(1..n-1) m) * &2 pow ((n - 1) * L) *
         (norm z * d0 * exp(norm z * (T0 + d0)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sharp_aux; sharp_alg] THEN
  REWRITE_TAC[GSYM(MATCH_MP VSUM_SUB (SPEC_ALL FINITE_SHARP_INDEX))] THEN
  MATCH_MP_TAC VSUM_NORM_BOUND THEN REWRITE_TAC[FINITE_SHARP_INDEX] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `mu:num->num`] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IN_SHARP_INDEX]) THEN
  SUBGOAL_THEN
   `norm(sharp_omega n bb lg mu) <= T0 /\
    norm(sharp_omega n bb lg mu - vsum(1..n) (\r. Cx(&(mu r)) * lg r))
    <= d0`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SHARP_TERM_ALGTERM_BOUND THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ASM_REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ASM_MESON_TAC[SHARP_INDEX_MU_LE; LE_TRANS];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The same bounds in the form of the size functions sharp_ubd and           *)
(* sharp_errb of the parametric core (derivative orders with                 *)
(* nsum(1..n-1) m <= S0 and Lv r <= Lm).                                     *)
(* ------------------------------------------------------------------------- *)

let SHARP_AUX_UBD = prove
 (`!n h L0 Lv Lm p bb lg m z P B S0 T0 N.
     1 <= n /\ &1 <= B /\ &0 <= P /\
     (!x. x IN sharp_index h L0 Lv n ==> abs(p x) <= P) /\
     (!r. r IN 1..n ==> norm(bb r) <= B /\ Lv r <= Lm) /\
     (!mu. mu IN cartesian_product (1..n) (\r. 0..Lv r)
           ==> norm(sharp_omega n bb lg mu) <= T0) /\
     norm z + &1 <= &N /\ nsum(1..n-1) m <= S0
     ==> norm(sharp_aux n h L0 Lv p bb lg m z) <=
         sharp_ubd n h L0 Lv Lm P B S0 T0 N (norm z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sharp_ubd] THEN
  TRANS_TAC REAL_LE_TRANS
   `&(CARD(sharp_index h L0 Lv n)) * P * &2 pow ((L0 + 2) * (N + h)) *
    (&4 * B + &2) pow (nsum(1..n-1) m) * &2 pow ((n - 1) * Lm) *
    exp(norm(z:complex) * T0)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SHARP_AUX_BOUND THEN ASM_REWRITE_TAC[];
                  ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC]) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC]);;

let SHARP_AUX_ERRB = prove
 (`!n h L0 Lv Lm p bb lg m z P B S0 T0 d0 N.
     1 <= n /\ &1 <= B /\ &0 <= P /\ &0 <= d0 /\
     (!x. x IN sharp_index h L0 Lv n ==> abs(p x) <= P) /\
     (!r. r IN 1..n ==> norm(bb r) <= B /\ Lv r <= Lm) /\
     (!mu. mu IN cartesian_product (1..n) (\r. 0..Lv r)
           ==> norm(sharp_omega n bb lg mu) <= T0 /\
               norm(sharp_omega n bb lg mu -
                    vsum(1..n) (\r. Cx(&(mu r)) * lg r)) <= d0) /\
     norm z + &1 <= &N /\ nsum(1..n-1) m <= S0
     ==> norm(sharp_aux n h L0 Lv p bb lg m z -
              sharp_alg n h L0 Lv p bb lg m z) <=
         sharp_errb n h L0 Lv Lm P B S0 T0 d0 N (norm z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sharp_errb] THEN
  TRANS_TAC REAL_LE_TRANS
   `&(CARD(sharp_index h L0 Lv n)) * P * &2 pow ((L0 + 2) * (N + h)) *
    (&4 * B + &2) pow (nsum(1..n-1) m) * &2 pow ((n - 1) * Lm) *
    (norm(z:complex) * d0 * exp(norm z * (T0 + d0)))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SHARP_AUX_ALG_APPROX THEN ASM_REWRITE_TAC[];
                  ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC]) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]]);;

(* ------------------------------------------------------------------------- *)
(* The omega bounds of the numeric layer: for &1 <= norm(bb n) (so that      *)
(* |mu_n / bb n| <= mu_n) and |Lambda| <= 1, |omega| <= L (n-1) G0 +         *)
(* Ln (GA + 1) and |omega - sum_r mu_r lg r| <= Ln |Lambda|.                 *)
(* ------------------------------------------------------------------------- *)

let SHARP_OMEGA_BOUNDS = prove
 (`!n (bb:num->complex) (lg:num->complex) L Ln mu G0 GA.
     1 <= n /\ &1 <= norm(bb n) /\
     (!r. r IN 1..n-1 ==> norm(lg r) <= G0) /\ norm(lg n) <= GA /\
     norm(vsum(1..n) (\r. bb r * lg r)) <= &1 /\
     mu IN cartesian_product (1..n) (\r. 0..sharp_lv n L Ln r)
     ==> norm(sharp_omega n bb lg mu) <=
         &L * &(n - 1) * G0 + &Ln * (GA + &1) /\
         norm(sharp_omega n bb lg mu - vsum(1..n) (\r. Cx(&(mu r)) * lg r))
         <= &Ln * norm(vsum(1..n) (\r. bb r * lg r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `Lam = vsum(1..n) (\r. (bb:num->complex) r * (lg:num->complex) r)` THEN
  SUBGOAL_THEN `!r. r IN 1..n ==> (mu:num->num) r <= sharp_lv n L Ln r`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SHARP_INDEX_MU_LE THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(mu:num->num) n <= Ln` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL; sharp_lv];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((bb:num->complex) n = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_NORM_ZERO] THEN
    UNDISCH_TAC `&1 <= norm((bb:num->complex) n)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(sharp_omega n bb lg mu -
         vsum(1..n) (\r. Cx(&(mu r)) * (lg:num->complex) r)) <=
    &Ln * norm(Lam:complex)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[SHARP_OMEGA_EQ] THEN
    REWRITE_TAC[VECTOR_ARITH `(a - b) - a:complex = --b`; NORM_NEG] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; COMPLEX_NORM_CX;
                REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    SUBGOAL_THEN `&0 < norm((bb:num->complex) n)` ASSUME_TAC THENL
     [UNDISCH_TAC `&1 <= norm((bb:num->complex) n)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    TRANS_TAC REAL_LE_TRANS `&Ln * &1` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_MUL_RID; REAL_OF_NUM_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(vsum(1..n) (\r. Cx(&(mu r)) * (lg:num->complex) r)) <=
    &(n - 1) * (&L * G0) + &Ln * GA`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `sum(1..n) (\r. if r = n then &Ln * GA else &L * G0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
      COND_CASES_TAC THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS; NORM_POS_LE] THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE];
        ALL_TAC] THEN
      SUBGOAL_THEN `r IN 1..n-1` ASSUME_TAC THENL
       [UNDISCH_TAC `r IN 1..n` THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS; NORM_POS_LE] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
          is_forall(concl th) && free_in `sharp_lv` (concl th))) THEN
        ASM_REWRITE_TAC[sharp_lv; REAL_OF_NUM_LE];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `0 < n /\ 1 <= n` (fun th ->
      REWRITE_TAC[MATCH_MP SUM_CLAUSES_RIGHT th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `sum(1..n-1) (\r. if r = n then &Ln * GA else &L * G0) =
                  sum(1..n-1) (\r. &L * G0)` SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(n - 1 + 1) - 1 = n - 1`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`sharp_omega n bb (lg:num->complex) mu`;
                 `vsum(1..n) (\r. Cx(&(mu r)) * (lg:num->complex) r)`]
                NORM_TRIANGLE_SUB) THEN
  SUBGOAL_THEN `&Ln * norm(Lam:complex) <= &Ln * &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  UNDISCH_TAC
   `norm(sharp_omega n bb lg mu -
         vsum(1..n) (\r. Cx(&(mu r)) * (lg:num->complex) r)) <=
    &Ln * norm(Lam:complex)` THEN
  UNDISCH_TAC
   `norm(vsum(1..n) (\r. Cx(&(mu r)) * (lg:num->complex) r)) <=
    &(n - 1) * (&L * G0) + &Ln * GA` THEN
  REAL_ARITH_TAC);;
