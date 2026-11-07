(* ========================================================================= *)
(* Two logarithms: the analytic interpolation lemma for                      *)
(* interpolation determinants (Laurent).                                     *)
(*                                                                           *)
(* Purpose: for entire ph_1, ..., ph_n bounded by M_i on the disc of radius  *)
(* rr and points zeta_1, ..., zeta_n in the disc of radius r <= rr,          *)
(*   |det(ph_i(zeta_j))| <= n! (r / rr)^(n(n-1)/2) M_1 ... M_n,              *)
(* together with the mixed and perturbed forms used in the proof of Lemma    *)
(* 11.6 of Y. Bugeaud, Linear Forms in Logarithms and Applications           *)
(* (EMS 2018); see also M. Laurent, Acta Arith. 66 (1994). The mixed and     *)
(* perturbed forms are first proved with a bound B for the products along    *)
(* permutations of the values on the circle |w| = rho (Laurent 1994, Lemmas  *)
(* 6-7, the form used by the Laurent bound of section 10), then for row      *)
(* bounds M_i (rho = rr / r, B = M_1 ... M_n).                               *)
(*                                                                           *)
(* Main results: TL_INTERP_CDET_ZERO_ORDER_MIXED and its case s = 1..n       *)
(* TL_INTERP_CDET_ZERO_ORDER (the determinant of the values ph_i(w zeta_j)   *)
(* is w^(k(k-1)/2) times an entire function of w),                           *)
(* INTERPOLATION_DETERMINANT_SCALED (the bound at any complex w with         *)
(* |w| r <= rr), INTERPOLATION_DETERMINANT (w = 1),                          *)
(* INTERPOLATION_DETERMINANT_MIXED_PERM and INTERPOLATION_DETERMINANT_MIXED  *)
(* (only the rows in s are interpolated, the others carry factors th i j of  *)
(* norm at most 1), CDET_PERTURB_EXPANSION (det(f_ij (1 + c th_ij)) expanded *)
(* over the subsets of the rows), INTERPOLATION_DETERMINANT_PERTURBED_PERM   *)
(* and INTERPOLATION_DETERMINANT_PERTURBED (the bounds with the factor 2^n). *)
(*                                                                           *)
(* Uses: Baker/twolog_det.ml (CDET_ROWS_CMUL, CDET_MULTILINEAR,              *)
(* CDET_NORM_LE_PERM, CDET_NORM_LE, CDET_HOLOMORPHIC), Library/ring_det.ml   *)
(* (RING_DET_EQ, RING_DET_IDENTICAL_ROWS), Baker/lemmas.ml                   *)
(* (CPRODUCT_POW_NSUM, FINITE_ARGMIN); holomorphic functions and the maximum *)
(* modulus principle of Multivariate/cauchy.ml.                              *)
(* ========================================================================= *)

needs "Baker/lemmas.ml";;
needs "Baker/twolog_det.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Division of an entire function by z^n with entire quotient:               *)
(* f(z) = a_0 + a_1 z + ... + a_(n-1) z^(n-1) + z^n g(z).                    *)
(* ------------------------------------------------------------------------- *)

let TL_INTERP_ENTIRE_FACTOR_LT = prove
 (`!f:complex->complex n.
        f holomorphic_on (:complex)
        ==> ?a g. g holomorphic_on (:complex) /\
                  !z. f z = vsum {t | t < n} (\t. z pow t * a t) +
                            z pow n * g z`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THENL
   [MAP_EVERY EXISTS_TAC [`\t:num. Cx(&0)`; `f:complex->complex`] THEN
    ASM_REWRITE_TAC[NUMSEG_CLAUSES_LT; VSUM_CLAUSES; complex_pow;
                    COMPLEX_MUL_LID; COMPLEX_VEC_0; COMPLEX_ADD_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:num->complex`
   (X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`\t. if t = n then (g:complex->complex)(Cx(&0)) else (a:num->complex) t`;
    `\z. if z = Cx(&0) then complex_derivative (g:complex->complex) (Cx(&0))
         else (g z - g(Cx(&0))) / (z - Cx(&0))`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC POLE_LEMMA_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN
  SIMP_TAC[NUMSEG_CLAUSES_LT; VSUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM;
           LT_REFL] THEN
  SUBGOAL_THEN
   `vsum {t | t < n}
         (\t. z pow t * (if t = n then (g:complex->complex)(Cx(&0))
                         else (a:num->complex) t)) =
    vsum {t | t < n} (\t. z pow t * a t)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[IN_ELIM_THM; LT_IMP_NE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(g:complex->complex) z =
    g(Cx(&0)) + z * (if z = Cx(&0) then complex_derivative g (Cx(&0))
                     else (g z - g(Cx(&0))) / (z - Cx(&0)))`
  MP_TAC THENL
   [COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID];
      UNDISCH_TAC `~(z = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD];
    ALL_TAC] THEN
  SPEC_TAC(`if z = Cx(&0) then complex_derivative (g:complex->complex) (Cx(&0))
            else (g z - g(Cx(&0))) / (z - Cx(&0))`,`d:complex`) THEN
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[complex_pow] THEN
  SPEC_TAC(`vsum {t | t < n} (\t. z pow t * (a:num->complex) t)`,
           `v:complex`) THEN
  CONV_TAC COMPLEX_RING);;

let TL_INTERP_VSUM_SPLIT_LAST = prove
 (`!n (h:num->complex) (a:num->complex) c.
        vsum(0..n) (\t. h t * (if t < n then a t else c)) =
        vsum {t | t < n} (\t. h t * a t) + h n * c`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `0..n = n INSERT {t | t < n}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_INSERT; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  SUBGOAL_THEN
   `vsum {t | t < n} (\t. (h:num->complex) t * (if t < n then a t else c)) =
    vsum {t | t < n} (\t. h t * a t)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_ADD_SYM]);;

let TL_INTERP_ENTIRE_FACTOR = prove
 (`!f:complex->complex n.
        f holomorphic_on (:complex)
        ==> ?a g. g holomorphic_on (:complex) /\
                  !z. f z = vsum(0..n) (\t. z pow t *
                                            (if t < n then a t else g z))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP TL_INTERP_ENTIRE_FACTOR_LT) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  SIMP_TAC[TL_INTERP_VSUM_SPLIT_LAST]);;

(* ------------------------------------------------------------------------- *)
(* Combinatorics: a sum of exponents mu i <= k over a set s of k indices,    *)
(* injective on the exponents < k, is at least k(k-1)/2.                     *)
(* ------------------------------------------------------------------------- *)

let TL_INTERP_MUL_PRED = prove
 (`!k. k * (k - 1) + k = k * k`,
  INDUCT_TAC THEN REWRITE_TAC[SUC_SUB1; MULT_CLAUSES] THEN ARITH_TAC);;

let TL_INTERP_NSUM_INJ_LOWER = prove
 (`!s (f:num->num).
        FINITE s /\ (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> CARD s * (CARD s - 1) <= 2 * nsum s f`,
  SUBGOAL_THEN
   `!k s (f:num->num).
        FINITE s /\ CARD s = k /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> k * (k - 1) <= 2 * nsum s f`
   (fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN
              ASM_REWRITE_TAC[]) THEN
  INDUCT_TAC THENL [REWRITE_TAC[MULT_CLAUSES; LE_0]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:num->bool`; `\x. --(&((f:num->num) x)):real`]
    FINITE_ARGMIN) THEN
  REWRITE_TAC[REAL_LE_NEG2; REAL_OF_NUM_LE] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `CARD({}:num->bool) = SUC k` THEN
    REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `k <= (f:num->num) x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (f:num->num) s`; `0..(f:num->num) x`]
           CARD_SUBSET) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG; SUBSET; FORALL_IN_IMAGE; IN_NUMSEG; LE_0] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:num->num`; `s:num->bool`] CARD_IMAGE_INJ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[CARD_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s DELETE (x:num)`; `f:num->num`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; SUC_SUB1] THEN
    REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:num->num`; `s:num->bool`; `x:num`] NSUM_DELETE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(SPEC `k:num` TL_INTERP_MUL_PRED) THEN
  UNDISCH_TAC `k <= (f:num->num) x` THEN
  REWRITE_TAC[SUC_SUB1; MULT_CLAUSES] THEN ARITH_TAC);;

let TL_INTERP_ARITH_AUX = prove
 (`!k l s. k * (k - 1) <= 2 * s
           ==> ((k + l) * ((k + l) - 1)) DIV 2 <= s + l * (k + l)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(2 * (s + l * (k + l))) DIV 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIV_MONO THEN
    MP_TAC(SPEC `k:num` TL_INTERP_MUL_PRED) THEN
    MP_TAC(SPEC `k + l:num` TL_INTERP_MUL_PRED) THEN
    UNDISCH_TAC `k * (k - 1) <= 2 * s` THEN ARITH_TAC;
    SIMP_TAC[DIV_MULT; ARITH_EQ; LE_REFL]]);;

let TL_INTERP_MULTIINDEX_LOWER_GEN = prove
 (`!s k (mu:num->num).
        FINITE s /\ CARD s = k /\
        (!i. i IN s ==> mu i <= k) /\
        (!i i'. i IN s /\ i' IN s /\ mu i < k /\ mu i = mu i' ==> i = i')
        ==> (k * (k - 1)) DIV 2 <= nsum s mu`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:num->bool`; `\i. (mu:num->num) i < k`; `mu:num->num`;
                 `\i:num. (k:num)`] NSUM_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `nsum s (\x. if (mu:num->num) x < k then mu x else k) = nsum s mu`
  SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `~(m < n) /\ m <= n ==> n = m`) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `FINITE {i | i IN s /\ ~((mu:num->num) i < k)}`
   (fun th -> REWRITE_TAC[MATCH_MP NSUM_CONST th]) THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {i | i IN s /\ (mu:num->num) i < k} +
    CARD {i | i IN s /\ ~(mu i < k)} = k`
  MP_TAC THENL
   [UNDISCH_TAC `CARD(s:num->bool) = k` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CARD_UNION_EQ THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{i | i IN s /\ (mu:num->num) i < k}`; `mu:num->num`]
         TL_INTERP_NSUM_INJ_LOWER) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SPEC_TAC(`nsum {i | i IN s /\ (mu:num->num) i < k} mu`,`t:num`) THEN
  SPEC_TAC(`CARD {i | i IN s /\ ~((mu:num->num) i < k)}`,`l:num`) THEN
  SPEC_TAC(`CARD {i | i IN s /\ (mu:num->num) i < k}`,`h:num`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[TL_INTERP_ARITH_AUX]);;

(* ------------------------------------------------------------------------- *)
(* Algebra of the multilinear expansion of the determinant whose rows        *)
(* i IN s are ph i (w * zeta j) (the other rows are arbitrary).              *)
(* ------------------------------------------------------------------------- *)

let TL_INTERP_CPRODUCT_POW_RESTRICT = prove
 (`!s t (f:num->num) (w:complex).
        FINITE t /\ s SUBSET t
        ==> cproduct t (\i. if i IN s then w pow (f i) else Cx(&1)) =
            w pow (nsum s f)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(s:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `cproduct s (\i. if i IN (s:num->bool) then (w:complex) pow ((f:num->num) i)
                    else Cx(&1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CPRODUCT_SUPERSET THEN ASM_SIMP_TAC[];
    TRANS_TAC EQ_TRANS
     `cproduct (s:num->bool) (\i. (w:complex) pow ((f:num->num) i))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CPRODUCT_EQ THEN SIMP_TAC[];
      ASM_SIMP_TAC[CPRODUCT_POW_NSUM]]]);;

let TL_INTERP_MONOMIAL_TERM_GEN = prove
 (`!n k s (mu:num->num) (a:num->num->complex) (q:num->num->complex)
    (u:num->num->complex) (w:complex) (zeta:num->complex).
        s SUBSET 1..n /\ CARD s = k /\ (!i. i IN s ==> mu i <= k)
        ==> ring_det complex_ring (1..n)
              (\i j. if i IN s
                     then (w * zeta j) pow (mu i) *
                          (if mu i < k then a i (mu i) else q i j)
                     else u i j) =
            w pow ((k * (k - 1)) DIV 2) *
            w pow (nsum s mu - (k * (k - 1)) DIV 2) *
            cproduct(1..n)
              (\i. if i IN s /\ mu i < k then a i (mu i) else Cx(&1)) *
            ring_det complex_ring (1..n)
              (\i j. if i IN s
                     then zeta j pow (mu i) *
                          (if mu i < k then Cx(&1) else q i j)
                     else u i j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`n:num`;
    `\i. (if i IN s then (w:complex) pow (mu i) else Cx(&1)) *
         (if i IN s /\ (mu:num->num) i < k
          then (a:num->num->complex) i (mu i) else Cx(&1))`;
    `\i j. if i IN s
           then (zeta:num->complex) j pow (mu i) *
                (if (mu:num->num) i < k then Cx(&1)
                 else (q:num->num->complex) i j)
           else (u:num->num->complex) i j`]
   CDET_ROWS_CMUL) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\i j. ((if i IN s then (w:complex) pow (mu i) else Cx(&1)) *
            (if i IN s /\ (mu:num->num) i < k
             then (a:num->num->complex) i (mu i) else Cx(&1))) *
           (if i IN s
            then (zeta:num->complex) j pow (mu i) *
                 (if mu i < k then Cx(&1) else (q:num->num->complex) i j)
            else (u:num->num->complex) i j)) =
    (\i j. if i IN s
           then (w * zeta j) pow (mu i) *
                (if mu i < k then a i (mu i) else q i j)
           else u i j)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    ASM_CASES_TAC `(i:num) IN s` THEN ASM_REWRITE_TAC[COMPLEX_MUL_LID] THEN
    COND_CASES_TAC THEN REWRITE_TAC[COMPLEX_POW_MUL] THEN
    CONV_TAC COMPLEX_RING;
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[CPRODUCT_MUL; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[TL_INTERP_CPRODUCT_POW_RESTRICT; FINITE_NUMSEG] THEN
  ASM_CASES_TAC
   `?i i'. i IN s /\ i' IN s /\ ~(i = i') /\
           (mu:num->num) i = mu i' /\ mu i < k`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `i:num`
     (X_CHOOSE_THEN `i':num` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(mu:num->num) i' < k` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_det complex_ring (1..n)
        (\i j. if i IN s
               then (zeta:num->complex) j pow (mu i) *
                    (if (mu:num->num) i < k then Cx(&1)
                     else (q:num->num->complex) i j)
               else (u:num->num->complex) i j) = Cx(&0)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[COMPLEX_RING_CLAUSES]
       (ISPEC `complex_ring` RING_DET_IDENTICAL_ROWS)) THEN
      MAP_EVERY EXISTS_TAC [`i:num`; `i':num`] THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG] THEN ASM_MESON_TAC[SUBSET];
      REWRITE_TAC[COMPLEX_MUL_RZERO]];
    SUBGOAL_THEN `(k * (k - 1)) DIV 2 <= nsum s (mu:num->num)` ASSUME_TAC
    THENL
     [MATCH_MP_TAC TL_INTERP_MULTIINDEX_LOWER_GEN THEN
      ASM_MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(w:complex) pow (nsum (s:num->bool) mu) =
      w pow ((k * (k - 1)) DIV 2) * w pow (nsum s mu - (k * (k - 1)) DIV 2)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM COMPLEX_POW_ADD] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `!m s:num. m <= s ==> s = m + (s - m)`) THEN
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[COMPLEX_MUL_AC]]]);;

(* ------------------------------------------------------------------------- *)
(* The zero at w = 0 (Bugeaud, Linear Forms in Logarithms, Lemma 11.6):      *)
(* if only the rows in s are expanded in powers of w (the other rows         *)
(* are arbitrary entire functions of w), the determinant has a zero of       *)
(* order at least CARD s (CARD s - 1) / 2 at w = 0. For s = 1..n:            *)
(* det(ph_i(w zeta_j)) = w^(n(n-1)/2) E(w) with E entire.                    *)
(* ------------------------------------------------------------------------- *)

let TL_INTERP_CDET_ZERO_ORDER_MIXED = prove
 (`!n s (ph:num->complex->complex) (G:num->num->complex->complex)
    (zeta:num->complex).
        s SUBSET 1..n /\
        (!i. i IN s ==> ph i holomorphic_on (:complex)) /\
        (!i j. i IN 1..n /\ j IN 1..n /\ ~(i IN s)
               ==> G i j holomorphic_on (:complex))
        ==> ?E. E holomorphic_on (:complex) /\
                !w. ring_det complex_ring (1..n)
                      (\i j. if i IN s then ph i (w * zeta j) else G i j w) =
                    w pow ((CARD s * (CARD s - 1)) DIV 2) * E w`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `k = CARD(s:num->bool)` THEN
  SUBGOAL_THEN
   `!i. ?(a:num->complex) (Q:complex->complex).
        i IN s
        ==> Q holomorphic_on (:complex) /\
            !z. (ph:num->complex->complex) i z =
                vsum(0..k) (\t. z pow t * (if t < k then a t else Q z))`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(i:num) IN s` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TL_INTERP_ENTIRE_FACTOR THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`a:num->num->complex`; `Q:num->complex->complex`] THEN
  DISCH_TAC THEN
  EXISTS_TAC
   `\w. vsum (cartesian_product (1..n) (\i. 0..k))
             (\mu. w pow (nsum s mu - (k * (k - 1)) DIV 2) *
                   cproduct(1..n)
                     (\i. if i IN s /\ mu i < k
                          then (a:num->num->complex) i (mu i) else Cx(&1)) *
                   ring_det complex_ring (1..n)
                     (\i j. if i IN s
                            then (zeta:num->complex) j pow (mu i) *
                                 (if mu i < k then Cx(&1)
                                  else (Q:num->complex->complex) i
                                         (w * zeta j))
                            else if mu i = 0
                            then (G:num->num->complex->complex) i j w
                            else Cx(&0)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_VSUM THEN
    SIMP_TAC[FINITE_CARTESIAN_PRODUCT_FINITE; FINITE_NUMSEG] THEN
    X_GEN_TAC `mu:num->num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN CONJ_TAC THENL
     [SIMP_TAC[HOLOMORPHIC_ON_POW; HOLOMORPHIC_ON_ID]; ALL_TAC] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
    MATCH_MP_TAC CDET_HOLOMORPHIC THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `(i:num) IN s` THEN
    ASM_REWRITE_TAC[] THENL
     [ASM_CASES_TAC `(mu:num->num) i < k` THEN
      ASM_REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
      REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
      SUBGOAL_THEN
       `(\w. (Q:num->complex->complex) i (w * (zeta:num->complex) j)) =
        Q i o (\w. w * zeta j)`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
      SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `(:complex)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV];
      ASM_CASES_TAC `(mu:num->num) i = 0` THEN
      ASM_REWRITE_TAC[HOLOMORPHIC_ON_CONST; ETA_AX] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `w:complex` THEN
  MP_TAC(ISPECL
   [`n:num`; `k:num`;
    `\i j. if i IN s
           then (ph:num->complex->complex) i (w * (zeta:num->complex) j)
           else (G:num->num->complex->complex) i j w`;
    `\i t j. if i IN s
             then (w * (zeta:num->complex) j) pow t *
                  (if t < k then (a:num->num->complex) i t
                   else (Q:num->complex->complex) i (w * zeta j))
             else if t = 0 then (G:num->num->complex->complex) i j w
             else Cx(&0)`]
   CDET_MULTILINEAR) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(i:num) IN s` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[];
      REWRITE_TAC[GSYM COMPLEX_VEC_0; VSUM_DELTA; IN_NUMSEG; LE_0]];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_CARTESIAN_PRODUCT_FINITE;
           FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `mu:num->num` THEN
  REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_NUMSEG; LE_0] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`n:num`; `k:num`; `s:num->bool`; `mu:num->num`; `a:num->num->complex`;
    `\i j. (Q:num->complex->complex) i (w * (zeta:num->complex) j)`;
    `\i j. if (mu:num->num) i = 0 then (G:num->num->complex->complex) i j w
           else Cx(&0)`;
    `w:complex`; `zeta:num->complex`] TL_INTERP_MONOMIAL_TERM_GEN) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; IN_NUMSEG];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[]);;

let TL_INTERP_CDET_ZERO_ORDER = prove
 (`!n (ph:num->complex->complex) (zeta:num->complex).
        (!i. i IN 1..n ==> ph i holomorphic_on (:complex))
        ==> ?E. E holomorphic_on (:complex) /\
                !w. ring_det complex_ring (1..n) (\i j. ph i (w * zeta j)) =
                    w pow ((n * (n - 1)) DIV 2) * E w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `1..n`; `ph:num->complex->complex`;
                 `\i:num j:num w:complex. Cx(&0)`; `zeta:num->complex`]
    TL_INTERP_CDET_ZERO_ORDER_MIXED) THEN
  ASM_REWRITE_TAC[SUBSET_REFL; CARD_NUMSEG_1; HOLOMORPHIC_ON_CONST] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `E:complex->complex` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:complex` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `w:complex`) THEN
  MATCH_MP_TAC RING_DET_EQ THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Maximum modulus on the disc |w| <= rr / r: the interpolation lemma, first *)
(* at an arbitrary point w with |w| r <= rr, then at w = 1; the mixed        *)
(* version (only the rows in s are interpolated, the others carry factors    *)
(* th i j with norm at most 1), first with a bound B for the products along  *)
(* permutations on the circle |w| = rho, then with row bounds.               *)
(* ------------------------------------------------------------------------- *)

let TL_INTERP_MAXMOD = prove
 (`!(D:complex->complex) E m R B w.
        &0 < R /\ E holomorphic_on (:complex) /\
        (!z. D z = z pow m * E z) /\
        (!z. norm z = R ==> norm(D z) <= B) /\
        norm w <= R
        ==> norm(D w) <= B * (norm w / R) pow m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`E:complex->complex`; `cball(vec 0:complex,R)`;
                 `B / R pow m`] MAXIMUM_MODULUS_FRONTIER) THEN
  REWRITE_TAC[BOUNDED_CBALL; FRONTIER_CBALL; IN_SPHERE_0; IN_CBALL_0] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET; SUBSET_UNIV];
      ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET; SUBSET_UNIV;
                    HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
      REWRITE_TAC[REAL_MUL_SYM]];
    DISCH_THEN(MP_TAC o SPEC `w:complex`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(w:complex) pow m * B / R pow m` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; NORM_POS_LE];
    REWRITE_TAC[REAL_POW_DIV; real_div; REAL_MUL_AC; REAL_LE_REFL]]);;

let INTERPOLATION_DETERMINANT_SCALED = prove
 (`!n (ph:num->complex->complex) (zeta:num->complex) r rr M w.
        &0 < r /\ &0 < rr /\ norm(w) * r <= rr /\
        (!i. i IN 1..n ==> ph i holomorphic_on (:complex)) /\
        (!i z. i IN 1..n /\ norm z <= rr ==> norm(ph i z) <= M i) /\
        (!j. j IN 1..n ==> norm(zeta j) <= r)
        ==> norm(ring_det complex_ring (1..n) (\i j. ph i (w * zeta j))) <=
            &(FACT n) * (norm(w) * r / rr) pow ((n * (n - 1)) DIV 2) *
            product(1..n) M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `ph:num->complex->complex`; `zeta:num->complex`]
         TL_INTERP_CDET_ZERO_ORDER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:complex->complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < rr / r` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\w. ring_det complex_ring (1..n)
          (\i j. (ph:num->complex->complex) i (w * (zeta:num->complex) j))`;
    `E:complex->complex`; `(n * (n - 1)) DIV 2`; `rr / r`;
    `&(FACT n) * product(1..n) (M:num->real)`; `w:complex`]
   TL_INTERP_MAXMOD) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      MATCH_MP_TAC CDET_NORM_LE THEN
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `rr / r * r` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]];
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(w:complex) / (rr / r) = norm w * r / rr` SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < r`; `&0 < rr`] THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[REAL_MUL_AC]]);;

let INTERPOLATION_DETERMINANT = prove
 (`!n (ph:num->complex->complex) (zeta:num->complex) r rr M.
       &0 < r /\ r <= rr /\
       (!i. i IN 1..n ==> ph i holomorphic_on (:complex)) /\
       (!i z. i IN 1..n /\ norm z <= rr ==> norm(ph i z) <= M i) /\
       (!j. j IN 1..n ==> norm(zeta j) <= r)
       ==> norm(ring_det complex_ring (1..n) (\i j. ph i (zeta j))) <=
           &(FACT n) * (r / rr) pow ((n * (n - 1)) DIV 2) * product(1..n) M`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rr` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `ph:num->complex->complex`; `zeta:num->complex`;
                 `r:real`; `rr:real`; `M:num->real`; `Cx(&1)`]
         INTERPOLATION_DETERMINANT_SCALED) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_NORM_CX; REAL_ABS_NUM;
                  REAL_MUL_LID]);;

let INTERPOLATION_DETERMINANT_MIXED_PERM = prove
 (`!n s (ph:num->complex->complex) (th:num->num->complex)
    (zeta:num->complex) rho B.
      s SUBSET 1..n /\ &1 <= rho /\
      (!i. i IN 1..n ==> ph i holomorphic_on (:complex)) /\
      (!i j. i IN 1..n /\ j IN 1..n ==> norm(th i j) <= &1) /\
      (!w p. norm w = rho /\ p permutes 1..n
             ==> product(1..n) (\i. norm(ph i (w * zeta (p i)))) <= B)
      ==> norm(ring_det complex_ring (1..n)
                 (\i j. if i IN s then ph i (zeta j)
                        else th i j * ph i (zeta j)))
          <= &(FACT n) * inv rho pow ((CARD s * (CARD s - 1)) DIV 2) * B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`n:num`; `s:num->bool`; `ph:num->complex->complex`;
    `\i j w. (th:num->num->complex) i j *
             (ph:num->complex->complex) i (w * (zeta:num->complex) j)`;
    `zeta:num->complex`] TL_INTERP_CDET_ZERO_ORDER_MIXED) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_LMUL THEN
    SUBGOAL_THEN
     `(\w. (ph:num->complex->complex) i (w * (zeta:num->complex) j)) =
      ph i o (\w. w * zeta j)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
    SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `(:complex)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV];
    DISCH_THEN(X_CHOOSE_THEN `E:complex->complex` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL
   [`\w. ring_det complex_ring (1..n)
          (\i j. if i IN s
                 then (ph:num->complex->complex) i (w * (zeta:num->complex) j)
                 else (th:num->num->complex) i j * ph i (w * zeta j))`;
    `E:complex->complex`; `(CARD(s:num->bool) * (CARD s - 1)) DIV 2`;
    `rho:real`; `&(FACT n) * B`; `Cx(&1)`]
   TL_INTERP_MAXMOD) THEN
  REWRITE_TAC[COMPLEX_MUL_LID] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      MATCH_MP_TAC CDET_NORM_LE_PERM THEN
      X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
      TRANS_TAC REAL_LE_TRANS
       `product(1..n) (\i. norm((ph:num->complex->complex) i
                                  (z * (zeta:num->complex) (p i))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN
        STRIP_TAC THEN REWRITE_TAC[NORM_POS_LE] THEN
        COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; COMPLEX_NORM_MUL] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `th:num->num->complex`)) (concl th))) THEN
        ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(y:real) = z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; real_div; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let TL_INTERP_PERM_PRODUCT_LE = prove
 (`!n (ph:num->complex->complex) zeta r rr M w p.
      &0 < r /\
      (!i z. i IN 1..n /\ norm z <= rr ==> norm(ph i z) <= M i) /\
      (!j. j IN 1..n ==> norm(zeta j) <= r) /\
      norm w = rr / r /\ p permutes 1..n
      ==> product(1..n) (\i. norm(ph i (w * zeta (p i)))) <= product(1..n) M`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[NORM_POS_LE] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `norm((zeta:num->complex) (p(i:num))) <= r` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `rr / r * r` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS];
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]]);;

let INTERPOLATION_DETERMINANT_MIXED = prove
 (`!n s ph th zeta r rr M.
      s SUBSET 1..n /\ &0 < r /\ r <= rr /\
      (!i. i IN 1..n ==> ph i holomorphic_on (:complex)) /\
      (!i z. i IN 1..n /\ norm z <= rr ==> norm(ph i z) <= M i) /\
      (!j. j IN 1..n ==> norm(zeta j) <= r) /\
      (!i j. i IN 1..n /\ j IN 1..n ==> norm(th i j) <= &1)
      ==> norm(ring_det complex_ring (1..n)
                 (\i j. if i IN s then ph i (zeta j)
                        else th i j * ph i (zeta j)))
          <= &(FACT n) * (r / rr) pow ((CARD s * (CARD s - 1)) DIV 2) *
             product(1..n) M`,
  MAP_EVERY X_GEN_TAC
   [`n:num`; `s:num->bool`; `ph:num->complex->complex`;
    `th:num->num->complex`; `zeta:num->complex`; `r:real`; `rr:real`;
    `M:num->real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `s:num->bool`; `ph:num->complex->complex`;
                 `th:num->num->complex`; `zeta:num->complex`; `rr / r`;
                 `product(1..n) (M:num->real)`]
    INTERPOLATION_DETERMINANT_MIXED_PERM) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID; REAL_INV_DIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TL_INTERP_PERM_PRODUCT_LE THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Expansion of a perturbed determinant over the subsets of the rows, and    *)
(* the resulting bound (Bugeaud, Lemma 11.6, formula (11.12)), first with a  *)
(* bound B for the products along permutations on the circle |w| = rho, then *)
(* with row bounds.                                                          *)
(* ------------------------------------------------------------------------- *)

let TL_INTERP_VSUM_01 = prove
 (`!g:num->complex. vsum(0..1) g = g 0 + g 1`,
  GEN_TAC THEN
  REWRITE_TAC[MATCH_MP VSUM_CLAUSES_LEFT (ARITH_RULE `0 <= 1`)] THEN
  REWRITE_TAC[ADD_CLAUSES; VSUM_SING_NUMSEG]);;

let TL_INTERP_CPRODUCT_COND_CONST = prove
 (`!n (P:num->bool) (c:complex).
        cproduct(1..n) (\i. if i IN 1..n /\ P i then Cx(&1) else c) =
        c pow (n - CARD {i | i IN 1..n /\ P i})`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS
   `cproduct ((1..n) DIFF {i | i IN 1..n /\ (P:num->bool) i})
             (\i. if i IN 1..n /\ P i then Cx(&1) else (c:complex))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CPRODUCT_SUPERSET THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM; SUBSET_DIFF] THEN
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `cproduct ((1..n) DIFF {i | i IN 1..n /\ (P:num->bool) i})
             (\i. (c:complex))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CPRODUCT_EQ THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[];
    SIMP_TAC[CPRODUCT_CONST; FINITE_DIFF; FINITE_NUMSEG] THEN
    AP_TERM_TAC THEN
    SIMP_TAC[CARD_DIFF; FINITE_NUMSEG; CARD_NUMSEG_1; SUBSET_RESTRICT]]);;

let CDET_PERTURB_EXPANSION = prove
 (`!n (f:num->num->complex) th c.
        ring_det complex_ring (1..n) (\i j. f i j * (Cx(&1) + c * th i j)) =
        vsum {J | J SUBSET 1..n}
             (\J. c pow (n - CARD J) *
                  ring_det complex_ring (1..n)
                    (\i j. if i IN J then f i j else th i j * f i j))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`n:num`; `1`;
    `\i j. (f:num->num->complex) i j * (Cx(&1) + c * th i j)`;
    `\i t j. if i IN 1..n /\ t = 0 then (f:num->num->complex) i j
             else c * (th:num->num->complex) i j * f i j`]
   CDET_MULTILINEAR) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[TL_INTERP_VSUM_01] THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    CONV_TAC COMPLEX_RING;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `{J | J SUBSET 1..n} =
    IMAGE (\mu. {i | i IN 1..n /\ (mu:num->num) i = 0})
          (cartesian_product (1..n) (\i. 0..1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `J:num->bool` THEN EQ_TAC THENL
     [DISCH_TAC THEN
      EXISTS_TAC `RESTRICTION (1..n) (\i. if i IN J then 0 else 1)` THEN
      REWRITE_TAC[RESTRICTION_IN_CARTESIAN_PRODUCT] THEN CONJ_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; RESTRICTION] THEN
        X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(i:num) IN 1..n` THEN
        ASM_REWRITE_TAC[] THENL
         [COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ];
          ASM_MESON_TAC[SUBSET]];
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
        COND_CASES_TAC THEN ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `mu:num->num` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\mu. {i | i IN 1..n /\ (mu:num->num) i = 0}`;
    `\J. (c:complex) pow (n - CARD J) *
         ring_det complex_ring (1..n)
           (\i j. if i IN J then (f:num->num->complex) i j
                  else (th:num->num->complex) i j * f i j)`;
    `cartesian_product (1..n) (\i:num. 0..1)`] VSUM_IMAGE) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_CARTESIAN_PRODUCT_FINITE; FINITE_NUMSEG] THEN
    REWRITE_TAC[IN_CARTESIAN_PRODUCT; EXTENSIONAL; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`mu:num->num`; `nu:num->num`] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:num` THEN
    ASM_CASES_TAC `(x:num) IN 1..n` THENL
     [SUBGOAL_THEN
       `(mu:num->num) x IN 0..1 /\ (nu:num->num) x IN 0..1 /\
        (mu x = 0 <=> nu x = 0)`
      MP_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC];
      ASM_SIMP_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `mu:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM; IN_ELIM_THM] THEN
  MP_TAC(ISPECL
   [`n:num`;
    `\i. if i IN 1..n /\ (mu:num->num) i = 0 then Cx(&1) else c`;
    `\i j. if i IN 1..n /\ (mu:num->num) i = 0 then (f:num->num->complex) i j
           else (th:num->num->complex) i j * f i j`]
   CDET_ROWS_CMUL) THEN
  REWRITE_TAC[TL_INTERP_CPRODUCT_COND_CONST] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[COMPLEX_MUL_LID]);;

let TL_INTERP_ARITH_AUX2 = prove
 (`!k l s. k * (k - 1) <= 2 * s + 1
           ==> ((k + l) * ((k + l) - 1)) DIV 2 <= (k + l) * l + s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(2 * ((k + l) * l + s) + 1) DIV 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIV_MONO THEN
    MP_TAC(SPEC `k:num` TL_INTERP_MUL_PRED) THEN
    MP_TAC(SPEC `k + l:num` TL_INTERP_MUL_PRED) THEN
    UNDISCH_TAC `k * (k - 1) <= 2 * s + 1` THEN ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `(2 * x + 1) DIV 2 = x`; LE_REFL]]);;

let TL_INTERP_EXPONENT_BOUND = prove
 (`!n k. k <= n
         ==> (n * (n - 1)) DIV 2 <= n * (n - k) + (k * (k - 1)) DIV 2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `l:num` SUBST1_TAC o
    GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  REWRITE_TAC[ADD_SUB2] THEN MATCH_MP_TAC TL_INTERP_ARITH_AUX2 THEN
  REWRITE_TAC[ARITH_RULE `x <= 2 * x DIV 2 + 1`]);;

let TL_INTERP_VSUM_NORM_CONST = prove
 (`!s (f:A->complex) B C.
        FINITE s /\ (!x. x IN s ==> norm(f x) <= B) /\ &(CARD s) * B <= C
        ==> norm(vsum s f) <= C`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (s:A->bool) (\x. B)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SUM_CONST]]);;

let INTERPOLATION_DETERMINANT_PERTURBED_PERM = prove
 (`!n (ph:num->complex->complex) (th:num->num->complex) (zeta:num->complex)
    rho B c.
     &1 <= rho /\
     (!i. i IN 1..n ==> ph i holomorphic_on (:complex)) /\
     (!i j. i IN 1..n /\ j IN 1..n ==> norm(th i j) <= &1) /\
     (!w p. norm w = rho /\ p permutes 1..n
            ==> product(1..n) (\i. norm(ph i (w * zeta (p i)))) <= B) /\
     norm c <= inv(rho pow n)
     ==> norm(ring_det complex_ring (1..n)
                (\i j. ph i (zeta j) * (Cx(&1) + c * th i j))) <=
         &2 pow n * &(FACT n) * inv(rho pow ((n * (n - 1)) DIV 2)) * B`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CDET_PERTURB_EXPANSION] THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv rho /\ inv rho <= &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_INV_LE_1]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `product(1..n) (\i. norm((ph:num->complex->complex) i
                                (Cx rho * (zeta:num->complex) (I i))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN REWRITE_TAC[NORM_POS_LE];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[PERMUTES_I; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC TL_INTERP_VSUM_NORM_CONST THEN
  EXISTS_TAC `&(FACT n) * inv(rho pow ((n * (n - 1)) DIV 2)) * B` THEN
  SIMP_TAC[FINITE_POWERSET; FINITE_NUMSEG; CARD_POWERSET; CARD_NUMSEG_1;
           REAL_OF_NUM_POW; REAL_LE_REFL] THEN
  X_GEN_TAC `J:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `CARD(J:num->bool) <= n` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_1] THEN
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `J:num->bool`; `ph:num->complex->complex`;
                 `th:num->num->complex`; `zeta:num->complex`; `rho:real`;
                 `B:real`] INTERPOLATION_DETERMINANT_MIXED_PERM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `inv(rho pow n) pow (n - CARD(J:num->bool)) *
    &(FACT n) * inv rho pow ((CARD J * (CARD J - 1)) DIV 2) * B` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_POW_LE; NORM_POS_LE; REAL_POW_LE2];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_POW_INV; REAL_POW_POW] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a:real) * b * c * d = b * (a * c) * d`] THEN
  REWRITE_TAC[GSYM REAL_POW_ADD] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[TL_INTERP_EXPONENT_BOUND]);;

let INTERPOLATION_DETERMINANT_PERTURBED = prove
 (`!n ph th zeta r rr M c.
      &0 < r /\ r <= rr /\
      (!i. i IN 1..n ==> ph i holomorphic_on (:complex)) /\
      (!i z. i IN 1..n /\ norm z <= rr ==> norm(ph i z) <= M i) /\
      (!j. j IN 1..n ==> norm(zeta j) <= r) /\
      (!i j. i IN 1..n /\ j IN 1..n ==> norm(th i j) <= &1) /\
      norm c <= (r / rr) pow n
      ==> norm(ring_det complex_ring (1..n)
                 (\i j. ph i (zeta j) * (Cx(&1) + c * th i j))) <=
          &2 pow n * &(FACT n) * (r / rr) pow ((n * (n - 1)) DIV 2) *
          product(1..n) M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `ph:num->complex->complex`; `th:num->num->complex`;
                 `zeta:num->complex`; `rr / r`; `product(1..n) (M:num->real)`;
                 `c:complex`] INTERPOLATION_DETERMINANT_PERTURBED_PERM) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID; GSYM REAL_POW_INV;
               REAL_INV_DIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TL_INTERP_PERM_PRODUCT_LE THEN ASM_MESON_TAC[]);;
