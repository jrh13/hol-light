(* ========================================================================= *)
(* Polynomials over C: factorization, Newton identities, power sums.         *)
(*                                                                           *)
(* Purpose: complex polynomial functions vsum(0..n) (\i. c i * z pow i):     *)
(* equal functions have equal coefficients; factorization into linear        *)
(* factors (by the fundamental theorem of algebra FTA); multiplication by a  *)
(* linear factor; the coefficients of a product prod_i (x - z i) and the     *)
(* derivative of a product; the Newton identities between these coefficients *)
(* and the power sums sum_i z i^m, hence integer coefficients give integer   *)
(* power sums, and conversely up to factorials; and the basic Liouville-type *)
(* estimate: a nonzero member of a finite family whose power sums are all    *)
(* integers is not too small.                                                *)
(*                                                                           *)
(* Main results: COMPLEX_POLYFUN_EQ (coefficient comparison),                *)
(*   COMPLEX_POLYFUN_FACTOR (factorization into linear factors),             *)
(*   COMPLEX_POLYFUN_MUL_LINEAR, CPRODUCT_DELETE, CPRODUCT_LINEAR_POLYFUN    *)
(*   (coefficients of a product of linear factors),                          *)
(*   HAS_COMPLEX_DERIVATIVE_CPRODUCT, MONIC_VANISHING_AT_COMPLEX_COEFF (the  *)
(*   coefficients of monic_vanishing_at complex_ring), NEWTON_IDENTITIES,    *)
(*   NEWTON_INTEGER_POWER_SUMS, NEWTON_INTEGER_COEFFICIENTS,                 *)
(*   POWER_SUMS_INTEGER_LOWER_BOUND (the Liouville-type estimate).           *)
(*                                                                           *)
(* Uses: Baker/prelim.ml (complex integers, COMPLEX_INTEGER_ZINC);           *)
(*   100/transcendence.ml (monic_vanishing_at, newton_identities,            *)
(*   powersums_subring_if_poly_subring, poly_eval_vsum).                     *)
(* ========================================================================= *)

needs "Baker/prelim.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Basic manipulation of complex polynomial functions.                       *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_POLYFUN_EQ = prove
 (`!n c d. (!z. vsum(0..n) (\i. c i * z pow i) =
                vsum(0..n) (\i. d i * z pow i)) <=>
           (!i. i IN 0..n ==> c i = d i)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM COMPLEX_SUB_0] THEN
  SIMP_TAC[GSYM VSUM_SUB_NUMSEG; GSYM COMPLEX_SUB_RDISTRIB] THEN
  REWRITE_TAC[COMPLEX_POLYFUN_EQ_0]);;

let COMPLEX_POLYFUN_LINEAR_FACTOR_TOP = prove
 (`!a c n.
        1 <= n
        ==> ?b. b(n - 1) = c n /\
                !z. vsum(0..n) (\i. c(i) * z pow i) =
                    (z - a) * vsum(0..n-1) (\i. b(i) * z pow i) +
                    vsum(0..n) (\i. c(i) * a pow i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM COMPLEX_EQ_SUB_RADD] THEN
  ASM_SIMP_TAC[COMPLEX_SUB_POLYFUN] THEN
  EXISTS_TAC `\j. vsum (j + 1..n) (\i. c i * a pow (i - j - 1))` THEN
  REWRITE_TAC[] THEN ASM_SIMP_TAC[SUB_ADD; VSUM_SING_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `n - (n - 1) - 1 = 0`; complex_pow; COMPLEX_MUL_RID]);;

let COMPLEX_POLYFUN_FACTOR = prove
 (`!n a. ~(a n = Cx(&0))
         ==> ?r. !z. vsum(0..n) (\i. a i * z pow i) =
                     a n * cproduct(1..n) (\i. z - r i)`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC `\i:num. Cx(&0)` THEN
    REWRITE_TAC[VSUM_SING_NUMSEG; CPRODUCT_CLAUSES_NUMSEG; ARITH] THEN
    REWRITE_TAC[complex_pow; COMPLEX_MUL_RID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:num->complex`; `SUC n`] FTA) THEN ANTS_TAC THENL
   [DISJ2_TAC THEN DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `w:complex`)] THEN
  MP_TAC(ISPECL [`w:complex`; `a:num->complex`; `SUC n`]
    COMPLEX_POLYFUN_LINEAR_FACTOR_TOP) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= SUC n`; SUC_SUB1; COMPLEX_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->complex` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:num->complex`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `r:num->complex`) THEN
  EXISTS_TAC `\i. if i = SUC n then w else (r:num->complex) i` THEN
  ASM_REWRITE_TAC[CPRODUCT_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  GEN_TAC THEN
  SUBGOAL_THEN
   `cproduct(1..n) (\i. z - (if i = SUC n then w else r i)) =
    cproduct(1..n) (\i. z - r i)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CPRODUCT_EQ THEN
    SIMP_TAC[IN_NUMSEG; ARITH_RULE `i <= n ==> ~(i = SUC n)`];
    REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING]);;

let COMPLEX_POLYFUN_MUL_LINEAR = prove
 (`!n c w x.
        (x - w) * vsum(0..n) (\k. c k * x pow k) =
        vsum(0..SUC n)
         (\k. ((if k = 0 then Cx(&0) else c(k - 1)) -
               w * (if k <= n then c k else Cx(&0))) * x pow k)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[COMPLEX_SUB_RDISTRIB; VSUM_SUB_NUMSEG] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN BINOP_TAC THENL
   [CONV_TAC(RAND_CONV(REWRITE_CONV
     [MATCH_MP VSUM_CLAUSES_LEFT (ARITH_RULE `0 <= SUC n`)])) THEN
    REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_LID; ADD1; VSUM_OFFSET] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_POW_ADD] THEN CONV_TAC COMPLEX_RING;
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
    SIMP_TAC[VSUM_CLAUSES_NUMSEG; LE_0; ARITH_RULE `~(SUC n <= n)`] THEN
    REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID]]);;

(* ------------------------------------------------------------------------- *)
(* Products of linear factors and their coefficients.                        *)
(* ------------------------------------------------------------------------- *)

let CPRODUCT_DELETE = prove
 (`!f s (a:A).
        FINITE s /\ a IN s ==> cproduct s f = f a * cproduct (s DELETE a) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:A`; `f:A->complex`; `s DELETE (a:A)`]
    (CONJUNCT2 CPRODUCT_CLAUSES)) THEN
  ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE; INSERT_DELETE]);;

let CPRODUCT_LINEAR_POLYFUN = prove
 (`!s (z:A->complex).
        FINITE s
        ==> ?c. c(CARD s) = Cx(&1) /\
                !x. cproduct s (\i. x - z i) =
                    vsum(0..CARD s) (\k. c k * x pow k)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [GEN_TAC THEN EXISTS_TAC `\k:num. Cx(&1)` THEN
    REWRITE_TAC[CARD_CLAUSES; CPRODUCT_CLAUSES; VSUM_SING_NUMSEG] THEN
    REWRITE_TAC[complex_pow; COMPLEX_MUL_RID];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `z:A->complex` THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `c:num->complex` STRIP_ASSUME_TAC o
    SPEC `z:A->complex`) THEN
  ASM_SIMP_TAC[CARD_CLAUSES; CPRODUCT_CLAUSES] THEN
  EXISTS_TAC
   `\k. (if k = 0 then Cx(&0) else c(k - 1)) -
        (z:A->complex) a * (if k <= CARD(s:A->bool) then c k else Cx(&0))` THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; ARITH_RULE `~(SUC n <= n)`] THEN
  REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_SUB_RZERO] THEN
  ASM_REWRITE_TAC[GSYM COMPLEX_POLYFUN_MUL_LINEAR]);;

let HAS_COMPLEX_DERIVATIVE_CPRODUCT = prove
 (`!s (f:A->complex->complex) f' x.
        FINITE s /\
        (!i. i IN s ==> (f i has_complex_derivative f' i) (at x))
        ==> ((\x. cproduct s (\i. f i x)) has_complex_derivative
             vsum s (\i. f' i * cproduct (s DELETE i) (\j. f j x))) (at x)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[CPRODUCT_CLAUSES; VSUM_CLAUSES; COMPLEX_VEC_0;
                HAS_COMPLEX_DERIVATIVE_CONST];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CPRODUCT_CLAUSES; VSUM_CLAUSES] THEN
  SUBGOAL_THEN
   `vsum s (\i. f' i * cproduct ((a INSERT s) DELETE i) (\j. f j x)) =
    (f:A->complex->complex) a x *
    vsum s (\i. f' i * cproduct (s DELETE i) (\j. f j x))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL] THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `i:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a INSERT s) DELETE (i:A) = a INSERT (s DELETE i)`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CPRODUCT_CLAUSES; FINITE_DELETE; IN_DELETE] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a INSERT s) DELETE (a:A) = s` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_MUL_AT THEN ASM_SIMP_TAC[ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Newton identities for the coefficients c of prod_{i IN s} (x - z i):      *)
(*   (CARD s - u) * c u = -- sum_{k = u+1}^{CARD s} c k * p(k - u)           *)
(* where p m = sum_{i IN s} z i pow m are the power sums: c k is the k-th    *)
(* coefficient of monic_vanishing_at complex_ring s z, and the identities    *)
(* and the integrality of the power sums are newton_identities and           *)
(* powersums_subring_if_poly_subring of 100/transcendence.ml.                *)
(* ------------------------------------------------------------------------- *)

let MONIC_VANISHING_AT_COMPLEX_COEFF = prove
 (`!s (z:A->complex) c.
        FINITE s /\
        (!x. cproduct s (\i. x - z i) = vsum(0..CARD s) (\k. c k * x pow k))
        ==> !k. coeff k (monic_vanishing_at complex_ring s z) =
                if k <= CARD s then c k else Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `p = monic_vanishing_at complex_ring s (z:A->complex)` THEN
  SUBGOAL_THEN `ring_polynomial complex_ring (p:(1->num)->complex) /\
                poly_deg complex_ring p <= CARD(s:A->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN
    ASM_SIMP_TAC[monic_vanishing_at_poly; deg_monic_vanishing_at_le;
                 IN_UNIV; COMPLEX_RING_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. vsum(0..CARD s) (\k. coeff k (p:(1->num)->complex) * x pow k) =
        vsum(0..CARD(s:A->bool)) (\k. c k * x pow k)`
  MP_TAC THENL
   [ASM_SIMP_TAC[poly_eval_vsum] THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN EXPAND_TAC "p" THEN
    ASM_SIMP_TAC[eval_monic_vanishing_at; IN_UNIV; COMPLEX_RING_CLAUSES;
                 COMPLEX_RING_SUB; COMPLEX_RING_PRODUCT];
    REWRITE_TAC[COMPLEX_POLYFUN_EQ; IN_NUMSEG; LE_0] THEN DISCH_TAC] THEN
  X_GEN_TAC `k:num` THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(MESON[] `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`complex_ring`; `p:(1->num)->complex`; `k:num`]
    COEFF_NONZERO_LE_DEG) THEN
  ASM_REWRITE_TAC[COMPLEX_RING_CLAUSES] THEN ASM_ARITH_TAC);;

let NEWTON_IDENTITIES = prove
 (`!s (z:A->complex) c.
        FINITE s /\
        (!x. cproduct s (\i. x - z i) = vsum(0..CARD s) (\k. c k * x pow k))
        ==> !u. u <= CARD s
                ==> Cx(&(CARD s - u)) * c u =
                    --vsum(u+1..CARD s)
                          (\k. c k * vsum s (\i. z i pow (k - u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `z:A->complex`; `c:num->complex`]
    MONIC_VANISHING_AT_COMPLEX_COEFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `u:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`complex_ring`; `z:A->complex`; `s:A->bool`;
                 `CARD(s:A->bool) - u`] newton_identities) THEN
  ASM_SIMP_TAC[IN_UNIV; COMPLEX_RING_CLAUSES; coeff_x_derivative;
               COMPLEX_RING_POW; COMPLEX_RING_SUM; FINITE_NUMSEG;
               COMPLEX_RING_OF_NUM] THEN
  ABBREV_TAC `D = CARD(s:A->bool)` THEN
  SUBGOAL_THEN
   `vsum(0..D - u)
     (\a'. (if a' <= D then if D - a' <= D then (c:num->complex)(D - a')
                             else Cx(&0) else Cx(&0)) *
           vsum s (\x. (z:A->complex) x pow (D - u - a'))) =
    Cx(&D) * c u + vsum(u+1..D) (\k. c k * vsum s (\i. z i pow (k - u)))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\k. (c:num->complex) k *
                        vsum s (\i. (z:A->complex) i pow (k - u))`;
                   `u:num`; `D:num`] VSUM_REFLECT) THEN
    ASM_SIMP_TAC[VSUM_CLAUSES_LEFT; GSYM NOT_LE; SUB_REFL; complex_pow;
                 VSUM_CONST; COMPLEX_CMUL; COMPLEX_MUL_RID] THEN
    DISCH_TAC THEN
    TRANS_TAC EQ_TRANS `vsum(0..D - u) (\i. (c:num->complex)(D - i) *
                          vsum s (\i'. (z:A->complex) i' pow (D - i - u)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `i <= D /\ D - i <= D` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_ARITH_TAC; REWRITE_TAC[ARITH_RULE `D - u - i = D - i - (u:num)`]];
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC COMPLEX_RING];
    ALL_TAC] THEN
  ASM_CASES_TAC `u = 0` THENL
   [ASM_CASES_TAC `D = 0` THEN ASM_REWRITE_TAC[SUB_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[ARITH_RULE `~(D = 0) ==> ~(D <= D - 1)`; VSUM_TRIV_NUMSEG;
                 ARITH] THEN
    CONV_TAC COMPLEX_RING;
    ASM_SIMP_TAC[ARITH_RULE `~(u = 0) /\ u <= D
                             ==> D - u <= D - 1 /\ D - 1 - (D - u) + 1 = u`;
                 GSYM REAL_OF_NUM_SUB; CX_SUB] THEN
    CONV_TAC COMPLEX_RING]);;

(* ------------------------------------------------------------------------- *)
(* Integrality consequences of the Newton identities.                        *)
(* ------------------------------------------------------------------------- *)

let CPRODUCT_LINEAR_POLYFUN_TOP = prove
 (`!s (z:A->complex) c.
        FINITE s /\
        (!x. cproduct s (\i. x - z i) = vsum(0..CARD s) (\k. c k * x pow k))
        ==> c(CARD s) = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `z:A->complex`] CPRODUCT_LINEAR_POLYFUN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!i. i IN 0..CARD(s:A->bool) ==> c i:complex = b i` MP_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_POLYFUN_EQ] THEN ASM_MESON_TAC[];
    DISCH_THEN(MP_TAC o SPEC `CARD(s:A->bool)`) THEN
    ASM_REWRITE_TAC[IN_NUMSEG; LE_0; LE_REFL]]);;

let NEWTON_INTEGER_POWER_SUMS = prove
 (`!s (z:A->complex) c.
        FINITE s /\
        (!x. cproduct s (\i. x - z i) = vsum(0..CARD s) (\k. c k * x pow k)) /\
        (!k. k <= CARD s ==> complex_integer(c k))
        ==> !m. complex_integer(vsum s (\i. z i pow m))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `m:num` THEN
  MP_TAC(ISPECL [`complex_ring`; `ZinC`; `s:A->bool`; `z:A->complex`;
                 `m:num`] powersums_subring_if_poly_subring) THEN
  MP_TAC(ISPECL [`s:A->bool`; `z:A->complex`; `c:num->complex`]
    MONIC_VANISHING_AT_COMPLEX_COEFF) THEN
  ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING; ZinC_subring_complex;
               IN_UNIV; COMPLEX_RING_CLAUSES; COMPLEX_RING_SUM;
               COMPLEX_RING_POW; GSYM COMPLEX_INTEGER_ZINC] THEN
  DISCH_THEN(K ALL_TAC) THEN DISCH_THEN MATCH_MP_TAC THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[COMPLEX_INTEGER_CLOSED]);;

let NEWTON_INTEGER_COEFFICIENTS = prove
 (`!s (z:A->complex) c.
        FINITE s /\
        (!x. cproduct s (\i. x - z i) = vsum(0..CARD s) (\k. c k * x pow k)) /\
        (!m. 1 <= m /\ m <= CARD s ==> complex_integer(vsum s (\i. z i pow m)))
        ==> !k. k <= CARD s
                ==> complex_integer(Cx(&(FACT(CARD s - k))) * c k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `D = CARD(s:A->bool)` THEN
  SUBGOAL_THEN `(c:num->complex) D = Cx(&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CPRODUCT_LINEAR_POLYFUN_TOP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t <= D ==> complex_integer(Cx(&(FACT t)) * c(D - t))`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `D - k`) THEN
    ASM_SIMP_TAC[ARITH_RULE `k <= D ==> D - (D - k) = k`; ARITH_RULE `D - k <=
      D`]] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `t:num` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t = 0` THENL
   [ASM_REWRITE_TAC[FACT; SUB_0; COMPLEX_MUL_LID; COMPLEX_INTEGER_CX_NUM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:A->bool`; `z:A->complex`; `c:num->complex`]
    NEWTON_IDENTITIES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `D - t`) THEN
  ASM_SIMP_TAC[ARITH_RULE `t <= D ==> D - (D - t) = t`;
               ARITH_RULE `D - t <= D`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `FACT t = t * FACT(t - 1)` SUBST1_TAC THENL
   [MP_TAC(SPEC `t - 1` (CONJUNCT2 FACT)) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(t = 0) ==> SUC(t - 1) = t`];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `(a * b) * c:complex = b * (a * c)`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[COMPLEX_MUL_RNEG] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC COMPLEX_INTEGER_NEG THEN
  MATCH_MP_TAC COMPLEX_INTEGER_VSUM THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `FACT(t - 1) = FACT(D - k) * FACT((t - 1) - (D - k)) *
                  binom((D - k) + ((t - 1) - (D - k)),(t - 1) - (D - k))`
  SUBST1_TAC THENL
   [REWRITE_TAC[BINOM_FACT] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING
   `(a * b * c) * d * e:complex = (b * c) * (a * d) * e`] THEN
  MATCH_MP_TAC COMPLEX_INTEGER_MUL THEN
  REWRITE_TAC[GSYM CX_MUL; REAL_OF_NUM_MUL; COMPLEX_INTEGER_CX_NUM] THEN
  MATCH_MP_TAC COMPLEX_INTEGER_MUL THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `D - k`) THEN
    ASM_SIMP_TAC[ARITH_RULE `k <= D ==> D - (D - k) = k`] THEN
    DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The basic Liouville-type estimate: a nonzero member of a finite family    *)
(* whose power sums are all integers cannot be too small.                    *)
(* ------------------------------------------------------------------------- *)

let POWER_SUMS_INTEGER_LOWER_BOUND = prove
 (`!s (z:A->complex) a b.
        FINITE s /\ a IN s /\ ~(z a = Cx(&0)) /\ &1 <= b /\
        (!i. i IN s ==> norm(z i) <= b) /\
        (!m. 1 <= m ==> complex_integer(vsum s (\i. z i pow m)))
        ==> inv(&(FACT(CARD s)) * b pow (CARD s - 1)) <= norm(z a)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `t = {i | i IN s /\ ~((z:A->complex) i = Cx(&0))}` THEN
  SUBGOAL_THEN `FINITE(t:A->bool) /\ t SUBSET s /\ (a:A) IN t`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_RESTRICT];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. 1 <= m ==> vsum t (\i. (z:A->complex) i pow m) =
                   vsum s (\i. z i pow m)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC VSUM_SUPERSET THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[IN_ELIM_THM; COMPLEX_VEC_0] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(z:A->complex) x = Cx(&0)` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ASM_SIMP_TAC[COMPLEX_POW_ZERO; LE_1]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:A->bool`; `z:A->complex`] CPRODUCT_LINEAR_POLYFUN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:A->bool`; `z:A->complex`; `c:num->complex`]
    NEWTON_INTEGER_COEFFICIENTS) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[LE_0; SUB_0] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Cx(&0)`) THEN
  SUBGOAL_THEN `vsum (0..CARD(t:A->bool)) (\k. c k * Cx (&0) pow k) = c 0`
  SUBST1_TAC THENL
   [SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0; complex_pow; COMPLEX_MUL_RID] THEN
    MATCH_MP_TAC(COMPLEX_RING `y = Cx(&0) ==> x + y = x`) THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
    REWRITE_TAC[IN_NUMSEG; COMPLEX_POW_ZERO; COMPLEX_VEC_0] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `0 + 1 <= k ==> ~(k = 0)`; COMPLEX_MUL_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_SUB_LZERO] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
  MP_TAC(ISPEC `Cx(&(FACT(CARD(t:A->bool)))) *
                cproduct t (\i. --(z:A->complex) i)` COMPLEX_INTEGER_NORM) THEN
  ASM_SIMP_TAC[COMPLEX_ENTIRE; CX_INJ; REAL_OF_NUM_EQ; FACT_NZ;
               CPRODUCT_EQ_0; COMPLEX_NEG_EQ_0] THEN
  ANTS_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_MUL; NORM_CPRODUCT; COMPLEX_NORM_CX;
               REAL_ABS_NUM; NORM_NEG] THEN
  MP_TAC(ISPECL [`\i:A. norm((z:A->complex) i)`; `t:A->bool`; `a:A`]
    PRODUCT_DELETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `product (t DELETE (a:A)) (\i. norm((z:A->complex) i)) <=
    b pow (CARD(s:A->bool) - 1)`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `product (t DELETE (a:A)) (\i. b)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_LE THEN
      ASM_SIMP_TAC[FINITE_DELETE; NORM_POS_LE; IN_DELETE] THEN ASM SET_TAC[];
      ASM_SIMP_TAC[PRODUCT_CONST; FINITE_DELETE; CARD_DELETE] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `CARD(t:A->bool) <= CARD(s:A->bool)` MP_TAC THENL
       [ASM_SIMP_TAC[CARD_SUBSET]; ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(FACT(CARD(t:A->bool))) <= &(FACT(CARD(s:A->bool)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC FACT_MONO THEN
    ASM_SIMP_TAC[CARD_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < &(FACT(CARD(s:A->bool))) * b pow (CARD(s:A->bool) - 1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `&1 <= x ==> x <= y ==> &1 <= y`)) THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `f * n * (b:real) = n * f * b`] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN
    ASM_SIMP_TAC[FINITE_DELETE; NORM_POS_LE];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]]);;
