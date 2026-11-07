(* ========================================================================= *)
(* The superelliptic equation: two simple roots give finitely many x.        *)
(*                                                                           *)
(* Purpose: if d1 (x - z1) and d2 (x - z2) are both m-th powers of integer   *)
(* polynomial expressions in z1 resp. z2 (m >= 3, d1, d2 from finite sets),  *)
(* then x lies in a finite set. Route: the Siegel identity for               *)
(* lambda_j = rho2 xi1 - zeta^j rho1 xi2 in a common number field            *)
(* (NF_PRIMITIVE_ELEMENT), the product of the lambda_j is fixed, bounded     *)
(* norms (NF_BOUNDED_NORM_FINITE), and the unit equation NF_UNIT_EQUATION.   *)
(*                                                                           *)
(* Main results: SUPERELL_TWO_ROOTS, SUPERELL_TR_CORE (the same for data     *)
(* in one fixed order), UNITY_ROOT_PRODUCT_DIFF; the generic number field    *)
(* steps NF_ORDER_FACTOR_NORMS (factors of a fixed non-zero order element    *)
(* have bounded non-zero norms) and NF_SIEGEL_RATIO_FINITE (the ratios       *)
(* l0 1 / l2 1 of the solutions of cc0 l0 + cc1 l1 + cc2 l2 = 0 with bounded *)
(* norms lie in a finite set), used also by Baker/hyperell_roots.ml.         *)
(*                                                                           *)
(* Uses: Baker/nf_fields.ml (NF_PRIMITIVE_ELEMENT), Baker/uniteq.ml          *)
(* (NF_UNIT_EQUATION), Baker/nf_box.ml (NF_BOUNDED_NORM_FINITE),             *)
(* Baker/nf_units.ml (NF_UNIT_NONZERO, NF_UNIT_DIV), Baker/nf_order.ml       *)
(* (NF_ORDER_CPRODUCT, NF_NORM_INTEGER), Baker/nf_defs.ml (NF_DATA_1_IN),    *)
(* Baker/algint.ml (ALGEBRAIC_INTEGER_POW_ROOT,                              *)
(* ALGEBRAIC_INTEGER_ROOT_OF_UNITY), Baker/lemmas.ml (UNITY_ROOT_CEXP),      *)
(* Baker/algebraic.ml (CPRODUCT_DELETE, CPRODUCT_LINEAR_POLYFUN).            *)
(* ========================================================================= *)

needs "Baker/nf_fields.ml";;
needs "Baker/uniteq.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Products over the m-th roots of unity.                                    *)
(* ------------------------------------------------------------------------- *)

let SUPERELL_TR_POLY_ROOTS_ZERO = prove
 (`!n (a:num->complex) s.
        FINITE s /\ n < CARD s /\
        (!z. z IN s ==> vsum(0..n) (\i. a i * z pow i) = Cx(&0))
        ==> !z. vsum(0..n) (\i. a i * z pow i) = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[COMPLEX_POLYFUN_EQ_0] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPLEX_POLYFUN_ROOTBOUND) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `CARD(s:complex->bool) <=
    CARD {z | vsum(0..n) (\i. (a:num->complex) i * z pow i) = Cx(&0)}`
  MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ASM_ARITH_TAC]);;

let SUPERELL_TR_POLY_SHIFT = prove
 (`!m (c:num->complex) z.
        1 <= m /\ c m = Cx(&1)
        ==> vsum(0..m) (\k. c k * z pow k) - (z pow m - Cx(&1)) =
            vsum(0..m-1) (\k. (if k = 0 then c 0 + Cx(&1) else c k) *
                              z pow k)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VSUM_CLAUSES_RIGHT; LE_0; ARITH_RULE `1 <= m ==> 0 < m`] THEN
  REWRITE_TAC[MATCH_MP VSUM_CLAUSES_LEFT (SPEC `m - 1` LE_0)] THEN
  REWRITE_TAC[ARITH_RULE `0 + 1 = 1`; complex_pow] THEN
  SUBGOAL_THEN
   `vsum(1..m-1) (\k. (if k = 0 then c 0 + Cx(&1) else c k) * z pow k) =
    vsum(1..m-1) (\k. c k * z pow k)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    SIMP_TAC[ARITH_RULE `1 <= k ==> ~(k = 0)`];
    CONV_TAC COMPLEX_RING]);;

let SUPERELL_TR_UNITY_ROOT_FACTOR = prove
 (`!m w. 1 <= m /\ w pow m = Cx(&1) /\
         (!j k. j < m /\ k < m /\ w pow j = w pow k ==> j = k)
         ==> !z. cproduct(0..m-1) (\j. z - w pow j) = z pow m - Cx(&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `CARD(0..m-1) = m` ASSUME_TAC THENL
   [REWRITE_TAC[CARD_NUMSEG] THEN UNDISCH_TAC `1 <= m` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`0..m-1`; `\j. (w:complex) pow j`]
    CPRODUCT_LINEAR_POLYFUN) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->complex`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c"))) THEN
  SUBGOAL_THEN
   `!z. vsum(0..m) (\k. c k * z pow k) - (z pow m - Cx(&1)) =
        vsum(0..m-1) (\k. (if k = 0 then c 0 + Cx(&1) else c k) * z pow k)`
  (LABEL_TAC "diff") THENL
   [GEN_TAC THEN MATCH_MP_TAC SUPERELL_TR_POLY_SHIFT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "c" (fun th -> REWRITE_TAC[th]) THEN
  ONCE_REWRITE_TAC[GSYM COMPLEX_SUB_0] THEN
  USE_THEN "diff" (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC SUPERELL_TR_POLY_ROOTS_ZERO THEN
  EXISTS_TAC `IMAGE (\j. (w:complex) pow j) (0..m-1)` THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG];
    MP_TAC(ISPECL [`\j. (w:complex) pow j`; `0..m-1`] CARD_IMAGE_INJ) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  USE_THEN "diff" (fun th -> REWRITE_TAC[GSYM th]) THEN
  USE_THEN "c" (fun th -> REWRITE_TAC[GSYM th]) THEN
  SUBGOAL_THEN `cproduct(0..m-1) (\i. (w:complex) pow j - w pow i) = Cx(&0)`
  SUBST1_TAC THENL
   [SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN EXISTS_TAC `j:num` THEN
    ASM_REWRITE_TAC[IN_NUMSEG; COMPLEX_SUB_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_POW_POW] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  REWRITE_TAC[GSYM COMPLEX_POW_POW] THEN
  ASM_REWRITE_TAC[COMPLEX_POW_ONE] THEN CONV_TAC COMPLEX_RING);;

let UNITY_ROOT_PRODUCT_DIFF = prove
 (`!m (A:complex) B.
       1 <= m
       ==> cproduct(0..m-1)
             (\j. A - cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &m)) pow j * B) =
           A pow m - B pow m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(m - 1 + 1) - 0 = m` ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= m` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `w = cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &m))` THEN
  ASM_CASES_TAC `B = Cx(&0)` THENL
   [ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_SUB_RZERO;
                    CPRODUCT_CONST_NUMSEG; COMPLEX_POW_ZERO] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[COMPLEX_SUB_RZERO]];
    ALL_TAC] THEN
  MP_TAC(SPEC `m:num` UNITY_ROOT_CEXP) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`m:num`; `w:complex`] SUPERELL_TR_UNITY_ROOT_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `(A:complex) / B`) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `cproduct(0..m-1) (\j. (A:complex) - w pow j * B) =
    cproduct(0..m-1) (\j. B * (A / B - w pow j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CPRODUCT_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `~(B = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  SIMP_TAC[CPRODUCT_MUL; FINITE_NUMSEG; CPRODUCT_CONST_NUMSEG] THEN
  ASM_REWRITE_TAC[COMPLEX_POW_DIV] THEN
  SUBGOAL_THEN `~((B:complex) pow m = Cx(&0))` MP_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_POW_EQ_0]; CONV_TAC COMPLEX_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* The primitive m-th root of unity and m-th roots of algebraic integers.    *)
(* ------------------------------------------------------------------------- *)

let SUPERELL_TR_ZETA = prove
 (`!m. 3 <= m
       ==> cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &m)) pow m = Cx(&1) /\
           ~(cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &m)) = Cx(&0)) /\
           ~(cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &m)) = Cx(&1)) /\
           ~(cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &m)) pow 2 = Cx(&1)) /\
           algebraic_integer(cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &m)))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `m:num` UNITY_ROOT_CEXP) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `w = cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &m))` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[CEXP_NZ];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`1`; `0`]) THEN
    ASM_REWRITE_TAC[complex_pow; COMPLEX_POW_1] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`2`; `0`]) THEN
    ASM_REWRITE_TAC[complex_pow] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC ALGEBRAIC_INTEGER_ROOT_OF_UNITY THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let SUPERELL_TR_ROOT_EXISTS = prove
 (`!d m. 1 <= m /\ algebraic_integer d /\ ~(d = Cx(&0))
         ==> ?rho. rho pow m = d /\ algebraic_integer rho /\
                   ~(rho = Cx(&0))`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `cexp(clog d / Cx(&m))` THEN
  SUBGOAL_THEN `cexp(clog d / Cx(&m)) pow m = d` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CEXP_N] THEN
    SUBGOAL_THEN `~(Cx(&m) = Cx(&0))` ASSUME_TAC THENL
     [REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[COMPLEX_DIV_LMUL; CEXP_CLOG]];
    ASM_REWRITE_TAC[CEXP_NZ] THEN
    MATCH_MP_TAC ALGEBRAIC_INTEGER_POW_ROOT THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Elements of a number field with a fixed denominator D: a conjugate        *)
(* vector Z with D Z in the order Z[theta]; D^N times integer polynomials.   *)
(* ------------------------------------------------------------------------- *)

let SUPERELL_TR_PRIMITIVE = prove
 (`!s. FINITE s /\ (!z. z IN s ==> algebraic_number z)
       ==> ?n c r D. nf_data n c r /\ integer D /\ ~(D = &0) /\
                     !z. z IN s
                         ==> ?Z. nf_order n r (\k. Cx D * Z k) /\ Z 1 = z`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP NF_PRIMITIVE_ELEMENT) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `c:num->real`
   (X_CHOOSE_THEN `r:num->complex` (X_CHOOSE_THEN `D:real`
     STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC
   [`n:num`; `c:num->real`; `r:num->complex`; `D:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(Cx D = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CX_INJ]; ALL_TAC] THEN
  EXISTS_TAC
   `\k. vsum(0..n-1) (\i. Cx(p i) * (r:num->complex) k pow i) / Cx D` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[nf_order] THEN
    MAP_EVERY EXISTS_TAC [`n - 1`; `p:num->real`] THEN
    ASM_SIMP_TAC[COMPLEX_DIV_LMUL];
    REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `~(Cx D = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD]);;

let SUPERELL_TR_DPOW_POLY = prove
 (`!n r D (Z:num->complex) (q:num->real) N.
        integer D /\ nf_order n r (\k. Cx D * Z k) /\ (!i. integer(q i))
        ==> nf_order n r
             (\k. Cx D pow N * vsum(0..N) (\l. Cx(q l) * Z k pow l))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NF_ORDER_EQ THEN
  EXISTS_TAC `\k. vsum(0..N) (\l. Cx(q l * D pow (N - l)) *
                                  (Cx D * (Z:num->complex) k) pow l)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `r:num->complex`;
     `\l k. Cx((q:num->real) l * D pow (N - l)) *
            (Cx D * (Z:num->complex) k) pow l`; `0..N`] NF_ORDER_VSUM) THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`n:num`; `r:num->complex`;
      `\k:num. Cx((q:num->real) l * D pow (N - l))`;
      `\k. (Cx D * (Z:num->complex) k) pow l`] NF_ORDER_MUL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC NF_ORDER_CX THEN ASM_SIMP_TAC[INTEGER_CLOSED];
      MP_TAC(ISPECL [`n:num`; `r:num->complex`;
                     `\k. Cx D * (Z:num->complex) k`; `l:num`]
        NF_ORDER_POW) THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    REWRITE_TAC[CX_MUL; CX_POW; COMPLEX_POW_MUL] THEN
    SUBGOAL_THEN `Cx D pow N = Cx D pow (N - l) * Cx D pow l` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM COMPLEX_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      CONV_TAC COMPLEX_RING]]);;

let SUPERELL_TR_DPOW_MONO = prove
 (`!n r D N N' (a:num->complex).
        integer D /\ nf_order n r (\k. Cx D pow N * a k) /\ N <= N'
        ==> nf_order n r (\k. Cx D pow N' * a k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NF_ORDER_EQ THEN
  EXISTS_TAC `\k. Cx(D pow (N' - N)) * (Cx D pow N * (a:num->complex) k)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `r:num->complex`; `\k:num. Cx(D pow (N' - N))`;
                   `\k. Cx D pow N * (a:num->complex) k`] NF_ORDER_MUL) THEN
    ASM_SIMP_TAC[NF_ORDER_CX; INTEGER_POW];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[CX_POW; COMPLEX_MUL_ASSOC; GSYM COMPLEX_POW_ADD] THEN
    ASM_SIMP_TAC[SUB_ADD]]);;

let SUPERELL_TR_DPOW_MUL = prove
 (`!n r D N1 N2 (a:num->complex) b.
        nf_order n r (\k. Cx D pow N1 * a k) /\
        nf_order n r (\k. Cx D pow N2 * b k)
        ==> nf_order n r (\k. Cx D pow (N1 + N2) * (a k * b k))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NF_ORDER_EQ THEN
  EXISTS_TAC
   `\k. (Cx D pow N1 * (a:num->complex) k) * (Cx D pow N2 * b k)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `r:num->complex`;
                   `\k. Cx D pow N1 * (a:num->complex) k`;
                   `\k. Cx D pow N2 * (b:num->complex) k`] NF_ORDER_MUL) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_POW_ADD] THEN
    CONV_TAC COMPLEX_RING]);;

let SUPERELL_TR_DPOW_SUB = prove
 (`!n r D N (a:num->complex) b.
        nf_order n r (\k. Cx D pow N * a k) /\
        nf_order n r (\k. Cx D pow N * b k)
        ==> nf_order n r (\k. Cx D pow N * (a k - b k))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NF_ORDER_EQ THEN
  EXISTS_TAC `\k. Cx D pow N * (a:num->complex) k - Cx D pow N * b k` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `r:num->complex`;
                   `\k. Cx D pow N * (a:num->complex) k`;
                   `\k. Cx D pow N * (b:num->complex) k`] NF_ORDER_SUB) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_SUB_LDISTRIB]]);;

let SUPERELL_TR_DPOW_POW1 = prove
 (`!n r D (Z:num->complex) j.
        nf_order n r (\k. Cx D * Z k)
        ==> nf_order n r (\k. Cx D pow j * Z k pow j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `r:num->complex`; `\k. Cx D * (Z:num->complex) k`;
                 `j:num`] NF_ORDER_POW) THEN
  ASM_REWRITE_TAC[COMPLEX_POW_MUL]);;

let SUPERELL_TR_LAMBDA_ORDER = prove
 (`!n r D (Z1:num->complex) Z2 R1 R2 ZE (q1:num->real) q2 n1 n2 m j.
        integer D /\
        nf_order n r (\k. Cx D * Z1 k) /\ nf_order n r (\k. Cx D * Z2 k) /\
        nf_order n r (\k. Cx D * R1 k) /\ nf_order n r (\k. Cx D * R2 k) /\
        nf_order n r (\k. Cx D * ZE k) /\
        (!i. integer(q1 i)) /\ (!i. integer(q2 i)) /\ j < m
        ==> nf_order n r
             (\k. Cx D pow (n1 + n2 + m) *
                  (R2 k * vsum(0..n1-1) (\l. Cx(q1 l) * Z1 k pow l) -
                   ZE k pow j * R1 k *
                   vsum(0..n2-1) (\l. Cx(q2 l) * Z2 k pow l)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUPERELL_TR_DPOW_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUPERELL_TR_DPOW_MONO THEN EXISTS_TAC `1 + (n1 - 1)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUPERELL_TR_DPOW_MUL THEN
      ASM_REWRITE_TAC[COMPLEX_POW_1] THEN
      MATCH_MP_TAC SUPERELL_TR_DPOW_POLY THEN ASM_REWRITE_TAC[];
      ASM_ARITH_TAC];
    MATCH_MP_TAC SUPERELL_TR_DPOW_MONO THEN EXISTS_TAC `j + 1 + (n2 - 1)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUPERELL_TR_DPOW_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUPERELL_TR_DPOW_POW1 THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SUPERELL_TR_DPOW_MUL THEN
        ASM_REWRITE_TAC[COMPLEX_POW_1] THEN
        MATCH_MP_TAC SUPERELL_TR_DPOW_POLY THEN ASM_REWRITE_TAC[]];
      ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Norms of products; transfer of identities from the first conjugate.       *)
(* ------------------------------------------------------------------------- *)

let SUPERELL_TR_NF_NORM_CPRODUCT = prove
 (`!n (f:A->num->complex) s.
        FINITE s
        ==> cproduct(1..n) (\k. cproduct s (\j. f j k)) =
            cproduct s (\j. cproduct(1..n) (f j))`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES; CPRODUCT_1] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CPRODUCT_MUL; FINITE_NUMSEG] THEN
  REWRITE_TAC[ETA_AX]);;

let SUPERELL_TR_CPRODUCT_NORM_LE = prove
 (`!s (f:A->complex) a.
        FINITE s /\ a IN s /\ (!j. j IN s ==> &1 <= norm(f j))
        ==> norm(f a) <= norm(cproduct s f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->complex`; `s:A->bool`; `a:A`] CPRODUCT_DELETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&1 <= product (s DELETE (a:A)) (\j. norm((f:A->complex) j))`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM(ISPEC `s DELETE (a:A)` PRODUCT_ONE)] THEN
    MATCH_MP_TAC PRODUCT_LE THEN
    ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE; REAL_POS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_MUL; NORM_CPRODUCT; FINITE_DELETE] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]);;

let SUPERELL_TR_NORM_GE_1 = prove
 (`!n c r a. nf_data n c r /\ nf_order n r a /\ ~(cproduct(1..n) a = Cx(&0))
             ==> &1 <= norm(cproduct(1..n) a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`; `a:num->complex`]
    NF_NORM_INTEGER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~(cproduct(1..n) (a:num->complex) = Cx(&0))` THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CX; CX_INJ] THEN
  ASM_MESON_TAC[REAL_ABS_INTEGER_LEMMA]);;

let SUPERELL_TR_ORDER_TRANSFER = prove
 (`!n c r (a:num->complex) b.
        nf_data n c r /\ nf_order n r a /\ nf_order n r b /\ a 1 = b 1
        ==> !k. k IN 1..n ==> a k = b k`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM COMPLEX_SUB_0] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                 `\k. (a:num->complex) k - b k`; `1`; `k:num`]
    NF_ORDER_ZERO) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[NF_ORDER_SUB; COMPLEX_SUB_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The norm step: order elements whose product (at the first conjugate) is a *)
(* fixed non-zero order element G have non-zero norms of size at most that   *)
(* of the norm of G.                                                         *)
(* ------------------------------------------------------------------------- *)

let NF_ORDER_FACTOR_NORMS = prove
 (`!n c r (f:A->num->complex) s G.
     nf_data n c r /\ FINITE s /\ (!j. j IN s ==> nf_order n r (f j)) /\
     nf_order n r G /\ ~(G 1 = Cx(&0)) /\ cproduct s (\j. f j 1) = G 1
     ==> !j. j IN s
             ==> ~(cproduct(1..n) (f j) = Cx(&0)) /\
                 norm(cproduct(1..n) (f j)) <= norm(cproduct(1..n) G)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  SUBGOAL_THEN
   `!k. k IN 1..n ==> cproduct s (\j. (f:A->num->complex) j k) = G k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUPERELL_TR_ORDER_TRANSFER THEN
    MAP_EVERY EXISTS_TAC [`c:num->real`; `r:num->complex`] THEN
    ASM_SIMP_TAC[NF_ORDER_CPRODUCT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cproduct(1..n) (G:num->complex) =
    cproduct s (\j. cproduct(1..n) ((f:A->num->complex) j))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM SUPERELL_TR_NF_NORM_CPRODUCT] THEN
    MATCH_MP_TAC CPRODUCT_EQ THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(cproduct(1..n) (G:num->complex) = Cx(&0))` ASSUME_TAC THENL
   [SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN
    ASM_MESON_TAC[NF_ORDER_ZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j IN s ==> ~(cproduct(1..n) ((f:A->num->complex) j) = Cx(&0))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `~(cproduct(1..n) (G:num->complex) = Cx(&0))` THEN
    ASM_SIMP_TAC[CPRODUCT_EQ_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `j:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`s:A->bool`; `\j. cproduct(1..n) ((f:A->num->complex) j)`;
                 `j:A`] SUPERELL_TR_CPRODUCT_NORM_LE) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[SUPERELL_TR_NORM_GE_1]);;

(* ------------------------------------------------------------------------- *)
(* The linear factors lambda_j = rho2 xi1 - zeta^j rho1 xi2 (scaled by D^M)  *)
(* have bounded non-zero norms: their product is D^(Mm) d1 d2 (z2 - z1).     *)
(* ------------------------------------------------------------------------- *)

let SUPERELL_TR_LAMBDA_NORMS = prove
 (`!n c r D m z1 z2 rho1 rho2 (Z1:num->complex) Z2 R1 R2 ZE n1 n2 x
    (q1:num->real) q2 (lam:num->num->complex) (G:num->complex).
     nf_data n c r /\ integer D /\ ~(D = &0) /\ 3 <= m /\
     ~(z1 = z2) /\ ~(rho1 = Cx(&0)) /\ ~(rho2 = Cx(&0)) /\
     nf_order n r (\k. Cx D * Z1 k) /\ nf_order n r (\k. Cx D * Z2 k) /\
     nf_order n r (\k. Cx D * R1 k) /\ nf_order n r (\k. Cx D * R2 k) /\
     nf_order n r (\k. Cx D * ZE k) /\
     Z1 1 = z1 /\ Z2 1 = z2 /\ R1 1 = rho1 /\ R2 1 = rho2 /\
     ZE 1 = cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &m)) /\
     (!i. integer(q1 i)) /\ (!i. integer(q2 i)) /\
     rho1 pow m * (x - z1) = vsum(0..n1-1) (\i. Cx(q1 i) * z1 pow i) pow m /\
     rho2 pow m * (x - z2) = vsum(0..n2-1) (\i. Cx(q2 i) * z2 pow i) pow m
     ==> (!j k. lam j k =
                Cx D pow (n1 + n2 + m) *
                (R2 k * vsum(0..n1-1) (\l. Cx(q1 l) * Z1 k pow l) -
                 ZE k pow j * R1 k *
                 vsum(0..n2-1) (\l. Cx(q2 l) * Z2 k pow l))) /\
         (!k. G k = Cx D pow ((n1 + n2 + m) * m) * R1 k pow m * R2 k pow m *
                    (Z2 k - Z1 k))
         ==> !j. j < m
                 ==> nf_order n r (lam j) /\
                     ~(cproduct(1..n) (lam j) = Cx(&0)) /\
                     norm(cproduct(1..n) (lam j)) <= norm(cproduct(1..n) G)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lam") (LABEL_TAC "G")) THEN
  SUBGOAL_THEN `!j. j < m ==> nf_order n r ((lam:num->num->complex) j)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC NF_ORDER_EQ THEN
    EXISTS_TAC
     `\k. Cx D pow (n1 + n2 + m) *
          (R2 k * vsum(0..n1-1) (\l. Cx(q1 l) * Z1 k pow l) -
           ZE k pow j * R1 k *
           vsum(0..n2-1) (\l. Cx(q2 l) * (Z2:num->complex) k pow l))` THEN
    USE_THEN "lam" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SUPERELL_TR_LAMBDA_ORDER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `nf_order n r (G:num->complex)` ASSUME_TAC THENL
   [MATCH_MP_TAC NF_ORDER_EQ THEN
    EXISTS_TAC `\k. Cx D pow ((n1 + n2 + m) * m) * R1 k pow m * R2 k pow m *
                    ((Z2:num->complex) k - Z1 k)` THEN
    USE_THEN "G" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SUPERELL_TR_DPOW_MONO THEN EXISTS_TAC `m + m + 1` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUPERELL_TR_DPOW_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUPERELL_TR_DPOW_POW1 THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC SUPERELL_TR_DPOW_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUPERELL_TR_DPOW_POW1 THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC SUPERELL_TR_DPOW_SUB THEN ASM_REWRITE_TAC[COMPLEX_POW_1];
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `m * m` THEN CONJ_TAC THENL
       [SUBGOAL_THEN `3 * m <= m * m` MP_TAC THENL
         [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ASM_ARITH_TAC];
        REWRITE_TAC[LE_MULT_RCANCEL] THEN ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. (lam:num->num->complex) j 1 =
        Cx D pow (n1 + n2 + m) *
        (rho2 * vsum(0..n1-1) (\l. Cx(q1 l) * z1 pow l) -
         cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &m)) pow j * rho1 *
         vsum(0..n2-1) (\l. Cx(q2 l) * z2 pow l))`
  ASSUME_TAC THENL
   [USE_THEN "lam" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(G:num->complex) 1 =
    Cx D pow ((n1 + n2 + m) * m) * rho1 pow m * rho2 pow m * (z2 - z1)`
  ASSUME_TAC THENL
   [USE_THEN "G" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "lam" (K ALL_TAC) THEN REMOVE_THEN "G" (K ALL_TAC) THEN
  SUBGOAL_THEN `~((G:num->complex) 1 = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; CX_INJ; COMPLEX_SUB_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                 `lam:num->num->complex`; `0..m-1`; `G:num->complex`]
    NF_ORDER_FACTOR_NORMS) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[CPRODUCT_MUL; FINITE_NUMSEG; CPRODUCT_CONST_NUMSEG] THEN
    ASM_SIMP_TAC[UNITY_ROOT_PRODUCT_DIFF; ARITH_RULE `3 <= m ==> 1 <= m`] THEN
    SUBGOAL_THEN `(m - 1 + 1) - 0 = m` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_POW_POW; COMPLEX_POW_MUL] THEN
    UNDISCH_TAC
     `(rho1:complex) pow m * ((x:complex) - z1) =
      vsum(0..n1-1) (\i. Cx(q1 i) * z1 pow i) pow m` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    UNDISCH_TAC
     `(rho2:complex) pow m * ((x:complex) - z2) =
      vsum(0..n2-1) (\i. Cx(q2 i) * z2 pow i) pow m` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    CONV_TAC COMPLEX_RING;
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `j <= m - 1` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The Siegel identity and the unit equation step.                           *)
(* ------------------------------------------------------------------------- *)

let SUPERELL_TR_SIEGEL_COEFFS = prove
 (`!n r D (ZE:num->complex).
        integer D /\ nf_order n r (\k. Cx D * ZE k)
        ==> nf_order n r (\k. Cx D * (Cx D * ZE k) - (Cx D * ZE k) pow 2) /\
            nf_order n r (\k. (Cx D * ZE k) pow 2 - Cx D * Cx D) /\
            nf_order n r (\k. Cx D * Cx D - Cx D * (Cx D * ZE k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `nf_order n r (\k:num. Cx D)` ASSUME_TAC THENL
   [MATCH_MP_TAC NF_ORDER_CX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `nf_order n r (\k. (Cx D * (ZE:num->complex) k) pow 2)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `r:num->complex`; `\k. Cx D * (ZE:num->complex) k`;
                   `2`] NF_ORDER_POW) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `nf_order n r (\k. Cx D * (Cx D * (ZE:num->complex) k))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `r:num->complex`; `\k:num. Cx D`;
                   `\k. Cx D * (ZE:num->complex) k`] NF_ORDER_MUL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `nf_order n r (\k:num. Cx D * Cx D)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `r:num->complex`; `\k:num. Cx D`;
                   `\k:num. Cx D`] NF_ORDER_MUL) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC NF_ORDER_SUB THEN ASM_REWRITE_TAC[]);;

let SUPERELL_TR_SIEGEL_NONZERO = prove
 (`!D zeta. ~(D = &0) /\ ~(zeta = Cx(&0)) /\ ~(zeta = Cx(&1)) /\
            ~(zeta pow 2 = Cx(&1))
            ==> ~(Cx D * (Cx D * zeta) - (Cx D * zeta) pow 2 = Cx(&0)) /\
                ~((Cx D * zeta) pow 2 - Cx D * Cx D = Cx(&0)) /\
                ~(Cx D * Cx D - Cx D * (Cx D * zeta) = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_RING
   `Cx D * (Cx D * zeta) - (Cx D * zeta) pow 2 =
    (Cx D * Cx D) * zeta * (Cx(&1) - zeta)`;
   COMPLEX_RING
   `(Cx D * zeta) pow 2 - Cx D * Cx D = (Cx D * Cx D) * (zeta pow 2 - Cx(&1))`;
   COMPLEX_RING
   `Cx D * Cx D - Cx D * (Cx D * zeta) = (Cx D * Cx D) * (Cx(&1) - zeta)`] THEN
  ASM_REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ; COMPLEX_SUB_0]);;

let SUPERELL_TR_UNIT_STEP = prove
 (`!n c r (A:(num->complex)->bool) cc0 cc1 cc2.
        nf_data n c r /\
        (!b. b IN A ==> nf_order n r b /\ ~(cproduct(1..n) b = Cx(&0))) /\
        nf_order n r cc0 /\ nf_order n r cc1 /\ nf_order n r cc2 /\
        ~(cc0 1 = Cx(&0)) /\ ~(cc1 1 = Cx(&0)) /\ ~(cc2 1 = Cx(&0))
        ==> ?UU. !b0 b1 b2.
                   b0 IN A /\ b1 IN A /\ b2 IN A
                   ==> FINITE(UU b0 b1 b2) /\
                       !u v. nf_unit n r u /\ nf_unit n r v /\
                             (!k. k IN 1..n
                                  ==> (cc0 k * b0 k) * u k +
                                      (cc1 k * b1 k) * v k =
                                      --(cc2 k * b2 k))
                             ==> u 1 IN UU b0 b1 b2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  SUBGOAL_THEN
   `!b0 b1 b2. b0 IN A /\ b1 IN A /\ b2 IN A
               ==> ?U. FINITE U /\
                       !u v. nf_unit n r u /\ nf_unit n r v /\
                             (!k. k IN 1..n
                                  ==> ((cc0:num->complex) k * b0 k) * u k +
                                      ((cc1:num->complex) k * b1 k) * v k =
                                      --((cc2:num->complex) k * b2 k))
                             ==> u 1 IN U`
  (ACCEPT_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `nf_order n r (b0:num->complex) /\ nf_order n r (b1:num->complex) /\
    nf_order n r (b2:num->complex) /\ ~(b0 1 = Cx(&0)) /\
    ~(b1 1 = Cx(&0)) /\ ~(b2 1 = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NF_UNIT_NORM_NONZERO]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                 `\k. (cc0:num->complex) k * b0 k`;
                 `\k. (cc1:num->complex) k * b1 k`;
                 `\k. --((cc2:num->complex) k * b2 k)`] NF_UNIT_EQUATION) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC NF_ORDER_MUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC NF_ORDER_MUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC NF_ORDER_NEG THEN MATCH_MP_TAC NF_ORDER_MUL THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[COMPLEX_ENTIRE];
    ASM_REWRITE_TAC[COMPLEX_ENTIRE];
    ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_NEG_EQ_0]]);;

(* ------------------------------------------------------------------------- *)
(* Field identities: recovering x from the ratio lambda_0 / lambda_2.        *)
(* ------------------------------------------------------------------------- *)

let SUPERELL_TR_MOEBIUS = prove
 (`!A B w:complex.
        ~(B = Cx(&0)) /\ ~(A - w * B = Cx(&0)) /\ ~(w = Cx(&1))
        ==> (Cx(&1) - (A - B) / (A - w * B) * w) /
            (Cx(&1) - (A - B) / (A - w * B)) = A / B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(Cx(&1) - w = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_SUB_0]; ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx(&1) - (A - B) / (A - w * B) = Cx(&0))` MP_TAC THENL
   [SUBGOAL_THEN `Cx(&1) - (A - B) / (A - w * B) =
                  B * (Cx(&1) - w) / (A - w * B)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `~((A:complex) - w * B = Cx(&0))` THEN
      CONV_TAC COMPLEX_FIELD;
      ASM_REWRITE_TAC[complex_div; COMPLEX_ENTIRE; COMPLEX_INV_EQ_0]];
    ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD);;

let SUPERELL_TR_MOEBIUS2 = prove
 (`!x z1 z2:complex.
        ~(x = z2) /\ ~(z1 = z2)
        ==> x = (z1 - (x - z1) / (x - z2) * z2) /
                (Cx(&1) - (x - z1) / (x - z2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(Cx(&1) - (x - z1) / (x - z2) = Cx(&0))` MP_TAC THENL
   [SUBGOAL_THEN `Cx(&1) - (x - z1) / (x - z2) = (z1 - z2) / (x - z2)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `~(x:complex = z2)` THEN CONV_TAC COMPLEX_FIELD;
      ASM_REWRITE_TAC[complex_div; COMPLEX_ENTIRE; COMPLEX_INV_EQ_0;
                      COMPLEX_SUB_0]];
    ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD);;

let SUPERELL_TR_RECOVER = prove
 (`!m z1 z2 rho1 rho2 xi1 xi2 x w t:complex.
        1 <= m /\ ~(z1 = z2) /\ ~(rho1 = Cx(&0)) /\ ~(rho2 = Cx(&0)) /\
        ~(w = Cx(&1)) /\
        rho1 pow m * (x - z1) = xi1 pow m /\
        rho2 pow m * (x - z2) = xi2 pow m /\
        ~(rho2 * xi1 - w * rho1 * xi2 = Cx(&0)) /\ ~(x = z2) /\
        t = (rho2 * xi1 - rho1 * xi2) / (rho2 * xi1 - w * rho1 * xi2)
        ==> x = (z1 - ((Cx(&1) - t * w) / (Cx(&1) - t)) pow m * z2) /
                (Cx(&1) - ((Cx(&1) - t * w) / (Cx(&1) - t)) pow m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(xi2 = Cx(&0))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(rho2:complex) pow m * ((x:complex) - z2) = xi2 pow m` THEN
    ASM_REWRITE_TAC[COMPLEX_POW_ZERO; COMPLEX_ENTIRE; COMPLEX_POW_EQ_0;
                    COMPLEX_SUB_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((rho1:complex) * xi2 = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_ENTIRE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Cx(&1) - t * w) / (Cx(&1) - t) = (rho2 * xi1) / (rho1 * xi2)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUPERELL_TR_MOEBIUS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((rho2 * xi1) / (rho1 * xi2)) pow m = ((x:complex) - z1) / (x - z2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_POW_DIV; COMPLEX_POW_MUL] THEN
    UNDISCH_TAC `(rho1:complex) pow m * ((x:complex) - z1) = xi1 pow m` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    UNDISCH_TAC `(rho2:complex) pow m * ((x:complex) - z2) = xi2 pow m` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    SUBGOAL_THEN `~((rho1:complex) pow m = Cx(&0)) /\
                  ~((rho2:complex) pow m = Cx(&0)) /\
                  ~((x:complex) - z2 = Cx(&0))`
    MP_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_POW_EQ_0; COMPLEX_SUB_0];
      CONV_TAC COMPLEX_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC SUPERELL_TR_MOEBIUS2 THEN ASM_REWRITE_TAC[]);;

let SUPERELL_TR_FINITE_TRIPLE = prove
 (`!(A:B->bool) (U:B->B->B->C->bool) (f:B->B->B->C->D).
        FINITE A /\ (!a b c. a IN A /\ b IN A /\ c IN A ==> FINITE(U a b c))
        ==> FINITE {f a b c w | a,b,c,w |
                                a IN A /\ b IN A /\ c IN A /\ w IN U a b c}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `UNIONS (IMAGE (\p. IMAGE ((f:B->B->B->C->D) (FST p) (FST(SND p))
                                (SND(SND p)))
                             ((U:B->B->B->C->bool) (FST p) (FST(SND p))
                                (SND(SND p))))
                  ((A:B->bool) CROSS A CROSS A))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[FINITE_CROSS];
      REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE;
                EXISTS_PAIR_THM; IN_CROSS; IN_IMAGE] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The Siegel step: for fixed non-zero order elements cc0, cc1, cc2, order   *)
(* elements l0, l1, l2 of bounded non-zero norm with cc0 l0 + cc1 l1 + cc2   *)
(* l2 = 0 at all conjugates have l0 1 / l2 1 in a fixed finite set (bounded  *)
(* norms: NF_BOUNDED_NORM_FINITE; the unit equation: SUPERELL_TR_UNIT_STEP). *)
(* ------------------------------------------------------------------------- *)

let NF_SIEGEL_RATIO_FINITE = prove
 (`!n c r (cc0:num->complex) cc1 cc2 B.
     nf_data n c r /\
     nf_order n r cc0 /\ nf_order n r cc1 /\ nf_order n r cc2 /\
     ~(cc0 1 = Cx(&0)) /\ ~(cc1 1 = Cx(&0)) /\ ~(cc2 1 = Cx(&0))
     ==> ?U. FINITE U /\
             !l0 l1 l2.
               nf_order n r l0 /\ nf_order n r l1 /\ nf_order n r l2 /\
               ~(cproduct(1..n) l0 = Cx(&0)) /\
               ~(cproduct(1..n) l1 = Cx(&0)) /\
               ~(cproduct(1..n) l2 = Cx(&0)) /\
               norm(cproduct(1..n) l0) <= B /\
               norm(cproduct(1..n) l1) <= B /\
               norm(cproduct(1..n) l2) <= B /\
               (!k. k IN 1..n
                    ==> cc0 k * l0 k + cc1 k * l1 k + cc2 k * l2 k = Cx(&0))
               ==> l0 1 / l2 1 IN U`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`; `B:real`]
    NF_BOUNDED_NORM_FINITE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:(num->complex)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Abd")))) THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
     `A:(num->complex)->bool`; `cc0:num->complex`; `cc1:num->complex`;
     `cc2:num->complex`] SUPERELL_TR_UNIT_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN
    `UU:(num->complex)->(num->complex)->(num->complex)->complex->bool`
    (LABEL_TAC "UU")) THEN
  EXISTS_TAC
   `{(b0:num->complex) 1 / b2 1 * (w:complex) | b0,b1,b2,w |
     b0 IN A /\ b1 IN A /\ b2 IN A /\
     w IN (UU:(num->complex)->(num->complex)->(num->complex)->
              complex->bool) b0 b1 b2}` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`A:(num->complex)->bool`;
      `UU:(num->complex)->(num->complex)->(num->complex)->complex->bool`;
      `\(b0:num->complex) (b1:num->complex) (b2:num->complex) (w:complex).
         b0 1 / b2 1 * w`]
     SUPERELL_TR_FINITE_TRIPLE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "UU" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`l0:num->complex`; `l1:num->complex`;
                       `l2:num->complex`] THEN
  STRIP_TAC THEN
  MAP_EVERY (fun (l,b,u,lab) ->
    USE_THEN "Abd" (MP_TAC o SPEC l) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN b (X_CHOOSE_THEN u
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC lab))))))
   [`l0:num->complex`,`b0:num->complex`,`u0:num->complex`,"d0";
    `l1:num->complex`,`b1:num->complex`,`u1:num->complex`,"d1";
    `l2:num->complex`,`b2:num->complex`,`u2:num->complex`,"d2"] THEN
  SUBGOAL_THEN `(u0:num->complex) 1 / (u2:num->complex) 1 IN
                UU (b0:num->complex) (b1:num->complex) (b2:num->complex)`
  ASSUME_TAC THENL
   [USE_THEN "UU" (MP_TAC o SPECL [`b0:num->complex`; `b1:num->complex`;
                                   `b2:num->complex`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`\k. (u0:num->complex) k / u2 k`;
                               `\k. (u1:num->complex) k / u2 k`] o
               CONJUNCT2) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[NF_UNIT_DIV] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((u2:num->complex) k = Cx(&0))` MP_TAC THENL
     [ASM_MESON_TAC[NF_UNIT_NONZERO]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      free_in `cc2:num->complex` (concl th) &&
      free_in `l2:num->complex` (concl th))) THEN
    MAP_EVERY (fun l -> USE_THEN l (fun th ->
      REWRITE_TAC[MP (SPEC `k:num` th) (ASSUME `k IN 1..n`)]))
     ["d0"; "d1"; "d2"] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`b0:num->complex`; `b1:num->complex`;
                        `b2:num->complex`;
                        `(u0:num->complex) 1 / (u2:num->complex) 1`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((b2:num->complex) 1 = Cx(&0)) /\
                ~((u2:num->complex) 1 = Cx(&0))` MP_TAC THENL
   [ASM_MESON_TAC[NF_UNIT_NORM_NONZERO; NF_UNIT_NONZERO]; ALL_TAC] THEN
  MAP_EVERY (fun l -> USE_THEN l (fun th ->
      REWRITE_TAC[MP (SPEC `1` th) (ASSUME `1 IN 1..n`)]))
     ["d0"; "d2"] THEN
  CONV_TAC COMPLEX_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The core: for fixed field data (conjugate vectors of z1, z2, rho1, rho2   *)
(* and zeta in one number field), the set of x is finite.                    *)
(* ------------------------------------------------------------------------- *)

let SUPERELL_TR_CORE = prove
 (`!n c r D m z1 z2 rho1 rho2 (Z1:num->complex) Z2 R1 R2 ZE n1 n2.
     nf_data n c r /\ integer D /\ ~(D = &0) /\ 3 <= m /\
     ~(z1 = z2) /\ ~(rho1 = Cx(&0)) /\ ~(rho2 = Cx(&0)) /\
     nf_order n r (\k. Cx D * Z1 k) /\ nf_order n r (\k. Cx D * Z2 k) /\
     nf_order n r (\k. Cx D * R1 k) /\ nf_order n r (\k. Cx D * R2 k) /\
     nf_order n r (\k. Cx D * ZE k) /\
     Z1 1 = z1 /\ Z2 1 = z2 /\ R1 1 = rho1 /\ R2 1 = rho2 /\
     ZE 1 = cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &m))
     ==> FINITE {x | ?q1 q2. (!i. integer(q1 i)) /\ (!i. integer(q2 i)) /\
                     rho1 pow m * (x - z1) =
                     vsum(0..n1-1) (\i. Cx(q1 i) * z1 pow i) pow m /\
                     rho2 pow m * (x - z2) =
                     vsum(0..n2-1) (\i. Cx(q2 i) * z2 pow i) pow m}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `m:num` SUPERELL_TR_ZETA) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `zeta = cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &m))` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  ABBREV_TAC
   `G = \k. Cx D pow ((n1 + n2 + m) * m) * R1 k pow m * R2 k pow m *
            ((Z2:num->complex) k - Z1 k)` THEN
  MP_TAC(ISPECL [`n:num`; `r:num->complex`; `D:real`; `ZE:num->complex`]
    SUPERELL_TR_SIEGEL_COEFFS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`D:real`; `zeta:complex`] SUPERELL_TR_SIEGEL_NONZERO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
     `\k. Cx D * (Cx D * (ZE:num->complex) k) - (Cx D * ZE k) pow 2`;
     `\k. (Cx D * (ZE:num->complex) k) pow 2 - Cx D * Cx D`;
     `\k. Cx D * Cx D - Cx D * (Cx D * (ZE:num->complex) k)`;
     `norm(cproduct(1..n) (G:num->complex))`] NF_SIEGEL_RATIO_FINITE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `TT:complex->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TT"))) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `(z2:complex) INSERT
    IMAGE (\t. (z1 - ((Cx(&1) - t * zeta pow 2) / (Cx(&1) - t)) pow m * z2) /
               (Cx(&1) - ((Cx(&1) - t * zeta pow 2) / (Cx(&1) - t)) pow m))
          (TT:complex->bool)` THEN
  ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; IN_IMAGE] THEN
  X_GEN_TAC `x:complex` THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:num->real` (X_CHOOSE_THEN `q2:num->real`
    STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `x:complex = z2` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `xi1 = vsum(0..n1-1) (\i. Cx(q1 i) * z1 pow i)` THEN
  ABBREV_TAC `xi2 = vsum(0..n2-1) (\i. Cx(q2 i) * z2 pow i)` THEN
  ABBREV_TAC
   `lam = \j k. Cx D pow (n1 + n2 + m) *
                (R2 k * vsum(0..n1-1) (\l. Cx(q1 l) * Z1 k pow l) -
                 ZE k pow j * R1 k *
                 vsum(0..n2-1) (\l. Cx(q2 l) *
                                    (Z2:num->complex) k pow l))` THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`; `D:real`; `m:num`;
                 `z1:complex`; `z2:complex`; `rho1:complex`; `rho2:complex`;
                 `Z1:num->complex`; `Z2:num->complex`; `R1:num->complex`;
                 `R2:num->complex`; `ZE:num->complex`; `n1:num`; `n2:num`;
                 `x:complex`; `q1:num->real`; `q2:num->real`;
                 `lam:num->num->complex`; `G:num->complex`]
    SUPERELL_TR_LAMBDA_NORMS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "lam" THEN REWRITE_TAC[];
      EXPAND_TAC "G" THEN REWRITE_TAC[]];
    DISCH_TAC] THEN
  SUBGOAL_THEN `0 < m /\ 1 < m /\ 2 < m` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "TT" (MP_TAC o SPECL [`(lam:num->num->complex) 0`;
    `(lam:num->num->complex) 1`; `(lam:num->num->complex) 2`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    EXPAND_TAC "lam" THEN REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(lam:num->num->complex) 0 1 =
    Cx D pow (n1 + n2 + m) * (rho2 * xi1 - rho1 * xi2) /\
    (lam:num->num->complex) 2 1 =
    Cx D pow (n1 + n2 + m) * (rho2 * xi1 - zeta pow 2 * rho1 * xi2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN ASM_REWRITE_TAC[complex_pow; COMPLEX_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((lam:num->num->complex) 2 1 = Cx(&0))` MP_TAC THENL
   [MATCH_MP_TAC NF_UNIT_NORM_NONZERO THEN EXISTS_TAC `n:num` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; CX_INJ] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `((rho2:complex) * xi1 - rho1 * xi2) /
              (rho2 * xi1 - zeta pow 2 * rho1 * xi2)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:num`; `z1:complex`; `z2:complex`; `rho1:complex`;
                   `rho2:complex`; `xi1:complex`; `xi2:complex`; `x:complex`;
                   `(zeta:complex) pow 2`;
                   `((rho2:complex) * xi1 - rho1 * xi2) /
                    (rho2 * xi1 - zeta pow 2 * rho1 * xi2)`]
      SUPERELL_TR_RECOVER) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    SUBGOAL_THEN
     `((rho2:complex) * xi1 - rho1 * xi2) /
      (rho2 * xi1 - zeta pow 2 * rho1 * xi2) =
      (Cx D pow (n1 + n2 + m) * (rho2 * xi1 - rho1 * xi2)) /
      (Cx D pow (n1 + n2 + m) * (rho2 * xi1 - zeta pow 2 * rho1 * xi2))`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `~(Cx D pow (n1 + n2 + m) = Cx(&0))` MP_TAC THENL
       [ASM_REWRITE_TAC[COMPLEX_POW_EQ_0; CX_INJ]; CONV_TAC COMPLEX_FIELD];
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Fixed d1, d2: choose m-th roots rho_i and a common field                  *)
(* (SUPERELL_TR_PRIMITIVE).                                                  *)
(* ------------------------------------------------------------------------- *)

let SUPERELL_TR_TWO_ROOTS_FIXED = prove
 (`!m z1 z2 d1 d2 n1 n2.
     3 <= m /\ ~(z1 = z2) /\ algebraic_integer z1 /\ algebraic_integer z2 /\
     algebraic_integer d1 /\ ~(d1 = Cx(&0)) /\
     algebraic_integer d2 /\ ~(d2 = Cx(&0))
     ==> FINITE {x | ?q1 q2. (!i. integer(q1 i)) /\ (!i. integer(q2 i)) /\
                     d1 * (x - z1) =
                     vsum(0..n1-1) (\i. Cx(q1 i) * z1 pow i) pow m /\
                     d2 * (x - z2) =
                     vsum(0..n2-1) (\i. Cx(q2 i) * z2 pow i) pow m}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d1:complex`; `m:num`] SUPERELL_TR_ROOT_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho1:complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d2:complex`; `m:num`] SUPERELL_TR_ROOT_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho2:complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `m:num` SUPERELL_TR_ZETA) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `{z1:complex, z2, rho1, rho2,
                 cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &m))}`
    SUPERELL_TR_PRIMITIVE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT;
                NOT_IN_EMPTY] THEN
    ASM_SIMP_TAC[ALGEBRAIC_INTEGER_IMP_ALGEBRAIC_NUMBER];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `c:num->real`
   (X_CHOOSE_THEN `r:num->complex` (X_CHOOSE_THEN `D:real`
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Z")))))))) THEN
  USE_THEN "Z" (MP_TAC o SPEC `z1:complex`) THEN REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `Z1:num->complex` STRIP_ASSUME_TAC) THEN
  USE_THEN "Z" (MP_TAC o SPEC `z2:complex`) THEN REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `Z2:num->complex` STRIP_ASSUME_TAC) THEN
  USE_THEN "Z" (MP_TAC o SPEC `rho1:complex`) THEN REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `R1:num->complex` STRIP_ASSUME_TAC) THEN
  USE_THEN "Z" (MP_TAC o SPEC `rho2:complex`) THEN REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `R2:num->complex` STRIP_ASSUME_TAC) THEN
  USE_THEN "Z" (MP_TAC o SPEC `cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &m))`) THEN
  REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `ZE:num->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`; `D:real`; `m:num`;
                 `z1:complex`; `z2:complex`; `rho1:complex`; `rho2:complex`;
                 `Z1:num->complex`; `Z2:num->complex`; `R1:num->complex`;
                 `R2:num->complex`; `ZE:num->complex`; `n1:num`; `n2:num`]
    SUPERELL_TR_CORE) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The export: finite union over the finitely many (d1, d2).                 *)
(* ------------------------------------------------------------------------- *)

let SUPERELL_TWO_ROOTS = prove
 (`!m z1 z2 (DD1:complex->bool) DD2 n1 n2.
   3 <= m /\ ~(z1 = z2) /\ algebraic_integer z1 /\ algebraic_integer z2 /\
   FINITE DD1 /\ FINITE DD2 /\
   (!d. d IN DD1 ==> algebraic_integer d /\ ~(d = Cx(&0))) /\
   (!d. d IN DD2 ==> algebraic_integer d /\ ~(d = Cx(&0)))
   ==> FINITE {x | ?d1 d2 q1 q2.
                     d1 IN DD1 /\ d2 IN DD2 /\
                     (!i. integer(q1 i)) /\ (!i. integer(q2 i)) /\
                     d1 * (x - z1) =
                     vsum(0..n1-1) (\i. Cx(q1 i) * z1 pow i) pow m /\
                     d2 * (x - z2) =
                     vsum(0..n2-1) (\i. Cx(q2 i) * z2 pow i) pow m}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `UNIONS {{x | ?q1 q2. (!i. integer(q1 i)) /\ (!i. integer(q2 i)) /\
                         d1 * (x - z1) =
                         vsum(0..n1-1) (\i. Cx(q1 i) * z1 pow i) pow m /\
                         d2 * (x - z2) =
                         vsum(0..n2-1) (\i. Cx(q2 i) * z2 pow i) pow m} |
            d1,d2 | d1 IN DD1 /\ d2 IN (DD2:complex->bool)}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`d1:complex`; `d2:complex`] THEN STRIP_TAC THEN
      MATCH_MP_TAC SUPERELL_TR_TWO_ROOTS_FIXED THEN ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_GSPEC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]]);;
