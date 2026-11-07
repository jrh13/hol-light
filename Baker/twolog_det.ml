(* ========================================================================= *)
(* Two logarithms: determinants of n x n arrays indexed by 1..n.             *)
(*                                                                           *)
(* Purpose: the determinant lemmas used by the two-logarithm development,    *)
(* for the complex and real determinants ring_det complex_ring (1..n) f and  *)
(* ring_det real_ring (1..n) f of Library/ring_det.ml: the Leibniz formula   *)
(* with vsum / cproduct and sum / product (COMPLEX_RING_DET, REAL_RING_DET), *)
(* the algebraic lemmas of ring_det.ml in that form, and the analytic ones   *)
(* proved on the Leibniz formula.                                            *)
(*                                                                           *)
(* Main results: COMPLEX_RING_DET, REAL_RING_DET, CDET_CX, CDET_ROWS_CMUL,   *)
(* CDET_MULTILINEAR, CDET_NORM_LE_PERM (n! times a bound for all products    *)
(* along permutations), CDET_NORM_LE (n! times the product of the row        *)
(* bounds), CDET_HOLOMORPHIC, RDET_INTEGER_COLUMNS, CDET_DEPENDENT_ROWS,     *)
(* CDET_MINOR_SELECTION.                                                     *)
(*                                                                           *)
(* Uses: Library/ring_det.ml (ring_det, RING_DET_MULTILINEAR,                *)
(* RING_DET_DEPENDENT_ROWS, RING_DET_MINOR_SELECTION), Library/ringtheory.ml *)
(* (REAL_RING_SUM, REAL_RING_PRODUCT), and complex_ring of                   *)
(* Multivariate/complex_ring.ml with COMPLEX_RING_CLAUSES,                   *)
(* FIELD_COMPLEX_RING, INTEGRAL_DOMAIN_COMPLEX_RING and the bridges          *)
(* COMPLEX_RING_SUM, COMPLEX_RING_PRODUCT; Multivariate/canal.ml             *)
(* (HOLOMORPHIC_ON_VSUM, HOLOMORPHIC_ON_CPRODUCT).                           *)
(*                                                                           *)
(* Sections 9 and 10 need no Baker files beyond Baker/lemmas.ml (section 1); *)
(* Baker/make_twolog.ml and Baker/make_laurent.ml load them alone.           *)
(* ========================================================================= *)

needs "Library/ring_det.ml";;
needs "Multivariate/canal.ml";;
needs "Multivariate/complex_ring.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The Leibniz formula for complex and real determinants; the embedding of   *)
(* the real ring into the complex ring.                                      *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_RING_DET = prove
 (`!s (f:A->A->complex).
        FINITE s
        ==> ring_det complex_ring s f =
            vsum {p | p permutes s}
                 (\p. Cx(sign p) * cproduct s (\i. f i (p i)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_det] THEN
  ASM_SIMP_TAC[GSYM COMPLEX_RING_SUM; FINITE_PERMUTATIONS] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `p:A->A` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[GSYM COMPLEX_RING_PRODUCT] THEN
  REWRITE_TAC[ring_sign; sign; COMPLEX_RING_CLAUSES] THEN
  COND_CASES_TAC THEN REWRITE_TAC[CX_NEG]);;

let REAL_RING_DET = prove
 (`!s (f:A->A->real).
        ring_det real_ring s f =
        sum {p | p permutes s} (\p. sign p * product s (\i. f i (p i)))`,
  REWRITE_TAC[ring_det; ring_sign; sign; REAL_RING_CLAUSES; REAL_RING_SUM;
              REAL_RING_PRODUCT]);;

let TL_RING_HOMOMORPHISM_CX = prove
 (`ring_homomorphism(real_ring,complex_ring) Cx`,
  REWRITE_TAC[ring_homomorphism; REAL_RING_CLAUSES; COMPLEX_RING_CLAUSES;
              SUBSET_UNIV; IN_UNIV; CX_NEG; CX_ADD; CX_MUL]);;

(* ------------------------------------------------------------------------- *)
(* Algebraic lemmas, from ring_det.                                          *)
(* ------------------------------------------------------------------------- *)

let CDET_CX = prove
 (`!n f. ring_det complex_ring (1..n) (\i j. Cx(f i j)) =
         Cx(ring_det real_ring (1..n) f)`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC RING_DET_HOMOMORPHISM THEN
  REWRITE_TAC[TL_RING_HOMOMORPHISM_CX; FINITE_NUMSEG; REAL_RING_CLAUSES;
              IN_UNIV]);;

let CDET_ROWS_CMUL = prove
 (`!n (c:num->complex) (h:num->num->complex).
        ring_det complex_ring (1..n) (\i j. c i * h i j) =
        cproduct(1..n) c * ring_det complex_ring (1..n) h`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`complex_ring`; `1..n`; `c:num->complex`;
                 `h:num->num->complex`] RING_DET_ROWS_MUL) THEN
  REWRITE_TAC[FINITE_NUMSEG; COMPLEX_RING_CLAUSES; IN_UNIV] THEN
  SIMP_TAC[GSYM COMPLEX_RING_PRODUCT; FINITE_NUMSEG]);;

let CDET_MULTILINEAR = prove
 (`!n m (f:num->num->complex) (g:num->num->num->complex).
        (!i j. i IN 1..n /\ j IN 1..n ==> f i j = vsum (0..m) (\t. g i t j))
        ==> ring_det complex_ring (1..n) f =
            vsum (cartesian_product (1..n) (\i. 0..m))
                 (\mu. ring_det complex_ring (1..n) (\i j. g i (mu i) j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(cartesian_product (1..n) (\i:num. 0..m))`
  ASSUME_TAC THENL
   [SIMP_TAC[FINITE_CARTESIAN_PRODUCT_FINITE; FINITE_NUMSEG];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM COMPLEX_RING_SUM] THEN
  MATCH_MP_TAC RING_DET_MULTILINEAR THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; COMPLEX_RING_CLAUSES; IN_UNIV;
               COMPLEX_RING_SUM]);;

(* ------------------------------------------------------------------------- *)
(* Analytic lemmas (on the Leibniz formula).                                 *)
(* ------------------------------------------------------------------------- *)

let CDET_NORM_LE_PERM = prove
 (`!n (f:num->num->complex) B.
     (!p. p permutes 1..n ==> product(1..n) (\i. norm(f i (p i))) <= B)
     ==> norm(ring_det complex_ring (1..n) f) <= &(FACT n) * B`,
  REPEAT STRIP_TAC THEN SIMP_TAC[COMPLEX_RING_DET; FINITE_NUMSEG] THEN
  TRANS_TAC REAL_LE_TRANS `sum {p | p permutes 1..n} (\p:num->num. B)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN
    SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_SIGN_PERMUTATION;
                REAL_MUL_LID] THEN
    SIMP_TAC[NORM_CPRODUCT; FINITE_NUMSEG] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    SIMP_TAC[SUM_CONST; FINITE_PERMUTATIONS; FINITE_NUMSEG;
             CARD_PERMUTATIONS; CARD_NUMSEG_1; REAL_LE_REFL]]);;

let CDET_NORM_LE = prove
 (`!n (f:num->num->complex) M.
        (!i j. i IN 1..n /\ j IN 1..n ==> norm(f i j) <= M i)
        ==> norm(ring_det complex_ring (1..n) f) <=
            &(FACT n) * product(1..n) M`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CDET_NORM_LE_PERM THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN
  REWRITE_TAC[NORM_POS_LE] THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]);;

let CDET_HOLOMORPHIC = prove
 (`!n (f:complex->num->num->complex) s.
        (!i j. i IN 1..n /\ j IN 1..n ==> (\w. f w i j) holomorphic_on s)
        ==> (\w. ring_det complex_ring (1..n) (f w)) holomorphic_on s`,
  REPEAT STRIP_TAC THEN SIMP_TAC[COMPLEX_RING_DET; FINITE_NUMSEG] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_VSUM THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG; IN_ELIM_THM] THEN
  X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_CPRODUCT THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Integrality.                                                              *)
(* ------------------------------------------------------------------------- *)

let RDET_INTEGER_COLUMNS = prove
 (`!n (f:num->num->real) d.
        (!i j. i IN 1..n /\ j IN 1..n ==> integer(f i j * d j))
        ==> integer(ring_det real_ring (1..n) f * product(1..n) d)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`real_ring`; `1..n`; `d:num->real`; `f:num->num->real`]
    RING_DET_COLUMNS_MUL) THEN
  REWRITE_TAC[FINITE_NUMSEG; REAL_RING_CLAUSES; IN_UNIV; REAL_RING_PRODUCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_DET_CLOSED THEN
  ASM_SIMP_TAC[REAL_RING_CLAUSES; INTEGER_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* Linear dependence of rows; non-vanishing minors.                          *)
(* ------------------------------------------------------------------------- *)

let CDET_DEPENDENT_ROWS = prove
 (`!n (f:num->num->complex) c.
        (?i. i IN 1..n /\ ~(c i = Cx(&0))) /\
        (!j. j IN 1..n ==> vsum(1..n) (\i. c i * f i j) = Cx(&0))
        ==> ring_det complex_ring (1..n) f = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`complex_ring`; `1..n`; `f:num->num->complex`;
                 `c:num->complex`] RING_DET_DEPENDENT_ROWS) THEN
  REWRITE_TAC[INTEGRAL_DOMAIN_COMPLEX_RING; FINITE_NUMSEG; COMPLEX_RING_CLAUSES;
              IN_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_SIMP_TAC[COMPLEX_RING_SUM; FINITE_NUMSEG]]);;

let CDET_MINOR_SELECTION = prove
 (`!m (t:A->bool) (f:num->A->complex).
        FINITE t /\
        (!c. (!j. j IN t ==> vsum(1..m) (\i. c i * f i j) = Cx(&0))
             ==> (!i. i IN 1..m ==> c i = Cx(&0)))
        ==> ?g. (!j. j IN 1..m ==> g j IN t) /\
                (!j j'. j IN 1..m /\ j' IN 1..m /\ g j = g j' ==> j = j') /\
                ~(ring_det complex_ring (1..m) (\i j. f i (g j)) = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`complex_ring`; `1..m`; `t:A->bool`; `f:num->A->complex`]
    RING_DET_MINOR_SELECTION) THEN
  REWRITE_TAC[FIELD_COMPLEX_RING; FINITE_NUMSEG; COMPLEX_RING_CLAUSES;
              IN_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `c:num->complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[GSYM COMPLEX_RING_SUM; FINITE_NUMSEG]);;
