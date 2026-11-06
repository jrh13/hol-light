(* ========================================================================= *)
(* The complex numbers as a ring: complex_ring, a field of characteristic 0, *)
(* and its ring operations, sums, products, powers and polynomial            *)
(* evaluation in the complex notation; complex conjugation as a ring         *)
(* automorphism. Needs only the algebra of the complex numbers               *)
(* (Multivariate/complex_algebra.ml) and Library/ringtheory.ml.              *)
(* ========================================================================= *)

prioritize_real();;
needs "Library/ringtheory.ml";;
needs "Multivariate/complex_algebra.ml";;

prioritize_complex();;

let complex_ring = new_definition
 `complex_ring = ring((:complex),Cx(&0),Cx(&1),( -- ),( + ),( * ))`;;

let COMPLEX_RING_CLAUSES = prove
 (`ring_carrier complex_ring = (:complex) /\
   ring_0 complex_ring = Cx(&0) /\
   ring_1 complex_ring = Cx(&1) /\
   ring_neg complex_ring = ( -- ) /\
   ring_add complex_ring = ( + ) /\
   ring_mul complex_ring = ( * )`,
  PURE_REWRITE_TAC
   [GSYM PAIR_EQ; ring_carrier; ring_0; ring_1; ring_neg; ring_add; ring_mul;
    BETA_THM; PAIR] THEN
  PURE_REWRITE_TAC[complex_ring; GSYM(CONJUNCT2 ring_tybij)] THEN
  REWRITE_TAC[IN_UNIV] THEN CONV_TAC COMPLEX_RING);;

let FIELD_COMPLEX_RING = prove
 (`field complex_ring`,
  REWRITE_TAC[field; COMPLEX_RING_CLAUSES; IN_UNIV; CX_INJ] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN MESON_TAC[COMPLEX_MUL_RINV]);;

let INTEGRAL_DOMAIN_COMPLEX_RING = prove
 (`integral_domain complex_ring`,
  SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; FIELD_COMPLEX_RING]);;

let COMPLEX_RING_OF_NUM = prove
 (`ring_of_num complex_ring = \n. Cx(&n)`,
  REWRITE_TAC[FUN_EQ_THM] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ring_of_num; COMPLEX_RING_CLAUSES; GSYM REAL_OF_NUM_SUC;
                  CX_ADD]);;

let COMPLEX_RING_OF_INT = prove
 (`ring_of_int complex_ring = \n. Cx(real_of_int n)`,
  REWRITE_TAC[FUN_EQ_THM; RING_OF_INT_CASES; FORALL_INT_CASES] THEN
  REWRITE_TAC[int_neg_th; int_of_num_th; COMPLEX_RING_OF_NUM] THEN
  REWRITE_TAC[COMPLEX_RING_CLAUSES; CX_NEG]);;

let RING_CHAR_COMPLEX_RING = prove
 (`ring_char complex_ring = 0`,
  REWRITE_TAC[RING_CHAR_EQ_0; COMPLEX_RING_OF_NUM; COMPLEX_RING_CLAUSES;
              CX_INJ; REAL_OF_NUM_EQ]);;

let COMPLEX_RING_SUB = prove
 (`ring_sub complex_ring = ( - )`,
  REWRITE_TAC[FUN_EQ_THM; ring_sub; COMPLEX_RING_CLAUSES; complex_sub]);;

let COMPLEX_RING_INV = prove
 (`ring_inv complex_ring = inv`,
  REWRITE_TAC[FUN_EQ_THM; ring_inv; COMPLEX_RING_CLAUSES] THEN
  SIMP_TAC[FIELD_UNIT; FIELD_COMPLEX_RING; COMPLEX_RING_CLAUSES;
           IN_UNIV; COND_SWAP] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_INV_0] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN POP_ASSUM MP_TAC THEN
  CONV_TAC COMPLEX_FIELD);;

let COMPLEX_RING_DIV = prove
 (`ring_div complex_ring = ( / )`,
  REWRITE_TAC[FUN_EQ_THM; ring_div; COMPLEX_RING_INV; COMPLEX_RING_CLAUSES;
              complex_div]);;

let COMPLEX_RING_POW = prove
 (`ring_pow complex_ring = (pow)`,
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ring_pow; complex_pow; COMPLEX_RING_CLAUSES]);;

let COMPLEX_RING_SUM = prove
 (`!s (f:A->complex). FINITE s ==> ring_sum complex_ring s f = vsum s f`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[RING_SUM_CLAUSES; VSUM_CLAUSES; COMPLEX_RING_CLAUSES; IN_UNIV;
           COMPLEX_VEC_0]);;

let COMPLEX_RING_PRODUCT = prove
 (`!s (f:A->complex).
        FINITE s ==> ring_product complex_ring s f = cproduct s f`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[RING_PRODUCT_CLAUSES; CPRODUCT_CLAUSES; COMPLEX_RING_CLAUSES;
           IN_UNIV]);;

let POLY_EVAL_COMPLEX_RING = prove
 (`!p z. p IN ring_carrier(poly_ring complex_ring (:1))
         ==> poly_eval complex_ring p z =
             vsum(0..poly_deg complex_ring p) (\i. coeff i p * z pow i)`,
  SIMP_TAC[POLY_EVAL_EXPAND; COMPLEX_RING_CLAUSES; IN_UNIV;
           COMPLEX_RING_SUM; FINITE_NUMSEG; COMPLEX_RING_POW]);;

let RING_HOMOMORPHISM_CNJ = prove
 (`ring_homomorphism(complex_ring,complex_ring) cnj`,
  REWRITE_TAC[ring_homomorphism; COMPLEX_RING_CLAUSES; SUBSET_UNIV; IN_UNIV;
              CNJ_ADD; CNJ_MUL; CNJ_NEG; CNJ_CX]);;

let RING_AUTOMORPHISM_CNJ = prove
 (`ring_automorphism complex_ring cnj`,
  REWRITE_TAC[ring_automorphism; ring_isomorphism; ring_isomorphisms] THEN
  EXISTS_TAC `cnj` THEN
  REWRITE_TAC[RING_HOMOMORPHISM_CNJ; COMPLEX_RING_CLAUSES; IN_UNIV; CNJ_CNJ]);;
