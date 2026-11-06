(* ========================================================================= *)
(* The field of complex numbers is algebraically closed: the fundamental     *)
(* theorem of algebra (FTA of Multivariate/cauchy.ml) for complex_ring of    *)
(* Multivariate/complex_ring.ml.                                             *)
(* ========================================================================= *)

needs "Library/fieldtheory.ml";;
needs "Multivariate/cauchy.ml";;
needs "Multivariate/complex_ring.ml";;

let ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING = prove
 (`algebraically_closed_field complex_ring`,
  REWRITE_TAC[algebraically_closed_field; FIELD_COMPLEX_RING] THEN
  X_GEN_TAC `p:(1->num)->complex` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[POLY_EVAL_COMPLEX_RING; COMPLEX_RING_CLAUSES; IN_UNIV] THEN
  MATCH_MP_TAC FTA THEN DISJ2_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `poly_deg complex_ring (p:(1->num)->complex)`) THEN
  ASM_SIMP_TAC[IN_NUMSEG; LE_REFL; LE_1] THEN
  MP_TAC(ISPECL [`complex_ring`; `p:(1->num)->complex`] POLY_TOP_EQ_0) THEN
  ASM_REWRITE_TAC[RING_POLYNOMIAL; COMPLEX_RING_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[POLY_DEG_0]);;
