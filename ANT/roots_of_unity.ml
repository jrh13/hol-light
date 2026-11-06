(* ========================================================================= *)
(* Roots of unity in number fields. If a number field k contains a root of   *)
(* unity of order m then phi(m) divides the degree [k:Q]                     *)
(* (NUMBER_FIELD_ROOT_OF_UNITY_PHI_DIVIDES: the minimal polynomial of a      *)
(* primitive m-th root of unity over Q is the m-th cyclotomic polynomial, of *)
(* degree phi(m)), so the roots of unity of k, a finite cyclic group, have   *)
(* an even order w with phi(w) dividing [k:Q]                                *)
(* (NUMBER_FIELD_ROOTS_OF_UNITY_CARD). A number field with a real embedding  *)
(* has only 1 and -1 as roots of unity (NUMBER_FIELD_REAL_ROOTS_OF_UNITY).   *)
(* The roots of unity are units of the ring of integers                      *)
(* (RING_OF_INTEGERS_ROOT_OF_UNITY_UNIT of ANT/numfield.ml), and they are    *)
(* all the units if and only if there is only one infinite place, that is k  *)
(* = Q or k is imaginary quadratic (NUMBER_FIELD_UNITS_EQ_ROOTS_OF_UNITY).   *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/fieldtheory.ml                       *)
(* (MINIMAL_POLYNOMIAL_DEG_DIVIDES_EXTENSION_DEGREE), ANT/numfield.ml        *)
(* (RING_OF_INTEGERS_ROOT_OF_UNITY_UNIT), ANT/cyclotomic_poly.ml             *)
(* (CYCLOTOMIC_POLY_DEG), ANT/cyclotomic_field.ml                            *)
(* (CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL), ANT/complex_embeddings.ml           *)
(* (COMPLEX_EMBEDDINGS_ROOT_OF_UNITY), ANT/infinite_places.ml                *)
(* (real_embeddings) and ANT/unit_theorem.ml                                 *)
(* (NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC, NUMBER_FIELD_UNITS_ROOTS_OF_UNITY).  *)
(* Also Multivariate/complex_ring.ml (complex_ring).                         *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "ANT/numfield.ml";;
needs "ANT/cyclotomic_poly.ml";;
needs "ANT/cyclotomic_field.ml";;
needs "ANT/complex_embeddings.ml";;
needs "ANT/infinite_places.ml";;
needs "ANT/unit_theorem.ml";;
needs "Multivariate/complex_ring.ml";;

(* ------------------------------------------------------------------------- *)
(* The degree of a root of unity, the number of roots of unity.              *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_ROOT_OF_UNITY_PHI_DIVIDES = prove
 (`!k (z:A) m.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = m /\ ~(m = 0)
        ==> phi m divides
            extension_degree (subfield_generated k {ring_0 k},k) I`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `m:num`]
    CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `z:A`] MINIMAL_POLYNOMIAL_DEG_DIVIDES_EXTENSION_DEGREE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[number_field]; ALL_TAC] THEN
  ASM_REWRITE_TAC[CYCLOTOMIC_POLY_DEG] THEN
  SUBGOAL_THEN
   `~(ring_1 (subfield_generated k {ring_0 k}) =
      ring_0 (subfield_generated k {ring_0 (k:A ring)}))`
  (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[SUBFIELD_GENERATED] THEN
  ASM_MESON_TAC[NUMBER_FIELD_IMP_FIELD; FIELD_NONTRIVIAL]);;

let NUMBER_FIELD_ROOTS_OF_UNITY_CARD = prove
 (`!k:A ring.
        number_field k
        ==> ?w. {x | x IN ring_carrier k /\
                     ?n. 1 <= n /\ ring_pow k x n = ring_1 k} HAS_SIZE w /\
                EVEN w /\
                phi w divides
                extension_degree (subfield_generated k {ring_0 k},k) I`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `z:A` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC)
    (LABEL_TAC "gen"))) o MATCH_MP NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC) THEN
  ABBREV_TAC `w = ring_order k (z:A)` THEN
  SUBGOAL_THEN `~(w = 0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `z:A`; `m:num`] RING_POW_EQ_1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DIVIDES_ZERO]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z:A = ring_0 k)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `ring_pow k (ring_0 k) m = ring_1 (k:A ring)` THEN
    ASM_SIMP_TAC[RING_POW_ZERO; ARITH_RULE `1 <= m ==> ~(m = 0)`] THEN
    ASM_MESON_TAC[FIELD_NONTRIVIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_regular k (z:A)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_REGULAR]; ALL_TAC] THEN
  EXISTS_TAC `w:num` THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `{x | x IN ring_carrier k /\ ?n. 1 <= n /\ ring_pow k x n = ring_1 k} =
      IMAGE (\j. ring_pow k (z:A) j) {j | j < w}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `x:A` THEN EQ_TAC THENL
       [STRIP_TAC THEN USE_THEN "gen" (MP_TAC o SPEC `x:A`) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
        EXISTS_TAC `j MOD w` THEN ASM_SIMP_TAC[MOD_LT_EQ] THEN
        ASM_SIMP_TAC[RING_POW_EQ] THEN REWRITE_TAC[CONG_RMOD; CONG_REFL];
        DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 SUBST1_TAC
          ASSUME_TAC)) THEN
        ASM_SIMP_TAC[RING_POW] THEN EXISTS_TAC `w:num` THEN
        ASM_SIMP_TAC[LE_1; GSYM RING_POW_MUL] THEN
        ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[RING_POW_MUL] THEN
        EXPAND_TAC "w" THEN ASM_SIMP_TAC[RING_POW_RING_ORDER; RING_POW_ONE]];
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
      REWRITE_TAC[HAS_SIZE_NUMSEG_LT; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[RING_POW_EQ] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `w:num` THEN
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `~(ring_neg k (ring_1 k) = ring_1 (k:A ring))` ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `2`] NUMBER_FIELD_RING_OF_NUM_EQ_0) THEN
      ASM_REWRITE_TAC[ARITH_EQ] THEN
      REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; RING_OF_NUM_ADD; RING_OF_NUM_1] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
      SIMP_TAC[RING_ADD_LNEG; RING_1];
      ALL_TAC] THEN
    USE_THEN "gen" (MP_TAC o SPEC `ring_neg k (ring_1 k):A`) THEN
    ANTS_TAC THENL
     [SIMP_TAC[RING_NEG; RING_1] THEN EXISTS_TAC `2` THEN
      SIMP_TAC[RING_POW_2; RING_MUL_LNEG; RING_MUL_RNEG; RING_NEG_NEG;
               RING_MUL_LID; RING_1; RING_NEG] THEN ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `j:num` (LABEL_TAC "j"))] THEN
    SUBGOAL_THEN `w divides j * 2` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `z:A`; `j * 2`] RING_POW_EQ_1) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[RING_POW_MUL] THEN USE_THEN "j" (SUBST1_TAC o SYM) THEN
      SIMP_TAC[RING_POW_2; RING_MUL_LNEG; RING_MUL_RNEG; RING_NEG_NEG;
               RING_MUL_LID; RING_1; RING_NEG];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM NOT_ODD] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:num) divides j` MP_TAC THENL
     [MATCH_MP_TAC COPRIME_DIVPROD THEN EXISTS_TAC `2` THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[COPRIME_2];
      ALL_TAC] THEN
    EXPAND_TAC "w" THEN ASM_SIMP_TAC[GSYM RING_POW_EQ_1] THEN
    USE_THEN "j" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC NUMBER_FIELD_ROOT_OF_UNITY_PHI_DIVIDES THEN
    EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Fields with a real embedding.                                             *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_REAL_ROOTS_OF_UNITY = prove
 (`!k:A ring.
        number_field k /\ ~(real_embeddings k = {})
        ==> {x | x IN ring_carrier k /\
                 ?n. 1 <= n /\ ring_pow k x n = ring_1 k} =
            {ring_1 k, ring_neg k (ring_1 k)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `g:A->complex` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[real_embeddings; IN_ELIM_THM]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "real")) THEN
  MP_TAC(ISPECL [`k:A ring`; `g:A->complex`]
    COMPLEX_EMBEDDINGS_MONOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[ring_monomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")) THEN
  SUBGOAL_THEN `(g:A->complex)(ring_1 k) = Cx(&1) /\
                g(ring_neg k (ring_1 k)) = Cx(-- &1)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
      RING_HOMOMORPHISM_1) THEN
    MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
      RING_HOMOMORPHISM_NEG) THEN
    ASM_SIMP_TAC[COMPLEX_RING_CLAUSES; RING_1; CX_NEG];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `g:A->complex`; `x:A`; `n:num`]
      COMPLEX_EMBEDDINGS_ROOT_OF_UNITY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "real" (MP_TAC o SPEC `x:A`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real` (LABEL_TAC "gx")) THEN
    USE_THEN "gx" SUBST1_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ARITH
     `abs (a:real) = &1 <=> a = &1 \/ a = -- &1`] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    USE_THEN "inj" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[RING_1; RING_NEG];
    STRIP_TAC THEN ASM_SIMP_TAC[RING_1; RING_NEG] THENL
     [EXISTS_TAC `1` THEN REWRITE_TAC[RING_POW_1; LE_REFL] THEN
      ASM_SIMP_TAC[RING_POW_1; RING_1];
      EXISTS_TAC `2` THEN
      ASM_SIMP_TAC[RING_POW_2; RING_MUL_LNEG; RING_MUL_RNEG; RING_NEG_NEG;
                   RING_MUL_LID; RING_1; RING_NEG] THEN
      ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Roots of unity as units.                                                  *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_UNITS_EQ_ROOTS_OF_UNITY = prove
 (`!k:A ring.
        number_field k
        ==> ({u | ring_unit (ring_of_integers k) u} =
             {x | x IN ring_carrier k /\
                  ?n. 1 <= n /\ ring_pow k x n = ring_1 k} <=>
             CARD(infinite_places k) = 1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP
    NUMBER_FIELD_UNITS_ROOTS_OF_UNITY th)]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:A`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    X_GEN_TAC `u:A` THEN EQ_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[RING_UNIT_IN_CARRIER; RING_OF_INTEGERS_SUBSET;
                      SUBSET];
        ASM_MESON_TAC[]];
      MESON_TAC[RING_OF_INTEGERS_ROOT_OF_UNITY_UNIT]]]);;
