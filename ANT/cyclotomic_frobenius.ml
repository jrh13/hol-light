(* ========================================================================= *)
(* Decomposition and Frobenius elements in cyclotomic fields.                *)
(*                                                                           *)
(* In k = Q(z) with z of order n, a prime P of O_k over a prime p not        *)
(* dividing n is unramified: its inertia group is trivial                    *)
(* (CYCLOTOMIC_FIELD_INERTIA_GROUP), and its Frobenius element maps z to z^p *)
(* (CYCLOTOMIC_FIELD_FROBENIUS_ELEMENT). In a field of characteristic 0 the  *)
(* image of the prime subfield in O_k / P has p elements for a prime P over  *)
(* p (NUMBER_FIELD_RESIDUE_PRIME_FIELD_CARD).                                *)
(*                                                                           *)
(* Uses: ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml,       *)
(* ANT/decomposition.ml (frobenius_element, inertia_group),                  *)
(* ANT/nf_decomposition.ml and ANT/cyclotomic_galois.ml                      *)
(* (CYCLOTOMIC_FIELD_GALOIS_EXTENSION, CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ).    *)
(* ========================================================================= *)

needs "ANT/cyclotomic_galois.ml";;
needs "ANT/nf_decomposition.ml";;

let NUMBER_FIELD_RESIDUE_PRIME_FIELD_CARD = prove
 (`!(k:A ring) P p.
        field k /\ ring_char k = 0 /\ prime p /\
        ring_ideal (ring_of_integers k) P /\
        (!m. ring_of_int k m IN P <=> &p divides m)
        ==> CARD {ring_coset (ring_of_integers k) P (I a) | a |
                  a IN ring_carrier(subfield_generated k {ring_0 k}) /\
                  I a IN ring_carrier(ring_of_integers k)} = p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[I_THM] THEN
  SUBGOAL_THEN
   `!a. a IN ring_carrier(subfield_generated k {ring_0 k}) /\
        a IN ring_carrier(ring_of_integers k) <=>
        ?n. a = ring_of_int (k:A ring) n`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_PRIME_SUBFIELD) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `a:A`) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n n'. ring_coset (ring_of_integers k) P (ring_of_int k n) =
           ring_coset (ring_of_integers k) P (ring_of_int (k:A ring) n') <=>
           &p divides (n - n')`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_COSET_EQ o lhand o snd) THEN
    ASM_REWRITE_TAC[RING_OF_INT_IN_RING_OF_INTEGERS] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[RING_OF_INTEGERS; GSYM RING_OF_INT_SUB] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{ring_coset (ring_of_integers k) P a | a |
     a IN ring_carrier(subfield_generated k {ring_0 k}) /\
     a IN ring_carrier(ring_of_integers k)} =
    IMAGE (\i. ring_coset (ring_of_integers k) P
                (ring_of_int (k:A ring) (&i))) {i | i < p}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `X:A->bool` THEN ASM_REWRITE_TAC[] THEN EQ_TAC THENL
     [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `a:A` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:int`) ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `num_of_int(n rem &p)` THEN
      SUBGOAL_THEN `~(&p:int = &0)` ASSUME_TAC THENL
       [REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
      ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_REM_POS] THEN CONJ_TAC THENL
       [REWRITE_TAC[INT_REM_DIV] THEN CONV_TAC INTEGER_RULE;
        REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
        ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_REM_POS] THEN
        MATCH_MP_TAC INT_LT_REM THEN REWRITE_TAC[INT_OF_NUM_LT] THEN
        UNDISCH_TAC `prime p` THEN REWRITE_TAC[GSYM LT_NZ] THEN
        MESON_TAC[PRIME_IMP_NZ; LT_NZ]];
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `ring_of_int (k:A ring) (&i)` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [MESON_TAC[]; CONV_TAC INTEGER_RULE]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT; IN_ELIM_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN MATCH_MP_TAC INT_CONG_IMP_EQ THEN
  EXISTS_TAC `&p:int` THEN
  ASM_REWRITE_TAC[int_congruent; GSYM int_divides] THEN
  UNDISCH_TAC `i < p:num` THEN UNDISCH_TAC `j < p:num` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let CYCLOTOMIC_FIELD_INERTIA_GROUP = prove
 (`!(k:A ring) z n p P.
        number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
        subfield_generated k {z} = k /\
        prime p /\ ~(p divides n) /\
        maximal_ideal (ring_of_integers k) P /\ ring_of_num k p IN P
        ==> group_carrier(inertia_group(subfield_generated k {ring_0 k},k) I
                           (ring_of_integers k) P) = {I}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~((p:num) divides 0)` THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_PRIME_IDEAL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `~(ring_of_num k n IN (P:A->bool))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `p:num`]
      RING_OF_INT_IN_PRIME_IDEAL) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN
    DISCH_THEN(MP_TAC o SPEC `&n:int`) THEN
    ASM_REWRITE_TAC[RING_OF_INT_OF_NUM; GSYM num_divides];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_pow k z n = ring_1 (k:A ring)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `z:A`] RING_POW_RING_ORDER) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [MATCH_MP_TAC ROOT_OF_UNITY_IN_RING_OF_INTEGERS THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k}:A ring`;
                 `k:A ring`; `ring_of_integers k:A ring`; `P:A->bool`]
    (CONJUNCT1 INERTIA_GROUP)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING;
                    DECOMPOSITION_GROUP_RING_OF_INTEGERS];
    DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:A->A` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `(f:A->A) z = z` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `n:num`;
                     `(f:A->A) z`; `z:A`] ROOTS_OF_UNITY_EQ_MOD_IDEAL) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_RING_OF_INTEGERS; RING_OF_INTEGERS] THEN
      CONJ_TAC THENL
       [MP_TAC(MATCH_MP GALOIS_GROUP_RING_OF_INTEGERS (ASSUME
         `(f:A->A) IN group_carrier
            (galois_group(subfield_generated k {ring_0 k},k) I)`)) THEN
        UNDISCH_TAC `(z:A) IN ring_carrier(ring_of_integers k)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `ring_homomorphism(k,k) (f:A->A)` ASSUME_TAC THENL
       [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM);
        ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_POW
        (ASSUME `ring_homomorphism(k,k) (f:A->A)`))] THEN
      ASM_MESON_TAC[RING_HOMOMORPHISM_1];
      ALL_TAC] THEN
    MATCH_MP_TAC CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `z:A`] THEN
    ASM_REWRITE_TAC[GALOIS_GROUP_I; I_THM];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GALOIS_GROUP_I; IMAGE_I; I_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN ring_carrier k` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_SUB_REFL] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`]
      IN_RING_IDEAL_0) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS]]);;

let CYCLOTOMIC_FIELD_FROBENIUS_ELEMENT = prove
 (`!(k:A ring) z n p P.
        number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
        subfield_generated k {z} = k /\
        prime p /\ ~(p divides n) /\
        maximal_ideal (ring_of_integers k) P /\ ring_of_num k p IN P
        ==> frobenius_element (subfield_generated k {ring_0 k},k) I
              (ring_of_integers k) P z =
            ring_pow k z p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~((p:num) divides 0)` THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_PRIME_IDEAL) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `!m. ring_of_int (k:A ring) m IN P <=> &p divides m`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `p:num`]
      RING_OF_INT_IN_PRIME_IDEAL) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(ring_of_num k n IN (P:A->bool))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM RING_OF_INT_OF_NUM; GSYM num_divides]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_pow k z n = ring_1 (k:A ring)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `z:A`] RING_POW_RING_ORDER) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [MATCH_MP_TAC ROOT_OF_UNITY_IN_RING_OF_INTEGERS THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(P = {ring_0 (k:A ring)})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `ring_of_num k p IN (P:A->bool)` THEN
    ASM_REWRITE_TAC[IN_SING; RING_OF_NUM_EQ_0] THEN
    UNDISCH_TAC `number_field(k:A ring)` THEN SIMP_TAC[number_field] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[NUMBER_RULE
     `((0:num) divides n) <=> n = 0`] THEN
    ASM_MESON_TAC[PRIME_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `n:num`; `p:num`; `P:A->bool`]
    CYCLOTOMIC_FIELD_INERTIA_GROUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `P:A->bool`; `p:num`]
    NUMBER_FIELD_RESIDUE_PRIME_FIELD_CARD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `number_field(k:A ring)` THEN
    SIMP_TAC[number_field];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k}:A ring`;
                 `k:A ring`; `ring_of_integers k:A ring`; `P:A->bool`]
    FROBENIUS_ELEMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING;
                    GALOIS_GROUP_RING_OF_INTEGERS] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `number_field(k:A ring)` THEN SIMP_TAC[number_field];
      MATCH_MP_TAC CYCLOTOMIC_FIELD_GALOIS_EXTENSION THEN
      MAP_EVERY EXISTS_TAC [`z:A`; `n:num`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `g = frobenius_element (subfield_generated k {ring_0 k},k) I
          (ring_of_integers k) (P:A->bool)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `g:A->A`)) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_homomorphism(k,k) (g:A->A)` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `n:num`;
                 `(g:A->A) z`; `ring_pow k (z:A) p`]
    ROOTS_OF_UNITY_EQ_MOD_IDEAL) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_RING_OF_INTEGERS; RING_OF_INTEGERS] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(MATCH_MP GALOIS_GROUP_RING_OF_INTEGERS (ASSUME
     `(g:A->A) IN group_carrier
        (galois_group(subfield_generated k {ring_0 k},k) I)`)) THEN
    UNDISCH_TAC `(z:A) IN ring_carrier(ring_of_integers k)` THEN SET_TAC[];
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `z:A`; `p:num`] RING_POW) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS];
    ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_POW
      (ASSUME `ring_homomorphism(k,k) (g:A->A)`))] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_1];
    ASM_SIMP_TAC[RING_POW_POW] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_SIMP_TAC[RING_POW_MUL; RING_POW_ONE]]);;
