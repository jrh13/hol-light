(* ========================================================================= *)
(* Primitive elements in the conjugate-vector framework.                     *)
(*                                                                           *)
(* Purpose: every algebraic integer z is the first conjugate r 1 of some     *)
(* nf_data n c r (NF_DATA_EXISTS): in the number field K = Q(z) of ANT/,     *)
(* the conjugates g z of z under the [K:Q] complex embeddings g are          *)
(* distinct, since z generates K, and they are the roots of a monic integer  *)
(* polynomial of degree n <= [K:Q] (RING_OF_INTEGERS_CONJUGATES_POLYFUN); an *)
(* integer polynomial of degree m < n vanishing at one root g z vanishes at  *)
(* z (g is injective), hence at all [K:Q] > m conjugates of z, so it is      *)
(* zero. Finitely many algebraic numbers lie in one nf_data field, with a    *)
(* common denominator (NF_PRIMITIVE_ELEMENT): the field they generate has an *)
(* integral primitive element (NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT_Q of  *)
(* ANT/integrality.ml), whose nf_data field is that field                    *)
(* (NF_DATA_FIELD_CARRIER).                                                  *)
(*                                                                           *)
(* Main results: NF_DATA_EXISTS, NF_PRIMITIVE_ELEMENT.                       *)
(*                                                                           *)
(* Uses: ANT/complex_embeddings.ml (complex_embeddings,                      *)
(* RING_OF_INTEGERS_CONJUGATES_POLYFUN, COMPLEX_EMBEDDINGS_HAS_SIZE,         *)
(* COMPLEX_EMBEDDINGS_MONOMORPHISM, COMPLEX_EMBEDDINGS_RESTRICTION),         *)
(* ANT/hermite.ml (NUMBER_FIELD_GENERATOR_CONJUGATES), ANT/integrality.ml    *)
(* (NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT_Q), Library/fieldtheory.ml       *)
(* (SUBFIELD_GENERATED_IDEMPOT, SUBFIELD_GENERATED_IDEMPOT_GEN),             *)
(* Library/permutations.ml (swap, PERMUTES_SWAP),                            *)
(* Multivariate/complex_algebra.ml (COMPLEX_POLYFUN_ROOTBOUND),              *)
(* Baker/algebraic.ml (COMPLEX_POLYFUN_FACTOR), Baker/algint.ml              *)
(* (algebraic_integer), Baker/ant_bridge_complex.ml                          *)
(* (NUMBER_FIELD_COMPLEX_SUBFIELD_GENERATED, BRIDGE_NF_HOM_POLY,             *)
(* BRIDGE_NF_SUBRING_POLY, BRIDGE_NF_GEN_IN), Baker/sharp_tools.ml           *)
(* (RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED), Baker/nf_defs.ml           *)
(* (nf_data), Baker/ant_bridge_nf.ml (NF_DATA_FIELD_CARRIER).                *)
(* ========================================================================= *)

needs "ANT/hermite.ml";;
needs "Baker/sharp_tools.ml";;
needs "Baker/ant_bridge_nf.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Every algebraic integer is the first conjugate of some nf_data: the roots *)
(* of the monic integer polynomial of its conjugates, z first.               *)
(* ------------------------------------------------------------------------- *)

let NF_FIELD_CPRODUCT_PERMUTE = prove
 (`!(f:A->complex) p s.
        p permutes s ==> cproduct s f = cproduct s (\i. f(p i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\i. (f:A->complex)((p:A->A) i)) = f o p` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[cproduct] THEN
  MATCH_MP_TAC(MATCH_MP ITERATE_PERMUTE MONOIDAL_COMPLEX_MUL) THEN
  ASM_REWRITE_TAC[]);;

let NF_FIELD_ROOT_FIRST = prove
 (`!n (r0:num->complex) z.
        cproduct(1..n) (\i. z - r0 i) = Cx(&0)
        ==> ?r. r 1 = z /\
                !x. cproduct(1..n) (\i. x - r i) =
                    cproduct(1..n) (\i. x - r0 i)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG; COMPLEX_SUB_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\i. (r0:num->complex)(swap(1,j) i)` THEN
  REWRITE_TAC[swap] THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:complex` THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`\i. x - (r0:num->complex) i`; `swap(1,j)`; `1..n`]
    NF_FIELD_CPRODUCT_PERMUTE) THEN
  REWRITE_TAC[swap] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC PERMUTES_SWAP THEN
  UNDISCH_TAC `j IN 1..n` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

let NF_DATA_EXISTS = prove
 (`!z. algebraic_integer z ==> ?n c r. nf_data n c r /\ r 1 = z`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `K = subfield_generated complex_ring {z:complex}` THEN
  SUBGOAL_THEN `number_field(K:complex ring)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    MATCH_MP_TAC NUMBER_FIELD_COMPLEX_SUBFIELD_GENERATED THEN
    ASM_SIMP_TAC[FINITE_SING; IN_SING; ALGEBRAIC_INTEGER_IMP_ALGEBRAIC_NUMBER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(z:complex) IN ring_carrier K /\ z IN ring_carrier(ring_of_integers K) /\
    ring_carrier K subring_of complex_ring /\ ring_0 K = Cx(&0) /\
    ring_homomorphism(K,complex_ring) I`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    REWRITE_TAC[BRIDGE_NF_GEN_IN; IN_ELIM_THM;
                RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED;
                CONJUNCT2 SUBFIELD_GENERATED; COMPLEX_RING_CLAUSES;
                SUBRING_SUBFIELD_GENERATED;
                RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* the conjugates of z: the roots of a monic integer polynomial *)
  MP_TAC(ISPECL [`K:complex ring`; `z:complex`]
    RING_OF_INTEGERS_CONJUGATES_POLYFUN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `c:num->real`
    STRIP_ASSUME_TAC)) THEN
  (* they are distinct (z generates K), so there are [K:Q] of them *)
  SUBGOAL_THEN
   `IMAGE (\g:complex->complex. g z) (complex_embeddings K) HAS_SIZE
    extension_degree (subfield_generated K {Cx(&0)},K:complex ring) I`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    MP_TAC(ISPEC `K:complex ring` COMPLEX_EMBEDDINGS_HAS_SIZE) THEN
    MP_TAC(ISPECL [`K:complex ring`; `z:complex`]
      NUMBER_FIELD_GENERATOR_CONJUGATES) THEN
    SUBGOAL_THEN `subfield_generated K {z:complex} = K` SUBST1_TAC THENL
     [EXPAND_TAC "K" THEN REWRITE_TAC[SUBFIELD_GENERATED_IDEMPOT];
      ASM_SIMP_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  (* an integer polynomial vanishes at one conjugate iff at z *)
  SUBGOAL_THEN
   `!g b m. g IN complex_embeddings K /\ (!i. integer(b i))
            ==> (vsum(0..m) (\i. Cx(b i) * g z pow i) = Cx(&0) <=>
                 vsum(0..m) (\i. Cx(b i) * z pow i) = Cx(&0))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `ring_homomorphism(K,complex_ring) (g:complex->complex)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(g:complex->complex) IN complex_embeddings K` THEN
      SIMP_TAC[complex_embeddings; IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`{z:complex}`; `g:complex->complex`; `z:complex`;
                   `b:num->real`; `m:num`] BRIDGE_NF_HOM_POLY) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[RATIONAL_INTEGER]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN
     `vsum(0..m) (\i. Cx(b i) * z pow i) IN ring_carrier K /\
      Cx(&0) IN ring_carrier K /\ (g:complex->complex)(Cx(&0)) = Cx(&0)`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[BRIDGE_NF_SUBRING_POLY] THEN
      ASM_MESON_TAC[RING_0; RING_HOMOMORPHISM_0; COMPLEX_RING_CLAUSES];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`K:complex ring`; `g:complex->complex`]
      COMPLEX_EMBEDDINGS_MONOMORPHISM) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[NUMBER_FIELD_IMP_FIELD]; ALL_TAC] THEN
    REWRITE_TAC[ring_monomorphism] THEN
    DISCH_THEN(MP_TAC o SPECL [`vsum(0..m) (\i. Cx(b i) * z pow i)`;
      `Cx(&0)`] o CONJUNCT2 o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the roots, enumerated with z first *)
  MP_TAC(SPECL [`n:num`; `\i. Cx((c:num->real) i)`] COMPLEX_POLYFUN_FACTOR) THEN
  ASM_REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ; COMPLEX_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:num->complex` ASSUME_TAC) THEN
  MP_TAC(SPECL [`n:num`; `r0:num->complex`; `z:complex`]
    NF_FIELD_ROOT_FIRST) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
    FIRST_ASSUM(MP_TAC o SPEC `z:complex` o GEN_REWRITE_RULE I [EXTENSION] o
      check (is_eq o concl)) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`K:complex ring`; `I:complex->complex`]
      COMPLEX_EMBEDDINGS_RESTRICTION) THEN
    ASM_REWRITE_TAC[I_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->complex` (CONJUNCTS_THEN2 ASSUME_TAC
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th])))) THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`; `r:num->complex`] THEN
  ASM_REWRITE_TAC[nf_data] THEN
  (* every root r k is a conjugate g z; a polynomial of degree m < n *)
  (* vanishing at r k vanishes at z, so at all [K:Q] >= n conjugates *)
  MAP_EVERY X_GEN_TAC [`k:num`; `m:num`; `b:num->real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?g. g IN complex_embeddings(K:complex ring) /\ (r:num->complex) k = g z`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `(r:num->complex) k` o
      GEN_REWRITE_RULE I [EXTENSION] o check (is_eq o concl)) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN
    ASM_MESON_TAC[COMPLEX_SUB_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `vsum(0..m) (\i. Cx(b i) * z pow i) = Cx(&0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`m:num`; `\i. Cx((b:num->real) i)`]
    COMPLEX_POLYFUN_ROOTBOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[CX_INJ; IN_NUMSEG; LE_0]; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`IMAGE (\g:complex->complex. g z) (complex_embeddings K)`;
    `{w | vsum(0..m) (\i. Cx(b i) * w pow i) = Cx(&0)}`] CARD_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Primitive elements: finitely many algebraic numbers in one nf_data field, *)
(* with a common denominator D.                                              *)
(* ------------------------------------------------------------------------- *)

let NF_PRIMITIVE_ELEMENT = prove
 (`!s. FINITE s /\ (!z. z IN s ==> algebraic_number z)
       ==> ?n c r D. nf_data n c r /\ integer D /\ ~(D = &0) /\
                     !z. z IN s
                         ==> ?p. (!i. integer(p i)) /\
                                 Cx D * z =
                                 vsum(0..n-1) (\i. Cx(p i) * r 1 pow i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `number_field(subfield_generated complex_ring s)` MP_TAC THENL
   [ASM_MESON_TAC[NUMBER_FIELD_COMPLEX_SUBFIELD_GENERATED]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:complex` MP_TAC o
    MATCH_MP NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT_Q) THEN
  REWRITE_TAC[RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `subfield_generated complex_ring {a:complex} =
                subfield_generated complex_ring s` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`complex_ring`; `{a:complex}`; `s:complex->bool`]
      SUBFIELD_GENERATED_IDEMPOT_GEN) THEN
    ASM_REWRITE_TAC[SING_SUBSET] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `c:num->real`
    (X_CHOOSE_THEN `r:num->complex` STRIP_ASSUME_TAC)) o
    MATCH_MP NF_DATA_EXISTS) THEN
  SUBGOAL_THEN `!z. z IN s ==> ?d p. integer d /\ ~(d = &0) /\
                     (!i. integer(p i)) /\
                     Cx d * z = vsum(0..n-1) (\i. Cx(p i) * r 1 pow i)`
  MP_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`]
      NF_DATA_FIELD_CARRIER) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
    ASM_REWRITE_TAC[COMPLEX_RING_CLAUSES; IN_UNIV];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV)
    [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:complex->real`
   (X_CHOOSE_THEN `p:complex->num->real` ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`; `r:num->complex`;
                        `product s (d:complex->real)`] THEN
  ASM_SIMP_TAC[INTEGER_PRODUCT; PRODUCT_EQ_0; NOT_EXISTS_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  EXISTS_TAC `\i:num. product (s DELETE z) (d:complex->real) *
                      (p:complex->num->real) z i` THEN
  SUBGOAL_THEN `integer(d(z:complex)) /\ ~(d z = &0) /\
                (!i. integer((p:complex->num->real) z i)) /\
                Cx(d z) * z = vsum(0..n-1) (\i. Cx(p z i) * r 1 pow i)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGER_MUL THEN
    ASM_SIMP_TAC[INTEGER_PRODUCT; IN_DELETE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:complex->real`; `s:complex->bool`; `z:complex`]
    PRODUCT_DELETE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `Cx(d (z:complex) * product (s DELETE z) d) * z =
                Cx(product (s DELETE z) d) * (Cx(d z) * z)` SUBST1_TAC THENL
   [REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[CX_MUL] THEN
  REPEAT STRIP_TAC THEN CONV_TAC COMPLEX_RING);;
