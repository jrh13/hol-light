(* ========================================================================= *)
(* Norms of extended ideals and the relative fundamental identity.           *)
(*                                                                           *)
(* For a field k with a ring homomorphism h into a number field l (then k is *)
(* a number field, NUMBER_FIELD_HOMOMORPHIC_PREIMAGE), with O_k and O_l the  *)
(* rings of integers and [l:k] = extension_degree(k,l) h:                    *)
(*                                                                           *)
(*   N(j O_l) = N(j)^[l:k] for every nonzero ideal j of O_k                  *)
(*                                  (NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q),   *)
(*   sum of e(P|p) f(P|p) over the primes P above p = [l:k] for every        *)
(*   nonzero prime p of O_k (NUMBER_FIELD_FUNDAMENTAL_IDENTITY),             *)
(*                                                                           *)
(* with e(P|p) = ramification_index (O_k,O_l) h P and f(P|p) =               *)
(* residue_degree (O_k,O_l) h P (ANT/prime_split.ml); hence                  *)
(* 1 <= e(P|p), 1 <= f(P|p), e(P|p) f(P|p) <= [l:k], and there are between   *)
(* 1 and [l:k] primes above p.                                               *)
(*                                                                           *)
(* Route (no basis of O_l over O_k, which need not exist). A family of       *)
(* elements b_i of a Dedekind domain, not all 0, satisfies b_i t = e u_i     *)
(* with some u_i outside a given proper ideal j (DEDEKIND_PRIMITIVE_MULTIPLE *)
(* of ANT/dedekind.ml: if c b = (e) for the ideal b of the family, take t in *)
(* c but not in c j); with a common denominator                              *)
(* (RING_OF_INTEGERS_COMMON_DENOMINATOR of ANT/numfield.ml) a relation over  *)
(* k among elements of any ring yields one over O_k with a coefficient       *)
(* outside j (NUMBER_FIELD_INDEPENDENT_MOD_IDEAL). Hence lifts to O_l of a   *)
(* basis of O_l/J over O_k/p are independent over k                          *)
(* (RING_OF_INTEGERS_QUOTIENT_FREE_BASIS_LE); since the contraction of pO_l  *)
(* is p (RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME) this gives      *)
(* N(pO_l) <= N(p)^[l:k], and by multiplicativity N(jO_l) <= N(j)^[l:k] for  *)
(* every nonzero ideal j (NUMBER_FIELD_IDEAL_NORM_EXTENSION_LE). A nonzero   *)
(* integer m in j gives (m) = j c and N((m)O_l) = |m|^[l:Q] =                *)
(* (|m|^[k:Q])^[l:k] = N((m))^[l:k] by the tower law, which forces equality. *)
(* The identity follows from the factorization of pO_l and N(P) =            *)
(* N(p)^f(P|p).                                                              *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/fieldtheory.ml (ring_independent,    *)
(* extension_degree, FREE_BASIS_FIELD, FREE_BASIS_INDEPENDENT_EQ,            *)
(* FREE_BASIS_EXISTS), Library/products.ml (EXP_NSUM, NPRODUCT_EQ),          *)
(* Library/ring_det.ml (free_basis, FREE_BASIS_INDEPENDENT,                  *)
(* FREE_BASIS_HAS_SIZE), ANT/ideal_arith.ml, ANT/dedekind.ml                 *)
(* (DEDEKIND_PRIMITIVE_MULTIPLE), ANT/ideal_norm.ml, ANT/numfield.ml         *)
(* (RING_OF_INTEGERS_COMMON_DENOMINATOR), ANT/ring_of_integers.ml,           *)
(* ANT/norm_index.ml (NUMBER_FIELD_IDEAL_NORM_MUL_Q) and                     *)
(* ANT/relative_split.ml.                                                    *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/products.ml";;
needs "ANT/algmisc.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/ideal_norm.ml";;
needs "Library/ring_det.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/norm_index.ml";;
needs "ANT/trace_form.ml";;
needs "ANT/relative_split.ml";;

(* ------------------------------------------------------------------------- *)
(* Lifts of a basis of O_l / J over O_k / p are independent over k.          *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_INDEPENDENT_MOD_IDEAL = prove
 (`!k:A ring l:B ring h j s (w:K->B).
        number_field k /\ ring_homomorphism(k,l) h /\
        ring_ideal (ring_of_integers k) j /\
        ~(j = ring_carrier(ring_of_integers k)) /\
        FINITE s /\ (!i. i IN s ==> w i IN ring_carrier l) /\
        (!u. (!i. i IN s ==> u i IN ring_carrier(ring_of_integers k)) /\
             ring_sum l s (\i. ring_mul l (h(u i)) (w i)) = ring_0 l
             ==> !i. i IN s ==> u i IN j)
        ==> !c. (!i. i IN s ==> c i IN ring_carrier k) /\
                ring_sum l s (\i. ring_mul l (h(c i)) (w i)) = ring_0 l
                ==> !i. i IN s ==> c i = ring_0 k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `c:K->A` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  PURE_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_SUBSET) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `s:K->bool`; `c:K->A`]
    RING_OF_INTEGERS_COMMON_DENOMINATOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`; `s:K->bool`;
                 `\i. ring_mul k d ((c:K->A) i)`]
    DEDEKIND_PRIMITIVE_MULTIPLE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_OF_INTEGERS] THEN
    UNDISCH_TAC `?i. i IN s /\ ~((c:K->A) i = ring_0 k)` THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN];
    DISCH_THEN(X_CHOOSE_THEN `t:A` (X_CHOOSE_THEN `e:A`
      (X_CHOOSE_THEN `u:K->A`
        (STRIP_ASSUME_TAC o REWRITE_RULE[RING_OF_INTEGERS]))))] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:K->A`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC]; ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN
   `(d:A) IN ring_carrier k /\ (t:A) IN ring_carrier k /\
    (e:A) IN ring_carrier k /\
    ring_mul k (ring_inv k e) (ring_mul k d t) IN ring_carrier k`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL; RING_INV]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum l s (\i. ring_mul l ((h:A->B)
      (ring_mul k (ring_mul k (ring_inv k e) (ring_mul k d t)) ((c:K->A) i)))
      ((w:K->B) i))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `x:K` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `e:A`] FIELD_MUL_LINV) THEN
    MP_TAC(ISPECL [`k:A ring`; `e:A`] RING_INV) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:K`) THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN RING_TAC THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[EXTENSION_LINCOMB_LMUL] THEN MATCH_MP_TAC RING_MUL_RZERO THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]]);;

let RING_OF_INTEGERS_QUOTIENT_FREE_BASIS_LE = prove
 (`!k:A ring l:B ring h p J (g:(A->bool)->(B->bool)) m G.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        maximal_ideal (ring_of_integers k) p /\
        ring_ideal (ring_of_integers l) J /\
        ring_homomorphism(quotient_ring (ring_of_integers k) p,
                          quotient_ring (ring_of_integers l) J) g /\
        (!y. y IN ring_carrier(ring_of_integers k)
             ==> g(ring_coset (ring_of_integers k) p y) =
                 ring_coset (ring_of_integers l) J (h y)) /\
        free_basis (quotient_ring (ring_of_integers k) p,
                    quotient_ring (ring_of_integers l) J) g m G
        ==> m <= extension_degree(k,l) h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MAXIMAL_IDEAL_IMP_PSUBSET) THEN
  REWRITE_TAC[PSUBSET] THEN STRIP_TAC THEN
  SUBGOAL_THEN `field(quotient_ring (ring_of_integers k) (p:A->bool))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[FIELD_QUOTIENT_RING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER)) THEN
  MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
   (ISPEC `ring_of_integers l:B ring` RING_MUL)) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?w:num->B. !i. i < m
                   ==> w i IN ring_carrier(ring_of_integers l) /\
                       G i = ring_coset (ring_of_integers l) J (w i)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
    ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < m ==> (w:num->B) i IN ring_carrier l` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET]
      (ISPEC `l:B ring` RING_OF_INTEGERS_SUBSET)) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j. i < m /\ j < m /\ (w:num->B) i = w j ==> i = j`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:(A->bool)->(B->bool)`;
                   `quotient_ring (ring_of_integers k) (p:A->bool)`;
                   `quotient_ring (ring_of_integers l) (J:B->bool)`; `m:num`;
                   `G:num->(B->bool)`]
      FREE_BASIS_FIELD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MATCH_MP_TAC th) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_independent (k,l) (h:A->B) (IMAGE (w:num->B) {i | i < m})`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `m:num`; `w:num->B`]
      FREE_BASIS_INDEPENDENT_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`;
                   `{i:num | i < m}`; `w:num->B`]
      NUMBER_FIELD_INDEPENDENT_MOD_IDEAL) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `u:num->A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`g:(A->bool)->(B->bool)`;
                   `quotient_ring (ring_of_integers k) (p:A->bool)`;
                   `quotient_ring (ring_of_integers l) (J:B->bool)`; `m:num`;
                   `G:num->(B->bool)`;
                   `\i. ring_coset (ring_of_integers k) p ((u:num->A) i)`]
      FREE_BASIS_INDEPENDENT) THEN
    SIMP_TAC[QUOTIENT_RING_0; RING_COSET_EQ_IDEAL;
             ASSUME `ring_ideal (ring_of_integers k) (p:A->bool)`;
             ASSUME `ring_ideal (ring_of_integers l) (J:B->bool)`;
             ASSUME `!i. i < m
                         ==> (u:num->A) i IN ring_carrier(ring_of_integers k)`;
             ASSUME `free_basis (quotient_ring (ring_of_integers k) p,
                                 quotient_ring (ring_of_integers l) J)
                                (g:(A->bool)->(B->bool)) m G`] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN
      EXISTS_TAC `(u:num->A) i` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum (quotient_ring (ring_of_integers l) J) {i | i < m}
        (\i. ring_mul (quotient_ring (ring_of_integers l) J)
               (ring_coset (ring_of_integers l) J ((h:A->B)((u:num->A) i)))
               (ring_coset (ring_of_integers l) J (w i)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`;
                   `quotient_ring (ring_of_integers l) (J:B->bool)`;
                   `ring_coset (ring_of_integers l) (J:B->bool)`;
                   `{i:num | i < m}`; `\i. (h:A->B)((u:num->A) i)`;
                   `w:num->B`] RING_HOMOMORPHISM_SUM_MUL) THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_COSET; FINITE_NUMSEG_LT;
                 IN_ELIM_THM] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[RING_OF_INTEGERS] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_RING_OF_INTEGERS o
      rand o lhand o snd) THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`] RING_COSET_0) THEN
    ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; RING_OF_INTEGERS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[FINITE_EXTENSION_RING_MATROID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_matroid(k,l) (h:A->B)`; `IMAGE (w:num->B) {i | i < m}`]
    MATROID_DIMENSION_GE_FINITE_CARD) THEN
  ASM_SIMP_TAC[RING_MATROID_INDEPENDENT; extension_degree] THEN
  MP_TAC(ISPECL [`w:num->B`; `{i:num | i < m}`] CARD_IMAGE_INJ) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Norms of extended ideals.                                                 *)
(* ------------------------------------------------------------------------- *)

let RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME = prove
 (`!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> {x | x IN ring_carrier(ring_of_integers k) /\
                 h x IN ideal_generated (ring_of_integers l) (IMAGE h p)} = p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:B->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `P:B->bool`;
                 `IMAGE (h:A->B) p`] IDEAL_GENERATED_MINIMAL) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `P:B->bool`]
    RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
  ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER)) THEN
  MP_TAC(MATCH_MP PRIME_IDEAL_IMP_SUBSET
   (ASSUME `prime_ideal (ring_of_integers k) (p:A->bool)`)) THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `IMAGE (h:A->B) p`]
    IDEAL_GENERATED_SUBSET_CARRIER) THEN
  SET_TAC[]);;

let NUMBER_FIELD_IDEAL_NORM_EXTENSION_PRIME_LE = prove
 (`!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> ideal_norm (ring_of_integers l)
              (ideal_generated (ring_of_integers l) (IMAGE h p)) <=
            ideal_norm (ring_of_integers k) p EXP extension_degree(k,l) h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    RING_OF_INTEGERS_IDEAL_EXTENSION) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)` THEN
  SUBGOAL_THEN `ring_ideal (ring_of_integers l) (J:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_integers l:B ring`;
                 `h:A->B`; `J:B->bool`]
    RESIDUE_DEGREE_QUOTIENT_RING) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_OF_INTEGERS] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(A->bool)->(B->bool)` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `maximal_ideal (ring_of_integers k) (p:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `field(quotient_ring (ring_of_integers k) (p:A->bool)) /\
    FINITE(ring_carrier(quotient_ring (ring_of_integers k) (p:A->bool))) /\
    FINITE(ring_carrier(quotient_ring (ring_of_integers l) (J:B->bool)))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_QUOTIENT_RING; PRIME_IMP_RING_IDEAL;
                 RING_OF_INTEGERS_FINITE_QUOTIENT];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`quotient_ring (ring_of_integers k) (p:A->bool)`;
                 `quotient_ring (ring_of_integers l) (J:B->bool)`;
                 `g:(A->bool)->(B->bool)`;
                 `ring_carrier(quotient_ring (ring_of_integers l) (J:B->bool))`]
    FREE_BASIS_EXISTS) THEN
  ASM_REWRITE_TAC[ring_spanning; SUBSET_REFL; RING_SPAN_SELF] THEN
  DISCH_THEN(X_CHOOSE_TAC `G:num->(B->bool)`) THEN
  MP_TAC(ISPECL [`g:(A->bool)->(B->bool)`;
                 `quotient_ring (ring_of_integers k) (p:A->bool)`;
                 `quotient_ring (ring_of_integers l) (J:B->bool)`;
                 `extension_degree
                   (quotient_ring (ring_of_integers k) (p:A->bool),
                    quotient_ring (ring_of_integers l) (J:B->bool))
                   (g:(A->bool)->(B->bool))`;
                 `G:num->(B->bool)`]
    FREE_BASIS_HAS_SIZE) THEN
  ASM_REWRITE_TAC[HAS_SIZE; GSYM ideal_norm] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:A->bool`] IDEAL_NORM_POS) THEN
  ASM_REWRITE_TAC[LE_EXP] THEN DISCH_TAC THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; DISJ2_TAC] THEN
  MATCH_MP_TAC RING_OF_INTEGERS_QUOTIENT_FREE_BASIS_LE THEN
  MAP_EVERY EXISTS_TAC
   [`p:A->bool`; `J:B->bool`; `g:(A->bool)->(B->bool)`; `G:num->(B->bool)`] THEN
  ASM_REWRITE_TAC[]);;

let NUMBER_FIELD_IDEAL_NORM_EXTENSION_LE = prove
 (`!k:A ring l:B ring h j.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
        ==> ideal_norm (ring_of_integers l)
              (ideal_generated (ring_of_integers l) (IMAGE h j)) <=
            ideal_norm (ring_of_integers k) j EXP extension_degree(k,l) h`,
  REPEAT GEN_TAC THEN
  WF_INDUCT_TAC `ideal_norm (ring_of_integers k) (j:A->bool)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `j:A->bool`]
    RING_OF_INTEGERS_IDEAL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `j = ring_carrier(ring_of_integers k:A ring)` THEN
  ASM_SIMP_TAC[IDEAL_NORM_CARRIER; EXP_ONE; LE_REFL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`]
    MAXIMAL_SUPERIDEAL_EXISTS) THEN
  ASM_SIMP_TAC[proper_ideal; PSUBSET; RING_IDEAL_IMP_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `prime_ideal (ring_of_integers k) (p:A->bool) /\ ~(p = {ring_0 k})`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MAXIMAL_IMP_PRIME_IDEAL] THEN
    MP_TAC(MATCH_MP RING_IDEAL_IMP_NONEMPTY
     (ASSUME `ring_ideal (ring_of_integers k) (j:A->bool)`)) THEN
    MAP_EVERY UNDISCH_TAC [`(j:A->bool) SUBSET p`; `~(j = {ring_0 k:A})`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`; `p:A->bool`]
    DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; MAXIMAL_IMP_RING_IDEAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (SUBST_ALL_TAC o SYM))) THEN
  SUBGOAL_THEN `~(c = {ring_0 k:A})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `~(ideal_prod (ring_of_integers k) p c = {ring_0 k:A})` THEN
    ASM_SIMP_TAC[REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers k:A ring` IDEAL_PROD_RZERO);
                 MAXIMAL_IMP_RING_IDEAL; RING_IDEAL_IMP_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `p:A->bool`; `c:A->bool`]
    NUMBER_FIELD_IDEAL_NORM_MUL_Q) THEN
  ASM_SIMP_TAC[MAXIMAL_IMP_RING_IDEAL] THEN DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `c:A->bool`]
    RING_OF_INTEGERS_IDEAL_EXTENSION) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    RING_OF_INTEGERS_IDEAL_EXTENSION) THEN
  ASM_SIMP_TAC[MAXIMAL_IMP_RING_IDEAL] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_integers l:B ring`;
                 `h:A->B`; `p:A->bool`; `c:A->bool`]
    IDEAL_PROD_HOMOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_OF_INTEGERS; MAXIMAL_IMP_RING_IDEAL;
               RING_IDEAL_IMP_SUBSET] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`l:B ring`;
                 `ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)`;
                 `ideal_generated (ring_of_integers l) (IMAGE (h:A->B) c)`]
    NUMBER_FIELD_IDEAL_NORM_MUL_Q) THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MULT_EXP] THEN MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC NUMBER_FIELD_IDEAL_NORM_EXTENSION_PRIME_LE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:A ring`; `c:A->bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `1 * b < a * b ==> b < a * b`) THEN
  REWRITE_TAC[LT_MULT_RCANCEL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC IDEAL_NORM_GT_1 THEN
    ASM_SIMP_TAC[MAXIMAL_IMP_RING_IDEAL; RING_OF_INTEGERS_FINITE_QUOTIENT] THEN
    ASM_MESON_TAC[MAXIMAL_IDEAL_IMP_PSUBSET; PSUBSET];
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> ~(n = 0)`) THEN
    MATCH_MP_TAC IDEAL_NORM_POS THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS_FINITE_QUOTIENT]]);;

let NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q = prove
 (`!k:A ring l:B ring h j.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
        ==> ideal_norm (ring_of_integers l)
              (ideal_generated (ring_of_integers l) (IMAGE h j)) =
            ideal_norm (ring_of_integers k) j EXP extension_degree(k,l) h`,
  let lemma = prove
   (`!a b c d. a <= b /\ c <= d /\ ~(c = 0) /\ a * c = b * d ==> a = b`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`b:num`; `a:num`; `c:num`] LE_MULT_RCANCEL) THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `j:A->bool`] RING_OF_INTEGERS_IDEAL_INTEGER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m:int` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                 `ideal_generated (ring_of_integers k) {ring_of_int k m:A}`;
                 `j:A->bool`] DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_IDEAL_IDEAL_GENERATED;
               IDEAL_GENERATED_MINIMAL; SING_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(c = {ring_0 k:A})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `ideal_prod (ring_of_integers k) j {ring_0 k} =
                 ideal_generated (ring_of_integers k) {ring_of_int k m:A}` THEN
    SIMP_TAC[REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers k:A ring` IDEAL_PROD_RZERO);
             RING_IDEAL_IMP_SUBSET;
             ASSUME `ring_ideal (ring_of_integers k) (j:A->bool)`] THEN
    DISCH_THEN(MP_TAC o SPEC `ring_of_int k m:A` o REWRITE_RULE[EXTENSION]) THEN
    REWRITE_TAC[IN_SING; IN_IDEAL_GENERATED_SELF;
                RING_OF_INT_IN_RING_OF_INTEGERS] THEN
    MP_TAC(ASSUME `number_field(k:A ring)`) THEN
    SIMP_TAC[number_field; RING_OF_INT_EQ_0_CHAR_0] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `j:A->bool`]
    RING_OF_INTEGERS_IDEAL_EXTENSION) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `c:A->bool`]
    RING_OF_INTEGERS_IDEAL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC lemma THEN
  EXISTS_TAC `ideal_norm (ring_of_integers l)
                (ideal_generated (ring_of_integers l) (IMAGE (h:A->B) c))` THEN
  EXISTS_TAC `ideal_norm (ring_of_integers k) c EXP
              extension_degree(k:A ring,l:B ring) h` THEN
  ASM_SIMP_TAC[NUMBER_FIELD_IDEAL_NORM_EXTENSION_LE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1 <= n ==> ~(n = 0)`) THEN
    ASM_SIMP_TAC[IDEAL_NORM_POS; RING_OF_INTEGERS_FINITE_QUOTIENT;
                 RING_IDEAL_IDEAL_GENERATED];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MULT_EXP] THEN
  MP_TAC(ISPECL [`k:A ring`; `j:A->bool`; `c:A->bool`]
    NUMBER_FIELD_IDEAL_NORM_MUL_Q) THEN
  MP_TAC(ISPECL [`l:B ring`;
                 `ideal_generated (ring_of_integers l) (IMAGE (h:A->B) j)`;
                 `ideal_generated (ring_of_integers l) (IMAGE (h:A->B) c)`]
    NUMBER_FIELD_IDEAL_NORM_MUL_Q) THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_integers l:B ring`;
                 `h:A->B`; `j:A->bool`; `c:A->bool`]
    IDEAL_PROD_HOMOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_OF_INTEGERS; RING_IDEAL_IMP_SUBSET] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_IMAGE_IDEAL_GENERATED; IMAGE_CLAUSES;
               RING_HOMOMORPHISM_RING_OF_INTEGERS; SING_SUBSET;
               RING_OF_INT_IN_RING_OF_INTEGERS] THEN
  REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_RING_OF_INT
   (ASSUME `ring_homomorphism(k:A ring,l:B ring) h`)] THEN
  ASM_SIMP_TAC[RING_OF_INTEGERS_IDEAL_NORM_INTEGER; NUMBER_FIELD_TOWER_LAW;
               EXP_EXP]);;

(* ------------------------------------------------------------------------- *)
(* The fundamental identity and its consequences.                            *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_FUNDAMENTAL_IDENTITY = prove
 (`!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
                 (\P. ramification_index
                        (ring_of_integers k,ring_of_integers l) h P *
                      residue_degree
                        (ring_of_integers k,ring_of_integers l) h P) =
            extension_degree(k,l) h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!P. P IN {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
        ==> prime_ideal (ring_of_integers l) P /\ ~(P = {ring_0 l}) /\
            IMAGE (h:A->B) p SUBSET P`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
      RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [EXTENSION] o
               CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q) THEN
  ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL;
               NUMBER_FIELD_PRIME_FACTORIZATION] THEN
  W(MP_TAC o PART_MATCH (lhand o rand o rand) IDEAL_NORM_IDEAL_PRODUCT o
    lhand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS] THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_IDEAL_IDEAL_POW] THEN
    X_GEN_TAC `P:B->bool` THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REWRITE_RULE[RING_OF_INTEGERS]
       (ISPEC `ring_of_integers l:B ring` IDEAL_POW_EQ_ZERO);
                   INTEGRAL_DOMAIN_RING_OF_INTEGERS; NUMBER_FIELD_IMP_FIELD;
                   PRIME_IMP_RING_IDEAL];
      ASM_SIMP_TAC[RING_OF_INTEGERS_FINITE_QUOTIENT; RING_IDEAL_IDEAL_POW]];
    DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!P. P IN {P | prime_ideal (ring_of_integers l) P /\
                  IMAGE (h:A->B) p SUBSET P}
        ==> ideal_norm (ring_of_integers l)
              (ideal_pow (ring_of_integers l) P
                 (ramification_index
                    (ring_of_integers k,ring_of_integers l) h P)) =
            ideal_norm (ring_of_integers k) p EXP
            (ramification_index
               (ring_of_integers k,ring_of_integers l) h P *
             residue_degree
               (ring_of_integers k,ring_of_integers l) h P)`
  (fun th -> REWRITE_TAC[MATCH_MP NPRODUCT_EQ th]) THENL
   [X_GEN_TAC `P:B->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:B->bool`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `P:B->bool`]
      RING_OF_INTEGERS_IDEAL_NORM_PRIME) THEN
    ASM_SIMP_TAC[IDEAL_NORM_IDEAL_POW; DEDEKIND_RING_OF_INTEGERS;
                 PRIME_IMP_RING_IDEAL; RING_OF_INTEGERS_FINITE_QUOTIENT;
                 RING_OF_INTEGERS] THEN
    REWRITE_TAC[EXP_EXP; MULT_SYM];
    ASM_SIMP_TAC[GSYM EXP_NSUM] THEN
    SUBGOAL_THEN `1 < ideal_norm (ring_of_integers k) (p:A->bool)` MP_TAC THENL
     [MATCH_MP_TAC IDEAL_NORM_GT_1 THEN
      ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL; RING_OF_INTEGERS_FINITE_QUOTIENT] THEN
      ASM_MESON_TAC[PRIME_IDEAL_IMP_PSUBSET; PSUBSET];
      SIMP_TAC[EQ_EXP; ARITH_RULE `1 < n ==> ~(n = 0) /\ ~(n = 1)`] THEN
      MESON_TAC[]]]);;

let NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS = prove
 (`!k:A ring l:B ring h p P.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P
        ==> 1 <= ramification_index
                   (ring_of_integers k,ring_of_integers l) h P /\
            1 <= residue_degree
                   (ring_of_integers k,ring_of_integers l) h P /\
            ramification_index
              (ring_of_integers k,ring_of_integers l) h P *
            residue_degree
              (ring_of_integers k,ring_of_integers l) h P
            <= extension_degree(k,l) h`,
  REPEAT STRIP_TAC THENL
   [ALL_TAC;
    ALL_TAC;
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
      NUMBER_FIELD_FUNDAMENTAL_IDENTITY) THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
      NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP EQ_IMP_LE) THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] NSUM_POS_BOUND)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `P:B->bool`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM]] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `P:B->bool` o GEN_REWRITE_RULE I [EXTENSION] o
             CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THENL
   [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `P:B->bool`]
      RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN
    ASM_REWRITE_TAC[ramification_index] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
      RING_OF_INTEGERS_IDEAL_EXTENSION) THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `P:B->bool`;
                   `ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)`;
                   `1`] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_IDEAL_IDEAL_GENERATED;
                 IDEAL_POW_1; PRIME_IMP_RING_IDEAL; IDEAL_GENERATED_MINIMAL;
                 RING_OF_INTEGERS];
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `P:B->bool`]
      RING_OF_INTEGERS_IDEAL_NORM_PRIME) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    ASM_CASES_TAC
     `residue_degree (ring_of_integers k,ring_of_integers l)
                              (h:A->B) P = 0` THEN
    ASM_REWRITE_TAC[EXP] THEN
    MATCH_MP_TAC(ARITH_RULE `1 < n ==> ~(n = 1)`) THEN
    MATCH_MP_TAC IDEAL_NORM_GT_1 THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL; RING_OF_INTEGERS_FINITE_QUOTIENT] THEN
    MP_TAC(MATCH_MP PRIME_IDEAL_IMP_PSUBSET
     (ASSUME `prime_ideal (ring_of_integers l) (P:B->bool)`)) THEN
    SIMP_TAC[PSUBSET]]);;

let NUMBER_FIELD_CARD_PRIME_IDEALS_ABOVE = prove
 (`!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> 1 <= CARD {P | prime_ideal (ring_of_integers l) P /\
                           IMAGE h p SUBSET P} /\
            CARD {P | prime_ideal (ring_of_integers l) P /\
                      IMAGE h p SUBSET P}
            <= extension_degree(k,l) h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; CARD_EQ_0] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    NUMBER_FIELD_FUNDAMENTAL_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[CARD_EQ_NSUM] THEN MATCH_MP_TAC NSUM_LE THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `P:B->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `P:B->bool`]
    NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN ARITH_TAC);;
