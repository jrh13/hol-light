(* ========================================================================= *)
(* Hilbert formula for the different and the tame exponent of the relative   *)
(* different (Serre, Local Fields III.6 and IV.1 Proposition 4; Neukirch     *)
(* III.2.6).                                                                 *)
(*                                                                           *)
(* For number fields, field k, number_field l and ring_homomorphism(k,l) h,  *)
(* p a nonzero prime of O_k, Q a prime of O_l above p (IMAGE h p SUBSET Q),  *)
(* D = number_field_different (k,l) h (ANT/different.ml), v_Q the valuation  *)
(* ideal_valuation (ring_of_integers l) Q, e = e(Q|p) =                      *)
(* ramification_index (ring_of_integers k,ring_of_integers l) h Q, char(Q)   *)
(* the characteristic of the residue field O_l/Q and, for l Galois over k,   *)
(* the lower numbering groups of ANT/ramification_groups.ml                  *)
(* G_i = group_carrier(inertia_group (k,l) h (ring_of_integers l)            *)
(*                       (ideal_pow (ring_of_integers l) Q (i + 1))):        *)
(*                                                                           *)
(*   v_Q(D) = sum over all i >= 0 of (|G_i| - 1)                             *)
(*                 (NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA; the sum over     *)
(*                 i < n for any n with G_n = 1 is                           *)
(*                 NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_LT)                *)
(*   e - 1 <= v_Q(D), and v_Q(D) = e - 1 iff char(Q) does not divide e       *)
(*                 (NUMBER_FIELD_DIFFERENT_VALUATION_TAME)                   *)
(*   e <= v_Q(D) iff char(Q) divides e                                       *)
(*                 (NUMBER_FIELD_DIFFERENT_VALUATION_WILD)                   *)
(*                                                                           *)
(* the last two for every extension of number fields, Galois or not; the     *)
(* absolute NUMBER_FIELD_DIFFERENT_VALUATION_TAME_Q and _WILD of             *)
(* ANT/different_exponent.ml (proved there by traces) are the case of k the  *)
(* prime subfield, by RAMIFICATION_INDEX_PRIME_SUBFIELD and                  *)
(* RING_OF_NUM_IN_PRIME_IDEAL. On the way, for k -> l -> m with m Galois     *)
(* over k and P a prime of O_m above Q, e(P|Q) v_Q(D_(l/k)) is the sum over  *)
(* i < n of the |G_i| - |G_i(m/l)|, G_i and G_i(m/l) the lower numbering     *)
(* groups of P over k and over l                                             *)
(* (NUMBER_FIELD_DIFFERENT_VALUATION_GALOIS_OVERFIELD), with the groups over *)
(* l those over k intersected with Gal(m/l) (INERTIA_GROUP_TOWER of          *)
(* ANT/decomposition.ml) and G_1 in a subgroup c of G_0 iff the index of c   *)
(* in G_0 is prime to char(P) (INERTIA_GROUP_WILD_SUBSET of                  *)
(* ANT/ramification_groups.ml).                                              *)
(*                                                                           *)
(* Routes. Over the decomposition field Z of Q (ANT/decomposition_field.ml)  *)
(* Q is the only prime above Q INTER Z, which is unramified over p, so       *)
(* D_(Z/k) is prime to Q and v_Q(D_(l/k)) = v_Q(D_(l/Z)) by the tower law    *)
(* NUMBER_FIELD_DIFFERENT_TOWER. Over Z there is a local power basis a       *)
(* (NUMBER_FIELD_LOCAL_POWER_BASIS of ANT/power_basis_extension.ml), so      *)
(* v_Q(D) = v_Q(Df(a)); Df(a) is the product of the a - g(a), g <> 1 in      *)
(* Gal(l/Z) = D_Q (GALOIS_PRIMITIVE_ELEMENT_DERIVATIVE of                    *)
(* Library/galois.ml), and g is in G_i iff                                   *)
(* g(a) == a modulo Q^(i+1) (INERTIA_GROUP_IDEAL_POW_LOCAL_GENERATOR), so    *)
(* v_Q(a - g(a)) counts the i with g in G_i and the formula is a double      *)
(* count (NSUM_CARD_SUBSETS_DELETE). For the tame exponent take a Galois     *)
(* closure m of l over k (NUMBER_FIELD_GALOIS_CLOSURE) and a prime P of O_m  *)
(* above Q: the tower law and the Hilbert formulae for m/k and m/l give      *)
(* e(P|Q) v_Q(D_(l/k)) as the sum of the |G_i| - |G_i INTER H|, H =          *)
(* Gal(m/l). Its term i = 0 is e(P|Q) (e - 1), as |G_0| = e(P|p) = e(P|Q) e  *)
(* and |G_0 INTER H| = e(P|Q); the other terms all vanish iff G_1 SUBSET H,  *)
(* and G_1, a normal subgroup of G_0 of p-power order and index prime to p   *)
(* (INERTIA_GROUP_WILD_PGROUP, INERTIA_GROUP_TAME_QUOTIENT), lies in G_0     *)
(* INTER H iff its index e is prime to p (INERTIA_GROUP_WILD_SUBSET).        *)
(*                                                                           *)
(* Generic lemma with a library home: NSUM_CARD_SUBSETS_DELETE (iterate.ml). *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (IN_RING_IDEAL_SUB_SYM),                      *)
(* Library/grouptheory.ml (Sylow), Library/galois.ml                         *)
(* (GALOIS_PRIMITIVE_ELEMENT_DERIVATIVE), ANT/dedekind.ml,                   *)
(* ANT/ideal_arith.ml, ANT/numfield.ml, ANT/prime_split.ml,                  *)
(* ANT/relative_split.ml, ANT/different.ml, ANT/different_extension.ml,      *)
(* ANT/decomposition.ml, ANT/nf_decomposition.ml,                            *)
(* ANT/decomposition_field.ml, ANT/split_primes.ml                           *)
(* (NUMBER_FIELD_GALOIS_CLOSURE), ANT/ramification_groups.ml and             *)
(* ANT/power_basis_extension.ml.                                             *)
(* ========================================================================= *)

needs "Library/grouptheory.ml";;
needs "Library/galois.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/numfield.ml";;
needs "ANT/prime_split.ml";;
needs "ANT/relative_split.ml";;
needs "ANT/different.ml";;
needs "ANT/different_extension.ml";;
needs "ANT/decomposition.ml";;
needs "ANT/nf_decomposition.ml";;
needs "ANT/decomposition_field.ml";;
needs "ANT/split_primes.ml";;
needs "ANT/ideal_norm_extension.ml";;
needs "ANT/ramification_groups.ml";;
needs "ANT/power_basis_extension.ml";;

(* ------------------------------------------------------------------------- *)
(* A double count.                                                           *)
(* ------------------------------------------------------------------------- *)

(* Counting: sum over g in G - {e} of #{i < n | g IN H i} is the sum over    *)
(* i < n of |H i| - 1, for subsets H i of G containing e.                    *)
let NSUM_CARD_SUBSETS_DELETE = prove
 (`!(G:K->bool) e (H:num->K->bool) n.
        FINITE G /\ (!i. i < n ==> H i SUBSET G /\ e IN H i)
        ==> nsum (G DELETE e) (\g. CARD {i | i < n /\ g IN H i}) =
            nsum {i | i < n} (\i. CARD(H i) - 1)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `nsum (G DELETE e)
      (\g:K. nsum {i | i < (n:num)} (\i. if g IN H i then 1 else 0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `g:K` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM NSUM_RESTRICT_SET] THEN
    SIMP_TAC[NSUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[IN_ELIM_THM; MULT_CLAUSES];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NSUM_SWAP o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG_LT] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM NSUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[NSUM_CONST; FINITE_RESTRICT; FINITE_DELETE; MULT_CLAUSES] THEN
  SUBGOAL_THEN
   `{g:K | g IN G DELETE e /\ g IN H i} = (H:num->K->bool) i DELETE e`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i:num < n`) o
      check (is_forall o concl)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE((H:num->K->bool) i) /\ e IN H i` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i:num < n`) o
      check (is_forall o concl)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `G:K->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_DELETE]);;

(* ------------------------------------------------------------------------- *)
(* The lower numbering groups through a local generator; Hilbert formula.    *)
(* ------------------------------------------------------------------------- *)

let INERTIA_GROUP_IDEAL_POW_LOCAL_GENERATOR = prove
 (`!(h:A->B) k l p Q a s f i.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
        a IN ring_carrier(ring_of_integers l) /\
        s IN ring_carrier(ring_of_integers k) /\ ~(s IN p) /\
        (!y. y IN ring_carrier(ring_of_integers l)
             ==> ring_mul l (h s) y IN
                 ring_carrier(subring_generated l
                   (a INSERT IMAGE h (ring_carrier(ring_of_integers k))))) /\
        f IN group_carrier(decomposition_group(k,l) h Q)
        ==> (f IN group_carrier(inertia_group(k,l) h (ring_of_integers l)
                                 (ideal_pow (ring_of_integers l) Q (i + 1))) <=>
             ring_sub l (f a) a IN ideal_pow (ring_of_integers l) Q (i + 1))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC
   `R = ring_carrier(subring_generated l
          (a INSERT IMAGE (h:A->B) (ring_carrier(ring_of_integers k))))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `f IN group_carrier(galois_group(k,l) (h:A->B))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)` THEN
    SIMP_TAC[DECOMPOSITION_GROUP; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `ring_of_integers l:B ring`;
                 `Q:B->bool`; `i:num`] INERTIA_GROUP_IDEAL_POW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING] THEN
    REWRITE_TAC[GALOIS_GROUP_RING_OF_INTEGERS];
    DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `J = ideal_pow (ring_of_integers l) Q (i + 1):B->bool` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_GROUP_RING_OF_INTEGERS) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!c. c IN ring_carrier k ==> (f:B->B)((h:A->B) c) = h c`
  ASSUME_TAC THENL
   [UNDISCH_TAC `f IN group_carrier(galois_group(k,l) (h:A->B))` THEN
    SIMP_TAC[IN_GALOIS_GROUP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN ring_carrier(ring_of_integers l) ==> (z:B) IN ring_carrier l`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `l:B ring` RING_OF_INTEGERS_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c IN ring_carrier(ring_of_integers k) ==> (c:A) IN ring_carrier k`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c IN ring_carrier(ring_of_integers k)
        ==> (h:A->B) c IN ring_carrier(ring_of_integers l)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
    EXISTS_TAC `ring_of_integers k:A ring` THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_ideal (ring_of_integers l) (J:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW]; ALL_TAC] THEN
  (* the elements z of O_l with f z == z mod J form a subring containing    *)
  (* O_k[a]                                                                 *)
  SUBGOAL_THEN
   `R SUBSET {z:B | z IN ring_carrier(ring_of_integers l) /\
                    ring_sub l (f z) z IN J}`
  ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INSERT_SUBSET; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:A` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[RING_SUB_REFL] THEN
      MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`]
        IN_RING_IDEAL_0) THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS];
      ALL_TAC] THEN
    REWRITE_TAC[subring_of; SUBSET; IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`]
      IN_RING_IDEAL_0) THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`]
      IN_RING_IDEAL_NEG) THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`]
      IN_RING_IDEAL_ADD) THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`]
      IN_RING_IDEAL_LMUL) THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`]
      IN_RING_IDEAL_RMUL) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN
    REPEAT DISCH_TAC THEN
    MP_TAC(ISPEC `l:B ring` (CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN
    REWRITE_TAC[subring_of] THEN STRIP_TAC THEN
    REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0
                 (ASSUME `ring_homomorphism(l,l) (f:B->B)`);
                MATCH_MP RING_HOMOMORPHISM_1
                 (ASSUME `ring_homomorphism(l,l) (f:B->B)`)] THEN
    ASM_SIMP_TAC[RING_SUB_REFL; RING_0; RING_1] THEN
    SUBGOAL_THEN
     `!z. z IN ring_carrier(ring_of_integers l)
          ==> (z:B) IN ring_carrier l /\ (f:B->B) z IN ring_carrier l /\
              f z IN ring_carrier(ring_of_integers l)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `z:B` THEN STRIP_TAC THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP
        (ASSUME `(z:B) IN ring_carrier(ring_of_integers l)`)) THEN
      ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_NEG
                    (ASSUME `ring_homomorphism(l,l) (f:B->B)`)] THEN
      SUBGOAL_THEN
       `ring_sub l (ring_neg l ((f:B->B) z)) (ring_neg l z) =
        ring_neg l (ring_sub l (f z) z)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(RING_RULE
         `ring_sub r (ring_neg r x) (ring_neg r y) =
          ring_neg r (ring_sub r x (y:B))`) THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`z:B`; `w:B`] THEN STRIP_TAC THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP
        (ASSUME `(z:B) IN ring_carrier(ring_of_integers l)`)) THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP
        (ASSUME `(w:B) IN ring_carrier(ring_of_integers l)`)) THEN
      ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_ADD
                    (ASSUME `ring_homomorphism(l,l) (f:B->B)`)] THEN
      SUBGOAL_THEN
       `ring_sub l (ring_add l ((f:B->B) z) (f w)) (ring_add l z w) =
        ring_add l (ring_sub l (f z) z) (ring_sub l (f w) w)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(RING_RULE
         `ring_sub r (ring_add r x u) (ring_add r y v) =
          ring_add r (ring_sub r x y) (ring_sub r u (v:B))`) THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`z:B`; `w:B`] THEN STRIP_TAC THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP
        (ASSUME `(z:B) IN ring_carrier(ring_of_integers l)`)) THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP
        (ASSUME `(w:B) IN ring_carrier(ring_of_integers l)`)) THEN
      ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
                    (ASSUME `ring_homomorphism(l,l) (f:B->B)`)] THEN
      SUBGOAL_THEN
       `ring_sub l (ring_mul l ((f:B->B) z) (f w)) (ring_mul l z w) =
        ring_add l (ring_mul l (ring_sub l (f z) z) (f w))
                   (ring_mul l z (ring_sub l (f w) w))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(RING_RULE
         `ring_sub r (ring_mul r x u) (ring_mul r y v) =
          ring_add r (ring_mul r (ring_sub r x y) u)
                     (ring_mul r y (ring_sub r u (v:B)))`) THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  (* cancel h(s) *)
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP
    (ASSUME `(x:B) IN ring_carrier(ring_of_integers l)`) o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `R:B->bool`)) (concl th) &&
      can (find_term ((=) `ring_mul l ((h:A->B) s)`)) (concl th))) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ring_mul l ((h:A->B) s) x` o
    REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `R:B->bool`)) (lhand(concl th)))) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h:A->B) s IN ring_carrier(ring_of_integers l) /\
                (f:B->B) x IN ring_carrier(ring_of_integers l)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `Q:B->bool`]
    NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((h:A->B) s IN Q)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((s:A) IN p)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o check
      (fun th -> is_eq(concl th) && rhs(concl th) = `p:A->bool`)) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `Q:B->bool`; `(h:A->B) s`;
                 `ring_sub l ((f:B->B) x) x`; `0`; `i + 1`]
    DEDEKIND_IDEAL_POW_MUL_CANCEL) THEN
  ASM_SIMP_TAC[RING_OF_INTEGERS; ADD_CLAUSES; DEDEKIND_RING_OF_INTEGERS;
               IDEAL_POW_1; PRIME_IMP_RING_IDEAL] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `ring_of_integers l:B ring` RING_SUB) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(x:B) IN ring_carrier l /\ (f:B->B) x IN ring_carrier l /\
    (h:A->B) s IN ring_carrier l /\ (s:A) IN ring_carrier k`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul l ((h:A->B) s) (ring_sub l ((f:B->B) x) x) =
    ring_sub l (f (ring_mul l (h s) x)) (ring_mul l (h s) x)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
                  (ASSUME `ring_homomorphism(l,l) (f:B->B)`)] THEN
    MATCH_MP_TAC(RING_RULE
     `ring_mul r t (ring_sub r u x) =
      ring_sub r (ring_mul r t u) (ring_mul r t (x:B))`) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* Hilbert formula when Q is the only prime of O_l above p.                  *)
let NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_ONE_PRIME = prove
 (`!(h:A->B) k l p Q n.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P} = {Q} /\
        group_carrier(inertia_group(k,l) h (ring_of_integers l)
                        (ideal_pow (ring_of_integers l) Q (n + 1))) = {I}
        ==> ideal_valuation (ring_of_integers l) Q
              (number_field_different (k,l) h) =
            nsum {i | i < n}
              (\i. CARD(group_carrier(inertia_group(k,l) h (ring_of_integers l)
                          (ideal_pow (ring_of_integers l) Q (i + 1)))) - 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `field k /\ ring_homomorphism(k,l) (h:A->B)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
    SIMP_TAC[field_extension; RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `prime_ideal (ring_of_integers l) (Q:B->bool) /\ IMAGE (h:A->B) p SUBSET Q`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `Q:B->bool` o
      REWRITE_RULE[EXTENSION; IN_ELIM_THM; IN_SING] o check (fun th ->
        is_eq(concl th) && rhs(concl th) = `{Q:B->bool}`)) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `Q:B->bool`]
    NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_SEPARABLE_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD o
    check (fun th -> concl th = `number_field(l:B ring)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_RING_OF_INTEGERS o
    check (fun th -> concl th = `number_field(l:B ring)`)) THEN
  ABBREV_TAC `G = group_carrier(galois_group(k,l) (h:A->B))` THEN
  (* D_Q = G *)
  SUBGOAL_THEN
   `!f. f IN group_carrier(decomposition_group(k,l) (h:A->B) Q) <=> f IN G`
  ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[DECOMPOSITION_GROUP] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `f:B->B` THEN
    EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Q:B->bool) SUBSET ring_carrier(ring_of_integers l)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[PRIME_IDEAL_IMP_SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                   `ring_of_integers l:B ring`; `f:B->B`; `Q:B->bool`]
      GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING; GALOIS_GROUP_RING_OF_INTEGERS;
                    PRIME_IDEAL_IMP_SUBSET] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE (f:B->B) Q IN
                  {P | prime_ideal (ring_of_integers l) P /\
                       IMAGE (h:A->B) p SUBSET P}`
    MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `c:A` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN
       `(c:A) IN {a | a IN ring_carrier k /\ (h:A->B) a IN IMAGE (f:B->B) Q}`
      MP_TAC THENL
       [ASM_REWRITE_TAC[];
        SIMP_TAC[IN_ELIM_THM]];
      ASM_REWRITE_TAC[IN_SING]];
    ALL_TAC] THEN
  (* the local power basis *)
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `Q:B->bool`]
    NUMBER_FIELD_LOCAL_POWER_BASIS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:B` (X_CHOOSE_THEN `s:A` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `a:B`;
                 `s:A`; `Q:B->bool`]
    NUMBER_FIELD_DIFFERENT_LOCAL_POWER_BASIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(a:B) IN ring_carrier l` ASSUME_TAC THENL
   [MP_TAC(ISPEC `l:B ring` RING_OF_INTEGERS_SUBSET) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
    GALOIS_PRIMITIVE_ELEMENT_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) SUBST1_TAC) THEN
  SUBGOAL_THEN `FINITE(G:(B->B)->bool) /\ (I:B->B) IN G` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN ASM_SIMP_TAC[FINITE_GALOIS_GROUP; GALOIS_GROUP_I];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f. f IN G
        ==> (f:B->B) a IN ring_carrier(ring_of_integers l) /\
            ring_sub l a (f a) IN ring_carrier(ring_of_integers l)`
  ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_GROUP_RING_OF_INTEGERS) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `a:B`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `ring_of_integers l:B ring` RING_SUB) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f. f IN G /\ ~(f = I) ==> ~(ring_sub l a ((f:B->B) a) = ring_0 l)`
  ASSUME_TAC THENL
   [X_GEN_TAC `f:B->B` THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(f:B->B) IN G`)) THEN
    SUBGOAL_THEN `(f:B->B) a IN ring_carrier l` ASSUME_TAC THENL
     [MP_TAC(ISPEC `l:B ring` RING_OF_INTEGERS_SUBSET) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`; `a:B`; `(f:B->B) a`] RING_SUB_EQ_0) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~(f:B->B = I)` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
      GALOIS_PRIMITIVE_ELEMENT_DERIVATIVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`f:B->B`; `I:B->B`] o CONJUNCT1) THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(f:B->B) IN G` THEN EXPAND_TAC "G" THEN SIMP_TAC[];
      REWRITE_TAC[GALOIS_GROUP_I];
      REWRITE_TAC[I_THM] THEN FIRST_ASSUM(ACCEPT_TAC o SYM)];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `G DELETE (I:B->B)`;
                 `\f:B->B. ring_sub l a (f a)`]
    RING_PRODUCT_RING_OF_INTEGERS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_DELETE] THEN X_GEN_TAC `f:B->B` THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(f:B->B) IN G`)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `Q:B->bool`;
                 `\f:B->B. ring_sub l a (f a)`; `G DELETE (I:B->B)`]
    IDEAL_VALUATION_PRINCIPAL_PRODUCT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE; RING_OF_INTEGERS] THEN
    X_GEN_TAC `f:B->B` THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(f:B->B) IN G`)) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  (* each term: the valuation counts the G_i containing f *)
  MP_TAC(ISPECL [`G:(B->B)->bool`; `I:B->B`;
                 `\i. group_carrier(inertia_group(k,l) (h:A->B)
                        (ring_of_integers l)
                        (ideal_pow (ring_of_integers l) Q (i + 1)))`; `n:num`]
    NSUM_CARD_SUBSETS_DELETE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [EXPAND_TAC "G" THEN REWRITE_TAC[inertia_group] THEN
      REWRITE_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET];
      MP_TAC(ISPEC
       `inertia_group(k,l) (h:A->B) (ring_of_integers l)
          (ideal_pow (ring_of_integers l) Q (i + 1))` GROUP_ID) THEN
      REWRITE_TAC[CONJUNCT1(CONJUNCT2 INERTIA_GROUP)]];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `f:B->B` THEN
  REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(f:B->B) IN G`)) THEN
  SUBGOAL_THEN `~(ring_sub l a ((f:B->B) a) = ring_0 l)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `v = ideal_valuation (ring_of_integers l) Q
          (ideal_generated (ring_of_integers l)
             {ring_sub l a ((f:B->B) a)})` THEN
  SUBGOAL_THEN
   `!i. (f:B->B) IN group_carrier(inertia_group(k,l) (h:A->B)
                    (ring_of_integers l)
                    (ideal_pow (ring_of_integers l) Q (i + 1))) <=>
        i + 1 <= v`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`;
                   `Q:B->bool`; `a:B`; `s:A`; `f:B->B`; `i:num`]
      INERTIA_GROUP_IDEAL_POW_LOCAL_GENERATOR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`;
                   `ideal_pow (ring_of_integers l) Q (i + 1):B->bool`;
                   `(f:B->B) a`; `a:B`] IN_RING_IDEAL_SUB_SYM) THEN
    REWRITE_TAC[RING_IDEAL_IDEAL_POW; RING_OF_INTEGERS] THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "v" THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `Q:B->bool`;
                   `ring_sub l a ((f:B->B) a)`; `i + 1`]
      DEDEKIND_IN_IDEAL_POW_VALUATION) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `v:num <= n` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(n + 1 <= v) ==> v:num <= n`) THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `v:num`)) (concl th))) THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `{I:B->B}`)) THEN
    REWRITE_TAC[IN_SING] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `i + 1 <= v <=> i < v`] THEN
  SUBGOAL_THEN `{i | i < (n:num) /\ i < v} = {i | i < v}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    UNDISCH_TAC `v:num <= n` THEN ARITH_TAC;
    REWRITE_TAC[CARD_NUMSEG_LT]]);;

(* Hilbert formula: v_Q(D) is the sum of the |G_i| - 1 over i < n, for any n *)
(* with G_n = 1.                                                             *)
let NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_LT = prove
 (`!(h:A->B) k l p Q n.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
        group_carrier(inertia_group(k,l) h (ring_of_integers l)
                        (ideal_pow (ring_of_integers l) Q (n + 1))) = {I}
        ==> ideal_valuation (ring_of_integers l) Q
              (number_field_different (k,l) h) =
            nsum {i | i < n}
              (\i. CARD(group_carrier(inertia_group(k,l) h (ring_of_integers l)
                          (ideal_pow (ring_of_integers l) Q (i + 1)))) - 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `field k /\ ring_homomorphism(k,l) (h:A->B)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
    SIMP_TAC[field_extension; RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  ABBREV_TAC
   `z = fixed_field l (group_carrier(decomposition_group(k,l) (h:A->B) Q))` THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `Q:B->bool`;
                 `z:B->bool`] NUMBER_FIELD_DECOMPOSITION_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `z:B->bool`]
    NUMBER_FIELD_INTERMEDIATE_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `z:B->bool`; `p:A->bool`;
                 `Q:B->bool`] NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD o
    check (fun th -> concl th = `number_field(l:B ring)`)) THEN
  SUBGOAL_THEN
   `~(Q INTER z = {ring_0(subfield_generated l (z:B->bool))}) /\
    dedekind_domain(ring_of_integers(subfield_generated l (z:B->bool))) /\
    dedekind_domain(ring_of_integers(l:B ring)) /\
    ~(Q = {ring_0(l:B ring)})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT1(CONJUNCT2 SUBFIELD_GENERATED)] THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `Q:B->bool`]
      NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* l is Galois over the decomposition field *)
  SUBGOAL_THEN `galois_extension(subfield_generated l z,l) (I:B->B)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                   `subfield_generated l (z:B->bool)`; `l:B ring`]
      GALOIS_EXTENSION_INTERMEDIATE) THEN
    REWRITE_TAC[I_O_ID; field_extension] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the tower of differents *)
  MP_TAC(ISPECL [`k:A ring`; `subfield_generated l (z:B->bool)`; `l:B ring`;
                 `h:A->B`; `I:B->B`] NUMBER_FIELD_DIFFERENT_TOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[I_O_ID]] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`subfield_generated l (z:B->bool)`; `l:B ring`; `I:B->B`;
                 `number_field_different (k,subfield_generated l z)
                    (h:A->B)`] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RING_IDEAL_NUMBER_FIELD_DIFFERENT];
    DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  MP_TAC(ISPECL [`k:A ring`; `subfield_generated l (z:B->bool)`; `h:A->B`]
    NUMBER_FIELD_DIFFERENT_NONZERO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`subfield_generated l (z:B->bool)`; `l:B ring`; `I:B->B`]
    NUMBER_FIELD_DIFFERENT_NONZERO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `Q:B->bool`;
                 `number_field_different (subfield_generated l z,l) (I:B->B)`;
                 `ideal_generated (ring_of_integers l)
                    (IMAGE (I:B->B)
                      (number_field_different (k,subfield_generated l z)
                         (h:A->B)))`]
    IDEAL_VALUATION_IDEAL_PROD) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS; RING_IDEAL_NUMBER_FIELD_DIFFERENT;
                RING_IDEAL_IDEAL_GENERATED] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  (* the decomposition field part is unramified at Q *)
  SUBGOAL_THEN
   `ideal_valuation (ring_of_integers l) Q
      (ideal_generated (ring_of_integers l)
         (IMAGE (I:B->B)
           (number_field_different (k,subfield_generated l z) (h:A->B)))) =
    0`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`subfield_generated l (z:B->bool)`; `l:B ring`; `I:B->B`;
                   `Q INTER (z:B->bool)`; `Q:B->bool`;
                   `number_field_different (k,subfield_generated l z)
                      (h:A->B)`]
      NUMBER_FIELD_IDEAL_VALUATION_EXTENSION) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[RING_IDEAL_NUMBER_FIELD_DIFFERENT; IMAGE_I] THEN
      SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[MULT_EQ_0] THEN DISJ2_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers(subfield_generated l (z:B->bool))`;
                   `Q INTER (z:B->bool)`;
                   `number_field_different (k,subfield_generated l z)
                      (h:A->B)`; `1`]
      DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[RING_OF_INTEGERS; RING_IDEAL_NUMBER_FIELD_DIFFERENT];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ring_of_integers(subfield_generated l (z:B->bool))`;
                   `Q INTER (z:B->bool)`] IDEAL_POW_1) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC PRIME_IMP_RING_IDEAL THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `subfield_generated l (z:B->bool)`; `h:A->B`;
                   `Q INTER (z:B->bool)`]
      NUMBER_FIELD_DIFFERENT_RAMIFIED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REWRITE_TAC[ADD_CLAUSES]] THEN
  (* the formula over the decomposition field *)
  SUBGOAL_THEN
   `!i. group_carrier(inertia_group(subfield_generated l z,l) (I:B->B)
                       (ring_of_integers l)
                       (ideal_pow (ring_of_integers l) Q (i + 1))) =
        group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l)
                       (ideal_pow (ring_of_integers l) Q (i + 1)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                   `ring_of_integers l:B ring`; `z:B->bool`;
                   `ideal_pow (ring_of_integers l) Q (i + 1):B->bool`]
      INERTIA_GROUP_INTERMEDIATE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING; RING_IDEAL_IDEAL_POW;
                      GALOIS_GROUP_RING_OF_INTEGERS];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[SET_RULE `(s:(B->B)->bool) INTER t = s <=> s SUBSET t`] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                   `ring_of_integers l:B ring`; `Q:B->bool`; `i:num`]
      INERTIA_GROUP_IDEAL_POW) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING; GALOIS_GROUP_RING_OF_INTEGERS];
      DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:B->B`; `subfield_generated l (z:B->bool)`; `l:B ring`;
                 `Q INTER (z:B->bool)`; `Q:B->bool`; `n:num`]
    NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_ONE_PRIME) THEN
  ASM_REWRITE_TAC[IMAGE_I]);;

(* Hilbert formula, as the sum over all i >= 0 (the G_i are 1 for large i).  *)
let NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA = prove
 (`!(h:A->B) k l p Q.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> ideal_valuation (ring_of_integers l) Q
              (number_field_different (k,l) h) =
            nsum (:num)
              (\i. CARD(group_carrier(inertia_group(k,l) h (ring_of_integers l)
                          (ideal_pow (ring_of_integers l) Q (i + 1)))) - 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `field k /\ ring_homomorphism(k,l) (h:A->B)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_IMP_FIELD_EXTENSION; field_extension;
                  RING_MONOMORPHISM_IMP_HOMOMORPHISM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `Q:B->bool`]
    NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `ring_of_integers l:B ring`; `Q:B->bool`]
    INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING;
                    GALOIS_GROUP_RING_OF_INTEGERS] THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      NUMBER_FIELD_TOWER_LAW) THEN
    MP_TAC(ISPEC `l:B ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `n:num`)] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `Q:B->bool`;
                 `n:num`] NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_LT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN
  REWRITE_TAC[SUBSET_UNIV; IN_UNIV; IN_ELIM_THM; NOT_LT] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CARD_SING; SUB_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The tame exponent of the relative different, through a Galois closure.    *)
(* ------------------------------------------------------------------------- *)

(* For k -> l -> m with m Galois over k and P above Q above p, e(P|Q)        *)
(* v_Q(D_(l/k)) is the sum of the |G_i| - |G_i INTER Gal(m/l)|, G_i the      *)
(* lower numbering groups of P over k.                                       *)
let NUMBER_FIELD_DIFFERENT_VALUATION_GALOIS_OVERFIELD = prove
 (`!k:A ring l:B ring m:C ring h j p Q P n.
        field l /\ number_field m /\
        ring_homomorphism(k,l) h /\ ring_homomorphism(l,m) j /\
        galois_extension(k,m) (j o h) /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
        prime_ideal (ring_of_integers m) P /\ IMAGE j Q SUBSET P /\
        group_carrier(inertia_group(k,m) (j o h) (ring_of_integers m)
                       (ideal_pow (ring_of_integers m) P (n + 1))) = {I}
        ==> ramification_index (ring_of_integers l,ring_of_integers m) j P *
            ideal_valuation (ring_of_integers l) Q
              (number_field_different (k,l) h) =
            nsum {i | i < n}
             (\i. CARD(group_carrier(inertia_group(k,m) (j o h)
                         (ring_of_integers m)
                         (ideal_pow (ring_of_integers m) P (i + 1)))) -
                  CARD(group_carrier(inertia_group(l,m) j
                         (ring_of_integers m)
                         (ideal_pow (ring_of_integers m) P (i + 1)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `field(k:A ring)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
    SIMP_TAC[field_extension];
    ALL_TAC] THEN
  SUBGOAL_THEN `number_field(l:B ring)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `j:B->C`]
      NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD o
    check (fun th -> concl th = `number_field(m:C ring)`)) THEN
  SUBGOAL_THEN `ring_homomorphism(k,m) ((j:B->C) o (h:A->B))` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((j:B->C) o (h:A->B)) p SUBSET P` ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (j:B->C) Q` THEN ASM_SIMP_TAC[IMAGE_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `galois_extension(l,m) (j:B->C)` ASSUME_TAC THENL
   [MATCH_MP_TAC GALOIS_EXTENSION_INTERMEDIATE THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`] THEN
    ASM_REWRITE_TAC[field_extension] THEN
    CONJ_TAC THEN MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Q = {ring_0(l:B ring)})` ASSUME_TAC THENL
   [MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `h:A->B`; `p:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(group_carrier(galois_group(k,m) ((j:B->C) o (h:A->B)))) /\
    (I:C->C) IN group_carrier(galois_group(l,m) j)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GALOIS_GROUP_I] THEN MATCH_MP_TAC FINITE_GALOIS_GROUP THEN
    MP_TAC(ISPECL [`k:A ring`; `m:C ring`; `(j:B->C) o (h:A->B)`]
      NUMBER_FIELD_TOWER_LAW) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the inertia groups over l *)
  SUBGOAL_THEN
   `!i. group_carrier(inertia_group(l,m) (j:B->C) (ring_of_integers m)
                       (ideal_pow (ring_of_integers m) P (i + 1))) =
        group_carrier(inertia_group(k,m) (j o (h:A->B)) (ring_of_integers m)
                       (ideal_pow (ring_of_integers m) P (i + 1))) INTER
        group_carrier(galois_group(l,m) j)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INERTIA_GROUP_TOWER THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING; RING_IDEAL_IDEAL_POW;
                    GALOIS_GROUP_RING_OF_INTEGERS];
    ALL_TAC] THEN
  (* the two Hilbert formulae *)
  MP_TAC(ISPECL [`j:B->C`; `l:B ring`; `m:C ring`; `Q:B->bool`; `P:C->bool`;
                 `n:num`] NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_LT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SET_RULE `{a:C->C} INTER s = {a} <=> a IN s`];
    DISCH_THEN(LABEL_TAC "hl")] THEN
  MP_TAC(ISPECL [`(j:B->C) o (h:A->B)`; `k:A ring`; `m:C ring`; `p:A->bool`;
                 `P:C->bool`; `n:num`]
    NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_LT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "hk")] THEN
  (* the tower of differents *)
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `m:C ring`; `h:A->B`; `j:B->C`]
    NUMBER_FIELD_DIFFERENT_TOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "tower")] THEN
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `j:B->C`;
                 `number_field_different (k,l) (h:A->B)`]
    RING_OF_INTEGERS_IDEAL_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RING_IDEAL_NUMBER_FIELD_DIFFERENT];
    DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_DIFFERENT_NONZERO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `j:B->C`]
    NUMBER_FIELD_DIFFERENT_NONZERO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers m:C ring`; `P:C->bool`;
                 `number_field_different (l,m) (j:B->C)`;
                 `ideal_generated (ring_of_integers m)
                    (IMAGE (j:B->C) (number_field_different (k,l) (h:A->B)))`]
    IDEAL_VALUATION_IDEAL_PROD) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS; RING_IDEAL_NUMBER_FIELD_DIFFERENT;
                RING_IDEAL_IDEAL_GENERATED] THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS] THEN
    MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `(j:B->C) o (h:A->B)`; `p:A->bool`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(LABEL_TAC "prod")] THEN
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `j:B->C`; `Q:B->bool`; `P:C->bool`;
                 `number_field_different (k,l) (h:A->B)`]
    NUMBER_FIELD_IDEAL_VALUATION_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RING_IDEAL_NUMBER_FIELD_DIFFERENT];
    DISCH_THEN(LABEL_TAC "ext")] THEN
  (* compare the two sums *)
  SUBGOAL_THEN
   `!i. CARD(group_carrier(inertia_group(k,m) ((j:B->C) o (h:A->B))
              (ring_of_integers m)
              (ideal_pow (ring_of_integers m) P (i + 1)))) - 1 =
        (CARD(group_carrier(inertia_group(l,m) j (ring_of_integers m)
              (ideal_pow (ring_of_integers m) P (i + 1)))) - 1) +
        (CARD(group_carrier(inertia_group(k,m) (j o h) (ring_of_integers m)
              (ideal_pow (ring_of_integers m) P (i + 1)))) -
         CARD(group_carrier(inertia_group(l,m) j (ring_of_integers m)
              (ideal_pow (ring_of_integers m) P (i + 1)))))`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `i:num` THEN
    MATCH_MP_TAC(ARITH_RULE
     `1 <= b /\ b:num <= a ==> a - 1 = (b - 1) + (a - b)`) THEN
    SUBGOAL_THEN
     `FINITE(group_carrier(inertia_group(k,m) ((j:B->C) o (h:A->B))
        (ring_of_integers m) (ideal_pow (ring_of_integers m) P (i + 1))))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `group_carrier(galois_group(k,m) ((j:B->C) o (h:A->B)))` THEN
      ASM_REWRITE_TAC[inertia_group; GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n:num = 0)`] THEN
      ASM_SIMP_TAC[CARD_EQ_0; FINITE_INTER] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `I:C->C` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `i:num` o check (fun th ->
        is_forall(concl th) && is_eq(snd(dest_forall(concl th))))) THEN
      MP_TAC(ISPEC
       `inertia_group(l,m) (j:B->C) (ring_of_integers m)
          (ideal_pow (ring_of_integers m) P (i + 1))` GROUP_ID) THEN
      REWRITE_TAC[CONJUNCT1(CONJUNCT2 INERTIA_GROUP)];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_REWRITE_TAC[INTER_SUBSET]];
    ALL_TAC] THEN
  REMOVE_THEN "hk" MP_TAC THEN REMOVE_THEN "tower" SUBST1_TAC THEN
  REMOVE_THEN "prod" SUBST1_TAC THEN REMOVE_THEN "hl" SUBST1_TAC THEN
  REMOVE_THEN "ext" SUBST1_TAC THEN
  REMOVE_THEN "pt" (fun th -> REWRITE_TAC[th]) THEN
  SIMP_TAC[NSUM_ADD; FINITE_NUMSEG_LT] THEN ARITH_TAC);;

(* The exponent of Q in the different of any extension of number fields:     *)
(* v_Q(D) = e - 1 iff the residue characteristic does not divide e = e(Q|p), *)
(* otherwise v_Q(D) >= e.                                                    *)
let NUMBER_FIELD_DIFFERENT_VALUATION_TAME,
    NUMBER_FIELD_DIFFERENT_VALUATION_WILD = (CONJ_PAIR o prove)
 (`(!k:A ring l:B ring h p Q.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> ramification_index (ring_of_integers k,ring_of_integers l) h Q - 1
            <= ideal_valuation (ring_of_integers l) Q
                 (number_field_different (k,l) h) /\
            (ideal_valuation (ring_of_integers l) Q
               (number_field_different (k,l) h) =
             ramification_index (ring_of_integers k,ring_of_integers l) h Q - 1
             <=> ~(ring_char(quotient_ring (ring_of_integers l) Q) divides
                   ramification_index (ring_of_integers k,ring_of_integers l)
                                      h Q))) /\
   (!k:A ring l:B ring h p Q.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> (ramification_index (ring_of_integers k,ring_of_integers l) h Q <=
             ideal_valuation (ring_of_integers l) Q
               (number_field_different (k,l) h) <=>
             ring_char(quotient_ring (ring_of_integers l) Q) divides
             ramification_index (ring_of_integers k,ring_of_integers l) h Q))`,
  let core = prove
   (`!k:A ring l:B ring h p Q.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> 1 <= ramification_index (ring_of_integers k,ring_of_integers l)
                   h Q /\
            (~(ring_char(quotient_ring (ring_of_integers l) Q) divides
               ramification_index (ring_of_integers k,ring_of_integers l) h Q)
             ==> ideal_valuation (ring_of_integers l) Q
                   (number_field_different (k,l) h) =
                 ramification_index (ring_of_integers k,ring_of_integers l)
                   h Q - 1) /\
            (ring_char(quotient_ring (ring_of_integers l) Q) divides
             ramification_index (ring_of_integers k,ring_of_integers l) h Q
             ==> ramification_index (ring_of_integers k,ring_of_integers l)
                   h Q <=
                 ideal_valuation (ring_of_integers l) Q
                   (number_field_different (k,l) h))`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD o
      check (fun th -> concl th = `number_field(l:B ring)`)) THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      NUMBER_FIELD_GALOIS_CLOSURE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:(B#num)ring`
      (X_CHOOSE_THEN `j:B->B#num` STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD o
      check (fun th -> concl th = `number_field(m:(B#num)ring)`)) THEN
    SUBGOAL_THEN `~(Q = {ring_0(l:B ring)})` ASSUME_TAC THENL
     [MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN
      MAP_EVERY EXISTS_TAC [`k:A ring`; `h:A->B`; `p:A->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    (* a prime P of the Galois closure above Q *)
    SUBGOAL_THEN
     `?P. prime_ideal (ring_of_integers m) P /\
          IMAGE (j:B->B#num) Q SUBSET P`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`l:B ring`; `m:(B#num)ring`; `j:B->B#num`; `Q:B->bool`]
        RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPECL [`ring_of_integers m:(B#num)ring`;
                     `ideal_generated (ring_of_integers m)
                        (IMAGE (j:B->B#num) Q)`]
        MAXIMAL_SUPERIDEAL_EXISTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[proper_ideal; PSUBSET; RING_IDEAL_IDEAL_GENERATED;
                        IDEAL_GENERATED_SUBSET];
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `P:B#num->bool` THEN
      STRIP_TAC THEN ASM_SIMP_TAC[MAXIMAL_IMP_PRIME_IDEAL] THEN
      TRANS_TAC SUBSET_TRANS
       `ideal_generated (ring_of_integers m) (IMAGE (j:B->B#num) Q)` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`ring_of_integers m:(B#num)ring`;
                     `IMAGE (j:B->B#num) Q`]
        IDEAL_GENERATED_SUBSET_CARRIER) THEN
      MATCH_MP_TAC(SET_RULE
       `(s:B#num->bool) SUBSET c ==> c INTER s SUBSET g ==> s SUBSET g`) THEN
      TRANS_TAC SUBSET_TRANS
       `IMAGE (j:B->B#num) (ring_carrier(ring_of_integers l))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_SIMP_TAC[PRIME_IDEAL_IMP_SUBSET];
        MP_TAC(ISPECL [`l:B ring`; `m:(B#num)ring`; `j:B->B#num`]
          RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[ring_homomorphism]];
      ALL_TAC] THEN
    SUBGOAL_THEN `ring_homomorphism(k,m) ((j:B->B#num) o (h:A->B))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE ((j:B->B#num) o (h:A->B)) p SUBSET P` ASSUME_TAC THENL
     [REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (j:B->B#num) Q` THEN ASM_SIMP_TAC[IMAGE_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `galois_extension(l,m) (j:B->B#num)` ASSUME_TAC THENL
     [MATCH_MP_TAC GALOIS_EXTENSION_INTERMEDIATE THEN
      MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`] THEN
      ASM_REWRITE_TAC[field_extension] THEN
      CONJ_TAC THEN MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
      ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(j:B->B#num) o (h:A->B)`; `k:A ring`; `m:(B#num)ring`;
                   `p:A->bool`; `P:B#num->bool`]
      NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN
     `finite_extension(k,m) ((j:B->B#num) o (h:A->B)) /\
      dedekind_domain(ring_of_integers m:(B#num)ring) /\
      field_of_fractions(ring_of_integers m:(B#num)ring,m) I`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `m:(B#num)ring`; `(j:B->B#num) o (h:A->B)`]
        NUMBER_FIELD_TOWER_LAW) THEN
      MP_TAC(ISPEC `m:(B#num)ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    (* the residue characteristics agree *)
    SUBGOAL_THEN
     `ring_char(quotient_ring (ring_of_integers m) (P:B#num->bool)) =
      ring_char(quotient_ring (ring_of_integers l) (Q:B->bool))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`l:B ring`; `Q:B->bool`]
        RING_OF_INTEGERS_PRIME_IDEAL_ABOVE) THEN
      ASM_REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC o CONJUNCT1) THEN
      SUBGOAL_THEN `ring_of_num m q IN (P:B#num->bool)` ASSUME_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `q:num` o
          MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM o check (fun th ->
            concl th = `ring_homomorphism(l,m) (j:B->B#num)`)) THEN
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          concl th = `IMAGE (j:B->B#num) Q SUBSET P`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`ring_of_integers l:B ring`; `Q:B->bool`; `q:num`]
        RING_OF_NUM_IN_PRIME_IDEAL) THEN
      MP_TAC(ISPECL [`ring_of_integers m:(B#num)ring`; `P:B#num->bool`;
                     `q:num`] RING_OF_NUM_IN_PRIME_IDEAL) THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN MESON_TAC[];
      ALL_TAC] THEN
    (* the orders of the inertia groups *)
    MP_TAC(ISPECL [`(j:B->B#num) o (h:A->B)`; `k:A ring`; `m:(B#num)ring`;
                   `p:A->bool`; `P:B#num->bool`]
      NUMBER_FIELD_DECOMPOSITION_GROUP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2)] THEN
    MP_TAC(ISPECL [`j:B->B#num`; `l:B ring`; `m:(B#num)ring`;
                   `Q:B->bool`; `P:B#num->bool`]
      NUMBER_FIELD_DECOMPOSITION_GROUP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2)] THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `m:(B#num)ring`; `h:A->B`;
                   `j:B->B#num`; `Q:B->bool`; `P:B#num->bool`]
      NUMBER_FIELD_RAMIFICATION_INDEX_TOWER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    (* the inertia group over l is a subgroup of that over k *)
    SUBGOAL_THEN
     `group_carrier(inertia_group(l,m) (j:B->B#num) (ring_of_integers m) P)
      subgroup_of inertia_group(k,m) (j o (h:A->B)) (ring_of_integers m) P`
    ASSUME_TAC THENL
     [REWRITE_TAC[subgroup_of; CONJUNCT2 INERTIA_GROUP] THEN
      MP_TAC(ISPEC `inertia_group(l,m) (j:B->B#num) (ring_of_integers m) P`
        GROUP_ID) THEN
      MP_TAC(ISPEC `inertia_group(l,m) (j:B->B#num) (ring_of_integers m) P`
        GROUP_INV) THEN
      MP_TAC(ISPEC `inertia_group(l,m) (j:B->B#num) (ring_of_integers m) P`
        GROUP_MUL) THEN
      REWRITE_TAC[CONJUNCT2 INERTIA_GROUP] THEN
      REPEAT DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL [`h:A->B`; `j:B->B#num`; `k:A ring`; `l:B ring`;
                     `m:(B#num)ring`; `ring_of_integers m:(B#num)ring`;
                     `P:B#num->bool`] INERTIA_GROUP_TOWER) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[RING_OF_INTEGERS_SUBRING; PRIME_IMP_RING_IDEAL] THEN
        REWRITE_TAC[GALOIS_GROUP_RING_OF_INTEGERS];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INTER_SUBSET]];
      ALL_TAC] THEN
    (* the wild group lies in it iff p does not divide e(Q|p) *)
    MP_TAC(ISPECL [`(j:B->B#num) o (h:A->B)`; `k:A ring`; `m:(B#num)ring`;
                   `ring_of_integers m:(B#num)ring`; `P:B#num->bool`;
                   `group_carrier(inertia_group(l,m) (j:B->B#num)
                      (ring_of_integers m) P)`;
                   `ramification_index (ring_of_integers k,ring_of_integers l)
                      (h:A->B) Q`]
      INERTIA_GROUP_WILD_SUBSET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING;
                      GALOIS_GROUP_RING_OF_INTEGERS] THEN
      REWRITE_TAC[MULT_AC];
      ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
    (* the lower numbering groups are eventually trivial *)
    MP_TAC(ISPECL [`(j:B->B#num) o (h:A->B)`; `k:A ring`; `m:(B#num)ring`;
                   `ring_of_integers m:(B#num)ring`; `P:B#num->bool`]
      INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING; GALOIS_GROUP_RING_OF_INTEGERS];
      DISCH_THEN(X_CHOOSE_TAC `N:num`)] THEN
    (* the different through the Galois closure *)
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `m:(B#num)ring`; `h:A->B`;
                   `j:B->B#num`; `p:A->bool`; `Q:B->bool`; `P:B#num->bool`;
                   `N + 1`]
      NUMBER_FIELD_DIFFERENT_VALUATION_GALOIS_OVERFIELD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      DISCH_TAC] THEN
    (* now in terms of the groups G i and G1 i *)
    ABBREV_TAC
     `G = \i. group_carrier(inertia_group(k,m) ((j:B->B#num) o (h:A->B))
                (ring_of_integers m)
                (ideal_pow (ring_of_integers m) P (i + 1)))` THEN
    ABBREV_TAC
     `G' = \i. group_carrier(inertia_group(l,m) (j:B->B#num)
                (ring_of_integers m)
                (ideal_pow (ring_of_integers m) P (i + 1)))` THEN
    SUBGOAL_THEN
     `(!i. (G:num->(B#num->B#num)->bool) i =
           group_carrier(inertia_group(k,m) ((j:B->B#num) o (h:A->B))
              (ring_of_integers m)
              (ideal_pow (ring_of_integers m) P (i + 1)))) /\
      (!i. (G':num->(B#num->B#num)->bool) i =
           group_carrier(inertia_group(l,m) (j:B->B#num)
              (ring_of_integers m)
              (ideal_pow (ring_of_integers m) P (i + 1))))`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["G"; "G'"] THEN REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `H = group_carrier(galois_group(l,m) (j:B->B#num))` THEN
    ABBREV_TAC
     `e1 = ramification_index (ring_of_integers l,ring_of_integers m)
             (j:B->B#num) P` THEN
    ABBREV_TAC
     `e2 = ramification_index (ring_of_integers k,ring_of_integers l)
             (h:A->B) Q` THEN
    ABBREV_TAC
     `v = ideal_valuation (ring_of_integers l) Q
            (number_field_different (k,l) (h:A->B))` THEN
    ABBREV_TAC
     `c = ring_char(quotient_ring (ring_of_integers l) (Q:B->bool))` THEN
    SUBGOAL_THEN
     `(!i. (G':num->(B#num->B#num)->bool) i = G i INTER H) /\
      (!i. FINITE((G:num->(B#num->B#num)->bool) i)) /\
      (!i i'. i <= i' ==> (G:num->(B#num->B#num)->bool) i' SUBSET G i) /\
      (!i. (I:B#num->B#num) IN G' i) /\
      CARD((G:num->(B#num->B#num)->bool) 0) = e1 * e2 /\
      CARD((G':num->(B#num->B#num)->bool) 0) = e1 /\
      (G 1 SUBSET G' 0 <=> ~(c divides e2)) /\
      (!i. N <= i ==> G i = {I:B#num->B#num}) /\
      e1 * v = nsum {i | i < N + 1} (\i. CARD(G i) - CARD(G' i))`
    MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN GEN_TAC THEN EXPAND_TAC "H" THEN
        MATCH_MP_TAC INERTIA_GROUP_TOWER THEN
        ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING; RING_IDEAL_IDEAL_POW;
                        GALOIS_GROUP_RING_OF_INTEGERS];
        ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC
         `group_carrier(galois_group(k,m) ((j:B->B#num) o (h:A->B)))` THEN
        REWRITE_TAC[inertia_group; GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET] THEN
        ASM_SIMP_TAC[FINITE_GALOIS_GROUP];
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC INERTIA_GROUP_IDEAL_POW_MONO THEN
        ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING;
                        GALOIS_GROUP_RING_OF_INTEGERS];
        ASM_REWRITE_TAC[] THEN GEN_TAC THEN
        MP_TAC(ISPEC
         `inertia_group(l,m) (j:B->B#num) (ring_of_integers m)
            (ideal_pow (ring_of_integers m) P (i + 1))` GROUP_ID) THEN
        REWRITE_TAC[CONJUNCT1(CONJUNCT2 INERTIA_GROUP)];
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_SIMP_TAC[IDEAL_POW_1; PRIME_IMP_RING_IDEAL];
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_SIMP_TAC[IDEAL_POW_1; PRIME_IMP_RING_IDEAL];
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_SIMP_TAC[IDEAL_POW_1; PRIME_IMP_RING_IDEAL];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(I:B#num->B#num) IN H /\
      (!i. (I:B#num->B#num) IN (G:num->(B#num->B#num)->bool) i) /\
      (!i. FINITE((G':num->(B#num->B#num)->bool) i))`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_INTER; FINITE_INTER]; ALL_TAC] THEN
    SUBGOAL_THEN `~(e1:num = 0) /\ ~(e2:num = 0)` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `(G':num->(B#num->B#num)->bool) 0` CARD_EQ_0) THEN
      MP_TAC(ISPEC `(G:num->(B#num->B#num)->bool) 0` CARD_EQ_0) THEN
      ASM_REWRITE_TAC[MULT_EQ_0] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    (* split off the term i = 0 *)
    MP_TAC(ISPECL
     [`\i. CARD((G:num->(B#num->B#num)->bool) i) -
           CARD((G':num->(B#num->B#num)->bool) i)`;
      `{i | i < N + 1}`; `0`] NSUM_DELETE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `e1 * v:num`)) THEN
    REWRITE_TAC[] THEN
    REWRITE_TAC[ASSUME `CARD((G:num->(B#num->B#num)->bool) 0) = e1 * e2`;
                ASSUME `CARD((G':num->(B#num->B#num)->bool) 0) = e1`] THEN
    DISCH_TAC THEN
    ASM_CASES_TAC `(c:num) divides e2` THEN ASM_REWRITE_TAC[] THENL
     [(* wild case: the group G 1 is not inside Gal(m/l) *)
      SUBGOAL_THEN `~((G:num->(B#num->B#num)->bool) 1 SUBSET H)`
      ASSUME_TAC THENL
       [DISCH_TAC THEN
        UNDISCH_TAC
         `(G:num->(B#num->B#num)->bool) 1 SUBSET G' 0 <=>
          ~((c:num) divides e2)` THEN
        ASM_REWRITE_TAC[SUBSET_INTER] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `~(N:num = 0)` ASSUME_TAC THENL
       [DISCH_TAC THEN
        UNDISCH_TAC `~((G:num->(B#num->B#num)->bool) 1 SUBSET H)` THEN
        REWRITE_TAC[] THEN
        SUBGOAL_THEN `(G:num->(B#num->B#num)->bool) 1 = {I}` SUBST1_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
          ASM_REWRITE_TAC[SING_SUBSET]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `1 <= CARD((G:num->(B#num->B#num)->bool) 1) -
             CARD((G':num->(B#num->B#num)->bool) 1)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `a:num < b ==> 1 <= b - a`) THEN
        MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[PSUBSET] THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL
       [`\i. CARD((G:num->(B#num->B#num)->bool) i) -
             CARD((G':num->(B#num->B#num)->bool) i)`;
        `{i | i < N + 1} DELETE 0`; `1`] NSUM_DELETE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[FINITE_DELETE; FINITE_NUMSEG_LT; IN_DELETE;
                    IN_ELIM_THM] THEN
        ASM_ARITH_TAC;
        REWRITE_TAC[] THEN DISCH_TAC] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(e1:num) * v <= e1 * (e2 - 1)` MP_TAC THENL
       [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
        REWRITE_TAC[LEFT_SUB_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC];
      (* tame case: all G i, i >= 1, lie in Gal(m/l) *)
      SUBGOAL_THEN
       `nsum ({i | i < N + 1} DELETE 0)
          (\i. CARD((G:num->(B#num->B#num)->bool) i) -
               CARD((G':num->(B#num->B#num)->bool) i)) = 0`
      ASSUME_TAC THENL
       [MATCH_MP_TAC NSUM_EQ_0 THEN X_GEN_TAC `i:num` THEN
        REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN STRIP_TAC THEN
        REWRITE_TAC[] THEN
        SUBGOAL_THEN `(G:num->(B#num->B#num)->bool) i SUBSET G 1`
        MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC
         `(G:num->(B#num->B#num)->bool) 1 SUBSET G' 0 <=>
          ~((c:num) divides e2)` THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `(G:num->(B#num->B#num)->bool) i INTER H = G i`
          (fun th -> REWRITE_TAC[th; SUB_REFL]) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(e1:num) * v = e1 * (e2 - 1)` MP_TAC THENL
       [REWRITE_TAC[LEFT_SUB_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
        ASM_REWRITE_TAC[EQ_MULT_LCANCEL]]]) in
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> q /\ r) ==> (p ==> q) /\ (p ==> r)`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP core) THEN
  ASM_CASES_TAC
   `ring_char(quotient_ring (ring_of_integers l) (Q:B->bool)) divides
    ramification_index (ring_of_integers k,ring_of_integers l) (h:A->B) Q` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;
