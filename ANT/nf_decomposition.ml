(* ========================================================================= *)
(* Decomposition and inertia groups and Frobenius elements in a Galois       *)
(* extension of number fields (k,l) h (number_field l and                    *)
(* galois_extension(k,l) h, which gives field k and ring_homomorphism(k,l)   *)
(* h): the results of ANT/decomposition.ml for b = ring_of_integers l, at a  *)
(* prime Q of O_l above a nonzero prime p of O_k = ring_of_integers k (IMAGE *)
(* h p SUBSET Q). With e = e(Q|p), f = f(Q|p) and r the number of primes of  *)
(* O_l above p:                                                              *)
(*                                                                           *)
(*   G is transitive on the primes above p                                   *)
(*                           (NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE)          *)
(*   |D_Q| = e f, |I_Q| = e, r e f = [l:k]                                   *)
(*                           (NUMBER_FIELD_DECOMPOSITION_GROUP)              *)
(*   e = 1 <=> I_Q = {I}     (NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP)         *)
(*   v_g(Q)(g(x)) = v_Q(x)   (NUMBER_FIELD_DEDEKIND_VALUATION_CONJUGATE)     *)
(*                                                                           *)
(* and for Q unramified over p (e(Q|p) = 1), frobenius_element (k,l) h       *)
(* (ring_of_integers l) Q is the unique f in G with f(x) == x^N(p) (mod Q)   *)
(* for all x in O_l, N(p) = ideal_norm (ring_of_integers k) p, with          *)
(* Frob_g(Q) = g Frob_Q g^-1 (NUMBER_FIELD_FROBENIUS_ELEMENT). It generates  *)
(* D_Q, with order f(Q|p) (NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS), and  *)
(* for g in G the Frobenius element at g(Q) is g Frob_Q g^-1, so D_(g(Q))    *)
(* lies in a subgroup H iff g Frob_Q g^-1 does                               *)
(* (NUMBER_FIELD_FROBENIUS_CONJUGATE_PRIME).                                 *)
(*                                                                           *)
(* Galois conjugates of ideals: elements f of G restrict to automorphisms of *)
(* O_l (GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM), map ideals, primes and  *)
(* products of ideals to ideals, primes and products                         *)
(* (GALOIS_GROUP_RING_OF_INTEGERS_IDEAL) and generated ideals to generated   *)
(* ideals (GALOIS_GROUP_IMAGE_IDEAL_GENERATED); the f in G with f(Q) = g(Q)  *)
(* form a coset of D_Q, so there are |D_Q| of them                           *)
(* (CARD_GALOIS_GROUP_IMAGE_FIBER); for a number field k Galois over its     *)
(* prime field, N(f(j)) = N(j) for every ideal j of O_k                      *)
(* (NUMBER_FIELD_IDEAL_NORM_GALOIS_IMAGE; for nonzero primes                 *)
(* NUMBER_FIELD_IDEAL_NORM_CONJUGATE).                                       *)
(*                                                                           *)
(* Routes: O_l is stable under G (GALOIS_GROUP_RING_OF_INTEGERS, so under    *)
(* D_Q: DECOMPOSITION_GROUP_RING_OF_INTEGERS), the base ring is O_k          *)
(* (RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ) and the primes above p are     *)
(* maximal with finite residue fields and contraction p                      *)
(* (NUMBER_FIELD_PRIME_IDEAL_ABOVE of ANT/relative_split.ml); v_P is         *)
(* dedekind_valuation (ring_of_integers l,l) I P of                          *)
(* ANT/dedekind_valuation.ml. The ramification index is constant on the      *)
(* G-orbit of Q by the tower law for e (RAMIFICATION_INDEX_TOWER) through g, *)
(* of index 1 (NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE), and the residue   *)
(* degree by EXTENSION_DEGREE_RESIDUE_CONJUGATE; as the orbit is all primes  *)
(* above p, the relative fundamental identity                                *)
(* (NUMBER_FIELD_FUNDAMENTAL_IDENTITY) becomes r e f = [l:k] = r |D_Q|       *)
(* (DECOMPOSITION_GROUP_INDEX). The residue field of p embeds in that of Q,  *)
(* so the image of O_k there has N(p) elements (IDEAL_NORM_RESIDUE_IMAGE,    *)
(* from RESIDUE_DEGREE_QUOTIENT_RING).                                       *)
(*                                                                           *)
(* Uses: ANT/ideal_arith.ml, ANT/dedekind.ml (DEDEKIND_IDEAL_INDUCT),        *)
(* ANT/decomposition.ml, ANT/numfield.ml, ANT/ring_of_integers.ml,           *)
(* ANT/ideal_norm.ml, ANT/norm_index.ml (NUMBER_FIELD_IDEAL_NORM_MUL_Q),     *)
(* ANT/nf_valuation.ml (RING_OF_INTEGERS_FRACTION_FIELD),                    *)
(* ANT/relative_split.ml (contractions, RAMIFICATION_INDEX_TOWER,            *)
(* RESIDUE_DEGREE_QUOTIENT_RING), ANT/relative_degree.ml and                 *)
(* ANT/splitting_types.ml (unramified, UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED).    *)
(* ========================================================================= *)

needs "ANT/decomposition.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/ideal_norm.ml";;
needs "ANT/nf_valuation.ml";;
needs "ANT/relative_split.ml";;
needs "ANT/relative_degree.ml";;
needs "ANT/splitting_types.ml";;

(* ------------------------------------------------------------------------- *)
(* The ring of integers as a G-stable subring; primes above p.               *)
(* ------------------------------------------------------------------------- *)

let GALOIS_GROUP_RING_OF_INTEGERS = prove
 (`!(h:A->B) k l f.
        f IN group_carrier(galois_group(k,l) h)
        ==> IMAGE f (ring_carrier(ring_of_integers l)) SUBSET
            ring_carrier(ring_of_integers l)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_GROUP_RING_AUTOMORPHISM) THEN
  REWRITE_TAC[ring_automorphism] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM) THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
  SIMP_TAC[ring_homomorphism]);;

(* The elements of a decomposition group preserve the ring of integers.      *)
let DECOMPOSITION_GROUP_RING_OF_INTEGERS = prove
 (`!(h:A->B) k l Q f.
        f IN group_carrier(decomposition_group(k,l) h Q)
        ==> IMAGE f (ring_carrier(ring_of_integers l)) SUBSET
            ring_carrier(ring_of_integers l)`,
  REWRITE_TAC[DECOMPOSITION_GROUP; IN_ELIM_THM] THEN
  MESON_TAC[GALOIS_GROUP_RING_OF_INTEGERS]);;

let GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM = prove
 (`!(h:A->B) k l f.
        f IN group_carrier(galois_group(k,l) h)
        ==> IMAGE f (ring_carrier(ring_of_integers l)) =
            ring_carrier(ring_of_integers l) /\
            ring_isomorphism(ring_of_integers l,ring_of_integers l) f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC GALOIS_GROUP_SUBRING_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`; `l:B ring`] THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING] THEN
  MESON_TAC[GALOIS_GROUP_RING_OF_INTEGERS]);;

let GALOIS_GROUP_RING_OF_INTEGERS_IDEAL = prove
 (`!(h:A->B) k l f j.
        f IN group_carrier(galois_group(k,l) h) /\
        ring_ideal (ring_of_integers l) j
        ==> ring_ideal (ring_of_integers l) (IMAGE f j) /\
            (IMAGE f j = {ring_0 l} <=> j = {ring_0 l}) /\
            (prime_ideal (ring_of_integers l) (IMAGE f j) <=>
             prime_ideal (ring_of_integers l) j) /\
            (!j'. j' SUBSET ring_carrier(ring_of_integers l)
                  ==> IMAGE f (ideal_prod (ring_of_integers l) j j') =
                      ideal_prod (ring_of_integers l)
                        (IMAGE f j) (IMAGE f j'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!f. f IN group_carrier(galois_group(k:A ring,l:B ring) h)
        ==> IMAGE f (ring_carrier(ring_of_integers l)) SUBSET
            ring_carrier(ring_of_integers l)`
  ASSUME_TAC THENL [MESON_TAC[GALOIS_GROUP_RING_OF_INTEGERS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `ring_of_integers l:B ring`; `f:B->B`]
    GALOIS_GROUP_SUBRING_IMAGE) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `ring_of_integers l:B ring`; `f:B->B`; `j:B->bool`]
    GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN
  ASM_SIMP_TAC[RING_OF_INTEGERS_SUBRING; RING_IDEAL_IMP_SUBSET] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM) THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_0) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_GROUP_PERMUTES) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES) THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `j:B->bool`]
      IN_RING_IDEAL_0) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[RING_OF_INTEGERS]) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN
    MATCH_MP_TAC(SET_RULE
     `!f (g:B->B) s a. (!x. g(f x) = x) /\ f a = a
                       ==> (a IN s ==> (IMAGE f s = {a} <=> s = {a}))`) THEN
    EXISTS_TAC `inverse(f:B->B)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC IDEAL_PROD_EPIMORPHIC_IMAGE THEN
    ASM_SIMP_TAC[RING_ISOMORPHISM_IMP_EPIMORPHISM; RING_IDEAL_IMP_SUBSET]]);;

let GALOIS_GROUP_IMAGE_IDEAL_GENERATED = prove
 (`!(h:A->B) k l f t.
        f IN group_carrier(galois_group(k,l) h) /\
        t SUBSET ring_carrier(ring_of_integers l)
        ==> IMAGE f (ideal_generated (ring_of_integers l) t) =
            ideal_generated (ring_of_integers l) (IMAGE f t)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_ISOMORPHISM_IMP_EPIMORPHISM THEN
  ASM_MESON_TAC[GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM]);;

(* Neukirch I.9.1 for number fields: G is transitive on the primes above p.  *)

let NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE = prove
 (`!(h:A->B) k l p P P'.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P /\
        prime_ideal (ring_of_integers l) P' /\ IMAGE h p SUBSET P'
        ==> ?f. f IN group_carrier(galois_group(k,l) h) /\ IMAGE f P = P'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `field k /\ ring_homomorphism(k,l) (h:A->B)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
    SIMP_TAC[field_extension; RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `P:B->bool`]
    NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `P':B->bool`]
    NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC GALOIS_GROUP_TRANSITIVE_PRIME_IDEALS THEN
  EXISTS_TAC `ring_of_integers l:B ring` THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING] THEN
  MESON_TAC[GALOIS_GROUP_RING_OF_INTEGERS]);;

let CARD_GALOIS_GROUP_IMAGE_FIBER = prove
 (`!(h:A->B) k l Q g.
        FINITE(group_carrier(galois_group(k,l) h)) /\
        g IN group_carrier(galois_group(k,l) h)
        ==> CARD {f | f IN group_carrier(galois_group(k,l) h) /\
                      IMAGE f Q = IMAGE g Q} =
            CARD(group_carrier(decomposition_group(k,l) h Q))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DECOMPOSITION_GROUP] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
  EXISTS_TAC `\d:B->B. (g:B->B) o d` THEN
  EXISTS_TAC `\f:B->B. inverse(g:B->B) o f` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_GROUP_PERMUTES) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES) THEN
  SUBGOAL_THEN `inverse(g:B->B) o g = I /\ g o inverse g = I`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM];
                          ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; o_ASSOC; I_O_ID; IMAGE_o] THEN
  ASM_REWRITE_TAC[I_O_ID; GSYM IMAGE_o; IMAGE_I] THEN
  CONJ_TAC THENL [DISJ1_TAC THEN ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
  ASM_SIMP_TAC[GALOIS_GROUP_COMPOSE; GALOIS_GROUP_INVERSE] THEN
  REWRITE_TAC[IMAGE_o] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM IMAGE_o] THEN
  ASM_REWRITE_TAC[IMAGE_I]);;

(* The image of O_k in O_l / Q is a copy of the residue field O_k / p.       *)

let IDEAL_NORM_RESIDUE_IMAGE = prove
 (`!(h:A->B) k l p Q.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> CARD {ring_coset (ring_of_integers l) Q (h a) | a |
                  a IN ring_carrier k /\
                  h a IN ring_carrier(ring_of_integers l)} =
            ideal_norm (ring_of_integers k) p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `ring_monomorphism(k:A ring,l:B ring) h` ASSUME_TAC THENL
   [ASM_MESON_TAC[finite_extension; field_extension]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_homomorphism(ring_of_integers k,ring_of_integers l) (h:A->B)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_OF_INTEGERS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`;
                 `Q:B->bool`] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_integers l:B ring`;
                 `h:A->B`; `Q:B->bool`] RESIDUE_DEGREE_QUOTIENT_RING) THEN
  ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(A->bool)->(B->bool)` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[ideal_norm] THEN
  SUBGOAL_THEN
   `{ring_coset (ring_of_integers l) Q ((h:A->B) a) | a |
     a IN ring_carrier k /\ h a IN ring_carrier(ring_of_integers l)} =
    IMAGE g (ring_carrier(quotient_ring (ring_of_integers k) p))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; PRIME_IMP_RING_IDEAL] THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
   [UNDISCH_TAC
     `ring_monomorphism (quotient_ring (ring_of_integers k) p,
                         quotient_ring (ring_of_integers l) Q)
                        (g:(A->bool)->(B->bool))` THEN
    REWRITE_TAC[ring_monomorphism] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Q = {ring_0(l:B ring)})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(p = {ring_0(k:A ring)})` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (h:A->B) p SUBSET {ring_0 l}` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SING] THEN
      DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:A) IN ring_carrier k` ASSUME_TAC THENL
       [ASM_MESON_TAC[PRIME_IDEAL_IMP_SUBSET; RING_OF_INTEGERS_SUBSET;
                      SUBSET];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
        RING_HOMOMORPHISM_0) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `ring_monomorphism(k:A ring,l:B ring) h` THEN
      REWRITE_TAC[ring_monomorphism] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[RING_0];
      REWRITE_TAC[SING_SUBSET] THEN
      ASM_MESON_TAC[IN_RING_IDEAL_0; PRIME_IMP_RING_IDEAL; RING_OF_INTEGERS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_integers l:B ring`;
                 `h:A->B`; `Q:B->bool`]
    FINITE_QUOTIENT_RING_HOMOMORPHIC_PREIMAGE) THEN
  ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL; RING_OF_INTEGERS_FINITE_QUOTIENT]);;

(* ------------------------------------------------------------------------- *)
(* Ramification index, residue degree and ideal norm on the orbit;           *)
(* |D_Q| = e f.                                                              *)
(* ------------------------------------------------------------------------- *)

(* e(g(Q)|p) = e(g(Q)|Q) e(Q|p) for the tower O_k -> O_l -> O_l through h    *)
(* and g, as g o h = h on O_k, and e(g(Q)|Q) = 1 for the automorphism g.     *)

let NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE = prove
 (`!(h:A->B) k l f Q.
        number_field l /\ ring_monomorphism(k,l) h /\
        f IN group_carrier(galois_group(k,l) h) /\
        prime_ideal (ring_of_integers l) Q /\
        ~({x | x IN ring_carrier(ring_of_integers k) /\ h x IN Q} =
          {ring_0 k})
        ==> ramification_index (ring_of_integers k,ring_of_integers l) h
              (IMAGE f Q) =
            ramification_index (ring_of_integers k,ring_of_integers l) h Q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `dedekind_domain(ring_of_integers l:B ring) /\
    ring_monomorphism(ring_of_integers k,ring_of_integers l) (h:A->B) /\
    ring_monomorphism(ring_of_integers l,ring_of_integers l) (f:B->B) /\
    subring_generated l (ring_carrier(ring_of_integers l)) =
    ring_of_integers l /\
    ring_carrier(ring_of_integers k) SUBSET ring_carrier k /\
    ring_0(ring_of_integers l) = ring_0 l /\
    ring_0(ring_of_integers k) = ring_0 k /\
    (!f. f IN group_carrier(galois_group(k,l) h)
         ==> IMAGE f (ring_carrier(ring_of_integers l)) SUBSET
             ring_carrier(ring_of_integers l))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_MONOMORPHISM_RING_OF_INTEGERS;
                 RING_OF_INTEGERS_SUBRING; RING_OF_INTEGERS_SUBSET;
                 RING_OF_INTEGERS] THEN
    CONJ_TAC THENL [ALL_TAC; MESON_TAC[GALOIS_GROUP_RING_OF_INTEGERS]] THEN
    MATCH_MP_TAC RING_MONOMORPHISM_RING_OF_INTEGERS THEN
    ASM_MESON_TAC[GALOIS_GROUP_RING_AUTOMORPHISM; ring_automorphism;
                  RING_ISOMORPHISM_IMP_MONOMORPHISM];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_GROUP_PERMUTES o check (fun th ->
    concl th = `f IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `ring_of_integers l:B ring`;
                 `f:B->B`; `Q:B->bool`] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[PRIME_IDEAL_IMP_SUBSET]; STRIP_TAC] THEN
  ABBREV_TAC `s = ring_of_integers(l:B ring)` THEN
  ABBREV_TAC `r = ring_of_integers(k:A ring)` THEN
  SUBGOAL_THEN `!x. x IN ring_carrier r ==> (f:B->B) ((h:A->B) x) = h x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`; `x:A`]
      GALOIS_GROUP_FIXES) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. (f:B->B) y IN IMAGE f Q <=> y IN Q` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?x. x IN ring_carrier r /\ (h:A->B) x IN Q /\ ~(h x = ring_0 l)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `~({x | x IN ring_carrier r /\ (h:A->B) x IN Q} = {ring_0 k})` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING; NOT_FORALL_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `x = ring_0(k:A ring)` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[RING_0; PRIME_IMP_RING_IDEAL; IN_RING_IDEAL_0;
                    RING_MONOMORPHISM_IMP_HOMOMORPHISM; RING_HOMOMORPHISM_0];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
        RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o MATCH_MP
        RING_HOMOMORPHISM_0) THEN
      UNDISCH_TAC `ring_monomorphism(k:A ring,l:B ring) h` THEN
      REWRITE_TAC[ring_monomorphism] THEN
      DISCH_THEN(MP_TAC o SPECL [`x:A`; `ring_0 k:A`] o CONJUNCT2) THEN
      ASM_SIMP_TAC[RING_0] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->B) x IN IMAGE (f:B->B) Q` ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:A->B) x = (f:B->B) (h x)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (f:B->B) Q = {ring_0 s})` ASSUME_TAC THENL
   [DISCH_THEN(fun th ->
      UNDISCH_TAC `(h:A->B) x IN IMAGE (f:B->B) Q` THEN
      REWRITE_TAC[th; IN_SING]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ramification_index (s,s) (f:B->B) (IMAGE f Q) = 1`
  ASSUME_TAC THENL
   [REWRITE_TAC[ramification_index] THEN
    SUBGOAL_THEN `{y | y IN ring_carrier s /\ (f:B->B) y IN IMAGE f Q} = Q`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`s:B ring`; `Q:B->bool`] PRIME_IDEAL_IMP_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_RING_IDEAL; PRIME_IMP_RING_IDEAL] THEN
    MP_TAC(ISPECL [`s:B ring`; `IMAGE (f:B->B) Q`; `IMAGE (f:B->B) Q`]
      IDEAL_VALUATION_PRIME) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `s:B ring`; `s:B ring`; `h:A->B`; `f:B->B`;
                 `IMAGE (f:B->B) Q`] RAMIFICATION_INDEX_TOWER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{y | y IN ring_carrier s /\ y IN Q} = (Q:B->bool)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`s:B ring`; `Q:B->bool`] PRIME_IDEAL_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MULT_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ramification_index] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `IMAGE (h:A->B)
    {x | x IN ring_carrier r /\ ((f:B->B) o h) x IN IMAGE f Q}` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; o_THM] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM; o_THM]]);;

let NUMBER_FIELD_IDEAL_NORM_CONJUGATE = prove
 (`!(h:A->B) k l f Q.
        number_field l /\ f IN group_carrier(galois_group(k,l) h) /\
        prime_ideal (ring_of_integers l) Q /\ ~(Q = {ring_0 l})
        ==> ideal_norm (ring_of_integers l) (IMAGE f Q) =
            ideal_norm (ring_of_integers l) Q`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `ring_homomorphism(l,l) (f:B->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_RING_AUTOMORPHISM; ring_automorphism;
                  RING_ISOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`]
    GALOIS_GROUP_PERMUTES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES) THEN
  SUBGOAL_THEN
   `inverse(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`galois_group(k,l) (h:A->B)`; `f:B->B`] GROUP_INV) THEN
    ASM_REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 GALOIS_GROUP))];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. g IN group_carrier(galois_group(k,l) (h:A->B))
        ==> IMAGE g (ring_carrier(ring_of_integers l)) SUBSET
            ring_carrier(ring_of_integers l)`
  ASSUME_TAC THENL [MESON_TAC[GALOIS_GROUP_RING_OF_INTEGERS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `ring_of_integers l:B ring`;
                 `f:B->B`; `Q:B->bool`] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN
  ASM_SIMP_TAC[RING_OF_INTEGERS_SUBRING; PRIME_IDEAL_IMP_SUBSET] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`f:B->B`; `l:B ring`; `l:B ring`; `Q:B->bool`;
                 `IMAGE (f:B->B) Q`] IDEAL_NORM_RESIDUE_IMAGE) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ideal_norm] THEN
  ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; PRIME_IMP_RING_IDEAL] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `c:B->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `b:B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `inverse(f:B->B) b` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`]
      GALOIS_GROUP_PERMUTES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP PERMUTES_INVERSE) THEN
    SIMP_TAC[PERMUTES_IN_IMAGE] THEN DISCH_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET) THEN
    FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(f:B->B) a` THEN ASM_REWRITE_TAC[]]);;

let NUMBER_FIELD_IDEAL_NORM_GALOIS_IMAGE = prove
 (`!(h:A->B) k l f j.
        number_field l /\ f IN group_carrier(galois_group(k,l) h) /\
        ring_ideal (ring_of_integers l) j
        ==> ideal_norm (ring_of_integers l) (IMAGE f j) =
            ideal_norm (ring_of_integers l) j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `j = {ring_0(l:B ring)}` THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP RING_HOMOMORPHISM_0) THEN REFL_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_RING_OF_INTEGERS) THEN
  SUBGOAL_THEN
   `!j. ring_ideal (ring_of_integers l) j /\
        ~(j = {ring_0(ring_of_integers l)})
        ==> ideal_norm (ring_of_integers l) (IMAGE (f:B->B) j) =
            ideal_norm (ring_of_integers l) j`
   (fun th -> ASM_SIMP_TAC[th; RING_OF_INTEGERS]) THEN
  MATCH_MP_TAC DEDEKIND_IDEAL_INDUCT THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`q:B->bool`; `i:B->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `f:B->B`; `q:B->bool`]
    GALOIS_GROUP_RING_OF_INTEGERS_IDEAL) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `f:B->B`; `i:B->bool`]
    GALOIS_GROUP_RING_OF_INTEGERS_IDEAL) THEN
  ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL; RING_IDEAL_IMP_SUBSET] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NUMBER_FIELD_IDEAL_NORM_MUL_Q; PRIME_IMP_RING_IDEAL] THEN
  ASM_MESON_TAC[NUMBER_FIELD_IDEAL_NORM_CONJUGATE]);;

(* Neukirch I.9.6: with e and f constant on the primes above p, the          *)
(* fundamental identity gives r e f = [l:k], and r |D_Q| = [l:k].            *)

let NUMBER_FIELD_DECOMPOSITION_GROUP = prove
 (`!(h:A->B) k l p Q.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> CARD(group_carrier(decomposition_group(k,l) h Q)) =
            ramification_index (ring_of_integers k,ring_of_integers l) h Q *
            residue_degree (ring_of_integers k,ring_of_integers l) h Q /\
            CARD(group_carrier(inertia_group(k,l) h (ring_of_integers l) Q)) =
            ramification_index (ring_of_integers k,ring_of_integers l) h Q /\
            CARD {P | prime_ideal (ring_of_integers l) P /\
                      IMAGE h p SUBSET P} *
            ramification_index (ring_of_integers k,ring_of_integers l) h Q *
            residue_degree (ring_of_integers k,ring_of_integers l) h Q =
            extension_degree(k,l) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `field k /\ ring_homomorphism(k,l) (h:A->B)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
    SIMP_TAC[field_extension; RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `ring_monomorphism(k:A ring,l:B ring) h` ASSUME_TAC THENL
   [ASM_MESON_TAC[finite_extension; field_extension]; ALL_TAC] THEN
  SUBGOAL_THEN
   `subring_generated l (ring_carrier(ring_of_integers l)) =
    ring_of_integers l /\
    (!f. f IN group_carrier(galois_group(k,l) h)
         ==> IMAGE f (ring_carrier(ring_of_integers l)) SUBSET
             ring_carrier(ring_of_integers l)) /\
    (!P. P SUBSET ring_carrier(ring_of_integers l)
         ==> {a | a IN ring_carrier k /\ (h:A->B) a IN P} =
             {x | x IN ring_carrier(ring_of_integers k) /\ h x IN P}) /\
    dedekind_domain(ring_of_integers l) /\
    ring_0(ring_of_integers l) = ring_0 l /\
    ring_0(ring_of_integers k) = ring_0 k`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_OF_INTEGERS_SUBRING; DEDEKIND_RING_OF_INTEGERS;
                 RING_OF_INTEGERS] THEN
    CONJ_TAC THENL [MESON_TAC[GALOIS_GROUP_RING_OF_INTEGERS]; ALL_TAC] THEN
    X_GEN_TAC `P:B->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_SUBSET) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; SUBSET] THEN
    UNDISCH_TAC `P SUBSET ring_carrier(ring_of_integers(l:B ring))` THEN
    REWRITE_TAC[SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN p ==> x IN ring_carrier k /\
                   ((h:A->B) x = ring_0 l <=> x = ring_0 k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN ring_carrier k` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_IDEAL_IMP_SUBSET; RING_OF_INTEGERS_SUBSET; SUBSET];
      ASM_REWRITE_TAC[]] THEN
    UNDISCH_TAC `ring_monomorphism(k:A ring,l:B ring) h` THEN
    REWRITE_TAC[ring_monomorphism] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_0) THEN
    ASM_MESON_TAC[RING_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. prime_ideal (ring_of_integers l) P /\ IMAGE (h:A->B) p SUBSET P
        ==> ~(P = {ring_0 l}) /\ maximal_ideal (ring_of_integers l) P /\
            FINITE(ring_carrier(quotient_ring (ring_of_integers l) P)) /\
            {a | a IN ring_carrier k /\ h a IN P} = p`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:B->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q /\ r) /\ s ==> p /\ q /\ r /\ s`) THEN
    REPEAT CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(p = {ring_0(k:A ring)})` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (h:A->B) p SUBSET {ring_0 l}` THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SING] THEN ASM_MESON_TAC[];
        REWRITE_TAC[SING_SUBSET] THEN
        ASM_MESON_TAC[IN_RING_IDEAL_0; PRIME_IMP_RING_IDEAL]];
      DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN
        ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL]];
      ASM_SIMP_TAC[PRIME_IDEAL_IMP_SUBSET] THEN
      MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`;
                     `P:B->bool`]
        RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP
   (CONJ (ASSUME `prime_ideal (ring_of_integers l) (Q:B->bool)`)
         (ASSUME `IMAGE (h:A->B) p SUBSET Q`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `{P | prime_ideal (ring_of_integers l) P /\ IMAGE (h:A->B) p SUBSET P} =
    {Q' | maximal_ideal (ring_of_integers l) Q' /\
          {a | a IN ring_carrier k /\ h a IN Q'} =
          {a | a IN ring_carrier k /\ h a IN Q}}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `P:B->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EQ_TAC THENL
     [ASM_MESON_TAC[];
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)] THEN
    ASM_SIMP_TAC[MAXIMAL_IMP_PRIME_IDEAL] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN
    DISCH_TAC THEN
    UNDISCH_TAC `{a | a IN ring_carrier k /\ (h:A->B) a IN P} = p` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. residue_degree (ring_of_integers k,ring_of_integers l) (h:A->B) P =
        extension_degree
         (subring_generated (quotient_ring (ring_of_integers l) P)
           (IMAGE (ring_coset (ring_of_integers l) P o h)
                  {a | a IN ring_carrier k /\
                       h a IN ring_carrier(ring_of_integers l)}),
          quotient_ring (ring_of_integers l) P) I`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[residue_degree] THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN ring_carrier(ring_of_integers k) /\ (h:A->B) x IN Q} = p`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`;
                   `Q:B->bool`] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `ring_of_integers l:B ring`;
                 `Q:B->bool`] DECOMPOSITION_GROUP_INDEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(check (fun th ->
    is_eq(concl th) &&
    can (find_term ((=) `prime_ideal:(B)ring->(B->bool)->bool`))
        (lhs(concl th))) th)]) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!P. P IN {P | prime_ideal (ring_of_integers l) P /\
                  IMAGE (h:A->B) p SUBSET P}
        ==> ramification_index (ring_of_integers k,ring_of_integers l) h P =
            ramification_index (ring_of_integers k,ring_of_integers l) h Q /\
            residue_degree (ring_of_integers k,ring_of_integers l) h P =
            residue_degree (ring_of_integers k,ring_of_integers l) h Q`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:B->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP
     (CONJ (ASSUME `prime_ideal (ring_of_integers l) (P:B->bool)`)
           (ASSUME `IMAGE (h:A->B) p SUBSET P`)) o check (fun th ->
       is_forall(concl th) &&
       can (find_term ((=) `maximal_ideal:(B)ring->(B->bool)->bool`))
           (concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                   `ring_of_integers l:B ring`; `Q:B->bool`; `P:B->bool`]
      GALOIS_GROUP_TRANSITIVE_PRIME_IDEALS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:B->B`
     (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC EXTENSION_DEGREE_RESIDUE_CONJUGATE THEN
      EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SPEC `Q:B->bool` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t &&
                             fst(dest_const t) = "residue_degree"))
        (concl th) &&
    not(can (find_term (fun t -> is_const t &&
                                 fst(dest_const t) = "ramification_index"))
        (concl th)))) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `ring_of_integers l:B ring`;
                 `Q:B->bool`] CARD_DECOMPOSITION_GROUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(check (fun th ->
    is_eq(concl th) &&
    can (find_term (fun t -> is_const t &&
                             fst(dest_const t) = "residue_degree"))
        (lhs(concl th))) th)]) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    NUMBER_FIELD_FUNDAMENTAL_IDENTITY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `S = {P | prime_ideal (ring_of_integers l) P /\
             IMAGE (h:A->B) p SUBSET P}` THEN
  ABBREV_TAC
   `e = ramification_index (ring_of_integers k,ring_of_integers l)
          (h:A->B) Q` THEN
  ABBREV_TAC
   `fd = residue_degree (ring_of_integers k,ring_of_integers l)
           (h:A->B) Q` THEN
  SUBGOAL_THEN
   `nsum S (\P. ramification_index (ring_of_integers k,ring_of_integers l)
                  (h:A->B) P *
                residue_degree (ring_of_integers k,ring_of_integers l) h P) =
    CARD S * e * fd`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM NSUM_CONST] THEN MATCH_MP_TAC NSUM_EQ THEN
    ASM_SIMP_TAC[];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `fd:num`)) THEN
  SUBGOAL_THEN `~(CARD(S:(B->bool)->bool) = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `Q:B->bool` THEN EXPAND_TAC "S" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(group_carrier(decomposition_group(k,l) (h:A->B) Q)) =
    (e:num) * (fd:num)`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`CARD(S:(B->bool)->bool)`;
                  `CARD(group_carrier(decomposition_group(k,l) (h:A->B) Q))`;
                  `(e:num) * (fd:num)`] EQ_MULT_LCANCEL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(CARD(group_carrier(decomposition_group(k,l) (h:A->B) Q)) = 0)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `FINITE(group_carrier(decomposition_group(k,l) (h:A->B) Q))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `group_carrier(galois_group(k,l) (h:A->B))` THEN
      ASM_SIMP_TAC[FINITE_GALOIS_GROUP] THEN
      REWRITE_TAC[decomposition_group;
                  GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET];
      ASM_SIMP_TAC[CARD_EQ_0; GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `group_id(decomposition_group(k,l) (h:A->B) Q)` THEN
      REWRITE_TAC[GROUP_ID]];
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`CARD(group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q))`;
    `e:num`; `fd:num`] EQ_MULT_RCANCEL) THEN
  SUBGOAL_THEN `~((fd:num) = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `~(CARD(group_carrier(decomposition_group(k,l) (h:A->B) Q)) = 0)` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_MESON_TAC[]);;

(* The inertia field. For L Galois over a number field K with a prime Q over *)
(* P, the fixed field T of I_Q has e(Q INTER T | P) = 1 and f(Q | Q INTER T) *)
(* = 1 (Neukirch I (9.6); NUMBER_FIELD_INERTIA_FIELD), from the              *)
(* decomposition group counts of NUMBER_FIELD_DECOMPOSITION_GROUP for L/T    *)
(* and L/K, since Gal(L/T) = I_Q, and the tower law                          *)
(* RAMIFICATION_INDEX_TOWER.                                                 *)
let NUMBER_FIELD_INERTIA_FIELD = prove
 (`!(h:A->B) k l p Q.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> ramification_index
             (ring_of_integers k,
              ring_of_integers(subfield_generated l
               (fixed_field l (group_carrier
                 (inertia_group(k,l) h (ring_of_integers l) Q))))) h
             (Q INTER
              ring_carrier(ring_of_integers(subfield_generated l
               (fixed_field l (group_carrier
                 (inertia_group(k,l) h (ring_of_integers l) Q)))))) = 1 /\
            residue_degree
             (ring_of_integers(subfield_generated l
               (fixed_field l (group_carrier
                 (inertia_group(k,l) h (ring_of_integers l) Q)))),
              ring_of_integers l)
             I Q = 1`,
  let lemma = prove
   (`!(c:num) (d:num) (f:num) (e:num) (x:num).
          ~(d = 0) /\ d * f = e /\ e = d * x /\ c = d /\ c = d * f
          ==> x = 1 /\ f = 1`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`d:num`; `f:num`; `1`] EQ_MULT_LCANCEL) THEN
    MP_TAC(SPECL [`d:num`; `x:num`; `f:num`] EQ_MULT_LCANCEL) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `f = 1` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `field k /\ ring_homomorphism(k,l) (h:A->B)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
    SIMP_TAC[field_extension; RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  ABBREV_TAC
   `G = group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q)` THEN
  SUBGOAL_THEN `finite_extension(k,l) (h:A->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NUMBER_FIELD_TOWER_LAW]; ALL_TAC] THEN
  SUBGOAL_THEN `(G:(B->B)->bool) subgroup_of galois_group(k,l) (h:A->B)`
  ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[inertia_group; SUBGROUP_SUBGROUP_GENERATED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `G:(B->B)->bool`]
    GALOIS_GROUP_FIXED_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Ti = fixed_field l (G:(B->B)->bool)` THEN
  ABBREV_TAC `M = subfield_generated l (Ti:B->bool)` THEN
  SUBGOAL_THEN
   `field(l:B ring) /\ field M /\ ring_carrier M = Ti /\
    Ti SUBSET ring_carrier l /\ ring_homomorphism(M,l) (I:B->B)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN
    ASM_SIMP_TAC[NUMBER_FIELD_IMP_FIELD; FIELD_SUBFIELD_GENERATED;
                 CARRIER_SUBFIELD_GENERATED_SUBFIELD; SUBFIELD_OF_IMP_SUBSET;
                 RING_HOMOMORPHISM_SUBFIELD_INCLUSION];
    ALL_TAC] THEN
  SUBGOAL_THEN `number_field(M:B ring)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`M:B ring`; `l:B ring`; `I:B->B`]
      NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `galois_extension(M,l) (I:B->B)` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC GALOIS_EXTENSION_SUBFIELD_GENERATED THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q) =
    {f | f IN group_carrier(galois_group(k,l) h) /\
         IMAGE f Q = Q /\
         !x. x IN ring_carrier(ring_of_integers l)
             ==> ring_sub l (f x) x IN Q}`
  MP_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 INERTIA_GROUP) THEN
    REWRITE_TAC[RING_OF_INTEGERS_SUBRING;
                DECOMPOSITION_GROUP_RING_OF_INTEGERS] THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `group_carrier(decomposition_group(M,l) (I:B->B) Q) = G /\
    group_carrier(inertia_group(M,l) (I:B->B) (ring_of_integers l) Q) = G`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[DECOMPOSITION_GROUP] THEN
    MP_TAC(ISPECL [`I:B->B`; `M:B ring`; `l:B ring`;
                   `ring_of_integers l:B ring`; `Q:B->bool`]
      (CONJUNCT1 INERTIA_GROUP)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[RING_OF_INTEGERS_SUBRING;
                  DECOMPOSITION_GROUP_RING_OF_INTEGERS] THEN
      ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL];
      ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL]] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
     lhs(concl th) = `G:(B->B)->bool`)) THEN
  SUBGOAL_THEN `ring_monomorphism(k,l) (h:A->B)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
      GALOIS_IMP_FIELD_EXTENSION) THEN
    ASM_SIMP_TAC[field_extension];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_monomorphism(k,M) (h:A->B) /\ ring_monomorphism(M,l) (I:B->B)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `M = subring_generated l (Ti:B->bool)` SUBST1_TAC THENL
       [EXPAND_TAC "M" THEN
        UNDISCH_TAC `ring_carrier M = (Ti:B->bool)` THEN EXPAND_TAC "M" THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
          [SYM th]) THEN
        REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED];
        MATCH_MP_TAC RING_MONOMORPHISM_INTO_SUBRING THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
      ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a:A. a IN p /\ ~(a = ring_0 k)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(p = {ring_0(k:A ring)})` THEN
    MATCH_MP_TAC(SET_RULE
     `(z:A) IN s ==> ~(s = {z}) ==> ?a. a IN s /\ ~(a = z)`) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:A->bool`]
      IN_RING_IDEAL_0) THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL; RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier k` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:A->bool`]
      RING_IDEAL_IMP_SUBSET) THEN
    MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_SUBSET) THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN
    REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->B) a IN Q /\ ~(h a = ring_0 l)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (h:A->B) p SUBSET Q` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `a:A`) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `a:A`]
        RING_MONOMORPHISM_EQ_0) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Q = {ring_0(l:B ring)})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(h:A->B) a IN {ring_0(l:B ring)}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`M:B ring`; `l:B ring`; `I:B->B`; `Q:B->bool`]
    RING_OF_INTEGERS_PRIME_IDEAL_BELOW) THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM; IMAGE_I] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:B->bool` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`M:B ring`; `l:B ring`; `I:B->B`; `q:B->bool`; `Q:B->bool`]
    RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM; IMAGE_I; I_THM] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `Q INTER ring_carrier(ring_of_integers M) = (q:B->bool)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `q:B->bool`)) THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`I:B->B`; `M:B ring`; `l:B ring`; `q:B->bool`; `Q:B->bool`]
    NUMBER_FIELD_DECOMPOSITION_GROUP) THEN
  ASM_REWRITE_TAC[IMAGE_I] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT1)) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `Q:B->bool`]
    NUMBER_FIELD_DECOMPOSITION_GROUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2) THEN
  SUBGOAL_THEN `~(CARD(G:(B->B)->bool) = 0)` ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[CARD_EQ_0]
     `FINITE (s:A->bool) /\ ~(s = {}) ==> ~(CARD s = 0)`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `group_carrier(galois_group(k,l) (h:A->B))` THEN
      ASM_SIMP_TAC[FINITE_GALOIS_GROUP] THEN
      ASM_MESON_TAC[subgroup_of];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rand(concl th) = `G:(B->B)->bool` &&
        can (find_term (fun t -> is_const t &&
                                 fst(dest_const t) = "inertia_group"))
          (concl th) && can (find_term ((=) `k:A ring`)) (concl th))) THEN
      MESON_TAC[GROUP_ID; MEMBER_NOT_EMPTY]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_integers M:B ring`;
                 `ring_of_integers l:B ring`; `h:A->B`; `I:B->B`; `Q:B->bool`]
    RAMIFICATION_INDEX_TOWER) THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_RING_OF_INTEGERS; DEDEKIND_RING_OF_INTEGERS;
               I_O_ID; I_THM; RING_OF_INTEGERS] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `Q:B->bool`]
    RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
     can (find_term (fun t -> is_const t &&
       fst(dest_const t) = "ramification_index")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `~(ramification_index (ring_of_integers M,ring_of_integers l) (I:B->B) Q =
      0)`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `~(CARD(G:(B->B)->bool) = 0)`) THEN
    MP_TAC(ASSUME `CARD(G:(B->B)->bool) =
      ramification_index (ring_of_integers M,ring_of_integers l)
                         (I:B->B) Q`) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC lemma THEN
  MAP_EVERY EXISTS_TAC
   [`CARD(G:(B->B)->bool)`;
    `ramification_index (ring_of_integers M,ring_of_integers l) (I:B->B) Q`;
    `ramification_index (ring_of_integers k,ring_of_integers l)
                        (h:A->B) Q`] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP = prove
 (`!(h:A->B) k l p Q.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> (ramification_index (ring_of_integers k,ring_of_integers l) h Q =
             1 <=>
             group_carrier(inertia_group(k,l) h (ring_of_integers l) Q) =
             {I})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
    MATCH_MP NUMBER_FIELD_DECOMPOSITION_GROUP) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `field k /\ ring_homomorphism(k,l) (h:A->B)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
    SIMP_TAC[field_extension; RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `FINITE(group_carrier
            (inertia_group(k,l) (h:A->B) (ring_of_integers l) Q)) /\
    I IN group_carrier(inertia_group(k,l) h (ring_of_integers l) Q)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `group_carrier(galois_group(k,l) (h:A->B))` THEN
      ASM_SIMP_TAC[FINITE_GALOIS_GROUP] THEN
      REWRITE_TAC[inertia_group; GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET];
      MP_TAC(ISPEC
       `inertia_group(k,l) (h:A->B) (ring_of_integers l) Q` GROUP_ID) THEN
      REWRITE_TAC[INERTIA_GROUP]];
    ALL_TAC] THEN
  EQ_TAC THENL [ALL_TAC; SIMP_TAC[CARD_SING]] THEN
  DISCH_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
  ASM_REWRITE_TAC[SING_SUBSET; CARD_SING]);;

(* The valuations at conjugate primes correspond: v_g(Q)(g(x)) = v_Q(x), by  *)
(* IDEAL_VALUATION_HOMOMORPHIC_IMAGE for the automorphism g of O_l, of       *)
(* ramification index 1 at g(Q).                                             *)

let NUMBER_FIELD_DEDEKIND_VALUATION_CONJUGATE = prove
 (`!(h:A->B) k l f Q x.
        number_field l /\ f IN group_carrier(galois_group(k,l) h) /\
        prime_ideal (ring_of_integers l) Q /\ ~(Q = {ring_0 l}) /\
        x IN ring_carrier l /\ ~(x = ring_0 l)
        ==> dedekind_valuation (ring_of_integers l,l) I (IMAGE f Q) (f x) =
            dedekind_valuation (ring_of_integers l,l) I Q x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `l:B ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[field_of_fractions; RING_OF_INTEGERS; I_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:B` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:B` (X_CHOOSE_THEN `c:B` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `ring_homomorphism(l,l) (f:B->B) /\
    ring_monomorphism(ring_of_integers l,ring_of_integers l) f /\
    subring_generated l (ring_carrier(ring_of_integers l)) =
    ring_of_integers l /\
    (!g. g IN group_carrier(galois_group(k,l) (h:A->B))
         ==> IMAGE g (ring_carrier(ring_of_integers l)) SUBSET
             ring_carrier(ring_of_integers l)) /\
    ring_0(ring_of_integers l) = ring_0 l /\
    ring_carrier(ring_of_integers l) SUBSET ring_carrier l`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS_SUBRING; RING_OF_INTEGERS;
                RING_OF_INTEGERS_SUBSET] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[GALOIS_GROUP_RING_AUTOMORPHISM; ring_automorphism;
                    RING_ISOMORPHISM_IMP_HOMOMORPHISM];
      MATCH_MP_TAC RING_MONOMORPHISM_RING_OF_INTEGERS THEN
      ASM_MESON_TAC[GALOIS_GROUP_RING_AUTOMORPHISM; ring_automorphism;
                    RING_ISOMORPHISM_IMP_MONOMORPHISM];
      MESON_TAC[GALOIS_GROUP_RING_OF_INTEGERS]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_GROUP_PERMUTES o check (fun th ->
    concl th = `f IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES) THEN
  SUBGOAL_THEN `!y:B. (f:B->B) y IN IMAGE f Q <=> y IN Q` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ring_carrier l ==> ((f:B->B) y = ring_0 l <=> y = ring_0 l)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `f:B->B`] RING_HOMOMORPHISM_0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `inverse(f:B->B)` o check (fun th ->
        concl th = `(f:B->B) y = ring_0 l`)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
        [SYM(check (fun th -> concl th = `(f:B->B)(ring_0 l) = ring_0 l`) th)])
      THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `ring_of_integers l:B ring`;
                 `f:B->B`; `Q:B->bool`] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[PRIME_IDEAL_IMP_SUBSET]; STRIP_TAC] THEN
  SUBGOAL_THEN `?y. y IN Q /\ ~(y = ring_0(l:B ring))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(Q = {ring_0(l:B ring)})` THEN
    MATCH_MP_TAC(SET_RULE
     `(z:B) IN Q ==> ~(Q = {z}) ==> ?y. y IN Q /\ ~(y = z)`) THEN
    ASM_MESON_TAC[IN_RING_IDEAL_0; PRIME_IMP_RING_IDEAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `prime_ideal (ring_of_integers l) (IMAGE (f:B->B) Q) /\
                ~(IMAGE f Q = {ring_0 l})`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\s. (f:B->B) y IN s`) THEN
    ASM_SIMP_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{y | y IN ring_carrier(ring_of_integers l) /\ y IN Q} = (Q:B->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers l:B ring`; `Q:B->bool`]
      PRIME_IDEAL_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ramification_index (ring_of_integers l,ring_of_integers l) (f:B->B)
      (IMAGE f Q) = 1`
  ASSUME_TAC THENL
   [REWRITE_TAC[ramification_index] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_RING_IDEAL; PRIME_IMP_RING_IDEAL] THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `IMAGE (f:B->B) Q`;
                   `IMAGE (f:B->B) Q`] IDEAL_VALUATION_PRIME) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN ring_carrier(ring_of_integers l) /\ ~(z = ring_0 l)
        ==> ideal_valuation (ring_of_integers l) (IMAGE (f:B->B) Q)
             (ideal_generated (ring_of_integers l) {f z}) =
            ideal_valuation (ring_of_integers l) Q
             (ideal_generated (ring_of_integers l) {z})`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:B` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `ring_of_integers l:B ring`;
                   `f:B->B`; `IMAGE (f:B->B) Q`;
                   `ideal_generated (ring_of_integers l) {z:B}`]
      IDEAL_VALUATION_HOMOMORPHIC_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\s. (z:B) IN s`) THEN
      ASM_SIMP_TAC[IN_SING; IDEAL_GENERATED_INC_GEN; IN_SING];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `ring_of_integers l:B ring`;
                   `f:B->B`; `{z:B}`]
      IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN
    ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM; SING_SUBSET;
                 IMAGE_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(a:B) IN ring_carrier l /\ (c:B) IN ring_carrier l /\
    ~(a = ring_0 l)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[]; STRIP_TAC] THEN
    UNDISCH_TAC `ring_mul l c x = (a:B)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(f:B->B) x IN ring_carrier l /\
    f a IN ring_carrier(ring_of_integers l) /\
    f c IN ring_carrier(ring_of_integers l) /\
    ~(f a = ring_0 l) /\ ~(f c = ring_0 l) /\
    ring_mul l (f c) (f x) = f a`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[GALOIS_GROUP_PERMUTES; PERMUTES_IN_IMAGE];
      ASM SET_TAC[];
      ASM SET_TAC[];
      UNDISCH_TAC `ring_mul l c x = (a:B)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      CONV_TAC SYM_CONV THEN
      UNDISCH_TAC `ring_homomorphism(l:B ring,l) f` THEN
      SIMP_TAC[ring_homomorphism] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `l:B ring`; `I:B->B`;
                 `Q:B->bool`; `x:B`; `a:B`; `c:B`] DEDEKIND_VALUATION) THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `l:B ring`; `I:B->B`;
                 `IMAGE (f:B->B) Q`; `(f:B->B) x`; `(f:B->B) a`;
                 `(f:B->B) c`] DEDEKIND_VALUATION) THEN
  ASM_REWRITE_TAC[I_THM] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Frobenius elements of unramified primes. At a maximal ideal Q of a        *)
(* G-stable subring b of l with finite residue field and trivial inertia,    *)
(* the Frobenius element generates the decomposition group, and its order is *)
(* |D_Q| (DECOMPOSITION_GROUP_FROBENIUS_GENERATED). So for number fields, at *)
(* a prime Q unramified over p, it generates D_Q and has order f(Q|p)        *)
(* (NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS).                             *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_FROBENIUS_ELEMENT = prove
 (`!(h:A->B) k l p Q.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
        ramification_index (ring_of_integers k,ring_of_integers l) h Q = 1
        ==> frobenius_element (k,l) h (ring_of_integers l) Q
            IN group_carrier(decomposition_group(k,l) h Q) /\
            (!f. f IN group_carrier(galois_group(k,l) h) /\
                 (!x. x IN ring_carrier(ring_of_integers l)
                      ==> ring_sub l (f x)
                           (ring_pow l x (ideal_norm (ring_of_integers k) p))
                          IN Q)
                 <=> f = frobenius_element (k,l) h (ring_of_integers l) Q) /\
            (!f. f IN group_carrier(galois_group(k,l) h)
                 ==> frobenius_element (k,l) h (ring_of_integers l)
                       (IMAGE f Q) =
                     f o frobenius_element (k,l) h (ring_of_integers l) Q o
                     inverse f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `field k /\ ring_homomorphism(k,l) (h:A->B)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
    SIMP_TAC[field_extension; RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `Q:B->bool`]
    NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `Q:B->bool`]
    NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `Q:B->bool`]
    IDEAL_NORM_RESIDUE_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `subring_generated l (ring_carrier(ring_of_integers l)) =
    ring_of_integers l /\
    (!f. f IN group_carrier(galois_group(k,l) (h:A->B))
         ==> IMAGE f (ring_carrier(ring_of_integers l)) SUBSET
             ring_carrier(ring_of_integers (l:B ring)))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS_SUBRING] THEN
    MESON_TAC[GALOIS_GROUP_RING_OF_INTEGERS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `ring_of_integers l:B ring`;
                 `Q:B->bool`] FROBENIUS_ELEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FROBENIUS_ELEMENT_CONJUGATE THEN
  ASM_REWRITE_TAC[]);;

(* At a prime Q with trivial inertia the decomposition group is generated by *)
(* the Frobenius element, whose order is |D_Q|.                              *)
let DECOMPOSITION_GROUP_FROBENIUS_GENERATED = prove
 (`!(h:A->B) k l b Q.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        maximal_ideal b Q /\ FINITE(ring_carrier(quotient_ring b Q)) /\
        group_carrier(inertia_group(k,l) h b Q) = {I}
        ==> group_carrier(subgroup_generated (galois_group(k,l) h)
                           {frobenius_element (k,l) h b Q}) =
            group_carrier(decomposition_group(k,l) h Q) /\
            group_element_order (galois_group(k,l) h)
              (frobenius_element (k,l) h b Q) =
            CARD(group_carrier(decomposition_group(k,l) h Q))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!f. f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)
        ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b`
  ASSUME_TAC THENL
   [REWRITE_TAC[DECOMPOSITION_GROUP; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`]
    FROBENIUS_ELEMENT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Fr = frobenius_element (k,l) (h:A->B) b Q` THEN
  ABBREV_TAC
   `q = CARD {ring_coset b Q ((h:A->B) a) | a |
              a IN ring_carrier k /\ h a IN ring_carrier b}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `Fr:B->B`)) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_carrier b SUBSET ring_carrier l /\
    ring_sub b = ring_sub l /\ ring_pow b = ring_pow (l:B ring)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `subring_generated l (ring_carrier b) = (b:B ring)` THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[RING_CARRIER_SUBRING_GENERATED_SUBSET;
                RING_SUB_SUBRING_GENERATED; RING_POW_SUBRING_GENERATED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`]
    DECOMPOSITION_GROUP_RESIDUE_EPIMORPHISM) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`]
    DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`]
    CARD_DECOMPOSITION_GROUP) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`]
    SUBRING_GENERATED_QUOTIENT_RING_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[finite_extension; field_extension;
                  RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  ABBREV_TAC
   `kP = subring_generated (quotient_ring b Q)
          (IMAGE (ring_coset b Q o (h:A->B))
                 {a | a IN ring_carrier k /\ h a IN ring_carrier b})` THEN
  ABBREV_TAC
   `rho = \f X. if X IN ring_carrier(quotient_ring b Q)
                then IMAGE (f:B->B) X else X` THEN
  ASM_REWRITE_TAC[CARD_SING; MULT_CLAUSES] THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`I:(B->bool)->(B->bool)`; `kP:(B->bool)ring`;
                 `quotient_ring b (Q:B->bool)`] GALOIS_GROUP_FINITE_FIELD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[field_extension] THEN
    SUBGOAL_THEN `field(quotient_ring b (Q:B->bool))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[FIELD_QUOTIENT_RING]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "kP" THEN
    REWRITE_TAC[REWRITE_RULE[GSYM I_DEF] RING_MONOMORPHISM_INCLUSION] THEN
    MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_IMP_FIELD THEN
    ASM_SIMP_TAC[FINITE_SUBRING_GENERATED; INTEGRAL_DOMAIN_SUBRING_GENERATED;
                 FIELD_IMP_INTEGRAL_DOMAIN];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `frobq = \X. if X IN ring_carrier(quotient_ring b Q)
              then ring_pow (quotient_ring b Q) X q else (X:B->bool)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(rho:(B->B)->(B->bool)->(B->bool)) Fr = frobq` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rho"; "frobq"] THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC `X:B->bool` THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `X IN ring_carrier(quotient_ring b (Q:B->bool))`)) THEN
    ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                   `Fr:B->B`; `x:B`] DECOMPOSITION_GROUP_IMAGE_RING_COSET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`b:B ring`; `quotient_ring b (Q:B->bool)`;
                   `ring_coset b (Q:B->bool)`]
      RING_HOMOMORPHISM_POW) THEN
    ASM_SIMP_TAC[RING_EPIMORPHISM_RING_COSET;
                 RING_EPIMORPHISM_IMP_HOMOMORPHISM] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:B`; `q:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `(Fr:B->B) x IN ring_carrier b /\ ring_pow l x q IN ring_carrier b`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ring_pow b = ring_pow (l:B ring)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[RING_POW] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `Fr:B->B` o check (fun th ->
        is_forall(concl th) &&
        free_in `galois_group(k:A ring,l:B ring) h` (concl th))) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`b:B ring`; `Q:B->bool`; `(Fr:B->B) x`; `ring_pow l x q:B`]
      RING_COSET_EQ) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(group_carrier(decomposition_group(k,l) (h:A->B) Q)) /\
    FINITE(group_carrier(galois_group(kP,quotient_ring b (Q:B->bool)) I))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `group_carrier(galois_group(k,l) (h:A->B))` THEN
      ASM_SIMP_TAC[FINITE_GALOIS_GROUP] THEN
      REWRITE_TAC[DECOMPOSITION_GROUP] THEN SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [group_epimorphism] o
        check (fun th -> let hd = fst(strip_comb(concl th)) in
                         is_const hd &&
                         fst(dest_const hd) = "group_epimorphism")) THEN
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
      SIMP_TAC[FINITE_IMAGE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `group_monomorphism
     (decomposition_group(k,l) (h:A->B) Q,
      galois_group(kP,quotient_ring b (Q:B->bool)) I) rho`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GROUP_MONOMORPHISM; DECOMPOSITION_GROUP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `group_element_order (decomposition_group(k,l) (h:A->B) Q) Fr =
    extension_degree (kP,quotient_ring b (Q:B->bool)) I`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rho:(B->B)->(B->bool)->(B->bool)`;
                   `decomposition_group(k,l) (h:A->B) Q`;
                   `galois_group(kP,quotient_ring b (Q:B->bool)) I`; `Fr:B->B`]
      GROUP_ELEMENT_ORDER_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`galois_group(kP,quotient_ring b (Q:B->bool)) I`;
                   `frobq:(B->bool)->(B->bool)`]
      SUBGROUP_GENERATED_ELEMENT_ORDER) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`decomposition_group(k,l) (h:A->B) Q`; `Fr:B->B`]
      SUBGROUP_GENERATED_ELEMENT_ORDER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[decomposition_group] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUBGROUP_GENERATED_IDEMPOT_GEN THEN
    REWRITE_TAC[GSYM decomposition_group] THEN ASM SET_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      lhand(concl th) = `group_element_order
         (decomposition_group(k,l) (h:A->B) Q) Fr`)) THEN
    REWRITE_TAC[decomposition_group; GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED]]);;

let NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS = prove
 (`!(h:A->B) k l p Q.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
        ramification_index (ring_of_integers k,ring_of_integers l) h Q = 1
        ==> group_carrier(subgroup_generated (galois_group(k,l) h)
                {frobenius_element (k,l) h (ring_of_integers l) Q}) =
            group_carrier(decomposition_group(k,l) h Q) /\
            group_element_order (galois_group(k,l) h)
              (frobenius_element (k,l) h (ring_of_integers l) Q) =
            residue_degree (ring_of_integers k,ring_of_integers l) h Q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `field k /\ ring_homomorphism(k,l) (h:A->B)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_IMP_FIELD_EXTENSION; field_extension;
                  RING_MONOMORPHISM_IMP_HOMOMORPHISM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `Q:B->bool`]
    NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `Q:B->bool`]
    NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `Q:B->bool`]
    NUMBER_FIELD_DECOMPOSITION_GROUP) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
  MATCH_MP_TAC DECOMPOSITION_GROUP_FROBENIUS_GENERATED THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING] THEN
  MESON_TAC[GALOIS_GROUP_RING_OF_INTEGERS]);;

let NUMBER_FIELD_FROBENIUS_CONJUGATE_PRIME = prove
 (`!(h:A->B) k l H p Q g.
        number_field l /\ galois_extension(k,l) h /\
        H subgroup_of galois_group(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        unramified (ring_of_integers k,ring_of_integers l) h p /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
        g IN group_carrier(galois_group(k,l) h)
        ==> prime_ideal (ring_of_integers l) (IMAGE g Q) /\
            IMAGE h p SUBSET IMAGE g Q /\
            frobenius_element (k,l) h (ring_of_integers l) (IMAGE g Q) =
            group_conjugation (galois_group(k,l) h) g
              (frobenius_element (k,l) h (ring_of_integers l) Q) /\
            (group_carrier(decomposition_group(k,l) h (IMAGE g Q)) SUBSET H <=>
             group_conjugation (galois_group(k,l) h) g
               (frobenius_element (k,l) h (ring_of_integers l) Q) IN H)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ q /\ (p /\ q ==> r /\ s) ==> p /\ q /\ r /\ s`) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                   `ring_of_integers l:B ring`; `g:B->B`; `Q:B->bool`]
      GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[RING_OF_INTEGERS_SUBRING; PRIME_IDEAL_IMP_SUBSET] THEN
      MESON_TAC[GALOIS_GROUP_RING_OF_INTEGERS];
      ASM_SIMP_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN
    DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(h:A->B) x` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    CONV_TAC SYM_CONV THEN
    UNDISCH_TAC `g IN group_carrier(galois_group(k,l) (h:A->B))` THEN
    REWRITE_TAC[GALOIS_GROUP; IN_ELIM_THM] THEN
    DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` PRIME_IDEAL_IMP_SUBSET) THEN
    DISCH_THEN(MP_TAC o SPEC `p:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_SUBSET) THEN ASM SET_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `!P. prime_ideal (ring_of_integers l) P /\ IMAGE (h:A->B) p SUBSET P
        ==> ramification_index (ring_of_integers k,ring_of_integers l) h P = 1`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED; weakly_unramified];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `Q:B->bool`]
    NUMBER_FIELD_FROBENIUS_ELEMENT) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[group_conjugation; GALOIS_GROUP]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`;
                 `IMAGE (g:B->B) Q`]
    NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN EQ_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(x:B->B) IN s ==> s SUBSET t ==> x IN t`) THEN
    MATCH_MP_TAC SUBGROUP_GENERATED_INC THEN REWRITE_TAC[IN_SING] THEN
    REWRITE_TAC[SING_SUBSET] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`;
                   `IMAGE (g:B->B) Q`] NUMBER_FIELD_FROBENIUS_ELEMENT) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `IMAGE (g:B->B) Q`]
      (CONJUNCT1 DECOMPOSITION_GROUP)) THEN
    DISCH_THEN SUBST1_TAC THEN SIMP_TAC[IN_ELIM_THM];
    DISCH_TAC THEN MATCH_MP_TAC SUBGROUP_GENERATED_MINIMAL THEN
    ASM_REWRITE_TAC[SING_SUBSET]]);;
