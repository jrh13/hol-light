(* ========================================================================= *)
(* Fractional ideals of a domain r in a field of fractions k along h         *)
(* (field_of_fractions (r,k) h); for r Dedekind their group, valuations and  *)
(* unique factorization, the principal fractional ideals and the class       *)
(* group.                                                                    *)
(*                                                                           *)
(*   fractional_ideal (r,k) h J <=> J is a nonzero h(r)-submodule of k with  *)
(*                                  h(d) J SUBSET h(r) for a nonzero d of r  *)
(*   fractional_ideal_inv (r,k) h J = {x | x J SUBSET h(r)}                  *)
(*   fractional_ideal_group (r,k) h = the group of fractional ideals, with   *)
(*                                  identity h(r), the inverse               *)
(*                                  fractional_ideal_inv and the span of the *)
(*                                  setwise product as product               *)
(*   fractional_ideal_valuation (r,k) h P J = v_P(j) - v_P((d)) for any      *)
(*                                  representation h(d) J = h(j)             *)
(*                                                                           *)
(* The product of J1 and J2 is ring_span (r,k) h (ring_setmul k J1 J2) and   *)
(* the principal fractional ideal of x is ring_span (r,k) h {x}. The former  *)
(* notion in fraction_ring r is the instance h = ring_fractionate r {a |     *)
(* ring_regular r a} (FIELD_OF_FRACTIONS_FRACTION_RING).                     *)
(*                                                                           *)
(* Main results: every fractional ideal is a scaled nonzero ideal            *)
(* (FRACTIONAL_IDEAL_SCALED_IDEAL), products, inverses and principal ideals  *)
(* are fractional ideals (FRACTIONAL_IDEAL_MUL,                              *)
(* FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV, FRACTIONAL_IDEAL_PRINCIPAL). For r *)
(* Dedekind: J J^-1 = h(r) (DEDEKIND_FRACTIONAL_IDEAL_INVERTIBLE,            *)
(* DEDEKIND_FRACTIONAL_IDEAL_MUL_INV), so the fractional ideals form an      *)
(* abelian group (FRACTIONAL_IDEAL_GROUP, ABELIAN_FRACTIONAL_IDEAL_GROUP);   *)
(* the valuations at the nonzero primes P extend ideal_valuation and         *)
(* dedekind_valuation (FRACTIONAL_IDEAL_VALUATION_IMAGE,                     *)
(* FRACTIONAL_IDEAL_VALUATION_PRINCIPAL), are additive on products, change   *)
(* sign on inverses, are nonzero at finitely many P, can be prescribed       *)
(* (FRACTIONAL_IDEAL_PRESCRIBED_VALUATIONS) and determine inclusion,         *)
(* equality and membership (FRACTIONAL_IDEAL_SUBSET_VALUATION,               *)
(* FRACTIONAL_IDEAL_EQ_VALUATION, IN_FRACTIONAL_IDEAL_VALUATION); unique     *)
(* factorization J = prod P^v_P(J) with integer exponents                    *)
(* (DEDEKIND_FRACTIONAL_IDEAL_FACTORIZATION), and the group is free abelian  *)
(* on the nonzero primes (FRACTIONAL_IDEAL_GROUP_FREE_ABELIAN). The          *)
(* principal fractional ideals are the image of k^*                          *)
(* (GROUP_HOMOMORPHISM_PRINCIPAL_FRACTIONAL_IDEAL) with kernel the image of  *)
(* the units of r (GROUP_KERNEL_PRINCIPAL_FRACTIONAL_IDEAL); the exact       *)
(* sequence 1 -> r^* -> k^* -> fractional ideals -> class group -> 1, with   *)
(* h(j) mapped to the class of j (FRACTIONAL_IDEAL_CLASS_GROUP_EXACT), and   *)
(* class_group r is isomorphic to the quotient by the principal fractional   *)
(* ideals (FRACTIONAL_IDEAL_CLASS_GROUP). Classes of products of primes: the *)
(* class of the fractional ideal prod_(P IN t) P^e(P) is prod [P]^e(P)       *)
(* (FRACTIONAL_IDEAL_CLASS_PRIME_SUM), such a product of classes is trivial  *)
(* iff some x has v_P(x) = e(P) on t and 0 elsewhere                         *)
(* (CLASS_GROUP_SUM_PRIME_CLASSES_EQ_ID), and [j] = prod_(P IN t)            *)
(* [P]^(v_P(j) - v_P(x)) when v_P(x) = v_P(j) outside t                      *)
(* (IDEAL_CLASS_EQ_SUM_PRIME_CLASSES).                                       *)
(*                                                                           *)
(* Route: a fractional ideal J is h(d)^-1 h(j) for an ideal j of r, and      *)
(* products correspond to ideal products                                     *)
(* (RING_SPAN_SETMUL_IMAGE_IDEAL_PROD), so the group laws and the valuations *)
(* reduce to the ideal arithmetic of ANT/dedekind.ml; the valuation is well  *)
(* defined by FRACTIONAL_IDEAL_SCALED_IDEAL_COMPARE. The isomorphism with    *)
(* the free abelian group maps J to its valuations, the class map maps       *)
(* h(d)^-1 h(j) to the class of j. The spans of setwise products are those   *)
(* of Library/fieldtheory.ml (RING_SPAN_SETMUL_SPAN, RING_SPAN_SETMUL_ASSOC, *)
(* RING_SPAN_SETMUL_SYM).                                                    *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (IMAGE_HOMOMORPHISM_MUL,                      *)
(* FIELD_OF_FRACTIONS_IMP_MONOMORPHISM), Library/fieldtheory.ml (ring_span,  *)
(* spans of setwise products), Library/grouptheory.ml (free_abelian_group,   *)
(* group_exactness, quotient_group), Library/ring_groups.ml (unit_group),    *)
(* ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml               *)
(* (ideal_class), ANT/dedekind_valuation.ml (dedekind_valuation),            *)
(* ANT/classgroup.ml and ANT/classgroup_group.ml (class_group).              *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/grouptheory.ml";;
needs "Library/ring_groups.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/dedekind_struct.ml";;
needs "ANT/dedekind_valuation.ml";;
needs "ANT/classgroup.ml";;
needs "ANT/classgroup_group.ml";;

(* ------------------------------------------------------------------------- *)
(* Fractional ideals and their inverses.                                     *)
(* ------------------------------------------------------------------------- *)

let fractional_ideal = new_definition
 `fractional_ideal (r:A ring,k:B ring) (h:A->B) (J:B->bool) <=>
        field_of_fractions (r,k) h /\
        J SUBSET ring_carrier k /\ ~(J = {ring_0 k}) /\ ring_0 k IN J /\
        (!x y. x IN J /\ y IN J ==> ring_add k x y IN J) /\
        (!a x. a IN ring_carrier r /\ x IN J ==> ring_mul k (h a) x IN J) /\
        ?d. d IN ring_carrier r /\ ~(d = ring_0 r) /\
            !x. x IN J ==> ring_mul k (h d) x IN IMAGE h (ring_carrier r)`;;

let fractional_ideal_inv = new_definition
 `fractional_ideal_inv (r:A ring,k:B ring) (h:A->B) (J:B->bool) =
        {x | x IN ring_carrier k /\
             !y. y IN J ==> ring_mul k x y IN IMAGE h (ring_carrier r)}`;;

let FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS = prove
 (`!r k (h:A->B) J.
        fractional_ideal (r,k) h J ==> field_of_fractions (r,k) h`,
  SIMP_TAC[fractional_ideal]);;

let FRACTIONAL_IDEAL_IMP_SUBSET = prove
 (`!r k (h:A->B) J. fractional_ideal (r,k) h J ==> J SUBSET ring_carrier k`,
  SIMP_TAC[fractional_ideal]);;

let FRACTIONAL_IDEAL_IMP_NONZERO = prove
 (`!r k (h:A->B) J.
        fractional_ideal (r,k) h J ==> ?x. x IN J /\ ~(x = ring_0 k)`,
  REWRITE_TAC[fractional_ideal] THEN SET_TAC[]);;

let IN_FRACTIONAL_IDEAL_0 = prove
 (`!r k (h:A->B) J. fractional_ideal (r,k) h J ==> ring_0 k IN J`,
  SIMP_TAC[fractional_ideal]);;

let IN_FRACTIONAL_IDEAL_ADD = prove
 (`!r k (h:A->B) J x y.
        fractional_ideal (r,k) h J /\ x IN J /\ y IN J
        ==> ring_add k x y IN J`,
  SIMP_TAC[fractional_ideal]);;

let IN_FRACTIONAL_IDEAL_LMUL = prove
 (`!r k (h:A->B) J a x.
        fractional_ideal (r,k) h J /\ a IN ring_carrier r /\ x IN J
        ==> ring_mul k (h a) x IN J`,
  SIMP_TAC[fractional_ideal]);;

let IN_FRACTIONAL_IDEAL_NEG = prove
 (`!r k (h:A->B) J x.
        fractional_ideal (r,k) h J /\ x IN J ==> ring_neg k x IN J`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM o
    MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS) THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[FRACTIONAL_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `J:B->bool`;
                 `ring_neg r (ring_1 r):A`; `x:B`]
    IN_FRACTIONAL_IDEAL_LMUL) THEN
  ASM_SIMP_TAC[RING_NEG; RING_1] THEN
  FIRST_ASSUM(fun th -> SIMP_TAC[RING_1; MATCH_MP RING_HOMOMORPHISM_NEG th;
                                 MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
  ASM_SIMP_TAC[RING_MUL_LNEG; RING_MUL_LID; RING_1]);;

let IN_FRACTIONAL_IDEAL_SUB = prove
 (`!r k (h:A->B) J x y.
        fractional_ideal (r,k) h J /\ x IN J /\ y IN J
        ==> ring_sub k x y IN J`,
  REWRITE_TAC[ring_sub] THEN
  MESON_TAC[IN_FRACTIONAL_IDEAL_ADD; IN_FRACTIONAL_IDEAL_NEG]);;

let FRACTIONAL_IDEAL_RING_SPAN = prove
 (`!r k (h:A->B) J.
        fractional_ideal (r,k) h J ==> ring_span (r,k) h J = J`,
  REWRITE_TAC[fractional_ideal] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RING_SPAN_EQ_SELF THEN ASM_REWRITE_TAC[]);;

(* The image of a nonzero ideal is a fractional ideal.                       *)

let RING_IDEAL_IMP_FRACTIONAL_IDEAL = prove
 (`!r k (h:A->B) j.
        field_of_fractions (r,k) h /\ ring_ideal r j /\ ~(j = {ring_0 r})
        ==> fractional_ideal (r,k) h (IMAGE h j)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
  SUBGOAL_THEN `?a:A. a IN j /\ ~(a = ring_0 r)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_RING_IDEAL_0; SET_RULE
     `(z:A) IN s /\ ~(s = {z}) ==> ?a. a IN s /\ ~(a = z)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((h:A->B) a = ring_0 k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0; SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  ASM_REWRITE_TAC[fractional_ideal] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC(SET_RULE
     `!x:B. x IN s /\ ~(x = z) ==> ~(s = {z})`) THEN
    EXISTS_TAC `(h:A->B) a` THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(h:A->B)(ring_0 r) = ring_0 k`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[IN_RING_IDEAL_0];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `ring_add k ((h:A->B) x) (h y) = h(ring_add r x y)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[IN_RING_IDEAL_ADD]];
    X_GEN_TAC `c:A` THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `ring_mul k ((h:A->B) c) (h x) = h(ring_mul r c x)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[IN_RING_IDEAL_LMUL]];
    EXISTS_TAC `ring_1 r:A` THEN
    ASM_SIMP_TAC[RING_1; INTEGRAL_DOMAIN_NONTRIVIAL] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[RING_MUL_LID; FUN_IN_IMAGE]]]);;

let FRACTIONAL_IDEAL_CARRIER = prove
 (`!r k (h:A->B).
        fractional_ideal (r,k) h (IMAGE h (ring_carrier r)) <=>
        field_of_fractions (r,k) h`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS]; DISCH_TAC] THEN
  MATCH_MP_TAC RING_IDEAL_IMP_FRACTIONAL_IDEAL THEN
  ASM_REWRITE_TAC[RING_IDEAL_CARRIER] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  ASM_MESON_TAC[INTEGRAL_DOMAIN_NONTRIVIAL; RING_1; RING_0; IN_SING]);;

(* Multiples x J by nonzero x and the inverse of a fractional ideal.         *)

let FRACTIONAL_IDEAL_IMAGE_MUL = prove
 (`!r k (h:A->B) J x.
        fractional_ideal (r,k) h J /\ x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> fractional_ideal (r,k) h (IMAGE (ring_mul k x) J)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[fractional_ideal] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `d:A`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (LABEL_TAC "den"))))))))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  SUBGOAL_THEN `!y:B. y IN J ==> y IN ring_carrier k` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!c:A. c IN ring_carrier r ==> (h:A->B) c IN ring_carrier k`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[RING_MUL];
    SUBGOAL_THEN `?y:B. y IN J /\ ~(y = ring_0 k)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!x:B. x IN s /\ ~(x = z) ==> ~(s = {z})`) THEN
    EXISTS_TAC `ring_mul k x y:B` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; INTEGRAL_DOMAIN_MUL_EQ_0];
    SUBGOAL_THEN `ring_0 k:B = ring_mul k x (ring_0 k)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[RING_MUL_RZERO]; ASM_SIMP_TAC[FUN_IN_IMAGE]];
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `ring_add k (ring_mul k x y) (ring_mul k x z) =
      ring_mul k x (ring_add k y (z:B))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[RING_ADD_LDISTRIB]; ASM_SIMP_TAC[FUN_IN_IMAGE]];
    X_GEN_TAC `c:A` THEN DISCH_TAC THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `ring_mul k ((h:A->B) c) (ring_mul k x y) =
      ring_mul k x (ring_mul k (h c) y)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[RING_RULE
       `ring_mul r a (ring_mul r b c) = ring_mul r b (ring_mul r a (c:B))`];
      ASM_SIMP_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:B`]
    FIELD_FRACTION_NONZERO) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  EXISTS_TAC `ring_mul r b d:A` THEN
  ASM_SIMP_TAC[RING_MUL; INTEGRAL_DOMAIN_MUL_EQ_0] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  USE_THEN "den" (MP_TAC o SPEC `y:B`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_IMAGE]] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ring_mul r a c:A` THEN ASM_SIMP_TAC[RING_MUL] THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    rand(concl th) = `(h:A->B) a`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    rand(concl th) = `(h:A->B) c`)) THEN
  ASM_SIMP_TAC[RING_RULE
   `ring_mul r (ring_mul r b d) (ring_mul r x y) =
    ring_mul r (ring_mul r b x) (ring_mul r d (y:B))`]);;

(* Route: with a denominator d of J, the element h(d) is a nonzero member   *)
(* of the inverse; if y0 is a nonzero member of J and h(u) = h(d) y0, then   *)
(* u is a denominator of the inverse.                                        *)

let FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV = prove
 (`!r k (h:A->B) J.
        fractional_ideal (r,k) h J
        ==> fractional_ideal (r,k) h (fractional_ideal_inv (r,k) h J)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fractional_ideal; fractional_ideal_inv] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `d:A`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (LABEL_TAC "den"))))))))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  SUBGOAL_THEN `!y:B. y IN J ==> y IN ring_carrier k` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:A->B) (ring_carrier r) subring_of k` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[ring_image] SUBRING_RING_IMAGE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[];
    REWRITE_TAC[EXTENSION; IN_SING; IN_ELIM_THM; NOT_FORALL_THM] THEN
    EXISTS_TAC `(h:A->B) d` THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0];
    REWRITE_TAC[RING_0];
    ASM_SIMP_TAC[RING_MUL_LZERO; IN_SUBRING_0];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RING_ADD; RING_ADD_RDISTRIB; IN_SUBRING_ADD];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RING_MUL; GSYM RING_MUL_ASSOC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y0:B. y0 IN J /\ ~(y0 = ring_0 k)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?u:A. u IN ring_carrier r /\ (h:A->B) u = ring_mul k (h d) y0`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "den" (MP_TAC o SPEC `y0:B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_IMAGE]] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `u:A` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(h:A->B)(ring_0 r) = ring_mul k (h d) y0` THEN
    DISCH_THEN(MP_TAC o SYM) THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0] THEN
    ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0];
    X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RING_RULE
     `ring_mul r (ring_mul r a b) c = ring_mul r a (ring_mul r c (b:B))`] THEN
    MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC[FUN_IN_IMAGE]]);;

let FRACTIONAL_IDEAL_DENOMINATOR = prove
 (`!r k (h:A->B) J.
        fractional_ideal (r,k) h J
        ==> ?d. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                !x. x IN J ==> ring_mul k (h d) x IN IMAGE h (ring_carrier r)`,
  SIMP_TAC[fractional_ideal]);;

(* The image of a product of ideals is the product of the images.            *)

let RING_SPAN_SETMUL_IMAGE_IDEAL_PROD = prove
 (`!(h:A->B) r k i j.
        ring_homomorphism(r,k) h /\ ring_ideal r i /\ ring_ideal r j
        ==> ring_span (r,k) h (ring_setmul k (IMAGE h i) (IMAGE h j)) =
            IMAGE h (ideal_prod r i j)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET o
    check (fun th -> concl th = t))) [`ring_ideal r (i:A->bool)`;
                                      `ring_ideal r (j:A->bool)`] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_SPAN_MINIMAL THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(h:A->B)(ring_0 r) = ring_0 k`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      MESON_TAC[RING_IDEAL_IDEAL_PROD; IN_RING_IDEAL_0];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `(x:A) IN ring_carrier r /\ (y:A) IN ring_carrier r`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_PROD; SUBSET];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `ring_add k ((h:A->B) x) (h y) = h(ring_add r x y)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_MESON_TAC[IN_RING_IDEAL_ADD; RING_IDEAL_IDEAL_PROD]];
      X_GEN_TAC `a:A` THEN DISCH_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:A) IN ring_carrier r` ASSUME_TAC THENL
       [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_PROD; SUBSET];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `ring_mul k ((h:A->B) a) (h y) = h(ring_mul r a y)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_MESON_TAC[IN_RING_IDEAL_LMUL; RING_IDEAL_IDEAL_PROD]];
      MATCH_MP_TAC(SET_RULE `(s:B->bool) SUBSET t ==> u INTER s SUBSET t`) THEN
      REWRITE_TAC[SUBSET; ring_setmul; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `(x:A) IN ring_carrier r /\ (y:A) IN ring_carrier r`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `ring_mul k ((h:A->B) x) (h y) = h(ring_mul r x y)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_SIMP_TAC[RING_MUL_IN_IDEAL_PROD]]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[IDEAL_PROD_EXPLICIT; SUBSET; FORALL_IN_IMAGE;
               FORALL_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `u:num->A`; `v:num->A`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. i < n ==> (u:num->A) i IN ring_carrier r /\
     (v:num->A) i IN ring_carrier r`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\i. ring_mul r ((u:num->A) i) (v i)`; `{i:num | i < n}`]
    (MATCH_MP RING_HOMOMORPHISM_SUM
      (ASSUME `ring_homomorphism(r,k) (h:A->B)`))) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL; o_DEF] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SPAN_SUM THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC RING_SPAN_INC THEN ASM_SIMP_TAC[RING_MUL] THEN
  REWRITE_TAC[ring_setmul; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`(h:A->B)((u:num->A) i)`; `(h:A->B)((v:num->A) i)`] THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE]);;

(* The fractional ideals inside h(r) are the images of the nonzero ideals.   *)

let FRACTIONAL_IDEAL_INTEGRAL = prove
 (`!r k (h:A->B) J.
        fractional_ideal (r,k) h J /\ J SUBSET IMAGE h (ring_carrier r) <=>
        field_of_fractions (r,k) h /\
        ?j. ring_ideal r j /\ ~(j = {ring_0 r}) /\ J = IMAGE h j`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC; MESON_TAC[RING_IDEAL_IMP_FRACTIONAL_IDEAL; IMAGE_SUBSET;
                         RING_IDEAL_IMP_SUBSET]] THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `{a:A | a IN ring_carrier r /\ (h:A->B) a IN J}` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[RING_IDEAL; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[] THEN
    ASM_SIMP_TAC[RING_0; RING_ADD; RING_MUL] THEN
    ASM_MESON_TAC[IN_FRACTIONAL_IDEAL_0; IN_FRACTIONAL_IDEAL_ADD;
                  IN_FRACTIONAL_IDEAL_LMUL];
    FIRST_ASSUM(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC o
      MATCH_MP FRACTIONAL_IDEAL_IMP_NONZERO) THEN
    SUBGOAL_THEN `?a:A. a IN ring_carrier r /\ (h:A->B) a = x`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!a:A. a IN j /\ ~(a = z) ==> ~(j = {z})`) THEN
    EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    ASM SET_TAC[]]);;

let FRACTIONAL_IDEAL_SCALED_IDEAL = prove
 (`!r k (h:A->B) J.
        fractional_ideal (r,k) h J
        ==> ?d j. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                  ring_ideal r j /\ ~(j = {ring_0 r}) /\
                  IMAGE (ring_mul k (h d)) J = IMAGE h j`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `d:A` STRIP_ASSUME_TAC o
    MATCH_MP FRACTIONAL_IDEAL_DENOMINATOR) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`;
                 `IMAGE (ring_mul k ((h:A->B) d)) J`]
    FRACTIONAL_IDEAL_INTEGRAL) THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC FRACTIONAL_IDEAL_IMAGE_MUL THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_MONOMORPHISM_EQ_0];
    DISCH_THEN(X_CHOOSE_THEN `j:A->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    MAP_EVERY EXISTS_TAC [`d:A`; `j:A->bool`] THEN ASM_REWRITE_TAC[]]);;

(* Converse: h(d)^-1 h(j) is a fractional ideal.                            *)

let FRACTIONAL_IDEAL_SCALED_IDEAL_EQ = prove
 (`!r k (h:A->B) J.
        fractional_ideal (r,k) h J <=>
        field_of_fractions (r,k) h /\ J SUBSET ring_carrier k /\
        ?d j. d IN ring_carrier r /\ ~(d = ring_0 r) /\
              ring_ideal r j /\ ~(j = {ring_0 r}) /\
              IMAGE (ring_mul k (h d)) J = IMAGE h j`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS];
      ASM_MESON_TAC[FRACTIONAL_IDEAL_IMP_SUBSET];
      ASM_MESON_TAC[FRACTIONAL_IDEAL_SCALED_IDEAL]];
    STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  SUBGOAL_THEN
   `(h:A->B) d IN ring_carrier k /\ ~(h d = ring_0 k)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_MONOMORPHISM_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `J = IMAGE (ring_mul k (ring_inv k ((h:A->B) d)))
              (IMAGE (ring_mul k (h d)) J)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:B. x IN s ==> f x = x) ==> s = IMAGE f s`) THEN
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:B) IN ring_carrier k` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_MUL_ASSOC; RING_INV; FIELD_MUL_LINV; RING_MUL_LID];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FRACTIONAL_IDEAL_IMAGE_MUL THEN
    ASM_SIMP_TAC[RING_IDEAL_IMP_FRACTIONAL_IDEAL; RING_INV] THEN
    ASM_MESON_TAC[FIELD_INV_EQ_0]]);;

(* Products of fractional ideals are fractional ideals.                      *)

let FRACTIONAL_IDEAL_MUL = prove
 (`!r k (h:A->B) J1 J2.
        fractional_ideal (r,k) h J1 /\ fractional_ideal (r,k) h J2
        ==> fractional_ideal (r,k) h (ring_span (r,k) h (ring_setmul k J1 J2))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  SUBGOAL_THEN
   `(J1:B->bool) SUBSET ring_carrier k /\ (J2:B->bool) SUBSET ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FRACTIONAL_IDEAL_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:A->B) (ring_carrier r) subring_of k` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[ring_image] SUBRING_RING_IMAGE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:A. a IN ring_carrier r ==> (h:A->B) a IN ring_carrier k`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  ASM_REWRITE_TAC[fractional_ideal; RING_SPAN_SUBSET; RING_SPAN_0] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `J1:B->bool`]
      FRACTIONAL_IDEAL_IMP_NONZERO) THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `J2:B->bool`]
      FRACTIONAL_IDEAL_IMP_NONZERO) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `y:B` THEN STRIP_TAC THEN X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!x:B. x IN s /\ ~(x = z) ==> ~(s = {z})`) THEN
    EXISTS_TAC `ring_mul k x y:B` THEN
    SUBGOAL_THEN `(x:B) IN ring_carrier k /\ (y:B) IN ring_carrier k`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0] THEN MATCH_MP_TAC RING_SPAN_INC THEN
    ASM_SIMP_TAC[RING_MUL] THEN REWRITE_TAC[ring_setmul; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`x:B`; `y:B`] THEN ASM_REWRITE_TAC[];
    SIMP_TAC[RING_SPAN_ADD];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SPAN_MUL THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `J1:B->bool`]
    FRACTIONAL_IDEAL_DENOMINATOR) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `J2:B->bool`]
    FRACTIONAL_IDEAL_DENOMINATOR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d2:A` THEN STRIP_TAC THEN X_GEN_TAC `d1:A` THEN STRIP_TAC THEN
  EXISTS_TAC `ring_mul r d1 d2:A` THEN
  ASM_SIMP_TAC[RING_MUL; INTEGRAL_DOMAIN_MUL_EQ_0] THEN
  SUBGOAL_THEN
   `ring_span (r,k) h (ring_setmul k J1 J2) SUBSET
    {z | z IN ring_carrier k /\
         ring_mul k ((h:A->B)(ring_mul r d1 d2)) z IN
         IMAGE h (ring_carrier r)}`
  (fun th -> MP_TAC th THEN SET_TAC[]) THEN
  MATCH_MP_TAC RING_SPAN_MINIMAL THEN REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `(h:A->B)(ring_mul r d1 d2) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[RING_0];
    ASM_SIMP_TAC[RING_MUL_RZERO; IN_SUBRING_0];
    MAP_EVERY X_GEN_TAC [`y:B`; `z:B`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RING_ADD; RING_ADD_LDISTRIB; IN_SUBRING_ADD];
    MAP_EVERY X_GEN_TAC [`a:A`; `y:B`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RING_MUL; RING_RULE
     `ring_mul r a (ring_mul r b c) = ring_mul r b (ring_mul r a (c:B))`] THEN
    MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    MATCH_MP_TAC(SET_RULE `(s:B->bool) SUBSET t ==> u INTER s SUBSET t`) THEN
    REWRITE_TAC[ring_setmul; SUBSET; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:B) IN ring_carrier k /\ (y:B) IN ring_carrier k`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[RING_MUL]] THEN
    SUBGOAL_THEN
     `ring_mul k ((h:A->B)(ring_mul r d1 d2)) (ring_mul k x y) =
      ring_mul k (ring_mul k (h d1) x) (ring_mul k (h d2) y)`
    SUBST1_TAC THENL
     [FIRST_ASSUM(fun th ->
        ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]) THEN
      ASM_SIMP_TAC[RING_RULE
       `ring_mul r (ring_mul r a b) (ring_mul r x y) =
        ring_mul r (ring_mul r a x) (ring_mul r b (y:B))`];
      MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC[]]]);;

(* h(r) is the identity for the product.                                     *)

let FRACTIONAL_IDEAL_MUL_LID = prove
 (`!r k (h:A->B) J.
        fractional_ideal (r,k) h J
        ==> ring_span (r,k) h (ring_setmul k (IMAGE h (ring_carrier r)) J) =
            J`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FRACTIONAL_IDEAL_IMP_SUBSET) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
      [GSYM(MATCH_MP FRACTIONAL_IDEAL_RING_SPAN th)]) THEN
    MATCH_MP_TAC RING_SPAN_MONO THEN
    REWRITE_TAC[ring_setmul; SUBSET; FORALL_IN_GSPEC; IMP_CONJ;
                RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[IN_FRACTIONAL_IDEAL_LMUL];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    MATCH_MP_TAC RING_SPAN_INC THEN
    SUBGOAL_THEN `(x:B) IN ring_carrier k` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[ring_setmul; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`(h:A->B)(ring_1 r)`; `x:B`] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; RING_1] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
    ASM_SIMP_TAC[RING_MUL_LID]]);;

let DEDEKIND_FRACTIONAL_IDEAL_INVERTIBLE = prove
 (`!r k (h:A->B) J.
        dedekind_domain r /\ fractional_ideal (r,k) h J
        ==> ?n x y. (!i. i < n:num
                         ==> x i IN J /\
                             y i IN fractional_ideal_inv (r,k) h J) /\
                    ring_sum k {i | i < n}
                      (\i. ring_mul k (x i) (y i)) =
                    ring_1 k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FRACTIONAL_IDEAL_IMP_SUBSET) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FRACTIONAL_IDEAL_SCALED_IDEAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:A`; `j:A->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`] DEDEKIND_IDEAL_INVERTIBLE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:A`; `n:num`; `u:num->A`; `v:num->A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i < n ==> (u:num->A) i IN ring_carrier r /\
                  (v:num->A) i IN ring_carrier r`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[fractional_ideal_inv; IN_ELIM_THM] THEN
  SUBGOAL_THEN `!x. x IN J ==> x IN ring_carrier(k:B ring)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN ring_carrier r ==> ((h:A->B) x = ring_0 k <=> x = ring_0 r)`
  ASSUME_TAC THENL [ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  (* x_i IN J with h(u_i) = h(d) x_i. *)
  SUBGOAL_THEN
   `!i. ?z. i < n
            ==> z IN J /\
                (h:A->B)((u:num->A) i) = ring_mul k (h d) z`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(h:A->B)((u:num->A) i) IN IMAGE (ring_mul k (h d)) J`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]];
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `z:num->B` THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `ring_inv k ((h:A->B) c) IN ring_carrier k /\
    ring_mul k (h c) (ring_inv k (h c)) = ring_1 k`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[RING_INV; FIELD_MUL_RINV]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`n:num`; `z:num->B`;
    `\i. ring_mul k (ring_mul k ((h:A->B) d) (h((v:num->A) i)))
                     (ring_inv k (h(c:A)))`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [(* y_i = h(d) h(v_i) / h(c) is in the inverse. *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(v:num->A) i IN ring_carrier r /\
      (h:A->B) d IN ring_carrier k /\ h(v i) IN ring_carrier k`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ASM_SIMP_TAC[RING_MUL]] THEN
    X_GEN_TAC `w:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ring_mul k ((h:A->B) d) w IN IMAGE h j` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (ring_mul k ((h:A->B) d)) J = IMAGE h j` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC `a:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?b:A. b IN ring_carrier r /\ ring_mul r a ((v:num->A) i) = ring_mul r c b`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `a:A` (CONJUNCT2(CONJUNCT2(MATCH_MP (ASSUME
       `!i. i < n ==> (u:num->A) i IN j /\ v i IN ring_carrier r /\
                      !a. a IN j ==> ring_divides r c (ring_mul r a (v i))`)
       (ASSUME `i:num < n`))))) THEN
      ASM_REWRITE_TAC[ring_divides] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_mul k ((h:A->B) a) (h((v:num->A) i)) =
      ring_mul k (h c) (h b)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `h:A->B`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `b:A` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
     `ring_mul k ((h:A->B) d) w = h a /\
      ring_mul k (h a) (h((v:num->A) i)) = ring_mul k (h c) (h b) /\
      ring_mul k (h c) (ring_inv k (h c)) = ring_1 k
      ==> ring_mul k (ring_mul k (ring_mul k (h d) (h (v i)))
                                   (ring_inv k (h c))) w = h b`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* The sum is h(c) / h(c) = 1. *)
  TRANS_TAC EQ_TRANS
   `ring_sum k {i | i < n}
      (\i:num. ring_mul k ((h:A->B)(ring_mul r (u i) (v i)))
                       (ring_inv k (h(c:A))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(u:num->A) i IN ring_carrier r /\ (v:num->A) i IN ring_carrier r /\
      (h:A->B) d IN ring_carrier k /\ h(v i) IN ring_carrier k /\
      (z:num->B) i IN ring_carrier k /\
      h(u i) = ring_mul k (h d) (z i)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_RULE
     `ring_mul k z (ring_mul k (ring_mul k a b) c) =
      ring_mul k (ring_mul k (ring_mul k a z) b) (c:B)`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:B ring`;
                 `\i:num. (h:A->B)(ring_mul r (u i) (v i))`;
                 `ring_inv k ((h:A->B) c)`; `{i:num | i < n}`]
    RING_SUM_RMUL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`\i. ring_mul r ((u:num->A) i) (v i)`; `{i:num | i < n}`]
    (MATCH_MP RING_HOMOMORPHISM_SUM
      (ASSUME `ring_homomorphism (r,k) (h:A->B)`))) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL; o_DEF] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

let DEDEKIND_FRACTIONAL_IDEAL_MUL_INV = prove
 (`!r k (h:A->B) J.
        dedekind_domain r /\ fractional_ideal (r,k) h J
        ==> ring_span (r,k) h
              (ring_setmul k J (fractional_ideal_inv (r,k) h J)) =
            IMAGE h (ring_carrier r)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FRACTIONAL_IDEAL_IMP_SUBSET) THEN
  SUBGOAL_THEN `IMAGE (h:A->B) (ring_carrier r) subring_of k` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[ring_image] SUBRING_RING_IMAGE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `fractional_ideal_inv (r,k) (h:A->B) J SUBSET ring_carrier k`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV;
                  FRACTIONAL_IDEAL_IMP_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_SPAN_MINIMAL THEN
    ASM_SIMP_TAC[IN_SUBRING_0; IN_SUBRING_ADD] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE];
      MATCH_MP_TAC(SET_RULE `(s:B->bool) SUBSET t ==> u INTER s SUBSET t`) THEN
      REWRITE_TAC[ring_setmul; SUBSET; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[fractional_ideal_inv; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:B) IN ring_carrier k` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[RING_MUL_SYM]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `J:B->bool`]
    DEDEKIND_FRACTIONAL_IDEAL_INVERTIBLE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `x:num->B`; `y:num->B`] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h:A->B) a IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(h:A->B) a =
    ring_mul k (h a) (ring_sum k {i | i < n}
                       (\i. ring_mul k ((x:num->B) i) (y i)))`
  SUBST1_TAC THENL [ASM_SIMP_TAC[RING_MUL_RID]; ALL_TAC] THEN
  MATCH_MP_TAC RING_SPAN_MUL THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN MATCH_MP_TAC RING_SPAN_SUM THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC RING_SPAN_INC THEN
  SUBGOAL_THEN
   `(x:num->B) i IN ring_carrier k /\ (y:num->B) i IN ring_carrier k`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[RING_MUL]] THEN
  REWRITE_TAC[ring_setmul; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`(x:num->B) i`; `(y:num->B) i`] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The group of fractional ideals of a Dedekind domain.                      *)
(* ------------------------------------------------------------------------- *)

let fractional_ideal_group = new_definition
 `fractional_ideal_group (r:A ring,k:B ring) (h:A->B) =
    group({J | fractional_ideal (r,k) h J},
          IMAGE h (ring_carrier r),
          fractional_ideal_inv (r,k) h,
          (\J1 J2. ring_span (r,k) h (ring_setmul k J1 J2)))`;;

let FRACTIONAL_IDEAL_GROUP = prove
 (`!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> group_carrier(fractional_ideal_group (r,k) h) =
              {J | fractional_ideal (r,k) h J} /\
            group_id(fractional_ideal_group (r,k) h) =
              IMAGE h (ring_carrier r) /\
            group_inv(fractional_ideal_group (r,k) h) =
              fractional_ideal_inv (r,k) h /\
            group_mul(fractional_ideal_group (r,k) h) =
              (\J1 J2. ring_span (r,k) h (ring_setmul k J1 J2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl fractional_ideal_group)))))
   (CONJUNCT2 group_tybij)))) THEN
  REWRITE_TAC[GSYM fractional_ideal_group] THEN ANTS_TAC THENL
   [ALL_TAC; SIMP_TAC[group_carrier; group_id; group_inv; group_mul]] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_CARRIER; FRACTIONAL_IDEAL_MUL;
               FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RING_SPAN_SETMUL_ASSOC THEN
    ASM_MESON_TAC[FRACTIONAL_IDEAL_IMP_SUBSET];
    X_GEN_TAC `J:B->bool` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[FRACTIONAL_IDEAL_MUL_LID] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SPAN_SETMUL_SYM o
      lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[FRACTIONAL_IDEAL_IMP_SUBSET; FRACTIONAL_IDEAL_CARRIER];
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[FRACTIONAL_IDEAL_MUL_LID]];
    X_GEN_TAC `J:B->bool` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[DEDEKIND_FRACTIONAL_IDEAL_MUL_INV] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SPAN_SETMUL_SYM o
      lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[FRACTIONAL_IDEAL_IMP_SUBSET;
                    FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV];
      DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[DEDEKIND_FRACTIONAL_IDEAL_MUL_INV]]]);;

let ABELIAN_FRACTIONAL_IDEAL_GROUP = prove
 (`!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> abelian_group(fractional_ideal_group (r,k) h)`,
  SIMP_TAC[abelian_group; FRACTIONAL_IDEAL_GROUP; IN_ELIM_THM] THEN
  MESON_TAC[RING_SPAN_SETMUL_SYM; FRACTIONAL_IDEAL_IMP_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Valuations of fractional ideals.                                          *)
(* ------------------------------------------------------------------------- *)

(* Two representations h(d) J = h(j) and h(e) J = h(i) give (e) j = (d) i. *)

let FRACTIONAL_IDEAL_SCALED_IDEAL_COMPARE = prove
 (`!r k (h:A->B) J d j d' j'.
        field_of_fractions (r,k) h /\ J SUBSET ring_carrier k /\
        d IN ring_carrier r /\ d' IN ring_carrier r /\
        ring_ideal r j /\ ring_ideal r j' /\
        IMAGE (ring_mul k (h d)) J = IMAGE h j /\
        IMAGE (ring_mul k (h d')) J = IMAGE h j'
        ==> ideal_prod r (ideal_generated r {d'}) j =
            ideal_prod r (ideal_generated r {d}) j'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  ASM_SIMP_TAC[IDEAL_PROD_SCALE] THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET o
    check (fun th -> concl th = t))) [`ring_ideal r (j:A->bool)`;
                                      `ring_ideal r (j':A->bool)`] THEN
  SUBGOAL_THEN
   `IMAGE (ring_mul r d') j SUBSET ring_carrier r /\
    IMAGE (ring_mul r (d:A)) j' SUBSET ring_carrier r`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[RING_MUL; SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `!(f:A->B) u. (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\
                 s SUBSET u /\ t SUBSET u /\ IMAGE f s = IMAGE f t
                 ==> s = t`) THEN
  MAP_EVERY EXISTS_TAC [`h:A->B`; `ring_carrier r:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_INJECTIVE_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[IMAGE_HOMOMORPHISM_MUL] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    rand(concl th) = `IMAGE (h:A->B) j'`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    rand(concl th) = `IMAGE (h:A->B) j`)) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x:B. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE (g:B->B) s`) THEN
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(x:B) IN ring_carrier k /\ (h:A->B) d IN ring_carrier k /\
    h d' IN ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_RULE
   `ring_mul r a (ring_mul r b c) = ring_mul r b (ring_mul r a (c:B))`]);;

let fractional_ideal_valuation = new_definition
 `fractional_ideal_valuation (r:A ring,k:B ring) (h:A->B) (P:A->bool) J =
  @v:int. !d j. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                ring_ideal r j /\ ~(j = {ring_0 r}) /\
                IMAGE (ring_mul k (h d)) J = IMAGE h j
                ==> v = &(ideal_valuation r P j) -
                        &(ideal_valuation r P (ideal_generated r {d}))`;;

let FRACTIONAL_IDEAL_VALUATION = prove
 (`!r k (h:A->B) P J d j.
        dedekind_domain r /\ fractional_ideal (r,k) h J /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        d IN ring_carrier r /\ ~(d = ring_0 r) /\
        ring_ideal r j /\ ~(j = {ring_0 r}) /\
        IMAGE (ring_mul k (h d)) J = IMAGE h j
        ==> fractional_ideal_valuation (r,k) h P J =
            &(ideal_valuation r P j) -
            &(ideal_valuation r P (ideal_generated r {d}))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fractional_ideal_valuation] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `v:int` THEN BETA_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [`d:A`; `j:A->bool`]) THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MAP_EVERY X_GEN_TAC [`d':A`; `j':A->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `J:B->bool`;
                 `d:A`; `j:A->bool`; `d':A`; `j':A->bool`]
    FRACTIONAL_IDEAL_SCALED_IDEAL_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS;
                  FRACTIONAL_IDEAL_IMP_SUBSET];
    DISCH_THEN(MP_TAC o AP_TERM `ideal_valuation r (P:A->bool)`)] THEN
  ASM_SIMP_TAC[IDEAL_VALUATION_IDEAL_PROD; RING_IDEAL_IDEAL_GENERATED;
               IDEAL_GENERATED_EQ_0] THEN
  REWRITE_TAC[INT_ARITH `(a:int) - b = c - d <=> d + a = b + c`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC);;

let FRACTIONAL_IDEAL_VALUATION_IMAGE = prove
 (`!r k (h:A->B) P j.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        ring_ideal r j /\ ~(j = {ring_0 r})
        ==> fractional_ideal_valuation (r,k) h P (IMAGE h j) =
            &(ideal_valuation r P j)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`;
                 `IMAGE (h:A->B) j`; `ring_1 r:A`; `j:A->bool`]
    FRACTIONAL_IDEAL_VALUATION) THEN
  ASM_SIMP_TAC[RING_IDEAL_IMP_FRACTIONAL_IDEAL; RING_1;
               INTEGRAL_DOMAIN_NONTRIVIAL] THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:A. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE (g:A->B) s`) THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC RING_MUL_LID THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_IDEAL_IMP_SUBSET;
                  SUBSET];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `ring_1 r:A`] IDEAL_GENERATED_SING_EQ_CARRIER) THEN
  REWRITE_TAC[RING_1; RING_UNIT_1] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`] IDEAL_VALUATION_CARRIER) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_PROPER_IDEAL; PROPER_IDEAL_ALT];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_SUB_RZERO]]);;

let FRACTIONAL_IDEAL_VALUATION_CARRIER = prove
 (`!r k (h:A->B) P.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r})
        ==> fractional_ideal_valuation (r,k) h P (IMAGE h (ring_carrier r)) =
            &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`;
                 `ring_carrier r:A->bool`]
    FRACTIONAL_IDEAL_VALUATION_IMAGE) THEN
  ASM_REWRITE_TAC[RING_IDEAL_CARRIER] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[DEDEKIND_IMP_INTEGRAL_DOMAIN; INTEGRAL_DOMAIN_NONTRIVIAL;
                  RING_1; RING_0; IN_SING];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_EQ] THEN MATCH_MP_TAC IDEAL_VALUATION_CARRIER THEN
  ASM_MESON_TAC[PRIME_IMP_PROPER_IDEAL; PROPER_IDEAL_ALT]);;

(* A representation of the product from representations of the factors.     *)

let FRACTIONAL_IDEAL_SCALED_IDEAL_MUL = prove
 (`!r k (h:A->B) J1 J2 d1 j1 d2 j2.
        fractional_ideal (r,k) h J1 /\ fractional_ideal (r,k) h J2 /\
        d1 IN ring_carrier r /\ d2 IN ring_carrier r /\
        ring_ideal r j1 /\ ring_ideal r j2 /\
        IMAGE (ring_mul k (h d1)) J1 = IMAGE h j1 /\
        IMAGE (ring_mul k (h d2)) J2 = IMAGE h j2
        ==> IMAGE (ring_mul k (h(ring_mul r d1 d2)))
                  (ring_span (r,k) h (ring_setmul k J1 J2)) =
            IMAGE h (ideal_prod r j1 j2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  SUBGOAL_THEN
   `(J1:B->bool) SUBSET ring_carrier k /\ (J2:B->bool) SUBSET ring_carrier k /\
    (h:A->B) d1 IN ring_carrier k /\ h d2 IN ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FRACTIONAL_IDEAL_IMP_SUBSET; RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]) THEN
  ASM_SIMP_TAC[GSYM RING_SPAN_IMAGE_MUL; RING_MUL; RING_SETMUL] THEN
  ASM_SIMP_TAC[GSYM RING_SETMUL_IMAGE_MUL] THEN
  ASM_SIMP_TAC[RING_SPAN_SETMUL_IMAGE_IDEAL_PROD]);;

(* Common denominators of two fractional ideals.                             *)

let FRACTIONAL_IDEAL_COMMON_DENOMINATOR = prove
 (`!r k (h:A->B) J1 J2.
        fractional_ideal (r,k) h J1 /\ fractional_ideal (r,k) h J2
        ==> ?d j1 j2. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                      ring_ideal r j1 /\ ~(j1 = {ring_0 r}) /\
                      ring_ideal r j2 /\ ~(j2 = {ring_0 r}) /\
                      IMAGE (ring_mul k (h d)) J1 = IMAGE h j1 /\
                      IMAGE (ring_mul k (h d)) J2 = IMAGE h j2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  SUBGOAL_THEN `IMAGE (h:A->B) (ring_carrier r) subring_of k` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[ring_image] SUBRING_RING_IMAGE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `J1:B->bool`]
    FRACTIONAL_IDEAL_DENOMINATOR) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `J2:B->bool`]
    FRACTIONAL_IDEAL_DENOMINATOR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d2:A` THEN STRIP_TAC THEN X_GEN_TAC `d1:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!J d d'. fractional_ideal (r,k) h J /\
             d IN ring_carrier r /\ ~(d = ring_0 r) /\
             d' IN ring_carrier r /\ ~(d' = ring_0 r) /\
             (!x. x IN J ==>
               ring_mul k ((h:A->B) d) x IN IMAGE h (ring_carrier r))
             ==> ?j. ring_ideal r j /\ ~(j = {ring_0 r}) /\
                     IMAGE (ring_mul k (h(ring_mul r d d'))) J = IMAGE h j`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`;
                   `IMAGE (ring_mul k ((h:A->B)(ring_mul r d d'))) J`]
      FRACTIONAL_IDEAL_INTEGRAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `(h:A->B)(ring_mul r d d') IN ring_carrier k /\
      ~(h(ring_mul r d d') = ring_0 k)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[RING_MUL; RING_HOMOMORPHISM_IN_CARRIER];
        ASM_SIMP_TAC[RING_MUL; RING_MONOMORPHISM_EQ_0;
                     INTEGRAL_DOMAIN_MUL_EQ_0]];
      ASM_SIMP_TAC[FRACTIONAL_IDEAL_IMAGE_MUL]] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FRACTIONAL_IDEAL_IMP_SUBSET) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:B` THEN
      DISCH_TAC THEN
    SUBGOAL_THEN
     `ring_mul k ((h:A->B)(ring_mul r d d')) x =
      ring_mul k (h d') (ring_mul k (h d) x)`
    SUBST1_TAC THENL
     [FIRST_ASSUM(fun th ->
        ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]) THEN
      SUBGOAL_THEN
       `(x:B) IN ring_carrier k /\ (h:A->B) d IN ring_carrier k /\
        h d' IN ring_carrier k`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET; RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
      ASM_SIMP_TAC[RING_RULE
       `ring_mul r (ring_mul r a b) c = ring_mul r b (ring_mul r a (c:B))`];
      MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC[FUN_IN_IMAGE]];
    DISCH_TAC] THEN
  EXISTS_TAC `ring_mul r d1 d2:A` THEN
  ASM_SIMP_TAC[RING_MUL; INTEGRAL_DOMAIN_MUL_EQ_0] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`J1:B->bool`; `d1:A`; `d2:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `j1:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`J2:B->bool`; `d2:A`; `d1:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_mul r d2 d1:A = ring_mul r d1 d2` SUBST1_TAC THENL
   [ASM_MESON_TAC[RING_MUL_SYM]; REWRITE_TAC[]]);;

(* Principal fractional ideals h(r) x.                                       *)

let FRACTIONAL_IDEAL_PRINCIPAL = prove
 (`!r k (h:A->B) x.
        field_of_fractions (r,k) h /\ x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> fractional_ideal (r,k) h (ring_span (r,k) h {x})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  ASM_SIMP_TAC[RING_SPAN_SING_IMAGE] THEN
  MATCH_MP_TAC FRACTIONAL_IDEAL_IMAGE_MUL THEN
  ASM_REWRITE_TAC[FRACTIONAL_IDEAL_CARRIER]);;

(* Valuations of products, inverses and principal fractional ideals.         *)

let FRACTIONAL_IDEAL_VALUATION_MUL = prove
 (`!r k (h:A->B) P J1 J2.
        dedekind_domain r /\
        fractional_ideal (r,k) h J1 /\ fractional_ideal (r,k) h J2 /\
        prime_ideal r P /\ ~(P = {ring_0 r})
        ==> fractional_ideal_valuation (r,k) h P
              (ring_span (r,k) h (ring_setmul k J1 J2)) =
            fractional_ideal_valuation (r,k) h P J1 +
            fractional_ideal_valuation (r,k) h P J2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `J1:B->bool`]
    FRACTIONAL_IDEAL_SCALED_IDEAL) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `J2:B->bool`]
    FRACTIONAL_IDEAL_SCALED_IDEAL) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d2:A`; `j2:A->bool`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`d1:A`; `j1:A->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `J1:B->bool`; `J2:B->bool`;
                 `d1:A`; `j1:A->bool`; `d2:A`; `j2:A->bool`]
    FRACTIONAL_IDEAL_SCALED_IDEAL_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`;
                 `ring_span (r,k) (h:A->B) (ring_setmul k J1 J2)`;
                 `ring_mul r d1 d2:A`; `ideal_prod r j1 j2:A->bool`]
    FRACTIONAL_IDEAL_VALUATION) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`;
                 `J1:B->bool`; `d1:A`; `j1:A->bool`]
    FRACTIONAL_IDEAL_VALUATION) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`;
                 `J2:B->bool`; `d2:A`; `j2:A->bool`]
    FRACTIONAL_IDEAL_VALUATION) THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_MUL; RING_MUL; INTEGRAL_DOMAIN_MUL_EQ_0;
               RING_IDEAL_IDEAL_PROD; IDEAL_PROD_EQ_ZERO] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ASM_SIMP_TAC[IDEAL_VALUATION_IDEAL_PROD; IDEAL_VALUATION_PRINCIPAL_MUL] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC);;

let FRACTIONAL_IDEAL_VALUATION_INV = prove
 (`!r k (h:A->B) P J.
        dedekind_domain r /\ fractional_ideal (r,k) h J /\
        prime_ideal r P /\ ~(P = {ring_0 r})
        ==> fractional_ideal_valuation (r,k) h P
              (fractional_ideal_inv (r,k) h J) =
            --(fractional_ideal_valuation (r,k) h P J)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `J:B->bool`;
                 `fractional_ideal_inv (r,k) (h:A->B) J`]
    FRACTIONAL_IDEAL_VALUATION_MUL) THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV;
               DEDEKIND_FRACTIONAL_IDEAL_MUL_INV] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`]
    FRACTIONAL_IDEAL_VALUATION_CARRIER) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS];
    DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC]);;

let FRACTIONAL_IDEAL_VALUATION_PRINCIPAL = prove
 (`!r k (h:A->B) P x.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> fractional_ideal_valuation (r,k) h P (ring_span (r,k) h {x}) =
            dedekind_valuation (r,k) h P x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:B`]
    FIELD_FRACTION_NONZERO) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `x:B`;
                 `a:A`; `b:A`] DEDEKIND_VALUATION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC FRACTIONAL_IDEAL_VALUATION THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_PRINCIPAL; RING_IDEAL_IDEAL_GENERATED;
               IDEAL_GENERATED_EQ_0] THEN
  SUBGOAL_THEN `(h:A->B) b IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM RING_SPAN_IMAGE_MUL; SING_SUBSET; IMAGE_CLAUSES] THEN
  ASM_SIMP_TAC[GSYM RING_SPAN_IMAGE_IDEAL_GENERATED; SING_SUBSET;
               IMAGE_CLAUSES]);;

(* Finite support.                                                           *)

let FRACTIONAL_IDEAL_VALUATION_FINITE = prove
 (`!r k (h:A->B) J.
        dedekind_domain r /\ fractional_ideal (r,k) h J
        ==> FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                        ~(fractional_ideal_valuation (r,k) h P J = &0)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FRACTIONAL_IDEAL_SCALED_IDEAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:A`; `j:A->bool`] THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
         ~(ideal_valuation r P (j:A->bool) = 0)} UNION
    {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
         ~(ideal_valuation r P (ideal_generated r {d:A}) = 0)}` THEN
  ASM_SIMP_TAC[FINITE_UNION; IDEAL_VALUATION_FINITE_SUPPORT;
               RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_EQ_0] THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(fractional_ideal_valuation (r,k) (h:A->B) P J = &0)` THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `J:B->bool`;
                 `d:A`; `j:A->bool`] FRACTIONAL_IDEAL_VALUATION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC);;

(* Containment and equality are decided by the valuations.                  *)

let FRACTIONAL_IDEAL_SUBSET_VALUATION = prove
 (`!r k (h:A->B) J1 J2.
        dedekind_domain r /\
        fractional_ideal (r,k) h J1 /\ fractional_ideal (r,k) h J2
        ==> (J1 SUBSET J2 <=>
             !P. prime_ideal r P /\ ~(P = {ring_0 r})
                 ==> fractional_ideal_valuation (r,k) h P J2 <=
                     fractional_ideal_valuation (r,k) h P J1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `J1:B->bool`; `J2:B->bool`]
    FRACTIONAL_IDEAL_COMMON_DENOMINATOR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:A`; `j1:A->bool`; `j2:A->bool`] THEN STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `(j1:A->bool) SUBSET j2` THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(J1:B->bool) SUBSET ring_carrier k /\
       (J2:B->bool) SUBSET ring_carrier k /\
      (h:A->B) d IN ring_carrier k /\ ~(h d = ring_0 k) /\
      (j1:A->bool) SUBSET ring_carrier r /\ (j2:A->bool) SUBSET ring_carrier r`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FRACTIONAL_IDEAL_IMP_SUBSET; RING_HOMOMORPHISM_IN_CARRIER;
                    RING_MONOMORPHISM_EQ_0; RING_IDEAL_IMP_SUBSET];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `IMAGE (ring_mul k ((h:A->B) d)) J1 SUBSET
      IMAGE (ring_mul k (h d)) J2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `!u. (!x y. x IN u /\ y IN u /\ (f:B->B) x = f y ==> x = y) /\
        s SUBSET u /\ t SUBSET u
        ==> (s SUBSET t <=> IMAGE f s SUBSET IMAGE f t)`) THEN
      EXISTS_TAC `ring_carrier k:B->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[INTEGRAL_DOMAIN_MUL_LCANCEL];
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE
       `!u. (!x y. x IN u /\ y IN u /\ (f:A->B) x = f y ==> x = y) /\
        s SUBSET u /\ t SUBSET u
        ==> (IMAGE f s SUBSET IMAGE f t <=> s SUBSET t)`) THEN
      EXISTS_TAC `ring_carrier r:A->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[RING_MONOMORPHISM_INJECTIVE_EQ]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[DEDEKIND_IDEAL_SUBSET_VALUATION] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `P:A->bool` THEN
  ASM_CASES_TAC `prime_ideal r (P:A->bool) /\ ~(P = {ring_0 r})` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `J1:B->bool`;
                 `d:A`; `j1:A->bool`] FRACTIONAL_IDEAL_VALUATION) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `J2:B->bool`;
                 `d:A`; `j2:A->bool`] FRACTIONAL_IDEAL_VALUATION) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[INT_ARITH `(a:int) - c <= b - c <=> a <= b`; INT_OF_NUM_LE]);;

let FRACTIONAL_IDEAL_EQ_VALUATION = prove
 (`!r k (h:A->B) J1 J2.
        dedekind_domain r /\
        fractional_ideal (r,k) h J1 /\ fractional_ideal (r,k) h J2
        ==> (J1 = J2 <=>
             !P. prime_ideal r P /\ ~(P = {ring_0 r})
                 ==> fractional_ideal_valuation (r,k) h P J1 =
                     fractional_ideal_valuation (r,k) h P J2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [SIMP_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_SUBSET_VALUATION; INT_LE_REFL]);;

let IN_FRACTIONAL_IDEAL_VALUATION = prove
 (`!r k (h:A->B) J x.
        dedekind_domain r /\ fractional_ideal (r,k) h J /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> (x IN J <=>
             !P. prime_ideal r P /\ ~(P = {ring_0 r})
                 ==> fractional_ideal_valuation (r,k) h P J <=
                     dedekind_valuation (r,k) h P x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  TRANS_TAC EQ_TRANS `ring_span (r,k) (h:A->B) {x} SUBSET J` THEN
  CONJ_TAC THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
        [GSYM(MATCH_MP FRACTIONAL_IDEAL_RING_SPAN th)]) THEN
      MATCH_MP_TAC RING_SPAN_MONO THEN ASM SET_TAC[];
      MATCH_MP_TAC(SET_RULE `(x:B) IN s ==> s SUBSET t ==> x IN t`) THEN
      MATCH_MP_TAC RING_SPAN_INC THEN ASM_REWRITE_TAC[IN_SING]];
    ASM_SIMP_TAC[FRACTIONAL_IDEAL_SUBSET_VALUATION; FRACTIONAL_IDEAL_PRINCIPAL;
                 FRACTIONAL_IDEAL_VALUATION_PRINCIPAL]]);;

let FRACTIONAL_IDEAL_INTEGRAL_VALUATION = prove
 (`!r k (h:A->B) J.
        dedekind_domain r /\ fractional_ideal (r,k) h J
        ==> (J SUBSET IMAGE h (ring_carrier r) <=>
             !P. prime_ideal r P /\ ~(P = {ring_0 r})
                 ==> &0 <= fractional_ideal_valuation (r,k) h P J)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS) THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_SUBSET_VALUATION; FRACTIONAL_IDEAL_CARRIER;
               FRACTIONAL_IDEAL_VALUATION_CARRIER]);;

(* Prescribed valuations: the fractional ideals realize every finitely       *)
(* supported family of integers at the nonzero primes.                       *)

let FRACTIONAL_IDEAL_PRESCRIBED_VALUATIONS = prove
 (`!r k (h:A->B) (e:(A->bool)->int).
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(e P = &0)}
        ==> ?J. fractional_ideal (r,k) h J /\
                !P. prime_ideal r P /\ ~(P = {ring_0 r})
                    ==> fractional_ideal_valuation (r,k) h P J = e P`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `ep = \P:A->bool. num_of_int(max (&0) (e P))` THEN
  ABBREV_TAC `em = \P:A->bool. num_of_int(max (&0) (--(e P)))` THEN
  SUBGOAL_THEN
   `!P:A->bool. &(ep P):int = max (&0) (e P) /\
                &(em P):int = max (&0) (--(e P))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["ep"; "em"] THEN
    CONJ_TAC THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(ep P = 0)} /\
    FINITE {P:A->bool | prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(em P = 0)}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE
     [IMP_CONJ] FINITE_SUBSET)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `P:A->bool` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `ep:(A->bool)->num`] IDEAL_OF_VALUATIONS) THEN
  MP_TAC(ISPECL [`r:A ring`; `em:(A->bool)->num`] IDEAL_OF_VALUATIONS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `jp = ideal_of_valuations r (ep:(A->bool)->num)` THEN
  ABBREV_TAC `jm = ideal_of_valuations r (em:(A->bool)->num)` THEN
  REPEAT STRIP_TAC THEN
  EXISTS_TAC
   `ring_span (r,k) (h:A->B)
      (ring_setmul k (IMAGE h jp)
                     (fractional_ideal_inv (r,k) h (IMAGE h jm)))` THEN
  SUBGOAL_THEN
   `fractional_ideal (r,k) (h:A->B) (IMAGE h jp) /\
    fractional_ideal (r,k) (h:A->B) (IMAGE h jm)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IMP_FRACTIONAL_IDEAL]; ALL_TAC] THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_MUL; FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV] THEN
  X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_VALUATION_MUL; FRACTIONAL_IDEAL_VALUATION_INV;
               FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV;
               FRACTIONAL_IDEAL_VALUATION_IMAGE] THEN
  INT_ARITH_TAC);;

(* The valuation at P is a homomorphism to the additive group of integers.   *)

let GROUP_HOMOMORPHISM_FRACTIONAL_IDEAL_VALUATION = prove
 (`!r k (h:A->B) P.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r})
        ==> group_homomorphism (fractional_ideal_group (r,k) h,integer_group)
                               (fractional_ideal_valuation (r,k) h P)`,
  SIMP_TAC[GROUP_HOMOMORPHISM; INTEGER_GROUP; SUBSET_UNIV;
           FRACTIONAL_IDEAL_GROUP; IN_ELIM_THM;
           FRACTIONAL_IDEAL_VALUATION_MUL]);;

let FRACTIONAL_IDEAL_VALUATION_PRIME = prove
 (`!r k (h:A->B) P Q.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        prime_ideal r Q /\ ~(Q = {ring_0 r})
        ==> fractional_ideal_valuation (r,k) h Q (IMAGE h P) =
            if P = Q then &1 else &0`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_VALUATION_IMAGE; PRIME_IMP_RING_IDEAL;
               IDEAL_VALUATION_PRIME] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let FRACTIONAL_IDEAL_VALUATION_ZPOW = prove
 (`!r k (h:A->B) P J n.
        dedekind_domain r /\ fractional_ideal (r,k) h J /\
        prime_ideal r P /\ ~(P = {ring_0 r})
        ==> fractional_ideal_valuation (r,k) h P
              (group_zpow (fractional_ideal_group (r,k) h) J n) =
            n * fractional_ideal_valuation (r,k) h P J`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`]
    GROUP_HOMOMORPHISM_FRACTIONAL_IDEAL_VALUATION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_ZPOW) THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_GROUP; IN_ELIM_THM; GROUP_ZPOW_INTEGER_GROUP]);;

(* The valuations of a finite product of integer powers of nonzero primes,   *)
(* and the factorization of a fractional ideal into prime powers.            *)

let FRACTIONAL_IDEAL_VALUATION_PRIME_PRODUCT = prove
 (`!r k (h:A->B) s (e:(A->bool)->int) Q.
        dedekind_domain r /\ field_of_fractions (r,k) h /\ FINITE s /\
        (!P. P IN s ==> prime_ideal r P /\ ~(P = {ring_0 r})) /\
        prime_ideal r Q /\ ~(Q = {ring_0 r})
        ==> fractional_ideal_valuation (r,k) h Q
              (group_sum (fractional_ideal_group (r,k) h) s
                 (\P. group_zpow (fractional_ideal_group (r,k) h)
                        (IMAGE h P) (e P))) =
            if Q IN s then e Q else &0`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `G = fractional_ideal_group (r,k) (h:A->B)` THEN
  SUBGOAL_THEN
   `!P. P IN s ==> IMAGE (h:A->B) P IN group_carrier G`
  ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN ASM_SIMP_TAC[FRACTIONAL_IDEAL_GROUP; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_IDEAL_IMP_FRACTIONAL_IDEAL THEN
    ASM_MESON_TAC[PRIME_IMP_RING_IDEAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(B->bool)group`; `integer_group`;
                 `fractional_ideal_valuation (r,k) (h:A->B) Q`;
                   `s:(A->bool)->bool`;
                 `\P. group_zpow G (IMAGE (h:A->B) P) ((e:(A->bool)->int) P)`]
    GROUP_SUM_HOMOMORPHIC_IMAGE) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "G" THEN
    ASM_SIMP_TAC[ABELIAN_FRACTIONAL_IDEAL_GROUP; ABELIAN_INTEGER_GROUP;
                 GROUP_HOMOMORPHISM_FRACTIONAL_IDEAL_VALUATION] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:(A->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_ZPOW THEN
      UNDISCH_TAC `!P. P IN s ==> IMAGE (h:A->B) P IN group_carrier G` THEN
      EXPAND_TAC "G" THEN ASM_SIMP_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  TRANS_TAC EQ_TRANS
   `group_sum integer_group s
      (\P:A->bool. if P = Q then (e:(A->bool)->int) P else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GROUP_SUM_EQ THEN X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `Q:A->bool`;
                   `IMAGE (h:A->B) P`; `(e:(A->bool)->int) P`]
      FRACTIONAL_IDEAL_VALUATION_ZPOW) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_IDEAL_IMP_FRACTIONAL_IDEAL THEN
      ASM_MESON_TAC[PRIME_IMP_RING_IDEAL];
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[FRACTIONAL_IDEAL_VALUATION_PRIME] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_MUL_RID; INT_MUL_RZERO];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `group_sum integer_group (s INTER {Q:A->bool})
      (\P:A->bool. if P = Q then (e:(A->bool)->int) P else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GROUP_SUM_SUPERSET THEN
    REWRITE_TAC[INTER_SUBSET; INTEGER_GROUP; IN_INTER; IN_SING] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[SET_RULE `(a:A) IN s ==> s INTER {a} = {a}`] THEN
    REWRITE_TAC[GROUP_SUM_SING; INTEGER_GROUP; IN_UNIV];
    ASM_SIMP_TAC[SET_RULE `~((a:A) IN s) ==> s INTER {a} = {}`] THEN
    REWRITE_TAC[GROUP_SUM_CLAUSES_EXISTS; INTEGER_GROUP]]);;

let DEDEKIND_FRACTIONAL_IDEAL_FACTORIZATION = prove
 (`!r k (h:A->B) J.
        dedekind_domain r /\ fractional_ideal (r,k) h J
        ==> group_sum (fractional_ideal_group (r,k) h)
              {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                   ~(fractional_ideal_valuation (r,k) h P J = &0)}
              (\P. group_zpow (fractional_ideal_group (r,k) h) (IMAGE h P)
                     (fractional_ideal_valuation (r,k) h P J)) =
            J`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`]
    FRACTIONAL_IDEAL_EQ_VALUATION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> W(MP_TAC o
    PART_MATCH (lhand o rand) th o snd)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!X. X IN group_carrier(fractional_ideal_group (r,k) (h:A->B))
          ==> fractional_ideal (r,k) h X`
    MATCH_MP_TAC THENL
     [ASM_SIMP_TAC[FRACTIONAL_IDEAL_GROUP; IN_ELIM_THM];
      REWRITE_TAC[GROUP_SUM]];
    DISCH_THEN SUBST1_TAC] THEN
  X_GEN_TAC `Q:A->bool` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_VALUATION_PRIME_PRODUCT;
               FRACTIONAL_IDEAL_VALUATION_FINITE; IN_ELIM_THM] THEN
  MESON_TAC[]);;

(* The group of fractional ideals is free abelian on the nonzero primes, the *)
(* coordinates of J being its valuations.                                    *)

let FRACTIONAL_IDEAL_GROUP_FREE_ABELIAN_EXPLICIT = prove
 (`!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> ?f. group_isomorphism
                  (fractional_ideal_group (r,k) h,
                   free_abelian_group
                     {P | prime_ideal r P /\ ~(P = {ring_0 r})})
                  f /\
                !J P. fractional_ideal (r,k) h J /\
                      prime_ideal r P /\ ~(P = {ring_0 r})
                      ==> dest_frag (f J) P =
                          fractional_ideal_valuation (r,k) h P J`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `v = \J P. if prime_ideal r P /\ ~(P = {ring_0 r})
              then fractional_ideal_valuation (r,k) (h:A->B) P J else &0` THEN
  SUBGOAL_THEN
   `!J. fractional_ideal (r,k) (h:A->B) J
        ==> dest_frag (mk_frag ((v:(B->bool)->(A->bool)->int) J)) = v J`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 frag_tybij)] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `{P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
           ~(fractional_ideal_valuation (r,k) (h:A->B) P J = &0)}` THEN
    ASM_SIMP_TAC[FRACTIONAL_IDEAL_VALUATION_FINITE] THEN
    EXPAND_TAC "v" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\J. mk_frag((v:(B->bool)->(A->bool)->int) J)` THEN
  CONJ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[] THEN EXPAND_TAC "v" THEN SIMP_TAC[]] THEN
  REWRITE_TAC[GROUP_ISOMORPHISM; GROUP_HOMOMORPHISM] THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_GROUP; FREE_ABELIAN_GROUP] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `J:B->bool` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[frag_support; IN_ELIM_THM] THEN
    EXPAND_TAC "v" THEN X_GEN_TAC `P:A->bool` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`J1:B->bool`; `J2:B->bool`] THEN STRIP_TAC THEN
    REWRITE_TAC[FRAG_EQ; DEST_FRAG_ADD] THEN
    ASM_SIMP_TAC[FRACTIONAL_IDEAL_MUL] THEN EXPAND_TAC "v" THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `P:A->bool` THEN
    BETA_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[FRACTIONAL_IDEAL_VALUATION_MUL; INT_ADD_LID];
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `c:(A->bool)frag` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `J:B->bool` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[frag_support; IN_ELIM_THM] THEN
      EXPAND_TAC "v" THEN X_GEN_TAC `P:A->bool` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`;
      `dest_frag(c:(A->bool)frag)`]
      FRACTIONAL_IDEAL_PRESCRIBED_VALUATIONS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `frag_support(c:(A->bool)frag)` THEN
      REWRITE_TAC[FINITE_FRAG_SUPPORT; frag_support] THEN SET_TAC[];
      MATCH_MP_TAC MONO_EXISTS] THEN
    X_GEN_TAC `J:B->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FRAG_EQ] THEN ASM_SIMP_TAC[] THEN EXPAND_TAC "v" THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `P:A->bool` THEN
    BETA_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `!x. x IN frag_support(c:(A->bool)frag)
                     ==> prime_ideal r x /\ ~(x = {ring_0 r})` THEN
    DISCH_THEN(MP_TAC o SPEC `P:A->bool`) THEN
    REWRITE_TAC[frag_support; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`J1:B->bool`; `J2:B->bool`] THEN
    REWRITE_TAC[FRAG_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `J1:B->bool`;
                   `J2:B->bool`] FRACTIONAL_IDEAL_EQ_VALUATION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C AP_THM `P:A->bool`) THEN
    EXPAND_TAC "v" THEN ASM_REWRITE_TAC[]]);;

let FRACTIONAL_IDEAL_GROUP_FREE_ABELIAN = prove
 (`!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> fractional_ideal_group (r,k) h isomorphic_group
            free_abelian_group {P | prime_ideal r P /\ ~(P = {ring_0 r})}`,
  REWRITE_TAC[isomorphic_group] THEN
  MESON_TAC[FRACTIONAL_IDEAL_GROUP_FREE_ABELIAN_EXPLICIT]);;

(* ------------------------------------------------------------------------- *)
(* Principal fractional ideals, the class group and the exact sequence       *)
(* 1 -> r^* -> k^* -> fractional ideals -> class group -> 1.                *)
(* ------------------------------------------------------------------------- *)

let GROUP_HOMOMORPHISM_PRINCIPAL_FRACTIONAL_IDEAL = prove
 (`!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> group_homomorphism (unit_group k,fractional_ideal_group (r,k) h)
                               (\x. ring_span (r,k) h {x})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  ASM_SIMP_TAC[GROUP_HOMOMORPHISM; FRACTIONAL_IDEAL_GROUP; FIELD_UNIT_GROUP;
               SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_DIFF; IN_SING;
               FRACTIONAL_IDEAL_PRINCIPAL] THEN
  REWRITE_TAC[UNIT_GROUP] THEN
  MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RING_SPAN_SETMUL_SPAN; SING_SUBSET; RING_SETMUL_SING;
               RING_SPAN_SUBSET]);;

let GROUP_KERNEL_PRINCIPAL_FRACTIONAL_IDEAL = prove
 (`!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> group_kernel (unit_group k,fractional_ideal_group (r,k) h)
                         (\x. ring_span (r,k) h {x}) =
            IMAGE h {u | ring_unit r u}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  ASM_SIMP_TAC[group_kernel; FRACTIONAL_IDEAL_GROUP; FIELD_UNIT_GROUP] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_SING] THEN
  X_GEN_TAC `x:B` THEN
  ASM_CASES_TAC `(x:B) IN ring_carrier k` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    ASM_MESON_TAC[RING_UNIT_IN_CARRIER; RING_HOMOMORPHISM_IN_CARRIER]] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:B`]
    DEDEKIND_VALUATION_UNIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `x:B = ring_0 k` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`;
                 `ring_span (r,k) (h:A->B) {x}`;
                 `IMAGE (h:A->B) (ring_carrier r)`]
    FRACTIONAL_IDEAL_EQ_VALUATION) THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_PRINCIPAL; FRACTIONAL_IDEAL_CARRIER;
               FRACTIONAL_IDEAL_VALUATION_PRINCIPAL;
               FRACTIONAL_IDEAL_VALUATION_CARRIER]);;

(* The representation h(b) h(r) x = h((a)) of a principal fractional ideal.  *)

let FRACTIONAL_IDEAL_PRINCIPAL_SCALED = prove
 (`!r k (h:A->B) x a b.
        field_of_fractions (r,k) h /\ x IN ring_carrier k /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ ring_mul k (h b) x = h a
        ==> IMAGE (ring_mul k (h b)) (ring_span (r,k) h {x}) =
            IMAGE h (ideal_generated r {a})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  SUBGOAL_THEN `(h:A->B) b IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM RING_SPAN_IMAGE_MUL; SING_SUBSET; IMAGE_CLAUSES] THEN
  ASM_SIMP_TAC[GSYM RING_SPAN_IMAGE_IDEAL_GENERATED; SING_SUBSET;
               IMAGE_CLAUSES]);;

(* The class of a fractional ideal: the class of j for any representation   *)
(* h(d) J = h(j).                                                           *)

let FRACTIONAL_IDEAL_CLASS_EXISTS = prove
 (`!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> ?f. group_epimorphism (fractional_ideal_group (r,k) h,class_group r)
                                  f /\
                (!J d j. fractional_ideal (r,k) h J /\
                         d IN ring_carrier r /\ ~(d = ring_0 r) /\
                         ring_ideal r j /\ ~(j = {ring_0 r}) /\
                         IMAGE (ring_mul k (h d)) J = IMAGE h j
                         ==> f J = ideal_class r j) /\
                group_kernel (fractional_ideal_group (r,k) h,class_group r) f =
                {ring_span (r,k) h {x} | x | x IN ring_carrier k /\
                                             ~(x = ring_0 k)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  SUBGOAL_THEN
   `?f. !J d j. fractional_ideal (r,k) h J /\
                d IN ring_carrier r /\ ~(d = ring_0 r) /\
                ring_ideal r j /\ ~(j = {ring_0 r}) /\
                IMAGE (ring_mul k ((h:A->B) d)) J = IMAGE h j
                ==> (f:(B->bool)->(A->bool)->bool) J = ideal_class r j`
  MP_TAC THENL
   [EXISTS_TAC
     `\J. ideal_class r
            (@j. ring_ideal r j /\ ~(j = {ring_0 r}) /\
                 ?d. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                     IMAGE (ring_mul k ((h:A->B) d)) J = IMAGE h j)` THEN
    REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `?j. ring_ideal r j /\ ~(j = {ring_0 r}) /\
          ?d. d IN ring_carrier r /\ ~(d = ring_0 r) /\
              IMAGE (ring_mul k ((h:A->B) d)) J = IMAGE h j`
    MP_TAC THENL
     [EXISTS_TAC `j:A->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `d:A` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SELECT_RULE)] THEN
    ABBREV_TAC
     `j0 = @j. ring_ideal r j /\ ~(j = {ring_0 r}) /\
               ?d. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                   IMAGE (ring_mul k ((h:A->B) d)) J = IMAGE h j` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `d0:A` STRIP_ASSUME_TAC))) THEN
    ASM_SIMP_TAC[IDEAL_CLASS_EQ] THEN REWRITE_TAC[IN_IDEAL_CLASS] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`d:A`; `d0:A`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FRACTIONAL_IDEAL_SCALED_IDEAL_COMPARE THEN
    MAP_EVERY EXISTS_TAC [`k:B ring`; `h:A->B`; `J:B->bool`] THEN
    ASM_MESON_TAC[FRACTIONAL_IDEAL_IMP_SUBSET];
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `f:(B->bool)->(A->bool)->bool` THEN DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GROUP_EPIMORPHISM; GROUP_HOMOMORPHISM; group_image] THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_GROUP] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `!J. fractional_ideal (r,k) (h:A->B) J
        ==> ?d j. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                  ring_ideal r j /\ ~(j = {ring_0 r}) /\
                  IMAGE (ring_mul k (h d)) J = IMAGE h j /\
                  (f:(B->bool)->(A->bool)->bool) J = ideal_class r j`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FRACTIONAL_IDEAL_SCALED_IDEAL) THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `J:B->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `J:B->bool`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`d:A`; `j:A->bool`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[IDEAL_CLASS_IN_CLASS_GROUP];
    MAP_EVERY X_GEN_TAC [`J1:B->bool`; `J2:B->bool`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `J1:B->bool`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `J2:B->bool`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`d2:A`; `j2:A->bool`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`d1:A`; `j1:A->bool`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CLASS_GROUP_MUL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `ring_mul r d1 d2:A` THEN
    ASM_SIMP_TAC[FRACTIONAL_IDEAL_MUL; RING_MUL; INTEGRAL_DOMAIN_MUL_EQ_0;
                 RING_IDEAL_IDEAL_PROD; IDEAL_PROD_EQ_ZERO] THEN
    MATCH_MP_TAC FRACTIONAL_IDEAL_SCALED_IDEAL_MUL THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `J:B->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `J:B->bool`) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`d:A`; `j:A->bool`] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[IDEAL_CLASS_IN_CLASS_GROUP];
      ASM_SIMP_TAC[CLASS_GROUP] THEN
      REWRITE_TAC[ideal_classes; SUBSET; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN
      EXISTS_TAC `IMAGE (h:A->B) j` THEN
      ASM_SIMP_TAC[RING_IDEAL_IMP_FRACTIONAL_IDEAL] THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `ring_1 r:A` THEN
      ASM_SIMP_TAC[RING_IDEAL_IMP_FRACTIONAL_IDEAL; RING_1;
                   INTEGRAL_DOMAIN_NONTRIVIAL] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
      REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x:A. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE (g:A->B) s`) THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC RING_MUL_LID THEN
      ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_IDEAL_IMP_SUBSET;
                    SUBSET]];
    ALL_TAC] THEN
  REWRITE_TAC[group_kernel] THEN ASM_SIMP_TAC[FRACTIONAL_IDEAL_GROUP] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `J:B->bool` THEN
  EQ_TAC THENL
   [STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `J:B->bool`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`d:A`; `j:A->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `principal_ideal r (j:A->bool)` MP_TAC THENL
     [MP_TAC(ISPECL [`r:A ring`; `j:A->bool`] IDEAL_CLASS_EQ_ID) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[principal_ideal; LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC `a:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      rand(concl th) = `j:A->bool`)) THEN
    SUBGOAL_THEN `~(a:A = ring_0 r)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[IDEAL_GENERATED_0];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(h:A->B) a IN ring_carrier k /\ h d IN ring_carrier k /\
      ~(h d = ring_0 k) /\ ~(h a = ring_0 k)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_MONOMORPHISM_EQ_0];
      ALL_TAC] THEN
    EXISTS_TAC `ring_mul k (ring_inv k ((h:A->B) d)) (h a)` THEN
    ASM_SIMP_TAC[RING_MUL; RING_INV; INTEGRAL_DOMAIN_MUL_EQ_0;
                 FIELD_INV_EQ_0] THEN
    MATCH_MP_TAC(SET_RULE
     `!(f:B->B) u. (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\
                   s SUBSET u /\ t SUBSET u /\ IMAGE f s = IMAGE f t
                   ==> s = t`) THEN
    MAP_EVERY EXISTS_TAC
     [`ring_mul k ((h:A->B) d)`; `ring_carrier k:B->bool`] THEN
    REWRITE_TAC[RING_SPAN_SUBSET] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[INTEGRAL_DOMAIN_MUL_LCANCEL];
      ASM_MESON_TAC[FRACTIONAL_IDEAL_IMP_SUBSET];
      ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC FRACTIONAL_IDEAL_PRINCIPAL_SCALED THEN
      ASM_SIMP_TAC[RING_MUL; RING_INV] THEN
      ASM_SIMP_TAC[RING_MUL_ASSOC; RING_INV; FIELD_MUL_RINV; RING_MUL_LID]];
    DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[FRACTIONAL_IDEAL_PRINCIPAL] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:B`]
      FIELD_FRACTION_NONZERO) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ring_span (r,k) (h:A->B) {x}`; `b:A`;
                   `ideal_generated r {a:A}`] (ASSUME
     `!J d j. fractional_ideal (r,k) h J /\
              d IN ring_carrier r /\ ~(d = ring_0 r) /\
              ring_ideal r j /\ ~(j = {ring_0 r}) /\
              IMAGE (ring_mul k ((h:A->B) d)) J = IMAGE h j
              ==> (f:(B->bool)->(A->bool)->bool) J = ideal_class r j`)) THEN
    ASM_SIMP_TAC[FRACTIONAL_IDEAL_PRINCIPAL; RING_IDEAL_IDEAL_GENERATED;
                 IDEAL_GENERATED_EQ_0; FRACTIONAL_IDEAL_PRINCIPAL_SCALED] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[IDEAL_CLASS_EQ_ID; IDEAL_GENERATED_EQ_0] THEN
    ASM_MESON_TAC[PRINCIPAL_IDEAL_IDEAL_GENERATED_SING]]);;

(* The exact sequence 1 -> r^* -> k^* -> fractional ideals -> Cl(r) -> 1.  *)

let FRACTIONAL_IDEAL_CLASS_GROUP_EXACT = prove
 (`!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> ?f. group_monomorphism (unit_group r,unit_group k) h /\
                group_exactness
                 (unit_group r,unit_group k,fractional_ideal_group (r,k) h)
                 (h,(\x. ring_span (r,k) h {x})) /\
                group_exactness
                 (unit_group k,fractional_ideal_group (r,k) h,class_group r)
                 ((\x. ring_span (r,k) h {x}),f) /\
                group_epimorphism (fractional_ideal_group (r,k) h,
                                   class_group r) f /\
                !j. ring_ideal r j /\ ~(j = {ring_0 r})
                    ==> f(IMAGE h j) = ideal_class r j`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`]
    FRACTIONAL_IDEAL_CLASS_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `f:(B->bool)->(A->bool)->bool` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[group_exactness; GROUP_HOMOMORPHISM_PRINCIPAL_FRACTIONAL_IDEAL;
               GROUP_KERNEL_PRINCIPAL_FRACTIONAL_IDEAL] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GROUP_HOMOMORPHISM_UNIT_GROUP) THEN
  ASM_REWRITE_TAC[group_monomorphism] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [group_epimorphism]) THEN
  ASM_REWRITE_TAC[group_image; UNIT_GROUP; FIELD_UNIT_GROUP] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:A`; `y:A`]
      RING_MONOMORPHISM_INJECTIVE_EQ) THEN
    ASM_SIMP_TAC[RING_UNIT_IN_CARRIER];
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[FIELD_UNIT] THEN MESON_TAC[];
    X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `ring_1 r:A` THEN
    ASM_SIMP_TAC[RING_IDEAL_IMP_FRACTIONAL_IDEAL; RING_1;
                 INTEGRAL_DOMAIN_NONTRIVIAL] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:A. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE (g:A->B) s`) THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC RING_MUL_LID THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_IDEAL_IMP_SUBSET;
                  SUBSET]]);;

(* The class group is the group of fractional ideals modulo the principal   *)
(* ones.                                                                     *)

let FRACTIONAL_IDEAL_CLASS_GROUP = prove
 (`!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> class_group r isomorphic_group
            quotient_group (fractional_ideal_group (r,k) h)
              {ring_span (r,k) h {x} | x | x IN ring_carrier k /\
                                           ~(x = ring_0 k)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`]
    FRACTIONAL_IDEAL_CLASS_EXISTS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:(B->bool)->(A->bool)->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  MATCH_MP_TAC FIRST_GROUP_EPIMORPHISM_THEOREM THEN ASM_REWRITE_TAC[]);;

let FRACTIONAL_IDEAL_CLASS_PRIME_SUM = prove
 (`!r k (h:A->B) f t e.
        dedekind_domain r /\ field_of_fractions (r,k) h /\ FINITE t /\
        (!P. P IN t ==> prime_ideal r P /\ ~(P = {ring_0 r})) /\
        group_homomorphism(fractional_ideal_group (r,k) h,class_group r) f /\
        (!j. ring_ideal r j /\ ~(j = {ring_0 r})
             ==> f(IMAGE h j) = ideal_class r j)
        ==> f(group_sum (fractional_ideal_group (r,k) h) t
               (\P. group_zpow (fractional_ideal_group (r,k) h)
                      (IMAGE h P) (e P))) =
            group_sum (class_group r) t
              (\P. group_zpow (class_group r) (ideal_class r P) (e P))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`fractional_ideal_group (r,k) (h:A->B)`; `class_group (r:A ring)`;
    `f:(B->bool)->(A->bool)->bool`; `t:(A->bool)->bool`;
    `\P:A->bool. group_zpow (fractional_ideal_group (r,k) (h:A->B))
                            (IMAGE h P) (e P)`]
   GROUP_SUM_HOMOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[ABELIAN_FRACTIONAL_IDEAL_GROUP; ABELIAN_CLASS_GROUP;
               DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN
  SUBGOAL_THEN
   `!P. P IN t
        ==> IMAGE (h:A->B) P IN group_carrier(fractional_ideal_group (r,k) h)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FRACTIONAL_IDEAL_GROUP; IN_ELIM_THM] THEN
    MATCH_MP_TAC RING_IDEAL_IMP_FRACTIONAL_IDEAL THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[GROUP_ZPOW] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `t:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC GROUP_SUM_EQ THEN X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM] THEN
  FIRST_ASSUM(fun th -> W(MP_TAC o PART_MATCH (lhand o rand)
   (MATCH_MP GROUP_HOMOMORPHISM_ZPOW th) o lhand o snd)) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL]);;

(* A product of powers of classes of primes is trivial iff some element      *)
(* of k has these exponents as valuations (and 0 elsewhere).                 *)
let CLASS_GROUP_SUM_PRIME_CLASSES_EQ_ID = prove
 (`!r k (h:A->B) t e.
        dedekind_domain r /\ field_of_fractions (r,k) h /\ FINITE t /\
        (!P. P IN t ==> prime_ideal r P /\ ~(P = {ring_0 r}))
        ==> (group_sum (class_group r) t
               (\P. group_zpow (class_group r) (ideal_class r P) (e P)) =
             group_id (class_group r) <=>
             ?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\
                 !P. prime_ideal r P /\ ~(P = {ring_0 r})
                     ==> dedekind_valuation (r,k) h P x =
                         if P IN t then e P else &0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`]
    FRACTIONAL_IDEAL_CLASS_GROUP_EXACT) THEN
  ASM_REWRITE_TAC[group_exactness; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:(B->bool)->(A->bool)->bool` THEN STRIP_TAC THEN
  ABBREV_TAC
   `D = group_sum (fractional_ideal_group (r,k) (h:A->B)) t
          (\P. group_zpow (fractional_ideal_group (r,k) h)
                 (IMAGE h P) (e P))` THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`;
                 `f:(B->bool)->(A->bool)->bool`; `t:(A->bool)->bool`;
                 `e:(A->bool)->int`] FRACTIONAL_IDEAL_CLASS_PRIME_SUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `group_epimorphism (fractional_ideal_group (r,k) (h:A->B),
                                    class_group r) f` THEN
    SIMP_TAC[group_epimorphism];
    ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `(D:B->bool) IN group_carrier(fractional_ideal_group (r,k) (h:A->B))`
  ASSUME_TAC THENL [EXPAND_TAC "D" THEN REWRITE_TAC[GROUP_SUM]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `(D:B->bool) IN group_kernel (fractional_ideal_group (r,k) (h:A->B),
                                 class_group r) f` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[group_kernel; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check
   (fun th -> is_eq(concl th) &&
              let l = fst(strip_comb(lhand(concl th))) in
              is_const l && fst(dest_const l) = "group_image")) THEN
  ASM_SIMP_TAC[group_image; FIELD_UNIT_GROUP; IN_IMAGE; IN_DIFF; IN_SING] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `(x:B) IN ring_carrier k` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `x:B = ring_0 k` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `D:B->bool`;
                 `ring_span (r,k) (h:A->B) {x}`]
    FRACTIONAL_IDEAL_EQ_VALUATION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FRACTIONAL_IDEAL_PRINCIPAL] THEN
    UNDISCH_TAC
     `(D:B->bool) IN group_carrier(fractional_ideal_group (r,k) (h:A->B))` THEN
    ASM_SIMP_TAC[FRACTIONAL_IDEAL_GROUP; IN_ELIM_THM];
    DISCH_THEN SUBST1_TAC] THEN
  EXPAND_TAC "D" THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_VALUATION_PRIME_PRODUCT;
               FRACTIONAL_IDEAL_VALUATION_PRINCIPAL] THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC EQ_SYM_EQ);;

(* If x and j have the same valuations outside a finite set t of primes,     *)
(* the class of j is a product of powers of the classes of the primes in t.  *)
let IDEAL_CLASS_EQ_SUM_PRIME_CLASSES = prove
 (`!r k (h:A->B) t j x.
        dedekind_domain r /\ field_of_fractions (r,k) h /\ FINITE t /\
        (!P. P IN t ==> prime_ideal r P /\ ~(P = {ring_0 r})) /\
        ring_ideal r j /\ ~(j = {ring_0 r}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\
        (!P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN t)
             ==> dedekind_valuation (r,k) h P x = &(ideal_valuation r P j))
        ==> ideal_class r j =
            group_sum (class_group r) t
              (\P. group_zpow (class_group r) (ideal_class r P)
                     (&(ideal_valuation r P j) -
                      dedekind_valuation (r,k) h P x))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`]
    FRACTIONAL_IDEAL_CLASS_GROUP_EXACT) THEN
  ASM_REWRITE_TAC[group_exactness; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:(B->bool)->(A->bool)->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `group_homomorphism (fractional_ideal_group (r,k) (h:A->B),
                        class_group r) f`
  ASSUME_TAC THENL
   [UNDISCH_TAC `group_epimorphism (fractional_ideal_group (r,k) (h:A->B),
                                    class_group r) f` THEN
    SIMP_TAC[group_epimorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`;
                 `f:(B->bool)->(A->bool)->bool`; `t:(A->bool)->bool`;
                 `\P. &(ideal_valuation r P (j:A->bool)) -
                      dedekind_valuation (r,k) (h:A->B) P x`]
    FRACTIONAL_IDEAL_CLASS_PRIME_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC `G = fractional_ideal_group (r,k) (h:A->B)` THEN
  SUBGOAL_THEN
   `IMAGE (h:A->B) j IN group_carrier G /\
    ring_span (r,k) h {x} IN group_carrier G`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    ASM_SIMP_TAC[FRACTIONAL_IDEAL_GROUP; IN_ELIM_THM;
                 FRACTIONAL_IDEAL_PRINCIPAL; RING_IDEAL_IMP_FRACTIONAL_IDEAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `f(ring_span (r,k) (h:A->B) {x}) = group_id (class_group r)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `ring_span (r,k) (h:A->B) {x} IN
      group_kernel (G,class_group r) f`
    MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check
       (fun th -> is_eq(concl th) &&
                  let l = fst(strip_comb(lhand(concl th))) in
                  is_const l && fst(dest_const l) = "group_image")) THEN
      ASM_SIMP_TAC[group_image; FIELD_UNIT_GROUP; IN_IMAGE; IN_DIFF;
                   IN_SING] THEN
      EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[group_kernel; IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `group_sum G t
     (\P. group_zpow G (IMAGE (h:A->B) P)
            (&(ideal_valuation r P j) - dedekind_valuation (r,k) h P x)) =
    group_div G (IMAGE h j) (ring_span (r,k) h {x})`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`;
                   `group_sum G t
                     (\P. group_zpow G (IMAGE (h:A->B) P)
                            (&(ideal_valuation r P j) -
                             dedekind_valuation (r,k) h P x))`;
                   `group_div G (IMAGE (h:A->B) j) (ring_span (r,k) h {x})`]
      FRACTIONAL_IDEAL_EQ_VALUATION) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `group_sum G t
         (\P. group_zpow G (IMAGE (h:A->B) P)
                (&(ideal_valuation r P j) -
                 dedekind_valuation (r,k) h P x)) IN group_carrier G /\
        group_div G (IMAGE (h:A->B) j) (ring_span (r,k) h {x}) IN
        group_carrier G`
      MP_TAC THENL
       [ASM_SIMP_TAC[GROUP_SUM; GROUP_DIV];
        EXPAND_TAC "G" THEN ASM_SIMP_TAC[FRACTIONAL_IDEAL_GROUP] THEN
        REWRITE_TAC[IN_ELIM_THM]];
      DISCH_THEN SUBST1_TAC] THEN
    X_GEN_TAC `Q:A->bool` THEN STRIP_TAC THEN
    EXPAND_TAC "G" THEN
    ASM_SIMP_TAC[FRACTIONAL_IDEAL_VALUATION_PRIME_PRODUCT] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `Q:A->bool`]
      GROUP_HOMOMORPHISM_FRACTIONAL_IDEAL_VALUATION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_DIV) THEN
    DISCH_THEN(MP_TAC o SPECL [`IMAGE (h:A->B) j`;
                               `ring_span (r,k) (h:A->B) {x}`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[group_div; INTEGER_GROUP; FRACTIONAL_IDEAL_VALUATION_IMAGE;
                 FRACTIONAL_IDEAL_VALUATION_PRINCIPAL] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(B->bool)group`; `class_group (r:A ring)`;
                 `f:(B->bool)->(A->bool)->bool`] GROUP_HOMOMORPHISM_DIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
  REWRITE_TAC[group_div; GROUP_INV_ID] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC GROUP_MUL_RID THEN
  ASM_SIMP_TAC[IDEAL_CLASS_IN_CLASS_GROUP]);;
