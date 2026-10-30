(* ========================================================================= *)
(* The additive group and the unit group of a ring.                          *)
(*                                                                           *)
(*   ring_additive_group r = the group of r under ring_add r, with identity  *)
(*                           ring_0 r and inverse ring_neg r                 *)
(*   unit_group r          = the group of the units of r under ring_mul r,   *)
(*                           with identity ring_1 r and inverse ring_inv r   *)
(*                                                                           *)
(* Main results: the characterizations RING_ADDITIVE_GROUP and UNIT_GROUP    *)
(* (in the style of INTEGER_GROUP); both groups are abelian, finite sums in  *)
(* the additive group are ring sums (GROUP_SUM_RING_ADDITIVE_GROUP), and     *)
(* powers and finite products in the unit group are the ring ones            *)
(* (UNIT_GROUP_POW, UNIT_GROUP_SUM); ideals and subrings are subgroups of    *)
(* the additive group (RING_IDEAL_IMP_SUBGROUP,                              *)
(* SUBRING_IMP_SUBGROUP_ADDITIVE); the units of a field are its nonzero      *)
(* elements (FIELD_UNIT_GROUP); ring homomorphisms induce group              *)
(* homomorphisms of both groups (GROUP_HOMOMORPHISM_RING_ADDITIVE_GROUP,     *)
(* GROUP_HOMOMORPHISM_UNIT_GROUP); the units of a subring form a subgroup of *)
(* the units, isomorphic to the unit group of the subring by the identity    *)
(* (UNIT_GROUP_SUBRING_GENERATED); and distinct homomorphisms from a group   *)
(* into the units of an integral domain are linearly independent             *)
(* (GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT, Dedekind's independence of        *)
(* characters).                                                              *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/grouptheory.ml";;

(* ------------------------------------------------------------------------- *)
(* The additive group of a ring. Finite sums in it are ring sums             *)
(* (GROUP_SUM_RING_ADDITIVE_GROUP).                                          *)
(* ------------------------------------------------------------------------- *)

let ring_additive_group = new_definition
 `ring_additive_group (r:A ring) =
        group(ring_carrier r,ring_0 r,ring_neg r,ring_add r)`;;

let RING_ADDITIVE_GROUP = prove
 (`(!r:A ring. group_carrier(ring_additive_group r) = ring_carrier r) /\
   (!r:A ring. group_id(ring_additive_group r) = ring_0 r) /\
   (!r:A ring. group_inv(ring_additive_group r) = ring_neg r) /\
   (!r:A ring. group_mul(ring_additive_group r) = ring_add r)`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl ring_additive_group)))))
   (CONJUNCT2 group_tybij)))) THEN
  REWRITE_TAC[GSYM ring_additive_group] THEN ANTS_TAC THENL
   [SIMP_TAC[RING_0; RING_NEG; RING_ADD; RING_ADD_ASSOC; RING_ADD_LZERO;
             RING_ADD_RZERO; RING_ADD_LNEG; RING_ADD_RNEG];
    SIMP_TAC[group_carrier; group_id; group_inv; group_mul]]);;

let ABELIAN_RING_ADDITIVE_GROUP = prove
 (`!r:A ring. abelian_group(ring_additive_group r)`,
  REWRITE_TAC[abelian_group; RING_ADDITIVE_GROUP] THEN
  MESON_TAC[RING_ADD_SYM]);;

let GROUP_HOMOMORPHISM_RING_ADDITIVE_GROUP = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f
        ==> group_homomorphism(ring_additive_group r,ring_additive_group r') f`,
  SIMP_TAC[ring_homomorphism; GROUP_HOMOMORPHISM; RING_ADDITIVE_GROUP]);;

let GROUP_SUM_RING_ADDITIVE_GROUP = prove
 (`!r s (f:K->A).
        FINITE s ==> group_sum (ring_additive_group r) s f = ring_sum r s f`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[CONJUNCT1(SPEC_ALL GROUP_SUM_CLAUSES_EXISTS);
              RING_SUM_CLAUSES; RING_ADDITIVE_GROUP] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ABELIAN_GROUP_SUM_CLAUSES; ABELIAN_RING_ADDITIVE_GROUP;
               FINITE_RESTRICT; RING_SUM_CLAUSES; RING_ADDITIVE_GROUP]);;

let RING_IDEAL_IMP_SUBGROUP = prove
 (`!r j:A->bool. ring_ideal r j ==> j subgroup_of ring_additive_group r`,
  SIMP_TAC[ring_ideal; subgroup_of; RING_ADDITIVE_GROUP]);;

let SUBRING_IMP_SUBGROUP_ADDITIVE = prove
 (`!r s:A->bool. s subring_of r ==> s subgroup_of ring_additive_group r`,
  SIMP_TAC[subring_of; subgroup_of; RING_ADDITIVE_GROUP]);;

let RING_ADDITIVE_GROUP_PRODUCT_RING = prove
 (`!k (r:K->A ring).
        ring_additive_group(product_ring k r) =
        product_group k (\i. ring_additive_group(r i))`,
  REWRITE_TAC[GROUPS_EQ; RING_ADDITIVE_GROUP; PRODUCT_GROUP; PRODUCT_RING]);;

let RING_ADDITIVE_GROUP_RESTRICTED_PRODUCT_RING = prove
 (`!k (r:K->A ring) s.
        (!i. i IN k ==> s i subring_of r i)
        ==> ring_additive_group(restricted_product_ring k r s) =
            restricted_product_group k (\i. ring_additive_group(r i)) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GROUPS_EQ] THEN
  ASM_SIMP_TAC[RING_ADDITIVE_GROUP; RESTRICTED_PRODUCT_GROUP;
               RESTRICTED_PRODUCT_RING; SUBRING_IMP_SUBGROUP_ADDITIVE]);;

(* ------------------------------------------------------------------------- *)
(* The unit group and its basic properties.                                  *)
(* ------------------------------------------------------------------------- *)

let unit_group = new_definition
 `unit_group (r:A ring) =
  group({x | ring_unit r x},ring_1 r,ring_inv r,ring_mul r)`;;

let UNIT_GROUP = prove
 (`(!r:A ring. group_carrier(unit_group r) = {x | ring_unit r x}) /\
   (!r:A ring. group_id(unit_group r) = ring_1 r) /\
   (!r:A ring. group_inv(unit_group r) = ring_inv r) /\
   (!r:A ring. group_mul(unit_group r) = ring_mul r)`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl unit_group)))))
   (CONJUNCT2 group_tybij)))) THEN
  REWRITE_TAC[GSYM unit_group] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[RING_UNIT_1; RING_UNIT_INV; RING_UNIT_MUL] THEN
    SIMP_TAC[RING_MUL_LINV; RING_MUL_RINV] THEN
    MESON_TAC[RING_MUL_ASSOC; RING_MUL_LID; RING_MUL_RID;
              RING_UNIT_IN_CARRIER];
    SIMP_TAC[group_carrier; group_id; group_inv; group_mul]]);;

let ABELIAN_UNIT_GROUP = prove
 (`!r:A ring. abelian_group(unit_group r)`,
  REWRITE_TAC[abelian_group; UNIT_GROUP; IN_ELIM_THM] THEN
  MESON_TAC[RING_MUL_SYM; RING_UNIT_IN_CARRIER]);;

let UNIT_GROUP_POW = prove
 (`!r:A ring x n. group_pow (unit_group r) x n = ring_pow r x n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[group_pow; ring_pow; UNIT_GROUP]);;

let UNIT_GROUP_SUM = prove
 (`!r:A ring s (f:K->A).
        FINITE s /\ (!i. i IN s ==> ring_unit r (f i))
        ==> group_sum (unit_group r) s f = ring_product r s f`,
  GEN_TAC THEN GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CONJUNCT1(SPEC_ALL GROUP_SUM_CLAUSES_EXISTS); FINITE_RESTRICT;
           ABELIAN_GROUP_SUM_CLAUSES; ABELIAN_UNIT_GROUP; FORALL_IN_INSERT;
           RING_PRODUCT_CLAUSES; UNIT_GROUP; IN_ELIM_THM;
           RING_UNIT_IN_CARRIER]);;

let FIELD_UNIT_GROUP = prove
 (`!k:A ring.
        field k
        ==> group_carrier(unit_group k) = ring_carrier k DIFF {ring_0 k}`,
  SIMP_TAC[UNIT_GROUP; FIELD_UNIT; EXTENSION; IN_ELIM_THM; IN_DIFF;
           IN_SING]);;

let SUBGROUP_POSITIVE_REALS = prove
 (`{x:real | &0 < x} subgroup_of unit_group real_ring`,
  REWRITE_TAC[subgroup_of; UNIT_GROUP; REAL_RING_INV; SUBSET; IN_ELIM_THM] THEN
  SIMP_TAC[FIELD_UNIT; FIELD_REAL_RING; REAL_RING_CLAUSES; IN_UNIV] THEN
  SIMP_TAC[REAL_LT_IMP_NZ; REAL_LT_01; REAL_LT_INV; REAL_LT_MUL]);;

(* ------------------------------------------------------------------------- *)
(* Homomorphisms and subrings.                                               *)
(* ------------------------------------------------------------------------- *)

let GROUP_HOMOMORPHISM_UNIT_GROUP = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f
        ==> group_homomorphism(unit_group r,unit_group r') f`,
  REWRITE_TAC[GROUP_HOMOMORPHISM; UNIT_GROUP; SUBSET; FORALL_IN_IMAGE;
              IN_ELIM_THM] THEN
  MESON_TAC[RING_UNIT_HOMOMORPHIC_IMAGE; RING_HOMOMORPHISM_MUL;
            RING_UNIT_IN_CARRIER]);;

(* The two groups are not equal in general: the inverse functions differ     *)
(* outside the units of the subring.                                         *)

let UNIT_GROUP_SUBRING_GENERATED = prove
 (`!r:A ring s.
        {x | ring_unit (subring_generated r s) x} subgroup_of unit_group r /\
        group_isomorphism
         (unit_group(subring_generated r s),
          subgroup_generated (unit_group r)
                             {x | ring_unit (subring_generated r s) x}) I`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `s:A->bool`] RING_HOMOMORPHISM_INCLUSION) THEN
  DISCH_THEN(MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_UNIT_GROUP) THEN
  DISCH_THEN(fun th ->
    ASSUME_TAC th THEN MP_TAC(MATCH_MP SUBGROUP_GROUP_IMAGE th)) THEN
  REWRITE_TAC[group_image; IMAGE_ID; UNIT_GROUP] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[GROUP_ISOMORPHISM; GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ;
               CARRIER_SUBGROUP_GENERATED_SUBGROUP; I_DEF; IMAGE_ID;
               UNIT_GROUP; SUBSET_REFL]);;

(* The units of the image of a monomorphism are the images of the units      *)
(* (RING_MONOMORPHISM_UNITS_IMAGE), and the units of a binary product are    *)
(* the pairs of units (RING_UNIT_PROD_RING, UNIT_GROUP_PROD_RING).           *)
let RING_MONOMORPHISM_UNITS_IMAGE = prove
 (`!r r' (f:A->B).
        ring_monomorphism(r,r') f
        ==> {y | ring_unit (subring_generated r' (IMAGE f (ring_carrier r)))
                           y} =
            IMAGE f {u | ring_unit r u}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `IMAGE (f:A->B) (ring_carrier r) subring_of r'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `r':B ring`; `f:A->B`] SUBRING_RING_IMAGE) THEN
    ASM_REWRITE_TAC[ring_image];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_UNIT_SUBRING_GENERATED] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `y:B` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC)
     (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[ring_unit] THEN
    EXISTS_TAC `b:A` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ring_monomorphism(r,r') (f:A->B)` THEN
    REWRITE_TAC[ring_monomorphism] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[RING_MUL; RING_1] THEN
    FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th;
                                       MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
    UNDISCH_TAC `ring_inv r' y = (f:A->B) b` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `y = (f:A->B) a` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[RING_MUL_RINV];
    DISCH_THEN(X_CHOOSE_THEN `a:A` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `(a:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[ring_unit]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[RING_UNIT_HOMOMORPHIC_IMAGE];
      EXISTS_TAC `ring_inv r a:A` THEN ASM_SIMP_TAC[RING_INV] THEN
      CONV_TAC SYM_CONV THEN
      FIRST_ASSUM(fun th ->
        ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_INV th])]]);;

let RING_UNIT_PROD_RING = prove
 (`!(r:A ring) (r':B ring) x y.
        ring_unit (prod_ring r r') (x,y) <=> ring_unit r x /\ ring_unit r' y`,
  REWRITE_TAC[ring_unit; PROD_RING; EXISTS_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
  MESON_TAC[]);;

let UNIT_GROUP_PROD_RING = prove
 (`!(r:A ring) (r':B ring).
        group_isomorphism
         (unit_group(prod_ring r r'),prod_group (unit_group r) (unit_group r'))
         I`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GROUP_ISOMORPHISM; GROUP_HOMOMORPHISM; IMAGE_I; I_THM] THEN
  REWRITE_TAC[UNIT_GROUP; PROD_GROUP; PROD_RING] THEN
  REWRITE_TAC[EXTENSION; SUBSET; FORALL_PAIR_THM; IN_ELIM_THM; IN_CROSS;
              RING_UNIT_PROD_RING] THEN
  MESON_TAC[]);;

let UNIT_GROUP_PRODUCT_RING = prove
 (`!k (r:K->A ring).
        group_isomorphism
         (unit_group(product_ring k r),product_group k (\i. unit_group(r i)))
         I`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GROUP_ISOMORPHISM; GROUP_HOMOMORPHISM; IMAGE_I; I_THM] THEN
  REWRITE_TAC[UNIT_GROUP; PRODUCT_GROUP; PRODUCT_RING] THEN
  REWRITE_TAC[RING_UNIT_PRODUCT_RING;
              SET_RULE `{x | x IN s} = s:(K->A)->bool`] THEN
  REWRITE_TAC[SUBSET_REFL] THEN MESON_TAC[]);;

let UNIT_GROUP_RESTRICTED_PRODUCT_RING = prove
 (`!k (r:K->A ring) s.
        (!i. i IN k ==> s i subring_of r i)
        ==> group_isomorphism
             (unit_group(restricted_product_ring k r s),
              restricted_product_group k (\i. unit_group(r i))
               (\i. {x | ring_unit (subring_generated (r i) (s i)) x})) I`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `group_carrier(restricted_product_group k (\i. unit_group((r:K->A ring) i))
      (\i. {x | ring_unit (subring_generated (r i) (s i)) x})) =
    group_carrier(unit_group(restricted_product_ring k r s))`
  ASSUME_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) (CONJUNCT1 RESTRICTED_PRODUCT_GROUP) o
      lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[UNIT_GROUP_SUBRING_GENERATED]; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[UNIT_GROUP; RING_UNIT_RESTRICTED_PRODUCT_RING] THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GROUP_ISOMORPHISM; GROUP_HOMOMORPHISM; IMAGE_I; I_THM] THEN
  REWRITE_TAC[SUBSET_REFL; UNIT_GROUP; RESTRICTED_PRODUCT_GROUP;
              RESTRICTED_PRODUCT_RING] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Dedekind's independence of characters: distinct homomorphisms from a      *)
(* group into the units of an integral domain l are linearly independent     *)
(* over l. If a combination of them with coefficients in l vanishes on the   *)
(* group, every coefficient is 0, for an indexed family                      *)
(* (GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT) and for a finite set of           *)
(* homomorphisms (GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_SET). The induction  *)
(* step multiplies a vanishing combination by the values at a point y and    *)
(* subtracts (GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_LEMMA).                  *)
(* ------------------------------------------------------------------------- *)

let GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_LEMMA = prove
 (`!(f:K->A->B) G l s d a y.
        FINITE s /\
        (!i. i IN s ==> group_homomorphism(G,unit_group l) (f i)) /\
        (!i. i IN s ==> d i IN ring_carrier l) /\
        a IN s /\ y IN group_carrier G /\
        (!x. x IN group_carrier G
             ==> ring_sum l s (\i. ring_mul l (d i) (f i x)) = ring_0 l)
        ==> !x. x IN group_carrier G
                ==> ring_sum l s
                     (\i. ring_mul l
                           (ring_mul l (d i) (ring_sub l (f i y) (f a y)))
                           (f i x)) = ring_0 l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i x. i IN s /\ x IN group_carrier G
          ==> (f:K->A->B) i x IN ring_carrier l /\
              ring_mul l (d i) (f i x) IN ring_carrier l`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:K`; `z:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f:K->A->B) i z IN ring_carrier l`
      (fun th -> ASM_SIMP_TAC[th; RING_MUL]) THEN
    SUBGOAL_THEN `group_homomorphism(G,unit_group l) ((f:K->A->B) i)`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `z:A` o CONJUNCT1) THEN
    ASM_SIMP_TAC[UNIT_GROUP; IN_ELIM_THM; RING_UNIT_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN `group_mul G (y:A) x IN group_carrier G` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GROUP_MUL]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum l s
      (\i. ring_sub l (ring_mul l (d i) ((f:K->A->B) i (group_mul G y x)))
                      (ring_mul l (f a y) (ring_mul l (d i) (f i x))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(f:K->A->B) i (group_mul G y x) = ring_mul l (f i y) (f i x)`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `group_homomorphism(G,unit_group l) ((f:K->A->B) i)`
      MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> ASM_SIMP_TAC[MATCH_MP GROUP_HOMOMORPHISM_MUL th])
        THEN
      REWRITE_TAC[UNIT_GROUP];
      ALL_TAC] THEN
    MATCH_MP_TAC(RING_RULE
     `!r c u v w:B.
        c IN ring_carrier r /\ u IN ring_carrier r /\
        v IN ring_carrier r /\ w IN ring_carrier r
        ==> ring_mul r (ring_mul r c (ring_sub r u v)) w =
            ring_sub r (ring_mul r c (ring_mul r u w))
                       (ring_mul r v (ring_mul r c w))`) THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[RING_SUM_SUB; RING_SUM_LMUL; RING_MUL; RING_MUL_RZERO;
                 RING_SUB_REFL; RING_0]]);;

let GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT = prove
 (`!(f:K->A->B) G l s c.
        integral_domain l /\ FINITE s /\
        (!i. i IN s ==> group_homomorphism(G,unit_group l) (f i)) /\
        (!i j. i IN s /\ j IN s /\ ~(i = j)
               ==> ?x. x IN group_carrier G /\ ~(f i x = f j x)) /\
        (!i. i IN s ==> c i IN ring_carrier l) /\
        (!x. x IN group_carrier G
             ==> ring_sum l s (\i. ring_mul l (c i) (f i x)) = ring_0 l)
        ==> !i. i IN s ==> c i = ring_0 l`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!t. FINITE t
        ==> t SUBSET (s:K->bool)
            ==> !d. (!i. i IN t ==> d i IN ring_carrier l) /\
                    (!x. x IN group_carrier G
                         ==> ring_sum l t
                               (\i. ring_mul l (d i) ((f:K->A->B) i x)) =
                             ring_0 l)
                    ==> !i. i IN t ==> d i = ring_0 l`
   (fun th -> MP_TAC(SPEC `s:K->bool` th) THEN
              ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
              ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; INSERT_SUBSET] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `t:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fun ih -> STRIP_TAC THEN X_GEN_TAC `d:K->B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sum")) THEN
    MP_TAC(MP ih (ASSUME `(t:K->bool) SUBSET s`))) THEN
  SUBGOAL_THEN
   `!i. i IN a INSERT t
        ==> group_homomorphism(G,unit_group l) ((f:K->A->B) i)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i x. i IN a INSERT t /\ x IN group_carrier G
          ==> (f:K->A->B) i x IN ring_carrier l`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:K`; `z:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `group_homomorphism(G,unit_group l) ((f:K->A->B) i)`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `z:A` o CONJUNCT1) THEN
    ASM_SIMP_TAC[UNIT_GROUP; IN_ELIM_THM; RING_UNIT_IN_CARRIER];
    ALL_TAC] THEN
  DISCH_THEN(fun ih ->
    SUBGOAL_THEN `!i. i IN t ==> (d:K->B) i = ring_0 l` ASSUME_TAC THENL
     [X_GEN_TAC `i:K` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:K`; `a:K`]) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPEC
       `\j. ring_mul l (d j) (ring_sub l ((f:K->A->B) j y) (f a y))` ih) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[RING_MUL; RING_SUB; IN_INSERT] THEN
        X_GEN_TAC `x:A` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`f:K->A->B`; `G:A group`; `l:B ring`;
                       `(a:K) INSERT t`; `d:K->B`; `a:K`; `y:A`]
            GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_LEMMA) THEN
        ASM_SIMP_TAC[FINITE_INSERT; IN_INSERT] THEN
        DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
        ASM_SIMP_TAC[RING_SUM_CLAUSES; RING_MUL; RING_SUB; RING_0; IN_INSERT;
                     RING_SUB_REFL; RING_MUL_LZERO; RING_MUL_RZERO;
                     RING_ADD_LZERO; RING_SUM];
        DISCH_THEN(MP_TAC o SPEC `i:K`) THEN
        ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; RING_SUB; RING_SUB_EQ_0;
                     IN_INSERT]];
      ALL_TAC]) THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT] THEN
  SUBGOAL_THEN
   `ring_sum l t
      (\i. ring_mul l (d i) ((f:K->A->B) i (group_id G))) =
    ring_0 l`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ_0 THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; GROUP_ID; IN_INSERT];
    ALL_TAC] THEN
  REMOVE_THEN "sum" (MP_TAC o SPEC `group_id G:A`) THEN
  SUBGOAL_THEN `group_homomorphism(G,unit_group l) ((f:K->A->B) a)`
  MP_TAC THENL [ASM_SIMP_TAC[IN_INSERT]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASM_SIMP_TAC[RING_SUM_CLAUSES; RING_MUL; GROUP_ID;
    IN_INSERT; RING_MUL_LZERO; RING_SUM_0; RING_ADD_RZERO; RING_MUL_RID;
    REWRITE_RULE[UNIT_GROUP] (MATCH_MP GROUP_HOMOMORPHISM_OF_ID th)]));;

let GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_SET = prove
 (`!G l:B ring s c.
        integral_domain l /\ FINITE s /\
        (!f. f IN s ==> group_homomorphism(G,unit_group l) f) /\
        (!f g. f IN s /\ g IN s /\ ~(f = g)
               ==> ?x:A. x IN group_carrier G /\ ~(f x = g x)) /\
        (!f. f IN s ==> c f IN ring_carrier l) /\
        (!x. x IN group_carrier G
             ==> ring_sum l s (\f. ring_mul l (c f) (f x)) = ring_0 l)
        ==> !f. f IN s ==> c f = ring_0 l`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\f:A->B. f`; `G:A group`; `l:B ring`; `s:(A->B)->bool`;
                 `c:(A->B)->B`] GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT) THEN
  REWRITE_TAC[]);;
