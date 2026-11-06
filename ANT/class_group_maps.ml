(* ========================================================================= *)
(* Maps of ideal class groups for an extension of number fields: the         *)
(* extension map Cl(O_k) -> Cl(O_l) and the norm map Cl(O_l) -> Cl(O_k),     *)
(* whose composite is the [l:k]-th power map.                                *)
(*                                                                           *)
(* The maps are induced by maps of ideals                                    *)
(* (CLASS_GROUP_HOMOMORPHISM_IDEAL_MAP of ANT/classgroup_group.ml; for the   *)
(* extension of ideals along a monomorphism of Dedekind domains,             *)
(* DEDEKIND_CLASS_GROUP_EXTENSION).                                          *)
(*                                                                           *)
(* For a field k with a ring homomorphism h into a number field l (as in     *)
(* ANT/relative_split.ml), O_k and O_l the rings of integers, n = [l:k] =    *)
(* extension_degree(k,l) h and N the relative ideal norm                     *)
(* number_field_ideal_norm (k,l) h of ANT/ideal_norm_extension.ml:           *)
(*                                                                           *)
(*   [j] |-> [j O_l] is a homomorphism Cl(O_k) -> Cl(O_l)                    *)
(*                          (NUMBER_FIELD_CLASS_GROUP_EXTENSION)             *)
(*   [J] |-> [N(J)] is a homomorphism Cl(O_l) -> Cl(O_k)                     *)
(*                          (NUMBER_FIELD_CLASS_GROUP_NORM)                  *)
(*   the norm of the extension of a class c is c^n                           *)
(*                          (NUMBER_FIELD_CLASS_GROUP_NORM_EXTENSION)        *)
(*   for l Galois over k the extension of the norm of [J] is the class of    *)
(*   the product of the conjugates g(J), g in Gal(l/k)                       *)
(*                        (NUMBER_FIELD_CLASS_GROUP_EXTENSION_NORM_GALOIS)   *)
(*                                                                           *)
(* On the level of ideals: if j O_l is principal then so is j^n              *)
(* (NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_POW), and for n coprime to the    *)
(* class number h_k of O_k, j O_l is principal iff j is                      *)
(* (NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_COPRIME). So for n coprime to h_k *)
(* the extension map is injective                                            *)
(* (NUMBER_FIELD_CLASS_GROUP_EXTENSION_MONOMORPHISM), the norm map is        *)
(* surjective (NUMBER_FIELD_CLASS_GROUP_NORM_EPIMORPHISM) and h_k divides    *)
(* the class number h_l of O_l (NUMBER_FIELD_CLASS_NUMBER_DIVIDES). The      *)
(* contraction of j O_l is j for every ideal j of O_k                        *)
(* (RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION of                          *)
(* ANT/ideal_norm_extension.ml).                                             *)
(*                                                                           *)
(* Routes. Norm: N(J1 J2) = N(J1) N(J2), N(x O_l) = N(x) O_k and N(J) = 0    *)
(* iff J = 0 (NUMBER_FIELD_IDEAL_NORM_MUL, _PRINCIPAL, _EQ_0). The           *)
(* composite: N(j O_l) = j^n (NUMBER_FIELD_IDEAL_NORM_EXTENSION) and         *)
(* CLASS_GROUP_POW; the Galois case is                                       *)
(* NUMBER_FIELD_GALOIS_PRODUCT_IDEAL_NORM. Coprime degree: j^n principal     *)
(* implies j principal (DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME of              *)
(* ANT/classgroup_group.ml); every class c is c^(n m), the norm of the       *)
(* extension of c^m, for n m == 1 (mod h_k) (CONG_SOLVE); h_k divides h_l by *)
(* CARD_DIVIDES_GROUP_EPIMORPHIC_IMAGE.                                      *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/grouptheory.ml,                      *)
(* Library/pocklington.ml (CONG_SOLVE), Library/ring_det.ml (algebra_norm),  *)
(* Library/galois.ml (galois_group, galois_extension), ANT/ideal_arith.ml,   *)
(* ANT/dedekind_struct.ml (ideal_class), ANT/numfield.ml,                    *)
(* ANT/ring_of_integers.ml, ANT/classgroup.ml, ANT/classgroup_group.ml,      *)
(* ANT/relative_split.ml (RING_OF_INTEGERS_IDEAL_EXTENSION),                 *)
(* ANT/integrality.ml (NUMBER_FIELD_NORM_INTEGRAL) and                       *)
(* ANT/ideal_norm_extension.ml.                                              *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/grouptheory.ml";;
needs "Library/pocklington.ml";;
needs "Library/ring_det.ml";;
needs "Library/galois.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/dedekind_struct.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/classgroup.ml";;
needs "ANT/classgroup_group.ml";;
needs "ANT/relative_split.ml";;
needs "ANT/integrality.ml";;
needs "ANT/ideal_norm_extension.ml";;

(* The map [j] |-> [g(j)] is well defined: (a) j1 = (b) j2 gives             *)
(* (c) g(j1) = (d) g(j2) with g((a)) = (c), g((b)) = (d).                    *)

(* The extension of ideals along a monomorphism of Dedekind domains.         *)

(* ------------------------------------------------------------------------- *)
(* Number fields: the extension map and the norm map.                        *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_CLASS_GROUP_EXTENSION = prove
 (`!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> ?f. group_homomorphism(class_group(ring_of_integers k),
                                   class_group(ring_of_integers l)) f /\
                !j. ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
                    ==> f(ideal_class (ring_of_integers k) j) =
                        ideal_class (ring_of_integers l)
                          (ideal_generated (ring_of_integers l) (IMAGE h j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_integers l:B ring`;
                 `h:A->B`] DEDEKIND_CLASS_GROUP_EXTENSION) THEN
  REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS] THEN DISCH_TAC THEN
  MATCH_MP_TAC RING_MONOMORPHISM_RING_OF_INTEGERS THEN
  MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
  ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING; NUMBER_FIELD_IMP_FIELD]);;

let NUMBER_FIELD_CLASS_GROUP_NORM = prove
 (`!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> ?g. group_homomorphism(class_group(ring_of_integers l),
                                   class_group(ring_of_integers k)) g /\
                !J. ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l})
                    ==> g(ideal_class (ring_of_integers l) J) =
                        ideal_class (ring_of_integers k)
                          (number_field_ideal_norm (k,l) h J)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `ring_of_integers k:A ring`;
                 `number_field_ideal_norm (k:A ring,l:B ring) h`]
    CLASS_GROUP_HOMOMORPHISM_IDEAL_MAP) THEN
  REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[NUMBER_FIELD_IDEAL_NORM_IDEAL;
               NUMBER_FIELD_IDEAL_NORM_EQ_0;
               NUMBER_FIELD_IDEAL_NORM_MUL] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NUMBER_FIELD_IDEAL_NORM_PRINCIPAL] THEN
  REWRITE_TAC[principal_ideal] THEN
  EXISTS_TAC `algebra_norm (k,l) (h:A->B) a` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC NUMBER_FIELD_NORM_INTEGRAL THEN ASM_REWRITE_TAC[]);;

(* The composite Cl(O_k) -> Cl(O_l) -> Cl(O_k) is the [l:k]-th power map.    *)

let NUMBER_FIELD_CLASS_GROUP_NORM_EXTENSION = prove
 (`!k:A ring l:B ring h f g.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        (!j. ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
             ==> f(ideal_class (ring_of_integers k) j) =
                 ideal_class (ring_of_integers l)
                   (ideal_generated (ring_of_integers l) (IMAGE h j))) /\
        (!J. ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l})
             ==> g(ideal_class (ring_of_integers l) J) =
                 ideal_class (ring_of_integers k)
                   (number_field_ideal_norm (k,l) h J))
        ==> !c. c IN group_carrier(class_group(ring_of_integers k))
                ==> g(f c) = group_pow (class_group(ring_of_integers k)) c
                               (extension_degree(k,l) h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CLASS_GROUP; DEDEKIND_RING_OF_INTEGERS; ideal_classes;
               FORALL_IN_GSPEC; RING_OF_INTEGERS] THEN
  X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `j:A->bool`]
    RING_OF_INTEGERS_IDEAL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  ASM_SIMP_TAC[RING_IDEAL_IDEAL_GENERATED;
               NUMBER_FIELD_IDEAL_NORM_EXTENSION] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CLASS_GROUP_POW THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS]);;

let NUMBER_FIELD_CLASS_GROUP_EXTENSION_NORM_GALOIS = prove
 (`!k:A ring l:B ring h f g J.
        number_field l /\ galois_extension(k,l) h /\
        (!j. ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
             ==> f(ideal_class (ring_of_integers k) j) =
                 ideal_class (ring_of_integers l)
                   (ideal_generated (ring_of_integers l) (IMAGE h j))) /\
        (!J. ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l})
             ==> g(ideal_class (ring_of_integers l) J) =
                 ideal_class (ring_of_integers k)
                   (number_field_ideal_norm (k,l) h J)) /\
        ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l})
        ==> f(g(ideal_class (ring_of_integers l) J)) =
            ideal_class (ring_of_integers l)
              (ideal_product (ring_of_integers l)
                 (group_carrier(galois_group (k,l) h)) (\s. IMAGE s J))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `field k /\ ring_homomorphism(k,l) (h:A->B)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
    SIMP_TAC[field_extension; RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[NUMBER_FIELD_GALOIS_PRODUCT_IDEAL_NORM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[NUMBER_FIELD_IDEAL_NORM_IDEAL;
               NUMBER_FIELD_IDEAL_NORM_EQ_0]);;

let NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_POW = prove
 (`!k:A ring l:B ring h j.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        ring_ideal (ring_of_integers k) j /\
        principal_ideal (ring_of_integers l)
          (ideal_generated (ring_of_integers l) (IMAGE h j))
        ==> principal_ideal (ring_of_integers k)
              (ideal_pow (ring_of_integers k) j (extension_degree(k,l) h))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[principal_ideal; IMP_CONJ] THEN
  REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[GSYM NUMBER_FIELD_IDEAL_NORM_EXTENSION] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[NUMBER_FIELD_IDEAL_NORM_PRINCIPAL] THEN
  EXISTS_TAC `algebra_norm (k,l) (h:A->B) x` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC NUMBER_FIELD_NORM_INTEGRAL THEN ASM_REWRITE_TAC[]);;

let NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_COPRIME = prove
 (`!k:A ring l:B ring h j.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        ring_ideal (ring_of_integers k) j /\
        coprime(extension_degree(k,l) h,class_number(ring_of_integers k))
        ==> (principal_ideal (ring_of_integers l)
               (ideal_generated (ring_of_integers l) (IMAGE h j)) <=>
             principal_ideal (ring_of_integers k) j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME THEN
    EXISTS_TAC `extension_degree(k:A ring,l:B ring) h` THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS;
                 NUMBER_FIELD_CLASS_GROUP_FINITE] THEN
    MATCH_MP_TAC NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_POW THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[principal_ideal] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` (STRIP_ASSUME_TAC o GSYM)) THEN
    EXISTS_TAC `(h:A->B) a` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `ring_homomorphism(ring_of_integers k,ring_of_integers l) (h:A->B)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_OF_INTEGERS]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_IMAGE_IDEAL_GENERATED; SING_SUBSET] THEN
    REWRITE_TAC[IMAGE_CLAUSES]]);;

(* ------------------------------------------------------------------------- *)
(* Degree coprime to the class number: injective extension, surjective norm. *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_CLASS_GROUP_EXTENSION_MONOMORPHISM = prove
 (`!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        coprime(extension_degree(k,l) h,class_number(ring_of_integers k))
        ==> ?f. group_monomorphism(class_group(ring_of_integers k),
                                   class_group(ring_of_integers l)) f /\
                !j. ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
                    ==> f(ideal_class (ring_of_integers k) j) =
                        ideal_class (ring_of_integers l)
                          (ideal_generated (ring_of_integers l) (IMAGE h j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_CLASS_GROUP_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `f:((A->bool)->bool)->((B->bool)->bool)` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[GROUP_MONOMORPHISM] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!c. c IN group_carrier(class_group(ring_of_integers k))
        ==> (f:((A->bool)->bool)->((B->bool)->bool)) c =
            group_id(class_group(ring_of_integers l))
            ==> c = group_id(class_group(ring_of_integers k))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CONJUNCT1 CLASS_GROUP; DEDEKIND_RING_OF_INTEGERS;
                 ideal_classes; FORALL_IN_GSPEC; RING_OF_INTEGERS] THEN
    X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `j:A->bool`]
      RING_OF_INTEGERS_IDEAL_EXTENSION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`;
                   `ideal_generated (ring_of_integers l) (IMAGE (h:A->B) j)`]
      IDEAL_CLASS_EQ_ID) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`]
      IDEAL_CLASS_EQ_ID) THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_OF_INTEGERS] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    ASM_MESON_TAC[NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_COPRIME];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[group_kernel; IN_ELIM_THM; IN_SING] THEN
  X_GEN_TAC `c:(A->bool)->bool` THEN EQ_TAC THENL
   [ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GROUP_ID] THEN
    ASM_MESON_TAC[GROUP_HOMOMORPHISM_OF_ID]]);;

let NUMBER_FIELD_CLASS_GROUP_NORM_EPIMORPHISM = prove
 (`!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        coprime(extension_degree(k,l) h,class_number(ring_of_integers k))
        ==> ?g. group_epimorphism(class_group(ring_of_integers l),
                                  class_group(ring_of_integers k)) g /\
                !J. ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l})
                    ==> g(ideal_class (ring_of_integers l) J) =
                        ideal_class (ring_of_integers k)
                          (number_field_ideal_norm (k,l) h J)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_CLASS_GROUP_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:((A->bool)->bool)->((B->bool)->bool)`
    STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_CLASS_GROUP_NORM) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `g:((B->bool)->bool)->((A->bool)->bool)` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[group_epimorphism] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`;
                 `f:((A->bool)->bool)->((B->bool)->bool)`;
                 `g:((B->bool)->bool)->((A->bool)->bool)`]
    NUMBER_FIELD_CLASS_GROUP_NORM_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ASM_MESON_TAC[group_homomorphism]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN
  X_GEN_TAC `c:(A->bool)->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`extension_degree(k:A ring,l:B ring) h`; `1`;
                 `class_number(ring_of_integers k:A ring)`] CONG_SOLVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  EXISTS_TAC
   `(f:((A->bool)->bool)->((B->bool)->bool))
      (group_pow (class_group(ring_of_integers k)) c m)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[group_homomorphism; GROUP_POW; SUBSET; FUN_IN_IMAGE]] THEN
  ASM_SIMP_TAC[GROUP_POW] THEN
  ASM_SIMP_TAC[GSYM GROUP_POW_MUL] THEN
  TRANS_TAC EQ_TRANS
   `group_pow (class_group(ring_of_integers k)) (c:(A->bool)->bool) 1` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[GROUP_POW_1]; ALL_TAC] THEN
  ASM_SIMP_TAC[GROUP_POW_EQ] THEN
  MATCH_MP_TAC CONG_DIVIDES_MODULUS THEN
  EXISTS_TAC `class_number(ring_of_integers k:A ring)` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[CONG_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`class_group(ring_of_integers k:A ring)`;
                   `c:(A->bool)->bool`]
      GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER) THEN
    MP_TAC(ISPEC `k:A ring` HAS_SIZE_CLASS_GROUP) THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
    ASM_SIMP_TAC[HAS_SIZE]]);;

let NUMBER_FIELD_CLASS_NUMBER_DIVIDES = prove
 (`!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        coprime(extension_degree(k,l) h,class_number(ring_of_integers k))
        ==> class_number(ring_of_integers k) divides
            class_number(ring_of_integers l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_CLASS_GROUP_NORM_EPIMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:((B->bool)->bool)->((A->bool)->bool)`
    (MP_TAC o CONJUNCT1)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    CARD_DIVIDES_GROUP_EPIMORPHIC_IMAGE)) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ASM_SIMP_TAC[FINITE_CLASS_GROUP] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CLASS_GROUP; DEDEKIND_RING_OF_INTEGERS; class_number]);;
