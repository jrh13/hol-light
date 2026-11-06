(* ========================================================================= *)
(* The ideal class group of a Dedekind domain as a group, in the sense of    *)
(* Library/grouptheory.ml.                                                   *)
(*                                                                           *)
(*   class_group r = the group with carrier ideal_classes r, identity the    *)
(*                   class of the unit ideal, the class of jk as the product *)
(*                   of the classes of j and k, and as inverse of the class  *)
(*                   of j the ideals k with jk nonzero principal.            *)
(*                                                                           *)
(* Main results, for a Dedekind domain r: the characterization CLASS_GROUP   *)
(* (in the style of QUOTIENT_GROUP), products, inverses and powers of        *)
(* classes (CLASS_GROUP_MUL, CLASS_GROUP_INV, CLASS_GROUP_POW), the class of *)
(* j is the identity iff j is principal (IDEAL_CLASS_EQ_ID,                  *)
(* CLASS_GROUP_POW_EQ_ID), the class group is abelian, and it is trivial iff *)
(* r is a PID. For a number field k the class group of ring_of_integers k is *)
(* finite of order the class number h (HAS_SIZE_CLASS_GROUP), so j^h is      *)
(* principal for every ideal j (Lagrange, GROUP_POW_GROUP_ORDER;             *)
(* NUMBER_FIELD_PRINCIPAL_IDEAL_POW_CLASS_NUMBER). With finitely many        *)
(* classes and n coprime to the class number, j^n principal implies j        *)
(* principal (DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME,                          *)
(* NUMBER_FIELD_PRINCIPAL_IDEAL_POW_COPRIME), and coprime x, y ((x) + (y) =  *)
(* r) with x y = z^n, n <> 0, give x = u w^n with u a unit                   *)
(* (DEDEKIND_COPRIME_MUL_POW, NUMBER_FIELD_COPRIME_MUL_POW; the analogue of  *)
(* UFD_COPRIME_MUL_POW of ANT/ufd.ml, through                                *)
(* DEDEKIND_IDEAL_COPRIME_PROD_POW of ANT/dedekind.ml). A map g from the     *)
(* ideals of a Dedekind domain r to the ideals of a Dedekind domain s that   *)
(* maps nonzero ideals to nonzero ideals, products to products and nonzero   *)
(* principal ideals to principal ideals induces a homomorphism of the class  *)
(* groups with [j] |-> [g(j)] (CLASS_GROUP_HOMOMORPHISM_IDEAL_MAP; well      *)
(* defined since (a) j1 = (b) j2 gives (c) g(j1) = (d) g(j2) with g((a)) =   *)
(* (c) and g((b)) = (d)); for a ring monomorphism h : r -> s this applies to *)
(* the extension of ideals j |-> j s = ideal_generated s (IMAGE h j)         *)
(* (DEDEKIND_CLASS_GROUP_EXTENSION, by IDEAL_PROD_HOMOMORPHIC_IMAGE,         *)
(* IDEAL_GENERATED_IMAGE_IDEAL_GENERATED and                                 *)
(* IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0 of ANT/ideal_arith.ml).            *)
(*                                                                           *)
(* The zero ideal has the empty class, and both operations give the empty    *)
(* set on it, so CLASS_GROUP_MUL and CLASS_GROUP_POW need no hypothesis that *)
(* the ideals are nonzero.                                                   *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/grouptheory.ml, ANT/ideal_arith.ml,  *)
(* ANT/dedekind.ml, ANT/dedekind_struct.ml (ideal_class, IN_IDEAL_CLASS,     *)
(* DEDEKIND_IDEAL_CLASS_INVERSE), ANT/numfield.ml, ANT/ring_of_integers.ml   *)
(* (DEDEKIND_RING_OF_INTEGERS) and ANT/classgroup.ml.                        *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/grouptheory.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/dedekind_struct.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/classgroup.ml";;

(* ------------------------------------------------------------------------- *)
(* The class group.                                                          *)
(* ------------------------------------------------------------------------- *)

(* The product of classes c and d is the set of ideals equivalent to some   *)
(* jk with j in c and k in d; the inverse of c is the set of ideals k with   *)
(* jk equivalent to the unit ideal (nonzero principal) for some j in c.      *)

let class_group = new_definition
 `class_group (r:A ring) =
    group(ideal_classes r,
          ideal_class r (ring_carrier r),
          (\c. {k | ring_ideal r k /\
                    ?j. j IN c /\
                        ring_carrier r IN ideal_class r (ideal_prod r j k)}),
          (\c d. {l | ?j k. j IN c /\ k IN d /\
                            l IN ideal_class r (ideal_prod r j k)}))`;;

let CLASS_GROUP =
  let lemma = prove
   (`!r j:A->bool.
          dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r})
          ==> ?k. ring_ideal r k /\ ~(k = {ring_0 r}) /\
                  ring_carrier r IN ideal_class r (ideal_prod r j k) /\
                  {l | ring_ideal r l /\
                       ?m. m IN ideal_class r j /\
                           ring_carrier r IN ideal_class r (ideal_prod r m l)} =
                  ideal_class r k`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) THEN
    MP_TAC(ISPECL [`r:A ring`; `j:A->bool`] DEDEKIND_IDEAL_CLASS_INVERSE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `k:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `l:A->bool` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `m:A->bool` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `ring_ideal r m /\ ~(l = {ring_0 r:A})`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC
         `(ring_carrier r:A->bool) IN ideal_class r (ideal_prod r m l)` THEN
        UNDISCH_TAC `(m:A->bool) IN ideal_class r j` THEN
        REWRITE_TAC[IN_IDEAL_CLASS] THEN REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~(ideal_prod r m l = {ring_0 r:A})` THEN
        ASM_SIMP_TAC[IDEAL_PROD_RZERO; RING_IDEAL_IMP_SUBSET];
        ALL_TAC] THEN
      (* With j ~ k for k IN ideal_class r j and R for the unit ideal:    *)
      (* k = k R ~ k (j l) = (j k) l ~ R l = l, as j l ~ m l ~ R ~ j k.   *)
      MATCH_MP_TAC IDEAL_CLASS_TRANS THEN
      EXISTS_TAC `ideal_prod r (ideal_prod r j k) l:A->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `(ideal_prod r j l:A->bool) IN ideal_class r (ring_carrier r)`
        ASSUME_TAC THENL
         [MATCH_MP_TAC IDEAL_CLASS_SYM THEN
          MATCH_MP_TAC IDEAL_CLASS_TRANS THEN
          EXISTS_TAC `ideal_prod r m l:A->bool` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC IDEAL_CLASS_MUL THEN
          ASM_SIMP_TAC[IDEAL_CLASS_REFL];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`r:A ring`; `k:A->bool`; `ring_carrier r:A->bool`;
                       `k:A->bool`; `ideal_prod r j l:A->bool`]
          IDEAL_CLASS_MUL) THEN
        ASM_SIMP_TAC[IDEAL_CLASS_REFL; IDEAL_PROD_CARRIER] THEN
        ASM_SIMP_TAC[IDEAL_PROD_AC; RING_IDEAL_IMP_SUBSET];
        MP_TAC(ISPECL [`r:A ring`; `ideal_prod r j k:A->bool`; `l:A->bool`;
                       `ring_carrier r:A->bool`; `l:A->bool`]
          IDEAL_CLASS_MUL) THEN
        ASM_SIMP_TAC[IDEAL_CLASS_REFL; IDEAL_PROD_CARRIER_LEFT]];
      DISCH_TAC THEN CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IDEAL_CLASS]) THEN
        SIMP_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `j:A->bool` THEN ASM_SIMP_TAC[IDEAL_CLASS_REFL] THEN
      MATCH_MP_TAC IDEAL_CLASS_TRANS THEN
      EXISTS_TAC `ideal_prod r j k:A->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC IDEAL_CLASS_MUL THEN
      ASM_SIMP_TAC[IDEAL_CLASS_REFL; IDEAL_CLASS_SYM]]) in
  prove
   (`(!r:A ring.
          dedekind_domain r
          ==> group_carrier(class_group r) = ideal_classes r) /\
     (!r:A ring.
          dedekind_domain r
          ==> group_id(class_group r) = ideal_class r (ring_carrier r)) /\
     (!r:A ring.
          dedekind_domain r
          ==> group_inv(class_group r) =
              \c. {k | ring_ideal r k /\
                       ?j. j IN c /\
                           ring_carrier r IN
                           ideal_class r (ideal_prod r j k)}) /\
     (!r:A ring.
          dedekind_domain r
          ==> group_mul(class_group r) =
              \c d. {l | ?j k. j IN c /\ k IN d /\
                               l IN ideal_class r (ideal_prod r j k)})`,
    REWRITE_TAC[AND_FORALL_THM; TAUT
     `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
    X_GEN_TAC `r:A ring` THEN DISCH_TAC THEN
    MP_TAC(fst(EQ_IMP_RULE
     (ISPEC(rand(rand(snd(strip_forall(concl class_group)))))
     (CONJUNCT2 group_tybij)))) THEN
    REWRITE_TAC[GSYM class_group] THEN ANTS_TAC THENL
     [ALL_TAC; SIMP_TAC[group_carrier; group_id; group_inv; group_mul]] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INTEGRAL_DOMAIN_UNIT_IDEAL) THEN
    SUBGOAL_THEN
     `!j k. ring_ideal r j /\ ring_ideal r k
            ==> {l | ?j' k'. j' IN ideal_class r j /\ k' IN ideal_class r k /\
                             l IN ideal_class r (ideal_prod r j' k')} =
                ideal_class r (ideal_prod r j k:A->bool)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      X_GEN_TAC `l:A->bool` THEN EQ_TAC THENL
       [ASM_MESON_TAC[IDEAL_CLASS_MUL; IDEAL_CLASS_TRANS];
        DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`j:A->bool`; `k:A->bool`] THEN
        FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
          GEN_REWRITE_RULE I [IN_IDEAL_CLASS]) THEN
        ASM_SIMP_TAC[IDEAL_PROD_EQ_ZERO; DE_MORGAN_THM;
                     IDEAL_CLASS_REFL]];
      ALL_TAC] THEN
    MP_TAC(ISPEC `r:A ring` lemma) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `iv:(A->bool)->A->bool`) THEN
    REWRITE_TAC[ideal_classes; RIGHT_FORALL_IMP_THM; IMP_CONJ;
                FORALL_IN_GSPEC] THEN
    SUBGOAL_THEN
     `!j. ring_ideal r j /\ ~(j = {ring_0 r})
          ==> ideal_class r j IN
              {ideal_class r j | j | ring_ideal r j /\ ~(j = {ring_0 r:A})}`
    ASSUME_TAC THENL [REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    ASM_SIMP_TAC[RING_IDEAL_IDEAL_PROD; IDEAL_PROD_EQ_ZERO;
                 IDEAL_PROD_CARRIER; IDEAL_PROD_CARRIER_LEFT] THENL
     [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC IDEAL_PROD_ASSOC THEN
      ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET];
      MP_TAC(ISPECL [`r:A ring`; `iv(j:A->bool):A->bool`; `j:A->bool`]
        IDEAL_PROD_COMM) THEN
      ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; IDEAL_CLASS_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Classes as elements of the class group.                                   *)
(* ------------------------------------------------------------------------- *)

let IDEAL_CLASS_IN_CLASS_GROUP = prove
 (`!r j:A->bool.
        dedekind_domain r
        ==> (ideal_class r j IN group_carrier(class_group r) <=>
             ring_ideal r j /\ ~(j = {ring_0 r}))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CLASS_GROUP; ideal_classes; IN_ELIM_THM] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`; `k:A->bool`] IDEAL_CLASS_EQ) THEN
  ASM_SIMP_TAC[DEDEKIND_IMP_INTEGRAL_DOMAIN; IN_IDEAL_CLASS]);;

(* The zero ideal has the empty class, and the product of classes is empty   *)
(* if one factor is; so no nonzero hypotheses here and in CLASS_GROUP_POW.   *)

let CLASS_GROUP_MUL = prove
 (`!r j k:A->bool.
        dedekind_domain r /\ ring_ideal r j /\ ring_ideal r k
        ==> group_mul (class_group r) (ideal_class r j) (ideal_class r k) =
            ideal_class r (ideal_prod r j k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) THEN
  ASM_SIMP_TAC[CLASS_GROUP] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `l:A->bool` THEN EQ_TAC THENL
   [ASM_MESON_TAC[IDEAL_CLASS_MUL; IDEAL_CLASS_TRANS];
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`j:A->bool`; `k:A->bool`] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [IN_IDEAL_CLASS]) THEN
    ASM_SIMP_TAC[IDEAL_PROD_EQ_ZERO; DE_MORGAN_THM; IDEAL_CLASS_REFL]]);;

let IDEAL_CLASS_EQ_ID = prove
 (`!r j:A->bool.
        dedekind_domain r /\ ~(j = {ring_0 r})
        ==> (ideal_class r j = group_id(class_group r) <=>
             principal_ideal r j)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CLASS_GROUP] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INTEGRAL_DOMAIN_UNIT_IDEAL) THEN
  ASM_SIMP_TAC[IDEAL_CLASS_EQ] THEN
  ASM_MESON_TAC[IDEAL_CLASS_PRINCIPAL; PRINCIPAL_IDEAL_CLASS]);;

let CLASS_GROUP_INV = prove
 (`!r j k:A->bool.
        dedekind_domain r /\
        ring_ideal r j /\ ~(j = {ring_0 r}) /\
        ring_ideal r k /\ ~(k = {ring_0 r})
        ==> (group_inv (class_group r) (ideal_class r j) = ideal_class r k <=>
             principal_ideal r (ideal_prod r j k))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GROUP_LINV_EQ; IDEAL_CLASS_IN_CLASS_GROUP; CLASS_GROUP_MUL] THEN
  MATCH_MP_TAC IDEAL_CLASS_EQ_ID THEN
  ASM_SIMP_TAC[IDEAL_PROD_EQ_ZERO; DEDEKIND_IMP_INTEGRAL_DOMAIN]);;

let CLASS_GROUP_POW = prove
 (`!r (j:A->bool) n.
        dedekind_domain r /\ ring_ideal r j
        ==> group_pow (class_group r) (ideal_class r j) n =
            ideal_class r (ideal_pow r j n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[group_pow; ideal_pow; CLASS_GROUP_MUL; RING_IDEAL_IDEAL_POW] THEN
  ASM_SIMP_TAC[CLASS_GROUP]);;

let CLASS_GROUP_POW_EQ_ID = prove
 (`!r (j:A->bool) n.
        dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r})
        ==> (group_pow (class_group r) (ideal_class r j) n =
             group_id(class_group r) <=>
             principal_ideal r (ideal_pow r j n))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CLASS_GROUP_POW] THEN
  MATCH_MP_TAC IDEAL_CLASS_EQ_ID THEN
  ASM_SIMP_TAC[IDEAL_POW_EQ_ZERO; DEDEKIND_IMP_INTEGRAL_DOMAIN]);;

(* ------------------------------------------------------------------------- *)
(* The class group is abelian, and trivial exactly for a PID.                *)
(* ------------------------------------------------------------------------- *)

let ABELIAN_CLASS_GROUP = prove
 (`!r:A ring. dedekind_domain r ==> abelian_group(class_group r)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[abelian_group; CONJUNCT1 CLASS_GROUP; ideal_classes;
               IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[CLASS_GROUP_MUL] THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN
  ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET]);;

let TRIVIAL_CLASS_GROUP = prove
 (`!r:A ring. dedekind_domain r ==> (trivial_group(class_group r) <=> PID r)`,
  SIMP_TAC[TRIVIAL_GROUP_HAS_SIZE_1; CLASS_GROUP;
           DEDEKIND_PID_EQ_CLASS_NUMBER_1]);;

(* ------------------------------------------------------------------------- *)
(* Finite class groups: h-th powers are principal; number fields.            *)
(* ------------------------------------------------------------------------- *)

let DEDEKIND_PRINCIPAL_IDEAL_POW_CLASS_NUMBER = prove
 (`!r j:A->bool.
        dedekind_domain r /\ FINITE(ideal_classes r) /\ ring_ideal r j
        ==> principal_ideal r (ideal_pow r j (class_number r))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `j = {ring_0 r:A}` THENL
   [ASM_CASES_TAC `class_number(r:A ring) = 0` THEN
    ASM_SIMP_TAC[IDEAL_POW_0; PRINCIPAL_IDEAL_CARRIER] THEN
    MP_TAC(ISPECL [`r:A ring`; `j:A->bool`; `class_number(r:A ring)`]
      IDEAL_POW_EQ_ZERO) THEN
    ASM_SIMP_TAC[DEDEKIND_IMP_INTEGRAL_DOMAIN; PRINCIPAL_IDEAL_0];
    ASM_SIMP_TAC[GSYM CLASS_GROUP_POW_EQ_ID] THEN
    MP_TAC(ISPECL [`class_group r:((A->bool)->bool)group`;
                   `ideal_class r (j:A->bool)`] GROUP_POW_GROUP_ORDER) THEN
    ASM_SIMP_TAC[IDEAL_CLASS_IN_CLASS_GROUP; CLASS_GROUP; class_number]]);;

let FINITE_CLASS_GROUP = prove
 (`!k:A ring.
        number_field k
        ==> FINITE(group_carrier(class_group(ring_of_integers k)))`,
  SIMP_TAC[CLASS_GROUP; DEDEKIND_RING_OF_INTEGERS;
           NUMBER_FIELD_CLASS_GROUP_FINITE]);;

let HAS_SIZE_CLASS_GROUP = prove
 (`!k:A ring.
        number_field k
        ==> group_carrier(class_group(ring_of_integers k)) HAS_SIZE
            class_number(ring_of_integers k)`,
  SIMP_TAC[HAS_SIZE; class_number; CLASS_GROUP; DEDEKIND_RING_OF_INTEGERS;
           NUMBER_FIELD_CLASS_GROUP_FINITE]);;

let NUMBER_FIELD_PRINCIPAL_IDEAL_POW_CLASS_NUMBER = prove
 (`!k j:A->bool.
        number_field k /\ ring_ideal (ring_of_integers k) j
        ==> principal_ideal (ring_of_integers k)
              (ideal_pow (ring_of_integers k) j
                 (class_number(ring_of_integers k)))`,
  SIMP_TAC[DEDEKIND_PRINCIPAL_IDEAL_POW_CLASS_NUMBER;
           DEDEKIND_RING_OF_INTEGERS; NUMBER_FIELD_CLASS_GROUP_FINITE]);;

let DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME = prove
 (`!r j:A->bool n.
        dedekind_domain r /\ FINITE(ideal_classes r) /\ ring_ideal r j /\
        coprime(n,class_number r) /\ principal_ideal r (ideal_pow r j n)
        ==> principal_ideal r j`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `j = {ring_0 r:A}` THEN
  ASM_REWRITE_TAC[PRINCIPAL_IDEAL_0] THEN
  ASM_SIMP_TAC[GSYM IDEAL_CLASS_EQ_ID] THEN
  SUBGOAL_THEN `ideal_class r (j:A->bool) IN group_carrier(class_group r)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[IDEAL_CLASS_IN_CLASS_GROUP]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM GROUP_ELEMENT_ORDER_EQ_1] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [coprime]) THEN
  ASM_SIMP_TAC[GSYM GROUP_POW_EQ_ID] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CLASS_GROUP_POW_EQ_ID];
    MP_TAC(ISPECL [`class_group r:((A->bool)->bool)group`;
                   `ideal_class r (j:A->bool)`] GROUP_POW_GROUP_ORDER) THEN
    ASM_SIMP_TAC[CLASS_GROUP; class_number]]);;

let NUMBER_FIELD_PRINCIPAL_IDEAL_POW_COPRIME = prove
 (`!k j:A->bool n.
        number_field k /\ ring_ideal (ring_of_integers k) j /\
        coprime(n,class_number(ring_of_integers k)) /\
        principal_ideal (ring_of_integers k)
                        (ideal_pow (ring_of_integers k) j n)
        ==> principal_ideal (ring_of_integers k) j`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME THEN
  EXISTS_TAC `n:num` THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; NUMBER_FIELD_CLASS_GROUP_FINITE]);;

let DEDEKIND_COPRIME_MUL_POW = prove
 (`!r x y z:A n.
        dedekind_domain r /\ FINITE(ideal_classes r) /\
        coprime(n,class_number r) /\ ~(n = 0) /\
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r /\
        ring_setadd r (ideal_generated r {x}) (ideal_generated r {y}) =
        ring_carrier r /\
        ring_mul r x y = ring_pow r z n
        ==> ?u w. ring_unit r u /\ w IN ring_carrier r /\
                  x = ring_mul r u (ring_pow r w n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) THEN
  MP_TAC(ISPECL [`r:A ring`; `ideal_generated r {x:A}`;
                 `ideal_generated r {y:A}`; `ideal_generated r {z:A}`;
                 `n:num`] DEDEKIND_IDEAL_COPRIME_PROD_POW) THEN
  ASM_SIMP_TAC[RING_IDEAL_IDEAL_GENERATED; IDEAL_PROD_PRINCIPAL;
               IDEAL_POW_PRINCIPAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A->bool` (X_CHOOSE_THEN `b:A->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`r:A ring`; `a:A->bool`; `n:num`]
    DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      rand(concl th) = `ideal_pow r (a:A->bool) n`)) THEN
    REWRITE_TAC[principal_ideal] THEN ASM_MESON_TAC[];
    REWRITE_TAC[principal_ideal; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `w:A` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (SUBST_ALL_TAC o SYM)) THEN
  UNDISCH_TAC
   `ideal_generated r {x:A} = ideal_pow r (ideal_generated r {w}) n` THEN
  ASM_SIMP_TAC[IDEAL_POW_PRINCIPAL; IDEALS_GENERATED_SING_EQ; RING_POW] THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_ASSOCIATES] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  MAP_EVERY EXISTS_TAC [`u:A`; `w:A`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_MESON_TAC[RING_MUL_SYM; RING_POW; RING_UNIT_IN_CARRIER]);;

let NUMBER_FIELD_COPRIME_MUL_POW = prove
 (`!k x y z:A n.
        number_field k /\ coprime(n,class_number(ring_of_integers k)) /\
        ~(n = 0) /\
        x IN ring_carrier(ring_of_integers k) /\
        y IN ring_carrier(ring_of_integers k) /\
        z IN ring_carrier(ring_of_integers k) /\
        ring_setadd (ring_of_integers k)
          (ideal_generated (ring_of_integers k) {x})
          (ideal_generated (ring_of_integers k) {y}) =
        ring_carrier(ring_of_integers k) /\
        ring_mul k x y = ring_pow k z n
        ==> ?u w. ring_unit (ring_of_integers k) u /\
                  w IN ring_carrier(ring_of_integers k) /\
                  x = ring_mul k u (ring_pow k w n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `x:A`; `y:A`; `z:A`; `n:num`]
    DEDEKIND_COPRIME_MUL_POW) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; NUMBER_FIELD_CLASS_GROUP_FINITE;
               RING_OF_INTEGERS]);;

(* ------------------------------------------------------------------------- *)
(* Ideal maps compatible with products and principal ideals induce           *)
(* homomorphisms of class groups; the extension map along a monomorphism.    *)
(* ------------------------------------------------------------------------- *)

let CLASS_GROUP_HOMOMORPHISM_IDEAL_MAP =
  let lemma = prove
   (`!r:A ring s:B ring g j j'.
          integral_domain r /\ integral_domain s /\
          (!j. ring_ideal r j /\ ~(j = {ring_0 r})
               ==> ring_ideal s (g j) /\ ~(g j = {ring_0 s})) /\
          (!j k. ring_ideal r j /\ ~(j = {ring_0 r}) /\
                 ring_ideal r k /\ ~(k = {ring_0 r})
                 ==> g(ideal_prod r j k) = ideal_prod s (g j) (g k)) /\
          (!a. a IN ring_carrier r /\ ~(a = ring_0 r)
               ==> ?c. c IN ring_carrier s /\ ~(c = ring_0 s) /\
                       g(ideal_generated r {a}) = ideal_generated s {c}) /\
          j' IN ideal_class r j
          ==> g j' IN ideal_class s (g j)`,
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IDEAL_CLASS]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)))))) THEN
    REWRITE_TAC[IN_IDEAL_CLASS] THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN
     `?c. c IN ring_carrier s /\ ~(c = ring_0 s) /\
          (g:(A->bool)->(B->bool))(ideal_generated r {a:A}) =
          ideal_generated s {c:B}`
    (X_CHOOSE_THEN `c:B` STRIP_ASSUME_TAC) THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?d. d IN ring_carrier s /\ ~(d = ring_0 s) /\
          (g:(A->bool)->(B->bool))(ideal_generated r {b:A}) =
          ideal_generated s {d:B}`
    (X_CHOOSE_THEN `d:B` STRIP_ASSUME_TAC) THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`c:B`; `d:B`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY (fun t -> FIRST_X_ASSUM(SUBST1_TAC o SYM o
                          check (fun th -> rand(concl th) = t)))
     [`ideal_generated s {c:B}`; `ideal_generated s {d:B}`] THEN
    SUBGOAL_THEN
     `ideal_prod s ((g:(A->bool)->(B->bool)) (ideal_generated r {a})) (g j) =
      g(ideal_prod r (ideal_generated r {a}) j) /\
      ideal_prod s (g (ideal_generated r {b})) (g j') =
      g(ideal_prod r (ideal_generated r {b}) j')`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_EQ_0];
      ASM_REWRITE_TAC[]]) in
  prove
   (`!r:A ring s:B ring g.
          dedekind_domain r /\ dedekind_domain s /\
          (!j. ring_ideal r j /\ ~(j = {ring_0 r})
               ==> ring_ideal s (g j) /\ ~(g j = {ring_0 s})) /\
          (!j k. ring_ideal r j /\ ~(j = {ring_0 r}) /\
                 ring_ideal r k /\ ~(k = {ring_0 r})
                 ==> g(ideal_prod r j k) = ideal_prod s (g j) (g k)) /\
          (!a. a IN ring_carrier r /\ ~(a = ring_0 r)
               ==> principal_ideal s (g(ideal_generated r {a})))
          ==> ?f. group_homomorphism(class_group r,class_group s) f /\
                  !j. ring_ideal r j /\ ~(j = {ring_0 r})
                      ==> f(ideal_class r j) = ideal_class s (g j)`,
    REPEAT GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN o
      check (fun th -> concl th = `dedekind_domain(r:A ring)`)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN o
      check (fun th -> concl th = `dedekind_domain(s:B ring)`)) THEN
    SUBGOAL_THEN
     `!a. a IN ring_carrier r /\ ~(a = ring_0 r)
          ==> ?c. c IN ring_carrier s /\ ~(c = ring_0 s) /\
                  (g:(A->bool)->(B->bool))(ideal_generated r {a:A}) =
                  ideal_generated s {c:B}`
    ASSUME_TAC THENL
     [X_GEN_TAC `a:A` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `ring_ideal s ((g:(A->bool)->(B->bool))(ideal_generated r {a:A})) /\
        ~(g(ideal_generated r {a}) = {ring_0 s}) /\
        principal_ideal s (g(ideal_generated r {a}))`
      MP_TAC THENL
       [ASM_SIMP_TAC[RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_EQ_0];
        ALL_TAC] THEN
      REWRITE_TAC[principal_ideal] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `c:B` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `c:B` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[IDEAL_GENERATED_0];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!j j'. j' IN ideal_class r j
             ==> (g:(A->bool)->(B->bool)) j' IN ideal_class s (g j)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN
      EXISTS_TAC `r:A ring` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?f. !j. ring_ideal r j /\ ~(j = {ring_0 r})
              ==> f(ideal_class r j) =
                  ideal_class s ((g:(A->bool)->(B->bool)) j)`
    MP_TAC THENL
     [EXISTS_TAC
       `\c. ideal_class s ((g:(A->bool)->(B->bool))
                             (@j. ring_ideal r j /\ ~(j = {ring_0 r}) /\
                                  c = ideal_class r (j:A->bool)))` THEN
      X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      ABBREV_TAC `j' = @j'. ring_ideal r j' /\ ~(j' = {ring_0 r}) /\
                            ideal_class r j = ideal_class r (j':A->bool)` THEN
      SUBGOAL_THEN
       `ring_ideal r j' /\ ~(j' = {ring_0 r}) /\
        ideal_class r j = ideal_class r (j':A->bool)`
      STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "j'" THEN CONV_TAC SELECT_CONV THEN
        EXISTS_TAC `j:A->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(j':A->bool) IN ideal_class r j` ASSUME_TAC THENL
       [ASM_SIMP_TAC[GSYM IDEAL_CLASS_EQ]; ALL_TAC] THEN
      SUBGOAL_THEN
       `ring_ideal s ((g:(A->bool)->(B->bool)) j') /\ ~(g j' = {ring_0 s})`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`s:B ring`; `(g:(A->bool)->(B->bool)) j`;
                     `(g:(A->bool)->(B->bool)) j'`] IDEAL_CLASS_EQ) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC MONO_EXISTS] THEN
    X_GEN_TAC `f:((A->bool)->bool)->((B->bool)->bool)` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[GROUP_HOMOMORPHISM] THEN
    ASM_SIMP_TAC[CONJUNCT1 CLASS_GROUP; ideal_classes; SUBSET;
                 FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                 FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:A->bool` THEN REPEAT DISCH_TAC THEN
      ASM_SIMP_TAC[IN_ELIM_THM] THEN
      EXISTS_TAC `(g:(A->bool)->(B->bool)) j` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `j:A->bool` THEN REPEAT DISCH_TAC THEN
    X_GEN_TAC `k:A->bool` THEN REPEAT DISCH_TAC THEN
    ASM_SIMP_TAC[CLASS_GROUP_MUL] THEN
    ASM_SIMP_TAC[RING_IDEAL_IDEAL_PROD; IDEAL_PROD_EQ_ZERO]);;

let DEDEKIND_CLASS_GROUP_EXTENSION = prove
 (`!r:A ring s:B ring h.
        dedekind_domain r /\ dedekind_domain s /\ ring_monomorphism(r,s) h
        ==> ?f. group_homomorphism(class_group r,class_group s) f /\
                !j. ring_ideal r j /\ ~(j = {ring_0 r})
                    ==> f(ideal_class r j) =
                        ideal_class s (ideal_generated s (IMAGE h j))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLASS_GROUP_HOMOMORPHISM_IDEAL_MAP THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ASM_SIMP_TAC[RING_IDEAL_IDEAL_GENERATED;
               IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_PROD_HOMOMORPHIC_IMAGE THEN
    ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_IMAGE_IDEAL_GENERATED; SING_SUBSET] THEN
    REWRITE_TAC[principal_ideal; IMAGE_CLAUSES] THEN
    EXISTS_TAC `(h:A->B) a` THEN ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]]);;
