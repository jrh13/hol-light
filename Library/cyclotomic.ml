(* ========================================================================= *)
(* Cyclotomic extensions: the Galois group of k(z), for z of order n, as a   *)
(* subgroup of the multiplicative group of units modulo n, and all of it     *)
(* exactly when [k(z):k] = phi(n).                                           *)
(* ========================================================================= *)

needs "Library/galois.ml";;
needs "Library/modmul_group.ml";;

prioritize_num();;

(* For l generated over the image of k by an element z of finite order n,    *)
(* every element f of the Galois group sends z to a power z^e with e a unit  *)
(* mod n, and f |-> e is a monomorphism from the Galois group into the       *)
(* multiplicative group modmul_group n of the units mod n.                   *)

let CYCLOTOMIC_GALOIS_GROUP_MODMUL = prove
 (`!(h:A->B) k l z n.
        field l /\ z IN ring_carrier l /\ ring_order l z = n /\ ~(n = 0) /\
        subfield_generated l (z INSERT IMAGE h (ring_carrier k)) = l
        ==> ?e. group_monomorphism(galois_group(k,l) h,modmul_group n) e /\
                !f. f IN group_carrier(galois_group(k,l) h)
                    ==> f z = ring_pow l z (e f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  SUBGOAL_THEN
   `!f. f IN group_carrier(galois_group(k,l) (h:A->B))
        ==> ?j. j IN group_carrier(modmul_group n) /\ f z = ring_pow l z j`
  MP_TAC THENL
   [X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
    REWRITE_TAC[MODMUL_GROUP] THEN COND_CASES_TAC THENL
     [EXISTS_TAC `1` THEN REWRITE_TAC[IN_SING] THEN
      SUBGOAL_THEN `z = ring_1(l:B ring)` SUBST1_TAC THENL
       [ASM_MESON_TAC[RING_ORDER_EQ_1;
                      ARITH_RULE `n <= 1 /\ ~(n = 0) ==> n = 1`];
        ASM_MESON_TAC[RING_POW_1; RING_1; RING_HOMOMORPHISM_1]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`; `f:B->B`; `z:B`]
      RING_ENDOMORPHISM_ROOT_OF_UNITY) THEN
    ASM_REWRITE_TAC[ring_endomorphism] THEN
    DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN
    MP_TAC(ISPECL [`l:B ring`; `inverse(f:B->B)`; `z:B`]
      RING_ENDOMORPHISM_ROOT_OF_UNITY) THEN
    ASM_REWRITE_TAC[ring_endomorphism] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[GALOIS_GROUP_INVERSE; GALOIS_GROUP_RING_HOMOMORPHISM];
      DISCH_THEN(X_CHOOSE_TAC `i:num`)] THEN
    EXISTS_TAC `j MOD n` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[MOD_LT_EQ; COPRIME_LMOD] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `ring_pow l (z:B) (j * i) = ring_pow l z 1` MP_TAC THENL
       [ASM_SIMP_TAC[RING_POW_1; GSYM RING_POW_POW] THEN
        UNDISCH_TAC `(f:B->B) z = ring_pow l z j` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_POW
          (ASSUME `ring_homomorphism(l,l) (f:B->B)`))] THEN
        UNDISCH_TAC `inverse(f:B->B) z = ring_pow l z i` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        ASM_MESON_TAC[PERMUTES_INVERSES; GALOIS_GROUP_PERMUTES];
        ASM_SIMP_TAC[RING_POW_EQ_GEN] THEN CONV_TAC NUMBER_RULE];
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ring_order l (z:B) = n` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[RING_POW_MOD_ORDER]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `e:(B->B)->num` THEN DISCH_THEN(LABEL_TAC "e") THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[group_monomorphism; GROUP_HOMOMORPHISM; SUBSET;
              FORALL_IN_IMAGE] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ALL_TAC;
    MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC GALOIS_GROUP_EQ_ON_GENERATORS THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`; `l:B ring`; `{z:B}`] THEN
    ASM_REWRITE_TAC[SET_RULE `(s:B->bool) UNION {a} = a INSERT s`; IN_SING;
                    FORALL_UNWIND_THM2] THEN
    ASM_MESON_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:B->B) o g IN group_carrier(galois_group(k,l) (h:A->B))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[GALOIS_GROUP_COMPOSE]; ALL_TAC] THEN
  REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 GALOIS_GROUP))] THEN
  REWRITE_TAC[MODMUL_GROUP] THEN COND_CASES_TAC THEN BETA_TAC THENL
   [USE_THEN "e" (MP_TAC o CONJUNCT1 o C MATCH_MP
      (ASSUME `(f:B->B) o g IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
    ASM_REWRITE_TAC[MODMUL_GROUP; IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f. f IN group_carrier(galois_group(k,l) (h:A->B))
        ==> (e:(B->B)->num) f < n`
  ASSUME_TAC THENL
   [X_GEN_TAC `f':B->B` THEN DISCH_TAC THEN
    USE_THEN "e" (MP_TAC o CONJUNCT1 o C MATCH_MP
      (ASSUME `(f':B->B) IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
    ASM_REWRITE_TAC[MODMUL_GROUP; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL [`l:B ring`; `z:B`] RING_POW_EQ_LT) THEN
  ASM_SIMP_TAC[MOD_LT_EQ] THEN
  USE_THEN "e" (MP_TAC o CONJUNCT2 o C MATCH_MP
    (ASSUME `(f:B->B) o g IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `ring_order l (z:B) = n` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[RING_POW_MOD_ORDER] THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN
   `(g:B->B) z = ring_pow l z (e g) /\ (f:B->B) z = ring_pow l z (e f)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASSUME_TAC(MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM
   (ASSUME `(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`)) THEN
  ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_POW
    (ASSUME `ring_homomorphism(l,l) (f:B->B)`)] THEN
  ASM_SIMP_TAC[RING_POW_POW]);;

(* The monomorphism e is an isomorphism exactly when [l:k] = phi(n): the     *)
(* extension is finite and Galois (CYCLOTOMIC_EXTENSION_ABELIAN), so its     *)
(* group has [l:k] elements (GALOIS_EXTENSION_EQ_CARD), modmul_group n has   *)
(* phi(n) elements (HAS_SIZE_MODMUL_GROUP), and a monomorphism between       *)
(* finite groups of the same size is onto                                    *)
(* (GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE).                               *)
let CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM = prove
 (`!(h:A->B) k l z n.
        field_extension(k,l) h /\
        z IN ring_carrier l /\ ring_order l z = n /\ ~(n = 0) /\
        subfield_generated l (z INSERT IMAGE h (ring_carrier k)) = l
        ==> ((?e. group_isomorphism(galois_group(k,l) h,modmul_group n) e /\
                  !f. f IN group_carrier(galois_group(k,l) h)
                      ==> f z = ring_pow l z (e f)) <=>
             extension_degree(k,l) h = phi n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `z:B`; `n:num`]
    CYCLOTOMIC_EXTENSION_ABELIAN) THEN
  ASM_SIMP_TAC[RING_POW_EQ_1; DIVIDES_REFL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    GALOIS_EXTENSION_EQ_CARD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPEC `n:num` HAS_SIZE_MODMUL_GROUP) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_GALOIS_GROUP) THEN EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN (MP_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_ISOMORPHIC o
      CONJUNCT1)) THEN
    ASM_MESON_TAC[ISOMORPHIC_GROUP_ORDER];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `z:B`; `n:num`]
    CYCLOTOMIC_GALOIS_GROUP_MODMUL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[field_extension]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:(B->B)->num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE; FINITE_MODMUL_GROUP]);;
