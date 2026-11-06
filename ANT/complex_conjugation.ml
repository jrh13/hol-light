(* ========================================================================= *)
(* Complex conjugation as an element of order 2 of the absolute Galois group *)
(* of Q. No new constant.                                                    *)
(*                                                                           *)
(* For a field k normal over its prime subfield Q = subfield_generated k     *)
(* {ring_0 k} (for example Q-bar, or a Galois number field) and an embedding *)
(* e of k into the complex numbers, complex conjugation restricts to an      *)
(* automorphism c of k: e(c x) = cnj(e x), c c = 1, and c = 1 iff e(k) is    *)
(* real (GALOIS_GROUP_COMPLEX_CONJUGATION). When c is not 1, the elements x  *)
(* with e(x) real form a subfield of k over which k is a finite Galois       *)
(* extension of degree 2 (COMPLEX_CONJUGATION_REAL_SUBFIELD). For k          *)
(* algebraically closed of characteristic 0 and algebraic over Q (Q-bar)     *)
(* there are an embedding e and an element c of order 2 of Gal(k/Q) with e(c *)
(* x) = cnj(e x), and [k : k INTER R] = 2                                    *)
(* (ALGEBRAIC_CLOSURE_COMPLEX_CONJUGATION).                                  *)
(*                                                                           *)
(* Routes. The embedding e and cnj o e agree on Q, the elements where two    *)
(* homomorphisms agree forming a subfield                                    *)
(* (SUBFIELD_OF_HOMOMORPHIC_EQUALITIES, PRIME_SUBFIELD_MINIMAL), so for k    *)
(* normal over Q they have the same image (NORMAL_EXTENSION_IMAGES_EQ), and  *)
(* c = e^-1 o cnj o e on the carrier, the identity off it, is an involutive  *)
(* ring automorphism. The fixed field of the group {1, c} is the set of x    *)
(* with cnj(e x) = e x (REAL_CNJ), so the theorem of Artin                   *)
(* (ARTIN_FIXED_FIELD) gives the degree. For Q-bar, e extends an embedding   *)
(* of Q (PRIME_SUBFIELD_HOMOMORPHISM_EXISTS,                                 *)
(* ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM), k is normal over Q                *)
(* (ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION), and c is not the identity    *)
(* since e(i) is not real for i^2 = -1.                                      *)
(*                                                                           *)
(* Uses: Library/fieldtheory.ml, Library/galois.ml (galois_group,            *)
(* fixed_field, ARTIN_FIXED_FIELD), Multivariate/complex_ring.ml             *)
(* (complex_ring) and Multivariate/complex_field.ml                          *)
(* (ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING).                                *)
(* ========================================================================= *)

needs "Library/fieldtheory.ml";;
needs "Library/galois.ml";;
needs "ANT/complex_embeddings.ml";;
needs "Multivariate/complex_ring.ml";;
needs "Multivariate/complex_field.ml";;

(* ------------------------------------------------------------------------- *)
(* Complex conjugation on a normal extension of Q with an embedding into C,  *)
(* its fixed field, and the case of Q-bar.                                   *)
(* ------------------------------------------------------------------------- *)

let GALOIS_GROUP_COMPLEX_CONJUGATION = prove
 (`!(k:A ring) e.
        normal_extension(subfield_generated k {ring_0 k},k) I /\
        ring_homomorphism(k,complex_ring) e
        ==> ?c. c IN group_carrier
                      (galois_group(subfield_generated k {ring_0 k},k) I) /\
                (!x. x IN ring_carrier k ==> e(c x) = cnj(e x)) /\
                group_mul (galois_group(subfield_generated k {ring_0 k},k) I)
                          c c =
                group_id(galois_group(subfield_generated k {ring_0 k},k) I) /\
                (c = group_id
                       (galois_group(subfield_generated k {ring_0 k},k) I) <=>
                 !x. x IN ring_carrier k ==> real(e x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `field(k:A ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORMAL_IMP_FIELD_EXTENSION; field_extension]; ALL_TAC] THEN
  REWRITE_TAC[GALOIS_GROUP; IN_ELIM_THM; I_THM] THEN
  SUBGOAL_THEN `ring_monomorphism(k,complex_ring) (e:A->complex)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `e:A->complex`]
      FIELD_HOMOMORPHISM_IMP_MONOMORPHISM) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN
    DISCH_THEN(MP_TAC o SPEC `ring_1 k:A`) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
    REWRITE_TAC[RING_1; COMPLEX_RING_CLAUSES; CX_INJ] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_homomorphism(k,complex_ring) (cnj o (e:A->complex))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `complex_ring` THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_CNJ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:A. y IN ring_carrier(subfield_generated k {ring_0 k})
          ==> cnj((e:A->complex) y) = e y`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `e:A->complex`;
                   `cnj o (e:A->complex)`]
      SUBFIELD_OF_HOMOMORPHIC_EQUALITIES) THEN
    ASM_REWRITE_TAC[FIELD_COMPLEX_RING] THEN
    DISCH_THEN(MP_TAC o MATCH_MP PRIME_SUBFIELD_MINIMAL) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; o_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (e:A->complex) (ring_carrier k) =
    IMAGE (cnj o e) (ring_carrier k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NORMAL_EXTENSION_IMAGES_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`I:A->A`; `subfield_generated k {ring_0 (k:A ring)}`; `complex_ring`] THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; FIELD_COMPLEX_RING; I_THM; o_THM];
    ALL_TAC] THEN
  ABBREV_TAC
   `c = \x:A. if x IN ring_carrier k
              then @y. y IN ring_carrier k /\ (e:A->complex) y = cnj(e x)
              else x` THEN
  SUBGOAL_THEN
   `!x:A. x IN ring_carrier k
          ==> c x IN ring_carrier k /\ (e:A->complex)(c x) = cnj(e x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "c" THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SELECT_CONV THEN
    UNDISCH_TAC
     `IMAGE (e:A->complex) (ring_carrier k) =
      IMAGE (cnj o e) (ring_carrier k)` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `cnj((e:A->complex) x)`) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. ~(x IN ring_carrier k) ==> c x = x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "c" THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. c(c x) = x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN ASM_CASES_TAC `(x:A) IN ring_carrier k` THENL
     [MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `e:A->complex`;
                     `(c:A->A)(c x)`; `x:A`]
        RING_MONOMORPHISM_INJECTIVE_EQ) THEN
      ASM_SIMP_TAC[CNJ_CNJ];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_homomorphism(k,k) (c:A->A)` ASSUME_TAC THENL
   [REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
    W(fun (asl,w) -> let l,r = dest_eq w in
      MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `e:A->complex`; l; r]
        RING_MONOMORPHISM_INJECTIVE_EQ)) THEN
    FIRST_ASSUM((fun th ->
      ASM_SIMP_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL;
                   MATCH_MP RING_HOMOMORPHISM_0 th;
                   MATCH_MP RING_HOMOMORPHISM_1 th;
                   MATCH_MP RING_HOMOMORPHISM_NEG th;
                   MATCH_MP RING_HOMOMORPHISM_ADD th;
                   MATCH_MP RING_HOMOMORPHISM_MUL th]) o
      check (fun th -> concl th = `ring_homomorphism(k,complex_ring)
                                    (e:A->complex)`)) THEN
    REWRITE_TAC[COMPLEX_RING_CLAUSES; CNJ_ADD; CNJ_MUL; CNJ_NEG; CNJ_CX];
    ALL_TAC] THEN
  EXISTS_TAC `c:A->A` THEN ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PERMUTES_INVOLUTION THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ring_automorphism; ring_isomorphism] THEN
    EXISTS_TAC `c:A->A` THEN ASM_SIMP_TAC[ring_isomorphisms];
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN ring_carrier k` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; RING_CARRIER_SUBFIELD_GENERATED_SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `e:A->complex`;
                   `(c:A->A) y`; `y:A`] RING_MONOMORPHISM_INJECTIVE_EQ) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FUN_EQ_THM; I_THM; REAL_CNJ] THEN EQ_TAC THENL
     [DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th ->
        is_forall(concl th) && is_eq(snd(dest_forall(concl th))) &&
        can (find_term ((=) `c:A->A`)) (concl th) &&
        not(is_imp(snd(dest_forall(concl th)))))) THEN
      DISCH_TAC THEN ASM_MESON_TAC[];
      DISCH_TAC THEN X_GEN_TAC `x:A` THEN
      ASM_CASES_TAC `(x:A) IN ring_carrier k` THEN ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `e:A->complex`;
                     `(c:A->A) x`; `x:A`] RING_MONOMORPHISM_INJECTIVE_EQ) THEN
      ASM_SIMP_TAC[]]]);;

let COMPLEX_CONJUGATION_REAL_SUBFIELD = prove
 (`!(k:A ring) e c.
        field k /\ ring_homomorphism(k,complex_ring) e /\
        c IN group_carrier(galois_group(subfield_generated k {ring_0 k},k) I) /\
        (!x. x IN ring_carrier k ==> e(c x) = cnj(e x)) /\ ~(c = I)
        ==> {x | x IN ring_carrier k /\ real(e x)} subfield_of k /\
            finite_extension
             (subfield_generated k {x | x IN ring_carrier k /\ real(e x)},k)
             I /\
            galois_extension
             (subfield_generated k {x | x IN ring_carrier k /\ real(e x)},k)
             I /\
            extension_degree
             (subfield_generated k {x | x IN ring_carrier k /\ real(e x)},k)
             I = 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_monomorphism(k,complex_ring) (e:A->complex)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `e:A->complex`]
      FIELD_HOMOMORPHISM_IMP_MONOMORPHISM) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN
    DISCH_THEN(MP_TAC o SPEC `ring_1 k:A`) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
    REWRITE_TAC[RING_1; COMPLEX_RING_CLAUSES; CX_INJ] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_PERMUTES) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_AUTOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
  SUBGOAL_THEN `!x:A. x IN ring_carrier k ==> c x IN ring_carrier k`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:A->A) o c = I` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN ring_carrier k` THENL
     [MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `e:A->complex`;
                     `(c:A->A)(c x)`; `x:A`]
        RING_MONOMORPHISM_INJECTIVE_EQ) THEN
      ASM_SIMP_TAC[CNJ_CNJ];
      ASM_MESON_TAC[permutes]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `fixed_field k {I,c:A->A} = {x | x IN ring_carrier k /\ real(e x)}`
  (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC[EXTENSION; IN_FIXED_FIELD; IN_ELIM_THM; FORALL_IN_INSERT;
                NOT_IN_EMPTY; I_THM; REAL_CNJ] THEN
    X_GEN_TAC `x:A` THEN ASM_CASES_TAC `(x:A) IN ring_carrier k` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `e:A->complex`;
                   `(c:A->A) x`; `x:A`] RING_MONOMORPHISM_INJECTIVE_EQ) THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `{I,c:A->A}`] ARTIN_FIXED_FIELD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT;
                    NOT_IN_EMPTY; RING_AUTOMORPHISM_I] THEN
    REWRITE_TAC[subgroup_of; SYMMETRIC_GROUP; SUBSET; FORALL_IN_INSERT;
                NOT_IN_EMPTY; IN_ELIM_THM; IN_INSERT] THEN
    ASM_REWRITE_TAC[PERMUTES_I; INVERSE_I; I_O_ID] THEN
    SUBGOAL_THEN `inverse(c:A->A) = c` SUBST1_TAC THENL
     [MATCH_MP_TAC INVERSE_UNIQUE_o THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (DISJ_CASES_THEN SUBST1_TAC)) THEN
    ASM_REWRITE_TAC[I_O_ID];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBFIELD_OF_FIXED_FIELD THEN
    ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; ring_endomorphism;
                    RING_HOMOMORPHISM_I];
    SUBGOAL_THEN `~(I:A->A = c)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                 NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let ALGEBRAIC_CLOSURE_COMPLEX_CONJUGATION = prove
 (`!k:A ring.
        algebraically_closed_field k /\ ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I
        ==> ?e c. ring_monomorphism(k,complex_ring) e /\
                  c IN group_carrier
                        (galois_group(subfield_generated k {ring_0 k},k) I) /\
                  group_element_order
                   (galois_group(subfield_generated k {ring_0 k},k) I) c = 2 /\
                  (!x. x IN ring_carrier k ==> e(c x) = cnj(e x)) /\
                  extension_degree
                   (subfield_generated k
                      {x | x IN ring_carrier k /\ real(e x)},k) I = 2`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPECL [`k:A ring`; `complex_ring`]
    PRIME_SUBFIELD_HOMOMORPHISM_EXISTS) THEN
  ASM_REWRITE_TAC[FIELD_COMPLEX_RING; RING_CHAR_COMPLEX_RING] THEN
  DISCH_THEN(X_CHOOSE_TAC `h0:A->complex`) THEN
  MP_TAC(ISPECL [`subfield_generated k {ring_0 (k:A ring)}`; `k:A ring`;
                 `complex_ring`; `I:A->A`; `h0:A->complex`]
    ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:A->complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ring_monomorphism(k,complex_ring) (e:A->complex)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `e:A->complex`]
      FIELD_HOMOMORPHISM_IMP_MONOMORPHISM) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN
    DISCH_THEN(MP_TAC o SPEC `ring_1 k:A`) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
    REWRITE_TAC[RING_1; COMPLEX_RING_CLAUSES; CX_INJ] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `e:A->complex`]
    GALOIS_GROUP_COMPLEX_CONJUGATION) THEN
  ASM_SIMP_TAC[ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:A->A` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "iff"))))) THEN
  SUBGOAL_THEN
   `~(c = group_id(galois_group(subfield_generated k {ring_0 k},k)
                               (I:A->A)))`
  ASSUME_TAC THENL
   [REMOVE_THEN "iff" SUBST1_TAC THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    MP_TAC(ISPECL [`k:A ring`; `ring_neg k (ring_1 k):A`; `2`]
      ALGEBRAICALLY_CLOSED_FIELD_NTH_ROOT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_NEG; RING_1; ARITH_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_TAC `r:real`) THEN
    UNDISCH_TAC `ring_pow k i 2 = ring_neg k (ring_1 (k:A ring))` THEN
    DISCH_THEN(MP_TAC o AP_TERM `e:A->complex`) THEN
    FIRST_ASSUM((fun th ->
      ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_POW th;
                   MATCH_MP RING_HOMOMORPHISM_NEG th;
                   MATCH_MP RING_HOMOMORPHISM_1 th; RING_1]) o
      check (fun th -> concl th = `ring_homomorphism(k,complex_ring)
                                    (e:A->complex)`)) THEN
    REWRITE_TAC[COMPLEX_RING_POW; COMPLEX_RING_CLAUSES] THEN
    REWRITE_TAC[GSYM CX_POW; GSYM CX_NEG; CX_INJ] THEN
    MP_TAC(SPEC `r:real` REAL_LE_SQUARE) THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    REMOVE_THEN "iff" (K ALL_TAC)] THEN
  MP_TAC(ISPECL [`k:A ring`; `e:A->complex`; `c:A->A`]
    COMPLEX_CONJUGATION_REAL_SUBFIELD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `~(c = group_id(galois_group(subfield_generated k {ring_0 k},k)
                                 (I:A->A)))` THEN
    REWRITE_TAC[GALOIS_GROUP];
    STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e:A->complex`; `c:A->A`] THEN
  ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_EQ_2; GROUP_POW_2]);;
