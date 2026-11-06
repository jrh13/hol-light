(* ========================================================================= *)
(* The codifferent and the different of an extension of number fields; the   *)
(* different of a number field.                                              *)
(*                                                                           *)
(* For fields k, l with a ring homomorphism h : k -> l, the rings of         *)
(* integers O_k = ring_of_integers k and O_l = ring_of_integers l and the    *)
(* trace Tr = algebra_trace (k,l) h:                                         *)
(*                                                                           *)
(*   number_field_codifferent (k,l) h = {x IN l | Tr(x O_l) SUBSET O_k}      *)
(*   number_field_different (k,l) h   = {x IN O_l | x C SUBSET O_l}, C the   *)
(*                                      codifferent                          *)
(*                                                                           *)
(* The different is always an ideal of O_l                                   *)
(* (RING_IDEAL_NUMBER_FIELD_DIFFERENT). For l a number field (k a field):    *)
(* O_l is contained in C (RING_OF_INTEGERS_SUBSET_CODIFFERENT) and           *)
(* C is an O_l-module (NUMBER_FIELD_CODIFFERENT_MUL, _ADD); l has bases over *)
(* k inside O_l (NUMBER_FIELD_FREE_BASIS_INTEGRAL), whose discriminants d    *)
(* lie in O_k and map C into O_l                                             *)
(* (NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT), so C is a fractional ideal *)
(* (NUMBER_FIELD_CODIFFERENT_FRACTIONAL); D (d C) = (d)                      *)
(* (NUMBER_FIELD_DIFFERENT_CODIFFERENT), D is nonzero                        *)
(* (NUMBER_FIELD_DIFFERENT_NONZERO), C = {x IN l | x D SUBSET O_l},          *)
(* so D and C are inverse (NUMBER_FIELD_CODIFFERENT_DIFFERENT), and          *)
(* x / a IN C iff x D SUBSET a O_l (NUMBER_FIELD_CODIFFERENT_DIV);           *)
(* C and D depend only on the image of k                                     *)
(* (NUMBER_FIELD_CODIFFERENT_EQ_IMAGE).                                      *)
(* The ramification of the different and the tower law are in                *)
(* ANT/different_extension.ml, the relative discriminant in                  *)
(* ANT/discriminant_extension.ml.                                            *)
(*                                                                           *)
(* The different of a number field k is the case of its prime subfield,      *)
(* (k,l) h = (subfield_generated k {ring_0 k},k) I; there C = {x IN k |      *)
(* Tr(x O) SUBSET O} with O = ring_of_integers k and Tr the trace over the   *)
(* prime subfield (NUMBER_FIELD_CODIFFERENT_PRIME_SUBFIELD), the dual of O   *)
(* under the trace form. With d = number_field_discriminant k:               *)
(*                                                                           *)
(* Main results: C contains O and is the Z-span of the dual basis of any     *)
(* integral basis (NUMBER_FIELD_CODIFFERENT_DUAL_BASIS); d C is an ideal of  *)
(* O, so C is a fractional ideal (NUMBER_FIELD_CODIFFERENT_IDEAL); the       *)
(* different D is an ideal of O containing d, D (d C) = (d) and C = {x IN k  *)
(* | x D SUBSET O}, i.e. D and C are inverse                                 *)
(* (NUMBER_FIELD_DIFFERENT_CODIFFERENT_Q,                                    *)
(* NUMBER_FIELD_CODIFFERENT_DIFFERENT); N(D) = |d|                           *)
(* (NUMBER_FIELD_IDEAL_NORM_DIFFERENT), so D = O iff |d| = 1; x / p IN C iff *)
(* p divides the traces of all x y, y IN O                                   *)
(* (NUMBER_FIELD_CODIFFERENT_DIV_NUM). The theorem of Dedekind, D SUBSET     *)
(* P^(e(P) - 1) and P contains D iff P is ramified, is in                    *)
(* ANT/different_extension.ml for every extension                            *)
(* (NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION,                              *)
(* NUMBER_FIELD_DIFFERENT_RAMIFIED; over Q by                                *)
(* RAMIFICATION_INDEX_PRIME_SUBFIELD).                                       *)
(*                                                                           *)
(* Routes. For a basis w of l over k inside O_l with discriminant d, d C     *)
(* lies in the O_k-span of w by Cramer (BASIS_DISCRIMINANT_TIMES_COORD of    *)
(* Library/ring_det.ml); D is the ideal quotient ((d) : d C), so D (d C) =   *)
(* (d) (DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT). Over the prime subfield, for an *)
(* integral basis w the trace matrix T = (Tr(w_i w_j)) has integer entries   *)
(* and determinant d; with the cofactor matrix M of T the elements g_j =     *)
(* sum_m M_jm w_m of O satisfy Tr(w_i g_j) = d delta_ij, and det M = d^(n-1) *)
(* (RING_DET_COFACTOR of Library/ring_det.ml). By the nondegeneracy of the   *)
(* trace form (NUMBER_FIELD_TRACE_FORM_INJECTIVE of ANT/numfield.ml), d C is *)
(* the Z-span of the g_j (NUMBER_FIELD_CODIFFERENT_DUAL_SPAN), an ideal of   *)
(* index |d|^(n-1) (FREE_BASIS_INTEGER_RING_SPAN_INDEX). D is the ideal      *)
(* quotient ((d) : d C), so D (d C) = (d) by                                 *)
(* DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT, and N(D) |d|^(n-1) = N((d)) = |d|^n.  *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/fieldtheory.ml, ANT/algmisc.ml,      *)
(* Library/ring_det.ml (cofactors, RING_DET_COFACTOR), ANT/ideal_arith.ml,   *)
(* ANT/dedekind.ml, ANT/ideal_norm.ml, ANT/numfield.ml (traces),             *)
(* ANT/ring_of_integers.ml, ANT/norm_index.ml                                *)
(* (NUMBER_FIELD_IDEAL_NORM_MUL_Q, NUMBER_FIELD_TRACE_INTEGRAL_BASIS),       *)
(* ANT/discriminant.ml, ANT/relative_split.ml (rings of integers under       *)
(* homomorphisms, RING_OF_INTEGERS_SUBFIELD_GENERATED) and                   *)
(* ANT/integrality.ml (NUMBER_FIELD_TRACE_INTEGRAL).                         *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "ANT/algmisc.ml";;
needs "Library/ring_det.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/ideal_norm.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/norm_index.ml";;
needs "ANT/discriminant.ml";;
needs "ANT/relative_split.ml";;
needs "ANT/integrality.ml";;

(* ------------------------------------------------------------------------- *)
(* The codifferent and the different.                                        *)
(* ------------------------------------------------------------------------- *)

let number_field_codifferent = new_definition
 `number_field_codifferent (k:A ring,l:B ring) (h:A->B) =
  {x | x IN ring_carrier l /\
       !y. y IN ring_carrier(ring_of_integers l)
           ==> algebra_trace (k,l) h (ring_mul l x y) IN
               ring_carrier(ring_of_integers k)}`;;

let number_field_different = new_definition
 `number_field_different (k:A ring,l:B ring) (h:A->B) =
  {x | x IN ring_carrier(ring_of_integers l) /\
       !y. y IN number_field_codifferent (k,l) h
           ==> ring_mul l x y IN ring_carrier(ring_of_integers l)}`;;

let RING_IDEAL_NUMBER_FIELD_DIFFERENT = prove
 (`!(k:A ring) (l:B ring) h.
        ring_ideal (ring_of_integers l) (number_field_different (k,l) h)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `l:B ring` (CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN
  REWRITE_TAC[subring_of; SUBSET] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y:B. y IN number_field_codifferent (k,l) (h:A->B)
          ==> y IN ring_carrier l`
  ASSUME_TAC THENL
   [SIMP_TAC[number_field_codifferent; IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[ring_ideal; number_field_different; RING_OF_INTEGERS;
              SUBSET; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL_LNEG; RING_ADD_RDISTRIB;
               GSYM RING_MUL_ASSOC]);;

(* For a number field over its prime subfield the traces lie in the prime    *)
(* subfield, whose integers are those of k in it: C = {x IN k | Tr(x O)      *)
(* SUBSET O}.                                                                *)
let NUMBER_FIELD_CODIFFERENT_PRIME_SUBFIELD = prove
 (`!k:A ring.
        number_field_codifferent (subfield_generated k {ring_0 k},k) I =
        {x | x IN ring_carrier k /\
             !y. y IN ring_carrier(ring_of_integers k)
                 ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                       (ring_mul k x y) IN
                     ring_carrier(ring_of_integers k)}`,
  REWRITE_TAC[number_field_codifferent; RING_OF_INTEGERS_SUBFIELD_GENERATED;
              IN_INTER; ALGEBRA_TRACE_NORM_IN_CARRIER]);;

(* ------------------------------------------------------------------------- *)
(* Extensions: O_l lies in the codifferent, the codifferent is a fractional  *)
(* ideal, the different is a nonzero ideal and the inverse of the            *)
(* codifferent.                                                              *)
(* ------------------------------------------------------------------------- *)

let RING_OF_INTEGERS_SUBSET_CODIFFERENT = prove
 (`!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> ring_carrier(ring_of_integers l) SUBSET
            number_field_codifferent (k,l) h`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET; number_field_codifferent; IN_ELIM_THM] THEN
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL THEN
  ASM_SIMP_TAC[REWRITE_RULE[RING_OF_INTEGERS]
   (ISPEC `ring_of_integers l:B ring` RING_MUL)]);;

(* The codifferent is a module over O_l.                                     *)
let NUMBER_FIELD_CODIFFERENT_MUL,NUMBER_FIELD_CODIFFERENT_ADD =
 (CONJ_PAIR o prove)
 (`(!k:A ring l:B ring h a x.
        a IN ring_carrier(ring_of_integers l) /\
        x IN number_field_codifferent (k,l) h
        ==> ring_mul l a x IN number_field_codifferent (k,l) h) /\
   (!k:A ring l:B ring h x y.
        ring_homomorphism(k,l) h /\
        x IN number_field_codifferent (k,l) h /\
        y IN number_field_codifferent (k,l) h
        ==> ring_add l x y IN number_field_codifferent (k,l) h)`,
  REWRITE_TAC[number_field_codifferent; IN_ELIM_THM] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RING_MUL; RING_ADD;
               REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET] THEN
  X_GEN_TAC `z:B` THEN DISCH_TAC THENL
   [SUBGOAL_THEN
     `ring_mul l (ring_mul l a x) z = ring_mul (l:B ring) x (ring_mul l a z)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_mul (r:B ring) (ring_mul r a x) y =
        ring_mul r x (ring_mul r a y)`) THEN
      ASM_SIMP_TAC[REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[IN_SUBRING_MUL; RING_OF_INTEGERS_SUBRING]];
    ASM_SIMP_TAC[RING_ADD_RDISTRIB; ALGEBRA_TRACE_ADD; RING_MUL;
                 IN_SUBRING_ADD; RING_OF_INTEGERS_SUBRING;
                 REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET]]);;

(* A free basis of l over k inside O_l (integer multiples of any basis).     *)
let NUMBER_FIELD_FREE_BASIS_INTEGRAL = prove
 (`!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> ?w. free_basis (k,l) h (extension_degree(k,l) h) w /\
                !i. i < extension_degree(k,l) h
                    ==> w i IN ring_carrier(ring_of_integers l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `g:num->B` o
    MATCH_MP FINITE_EXTENSION_FREE_BASIS) THEN
  ABBREV_TAC `n = extension_degree(k:A ring,l:B ring) h` THEN
  SUBGOAL_THEN
   `?d. !i. i < n
            ==> ~(d i = &0) /\
                ring_mul l (ring_of_int l (d i)) ((g:num->B) i) IN
                ring_carrier(ring_of_integers l)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_INTEGRAL_MULTIPLE THEN
    ASM_MESON_TAC[FREE_BASIS_IN_CARRIER];
    ALL_TAC] THEN
  EXISTS_TAC `\i. ring_mul l ((h:A->B)(ring_of_int k ((d:num->int) i)))
                             ((g:num->B) i)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FREE_BASIS_SCALE THEN ASM_REWRITE_TAC[RING_OF_INT] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field] o
      check (fun th -> concl th = `number_field(k:A ring)`)) THEN
    ASM_SIMP_TAC[RING_OF_INT_EQ_0_CHAR_0];
    ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_RING_OF_INT
     (ASSUME `ring_homomorphism(k:A ring,l:B ring) h`)]]);;

(* With a free basis w of l over k inside O_l and its discriminant d in O_k, *)
(* d C SUBSET O_l (Cramer: BASIS_DISCRIMINANT_TIMES_COORD).                  *)
let NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT = prove
 (`!k:A ring l:B ring h n w x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        free_basis (k,l) h n w /\
        (!i. i < n ==> w i IN ring_carrier(ring_of_integers l)) /\
        x IN number_field_codifferent (k,l) h
        ==> basis_discriminant (k,l) h n w IN
            ring_carrier(ring_of_integers k) /\
            ~(basis_discriminant (k,l) h n w = ring_0 k) /\
            ring_mul l (h(basis_discriminant (k,l) h n w)) x IN
            ring_carrier(ring_of_integers l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD o
    check (fun th -> concl th = `number_field(l:B ring)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier l /\
                !y. y IN ring_carrier(ring_of_integers l)
                    ==> algebra_trace (k,l) h (ring_mul l x y) IN
                        ring_carrier(ring_of_integers (k:A ring))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:B) IN number_field_codifferent (k,l) (h:A->B)` THEN
    REWRITE_TAC[number_field_codifferent; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPEC `l:B ring` (CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN
  MP_TAC(ISPEC `k:A ring` (CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `!i j. i < n /\ j < n
          ==> algebra_trace (k,l) h (ring_mul l ((w:num->B) i) (w j)) IN
              ring_carrier(ring_of_integers (k:A ring))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL THEN
    ASM_SIMP_TAC[REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_MUL)];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ q /\ (p ==> r) ==> p /\ q /\ r`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[basis_discriminant] THEN MATCH_MP_TAC RING_DET_SUBRING THEN
    ASM_SIMP_TAC[IN_ELIM_THM; FINITE_NUMSEG_LT];
    MATCH_MP_TAC BASIS_DISCRIMINANT_NONZERO THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field] o
      check (fun th -> concl th = `number_field(k:A ring)`)) THEN
    SIMP_TAC[RING_OF_NUM_EQ_0; DIVIDES_ZERO] THEN DISCH_THEN(K ALL_TAC) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `w:num->B`]
      FREE_BASIS_EXTENSION_DEGREE) THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      NUMBER_FIELD_TOWER_LAW) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[EXTENSION_DEGREE_EQ_0; FINITE_IMP_FIELD_EXTENSION];
    DISCH_TAC] THEN
  ABBREV_TAC `d = basis_discriminant (k:A ring,l:B ring) h n w` THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `w:num->B`;
                 `ring_carrier(ring_of_integers k:A ring)`; `x:B`]
    BASIS_DISCRIMINANT_TIMES_COORD) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ring_mul l ((w:num->B) j) x = ring_mul l x (w j)`
    SUBST1_TAC THENL [ASM_MESON_TAC[RING_MUL_SYM]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `w:num->B`; `x:B`]
    BASIS_COORDINATES_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  SUBGOAL_THEN `(d:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `{i:num | i < n}`; `d:A`;
                 `\i. basis_coordinates (k,l) (h:A->B) n w x i`; `w:num->B`]
    EXTENSION_LINCOMB_LMUL) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; BASIS_COORDINATES_IN_CARRIER] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC IN_SUBRING_SUM THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER)) THEN
  ASM_SIMP_TAC[]);;

(* The codifferent is a fractional ideal: d C SUBSET O_l for some nonzero d  *)
(* in O_k (the discriminant of a basis of l over k inside O_l).              *)
let NUMBER_FIELD_CODIFFERENT_FRACTIONAL = prove
 (`!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> ?d. d IN ring_carrier(ring_of_integers k) /\ ~(d = ring_0 k) /\
                IMAGE (ring_mul l (h d)) (number_field_codifferent (k,l) h)
                SUBSET ring_carrier(ring_of_integers l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_FREE_BASIS_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `basis_discriminant (k,l) (h:A->B) (extension_degree(k,l) h) w` THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`;
                 `extension_degree(k:A ring,l:B ring) h`; `w:num->B`]
    NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `ring_1 l:B`) THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      RING_OF_INTEGERS_SUBSET_CODIFFERENT) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[IN_SUBRING_1; RING_OF_INTEGERS_SUBRING];
    STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* With d C SUBSET O_l, d C is an ideal of O_l and D (d C) = (d): D is the   *)
(* ideal quotient ((d) : d C), which contains d C.                           *)
let NUMBER_FIELD_DIFFERENT_CODIFFERENT = prove
 (`!k:A ring l:B ring h d.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        d IN ring_carrier(ring_of_integers k) /\ ~(d = ring_0 k) /\
        IMAGE (ring_mul l (h d)) (number_field_codifferent (k,l) h) SUBSET
        ring_carrier(ring_of_integers l)
        ==> ring_ideal (ring_of_integers l)
              (IMAGE (ring_mul l (h d)) (number_field_codifferent (k,l) h)) /\
            ideal_prod (ring_of_integers l) (number_field_different (k,l) h)
              (IMAGE (ring_mul l (h d)) (number_field_codifferent (k,l) h)) =
            ideal_generated (ring_of_integers l) {h d}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD o
    check (fun th -> concl th = `number_field(l:B ring)`)) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION o CONJUNCT1) THEN
  REWRITE_TAC[field_extension] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ABBREV_TAC `e = (h:A->B) d` THEN
  SUBGOAL_THEN
   `e IN ring_carrier(ring_of_integers l) /\ e IN ring_carrier l /\
    ~(e = ring_0 (l:B ring))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER)) THEN
    DISCH_THEN(MP_TAC o SPEC `d:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0; RING_OF_INTEGERS_SUBSET; SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC
   `J = IMAGE (ring_mul l e) (number_field_codifferent (k,l) (h:A->B))` THEN
  SUBGOAL_THEN
   `!x:B. x IN number_field_codifferent (k,l) (h:A->B) ==> x IN ring_carrier l`
  ASSUME_TAC THENL
   [SIMP_TAC[number_field_codifferent; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_ideal (ring_of_integers l) (J:B->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ring_ideal; RING_OF_INTEGERS] THEN
    EXPAND_TAC "J" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_IMAGE] THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `ring_0 l:B` THEN
      ASM_SIMP_TAC[RING_MUL_RZERO] THEN
      MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
        RING_OF_INTEGERS_SUBSET_CODIFFERENT) THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      SIMP_TAC[IN_SUBRING_0; RING_OF_INTEGERS_SUBRING];
      X_GEN_TAC `x:B` THEN DISCH_TAC THEN
      EXISTS_TAC `ring_mul l (ring_neg l (ring_1 l)) x:B` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(RING_RULE
         `ring_neg (r:B ring) (ring_mul r d x) =
          ring_mul r d (ring_mul r (ring_neg r (ring_1 r)) x)`) THEN
        ASM_SIMP_TAC[];
        MATCH_MP_TAC NUMBER_FIELD_CODIFFERENT_MUL THEN
        ASM_SIMP_TAC[IN_SUBRING_NEG; IN_SUBRING_1; RING_OF_INTEGERS_SUBRING]];
      MAP_EVERY X_GEN_TAC [`u:B`; `v:B`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `x:B` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))
       (X_CHOOSE_THEN `y:B` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
      EXISTS_TAC `ring_add l x y:B` THEN
      ASM_SIMP_TAC[NUMBER_FIELD_CODIFFERENT_ADD; RING_ADD_LDISTRIB];
      MAP_EVERY X_GEN_TAC [`a:B`; `y:B`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `x:B` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
      EXISTS_TAC `ring_mul l a x:B` THEN
      ASM_SIMP_TAC[NUMBER_FIELD_CODIFFERENT_MUL] THEN
      MATCH_MP_TAC(RING_RULE
       `ring_mul (r:B ring) a (ring_mul r d x) =
        ring_mul r d (ring_mul r a x)`) THEN
      ASM_SIMP_TAC[REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET]];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `number_field_different (k,l) (h:A->B) =
    ideal_quotient (ring_of_integers l)
      (ideal_generated (ring_of_integers l) {e}) (J:B->bool)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:B` THEN
    REWRITE_TAC[number_field_different; ideal_quotient; IN_ELIM_THM] THEN
    EXPAND_TAC "J" THEN REWRITE_TAC[FORALL_IN_IMAGE; RING_OF_INTEGERS] THEN
    ASM_CASES_TAC `(x:B) IN ring_carrier(ring_of_integers l)` THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ABS_TAC THEN
    MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)`) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:B) IN ring_carrier l /\ y IN ring_carrier l`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING; RING_MUL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`l:B ring`; `e:B`] RING_MUL_LINV) THEN
    ASM_SIMP_TAC[FIELD_UNIT] THEN
    MATCH_MP_TAC(RING_RULE
     `ring_mul (r:B ring) f e = ring_1 r
      ==> ring_mul r x y = ring_mul r f (ring_mul r x (ring_mul r e y))`) THEN
    ASM_SIMP_TAC[RING_INV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`;
                 `ideal_generated (ring_of_integers l) {e:B}`; `J:B->bool`]
    DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_IDEAL_IDEAL_GENERATED] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN
    ASM_REWRITE_TAC[SING_SUBSET] THEN EXPAND_TAC "J" THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `ring_1 l:B` THEN
    ASM_SIMP_TAC[RING_MUL_RID] THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      RING_OF_INTEGERS_SUBSET_CODIFFERENT) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[IN_SUBRING_1; RING_OF_INTEGERS_SUBRING];
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th])] THEN
  MATCH_MP_TAC IDEAL_PROD_COMM THEN ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET] THEN
  REWRITE_TAC[ideal_quotient] THEN SET_TAC[]);;

let NUMBER_FIELD_DIFFERENT_NONZERO = prove
 (`!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> ~(number_field_different (k,l) h = {ring_0 l})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_CODIFFERENT_FRACTIONAL) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `d:A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION o CONJUNCT1) THEN
  REWRITE_TAC[field_extension] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h:A->B) d IN number_field_different (k,l) h` MP_TAC THENL
   [REWRITE_TAC[number_field_different; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
        RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
      ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER)) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC
       `IMAGE (ring_mul l ((h:A->B) d)) (number_field_codifferent (k,l) h)
        SUBSET ring_carrier(ring_of_integers l)` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE]];
    ASM_REWRITE_TAC[IN_SING] THEN
    ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0; RING_OF_INTEGERS_SUBSET; SUBSET]]);;

(* If x D SUBSET O_l then x d lies in x D (d C) SUBSET d C, so x is in C.    *)
let NUMBER_FIELD_CODIFFERENT_DIFFERENT = prove
 (`!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> number_field_codifferent (k,l) h =
            {x | x IN ring_carrier l /\
                 !y. y IN number_field_different (k,l) h
                     ==> ring_mul l x y IN ring_carrier(ring_of_integers l)}`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:B` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(x:B) IN ring_carrier l` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:B) IN number_field_codifferent (k,l) (h:A->B)` THEN
      SIMP_TAC[number_field_codifferent; IN_ELIM_THM];
      ASM_REWRITE_TAC[number_field_different; IN_ELIM_THM]] THEN
    X_GEN_TAC `y:B` THEN STRIP_TAC THEN
    SUBGOAL_THEN `ring_mul l x y = ring_mul l y (x:B)` SUBST1_TAC THENL
     [MATCH_MP_TAC RING_MUL_SYM THEN
      ASM_SIMP_TAC[REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET];
      ASM_SIMP_TAC[]];
    STRIP_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD o
    check (fun th -> concl th = `number_field(l:B ring)`)) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_CODIFFERENT_FRACTIONAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `d:A`]
    NUMBER_FIELD_DIFFERENT_CODIFFERENT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION o CONJUNCT1) THEN
  REWRITE_TAC[field_extension] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(h:A->B) d IN ring_carrier(ring_of_integers l) /\ h d IN ring_carrier l /\
    ~(h d = ring_0 l)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
    ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
    DISCH_THEN(MP_TAC o SPEC `d:A` o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0; RING_OF_INTEGERS_SUBSET; SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC `e = (h:A->B) d` THEN
  ABBREV_TAC
   `J = IMAGE (ring_mul l e) (number_field_codifferent (k,l) (h:A->B))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ring_mul l x e IN (J:B->bool)` MP_TAC THENL
   [SUBGOAL_THEN
     `ring_ideal (ring_of_integers l)
        {z | z IN ring_carrier(ring_of_integers l) /\
             ring_mul l x z IN (J:B->bool)}`
    MP_TAC THENL
     [UNDISCH_TAC `ring_ideal (ring_of_integers l) (J:B->bool)` THEN
      REWRITE_TAC[ring_ideal; RING_OF_INTEGERS; SUBSET; IN_ELIM_THM] THEN
      STRIP_TAC THEN
      ASM_SIMP_TAC[IN_SUBRING_0; IN_SUBRING_NEG; IN_SUBRING_ADD;
                   IN_SUBRING_MUL; RING_OF_INTEGERS_SUBRING;
                   REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET;
                   RING_MUL_RZERO; RING_MUL_RNEG; RING_ADD_LDISTRIB] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `ring_mul l x (ring_mul l x' y) =
                    ring_mul l x' (ring_mul (l:B ring) x y)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(RING_RULE
         `ring_mul (r:B ring) x (ring_mul r a z) =
          ring_mul r a (ring_mul r x z)`) THEN
        ASM_SIMP_TAC[REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET];
        ASM_SIMP_TAC[]];
      DISCH_THEN(MP_TAC o SPECL [`number_field_different (k,l) (h:A->B)`;
                                 `J:B->bool`] o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] IDEAL_PROD_MINIMAL))] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; RING_OF_INTEGERS] THEN
      MAP_EVERY X_GEN_TAC [`a:B`; `b:B`] THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN
       `(a:B) IN ring_carrier(ring_of_integers l) /\
        (b:B) IN ring_carrier(ring_of_integers l)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `(a:B) IN number_field_different (k,l) (h:A->B)` THEN
          SIMP_TAC[number_field_different; IN_ELIM_THM];
          UNDISCH_TAC `(b:B) IN J` THEN
          UNDISCH_TAC `ring_ideal (ring_of_integers l) (J:B->bool)` THEN
          SIMP_TAC[ring_ideal; SUBSET]];
        ASM_SIMP_TAC[IN_SUBRING_MUL; RING_OF_INTEGERS_SUBRING]] THEN
      SUBGOAL_THEN `ring_mul l x (ring_mul l a b) =
                    ring_mul l (ring_mul l x a) (b:B)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC RING_MUL_ASSOC THEN
        ASM_SIMP_TAC[REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET];
        MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`;
                       `ring_mul l x a:B`; `b:B`] IN_RING_IDEAL_LMUL) THEN
        ASM_SIMP_TAC[RING_OF_INTEGERS]];
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `e:B`) THEN
      ASM_SIMP_TAC[IN_IDEAL_GENERATED_SELF]];
    EXPAND_TAC "J" THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:B` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(c:B) IN ring_carrier l` ASSUME_TAC THENL
     [UNDISCH_TAC `(c:B) IN number_field_codifferent (k,l) (h:A->B)` THEN
      SIMP_TAC[number_field_codifferent; IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `x:B = c` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`l:B ring`; `e:B`] THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
    SUBGOAL_THEN `ring_mul l e x = ring_mul l x (e:B)` SUBST1_TAC THENL
     [MATCH_MP_TAC RING_MUL_SYM THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]]);;

(* x / a is in C iff x D SUBSET a O_l, for a nonzero a in O_l (C = (O_l :    *)
(* D)).                                                                      *)
let NUMBER_FIELD_CODIFFERENT_DIV = prove
 (`!k:A ring l:B ring h a x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        a IN ring_carrier(ring_of_integers l) /\ ~(a = ring_0 l) /\
        x IN ring_carrier l
        ==> (ring_mul l (ring_inv l a) x IN number_field_codifferent (k,l) h <=>
             !d. d IN number_field_different (k,l) h
                 ==> ring_mul l x d IN
                     ideal_generated (ring_of_integers l) {a})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD o
    check (fun th -> concl th = `number_field(l:B ring)`)) THEN
  SUBGOAL_THEN `(a:B) IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!d. d IN number_field_different (k,l) (h:A->B)
        ==> d IN ring_carrier(l:B ring)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      RING_IDEAL_NUMBER_FIELD_DIFFERENT) THEN
    DISCH_THEN(MP_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
    MP_TAC(ISPEC `l:B ring` RING_OF_INTEGERS_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[NUMBER_FIELD_CODIFFERENT_DIFFERENT; IN_ELIM_THM;
               RING_MUL; RING_INV; FIELD_UNIT] THEN
  ASM_SIMP_TAC[RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING; RING_MUL;
               RING_MUL_ASSOC; RING_INV; FIELD_UNIT]);;

(* The codifferent and the different depend only on the image of the base.   *)
let NUMBER_FIELD_CODIFFERENT_EQ_IMAGE = prove
 (`!k1:A ring k2:C ring l:B ring h1 h2.
        field k1 /\ field k2 /\ number_field l /\
        ring_homomorphism(k1,l) h1 /\ ring_homomorphism(k2,l) h2 /\
        IMAGE h1 (ring_carrier k1) = IMAGE h2 (ring_carrier k2)
        ==> number_field_codifferent (k1,l) h1 =
            number_field_codifferent (k2,l) h2 /\
            number_field_different (k1,l) h1 =
            number_field_different (k2,l) h2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[number_field_different]] THEN
  SUBGOAL_THEN
   `ring_monomorphism(k1:A ring,l:B ring) h1 /\
    ring_monomorphism(k2:C ring,l:B ring) h2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FIELD_EXTENSION_IMP_MONOMORPHISM THEN
    MATCH_MP_TAC FINITE_IMP_FIELD_EXTENSION THEN
    ASM_MESON_TAC[NUMBER_FIELD_TOWER_LAW];
    ALL_TAC] THEN
  REWRITE_TAC[number_field_codifferent; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:B` THEN
  ASM_CASES_TAC `(x:B) IN ring_carrier l` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)`) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `ring_mul l x y IN ring_carrier(l:B ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_MUL; RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k1:A ring`; `l:B ring`; `h1:A->B`;
                 `algebra_trace (k1,l) (h1:A->B) (ring_mul l x y)`]
    RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE) THEN
  MP_TAC(ISPECL [`k2:C ring`; `l:B ring`; `h2:C->B`;
                 `algebra_trace (k2,l) (h2:C->B) (ring_mul l x y)`]
    RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE) THEN
  ASM_REWRITE_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  MP_TAC(ISPECL [`h1:A->B`; `h2:C->B`; `k1:A ring`; `k2:C ring`; `l:B ring`;
                 `ring_mul l x y:B`] ALGEBRA_TRACE_NORM_EQ_IMAGE) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A number field over its prime subfield: the codifferent is the Z-span of  *)
(* the dual basis of an integral basis, d C is an ideal.                     *)
(* ------------------------------------------------------------------------- *)

(* Membership in the codifferent can be tested on an integral basis.         *)
let NUMBER_FIELD_CODIFFERENT_INTEGRAL_BASIS = prove
 (`!k:A ring n w x.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w
        ==> (x IN
             number_field_codifferent (subfield_generated k {ring_0 k},k) I <=>
             x IN ring_carrier k /\
             !i. i < n
                 ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                       (ring_mul k x (w i)) IN
                     ring_carrier(ring_of_integers k))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  REWRITE_TAC[NUMBER_FIELD_CODIFFERENT_PRIME_SUBFIELD; IN_ELIM_THM] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `ring_of_integers k:A ring` RING_MUL) THEN
  REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `y:A` o CONJUNCT1 o CONJUNCT2 o
    GEN_REWRITE_RULE I [free_basis]) THEN
  ASM_REWRITE_TAC[INTEGER_RING; IN_UNIV; RING_OF_INTEGERS] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->int` SUBST1_TAC) THEN
  SUBGOAL_THEN `!i. i < n ==> (w:num->A) i IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_SUM_RING_OF_INTEGERS; IN_ELIM_THM;
               RING_OF_INT_IN_RING_OF_INTEGERS] THEN
  ASM_SIMP_TAC[NUMBER_FIELD_TRACE_MUL_LINCOMB; FINITE_NUMSEG_LT; IN_ELIM_THM;
               RING_OF_INT_IN_SUBFIELD_GENERATED] THEN
  W(MP_TAC o PART_MATCH (rand o rand)
    (ISPEC `k:A ring` RING_SUM_RING_OF_INTEGERS) o lhand o snd) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; RING_OF_INT_IN_RING_OF_INTEGERS] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[RING_SUM]);;

(* If Tr(w_i g_j) = a delta_ij for an integral basis w and a nonzero         *)
(* rational a, then a C is the Z-span of the g_j: for x in C, a x = sum_i    *)
(* Tr(x w_i) g_i, both sides having the same traces against the w_m.         *)
let NUMBER_FIELD_CODIFFERENT_DUAL_SPAN = prove
 (`!k:A ring n w g a.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
        a IN ring_carrier(subfield_generated k {ring_0 k}) /\
        ~(a = ring_0 k) /\
        (!j. j < n ==> g j IN ring_carrier k) /\
        (!i j. i < n /\ j < n
               ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                     (ring_mul k (w i) (g j)) =
                   if i = j then a else ring_0 k)
        ==> IMAGE (ring_mul k a)
             (number_field_codifferent (subfield_generated k {ring_0 k},k) I) =
            {ring_sum k {i | i < n}
                      (\i. ring_mul k (ring_of_int k (c i)) (g i)) |
             c IN (:num->int)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
    RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  SUBGOAL_THEN
   `(a:A) IN ring_carrier k /\
    ring_inv k a IN ring_carrier(subfield_generated k {ring_0 k}) /\
    ring_inv k a IN ring_carrier k /\ ring_mul k (ring_inv k a) a = ring_1 k`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_INV_IN_SUBFIELD_GENERATED; FIELD_SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
      ASM_SIMP_TAC[RING_INV] THEN DISCH_TAC THEN
      MATCH_MP_TAC RING_MUL_LINV THEN ASM_SIMP_TAC[FIELD_UNIT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c m. m < n
          ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                (ring_mul k (w m)
                  (ring_sum k {i | i < n}
                     (\i. ring_mul k (ring_of_int k (c i)) ((g:num->A) i)))) =
              ring_mul k (ring_of_int k (c m)) a`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[NUMBER_FIELD_TRACE_MUL_LINCOMB; FINITE_NUMSEG_LT; IN_ELIM_THM;
                 RING_OF_INT_IN_SUBFIELD_GENERATED] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum (k:A ring) {i | i < n}
        (\i. if i = m then ring_mul k (ring_of_int k ((c:num->int) m)) a
             else ring_0 k)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      ASM_CASES_TAC `i:num = m` THEN
      ASM_SIMP_TAC[RING_MUL_RZERO; RING_OF_INT];
      REWRITE_TAC[RING_SUM_DELTA; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[RING_MUL; RING_OF_INT]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:A` THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[NUMBER_FIELD_CODIFFERENT_INTEGRAL_BASIS] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?c. !i:num. i < n ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                          (ring_mul k x (w i)) =
                        ring_of_int (k:A ring) (c i)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
      ASM_MESON_TAC[NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS; RING_MUL;
                    RING_OF_INTEGERS_SUBSET; SUBSET];
      EXISTS_TAC `c:num->int`] THEN
    MATCH_MP_TAC NUMBER_FIELD_TRACE_FORM_INJECTIVE THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `n:num`; `w:num->A`] THEN
    ASM_SIMP_TAC[RING_SUM; RING_MUL; RING_OF_INT] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:num->A) m IN ring_carrier k` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_mul k (w m) (ring_mul k a x) =
      ring_mul k a (ring_mul k x ((w:num->A) m))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_mul (r:A ring) a (ring_mul r b c) =
        ring_mul r b (ring_mul r c a)`) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[NUMBER_FIELD_TRACE_SCALAR_MUL; RING_MUL] THEN
      MATCH_MP_TAC RING_MUL_SYM THEN ASM_REWRITE_TAC[RING_OF_INT]];
    DISCH_THEN(X_CHOOSE_THEN `c:num->int` SUBST1_TAC) THEN
    ABBREV_TAC `y = ring_sum k {i | i < n}
                 (\i. ring_mul k (ring_of_int k (c i)) ((g:num->A) i))` THEN
    SUBGOAL_THEN `(y:A) IN ring_carrier k` ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN REWRITE_TAC[RING_SUM]; ALL_TAC] THEN
    EXISTS_TAC `ring_mul k (ring_inv k a) y:A` THEN
    ASM_SIMP_TAC[NUMBER_FIELD_CODIFFERENT_INTEGRAL_BASIS; RING_MUL] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `ring_mul k (ring_inv k a) a = ring_1 (k:A ring)` THEN
      MATCH_MP_TAC(RING_RULE
       `ring_mul (r:A ring) b a = ring_1 r
        ==> c = ring_mul r a (ring_mul r b c)`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:num->A) m IN ring_carrier k` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_mul k (ring_mul k (ring_inv k a) y) (w m) =
      ring_mul k (ring_inv k a) (ring_mul k ((w:num->A) m) y)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_mul (r:A ring) (ring_mul r a b) c =
        ring_mul r a (ring_mul r c b)`) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[NUMBER_FIELD_TRACE_SCALAR_MUL; RING_MUL]] THEN
    EXPAND_TAC "y" THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN
     `ring_mul k (ring_inv k a) (ring_mul k (ring_of_int k (c m)) a) =
      ring_of_int (k:A ring) ((c:num->int) m)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `ring_mul k (ring_inv k a) a = ring_1 (k:A ring)` THEN
      MATCH_MP_TAC(RING_RULE
       `ring_mul (r:A ring) b a = ring_1 r
        ==> ring_mul r b (ring_mul r c a) = c`) THEN
      ASM_REWRITE_TAC[RING_OF_INT];
      REWRITE_TAC[RING_OF_INT_IN_RING_OF_INTEGERS]]]);;

(* The cofactor matrix M of the trace matrix T = (Tr(w_i w_j)) of an         *)
(* integral basis w, with det T = d: the elements g_j = sum_m M_jm w_m       *)
(* satisfy Tr(w_i g_j) = d delta_ij, and det M = d^(n - 1).                  *)
let NUMBER_FIELD_CODIFFERENT_ADJUGATE = prove
 (`!k:A ring n w.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w
        ==> ?M. ring_det integer_ring {i | i < n} M =
                number_field_discriminant k pow (n - 1) /\
                !i j. i < n /\ j < n
                      ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                            (ring_mul k (w i)
                               (ring_sum k {m | m < n}
                                  (\m. ring_mul k (ring_of_int k (M j m))
                                                  (w m)))) =
                          if i = j
                          then ring_of_int k (number_field_discriminant k)
                          else ring_0 k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  SUBGOAL_THEN `!i. i < n ==> (w:num->A) i IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_DISCRIMINANT_NONZERO) THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
    NUMBER_FIELD_DISCRIMINANT_BASIS) THEN
  ASM_REWRITE_TAC[basis_discriminant; RING_OF_INTEGERS] THEN
  DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `t = \i j. algebra_trace (integer_ring,ring_of_integers k)
                          (ring_of_int k)
                          (ring_mul k ((w:num->A) i) (w j))` THEN
  DISCH_TAC THEN
  EXISTS_TAC `ring_cofactor integer_ring {i:num | i < n} t` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`integer_ring`; `{i:num | i < n}`; `t:num->num->int`]
      RING_DET_COFACTOR) THEN
    ASM_REWRITE_TAC[INTEGRAL_DOMAIN_INTEGER_RING; FINITE_NUMSEG_LT;
                    INTEGER_RING; IN_UNIV; CARD_NUMSEG_LT; INTEGER_RING_POW];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NUMBER_FIELD_TRACE_MUL_LINCOMB; FINITE_NUMSEG_LT; IN_ELIM_THM;
               RING_OF_INT_IN_SUBFIELD_GENERATED] THEN
  TRANS_TAC EQ_TRANS
   `ring_of_int k (ring_sum integer_ring {m | m < n}
      (\m:num. ring_mul integer_ring (t i m)
             (ring_cofactor integer_ring {i | i < n} t j m))):A` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INTEGER_RING_SUM; INTEGER_RING] THEN
    SIMP_TAC[RING_OF_INT_ISUM; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    EXPAND_TAC "t" THEN
    MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
      NUMBER_FIELD_TRACE_INTEGRAL_BASIS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[IN_SUBRING_MUL; RING_OF_INTEGERS_SUBRING;
                 GSYM RING_OF_INT_MUL] THEN
    REWRITE_TAC[INT_MUL_SYM];
    MP_TAC(ISPECL [`integer_ring`; `{i:num | i < n}`; `t:num->num->int`;
                   `i:num`; `j:num`] RING_DET_ADJUGATE_ROWS) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; INTEGER_RING; IN_UNIV] THEN
    DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[RING_OF_INT_0]]);;

let NUMBER_FIELD_CODIFFERENT_DUAL_BASIS = prove
 (`!k:A ring n w.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w
        ==> ?w'. (!i j. i < n /\ j < n
                        ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                              (ring_mul k (w i) (w' j)) =
                            if i = j then ring_1 k else ring_0 k) /\
                 number_field_codifferent
                   (subfield_generated k {ring_0 k},k) I =
                 {ring_sum k {i | i < n}
                           (\i. ring_mul k (ring_of_int k (c i)) (w' i)) |
                  c IN (:num->int)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN
   `!i. i < n ==> (w:num->A) i IN ring_carrier k`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[FREE_BASIS_IN_CARRIER; RING_OF_INTEGERS_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
    NUMBER_FIELD_CODIFFERENT_ADJUGATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num->num->int` (ASSUME_TAC o CONJUNCT2)) THEN
  ABBREV_TAC `d = ring_of_int k (number_field_discriminant k):A` THEN
  ABBREV_TAC `g = \j. ring_sum k {m | m < n}
     (\m. ring_mul k (ring_of_int k ((M:num->num->int) j m))
                     ((w:num->A) m))` THEN
  SUBGOAL_THEN
   `(d:A) IN ring_carrier(subfield_generated k {ring_0 k}) /\
    ~(d = ring_0 k) /\ (!j. (g:num->A) j IN ring_carrier k)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["d"; "g"] THEN
    REWRITE_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED; RING_SUM] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
    ASM_SIMP_TAC[RING_OF_INT_EQ_0_CHAR_0; NUMBER_FIELD_DISCRIMINANT_NONZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_inv k d IN ring_carrier(subfield_generated k {ring_0 k}) /\
    ring_inv k d IN ring_carrier k /\
    ring_mul k (ring_inv k d) d = ring_1 (k:A ring)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_INV_IN_SUBFIELD_GENERATED; FIELD_SUBFIELD_GENERATED] THEN
    SUBGOAL_THEN `(d:A) IN ring_carrier k` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
      ASM_SIMP_TAC[RING_INV; RING_MUL_LINV; FIELD_UNIT]];
    ALL_TAC] THEN
  EXISTS_TAC `\j. ring_mul k (ring_inv k d) ((g:num->A) j)` THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `ring_mul k (w i) (ring_mul k (ring_inv k d) ((g:num->A) j)) =
      ring_mul k (ring_inv k d) (ring_mul k ((w:num->A) i) (g j))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_mul (r:A ring) a (ring_mul r b c) =
        ring_mul r b (ring_mul r a c)`) THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[NUMBER_FIELD_TRACE_SCALAR_MUL; RING_MUL] THEN
      EXPAND_TAC "g" THEN ASM_SIMP_TAC[] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[RING_MUL_RZERO]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`;
                 `\j. ring_mul k (ring_inv k d) ((g:num->A) j)`; `ring_1 k:A`]
    NUMBER_FIELD_CODIFFERENT_DUAL_SPAN) THEN
  ASM_SIMP_TAC[RING_MUL; RING_1; FIELD_NONTRIVIAL] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPEC `subfield_generated k {ring_0 k}:A ring` RING_1) THEN
    REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 SUBFIELD_GENERATED))];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = x) ==> s = IMAGE (f:A->A) s`) THEN
  SIMP_TAC[NUMBER_FIELD_CODIFFERENT_PRIME_SUBFIELD; IN_ELIM_THM;
           RING_MUL_LID]);;

(* d C is the Z-span of the g_j above, which lie in O, and C is an O-module. *)
let NUMBER_FIELD_CODIFFERENT_IDEAL = prove
 (`!k:A ring.
        number_field k
        ==> ring_ideal (ring_of_integers k)
              (IMAGE (ring_mul k (ring_of_int k (number_field_discriminant k)))
                     (number_field_codifferent
                        (subfield_generated k {ring_0 k},k) I))`,
  let lmul,ladd = (CONJ_PAIR o prove)
   (`(!k:A ring a x.
        a IN ring_carrier(ring_of_integers k) /\
        x IN number_field_codifferent (subfield_generated k {ring_0 k},k) I
        ==> ring_mul k a x IN
            number_field_codifferent (subfield_generated k {ring_0 k},k) I) /\
     (!k:A ring x y.
        number_field k /\
        x IN number_field_codifferent (subfield_generated k {ring_0 k},k) I /\
        y IN number_field_codifferent (subfield_generated k {ring_0 k},k) I
        ==> ring_add k x y IN
            number_field_codifferent (subfield_generated k {ring_0 k},k) I)`,
    SIMP_TAC[NUMBER_FIELD_CODIFFERENT_MUL; NUMBER_FIELD_CODIFFERENT_ADD;
             RING_HOMOMORPHISM_SUBFIELD_INCLUSION]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `w:num->A` o MATCH_MP RING_OF_INTEGERS_FREE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  ABBREV_TAC
   `n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I` THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
    NUMBER_FIELD_CODIFFERENT_ADJUGATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num->num->int` (ASSUME_TAC o CONJUNCT2)) THEN
  ABBREV_TAC `d = ring_of_int k (number_field_discriminant k):A` THEN
  ABBREV_TAC `g = \j. ring_sum k {m | m < n}
     (\m. ring_mul k (ring_of_int k ((M:num->num->int) j m))
                     ((w:num->A) m))` THEN
  SUBGOAL_THEN
   `(d:A) IN ring_carrier(ring_of_integers k) /\
    d IN ring_carrier(subfield_generated k {ring_0 k}) /\ ~(d = ring_0 k) /\
    !j. (g:num->A) j IN ring_carrier(ring_of_integers k)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["d"; "g"] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
    ASM_SIMP_TAC[RING_OF_INT_IN_RING_OF_INTEGERS;
                 RING_OF_INT_IN_SUBFIELD_GENERATED; RING_OF_INT_EQ_0_CHAR_0;
                 NUMBER_FIELD_DISCRIMINANT_NONZERO] THEN
    DISCH_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC IN_SUBRING_SUM THEN
    REWRITE_TAC[RING_OF_INTEGERS_SUBRING; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS_SUBRING; RING_OF_INT_IN_RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN number_field_codifferent (subfield_generated k {ring_0 k},k) I
        ==> x IN ring_carrier (k:A ring)`
  ASSUME_TAC THENL
   [SIMP_TAC[NUMBER_FIELD_CODIFFERENT_PRIME_SUBFIELD; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[ring_ideal; RING_OF_INTEGERS] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_IMAGE] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`; `g:num->A`; `d:A`]
      NUMBER_FIELD_CODIFFERENT_DUAL_SPAN) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET] THEN
      EXPAND_TAC "g" THEN ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN GEN_TAC THEN
    MATCH_MP_TAC IN_SUBRING_SUM THEN
    REWRITE_TAC[RING_OF_INTEGERS_SUBRING; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING; RING_OF_INT_IN_RING_OF_INTEGERS];
    EXISTS_TAC `ring_0 k:A` THEN
    ASM_SIMP_TAC[RING_MUL_RZERO; REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET;
                 REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET_CODIFFERENT;
                 FIELD_SUBFIELD_GENERATED; NUMBER_FIELD_IMP_FIELD;
                 RING_HOMOMORPHISM_SUBFIELD_INCLUSION;
                 IN_SUBRING_0; RING_OF_INTEGERS_SUBRING];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    EXISTS_TAC `ring_mul k (ring_neg k (ring_1 k)) x:A` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_neg (r:A ring) (ring_mul r d x) =
        ring_mul r d (ring_mul r (ring_neg r (ring_1 r)) x)`) THEN
      ASM_SIMP_TAC[REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET];
      MATCH_MP_TAC lmul THEN
      ASM_SIMP_TAC[IN_SUBRING_NEG; IN_SUBRING_1; RING_OF_INTEGERS_SUBRING]];
    MAP_EVERY X_GEN_TAC [`u:A`; `v:A`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))
     (X_CHOOSE_THEN `y:A` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
    EXISTS_TAC `ring_add k x y:A` THEN
    ASM_SIMP_TAC[ladd; RING_ADD_LDISTRIB;
                 REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET];
    MAP_EVERY X_GEN_TAC [`a:A`; `y:A`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
    EXISTS_TAC `ring_mul k a x:A` THEN ASM_SIMP_TAC[lmul] THEN
    MATCH_MP_TAC(RING_RULE
     `ring_mul (r:A ring) a (ring_mul r d x) =
      ring_mul r d (ring_mul r a x)`) THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* The different: an ideal, the inverse of the codifferent.                  *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_DISCRIMINANT_IN_DIFFERENT = prove
 (`!k:A ring.
        number_field k
        ==> ring_of_int k (number_field_discriminant k) IN
            number_field_different (subfield_generated k {ring_0 k},k) I`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[number_field_different; IN_ELIM_THM;
              RING_OF_INT_IN_RING_OF_INTEGERS] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET o
    MATCH_MP NUMBER_FIELD_CODIFFERENT_IDEAL) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]);;

(* D is the ideal quotient ((d) : d C) of O, and (d) is contained in d C.    *)
let NUMBER_FIELD_DIFFERENT_CODIFFERENT_Q = prove
 (`!k:A ring.
        number_field k
        ==> ideal_prod (ring_of_integers k)
              (number_field_different (subfield_generated k {ring_0 k},k) I)
              (IMAGE (ring_mul k (ring_of_int k (number_field_discriminant k)))
                     (number_field_codifferent
                        (subfield_generated k {ring_0 k},k) I)) =
            ideal_generated (ring_of_integers k)
              {ring_of_int k (number_field_discriminant k)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subfield_generated k {ring_0 k}:A ring`; `k:A ring`;
                 `I:A->A`; `ring_of_int k (number_field_discriminant k):A`]
    NUMBER_FIELD_DIFFERENT_CODIFFERENT) THEN
  ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; NUMBER_FIELD_IMP_FIELD;
               RING_HOMOMORPHISM_SUBFIELD_INCLUSION; I_THM;
               RING_OF_INTEGERS_SUBFIELD_GENERATED; IN_INTER;
               RING_OF_INT_IN_RING_OF_INTEGERS;
               RING_OF_INT_IN_SUBFIELD_GENERATED;
               RING_IDEAL_IMP_SUBSET; NUMBER_FIELD_CODIFFERENT_IDEAL] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  ASM_SIMP_TAC[RING_OF_INT_EQ_0_CHAR_0; NUMBER_FIELD_DISCRIMINANT_NONZERO;
               SUBFIELD_GENERATED]);;

(* If x D SUBSET O then x d lies in x D (d C) SUBSET d C, so x is in C.      *)
(* ------------------------------------------------------------------------- *)
(* The norm of the different is the absolute value of the discriminant.      *)
(* ------------------------------------------------------------------------- *)

(* N(D) N(d C) = N((d)) = |d|^n, and d C is the Z-span of the elements       *)
(* g = M w of O with |det M| = |d|^(n - 1).                                  *)
let NUMBER_FIELD_IDEAL_NORM_DIFFERENT = prove
 (`!k:A ring.
        number_field k
        ==> ideal_norm (ring_of_integers k)
              (number_field_different (subfield_generated k {ring_0 k},k) I) =
            num_of_int(abs(number_field_discriminant k))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `w:num->A` o MATCH_MP RING_OF_INTEGERS_FREE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_DEGREE_POS) THEN
  ABBREV_TAC
   `n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
    NUMBER_FIELD_CODIFFERENT_ADJUGATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num->num->int` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `g = \j. ring_sum k {m | m < n}
     (\m. ring_mul k (ring_of_int k ((M:num->num->int) j m))
                     ((w:num->A) m))` THEN
  SUBGOAL_THEN
   `!i. i < n
        ==> (g:num->A) i =
            ring_sum (ring_of_integers k) {j | j < n}
              (\j. ring_mul k (ring_of_int k (M i j)) (w j)) /\
            g i IN ring_carrier(ring_of_integers k)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC[] THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS;
      MATCH_MP_TAC IN_SUBRING_SUM THEN
      REWRITE_TAC[RING_OF_INTEGERS_SUBRING]] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC IN_SUBRING_MUL THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS_SUBRING; RING_OF_INT_IN_RING_OF_INTEGERS];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_DISCRIMINANT_NONZERO) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_DIFFERENT_CODIFFERENT_Q) THEN
  MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_CODIFFERENT_IDEAL) THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`; `g:num->A`;
                 `ring_of_int k (number_field_discriminant k):A`]
    NUMBER_FIELD_CODIFFERENT_DUAL_SPAN) THEN
  ASM_SIMP_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED; RING_OF_INT_EQ_0_CHAR_0] THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `D = number_field_discriminant (k:A ring)` THEN
  ABBREV_TAC `J = IMAGE (ring_mul k (ring_of_int k D))
                        (number_field_codifferent
                          (subfield_generated k {ring_0 k},k) I:A->bool)` THEN
  DISCH_THEN(LABEL_TAC "J") THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `ideal_norm (ring_of_integers k) (J:A->bool) =
    num_of_int(abs D) EXP (n - 1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `n:num`; `w:num->A`;
                   `g:num->A`; `M:num->num->int`]
      FREE_BASIS_INTEGER_RING_SPAN_INDEX) THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS; INT_POW_EQ_0; INT_ABS_POW;
                 NUM_OF_INT_ABS_POW] THEN
    SUBGOAL_THEN
     `!c. ring_sum (ring_of_integers k) {i | i < n}
            (\i. ring_mul k (ring_of_int k (c i)) ((g:num->A) i)) =
          ring_sum k {i | i < n}
            (\i. ring_mul k (ring_of_int k (c i)) (g i))`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC IN_SUBRING_MUL THEN
      ASM_SIMP_TAC[RING_OF_INTEGERS_SUBRING; RING_OF_INT_IN_RING_OF_INTEGERS];
      REMOVE_THEN "J" (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[ideal_norm; QUOTIENT_RING_CARRIER; HAS_SIZE]];
    REMOVE_THEN "J" (K ALL_TAC)] THEN
  MP_TAC(ISPECL
   [`k:A ring`;
    `number_field_different (subfield_generated k {ring_0 k},k) I:A->bool`;
    `J:A->bool`]
    NUMBER_FIELD_IDEAL_NORM_MUL_Q) THEN
  ASM_SIMP_TAC[RING_OF_INTEGERS_IDEAL_NORM_INTEGER;
               NUMBER_FIELD_DIFFERENT_NONZERO; FIELD_SUBFIELD_GENERATED;
               NUMBER_FIELD_IMP_FIELD; RING_HOMOMORPHISM_SUBFIELD_INCLUSION;
               RING_IDEAL_NUMBER_FIELD_DIFFERENT] THEN
  ANTS_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `\s:A->bool. ring_of_int k D IN s`) THEN
    EXPAND_TAC "J" THEN REWRITE_TAC[IN_IMAGE; IN_SING] THEN
    MATCH_MP_TAC(TAUT `~q /\ p ==> ~(p <=> q)`) THEN
    ASM_SIMP_TAC[RING_OF_INT_EQ_0_CHAR_0] THEN
    EXISTS_TAC `ring_1 k:A` THEN
    SIMP_TAC[RING_MUL_RID; RING_OF_INT] THEN
    MP_TAC(ISPECL [`subfield_generated k {ring_0 k}:A ring`; `k:A ring`;
                   `I:A->A`] RING_OF_INTEGERS_SUBSET_CODIFFERENT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; NUMBER_FIELD_IMP_FIELD;
                   RING_HOMOMORPHISM_SUBFIELD_INCLUSION];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[IN_SUBRING_1; RING_OF_INTEGERS_SUBRING];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(num_of_int(abs D) = 0)` MP_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS; INT_ABS_ZERO];
    UNDISCH_TAC `1 <= n` THEN SPEC_TAC(`num_of_int(abs D)`,`a:num`)] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL
   [`ideal_norm (ring_of_integers k)
      (number_field_different (subfield_generated k {ring_0 k},k) I:A->bool)`;
    `a:num`; `a EXP (n - 1)`] EQ_MULT_RCANCEL) THEN
  ASM_REWRITE_TAC[EXP_EQ_0] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  TRANS_TAC EQ_TRANS `a EXP n` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `1 <= n` THEN ARITH_TAC]);;

let NUMBER_FIELD_DIFFERENT_EQ_CARRIER = prove
 (`!k:A ring.
        number_field k
        ==> (number_field_different (subfield_generated k {ring_0 k},k) I =
             ring_carrier(ring_of_integers k) <=>
             abs(number_field_discriminant k) = &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_IDEAL_NORM_DIFFERENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `ideal_norm (ring_of_integers k:A ring)`) THEN
    ASM_REWRITE_TAC[IDEAL_NORM_CARRIER] THEN
    DISCH_THEN(MP_TAC o AP_TERM `int_of_num`) THEN
    SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS];
    DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `~(number_field_different (subfield_generated k {ring_0 k},k) I =
        {ring_0 k:A})`
    ASSUME_TAC THENL
     [MATCH_MP_TAC NUMBER_FIELD_DIFFERENT_NONZERO THEN
      ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; NUMBER_FIELD_IMP_FIELD;
                   RING_HOMOMORPHISM_SUBFIELD_INCLUSION];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                   `number_field_different
                      (subfield_generated k {ring_0 k},k) I:A->bool`]
      IDEAL_NORM_GT_1) THEN
    ASM_SIMP_TAC[RING_IDEAL_NUMBER_FIELD_DIFFERENT;
                 RING_OF_INTEGERS_FINITE_QUOTIENT] THEN
    REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Multiples of 1 / p in the codifferent, through the traces in a basis.     *)
(* ------------------------------------------------------------------------- *)

(* x / p is in C iff p divides the traces Tr(x y) of all y in O (computed in *)
(* an integral basis).                                                       *)
let NUMBER_FIELD_CODIFFERENT_DIV_NUM = prove
 (`!k:A ring n w p x.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
        ~(p = 0) /\ x IN ring_carrier(ring_of_integers k)
        ==> (ring_mul k (ring_inv k (ring_of_num k p)) x IN
             number_field_codifferent (subfield_generated k {ring_0 k},k) I <=>
             !y. y IN ring_carrier(ring_of_integers k)
                 ==> &p divides
                     algebra_trace (integer_ring,ring_of_integers k)
                       (ring_of_int k) (ring_mul k x y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  SUBGOAL_THEN `~(ring_of_num k p = ring_0 (k:A ring))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_NUM_EQ_0; DIVIDES_ZERO]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_inv k (ring_of_num k p) IN
    ring_carrier(subfield_generated k {ring_0 (k:A ring)})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RING_INV_IN_SUBFIELD_GENERATED THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED] THEN
    REWRITE_TAC[GSYM RING_OF_INT_OF_NUM; RING_OF_INT_IN_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. a IN ring_carrier k /\ b IN ring_carrier k
          ==> (ring_mul k (ring_inv k (ring_of_num k p)) a = b <=>
               a = ring_mul (k:A ring) (ring_of_num k p) b)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `ring_of_num k p:A`] RING_MUL_LINV) THEN
    ASM_SIMP_TAC[FIELD_UNIT; RING_OF_NUM] THEN DISCH_TAC THEN
    REPEAT STRIP_TAC THEN
    EQ_TAC THENL [DISCH_THEN(SUBST1_TAC o SYM); DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `ring_mul k (ring_inv k (ring_of_num k p)) (ring_of_num k p) =
                 ring_1 (k:A ring)` THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_mul (r:A ring) e q = ring_1 r
        ==> a = ring_mul r q (ring_mul r e a)`);
      MATCH_MP_TAC(RING_RULE
       `ring_mul (r:A ring) e q = ring_1 r
        ==> ring_mul r e (ring_mul r q b) = b`)] THEN
    ASM_SIMP_TAC[RING_OF_NUM; RING_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[NUMBER_FIELD_CODIFFERENT_PRIME_SUBFIELD; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[RING_MUL; RING_INV; RING_OF_NUM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)`) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_mul k x y IN ring_carrier(ring_of_integers (k:A ring))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IN_SUBRING_MUL THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING];
    ALL_TAC] THEN
  ABBREV_TAC
   `t = algebra_trace (integer_ring,ring_of_integers k) (ring_of_int k)
          (ring_mul k x y:A)` THEN
  SUBGOAL_THEN
   `algebra_trace (subfield_generated k {ring_0 k},k) I
      (ring_mul k (ring_mul k (ring_inv k (ring_of_num k p)) x) y) =
    ring_mul k (ring_inv k (ring_of_num k p)) (ring_of_int (k:A ring) t)`
  ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
      NUMBER_FIELD_TRACE_INTEGRAL_BASIS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[GSYM RING_MUL_ASSOC; RING_INV; RING_OF_NUM;
                 NUMBER_FIELD_TRACE_SCALAR_MUL; RING_MUL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`;
    `ring_mul k (ring_mul k (ring_inv k (ring_of_num k p)) x) y:A`]
    NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS) THEN
  ASM_SIMP_TAC[RING_MUL; RING_INV; RING_OF_NUM] THEN
  DISCH_THEN(K ALL_TAC) THEN
  ASM_SIMP_TAC[RING_OF_INT] THEN
  REWRITE_TAC[int_divides; GSYM RING_OF_INT_OF_NUM; GSYM RING_OF_INT_MUL] THEN
  ASM_SIMP_TAC[RING_OF_INT_EQ_CHAR_0] THEN MESON_TAC[]);;
