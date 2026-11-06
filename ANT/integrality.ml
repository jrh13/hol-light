(* ========================================================================= *)
(* Relative integrality, traces, norms and units of number fields, and       *)
(* integral primitive elements.                                              *)
(*                                                                           *)
(* Number fields k <= l (field k, number_field l, ring_homomorphism(k,l) h): *)
(* x in l lies in O_l iff it is integral over O_k along h                    *)
(* (RING_OF_INTEGERS_INTEGRAL_ELEMENT), iff the coefficients of its minimal  *)
(* polynomial over k lie in O_k (RING_OF_INTEGERS_MINIMAL_POLYNOMIAL; over   *)
(* Q, iff they are integers: RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q); the     *)
(* relative trace and norm map O_l into O_k (NUMBER_FIELD_TRACE_INTEGRAL,    *)
(* NUMBER_FIELD_NORM_INTEGRAL); x in O_l is a unit of O_l iff its relative   *)
(* norm is a unit of O_k (RING_OF_INTEGERS_UNIT_NORM), and x divides h(N(x)) *)
(* in O_l (NUMBER_FIELD_NORM_MULTIPLE); u in O_k is a unit iff N_{k/Q}(u) =  *)
(* 1 or -1 (RING_OF_INTEGERS_UNIT_NORM_Q, without complex embeddings, beside *)
(* RING_OF_INTEGERS_UNIT_NORM_PRODUCT of ANT/infinite_places.ml); l = k(a)   *)
(* with a in O_l (NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT), in particular k  *)
(* = Q(a) with a in O_k (NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT_Q).         *)
(*                                                                           *)
(* Routes. O_k is integrally closed with fraction field k                    *)
(* (INTEGRALLY_CLOSED_RING_OF_INTEGERS, RING_OF_INTEGERS_FRACTION_FIELD), so *)
(* the relative statements are the results on integrally closed domains of   *)
(* ANT/integral.ml (INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL,                    *)
(* INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM, INTEGRALLY_CLOSED_UNIT_NORM) with   *)
(* transitivity of integrality. The absolute unit criterion is               *)
(* ALGEBRA_NORM_UNIT of Library/ring_det.ml for an integral basis. A         *)
(* primitive element l = k(b) (PRIMITIVE_ELEMENT_THEOREM) is made integral   *)
(* by an integer multiple (NUMBER_FIELD_INTEGRAL_MULTIPLE).                  *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/fieldtheory.ml (minimal polynomials, *)
(* PRIMITIVE_ELEMENT_THEOREM), Library/ring_det.ml                           *)
(* (algebra_trace, algebra_norm, ALGEBRA_NORM_UNIT), ANT/integral.ml,        *)
(* ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml               *)
(* (NUMBER_FIELD_NORM_INTEGRAL_BASIS), ANT/nf_valuation.ml                   *)
(* (RING_OF_INTEGERS_FRACTION_FIELD) and ANT/relative_split.ml               *)
(* (NUMBER_FIELD_TOWER_LAW).                                                 *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/ring_det.ml";;
needs "ANT/integral.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/norm_index.ml";;
needs "ANT/nf_valuation.ml";;
needs "ANT/relative_split.ml";;

(* ------------------------------------------------------------------------- *)
(* Number fields: relative integrality, traces, norms and units;             *)
(* integral primitive elements.                                              *)
(* ------------------------------------------------------------------------- *)

let RING_OF_INTEGERS_INTEGRAL_ELEMENT = prove
 (`!k:A ring l:B ring h x.
        ring_homomorphism(k,l) h
        ==> (integral_element (ring_of_integers k,l) h x <=>
             x IN ring_carrier(ring_of_integers l))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ring_homomorphism(ring_of_integers k,l) (h:A->B)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ring_of_integers] THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_FROM_SUBRING_GENERATED THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_homomorphism(integer_ring,ring_of_integers k) (ring_of_int k:int->A)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `ring_of_integers(k:A ring)`
      RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN
    REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->B) o ring_of_int k = ring_of_int l` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_RING_OF_INT];
    ALL_TAC] THEN
  REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC INTEGRAL_ELEMENT_TRANS THEN
    EXISTS_TAC `ring_of_integers(k:A ring)` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:A` THEN REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM] THEN
    DISCH_TAC THEN REWRITE_TAC[ring_of_integers] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_ELEMENT_SUBRING_GENERATED o
      snd) THEN
    REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRAL_CLOSURE_SUBRING THEN
        REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT];
        MATCH_MP_TAC INTEGRAL_CLOSURE_SUPSET_IMAGE THEN
        REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT]];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`integer_ring`; `ring_of_integers k:A ring`; `l:B ring`;
                   `ring_of_int k:int->A`; `h:A->B`; `x:B`]
      INTEGRAL_ELEMENT_INTERMEDIATE) THEN
    ASM_REWRITE_TAC[]]);;

let RING_OF_INTEGERS_MINIMAL_POLYNOMIAL = prove
 (`!k:A ring l:B ring h x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        x IN ring_carrier l
        ==> (x IN ring_carrier(ring_of_integers l) <=>
             !i. coeff i (minimal_polynomial (k,l) h x) IN
                 ring_carrier(ring_of_integers k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `l:B ring`;
                 `I:A->A`; `h:A->B`; `x:B`]
    INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL) THEN
  ASM_SIMP_TAC[INTEGRALLY_CLOSED_RING_OF_INTEGERS;
               RING_OF_INTEGERS_FRACTION_FIELD; I_O_ID; IMAGE_I;
               RING_OF_INTEGERS_INTEGRAL_ELEMENT] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION; algebraic_extension]);;

(* Over the prime subfield: x is integral iff its minimal polynomial has   *)
(* integer coefficients (by RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER).      *)
let RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q = prove
 (`!k:A ring x.
        number_field k /\ x IN ring_carrier k
        ==> (x IN ring_carrier(ring_of_integers k) <=>
             !i. ?m. coeff i (minimal_polynomial
                                (subfield_generated k {ring_0 k},k) I x) =
                     ring_of_int k m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subfield_generated k {ring_0 k}:A ring`; `k:A ring`;
                 `I:A->A`; `x:A`] RING_OF_INTEGERS_MINIMAL_POLYNOMIAL) THEN
  ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; NUMBER_FIELD_IMP_FIELD;
               RING_HOMOMORPHISM_SUBFIELD_INCLUSION;
               RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER] THEN
  DISCH_THEN SUBST1_TAC THEN SET_TAC[]);;

let NUMBER_FIELD_TRACE_INTEGRAL,
    NUMBER_FIELD_NORM_INTEGRAL = (CONJ_PAIR o prove)
 (`(!k:A ring l:B ring h x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        x IN ring_carrier(ring_of_integers l)
        ==> algebra_trace (k,l) h x IN ring_carrier(ring_of_integers k)) /\
   (!k:A ring l:B ring h x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        x IN ring_carrier(ring_of_integers l)
        ==> algebra_norm (k,l) h x IN ring_carrier(ring_of_integers k))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `l:B ring`;
                 `I:A->A`; `h:A->B`; `x:B`]
    INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM) THEN
  ASM_SIMP_TAC[INTEGRALLY_CLOSED_RING_OF_INTEGERS;
               RING_OF_INTEGERS_FRACTION_FIELD; I_O_ID; IMAGE_I;
               RING_OF_INTEGERS_INTEGRAL_ELEMENT]);;

let RING_OF_INTEGERS_UNIT_NORM = prove
 (`!k:A ring l:B ring h x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        x IN ring_carrier(ring_of_integers l)
        ==> (ring_unit (ring_of_integers l) x <=>
             ring_unit (ring_of_integers k) (algebra_norm (k,l) h x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `l:B ring`;
                 `I:A->A`; `h:A->B`; `x:B`] INTEGRALLY_CLOSED_UNIT_NORM) THEN
  ASM_SIMP_TAC[INTEGRALLY_CLOSED_RING_OF_INTEGERS;
               RING_OF_INTEGERS_FRACTION_FIELD; I_O_ID; I_THM;
               RING_OF_INTEGERS_INTEGRAL_ELEMENT] THEN
  DISCH_TAC THEN TRANS_TAC EQ_TRANS
   `?y:B. y IN ring_carrier(ring_of_integers l) /\ ring_mul l x y = ring_1 l`
  THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[ring_unit; RING_OF_INTEGERS];
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let RING_OF_INTEGERS_UNIT_NORM_Q = prove
 (`!k x:A.
        number_field k
        ==> (ring_unit (ring_of_integers k) x <=>
             x IN ring_carrier(ring_of_integers k) /\
             (algebra_norm (subfield_generated k {ring_0 k},k) I x =
              ring_1 k \/
              algebra_norm (subfield_generated k {ring_0 k},k) I x =
              ring_neg k (ring_1 k)))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(x:A) IN ring_carrier(ring_of_integers k)` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[RING_UNIT_IN_CARRIER]] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `w:num->A` o MATCH_MP RING_OF_INTEGERS_FREE) THEN
  MP_TAC(ISPECL [`ring_of_int k:int->A`; `integer_ring`;
                 `ring_of_integers k:A ring`; `x:A`] ALGEBRA_NORM_UNIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MP_TAC(ISPEC `ring_of_integers(k:A ring)`
      RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN
    REWRITE_TAC[RING_OF_INTEGERS];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL
   [`k:A ring`;
    `extension_degree (subfield_generated k {ring_0 k},k:A ring) I`;
    `w:num->A`; `x:A`] NUMBER_FIELD_NORM_INTEGRAL_BASIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INTEGER_RING_UNIT; GSYM RING_OF_INT_1] THEN
  REWRITE_TAC[GSYM RING_OF_INT_NEG] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  ASM_SIMP_TAC[RING_OF_INT_EQ_CHAR_0]);;

(* x divides N(x) in O_l: the constant coefficient of the minimal polynomial *)
(* of x is a multiple of x, and N(x) is a positive power of it up to sign    *)
(* (ALGEBRA_NORM_MINIMAL_POLYNOMIAL).                                        *)
let NUMBER_FIELD_NORM_MULTIPLE = prove
 (`!k:A ring l:B ring h x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        x IN ring_carrier(ring_of_integers l)
        ==> h(algebra_norm (k,l) h x) IN
            ideal_generated (ring_of_integers l) {x}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[field_extension] o
    check (fun th -> concl th = `field_extension(k:A ring,l:B ring) h`)) THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `J = ideal_generated (ring_of_integers l) {x:B}` THEN
  SUBGOAL_THEN `ring_ideal (ring_of_integers l) (J:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:B) IN J` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN ASM_REWRITE_TAC[IN_IDEAL_GENERATED_SELF]; ALL_TAC] THEN
  SUBGOAL_THEN `algebraic_over (k,l) (h:A->B) x` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION o
      check (fun th -> concl th = `finite_extension(k:A ring,l:B ring) h`)) THEN
    REWRITE_TAC[algebraic_extension] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `x:B`]
    RING_OF_INTEGERS_MINIMAL_POLYNOMIAL) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    MINIMAL_POLYNOMIAL) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    ALGEBRA_NORM_MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `p = minimal_polynomial (k,l) (h:A->B) x` THEN
  ABBREV_TAC
   `m = extension_degree
         (subfield_generated l (x INSERT IMAGE (h:A->B) (ring_carrier k)),l)
         I` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                   `x INSERT IMAGE (h:A->B) (ring_carrier k)`]
      FINITE_EXTENSION_SUBFIELD_GENERATED) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    ASM_SIMP_TAC[EXTENSION_DEGREE_EQ_0; FIELD_EXTENSION_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. coeff i (p:(1->num)->A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. (h:A->B)(coeff i p) IN ring_carrier(ring_of_integers l)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. (h:A->B)(coeff i p) IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->B)(coeff 0 p) IN J` ASSUME_TAC THENL
   [UNDISCH_TAC `poly_extend (k,l) (h:A->B) (\v:1. x) p = ring_0 l` THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `\v:1. (x:B)`;
                   `p:(1->num)->A`] POLY_EXTEND_UNIVARIATE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC[RING_SUM_CLAUSES_LEFT; LE_0] THEN
    ASM_SIMP_TAC[RING_MUL; RING_POW; RING_1; ring_pow; RING_MUL_RID;
                 ADD_CLAUSES] THEN
    ABBREV_TAC
     `S = ring_sum l (1..poly_deg k p)
            (\i. ring_mul l ((h:A->B) (coeff i p)) (ring_pow l x i))` THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`l:B ring`; `(h:A->B)(coeff 0 p)`; `S:B`]
      RING_RNEG_UNIQUE) THEN
    ASM_SIMP_TAC[] THEN ANTS_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[RING_SUM];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` IN_RING_IDEAL_NEG)) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RING_OF_INTEGERS o
      lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REWRITE_RULE[RING_OF_INTEGERS]
       (ISPEC `ring_of_integers l:B ring` RING_MUL);
                   REWRITE_RULE[RING_OF_INTEGERS]
       (ISPEC `ring_of_integers l:B ring` RING_POW)];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC IN_RING_IDEAL_SUM THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `i = SUC(i - 1)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[ring_pow]] THEN
    SUBGOAL_THEN
     `ring_mul l ((h:A->B) (coeff (SUC (i - 1)) p))
        (ring_mul l x (ring_pow l x (i - 1))) =
      ring_mul l x (ring_mul l (h(coeff (SUC (i - 1)) p))
                                 (ring_pow l x (i - 1)))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_mul (r:B ring) a (ring_mul r x y) =
        ring_mul r x (ring_mul r a y)`) THEN
      ASM_SIMP_TAC[RING_POW];
      ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` IN_RING_IDEAL_RMUL)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_MUL)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_POW)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_pow k (ring_neg k (ring_1 k)) (poly_deg k p) IN ring_carrier k /\
    ring_mul k (ring_pow k (ring_neg k (ring_1 k)) (poly_deg k p))
      (coeff 0 (p:(1->num)->A)) IN ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_POW; RING_NEG; RING_1; RING_MUL]; ALL_TAC] THEN
  FIRST_ASSUM((fun th -> ASM_SIMP_TAC(RING_POW :: RING_MUL :: RING_NEG ::
    RING_1 :: map (C MATCH_MP th)
     [RING_HOMOMORPHISM_POW; RING_HOMOMORPHISM_MUL; RING_HOMOMORPHISM_NEG;
      RING_HOMOMORPHISM_1])) o
    check (fun th -> concl th = `ring_homomorphism(k:A ring,l:B ring) h`)) THEN
  SUBGOAL_THEN
   `ring_mul l (ring_pow l (ring_neg l (ring_1 l)) (poly_deg k p))
      ((h:A->B)(coeff 0 p)) IN J`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` IN_RING_IDEAL_LMUL)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_POW)) THEN
    MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_NEG)) THEN
    REWRITE_TAC[REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_1)];
    ALL_TAC] THEN
  SUBGOAL_THEN `m = SUC(m - 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[ring_pow]] THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
   (ISPEC `ring_of_integers l:B ring` IN_RING_IDEAL_RMUL)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
   (ISPEC `ring_of_integers l:B ring` RING_POW)) THEN
  ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]);;

let NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT = prove
 (`!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> ?a. a IN ring_carrier(ring_of_integers l) /\
                subring_generated l (a INSERT IMAGE h (ring_carrier k)) = l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    PRIMITIVE_ELEMENT_THEOREM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SEPARABLE_EXTENSION_CHAR0 THEN
    ASM_SIMP_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION] THEN
    ASM_MESON_TAC[number_field];
    DISCH_THEN(X_CHOOSE_THEN `b:B` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`l:B ring`; `b:B`] NUMBER_FIELD_INTEGRAL_MULTIPLE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:int` THEN STRIP_TAC THEN
  EXISTS_TAC `ring_mul l (ring_of_int l d) (b:B)` THEN
  ASM_REWRITE_TAC[SUBRING_GENERATED_SUPERSET] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
  REWRITE_TAC[SUBRING_SUBRING_GENERATED; INSERT_SUBSET] THEN
  SUBGOAL_THEN `IMAGE (h:A->B) (ring_carrier k) SUBSET ring_carrier l`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:A->B) (ring_carrier k) SUBSET
    ring_carrier(subring_generated l
     (ring_mul l (ring_of_int l d) b INSERT IMAGE h (ring_carrier k)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `~(ring_of_int k d:A = ring_0 k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INT_EQ_0_CHAR_0; number_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(b:B) = ring_mul l ((h:A->B) (ring_inv k (ring_of_int k d)))
                       (ring_mul l (ring_of_int l d) b)`
  (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THENL
   [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      RING_HOMOMORPHISM_RING_OF_INT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    SUBGOAL_THEN
     `ring_mul l ((h:A->B) (ring_inv k (ring_of_int k d)))
                 (h (ring_of_int k d)) = ring_1 l`
    MP_TAC THENL
     [FIRST_ASSUM((fun th -> ASM_SIMP_TAC[RING_INV; RING_OF_INT;
        FIELD_MUL_LINV; GSYM(MATCH_MP RING_HOMOMORPHISM_MUL th);
        MATCH_MP RING_HOMOMORPHISM_1 th]) o
        check (fun th -> concl th = `ring_homomorphism(k,l) (h:A->B)`));
      ALL_TAC] THEN
    MATCH_MP_TAC(RING_RULE
     `ring_mul (l:B ring) u v = ring_1 l
      ==> b = ring_mul l u (ring_mul l v b)`) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC `k:A ring` THEN
    ASM_SIMP_TAC[RING_INV; RING_OF_INT];
    ALL_TAC] THEN
  MATCH_MP_TAC RING_MUL_IN_SUBRING_GENERATED THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[RING_INV; RING_OF_INT];
    MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
    ASM_SIMP_TAC[IN_INSERT; RING_MUL; RING_OF_INT]]);;

let NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT_Q = prove
 (`!k:A ring.
        number_field k
        ==> ?a. a IN ring_carrier(ring_of_integers k) /\
                subfield_generated k {a} = k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPECL [`subfield_generated k {ring_0 k:A}`; `k:A ring`; `I:A->A`]
    NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION; FIELD_SUBFIELD_GENERATED;
               IMAGE_I] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[SUBRING_GENERATED_SUPERSET; SUBFIELD_GENERATED_SUPERSET] THEN
  MATCH_MP_TAC(SET_RULE
   `(t:A->bool) SUBSET u ==> s SUBSET t ==> s SUBSET u`) THEN
  MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
  REWRITE_TAC[SUBRING_SUBFIELD_GENERATED; INSERT_SUBSET] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC[IN_SING];
    MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
    ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED; SING_SUBSET] THEN
    MATCH_MP_TAC IN_SUBRING_0 THEN REWRITE_TAC[SUBRING_SUBFIELD_GENERATED]]);;
