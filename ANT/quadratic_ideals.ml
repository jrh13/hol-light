(* ========================================================================= *)
(* Quadratic fields: the Galois group, the norm and the trace, conjugate     *)
(* ideals and conjugate prime ideals. Let k be a number field of degree 2    *)
(* over its prime field Q = subfield_generated k {ring_0 k}.                 *)
(*                                                                           *)
(* k is Galois over Q with a Galois group of 2 elements                      *)
(* (QUADRATIC_FIELD_GALOIS_EXTENSION, QUADRATIC_FIELD_CONJUGATION_EXISTS);   *)
(* for x not in Q with x^2 in Q the nontrivial element s maps x to -x and a  *)
(* + b x to a - b x (QUADRATIC_FIELD_GALOIS_GROUP, x generates k:            *)
(* QUADRATIC_FIELD_SUBFIELD_GENERATED), and N(z) = z s(z), Tr(z) = z + s(z)  *)
(* (QUADRATIC_FIELD_NORM_TRACE_CONJUGATE), so N(a + b x) = a^2 - b^2 x^2 for *)
(* a, b in Q (QUADRATIC_FIELD_NORM; the trace is QUADRATIC_FIELD_TRACE of    *)
(* ANT/quadratic.ml). For x^2 = d an integer and the standard generator w of *)
(* O_k, w = (1 + x) / 2 if d == 1 (mod 4) and w = x otherwise, the norm form *)
(* and the trace of a + b w with a, b integers are a^2 + a b + (1 - d)/4 b^2 *)
(* and 2 a + b, resp. a^2 - d b^2 and 2 a                                    *)
(* (QUADRATIC_FIELD_NORM_TRACE_INTEGRAL_BASIS, from                          *)
(* QUADRATIC_FIELD_NORM_TRACE_HALF and QUADRATIC_FIELD_NORM_TRACE_SQRT).     *)
(*                                                                           *)
(* Conjugate ideals: j s(j) = N(j) O_k for every nonzero ideal j of O_k      *)
(* (QUADRATIC_FIELD_IDEAL_MUL_CONJUGATE, the case of degree 2 of             *)
(* NUMBER_FIELD_GALOIS_PRODUCT_IDEAL of ANT/conjugate_ideals.ml).            *)
(*                                                                           *)
(* Conjugate primes: for x^2 = d with d squarefree, d <> 1, p odd not        *)
(* dividing d and y^2 == d (mod p), s maps the prime (p, x - y) to (p, x +   *)
(* y) (QUADRATIC_FIELD_CONJUGATE_PRIME_PAIR); the prime ideals of the        *)
(* decomposition law are named in ANT/quadratic_split.ml                     *)
(* (QUADRATIC_FIELD_SPLIT_ODD_PRIME and the others).                         *)
(*                                                                           *)
(* Routes. Galois: x generates k, and k = Q(x) with x^2 in Q is a Kummer     *)
(* extension of degree 2 (KUMMER_EXTENSION_ABELIAN of Library/galois.ml);    *)
(* s(x)^2 = x^2 gives s(x) = -x unless s fixes the generator x. Norm and     *)
(* trace: the product and the sum over the Galois group                      *)
(* (ALGEBRA_TRACE_NORM_GALOIS); for w = (1 + x)/2, s(w) = 1 - w and w^2 = w  *)
(* - (1 - d)/4. Conjugate primes: s(x - y) = -(x + y) and                    *)
(* IDEAL_GENERATED_PAIR_EQ of Library/ringtheory.ml.                         *)
(*                                                                           *)
(* Uses: Library/integer.ml, Library/ringtheory.ml                           *)
(* (IDEAL_GENERATED_PAIR_EQ), Library/fieldtheory.ml, Library/galois.ml,     *)
(* Library/ring_det.ml (algebra_norm, algebra_trace), ANT/ideal_arith.ml     *)
(* (ideal products), ANT/ideal_norm.ml, ANT/numfield.ml, ANT/quadratic.ml,   *)
(* ANT/nf_decomposition.ml (GALOIS_GROUP_IMAGE_IDEAL_GENERATED) and          *)
(* ANT/conjugate_ideals.ml.                                                  *)
(* ========================================================================= *)

needs "Library/integer.ml";;
needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/ring_det.ml";;
needs "Library/galois.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/numfield.ml";;
needs "ANT/quadratic.ml";;
needs "ANT/conjugate_ideals.ml";;

(* ------------------------------------------------------------------------- *)
(* The Galois group of a quadratic field.                                    *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FIELD_SUBFIELD_GENERATED = prove
 (`!k:A ring x.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k}))
        ==> subfield_generated k {x} = k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  REWRITE_TAC[SUBFIELD_GENERATED_SUPERSET; SUBSET] THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `z:A`] QUADRATIC_FIELD_COORDINATES) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_carrier(subfield_generated k {ring_0 k}) SUBSET
    ring_carrier(subfield_generated k {x:A})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRIME_SUBFIELD_MINIMAL THEN
    ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED_EQ; FIELD_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN ring_carrier(subfield_generated k {x})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(a:A) IN ring_carrier(subfield_generated k {x}) /\
    (b:A) IN ring_carrier(subfield_generated k {x})`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`subfield_generated k {x:A}`; `b:A`; `x:A`] RING_MUL) THEN
  ASM_REWRITE_TAC[SUBFIELD_GENERATED] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subfield_generated k {x:A}`; `a:A`; `ring_mul k b x:A`]
    RING_ADD) THEN
  ASM_REWRITE_TAC[SUBFIELD_GENERATED]);;

let QUADRATIC_FIELD_GALOIS_EXTENSION = prove
 (`!k:A ring.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2
        ==> finite_extension (subfield_generated k {ring_0 k},k) I /\
            galois_extension (subfield_generated k {ring_0 k},k) I /\
            group_carrier(galois_group(subfield_generated k {ring_0 k},k) I)
            HAS_SIZE 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPEC `k:A ring` QUADRATIC_FIELD_INTEGER_SQUARE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`w:A`; `m:int`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `w:A`; `2`] KUMMER_EXTENSION_ABELIAN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED; IMAGE_I] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[RING_POW_SUBFIELD_GENERATED;
                  CONJUNCT2 SUBFIELD_GENERATED] THEN
      SUBGOAL_THEN
       `{y | y IN ring_carrier(subfield_generated k {ring_0 k}) /\
             ring_pow k y 2 = ring_1 k} =
        {ring_1 k, ring_neg k (ring_1 k:A)}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
        X_GEN_TAC `y:A` THEN
        ASM_CASES_TAC `(y:A) IN ring_carrier(subfield_generated k {ring_0 k})`
        THENL
         [MP_TAC(ISPECL [`k:A ring`; `y:A`] (INTEGRAL_DOMAIN_RULE
           `!r x:A. integral_domain r /\ x IN ring_carrier r
                    ==> (ring_pow r x 2 = ring_1 r <=>
                         x = ring_1 r \/ x = ring_neg r (ring_1 r))`)) THEN
          ANTS_TAC THENL
           [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
            MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`]
              RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
            ASM SET_TAC[];
            DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
          ASM_REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THEN
          DISCH_THEN SUBST_ALL_TAC THEN
          RULE_ASSUM_TAC(REWRITE_RULE[RING_1_IN_SUBFIELD_GENERATED]) THEN
          ASM_MESON_TAC[RING_1_IN_SUBFIELD_GENERATED;
                        RING_NEG_IN_SUBFIELD_GENERATED]];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(ring_1 k = ring_neg k (ring_1 k:A))` ASSUME_TAC THENL
       [REWRITE_TAC[RING_RULE
         `!r:A ring. ring_1 r = ring_neg r (ring_1 r) <=>
                     ring_of_num r 2 = ring_0 r`] THEN
        ASM_SIMP_TAC[NUMBER_FIELD_RING_OF_NUM_EQ_0; ARITH_EQ];
        ASM_SIMP_TAC[HAS_SIZE; FINITE_INSERT; FINITE_EMPTY; CARD_CLAUSES;
                     IN_INSERT; NOT_IN_EMPTY] THEN
        CONV_TAC NUM_REDUCE_CONV];
      ASM_REWRITE_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED];
      REWRITE_TAC[SUBFIELD_GENERATED_SUPERSET] THEN
      MP_TAC(ISPECL [`k:A ring`; `w:A`] QUADRATIC_FIELD_SUBFIELD_GENERATED) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN SET_TAC[]];
    STRIP_TAC] THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_GALOIS_GROUP] THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`]
    GALOIS_EXTENSION_EQ_CARD) THEN
  ASM_SIMP_TAC[]);;

let QUADRATIC_FIELD_GALOIS_GROUP = prove
 (`!k:A ring x s.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 IN ring_carrier(subfield_generated k {ring_0 k}) /\
        s IN group_carrier(galois_group(subfield_generated k {ring_0 k},k) I) /\
        ~(s = I)
        ==> group_carrier(galois_group(subfield_generated k {ring_0 k},k) I) =
            {I,s} /\
            s x = ring_neg k x /\
            !a b. a IN ring_carrier(subfield_generated k {ring_0 k}) /\
                  b IN ring_carrier(subfield_generated k {ring_0 k})
                  ==> s(ring_add k a (ring_mul k b x)) =
                      ring_sub k a (ring_mul k b x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPEC `k:A ring` QUADRATIC_FIELD_GALOIS_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_homomorphism(k,k) (s:A->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ring_carrier(subfield_generated k {ring_0 k}) ==> (s:A->A) y = y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`I:A->A`; `s:A->A`; `subfield_generated k {ring_0 k:A}`;
                   `k:A ring`; `y:A`] GALOIS_GROUP_FIXES) THEN
    ASM_REWRITE_TAC[I_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_carrier(subfield_generated k {ring_0 k}) SUBSET
                ring_carrier(k:A ring)`
  ASSUME_TAC THENL
   [REWRITE_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:A->A) x = ring_neg k x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `(s:A->A) x`; `x:A`] (INTEGRAL_DOMAIN_RULE
     `!r x y:A. integral_domain r /\ x IN ring_carrier r /\
                y IN ring_carrier r
                ==> (ring_pow r x 2 = ring_pow r y 2 <=>
                     x = y \/ x = ring_neg r y)`)) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
    SUBGOAL_THEN `(s:A->A) x IN ring_carrier k` ASSUME_TAC THENL
     [ASM_MESON_TAC[GALOIS_GROUP_IN_CARRIER]; ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `ring_pow k ((s:A->A) x) 2 = ring_pow k x 2`
     (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(ISPECL [`x:A`; `2`] (MATCH_MP RING_HOMOMORPHISM_POW
        (ASSUME `ring_homomorphism(k,k) (s:A->A)`))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~(s:A->A = I)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC GALOIS_GROUP_EQ_ON_GENERATORS THEN
    MAP_EVERY EXISTS_TAC [`I:A->A`; `subfield_generated k {ring_0 k:A}`;
                          `k:A ring`; `{x:A}`] THEN
    ASM_REWRITE_TAC[GALOIS_GROUP_I; IN_SING; I_THM; FORALL_UNWIND_THM2] THEN
    REWRITE_TAC[SUBFIELD_GENERATED_SUPERSET] THEN
    MP_TAC(ISPECL [`k:A ring`; `x:A`] QUADRATIC_FIELD_SUBFIELD_GENERATED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN SET_TAC[];
    ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; GALOIS_GROUP_I] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                 NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier k /\ (b:A) IN ring_carrier k`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[RING_MUL; MATCH_MP RING_HOMOMORPHISM_ADD th;
                 MATCH_MP RING_HOMOMORPHISM_MUL th]) THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `b:A`; `x:A`] (RING_RULE
   `!r a b x:A. a IN ring_carrier r /\ b IN ring_carrier r /\
                x IN ring_carrier r
                ==> ring_add r a (ring_mul r b (ring_neg r x)) =
                    ring_sub r a (ring_mul r b x)`)) THEN
  ASM_REWRITE_TAC[]);;

let QUADRATIC_FIELD_CONJUGATION_EXISTS = prove
 (`!k:A ring.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2
        ==> ?s. s IN group_carrier
                  (galois_group(subfield_generated k {ring_0 k},k) I) /\
                ~(s = I)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o
    MATCH_MP QUADRATIC_FIELD_GALOIS_EXTENSION) THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:A->A`; `g:A->A`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_CASES_TAC `f:A->A = I` THENL
   [EXISTS_TAC `g:A->A` THEN ASM_MESON_TAC[];
    EXISTS_TAC `f:A->A` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Norm and trace.                                                           *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FIELD_NORM_TRACE_CONJUGATE = prove
 (`!k:A ring s z.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        s IN group_carrier(galois_group(subfield_generated k {ring_0 k},k) I) /\
        ~(s = I) /\ z IN ring_carrier k
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I z =
            ring_mul k z (s z) /\
            algebra_trace (subfield_generated k {ring_0 k},k) I z =
            ring_add k z (s z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPEC `k:A ring` QUADRATIC_FIELD_INTEGER_SQUARE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`w:A`; `m:int`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `w:A`; `s:A->A`] QUADRATIC_FIELD_GALOIS_GROUP) THEN
  ASM_REWRITE_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPEC `k:A ring` QUADRATIC_FIELD_GALOIS_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `z:A`] ALGEBRA_TRACE_NORM_GALOIS) THEN
  ASM_REWRITE_TAC[I_THM] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN `(s:A->A) z IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_IN_CARRIER]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_PRODUCT_CLAUSES; RING_SUM_CLAUSES; FINITE_SING;
               IN_SING; RING_PRODUCT_SING; RING_SUM_SING; I_THM] THEN
  ASM_MESON_TAC[]);;

let QUADRATIC_FIELD_NORM = prove
 (`!k:A ring x a b.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 IN ring_carrier(subfield_generated k {ring_0 k}) /\
        a IN ring_carrier(subfield_generated k {ring_0 k}) /\
        b IN ring_carrier(subfield_generated k {ring_0 k})
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I
              (ring_add k a (ring_mul k b x)) =
            ring_sub k (ring_pow k a 2)
                       (ring_mul k (ring_pow k b 2) (ring_pow k x 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` QUADRATIC_FIELD_CONJUGATION_EXISTS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `s:A->A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `s:A->A`] QUADRATIC_FIELD_GALOIS_GROUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier k /\ (b:A) IN ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `s:A->A`; `ring_add k a (ring_mul k b x):A`]
    QUADRATIC_FIELD_NORM_TRACE_CONJUGATE) THEN
  ASM_SIMP_TAC[RING_ADD; RING_MUL] THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `b:A`; `x:A`] (RING_RULE
   `!r a b x:A. a IN ring_carrier r /\ b IN ring_carrier r /\
                x IN ring_carrier r
                ==> ring_mul r (ring_add r a (ring_mul r b x))
                               (ring_sub r a (ring_mul r b x)) =
                    ring_sub r (ring_pow r a 2)
                               (ring_mul r (ring_pow r b 2)
                                           (ring_pow r x 2))`)) THEN
  ASM_REWRITE_TAC[]);;

let QUADRATIC_FIELD_NORM_TRACE_SQRT = prove
 (`!k:A ring x d a b.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 = ring_of_int k d
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I
              (ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) x)) =
            ring_of_int k (a pow 2 - d * b pow 2) /\
            algebra_trace (subfield_generated k {ring_0 k},k) I
              (ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) x)) =
            ring_of_int k (&2 * a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `x:A`; `ring_of_int k a:A`;
                   `ring_of_int k b:A`] QUADRATIC_FIELD_NORM) THEN
    ASM_REWRITE_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[RING_OF_INT_SUB; RING_OF_INT_MUL; RING_OF_INT_POW] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC RING_MUL_SYM THEN
    SIMP_TAC[RING_POW; RING_OF_INT];
    MP_TAC(ISPECL [`k:A ring`; `x:A`; `ring_of_int k a:A`;
                   `ring_of_int k b:A`] QUADRATIC_FIELD_TRACE) THEN
    ASM_REWRITE_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[RING_OF_INT_MUL; RING_OF_INT_OF_NUM]]);;

let QUADRATIC_FIELD_NORM_TRACE_HALF = prove
 (`!k:A ring x d a b.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 = ring_of_int k d /\ (d == &1) (mod &4)
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I
              (ring_add k (ring_of_int k a)
                 (ring_mul k (ring_of_int k b)
                    (ring_div k (ring_add k (ring_1 k) x)
                                (ring_of_num k 2)))) =
            ring_of_int k (a pow 2 + a * b + ((&1 - d) div &4) * b pow 2) /\
            algebra_trace (subfield_generated k {ring_0 k},k) I
              (ring_add k (ring_of_int k a)
                 (ring_mul k (ring_of_int k b)
                    (ring_div k (ring_add k (ring_1 k) x)
                                (ring_of_num k 2)))) =
            ring_of_int k (&2 * a + b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  SUBGOAL_THEN `~(ring_of_num k 2 = ring_0 (k:A ring)) /\
                ~(ring_of_num k 4 = ring_0 (k:A ring))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NUMBER_FIELD_RING_OF_NUM_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`; `x:A`]
    SUBFIELD_GENERATED_HALF_SUCC) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `w = ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2):A` THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` QUADRATIC_FIELD_CONJUGATION_EXISTS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `s:A->A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `s:A->A`] QUADRATIC_FIELD_GALOIS_GROUP) THEN
  ASM_REWRITE_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_homomorphism(k,k) (s:A->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:A->A) w = ring_sub k (ring_1 k) w` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `ring_of_num k 2:A`] THEN
    ASM_SIMP_TAC[RING_OF_NUM; RING_SUB; RING_1] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[GALOIS_GROUP_IN_CARRIER]; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS `(s:A->A)(ring_mul k (ring_of_num k 2) w)` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> SIMP_TAC[RING_OF_NUM;
        ASSUME `(w:A) IN ring_carrier k`;
        MATCH_MP RING_HOMOMORPHISM_MUL th;
        MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th]);
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> ASM_SIMP_TAC[RING_1;
      MATCH_MP RING_HOMOMORPHISM_ADD th; MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
    MP_TAC(ISPECL [`k:A ring`; `x:A`; `w:A`] (RING_RULE
     `!r x w:A. x IN ring_carrier r /\ w IN ring_carrier r /\
                ring_mul r (ring_of_num r 2) w = ring_add r (ring_1 r) x
                ==> ring_add r (ring_1 r) (ring_neg r x) =
                    ring_mul r (ring_of_num r 2)
                               (ring_sub r (ring_1 r) w)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `t = (&1 - d) div &4:int` THEN
  SUBGOAL_THEN `&4 * t:int = &1 - d` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
    REWRITE_TAC[INT_MUL_DIV_EQ] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!d n:int. (d == &1) (mod n) ==> n divides (&1 - d)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_pow k w 2 = ring_sub k w (ring_of_int k t):A`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `ring_of_num k 4:A`] THEN
    ASM_SIMP_TAC[RING_OF_NUM; RING_SUB; RING_POW; RING_OF_INT] THEN
    SUBGOAL_THEN `ring_mul k (ring_of_num k 4) (ring_of_int k t) =
                  ring_sub k (ring_1 k) (ring_of_int k d):A`
    MP_TAC THENL
     [REWRITE_TAC[GSYM RING_OF_INT_OF_NUM; GSYM RING_OF_INT_MUL;
                  GSYM RING_OF_INT_1; GSYM RING_OF_INT_SUB] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `x:A`; `w:A`; `ring_of_int k t:A`;
                   `ring_of_int k d:A`] (RING_RULE
     `!r x w u e:A. x IN ring_carrier r /\ w IN ring_carrier r /\
                    u IN ring_carrier r /\ e IN ring_carrier r /\
                    ring_mul r (ring_of_num r 2) w = ring_add r (ring_1 r) x /\
                    ring_pow r x 2 = e /\
                    ring_mul r (ring_of_num r 4) u = ring_sub r (ring_1 r) e
                    ==> ring_mul r (ring_of_num r 4) (ring_pow r w 2) =
                        ring_mul r (ring_of_num r 4) (ring_sub r w u)`)) THEN
    ASM_REWRITE_TAC[RING_OF_INT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `s:A->A`;
                 `ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) w)
                  :A`] QUADRATIC_FIELD_NORM_TRACE_CONJUGATE) THEN
  ASM_SIMP_TAC[RING_ADD; RING_MUL; RING_OF_INT] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  FIRST_ASSUM(fun th -> SIMP_TAC[RING_MUL; RING_OF_INT;
    ASSUME `(w:A) IN ring_carrier k`;
    MATCH_MP RING_HOMOMORPHISM_ADD th; MATCH_MP RING_HOMOMORPHISM_MUL th;
    MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th]) THEN
  REWRITE_TAC[ASSUME `(s:A->A) w = ring_sub k (ring_1 k) w`] THEN
  REWRITE_TAC[RING_OF_INT_ADD; RING_OF_INT_MUL; RING_OF_INT_POW;
              RING_OF_INT_OF_NUM] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `ring_of_int k a:A`; `ring_of_int k b:A`;
                   `w:A`; `ring_of_int k t:A`] (RING_RULE
     `!r a b w t:A.
        a IN ring_carrier r /\ b IN ring_carrier r /\ w IN ring_carrier r /\
        t IN ring_carrier r /\ ring_pow r w 2 = ring_sub r w t
        ==> ring_mul r (ring_add r a (ring_mul r b w))
                       (ring_add r a (ring_mul r b (ring_sub r (ring_1 r) w))) =
            ring_add r (ring_pow r a 2)
                       (ring_add r (ring_mul r a b)
                                   (ring_mul r t (ring_pow r b 2)))`));
    MP_TAC(ISPECL [`k:A ring`; `ring_of_int k a:A`; `ring_of_int k b:A`;
                   `w:A`] (RING_RULE
     `!r a b w:A.
        a IN ring_carrier r /\ b IN ring_carrier r /\ w IN ring_carrier r
        ==> ring_add r (ring_add r a (ring_mul r b w))
                       (ring_add r a (ring_mul r b (ring_sub r (ring_1 r) w))) =
            ring_add r (ring_mul r (ring_of_num r 2) a) b`))] THEN
  ASM_REWRITE_TAC[RING_OF_INT]);;

let QUADRATIC_FIELD_NORM_TRACE_INTEGRAL_BASIS = prove
 (`!k:A ring x d w a b.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 = ring_of_int k d /\
        w = (if (d == &1) (mod &4)
             then ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2)
             else x)
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I
              (ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) w)) =
            ring_of_int k (if (d == &1) (mod &4)
                           then a pow 2 + a * b + ((&1 - d) div &4) * b pow 2
                           else a pow 2 - d * b pow 2) /\
            algebra_trace (subfield_generated k {ring_0 k},k) I
              (ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) w)) =
            ring_of_int k (if (d == &1) (mod &4) then &2 * a + b else &2 * a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`; `a:int`; `b:int`]
      QUADRATIC_FIELD_NORM_TRACE_HALF);
    MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`; `a:int`; `b:int`]
      QUADRATIC_FIELD_NORM_TRACE_SQRT)] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Conjugate ideals.                                                         *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FIELD_IDEAL_MUL_CONJUGATE = prove
 (`!k:A ring s j.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        s IN group_carrier(galois_group(subfield_generated k {ring_0 k},k) I) /\
        ~(s = I) /\
        ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
        ==> ideal_prod (ring_of_integers k) j (IMAGE s j) =
            ideal_generated (ring_of_integers k)
              {ring_of_num k (ideal_norm (ring_of_integers k) j)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` QUADRATIC_FIELD_INTEGER_SQUARE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`w:A`; `m:int`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `w:A`; `s:A->A`] QUADRATIC_FIELD_GALOIS_GROUP) THEN
  ASM_REWRITE_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPEC `k:A ring` QUADRATIC_FIELD_GALOIS_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `j:A->bool`]
    NUMBER_FIELD_GALOIS_PRODUCT_IDEAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `s:A->A`; `j:A->bool`]
    GALOIS_GROUP_RING_OF_INTEGERS_IDEAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_SIMP_TAC[IDEAL_PRODUCT_INSERT; FINITE_SING; IN_SING;
               IDEAL_PRODUCT_SING; IMAGE_I]);;

(* ------------------------------------------------------------------------- *)
(* The prime ideals of the decomposition law.                                *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FIELD_CONJUGATE_PRIME_PAIR = prove
 (`!k:A ring x d s p y.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        s IN group_carrier(galois_group(subfield_generated k {ring_0 k},k) I) /\
        ~(s = I)
        ==> IMAGE s (ideal_generated (ring_of_integers k)
                       {ring_of_num k p, ring_sub k x (ring_of_int k y)}) =
            ideal_generated (ring_of_integers k)
              {ring_of_num k p, ring_add k x (ring_of_int k y)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `s:A->A`] QUADRATIC_FIELD_GALOIS_GROUP) THEN
  ASM_REWRITE_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM] THEN
    MATCH_MP_TAC INTEGRAL_ELEMENT_QUADRATIC THEN
    MAP_EVERY EXISTS_TAC [`&0:int`; `--d:int`] THEN
    ASM_SIMP_TAC[RING_OF_INT_0; RING_MUL_LZERO; RING_ADD_LZERO; RING_NEG;
                 RING_OF_INT; RING_OF_INT_NEG; RING_ADD_RNEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_of_num k p IN ring_carrier(ring_of_integers k) /\
    ring_of_int k y IN ring_carrier(ring_of_integers k) /\
    ring_sub k x (ring_of_int k y) IN ring_carrier(ring_of_integers k) /\
    ring_add k x (ring_of_int k y) IN ring_carrier(ring_of_integers k) /\
    ring_neg k (ring_add k x (ring_of_int k y)) IN
    ring_carrier(ring_of_integers (k:A ring))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `ring_of_integers k:A ring` RING_SUB) THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_ADD) THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_NEG) THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_OF_INT) THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_OF_NUM) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN REPEAT DISCH_TAC THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `s:A->A`;
                 `{ring_of_num k p, ring_sub k x (ring_of_int k y):A}`]
    GALOIS_GROUP_IMAGE_IDEAL_GENERATED) THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IMAGE_CLAUSES] THEN
  SUBGOAL_THEN `ring_homomorphism(k,k) (s:A->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM]; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th]) THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[RING_OF_INT;
    MATCH_MP RING_HOMOMORPHISM_SUB th;
    MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th]) THEN
  SUBGOAL_THEN
   `ring_sub k (ring_neg k x) (ring_of_int k y) =
    ring_neg k (ring_add k x (ring_of_int k y)):A`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `x:A`; `ring_of_int k y:A`] (RING_RULE
     `!r x y:A. x IN ring_carrier r /\ y IN ring_carrier r
                ==> ring_sub r (ring_neg r x) y =
                    ring_neg r (ring_add r x y)`)) THEN
    ASM_REWRITE_TAC[RING_OF_INT];
    ALL_TAC] THEN
  MATCH_MP_TAC IDEAL_GENERATED_PAIR_EQ THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[RING_OF_INTEGERS] (ISPECL
   [`ring_of_integers k:A ring`; `j:A->bool`] IN_RING_IDEAL_NEG)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `ring_add k x (ring_of_int k y) =
                  ring_neg k (ring_neg k (ring_add k x (ring_of_int k y))):A`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_NEG_NEG THEN
      MP_TAC(ISPECL [`k:A ring`; `x:A`; `ring_of_int k y:A`] RING_ADD) THEN
      ASM_REWRITE_TAC[RING_OF_INT];
      ASM_SIMP_TAC[]];
    ASM_SIMP_TAC[]]);;
