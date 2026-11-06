(* ========================================================================= *)
(* Power bases: the index formula and the trace dual basis of the powers.    *)
(*                                                                           *)
(* For a number field k with prime subfield Q = subfield_generated k {ring_0 *)
(* k}, ring of integers O = ring_of_integers k and discriminant d_K =        *)
(* number_field_discriminant k, and an element a of k whose minimal          *)
(* polynomial f = minimal_polynomial (Q,k) I a has degree [k:Q] (so 1, a,    *)
(* ..., a^(n-1) is a Q-basis of k, NUMBER_FIELD_FREE_BASIS_POWERS of         *)
(* ANT/power_basis.ml; this holds when k = Q(a),                             *)
(* NUMBER_FIELD_GENERATOR_MINIMAL_POLYNOMIAL_DEGREE), with Df the derivative *)
(* of f and Z[a] = subring_generated k {a}:                                  *)
(*                                                                           *)
(*  disc(1, a, ..., a^(n-1)) = poly_discriminant Q f                         *)
(*                   (NUMBER_FIELD_POWER_BASIS_POLY_DISCRIMINANT)            *)
(*  poly_discriminant Q f = N^2 d_K, N = [O : Z[a]] for a in O               *)
(*                   (NUMBER_FIELD_POLY_DISCRIMINANT_INDEX, and for a monic  *)
(*                   integer polynomial m of degree [k:Q] with m(a) = 0:     *)
(*                   NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_INTEGER)           *)
(*  disc(m) squarefree ==> Z[a] = O and d_K = disc(m)                        *)
(*                   (NUMBER_FIELD_POLY_DISCRIMINANT_SQUAREFREE)             *)
(*  p^2 not dividing disc(m) ==> O = Z[a] + pO                               *)
(*                   (NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_COPRIME)          *)
(*                                                                           *)
(* Along the way: the trace dual basis of the powers                         *)
(* (NUMBER_FIELD_POWER_BASIS_DUAL, by the Lagrange coefficient sum           *)
(* RING_SUM_LAGRANGE_COEFF of Library/ringtheory.ml), the dual of a          *)
(* lattice spanned by a Q-basis (NUMBER_FIELD_TRACE_DUAL_LATTICE), the       *)
(* coefficients of f = (X - a) b span Z[a] (SUBRING_GENERATED_HORNER_SPAN),  *)
(* Df(a) IN Z[a] (NUMBER_FIELD_MINIMAL_POLYNOMIAL_DERIV_SUBRING) and Z[a] =  *)
(* O implies k = Q(a) (NUMBER_FIELD_SUBRING_GENERATED_EQ_RING_OF_INTEGERS).  *)
(* The codifferent and the different of Z[a] for a in O (Euler:              *)
(* NUMBER_FIELD_CODIFFERENT_POWER_BASIS_Q,                                   *)
(* NUMBER_FIELD_DERIVATIVE_IN_DIFFERENT_Q,                                   *)
(* NUMBER_FIELD_DIFFERENT_POWER_BASIS_Q) are the case k = Q of the relative  *)
(* theorems of ANT/power_basis_extension.ml.                                 *)
(*                                                                           *)
(* Routes. In an algebraic closure l of k                                    *)
(* (ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) the [k:Q] homomorphisms e_t give     *)
(* distinct roots x_t = e_t(a) of the image of f, which is the product of    *)
(* the X - x_t, and e_t(Df(a)) is the product of the x_t - x_s, s <> t; the  *)
(* trace maps to the sum over the e_t                                        *)
(* (NUMBER_FIELD_POWER_BASIS_HOMOMORPHISMS, from ANT/power_basis.ml).        *)
(* Discriminant: the image of the basis discriminant is the square of the    *)
(* Vandermonde determinant of the x_t                                        *)
(* (NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS), that of the polynomial         *)
(* discriminant too (POLY_DISCRIMINANT_VANDERMONDE of Library/ring_det.ml).  *)
(* Index: Z[a] is the Z-span of the powers (SUBRING_GENERATED_INT_LINCOMB of *)
(* ANT/dedekind_kummer.ml) and NUMBER_FIELD_DISCRIMINANT_INDEX of            *)
(* ANT/discriminant.ml applies; a squarefree N^2 d_K forces N = 1, and Z[a]  *)
(* + pO = O iff p does not divide N (SUBRING_GENERATED_INDEX_COPRIME).       *)
(* Euler: with f = (X - a) b over k, e_t maps b to the product of the X -    *)
(* x_s, s <> t, so Tr(a^i b_j / Df(a)) is the coefficient sum of the         *)
(* Lagrange interpolation of X^i at the x_t, that is delta_ij; hence the b_j *)
(* / Df(a) form the trace dual basis of the powers; by the Horner recursion  *)
(* b_(t-1) = f_t + a b_t (with b_(n-1) = 1) the b_j span Z[a] over Z.        *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (polynomials, derivatives, poly_extend,       *)
(* RING_SUM_LAGRANGE_COEFF, COEFF_POLY_MUL_X_MINUS),                         *)
(* Library/fieldtheory.ml (minimal polynomials, algebraic closures,          *)
(* SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC), Library/ring_det.ml (free_basis,    *)
(* algebra_trace, basis_discriminant, poly_discriminant, Vandermonde),       *)
(* ANT/numfield.ml (traces, NUMBER_FIELD_TRACE_FORM_INJECTIVE, integer       *)
(* linear combinations), ANT/ring_of_integers.ml, ANT/discriminant.ml        *)
(* (NUMBER_FIELD_DISCRIMINANT_INDEX), ANT/integrality.ml                     *)
(* (RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q), ANT/dedekind_kummer.ml           *)
(* (SUBRING_GENERATED_INT_LINCOMB, SUBRING_GENERATED_INDEX_COPRIME,          *)
(* RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL) and ANT/power_basis.ml       *)
(* (NUMBER_FIELD_HOMOMORPHISMS_HAS_SIZE, NUMBER_FIELD_FREE_BASIS_POWERS,     *)
(* NUMBER_FIELD_TRACE_HOMOMORPHISMS,                                         *)
(* NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS).                                 *)
(* ========================================================================= *)


needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/ring_det.ml";;
needs "ANT/algmisc.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/discriminant.ml";;
needs "ANT/integrality.ml";;
needs "ANT/dedekind_kummer.ml";;
needs "ANT/power_basis.ml";;

(* ------------------------------------------------------------------------- *)
(* The homomorphisms into an algebraic closure for a power basis.            *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_POWER_BASIS_HOMOMORPHISMS = prove
 (`!(k:A ring) a f m.
        number_field k /\ a IN ring_carrier k /\
        f = minimal_polynomial (subfield_generated k {ring_0 k},k) I a /\
        m = extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_deg (subfield_generated k {ring_0 k}) f = m
        ==> ?(l:(A#num)ring) g e.
              field l /\ ring_monomorphism(k,l) g /\
              (!i. i < m ==> ring_homomorphism(k,l) (e i) /\
                             e i a IN ring_carrier l) /\
              (!i y. i < m /\
                     y IN ring_carrier(subfield_generated k {ring_0 k})
                     ==> e i y = g y) /\
              (!u v. u < m /\ v < m ==> (e u a = e v a <=> u = v)) /\
              g o f =
              ring_product (poly_ring l (:1)) {i | i < m}
                (\i. poly_sub l (poly_var l one) (poly_const l (e i a))) /\
              (!i. i < m
                   ==> e i (poly_extend (subfield_generated k {ring_0 k},k) I
                              (\v. a)
                              (poly_deriv (subfield_generated k {ring_0 k})
                                 f)) =
                       ring_product l ({t | t < m} DELETE i)
                         (\t. ring_sub l (e i a) (e t a))) /\
              (!x. x IN ring_carrier k
                   ==> g(algebra_trace (subfield_generated k {ring_0 k},k) I
                           x) =
                       ring_sum l {i | i < m} (\i. e i x))`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(ASSUME_TAC o SYM o
      check (fun th -> lhs(concl th) = `m:num`)) THEN
    FIRST_X_ASSUM(ASSUME_TAC o SYM o
      check (fun th -> lhs(concl th) = `f:(1->num)->A`)) THEN
    MP_TAC(ISPECL [`k:A ring`; `a:A`] NUMBER_FIELD_FREE_BASIS_POWERS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [number_field]) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
    SUBGOAL_THEN
     `algebraic_over (subfield_generated k {ring_0 k},k) (I:A->A) a /\
      field_extension (subfield_generated k {ring_0 k},k) (I:A->A)`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[NUMBER_FIELD_ALGEBRAIC; FIELD_EXTENSION_SUBFIELD_GENERATED];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_polynomial (subfield_generated k {ring_0 k}) (f:(1->num)->A) /\
      monic (subfield_generated k {ring_0 k}) f`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN
      ASM_SIMP_TAC[RING_POLYNOMIAL; MINIMAL_POLYNOMIAL_IN_CARRIER;
                   MINIMAL_POLYNOMIAL_MONIC];
      ALL_TAC] THEN
    MP_TAC(ISPEC `k:A ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
    ASM_REWRITE_TAC[algebraic_extension; field_extension] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:(A#num)ring` (X_CHOOSE_THEN `g:A->A#num`
      STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    SUBGOAL_THEN `ring_char(l:(A#num)ring) = 0` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_CHAR_MONOMORPHIC_IMAGE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `l:(A#num)ring`]
      NUMBER_FIELD_HOMOMORPHISMS_HAS_SIZE) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC
     `E = {h:A->A#num | ring_homomorphism(k,l) h /\
                        h IN EXTENSIONAL(ring_carrier k)}` THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP HAS_SIZE_INDEX) THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:num->A->A#num` (fun th0 ->
      let th1,th2 = CONJ_PAIR th0 in
      SUBGOAL_THEN
       `!i j. i < m /\ j < m ==> ((e:num->A->A#num) i = e j <=> i = j)`
      ASSUME_TAC THENL [MESON_TAC[th1; th2]; ALL_TAC] THEN
      SUBGOAL_THEN
       `!i. i < m ==> ring_homomorphism(k,l) ((e:num->A->A#num) i) /\
                      e i IN EXTENSIONAL(ring_carrier k)`
      ASSUME_TAC THENL
       [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        MP_TAC(SPEC `i:num` th1) THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "E" THEN SIMP_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      SUBGOAL_THEN `E = IMAGE (e:num->A->A#num) {i | i < m}` SUBST_ALL_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[th1; th2];
        ALL_TAC])) THEN
    SUBGOAL_THEN
     `!i y. i < m /\ y IN ring_carrier(subfield_generated k {ring_0 k})
            ==> (e:num->A->A#num) i y = g y`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`(e:num->A->A#num) i`; `g:A->A#num`; `k:A ring`;
                     `l:(A#num)ring`; `{ring_0 k:A}`]
        RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED) THEN
      ASM_SIMP_TAC[IN_SING; ISPECL [`k:A ring`; `l:(A#num)ring`]
                                   RING_HOMOMORPHISM_0];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!u v. u < m /\ v < m
            ==> ((e:num->A->A#num) u a = e v a <=> u = v)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(e:num->A->A#num) u = e v` MP_TAC THENL
       [ALL_TAC; ASM_SIMP_TAC[]] THEN
      MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC `ring_carrier k:A->bool` THEN
      ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN
       `ring_span (subfield_generated k {ring_0 k},k) I
         (IMAGE (\i. ring_pow k (a:A) i) {i | i < m}) = ring_carrier k`
      ASSUME_TAC THENL
       [ASM_MESON_TAC[FREE_BASIS_FIELD; FIELD_SUBFIELD_GENERATED;
                      RING_HOMOMORPHISM_SUBFIELD_INCLUSION;
                      ring_basis; ring_spanning];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`I:A->A`; `(e:num->A->A#num) u`; `(e:num->A->A#num) v`;
                     `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                     `l:(A#num)ring`;
                     `IMAGE (\i. ring_pow k (a:A) i) {i | i < m}`]
        RING_HOMOMORPHISMS_EQ_FROM_RING_SPAN) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[I_THM; IMP_CONJ_ALT; FORALL_IN_IMAGE; IN_ELIM_THM;
                     ISPECL [`k:A ring`; `l:(A#num)ring`]
                       RING_HOMOMORPHISM_POW];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!i. i < m ==> (e:num->A->A#num) i o (f:(1->num)->A) = g o f`
    ASSUME_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
      X_GEN_TAC `u:1->num` THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC
       `ring_polynomial (subfield_generated k {ring_0 k}) (f:(1->num)->A)` THEN
      SIMP_TAC[ring_polynomial; ring_powerseries];
      ALL_TAC] THEN
    UNDISCH_THEN
     `!i y. i < m /\ y IN ring_carrier(subfield_generated k {ring_0 k})
            ==> (e:num->A->A#num) i y = g y` (K ALL_TAC) THEN
    SUBGOAL_THEN `!i. i < m ==> (e:num->A->A#num) i a IN ring_carrier l`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
      EXISTS_TAC `k:A ring` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_monomorphism(subfield_generated k {ring_0 k},l) (g:A->A#num)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
      ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; FIELD_IMP_NONTRIVIAL_RING] THEN
      MP_TAC(ISPECL [`g:A->A#num`; `k:A ring`; `l:(A#num)ring`;
                     `ring_carrier(subfield_generated k {ring_0 k:A})`]
        RING_HOMOMORPHISM_FROM_SUBRING_GENERATED) THEN
      ASM_REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED];
      FIRST_ASSUM(ASSUME_TAC o
        MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)] THEN
    SUBGOAL_THEN
     `ring_polynomial l ((g:A->A#num) o f) /\ poly_deg l (g o f) = m /\
      monic l (g o f)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC RING_POLYNOMIAL_COMPOSE THEN
        EXISTS_TAC `subfield_generated k {ring_0 k:A}` THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`subfield_generated k {ring_0 k:A}`; `l:(A#num)ring`;
                       `g:A->A#num`; `f:(1->num)->A`]
          POLY_DEG_MONOMORPHIC_IMAGE) THEN
        ASM_REWRITE_TAC[];
        STRIP_TAC THEN UNDISCH_TAC
         `monic (subfield_generated k {ring_0 k}) (f:(1->num)->A)` THEN
        ASM_REWRITE_TAC[monic; COEFF_COMPOSE] THEN DISCH_THEN SUBST1_TAC THEN
        MP_TAC(ISPECL [`subfield_generated k {ring_0 k:A}`; `l:(A#num)ring`;
                       `g:A->A#num`] RING_HOMOMORPHISM_1) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(g:A->A#num) o (f:(1->num)->A) =
      ring_product (poly_ring l (:1)) {i | i < m}
        (\i. poly_sub l (poly_var l one)
                        (poly_const l ((e:num->A->A#num) i a)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MONIC_POLY_EQ_ROOTS_PRODUCT THEN
      ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; GSYM RING_POLYNOMIAL;
                   FINITE_NUMSEG_LT; CARD_NUMSEG_LT; IN_ELIM_THM] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`I:A->A`; `(e:num->A->A#num) i`;
                     `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                     `l:(A#num)ring`; `a:A`]
        MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE) THEN
      ASM_SIMP_TAC[I_O_ID];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!i. i < m
          ==> (e:num->A->A#num) i
                (poly_extend (subfield_generated k {ring_0 k},k) I (\v. a)
                   (poly_deriv (subfield_generated k {ring_0 k}) f)) =
              poly_eval l (poly_deriv l ((g:A->A#num) o (f:(1->num)->A)))
                (e i a)`
    ASSUME_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `ring_homomorphism(subfield_generated k {ring_0 k},l)
                         ((e:num->A->A#num) i)`
      ASSUME_TAC THENL
       [MP_TAC(ISPECL [`(e:num->A->A#num) i`; `k:A ring`; `l:(A#num)ring`;
                       `ring_carrier(subfield_generated k {ring_0 k:A})`]
          RING_HOMOMORPHISM_FROM_SUBRING_GENERATED) THEN
        ASM_SIMP_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED];
        ALL_TAC] THEN
      MP_TAC(ISPECL
       [`subfield_generated k {ring_0 k:A}`; `k:A ring`; `l:(A#num)ring`;
        `I:A->A`; `(:1)`; `\v:1. (a:A)`; `(e:num->A->A#num) i`;
        `poly_deriv (subfield_generated k {ring_0 k:A}) f`]
       POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN
      ASM_SIMP_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION; POLY_DERIV_IN_CARRIER;
                   GSYM RING_POLYNOMIAL; SUBSET; FORALL_IN_IMAGE; I_O_ID] THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[POLY_EXTEND_EVALUATE] THEN REWRITE_TAC[poly_eval] THEN
      BINOP_TAC THENL
       [MP_TAC(ISPECL [`subfield_generated k {ring_0 k:A}`; `l:(A#num)ring`;
                       `(e:num->A->A#num) i`; `f:(1->num)->A`]
          POLY_DERIV_HOMOMORPHIC_IMAGE) THEN
        ASM_SIMP_TAC[RING_POLYNOMIAL_IMP_POWERSERIES];
        REWRITE_TAC[o_DEF]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!i. i < m
          ==> poly_eval l (poly_deriv l ((g:A->A#num) o (f:(1->num)->A)))
                ((e:num->A->A#num) i a) =
              ring_product l ({t | t < m} DELETE i)
                (\t. ring_sub l (e i a) (e t a))`
    ASSUME_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`l:(A#num)ring`; `\t. (e:num->A->A#num) t a`;
                     `{t:num | t < m}`; `i:num`]
        POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS) THEN
      ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `!x. x IN ring_carrier k
          ==> (g:A->A#num)
                (algebra_trace (subfield_generated k {ring_0 k},k) I x) =
              ring_sum l {i | i < m} (\i. (e:num->A->A#num) i x)`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `l:(A#num)ring`;
                     `IMAGE (e:num->A->A#num) {i | i < m}`;
                     `g:A->A#num`; `x:A`] NUMBER_FIELD_TRACE_HOMOMORPHISMS) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[FORALL_IN_IMAGE; SUBSET; IN_ELIM_THM];
        DISCH_THEN SUBST1_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_IMAGE o lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN UNDISCH_TAC
         `!i j. i < m /\ j < m ==> ((e:num->A->A#num) i = e j <=> i = j)` THEN
        MESON_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[o_DEF];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`l:(A#num)ring`; `g:A->A#num`; `e:num->A->A#num`] THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(e:num->A->A#num) i`; `g:A->A#num`; `k:A ring`;
                   `l:(A#num)ring`; `{ring_0 k:A}`]
      RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED) THEN
    ASM_SIMP_TAC[IN_SING; ISPECL [`k:A ring`; `l:(A#num)ring`]
                                 RING_HOMOMORPHISM_0]);;


(* ------------------------------------------------------------------------- *)
(* The discriminant of a power basis and the index formula.                  *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_POWER_BASIS_POLY_DISCRIMINANT = prove
 (`!(k:A ring) a.
        number_field k /\ a IN ring_carrier k /\
        poly_deg (subfield_generated k {ring_0 k})
          (minimal_polynomial (subfield_generated k {ring_0 k},k) I a) =
        extension_degree (subfield_generated k {ring_0 k},k) I
        ==> basis_discriminant (subfield_generated k {ring_0 k},k) I
              (extension_degree (subfield_generated k {ring_0 k},k) I)
              (\i. ring_pow k a i) =
            poly_discriminant (subfield_generated k {ring_0 k})
              (minimal_polynomial (subfield_generated k {ring_0 k},k) I a)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`] NUMBER_FIELD_FREE_BASIS_POWERS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `algebraic_over (subfield_generated k {ring_0 k},k) (I:A->A) a /\
    field_extension (subfield_generated k {ring_0 k},k) (I:A->A)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NUMBER_FIELD_ALGEBRAIC; FIELD_EXTENSION_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  ABBREV_TAC
   `f = minimal_polynomial (subfield_generated k {ring_0 k},k) (I:A->A) a` THEN
  ABBREV_TAC
   `m = extension_degree (subfield_generated k {ring_0 k},k:A ring) I` THEN
  SUBGOAL_THEN
   `f IN ring_carrier(poly_ring (subfield_generated k {ring_0 k}) (:1)) /\
    monic (subfield_generated k {ring_0 k}) (f:(1->num)->A)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN
    ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER; MINIMAL_POLYNOMIAL_MONIC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `f:(1->num)->A`; `m:num`]
    NUMBER_FIELD_POWER_BASIS_HOMOMORPHISMS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(A#num)ring` (X_CHOOSE_THEN `g:A->A#num`
    (X_CHOOSE_THEN `e:num->A->A#num` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `(g:A->A#num) o (f:(1->num)->A)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN
   `ring_monomorphism(subfield_generated k {ring_0 k},l) (g:A->A#num)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; FIELD_IMP_NONTRIVIAL_RING] THEN
    MP_TAC(ISPECL [`g:A->A#num`; `k:A ring`; `l:(A#num)ring`;
                   `ring_carrier(subfield_generated k {ring_0 k:A})`]
      RING_HOMOMORPHISM_FROM_SUBRING_GENERATED) THEN
    ASM_REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED];
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)] THEN
  UNDISCH_TAC `ring_monomorphism(k,l) (g:A->A#num)` THEN
  REWRITE_TAC[ring_monomorphism] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[basis_discriminant] THEN
    MESON_TAC[RING_DET; RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
    MESON_TAC[POLY_DISCRIMINANT_IN_CARRIER;
              RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:(A#num)ring`; `m:num`;
                 `\i. ring_pow k (a:A) i`; `e:num->A->A#num`; `g:A->A#num`]
    NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`g:A->A#num`; `subfield_generated k {ring_0 k:A}`;
                 `l:(A#num)ring`; `f:(1->num)->A`]
    POLY_DISCRIMINANT_HOMOMORPHISM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`subfield_generated k {ring_0 k:A}`; `l:(A#num)ring`;
                   `g:A->A#num`; `f:(1->num)->A`]
      POLY_DEG_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `poly_deg l ((g:A->A#num) o (f:(1->num)->A)) = m`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subfield_generated k {ring_0 k:A}`; `l:(A#num)ring`;
                   `g:A->A#num`; `f:(1->num)->A`]
      POLY_DEG_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(A#num)ring`; `(g:A->A#num) o (f:(1->num)->A)`;
                 `ring_1 l:A#num`; `\i. (e:num->A->A#num) i a`]
    POLY_DISCRIMINANT_VANDERMONDE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_1] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
      MATCH_MP_TAC RING_POLYNOMIAL_COMPOSE THEN
      EXISTS_TAC `subfield_generated k {ring_0 k:A}` THEN
      ASM_REWRITE_TAC[RING_POLYNOMIAL];
      ALL_TAC] THEN
    REWRITE_TAC[POLY_CONST_1] THEN
    REWRITE_TAC[GSYM(ISPECL [`l:(A#num)ring`; `(:1)`]
      (CONJUNCT1(CONJUNCT2(CONJUNCT2 POLY_RING))))] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_MUL_LID THEN
    REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
    MATCH_MP_TAC RING_POLYNOMIAL_COMPOSE THEN
    EXISTS_TAC `subfield_generated k {ring_0 k:A}` THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[RING_POW_ONE] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN
  SUBGOAL_THEN
   `ring_det l {i | i < m} (\i j. (e:num->A->A#num) i (ring_pow k a j)) =
    ring_det l {i | i < m} (\i j. ring_pow l (e i a) j)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `l:(A#num)ring`; `(e:num->A->A#num) i`]
      RING_HOMOMORPHISM_POW) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RING_MUL_LID THEN REWRITE_TAC[RING_DET]);;

(* A generator a of k (k = Q(a)) has a minimal polynomial of degree [k:Q].  *)
let NUMBER_FIELD_GENERATOR_MINIMAL_POLYNOMIAL_DEGREE = prove
 (`!(k:A ring) a.
        number_field k /\ a IN ring_carrier k /\ subfield_generated k {a} = k
        ==> poly_deg (subfield_generated k {ring_0 k})
              (minimal_polynomial (subfield_generated k {ring_0 k},k) I a) =
            extension_degree (subfield_generated k {ring_0 k},k) I`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN
   `algebraic_over (subfield_generated k {ring_0 k},k) (I:A->A) a /\
    field_extension (subfield_generated k {ring_0 k},k) (I:A->A)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NUMBER_FIELD_ALGEBRAIC; FIELD_EXTENSION_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `a:A`] EXTENSION_DEGREE_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `a:A`] SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `subfield_generated k
      (a INSERT IMAGE I (ring_carrier(subfield_generated k {ring_0 k}))) =
    subfield_generated k {a:A}`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[IMAGE_I; SUBFIELD_GENERATED_INSERT] THEN
  MATCH_MP_TAC SUBFIELDS_GENERATED_EQ THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IN_SUBFIELD_0) THEN SET_TAC[]);;

(* The index formula: for an algebraic integer a generating k, the           *)
(* discriminant of the minimal polynomial of a is [O : Z[a]]^2 d_K.          *)
let NUMBER_FIELD_POLY_DISCRIMINANT_INDEX = prove
 (`!(k:A ring) a.
        number_field k /\ a IN ring_carrier(ring_of_integers k) /\
        poly_deg (subfield_generated k {ring_0 k})
          (minimal_polynomial (subfield_generated k {ring_0 k},k) I a) =
        extension_degree (subfield_generated k {ring_0 k},k) I
        ==> ?N. {ring_coset (ring_of_integers k)
                   (ring_carrier(subring_generated k {a})) x |
                 x | x IN ring_carrier(ring_of_integers k)} HAS_SIZE N /\
                poly_discriminant (subfield_generated k {ring_0 k})
                  (minimal_polynomial (subfield_generated k {ring_0 k},k) I
                     a) =
                ring_of_int k (&N pow 2 * number_field_discriminant k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`]
    RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(1->num)->int` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `q:(1->num)->int`]
    SUBRING_GENERATED_INT_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`;
                 `extension_degree
                    (subfield_generated k {ring_0 k},k:A ring) I`;
                 `\i. ring_pow k (a:A) i`;
                 `ring_carrier(subring_generated k {a:A})`]
    NUMBER_FIELD_DISCRIMINANT_INDEX) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[NUMBER_FIELD_FREE_BASIS_POWERS] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `a:A`; `i:num`]
      RING_POW) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N:num` THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && is_comb(rhs(concl th)) &&
    fst(strip_comb(rhs(concl th))) = `ring_of_int:(A ring)->int->A`)) THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC NUMBER_FIELD_POWER_BASIS_POLY_DISCRIMINANT THEN
  ASM_REWRITE_TAC[]);;

(* The same over Z, for a monic integer polynomial m of degree [k:Q] with    *)
(* m(a) = 0 and k = Q(a).                                                    *)
let NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_INTEGER = prove
 (`!(k:A ring) a m.
        number_field k /\ a IN ring_carrier k /\
        subfield_generated k {a} = k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_deg integer_ring m =
        extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k
        ==> ?N. {ring_coset (ring_of_integers k)
                   (ring_carrier(subring_generated k {a})) x |
                 x | x IN ring_carrier(ring_of_integers k)} HAS_SIZE N /\
                poly_discriminant integer_ring m =
                &N pow 2 * number_field_discriminant k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM; integral_element] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`]
    NUMBER_FIELD_GENERATOR_MINIMAL_POLYNOMIAL_DEGREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`] NUMBER_FIELD_POLY_DISCRIMINANT_INDEX) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `algebraic_over (subfield_generated k {ring_0 k},k) (I:A->A) a /\
    field_extension (subfield_generated k {ring_0 k},k) (I:A->A)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NUMBER_FIELD_ALGEBRAIC; FIELD_EXTENSION_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_monomorphism(integer_ring,subfield_generated k {ring_0 k})
                     (ring_of_int k:int->A)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ring_monomorphism; INTEGER_RING; IN_UNIV] THEN
    ASM_SIMP_TAC[RING_OF_INT_EQ_CHAR_0] THEN
    MP_TAC(ISPEC `subfield_generated k {ring_0 k:A}`
      RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN
    REWRITE_TAC[RING_OF_INT_SUBFIELD_GENERATED];
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)] THEN
  SUBGOAL_THEN
   `(ring_of_int k:int->A) o m IN
    ring_carrier(poly_ring (subfield_generated k {ring_0 k}) (:1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
    MATCH_MP_TAC RING_POLYNOMIAL_COMPOSE THEN
    EXISTS_TAC `integer_ring` THEN ASM_REWRITE_TAC[RING_POLYNOMIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `poly_extend (subfield_generated k {ring_0 k},k) I (\v:1. a)
      ((ring_of_int k:int->A) o (m:(1->num)->int)) = ring_0 k`
  ASSUME_TAC THENL
   [FIRST_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o
      check (fun th -> is_eq(concl th) && rand(concl th) = `ring_0 k:A` &&
                       is_comb(lhs(concl th)) &&
                       rand(lhs(concl th)) = `m:(1->num)->int`)) THEN
    SIMP_TAC[POLY_EXTEND_EVALUATE; RING_HOMOMORPHISM_SUBFIELD_INCLUSION;
             RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN
    REWRITE_TAC[I_O_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `minimal_polynomial (subfield_generated k {ring_0 k},k) I a =
    (ring_of_int k:int->A) o m`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`integer_ring`; `subfield_generated k {ring_0 k:A}`;
                   `ring_of_int k:int->A`; `m:(1->num)->int`]
      MONIC_HOMOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING; FIELD_SUBFIELD_GENERATED] THEN
    STRIP_TAC THEN MATCH_MP_TAC MONIC_DIVIDES_EQ THEN
    EXISTS_TAC `subfield_generated k {ring_0 k:A}` THEN
    ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_MONIC; MINIMAL_POLYNOMIAL_DIVIDES] THEN
    ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_int k:int->A`; `integer_ring`;
                 `subfield_generated k {ring_0 k:A}`; `m:(1->num)->int`]
    POLY_DISCRIMINANT_HOMOMORPHISM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`integer_ring`; `subfield_generated k {ring_0 k:A}`;
                   `ring_of_int k:int->A`; `m:(1->num)->int`]
      POLY_DEG_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && is_comb(lhs(concl th)) &&
    rator(lhs(concl th)) = `minimal_polynomial
      (subfield_generated k {ring_0 k},k) (I:A->A)`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    is_eq(concl th) && is_comb(lhs(concl th)) &&
    fst(strip_comb(lhs(concl th))) =
    `poly_discriminant:(A ring)->((1->num)->A)->A`)) THEN
  ASM_SIMP_TAC[RING_OF_INT_EQ_CHAR_0]);;

(* If the discriminant of m is squarefree then Z[a] = O and d_K = disc(m).    *)
let NUMBER_FIELD_POLY_DISCRIMINANT_SQUAREFREE = prove
 (`!(k:A ring) a m.
        number_field k /\ a IN ring_carrier k /\
        subfield_generated k {a} = k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_deg integer_ring m =
        extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
        squarefree(num_of_int(abs(poly_discriminant integer_ring m)))
        ==> ring_carrier(subring_generated k {a}) =
            ring_carrier(ring_of_integers k) /\
            number_field_discriminant k = poly_discriminant integer_ring m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `m:(1->num)->int`]
    NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_INTEGER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `N = 1` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [squarefree] o
      check (fun th -> fst(strip_comb(concl th)) = `squarefree`)) THEN
    ASM_REWRITE_TAC[INT_ABS_MUL; INT_ABS_POW; INT_ABS_NUM] THEN
    SIMP_TAC[NUM_OF_INT_MUL; INT_POS; INT_ABS_POS; INT_OF_NUM_POW;
             NUM_OF_INT_OF_NUM] THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_POW_ONE; INT_MUL_LID] THEN
  SUBGOAL_THEN
   `ring_carrier(subring_generated k {a:A}) SUBSET
    ring_carrier(ring_of_integers k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
    REWRITE_TAC[RING_OF_INTEGERS_SUBRING; SING_SUBSET] THEN
    REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM; integral_element] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  UNDISCH_TAC
   `{ring_coset (ring_of_integers k)
                (ring_carrier(subring_generated k {a:A}))
                x | x | x IN ring_carrier(ring_of_integers k)} HAS_SIZE 1` THEN
  REWRITE_TAC[ONE; HAS_SIZE_CLAUSES; HAS_SIZE_0; UNWIND_THM2;
              NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:A->bool`) THEN
  SUBGOAL_THEN `ring_0 k IN ring_carrier(ring_of_integers k:A ring)`
  ASSUME_TAC THENL
   [MESON_TAC[RING_0; RING_OF_INTEGERS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_coset (ring_of_integers k)
      (ring_carrier(subring_generated k {a:A})) x =
    ring_coset (ring_of_integers k)
      (ring_carrier(subring_generated k {a})) (ring_0 k)`
  MP_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!(f:A->A->bool) s u v c.
        {f y | y | y IN s} = {c} /\ u IN s /\ v IN s ==> f u = f v`) THEN
    MAP_EVERY EXISTS_TAC
     [`ring_carrier(ring_of_integers k:A ring)`; `c:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_carrier(subring_generated k {a:A}) subring_of ring_of_integers k`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `{a:A}`] SUBRING_SUBRING_GENERATED) THEN
    REWRITE_TAC[subring_of; RING_OF_INTEGERS] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_COSET_EQ] THEN REWRITE_TAC[RING_OF_INTEGERS] THEN
  SUBGOAL_THEN `(x:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_SUB_RZERO]);;

(* If p^2 does not divide disc(m) then p does not divide [O : Z[a]], i.e.    *)
(* Z[a] + pO = O, the hypothesis of DEDEKIND_KUMMER_Q.                       *)
let NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_COPRIME = prove
 (`!(k:A ring) a m p.
        number_field k /\ a IN ring_carrier k /\
        subfield_generated k {a} = k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_deg integer_ring m =
        extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
        prime p /\ ~(&p pow 2 divides poly_discriminant integer_ring m)
        ==> ring_setadd (ring_of_integers k)
              (ring_carrier(subring_generated k {a}))
              (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
            ring_carrier(ring_of_integers k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `m:(1->num)->int`]
    NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_INTEGER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `p:num`; `N:num`]
    SUBRING_GENERATED_INDEX_COPRIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM;
                    integral_element] THEN
    ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `~(&p pow 2 divides poly_discriminant integer_ring m)` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(p:num) divides N` THEN
  REWRITE_TAC[num_divides] THEN CONV_TAC INTEGER_RULE);;


(* ------------------------------------------------------------------------- *)
(* The trace dual basis of the powers (Euler) and dual lattices.             *)
(* ------------------------------------------------------------------------- *)

(* Euler: for a generator a of k with minimal polynomial f and f = (X - a) b *)
(* over k, the trace dual basis of 1, a, ..., a^(m-1) is coeff_j(b) / Df(a). *)
(* In an algebraic closure the conjugates x_t of a give e_t(b) = the product *)
(* F_t of the X - x_s, s <> t, and e_t(Df(a)) = F_t(x_t), so the trace is   *)
(* the Lagrange coefficient sum RING_SUM_LAGRANGE_COEFF.                    *)
let NUMBER_FIELD_POWER_BASIS_DUAL = prove
 (`!(k:A ring) a f m d b.
        number_field k /\ a IN ring_carrier k /\
        f = minimal_polynomial (subfield_generated k {ring_0 k},k) I a /\
        m = extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_deg (subfield_generated k {ring_0 k}) f = m /\
        d = poly_extend (subfield_generated k {ring_0 k},k) I (\v. a)
              (poly_deriv (subfield_generated k {ring_0 k}) f) /\
        b IN ring_carrier(poly_ring k (:1)) /\
        f = poly_mul k (poly_sub k (poly_var k one) (poly_const k a)) b
        ==> ~(d = ring_0 k) /\
            !i j. i < m /\ j < m
                  ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                        (ring_mul k (ring_inv k d)
                           (ring_mul k (ring_pow k a i) (coeff j b))) =
                      if j = i then ring_1 k else ring_0 k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `f:(1->num)->A` &&
    can (term_match [] `poly_mul k p q:(1->num)->A`) (rhs(concl th)))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o
    check (fun th -> lhs(concl th) = `d:A`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o
    check (fun th -> lhs(concl th) = `m:num`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o
    check (fun th -> lhs(concl th) = `f:(1->num)->A`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `ring_polynomial k (b:(1->num)->A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_POLYNOMIAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_polynomial (subfield_generated k {ring_0 k}) (f:(1->num)->A)`
  ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL; MINIMAL_POLYNOMIAL_IN_CARRIER;
                 NUMBER_FIELD_ALGEBRAIC; FIELD_EXTENSION_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `f:(1->num)->A`; `m:num`]
    NUMBER_FIELD_POWER_BASIS_HOMOMORPHISMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(A#num)ring` (X_CHOOSE_THEN `g:A->A#num`
    (X_CHOOSE_THEN `e:num->A->A#num` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `(g:A->A#num) o (f:(1->num)->A)`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `poly_deriv:(A ring)->((1->num)->A)->((1->num)->A)`))
      (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN o
    check (fun th -> concl th = `field(l:(A#num)ring)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_NONTRIVIAL_RING o
    check (fun th -> concl th = `field(l:(A#num)ring)`)) THEN
  SUBGOAL_THEN `0 < m` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_DEGREE_POS) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:A) IN ring_carrier k` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[POLY_EXTEND]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t < m
        ==> ~((e:num->A->A#num) t d = ring_0 l) /\
            e t d = ring_product l ({s | s < m} DELETE t)
                      (\s. ring_sub l (e t a) (e s a))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_PRODUCT_EQ_0; FINITE_DELETE;
                 FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[IN_DELETE; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `s:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`l:(A#num)ring`; `(e:num->A->A#num) t a`;
                   `(e:num->A->A#num) s a`] RING_SUB_EQ_0) THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=)
        `ring_product:((A#num)ring)->(num->bool)->(num->A#num)->A#num`))
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:A ring`; `l:(A#num)ring`; `(e:num->A->A#num) 0`]
      RING_HOMOMORPHISM_0) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t < m
        ==> (e:num->A->A#num) t o (b:(1->num)->A) =
            ring_product (poly_ring l (:1)) ({s | s < m} DELETE t)
              (\s. poly_sub l (poly_var l one) (poly_const l (e s a)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ring_homomorphism(k,l) ((e:num->A->A#num) t)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(e:num->A->A#num) t a IN ring_carrier l` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    EXISTS_TAC `poly_ring l (:1):((1->num)->A#num)ring` THEN
    EXISTS_TAC `poly_sub l (poly_var l one)
                  (poly_const l ((e:num->A->A#num) t a))` THEN
    ASM_REWRITE_TAC[INTEGRAL_DOMAIN_POLY_RING] THEN
    REWRITE_TAC[RING_PRODUCT; GSYM RING_POLYNOMIAL] THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_VAR;
                 RING_POLYNOMIAL_CONST] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[POLY_RING_CLAUSES] THEN MATCH_MP_TAC MONIC_IMP_NONZERO THEN
      ASM_SIMP_TAC[MONIC_X_MINUS_A; RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_VAR;
                   RING_POLYNOMIAL_CONST];
      MATCH_MP_TAC RING_POLYNOMIAL_COMPOSE THEN EXISTS_TAC `k:A ring` THEN
      ASM_REWRITE_TAC[RING_POLYNOMIAL];
      ALL_TAC] THEN
    REWRITE_TAC[POLY_RING_CLAUSES] THEN
    TRANS_TAC EQ_TRANS `(e:num->A->A#num) t o (f:(1->num)->A)` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
        [SYM th]) o check (fun th -> is_eq(concl th) &&
          rhs(concl th) = `f:(1->num)->A` &&
          can (term_match [] `poly_mul k p q:(1->num)->A`)
              (lhs(concl th)))) THEN
      MP_TAC(ISPECL [`k:A ring`; `l:(A#num)ring`; `(e:num->A->A#num) t`;
                     `poly_sub k (poly_var k one) (poly_const k (a:A))`;
                     `b:(1->num)->A`] POLY_COMPOSE_HOMOMORPHISM_MUL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
        MATCH_MP_TAC RING_POLYNOMIAL_IMP_POWERSERIES THEN
        ASM_SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_VAR;
                     RING_POLYNOMIAL_CONST] THEN
        ASM_REWRITE_TAC[RING_POLYNOMIAL];
        DISCH_THEN SUBST1_TAC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `l:(A#num)ring`; `(e:num->A->A#num) t`;
                     `poly_var k one:(1->num)->A`;
                     `poly_const k (a:A):(1->num)->A`]
        POLY_COMPOSE_HOMOMORPHISM_SUB) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[RING_POWERSERIES_VAR; RING_POWERSERIES_CONST];
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[MATCH_MP POLY_COMPOSE_HOMOMORPHISM_VAR
        (ASSUME `ring_homomorphism(k,l) ((e:num->A->A#num) t)`)] THEN
      REWRITE_TAC[MATCH_MP POLY_COMPOSE_HOMOMORPHISM_CONST
        (CONJ (ASSUME `ring_homomorphism(k,l) ((e:num->A->A#num) t)`)
              (ASSUME `(a:A) IN ring_carrier k`))];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS `(g:A->A#num) o (f:(1->num)->A)` THEN CONJ_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `u:1->num` THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `ring_polynomial (subfield_generated k {ring_0 k}) (f:(1->num)->A)` THEN
      SIMP_TAC[ring_polynomial; ring_powerseries];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `(g:A->A#num) o (f:(1->num)->A)`)) THEN
    MP_TAC(ISPECL [`poly_ring l (:1):((1->num)->A#num)ring`;
                   `\s. poly_sub l (poly_var l one)
                          (poly_const l ((e:num->A->A#num) s a))`;
                   `{s:num | s < m}`; `t:num`] RING_PRODUCT_DELETE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; GSYM RING_POLYNOMIAL;
                   RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_VAR;
                   RING_POLYNOMIAL_CONST];
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[POLY_RING_CLAUSES]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_mul k (ring_inv k d)
      (ring_mul k (ring_pow k a i) (coeff j (b:(1->num)->A))) IN
    ring_carrier k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RING_MUL THEN
    ASM_SIMP_TAC[RING_INV; RING_MUL; RING_POW; COEFF_IN_CARRIER_ALT];
    ALL_TAC] THEN
  UNDISCH_TAC `ring_monomorphism(k,l) (g:A->A#num)` THEN
  REWRITE_TAC[ring_monomorphism] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER;
              RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
    COND_CASES_TAC THEN REWRITE_TAC[RING_0; RING_1];
    ALL_TAC] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th
   (ASSUME `ring_mul k (ring_inv k d) (ring_mul k (ring_pow k a i)
              (coeff j (b:(1->num)->A))) IN ring_carrier (k:A ring)`)]) o
    check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `algebra_trace:(A ring#A ring)->(A->A)->A->A`))
          (concl th))) THEN
  MP_TAC(ISPECL [`l:(A#num)ring`; `\t. (e:num->A->A#num) t a`; `m:num`;
                 `i:num`; `j:num`] RING_SUM_LAGRANGE_COEFF) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(g:A->A#num) (if j:num = i then ring_1 k else ring_0 k) =
    if j = i then ring_1 (l:(A#num)ring) else ring_0 l`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN
    ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_0
                  (ASSUME `ring_homomorphism(k,l) (g:A->A#num)`);
                 MATCH_MP RING_HOMOMORPHISM_1
                  (ASSUME `ring_homomorphism(k,l) (g:A->A#num)`)];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `t:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `ring_homomorphism(k,l) ((e:num->A->A#num) t)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `coeff j (b:(1->num)->A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(e:num->A->A#num) t (coeff j b) =
    coeff j (ring_product (poly_ring l (:1)) ({s | s < m} DELETE t)
               (\s. poly_sub l (poly_var l one) (poly_const l (e s a))))`
  ASSUME_TAC THENL
   [FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `t:num < m`))]) o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `b:(1->num)->A`)) (concl th))) THEN
    REWRITE_TAC[COEFF_COMPOSE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
                (ASSUME `ring_homomorphism(k,l) ((e:num->A->A#num) t)`);
               MATCH_MP RING_HOMOMORPHISM_POW
                (ASSUME `ring_homomorphism(k,l) ((e:num->A->A#num) t)`);
               MATCH_MP (MATCH_MP FIELD_HOMOMORPHISM_INV
                 (CONJ (ASSUME `field(k:A ring)`)
                   (ASSUME `ring_homomorphism(k,l) ((e:num->A->A#num) t)`)))
                 (ASSUME `(d:A) IN ring_carrier k`);
               RING_INV; RING_POW; RING_MUL] THEN
  REWRITE_TAC[ring_div] THEN
  MATCH_MP_TAC(RING_RULE
   `ring_mul r u (ring_mul r v w) = ring_mul r (ring_mul r v u) (w:B)`) THEN
  ASM_SIMP_TAC[RING_INV; RING_POW; RING_PRODUCT; COEFF_IN_CARRIER_ALT;
               RING_POLYNOMIAL]);;

(* The trace dual of the lattice spanned by a Q-basis w is the lattice       *)
(* spanned by the trace dual basis w* (Tr(w_i w*_j) = delta_ij).            *)
let NUMBER_FIELD_TRACE_DUAL_LATTICE = prove
 (`!k:A ring n w w'.
        number_field k /\
        free_basis (subfield_generated k {ring_0 k},k) I n w /\
        (!j. j < n ==> w' j IN ring_carrier k) /\
        (!i j. i < n /\ j < n
               ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                     (ring_mul k (w i) (w' j)) =
                   if i = j then ring_1 k else ring_0 k)
        ==> {x | x IN ring_carrier k /\
                 !c. algebra_trace (subfield_generated k {ring_0 k},k) I
                       (ring_mul k x
                          (ring_sum k {i | i < n}
                             (\i. ring_mul k (ring_of_int k (c i)) (w i)))) IN
                     ring_carrier(ring_of_integers k)} =
            {ring_sum k {i | i < n}
               (\i. ring_mul k (ring_of_int k (c i)) (w' i)) |
             c IN (:num->int)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  SUBGOAL_THEN
   `!x (c:num->int).
        x IN ring_carrier k
        ==> algebra_trace (subfield_generated k {ring_0 k},k) I
              (ring_mul k x
                 (ring_sum k {i | i < n}
                    (\i. ring_mul k (ring_of_int k (c i)) ((w:num->A) i)))) =
            ring_sum k {i | i < n}
              (\i. ring_mul k (ring_of_int k (c i))
                     (algebra_trace (subfield_generated k {ring_0 k},k) I
                        (ring_mul k x (w i))))`
  (LABEL_TAC "lin") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_TRACE_MUL_LINCOMB THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM;
                 RING_OF_INT_IN_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c i. i < n
          ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                (ring_mul k
                   (ring_sum k {j | j < n}
                      (\j. ring_mul k (ring_of_int k (c j)) ((w':num->A) j)))
                   ((w:num->A) i)) =
              ring_of_int k (c i)`
  (LABEL_TAC "dual") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `ring_mul k
        (ring_sum k {j | j < n}
           (\j. ring_mul k (ring_of_int k (c j)) ((w':num->A) j)))
        ((w:num->A) i) =
      ring_mul k (w i)
        (ring_sum k {j | j < n}
           (\j. ring_mul k (ring_of_int k (c j)) (w' j)))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[RING_SUM]; ALL_TAC] THEN
    ASM_SIMP_TAC[NUMBER_FIELD_TRACE_MUL_LINCOMB; FINITE_NUMSEG_LT;
                 IN_ELIM_THM; RING_OF_INT_IN_SUBFIELD_GENERATED] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum k {j | j < n}
        (\j. if j = i then ring_of_int k ((c:num->int) i)
             else ring_0 (k:A ring))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[RING_MUL_RID; RING_MUL_RZERO; RING_OF_INT] THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[RING_SUM_DELTA; IN_ELIM_THM; RING_OF_INT]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN
     `!i. i < n
          ==> ?m. algebra_trace (subfield_generated k {ring_0 k},k) I
                    (ring_mul k x ((w:num->A) i)) = ring_of_int k m`
    MP_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `ring_mul k x ((w:num->A) i)`]
        NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS) THEN
      ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `\j:num. if j = i then &1:int else &0`) THEN
      MATCH_MP_TAC(MESON[] `(a:A) = b ==> a IN s ==> b IN s`) THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      TRANS_TAC EQ_TRANS
       `ring_sum k {j | j < n} (\j. if j = i then (w:num->A) i
                                    else ring_0 k)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:num` THEN
        REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
        REWRITE_TAC[] THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[RING_OF_INT_1; RING_OF_INT_0; RING_MUL_LID;
                     RING_MUL_LZERO];
        ASM_SIMP_TAC[RING_SUM_DELTA; IN_ELIM_THM]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
    DISCH_THEN(X_CHOOSE_TAC `c:num->int`) THEN EXISTS_TAC `c:num->int` THEN
    MATCH_MP_TAC NUMBER_FIELD_TRACE_FORM_INJECTIVE THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `n:num`; `w:num->A`] THEN
    ASM_SIMP_TAC[RING_SUM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ring_mul k ((w:num->A) i) x = ring_mul k x (w i)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_mul k ((w:num->A) i)
        (ring_sum k {j | j < n}
           (\j. ring_mul k (ring_of_int k (c j)) ((w':num->A) j))) =
      ring_mul k
        (ring_sum k {j | j < n}
           (\j. ring_mul k (ring_of_int k (c j)) (w' j))) (w i)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[RING_SUM]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `c:num->int` SUBST1_TAC) THEN
    REWRITE_TAC[RING_SUM] THEN X_GEN_TAC `e:num->int` THEN
    USE_THEN "lin" (fun th -> SIMP_TAC[th; RING_SUM]) THEN
    MATCH_MP_TAC(MESON[RING_OF_INT_IN_RING_OF_INTEGERS]
     `!y m. y = ring_of_int k m
            ==> y IN ring_carrier(ring_of_integers (k:A ring))`) THEN
    EXISTS_TAC `isum {i | i < n} (\i. (e:num->int) i * c i)` THEN
    SIMP_TAC[RING_OF_INT_ISUM; FINITE_NUMSEG_LT; RING_OF_INT_MUL] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN
    REMOVE_THEN "dual" (MP_TAC o SPECL [`c:num->int`; `i:num`]) THEN
    ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Z[a]: the Horner span, Df(a) IN Z[a], and Z[a] = O implies k = Q(a).      *)
(* ------------------------------------------------------------------------- *)

(* If f = (X - a) b is monic of degree m with integer coefficients and Z[a]  *)
(* is spanned by 1, a, ..., a^(m-1), then the coefficients b_0, ..., b_(m-1) *)
(* of b also span Z[a] over Z (Horner: b_(m-1) = 1, b_(t-1) = c_t + a b_t). *)
let SUBRING_GENERATED_HORNER_SPAN = prove
 (`!(k:A ring) a f b m.
        ~trivial_ring k /\ a IN ring_carrier k /\
        ring_polynomial k f /\ monic k f /\ poly_deg k f = m /\
        (!i. ?n. coeff i f = ring_of_int k n) /\
        ring_polynomial k b /\
        f = poly_mul k (poly_sub k (poly_var k one) (poly_const k a)) b /\
        ring_carrier(subring_generated k {a}) =
        {ring_sum k {i | i < m}
           (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k a i)) |
         c IN (:num->int)}
        ==> ring_carrier(subring_generated k {a}) =
            {ring_sum k {j | j < m}
               (\j. ring_mul k (ring_of_int k (c j)) (coeff j b)) |
             c IN (:num->int)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `f:(1->num)->A` &&
    is_comb(rhs(concl th)))) THEN
  SUBGOAL_THEN
   `!t. coeff t (f:(1->num)->A) =
        ring_sub k (if t = 0 then ring_0 k else coeff (t - 1) b)
                   (ring_mul k a (coeff t b))`
  ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `f:(1->num)->A`)) THEN
    MATCH_MP_TAC COEFF_POLY_MUL_X_MINUS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(b = poly_0 k:(1->num)->A)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `monic k (f:(1->num)->A)` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `f:(1->num)->A`)) THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th ->
      concl th = `b = poly_0 k:(1->num)->A`)) THEN
    SIMP_TAC[POLY_MUL_0; RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_VAR;
             RING_POLYNOMIAL_CONST; MONIC_POLY_0;
             ASSUME `(a:A) IN ring_carrier k`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `poly_deg k (b:(1->num)->A) + 1 = m` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `a:A`; `b:(1->num)->A`]
      POLY_DEG_MUL_X_MINUS_A) THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `f:(1->num)->A`)) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. m <= t ==> coeff t (b:(1->num)->A) = ring_0 k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COEFF_ABOVE_DEG THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. coeff t (b:(1->num)->A) IN ring_carrier k`
  ASSUME_TAC THENL [ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT]; ALL_TAC] THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `coeff (m - 1) (b:(1->num)->A) = ring_1 k` ASSUME_TAC THENL
   [UNDISCH_TAC `monic k (f:(1->num)->A)` THEN
    ASM_REWRITE_TAC[monic] THEN
    ASM_SIMP_TAC[LE_REFL; RING_MUL_RZERO; RING_SUB_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. 1 <= t /\ t < m
        ==> coeff (t - 1) (b:(1->num)->A) =
            ring_add k (coeff t f) (ring_mul k a (coeff t b))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(RING_RULE `ring_add r (ring_sub r x y) y = (x:A)`) THEN
    ASM_SIMP_TAC[RING_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul k a (coeff 0 (b:(1->num)->A)) = ring_neg k (coeff 0 f)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC(RING_RULE
     `ring_neg r (ring_sub r (ring_0 r) y) = (y:A)`) THEN
    ASM_SIMP_TAC[RING_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t0 x. t0 < m
           ==> ring_sum k {t | t < m}
                 (\t. ring_mul k (ring_of_int k (if t = t0 then x else &0))
                                 (coeff t (b:(1->num)->A))) =
               ring_mul k (ring_of_int k x) (coeff t0 b)`
  (LABEL_TAC "delta") THENL
   [REPEAT STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `ring_sum k {t | t < m}
        (\t. if t = t0 then ring_mul k (ring_of_int k x)
                              (coeff t0 (b:(1->num)->A))
             else ring_0 k)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `t:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[RING_OF_INT_0; RING_MUL_LZERO];
      ASM_SIMP_TAC[RING_SUM_DELTA; IN_ELIM_THM; RING_MUL; RING_OF_INT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ?e. ring_of_int k n =
            ring_sum k {t | t < m}
              (\t. ring_mul k (ring_of_int k (e t))
                     (coeff t (b:(1->num)->A)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:int` THEN
    EXISTS_TAC `\t:num. if t = m - 1 then (n:int) else &0` THEN
    USE_THEN "delta" (fun th ->
      ASM_SIMP_TAC[th; ARITH_RULE `~(m = 0) ==> m - 1 < m`]) THEN
    ASM_SIMP_TAC[RING_MUL_RID; RING_OF_INT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < m
        ==> ?e. ring_mul k a (coeff j (b:(1->num)->A)) =
                ring_sum k {t | t < m}
                  (\t. ring_mul k (ring_of_int k (e t)) (coeff t b))`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(X_CHOOSE_TAC `n:int` o SPEC `j:num` o check (fun th ->
      is_forall(concl th) && is_exists(snd(dest_forall(concl th))) &&
      can (find_term ((=) `f:(1->num)->A`)) (concl th))) THEN
    ASM_CASES_TAC `j = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM RING_OF_INT_NEG] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_mul k a (coeff j (b:(1->num)->A)) =
      ring_sub k (coeff (j - 1) b) (ring_of_int k n)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `ring_add:(A ring)->A->A->A`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC(RING_RULE `ring_sub r (ring_add r x y) x = (y:A)`) THEN
      ASM_SIMP_TAC[RING_MUL; RING_OF_INT];
      ALL_TAC] THEN
    EXISTS_TAC `\t:num. (if t = j - 1 then &1 else &0) -
                        (if t = m - 1 then (n:int) else &0)` THEN
    MP_TAC(ISPECL [`k:A ring`; `{t:num | t < m}`;
                   `\t:num. coeff t (b:(1->num)->A)`] RING_INT_LINCOMB) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]) THEN
    SUBGOAL_THEN `j - 1 < m /\ m - 1 < m` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "delta" (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_SIMP_TAC[RING_OF_INT_1; RING_MUL_LID; RING_MUL_RID; RING_OF_INT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. ?c. ring_pow k a i =
            ring_sum k {t | t < m}
              (\t. ring_mul k (ring_of_int k (c t))
                     (coeff t (b:(1->num)->A)))`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[ring_pow; GSYM RING_OF_INT_1] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ring_pow] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `c:num->int` SUBST1_TAC) THEN
      ASM_SIMP_TAC[RING_MUL_INT_LINCOMB; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
      MATCH_MP_TAC RING_INT_LINCOMB_LINCOMB THEN
      ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!d. d < m ==> coeff (m - 1 - d) (b:(1->num)->A) IN
                  ring_carrier(subring_generated k {a})`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [DISCH_TAC THEN REWRITE_TAC[SUB_0] THEN
      FIRST_ASSUM(SUBST1_TAC o check (fun th ->
        concl th = `coeff (m - 1) (b:(1->num)->A) = ring_1 k`)) THEN
      MATCH_MP_TAC IN_SUBRING_1 THEN REWRITE_TAC[SUBRING_SUBRING_GENERATED];
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN `m - 1 - SUC d = (m - 1 - d) - 1` SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `m - 1 - d` o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `ring_add:(A ring)->A->A->A`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      FIRST_ASSUM(X_CHOOSE_THEN `n:int` SUBST1_TAC o SPEC `m - 1 - d` o
        check (fun th -> is_forall(concl th) &&
          is_exists(snd(dest_forall(concl th))) &&
          can (find_term ((=) `f:(1->num)->A`)) (concl th))) THEN
      MATCH_MP_TAC IN_SUBRING_ADD THEN
      REWRITE_TAC[SUBRING_SUBRING_GENERATED] THEN CONJ_TAC THENL
       [MATCH_MP_TAC IN_SUBRING_INT THEN
        REWRITE_TAC[SUBRING_SUBRING_GENERATED];
        MATCH_MP_TAC IN_SUBRING_MUL THEN
        REWRITE_TAC[SUBRING_SUBRING_GENERATED] THEN
        CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
        MATCH_MP_TAC SUBRING_GENERATED_INC THEN
        ASM_REWRITE_TAC[SING_SUBSET; IN_SING]]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:A` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EQ_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num->int` SUBST1_TAC) THEN
    MATCH_MP_TAC RING_INT_LINCOMB_LINCOMB THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    DISCH_THEN(X_CHOOSE_THEN `c:num->int` SUBST1_TAC) THEN
    MATCH_MP_TAC IN_SUBRING_SUM THEN
    REWRITE_TAC[SUBRING_SUBRING_GENERATED; IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC IN_SUBRING_MUL THEN
    REWRITE_TAC[SUBRING_SUBRING_GENERATED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC IN_SUBRING_INT THEN REWRITE_TAC[SUBRING_SUBRING_GENERATED];
      FIRST_X_ASSUM(MP_TAC o SPEC `m - 1 - j` o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `subring_generated:(A ring)->(A->bool)->A ring`))
          (concl th) && is_imp(snd(dest_forall(concl th))))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `m - 1 - (m - 1 - j) = j` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[]]]]);;

(* For an algebraic integer a, the value Df(a) of the derivative of its     *)
(* minimal polynomial lies in Z[a].                                          *)
let NUMBER_FIELD_MINIMAL_POLYNOMIAL_DERIV_SUBRING = prove
 (`!(k:A ring) a.
        number_field k /\ a IN ring_carrier(ring_of_integers k)
        ==> poly_extend (subfield_generated k {ring_0 k},k) I (\v. a)
              (poly_deriv (subfield_generated k {ring_0 k})
                 (minimal_polynomial (subfield_generated k {ring_0 k},k) I a))
            IN ring_carrier(subring_generated k {a})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. ?n. coeff i (minimal_polynomial (subfield_generated k {ring_0 k},k) I
                       (a:A)) = ring_of_int k n`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `a:A`]
      RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `f = minimal_polynomial (subfield_generated k {ring_0 k},k) I (a:A)` THEN
  SUBGOAL_THEN
   `(f:(1->num)->A) IN
    ring_carrier(poly_ring (subfield_generated k {ring_0 k}) (:1))`
  ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN MATCH_MP_TAC MINIMAL_POLYNOMIAL_IN_CARRIER THEN
    ASM_SIMP_TAC[NUMBER_FIELD_ALGEBRAIC; FIELD_EXTENSION_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subfield_generated k {ring_0 k:A}`; `k:A ring`; `I:A->A`;
                 `(\v. a):1->A`;
                 `poly_deriv (subfield_generated k {ring_0 k:A}) f`]
    POLY_EXTEND_UNIVARIATE) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION; POLY_DERIV_IN_CARRIER] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC IN_SUBRING_SUM THEN REWRITE_TAC[SUBRING_SUBRING_GENERATED] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[I_THM; COEFF_POLY_DERIV; SUBFIELD_GENERATED;
              RING_OF_NUM_SUBFIELD_GENERATED] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:int` SUBST1_TAC o SPEC `i + 1`) THEN
  MATCH_MP_TAC IN_SUBRING_MUL THEN REWRITE_TAC[SUBRING_SUBRING_GENERATED] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IN_SUBRING_MUL THEN
    SIMP_TAC[SUBRING_SUBRING_GENERATED; IN_SUBRING_NUM; IN_SUBRING_INT];
    MATCH_MP_TAC IN_SUBRING_POW THEN REWRITE_TAC[SUBRING_SUBRING_GENERATED] THEN
    MATCH_MP_TAC SUBRING_GENERATED_INC THEN
    ASM_REWRITE_TAC[SING_SUBSET; IN_SING]]);;

(* If Z[a] is the whole ring of integers then a generates k.                 *)
let NUMBER_FIELD_SUBRING_GENERATED_EQ_RING_OF_INTEGERS = prove
 (`!(k:A ring) a.
        number_field k /\
        ring_carrier(subring_generated k {a}) =
        ring_carrier(ring_of_integers k)
        ==> subfield_generated k {a} = k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  REWRITE_TAC[SUBFIELD_GENERATED_EQ; GSYM SUBSET_ANTISYM_EQ;
              RING_CARRIER_SUBFIELD_GENERATED_SUBSET] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`] NUMBER_FIELD_INTEGRAL_MULTIPLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:int` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(ring_of_int k n = ring_0 (k:A ring))` ASSUME_TAC THENL
   [ASM_MESON_TAC[number_field; RING_OF_INT_EQ_0_CHAR_0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `x = ring_mul k (ring_inv k (ring_of_int k n))
          (ring_mul k (ring_of_int k n) (x:A))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[RING_MUL_ASSOC; RING_INV; RING_OF_INT; FIELD_MUL_LINV;
                 RING_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ring_carrier(ring_of_integers k)
        ==> (y:A) IN ring_carrier(subfield_generated k {a})`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) &&
      rhs(concl th) = `ring_carrier(ring_of_integers k:A ring)`)) THEN
    REWRITE_TAC[GSYM SUBSET; SUBRING_SUBSET_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  MATCH_MP_TAC IN_SUBFIELD_MUL THEN
  ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED] THEN
  MATCH_MP_TAC IN_SUBFIELD_INV THEN
  ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED; RING_OF_INT_IN_RING_OF_INTEGERS]);;
