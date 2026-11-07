(* ========================================================================= *)
(* Embeddings of a number field into the complex numbers, algebraic integers *)
(* with bounded conjugates (Northcott, Kronecker), and the finite generation *)
(* of the unit group of the ring of integers (Dirichlet, without the rank).  *)
(*                                                                           *)
(*   complex_embeddings k = the ring homomorphisms k -> C (complex_ring of   *)
(*                          Multivariate/complex_ring.ml), normalized to the *)
(*                          value ARB outside the carrier (EXTENSIONAL)      *)
(*                                                                           *)
(* Main results: coefficient bounds and the Northcott finiteness for monic   *)
(* integer polynomials with bounded roots                                    *)
(* (COMPLEX_POLYFUN_MONIC_COEFF_BOUND,                                       *)
(* COMPLEX_POLYFUN_MONIC_INTEGER_ROOTS_FINITE); a number field k has exactly *)
(* [k:Q] embeddings (COMPLEX_EMBEDDINGS_HAS_SIZE), every homomorphism k -> C *)
(* agrees with one of them on the carrier, and the conjugates of x (its      *)
(* images) are the complex roots of its minimal polynomial                   *)
(* (COMPLEX_EMBEDDINGS_CONJUGATES); for an algebraic integer they are the    *)
(* roots of a monic integer polynomial of degree at most [k:Q]               *)
(* (RING_OF_INTEGERS_CONJUGATES_POLYFUN), so the algebraic integers with all *)
(* conjugates in a disc are finitely many                                    *)
(* (RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE); Kronecker: an algebraic     *)
(* integer with all conjugates of norm 1 is a root of unity                  *)
(* (RING_OF_INTEGERS_ROOT_OF_UNITY), and the roots of unity are finitely     *)
(* many (NUMBER_FIELD_ROOTS_OF_UNITY_FINITE); the unit group of O is         *)
(* finitely generated (NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED, and       *)
(* explicitly NUMBER_FIELD_UNITS_GENERATORS).                                *)
(*                                                                           *)
(* Routes. The coefficient bound is by induction on the degree n: a root w   *)
(* (FTA) splits off a linear factor (z - w) b(z), and the coefficient        *)
(* identity a_i = b_(i-1) - w * b_i gives |a_i| <= (1 + R)^n. Embeddings:    *)
(* all embeddings agree on the prime subfield Q                              *)
(* (RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED), so they are the          *)
(* extensions to k of any homomorphism from Q to C                           *)
(* (COMPLEX_EMBEDDINGS_EXTENSIONS; one exists by                             *)
(* PRIME_SUBFIELD_HOMOMORPHISM_EXISTS); so embeddings exist by               *)
(* RING_HOMOMORPHISM_EXTENSIONS_NONEMPTY, the conjugates are given by        *)
(* RING_HOMOMORPHISM_EXTENSIONS_ROOT and                                     *)
(* ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM_ROOT, and their number by           *)
(* HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS and SEPARABLE_EXTENSION_CHAR0.      *)
(* Northcott: the minimal polynomial of x in O is monic with integer         *)
(* coefficients (RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q) and of degree at     *)
(* most [k:Q] (MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE); its image under  *)
(* an embedding g has the conjugates as roots, so g x lies in the finite set *)
(* of COMPLEX_POLYFUN_MONIC_INTEGER_ROOTS_FINITE, and g is injective. Units  *)
(* without logarithms: the sizes norm(g u), g in the finite set of           *)
(* embeddings, are multiplicative and positive on the units, and only        *)
(* finitely many units have all sizes at most b (Northcott), so the          *)
(* criterion FINITELY_GENERATED_ABELIAN_GROUP_DISCRETE of                    *)
(* ANT/fingen_group.ml applies.                                              *)
(*                                                                           *)
(* General helpers: the prime subfield of C is {Cx q | rational q}           *)
(* (COMPLEX_PRIME_SUBFIELD); embeddings are injective                        *)
(* (COMPLEX_EMBEDDINGS_MONOMORPHISM), are the extensions of any homomorphism *)
(* from Q to C (COMPLEX_EMBEDDINGS_EXTENSIONS) and map roots of unity to the *)
(* unit circle (COMPLEX_EMBEDDINGS_ROOT_OF_UNITY).                           *)
(*                                                                           *)
(* Uses: Multivariate/complex_ring.ml (complex_ring and its arithmetic:      *)
(* COMPLEX_RING_CLAUSES, FIELD_COMPLEX_RING, COMPLEX_RING_OF_INT, _DIV,      *)
(* _POW, _SUM, POLY_EVAL_COMPLEX_RING), Multivariate/complex_algebra.ml (Cx, *)
(* norm, vsum, COMPLEX_POLYFUN_EQ_0, COMPLEX_POLYFUN_FINITE_ROOTS,           *)
(* COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT), Multivariate/cauchy.ml (FTA; no      *)
(* logarithm or exponential is used), Library/ringtheory.ml                  *)
(* (RING_OF_INT_EQ_CHAR_0), Library/fieldtheory.ml (embedding counts,        *)
(* extensions of homomorphisms,                                              *)
(* RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED,                            *)
(* PRIME_SUBFIELD_HOMOMORPHISM_EXISTS), Library/grouptheory.ml,              *)
(* ANT/integral.ml, ANT/numfield.ml (PRIME_SUBFIELD_CHAR_0),                 *)
(* ANT/fingen_group.ml (FINITELY_GENERATED_ABELIAN_GROUP_DISCRETE),          *)
(* Library/ring_groups.ml (unit_group, FINITELY_GENERATED_UNIT_GROUP),       *)
(* ANT/integrality.ml (RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q),               *)
(* Library/ring_det.ml (RING_MATRIX_SOLVE) and Multivariate/complex_field.ml *)
(* (ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING). NOT 100/transcendence.ml. The  *)
(* needs lines of Multivariate/cauchy.ml, complex_ring.ml and                *)
(* complex_field.ml come after those of the ANT files, so that these are     *)
(* loaded in the state of a fresh session, as in ANT/make.ml (cauchy.ml      *)
(* leaves complex priority).                                                 *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/grouptheory.ml";;
needs "Library/ring_det.ml";;
needs "ANT/algmisc.ml";;
needs "ANT/integral.ml";;
needs "ANT/numfield.ml";;
needs "ANT/integrality.ml";;
needs "ANT/fingen_group.ml";;
needs "Library/ring_groups.ml";;
needs "Multivariate/cauchy.ml";;
needs "Multivariate/complex_ring.ml";;
needs "Multivariate/complex_field.ml";;

let complex_embeddings = new_definition
 `complex_embeddings (k:A ring) =
  {f | ring_homomorphism(k,complex_ring) f /\
       f IN EXTENSIONAL (ring_carrier k)}`;;

(* A square complex matrix with nonzero determinant is onto: the adjugate    *)
(* gives the solution (COMPLEX_MATRIX_SOLVE, from RING_MATRIX_SOLVE).        *)
let COMPLEX_MATRIX_SOLVE = prove
 (`!s (m:K->K->complex) v.
        FINITE s /\ ~(ring_det complex_ring s m = Cx(&0))
        ==> ?t. !i. i IN s ==> vsum s (\j. m i j * t j) = v i`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`complex_ring`; `s:K->bool`; `m:K->K->complex`;
                 `v:K->complex`] RING_MATRIX_SOLVE) THEN
  ASM_SIMP_TAC[FIELD_UNIT; FIELD_COMPLEX_RING; COMPLEX_RING_CLAUSES;
               IN_UNIV; COMPLEX_RING_SUM] THEN MESON_TAC[]);;

(* The prime subfield of C is {Cx q | rational q}, as that of the reals is   *)
(* the set of the rationals (REAL_PRIME_SUBFIELD of ANT/numfield.ml).        *)
let COMPLEX_PRIME_SUBFIELD = prove
 (`ring_carrier(subfield_generated complex_ring {Cx(&0)}) =
   {Cx q | rational q}`,
  MP_TAC(ISPEC `complex_ring` PRIME_SUBFIELD_CHAR_0) THEN
  REWRITE_TAC[FIELD_COMPLEX_RING; RING_CHAR_COMPLEX_RING; COMPLEX_RING_CLAUSES;
              COMPLEX_RING_DIV; COMPLEX_RING_OF_INT] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; rational; GSYM CX_DIV;
              int_eq; int_of_num_th] THEN
  MESON_TAC[int_tybij; INTEGER_REAL_OF_INT]);;

(* ------------------------------------------------------------------------- *)
(* Monic polynomials with bounded roots.                                     *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_POLYFUN_MONIC_COEFF_BOUND = prove
 (`!n (a:num->complex) R.
        a n = Cx(&1) /\
        (!w. vsum(0..n) (\i. a i * w pow i) = Cx(&0) ==> norm w <= R)
        ==> !i. i <= n ==> norm(a i) <= (&1 + R) pow n`,
  let lemma = prove
   (`!n (b:num->complex) w z.
        (z - w) * vsum(0..n) (\i. b i * z pow i) =
        vsum(0..SUC n)
         (\i. ((if i = 0 then Cx(&0) else b(i - 1)) -
               w * (if i <= n then b i else Cx(&0))) * z pow i)`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[COMPLEX_SUB_RDISTRIB; VSUM_SUB_NUMSEG] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN BINOP_TAC THENL
     [REWRITE_TAC[MATCH_MP VSUM_CLAUSES_LEFT (SPEC `SUC n` LE_0)] THEN
      REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_LID; ADD1; VSUM_OFFSET] THEN
      REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
      SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
      MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[COMPLEX_POW_ADD] THEN CONV_TAC COMPLEX_RING;
      SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
      SIMP_TAC[VSUM_CLAUSES_NUMSEG; LE_0; ARITH_RULE `~(SUC n <= n)`] THEN
      REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID]]) in
  INDUCT_TAC THENL
   [SIMP_TAC[LE; real_pow; COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_LE_REFL];
    REPEAT GEN_TAC THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`a:num->complex`; `SUC n`] FTA) THEN ANTS_TAC THENL
   [DISJ2_TAC THEN DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN
    ASM_REWRITE_TAC[IN_NUMSEG; CX_INJ] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `w:complex`)] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT) THEN
  REWRITE_TAC[SUC_SUB1] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:num->complex`) THEN
  SUBGOAL_THEN
   `!i. i <= SUC n
        ==> (a:num->complex) i =
            (if i = 0 then Cx(&0) else b(i - 1)) -
            w * (if i <= n then b i else Cx(&0))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`SUC n`;
     `\i. (a:num->complex) i -
          ((if i = 0 then Cx(&0) else b(i - 1)) -
           w * (if i <= n then b i else Cx(&0)))`] COMPLEX_POLYFUN_EQ_0) THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_RDISTRIB; VSUM_SUB_NUMSEG; lemma;
                    COMPLEX_SUB_REFL] THEN
    REWRITE_TAC[COMPLEX_SUB_0; IN_NUMSEG; LE_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:num->complex) n = Cx(&1) /\ norm(w:complex) <= R`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_ASSUM(MP_TAC o SPEC `SUC n`) THEN
    REWRITE_TAC[LE_REFL; NOT_SUC; SUC_SUB1; ARITH_RULE `~(SUC n <= n)`;
                COMPLEX_MUL_RZERO; COMPLEX_SUB_RZERO] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`b:num->complex`; `R:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[COMPLEX_MUL_RZERO];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0:real <= (&1 + R) pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN MP_TAC(ISPEC `w:complex` NORM_POS_LE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o C MATCH_MP (ASSUME `i <= SUC n`)) THEN
  REWRITE_TAC[real_pow; REAL_ARITH `((&1:real) + R) * X = X + R * X`] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x:complex) <= X /\ norm(y:complex) <= Y ==> norm(x - y) <= X + Y`) THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN CONJ_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[COMPLEX_NORM_0; REAL_LE_REFL]]);;

(* The roots of the monic integer polynomials of degree n <= d with all      *)
(* roots in a disc of radius R: their coefficients are integers bounded by   *)
(* (1 + R)^d, so finitely many polynomials, each with finitely many roots.   *)

let COMPLEX_POLYFUN_MONIC_INTEGER_ROOTS_FINITE = prove
 (`!d R. FINITE {z | ?n c. 1 <= n /\ n <= d /\ (!i. integer(c i)) /\
                           c n = &1 /\
                           vsum(0..n) (\i. Cx(c i) * z pow i) = Cx(&0) /\
                           (!w. vsum(0..n) (\i. Cx(c i) * w pow i) = Cx(&0)
                                ==> norm w <= R)}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `UNIONS {{z | c n = &1 /\ vsum(0..n) (\i. Cx(c i) * z pow i) = Cx(&0)} |
            n IN 0..d /\
            c IN {c | (!i. i IN 0..d
                           ==> c i IN {x | integer x /\
                                           --((&1 + R) pow d) <= x /\
                                           x <= (&1 + R) pow d}) /\
                      (!i. ~(i IN 0..d) ==> c i = &0)}}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
      SIMP_TAC[FINITE_NUMSEG; FINITE_FUNSPACE; FINITE_INTSEG];
      MAP_EVERY X_GEN_TAC [`n:num`; `c:num->real`] THEN
      DISCH_THEN(K ALL_TAC) THEN ASM_CASES_TAC `(c:num->real) n = &1` THEN
      ASM_REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY;
                      COMPLEX_POLYFUN_FINITE_ROOTS] THEN
      EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[IN_NUMSEG; LE_0; LE_REFL; CX_INJ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; UNIONS_GSPEC; IN_NUMSEG; LE_0] THEN
  X_GEN_TAC `z:complex` THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `c:num->real`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`n:num`; `\i. if i <= n then (c:num->real) i else &0`] THEN
  MP_TAC(ISPECL [`n:num`; `\i. Cx((c:num->real) i)`; `R:real`]
    COMPLEX_POLYFUN_MONIC_COEFF_BOUND) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1:real <= &1 + R` ASSUME_TAC THENL
   [MP_TAC(ISPEC `z:complex` NORM_POS_LE) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LE_REFL] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[GSYM REAL_ABS_BOUNDS] THEN
      TRANS_TAC REAL_LE_TRANS `((&1:real) + R) pow n` THEN
      ASM_SIMP_TAC[REAL_POW_MONO];
      MP_TAC(ISPECL [`(&1:real) + R`; `d:num`] REAL_POW_LE) THEN
      REWRITE_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[] THEN ASM_ARITH_TAC;
    UNDISCH_TAC `vsum(0..n) (\i. Cx(c i) * z pow i) = Cx(&0)` THEN
    MATCH_MP_TAC(MESON[] `a = b ==> a = Cx(&0) ==> b = Cx(&0)`) THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Embeddings of a number field.                                             *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_EMBEDDINGS_RESTRICTION = prove
 (`!k:A ring f.
        ring_homomorphism(k,complex_ring) f
        ==> ?g. g IN complex_embeddings k /\
                !x. x IN ring_carrier k ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `RESTRICTION (ring_carrier k) (f:A->complex)` THEN
  REWRITE_TAC[complex_embeddings; IN_ELIM_THM; RESTRICTION_IN_EXTENSIONAL] THEN
  SIMP_TAC[RESTRICTION] THEN MATCH_MP_TAC RING_HOMOMORPHISM_EQ THEN
  EXISTS_TAC `f:A->complex` THEN ASM_SIMP_TAC[RESTRICTION]);;

let COMPLEX_EMBEDDINGS_MONOMORPHISM = prove
 (`!k:A ring g.
        field k /\ g IN complex_embeddings k
        ==> ring_monomorphism(k,complex_ring) g /\
            ring_monomorphism(subfield_generated k {ring_0 k},complex_ring) g`,
  REWRITE_TAC[complex_embeddings; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
  ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING; FIELD_COMPLEX_RING;
               FIELD_SUBFIELD_GENERATED] THEN
  SUBST1_TAC(SYM(CONJUNCT2(ISPEC `g:A->complex` I_O_ID))) THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `k:A ring` THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION]);;

(* All embeddings agree on Q, by                                             *)
(* RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED, so they are the extensions *)
(* to k of any homomorphism g from Q to C;                                   *)
(* HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS counts them, and                    *)
(* RING_HOMOMORPHISM_EXTENSIONS_ROOT with                                    *)
(* ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM_ROOT gives the conjugates.          *)

let COMPLEX_EMBEDDINGS_EXTENSIONS = prove
 (`!(g:A->complex) (k:A ring).
        field k /\
        ring_homomorphism(subfield_generated k {ring_0 k},complex_ring) g
        ==> complex_embeddings k =
            ring_homomorphism_extensions
             (subfield_generated k {ring_0 k},k,complex_ring) (I,g)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[complex_embeddings; ring_homomorphism_extensions; I_THM;
              EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `f:A->complex` THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f:A->complex`; `g:A->complex`;
                 `subfield_generated k {ring_0 k:A}`; `complex_ring`;
                 `{ring_0(subfield_generated k {ring_0 k:A})}`]
    RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED) THEN
  ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; IN_SING;
               PRIME_SUBFIELD_SUBFIELD_GENERATED;
               RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED;
               ISPECL [`subfield_generated k {ring_0 k:A}`; `complex_ring`]
                 RING_HOMOMORPHISM_0]);;

let COMPLEX_EMBEDDINGS_NONEMPTY = prove
 (`!k:A ring. number_field k ==> ~(complex_embeddings k = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [number_field]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPECL [`k:A ring`; `complex_ring`]
    PRIME_SUBFIELD_HOMOMORPHISM_EXISTS) THEN
  ASM_REWRITE_TAC[FIELD_COMPLEX_RING; RING_CHAR_COMPLEX_RING] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:A->complex`) THEN
  MP_TAC(ISPECL [`g:A->complex`; `k:A ring`] COMPLEX_EMBEDDINGS_EXTENSIONS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_EXTENSIONS_NONEMPTY THEN
  ASM_SIMP_TAC[ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING;
               FINITE_IMP_ALGEBRAIC_EXTENSION]);;

let COMPLEX_EMBEDDINGS_HAS_SIZE = prove
 (`!k:A ring.
        number_field k
        ==> complex_embeddings k HAS_SIZE
            extension_degree (subfield_generated k {ring_0 k},k) I`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [number_field]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPECL [`k:A ring`; `complex_ring`]
    PRIME_SUBFIELD_HOMOMORPHISM_EXISTS) THEN
  ASM_REWRITE_TAC[FIELD_COMPLEX_RING; RING_CHAR_COMPLEX_RING] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:A->complex`) THEN
  MP_TAC(ISPECL [`g:A->complex`; `k:A ring`] COMPLEX_EMBEDDINGS_EXTENSIONS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS THEN
  ASM_SIMP_TAC[SEPARABLE_EXTENSION_CHAR0; FINITE_IMP_ALGEBRAIC_EXTENSION;
               ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING;
               RING_CHAR_SUBFIELD_GENERATED]);;

let FINITE_COMPLEX_EMBEDDINGS = prove
 (`!k:A ring. number_field k ==> FINITE(complex_embeddings k)`,
  MESON_TAC[COMPLEX_EMBEDDINGS_HAS_SIZE; HAS_SIZE]);;

let COMPLEX_EMBEDDINGS_CONJUGATES = prove
 (`!k:A ring g x.
        number_field k /\ g IN complex_embeddings k /\ x IN ring_carrier k
        ==> IMAGE (\h. h x) (complex_embeddings k) =
            {z | poly_eval complex_ring
                   (g o minimal_polynomial
                          (subfield_generated k {ring_0 k},k) I x) z =
                 Cx(&0)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [number_field]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN
   `ring_homomorphism(subfield_generated k {ring_0 k},complex_ring)
                     (g:A->complex) /\
    field_extension(subfield_generated k {ring_0 k},k) (I:A->A) /\
    algebraic_over(subfield_generated k {ring_0 k},k) (I:A->A) x`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[complex_embeddings; IN_ELIM_THM]) THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED;
                 FIELD_EXTENSION_SUBFIELD_GENERATED; NUMBER_FIELD_ALGEBRAIC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:A->complex`; `k:A ring`] COMPLEX_EMBEDDINGS_EXTENSIONS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `z:complex` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `h:A->complex` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`I:A->A`; `g:A->complex`; `h:A->complex`;
                   `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                   `complex_ring`; `x:A`]
      RING_HOMOMORPHISM_EXTENSIONS_ROOT) THEN
    ASM_REWRITE_TAC[COMPLEX_RING_CLAUSES];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `complex_ring`; `I:A->A`; `g:A->complex`; `x:A`; `z:complex`]
    ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM_ROOT) THEN
  ASM_SIMP_TAC[ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING; COMPLEX_RING_CLAUSES;
               FINITE_IMP_ALGEBRAIC_EXTENSION; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:A->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `RESTRICTION (ring_carrier k) (s:A->complex)` THEN
  ASM_SIMP_TAC[RESTRICTION] THEN
  MATCH_MP_TAC RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION]);;

(* ------------------------------------------------------------------------- *)
(* Northcott, Kronecker, and the finite generation of the units.             *)
(* ------------------------------------------------------------------------- *)

(* The conjugates of an algebraic integer x are the complex roots of a monic *)
(* integer polynomial of degree at most [k:Q]: the image of its minimal      *)
(* polynomial under any embedding (RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q).   *)

let RING_OF_INTEGERS_CONJUGATES_POLYFUN = prove
 (`!k:A ring x.
        number_field k /\ x IN ring_carrier(ring_of_integers k)
        ==> ?n c. 1 <= n /\
                  n <= extension_degree (subfield_generated k {ring_0 k},k) I /\
                  (!i. integer(c i)) /\ c n = &1 /\
                  IMAGE (\g. g x) (complex_embeddings k) =
                  {z | vsum(0..n) (\i. Cx(c i) * z pow i) = Cx(&0)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:A->complex`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [number_field]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `(x:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `g:A->complex`]
    COMPLEX_EMBEDDINGS_MONOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_homomorphism(k,complex_ring) (g:A->complex) /\
    ring_homomorphism(subfield_generated k {ring_0 k},complex_ring) g`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `g:A->complex`; `x:A`]
    COMPLEX_EMBEDDINGS_CONJUGATES) THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`] RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q) THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `x:A`] MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE) THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `x:A`] MINIMAL_POLYNOMIAL) THEN
  ASM_SIMP_TAC[NUMBER_FIELD_ALGEBRAIC; FIELD_EXTENSION_SUBFIELD_GENERATED] THEN
  ABBREV_TAC
   `p = minimal_polynomial (subfield_generated k {ring_0 k},k) (I:A->A) x` THEN
  ABBREV_TAC
   `n = poly_deg (subfield_generated k {ring_0 k}) (p:(1->num)->A)` THEN
  STRIP_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:num->int` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!w. poly_eval complex_ring ((g:A->complex) o p) w =
        vsum(0..n) (\i. Cx(real_of_int((a:num->int) i)) * w pow i)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`subfield_generated k {ring_0 k:A}`; `complex_ring`;
                   `g:A->complex`; `p:(1->num)->A`]
      POLY_DEG_MONOMORPHIC_IMAGE) THEN
    MP_TAC(ISPECL [`subfield_generated k {ring_0 k:A}`; `complex_ring`;
                   `g:A->complex`; `(:1)`; `p:(1->num)->A`]
      IN_RING_POLYNOMIAL_CARRIER_COMPOSE) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN
    SIMP_TAC[POLY_EVAL_COMPLEX_RING] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    ASM_REWRITE_TAC[COEFF_COMPOSE; COMPLEX_RING_OF_INT; MATCH_MP
      RING_HOMOMORPHISM_RING_OF_INT
      (ASSUME `ring_homomorphism(k,complex_ring) (g:A->complex)`)];
    DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `\i. real_of_int((a:num->int) i)`] THEN
  ASM_REWRITE_TAC[INTEGER_REAL_OF_INT] THEN CONJ_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    MATCH_MP_TAC IRREDUCIBLE_IMP_POLY_DEG_NZ THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED];
    UNDISCH_TAC `monic (subfield_generated k {ring_0 k}) (p:(1->num)->A)` THEN
    ASM_REWRITE_TAC[monic; CONJUNCT2 SUBFIELD_GENERATED;
                    GSYM RING_OF_INT_1] THEN
    ASM_SIMP_TAC[RING_OF_INT_EQ_CHAR_0; int_of_num_th]]);;

let RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE = prove
 (`!k:A ring R.
        number_field k
        ==> FINITE {x | x IN ring_carrier(ring_of_integers k) /\
                        !g. g IN complex_embeddings k ==> norm(g x) <= R}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:A->complex`) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{x | x IN ring_carrier k /\
         (g:A->complex) x IN
         {z | ?n c. 1 <= n /\
                    n <= extension_degree
                          (subfield_generated k {ring_0 k},k) I /\
                    (!i. integer(c i)) /\ c n = &1 /\
                    vsum(0..n) (\i. Cx(c i) * z pow i) = Cx(&0) /\
                    (!w. vsum(0..n) (\i. Cx(c i) * w pow i) = Cx(&0)
                         ==> norm w <= R)}}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ_GENERAL THEN
    REWRITE_TAC[COMPLEX_POLYFUN_MONIC_INTEGER_ROOTS_FINITE] THEN
    MP_TAC(ISPECL [`k:A ring`; `g:A->complex`]
      COMPLEX_EMBEDDINGS_MONOMORPHISM) THEN
    ASM_SIMP_TAC[NUMBER_FIELD_IMP_FIELD] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT2 o
      GEN_REWRITE_RULE I [ring_monomorphism] o CONJUNCT1);
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`] RING_OF_INTEGERS_CONJUGATES_POLYFUN) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_MESON_TAC[]);;

(* Kronecker. Roots of unity have all conjugates of norm 1; conversely, if   *)
(* all conjugates of x have norm 1, the powers of x lie in the finite set of *)
(* the algebraic integers with all conjugates of norm at most 1, so they     *)
(* form a finite multiplicative system and x (nonzero) has a finite order    *)
(* (RING_ORDER_NONZERO_MULTSYS).                                             *)

let COMPLEX_EMBEDDINGS_ROOT_OF_UNITY = prove
 (`!k:A ring g x n.
        g IN complex_embeddings k /\ x IN ring_carrier k /\
        1 <= n /\ ring_pow k x n = ring_1 k
        ==> norm(g x) = &1`,
  REWRITE_TAC[complex_embeddings; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
    RING_HOMOMORPHISM_POW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`x:A`; `n:num`]) THEN
  ASM_SIMP_TAC[ISPECL [`k:A ring`; `complex_ring`] RING_HOMOMORPHISM_1;
               COMPLEX_RING_POW; COMPLEX_RING_CLAUSES] THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real` o SYM) THEN
  REWRITE_TAC[COMPLEX_NORM_POW; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[REAL_POW_EQ_1] THEN
  MP_TAC(ISPEC `(g:A->complex) x` NORM_POS_LE) THEN
  UNDISCH_TAC `1 <= n` THEN ARITH_TAC);;

let RING_OF_INTEGERS_ROOT_OF_UNITY = prove
 (`!k:A ring x.
        number_field k /\ x IN ring_carrier(ring_of_integers k)
        ==> ((?n. 1 <= n /\ ring_pow k x n = ring_1 k) <=>
             !g. g IN complex_embeddings k ==> norm(g x) = &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  EQ_TAC THENL [ASM_MESON_TAC[COMPLEX_EMBEDDINGS_ROOT_OF_UNITY]; DISCH_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:A->complex`) THEN
  SUBGOAL_THEN `~(x:A = ring_0 k)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g:A->complex`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o
      REWRITE_RULE[complex_embeddings; IN_ELIM_THM]) THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP RING_HOMOMORPHISM_0) THEN
    REWRITE_TAC[COMPLEX_RING_CLAUSES; COMPLEX_NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `ring_order k (x:A)` THEN
  ASM_SIMP_TAC[RING_POW_RING_ORDER; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  MATCH_MP_TAC RING_ORDER_NONZERO_MULTSYS THEN
  EXISTS_TAC `IMAGE (ring_pow k (x:A)) (:num)` THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_REGULAR; FIELD_IMP_INTEGRAL_DOMAIN] THEN
  REWRITE_TAC[ring_multsys; SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_IMAGE] THEN
  ASM_SIMP_TAC[RING_POW] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[ring_pow];
    ASM_MESON_TAC[RING_POW_ADD];
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `{y | y IN ring_carrier(ring_of_integers k) /\
           !g. g IN complex_embeddings k
               ==> norm((g:A->complex) y) <= &1}` THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    X_GEN_TAC `m:num` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `x:A`; `m:num`]
        RING_POW) THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS];
      X_GEN_TAC `h:A->complex` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o
        REWRITE_RULE[complex_embeddings; IN_ELIM_THM]) THEN
      DISCH_THEN(MP_TAC o MATCH_MP RING_HOMOMORPHISM_POW) THEN
      ASM_SIMP_TAC[COMPLEX_RING_POW; COMPLEX_NORM_POW; REAL_POW_ONE;
                   REAL_LE_REFL]];
    EXISTS_TAC `1` THEN ASM_SIMP_TAC[RING_POW_1]]);;

(* A root of unity x (x^n = 1) is a root of the monic polynomial X^n - 1     *)
(* over Z, so it is an algebraic integer with all conjugates of norm 1.      *)

let NUMBER_FIELD_ROOTS_OF_UNITY_FINITE = prove
 (`!k:A ring.
        number_field k
        ==> FINITE {x | x IN ring_carrier k /\
                        ?n. 1 <= n /\ ring_pow k x n = ring_1 k}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{x | x IN ring_carrier(ring_of_integers k) /\
         !g. g IN complex_embeddings k ==> norm((g:A->complex) x) <= &1}` THEN
  ASM_SIMP_TAC[RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[COMPLEX_EMBEDDINGS_ROOT_OF_UNITY; REAL_LE_REFL]] THEN
  REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM] THEN
  MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `\i:num. if i = 0 then -- &1 else &0:int`] THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT; INTEGER_RING;
                  IN_UNIV] THEN
  SUBGOAL_THEN
   `ring_sum k {i | i < n}
      (\i. ring_mul k (ring_of_int k (if i = 0 then -- &1 else &0))
                      (ring_pow k (x:A) i)) =
    ring_sum k {i | i < n} (\i. if i = 0 then ring_neg k (ring_1 k)
                                else ring_0 k)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_OF_INT_0; RING_OF_INT_CASES; RING_OF_NUM_1; ring_pow;
                 RING_MUL_LZERO; RING_POW; RING_MUL_RID; RING_NEG; RING_1];
    ASM_SIMP_TAC[RING_SUM_DELTA; IN_ELIM_THM; LE_1; RING_NEG; RING_1;
                 RING_ADD_RNEG]]);;

(* The criterion of ANT/fingen_group.ml with the sizes norm(g u), g in the   *)
(* embeddings: they are positive and multiplicative on the units, and the    *)
(* units with all sizes at most b are finitely many by Northcott.            *)

let NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED = prove
 (`!k:A ring.
        number_field k
        ==> finitely_generated_group(unit_group(ring_of_integers k))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MATCH_MP_TAC(ISPECL
   [`unit_group(ring_of_integers k):A group`; `complex_embeddings (k:A ring)`;
    `\(g:A->complex) (u:A). norm(g u)`]
   FINITELY_GENERATED_ABELIAN_GROUP_DISCRETE) THEN
  ASM_SIMP_TAC[ABELIAN_UNIT_GROUP; FINITE_COMPLEX_EMBEDDINGS; UNIT_GROUP;
               IN_ELIM_THM; RING_OF_INTEGERS] THEN
  SUBGOAL_THEN
   `!u. ring_unit (ring_of_integers k) u
        ==> (u:A) IN ring_carrier(ring_of_integers k) /\
            u IN ring_carrier k /\ ~(u = ring_0 k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_UNIT_IN_CARRIER) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; DISCH_TAC] THEN
    UNDISCH_TAC `ring_unit (ring_of_integers k) (u:A)` THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM(CONJUNCT1 RING_OF_INTEGERS)] THEN
    ASM_SIMP_TAC[RING_UNIT_0; INTEGRAL_DOMAIN_RING_OF_INTEGERS;
                 INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `i:A->complex`]
      COMPLEX_EMBEDDINGS_MONOMORPHISM) THEN
    ASM_REWRITE_TAC[RING_MONOMORPHISM_ALT; COMPLEX_NORM_NZ] THEN
    REWRITE_TAC[COMPLEX_RING_CLAUSES] THEN ASM_MESON_TAC[];
    REWRITE_TAC[complex_embeddings; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `i:A->complex`]
      RING_HOMOMORPHISM_MUL) THEN
    ASM_SIMP_TAC[COMPLEX_RING_CLAUSES; COMPLEX_NORM_MUL];
    X_GEN_TAC `b:real` THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `{x | x IN ring_carrier(ring_of_integers k) /\
           !g. g IN complex_embeddings k ==> norm((g:A->complex) x) <= b}` THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

let NUMBER_FIELD_UNITS_GENERATORS = prove
 (`!k:A ring.
        number_field k
        ==> ?t. FINITE t /\
                (!u. u IN t ==> ring_unit (ring_of_integers k) u) /\
                !u. ring_unit (ring_of_integers k) u
                    ==> ?n. u = ring_product k t (\v. ring_pow k v (n v))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
    NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED) THEN
  REWRITE_TAC[FINITELY_GENERATED_UNIT_GROUP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:A->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `n:A->num` o C MATCH_MP
   (ASSUME `ring_unit (ring_of_integers k) (u:A)`)) THEN
  EXISTS_TAC `n:A->num` THEN ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN
  REWRITE_TAC[ring_of_integers; RING_PRODUCT_SUBRING_GENERATED_GEN] THEN
  REWRITE_TAC[GSYM ring_of_integers] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `v:A` THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `v:A`; `(n:A->num) v`]
    RING_POW) THEN
  ASM_SIMP_TAC[RING_OF_INTEGERS; RING_UNIT_IN_CARRIER]);;
