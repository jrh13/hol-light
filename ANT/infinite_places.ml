(* ========================================================================= *)
(* Real embeddings and infinite places of a number field k; the trace, the   *)
(* norm and the discriminant of k through its complex embeddings; the sign   *)
(* of the discriminant.                                                      *)
(*                                                                           *)
(*   real_embeddings k = the embeddings k -> C with real values (r1 of them) *)
(*   infinite_places k = the archimedean absolute values x |-> |g x| of the  *)
(*                       embeddings g (r1 + r2 of them, where r2 is          *)
(*                       CARD(infinite_places k) - CARD(real_embeddings k))  *)
(*                                                                           *)
(* Main results: complex conjugation permutes the embeddings                 *)
(* (COMPLEX_EMBEDDINGS_CNJ, COMPLEX_EMBEDDINGS_CNJ_CNJ) with the real        *)
(* embeddings as fixed points (REAL_EMBEDDINGS_CNJ); two embeddings give the *)
(* same absolute value iff they are equal or conjugate                       *)
(* (COMPLEX_EMBEDDINGS_NORM_EQ), so [k:Q] + r1 = 2 (r1 + r2)                 *)
(* (CARD_INFINITE_PLACES, FINITE_INFINITE_PLACES), and k has one infinite    *)
(* place iff k = Q or k is imaginary quadratic (CARD_INFINITE_PLACES_EQ_1).  *)
(* Every embedding maps the trace and the norm of x to the sum and the       *)
(* product of the conjugates of x (NUMBER_FIELD_TRACE_COMPLEX_EMBEDDINGS,    *)
(* NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS); N((x)) is the product of the |g x| *)
(* for nonzero x in O (NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS), and    *)
(* the units of O are the x in O for which this product is 1                 *)
(* (RING_OF_INTEGERS_UNIT_NORM_PRODUCT). For an integral basis w and         *)
(* distinct embeddings e_0, ..., e_(n-1), det(e_i(w_j))^2 = d_K              *)
(* (NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS), and d_K > 0 iff r2 is even        *)
(* (NUMBER_FIELD_DISCRIMINANT_SIGN).                                         *)
(*                                                                           *)
(* Helpers: the absolute values of an embedding are positive at nonzero      *)
(* elements and multiplicative (COMPLEX_EMBEDDINGS_NORM_POS,                 *)
(* COMPLEX_EMBEDDINGS_NORM_MUL); x |-> Re(g x) is a ring monomorphism into R *)
(* for g real (REAL_EMBEDDINGS_MONOMORPHISM), and every embedding is real on *)
(* the prime subfield (COMPLEX_EMBEDDINGS_PRIME_SUBFIELD_REAL). The          *)
(* embeddings at a place v are g and its conjugate                           *)
(* (COMPLEX_EMBEDDINGS_NORM_FUN_EQ, INFINITE_PLACE_EMBEDDINGS), their number *)
(* n_v is 1 at a real place and 2 at a complex one                           *)
(* (CARD_INFINITE_PLACE_EMBEDDINGS, INFINITE_PLACES_DEGREE), and a sum over  *)
(* the embeddings is the sum over the places weighted by n_v                 *)
(* (INFINITE_PLACES_SUM); the places are positive at nonzero elements,       *)
(* multiplicative, equal to 1 at the roots of unity, and positive            *)
(* multiplicative functions on the unit group (INFINITE_PLACES_POS,          *)
(* INFINITE_PLACES_MUL, INFINITE_PLACES_ROOT_OF_UNITY,                       *)
(* INFINITE_PLACES_UNIT_GROUP).                                              *)
(*                                                                           *)
(* Routes. Absolute values: the equations for x and x + 1 give, for each x,  *)
(* h x = g x or h x = conj(g x), and evaluating at sums x + y makes the      *)
(* choice uniform. Counting: the fibres of g |-> (\x. |g x|) are the sets    *)
(* {g, conj g} (NSUM_IMAGE_GEN). Trace, norm and discriminant: the instances *)
(* for complex_ring of the theorems for homomorphisms into any field of      *)
(* ANT/power_basis.ml (NUMBER_FIELD_TRACE_HOMOMORPHISMS,                     *)
(* NUMBER_FIELD_NORM_HOMOMORPHISMS,                                          *)
(* NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS), with the [k:Q] embeddings of    *)
(* COMPLEX_EMBEDDINGS_HAS_SIZE and d_K the discriminant of an integral basis *)
(* (NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD). Sign: with the integral basis    *)
(* indexed by the embeddings (RING_DET_REINDEX), conjugation permutes the    *)
(* rows of the matrix by an involution with r2 transpositions                *)
(* (RING_DET_PERMUTE_ROWS, SIGN_INVOLUTION), so the conjugate of its         *)
(* determinant D is (-1)^r2 D, while D^2 = d_K is a nonzero integer.         *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/fieldtheory.ml (subfield_generated,  *)
(* extension_degree), Library/permutations.ml (sign, evenperm),              *)
(* Library/products.ml (product), Library/ring_det.ml (free_basis,           *)
(* algebra_trace, algebra_norm), ANT/ideal_norm.ml, ANT/numfield.ml,         *)
(* ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/discriminant.ml,          *)
(* ANT/power_basis.ml (NUMBER_FIELD_TRACE_HOMOMORPHISMS,                     *)
(* NUMBER_FIELD_NORM_HOMOMORPHISMS, NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS) *)
(* and ANT/complex_embeddings.ml (and with it Multivariate/cauchy.ml: cnj,   *)
(* vsum, cproduct). The needs line of ANT/complex_embeddings.ml comes after  *)
(* those of the light files, as in ANT/make.ml. Also                         *)
(* Multivariate/complex_ring.ml (COMPLEX_RING_CLAUSES, COMPLEX_RING_SUM,     *)
(* COMPLEX_RING_PRODUCT, RING_HOMOMORPHISM_CNJ).                             *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/permutations.ml";;
needs "Library/products.ml";;
needs "Library/ring_det.ml";;
needs "ANT/ideal_norm.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/norm_index.ml";;
needs "ANT/discriminant.ml";;
needs "ANT/power_basis.ml";;
needs "ANT/complex_embeddings.ml";;
needs "Multivariate/complex_ring.ml";;

let real_embeddings = new_definition
 `real_embeddings (k:A ring) =
  {g | g IN complex_embeddings k /\ !x. x IN ring_carrier k ==> real(g x)}`;;

let infinite_places = new_definition
 `infinite_places (k:A ring) =
  IMAGE (\g:A->complex. \x. norm(g x)) (complex_embeddings k)`;;

(* ------------------------------------------------------------------------- *)
(* Conjugate embeddings, real embeddings and the infinite places.            *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_EMBEDDINGS_CNJ = prove
 (`!k (g:A->complex).
        g IN complex_embeddings k
        ==> RESTRICTION (ring_carrier k) (cnj o g) IN complex_embeddings k`,
  REWRITE_TAC[complex_embeddings; IN_ELIM_THM; RESTRICTION_IN_EXTENSIONAL] THEN
  REWRITE_TAC[ring_homomorphism; COMPLEX_RING_CLAUSES; SUBSET_UNIV] THEN
  SIMP_TAC[RESTRICTION; RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL; o_THM;
           CNJ_ADD; CNJ_MUL; CNJ_NEG; CNJ_CX]);;

let COMPLEX_EMBEDDINGS_CNJ_CNJ = prove
 (`!k (g:A->complex).
        g IN complex_embeddings k
        ==> RESTRICTION (ring_carrier k)
              (cnj o RESTRICTION (ring_carrier k) (cnj o g)) = g`,
  REWRITE_TAC[RESTRICTION_COMPOSE_RIGHT; o_DEF; CNJ_CNJ; ETA_AX] THEN
  SIMP_TAC[RESTRICTION_FIXPOINT; complex_embeddings; IN_ELIM_THM]);;

let REAL_EMBEDDINGS_CNJ = prove
 (`!k (g:A->complex).
        g IN real_embeddings k <=>
        g IN complex_embeddings k /\
        RESTRICTION (ring_carrier k) (cnj o g) = g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_embeddings; IN_ELIM_THM] THEN
  ASM_CASES_TAC `(g:A->complex) IN complex_embeddings k` THEN
  ASM_REWRITE_TAC[RESTRICTION_UNIQUE; o_THM; REAL_CNJ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[complex_embeddings; IN_ELIM_THM; IN]) THEN
  ASM_REWRITE_TAC[]);;

let COMPLEX_EMBEDDINGS_NORM_POS = prove
 (`!k (g:A->complex) x.
        field k /\ g IN complex_embeddings k /\ x IN ring_carrier k
        ==> (&0 < norm(g x) <=> ~(x = ring_0 k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `g:A->complex`]
    COMPLEX_EMBEDDINGS_MONOMORPHISM) THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_ALT_EQ; COMPLEX_NORM_NZ;
               COMPLEX_RING_CLAUSES]);;

let COMPLEX_EMBEDDINGS_NORM_MUL = prove
 (`!k (g:A->complex) x y.
        g IN complex_embeddings k /\ x IN ring_carrier k /\ y IN ring_carrier k
        ==> norm(g(ring_mul k x y)) = norm(g x) * norm(g y)`,
  REWRITE_TAC[complex_embeddings; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
    RING_HOMOMORPHISM_MUL) THEN
  ASM_SIMP_TAC[COMPLEX_RING_CLAUSES; COMPLEX_NORM_MUL]);;

(* For each x the absolute values at x and x + 1 give h x = g x or h x =     *)
(* conj(g x) (lemma1); if both alternatives fail somewhere, at x and at y    *)
(* say, then they fail together at x + y (lemma2).                           *)
let COMPLEX_EMBEDDINGS_NORM_EQ = prove
 (`!k (g:A->complex) h.
        g IN complex_embeddings k /\ h IN complex_embeddings k
        ==> ((!x. x IN ring_carrier k ==> norm(h x) = norm(g x)) <=>
             h = g \/ h = RESTRICTION (ring_carrier k) (cnj o g))`,
  let lemma1 = prove
   (`!a b. norm a = norm b /\ norm(a + Cx(&1)) = norm(b + Cx(&1))
           ==> a = b \/ a = cnj b`,
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o AP_TERM `\t:real. t pow 2`)) THEN
    REWRITE_TAC[COMPLEX_SQNORM; RE_ADD; IM_ADD; RE_CX; IM_CX; COMPLEX_EQ;
                RE_CNJ; IM_CNJ] THEN
    CONV_TAC REAL_RING)
  and lemma2 = prove
   (`!a b c d:complex.
        ~(a = c) /\ (a = c \/ a = cnj c) /\ (b = d \/ b = cnj d) /\
        (a + b = c + d \/ a + b = cnj c + cnj d)
        ==> b = cnj d`,
    CONV_TAC COMPLEX_RING) in
  REPEAT GEN_TAC THEN REWRITE_TAC[complex_embeddings; IN_ELIM_THM] THEN
  REWRITE_TAC[ring_homomorphism; COMPLEX_RING_CLAUSES; SUBSET_UNIV] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `((h:A->complex) = g <=> !x. x IN ring_carrier k ==> h x = g x) /\
    (h = RESTRICTION (ring_carrier k) (cnj o g) <=>
     !x. x IN ring_carrier k ==> h x = cnj(g x))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[RESTRICTION_UNIQUE_ALT; o_THM] THEN
    ASM_MESON_TAC[EXTENSIONAL_EQ; IN];
    ALL_TAC] THEN
  EQ_TAC THENL [DISCH_TAC; STRIP_TAC THEN ASM_SIMP_TAC[COMPLEX_NORM_CNJ]] THEN
  SUBGOAL_THEN
   `!x. x IN ring_carrier k ==> (h:A->complex) x = g x \/ h x = cnj(g x)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma1 THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `ring_add k x (ring_1 k):A` th) THEN
                            MP_TAC(SPEC `x:A` th)) THEN
    ASM_SIMP_TAC[RING_ADD; RING_1];
    DISCH_TAC] THEN
  REWRITE_TAC[TAUT `p \/ q <=> ~p ==> q`; NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC lemma2 THEN
  MAP_EVERY EXISTS_TAC [`(h:A->complex) x`; `(g:A->complex) x`] THEN
  FIRST_X_ASSUM(fun th ->
    MAP_EVERY (MP_TAC o C SPEC th) [`x:A`; `y:A`; `ring_add k x y:A`]) THEN
  ASM_SIMP_TAC[RING_ADD; CNJ_ADD]);;

let FINITE_INFINITE_PLACES = prove
 (`!k:A ring. number_field k ==> FINITE(infinite_places k)`,
  SIMP_TAC[infinite_places; FINITE_IMAGE; FINITE_COMPLEX_EMBEDDINGS]);;

(* The fibre of g under g |-> (\x. |g x|) is {g, conj g}; summing 2 or 1     *)
(* over the embeddings according as they are real or not counts each place   *)
(* twice.                                                                    *)
let CARD_INFINITE_PLACES = prove
 (`!k:A ring.
        number_field k
        ==> CARD(complex_embeddings k) + CARD(real_embeddings k) =
            2 * CARD(infinite_places k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_COMPLEX_EMBEDDINGS) THEN
  ABBREV_TAC `c = \g:A->complex. RESTRICTION (ring_carrier k) (cnj o g)` THEN
  SUBGOAL_THEN
   `!g:A->complex. g IN complex_embeddings k
                   ==> c g IN complex_embeddings k /\ c(c g) = g /\
                       !x. ~(x IN ring_carrier k) ==> g x = ARB`
  ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    SIMP_TAC[COMPLEX_EMBEDDINGS_CNJ; COMPLEX_EMBEDDINGS_CNJ_CNJ] THEN
    SIMP_TAC[complex_embeddings; IN_ELIM_THM; IN_EXTENSIONAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(complex_embeddings k) + CARD(real_embeddings k) =
    nsum (complex_embeddings k) (\g:A->complex. if c g = g then 2 else 1)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `real_embeddings k = {g:A->complex | g IN complex_embeddings k /\ c g = g}`
    SUBST1_TAC THENL
     [EXPAND_TAC "c" THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; REAL_EMBEDDINGS_CNJ];
      ASM_SIMP_TAC[CARD_EQ_NSUM; FINITE_RESTRICT; NSUM_RESTRICT_SET;
                   GSYM NSUM_ADD] THEN
      MATCH_MP_TAC NSUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  REWRITE_TAC[infinite_places] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
   [MATCH_MP (ISPEC `\g:A->complex. \x. norm(g x)` NSUM_IMAGE_GEN) th]) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; ONCE_REWRITE_RULE[MULT_SYM] (GSYM NSUM_CONST)] THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `g:A->complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{h | h IN complex_embeddings k /\
         (\x. norm((h:A->complex) x)) = (\x. norm(g x))} = {g, c g}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `h:A->complex` THEN
    ASM_CASES_TAC `(h:A->complex) IN complex_embeddings k` THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    EXPAND_TAC "c" THEN ASM_SIMP_TAC[GSYM COMPLEX_EMBEDDINGS_NORM_EQ] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN EQ_TAC THEN SIMP_TAC[] THEN
    DISCH_TAC THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN ring_carrier k` THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[NSUM_CLAUSES; FINITE_SING; IN_SING; NSUM_SING] THEN
    ASM_CASES_TAC `(c:(A->complex)->(A->complex)) g = g` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

let CARD_INFINITE_PLACES_EQ_1 = prove
 (`!k:A ring.
        number_field k
        ==> (CARD(infinite_places k) = 1 <=>
             extension_degree (subfield_generated k {ring_0 k},k) I = 1 \/
             extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
             real_embeddings k = {})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CARD_INFINITE_PLACES) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPLEX_EMBEDDINGS_HAS_SIZE) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NUMBER_FIELD_DEGREE_POS) THEN
  SUBGOAL_THEN `real_embeddings (k:A ring) SUBSET complex_embeddings k`
  ASSUME_TAC THENL [SIMP_TAC[real_embeddings; SUBSET_RESTRICT]; ALL_TAC] THEN
  ABBREV_TAC
   `n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)` THEN
  REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(real_embeddings(k:A ring))` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`real_embeddings(k:A ring)`; `complex_embeddings(k:A ring)`]
    CARD_SUBSET) THEN
  ASM_SIMP_TAC[GSYM CARD_EQ_0] THEN ASM_ARITH_TAC);;

let REAL_EMBEDDINGS_MONOMORPHISM = prove
 (`!k (g:A->complex).
        field k /\ g IN real_embeddings k
        ==> ring_monomorphism(k,real_ring) (\x. Re(g x))`,
  REWRITE_TAC[real_embeddings; IN_ELIM_THM; real] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `g:A->complex`]
    COMPLEX_EMBEDDINGS_MONOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[ring_monomorphism; ring_homomorphism; COMPLEX_RING_CLAUSES;
              REAL_RING_CLAUSES; SUBSET; FORALL_IN_IMAGE; IN_UNIV;
              COMPLEX_EQ] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [STRIP_TAC THEN
    ASM_SIMP_TAC[RE_CX; RE_NEG; RE_ADD; complex_mul; RE; REAL_MUL_LZERO;
                 REAL_SUB_RZERO];
    ASM_MESON_TAC[]]);;

let COMPLEX_EMBEDDINGS_PRIME_SUBFIELD_REAL = prove
 (`!k (g:A->complex) a.
        field k /\ g IN complex_embeddings k /\
        a IN ring_carrier(subfield_generated k {ring_0 k})
        ==> real(g a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CNJ] THEN
  MP_TAC(ISPECL [`k:A ring`; `g:A->complex`] COMPLEX_EMBEDDINGS_CNJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:A->complex`;
                 `RESTRICTION (ring_carrier k) (cnj o (g:A->complex))`;
                 `k:A ring`; `complex_ring`; `{ring_0 k:A}`]
    RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[complex_embeddings; IN_ELIM_THM]) THEN
  ASM_REWRITE_TAC[IN_SING] THEN ANTS_TAC THENL
   [X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[RESTRICTION; o_THM] THEN
    MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
      RING_HOMOMORPHISM_0) THEN
    ASM_REWRITE_TAC[COMPLEX_RING_CLAUSES] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CNJ_CX];
    DISCH_THEN(MP_TAC o SPEC `a:A`) THEN
    ASM_REWRITE_TAC[RESTRICTION; o_THM] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The embeddings at an infinite place, local degrees, sums over the places, *)
(* the places as multiplicative functions.                                   *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_EMBEDDINGS_NORM_FUN_EQ = prove
 (`!k (g:A->complex) h.
        g IN complex_embeddings k /\ h IN complex_embeddings k
        ==> ((\x. norm(h x)) = (\x. norm(g x)) <=>
             h = g \/ h = RESTRICTION (ring_carrier k) (cnj o g))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) (GSYM COMPLEX_EMBEDDINGS_NORM_EQ) o
    rand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_TAC THEN X_GEN_TAC `x:A` THEN
  ASM_CASES_TAC `(x:A) IN ring_carrier k` THEN ASM_SIMP_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[complex_embeddings; IN_ELIM_THM;
                              EXTENSIONAL]) THEN
  ASM_SIMP_TAC[]);;

let INFINITE_PLACE_EMBEDDINGS = prove
 (`!k (g:A->complex).
        g IN complex_embeddings k
        ==> {h | h IN complex_embeddings k /\
                 (\x. norm(h x)) = (\x. norm(g x))} =
            {g, RESTRICTION (ring_carrier k) (cnj o g)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT;
                                    NOT_IN_EMPTY] THEN
  X_GEN_TAC `h:A->complex` THEN
  ASM_CASES_TAC `(h:A->complex) IN complex_embeddings k` THEN
  ASM_SIMP_TAC[COMPLEX_EMBEDDINGS_NORM_FUN_EQ] THEN
  ASM_MESON_TAC[COMPLEX_EMBEDDINGS_CNJ]);;

let CARD_INFINITE_PLACE_EMBEDDINGS = prove
 (`!k (g:A->complex).
        g IN complex_embeddings k
        ==> CARD {h | h IN complex_embeddings k /\
                      (\x. norm(h x)) = (\x. norm(g x))} =
            if g IN real_embeddings k then 1 else 2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INFINITE_PLACE_EMBEDDINGS] THEN
  ASM_REWRITE_TAC[REAL_EMBEDDINGS_CNJ] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
           NOT_IN_EMPTY] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_MESON_TAC[]);;

let INFINITE_PLACES_SUM = prove
 (`!k (f:(A->real)->real).
        number_field k
        ==> sum (infinite_places k)
              (\v. &(CARD {g | g IN complex_embeddings k /\
                               (\x. norm(g x)) = v}) * f v) =
            sum (complex_embeddings k) (\g. f (\x. norm(g x)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_COMPLEX_EMBEDDINGS) THEN
  MP_TAC(ISPECL [`\g:A->complex. \x. norm(g x)`;
                 `\g:A->complex. (f:(A->real)->real) (\x. norm(g x))`;
                 `complex_embeddings(k:A ring)`] SUM_IMAGE_GEN) THEN
  ASM_REWRITE_TAC[GSYM infinite_places] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `v:A->real` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  TRANS_TAC EQ_TRANS
   `sum {g | g IN complex_embeddings k /\ (\x. norm(g x)) = v}
        (\g:A->complex. (f:(A->real)->real) v)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[IN_ELIM_THM];
    MATCH_MP_TAC SUM_CONST THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_REWRITE_TAC[]]);;

let INFINITE_PLACES_DEGREE = prove
 (`!k v:A->real.
        number_field k /\ v IN infinite_places k
        ==> 1 <= CARD {g | g IN complex_embeddings k /\
                           (\x. norm(g x)) = v} /\
            CARD {g | g IN complex_embeddings k /\
                      (\x. norm(g x)) = v} <= 2`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; infinite_places] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_INFINITE_PLACE_EMBEDDINGS] THEN
  COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV);;

let INFINITE_PLACES_POS = prove
 (`!k (v:A->real) x.
        field k /\ v IN infinite_places k /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> &0 < v x`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; infinite_places] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  SIMP_TAC[COMPLEX_EMBEDDINGS_NORM_POS]);;

let INFINITE_PLACES_MUL = prove
 (`!k (v:A->real) x y.
        v IN infinite_places k /\ x IN ring_carrier k /\ y IN ring_carrier k
        ==> v(ring_mul k x y) = v x * v y`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; infinite_places] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  SIMP_TAC[COMPLEX_EMBEDDINGS_NORM_MUL]);;

let INFINITE_PLACES_ROOT_OF_UNITY = prove
 (`!k (v:A->real) x n.
        v IN infinite_places k /\ x IN ring_carrier k /\
        1 <= n /\ ring_pow k x n = ring_1 k
        ==> v x = &1`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; infinite_places] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  MESON_TAC[COMPLEX_EMBEDDINGS_ROOT_OF_UNITY]);;

let INFINITE_PLACES_UNIT_GROUP = prove
 (`!k v:A->real.
        number_field k /\ v IN infinite_places k
        ==> (!x. x IN group_carrier(unit_group(ring_of_integers k))
                 ==> &0 < v x) /\
            (!x y. x IN group_carrier(unit_group(ring_of_integers k)) /\
                   y IN group_carrier(unit_group(ring_of_integers k))
                   ==> v(group_mul (unit_group(ring_of_integers k)) x y) =
                       v x * v y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  REWRITE_TAC[UNIT_GROUP; IN_ELIM_THM; RING_OF_INTEGERS] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC INFINITE_PLACES_POS; MATCH_MP_TAC INFINITE_PLACES_MUL] THEN
  ASM_MESON_TAC[RING_OF_INTEGERS_UNIT_NONZERO]);;

(* ------------------------------------------------------------------------- *)
(* Trace, norm and units through the embeddings.                             *)
(* ------------------------------------------------------------------------- *)

(* The instances of NUMBER_FIELD_TRACE_HOMOMORPHISMS and                     *)
(* NUMBER_FIELD_NORM_HOMOMORPHISMS (ANT/power_basis.ml) for l = complex_ring *)
(* and the [k:Q] complex embeddings (COMPLEX_EMBEDDINGS_HAS_SIZE).           *)
let NUMBER_FIELD_TRACE_COMPLEX_EMBEDDINGS,
    NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS = (CONJ_PAIR o prove)
 (`(!k (g:A->complex) x.
        number_field k /\ g IN complex_embeddings k /\ x IN ring_carrier k
        ==> g(algebra_trace (subfield_generated k {ring_0 k},k) I x) =
            vsum (complex_embeddings k) (\h. h x)) /\
   (!k (g:A->complex) x.
        number_field k /\ g IN complex_embeddings k /\ x IN ring_carrier k
        ==> g(algebra_norm (subfield_generated k {ring_0 k},k) I x) =
            cproduct (complex_embeddings k) (\h. h x))`,
  REWRITE_TAC[AND_FORALL_THM;
              TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM COMPLEX_RING_SUM; GSYM COMPLEX_RING_PRODUCT;
               FINITE_COMPLEX_EMBEDDINGS] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NUMBER_FIELD_TRACE_HOMOMORPHISMS;
    MATCH_MP_TAC NUMBER_FIELD_NORM_HOMOMORPHISMS] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[complex_embeddings; IN_ELIM_THM]) THEN
  ASM_SIMP_TAC[FIELD_COMPLEX_RING; COMPLEX_EMBEDDINGS_HAS_SIZE; SUBSET;
               complex_embeddings; IN_ELIM_THM]);;

let NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS = prove
 (`!k x:A.
        number_field k /\ x IN ring_carrier(ring_of_integers k) /\
        ~(x = ring_0 k)
        ==> &(ideal_norm (ring_of_integers k)
                (ideal_generated (ring_of_integers k) {x})) =
            product (complex_embeddings k) (\g. norm(g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`] NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:int` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o AP_TERM `real_of_int`))) THEN
  REWRITE_TAC[int_of_num_th; int_abs_th] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `g:A->complex` o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
    MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    REWRITE_RULE[complex_embeddings; IN_ELIM_THM]) THEN
  MP_TAC(ISPECL [`k:A ring`; `g:A->complex`; `x:A`]
    NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS) THEN
  ASM_SIMP_TAC[REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET;
               MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (ASSUME
                 `ring_homomorphism(k,complex_ring) (g:A->complex)`)] THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
  ASM_SIMP_TAC[NORM_CPRODUCT; FINITE_COMPLEX_EMBEDDINGS; COMPLEX_RING_OF_INT;
               COMPLEX_NORM_CX]);;

let RING_OF_INTEGERS_UNIT_NORM_PRODUCT = prove
 (`!k x:A.
        number_field k
        ==> (ring_unit (ring_of_integers k) x <=>
             x IN ring_carrier(ring_of_integers k) /\
             product (complex_embeddings k) (\g. norm(g x)) = &1)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(x:A) IN ring_carrier(ring_of_integers k)` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[RING_UNIT_IN_CARRIER]] THEN
  ASM_CASES_TAC `x:A = ring_0 k` THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~p /\ ~q ==> (p <=> q)`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RING_UNIT_0; RING_OF_INTEGERS; NUMBER_FIELD_IMP_FIELD;
                    INTEGRAL_DOMAIN_RING_OF_INTEGERS;
                    INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING];
      MATCH_MP_TAC(REAL_ARITH `x:real = &0 ==> ~(x = &1)`) THEN
      ASM_SIMP_TAC[PRODUCT_EQ_0; FINITE_COMPLEX_EMBEDDINGS] THEN
      FIRST_ASSUM(MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
        MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY) THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      SIMP_TAC[complex_embeddings; IN_ELIM_THM; COMPLEX_NORM_ZERO] THEN
      MESON_TAC[RING_HOMOMORPHISM_0; COMPLEX_RING_CLAUSES]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS;
               REAL_OF_NUM_EQ; GSYM IDEAL_GENERATED_SING_EQ_CARRIER] THEN
  EQ_TAC THEN SIMP_TAC[IDEAL_NORM_CARRIER] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `1 < n ==> ~(n = 1)`) THEN
  MATCH_MP_TAC IDEAL_NORM_GT_1 THEN
  ASM_SIMP_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
  MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\s:A->bool. (x:A) IN s`) THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_INC_GEN; IN_SING]);;

(* ------------------------------------------------------------------------- *)
(* The discriminant through the embeddings, and its sign.                    *)
(* ------------------------------------------------------------------------- *)

(* The instance of NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS for complex_ring: *)
(* the discriminant of an integral basis w is d_K                            *)
(* (NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD), and embeddings that agree on k   *)
(* are equal.                                                                *)
let NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS = prove
 (`!k n w (e:num->A->complex).
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
        (!i. i < n ==> e i IN complex_embeddings k) /\
        (!i j. i < n /\ j < n /\ e i = e j ==> i = j)
        ==> ring_det complex_ring {i | i < n} (\i j. e i (w j)) pow 2 =
            Cx(real_of_int(number_field_discriminant k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[complex_embeddings; IN_ELIM_THM]) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `g:A->complex` (STRIP_ASSUME_TAC o
    REWRITE_RULE[complex_embeddings; IN_ELIM_THM]) o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
    MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY) THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
    RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
    NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `g:A->complex`) THEN
  REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (ASSUME
   `ring_homomorphism(k,complex_ring) (g:A->complex)`);
   COMPLEX_RING_OF_INT] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM COMPLEX_RING_POW] THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS THEN
  ASM_REWRITE_TAC[FIELD_COMPLEX_RING] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o snd o strip_forall o concl) o
    check (fun th -> rand(snd(strip_forall(concl th))) = `i:num = j`)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC `ring_carrier k:A->bool` THEN
  ASM_SIMP_TAC[]);;

let COMPLEX_EMBEDDINGS_VSUM_CNJ_REAL = prove
 (`!k (a:A) (b:A).
        number_field k /\ a IN ring_carrier k /\ b IN ring_carrier k
        ==> real(vsum (complex_embeddings k) (\g. cnj(g a) * g b))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(complex_embeddings (k:A ring))` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPLEX_EMBEDDINGS_HAS_SIZE; HAS_SIZE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_CNJ] THEN ASM_SIMP_TAC[CNJ_VSUM] THEN
  REWRITE_TAC[CNJ_MUL; CNJ_CNJ] THEN
  ABBREV_TAC
   `cj = \g:A->complex. RESTRICTION (ring_carrier k) (cnj o g)` THEN
  SUBGOAL_THEN
   `IMAGE (cj:(A->complex)->(A->complex)) (complex_embeddings k) =
    complex_embeddings k /\
    (!g. g IN complex_embeddings k ==> cj(cj g) = g)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cj" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPLEX_EMBEDDINGS_CNJ_CNJ]; DISCH_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; COMPLEX_EMBEDDINGS_CNJ] THEN
    X_GEN_TAC `g:A->complex` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `RESTRICTION (ring_carrier k) (cnj o (g:A->complex))` THEN
    ASM_SIMP_TAC[COMPLEX_EMBEDDINGS_CNJ];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE o rand o snd) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `g:A->complex` THEN DISCH_TAC THEN
  EXPAND_TAC "cj" THEN ASM_REWRITE_TAC[o_THM; RESTRICTION; CNJ_CNJ] THEN
  REWRITE_TAC[COMPLEX_MUL_SYM]);;

let NUMBER_FIELD_EMBEDDING_GRAM_DET = prove
 (`!k n (w:num->A) (e:num->A->complex).
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
        n = extension_degree (subfield_generated k {ring_0 k},k) I /\
        (!i. i < n ==> e i IN complex_embeddings k) /\
        (!i j. i < n /\ j < n /\ e i = e j ==> i = j)
        ==> ring_det real_ring {i | i < n}
              (\i j. Re(vsum {l | l < n} (\l. cnj(e l (w i)) * e l (w j))))
            pow 2 =
            real_of_int(number_field_discriminant k) pow 2`,
  let cx_hom = prove
   (`ring_homomorphism(real_ring,complex_ring) Cx`,
    REWRITE_TAC[ring_homomorphism; COMPLEX_RING_CLAUSES; REAL_RING_CLAUSES;
                SUBSET_UNIV; IN_UNIV; CX_ADD; CX_MUL; CX_NEG]) in
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC
   `n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `IMAGE (e:num->A->complex) {i | i < n} = complex_embeddings k`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:A ring` COMPLEX_EMBEDDINGS_HAS_SIZE) THEN
    ASM_REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
    MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; CARD_NUMSEG_LT] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < n ==> (w:num->A) i IN ring_carrier k` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP FREE_BASIS_IN_CARRIER o check (fun th ->
      free_in `w:num->A` (concl th))) THEN
    MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. i < n /\ j < n
          ==> Cx(Re(vsum {l | l < n}
                     (\l. cnj((e:num->A->complex) l (w i)) * e l (w j)))) =
              vsum {l | l < n} (\l. cnj(e l (w i)) * e l (w j))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL] THEN
    SUBGOAL_THEN
     `vsum {l | l < n} (\l. cnj((e:num->A->complex) l (w i)) * e l (w j)) =
      vsum (complex_embeddings k) (\g. cnj(g((w:num->A) i)) * g(w j))`
    SUBST1_TAC THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[SYM th]) THEN
      W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE o rand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]];
      MATCH_MP_TAC COMPLEX_EMBEDDINGS_VSUM_CNJ_REAL THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Cx(ring_det real_ring {i | i < n}
        (\i j. Re(vsum {l | l < n}
                 (\l. cnj((e:num->A->complex) l (w i)) * e l (w j))))) =
    cnj(ring_det complex_ring {i | i < n} (\l j. e l ((w:num->A) j))) *
    ring_det complex_ring {i | i < n} (\l j. e l (w j))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`real_ring`; `complex_ring`; `Cx`; `{i:num | i < n}`;
      `\i j. Re(vsum {l | l < n}
                 (\l. cnj((e:num->A->complex) l (w i)) * e l ((w:num->A) j)))`]
     RING_DET_HOMOMORPHISM) THEN
    REWRITE_TAC[cx_hom; FINITE_NUMSEG_LT; REAL_RING_CLAUSES; IN_UNIV] THEN
    DISCH_THEN SUBST1_TAC THEN
    TRANS_TAC EQ_TRANS
     `ring_det complex_ring {i | i < n}
        (\i j. vsum {l | l < n}
                 (\l. cnj((e:num->A->complex) l (w i)) * e l
                  ((w:num->A) j)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`complex_ring`; `{i:num | i < n}`;
      `\i l. cnj((e:num->A->complex) l ((w:num->A) i))`;
      `\l j. (e:num->A->complex) l ((w:num->A) j)`] RING_DET_MUL) THEN
    REWRITE_TAC[COMPLEX_RING_CLAUSES; IN_UNIV; FINITE_NUMSEG_LT] THEN
    ASM_SIMP_TAC[COMPLEX_RING_SUM; FINITE_NUMSEG_LT] THEN
    DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL
     [`complex_ring`; `complex_ring`; `cnj`; `{i:num | i < n}`;
      `\i l. (e:num->A->complex) l ((w:num->A) i)`] RING_DET_HOMOMORPHISM) THEN
    REWRITE_TAC[RING_HOMOMORPHISM_CNJ; FINITE_NUMSEG_LT; COMPLEX_RING_CLAUSES;
                IN_UNIV] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`complex_ring`; `{i:num | i < n}`;
                   `\l j. (e:num->A->complex) l ((w:num->A) j)`]
      RING_DET_TRANSP) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[COMPLEX_MUL_CNJ; GSYM CX_POW; CX_INJ] o
    check (fun th -> free_in `cnj` (concl th) && is_eq(concl th) &&
                     is_comb(lhs(concl th)))) THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`; `e:num->A->complex`]
    NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
  REWRITE_TAC[COMPLEX_NORM_POW; COMPLEX_NORM_CX] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_POW2_ABS]);;

(* With the integral basis indexed by the embeddings (lemma3), conjugation   *)
(* permutes the rows of the matrix by an involution c of the embeddings      *)
(* whose non-fixed points are the non-real ones, so the conjugate of the     *)
(* determinant z is sign(c) z, and sign(c) = (-1)^r2 (lemma2); z^2 = d_K is  *)
(* real and nonzero, so z is real or purely imaginary (lemma1).              *)
let NUMBER_FIELD_DISCRIMINANT_SIGN = prove
 (`!k:A ring.
        number_field k
        ==> (&0 < number_field_discriminant k <=>
             EVEN(CARD(infinite_places k) - CARD(real_embeddings k)))`,
  let lemma1 = prove
   (`!z r. z pow 2 = Cx r /\ ~(r = &0) /\ (cnj z = z \/ cnj z = --z)
           ==> (&0 < r <=> cnj z = z)`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[COMPLEX_EQ; COMPLEX_POW_2; RE_CNJ; IM_CNJ; RE_NEG; IM_NEG;
                complex_mul; RE; IM; RE_CX; IM_CX;
                REAL_ARITH `--x:real = x <=> x = &0`;
                REAL_ARITH `x:real = --x <=> x = &0`] THEN
    MP_TAC(SPEC `Re z` REAL_LE_SQUARE) THEN
    MP_TAC(SPEC `Im z` REAL_LE_SQUARE) THEN
    MAP_EVERY ASM_CASES_TAC [`Im z = &0`; `Re z = &0`] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN REAL_ARITH_TAC)
  and lemma2 = prove
   (`!(p:B->B) s.
        FINITE s /\ (!x. p(p x) = x) /\ (!x. ~(x IN s) ==> p x = x)
        ==> (evenperm p <=> EVEN(CARD {x | ~(p x = x)} DIV 2))`,
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SIGN_INVOLUTION) THEN
    REWRITE_TAC[sign; REAL_POW_NEG; REAL_POW_ONE] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)
  and lemma3 = prove
   (`!k:A ring.
        number_field k
        ==> ?v. (!h. h IN complex_embeddings k ==> v h IN ring_carrier k) /\
                ring_det complex_ring (complex_embeddings k)
                  (\(h:A->complex) (h':A->complex). h(v h')) pow 2 =
                Cx(real_of_int(number_field_discriminant k))`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_TAC `w:num->A` o MATCH_MP RING_OF_INTEGERS_FREE) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP HAS_SIZE_INDEX o
      MATCH_MP COMPLEX_EMBEDDINGS_HAS_SIZE) THEN
    ABBREV_TAC
     `n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)` THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:num->A->complex` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(!i j. i IN {i | i < n} /\ j IN {i | i < n} /\
             (e:num->A->complex) i = e j ==> i = j) /\
      complex_embeddings k = IMAGE e {i | i < n}`
    MP_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      UNDISCH_THEN
       `!x. x IN complex_embeddings k
            ==> (?m. m < n /\ (e:num->A->complex) m = x) /\
                (!m m'. (m < n /\ e m = x) /\ m' < n /\ e m' = x ==> m = m')`
       (K ALL_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)] THEN
    MP_TAC(ISPECL [`e:num->A->complex`; `{i:num | i < n}`]
      INJECTIVE_ON_LEFT_INVERSE) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `f:(A->complex)->num`) THEN
    EXISTS_TAC `(w:num->A) o (f:(A->complex)->num)` THEN
    MP_TAC(ISPECL
     [`complex_ring`; `e:num->A->complex`; `{i:num | i < n}`;
      `\(h:A->complex) (h':A->complex).
         h(((w:num->A) o (f:(A->complex)->num)) h')`]
     RING_DET_REINDEX) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_THEN
     `!i j. i IN {i | i < n} /\ j IN {i | i < n} /\
            (e:num->A->complex) i = e j ==> i = j` (K ALL_TAC) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`ring_of_int k:int->A`; `integer_ring`;
                     `ring_of_integers k:A ring`; `n:num`; `w:num->A`]
        FREE_BASIS_IN_CARRIER) THEN
      ASM_SIMP_TAC[] THEN MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET];
      MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`; `e:num->A->complex`]
        NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_DET_EQ THEN
      ASM_SIMP_TAC[IN_ELIM_THM]]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_COMPLEX_EMBEDDINGS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CARD_INFINITE_PLACES) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `v:(A->complex)->A` STRIP_ASSUME_TAC o
    MATCH_MP lemma3) THEN
  ABBREV_TAC
   `z = ring_det complex_ring (complex_embeddings k)
          (\(h:A->complex) (h':A->complex). h((v:(A->complex)->A) h'))` THEN
  DISCH_TAC THEN
  ABBREV_TAC
   `c = \h:A->complex. if h IN complex_embeddings k
                       then RESTRICTION (ring_carrier k) (cnj o h) else h` THEN
  SUBGOAL_THEN
   `(!h. (c:(A->complex)->(A->complex))(c h) = h) /\
    (!h. ~(h IN complex_embeddings k) ==> c h = h)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN SIMP_TAC[] THEN X_GEN_TAC `h:A->complex` THEN
    ASM_CASES_TAC `(h:A->complex) IN complex_embeddings k` THEN
    ASM_SIMP_TAC[COMPLEX_EMBEDDINGS_CNJ; COMPLEX_EMBEDDINGS_CNJ_CNJ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cnj z = ring_sign complex_ring (c:(A->complex)->(A->complex)) * z`
  MP_TAC THENL
   [UNDISCH_THEN
     `ring_det complex_ring (complex_embeddings k)
        (\(h:A->complex) (h':A->complex). h((v:(A->complex)->A) h')) = z`
     (SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`complex_ring`; `complex_ring`; `cnj`;
                   `complex_embeddings(k:A ring)`;
                   `\(h:A->complex) (h':A->complex). h((v:(A->complex)->A) h')`]
      RING_DET_HOMOMORPHISM) THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_CNJ; COMPLEX_RING_CLAUSES; IN_UNIV] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`complex_ring`; `complex_embeddings(k:A ring)`;
                   `\(h:A->complex) (h':A->complex). h((v:(A->complex)->A) h')`;
                   `c:(A->complex)->(A->complex)`] RING_DET_PERMUTE_ROWS) THEN
    ASM_SIMP_TAC[PERMUTES_INVOLUTION; COMPLEX_RING_CLAUSES] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_DET_EQ THEN
    EXPAND_TAC "c" THEN ASM_SIMP_TAC[RESTRICTION; o_THM];
    REWRITE_TAC[ring_sign; COMPLEX_RING_CLAUSES] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`c:(A->complex)->(A->complex)`;
                 `complex_embeddings(k:A ring)`] lemma2) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `{h | ~((c:(A->complex)->(A->complex)) h = h)} =
    complex_embeddings k DIFF real_embeddings k`
  SUBST1_TAC THENL
   [EXPAND_TAC "c" THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; REAL_EMBEDDINGS_CNJ] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_embeddings k SUBSET complex_embeddings(k:A ring)`
  ASSUME_TAC THENL [REWRITE_TAC[real_embeddings; SUBSET_RESTRICT]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_DIFF] THEN
  SUBGOAL_THEN
   `(CARD(complex_embeddings k) - CARD(real_embeddings(k:A ring))) DIV 2 =
    CARD(infinite_places k) - CARD(real_embeddings k)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `CARD(complex_embeddings k) - CARD(real_embeddings(k:A ring)) =
      2 * (CARD(infinite_places k) - CARD(real_embeddings k))`
    SUBST1_TAC THENL
     [UNDISCH_TAC
       `CARD(complex_embeddings k) + CARD(real_embeddings(k:A ring)) =
        2 * CARD(infinite_places k)` THEN
      ARITH_TAC;
      SIMP_TAC[DIV_MULT; ARITH_EQ]];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[int_lt; int_of_num_th] THEN
  MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_DISCRIMINANT_NONZERO) THEN
  ASM_REWRITE_TAC[int_eq; int_of_num_th] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`z:complex`; `real_of_int(number_field_discriminant(k:A ring))`]
   lemma1) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `evenperm(c:(A->complex)->(A->complex))` THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_MUL_LNEG] THEN
  DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `~(real_of_int(number_field_discriminant(k:A ring)) = &0)` THEN
  UNDISCH_TAC
   `z pow 2 = Cx(real_of_int(number_field_discriminant(k:A ring)))` THEN
  REWRITE_TAC[GSYM CX_INJ] THEN CONV_TAC COMPLEX_RING);;
