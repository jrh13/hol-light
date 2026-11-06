(* ========================================================================= *)
(* Trace, norm and discriminant of a number field through ring homomorphisms *)
(* into an arbitrary field; the discriminant of a power basis; norms of      *)
(* elements of subfields.                                                    *)
(*                                                                           *)
(* Notation: k is a number field, Q = subfield_generated k {ring_0 k} its    *)
(* prime subfield, [k:Q] = extension_degree (Q,k) I, Tr and N the trace and  *)
(* the norm of k over Q, algebra_trace (Q,k) I and algebra_norm (Q,k) I of   *)
(* Library/ring_det.ml.                                                      *)
(*                                                                           *)
(* Main results: for a set E of [k:Q] distinct ring homomorphisms from k     *)
(* into a field l, every homomorphism g : k -> l maps Tr(x) and N(x) to the  *)
(* sum and the product of the h(x), h in E                                   *)
(* (NUMBER_FIELD_TRACE_HOMOMORPHISMS, NUMBER_FIELD_NORM_HOMOMORPHISMS), and  *)
(* the discriminant of a Q-basis w to det(e_i(w_j))^2 for distinct           *)
(* homomorphisms e_0, ..., e_(n-1)                                           *)
(* (NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS); these are the analogues of the *)
(* theorems of ANT/infinite_places.ml for any field in place of C. Into an   *)
(* algebraically closed field of characteristic 0 there are exactly [k:Q]    *)
(* homomorphisms (NUMBER_FIELD_HOMOMORPHISMS_HAS_SIZE). If the minimal       *)
(* polynomial f of a has degree m = [k:Q], the discriminant of the power     *)
(* basis 1, a, ..., a^(m-1) is (-1)^(m(m-1)/2) N(Df(a)) for the derivative   *)
(* Df of f (NUMBER_FIELD_DISCRIMINANT_POWER_BASIS). For a subfield K of k    *)
(* and x in K, Tr_k(x) = [k:K] Tr_K(x) and N_k(x) = N_K(x)^[k:K]             *)
(* (NUMBER_FIELD_TRACE_TOWER, NUMBER_FIELD_NORM_TOWER). If the products of   *)
(* Q-bases e of K = subfield_generated k s1 and f of L = subfield_generated  *)
(* k s2 form a Q-basis of k, then Tr_k(x y) = Tr_K(x) Tr_L(y) for x in K and *)
(* y in L (ALGEBRA_TRACE_PRODUCT_BASIS).                                     *)
(*                                                                           *)
(* Helper: the powers of a generator a with deg f = [k:Q] form a Q-basis of  *)
(* k (NUMBER_FIELD_FREE_BASIS_POWERS).                                       *)
(*                                                                           *)
(* Routes. Trace and norm: for a Q-basis w and an enumeration e_i of E the   *)
(* matrix M = (e_i(w_j)) is invertible (independence of characters,          *)
(* RING_HOMOMORPHISMS_INDEPENDENT, with RING_DET_INDEPENDENT_ROWS; all       *)
(* homomorphisms agree on Q) and M X = diag(e_i(x)) M for the multiplication *)
(* matrix X of x, so RING_TRACE_DET_SIMILAR_DIAGONAL of Library/ring_det.ml  *)
(* applies; the trace matrix of w maps to the product of M with its          *)
(* transpose. Count: the homomorphism of Q into l given by                   *)
(* PRIME_SUBFIELD_HOMOMORPHISM_EXISTS has [k:Q] extensions to k              *)
(* (HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS, SEPARABLE_EXTENSION_CHAR0). Power *)
(* basis: in an algebraic closure l of k                                     *)
(* (ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) the m homomorphisms e_i give m       *)
(* distinct roots x_i = e_i(a) of the image of f, so that image is the       *)
(* product of the X - x_i (MONIC_POLY_EQ_ROOTS_PRODUCT) and e_i(Df(a)) is    *)
(* the product of the x_i - x_j for j <> i                                   *)
(* (POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS); the discriminant maps to the      *)
(* square of the Vandermonde determinant of the x_i (RING_DET_VANDERMONDE),  *)
(* and that square is (-1)^(m(m-1)/2) times the product of all x_i - x_j     *)
(* with i <> j (RING_PRODUCT_DIFFERENCES_SQUARE). Tower: the tower           *)
(* Q_K -> K -> k (ALGEBRA_TRACE_NORM_INTERMEDIATE), with the prime subfield  *)
(* Q_K of K in place of Q (ALGEBRA_TRACE_NORM_EQ_IMAGE,                      *)
(* PRIME_SUBFIELD_MONOMORPHIC_IMAGE).                                        *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/fieldtheory.ml (extension_degree,    *)
(* minimal_polynomial, algebraic closures, RING_HOMOMORPHISMS_INDEPENDENT,   *)
(* HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS, the powers of an algebraic         *)
(* element, the trace and the norm of field extensions), Library/ring_det.ml *)
(* (RING_DET_VANDERMONDE, POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS,              *)
(* RING_PRODUCT_DIFFERENCES_SQUARE, algebra_trace, algebra_norm),            *)
(* ANT/numfield.ml; MONIC_POLY_EQ_ROOTS_PRODUCT is in ringtheory.ml.         *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "ANT/algmisc.ml";;
needs "Library/ring_det.ml";;
needs "ANT/numfield.ml";;

(* ------------------------------------------------------------------------- *)
(* Trace, norm and discriminant through homomorphisms into a field.          *)
(* ------------------------------------------------------------------------- *)

(* For a Q-basis w and distinct homomorphisms e_i, i < n, into a field l,  *)
(* the matrix (e_i(w_j)) is invertible: a relation sum_i c_i e_i(w_j) = 0   *)
(* for all j extends to all of k by Q-linearity, so all c_i vanish by       *)
(* RING_HOMOMORPHISMS_INDEPENDENT (lemma_det). With the multiplication      *)
(* matrix X of x mapped by g it satisfies M X = diag(e_i(x)) M, which gives *)
(* the trace and the norm as the sum and the product of the e_i(x)          *)
(* (lemma_core); the discriminant is det of the trace matrix, which maps to *)
(* the product of M with its transpose.                                     *)
let NUMBER_FIELD_TRACE_HOMOMORPHISMS,
    NUMBER_FIELD_NORM_HOMOMORPHISMS,
    NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS =
  let lemma_det = prove
   (`!k (l:B ring) n w (e:num->A->B) g.
          field k /\ field l /\
          free_basis (subfield_generated k {ring_0 k},k) I n w /\
          (!i. i < n ==> ring_homomorphism(k,l) (e i)) /\
          (!i j. i < n /\ j < n /\ (!x. x IN ring_carrier k ==> e i x = e j x)
                 ==> i = j) /\
          ring_homomorphism(k,l) g
          ==> ~(ring_det l {i | i < n} (\i j. e i (w j)) = ring_0 l)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!i j. i IN {i | i < n} /\ j IN {i | i < n} /\ ~(i = j)
            ==> ?x. x IN ring_carrier k /\ ~((e:num->A->B) i x = e j x)`
    MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o check (is_imp o snd o strip_forall o concl) o
      check (fun th -> rand(snd(strip_forall(concl th))) = `i:num = j`)) THEN
    DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
    SUBGOAL_THEN
     `!i x. i < n /\ x IN ring_carrier k
            ==> (e:num->A->B) i x IN ring_carrier l`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`; `{i:num | i < n}`;
                   `\i j. (e:num->A->B) i ((w:num->A) j)`]
      RING_DET_INDEPENDENT_ROWS) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `c:num->B` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`e:num->A->B`; `k:A ring`; `l:B ring`; `{i:num | i < n}`;
                   `c:num->B`]
      RING_HOMOMORPHISMS_INDEPENDENT) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; FINITE_NUMSEG_LT] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                   `n:num`; `w:num->A`; `y:A`] BASIS_COORDINATES) THEN
    ASM_REWRITE_TAC[I_THM] THEN
    ABBREV_TAC
     `q = basis_coordinates (subfield_generated k {ring_0 k},k) (I:A->A)
            n w y` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    SUBGOAL_THEN
     `!j. j < n ==> (q:num->A) j IN ring_carrier k /\
                    (g:A->B)(q j) IN ring_carrier l`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER;
                    RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!i j. i < n /\ j < n
            ==> (e:num->A->B) i ((q:num->A) j) = g(q j)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`(e:num->A->B) i`; `g:A->B`; `k:A ring`; `l:B ring`;
                     `{ring_0 k:A}`]
        RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED) THEN
      ASM_SIMP_TAC[IN_SING;
                   ISPECL [`k:A ring`; `l:B ring`] RING_HOMOMORPHISM_0];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum l {i | i < n}
        (\i. ring_mul l ((c:num->B) i)
               (ring_sum l {j | j < n}
                  (\j. ring_mul l ((g:A->B)((q:num->A) j))
                                  ((e:num->A->B) i (w j)))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN AP_TERM_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `(e:num->A->B) i`;
                     `{j:num | j < n}`; `q:num->A`; `w:num->A`]
        RING_HOMOMORPHISM_SUM_MUL) THEN
      ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
      DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_MUL_SWAP o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN
    ASM_SIMP_TAC[IN_ELIM_THM; RING_MUL_RZERO]) in
  let lemma_core = prove
   (`!k (l:B ring) n w (e:num->A->B) g x.
          number_field k /\ field l /\
          free_basis (subfield_generated k {ring_0 k},k) I n w /\
          (!i. i < n ==> ring_homomorphism(k,l) (e i)) /\
          (!i j. i < n /\ j < n /\ (!x. x IN ring_carrier k ==> e i x = e j x)
                 ==> i = j) /\
          ring_homomorphism(k,l) g /\ x IN ring_carrier k
          ==> g(algebra_trace (subfield_generated k {ring_0 k},k) I x) =
              ring_sum l {i | i < n} (\i. e i x) /\
              g(algebra_norm (subfield_generated k {ring_0 k},k) I x) =
              ring_product l {i | i < n} (\i. e i x)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `n:num`; `w:num->A`;
                   `e:num->A->B`; `g:A->B`] lemma_det) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(K ALL_TAC o check (is_imp o snd o strip_forall o concl) o
      check (fun th -> rand(snd(strip_forall(concl th))) = `i:num = j`)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
    SUBGOAL_THEN
     `ring_homomorphism(subfield_generated k {ring_0 k},l) (g:A->B)`
    ASSUME_TAC THENL
     [SUBST1_TAC(SYM(CONJUNCT2(ISPEC `g:A->B` I_O_ID))) THEN
      MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `k:A ring` THEN
      ASM_REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION];
      ALL_TAC] THEN
    ABBREV_TAC
     `X = mul_matrix (subfield_generated k {ring_0 k},k) (I:A->A)
                                n w x` THEN
    SUBGOAL_THEN
     `!i j. i < n /\ j < n
            ==> (X:num->num->A) i j IN
                ring_carrier(subfield_generated k {ring_0 k})`
    ASSUME_TAC THENL
     [EXPAND_TAC "X" THEN ASM_SIMP_TAC[MUL_MATRIX_IN_CARRIER];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`; `{i:num | i < n}`;
                   `\i j:num. (e:num->A->B) i ((w:num->A) j)`;
                   `\i j:num. (g:A->B)((X:num->num->A) i j)`;
                   `\i:num. (e:num->A->B) i x`]
       RING_TRACE_DET_SIMILAR_DIAGONAL) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FIELD_UNIT; RING_DET] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
        ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
        MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC] THEN
      SUBGOAL_THEN `ring_homomorphism(k,l) ((e:num->A->B) a)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                     `n:num`; `w:num->A`; `x:A`; `b:num`]
        MUL_MATRIX_EXPAND) THEN
      ASM_REWRITE_TAC[I_THM] THEN
      DISCH_THEN(MP_TAC o AP_TERM `(e:num->A->B) a`) THEN
      MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `(e:num->A->B) a`;
                     `{i:num | i < n}`; `\i. (X:num->num->A) i b`; `w:num->A`]
        RING_HOMOMORPHISM_SUM_MUL) THEN
      ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
        DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL (ASSUME
       `ring_homomorphism(k,l) ((e:num->A->B) a)`)] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SUM_EQ THEN
      X_GEN_TAC `t:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`(e:num->A->B) a`; `g:A->B`; `k:A ring`; `l:B ring`;
                     `{ring_0 k:A}`]
        RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED) THEN
      ASM_SIMP_TAC[IN_SING;
                   ISPECL [`k:A ring`; `l:B ring`] RING_HOMOMORPHISM_0] THEN
      DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC RING_MUL_SYM THEN
      ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
      DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM))] THEN
    MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                   `n:num`; `w:num->A`; `x:A`] ALGEBRA_NORM_FREE_BASIS) THEN
    MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                   `n:num`; `w:num->A`; `x:A`] ALGEBRA_TRACE_FREE_BASIS) THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_SUM (ASSUME
       `ring_homomorphism(subfield_generated k {ring_0 k},l) (g:A->B)`);
                   FINITE_NUMSEG_LT; IN_ELIM_THM; o_DEF];
      MATCH_MP_TAC RING_DET_HOMOMORPHISM THEN
      ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]]) in
  let th1, th2 = (CONJ_PAIR o prove)
   (`(!(k:A ring) (l:B ring) E g x.
          number_field k /\ field l /\
          E HAS_SIZE extension_degree (subfield_generated k {ring_0 k},k) I /\
          (!h. h IN E ==> ring_homomorphism(k,l) h) /\
          E SUBSET EXTENSIONAL(ring_carrier k) /\
          ring_homomorphism(k,l) g /\ x IN ring_carrier k
          ==> g(algebra_trace (subfield_generated k {ring_0 k},k) I x) =
              ring_sum l E (\h. h x)) /\
     (!(k:A ring) (l:B ring) E g x.
          number_field k /\ field l /\
          E HAS_SIZE extension_degree (subfield_generated k {ring_0 k},k) I /\
          (!h. h IN E ==> ring_homomorphism(k,l) h) /\
          E SUBSET EXTENSIONAL(ring_carrier k) /\
          ring_homomorphism(k,l) g /\ x IN ring_carrier k
          ==> g(algebra_norm (subfield_generated k {ring_0 k},k) I x) =
              ring_product l E (\h. h x))`,
    REWRITE_TAC[AND_FORALL_THM;
                TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_TAC `w:num->A` o MATCH_MP NUMBER_FIELD_FREE_BASIS) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP HAS_SIZE_INDEX) THEN
    ABBREV_TAC
     `n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)` THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:num->A->B` (CONJUNCTS_THEN2 ASSUME_TAC
      MP_TAC)) THEN
    DISCH_THEN(fun th ->
      SUBGOAL_THEN `!i j. i < n /\ j < n /\ (e:num->A->B) i = e j ==> i = j`
      ASSUME_TAC THENL [ASM_MESON_TAC[th]; ALL_TAC] THEN
      SUBGOAL_THEN `E = IMAGE (e:num->A->B) {i | i < n}` SUBST_ALL_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[th];
        ALL_TAC]) THEN
    MP_TAC(ISPECL [`l:B ring`; `e:num->A->B`; `\h:A->B. h x`; `{i:num | i < n}`]
      RING_SUM_IMAGE) THEN
    MP_TAC(ISPECL [`l:B ring`; `e:num->A->B`; `\h:A->B. h x`; `{i:num | i < n}`]
      RING_PRODUCT_IMAGE) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; o_DEF] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    MATCH_MP_TAC lemma_core THEN EXISTS_TAC `w:num->A` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FORALL_IN_IMAGE; SUBSET; IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC `ring_carrier k:A->bool` THEN
    ASM_SIMP_TAC[]) in
  let th3 = prove
   (`!(k:A ring) (l:B ring) n w e g.
          number_field k /\ field l /\
          free_basis (subfield_generated k {ring_0 k},k) I n w /\
          (!i. i < n ==> ring_homomorphism(k,l) (e i)) /\
          (!i j. i < n /\ j < n /\
                 (!x. x IN ring_carrier k ==> e i x = e j x)
                 ==> i = j) /\
          ring_homomorphism(k,l) g
          ==> g(basis_discriminant (subfield_generated k {ring_0 k},k) I
                                       n w) =
              ring_pow l (ring_det l {i | i < n} (\i j. e i (w j))) 2`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!y. y IN ring_carrier k
          ==> (g:A->B)(algebra_trace (subfield_generated k {ring_0 k},k) I y) =
              ring_sum l {i | i < n} (\i. (e:num->A->B) i y)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `n:num`; `w:num->A`;
                     `e:num->A->B`; `g:A->B`; `y:A`] lemma_core) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_imp o snd o strip_forall o concl) o
        check (fun th -> rand(snd(strip_forall(concl th))) = `i:num = j`))] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
    SUBGOAL_THEN
     `ring_homomorphism(subfield_generated k {ring_0 k},l) (g:A->B)`
    ASSUME_TAC THENL
     [SUBST1_TAC(SYM(CONJUNCT2(ISPEC `g:A->B` I_O_ID))) THEN
      MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `k:A ring` THEN
      ASM_REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION];
      ALL_TAC] THEN
    REWRITE_TAC[basis_discriminant] THEN
    MP_TAC(ISPECL
     [`subfield_generated k {ring_0 k:A}`; `l:B ring`; `g:A->B`;
      `{i:num | i < n}`;
      `\i j:num. algebra_trace (subfield_generated k {ring_0 k},k) (I:A->A)
                   (ring_mul k (w i) (w j))`] RING_DET_HOMOMORPHISM) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT; ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
    DISCH_THEN SUBST1_TAC THEN
    TRANS_TAC EQ_TRANS
     `ring_det l {i | i < n}
        (\i j. ring_sum l {t | t < n}
                 (\t. ring_mul l ((e:num->A->B) t (w i)) (e t (w j))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `ring_mul k ((w:num->A) a) (w b) IN ring_carrier k`
      ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN
      X_GEN_TAC `t:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      SUBGOAL_THEN `ring_homomorphism(k,l) ((e:num->A->B) t)` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]);
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!i j. i < n /\ j < n ==> (e:num->A->B) i (w j) IN ring_carrier l`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`; `{i:num | i < n}`;
                   `\i t:num. (e:num->A->B) t ((w:num->A) i)`;
                   `\t j:num. (e:num->A->B) t ((w:num->A) j)`]
      RING_DET_MUL) THEN
    MP_TAC(ISPECL [`l:B ring`; `{i:num | i < n}`;
                   `\i j:num. (e:num->A->B) i ((w:num->A) j)`]
      RING_DET_TRANSP) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_POW_2; RING_DET]) in
  th1, th2, th3;;

(* All homomorphisms agree on Q, so they are the extensions of the          *)
(* homomorphism of Q into l given by PRIME_SUBFIELD_HOMOMORPHISM_EXISTS,    *)
(* which HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS counts.                       *)
let NUMBER_FIELD_HOMOMORPHISMS_HAS_SIZE = prove
 (`!(k:A ring) (l:B ring).
        number_field k /\ algebraically_closed_field l /\ ring_char l = 0
        ==> {h | ring_homomorphism(k,l) h /\ h IN EXTENSIONAL(ring_carrier k)}
            HAS_SIZE extension_degree (subfield_generated k {ring_0 k},k) I`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [number_field]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [algebraically_closed_field]) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`]
    PRIME_SUBFIELD_HOMOMORPHISM_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `g:A->B`) THEN
  MP_TAC(ISPECL [`I:A->A`; `g:A->B`; `subfield_generated k {ring_0 k:A}`;
                 `k:A ring`; `l:B ring`]
    HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS) THEN
  ASM_SIMP_TAC[SEPARABLE_EXTENSION_CHAR0; FINITE_IMP_ALGEBRAIC_EXTENSION;
               RING_CHAR_SUBFIELD_GENERATED] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ring_homomorphism_extensions; I_THM; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `h:A->B` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->B`; `subfield_generated k {ring_0 k:A}`;
                 `l:B ring`; `{ring_0(subfield_generated k {ring_0 k:A})}`]
    RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED) THEN
  REWRITE_TAC[PRIME_SUBFIELD_SUBFIELD_GENERATED; IN_SING] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                   `ring_carrier(subfield_generated k {ring_0 k:A})`]
      RING_HOMOMORPHISM_FROM_SUBRING_GENERATED) THEN
    ASM_REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`subfield_generated k {ring_0 k:A}`; `l:B ring`; `g:A->B`]
      RING_HOMOMORPHISM_0) THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] RING_HOMOMORPHISM_0) THEN
    ASM_REWRITE_TAC[CONJUNCT1(CONJUNCT2 SUBFIELD_GENERATED)] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The discriminant of a power basis.                                        *)
(* ------------------------------------------------------------------------- *)

(* The powers a^i, i < [k:Q], are distinct and independent                   *)
(* (MINIMAL_POLYNOMIAL_POWERS_HAS_SIZE,                                      *)
(* RING_INDEPENDENT_MINIMAL_POLYNOMIAL_POWERS); an independent set of the    *)
(* full dimension is a basis (MATROID_BASIS_LARGE_INDEPENDENT).              *)
let NUMBER_FIELD_FREE_BASIS_POWERS = prove
 (`!k:A ring a.
        number_field k /\ a IN ring_carrier k /\
        poly_deg (subfield_generated k {ring_0 k})
          (minimal_polynomial (subfield_generated k {ring_0 k},k) I a) =
        extension_degree (subfield_generated k {ring_0 k},k) I
        ==> free_basis (subfield_generated k {ring_0 k},k) I
              (extension_degree (subfield_generated k {ring_0 k},k) I)
              (\i. ring_pow k a i)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [number_field]) THEN
  SUBGOAL_THEN
   `field_extension(subfield_generated k {ring_0 k},k) (I:A->A) /\
    algebraic_over(subfield_generated k {ring_0 k},k) I a`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED;
                 NUMBER_FIELD_ALGEBRAIC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `a:A`] MINIMAL_POLYNOMIAL_POWERS_HAS_SIZE) THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `a:A`] RING_INDEPENDENT_MINIMAL_POLYNOMIAL_POWERS) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FREE_BASIS_FIELD; FIELD_SUBFIELD_GENERATED;
               RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM RING_MATROID_BASIS;
                 FIELD_SUBFIELD_GENERATED;
                 RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN
    MATCH_MP_TAC MATROID_BASIS_LARGE_INDEPENDENT THEN
    ASM_SIMP_TAC[RING_MATROID_INDEPENDENT; FIELD_SUBFIELD_GENERATED;
                 RING_HOMOMORPHISM_SUBFIELD_INCLUSION;
                 GSYM FINITE_EXTENSION_RING_MATROID] THEN
    UNDISCH_TAC
     `finite_extension(subfield_generated k {ring_0 k},k) (I:A->A)` THEN
    REWRITE_TAC[FINITE_EXTENSION_RING_MATROID; extension_degree] THEN
    ASM_SIMP_TAC[LE_REFL];
    MP_TAC(ISPECL
     [`\i. ring_pow k (a:A) i`;
      `{i | i < extension_degree(subfield_generated k {ring_0 k},k)
                 (I:A->A)}`]
      CARD_IMAGE_EQ_INJ) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT; IN_ELIM_THM]]);;

(* With the m homomorphisms e_i of k into an algebraic closure l and x_i =   *)
(* e_i(a), the discriminant maps to the square of the Vandermonde            *)
(* determinant of the x_i, while the image of f is the product of the X -    *)
(* x_i, so e_i(Df(a)) is the product of the x_i - x_j for j <> i;             *)
(* RING_PRODUCT_DIFFERENCES_SQUARE compares the two products.                *)
let NUMBER_FIELD_DISCRIMINANT_POWER_BASIS =
  prove
   (`!(k:A ring) a f m.
          number_field k /\ a IN ring_carrier k /\
          f = minimal_polynomial (subfield_generated k {ring_0 k},k) I a /\
          m = extension_degree (subfield_generated k {ring_0 k},k) I /\
          poly_deg (subfield_generated k {ring_0 k}) f = m
          ==> basis_discriminant (subfield_generated k {ring_0 k},k) I m
                (\i. ring_pow k a i) =
              ring_mul k
                (ring_pow k (ring_neg k (ring_1 k)) ((m * (m - 1)) DIV 2))
                (algebra_norm (subfield_generated k {ring_0 k},k) I
                   (poly_extend (subfield_generated k {ring_0 k},k) I (\v. a)
                      (poly_deriv (subfield_generated k {ring_0 k}) f)))`,
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
    ABBREV_TAC
     `y = poly_extend (subfield_generated k {ring_0 k},k) (I:A->A) (\v. a)
            (poly_deriv (subfield_generated k {ring_0 k}) f)` THEN
    SUBGOAL_THEN `(y:A) IN ring_carrier k` ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN REWRITE_TAC[POLY_EXTEND]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(g:A->A#num)(algebra_norm (subfield_generated k {ring_0 k},k) I y) =
      ring_product l {i | i < m}
        (\i. ring_product l ({t | t < m} DELETE i)
               (\t. ring_sub l ((e:num->A->A#num) i a) (e t a)))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `l:(A#num)ring`;
                     `IMAGE (e:num->A->A#num) {i | i < m}`;
                     `g:A->A#num`; `y:A`] NUMBER_FIELD_NORM_HOMOMORPHISMS) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[FORALL_IN_IMAGE; SUBSET; IN_ELIM_THM];
        DISCH_THEN SUBST1_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_IMAGE o
        lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN UNDISCH_TAC
         `!i j. i < m /\ j < m ==> ((e:num->A->A#num) i = e j <=> i = j)` THEN
        MESON_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN
      ASM_SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(g:A->A#num)(basis_discriminant (subfield_generated k {ring_0 k},k) I
                     m (\i. ring_pow k a i)) =
      ring_pow l (ring_product l {j | j < m}
                   (\j. ring_product l {i | i < j}
                          (\i. ring_sub l ((e:num->A->A#num) j a) (e i a)))) 2`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `l:(A#num)ring`; `m:num`;
                     `\i. ring_pow k (a:A) i`; `e:num->A->A#num`; `g:A->A#num`]
        NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[] THEN MAP_EVERY X_GEN_TAC [`u:num`; `v:num`] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `(e:num->A->A#num) u = e v` MP_TAC THENL
         [MATCH_MP_TAC EXTENSIONAL_EQ THEN
          EXISTS_TAC `ring_carrier k:A->bool` THEN ASM_SIMP_TAC[];
          ASM_SIMP_TAC[]];
        DISCH_THEN SUBST1_TAC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      TRANS_TAC EQ_TRANS
       `ring_det l {i | i < m}
          (\i j. ring_pow l ((e:num->A->A#num) i a) j)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN
        MP_TAC(ISPECL [`k:A ring`; `l:(A#num)ring`; `(e:num->A->A#num) i`]
          RING_HOMOMORPHISM_POW) THEN
        ASM_SIMP_TAC[];
        MP_TAC(BETA_RULE(ISPECL [`l:(A#num)ring`; `m:num`;
                                 `\i. (e:num->A->A#num) i a`]
          RING_DET_VANDERMONDE)) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `algebra_norm (subfield_generated k {ring_0 k},k) I (y:A) IN
      ring_carrier k`
    ASSUME_TAC THENL
     [MESON_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER;
                RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
      ALL_TAC] THEN
    UNDISCH_TAC `ring_monomorphism(k,l) (g:A->A#num)` THEN
    REWRITE_TAC[ring_monomorphism] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[basis_discriminant] THEN
      MESON_TAC[RING_DET; RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
      ASM_SIMP_TAC[RING_MUL; RING_POW; RING_NEG; RING_1];
      ALL_TAC] THEN
    MAP_EVERY (fun th -> ASM_SIMP_TAC[MATCH_MP th (ASSUME
      `ring_homomorphism(k,l) (g:A->A#num)`); RING_POW; RING_NEG; RING_1])
     [RING_HOMOMORPHISM_MUL; RING_HOMOMORPHISM_POW; RING_HOMOMORPHISM_NEG;
      RING_HOMOMORPHISM_1] THEN
    MP_TAC(BETA_RULE(ISPECL [`l:(A#num)ring`; `\i. (e:num->A->A#num) i a`;
                             `m:num`] RING_PRODUCT_DIFFERENCES_SQUARE)) THEN
    ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Traces and norms of elements of a subfield.                               *)
(* ------------------------------------------------------------------------- *)

(* For a subfield K of k and x in K: Tr_k(x) = [k:K] Tr_K(x) and N_k(x) =    *)
(* N_K(x)^[k:K], by ALGEBRA_TRACE_NORM_INTERMEDIATE for the tower            *)
(* Q_K -> K -> k, where Q_K is the prime subfield of K; it has the same      *)
(* elements as the prime subfield of k (PRIME_SUBFIELD_MONOMORPHIC_IMAGE),   *)
(* so ALGEBRA_TRACE_NORM_EQ_IMAGE identifies the two traces and norms of k.  *)
let NUMBER_FIELD_TRACE_TOWER,NUMBER_FIELD_NORM_TOWER = (CONJ_PAIR o prove)
 (`(!(k:A ring) K x.
        number_field k /\ field_extension(K,k) I /\ x IN ring_carrier K
        ==> algebra_trace (subfield_generated k {ring_0 k},k) I x =
            ring_mul k (ring_of_num k (extension_degree (K,k) I))
              (algebra_trace (subfield_generated K {ring_0 K},K) I x)) /\
   (!(k:A ring) K x.
        number_field k /\ field_extension(K,k) I /\ x IN ring_carrier K
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I x =
            ring_pow k (algebra_norm (subfield_generated K {ring_0 K},K) I x)
              (extension_degree (K,k) I))`,
  REWRITE_TAC[AND_FORALL_THM;
              TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN
   `field_extension(subfield_generated K {ring_0 K},K) (I:A->A) /\
    field_extension(subfield_generated k {ring_0 k},k) (I:A->A) /\
    field_extension(subfield_generated K {ring_0 K},k) (I:A->A)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED] THEN
    MP_TAC(ISPECL [`I:A->A`; `I:A->A`; `subfield_generated K {ring_0 K:A}`;
                   `K:A ring`; `k:A ring`] FIELD_EXTENSION_TRANS) THEN
    ASM_REWRITE_TAC[I_O_ID; FIELD_EXTENSION_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; I_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`I:A->A`; `I:A->A`; `subfield_generated K {ring_0 K:A}`;
                 `subfield_generated k {ring_0 k:A}`; `k:A ring`; `x:A`]
    ALGEBRA_TRACE_NORM_EQ_IMAGE) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[field_extension]) THEN
    ASM_REWRITE_TAC[IMAGE_I] THEN
    MP_TAC(ISPECL [`K:A ring`; `k:A ring`; `I:A->A`]
      PRIME_SUBFIELD_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[IMAGE_I];
    REWRITE_TAC[I_THM] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM))] THEN
  MP_TAC(ISPECL [`I:A->A`; `I:A->A`; `subfield_generated K {ring_0 K:A}`;
                 `K:A ring`; `k:A ring`; `x:A`]
    ALGEBRA_TRACE_NORM_INTERMEDIATE) THEN
  ASM_REWRITE_TAC[I_O_ID; I_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED; RING_OF_NUM_SUBFIELD_GENERATED;
              RING_POW_SUBFIELD_GENERATED] THEN
  SUBGOAL_THEN
   `algebra_trace (subfield_generated K {ring_0 K},K) I (x:A) IN
    ring_carrier K /\
    algebra_norm (subfield_generated K {ring_0 K},K) I (x:A) IN
    ring_carrier K`
  STRIP_ASSUME_TAC THENL
   [MESON_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER;
              RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:A ring`; `k:A ring`; `I:A->A`] RING_HOMOMORPHISM_MUL) THEN
  MP_TAC(ISPECL [`K:A ring`; `k:A ring`; `I:A->A`] RING_HOMOMORPHISM_POW) THEN
  MP_TAC(ISPECL [`K:A ring`; `k:A ring`; `I:A->A`]
    RING_HOMOMORPHISM_RING_OF_NUM) THEN
  ASM_REWRITE_TAC[I_THM] THEN REPEAT DISCH_TAC THEN
  ASM_SIMP_TAC[RING_OF_NUM]);;

(* The trace on a product basis: if e and f are free bases of the subfields  *)
(* generated by s1 and s2 over the prime subfield and the products e_i f_j a *)
(* free basis of k, the trace of x y with x, y in the two subfields is the   *)
(* product of their traces.                                                  *)
let ALGEBRA_TRACE_PRODUCT_BASIS = prove
 (`!(k:A ring) s1 s2 P R e f x y.
        field k /\
        free_basis (subfield_generated k {ring_0 k},subfield_generated k s1)
                   I P e /\
        free_basis (subfield_generated k {ring_0 k},subfield_generated k s2)
                   I R f /\
        free_basis (subfield_generated k {ring_0 k},k) I (P * R)
                   (\t. ring_mul k (e (t MOD P)) (f (t DIV P))) /\
        x IN ring_carrier(subfield_generated k s1) /\
        y IN ring_carrier(subfield_generated k s2)
        ==> algebra_trace (subfield_generated k {ring_0 k},k) I
              (ring_mul k x y) =
            ring_mul k
              (algebra_trace (subfield_generated k {ring_0 k},
                              subfield_generated k s1) I x)
              (algebra_trace (subfield_generated k {ring_0 k},
                              subfield_generated k s2) I y)`,
  let sum_lemma = prove
   (`!(k:A ring) s t (g:num->A) h.
        FINITE t /\
        (!i. i IN t ==> g i IN ring_carrier(subfield_generated k s) /\
                        h i IN ring_carrier(subfield_generated k s))
        ==> ring_sum (subfield_generated k s) t
              (\i. ring_mul (subfield_generated k s) (g i) (h i)) =
            ring_sum k t (\i. ring_mul k (g i) (h i))`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\i. ring_mul (subfield_generated k s) ((g:num->A) i) (h i)`;
                   `t:num->bool`] (MATCH_MP RING_HOMOMORPHISM_SUM
     (ISPECL [`k:A ring`; `s:A->bool`]
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION))) THEN
    ASM_SIMP_TAC[RING_MUL; I_THM; I_O_ID] THEN
    REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. ring_carrier(subfield_generated k {ring_0 k}) SUBSET
        ring_carrier(subfield_generated (k:A ring) s)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
    ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED; SING_SUBSET; IN_SUBFIELD_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. ring_homomorphism(subfield_generated k {ring_0 k},
                          subfield_generated (k:A ring) s) I`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    ASM_REWRITE_TAC[ring_homomorphism; CONJUNCT2 SUBFIELD_GENERATED; I_THM;
                    IMAGE_I];
    ALL_TAC] THEN
  ABBREV_TAC `a = mul_matrix (subfield_generated k {ring_0 k},
                              subfield_generated k s1) I P e (x:A)` THEN
  ABBREV_TAC `b = mul_matrix (subfield_generated k {ring_0 k},
                              subfield_generated k s2) I R f (y:A)` THEN
  SUBGOAL_THEN
   `(!i j. i < P /\ j < P
           ==> (a:num->num->A) i j IN
               ring_carrier(subfield_generated k {ring_0 k})) /\
    (!i j. i < R /\ j < R
           ==> (b:num->num->A) i j IN
               ring_carrier(subfield_generated k {ring_0 k}))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    ASM_MESON_TAC[MUL_MATRIX_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. i < P
         ==> ring_mul k x (e i) =
             ring_sum k {j | j < P}
               (\j. ring_mul k ((a:num->num->A) j i) (e j))) /\
    (!i. i < R
         ==> ring_mul k y (f i) =
             ring_sum k {j | j < R}
               (\j. ring_mul k ((b:num->num->A) j i) (f j)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`;
                     `subfield_generated k s1:A ring`; `P:num`;
                     `e:num->A`; `x:A`; `i:num`] MUL_MATRIX_EXPAND);
      MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`;
                     `subfield_generated k s2:A ring`; `R:num`;
                     `f:num->A`; `y:A`; `i:num`] MUL_MATRIX_EXPAND)] THEN
    ASM_REWRITE_TAC[I_THM] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) sum_lemma o lhand o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    (ANTS_TAC THENL
      [ASM_MESON_TAC[SUBSET; FREE_BASIS_IN_CARRIER]; ALL_TAC]) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `x IN ring_carrier k /\ y IN ring_carrier k /\
    (!i. i < P ==> (e:num->A) i IN ring_carrier k) /\
    (!i. i < R ==> (f:num->A) i IN ring_carrier k) /\
    (!i j. i < P /\ j < P ==> (a:num->num->A) i j IN ring_carrier k) /\
    (!i j. i < R /\ j < R ==> (b:num->num->A) i j IN ring_carrier k)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `s1:A->bool`]
      RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
    MP_TAC(ISPECL [`k:A ring`; `s2:A->bool`]
      RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
    MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`]
      RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
    MP_TAC(MATCH_MP FREE_BASIS_IN_CARRIER (ASSUME
     `free_basis (subfield_generated k {ring_0 k},subfield_generated k s1)
                 I P (e:num->A)`)) THEN
    MP_TAC(MATCH_MP FREE_BASIS_IN_CARRIER (ASSUME
     `free_basis (subfield_generated k {ring_0 k},subfield_generated k s2)
                 I R (f:num->A)`)) THEN
    MAP_EVERY UNDISCH_TAC
     [`!i j. i < P /\ j < P
             ==> (a:num->num->A) i j IN
                 ring_carrier(subfield_generated k {ring_0 k})`;
      `!i j. i < R /\ j < R
             ==> (b:num->num->A) i j IN
                 ring_carrier(subfield_generated k {ring_0 k})`;
      `(x:A) IN ring_carrier(subfield_generated k s1)`;
      `(y:A) IN ring_carrier(subfield_generated k s2)`] THEN
    REWRITE_TAC[SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u t. u < P * R /\ t < P * R
          ==> mul_matrix (subfield_generated k {ring_0 k},k) I
                (P * R) (\t. ring_mul k (e (t MOD P)) (f (t DIV P)))
                (ring_mul k x y) u t =
              ring_mul k ((a:num->num->A) (u MOD P) (t MOD P))
                         ((b:num->num->A) (u DIV P) (t DIV P))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[mul_matrix] THEN
    SUBGOAL_THEN `~(P = 0) /\ t MOD P < P /\ t DIV P < R` STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `P = 0` THENL
       [ASM_MESON_TAC[MULT_CLAUSES; LT]; ALL_TAC] THEN
      ASM_SIMP_TAC[MOD_LT_EQ; RDIV_LT_EQ];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`; `P:num * R`;
      `\t. ring_mul k ((e:num->A) (t MOD P)) ((f:num->A) (t DIV P))`;
      `ring_mul k (ring_mul k x y)
         (ring_mul k ((e:num->A) (t MOD P)) ((f:num->A) (t DIV P)))`;
      `\u. ring_mul k ((a:num->num->A) (u MOD P) (t MOD P))
                      ((b:num->num->A) (u DIV P) (t DIV P))`]
      BASIS_COORDINATES_UNIQUE) THEN
    REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION; I_THM] THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [ALL_TAC; DISCH_THEN(MP_TAC o SPEC `u:num`) THEN ASM_REWRITE_TAC[]] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `v:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(P = 0) ==> v MOD P < P /\ v DIV P < R` MP_TAC THENL
       [ASM_SIMP_TAC[MOD_LT_EQ; RDIV_LT_EQ];
        ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
      MP_TAC(ISPECL [`subfield_generated k {ring_0 k:A}`;
                     `(a:num->num->A) (v MOD P) (t MOD P)`;
                     `(b:num->num->A) (v DIV P) (t DIV P)`] RING_MUL) THEN
      ASM_SIMP_TAC[CONJUNCT2 SUBFIELD_GENERATED];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN
    TRANS_TAC EQ_TRANS
     `ring_mul k (ring_mul k x ((e:num->A) (t MOD P)))
                 (ring_mul k y ((f:num->A) (t DIV P)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_mul r (ring_mul r x y) (ring_mul r e f) =
        ring_mul r (ring_mul r x e) (ring_mul r y (f:A))`) THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_MUL_MOD_DIV o
      lhand o snd) THEN
    ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `v:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `v MOD P < P /\ v DIV P < R` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[MOD_LT_EQ; RDIV_LT_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC(RING_RULE
     `ring_mul r (ring_mul r a e) (ring_mul r b f) =
      ring_mul r (ring_mul r a b) (ring_mul r e (f:A))`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `P:num * R`;
                 `\t. ring_mul k ((e:num->A) (t MOD P)) ((f:num->A) (t DIV P))`;
                 `ring_mul k x y:A`] ALGEBRA_TRACE_FREE_BASIS) THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`;
                 `subfield_generated k s1:A ring`; `P:num`; `e:num->A`;
                 `x:A`] ALGEBRA_TRACE_FREE_BASIS) THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`;
                 `subfield_generated k s2:A ring`; `R:num`; `f:num->A`;
                 `y:A`] ALGEBRA_TRACE_FREE_BASIS) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION; RING_MUL] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS
   `ring_sum (subfield_generated k {ring_0 k}) {t | t < P * R}
      (\t. ring_mul (subfield_generated k {ring_0 k})
             ((a:num->num->A) (t MOD P) (t MOD P))
             ((b:num->num->A) (t DIV P) (t DIV P)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN
    ASM_SIMP_TAC[IN_ELIM_THM; CONJUNCT2 SUBFIELD_GENERATED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subfield_generated k {ring_0 k:A}`; `P:num`; `R:num`;
                 `\i. (a:num->num->A) i i`; `\i. (b:num->num->A) i i`]
    RING_SUM_MUL_MOD_DIV) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED]);;
