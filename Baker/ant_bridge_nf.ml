(* ========================================================================= *)
(* The conjugate-vector number fields as number fields of ANT/.              *)
(*                                                                           *)
(* For nf_data n c r (Baker/nf_defs.ml: f(z) = sum_{i=0..n} c i z^i =        *)
(* prod_{k=1..n} (z - r k) monic with integer coefficients, irreducible),    *)
(* K = subfield_generated complex_ring {r 1} is a number field of degree n   *)
(* whose elements are the P(r 1)/d (integer P of degree < n, d <> 0), and    *)
(* its n embeddings into C are                                               *)
(*   nf_embedding n r k : P(r 1)/d |-> P(r k)/d        (k IN 1..n),          *)
(* well defined by the uniqueness of reduced representatives                 *)
(* (NF_ORDER_REDUCE_UNIQUE). Every ring homomorphism K -> C is one of them   *)
(* (it sends r 1 to a root of f), and they are pairwise distinct. The        *)
(* predicates nf_elem, nf_alg_int, nf_order, nf_unit are the conjugate       *)
(* vectors of K, of its ring of integers, of Z[r 1] and of the               *)
(* units of Z[r 1]. Restricted to K, the n embeddings are the complex        *)
(* embeddings of K (complex_embeddings of ANT/complex_embeddings.ml), so the *)
(* product and the sum of the conjugates are the norm and the trace of K     *)
(* over its prime subfield (algebra_norm, algebra_trace of                   *)
(* Library/ring_det.ml) by the ANT theorems                                  *)
(* NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS and                                  *)
(* NUMBER_FIELD_TRACE_COMPLEX_EMBEDDINGS (ANT/infinite_places.ml), and the   *)
(* Northcott finiteness of Z[r 1] (only finitely many elements have all      *)
(* conjugates bounded) is that of the ring of integers of K                  *)
(* (RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE).                             *)
(*                                                                           *)
(* Main results: NF_DATA_NUMBER_FIELD, NF_DATA_FIELD_CARRIER,                *)
(* NF_EMBEDDING_MONOMORPHISM, NF_EMBEDDING_1, NF_EMBEDDING_ALL,              *)
(* NF_EMBEDDING_DISTINCT, NF_ELEM_EMBEDDINGS, NF_ALG_INT_EMBEDDINGS,         *)
(* NF_ORDER_EMBEDDINGS, NF_UNIT_EMBEDDINGS, NF_DATA_COMPLEX_EMBEDDINGS,      *)
(* NF_NORM_NUMBER_FIELD_NORM, NF_TRACE_NUMBER_FIELD_TRACE,                   *)
(* NF_ORDER_NORTHCOTT.                                                       *)
(*                                                                           *)
(* Uses: Baker/ant_bridge_complex.ml (RING_OF_INTEGERS_COMPLEX_SUBFIELD and  *)
(* the BRIDGE_NF_* lemmas on subfields of C and their homomorphisms),        *)
(* ANT/numfield.ml (number_field, NUMBER_FIELD_ALT,                          *)
(* NUMBER_FIELD_FREE_BASIS_DEGREE), ANT/complex_embeddings.ml                *)
(* (complex_embeddings, COMPLEX_PRIME_SUBFIELD,                              *)
(* RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE), ANT/infinite_places.ml       *)
(* (NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS,                                    *)
(* NUMBER_FIELD_TRACE_COMPLEX_EMBEDDINGS), Library/ring_det.ml (free_basis,  *)
(* algebra_norm, algebra_trace), Multivariate/complex_ring.ml                *)
(* (complex_ring), Baker/nf_defs.ml (NF_DATA_1_IN), Baker/nf_order.ml        *)
(* (NF_ORDER_REDUCE_UNIQUE, NF_DATA_ROOTS_DISTINCT, NF_NORM_INTEGER),        *)
(* Baker/laurent_nf_defs.ml (nf_elem, nf_alg_int).                           *)
(* ========================================================================= *)

needs "Baker/ant_bridge_complex.ml";;
needs "Baker/nf_order.ml";;
needs "Baker/laurent_nf_defs.ml";;

prioritize_real();;
prioritize_num();;

let nf_embedding = new_definition
 `nf_embedding n (r:num->complex) k (x:complex) =
  @y. ?d p. integer d /\ ~(d = &0) /\ (!i. integer(p i)) /\
            Cx d * x = vsum(0..n-1) (\i. Cx(p i) * r 1 pow i) /\
            Cx d * y = vsum(0..n-1) (\i. Cx(p i) * r k pow i)`;;

(* ------------------------------------------------------------------------- *)
(* 1. Common denominators.                                                   *)
(* ------------------------------------------------------------------------- *)

let BRIDGE_NF_COMMON_DENOMINATOR = prove
 (`!(q:A->real) s.
        FINITE s /\ (!i. i IN s ==> rational(q i))
        ==> ?d. integer d /\ ~(d = &0) /\ !i. i IN s ==> integer(d * q i)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[NOT_IN_EMPTY; INTEGER_CLOSED] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
  REMOVE_THEN "ih" MP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rational]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:real`; `e:real`] THEN STRIP_TAC THEN
  EXISTS_TAC `d * e:real` THEN
  ASM_SIMP_TAC[INTEGER_CLOSED; REAL_ENTIRE] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(d * e) * m / e = d * m` SUBST1_TAC THENL
     [UNDISCH_TAC `~(e = &0)` THEN CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[INTEGER_CLOSED]];
    X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(d * e) * (q:A->real) i = e * d * q i` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_SIMP_TAC[INTEGER_CLOSED]]]);;

(* ------------------------------------------------------------------------- *)
(* 2. The field K = Q(r 1) and the order Z[r 1].                             *)
(* ------------------------------------------------------------------------- *)

let BRIDGE_NF_ORDER_CMUL = prove
 (`!n r a x. integer x /\ nf_order n r a ==> nf_order n r (\k. Cx x * a k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `r:num->complex`; `(\k. Cx x):num->complex`;
                 `a:num->complex`] NF_ORDER_MUL) THEN
  ASM_SIMP_TAC[NF_ORDER_CX]);;

let NF_DATA_FIELD_CARRIER_ORDER = prove
 (`!n c r.
        nf_data n c r
        ==> ring_carrier(subfield_generated complex_ring {r 1}) =
            {x | ?d a. integer d /\ ~(d = &0) /\ nf_order n r a /\
                       Cx d * x = a 1}`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SING_SUBSET; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`&1`; `r:num->complex`] THEN
      REWRITE_TAC[INTEGER_CLOSED; NF_ORDER_ROOT; COMPLEX_MUL_LID] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    MATCH_MP_TAC SUBFIELD_OF_FIELD_INV THEN REWRITE_TAC[FIELD_COMPLEX_RING] THEN
    REWRITE_TAC[subring_of; complex_field_clauses; SUBSET_UNIV;
                IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`&1`; `\k:num. Cx(&0)`] THEN
      SIMP_TAC[INTEGER_CLOSED; NF_ORDER_CX; COMPLEX_MUL_RZERO] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      MAP_EVERY EXISTS_TAC [`&1`; `\k:num. Cx(&1)`] THEN
      SIMP_TAC[INTEGER_CLOSED; NF_ORDER_CX; COMPLEX_MUL_RID] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      X_GEN_TAC `x:complex` THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `a:num->complex`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`d:real`; `\k. --((a:num->complex) k)`] THEN
      ASM_SIMP_TAC[NF_ORDER_NEG] THEN
      UNDISCH_TAC `Cx d * x = a 1` THEN CONV_TAC COMPLEX_RING;
      MAP_EVERY X_GEN_TAC [`x:complex`; `y:complex`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `a:num->complex`
          STRIP_ASSUME_TAC))
       (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `b:num->complex`
          STRIP_ASSUME_TAC))) THEN
      MAP_EVERY EXISTS_TAC
       [`d * e:real`; `\k. Cx e * (a:num->complex) k + Cx d * b k`] THEN
      ASM_SIMP_TAC[INTEGER_CLOSED; REAL_ENTIRE; NF_ORDER_ADD;
                   BRIDGE_NF_ORDER_CMUL] THEN
      UNDISCH_TAC `Cx d * x = a 1` THEN UNDISCH_TAC `Cx e * y = b 1` THEN
      REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING;
      MAP_EVERY X_GEN_TAC [`x:complex`; `y:complex`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `a:num->complex`
          STRIP_ASSUME_TAC))
       (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `b:num->complex`
          STRIP_ASSUME_TAC))) THEN
      MAP_EVERY EXISTS_TAC
       [`d * e:real`; `\k. (a:num->complex) k * b k`] THEN
      ASM_SIMP_TAC[INTEGER_CLOSED; REAL_ENTIRE; NF_ORDER_MUL] THEN
      UNDISCH_TAC `Cx d * x = a 1` THEN UNDISCH_TAC `Cx e * y = b 1` THEN
      REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING;
      X_GEN_TAC `x:complex` THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `a:num->complex`
        STRIP_ASSUME_TAC)) THEN
      ASM_CASES_TAC `x = Cx(&0)` THENL
       [MAP_EVERY EXISTS_TAC [`&1`; `\k:num. Cx(&0)`] THEN
        ASM_SIMP_TAC[INTEGER_CLOSED; NF_ORDER_CX; COMPLEX_INV_0;
                     COMPLEX_MUL_RZERO] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN `~((a:num->complex) 1 = Cx(&0))` ASSUME_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
        ASM_REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(cproduct(1..n) (a:num->complex) = Cx(&0))`
      ASSUME_TAC THENL
       [MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                      `a:num->complex`] NF_NORM_EQ_0) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        DISCH_THEN(MP_TAC o SPEC `1`) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                    `a:num->complex`] NF_ADJUGATE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `b:num->complex` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                    `a:num->complex`] NF_NORM_INTEGER) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`m:real`; `\k. Cx d * (b:num->complex) k`] THEN
      ASM_SIMP_TAC[BRIDGE_NF_ORDER_CMUL] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `~(cproduct(1..n) (a:num->complex) = Cx(&0))` THEN
        ASM_REWRITE_TAC[CX_INJ];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `Cx d * x = a 1` THEN UNDISCH_TAC `~(x = Cx(&0))` THEN
      CONV_TAC COMPLEX_FIELD];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:complex` THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `a:num->complex`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [nf_order]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `p:num->real`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `x = inv(Cx d) * vsum(0..m) (\i. Cx(p i) * r 1 pow i)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `Cx d * x = a 1` THEN UNDISCH_TAC `~(d = &0)` THEN
      REWRITE_TAC[GSYM CX_INJ] THEN CONV_TAC COMPLEX_FIELD;
      MATCH_MP_TAC BRIDGE_NF_SUBFIELD_POLY THEN
      ASM_REWRITE_TAC[BRIDGE_NF_GEN_IN]]]);;

let NF_DATA_FIELD_CARRIER = prove
 (`!n c r.
        nf_data n c r
        ==> ring_carrier(subfield_generated complex_ring {r 1}) =
            {x | ?d p. integer d /\ ~(d = &0) /\ (!i. integer(p i)) /\
                       Cx d * x = vsum(0..n-1) (\i. Cx(p i) * r 1 pow i)}`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP NF_DATA_FIELD_CARRIER_ORDER th]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:complex` THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `d:real` MP_TAC) THENL
   [DISCH_THEN(X_CHOOSE_THEN `a:num->complex` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                  `a:num->complex`] NF_ORDER_REDUCE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num->real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `p:num->real`] THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `p:num->real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`d:real`;
      `\k. vsum(0..n-1) (\i. Cx(p i) * (r:num->complex) k pow i)`] THEN
    ASM_REWRITE_TAC[nf_order] THEN
    MAP_EVERY EXISTS_TAC [`n - 1`; `p:num->real`] THEN ASM_REWRITE_TAC[]]);;

let NF_DATA_ORDER_CARRIER = prove
 (`!n c r.
        nf_data n c r
        ==> ring_carrier(subring_generated complex_ring {r 1}) =
            {x | ?a. nf_order n r a /\ x = a 1}`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
    REWRITE_TAC[SING_SUBSET; IN_ELIM_THM; subring_of; COMPLEX_RING_CLAUSES;
                SUBSET_UNIV] THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `r:num->complex` THEN REWRITE_TAC[NF_ORDER_ROOT];
      EXISTS_TAC `\k:num. Cx(&0)` THEN SIMP_TAC[NF_ORDER_CX; INTEGER_CLOSED];
      EXISTS_TAC `\k:num. Cx(&1)` THEN SIMP_TAC[NF_ORDER_CX; INTEGER_CLOSED];
      X_GEN_TAC `x:complex` THEN
      DISCH_THEN(X_CHOOSE_THEN `a:num->complex` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `\k. --((a:num->complex) k)` THEN ASM_SIMP_TAC[NF_ORDER_NEG];
      MAP_EVERY X_GEN_TAC [`x:complex`; `y:complex`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `a:num->complex` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `b:num->complex` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `\k. (a:num->complex) k + b k` THEN
      ASM_SIMP_TAC[NF_ORDER_ADD];
      MAP_EVERY X_GEN_TAC [`x:complex`; `y:complex`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `a:num->complex` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `b:num->complex` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `\k. (a:num->complex) k * b k` THEN
      ASM_SIMP_TAC[NF_ORDER_MUL]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:complex` THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num->complex` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [nf_order]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `p:num->real`
      STRIP_ASSUME_TAC)) THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC BRIDGE_NF_SUBRING_POLY THEN
    ASM_REWRITE_TAC[SUBRING_SUBRING_GENERATED] THEN
    MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
    REWRITE_TAC[in_complex_ring; IN_SING]]);;

(* ------------------------------------------------------------------------- *)
(* 3. The embeddings P(r 1)/d |-> P(r k)/d.                                  *)
(* ------------------------------------------------------------------------- *)

let NF_EMBEDDING_POLY = prove
 (`!n c r k d p x.
        nf_data n c r /\ integer d /\ ~(d = &0) /\ (!i. integer(p i)) /\
        Cx d * x = vsum(0..n-1) (\i. Cx(p i) * r 1 pow i)
        ==> Cx d * nf_embedding n r k x =
            vsum(0..n-1) (\i. Cx(p i) * r k pow i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  SUBGOAL_THEN
   `?d p. integer d /\ ~(d = &0) /\ (!i. integer(p i)) /\
          Cx d * x = vsum(0..n-1) (\i. Cx(p i) * r 1 pow i) /\
          Cx d * nf_embedding n r k x =
          vsum(0..n-1) (\i. Cx(p i) * (r:num->complex) k pow i)`
  MP_TAC THENL
   [REWRITE_TAC[nf_embedding] THEN CONV_TAC SELECT_CONV THEN
    EXISTS_TAC
     `vsum(0..n-1) (\i. Cx(p i) * (r:num->complex) k pow i) / Cx d` THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `p:num->real`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPLEX_DIV_LMUL THEN ASM_REWRITE_TAC[CX_INJ];
    ALL_TAC] THEN
  SPEC_TAC(`nf_embedding n r k x`,`y:complex`) THEN GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `q:num->real`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                `\i. e * (p:num->real) i`; `\i. d * (q:num->real) i`; `1`]
    NF_ORDER_REDUCE_UNIQUE) THEN
  ASM_SIMP_TAC[INTEGER_CLOSED; CX_MUL; GSYM COMPLEX_MUL_ASSOC;
               VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `Cx d * x = vsum(0..n-1) (\i. Cx(p i) * r 1 pow i)` THEN
    UNDISCH_TAC `Cx e * x = vsum(0..n-1) (\i. Cx(q i) * r 1 pow i)` THEN
    CONV_TAC COMPLEX_RING;
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `vsum(0..n-1) (\i. Cx(e * p i) * (r:num->complex) k pow i) =
    vsum(0..n-1) (\i. Cx(d * q i) * r k pow i)`
  MP_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[CX_MUL; GSYM COMPLEX_MUL_ASSOC; VSUM_COMPLEX_LMUL;
                 FINITE_NUMSEG]] THEN
  MP_TAC(ASSUME `~(e = &0)`) THEN REWRITE_TAC[GSYM CX_INJ] THEN
  UNDISCH_TAC
   `Cx e * y = vsum(0..n-1) (\i. Cx(q i) * (r:num->complex) k pow i)` THEN
  CONV_TAC COMPLEX_FIELD);;

let NF_EMBEDDING_ORDER = prove
 (`!n c r k d a x.
        nf_data n c r /\ k IN 1..n /\ integer d /\ ~(d = &0) /\
        nf_order n r a /\ Cx d * x = a 1
        ==> Cx d * nf_embedding n r k x = a k`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `a:num->complex`]
    NF_ORDER_REDUCE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num->real` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC NF_EMBEDDING_POLY THEN
  EXISTS_TAC `c:num->real` THEN ASM_SIMP_TAC[]);;

let NF_EMBEDDING_ORDER_1 = prove
 (`!n c r k a.
        nf_data n c r /\ k IN 1..n /\ nf_order n r a
        ==> nf_embedding n r k (a 1) = a k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`; `&1`;
                `a:num->complex`; `(a:num->complex) 1`]
    NF_EMBEDDING_ORDER) THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED; COMPLEX_MUL_LID] THEN
  DISCH_THEN MATCH_MP_TAC THEN REAL_ARITH_TAC);;

let NF_EMBEDDING_HOMOMORPHISM = prove
 (`!n c r k.
        nf_data n c r /\ k IN 1..n
        ==> ring_homomorphism (subfield_generated complex_ring {r 1},
                               complex_ring) (nf_embedding n r k)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  REWRITE_TAC[ring_homomorphism; CONJUNCT2 SUBFIELD_GENERATED] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP NF_DATA_FIELD_CARRIER_ORDER th]) THEN
  REWRITE_TAC[COMPLEX_RING_CLAUSES; SUBSET_UNIV; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`;
                  `\k:num. Cx(&0)`] NF_EMBEDDING_ORDER_1) THEN
    ASM_SIMP_TAC[NF_ORDER_CX; INTEGER_CLOSED];
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`;
                  `\k:num. Cx(&1)`] NF_EMBEDDING_ORDER_1) THEN
    ASM_SIMP_TAC[NF_ORDER_CX; INTEGER_CLOSED];
    X_GEN_TAC `x:complex` THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `a:num->complex`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`;
                  `d:real`; `a:num->complex`; `x:complex`]
      NF_EMBEDDING_ORDER) THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`;
                  `d:real`; `\k. --((a:num->complex) k)`; `--x:complex`]
      NF_EMBEDDING_ORDER) THEN
    ASM_SIMP_TAC[NF_ORDER_NEG; COMPLEX_MUL_RNEG] THEN
    UNDISCH_TAC `~(d = &0)` THEN REWRITE_TAC[GSYM CX_INJ] THEN
    CONV_TAC COMPLEX_FIELD;
    MAP_EVERY X_GEN_TAC [`x:complex`; `y:complex`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `a:num->complex`
        STRIP_ASSUME_TAC))
     (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `b:num->complex`
        STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `Cx(d * e) * (x + y) = Cx e * a 1 + Cx d * b 1`
    ASSUME_TAC THENL
     [UNDISCH_TAC `Cx d * x = a 1` THEN UNDISCH_TAC `Cx e * y = b 1` THEN
      REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`;
                  `d:real`; `a:num->complex`; `x:complex`]
      NF_EMBEDDING_ORDER) THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`;
                  `e:real`; `b:num->complex`; `y:complex`]
      NF_EMBEDDING_ORDER) THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`;
                  `d * e:real`; `\k. Cx e * (a:num->complex) k + Cx d * b k`;
                  `x + y:complex`] NF_EMBEDDING_ORDER) THEN
    ASM_SIMP_TAC[NF_ORDER_ADD; BRIDGE_NF_ORDER_CMUL; INTEGER_CLOSED;
                 REAL_ENTIRE] THEN
    UNDISCH_TAC `~(d = &0)` THEN UNDISCH_TAC `~(e = &0)` THEN
    REWRITE_TAC[GSYM CX_INJ; CX_MUL] THEN CONV_TAC COMPLEX_FIELD;
    MAP_EVERY X_GEN_TAC [`x:complex`; `y:complex`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `a:num->complex`
        STRIP_ASSUME_TAC))
     (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `b:num->complex`
        STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `Cx(d * e) * (x * y) = a 1 * b 1` ASSUME_TAC THENL
     [UNDISCH_TAC `Cx d * x = a 1` THEN UNDISCH_TAC `Cx e * y = b 1` THEN
      REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`;
                  `d:real`; `a:num->complex`; `x:complex`]
      NF_EMBEDDING_ORDER) THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`;
                  `e:real`; `b:num->complex`; `y:complex`]
      NF_EMBEDDING_ORDER) THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`;
                  `d * e:real`; `\k. (a:num->complex) k * b k`;
                  `x * y:complex`] NF_EMBEDDING_ORDER) THEN
    ASM_SIMP_TAC[NF_ORDER_MUL; INTEGER_CLOSED; REAL_ENTIRE] THEN
    UNDISCH_TAC `~(d = &0)` THEN UNDISCH_TAC `~(e = &0)` THEN
    REWRITE_TAC[GSYM CX_INJ; CX_MUL] THEN CONV_TAC COMPLEX_FIELD]);;

let NF_EMBEDDING_MONOMORPHISM = prove
 (`!n c r k.
        nf_data n c r /\ k IN 1..n
        ==> ring_monomorphism (subfield_generated complex_ring {r 1},
                               complex_ring) (nf_embedding n r k) /\
            nf_embedding n r k (r 1) = r k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`]
    NF_EMBEDDING_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`subfield_generated complex_ring {(r:num->complex) 1}`;
                   `complex_ring`; `nf_embedding n r k`]
      FIELD_HOMOMORPHISM_IMP_MONOMORPHISM) THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; FIELD_COMPLEX_RING] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN
    DISCH_THEN(MP_TAC o SPEC `Cx(&1)`) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BRIDGE_NF_HOM_CLAUSES) THEN
    ASM_SIMP_TAC[BRIDGE_NF_SUBFIELD_RATIONAL; RATIONAL_CLOSED;
                 COMPLEX_RING_CLAUSES; CX_INJ] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC NF_EMBEDDING_ORDER_1 THEN EXISTS_TAC `c:num->real` THEN
    ASM_REWRITE_TAC[NF_ORDER_ROOT]]);;

let NF_EMBEDDING_1 = prove
 (`!n c r x.
        nf_data n c r /\
        x IN ring_carrier(subfield_generated complex_ring {r 1})
        ==> nf_embedding n r 1 x = x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP NF_DATA_FIELD_CARRIER_ORDER th]) THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:real`; `a:num->complex`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `1`;
                `d:real`; `a:num->complex`; `x:complex`]
    NF_EMBEDDING_ORDER) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `Cx d * x = a 1` THEN UNDISCH_TAC `~(d = &0)` THEN
  REWRITE_TAC[GSYM CX_INJ] THEN CONV_TAC COMPLEX_FIELD);;

let NF_EMBEDDING_ALL = prove
 (`!n c r f.
        nf_data n c r /\
        ring_homomorphism(subfield_generated complex_ring {r 1},complex_ring) f
        ==> ?k. k IN 1..n /\
                !x. x IN ring_carrier(subfield_generated complex_ring {r 1})
                    ==> f x = nf_embedding n r k x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BRIDGE_NF_HOM_CLAUSES) THEN
  SUBGOAL_THEN `?k. k IN 1..n /\ f((r:num->complex) 1) = r k`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `1`]
      NF_DATA_ROOT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `f:complex->complex`) THEN
    MP_TAC(ISPECL [`{(r:num->complex) 1}`; `f:complex->complex`;
                   `(r:num->complex) 1`; `c:num->real`; `n:num`]
      BRIDGE_NF_HOM_POLY) THEN
    ASM_SIMP_TAC[BRIDGE_NF_GEN_IN; RATIONAL_INTEGER; RATIONAL_CLOSED] THEN
    DISCH_THEN(K ALL_TAC) THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`]
      NF_DATA_FACTOR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG; COMPLEX_SUB_0];
    ALL_TAC] THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
  MP_TAC(ASSUME
   `x IN ring_carrier
          (subfield_generated complex_ring {(r:num->complex) 1})`) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NF_DATA_FIELD_CARRIER th]) THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:real`; `p:num->real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`;
                `d:real`; `p:num->real`; `x:complex`] NF_EMBEDDING_POLY) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(AP_TERM `f:complex->complex` (ASSUME
   `Cx d * x = vsum(0..n-1) (\i. Cx(p i) * (r:num->complex) 1 pow i)`)) THEN
  MP_TAC(ISPECL [`{(r:num->complex) 1}`; `f:complex->complex`;
                 `(r:num->complex) 1`; `p:num->real`; `n - 1`]
    BRIDGE_NF_HOM_POLY) THEN
  ASM_SIMP_TAC[BRIDGE_NF_GEN_IN; RATIONAL_INTEGER; RATIONAL_CLOSED;
               BRIDGE_NF_SUBFIELD_RATIONAL] THEN
  DISCH_THEN(K ALL_TAC) THEN
  UNDISCH_TAC `~(d = &0)` THEN REWRITE_TAC[GSYM CX_INJ] THEN
  CONV_TAC COMPLEX_FIELD);;

let NF_EMBEDDING_DISTINCT = prove
 (`!n c r k l.
        nf_data n c r /\ k IN 1..n /\ l IN 1..n /\
        (!x. x IN ring_carrier(subfield_generated complex_ring {r 1})
             ==> nf_embedding n r k x = nf_embedding n r l x)
        ==> k = l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`; `l:num`]
    NF_DATA_ROOTS_DISTINCT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN
   `nf_embedding n r k ((r:num->complex) 1) = nf_embedding n r l (r 1)`
  MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[BRIDGE_NF_GEN_IN];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`]
    NF_EMBEDDING_MONOMORPHISM) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `l:num`]
    NF_EMBEDDING_MONOMORPHISM) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 4. K is a number field of degree n, with the power basis.                 *)
(* ------------------------------------------------------------------------- *)

let NF_DATA_FREE_BASIS = prove
 (`!n c r.
        nf_data n c r
        ==> free_basis (subfield_generated complex_ring {Cx(&0)},
                        subfield_generated complex_ring {r 1})
                       I n (\i. r 1 pow i)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  SUBGOAL_THEN
   `!w. (!i. i < n ==> ?q. rational q /\ w i = Cx q)
        ==> ring_sum (subfield_generated complex_ring {(r:num->complex) 1})
                     {i | i < n} (\i. w i * r 1 pow i) =
            vsum(0..n-1) (\i. w i * r 1 pow i)`
  (LABEL_TAC "rs") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `{i:num | i < n} = 0..n-1` SUBST1_TAC THENL
     [REWRITE_TAC[NUMSEG_LT] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC BRIDGE_NF_RING_SUM_SUBFIELD THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `q:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[BRIDGE_NF_SUBFIELD_CLOSED; BRIDGE_NF_SUBFIELD_RATIONAL;
                 BRIDGE_NF_GEN_IN];
    ALL_TAC] THEN
  REWRITE_TAC[free_basis; COMPLEX_PRIME_SUBFIELD; IN_ELIM_THM; I_THM;
              CONJUNCT2 SUBFIELD_GENERATED; COMPLEX_RING_CLAUSES] THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[BRIDGE_NF_SUBFIELD_CLOSED; BRIDGE_NF_GEN_IN];
    X_GEN_TAC `x:complex` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NF_DATA_FIELD_CARRIER th]) THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`d:real`; `p:num->real`] THEN STRIP_TAC THEN
    EXISTS_TAC `\i:num. Cx(p i / d)` THEN
    SUBGOAL_THEN
     `!i. i < n ==> ?q. rational q /\ (\i:num. Cx(p i / d)) i = Cx q`
    ASSUME_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      EXISTS_TAC `(p:num->real) i / d` THEN ASM_SIMP_TAC[RATIONAL_CLOSED];
      ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "rs" (fun th -> FIRST_ASSUM(SUBST1_TAC o MATCH_MP th)) THEN
    SUBGOAL_THEN
     `vsum(0..n-1) (\i. (\i:num. Cx(p i / d)) i * (r:num->complex) 1 pow i) =
      inv(Cx d) * vsum(0..n-1) (\i. Cx(p i) * r 1 pow i)`
    SUBST1_TAC THENL
     [SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
      MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[CX_DIV; complex_div] THEN CONV_TAC COMPLEX_RING;
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `~(d = &0)` THEN REWRITE_TAC[GSYM CX_INJ] THEN
      CONV_TAC COMPLEX_FIELD];
    X_GEN_TAC `w:num->complex` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    USE_THEN "rs" (fun th -> FIRST_ASSUM(SUBST1_TAC o MATCH_MP th)) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `?q. !i. i < n ==> rational(q i) /\ w i = Cx(q i)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`q:num->real`; `{i:num | i < n}`]
      BRIDGE_NF_COMMON_DENOMINATOR) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `1`;
                  `\i. if i < n then e * (q:num->real) i else &0`]
      NF_DATA_DEGREE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED];
        ALL_TAC] THEN
      TRANS_TAC EQ_TRANS
       `Cx e * vsum(0..n-1) (\i. w i * (r:num->complex) 1 pow i)` THEN
      CONJ_TAC THENL
       [SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
        MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN
        STRIP_TAC THEN SUBGOAL_THEN `i < n` ASSUME_TAC THENL
         [ASM_ARITH_TAC; ASM_SIMP_TAC[CX_MUL]] THEN
        CONV_TAC COMPLEX_RING;
        ASM_REWRITE_TAC[COMPLEX_MUL_RZERO]];
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
      ASM_SIMP_TAC[REAL_ENTIRE]]]);;

let NF_DATA_NUMBER_FIELD = prove
 (`!n c r.
        nf_data n c r
        ==> number_field (subfield_generated complex_ring {r 1}) /\
            extension_degree (subfield_generated complex_ring {Cx(&0)},
                              subfield_generated complex_ring {r 1}) I = n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_FREE_BASIS) THEN
  SUBGOAL_THEN `number_field (subfield_generated complex_ring
                                {(r:num->complex) 1})`
  ASSUME_TAC THENL
   [REWRITE_TAC[NUMBER_FIELD_ALT; BRIDGE_NF_PRIME_SUBFIELD] THEN
    SIMP_TAC[FIELD_SUBFIELD_GENERATED; FIELD_COMPLEX_RING;
             RING_CHAR_SUBFIELD_GENERATED; RING_CHAR_COMPLEX_RING] THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `\i. (r:num->complex) 1 pow i`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`subfield_generated complex_ring {(r:num->complex) 1}`;
                   `n:num`; `\i. (r:num->complex) 1 pow i`]
      NUMBER_FIELD_FREE_BASIS_DEGREE) THEN
    ASM_REWRITE_TAC[BRIDGE_NF_PRIME_SUBFIELD]]);;

(* ------------------------------------------------------------------------- *)
(* 5. The conjugate-vector predicates as conjugate vectors of K.             *)
(* ------------------------------------------------------------------------- *)

let NF_ELEM_EMBEDDINGS = prove
 (`!n c r a.
        nf_data n c r
        ==> (nf_elem n r a <=>
             ?x. x IN ring_carrier(subfield_generated complex_ring {r 1}) /\
                 !k. k IN 1..n ==> a k = nf_embedding n r k x)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NF_DATA_FIELD_CARRIER th]) THEN
  REWRITE_TAC[nf_elem; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `p:num->real`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `Cx d * (a:num->complex) 1 = vsum(0..n-1) (\i. Cx(p i) * r 1 pow i)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `(a:num->complex) 1` THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`d:real`; `p:num->real`] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`;
                    `d:real`; `p:num->real`; `(a:num->complex) 1`]
        NF_EMBEDDING_POLY) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `Cx d * (a:num->complex) k = vsum(0..n-1) (\i. Cx(p i) * r k pow i)`
      MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(d = &0)` THEN REWRITE_TAC[GSYM CX_INJ] THEN
      CONV_TAC COMPLEX_FIELD];
    DISCH_THEN(X_CHOOSE_THEN `x:complex` (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `p:num->real` STRIP_ASSUME_TAC))
     ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `p:num->real`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC NF_EMBEDDING_POLY THEN EXISTS_TAC `c:num->real` THEN
    ASM_REWRITE_TAC[]]);;

let NF_ALG_INT_EMBEDDINGS = prove
 (`!n c r a.
        nf_data n c r
        ==> (nf_alg_int n r a <=>
             ?x. x IN ring_carrier
                        (ring_of_integers
                           (subfield_generated complex_ring {r 1})) /\
                 !k. k IN 1..n ==> a k = nf_embedding n r k x)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  MP_TAC(ISPEC
   `ring_carrier(subfield_generated complex_ring {(r:num->complex) 1})`
   RING_OF_INTEGERS_COMPLEX_SUBFIELD) THEN
  REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED; FIELD_COMPLEX_RING] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[nf_alg_int; IN_ELIM_THM;
                                    MATCH_MP NF_ELEM_EMBEDDINGS th]) THEN
  SUBGOAL_THEN
   `!x. x IN ring_carrier
               (subfield_generated complex_ring {(r:num->complex) 1}) /\
        (!k. k IN 1..n ==> (a:num->complex) k = nf_embedding n r k x)
        ==> a 1 = x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC NF_EMBEDDING_1 THEN EXISTS_TAC `c:num->real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `x:complex` STRIP_ASSUME_TAC) MP_TAC) THEN
    SUBGOAL_THEN `(a:num->complex) 1 = x` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN EXISTS_TAC `x:complex` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `x:complex` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(a:num->complex) 1 = x` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:complex` THEN ASM_REWRITE_TAC[]]);;

let NF_ORDER_EMBEDDINGS = prove
 (`!n c r a.
        nf_data n c r
        ==> (nf_order n r a <=>
             ?x. x IN ring_carrier(subring_generated complex_ring {r 1}) /\
                 !k. k IN 1..n ==> a k = nf_embedding n r k x)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NF_DATA_ORDER_CARRIER th]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `(a:num->complex) 1` THEN CONJ_TAC THENL
     [EXISTS_TAC `a:num->complex` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC NF_EMBEDDING_ORDER_1 THEN EXISTS_TAC `c:num->real` THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `x:complex` (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `b:num->complex` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    MATCH_MP_TAC NF_ORDER_EQ THEN EXISTS_TAC `b:num->complex` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC NF_EMBEDDING_ORDER_1 THEN
    EXISTS_TAC `c:num->real` THEN ASM_REWRITE_TAC[]]);;

let NF_UNIT_EMBEDDINGS = prove
 (`!n c r a.
        nf_data n c r
        ==> (nf_unit n r a <=>
             ?x. ring_unit (subring_generated complex_ring {r 1}) x /\
                 !k. k IN 1..n ==> a k = nf_embedding n r k x)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  REWRITE_TAC[nf_unit; ring_unit; CONJUNCT2 SUBRING_GENERATED;
              COMPLEX_RING_CLAUSES] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NF_DATA_ORDER_CARRIER th]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `b:num->complex` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `(a:num->complex) 1` THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `a:num->complex` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(b:num->complex) 1` THEN CONJ_TAC THENL
       [EXISTS_TAC `b:num->complex` THEN ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC NF_EMBEDDING_ORDER_1 THEN EXISTS_TAC `c:num->real` THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `x:complex` (CONJUNCTS_THEN2 (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `a':num->complex` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `y:complex` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `b:num->complex` STRIP_ASSUME_TAC) ASSUME_TAC)))
     MP_TAC)) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `!k. k IN 1..n ==> (a:num->complex) k = a' k` MP_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC NF_EMBEDDING_ORDER_1 THEN EXISTS_TAC `c:num->real` THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN
      DISCH_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NF_ORDER_EQ THEN EXISTS_TAC `a':num->complex` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `b:num->complex` THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                  `\k. (a':num->complex) k * b k - Cx(&1)`; `1`; `k:num`]
      NF_ORDER_ZERO) THEN
    ASM_SIMP_TAC[NF_ORDER_SUB; NF_ORDER_MUL; NF_ORDER_CX; INTEGER_CLOSED;
                 COMPLEX_SUB_0]]);;

(* ------------------------------------------------------------------------- *)
(* 6. The complex embeddings of K are the n embeddings, so the norm and the  *)
(*    trace are the product and the sum of the conjugates (the ANT theorems  *)
(*    NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS and                               *)
(*    NUMBER_FIELD_TRACE_COMPLEX_EMBEDDINGS of ANT/infinite_places.ml).      *)
(* ------------------------------------------------------------------------- *)

let NF_DATA_COMPLEX_EMBEDDINGS = prove
 (`!n c r.
        nf_data n c r
        ==> complex_embeddings(subfield_generated complex_ring {r 1}) =
            IMAGE (\k. RESTRICTION
                         (ring_carrier(subfield_generated complex_ring {r 1}))
                         (nf_embedding n r k))
                  (1..n) /\
            (!k l. k IN 1..n /\ l IN 1..n /\
                   RESTRICTION
                     (ring_carrier(subfield_generated complex_ring {r 1}))
                     (nf_embedding n r k) =
                   RESTRICTION
                     (ring_carrier(subfield_generated complex_ring {r 1}))
                     (nf_embedding n r l)
                   ==> k = l)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[RESTRICTION_EXTENSION] THEN CONJ_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NF_EMBEDDING_DISTINCT THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`; `r:num->complex`] THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; complex_embeddings; IN_ELIM_THM] THEN
  X_GEN_TAC `f:complex->complex` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                  `f:complex->complex`] NF_EMBEDDING_ALL) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EXTENSIONAL_EQ THEN
    EXISTS_TAC `ring_carrier(subfield_generated complex_ring
                               {(r:num->complex) 1})` THEN
    ASM_SIMP_TAC[RESTRICTION_IN_EXTENSIONAL; RESTRICTION];
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[RESTRICTION_IN_EXTENSIONAL] THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_EQ THEN
    EXISTS_TAC `nf_embedding n r k` THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`]
      NF_EMBEDDING_HOMOMORPHISM) THEN
    ASM_SIMP_TAC[RESTRICTION]]);;

let NF_NORM_NUMBER_FIELD_NORM,
    NF_TRACE_NUMBER_FIELD_TRACE = (CONJ_PAIR o prove)
 (`(!n c r x.
        nf_data n c r /\
        x IN ring_carrier(subfield_generated complex_ring {r 1})
        ==> algebra_norm
              (subfield_generated (subfield_generated complex_ring {r 1})
                 {ring_0 (subfield_generated complex_ring {r 1})},
               subfield_generated complex_ring {r 1}) I x =
            cproduct(1..n) (\k. nf_embedding n r k x)) /\
   (!n c r x.
        nf_data n c r /\
        x IN ring_carrier(subfield_generated complex_ring {r 1})
        ==> algebra_trace
              (subfield_generated (subfield_generated complex_ring {r 1})
                 {ring_0 (subfield_generated complex_ring {r 1})},
               subfield_generated complex_ring {r 1}) I x =
            vsum(1..n) (\k. nf_embedding n r k x))`,
  REWRITE_TAC[AND_FORALL_THM;
              TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `cproduct(1..n) (\k. nf_embedding n r k x) =
    cproduct (complex_embeddings
                (subfield_generated complex_ring {(r:num->complex) 1}))
             (\h. h x) /\
    vsum(1..n) (\k. nf_embedding n r k x) =
    vsum (complex_embeddings
            (subfield_generated complex_ring {(r:num->complex) 1}))
         (\h. h x)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP NF_DATA_COMPLEX_EMBEDDINGS) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) CPRODUCT_IMAGE o rand o snd);
      W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE o rand o snd)] THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[o_DEF; RESTRICTION];
    ALL_TAC] THEN
  ABBREV_TAC
   `g = RESTRICTION (ring_carrier(subfield_generated complex_ring
                                    {(r:num->complex) 1})) I` THEN
  SUBGOAL_THEN
   `g IN complex_embeddings(subfield_generated complex_ring
                              {(r:num->complex) 1}) /\
    !y. y IN ring_carrier(subfield_generated
                           (subfield_generated complex_ring {r 1})
                           {ring_0 (subfield_generated complex_ring {r 1})})
        ==> g y = y`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN
    REWRITE_TAC[complex_embeddings; IN_ELIM_THM;
                RESTRICTION_IN_EXTENSIONAL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_EQ THEN
      EXISTS_TAC `I:complex->complex` THEN
      SIMP_TAC[RESTRICTION; RING_HOMOMORPHISM_SUBFIELD_INCLUSION];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RESTRICTION_EQ THEN
      REWRITE_TAC[I_THM] THEN
      ASM_MESON_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET]];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP NF_DATA_NUMBER_FIELD) THEN
  MP_TAC(ISPECL [`subfield_generated complex_ring {(r:num->complex) 1}`;
                 `g:complex->complex`; `x:complex`]
    NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS) THEN
  MP_TAC(ISPECL [`subfield_generated complex_ring {(r:num->complex) 1}`;
                 `g:complex->complex`; `x:complex`]
    NUMBER_FIELD_TRACE_COMPLEX_EMBEDDINGS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER]);;

(* ------------------------------------------------------------------------- *)
(* 7. Northcott: finitely many elements of Z[r 1] have all conjugates        *)
(*    bounded (RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE for the ring of    *)
(*    integers of K, which contains Z[r 1]).                                 *)
(* ------------------------------------------------------------------------- *)

let NF_ORDER_NORTHCOTT = prove
 (`!n c r R. nf_data n c r
             ==> ?A. FINITE A /\ (!b. b IN A ==> nf_order n r b) /\
                     !a. nf_order n r a /\ (!k. k IN 1..n ==> norm(a k) <= R)
                         ==> ?b. b IN A /\ !k. k IN 1..n ==> a k = b k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP NF_DATA_NUMBER_FIELD) THEN
  EXISTS_TAC
   `IMAGE (\x k. nf_embedding n r k x)
     ({x | x IN ring_carrier(ring_of_integers
                  (subfield_generated complex_ring {(r:num->complex) 1})) /\
           !g. g IN complex_embeddings(subfield_generated complex_ring {r 1})
               ==> norm(g x) <= R} INTER
      ring_carrier(subring_generated complex_ring {r 1}))` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_INTER;
               RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NF_ORDER_EMBEDDINGS th]) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `a:num->complex` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:complex` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  EXISTS_TAC `\k. nf_embedding n r k (x:complex)` THEN
  ASM_SIMP_TAC[IN_IMAGE] THEN EXISTS_TAC `x:complex` THEN
  MP_TAC(ISPEC
   `ring_carrier(subfield_generated complex_ring {(r:num->complex) 1})`
   RING_OF_INTEGERS_COMPLEX_SUBFIELD) THEN
  SIMP_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED;
           SUBFIELD_SUBFIELD_GENERATED; FIELD_COMPLEX_RING] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `x IN ring_carrier(subfield_generated complex_ring {(r:num->complex) 1})`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBRING_SUBSET_SUBFIELD_GENERATED; SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `x = (a:num->complex) 1` SUBST1_TAC THENL
     [ASM_MESON_TAC[NF_EMBEDDING_1]; ALL_TAC] THEN
    MATCH_MP_TAC NF_ORDER_ALGEBRAIC_INTEGER THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`; `r:num->complex`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NF_ORDER_EMBEDDINGS th]) THEN
    ASM_MESON_TAC[];
    FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP
      NF_DATA_COMPLEX_EMBEDDINGS th)]) THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE; RESTRICTION] THEN ASM_MESON_TAC[]]);;
