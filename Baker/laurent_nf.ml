(* ========================================================================= *)
(* Two logarithms, the Laurent bound for algebraic numbers: number field     *)
(* infrastructure for heights.                                               *)
(*                                                                           *)
(* Purpose: elements of the number field K = Q(r 1) of nf_data n c r given   *)
(* by their conjugate vectors with a common denominator (nf_elem), algebraic *)
(* integers of K (nf_alg_int), and the pair height nf_proj_height of a       *)
(* pair be, ga of conjugate vectors. An element of K vanishing at one        *)
(* conjugate vanishes at all; all conjugates of an algebraic integer of K    *)
(* are algebraic integers and its norm is a rational integer (through the    *)
(* bridge Baker/ant_bridge_nf.ml: the images of an element of the ring of    *)
(* integers of K under ring homomorphisms, and its norm over Q); Liouville   *)
(* inequality for algebraic integers of K; the pair height for a             *)
(* quotient x = be 1 / ga 1 >= 1 dominates log x / n; behaviour of the       *)
(* pair height under products, powers and inversion (products and            *)
(* powers need non-vanishing hypotheses, since log of zero is an unspecified *)
(* real).                                                                    *)
(*                                                                           *)
(* Main results: NF_ELEM_ZERO, NF_ALG_INT_ALL, NF_ALG_INT_NORM_INTEGER,      *)
(* NF_LIOUVILLE, NF_PROJ_HEIGHT_GE, NF_PROJ_HEIGHT_INV, NF_PROJ_HEIGHT_MUL,  *)
(* NF_PROJ_HEIGHT_POW, their general forms NF_PROJ_HEIGHT_MUL_GEN,           *)
(* NF_PROJ_HEIGHT_POW_GEN, and NF_HEIGHT_ELEM_NONZERO; helper names          *)
(* NF_HEIGHT_*.                                                              *)
(*                                                                           *)
(* Uses: Baker/laurent_nf_defs.ml (nf_elem, nf_alg_int, nf_proj_height),     *)
(* Baker/ant_bridge_nf.ml (NF_ALG_INT_EMBEDDINGS, NF_EMBEDDING_HOMOMORPHISM, *)
(* NF_NORM_NUMBER_FIELD_NORM, NF_DATA_NUMBER_FIELD), ANT/numfield.ml         *)
(* (RING_OF_INTEGERS_CARRIER, RING_HOMOMORPHISM_RING_OF_INTEGERS,            *)
(* NUMBER_FIELD_NORM_INTEGRAL_Q), Library/fieldtheory.ml                     *)
(* (RING_OF_INT_SUBFIELD_GENERATED), Multivariate/complex_ring.ml            *)
(* (COMPLEX_RING_OF_INT), Baker/nf_order.ml (NF_DATA, NF_ORDER_ZERO),        *)
(* Baker/nf_defs.ml (nf_data, nf_order, NF_DATA_1_IN), Baker/algint.ml       *)
(* (algebraic_integer, INTEGRAL_ELEMENT_COMPLEX_RING).                       *)
(* ========================================================================= *)

needs "Baker/ant_bridge_nf.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Elements of K: an integer multiple lies in the order Z[theta]; vanishing  *)
(* at one conjugate implies vanishing at all conjugates.                     *)
(* ------------------------------------------------------------------------- *)

let NF_HEIGHT_ELEM_ORDER = prove
 (`!n r a. nf_elem n r a
           ==> ?d. integer d /\ ~(d = &0) /\ nf_order n r (\k. Cx d * a k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nf_elem; nf_order] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `p:num->real`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`n - 1`; `p:num->real`] THEN ASM_REWRITE_TAC[]);;

let NF_ELEM_ZERO = prove
 (`!n c r a k l. nf_data n c r /\ nf_elem n r a /\ k IN 1..n /\ l IN 1..n /\
                a k = Cx(&0) ==> a l = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC o
    MATCH_MP NF_HEIGHT_ELEM_ORDER) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                `\k. Cx d * (a:num->complex) k`; `k:num`; `l:num`]
    NF_ORDER_ZERO) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ENTIRE; CX_INJ]);;

let NF_HEIGHT_ELEM_NONZERO = prove
 (`!n c r a k. nf_data n c r /\ nf_elem n r a /\ ~(a 1 = Cx(&0)) /\
              k IN 1..n
              ==> ~(a k = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  UNDISCH_TAC `~((a:num->complex) 1 = Cx(&0))` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC NF_ELEM_ZERO THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`; `r:num->complex`; `k:num`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Conjugates of algebraic integers of K, and their norm, through the bridge *)
(* Baker/ant_bridge_nf.ml: they are the images x |-> nf_embedding n r k x of *)
(* an element x of the ring of integers of K, and their product is the norm  *)
(* of x (NUMBER_FIELD_NORM_INTEGRAL_Q).                                      *)
(* ------------------------------------------------------------------------- *)

let NF_ALG_INT_ALL = prove
 (`!n c r a k. nf_data n c r /\ nf_alg_int n r a /\ k IN 1..n
              ==> algebraic_integer(a k)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NF_ALG_INT_EMBEDDINGS th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:complex` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_ELEMENT_COMPLEX_RING] THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`]
    NF_EMBEDDING_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN(MP_TAC o SPEC `x:complex` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM]);;

let NF_ALG_INT_NORM_INTEGER = prove
 (`!n c r a. nf_data n c r /\ nf_alg_int n r a
            ==> ?m. integer m /\ cproduct(1..n) a = Cx m`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NF_ALG_INT_EMBEDDINGS th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `x IN ring_carrier(subfield_generated complex_ring
                                    {(r:num->complex) 1})`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `cproduct(1..n) a = cproduct(1..n) (\k. nf_embedding n r k x)`
  SUBST1_TAC THENL [MATCH_MP_TAC CPRODUCT_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `x:complex`]
    NF_NORM_NUMBER_FIELD_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`subfield_generated complex_ring {(r:num->complex) 1}`;
                 `x:complex`] NUMBER_FIELD_NORM_INTEGRAL_Q) THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[CONJUNCT1(MATCH_MP NF_DATA_NUMBER_FIELD th)]) THEN
  ASM_REWRITE_TAC[RING_OF_INT_SUBFIELD_GENERATED; COMPLEX_RING_OF_INT] THEN
  MESON_TAC[INTEGER_REAL_OF_INT]);;

(* ------------------------------------------------------------------------- *)
(* Liouville inequality: the norm of a non-zero algebraic integer of K is a  *)
(* non-zero integer.                                                         *)
(* ------------------------------------------------------------------------- *)

let NF_HEIGHT_PRODUCT_SPLIT = prove
 (`!(f:num->real) n. 1 <= n ==> product(1..n) f = f 1 * product(2..n) f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PRODUCT_CLAUSES_LEFT th]) THEN
  REWRITE_TAC[ARITH]);;

let NF_LIOUVILLE = prove
 (`!n c r w (B:num->real).
     nf_data n c r /\ nf_alg_int n r w /\ ~(w 1 = Cx(&0)) /\
     (!k. k IN 2..n ==> norm(w k) <= B k)
     ==> &1 <= norm(w 1) * product(2..n) B`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [nf_alg_int]) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `w:num->complex`]
    NF_ALG_INT_NORM_INTEGER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(m:real = &0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `cproduct(1..n) (w:num->complex) = Cx(&0)` THEN
    SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG; NOT_EXISTS_THM] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `w:num->complex`;
                  `k:num`] NF_HEIGHT_ELEM_NONZERO) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(m:real)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(m:real) = norm((w:num->complex) 1) * product(2..n) (\k. norm(w k))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `cproduct(1..n) (w:num->complex) = Cx m` THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
    SIMP_TAC[NORM_CPRODUCT; FINITE_NUMSEG; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[NF_HEIGHT_PRODUCT_SPLIT] THEN
    DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN REWRITE_TAC[NORM_POS_LE] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_NUMSEG]);;

(* ------------------------------------------------------------------------- *)
(* The height of a chosen pair: lower bound, inversion.                      *)
(* ------------------------------------------------------------------------- *)

let NF_PROJ_HEIGHT_GE = prove
 (`!n c r be ga x.
     nf_data n c r /\ nf_alg_int n r be /\ nf_alg_int n r ga /\
     ~(ga 1 = Cx(&0)) /\ be 1 = Cx x * ga 1 /\ &1 <= x
     ==> log x <= &n * nf_proj_height n be ga`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  SUBGOAL_THEN
   `!k. k IN 1..n
        ==> &0 < max (norm((be:num->complex) k)) (norm((ga:num->complex) k))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < b ==> &0 < max a b`) THEN
    REWRITE_TAC[COMPLEX_NORM_NZ] THEN MATCH_MP_TAC NF_HEIGHT_ELEM_NONZERO THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`; `r:num->complex`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[nf_alg_int];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&n * nf_proj_height n be ga =
    log(product(1..n) (\k. max (norm((be:num->complex) k))
                               (norm((ga:num->complex) k))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[nf_proj_height] THEN
    SUBGOAL_THEN `~(&n:real = &0)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC LOG_PRODUCT THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
   [UNDISCH_TAC `&1 <= x` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NF_HEIGHT_PRODUCT_SPLIT th]) THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`; `ga:num->complex`;
                 `\k. max (norm((be:num->complex) k))
                          (norm((ga:num->complex) k))`] NF_LIOUVILLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ARITH `b <= max a b`];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `&0 <= product(2..n) (\k. max (norm((be:num->complex) k))
                                 (norm((ga:num->complex) k)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN
    REWRITE_TAC[REAL_LE_MAX; NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((be:num->complex) 1) = x * norm((ga:num->complex) 1)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_ABS_REFL] THEN
    UNDISCH_TAC `&1 <= x` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `x * norm((ga:num->complex) 1) *
    product(2..n) (\k. max (norm((be:num->complex) k))
                           (norm((ga:num->complex) k)))` THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&1 <= x` THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL
     [UNDISCH_TAC
       `norm((be:num->complex) 1) = x * norm((ga:num->complex) 1)` THEN
      REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC]]);;

let NF_PROJ_HEIGHT_INV = prove
 (`!n be ga. nf_proj_height n ga be = nf_proj_height n be ga`,
  REWRITE_TAC[nf_proj_height; REAL_MAX_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Products and powers. Since log(&0) is an unspecified real, these need     *)
(* hypotheses keeping the maxima positive: in the general forms, a product   *)
(* (or a power) does not vanish simultaneously in both entries at any        *)
(* conjugate; in NF_PROJ_HEIGHT_MUL and NF_PROJ_HEIGHT_POW, the second       *)
(* entries ga do not vanish at any conjugate (for algebraic integers of K    *)
(* with ga 1 non-zero this is NF_HEIGHT_ELEM_NONZERO).                       *)
(* ------------------------------------------------------------------------- *)

let NF_HEIGHT_LOG_MAX_MUL = prove
 (`!b g b1 g1:complex.
     ~(b * b1 = Cx(&0)) \/ ~(g * g1 = Cx(&0))
     ==> log(max (norm(b * b1)) (norm(g * g1))) <=
         log(max (norm b) (norm g)) + log(max (norm b1) (norm g1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM COMPLEX_NORM_NZ; COMPLEX_NORM_MUL] THEN
  MP_TAC(ISPEC `b:complex` NORM_POS_LE) THEN
  MP_TAC(ISPEC `g:complex` NORM_POS_LE) THEN
  MP_TAC(ISPEC `b1:complex` NORM_POS_LE) THEN
  MP_TAC(ISPEC `g1:complex` NORM_POS_LE) THEN
  MAP_EVERY ABBREV_TAC
   [`u = norm(b:complex)`; `v = norm(g:complex)`; `u1 = norm(b1:complex)`;
    `v1 = norm(g1:complex)`] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `max (u * u1) (v * v1) <= max u v * max u1 v1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MAX_LE] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < max (u * u1) (v * v1)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < max u v /\ &0 < max u1 v1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < max u v * max u1 v1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `log(max u v * max u1 v1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[LOG_MUL; REAL_LE_REFL]]);;

let NF_PROJ_HEIGHT_MUL_GEN = prove
 (`!n be ga be' ga'.
     (!k. k IN 1..n
          ==> ~(be k * be' k = Cx(&0)) \/ ~(ga k * ga' k = Cx(&0)))
     ==> nf_proj_height n (\k. be k * be' k) (\k. ga k * ga' k) <=
         nf_proj_height n be ga + nf_proj_height n be' ga'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nf_proj_height; real_div] THEN
  REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC NF_HEIGHT_LOG_MAX_MUL THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG]);;

let NF_PROJ_HEIGHT_MUL = prove
 (`!n be ga be' ga'.
     1 <= n /\ (!k. k IN 1..n ==> ~(ga k = Cx(&0)) /\ ~(ga' k = Cx(&0)))
     ==> nf_proj_height n (\k. be k * be' k) (\k. ga k * ga' k) <=
         nf_proj_height n be ga + nf_proj_height n be' ga'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NF_PROJ_HEIGHT_MUL_GEN THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN DISJ2_TAC THEN
  ASM_SIMP_TAC[COMPLEX_ENTIRE]);;

let NF_HEIGHT_MAX_POW = prove
 (`!x y n. &0 <= x /\ &0 <= y ==> max (x pow n) (y pow n) = max x y pow n`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(SPECL [`x:real`; `y:real`] REAL_LE_TOTAL) THENL
   [SUBGOAL_THEN `x pow n <= y pow n` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `max x y = y /\ max (x pow n) (y pow n) = y pow n`
     (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_REAL_ARITH_TAC; REFL_TAC];
    SUBGOAL_THEN `y pow n <= x pow n` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `max x y = x /\ max (x pow n) (y pow n) = x pow n`
     (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_REAL_ARITH_TAC; REFL_TAC]]);;

let NF_HEIGHT_LOG_MAX_POW = prove
 (`!(b:complex) (g:complex) m.
     ~(b = Cx(&0)) \/ ~(g = Cx(&0))
     ==> log(max (norm(b pow m)) (norm(g pow m))) =
         &m * log(max (norm b) (norm g))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM COMPLEX_NORM_NZ] THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_POW] THEN
  SIMP_TAC[NF_HEIGHT_MAX_POW; NORM_POS_LE] THEN
  MATCH_MP_TAC LOG_POW THEN ASM_REAL_ARITH_TAC);;

let NF_PROJ_HEIGHT_POW_GEN = prove
 (`!n be ga m.
     (!k. k IN 1..n ==> ~(be k = Cx(&0)) \/ ~(ga k = Cx(&0)))
     ==> nf_proj_height n (\k. be k pow m) (\k. ga k pow m) =
         &m * nf_proj_height n be ga`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[nf_proj_height; real_div; REAL_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC NF_HEIGHT_LOG_MAX_POW THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG]);;

let NF_PROJ_HEIGHT_POW = prove
 (`!n be ga m.
     (!k. k IN 1..n ==> ~(ga k = Cx(&0)))
     ==> nf_proj_height n (\k. be k pow m) (\k. ga k pow m) =
         &m * nf_proj_height n be ga`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NF_PROJ_HEIGHT_POW_GEN THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN DISJ2_TAC THEN
  ASM_SIMP_TAC[]);;
