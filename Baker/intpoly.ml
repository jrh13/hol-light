(* ========================================================================= *)
(* Integer polynomial expressions in several complex variables.              *)
(*                                                                           *)
(* Purpose: intpoly v n b g means that g is a polynomial with integer        *)
(* coefficients in the variables x r (r IN v), of degree <= n r in x r,      *)
(* whose coefficients have absolute sum <= b. Closure under constants,       *)
(* variables, sums, products, powers, vsum, cproduct, integer multiples,     *)
(* monomials and integer linear forms, with explicit degrees and sizes; the  *)
(* upper bound norm(g x) <= b prod_r m r^(n r) for norm(x r) <= m r; sums of *)
(* products over (dependent) cartesian products; and the Liouville           *)
(* inequality for a nonzero intpoly at roots of monic integer polynomials,   *)
(* each given by the family of all its roots (from                           *)
(* POWER_SUMS_INTEGER_LOWER_BOUND).                                          *)
(*                                                                           *)
(* Main results: intpoly (definition), INTPOLY_CONST, INTPOLY_VAR,           *)
(*   INTPOLY_ADD, INTPOLY_SUB, INTPOLY_MUL, INTPOLY_POW, INTPOLY_VSUM,       *)
(*   INTPOLY_CPRODUCT, INTPOLY_MONOMIAL, INTPOLY_CMUL, INTPOLY_LINEAR,       *)
(*   INTPOLY_MONO, INTPOLY_BOUND; VSUM_CPRODUCT_CARTESIAN_PRODUCT,           *)
(*   CARD_CARTESIAN_PRODUCT;                                                 *)
(*   INTPOLY_LIOUVILLE_MONIC.                                                *)
(*                                                                           *)
(* Uses: Library/ring_det.ml (RING_SUM_PRODUCT_CARTESIAN_PRODUCT, of which   *)
(*   VSUM_CPRODUCT_CARTESIAN_PRODUCT is the complex case, through            *)
(*   COMPLEX_RING_SUM and COMPLEX_RING_PRODUCT of                            *)
(*   Multivariate/complex_ring.ml), Baker/prelim.ml (complex integers),      *)
(*   Baker/algebraic.ml (CPRODUCT_DELETE, POWER_SUMS_INTEGER_LOWER_BOUND).   *)
(* ========================================================================= *)

needs "Baker/algebraic.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* intpoly v n b g: g is an integer polynomial in the variables x r (r IN v) *)
(* of degree <= n r in x r, whose coefficients have absolute sum <= b. The   *)
(* terms are indexed by an arbitrary finite set of numbers.                  *)
(* ------------------------------------------------------------------------- *)

let intpoly = new_definition
 `intpoly (v:num->bool) (n:num->num) (b:real) (g:(num->complex)->complex) <=>
        ?(s:num->bool) c e. FINITE s /\
                (!k. k IN s ==> integer(c k) /\ !r. r IN v ==> e k r <= n r) /\
                sum s (\k. abs(c k)) <= b /\
                !x. g x = vsum s (\k. Cx(c k) *
                  cproduct v (\r. x r pow e k r))`;;

let INTPOLY_EQ = prove
 (`!v n b g g'. intpoly v n b g /\ (!x. g' x = g x) ==> intpoly v n b g'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM FUN_EQ_THM; ETA_AX] THEN MESON_TAC[]);;

let INTPOLY_MONO = prove
 (`!v n n' b b' g.
        intpoly v n b g /\ (!r. r IN v ==> n r <= n' r) /\ b <= b'
        ==> intpoly v n' b' g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[intpoly] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`s:num->bool`; `c:num->real`; `e:num->num->num`] THEN
  ASM_MESON_TAC[LE_TRANS; REAL_LE_TRANS]);;

let INTPOLY_EQ_ON = prove
 (`!v n b g x y.
        intpoly v n b g /\ (!r. r IN v ==> x r = y r) ==> g x = g y`,
  REWRITE_TAC[intpoly] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC CPRODUCT_EQ THEN
  ASM_SIMP_TAC[]);;

let INTPOLY_BOUND_POS = prove
 (`!v n b g. intpoly v n b g ==> &0 <= b`,
  REWRITE_TAC[intpoly] THEN REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `sum s (\k:num. abs(c k))` THEN
  ASM_SIMP_TAC[SUM_POS_LE; REAL_ABS_POS]);;

let INTPOLY_CONST = prove
 (`!v n b c. integer c /\ abs c <= b ==> intpoly v n b (\x. Cx c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[intpoly] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\k:num. c:real`; `\k:num r:num. 0`] THEN
  ASM_REWRITE_TAC[FINITE_SING; FORALL_IN_INSERT; NOT_IN_EMPTY; LE_0] THEN
  ASM_REWRITE_TAC[SUM_SING; VSUM_SING; complex_pow] THEN
  MATCH_MP_TAC(COMPLEX_RING
   `x = Cx(&1) ==> Cx c = Cx c * x`) THEN
  MATCH_MP_TAC CPRODUCT_EQ_1 THEN REWRITE_TAC[]);;

let INTPOLY_VAR = prove
 (`!v n b r.
        FINITE v /\ r IN v /\ 1 <= n r /\ &1 <= b
        ==> intpoly v n b (\x. x r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[intpoly] THEN
  MAP_EVERY EXISTS_TAC
   [`{0}`; `\k:num. &1`; `\k:num i:num. if i = r then 1 else 0`] THEN
  ASM_REWRITE_TAC[FINITE_SING; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[INTEGER_CLOSED; SUM_SING; VSUM_SING; REAL_ABS_NUM] THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LID] THEN CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[LE_0]; ALL_TAC] THEN
  X_GEN_TAC `x:num->complex` THEN
  MP_TAC(ISPECL [`\i:num. (x:num->complex) i pow (if i = r then 1 else 0)`;
                 `v:num->bool`; `r:num`] CPRODUCT_DELETE) THEN
  ASM_REWRITE_TAC[COMPLEX_POW_1] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(COMPLEX_RING `y = Cx(&1) ==> x = x * y`) THEN
  MATCH_MP_TAC CPRODUCT_EQ_1 THEN SIMP_TAC[IN_DELETE; complex_pow]);;

let INTPOLY_ADD = prove
 (`!v n b1 b2 g1 g2.
        intpoly v n b1 g1 /\ intpoly v n b2 g2
        ==> intpoly v n (b1 + b2) (\x. g1 x + g2 x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[intpoly] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `s1:num->bool` (X_CHOOSE_THEN `c1:num->real`
     (X_CHOOSE_THEN `e1:num->num->num` STRIP_ASSUME_TAC)))
   (X_CHOOSE_THEN `s2:num->bool` (X_CHOOSE_THEN `c2:num->real`
     (X_CHOOSE_THEN `e2:num->num->num` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (NUMPAIR 0) s1 UNION IMAGE (NUMPAIR 1) s2`;
    `\k. if NUMFST k = 0 then c1(NUMSND k) else c2(NUMSND k):real`;
    `\k. if NUMFST k = 0 then e1(NUMSND k) else e2(NUMSND k):num->num`] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (NUMPAIR 0) s1) (IMAGE (NUMPAIR 1) s2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    MESON_TAC[NUMPAIR_INJ; ARITH_RULE `~(0 = 1)`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; FORALL_IN_UNION; FORALL_IN_IMAGE;
               NUMPAIR_DEST; ARITH_EQ; SUM_UNION; VSUM_UNION] THEN
  ASM_SIMP_TAC[SUM_IMAGE; VSUM_IMAGE; NUMPAIR_INJ; o_DEF; NUMPAIR_DEST;
               ARITH_EQ] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[]);;

let INTPOLY_MUL = prove
 (`!v n1 n2 b1 b2 g1 g2.
        FINITE v /\ intpoly v n1 b1 g1 /\ intpoly v n2 b2 g2
        ==> intpoly v (\r. n1 r + n2 r) (b1 * b2) (\x. g1 x * g2 x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= b1 /\ &0 <= b2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[INTPOLY_BOUND_POS]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[intpoly]) THEN REWRITE_TAC[intpoly] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `s2:num->bool` (X_CHOOSE_THEN `c2:num->real`
     (X_CHOOSE_THEN `e2:num->num->num` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `s1:num->bool` (X_CHOOSE_THEN `c1:num->real`
     (X_CHOOSE_THEN `e1:num->num->num` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (\(i,j). NUMPAIR i j) (s1 CROSS s2)`;
    `\k. c1(NUMFST k) * c2(NUMSND k):real`;
    `\k (r:num). (e1:num->num->num) (NUMFST k) r +
                 (e2:num->num->num) (NUMSND k) r`] THEN
  SUBGOAL_THEN
   `!x y. x IN s1 CROSS s2 /\ y IN s1 CROSS s2 /\
          (\(i,j). NUMPAIR i j) x = (\(i,j). NUMPAIR i j) y ==> x = y`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; NUMPAIR_INJ; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE((s1:num->bool) CROSS (s2:num->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_CROSS]; ALL_TAC] THEN
  SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS;
           NUMPAIR_DEST; ASSUME `FINITE((s1:num->bool) CROSS (s2:num->bool))`;
           ASSUME `!x. (g1:(num->complex)->complex) x =
                       vsum s1 (\k:num. Cx(c1 k) *
                                        cproduct v (\r. x r pow e1 k r))`;
           ASSUME `!x. (g2:(num->complex)->complex) x =
                       vsum s2 (\k:num. Cx(c2 k) *
                                        cproduct v (\r. x r pow e2 k r))`] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[REWRITE_RULE[ETA_AX] (MATCH_MP SUM_IMAGE th)]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[REWRITE_RULE[ETA_AX]
   (MATCH_MP VSUM_IMAGE
      (CONJ (ASSUME `FINITE((s1:num->bool) CROSS (s2:num->bool))`) th))]) THEN
  REWRITE_TAC[o_DEF; LAMBDA_PAIR_THM; NUMPAIR_DEST] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[INTEGER_CLOSED; LE_ADD2];
    REWRITE_TAC[CROSS] THEN ASM_SIMP_TAC[GSYM SUM_SUM_PRODUCT] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[SUM_LMUL; SUM_RMUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SUM_POS_LE; REAL_ABS_POS];
    X_GEN_TAC `x:num->complex` THEN REWRITE_TAC[CROSS] THEN
    ASM_SIMP_TAC[GSYM VSUM_VSUM_PRODUCT] THEN
    ASM_SIMP_TAC[GSYM VSUM_COMPLEX_RMUL] THEN
    ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[COMPLEX_POW_ADD; CPRODUCT_MUL; CX_MUL] THEN
    REWRITE_TAC[COMPLEX_MUL_AC]]);;

let INTPOLY_NEG = prove
 (`!v n b g. intpoly v n b g ==> intpoly v n b (\x. --(g x))`,
  REWRITE_TAC[intpoly] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`s:num->bool`; `\k. --(c:num->real) k`; `e:num->num->num`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED; REAL_ABS_NEG; CX_NEG; COMPLEX_MUL_LNEG;
               VSUM_NEG]);;

let INTPOLY_SUB = prove
 (`!v n b1 b2 g1 g2.
        intpoly v n b1 g1 /\ intpoly v n b2 g2
        ==> intpoly v n (b1 + b2) (\x. g1 x - g2 x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[complex_sub] THEN
  MATCH_MP_TAC INTPOLY_ADD THEN ASM_SIMP_TAC[INTPOLY_NEG; ETA_AX]);;

let INTPOLY_POW = prove
 (`!v n b g k.
        FINITE v /\ intpoly v n b g
        ==> intpoly v (\r. k * n r) (b pow k) (\x. g x pow k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC(`k:num`,`k:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[complex_pow; real_pow; MULT_CLAUSES] THENL
   [MATCH_MP_TAC INTPOLY_CONST THEN
    REWRITE_TAC[INTEGER_CLOSED; REAL_ABS_NUM; REAL_LE_REFL];
    MATCH_MP_TAC INTPOLY_MONO THEN
    MAP_EVERY EXISTS_TAC [`\r:num. (n:num->num) r + k * n r`; `b *
      b pow k`] THEN
    REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTPOLY_MUL THEN ASM_REWRITE_TAC[ETA_AX];
      ARITH_TAC]]);;

let INTPOLY_VSUM = prove
 (`!v n (b:A->real) g t.
        FINITE t /\ (!i. i IN t ==> intpoly v n (b i) (g i))
        ==> intpoly v n (sum t b) (\x. vsum t (\i. g i x))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; SUM_CLAUSES; FORALL_IN_INSERT] THEN CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_VEC_0; NOT_IN_EMPTY] THEN
     MATCH_MP_TAC INTPOLY_CONST THEN
    REWRITE_TAC[INTEGER_CLOSED; REAL_ABS_NUM; REAL_LE_REFL];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INTPOLY_ADD THEN
    ASM_SIMP_TAC[ETA_AX]]);;

let INTPOLY_CPRODUCT = prove
 (`!v (n:A->num->num) b g t.
        FINITE v /\ FINITE t /\
        (!i. i IN t ==> intpoly v (n i) (b i) (g i))
        ==> intpoly v (\r. nsum t (\i. n i r)) (product t b)
                    (\x. cproduct t (\i. g i x))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  ASM_CASES_TAC `FINITE(v:num->bool)` THEN ASM_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES; PRODUCT_CLAUSES; NSUM_CLAUSES;
           FORALL_IN_INSERT] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY] THEN MATCH_MP_TAC INTPOLY_CONST THEN
    REWRITE_TAC[INTEGER_CLOSED; REAL_ABS_NUM; REAL_LE_REFL];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INTPOLY_MUL THEN
    ASM_SIMP_TAC[ETA_AX]]);;

let INTPOLY_BOUND = prove
 (`!v n b g x m.
        FINITE v /\ intpoly v n b g /\
        (!r. r IN v ==> norm(x r) <= m r /\ &1 <= m r)
        ==> norm(g x) <= b * product v (\r. m r pow n r)`,
  REWRITE_TAC[intpoly] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum (s:num->bool)
        (\k:num. abs((c:num->real) k) *
                 product (v:num->bool)
                         (\r. (m:num->real) r pow (n:num->num) r))`
  THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[NORM_CPRODUCT] THEN MATCH_MP_TAC PRODUCT_LE THEN
    ASM_REWRITE_TAC[NORM_POS_LE; COMPLEX_NORM_POW; REAL_LE_POW_2] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    CONJ_TAC THENL [SIMP_TAC[REAL_POW_LE; NORM_POS_LE]; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `(m:num->real) r pow (e:num->num->num) k r` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_SIMP_TAC[]];
    ASM_SIMP_TAC[SUM_RMUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_ARITH `&1 <= x ==> &0 <= x`]]);;

(* ------------------------------------------------------------------------- *)
(* Sums over tuples: a sum of products over a (dependent) cartesian product  *)
(* is the product of the sums (the complex case of                           *)
(* RING_SUM_PRODUCT_CARTESIAN_PRODUCT of ring_det.ml).                       *)
(* ------------------------------------------------------------------------- *)

let VSUM_CPRODUCT_CARTESIAN_PRODUCT = prove
 (`!(k:K->bool) (s:K->A->bool) (f:K->A->complex).
        FINITE k /\ (!i. i IN k ==> FINITE(s i))
        ==> vsum (cartesian_product k s) (\x. cproduct k (\i. f i (x i))) =
            cproduct k (\i. vsum (s i) (f i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`complex_ring`; `k:K->bool`; `s:K->A->bool`;
                 `f:K->A->complex`] RING_SUM_PRODUCT_CARTESIAN_PRODUCT) THEN
  ASM_SIMP_TAC[in_complex_ring; COMPLEX_RING_SUM; COMPLEX_RING_PRODUCT;
               FINITE_CARTESIAN_PRODUCT_FINITE] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC CPRODUCT_EQ THEN
  ASM_SIMP_TAC[COMPLEX_RING_SUM]);;

(* ------------------------------------------------------------------------- *)
(* Sums of an integer polynomial over all tuples of conjugates are integers  *)
(* when each family of conjugates has integer power sums.                    *)
(* ------------------------------------------------------------------------- *)

let INTPOLY_CARTESIAN_SUM_INTEGER = prove
 (`!v n b g (d:num->num) (rho:num->num->complex).
        FINITE v /\ intpoly v n b g /\
        (!r m. r IN v ==> complex_integer(vsum(1..d r) (\i. rho r i pow m)))
        ==> complex_integer
             (vsum (cartesian_product v (\r. 1..d r))
                   (\t. g(\r. rho r (t r))))`,
  REWRITE_TAC[intpoly] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE(cartesian_product v (\r:num. 1..d r))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_CARTESIAN_PRODUCT_FINITE; FINITE_NUMSEG]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_SWAP o rand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC COMPLEX_INTEGER_VSUM THEN X_GEN_TAC `k:num` THEN
  DISCH_TAC THEN ASM_SIMP_TAC[VSUM_COMPLEX_LMUL] THEN
  MATCH_MP_TAC COMPLEX_INTEGER_MUL THEN
  ASM_SIMP_TAC[COMPLEX_INTEGER_CX] THEN
  MP_TAC(ISPECL [`v:num->bool`; `\r:num. 1..d r`;
                 `\r i. (rho:num->num->complex) r i pow (e:num->num->num) k r`]
        VSUM_CPRODUCT_CARTESIAN_PRODUCT) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC COMPLEX_INTEGER_CPRODUCT THEN ASM_SIMP_TAC[ETA_AX]);;

let CARD_CARTESIAN_PRODUCT = prove
 (`!(k:K->bool) (s:K->A->bool).
        FINITE k /\ (!i. i IN k ==> FINITE(s i))
        ==> CARD(cartesian_product k s) = nproduct k (\i. CARD(s i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:K->bool`; `s:K->A->bool`; `\i:K x:A. Cx(&1)`]
        VSUM_CPRODUCT_CARTESIAN_PRODUCT) THEN
  ASM_SIMP_TAC[VSUM_CONST; FINITE_CARTESIAN_PRODUCT_FINITE; COMPLEX_CMUL;
               COMPLEX_MUL_RID; CPRODUCT_EQ_1] THEN
  ASM_SIMP_TAC[GSYM CX_PRODUCT; CX_INJ] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_NPRODUCT; REAL_OF_NUM_EQ]);;

let CARD_CARTESIAN_PRODUCT_NUMSEG = prove
 (`!v d. FINITE v
         ==> CARD(cartesian_product v (\r:num. 1..d r)) = nproduct v d`,
  SIMP_TAC[CARD_CARTESIAN_PRODUCT; FINITE_NUMSEG; CARD_NUMSEG_1; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Liouville inequality for a nonzero integer polynomial expression in roots *)
(* of monic integer polynomials (given by their families of all roots).      *)
(* ------------------------------------------------------------------------- *)

let INTPOLY_LIOUVILLE_MONIC = prove
 (`!v n b g d (rho:num->num->complex) t0 m.
        FINITE v /\ intpoly v n b g /\
        (!r k. r IN v ==> complex_integer(vsum(1..d r) (\i. rho r i pow k))) /\
        (!r i. r IN v /\ i IN 1..d r ==> norm(rho r i) <= m r) /\
        (!r. r IN v ==> &1 <= m r) /\
        t0 IN cartesian_product v (\r. 1..d r) /\
        ~(g(\r. rho r (t0 r)) = Cx(&0))
        ==> inv(&(FACT(nproduct v d)) *
                (max (&1) (b * product v (\r. m r pow n r))) pow
                (nproduct v d - 1))
            <= norm(g(\r. rho r (t0 r)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(cartesian_product v (\r:num. 1..d r))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_CARTESIAN_PRODUCT_FINITE; FINITE_NUMSEG];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM CARD_CARTESIAN_PRODUCT_NUMSEG] THEN
  MP_TAC(ISPECL
   [`cartesian_product v (\r:num. 1..d r)`;
    `\t:num->num. (g:(num->complex)->complex) (\r. rho r (t r))`;
    `t0:num->num`; `max (&1) (b * product v (\r:num. (m:num->real) r pow n r))`]
   POWER_SUMS_INTEGER_LOWER_BOUND) THEN
  ASM_REWRITE_TAC[REAL_MAX_MAX; REAL_ARITH `&1 <= max (&1) x`] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `t:num->num` THEN REWRITE_TAC[IN_CARTESIAN_PRODUCT] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= max (&1) b`) THEN
    MATCH_MP_TAC INTPOLY_BOUND THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`v:num->bool`; `\r:num. k * (n:num->num) r`; `b pow k`;
                   `\x. (g:(num->complex)->complex) x pow k`;
                   `d:num->num`; `rho:num->num->complex`]
      INTPOLY_CARTESIAN_SUM_INTEGER) THEN
    ASM_SIMP_TAC[INTPOLY_POW]]);;

(* ------------------------------------------------------------------------- *)
(* Monomials and integer multiples.                                          *)
(* ------------------------------------------------------------------------- *)

let INTPOLY_MONOMIAL = prove
 (`!v s k. FINITE v /\ s SUBSET v
           ==> intpoly v (\r. if r IN s then k r else 0) (&1)
                       (\x. cproduct s (\r. x r pow k r))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[intpoly] THEN
  MAP_EVERY EXISTS_TAC
   [`{0}`; `\i:num. &1`;
    `\i:num r:num. if r IN s then (k:num->num) r else 0`] THEN
  REWRITE_TAC[FINITE_SING; FORALL_IN_INSERT; NOT_IN_EMPTY; INTEGER_CLOSED;
              LE_REFL; SUM_SING; VSUM_SING; REAL_ABS_NUM; REAL_LE_REFL;
              COMPLEX_MUL_LID] THEN
  X_GEN_TAC `x:num->complex` THEN
  MP_TAC(ISPECL [`\r. (x:num->complex) r pow (if r IN s then k r else 0)`;
                 `s:num->bool`; `v:num->bool`] CPRODUCT_SUPERSET) THEN
  ASM_SIMP_TAC[complex_pow] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC CPRODUCT_EQ THEN SIMP_TAC[]);;

let INTPOLY_CMUL = prove
 (`!v n b g a. integer a /\ intpoly v n b g
               ==> intpoly v n (abs a * b) (\x. Cx a * g x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[intpoly] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`s:num->bool`; `\k. a * (c:num->real) k`; `e:num->num->num`] THEN
  ASM_SIMP_TAC[INTEGER_MUL; REAL_ABS_MUL; SUM_LMUL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; CX_MUL; COMPLEX_MUL_ASSOC]]);;

let INTPOLY_NUM_MUL = prove
 (`!v n b g k. intpoly v n b g ==> intpoly v n (&k * b) (\x. Cx(&k) * g x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`v:num->bool`; `n:num->num`; `b:real`;
                 `g:(num->complex)->complex`; `&k`] INTPOLY_CMUL) THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED; REAL_ABS_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Linear forms with integer coefficients.                                   *)
(* ------------------------------------------------------------------------- *)

let INTPOLY_LINEAR = prove
 (`!v (c:num->real) (p:num->num) t.
        FINITE v /\ FINITE t /\ (!j. j IN t ==> integer(c j) /\ p j IN v)
        ==> intpoly v (\r. 1) (sum t (\j. abs(c j)))
                    (\x. vsum t (\j. Cx(c j) * x(p j)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`v:num->bool`; `\r:num. 1`; `\j:num. abs((c:num->real) j)`;
                 `\j (x:num->complex). Cx((c:num->real) j) * x((p:num->num) j)`;
                 `t:num->bool`] INTPOLY_VSUM) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`v:num->bool`; `\r:num. 1`; `&1`;
                 `\x:num->complex. x((p:num->num) j)`;
                 `(c:num->real) j`] INTPOLY_CMUL) THEN
  REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC INTPOLY_VAR THEN
  ASM_SIMP_TAC[LE_REFL; REAL_LE_REFL]);;
