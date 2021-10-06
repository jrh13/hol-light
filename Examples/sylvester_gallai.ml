(* ========================================================================= *)
(* The Sylvester-Gallai theorem.                                             *)
(* ========================================================================= *)

needs "Multivariate/convex.ml";;

(* ------------------------------------------------------------------------- *)
(* The main lemma that we reduce things to.                                  *)
(* ------------------------------------------------------------------------- *)

let SYLVESTER_GALLAI_LEMMA = prove
 (`!p q b c:real^2.
        between b (q,c) /\ ~(p IN affine hull {q,c}) /\
        orthogonal (p - q) (c - q) /\ ~(c = b) /\ ~(c = q)
        ==> ~(b IN affine hull {p,c}) /\
            ?x. x IN affine hull {p,c} /\ dist(b,x) < dist(p,q)`,
  GEOM_ORIGIN_TAC `q:real^2` THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `c:real^2` THEN
  X_GEN_TAC `c:real` THEN
  ASM_CASES_TAC `c = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  ASM_REWRITE_TAC[REAL_LE_LT] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`pp:real^2`; `bb:real^2`] THEN
  REWRITE_TAC[BETWEEN_IN_SEGMENT; SEGMENT_CONVEX_HULL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
        CONVEX_HULL_SUBSET_AFFINE_HULL)) THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; IN_INSERT; SPAN_INSERT_0] THEN
  REWRITE_TAC[SPAN_SING; IN_ELIM_THM; IN_UNIV; VECTOR_MUL_ASSOC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bc:real` SUBST_ALL_TAC) THEN
  ABBREV_TAC `b:real = bc * c` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; orthogonal; DOT_2] THEN
  SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID] THEN
  ASM_SIMP_TAC[REAL_ENTIRE; REAL_LT_IMP_NZ; VECTOR_MUL_EQ_0] THEN
  ASM_SIMP_TAC[VECTOR_MUL_RCANCEL; BASIS_NONZERO; DIMINDEX_2; ARITH] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
   [GSYM SEGMENT_CONVEX_HULL]) THEN
  REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; between; DIST_0] THEN
  REWRITE_TAC[dist; GSYM VECTOR_SUB_RDISTRIB; NORM_MUL] THEN
  SIMP_TAC[NORM_BASIS; REAL_MUL_RID; DIMINDEX_2; ARITH] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `abs c = abs b + abs(b - c)
    ==> &0 < c ==> &0 <= b /\ (b < c \/ b = c)`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?p. ~(p = &0) /\ pp:real^2 = p % basis 2`
   (CHOOSE_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))
  THENL
   [EXISTS_TAC `(pp:real^2)$2` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `&0`) THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[AFFINE_HULL_2_ALT; EXISTS_IN_GSPEC; IN_UNIV; NORM_LT] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; CART_EQ; DIMINDEX_2; FORALL_2] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; REAL_ADD_LID] THEN
    REWRITE_TAC[REAL_RING `&0 = p + u * (&0 - p) <=> p = &0 \/ u = &1`] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN ASM_REWRITE_TAC[UNWIND_THM2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH
   `b - (p + u % (c - p)):real^2 = (b - u % c) - (&1 - u) % p`] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_SUB_RDISTRIB] THEN
  REWRITE_TAC[NORM_POS_LT; GSYM DOT_POS_LT] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(a - b) dot (a - b) = a dot a + b dot b - &2 * a dot b`] THEN
  REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN
  SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_2; ARITH; REAL_MUL_RZERO] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_SUB_RZERO] THEN
  SUBGOAL_THEN `&0 < c pow 2 /\ &0 < p pow 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
    ASM_REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE; REAL_ENTIRE];
    ALL_TAC] THEN
  ASM_CASES_TAC `b = &0` THENL
   [EXISTS_TAC `p pow 2 / (p pow 2 + c pow 2):real` THEN
    ASM_REWRITE_TAC[REAL_ARITH
     `(&0 - u * c) * (&0 - u * c) + ((&1 - u) * p) * ((&1 - u) * p) < p * p <=>
      u * u * c pow 2 < u * (&2 - u) * p pow 2`] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_DIV; REAL_LT_ADD] THEN
    SIMP_TAC[REAL_ARITH `u * c < (&2 - u) * p <=> u * (p + c) < &2 * p`] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LT_ADD] THEN
    ASM_REAL_ARITH_TAC;
    EXISTS_TAC `b:real / c` THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_SUB_REFL] THEN
    REWRITE_TAC[REAL_ARITH
     `&0 * &0 + (u * p) * (u * p) < p * p <=> &0 < (&1 - u * u) * p * p`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[GSYM REAL_POW_2] THEN
    REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_POW_1_LT THEN
    SIMP_TAC[ARITH_EQ; REAL_SUB_LE; REAL_ARITH `&1 - x < &1 <=> &0 < x`] THEN
    ASM_SIMP_TAC[ARITH_EQ; REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The following lemmas drive a case analysis to pick the right points.      *)
(* ------------------------------------------------------------------------- *)

let cases_quick = prove
 (`!q a b c:real^N.
        collinear {q,a,b,c} /\ between b (a,c)
        ==> between b (q,a) \/ between b (q,c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[COLLINEAR_AFFINE_HULL; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
  GEOM_ORIGIN_TAC `u:real^N` THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `v:real^N` THEN
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; IN_INSERT] THEN
  REWRITE_TAC[SPAN_INSERT_0; SPAN_SING; INSERT_SUBSET; EMPTY_SUBSET] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[between; dist; GSYM VECTOR_SUB_RDISTRIB] THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
  REWRITE_TAC[REAL_MUL_RID; GSYM REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[REAL_EQ_MUL_RCANCEL] THEN
  ASM_CASES_TAC `abs v = &0` THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let cases_lemma = prove
 (`!q a b c:real^N.
        collinear {q,a,b,c}
        ==> between a (q,b) \/ between a (q,c) \/
            between b (q,c) \/ between b (q,a) \/
            between c (q,a) \/ between c (q,b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `collinear {a:real^N,b,c}` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        COLLINEAR_SUBSET)) THEN SET_TAC[];
    REWRITE_TAC[COLLINEAR_BETWEEN_CASES] THEN
    REPEAT(ONCE_REWRITE_TAC[TAUT `a \/ b \/ c \/ d <=> (a \/ b) \/ c \/ d`] THEN
           MATCH_MP_TAC MONO_OR THEN CONJ_TAC) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] cases_quick) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[INSERT_AC]]);;

(* ------------------------------------------------------------------------- *)
(* Kelly's proof of the Sylvester-Gallai theorem.                            *)
(* ------------------------------------------------------------------------- *)

let SYLVESTER_GALLAI = prove
 (`!s:real^2->bool.
        FINITE s /\
        (!a b. a IN s /\ b IN s /\ ~(a = b)
               ==> ?c. c IN s /\ ~(c = a) /\ ~(c = b) /\ collinear {a,b,c})
        ==> collinear s`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^2->bool = {}` THEN
  ASM_REWRITE_TAC[COLLINEAR_EMPTY] THEN
  ASM_CASES_TAC `?a:real^2. s = {a}` THENL
   [ASM_MESON_TAC[COLLINEAR_SING]; STRIP_TAC] THEN
  ABBREV_TAC
   `L = {affine hull {a,b} | a IN s /\ b IN s /\ ~(a:real^2 = b)}` THEN
  SUBGOAL_THEN `FINITE(L:(real^2->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    ONCE_REWRITE_TAC[SET_RULE
     `{f x y | x IN s /\ y IN s /\ P x y} =
      {f x y | x IN s /\ y IN {y | y IN s /\ P x y}}`] THEN
    ASM_SIMP_TAC[FINITE_PRODUCT_DEPENDENT; FINITE_RESTRICT];
    ALL_TAC] THEN
  ASM_CASES_TAC `L:(real^2->bool)->bool = {}` THENL
   [UNDISCH_TAC `L:(real^2->bool)->bool = {}` THEN EXPAND_TAC "L" THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC
   `{ dist(closest_point l p,p) |
      l IN L /\ p IN {p:real^2 | p IN s /\ &0 < dist(closest_point l p,p)}}`
   INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_PRODUCT_DEPENDENT; FINITE_RESTRICT] THEN
  ASM_REWRITE_TAC[SET_RULE
   `{f x y | x IN s /\ y IN t x} = {} <=>
    s = {} \/ (!x. x IN s ==> t x = {})`] THEN
  MATCH_MP_TAC(TAUT `(p ==> r) /\ (q ==> r) ==> (~p ==> q) ==> r`) THEN
  CONJ_TAC THENL
   [SIMP_TAC[SET_RULE `{x | x IN s /\ P x} = {} <=> !x. x IN s ==> ~P x`] THEN
    REWRITE_TAC[GSYM DIST_NZ] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `l:real^2->bool` o
        GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(MP_TAC o SPEC `l:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `closed(l:real^2->bool) /\ ~(l = {})` ASSUME_TAC THENL
     [UNDISCH_TAC `(l:real^2->bool) IN L` THEN EXPAND_TAC "L" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[CLOSED_AFFINE; AFFINE_AFFINE_HULL] THEN
      REWRITE_TAC[AFFINE_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
      ASM_SIMP_TAC[CLOSEST_POINT_REFL]] THEN
    DISCH_TAC THEN MATCH_MP_TAC COLLINEAR_SUBSET THEN
    EXISTS_TAC `l:real^2->bool` THEN ASM_REWRITE_TAC[SUBSET] THEN
    UNDISCH_TAC `(l:real^2->bool) IN L` THEN EXPAND_TAC "L" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_MESON_TAC[COLLINEAR_AFFINE_HULL; SUBSET_REFL];
    ALL_TAC] THEN
  SIMP_TAC[IMP_CONJ; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`l:real^2->bool`; `p:real^2`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `affine(l:real^2->bool) /\ ~(l = {})` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(l:real^2->bool) IN L` THEN EXPAND_TAC "L" THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    SIMP_TAC[CLOSED_AFFINE; AFFINE_AFFINE_HULL] THEN
    REWRITE_TAC[AFFINE_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_AFFINE) THEN
  ABBREV_TAC `q = closest_point l p:real^2` THEN
  DISCH_TAC THEN REWRITE_TAC[DIST_NZ] THEN DISCH_TAC THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(q:real^2) IN l` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSEST_POINT_IN_SET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?b c:real^2. b IN s /\ c IN s /\ b IN l /\ c IN l /\
                 ~(b = c) /\ between b (q,c)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(l:real^2->bool) IN L` THEN EXPAND_TAC "L" THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    SUBGOAL_THEN
     `?c:real^2. c IN s /\ ~(c = a) /\ ~(c = b) /\ collinear {a, b, c}`
    (CHOOSE_THEN MP_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:real^2) IN l /\ (b:real^2) IN l` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "l" THEN SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
    MP_TAC(ISPECL [`q:real^2`; `a:real^2`; `b:real^2`; `c:real^2`]
        cases_lemma) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COLLINEAR_AFFINE_HULL; INSERT_SUBSET; EMPTY_SUBSET] THEN
      MAP_EVERY EXISTS_TAC [`a:real^2`; `b:real^2`] THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c:real^2 = q)` ASSUME_TAC THENL
   [ASM_MESON_TAC[BETWEEN_REFL_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `~((p:real^2) IN l)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSEST_POINT_SELF; DIST_EQ_0; REAL_LT_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^2`; `q:real^2`; `b:real^2`; `c:real^2`]
        SYLVESTER_GALLAI_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `~((p:real^2) IN l)` THEN REWRITE_TAC[CONTRAPOS_THM] THEN
      SPEC_TAC(`p:real^2`,`p:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
      EXPAND_TAC "q" THEN ONCE_REWRITE_TAC[ORTHOGONAL_SYM] THEN
      MATCH_MP_TAC CLOSEST_POINT_AFFINE_ORTHOGONAL THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `r:real^2` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`dist(closest_point (affine hull {p,c}) b:real^2,b)`;
      `affine hull {p:real^2,c}`; `b:real^2`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
      REWRITE_TAC[DIST_POS_LE; DIST_EQ_0] THEN
      ASM_SIMP_TAC[CLOSEST_POINT_REFL; CLOSED_AFFINE_HULL;
                   AFFINE_HULL_EQ_EMPTY; NOT_INSERT_EMPTY] THEN
      EXPAND_TAC "L" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `rb < qp ==> cb <= rb ==> ~(qp <= cb)`)) THEN
      MATCH_MP_TAC CLOSEST_POINT_LE THEN
      ASM_REWRITE_TAC[CLOSED_AFFINE_HULL]]]);;
