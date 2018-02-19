(* ========================================================================= *)
(* Half-baked development of Brouwer degree, enough to get some key results  *)
(* about homotopy of linear mappings. This roughly follows the elementary    *)
(* combinatorial construction (going back to Brouwer himself) in Dugundji's  *)
(* "Topology" book. The main differences are that we systematically use      *)
(* conic hulls instead of working on the surface of the sphere, and we       *)
(* keep the notion of orientation localized (see "relative_orientation").    *)
(*                                                                           *)
(*                 (c) Copyright, John Harrison 2014                         *)
(* ========================================================================= *)

needs "Multivariate/polytope.ml";;

(* ------------------------------------------------------------------------- *)
(* Somewhat general lemmas.                                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_1_EXISTS = prove
 (`!s. s HAS_SIZE 1 <=> ?!x. x IN s`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[EXTENSION; IN_SING] THEN MESON_TAC[]);;

let HAS_SIZE_2_EXISTS = prove
 (`!s. s HAS_SIZE 2 <=> ?x y. ~(x = y) /\ !z. z IN s <=> (z = x) \/ (z = y)`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let SIMPLEX_EXTREME_POINTS_NONEMPTY = prove
 (`!c. &(dimindex (:N)) - &1 simplex c ==> ~({v | v extreme_point_of c} = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SIMPLEX_EMPTY]) THEN
    MATCH_MP_TAC(INT_ARITH `&1:int <= d ==> d - &1 = -- &1 ==> F`) THEN
    REWRITE_TAC[INT_OF_NUM_LE; DIMINDEX_GE_1]]);;

(* ------------------------------------------------------------------------- *)
(* Characterizing membership in our simplices via quantifier-free formulas   *)
(* involving determinants.                                                   *)
(* ------------------------------------------------------------------------- *)

let IN_SPAN_DEPLETED_ROWS_QFREE = prove
 (`!A:real^N^N k.
        1 <= k /\ k <= dimindex(:N) /\ ~(det A = &0)
        ==> span {row i A | i IN 1..dimindex(:N) /\ ~(i = k)} =
            {x | det(lambda i. if i = k then x else A$i) = &0}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[DIM_EQ_SPAN; DIM_SPAN; SPAN_EQ_SELF]
   `s SUBSET t /\ subspace t /\ dim t <= dim s ==> span s = t`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_NUMSEG; IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC DET_IDENTICAL_ROWS THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `k:num`] THEN
    ASM_SIMP_TAC[row; LAMBDA_BETA; LAMBDA_ETA];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. det(lambda i. if i = k then x else (A:real^N^N)$i) =
        cofactor(A)$k dot x`
   (fun th -> REWRITE_TAC[th])
  THENL
   [X_GEN_TAC `x:real^N` THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
    MP_TAC(ISPECL [`(lambda i. if i = k then x else (A:real^N^N)$i):real^N^N`;
                   `k:num`] DET_COFACTOR_EXPANSION) THEN
    ASM_SIMP_TAC[dot; LAMBDA_BETA; IN_NUMSEG] THEN
    DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[cofactor; LAMBDA_BETA] THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSPACE_HYPERPLANE] THEN
  MP_TAC(ISPEC `cofactor(A:real^N^N)$k` DIM_HYPERPLANE) THEN
  ANTS_TAC THENL
   [DISCH_TAC THEN MP_TAC(SYM(ISPEC `A:real^N^N` DET_COFACTOR)) THEN
    SUBGOAL_THEN `det(cofactor A:real^N^N) = &0`
     (fun th -> ASM_REWRITE_TAC[th; REAL_POW_EQ_0]) THEN
    MATCH_MP_TAC DET_ZERO_ROW THEN EXISTS_TAC `k:num` THEN
    ASM_SIMP_TAC[row; LAMBDA_BETA; LAMBDA_ETA];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM RANK_EQ_FULL_DET]) THEN
  REWRITE_TAC[RANK_ROW] THEN
  MATCH_MP_TAC(ARITH_RULE `d <= a + 1 ==> d = n ==> n - 1 <= a`) THEN
  TRANS_TAC LE_TRANS
   `dim(row k (A:real^N^N) INSERT
        {row i A | i IN 1..dimindex(:N) /\ ~(i = k)})` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[DIM_INSERT] THEN ARITH_TAC] THEN
  MATCH_MP_TAC DIM_SUBSET THEN REWRITE_TAC[rows; IN_NUMSEG] THEN SET_TAC[]);;

let IN_CONVEX_HULL_ROWS = prove
 (`!A:real^N^N z:real^N.
        z IN convex hull (rows A) <=>
        ?a:real^N. (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= a$i) /\
                   sum (1..dimindex(:N)) (\i. a$i) = &1 /\
                   transp A ** a = z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rows] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[GSYM numseg] THEN
  SIMP_TAC[CONVEX_HULL_FINITE_IMAGE_EXPLICIT; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[MATRIX_MUL_DOT] THEN
  SIMP_TAC[row; IN_NUMSEG; LAMBDA_BETA] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:num->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(lambda i. u i):real^N` THEN
    ASM_SIMP_TAC[LAMBDA_BETA; transp; CART_EQ];
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\i. (v:real^N)$i` THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[CART_EQ]] THEN
  EXPAND_TAC "z" THEN SIMP_TAC[VSUM_COMPONENT] THEN
  SIMP_TAC[VECTOR_MUL_COMPONENT; LAMBDA_BETA; transp; dot] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

let IN_CONIC_CONVEX_HULL_ROWS = prove
 (`!A:real^N^N z:real^N.
        z IN conic hull (convex hull (rows A)) <=>
        ?a:real^N. (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= a$i) /\
                   transp A ** a = z`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[CONIC_HULL_EXPLICIT; IN_CONVEX_HULL_ROWS] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; IN_ELIM_THM; RIGHT_AND_EXISTS_THM] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`; `a:real^N`] THEN
    STRIP_TAC THEN EXISTS_TAC `c % a:real^N` THEN
    ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_LE_MUL] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL];
    X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
    ASM_CASES_TAC `a:real^N = vec 0` THENL
     [MAP_EVERY EXISTS_TAC
       [`&0`; `transp(A:real^N^N) ** basis 1`; `basis 1:real^N`] THEN
      SIMP_TAC[BASIS_COMPONENT; REAL_LE_REFL] THEN
      SIMP_TAC[SUM_DELTA; IN_NUMSEG; LE_REFL; DIMINDEX_GE_1] THEN
      CONJ_TAC THENL [MESON_TAC[REAL_POS]; EXPAND_TAC "z"] THEN
      ASM_MESON_TAC[MATRIX_VECTOR_MUL_RZERO; VECTOR_MUL_LZERO];
      MAP_EVERY EXISTS_TAC
       [`sum (1..dimindex(:N)) (\j. (a:real^N)$j)`;
        `inv(sum (1..dimindex(:N)) (\j. (a:real^N)$j)) % z:real^N`;
        `inv(sum (1..dimindex(:N)) (\j. a$j)) % a:real^N`] THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL] THEN
      REWRITE_TAC[VECTOR_MUL_COMPONENT; SUM_LMUL] THEN
      ASM_SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_LE_MUL; REAL_LE_INV_EQ] THEN
      REWRITE_TAC[VECTOR_ARITH
       `z:real^N = a % b % z <=> (b * a - &1) % z = vec 0`] THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_SUB_0] THEN
      MATCH_MP_TAC(TAUT `p ==> p /\ (p \/ q)`) THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN DISCH_THEN(MP_TAC o MATCH_MP
       (ONCE_REWRITE_RULE[IMP_CONJ_ALT] SUM_POS_EQ_0_NUMSEG)) THEN
      UNDISCH_TAC `~(a:real^N = vec 0)` THEN
      ASM_SIMP_TAC[CART_EQ; VEC_COMPONENT]]]);;

let IN_CONIC_CONVEX_HULL_ROWS_QFREE = prove
 (`!A:real^N^N z:real^N.
        ~(det A = &0)
        ==> (z IN conic hull (convex hull (rows A)) <=>
             !k. 1 <= k /\ k <= dimindex(:N)
                 ==> det(lambda i. if i = k then z else A$i) / det(A) >= &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_CONIC_CONVEX_HULL_ROWS] THEN
  ASM_SIMP_TAC[DET_TRANSP; CRAMER] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM2] THEN
  SIMP_TAC[LAMBDA_BETA] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o RAND_CONV o RAND_CONV o LAND_CONV)
   [GSYM DET_TRANSP] THEN
  SIMP_TAC[transp; LAMBDA_BETA; real_ge] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `k:num` THEN
  ASM_CASES_TAC `1 <= k /\ k <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN ASM_MESON_TAC[]);;

let IN_INTERIOR_CONIC_CONVEX_HULL_ROWS_QFREE = prove
 (`!A:real^N^N z:real^N.
        z IN interior(conic hull (convex hull (rows A))) <=>
        ~(det A = &0) /\
        (!k. 1 <= k /\ k <= dimindex(:N)
             ==> det(lambda i. if i = k then z else A$i) / det(A) > &0)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `det(A:real^N^N) = &0` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE `s = {} ==> ~(x IN s)`) THEN
    MATCH_MP_TAC EMPTY_INTERIOR_LOWDIM THEN
    REWRITE_TAC[DIM_CONIC_HULL; DIM_CONVEX_HULL; GSYM RANK_ROW] THEN
    ASM_REWRITE_TAC[GSYM DET_EQ_0_RANK];
    ASM_REWRITE_TAC[REAL_ARITH `x > &0 <=> x >= &0 /\ ~(x = &0)`]] THEN
  SUBGOAL_THEN
   `~(vec 0 IN affine hull (rows(A:real^N^N))) /\ ~(affine_dependent(rows A))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[DEPENDENT_AFFINE_DEPENDENT_CASES; DET_DEPENDENT_ROWS];
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE
   `(!k. P k ==> Q k /\ R k) <=> (!k. P k ==> Q k) /\ (!k. P k ==> R k)`] THEN
  ASM_SIMP_TAC[GSYM IN_CONIC_CONVEX_HULL_ROWS_QFREE; REAL_DIV_EQ_0] THEN
  ASM_CASES_TAC `z IN conic hull (convex hull (rows(A:real^N^N)))` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET]] THEN
  MATCH_MP_TAC(SET_RULE
   `(~(z IN s) <=> z IN {a | ?k. ~(P k ==> ~(a IN {z | Q k z}))})
    ==> (z IN s <=> (!k. P k ==> ~Q k z))`) THEN
  ASM_SIMP_TAC[GSYM IN_SPAN_DEPLETED_ROWS_QFREE] THEN
  REWRITE_TAC[NOT_IMP; IN_ELIM_THM] THEN EQ_TAC THENL
   [ASM_REWRITE_TAC[GSYM SET_DIFF_FRONTIER; IN_DIFF] THEN
    ASM_SIMP_TAC[FRONTIER_OF_CONVEX_CLOSED; CONVEX_CONIC_HULL; FINITE_ROWS;
      CONVEX_CONVEX_HULL; CLOSED_CONIC_HULL_STRONG; POLYTOPE_CONVEX_HULL] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        FACE_OF_CONIC_HULL_REV)) THEN
    ASM_REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [ASM_MESON_TAC[IN_SING; SPAN_0; LE_REFL; DIMINDEX_GE_1]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST_ALL_TAC o SYM))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        FACE_OF_CONVEX_HULL_SUBSET)) THEN
    SIMP_TAC[FINITE_IMP_COMPACT; FINITE_ROWS; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `r:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> s = t \/ ?x. x IN t /\ s SUBSET t DELETE x`)) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM
       (MP_TAC o GEN_REWRITE_RULE LAND_CONV [AFF_DIM_CONIC_HULL_DIM]) THEN
      REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; ROWS_NONEMPTY; DIM_CONVEX_HULL] THEN
      ASM_MESON_TAC[INT_LT_REFL; RANK_ROW; RANK_EQ_FULL_DET];
      REWRITE_TAC[rows; EXISTS_IN_GSPEC] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG] THEN
      ONCE_REWRITE_TAC[GSYM SPAN_CONVEX_HULL] THEN
      ONCE_REWRITE_TAC[GSYM SPAN_CONIC_HULL] THEN
      MATCH_MP_TAC SPAN_SUPERSET THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (SET_RULE `z IN s ==> s SUBSET t ==> z IN t`)) THEN
      REPEAT(MATCH_MP_TAC HULL_MONO) THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP(REWRITE_RULE[SUBSET]
     INTERIOR_SUBSET_RELATIVE_INTERIOR)) THEN
    ASM_CASES_TAC `z:real^N = vec 0` THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_CONIC_HULL; IN_DELETE;
                    AFFINE_HULL_CONVEX_HULL];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!s. z IN s /\ s INTER t = {} ==> z IN t ==> F`) THEN
    EXISTS_TAC `affine hull (conic hull(convex hull
        {row i (A:real^N^N) | i IN 1..dimindex (:N) /\ ~(i = k)}))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[AFFINE_HULL_CONIC_HULL; GSYM SPAN_AFFINE_HULL_INSERT] THEN
      REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; SPAN_CONVEX_HULL] THEN
      ASM_MESON_TAC[SPAN_EMPTY; IN_SING];
      MATCH_MP_TAC AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR THEN
      SIMP_TAC[CONVEX_CONIC_HULL; CONVEX_CONVEX_HULL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FACE_OF_CONIC_HULL THEN
        ASM_REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN
        ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN EXISTS_TAC
          `{row i (A:real^N^N) | i IN 1..dimindex (:N) /\ ~(i = k)}` THEN
        REWRITE_TAC[rows; IN_NUMSEG] THEN SET_TAC[];
        DISCH_THEN(MP_TAC o AP_TERM `dim:(real^N->bool)->num`) THEN
        REWRITE_TAC[DIM_CONIC_HULL; DIM_CONVEX_HULL] THEN
        MATCH_MP_TAC(ARITH_RULE
         `d = dimindex(:N) /\ s < dimindex(:N) ==> ~(s = d)`) THEN CONJ_TAC
        THENL [ASM_MESON_TAC[RANK_EQ_FULL_DET; RANK_ROW]; ALL_TAC] THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[GSYM DELETE] THEN
        MAP_EVERY (fun th ->
          W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd) THEN
          SIMP_TAC[FINITE_IMAGE; FINITE_DELETE; FINITE_NUMSEG] THEN
          MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS))
         [DIM_LE_CARD; CARD_IMAGE_LE] THEN
        ASM_SIMP_TAC[CARD_DELETE; CARD_NUMSEG_1; FINITE_NUMSEG; IN_NUMSEG] THEN
        SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> n - 1 < n`]]]]);;

(* ------------------------------------------------------------------------- *)
(* Apply a function row-wise.                                                *)
(* ------------------------------------------------------------------------- *)

let maprows = new_definition
 `maprows f (d:real^N^N) = ((lambda i. f(d$i)):real^N^N)`;;

let DET_MAPROWS_LINEAR = prove
 (`!f:real^N->real^N d. linear f ==> det(maprows f d) = det(matrix f) * det d`,
  SIMP_TAC[maprows; DET_LINEAR_ROWS]);;

let ROW_MAPROWS = prove
 (`!A:real^N^N i.
    1 <= i /\ i <= dimindex(:N) ==> row i (maprows f A) = f(row i A)`,
  SIMP_TAC[row; maprows; LAMBDA_BETA; LAMBDA_ETA]);;

let ROWS_MAPROWS = prove
 (`!f:real^N->real^N A:real^N^N. rows(maprows f A) = IMAGE f (rows A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rows; maprows; row] THEN
  REWRITE_TAC[SET_RULE `IMAGE f {g x | P x} = {f(g x) | P x}`] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. P x ==> f x = g x) ==> {f x | P x} = {g x | P x}`) THEN
  SIMP_TAC[LAMBDA_BETA; CART_EQ; LAMBDA_ETA]);;

let MAPROWS_COMPOSE = prove
 (`!f:real^N->real^N g:real^N->real^N.
        maprows (f o g) = maprows f o maprows g`,
  REWRITE_TAC[FUN_EQ_THM; maprows; CART_EQ; o_THM] THEN
  SIMP_TAC[LAMBDA_BETA]);;

(* ------------------------------------------------------------------------- *)
(* Relative orientation of a simplex under a function.                       *)
(* ------------------------------------------------------------------------- *)

let relative_orientation = new_definition
 `relative_orientation (f:real^N->real^N) s =
        let A = @A. rows A = {v | v extreme_point_of s} in
        real_sgn(det(maprows f A) / det A)`;;

let FINITE_SET_AS_MATRIX_ROWS = prove
 (`!s. FINITE s /\ ~(s = {}) /\ CARD s <= dimindex(:N)
       ==> ?A:real^N^N. rows A = s`,
  GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
  ASM_SIMP_TAC[GSYM CARD_LE_CARD; FINITE_NUMSEG; LE_C_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->real^N` (SUBST1_TAC o SYM)) THEN
  EXISTS_TAC `(lambda i. f i):real^N^N` THEN
  ASM_REWRITE_TAC[rows; GSYM IN_NUMSEG; SIMPLE_IMAGE] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
  SIMP_TAC[row; LAMBDA_BETA; IN_NUMSEG; LAMBDA_ETA]);;

let SIMPLEX_ORDERING_EXISTS = prove
 (`!s:real^N->bool.
        (&(dimindex(:N)) - &1) simplex s
        ==> ?A:real^N^N. rows A = {v | v extreme_point_of s}`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[SIMPLEX_EMPTY; INT_ARITH `&1:int <= n ==> ~(n - &1 = -- &1)`;
               INT_OF_NUM_LE; DIMINDEX_GE_1] THEN
  REWRITE_TAC[SIMPLEX_ALT1; HAS_SIZE] THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SET_AS_MATRIX_ROWS THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; LE_REFL] THEN
  ASM_MESON_TAC[EXTREME_POINT_EXISTS_CONVEX]);;

let DET_ORDERED_SIMPLEX_EQ_0 = prove
 (`!s:real^N->bool A.
        convex s /\ compact s /\ rows A = {v | v extreme_point_of s}
        ==> (det A = &0 <=>
             ~((&(dimindex(:N)) - &1) simplex s) \/ vec 0 IN affine hull s)`,
  SIMP_TAC[SIMPLEX_0_NOT_IN_AFFINE_HULL;
           TAUT `~p \/ q <=> ~(p /\ ~q)`] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[DET_EQ_0_RANK; RANK_ROW; independent] THEN
  REWRITE_TAC[DEPENDENT_EQ_DIM_LT_CARD; HAS_SIZE; FINITE_ROWS] THEN
  MP_TAC(ISPEC `A:real^N^N` CARD_ROWS_LE) THEN
  MP_TAC(ISPEC `rows(A:real^N^N)` DIM_LE_CARD) THEN
  SIMP_TAC[FINITE_ROWS] THEN ARITH_TAC);;

let DET_ORDERED_SIMPLEX_NZ = prove
 (`!s:real^N->bool A.
        (&(dimindex(:N)) - &1) simplex s /\
        ~(vec 0 IN affine hull s) /\
        rows A = {v | v extreme_point_of s}
        ==> ~(det A = &0)`,
  MESON_TAC[DET_ORDERED_SIMPLEX_EQ_0; SIMPLEX_IMP_COMPACT;
            SIMPLEX_IMP_CONVEX]);;

let RELATIVE_ORIENTATION = prove
 (`!A:real^N^N f s:real^N->bool.
        rows A = {v | v extreme_point_of s}
        ==> relative_orientation (f:real^N->real^N) s =
            real_sgn(det(maprows f A) / det A)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[relative_orientation] THEN
  ABBREV_TAC `B = @A:real^N^N. rows A = {v | v extreme_point_of s}` THEN
  SUBGOAL_THEN `rows(B:real^N^N) = rows(A:real^N^N)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\i. row i (B:real^N^N)`; `1..dimindex(:N)`]
        CARD_IMAGE_EQ_INJ) THEN
  MP_TAC(ISPECL [`\i. row i (A:real^N^N)`; `1..dimindex(:N)`]
        CARD_IMAGE_EQ_INJ) THEN
  REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1; GSYM SIMPLE_IMAGE] THEN
  REWRITE_TAC[REWRITE_RULE[GSYM IN_NUMSEG] (GSYM rows)] THEN
  ASM_CASES_TAC `CARD(rows(A:real^N^N)) = dimindex(:N)` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    MATCH_MP_TAC(MESON[]
     `(q ==> x = &0) /\ (p ==> y = &0) ==> p ==> q ==> x = y`) THEN
    CONJ_TAC THEN REWRITE_TAC[REAL_SGN_EQ; REAL_DIV_EQ_0] THEN
    DISCH_THEN(fun th -> DISJ2_TAC THEN MP_TAC th) THEN
    REWRITE_TAC[IN_NUMSEG] THEN MESON_TAC[DET_IDENTICAL_ROWS]] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN ASSUME_TAC th THEN MP_TAC th) THEN
  MP_TAC(ISPECL
   [`1..dimindex(:N)`; `rows(B:real^N^N)`; `\i. row i (A:real^N^N)`]
        SURJECTIVE_IFF_INJECTIVE_GEN) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_ROWS; FINITE_NUMSEG; CARD_NUMSEG_1] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; rows; row; FORALL_IN_GSPEC] THEN
    SIMP_TAC[IN_ELIM_THM; IN_NUMSEG; LAMBDA_ETA] THEN MESON_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[rows; FORALL_IN_GSPEC] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?p. p permutes 1..dimindex(:N) /\
        !i. i IN 1..dimindex(:N)
            ==> row (p i) (A:real^N^N) = row i (B:real^N^N)`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[PERMUTES_FINITE_INJECTIVE; FINITE_NUMSEG] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV
       [RIGHT_IMP_EXISTS_THM]) THEN
    REWRITE_TAC[SKOLEM_THM; GSYM IN_NUMSEG] THEN
    DISCH_THEN(X_CHOOSE_TAC `p:num->num`) THEN
    EXISTS_TAC `\i. if i IN 1..dimindex(:N) then p i else i` THEN
    SIMP_TAC[] THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`maprows (f:real^N->real^N) A`; `p:num->num`]
      DET_PERMUTE_ROWS) THEN
    MP_TAC(ISPECL [`A:real^N^N`; `p:num->num`] DET_PERMUTE_ROWS) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(DISCH_THEN(MP_TAC o MATCH_MP (REAL_RING
       `x = p * y ==> p * p = &1 ==> y = p * x`)) THEN
      REWRITE_TAC[SIGN_IDEMPOTENT] THEN DISCH_THEN SUBST1_TAC) THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[REAL_SGN_MUL; real_div; REAL_INV_MUL; REAL_SGN_SIGN] THEN
    SIMP_TAC[SIGN_IDEMPOTENT; REAL_FIELD
     `p * p = &1 ==> (p * x) * (inv p * y) = x * y`] THEN
    REWRITE_TAC[GSYM real_div] THEN BINOP_TAC THEN AP_TERM_TAC THEN
    RULE_ASSUM_TAC(SIMP_RULE[row; IN_NUMSEG; LAMBDA_ETA]) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP PERMUTES_IMAGE) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `IMAGE p s = s ==> !x. x IN s ==> p x IN s`)) THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; maprows; IN_NUMSEG] THEN
    ASM_MESON_TAC[]]);;

let RELATIVE_ORIENTATION_LINEAR = prove
 (`!f:real^N->real^N c.
      linear f /\
      (&(dimindex(:N)) - &1) simplex c /\ ~(vec 0 IN affine hull c)
      ==> relative_orientation f c = real_sgn(det(matrix f))`,
  SIMP_TAC[relative_orientation; DET_MAPROWS_LINEAR] THEN
  REPEAT STRIP_TAC THEN LET_TAC THEN
  SUBGOAL_THEN `rows(A:real^N^N) = {v | v extreme_point_of c}` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_ORDERING_EXISTS]; AP_TERM_TAC] THEN
  SUBGOAL_THEN `~(det(A:real^N^N) = &0)` MP_TAC THENL
   [ASM_MESON_TAC[DET_ORDERED_SIMPLEX_NZ]; CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Apply a function to the vertices of a simplex to get a new cell.          *)
(* ------------------------------------------------------------------------- *)

let vertex_image = new_definition
 `vertex_image (f:real^N->real^N) s =
     convex hull (IMAGE f {v | v extreme_point_of s})`;;

let VERTEX_IMAGE_LINEAR_GEN = prove
 (`!f:real^N->real^N s.
        linear f /\ convex s /\ compact s
        ==> vertex_image f s = IMAGE f s`,
  SIMP_TAC[vertex_image; CONVEX_HULL_LINEAR_IMAGE;
           GSYM KREIN_MILMAN_MINKOWSKI]);;

let VERTEX_IMAGE_LINEAR_POLYTOPE = prove
 (`!f:real^N->real^N p.
        linear f /\ polytope p ==> vertex_image f p = IMAGE f p`,
  SIMP_TAC[VERTEX_IMAGE_LINEAR_GEN; POLYTOPE_IMP_COMPACT;
           POLYTOPE_IMP_CONVEX]);;

let VERTEX_IMAGE_LINEAR = prove
 (`!f:real^N->real^N s.
        linear f /\ &(dimindex(:N)) - &1 simplex s
        ==> vertex_image f s = IMAGE f s`,
  MESON_TAC[VERTEX_IMAGE_LINEAR_POLYTOPE; SIMPLEX_IMP_POLYTOPE]);;

let CONIC_HULL_VERTEX_IMAGE_LINEAR = prove
 (`!f:real^N->real^N c.
        linear f /\ &(dimindex(:N)) - &1 simplex c
        ==> conic hull (vertex_image f c) =
            IMAGE f (conic hull c)`,
  SIMP_TAC[VERTEX_IMAGE_LINEAR; CONIC_HULL_LINEAR_IMAGE]);;

let DET_ORDERED_SIMPLEX_EQ_0_GEN = prove
 (`!f:real^N->real^N s A.
        polytope s /\ rows A = {v | v extreme_point_of s}
        ==> (det(maprows f A) = &0 <=>
             ~((&(dimindex(:N)) - &1) simplex (vertex_image f s)) \/
             vec 0 IN affine hull (vertex_image f s))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_POLYHEDRON_EXTREME_POINTS o MATCH_MP
        POLYTOPE_IMP_POLYHEDRON) THEN
  REWRITE_TAC[DET_EQ_0_RANK; RANK_ROW; ROWS_MAPROWS] THEN
  ASM_REWRITE_TAC[vertex_image; AFFINE_HULL_CONVEX_HULL] THEN
  ASM_CASES_TAC
   `CARD(IMAGE (f:real^N->real^N) {v | v extreme_point_of s}) < dimindex(:N)`
  THENL
   [MATCH_MP_TAC(TAUT `p /\ (~r ==> ~q) ==> (p <=> ~q \/ r)`) THEN
    CONJ_TAC THENL
     [ALL_TAC;
      DISCH_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
      ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_DIM] THEN
      MATCH_MP_TAC(INT_ARITH `x:int < y ==> ~(x - &1 = y - &1)`) THEN
      REWRITE_TAC[INT_OF_NUM_LT]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      LET_TRANS)) THEN
    ASM_SIMP_TAC[DIM_LE_CARD; FINITE_IMAGE];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `~(c:num < n) ==> c <= n ==> c = n`)) THEN
    ANTS_TAC THENL
     [TRANS_TAC LE_TRANS `CARD(rows(A:real^N^N))` THEN
      REWRITE_TAC[CARD_ROWS_LE] THEN
      ASM_SIMP_TAC[CARD_IMAGE_LE];
      DISCH_TAC]] THEN
  TRANS_TAC EQ_TRANS
   `dependent(IMAGE (f:real^N->real^N) {v | v extreme_point_of s})` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[DEPENDENT_EQ_DIM_LT_CARD; FINITE_IMAGE];
    REWRITE_TAC[DEPENDENT_AFFINE_DEPENDENT_CASES]] THEN
  ASM_CASES_TAC
   `vec 0 IN
    affine hull IMAGE (f:real^N->real^N) {v | v extreme_point_of s}` THEN
  ASM_REWRITE_TAC[TAUT `(p <=> ~q) <=> (~p <=> q)`] THEN
  EQ_TAC THEN ASM_SIMP_TAC[SIMPLEX_CONVEX_HULL; INT_SUB_ADD] THEN
  DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_IFF_CARD; AFF_DIM_CONVEX_HULL;
               FINITE_IMAGE]);;

let VERTEX_IMAGE_NONEMPTY = prove
 (`!f c. &(dimindex (:N)) - &1 simplex c ==> ~(vertex_image f c = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[vertex_image; CONVEX_HULL_EQ_EMPTY; IMAGE_EQ_EMPTY] THEN
  ASM_SIMP_TAC[SIMPLEX_EXTREME_POINTS_NONEMPTY]);;

let POLYTOPE_VERTEX_IMAGE = prove
 (`!f c. &(dimindex (:N)) - &1 simplex c ==> polytope(vertex_image f c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vertex_image] THEN
  MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMAGE THEN
  ASM_MESON_TAC[FINITE_POLYHEDRON_EXTREME_POINTS; SIMPLEX_IMP_POLYHEDRON]);;

let POLYHEDRON_CONIC_HULL_VERTEX_IMAGE = prove
 (`!f c. &(dimindex (:N)) - &1 simplex c
         ==> polyhedron(conic hull (vertex_image f c))`,
  SIMP_TAC[POLYHEDRON_CONIC_HULL_POLYTOPE; POLYTOPE_VERTEX_IMAGE]);;

let CLOSED_CONIC_HULL_VERTEX_IMAGE = prove
 (`!f c. &(dimindex (:N)) - &1 simplex c
         ==> closed(conic hull (vertex_image f c))`,
  SIMP_TAC[POLYHEDRON_CONIC_HULL_VERTEX_IMAGE; POLYHEDRON_IMP_CLOSED]);;

let CONVEX_CONIC_HULL_VERTEX_IMAGE = prove
 (`!f c. &(dimindex (:N)) - &1 simplex c
         ==> convex(conic hull (vertex_image f c))`,
  SIMP_TAC[POLYHEDRON_CONIC_HULL_VERTEX_IMAGE; POLYHEDRON_IMP_CONVEX]);;

let RELATIVE_ORIENTATION_NONZERO = prove
 (`!f:real^N->real^N s.
    (&(dimindex(:N)) - &1) simplex s
    ==> (~(relative_orientation f s = &0) <=>
         (&(dimindex(:N)) - &1) simplex (vertex_image f s) /\
         ~(vec 0 IN affine hull s) /\
         ~(vec 0 IN affine hull (vertex_image f s)))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (X_CHOOSE_TAC `A:real^N^N`  o MATCH_MP SIMPLEX_ORDERING_EXISTS) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RELATIVE_ORIENTATION th]) THEN
  REWRITE_TAC[REAL_SGN_EQ; REAL_DIV_EQ_0; DE_MORGAN_THM] THEN
  ASM_MESON_TAC[DET_ORDERED_SIMPLEX_EQ_0_GEN; DET_ORDERED_SIMPLEX_EQ_0;
    SIMPLEX_IMP_POLYTOPE; SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX]);;

let RELATIVE_ORIENTATION_COMPOSE = prove
 (`!f:real^N->real^N g:real^N->real^N c.
        &(dimindex(:N)) - &1 simplex c /\
        ~(relative_orientation f c = &0)
        ==> relative_orientation (g o f) c =
            relative_orientation g (vertex_image f c) *
            relative_orientation f c`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SIMPLEX_ORDERING_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_TAC `A:real^N^N`) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RELATIVE_ORIENTATION th]) THEN
  REWRITE_TAC[REAL_SGN_EQ; REAL_DIV_EQ_0; DE_MORGAN_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`maprows (f:real^N->real^N) A`; `g:real^N->real^N`;
                 `vertex_image (f:real^N->real^N) c`]
        RELATIVE_ORIENTATION) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ROWS_MAPROWS; vertex_image] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT THEN
    REWRITE_TAC[GSYM ROWS_MAPROWS] THEN
    DISCH_THEN(MP_TAC o MATCH_MP AFFINE_DEPENDENT_IMP_DEPENDENT) THEN
    ASM_MESON_TAC[DET_DEPENDENT_ROWS];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MAPROWS_COMPOSE; o_THM; GSYM REAL_SGN_MUL] THEN
  AP_TERM_TAC THEN REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_neg o concl))) THEN
  CONV_TAC REAL_FIELD);;

let ANY_IN_CONIC_HULL_SIMPLEX = prove
 (`!u t. convex u /\ bounded u /\ vec 0 IN interior u /\ UNIONS t = frontier u
         ==> !w:real^N. ?c. c IN t /\ w IN conic hull c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w:real^N. ~(w = vec 0) ==> ?c. c IN t /\ w IN conic hull c`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(fun th -> X_GEN_TAC `w:real^N` THEN MP_TAC th) THEN
    ASM_CASES_TAC `w:real^N = vec 0` THEN ASM_SIMP_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `basis 1:real^N`) THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[CONIC_HULL_CONTAINS_0] THEN
    X_GEN_TAC `c:real^N->bool` THEN
    ASM_CASES_TAC `c:real^N->bool = {}` THEN
    ASM_SIMP_TAC[CONIC_HULL_EMPTY; NOT_IN_EMPTY]] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `vec 0:real^N`; `w:real^N`]
      RAY_TO_FRONTIER) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(d % w:real^N) IN UNIONS t` MP_TAC THENL
   [ASM_MESON_TAC[]; REWRITE_TAC[IN_UNIONS]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `w:real^N = inv(d) % d % w` SUBST1_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
   MATCH_MP_TAC(REWRITE_RULE[conic] CONIC_CONIC_HULL) THEN
   ASM_SIMP_TAC[REAL_LE_INV_EQ; HULL_INC; REAL_LT_IMP_LE]);;

let NONBOUNDARY_IN_UNIQUE_CONIC_HULL_SIMPLEX = prove
 (`!u t w:real^N.
        convex u /\ bounded u /\ vec 0 IN interior u /\
        triangulation t /\ UNIONS t = frontier u /\
        (!c. c IN t ==> ~(w IN frontier(conic hull c)))
        ==> ?!c. c IN t /\ w IN conic hull c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_DEF] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[ANY_IN_CONIC_HULL_SIMPLEX]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N->bool`; `d:real^N->bool`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `c:real^N->bool = d` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th ->
  MP_TAC(SPEC `d:real^N->bool` th) THEN MP_TAC(SPEC `c:real^N->bool` th)) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[frontier; IN_DIFF; REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`relative_interior c:real^N->bool`;
                 `relative_interior d:real^N->bool`; `u:real^N->bool`]
        INTER_CONIC_HULL_SUBSETS_CONVEX_RELATIVE_FRONTIER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REWRITE_RULE[SUBSET] INTERIOR_SUBSET_RELATIVE_INTERIOR] THEN
    MP_TAC(ISPEC `u:real^N->bool` RELATIVE_FRONTIER_NONEMPTY_INTERIOR) THEN
    MP_TAC(ISPEC `c:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `d:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC(SET_RULE `!a. a IN s /\ ~(a IN t) ==> s = t ==> F`)] THEN
  EXISTS_TAC `w:real^N` THEN
  SUBGOAL_THEN
   `~((vec 0:real^N) IN affine hull c) /\ ~((vec 0:real^N) IN affine hull d)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NOT_IN_AFFINE_HULL_SURFACE_TRIANGULATION; SUBSET_REFL];
    ASM_SIMP_TAC[CONIC_HULL_RELATIVE_INTERIOR]] THEN
  ASM_CASES_TAC `relative_interior c:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[CONIC_HULL_EMPTY; NOT_IN_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY;
                  triangulation; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  ASM_CASES_TAC `relative_interior d:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[CONIC_HULL_EMPTY; NOT_IN_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY;
                  triangulation; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[IN_INSERT; IN_INTER;
               REWRITE_RULE[SUBSET] INTERIOR_SUBSET_RELATIVE_INTERIOR] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `c:real^N->bool`; `d:real^N->bool`]
        TRIANGULATION_DISJOINT_RELATIVE_INTERIORS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_SING] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPEC `c:real^N->bool` RELATIVE_INTERIOR_CONIC_HULL_0) THEN ANTS_TAC
  THENL [ASM_MESON_TAC[triangulation; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  ASM_SIMP_TAC[REWRITE_RULE[SUBSET] INTERIOR_SUBSET_RELATIVE_INTERIOR] THEN
  ASM_MESON_TAC[HULL_INC; SUBSET; RELATIVE_INTERIOR_SUBSET]);;

let CLOSURE_CONIC_HULL_VERTEX_IMAGE_NONFRONTIERS = prove
 (`!f t.
    FINITE t /\ (!c. c IN t ==> &(dimindex (:N)) - &1 simplex c)
    ==> closure {x | !c. c IN t
                         ==> ~(x IN frontier(conic hull vertex_image f c))} =
        (:real^N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERIOR_COMPLEMENT;
   SET_RULE `s = UNIV <=> UNIV DIFF s = {}`;
   SET_RULE `UNIV DIFF {x | !c. c IN t ==> ~(x IN f c)} =
             UNIONS {f c | c IN t}`] THEN
  MATCH_MP_TAC NOWHERE_DENSE_COUNTABLE_UNIONS_CLOSED THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMP_COUNTABLE; COUNTABLE_IMAGE] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; FRONTIER_CLOSED; INTERIOR_FRONTIER_EMPTY;
               CLOSED_CONIC_HULL_VERTEX_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Triply parametrized degree: counting point, triangulation and function    *)
(* ------------------------------------------------------------------------- *)

let brouwer_degree3 = new_definition
 `(brouwer_degree3:real^N#((real^N->bool)->bool)#(real^N->real^N)->real)
    (y,t,f) =
  sum {c | c IN t /\ y IN conic hull (vertex_image f c)}
      (\c. relative_orientation f c)`;;

(* ------------------------------------------------------------------------- *)
(* Invariance under perturbation of the function.                            *)
(* ------------------------------------------------------------------------- *)

let BROUWER_DEGREE3_PERTURB = prove
 (`!f:real^N->real^N t x.
    FINITE t /\
    (!c. c IN t ==> &(dimindex(:N)) - &1 simplex c) /\
    (!c. c IN t ==> ~(vec 0 IN vertex_image f c)) /\
    (!c. c IN t ==> ~(x IN frontier(conic hull (vertex_image f c))))
    ==> ?e. &0 < e /\
            !g. (!c v. c IN t /\ v extreme_point_of c ==> norm(f v - g v) < e)
                ==> brouwer_degree3(x,t,g) = brouwer_degree3(x,t,f) /\
                    (!c. c IN t
                         ==> ~(x IN frontier(conic hull (vertex_image g c))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[brouwer_degree3] THEN
  ONCE_REWRITE_TAC[SUM_RESTRICT_SET] THEN REWRITE_TAC[ETA_AX] THEN
  SUBGOAL_THEN
   `!c. c IN t
        ==> ?e. &0 < e /\
                !g. (!v. v extreme_point_of c ==> norm (f v - g v) < e)
                    ==> ~(x IN frontier (conic hull vertex_image g c)) /\
                        (if x IN conic hull vertex_image (g:real^N->real^N) c
                         then relative_orientation g c else &0) =
                        (if x IN conic hull vertex_image f c
                         then relative_orientation f c else &0)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `x:real^N = vec 0` THENL
     [UNDISCH_TAC
       `~(x IN frontier (conic hull vertex_image (f:real^N->real^N) c))` THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      ASM_REWRITE_TAC[frontier; IN_DIFF] THEN
      ASM_SIMP_TAC[CLOSED_CONIC_HULL_VERTEX_IMAGE; CLOSURE_CLOSED] THEN
      ASM_SIMP_TAC[CONIC_HULL_CONTAINS_0; VERTEX_IMAGE_NONEMPTY] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
        INTERIOR_SUBSET_RELATIVE_INTERIOR)) THEN
      ASM_SIMP_TAC[RELATIVE_INTERIOR_CONIC_HULL_0; POLYTOPE_VERTEX_IMAGE;
                   POLYTOPE_IMP_CONVEX] THEN
      ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
      ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP SIMPLEX_IMP_POLYHEDRON) THEN
    MP_TAC(ISPECL [`vertex_image (f:real^N->real^N) c`; `x:real^N`]
        HAUSDIST_STILL_SAME_PLACE_CONIC_HULL_STRONG) THEN
    ASM_SIMP_TAC[POLYTOPE_VERTEX_IMAGE; POLYTOPE_IMP_BOUNDED;
                 POLYTOPE_IMP_CONVEX; CLOSURE_CLOSED; POLYTOPE_IMP_CLOSED;
                 VERTEX_IMAGE_NONEMPTY] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?e. &0 < e /\
          !g. (!v. v extreme_point_of c ==> norm (f v - g v) < e) /\
              x IN conic hull vertex_image (f:real^N->real^N) c
              ==> relative_orientation g c = relative_orientation f c`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `x IN conic hull vertex_image (f:real^N->real^N) c` THENL
       [ALL_TAC; ASM_MESON_TAC[REAL_LT_01]] THEN
      SUBGOAL_THEN
       `x IN interior(conic hull vertex_image (f:real^N->real^N) c)`
      MP_TAC THENL
       [ASM_SIMP_TAC[GSYM SET_DIFF_FRONTIER; IN_DIFF]; ALL_TAC] THEN
      MP_TAC(ISPEC `c:real^N->bool` SIMPLEX_ORDERING_EXISTS) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `A:real^N^N`) THEN
      REWRITE_TAC[vertex_image] THEN FIRST_ASSUM(fun th ->
        ONCE_REWRITE_TAC [MATCH_MP RELATIVE_ORIENTATION th] THEN
        REWRITE_TAC[SYM th]) THEN
      REWRITE_TAC[GSYM ROWS_MAPROWS] THEN
      REWRITE_TAC[IN_INTERIOR_CONIC_CONVEX_HULL_ROWS_QFREE] THEN
      DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
      REWRITE_TAC[REAL_SGN_DIV] THEN
      MP_TAC(ISPECL [`maprows (f:real^N->real^N) A`;
                     `abs(det(maprows (f:real^N->real^N) A))`]
        CONTINUOUS_DET_EXPLICIT) THEN
      ASM_REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `g:real^N->real^N` THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `maprows (g:real^N->real^N) A`) THEN
      ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC] THEN
      SIMP_TAC[maprows; LAMBDA_BETA; GSYM VECTOR_SUB_COMPONENT] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
         `abs(x$i) <= norm x /\ norm x < d ==> abs((x:real^N)$i) < d`) THEN
      REWRITE_TAC[COMPONENT_LE_NORM] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[rows; row; LAMBDA_ETA]) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `min (d / &2) e:real` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; REAL_HALF] THEN
    X_GEN_TAC `g:real^N->real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vertex_image (g:real^N->real^N) c`) THEN
    ASM_SIMP_TAC[POLYTOPE_VERTEX_IMAGE; POLYTOPE_IMP_BOUNDED;
                 POLYTOPE_IMP_CONVEX; VERTEX_IMAGE_NONEMPTY] THEN
    ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[vertex_image] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) HAUSDIST_CONVEX_HULLS o
      lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_IMP_BOUNDED; FINITE_IMAGE;
                 FINITE_POLYHEDRON_EXTREME_POINTS] THEN
    MATCH_MP_TAC(REAL_ARITH
      `&0 < d /\ y <= d / &2 ==> x <= y ==> x < d`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_HAUSDIST_LE THEN
    ASM_SIMP_TAC[SIMPLEX_EXTREME_POINTS_NONEMPTY; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    TRANS_TAC REAL_LE_TRANS `norm((f:real^N->real^N) v - g v)` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[GSYM dist; GSYM SETDIST_SINGS] THENL
     [ALL_TAC; GEN_REWRITE_TAC RAND_CONV [SETDIST_SYM]] THEN
    MATCH_MP_TAC SETDIST_SUBSET_RIGHT THEN ASM SET_TAC[];
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `e:(real^N->bool)->real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `t:(real^N->bool)->bool = {}` THENL
     [ASM_REWRITE_TAC[SUM_CLAUSES; NOT_IN_EMPTY] THEN MESON_TAC[REAL_LT_01];
      ALL_TAC] THEN
    EXISTS_TAC `inf(IMAGE (e:(real^N->bool)->real) t)` THEN
    ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `g:real^N->real^N` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g:real^N->real^N`) THEN
    ASM_MESON_TAC[]]);;

let ORIENTING_PERTURBATION_EXISTS = prove
 (`!f:real^N->real^N t e.
        FINITE t /\
        (!c. c IN t ==> &(dimindex(:N)) - &1 simplex c) /\
        (!c. c IN t ==> ~(vec 0 IN affine hull c)) /\
        &0 < e
        ==> ?g. (!c v. c IN t /\ v extreme_point_of c ==> dist(f v,g v) < e) /\
                !c. c IN t ==> ~(relative_orientation g c = &0)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  SUBGOAL_THEN `bounded(UNIONS t:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC BOUNDED_UNIONS THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_BOUNDED];
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `!c:real^N->bool.
        c IN t
        ==> ?d. &0 < d /\
                !a. ~(a = &0) /\ abs(a) < d
                     ==> ~(relative_orientation (\x. f x + a % x) c = &0)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `c:real^N->bool` SIMPLEX_ORDERING_EXISTS) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `A:real^N^N` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RELATIVE_ORIENTATION th]) THEN
    REWRITE_TAC[REAL_SGN_EQ; REAL_DIV_EQ_0] THEN
    MP_TAC(ISPECL [`c:real^N->bool`; `A:real^N^N`] DET_ORDERED_SIMPLEX_NZ) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`maprows (f:real^N->real^N) A`; `A:real^N^N`]
          NEARBY_INVERTIBLE_MATRIX_GEN) THEN
    ASM_REWRITE_TAC[INVERTIBLE_DET_NZ] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:real` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `a:real`) THEN
    ASM_REWRITE_TAC[CONTRAPOS_THM] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[CART_EQ; maprows; LAMBDA_BETA; MATRIX_ADD_COMPONENT;
      MATRIX_CMUL_COMPONENT; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT];
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:(real^N->bool)->real` THEN STRIP_TAC THEN
    EXISTS_TAC
     `\x. (f:real^N->real^N) x +
          min (e / B) (inf (IMAGE (d:(real^N->bool)->real) t)) / &2 % x` THEN
    REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `c:real^N->bool` THEN
    ASM_CASES_TAC `(c:real^N->bool) IN t` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `c:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_ARITH `dist(x:real^N,x + y) = norm y`] THEN
      REWRITE_TAC[NORM_MUL] THEN ASM_CASES_TAC `v:real^N = vec 0` THEN
      ASM_REWRITE_TAC[NORM_0; REAL_MUL_RZERO] THEN
      TRANS_TAC REAL_LTE_TRANS `e / B * norm(v:real^N)` THEN
      ASM_SIMP_TAC[REAL_LT_RMUL_EQ; NORM_POS_LT; REAL_LE_LDIV_EQ;
       REAL_LE_LMUL_EQ; REAL_ARITH `e / B * v:real = (e * v) / B`] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[extreme_point_of]] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < d /\ &0 < e ==> abs(min e d / &2) < e`);
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
       `d <= c /\ &0 < d /\ &0 < e
        ==> ~(min e d / &2 = &0) /\ abs(min e d / &2) < c`) THEN
      ASM_SIMP_TAC[REAL_INF_LE_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_REFL]; ALL_TAC]] THEN
    ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE; REAL_LT_DIV]]);;

(* ------------------------------------------------------------------------- *)
(* Invariance under shift of counting point.                                 *)
(* ------------------------------------------------------------------------- *)

let BROUWER_DEGREE3_POINT_INDEPENDENCE = prove
 (`!f:real^N->real^N t u x y.
        2 <= dimindex(:N) /\
        convex u /\ bounded u /\ vec 0 IN interior u /\
        triangulation t /\ UNIONS t = frontier u /\
        (!c. c IN t ==> &(dimindex(:N)) - &1 simplex c) /\
        (!c. c IN t ==> ~(vec 0 IN vertex_image f c)) /\
        (!c. c IN t ==> ~(x IN frontier(conic hull (vertex_image f c)))) /\
        (!c. c IN t ==> ~(y IN frontier(conic hull (vertex_image f c))))
        ==> brouwer_degree3(x,t,f) = brouwer_degree3(y,t,f)`,
  let lemma0 = prove
   (`!f:A->real s.
          FINITE s
          ==> sum {t | t SUBSET s /\ t HAS_SIZE 2} (\t. sum t f) =
              &(CARD s - 1) * sum s f`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `!P. FINITE {t:A->bool | t SUBSET s /\ P t}` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE
        `{x | P x /\ Q x} = {x | x IN {y | P y} /\ Q x}`] THEN
      ASM_SIMP_TAC[FINITE_POWERSET; FINITE_RESTRICT];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `sum s (\x:A. sum {t | t SUBSET s /\ t HAS_SIZE 2 /\ x IN t}
                       (\t. f x))` THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (lhs o rand) SUM_SUM_PRODUCT o lhand o snd) THEN
      W(MP_TAC o PART_MATCH (lhs o rand) SUM_SUM_PRODUCT o
         rand o rand o snd) THEN
      SIMP_TAC[IN_ELIM_THM; HAS_SIZE] THEN ASM_REWRITE_TAC[GSYM HAS_SIZE] THEN
      REPEAT(DISCH_THEN SUBST1_TAC) THEN
      MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
      EXISTS_TAC `\(t:A->bool,x:A). (x,t)` THEN
      EXISTS_TAC `\(x:A,t:A->bool). (t,x)` THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IN_ELIM_PAIR_THM] THEN SET_TAC[];
      ASM_SIMP_TAC[SUM_CONST] THEN
      SUBGOAL_THEN
       `!x:A. x IN s
              ==> CARD {t | t SUBSET s /\ t HAS_SIZE 2 /\ x IN t} =
                  CARD s - 1`
       (fun th -> ASM_SIMP_TAC[th; SUM_LMUL]) THEN
      X_GEN_TAC `a:A` THEN DISCH_TAC THEN
      TRANS_TAC EQ_TRANS `CARD(IMAGE (\x:A. {a,x}) (s DELETE a))` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
        REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `t:A->bool` THEN
        REWRITE_TAC[HAS_SIZE_CONV `s HAS_SIZE 2`] THEN
        REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
        REWRITE_TAC[TAUT `p /\ (q /\ r) /\ s <=> r /\ p /\ q /\ s`] THEN
        SIMP_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
        REWRITE_TAC[NOT_IMP; IN_INSERT; NOT_IN_EMPTY; LEFT_OR_DISTRIB] THEN
        REWRITE_TAC[EXISTS_OR_THM; CONJ_ASSOC] THEN
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SWAP_EXISTS_THM] THEN
        REWRITE_TAC[ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1] THEN
        REWRITE_TAC[OR_EXISTS_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
        ASM SET_TAC[];
        ASM_SIMP_TAC[CARD_IMAGE_INJ; FINITE_DELETE; CARD_DELETE; IN_DELETE;
                     SET_RULE `{a,x} = {a,y} <=> x = y`]]])
  and lemma1 = prove
   (`!P a:real^N->real b s z.
      (?t. open t /\ z IN t /\
           !x y. (x IN t /\ P x) /\ (y IN t /\ P y) ==> a x = a y) /\
      (?t. open t /\ z IN t /\
           !x y. (x IN t /\ P x) /\ (y IN t /\ P y) ==> b x = b y)
      ==> ?t. open t /\ z IN t /\
              !x y. (x IN t /\ P x) /\ (y IN t /\ P y)
                    ==> a x + b x = a y + b y`,
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `t INTER u:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_INTER] THEN ASM SET_TAC[])
  and lemma2 = prove
   (`!P a:real^N->A->real k s z.
        FINITE k /\
        (!i. i IN k
             ==> ?t. open t /\ z IN t /\
                     !x y. (x IN t /\ P x) /\ (y IN t /\ P y) ==> a x i = a y i)
        ==> ?t. open t /\ z IN t /\
                !x y. (x IN t /\ P x) /\ (y IN t /\ P y)
                      ==> sum k (a x) = sum k (a y)`,
    REPEAT GEN_TAC THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `u:A->real^N->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `k:A->bool = {}` THEN ASM_REWRITE_TAC[SUM_CLAUSES] THENL
     [MESON_TAC[IN_UNIV; OPEN_UNIV]; ALL_TAC] THEN
    EXISTS_TAC `INTERS (IMAGE (u:A->real^N->bool) k)` THEN
    ASM_SIMP_TAC[OPEN_INTERS; FINITE_IMAGE; FORALL_IN_IMAGE; IN_INTERS] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[] THEN
    ASM SET_TAC[])
  and main_lemma = prove
   (`!A:real^N^N z k.
          2 <= dimindex(:N) /\
          1 <= k /\ k <= dimindex(:N) /\ ~(det A = &0) /\
          z IN relative_interior(conic hull
                 (convex hull {row i A | i IN 1..dimindex(:N) /\ ~(i = k)}))
          ==> ?e. &0 < e /\
                  !x. x IN ball(z,e)
                      ==> (x IN conic hull (convex hull (rows A)) <=>
                           &0 <= det(lambda i. if i = k then x else A$i) /
                                 det A) /\
                          (x IN interior(conic hull (convex hull (rows A))) <=>
                           &0 < det(lambda i. if i = k then x else A$i) /
                                det A)`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~dependent(rows(A:real^N^N))` ASSUME_TAC THENL
     [ASM_MESON_TAC[DET_DEPENDENT_ROWS]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [DEPENDENT_AFFINE_DEPENDENT_CASES]) THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!m. 1 <= m /\ m <= dimindex(:N)
          ==> conic hull
                (convex hull {row i A | i IN 1..dimindex(:N) /\ ~(i = m)})
              face_of conic hull(convex hull (rows(A:real^N^N)))`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_CONIC_HULL THEN
      ASM_REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `{row i (A:real^N^N) | i IN 1..dimindex(:N) /\ ~(i = m)}` THEN
      REWRITE_TAC[rows; IN_NUMSEG] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[IN_CONIC_CONVEX_HULL_ROWS_QFREE;
                 IN_INTERIOR_CONIC_CONVEX_HULL_ROWS_QFREE] THEN
    SUBGOAL_THEN
    `!i. 1 <= i /\ i <= dimindex(:N) /\ ~(i = k)
          ==> ?e. &0 < e /\
                  !x. x IN ball(z,e)
                      ==> &0 < det((lambda j. if j = i then x else A$j)) /
                               det(A:real^N^N)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `(\x. lift(det((lambda j. if j = i then x else A$j)) / det(A:real^N^N)))
        continuous at z`
      MP_TAC THENL
       [REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
        REWRITE_TAC[o_DEF; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_CMUL THEN
        MATCH_MP_TAC CONTINUOUS_LIFT_DET THEN
        MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN SIMP_TAC[LAMBDA_BETA] THEN
        ASM_CASES_TAC `p:num = i` THEN
        ASM_SIMP_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_LIFT_COMPONENT];
        REWRITE_TAC[continuous_at]] THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[DIST_LIFT] THEN
      DISCH_THEN(MP_TAC o SPEC
       `det((lambda j. if j = i then z else A$j)) / det(A:real^N^N)`) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_ARITH `&0 < x <=> ~(x < &0) /\ ~(x = &0)`];
        MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[IN_BALL] THEN
        MESON_TAC[REAL_ARITH `abs(z - x) < z ==> &0 < x`]] THEN
      CONJ_TAC THENL
       [DISCH_TAC THEN
        MP_TAC(ISPECL [`A:real^N^N`; `z:real^N`]
          IN_CONIC_CONVEX_HULL_ROWS_QFREE) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `p /\ ~q ==> ~(p <=> q)`) THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `z IN relative_interior s
            ==> relative_interior s SUBSET s /\ s SUBSET t
                ==> z IN t`)) THEN
          REWRITE_TAC[RELATIVE_INTERIOR_SUBSET; rows; IN_NUMSEG] THEN
          REPEAT(MATCH_MP_TAC HULL_MONO) THEN SET_TAC[];
          DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
          ASM_REWRITE_TAC[real_ge; GSYM REAL_NOT_LT]];
        ASM_SIMP_TAC[GSYM(REWRITE_RULE[EXTENSION; IN_ELIM_THM]
                          IN_SPAN_DEPLETED_ROWS_QFREE);
                     REAL_DIV_EQ_0] THEN
        DISCH_TAC THEN
        MP_TAC(ISPECL
         [`conic hull(convex hull (rows(A:real^N^N)))`;
          `conic hull(convex hull { row j (A:real^N^N) |
                                    j IN 1..dimindex(:N) /\ ~(j = i)})`;
          `conic hull(convex hull { row j (A:real^N^N) |
                                    j IN 1..dimindex(:N) /\ ~(j = k)})`]
         SUBSET_OF_FACE_OF_AFFINE_HULL) THEN
        ASM_SIMP_TAC[CONVEX_CONIC_HULL; CONVEX_CONVEX_HULL; NOT_IMP] THEN
        REPEAT CONJ_TAC THENL
         [REPEAT(MATCH_MP_TAC HULL_MONO) THEN
          REWRITE_TAC[rows; IN_NUMSEG] THEN SET_TAC[];
          ASM_SIMP_TAC[AFFINE_HULL_CONIC_HULL; CONVEX_HULL_EQ_EMPTY] THEN
          REWRITE_TAC[SET_RULE
           `{f x | x IN s /\ ~(x = a)} = {} <=> s SUBSET {a}`] THEN
          COND_CASES_TAC THENL
           [FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
              CARD_SUBSET)) THEN
            SIMP_TAC[FINITE_SING; CARD_SING; CARD_NUMSEG_1] THEN
            ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> ~(n <= 1)`];
            SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; IN_INSERT] THEN
            REWRITE_TAC[SPAN_INSERT_0; SPAN_CONVEX_HULL] THEN ASM SET_TAC[]];
          DISCH_THEN(MP_TAC o MATCH_MP SPAN_MONO) THEN
          REWRITE_TAC[SPAN_CONIC_HULL; SPAN_CONVEX_HULL] THEN
          SUBGOAL_THEN
           `row k (A:real^N^N) IN
            span {row j A | j IN 1..dimindex (:N) /\ ~(j = i)}`
          MP_TAC THENL
           [MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_NUMSEG] THEN
            ASM SET_TAC[];
            REWRITE_TAC[TAUT `p ==> ~q <=> ~(p /\ q)`;
                        GSYM INSERT_SUBSET]] THEN
          DISCH_THEN(MP_TAC o MATCH_MP SPAN_MONO) THEN
          REWRITE_TAC[SPAN_SPAN] THEN MATCH_MP_TAC(SET_RULE
           `!u. u SUBSET s /\ ~(u SUBSET t) ==> ~(s SUBSET t)`) THEN
          EXISTS_TAC `span(rows (A:real^N^N))` THEN CONJ_TAC THENL
           [MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
            REWRITE_TAC[SUBSPACE_SPAN] THEN
            REWRITE_TAC[SUBSET; rows; FORALL_IN_GSPEC] THEN
            X_GEN_TAC `j:num` THEN STRIP_TAC THEN
            ASM_CASES_TAC `j:num = k` THEN
            ASM_SIMP_TAC[SPAN_SUPERSET; IN_INSERT] THEN
            MATCH_MP_TAC SPAN_SUPERSET THEN
            REWRITE_TAC[IN_INSERT; IN_NUMSEG] THEN DISJ2_TAC THEN
            MATCH_MP_TAC SPAN_SUPERSET THEN ASM SET_TAC[];
            DISCH_THEN(MP_TAC o MATCH_MP DIM_SUBSET) THEN
            REWRITE_TAC[DIM_SPAN; GSYM RANK_ROW; NOT_LE] THEN
            SUBGOAL_THEN `rank(A:real^N^N) = dimindex(:N)` SUBST1_TAC THENL
             [ASM_MESON_TAC[RANK_EQ_FULL_DET]; ALL_TAC] THEN
            ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
            W(MP_TAC o PART_MATCH (lhand o rand) DIM_LE_CARD o
              lhand o snd) THEN
            ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_IMAGE; FINITE_NUMSEG] THEN
            MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS) THEN
            W(MP_TAC o PART_MATCH (lhand o rand)
               CARD_IMAGE_LE o lhand o snd) THEN
            ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG] THEN
            MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS) THEN
            SIMP_TAC[GSYM DELETE; CARD_DELETE; FINITE_NUMSEG] THEN
            ASM_REWRITE_TAC[CARD_NUMSEG_1; IN_NUMSEG] THEN ASM_ARITH_TAC]]];
      REWRITE_TAC[CONJ_ASSOC; GSYM IN_NUMSEG; GSYM IN_DELETE] THEN
      GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `ee:num->real` THEN
  REWRITE_TAC[FORALL_AND_THM; TAUT
    `(p ==> q /\ r) <=> (p ==> q) /\ (p ==> r)`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~((1..dimindex(:N)) DELETE k = {})` ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `s DELETE a = {} <=> s SUBSET {a}`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]  CARD_SUBSET)) THEN
    SIMP_TAC[FINITE_SING; CARD_SING; CARD_NUMSEG_1] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> ~(n <= 1)`];
    ALL_TAC] THEN
  EXISTS_TAC `inf(IMAGE ee ((1..dimindex(:N)) DELETE k))` THEN
  ASM_SIMP_TAC[IN_BALL; REAL_LT_INF_FINITE; IMAGE_EQ_EMPTY;
               FINITE_IMAGE; FINITE_NUMSEG; FINITE_DELETE] THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; real_gt; real_ge] THEN
  CONJ_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  EQ_TAC THEN ASM_SIMP_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `j:num = k` THEN ASM_REWRITE_TAC[] THEN
  TRY(MATCH_MP_TAC REAL_LT_IMP_LE) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_BALL; IN_NUMSEG; IN_DELETE]) THEN
  ASM SET_TAC[]) in
  SUBGOAL_THEN
   `!f:real^N->real^N t u x y.
        2 <= dimindex(:N) /\
        convex u /\ bounded u /\ vec 0 IN interior u /\
        triangulation t /\ UNIONS t = frontier u /\
        (!c. c IN t ==> &(dimindex(:N)) - &1 simplex c) /\
        (!c. c IN t ==> ~(vec 0 IN vertex_image f c)) /\
        (!c. c IN t ==> ~(x IN frontier(conic hull (vertex_image f c)))) /\
        (!c. c IN t ==> ~(y IN frontier(conic hull (vertex_image f c)))) /\
        (!c. c IN t ==> ~(relative_orientation f c = &0))
        ==> brouwer_degree3(x,t,f) = brouwer_degree3(y,t,f)`
  MP_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `!c:real^N->bool. c IN t ==> ~(vec 0 IN affine hull c)`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[NOT_IN_AFFINE_HULL_SURFACE_TRIANGULATION; SUBSET_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^N->real^N`; `t:(real^N->bool)->bool`]
        BROUWER_DEGREE3_PERTURB) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[triangulation]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
      MP_TAC(SPEC `y:real^N` th) THEN
      MP_TAC(SPEC `x:real^N` th)) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL  [`f:real^N->real^N`; `t:(real^N->bool)->bool`;
                    `min d e`] ORIENTING_PERTURBATION_EXISTS) THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; dist] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`g:real^N->real^N`; `t:(real^N->bool)->bool`; `u:real^N->bool`;
      `x:real^N`; `y:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `g:real^N->real^N`)) THEN
    REPLICATE_TAC 2 (ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[RELATIVE_ORIENTATION_NONZERO; HULL_INC]] THEN
  ASM_CASES_TAC `2 <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `t:(real^N->bool)->bool`] THEN
  ASM_CASES_TAC `triangulation(t:(real^N->bool)->bool)` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `FINITE(t:(real^N->bool)->bool)` THENL
   [ALL_TAC; ASM_MESON_TAC[triangulation]] THEN
  ONCE_REWRITE_TAC[TAUT
   `p /\ q /\ r /\ s /\ t ==> u <=> p /\ q /\ r /\ s ==> t ==> u`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; LEFT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!c:real^N->bool. c IN t ==> ~(vec 0 IN affine hull c)`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[NOT_IN_AFFINE_HULL_SURFACE_TRIANGULATION; SUBSET_REFL];
      ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^N. ?c. c IN t /\ w IN conic hull c` ASSUME_TAC THENL
   [MATCH_MP_TAC ANY_IN_CONIC_HULL_SIMPLEX THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. x IN (:real^N) DIFF
              UNIONS {frontier(conic hull (vertex_image f c)) | c IN t}`;
    `\x y:real^N. brouwer_degree3(x,t,f) = brouwer_degree3(y,t,f)`;
    `(:real^N) DIFF
     UNIONS {k | c,k | c IN t /\
                       k IN
                       {k | k face_of conic hull vertex_image f c /\
                            aff_dim k <= &(dimindex (:N)) - &2}}`]
        CONNECTED_EQUIVALENCE_RELATION_GEN) THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(MESON[]
     `(Q x /\ Q y) /\ (!z. Q z ==> P z)
      ==> (!a b. P a /\ P b /\ Q a /\ Q b
                 ==> brouwer_degree3(a,t,f) = brouwer_degree3(b,t,f))
          ==> brouwer_degree3(x,t,f) = brouwer_degree3(y,t,f)`) THEN
    CONJ_TAC THENL [REWRITE_TAC[UNIONS_GSPEC] THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CONTRAPOS_THM; UNIONS_GSPEC; IN_ELIM_THM] THEN
    GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
    ASM_SIMP_TAC[FRONTIER_OF_CONVEX_CLOSED; CONVEX_CONIC_HULL_VERTEX_IMAGE;
                 CLOSED_CONIC_HULL_VERTEX_IMAGE] THEN
    GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    MESON_TAC[INT_ARITH `k:int <= n - &2 ==> k < n`]] THEN
  MAP_EVERY (C UNDISCH_THEN (K ALL_TAC))
   [`!c. c IN t ==> ~((x:real^N) IN frontier (conic hull vertex_image f c))`;
    `!c. c IN t
         ==> ~((y:real^N) IN frontier (conic hull vertex_image f c))`] THEN
  REWRITE_TAC[EQ_SYM; EQ_TRANS] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[CONJ_SYM] OPEN_IN_OPEN] THEN
  REWRITE_TAC[MESON[]
   `(!t a. (?u. t = f a u /\ P u) /\ Q a t ==> R t a) <=>
    (!u a. P u /\ Q a (f a u) ==> R (f a u) a)`] THEN
  REWRITE_TAC[MESON[]
   `(?x. (?y. P x y /\ R x y) /\ Q x) <=> ?y x. P x y /\ R x y /\ Q x`] THEN
  REWRITE_TAC[UNWIND_THM2] THEN
  REWRITE_TAC[IN_INTER; IMP_IMP; GSYM CONJ_ASSOC] THEN
  SIMP_TAC[IN_DIFF; IN_UNIV] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_OPEN_IN_DIFF_UNIONS_LOWDIM THEN
    REWRITE_TAC[CONNECTED_UNIV; AFFINE_HULL_UNIV; OPEN_IN_REFL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[SET_RULE
        `{x | P x /\ Q x} = {x | x IN {x | P x} /\ Q x}`] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_RESTRICT THEN
      ASM_SIMP_TAC[FINITE_POLYHEDRON_FACES;
                   POLYHEDRON_CONIC_HULL_VERTEX_IMAGE];
      REWRITE_TAC[FORALL_IN_GSPEC; AFF_DIM_UNIV] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN INT_ARITH_TAC];
    MATCH_MP_TAC(SET_RULE
     `(!a u. a IN u /\ open u ==> ~((UNIV DIFF t) INTER u = {})) /\
      s SUBSET t
      ==> !u a. open u /\ P a /\ a IN u
                ==> ?z. ~(z IN s) /\ z IN u /\ ~(z IN t)`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM CLOSURE_NONEMPTY_OPEN_INTER; CLOSURE_COMPLEMENT] THEN
      REWRITE_TAC[SET_RULE `(!x. x IN UNIV DIFF s) <=> s = {}`] THEN
      MATCH_MP_TAC NOWHERE_DENSE_COUNTABLE_UNIONS_CLOSED THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE;
                   FINITE_IMP_COUNTABLE; FRONTIER_CLOSED] THEN
      ASM_SIMP_TAC[INTERIOR_FRONTIER_EMPTY; CLOSED_CONIC_HULL_VERTEX_IMAGE];
      REWRITE_TAC[UNIONS_GSPEC; SUBSET; IN_ELIM_THM] THEN
      GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
      REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
      ASM_SIMP_TAC[FRONTIER_OF_CONVEX_CLOSED; CONVEX_CONIC_HULL_VERTEX_IMAGE;
                   CLOSED_CONIC_HULL_VERTEX_IMAGE] THEN
      GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      MESON_TAC[INT_ARITH `k:int <= n - &2 ==> k < n`]];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^N` THEN REWRITE_TAC[UNIONS_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN DISCH_TAC THEN
  REWRITE_TAC[brouwer_degree3; ETA_AX] THEN
  REWRITE_TAC[TAUT `p /\ q /\ r /\ s /\ t /\ u <=>
                    (q /\ t /\ p) /\ (s /\ u /\ r)`] THEN
  SUBGOAL_THEN
   `!c:real^N->bool. c IN t ==> ~(vec 0 IN affine hull (vertex_image f c))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_ORIENTATION_NONZERO]; ALL_TAC] THEN
  ASM_CASES_TAC `z:real^N = vec 0` THENL
   [MATCH_MP_TAC(TAUT `F ==> p`) THEN
    FIRST_ASSUM(MP_TAC o GEN `c:real^N->bool` o ONCE_REWRITE_RULE[IMP_CONJ] o
     SPECL [`c:real^N->bool`; `{vec 0:real^N}`]) THEN
    ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_CONIC_HULL; IN_SING] THEN
    ASM_REWRITE_TAC[AFF_DIM_SING; INT_SUB_LE; INT_OF_NUM_LE] THEN
    ASM_MESON_TAC[VERTEX_IMAGE_NONEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!x. sum {c | c IN t /\ x IN conic hull vertex_image f c}
             (relative_orientation (f:real^N->real^N)) =
         sum {c | c IN t /\ x IN conic hull vertex_image f c /\
                  ~(z IN frontier(conic hull vertex_image f c))}
             (relative_orientation f) +
         sum {k | ?c. c IN t /\ k face_of c /\
                      aff_dim k = &(dimindex(:N)) - &2 /\
                      z IN conic hull (vertex_image f k)}
             (\k. sum {c | c IN {c | c IN t /\
                                     x IN conic hull vertex_image f c /\
                              z IN frontier(conic hull vertex_image f c)} /\
                           k face_of c}
                      (relative_orientation f))`
    (fun th -> ONCE_REWRITE_TAC[th])
  THENL
   [X_GEN_TAC `w:real^N` THEN TRANS_TAC EQ_TRANS
     `sum {c | c IN t /\ w IN conic hull vertex_image f c /\
               ~(z IN frontier(conic hull vertex_image f c))}
          (relative_orientation f) +
      sum {c | c IN t /\ w IN conic hull vertex_image f c /\
               z IN frontier(conic hull vertex_image f c)}
          (relative_orientation(f:real^N->real^N))` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
      ASM_SIMP_TAC[FINITE_RESTRICT] THEN SET_TAC[];
      AP_TERM_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      SUM_GROUP_RELATION o rand o snd) THEN
    ANTS_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN REFL_TAC] THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?k. k face_of c /\
          aff_dim k = &(dimindex (:N)) - &2 /\
          z IN conic hull (vertex_image (f:real^N->real^N) k)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN
       `?k. k face_of c /\
            aff_dim k < &(dimindex (:N)) - &1 /\
            z IN conic hull (vertex_image (f:real^N->real^N) k)`
      STRIP_ASSUME_TAC THENL
       [ALL_TAC;
        MP_TAC(ISPECL [`c:real^N->bool`; `k:real^N->bool`]
         FACE_OF_POLYHEDRON_FACE_OF_FACET) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_POLYHEDRON]; ALL_TAC] THEN
          CONJ_TAC THENL
           [DISCH_TAC; ASM_MESON_TAC[AFF_DIM_SIMPLEX; INT_LT_REFL]] THEN
          UNDISCH_TAC `z IN conic hull vertex_image (f:real^N->real^N) k` THEN
          ASM_REWRITE_TAC[vertex_image; EXTREME_POINT_OF_EMPTY; EMPTY_GSPEC;
           IMAGE_CLAUSES; CONVEX_HULL_EMPTY; CONIC_HULL_EMPTY; NOT_IN_EMPTY];
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^N->bool` THEN
          SIMP_TAC[facet_of] THEN STRIP_TAC THEN
          REWRITE_TAC[INT_ARITH `n - &2:int = (n - &1) - &1`] THEN
          CONJ_TAC THENL [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `z IN s ==> s SUBSET t ==> z IN t`)) THEN
          MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[vertex_image] THEN
          MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN
          REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
          ASM_MESON_TAC[EXTREME_POINT_OF_FACE]]] THEN
      UNDISCH_TAC `(z:real^N) IN frontier (conic hull vertex_image f c)` THEN
      ASM_SIMP_TAC[FRONTIER_OF_CONVEX_CLOSED; CONVEX_CONIC_HULL_VERTEX_IMAGE;
                   CLOSED_CONIC_HULL_VERTEX_IMAGE] THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[FACE_OF_CONIC_HULL_EQ] THEN
      REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM] THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
       [ASM_MESON_TAC[IN_SING]; ALL_TAC] THEN
      REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
      REWRITE_TAC[UNWIND_THM2; MESON[]
       `((p /\ x = y) /\ q) /\ r <=> y = x /\ p /\ q /\ r`] THEN
      DISCH_THEN(X_CHOOSE_THEN `l:real^N->bool`
       (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
      REWRITE_TAC[vertex_image] THEN DISCH_THEN(MP_TAC o MATCH_MP
       (ONCE_REWRITE_RULE[IMP_CONJ_ALT] FACE_OF_CONVEX_HULL_SUBSET)) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC FINITE_IMP_COMPACT THEN
        MATCH_MP_TAC FINITE_IMAGE THEN
        MATCH_MP_TAC FINITE_POLYHEDRON_EXTREME_POINTS THEN
        ASM_MESON_TAC[SIMPLEX_IMP_POLYHEDRON];
        REWRITE_TAC[EXISTS_SUBSET_IMAGE]] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `convex hull e:real^N->bool` THEN
      SUBGOAL_THEN `{v:real^N | v extreme_point_of convex hull e} = e`
      SUBST1_TAC THENL
       [MATCH_MP_TAC EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT THEN
        ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET; SIMPLEX_EXTREME_POINTS];
        ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET_FACE_OF_SIMPLEX]; DISCH_TAC] THEN
      MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
       [ASM_MESON_TAC[]; DISCH_TAC] THEN
      UNDISCH_TAC `aff_dim (conic hull l:real^N->bool) < &(dimindex (:N))` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN
         `~(vec 0 IN affine hull vertex_image (f:real^N->real^N) c)`
      ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `~affine_dependent(e:real^N->bool) /\
        ~affine_dependent {v:real^N | v extreme_point_of c}`
      MP_TAC THENL
       [MATCH_MP_TAC(MESON[AFFINE_INDEPENDENT_SUBSET]
         `s SUBSET t /\ ~affine_dependent t
          ==> ~affine_dependent s /\ ~affine_dependent t`) THEN
        ASM_MESON_TAC[SIMPLEX_EXTREME_POINTS];
        REWRITE_TAC[AFFINE_INDEPENDENT_IFF_CARD]] THEN
      SUBGOAL_THEN
       `aff_dim {v:real^N | v extreme_point_of c} = &(dimindex(:N)) - &1`
      SUBST1_TAC THENL
       [ASM_MESON_TAC[SIMPLEX_EXTREME_POINTS;
                      AFF_DIM_CONVEX_HULL; AFF_DIM_SIMPLEX];
        ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
      REWRITE_TAC[INT_ARITH `x - &1:int < y - &1 <=> x < y`] THEN
      REWRITE_TAC[INT_OF_NUM_LT] THEN MATCH_MP_TAC CARD_PSUBSET THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[SIMPLEX_EXTREME_POINTS]] THEN
      ASM_REWRITE_TAC[PSUBSET] THEN DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV
       [AFF_DIM_CONIC_HULL]) THEN
      ASM_REWRITE_TAC[GSYM vertex_image] THEN
      REWRITE_TAC[vertex_image] THEN COND_CASES_TAC THENL
       [ASM_MESON_TAC[CONIC_HULL_EMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
      REWRITE_TAC[GSYM vertex_image] THEN
      ASM_REWRITE_TAC[AFF_DIM_DIM; INT_SUB_ADD; INT_OF_NUM_LT] THEN
      MP_TAC(ISPEC `c:real^N->bool` SIMPLEX_ORDERING_EXISTS) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `A:real^N^N` (ASSUME_TAC o SYM)) THEN
      ASM_REWRITE_TAC[vertex_image] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`)) THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP RELATIVE_ORIENTATION (SYM th)]) THEN
      ASM_REWRITE_TAC[DIM_CONVEX_HULL; GSYM ROWS_MAPROWS] THEN
      REWRITE_TAC[REAL_SGN_EQ; REAL_DIV_EQ_0; DE_MORGAN_THM] THEN
      SIMP_TAC[GSYM RANK_EQ_FULL_DET; RANK_ROW; ROWS_MAPROWS; LT_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[EXISTS_UNIQUE] THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `l:real^N->bool` THEN
    REWRITE_TAC[LEFT_EXISTS_AND_THM; CONJ_ASSOC] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
    PURE_ONCE_REWRITE_TAC[TAUT `p <=> ~p ==> F`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(k INTER l:real^N->bool) face_of c` ASSUME_TAC THENL
     [ASM_MESON_TAC[FACE_OF_INTER]; ALL_TAC] THEN
    SUBGOAL_THEN
     `aff_dim(k INTER l:real^N->bool) < &(dimindex(:N)) - &2`
    ASSUME_TAC THENL
     [MP_TAC(ISPEC `k INTER l:real^N->bool` FACE_OF_AFF_DIM_LT) THEN
      FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (SET_RULE
       `~(l = k) ==> ~(k INTER l = k) \/ ~(k INTER l = l)`))
      THENL
       [DISCH_THEN(MP_TAC o SPEC `k:real^N->bool`);
        DISCH_THEN(MP_TAC o SPEC `l:real^N->bool`)] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      (CONJ_TAC THENL [ASM_MESON_TAC[FACE_OF_IMP_CONVEX]; ALL_TAC]) THEN
      MATCH_MP_TAC FACE_OF_SUBSET THEN EXISTS_TAC `c:real^N->bool` THEN
      ASM_SIMP_TAC[FACE_OF_INTER; INTER_SUBSET; FACE_OF_IMP_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(vec 0 IN affine hull (vertex_image (f:real^N->real^N) c))`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`c:real^N->bool`;
      `conic hull (vertex_image (f:real^N->real^N) (k INTER l))`]) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FACE_OF_CONIC_HULL THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[vertex_image] THEN
      W(MP_TAC o PART_MATCH (lhand o rand)
        FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT o snd) THEN
      REWRITE_TAC[EXISTS_SUBSET_IMAGE] THEN ANTS_TAC THENL
       [ALL_TAC;
        DISCH_THEN SUBST1_TAC THEN
        EXISTS_TAC `{v:real^N | v extreme_point_of k INTER l}` THEN
        REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`k INTER l:real^N->bool`; `c:real^N->bool`]
          EXTREME_POINT_OF_FACE) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]] THEN
      MATCH_MP_TAC(ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM]
       AFFINE_DEPENDENT_IMP_DEPENDENT) THEN
      MP_TAC(ISPEC `c:real^N->bool` SIMPLEX_ORDERING_EXISTS) THEN
      ASM_SIMP_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `A:real^N^N` (ASSUME_TAC o SYM)) THEN
      ASM_REWRITE_TAC[vertex_image] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`)) THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM(fun th ->
       REWRITE_TAC[MATCH_MP RELATIVE_ORIENTATION (SYM th)]) THEN
      REWRITE_TAC[REAL_SGN_EQ; REAL_DIV_EQ_0; DE_MORGAN_THM] THEN
      REWRITE_TAC[GSYM ROWS_MAPROWS] THEN MESON_TAC[DET_DEPENDENT_ROWS];
      REWRITE_TAC[AFF_DIM_CONIC_HULL] THEN
      MATCH_MP_TAC(INT_ARITH
       `x:int < a ==> (if p then x else x + &1) <= a`) THEN
      TRANS_TAC INT_LET_TRANS `aff_dim(k INTER l:real^N->bool)` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[vertex_image; AFF_DIM_CONVEX_HULL] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) AFF_DIM_LE_CARD o lhand o snd) THEN
      SUBGOAL_THEN
       `FINITE {v:real^N | v extreme_point_of k INTER l}`
      ASSUME_TAC THENL
       [MATCH_MP_TAC FINITE_POLYHEDRON_EXTREME_POINTS THEN
        ASM_MESON_TAC[FACE_OF_POLYHEDRON_POLYHEDRON; SIMPLEX_IMP_POLYHEDRON];
        ASM_SIMP_TAC[FINITE_IMAGE]] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_LE_TRANS) THEN
      REWRITE_TAC[INT_LE_SUB_RADD] THEN
      TRANS_TAC INT_LE_TRANS
       `&(CARD {v:real^N | v extreme_point_of k INTER l}):int` THEN
      ASM_SIMP_TAC[CARD_IMAGE_LE; INT_OF_NUM_LE] THEN
      MATCH_MP_TAC(INT_ARITH `n:int = c - &1 ==> c:int <= n + &1`) THEN
      TRANS_TAC EQ_TRANS
        `aff_dim(convex hull {v:real^N | v extreme_point_of k INTER l})` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
        ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE; SIMPLEX_IMP_POLYTOPE;
                      POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_COMPACT];
        ALL_TAC] THEN
      REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
      SUBGOAL_THEN
       `~affine_dependent {v:real^N | v extreme_point_of k INTER l}`
      MP_TAC THENL
       [ALL_TAC;
        SIMP_TAC[AFFINE_INDEPENDENT_IFF_CARD] THEN INT_ARITH_TAC] THEN
      MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
      EXISTS_TAC `{v:real^N | v extreme_point_of c}` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_EXTREME_POINTS]; ALL_TAC] THEN
       MP_TAC(ISPECL [`k INTER l:real^N->bool`; `c:real^N->bool`]
          EXTREME_POINT_OF_FACE) THEN
       ASM_REWRITE_TAC[] THEN SET_TAC[];
      SUBGOAL_THEN
       `z IN conic hull vertex_image f k INTER
             conic hull vertex_image (f:real^N->real^N) l`
      MP_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhs o rand)
        INTER_CONIC_HULL o rand o lhand o snd) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `~(z IN s) ==> t SUBSET s ==> ~(z IN t)`)) THEN
        MATCH_MP_TAC HULL_MONO THEN
        REWRITE_TAC[UNION_SUBSET; vertex_image] THEN
        CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN
        MATCH_MP_TAC IMAGE_SUBSET THENL
         [MP_TAC(ISPEC `k:real^N->bool` EXTREME_POINT_OF_FACE);
          MP_TAC(ISPEC `l:real^N->bool` EXTREME_POINT_OF_FACE)] THEN
        DISCH_THEN(MP_TAC o SPEC `c:real^N->bool`) THEN
        ASM_SIMP_TAC[] THEN SET_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      ASM_CASES_TAC `vertex_image (f:real^N->real^N) k = {}` THEN
      ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
      ASM_CASES_TAC `vertex_image (f:real^N->real^N) l = {}` THEN
      ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> z IN s ==> z IN t`) THEN
      MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[vertex_image] THEN
      W(MP_TAC o PART_MATCH (lhand o rand)
        CONVEX_HULL_INTER o lhand o snd) THEN
      SUBGOAL_THEN
       `~(affine_dependent (IMAGE (f:real^N->real^N)
          {v:real^N | v extreme_point_of c}))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC(ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM]
         AFFINE_DEPENDENT_IMP_DEPENDENT) THEN
        MP_TAC(ISPEC `c:real^N->bool` SIMPLEX_ORDERING_EXISTS) THEN
        ASM_SIMP_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `A:real^N^N` (ASSUME_TAC o SYM)) THEN
        ASM_REWRITE_TAC[vertex_image] THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`)) THEN
        ASM_REWRITE_TAC[] THEN FIRST_ASSUM(fun th ->
         REWRITE_TAC[MATCH_MP RELATIVE_ORIENTATION (SYM th)]) THEN
        REWRITE_TAC[REAL_SGN_EQ; REAL_DIV_EQ_0; DE_MORGAN_THM] THEN
        REWRITE_TAC[GSYM ROWS_MAPROWS] THEN MESON_TAC[DET_DEPENDENT_ROWS];
        ALL_TAC] THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          AFFINE_INDEPENDENT_SUBSET)) THEN
        REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN
        MATCH_MP_TAC IMAGE_SUBSET THENL
         [MP_TAC(ISPEC `k:real^N->bool` EXTREME_POINT_OF_FACE);
          MP_TAC(ISPEC `l:real^N->bool` EXTREME_POINT_OF_FACE)] THEN
        DISCH_THEN(MP_TAC o SPEC `c:real^N->bool`) THEN
        ASM_SIMP_TAC[] THEN SET_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC HULL_MONO THEN
      MATCH_MP_TAC(SET_RULE
       `IMAGE f (s INTER t) SUBSET u /\
        (!x y. x IN s UNION t /\ y IN s UNION t /\ f x = f y ==> x = y)
        ==> IMAGE f s INTER IMAGE f t SUBSET u`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; EXTREME_POINT_OF_INTER];
        ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE
       `!t. s SUBSET t /\
            (!x y. x IN t /\ y IN t /\ f x = f y ==> x = y)
            ==> !x y. x IN s /\ y IN s /\ f x = f y ==> x = y`) THEN
      EXISTS_TAC `{v:real^N | v extreme_point_of c}` THEN CONJ_TAC THENL
       [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
         [MP_TAC(ISPEC `k:real^N->bool` EXTREME_POINT_OF_FACE);
          MP_TAC(ISPEC `l:real^N->bool` EXTREME_POINT_OF_FACE)] THEN
        DISCH_THEN(MP_TAC o SPEC `c:real^N->bool`) THEN
        ASM_SIMP_TAC[] THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`f:real^N->real^N`; `{v:real^N | v extreme_point_of c}`]
        CARD_IMAGE_EQ_INJ) THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[FINITE_POLYHEDRON_EXTREME_POINTS;
                      SIMPLEX_IMP_POLYHEDRON];
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
      TRANS_TAC EQ_TRANS `(&(dimindex(:N)) - &1) + &1:int` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(INT_ARITH `s - &1:int = c ==> s = c + &1`);
        ASM_MESON_TAC[SIMPLEX_EXTREME_POINTS]] THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [AFFINE_INDEPENDENT_IFF_CARD]) THEN
      DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[GSYM AFF_DIM_CONVEX_HULL] THEN
      ASM_SIMP_TAC[AFF_DIM_DIM; GSYM vertex_image] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      MP_TAC(ISPEC `c:real^N->bool` SIMPLEX_ORDERING_EXISTS) THEN
      ASM_SIMP_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `A:real^N^N` (ASSUME_TAC o SYM)) THEN
      ASM_REWRITE_TAC[vertex_image] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`)) THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM(fun th ->
       REWRITE_TAC[MATCH_MP RELATIVE_ORIENTATION (SYM th)]) THEN
      REWRITE_TAC[REAL_SGN_EQ; REAL_DIV_EQ_0; DE_MORGAN_THM] THEN
      REWRITE_TAC[DIM_CONVEX_HULL; GSYM ROWS_MAPROWS] THEN
      SIMP_TAC[GSYM RANK_EQ_FULL_DET; RANK_ROW]];
    ALL_TAC] THEN
  MATCH_MP_TAC lemma1 THEN CONJ_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `{x | P x /\ Q x /\ R x } =
                             {x | x IN {x | P x /\ R x} /\ Q x}`] THEN
  ONCE_REWRITE_TAC[SUM_RESTRICT_SET] THEN MATCH_MP_TAC lemma2 THEN
  REWRITE_TAC[IN_ELIM_THM] THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
    X_GEN_TAC `c:real^N->bool` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o REWRITE_RULE[FRONTIER_INTERIORS])) THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV; DE_MORGAN_THM] THEN
    MATCH_MP_TAC(MESON[]
     `(z IN s ==> P s) /\ (z IN t ==> P t)
      ==> z IN s \/ z IN t ==> ?u. P u`) THEN
    CONJ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
    MESON_TAC[REWRITE_RULE[SUBSET] INTERIOR_SUBSET; OPEN_INTERIOR; IN_DIFF];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `UNIONS {{k:real^N->bool | k face_of c} | c IN t}` THEN
    REWRITE_TAC[FINITE_UNIONS] THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_POLYTOPE_FACES; SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
    REWRITE_TAC[UNIONS_IMAGE; facet_of] THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `k:real^N->bool` THEN
  REWRITE_TAC[CONJ_ASSOC; LEFT_EXISTS_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET; ETA_AX; IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
  SUBGOAL_THEN
   `!x. {c:real^N->bool | c IN t /\
                          z IN frontier (conic hull vertex_image f c) /\
                          x IN conic hull vertex_image (f:real^N->real^N) c /\
                          k face_of c} =
        {c | (c IN t /\ k face_of c) /\ x IN conic hull vertex_image f c}`
    (fun th -> ONCE_REWRITE_TAC[th])
  THENL
   [X_GEN_TAC `w:real^N` THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `d:real^N->bool` THEN EQ_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (SET_RULE `z IN s ==> s SUBSET t ==> z IN t`)) THEN
    SUBGOAL_THEN
     `~dependent(IMAGE (f:real^N->real^N) {v | v extreme_point_of d})`
    ASSUME_TAC THENL
     [MP_TAC(ISPEC `d:real^N->bool` SIMPLEX_ORDERING_EXISTS) THEN
      ASM_SIMP_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `A:real^N^N` (ASSUME_TAC o SYM)) THEN
      ASM_REWRITE_TAC[vertex_image] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `d:real^N->bool`)) THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM(fun th ->
       REWRITE_TAC[MATCH_MP RELATIVE_ORIENTATION (SYM th)]) THEN
      REWRITE_TAC[REAL_SGN_EQ; REAL_DIV_EQ_0; DE_MORGAN_THM] THEN
      REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN
      REWRITE_TAC[GSYM ROWS_MAPROWS] THEN MESON_TAC[DET_DEPENDENT_ROWS];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [DEPENDENT_AFFINE_DEPENDENT_CASES]) THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC FACE_OF_SUBSET_FRONTIER_AFF_DIM THEN CONJ_TAC THENL
     [MATCH_MP_TAC FACE_OF_CONIC_HULL THEN
      ASM_REWRITE_TAC[vertex_image; AFFINE_HULL_CONVEX_HULL] THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      REWRITE_TAC[EXISTS_SUBSET_IMAGE] THEN
      EXISTS_TAC `{v:real^N | v extreme_point_of k}` THEN
      MP_TAC(ISPECL [`k:real^N->bool`; `d:real^N->bool`]
        EXTREME_POINT_OF_FACE) THEN
      ASM_SIMP_TAC[] THEN SET_TAC[];
      REWRITE_TAC[AFF_DIM_CONIC_HULL] THEN MATCH_MP_TAC(INT_ARITH
       `x <= n - &2 ==> (if p then x else x + &1):int < n`) THEN
      REWRITE_TAC[vertex_image; AFF_DIM_CONVEX_HULL] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) AFF_DIM_LE_CARD o lhand o snd) THEN
      SUBGOAL_THEN `FINITE {v:real^N | v extreme_point_of k}` ASSUME_TAC THENL
       [MATCH_MP_TAC FINITE_POLYHEDRON_EXTREME_POINTS THEN
        ASM_MESON_TAC[FACE_OF_POLYHEDRON_POLYHEDRON; SIMPLEX_IMP_POLYHEDRON];
        ASM_SIMP_TAC[FINITE_IMAGE]] THEN
      MATCH_MP_TAC(INT_ARITH
       `b:int <= n - &1 ==> x <= b - &1 ==> x <= n - &2`) THEN
      TRANS_TAC INT_LE_TRANS
       `&(CARD {v:real^N | v extreme_point_of k}):int` THEN
      ASM_SIMP_TAC[CARD_IMAGE_LE; INT_OF_NUM_LE] THEN
      MATCH_MP_TAC(INT_ARITH `x - &1:int <= y - &2 ==> x <= y - &1`) THEN
      MP_TAC(ISPEC `{v:real^N | v extreme_point_of k}`
        AFF_DIM_AFFINE_INDEPENDENT) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
        EXISTS_TAC `{v:real^N | v extreme_point_of d}` THEN CONJ_TAC THENL
         [ASM_MESON_TAC[SIMPLEX_EXTREME_POINTS];
          MP_TAC(ISPECL [`k:real^N->bool`; `d:real^N->bool`]
           EXTREME_POINT_OF_FACE) THEN
          ASM_SIMP_TAC[] THEN SET_TAC[]];
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
       `x:int = n - &2 ==> x = y ==> y <= n - &2`)) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM AFF_DIM_CONVEX_HULL] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
      ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE; SIMPLEX_IMP_POLYTOPE;
                    POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_COMPACT]];
    ONCE_REWRITE_TAC[SET_RULE
     `{x | P x /\ Q x} = {x | x IN {x | P x} /\ Q x}`] THEN
    ONCE_REWRITE_TAC[SUM_RESTRICT_SET]] THEN
  SUBGOAL_THEN
   `?c d:real^N->bool.
      c IN t /\ d IN t /\ k face_of c /\ k face_of d /\ ~(c = d)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `?c:real^N->bool. c IN t /\ k face_of c` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `?a:real^N. a IN relative_interior (conic hull k)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) RELATIVE_INTERIOR_EQ_EMPTY o
        rand o snd) THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[CONVEX_CONIC_HULL; face_of];
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[CONIC_HULL_EQ_EMPTY] THEN
      ASM_REWRITE_TAC[GSYM AFF_DIM_EQ_MINUS1] THEN
      MATCH_MP_TAC(INT_ARITH `&2:int <= n ==> ~(n - &2 = -- &1)`) THEN
      ASM_REWRITE_TAC[INT_OF_NUM_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?d:real^N->bool. d IN t /\ ~(d = c) /\ a IN conic hull d`
    MP_TAC THENL
     [REWRITE_TAC[SET_RULE
       `(?d. d IN t /\ P d /\ a IN f d) <=>
        a IN UNIONS {f d | d IN t /\ P d}`] THEN
      MATCH_MP_TAC(MESON[CLOSURE_CLOSED]
       `closed s /\ a IN closure s ==> a IN s`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
        CONJ_TAC THENL
         [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
          MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_RESTRICT THEN
          ASM_MESON_TAC[];
          REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_CONIC_HULL_STRONG THEN
          ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]];
        ALL_TAC] THEN
      REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      REWRITE_TAC[EXISTS_IN_UNIONS; EXISTS_IN_GSPEC;
                  RIGHT_EXISTS_AND_THM] THEN
      SUBGOAL_THEN
       `ball (a:real^N,e) SUBSET {a | ?c. c IN t /\ a IN conic hull c}`
      MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~(ball(a:real^N,e) SUBSET conic hull c)` MP_TAC THENL
       [SUBGOAL_THEN `(a:real^N) IN frontier(conic hull c)` MP_TAC THENL
         [FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
           RELATIVE_INTERIOR_SUBSET)) THEN
          MATCH_MP_TAC(SET_RULE `s SUBSET t ==> a IN s ==> a IN t`) THEN
          MATCH_MP_TAC FACE_OF_SUBSET_FRONTIER_AFF_DIM THEN
          ASM_SIMP_TAC[AFF_DIM_CONIC_HULL] THEN
          CONJ_TAC THENL [ALL_TAC; INT_ARITH_TAC] THEN
          MATCH_MP_TAC FACE_OF_CONIC_HULL THEN ASM_SIMP_TAC[];
          REWRITE_TAC[FRONTIER_STRADDLE] THEN
          DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[SUBSET; IN_BALL] THEN SET_TAC[]];
        ONCE_REWRITE_TAC[IMP_IMP] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
         `~(s SUBSET t) /\ s SUBSET u
          ==> ?x. x IN s /\ x IN u /\ ~(x IN t)`)) THEN
        REWRITE_TAC[IN_ELIM_THM; IN_BALL; RIGHT_AND_EXISTS_THM;
                    LEFT_AND_EXISTS_THM] THEN
        GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^N` THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^N->bool` THEN
        ASM_CASES_TAC `d:real^N->bool = c` THEN
        ASM_REWRITE_TAC[DIST_SYM] THEN MESON_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^N->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC FACE_OF_TRANS `c INTER d:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[triangulation]] THEN
    MATCH_MP_TAC FACE_OF_SUBSET THEN EXISTS_TAC `c:real^N->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC SUBSET_OF_FACE_OF THEN
    EXISTS_TAC `c:real^N->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[triangulation]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `k SUBSET c /\ relative_interior k SUBSET k /\
      ~DISJOINT d (relative_interior k)
      ==> ~DISJOINT (c INTER d) (relative_interior k)`) THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL
      [`d:real^N->bool`; `relative_interior k:real^N->bool`;`u:real^N->bool`]
       INTER_CONIC_HULL_SUBSETS_CONVEX_RELATIVE_FRONTIER) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REWRITE_RULE[SUBSET] INTERIOR_SUBSET_RELATIVE_INTERIOR] THEN
      MATCH_MP_TAC(SET_RULE
       `relative_interior d SUBSET d /\
        relative_frontier u = frontier u /\
        c SUBSET frontier u /\ d SUBSET frontier u
        ==> c UNION relative_interior d SUBSET
            relative_frontier u`) THEN
      REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN CONJ_TAC THENL
       [MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN ASM SET_TAC[];
        FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN ASM SET_TAC[]];
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN SIMP_TAC[DISJOINT]] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `~((vec 0:real^N) IN affine hull k)` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; FACE_OF_IMP_SUBSET; HULL_MONO]; ALL_TAC] THEN
    UNDISCH_TAC `(a:real^N) IN relative_interior (conic hull k)` THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_CONIC_HULL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `2 <= CARD {c:real^N->bool | c IN t /\ k face_of c}`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `c:real^N->bool`
     (X_CHOOSE_THEN `d:real^N->bool` STRIP_ASSUME_TAC)) THEN
    TRANS_TAC LE_TRANS `CARD{c:real^N->bool,d:real^N->bool}` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[NOT_IN_EMPTY; IN_SING; ARITH];
      MATCH_MP_TAC CARD_SUBSET THEN
      ASM_SIMP_TAC[FINITE_RESTRICT] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f. sum {c:real^N->bool | c IN t /\ k face_of c} f =
        sum {u | u SUBSET {c | c IN t /\ k face_of c} /\ u HAS_SIZE 2}
            (\u. sum u f) / &(CARD {c | c IN t /\ k face_of c} - 1)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [X_GEN_TAC `f:(real^N->bool)->real` THEN
    W(MP_TAC o PART_MATCH (lhs o rand) lemma0 o
      lhand o rand o snd) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_RESTRICT]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC(REAL_FIELD `~(y = &0) ==> x = (y * x) / y`) THEN
    ASM_SIMP_TAC[REAL_OF_NUM_EQ; ARITH_RULE `2 <= n ==> ~(n - 1 = 0)`];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> (p /\ q /\ r) /\ s`] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_EQ; ARITH_RULE `2 <= n ==> ~(n - 1 = 0)`; REAL_FIELD
   `~(y = &0) ==> (a / y = b / y <=> a = b)`] THEN
  MATCH_MP_TAC lemma2 THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE
     `{x | P x /\ Q x} = {x | x IN {y | P y} /\ Q x}`] THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN MATCH_MP_TAC FINITE_POWERSET THEN
    ASM_SIMP_TAC[FINITE_RESTRICT];
    MAP_EVERY (C UNDISCH_THEN (K ALL_TAC))
     [`?c d:real^N->bool.
         c IN t /\ d IN t /\ k face_of c /\ k face_of d /\ ~(c = d)`;
      `?c:real^N->bool. c IN t /\ k face_of c`]] THEN
  REWRITE_TAC[HAS_SIZE_CONV `s HAS_SIZE 2`; IN_ELIM_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[MESON[] `(!a b c. P a b c) <=> (!b c a. P a b c)`] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ ~q /\ r ==> s <=> r ==> p /\ ~q ==> s`] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N->bool`; `d:real^N->bool`] THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `convex hull {v:real^N | v extreme_point_of c} = c /\
    convex hull {v:real^N | v extreme_point_of d} = d /\
    convex hull {v:real^N | v extreme_point_of k} = k`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
    (CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_IMP_CONVEX;
      MATCH_MP_TAC POLYTOPE_IMP_COMPACT]) THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; FACE_OF_POLYTOPE_POLYTOPE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?a b:real^N. ~(a IN k) /\ ~(b IN k) /\
                 a INSERT {v | v extreme_point_of k} =
                 {v | v extreme_point_of c} /\
                 b INSERT {v | v extreme_point_of k} =
                 {v | v extreme_point_of d}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> (p /\ r) /\ (q /\ s)`] THEN
    REWRITE_TAC[LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
     [MP_TAC(HAS_SIZE_CONV
       `({v | v extreme_point_of c} DIFF {v:real^N | v extreme_point_of k})
        HAS_SIZE 1`);
      MP_TAC(HAS_SIZE_CONV
       `({v | v extreme_point_of d} DIFF {v:real^N | v extreme_point_of k})
        HAS_SIZE 1`)] THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
    (CONJ_TAC THENL
     [MATCH_MP_TAC(MESON[HAS_SIZE; CARD_DIFF; FINITE_DIFF]
       `FINITE s /\ t SUBSET s /\ CARD s - CARD t = 1
        ==> (s DIFF t) HAS_SIZE 1`) THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[FINITE_POLYHEDRON_EXTREME_POINTS;
                      SIMPLEX_IMP_POLYHEDRON];
        ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        ASM_MESON_TAC[EXTREME_POINT_OF_FACE];
        DISCH_TAC] THEN
      MATCH_MP_TAC(ARITH_RULE
       `!n. x = n /\ y = n - 1 /\ 2 <= n ==> x - y = 1`) THEN
      EXISTS_TAC `dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_SUB;
                   ARITH_RULE `2 <= n ==> 1 <= n`] THEN
      CONJ_TAC THEN MATCH_MP_TAC(INT_ARITH
       `x - &1:int = y - &1 ==> x = y`) THEN
      W(MP_TAC o PART_MATCH (rand o rand) AFF_DIM_AFFINE_INDEPENDENT o
            lhand o snd) THEN
      REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM AFF_DIM_CONVEX_HULL] THEN
      ASM_REWRITE_TAC[] THENL
       [ASM_MESON_TAC[SIMPLEX_EXTREME_POINTS; AFF_DIM_SIMPLEX];
        REWRITE_TAC[INT_ARITH `x:int = y - &1 - &1 <=> y - &2 = x`]] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
      ASM_MESON_TAC[SIMPLEX_EXTREME_POINTS];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
      DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
       `s DIFF t = {a} ==> t SUBSET s ==> a INSERT t = s`)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        ASM_MESON_TAC[EXTREME_POINT_OF_FACE];
        SIMP_TAC[]] THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[] THEN DISCH_TAC THEN
      DISCH_THEN(MP_TAC o AP_TERM
       `(hull) convex:(real^N->bool)->real^N->bool`) THEN
      MATCH_MP_TAC(SET_RULE
       `!k. k SUBSET c /\ ~(k = c) /\ t SUBSET k ==> t = c ==> F`) THEN
      EXISTS_TAC `k:real^N->bool` THEN
      ASM_SIMP_TAC[FACE_OF_IMP_SUBSET] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[AFF_DIM_SIMPLEX; INT_ARITH `~(x - &2:int = x - &1)`];
        MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[INSERT_SUBSET] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        ASM_MESON_TAC[extreme_point_of; face_of]]]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?A:real^N^N.
        rows A = {v | v extreme_point_of c} /\
        {row i A | i IN 1..dimindex(:N) /\ ~(i = 1)} =
        {v | v extreme_point_of k}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{v:real^N | v extreme_point_of c}`; `a:real^N`]
        FINITE_INDEX_NUMSEG_SPECIAL) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      ASM_MESON_TAC[SIMPLEX_EXTREME_POINTS];
      DISCH_THEN(X_CHOOSE_THEN `f:num->real^N` MP_TAC)] THEN
    SUBGOAL_THEN
     `CARD {v:real^N | v extreme_point_of c} = dimindex(:N)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
      ONCE_REWRITE_TAC[INT_ARITH `c:int = n <=> c = (n - &1) + &1`] THEN
      ASM_MESON_TAC[SIMPLEX_EXTREME_POINTS];
      STRIP_TAC] THEN
    EXISTS_TAC `(lambda i. f i):real^N^N` THEN
    ASM_REWRITE_TAC[rows; row; LAMBDA_ETA] THEN CONJ_TAC THENL
     [REWRITE_TAC[SIMPLE_IMAGE; GSYM IN_NUMSEG] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
      SIMP_TAC[LAMBDA_BETA; IN_NUMSEG];
      MATCH_MP_TAC(SET_RULE
       `!a. (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
            z IN s /\ ~(a IN k) /\ a INSERT k = IMAGE f s /\ f z = a
            ==> {f x | x IN s /\ ~(x = z)} = k`) THEN
      EXISTS_TAC `a:real^N` THEN
      SIMP_TAC[LAMBDA_BETA; IMP_CONJ; IN_NUMSEG; LE_REFL; DIMINDEX_GE_1] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[IN_NUMSEG]; ALL_TAC] THEN
      ASM_REWRITE_TAC[extreme_point_of] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
      SIMP_TAC[LAMBDA_BETA; IN_NUMSEG]];
    ALL_TAC] THEN
  ABBREV_TAC `B:real^N^N = lambda i. if i = 1 then b else (A:real^N^N)$i` THEN
  SUBGOAL_THEN `rows(B:real^N^N) = {v | v extreme_point_of d}`
  ASSUME_TAC THENL
   [SIMP_TAC[rows; GSYM IN_NUMSEG] THEN MATCH_MP_TAC(SET_RULE
     `1 IN k /\ f 1 INSERT {f i | i IN k /\ ~(i = 1)} = s
      ==> {f i | i IN k} = s`) THEN
    EXPAND_TAC "B" THEN
    SIMP_TAC[row; IN_NUMSEG; LE_REFL; DIMINDEX_GE_1;
             LAMBDA_ETA; LAMBDA_BETA] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `b INSERT k = d ==> l = k ==> b INSERT l = d`)) THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[IN_NUMSEG; GSYM CONJ_ASSOC] THEN MATCH_MP_TAC(SET_RULE
     `(!x. P x ==> f x = g x) ==> {f x | P x} = {g x | P x}`) THEN
    SIMP_TAC[LAMBDA_BETA; row; LAMBDA_ETA];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`B:real^N^N`; `f:real^N->real^N`; `d:real^N->bool`]
        RELATIVE_ORIENTATION) THEN
  MP_TAC(ISPECL
   [`A:real^N^N`; `f:real^N->real^N`; `c:real^N->bool`]
        RELATIVE_ORIENTATION) THEN
  ASM_REWRITE_TAC[] THEN
  REPLICATE_TAC 2 (DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
   `x = y ==> ~(x = &0) ==> ~(y = &0)`)) THEN
  ASM_SIMP_TAC[REAL_SGN_EQ; REAL_DIV_EQ_0; DE_MORGAN_THM] THEN STRIP_TAC) THEN
  MP_TAC(ISPECL
   [`maprows (f:real^N->real^N) B`; `z:real^N`; `1`]
        main_lemma) THEN
  MP_TAC(ISPECL
   [`maprows (f:real^N->real^N) A`; `z:real^N`; `1`]
        main_lemma) THEN
  ASM_REWRITE_TAC[LE_REFL; DIMINDEX_GE_1] THEN
  ASM_REWRITE_TAC[ROWS_MAPROWS; GSYM vertex_image] THEN
  SUBGOAL_THEN
   `convex hull {row i (maprows (f:real^N->real^N) A) |
                 i IN 1..dimindex (:N) /\ ~(i = 1)} = vertex_image f k /\
    convex hull {row i (maprows (f:real^N->real^N) B) |
                 i IN 1..dimindex (:N) /\ ~(i = 1)} = vertex_image f k`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MATCH_MP_TAC(MESON[] `x = y /\ x = a ==> x = a /\ y = a`) THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
       `(!x. P x ==> f x = g x) ==> {f x | P x} = {g x | P x}`) THEN
      EXPAND_TAC "B" THEN
      SIMP_TAC[LAMBDA_BETA; row; LAMBDA_ETA; maprows; IN_NUMSEG];
      REWRITE_TAC[vertex_image] THEN AP_TERM_TAC THEN FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
      SIMP_TAC[IN_ELIM_THM; IN_NUMSEG; ROW_MAPROWS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `z IN relative_interior (conic hull vertex_image (f:real^N->real^N) k)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `conic hull vertex_image (f:real^N->real^N) k`
        RELATIVE_FRONTIER_OF_POLYHEDRON_ALT) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC POLYHEDRON_CONIC_HULL_POLYTOPE THEN
      REWRITE_TAC[vertex_image] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
      MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_POLYHEDRON_EXTREME_POINTS THEN
      MATCH_MP_TAC FACE_OF_POLYHEDRON_POLYHEDRON THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYHEDRON];
      DISCH_THEN(MP_TAC o SPEC `z:real^N` o
        GEN_REWRITE_RULE I [EXTENSION])] THEN
    ASM_SIMP_TAC[relative_frontier; REWRITE_RULE[SUBSET] CLOSURE_SUBSET;
                 IN_DIFF] THEN
    MATCH_MP_TAC(TAUT `~q ==> (~p <=> q) ==> p`) THEN
    REWRITE_TAC[IN_UNIONS; NOT_EXISTS_THM; IN_ELIM_THM] THEN
    X_GEN_TAC `f:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^N->bool`; `f:real^N->bool`]) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FACE_OF_TRANS THEN
      EXISTS_TAC `conic hull vertex_image (f:real^N->real^N) k` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FACE_OF_CONIC_HULL THEN
      SUBGOAL_THEN
       `~(dependent (IMAGE (f:real^N->real^N) {v | v extreme_point_of c}))`
      MP_TAC THENL
       [FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (funpow 3 RAND_CONV) [SYM th]) THEN
        REWRITE_TAC[GSYM ROWS_MAPROWS] THEN
        ASM_MESON_TAC[DET_DEPENDENT_ROWS];
        REWRITE_TAC[DEPENDENT_AFFINE_DEPENDENT_CASES; DE_MORGAN_THM] THEN
        STRIP_TAC] THEN
      ASM_REWRITE_TAC[vertex_image; AFFINE_HULL_CONVEX_HULL] THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN EXISTS_TAC
         `IMAGE (f:real^N->real^N) {v:real^N | v extreme_point_of k}` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      ASM_MESON_TAC[EXTREME_POINT_OF_FACE];
      MATCH_MP_TAC(INT_ARITH
       `!y:int. x < y /\ y <= z - &1 ==> x <= z - &2`) THEN
      EXISTS_TAC `aff_dim(conic hull vertex_image (f:real^N->real^N) k)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[vertex_image] THEN
        SIMP_TAC[CONVEX_CONIC_HULL; CONVEX_CONVEX_HULL];
        ALL_TAC] THEN
      REWRITE_TAC[AFF_DIM_CONIC_HULL] THEN MATCH_MP_TAC(INT_ARITH
       `x:int <= n - &2 ==> (if p then x else x + &1) <= n - &1`) THEN
      REWRITE_TAC[AFF_DIM_CONVEX_HULL; vertex_image] THEN
      SUBGOAL_THEN `FINITE {v:real^N | v extreme_point_of k}` ASSUME_TAC THENL
       [MATCH_MP_TAC FINITE_POLYHEDRON_EXTREME_POINTS THEN
        MATCH_MP_TAC FACE_OF_POLYHEDRON_POLYHEDRON THEN
        ASM_MESON_TAC[SIMPLEX_IMP_POLYHEDRON];
        ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) AFF_DIM_LE_CARD o lhand o snd) THEN
      ASM_SIMP_TAC[FINITE_IMAGE] THEN MATCH_MP_TAC(INT_ARITH
       `c:int < b ==> x <= c - &1 ==> x <= b - &2`) THEN
      REWRITE_TAC[INT_OF_NUM_LT] THEN
      TRANS_TAC LET_TRANS `CARD {v:real^N | v extreme_point_of k}` THEN
      ASM_SIMP_TAC[CARD_IMAGE_LE] THEN REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
      MATCH_MP_TAC(INT_ARITH `x - &1:int <= y - &2 ==> x < y`) THEN
      MP_TAC(ISPEC `{v:real^N | v extreme_point_of k}`
        AFF_DIM_AFFINE_INDEPENDENT) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
        EXISTS_TAC `{v:real^N | v extreme_point_of d}` THEN CONJ_TAC THENL
         [ASM_MESON_TAC[SIMPLEX_EXTREME_POINTS];
          MP_TAC(ISPECL [`k:real^N->bool`; `d:real^N->bool`]
           EXTREME_POINT_OF_FACE) THEN
          ASM_SIMP_TAC[] THEN SET_TAC[]];
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
       `x:int = n - &2 ==> x = y ==> y <= n - &2`)) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM AFF_DIM_CONVEX_HULL] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
      ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE; SIMPLEX_IMP_POLYTOPE;
                    POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_COMPACT]];
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[IN_BALL; TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `e1:real` THEN STRIP_TAC THEN
  X_GEN_TAC `e2:real` THEN STRIP_TAC THEN
  EXISTS_TAC `ball(z:real^N,e1) INTER ball(z,e2)` THEN
  SIMP_TAC[OPEN_INTER; OPEN_BALL; IN_INTER] THEN
  ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; IN_UNIV; IN_DIFF; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[IN_SING] THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`B:real^N^N`; `f:real^N->real^N`; `d:real^N->bool`]
        RELATIVE_ORIENTATION) THEN
  MP_TAC(ISPECL [`A:real^N^N`; `f:real^N->real^N`; `c:real^N->bool`]
        RELATIVE_ORIENTATION) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_ADD_RID] THEN
  SUBGOAL_THEN
   `!w:real^N. det(lambda i. if i = 1 then w else maprows f B$i) =
               det(lambda i. if i = 1 then w else maprows f A$i)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "B" THEN
    SIMP_TAC[CART_EQ; maprows; LAMBDA_BETA; LAMBDA_ETA];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(x IN frontier(conic hull vertex_image (f:real^N->real^N) c)) /\
    ~(y IN frontier(conic hull vertex_image (f:real^N->real^N) c))`
  MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[frontier; IN_DIFF] THEN
  DISCH_THEN(CONJUNCTS_THEN (MP_TAC o MATCH_MP (SET_RULE
   `~(x IN closure s /\ ~(x IN t))
    ==> s SUBSET closure s ==> ~(x IN s /\ ~(x IN t))`))) THEN
  ASM_SIMP_TAC[CLOSURE_SUBSET; IMP_IMP] THEN
  ASM_CASES_TAC
   `det(lambda i. if i = 1 then x:real^N else maprows f A$i) = &0` THEN
  ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_LT_REFL; REAL_LE_REFL] THEN
  ASM_CASES_TAC
   `det(lambda i. if i = 1 then y:real^N else maprows f A$i) = &0` THEN
  ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_LT_REFL; REAL_LE_REFL] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[GSYM real_div] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SGN_INEQS] THEN REWRITE_TAC[REAL_SGN_DIV] THEN
  SUBGOAL_THEN
   `real_sgn(det(B:real^N^N)) / real_sgn(det(A:real^N^N)) <= &0`
  MP_TAC THENL
   [ALL_TAC;
    MP_TAC(SPEC `det (maprows (f:real^N->real^N) B)` REAL_SGN_CASES) THEN
    MP_TAC(SPEC `det (maprows (f:real^N->real^N) A)` REAL_SGN_CASES) THEN
    MP_TAC(SPEC `det (B:real^N^N)` REAL_SGN_CASES) THEN
    MP_TAC(SPEC `det (A:real^N^N)` REAL_SGN_CASES) THEN
    MP_TAC(SPEC
     `det(lambda i.  if i = 1 then y else maprows (f:real^N->real^N) A$i)`
     REAL_SGN_CASES) THEN
    MP_TAC(SPEC
     `det(lambda i.  if i = 1 then x else maprows (f:real^N->real^N) A$i)`
     REAL_SGN_CASES) THEN
    ASM_REWRITE_TAC[CONJUNCT1 REAL_SGN_EQ] THEN
    REPLICATE_TAC 6 STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  SUBGOAL_THEN `~(relative_interior(conic hull k):real^N->bool = {})`
  MP_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    W(MP_TAC o PART_MATCH (lhs o rand) AFF_DIM_RELATIVE_INTERIOR o
      lhand o lhand o snd) THEN
    REWRITE_TAC[NOT_IMP] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[CONVEX_CONIC_HULL; FACE_OF_IMP_CONVEX]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[AFF_DIM_CONIC_HULL; AFF_DIM_EMPTY] THEN
    MATCH_MP_TAC(INT_ARITH
     `&2:int <= x ==> ~((if p then x - &2 else x - &2 + &1) = -- &1)`) THEN
    ASM_REWRITE_TAC[INT_OF_NUM_LE];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `w:real^N`)] THEN
  MP_TAC(ISPECL [`B:real^N^N`; `w:real^N`; `1`] main_lemma) THEN
  MP_TAC(ISPECL [`A:real^N^N`; `w:real^N`; `1`] main_lemma) THEN
  ASM_REWRITE_TAC[LE_REFL; DIMINDEX_GE_1] THEN
  SUBGOAL_THEN
   `{row i (B:real^N^N) | i IN 1..dimindex(:N) /\ ~(i = 1)} =
    {row i (A:real^N^N) | i IN 1..dimindex(:N) /\ ~(i = 1)}`
   (fun th -> ASM_REWRITE_TAC[th])
  THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x. P x ==> f x = g x) ==> {f x | P x} = {g x | P x}`) THEN
    EXPAND_TAC "B" THEN SIMP_TAC[IN_NUMSEG; row; LAMBDA_BETA; LAMBDA_ETA];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; RIGHT_IMP_FORALL_THM]] THEN
  MAP_EVERY X_GEN_TAC [`d1:real`; `d2:real`] THEN
  SUBGOAL_THEN `(w:real^N) IN frontier(interior(conic hull c))` MP_TAC THENL
   [REWRITE_TAC[frontier; INTERIOR_INTERIOR] THEN
    SUBGOAL_THEN
     `closure(interior(conic hull c)):real^N->bool = closure(conic hull c)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CONVEX_CLOSURE_INTERIOR THEN
      ONCE_REWRITE_TAC[TAUT `p /\ q <=> p /\ (p ==> q)`] THEN
      SIMP_TAC[GSYM AFF_DIM_NONEMPTY_INTERIOR_EQ] THEN
      ASM_SIMP_TAC[AFF_DIM_CONIC_HULL] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONVEX_CONIC_HULL; SIMPLEX_IMP_CONVEX]; DISCH_TAC] THEN
      SUBGOAL_THEN `aff_dim(c:real^N->bool) = &(dimindex(:N)) - &1`
      MP_TAC THENL [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
      REWRITE_TAC[GSYM AFF_DIM_EQ_MINUS1] THEN
      UNDISCH_TAC `2 <= dimindex(:N)` THEN
      REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC;
      REWRITE_TAC[GSYM frontier] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (SET_RULE `z IN relative_interior s
                  ==> relative_interior s SUBSET s /\ s SUBSET t
                      ==> z IN t`)) THEN
      REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN
      MATCH_MP_TAC FACE_OF_SUBSET_FRONTIER_AFF_DIM THEN
      ASM_SIMP_TAC[AFF_DIM_CONIC_HULL] THEN
      CONJ_TAC THENL [ALL_TAC; CONV_TAC INT_ARITH] THEN
      MATCH_MP_TAC FACE_OF_CONIC_HULL THEN ASM_MESON_TAC[]];
    REWRITE_TAC[frontier; IN_DIFF] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] CLOSURE_APPROACHABLE] THEN
  ASM_CASES_TAC `&0 < d1` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `&0 < d2` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `min d1 d2:real`) THEN
  ASM_REWRITE_TAC[IN_BALL; LEFT_IMP_EXISTS_THM; REAL_LT_MIN] THEN
  X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
  REPEAT(DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
         STRIP_TAC) THEN
  ASM_CASES_TAC `real_sgn(det(B:real^N^N)) = real_sgn(det(A:real^N^N))` THENL
   [ALL_TAC;
    MP_TAC(SPEC `det (B:real^N^N)` REAL_SGN_CASES) THEN
    MP_TAC(SPEC `det (A:real^N^N)` REAL_SGN_CASES) THEN
    ASM_REWRITE_TAC[CONJUNCT1 REAL_SGN_EQ] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN
   `(v:real^N) IN interior(conic hull c) /\ v IN interior(conic hull d)`
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (MESON[REAL_SGN_INEQS]
       `&0 < x ==> real_sgn x = real_sgn y ==> &0 < y`)) THEN
    ASM_REWRITE_TAC[REAL_SGN_DIV] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ONCE_REWRITE_TAC[CART_EQ] THEN
    EXPAND_TAC "B" THEN SIMP_TAC[LAMBDA_BETA];
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`)] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `v IN interior c /\ v IN interior d
    ==> interior c SUBSET relative_interior c /\
        interior d SUBSET relative_interior d
        ==> ~(relative_interior c INTER relative_interior d = {})`)) THEN
  REWRITE_TAC[INTERIOR_SUBSET_RELATIVE_INTERIOR] THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_CONIC_HULL] THEN
  MATCH_MP_TAC(SET_RULE
   `s INTER t SUBSET {a} ==> (s DELETE a) INTER (t DELETE a) = {}`) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
    [`relative_interior c:real^N->bool`; `relative_interior d:real^N->bool`;
     `u:real^N->bool`] INTER_CONIC_HULL_SUBSETS_CONVEX_RELATIVE_FRONTIER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REWRITE_RULE[SUBSET] INTERIOR_SUBSET_RELATIVE_INTERIOR] THEN
    MATCH_MP_TAC(SET_RULE
     `relative_interior c SUBSET c /\ relative_interior d SUBSET d /\
      relative_frontier u = frontier u /\
      c SUBSET frontier u /\ d SUBSET frontier u
      ==> relative_interior c UNION relative_interior d SUBSET
          relative_frontier u`) THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[EMPTY_SUBSET] THEN
  COND_CASES_TAC THEN REWRITE_TAC[SUBSET_REFL] THEN
  MATCH_MP_TAC(SET_RULE `s = {} ==> s SUBSET a`) THEN
  REWRITE_TAC[CONIC_HULL_EQ_EMPTY] THEN
  UNDISCH_TAC `~(c:real^N->bool = d)` THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `c:real^N->bool`; `d:real^N->bool`]
        TRIANGULATION_DISJOINT_RELATIVE_INTERIORS) THEN
  MAP_EVERY (MP_TAC o C ISPEC RELATIVE_INTERIOR_SUBSET)
   [`c:real^N->bool`; `d:real^N->bool`] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Degree of a linear mapping.                                               *)
(* ------------------------------------------------------------------------- *)

let BROUWER_DEGREE3_LINEAR_GEN = prove
 (`!f:real^N->real^N t y.
        FINITE t /\
        (!c. c IN t ==> &(dimindex (:N)) - &1 simplex c) /\
        (!c. c IN t ==> ~(vec 0 IN affine hull c)) /\
        linear f
        ==> brouwer_degree3(y,t,f) =
            real_sgn(det(matrix f)) *
            &(CARD {c | c IN t /\ y IN conic hull (vertex_image f c)})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[brouwer_degree3] THEN
  TRANS_TAC EQ_TRANS
   `sum {c | c IN t /\ y IN conic hull (vertex_image f c)}
        (\c:real^N->bool. real_sgn (det (matrix f)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RELATIVE_ORIENTATION_LINEAR THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC(ONCE_REWRITE_RULE[REAL_MUL_SYM] SUM_CONST) THEN
    ASM_SIMP_TAC[FINITE_RESTRICT]]);;

let BROUWER_DEGREE3_LINEAR = prove
 (`!f:real^N->real^N t u y.
        convex u /\ bounded u /\ vec 0 IN interior u /\
        triangulation t /\ UNIONS t = frontier u /\
        (!c. c IN t ==> &(dimindex (:N)) - &1 simplex c) /\
        linear f /\
        (!c. c IN t ==> ~(y IN frontier(conic hull (vertex_image f c))))
        ==> brouwer_degree3(y,t,f) = real_sgn(det(matrix f))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `FINITE(t:(real^N->bool)->bool)` THENL
   [ALL_TAC; ASM_MESON_TAC[triangulation]] THEN
  SUBGOAL_THEN `!c:real^N->bool. c IN t ==> ~(vec 0 IN affine hull c)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[NOT_IN_AFFINE_HULL_SURFACE_TRIANGULATION; SUBSET_REFL];
    ASM_SIMP_TAC[BROUWER_DEGREE3_LINEAR_GEN]] THEN
  REWRITE_TAC[REAL_RING `x * a = x <=> ~(x = &0) ==> a = &1`] THEN
  ASM_SIMP_TAC[REAL_SGN_EQ; DET_MATRIX_EQ_0_LEFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `g:real^N->real^N`]
        LINEAR_INVERSE_LEFT) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_EQ] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{c | c IN t /\ y IN conic hull vertex_image f c} =
    {c | c IN t /\ (g:real^N->real^N) y IN conic hull c}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `c:real^N->bool` THEN
    ASM_CASES_TAC `(c:real^N->bool) IN t` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CONIC_HULL_VERTEX_IMAGE_LINEAR] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. f(g x) = x) /\ (!y. g(f y) = y)
      ==> (y IN IMAGE f s <=> g y IN s)`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[HAS_SIZE] `s HAS_SIZE 1 ==> CARD s = 1`) THEN
  CONV_TAC HAS_SIZE_CONV THEN
  REWRITE_TAC[SET_RULE `(?a. s = {a}) <=> ?!a. a IN s`; IN_ELIM_THM] THEN
  MATCH_MP_TAC NONBOUNDARY_IN_UNIQUE_CONIC_HULL_SIMPLEX THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `!c. c IN t ==> ~((y:real^N) IN frontier(conic hull vertex_image f c))` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `c:real^N->bool` THEN
  ASM_CASES_TAC `(c:real^N->bool) IN t` THEN ASM_SIMP_TAC[CONTRAPOS_THM] THEN
  ASM_SIMP_TAC[VERTEX_IMAGE_LINEAR; CONIC_HULL_LINEAR_IMAGE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM]) THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) FRONTIER_BIJECTIVE_LINEAR_IMAGE o
    rand o snd) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Point-independent version of degree and its homotopy invariance.          *)
(* ------------------------------------------------------------------------- *)

let brouwer_degree2 = new_definition
 `brouwer_degree2(t,f) =
    let x = @x. !c. c IN t ==> ~(x IN frontier(conic hull vertex_image f c)) in
    brouwer_degree3(x,t,f)`;;

let BROUWER_DEGREE2_HOMOTOPY_INVARIANCE_LEMMA = prove
 (`!f g:real^N->real^N.
        2 <= dimindex(:N) /\
        homotopic_with (\x. T)
          (subtopology euclidean ((:real^N) DELETE vec 0),
           subtopology euclidean ((:real^N) DELETE vec 0)) f g
        ==> ?u t. convex u /\ bounded u /\ vec 0 IN interior u /\
                  triangulation t /\ UNIONS t = frontier u /\
                  (!c. c IN t ==> &(dimindex (:N)) - &1 simplex c) /\
                  brouwer_degree2(t,f) = brouwer_degree2(t,g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `vec 0:real^N` CHOOSE_SURROUNDING_SIMPLEX_FULL) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR_CBALL]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  EXISTS_TAC `u:real^N->bool` THEN REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_BOUNDED]; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMOTOPIC_WITH_EUCLIDEAN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,N)finite_sum->real^N`
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^N. x IN frontier u ==> r <= norm(x)` ASSUME_TAC THENL
   [REWRITE_TAC[frontier] THEN MATCH_MP_TAC(SET_RULE
     `(!x. ~(P x) ==> x IN i) ==> (!x. x IN c DIFF i ==> P x)`) THEN
    REWRITE_TAC[NORM_ARITH `~(r <= norm x) <=> dist(vec 0:real^N,x) < r`] THEN
    REWRITE_TAC[GSYM IN_BALL; GSYM SUBSET; GSYM INTERIOR_CBALL] THEN
    ASM_SIMP_TAC[SUBSET_INTERIOR];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((vec 0:real^N) IN frontier u)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_0; REAL_NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?R. &0 < R /\
        !t x. t IN interval[vec 0,vec 1] /\ x IN frontier u
              ==> R <= norm((h:real^(1,N)finite_sum->real^N) (pastecart t x))`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `setdist({vec 0},IMAGE (h:real^(1,N)finite_sum->real^N)
                        (interval[vec 0,vec 1] PCROSS frontier u))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
      REWRITE_TAC[SETDIST_POS_LE; SETDIST_EQ_0_SING] THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY; PCROSS_EQ_EMPTY; UNIT_INTERVAL_NONEMPTY] THEN
      REWRITE_TAC[DE_MORGAN_THM; FRONTIER_EQ_EMPTY] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[NOT_IN_EMPTY; INTERIOR_EMPTY];
        ASM_MESON_TAC[NOT_BOUNDED_UNIV];
        MATCH_MP_TAC(SET_RULE
         `(!x. x IN s ==> ~(h x = a)) /\ closure(IMAGE h s) = IMAGE h s
          ==> ~(a IN closure(IMAGE h s))`) THEN
        CONJ_TAC THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE;
               FORALL_PASTECART; PASTECART_IN_PCROSS]) THEN
          SIMP_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN ASM SET_TAC[];
          REWRITE_TAC[CLOSURE_EQ] THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
          MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
          ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL;
                       COMPACT_FRONTIER_BOUNDED] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
          ASM SET_TAC[]]];
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[NORM_ARITH `norm(x:real^N) = dist(vec 0,x)`] THEN
      MATCH_MP_TAC SETDIST_LE_DIST THEN
      SIMP_TAC[IN_SING; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(h:real^(1,N)finite_sum->real^N) uniformly_continuous_on
    interval[vec 0,vec 1] PCROSS frontier u`
  ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN
    ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL;
                 COMPACT_FRONTIER_BOUNDED] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [uniformly_continuous_on]) THEN
  DISCH_THEN(MP_TAC o SPEC `R / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`{f:real^N->bool | f facet_of u}`; `&(dimindex(:N)) - &1:int`;
    `min (&1 / &2) e`]
   FINE_TRIANGULAR_SUBDIVISION_OF_CELL_COMPLEX) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_HALF] THEN ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP TRIANGULATION_SIMPLEX_FACETS) THEN
    REWRITE_TAC[triangulation; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[facet_of] THEN
    ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE; SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP RELATIVE_FRONTIER_OF_POLYHEDRON o
    MATCH_MP SIMPLEX_IMP_POLYHEDRON) THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [AFF_DIM_EQ_FULL]) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_FRONTIER] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:(real^N->bool)->bool` THEN
  REPLICATE_TAC 4 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX; triangulation]; DISCH_TAC] THEN
  SUBGOAL_THEN `FINITE(t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[triangulation]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c a. a IN interval[vec 0,vec 1] /\ c IN t
          ==> ~(vec 0 IN vertex_image
                  ((h:real^(1,N)finite_sum->real^N) o pastecart a) c)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `~(vertex_image ((h:real^(1,N)finite_sum->real^N) o pastecart a) c = {})`
    MP_TAC THENL [ASM_MESON_TAC[VERTEX_IMAGE_NONEMPTY]; ALL_TAC] THEN
    REWRITE_TAC[vertex_image; CONVEX_HULL_EQ_EMPTY] THEN
    SIMP_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `w:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:real^(1,N)finite_sum->real^N) (pastecart a w) IN
                  vertex_image (h o pastecart a) c`
    MP_TAC THENL
     [REWRITE_TAC[vertex_image] THEN MATCH_MP_TAC HULL_INC THEN
      REWRITE_TAC[IN_IMAGE; o_THM; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[GSYM vertex_image]] THEN
    MATCH_MP_TAC(MESON[REAL_LT_REFL]
     `(w IN s ==> (!x. x IN s ==> dist(x,w) < dist(z,w)))
      ==> w IN s ==> ~(z IN s)`) THEN
    DISCH_TAC THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `!r. &0 < r /\ x <= r / &2 /\ r <= y ==> x < y`) THEN
    EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[DIST_0] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[extreme_point_of]) THEN ASM SET_TAC[]] THEN
    TRANS_TAC REAL_LE_TRANS
      `diameter(vertex_image
        ((h:real^(1,N)finite_sum->real^N) o pastecart a) c)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[dist] THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
      ASM_MESON_TAC[POLYTOPE_VERTEX_IMAGE; POLYTOPE_IMP_BOUNDED];
      ALL_TAC] THEN
    REWRITE_TAC[vertex_image; DIAMETER_CONVEX_HULL] THEN
    MATCH_MP_TAC DIAMETER_LE THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(NORM_ARITH `dist(x:real^N,y) < r ==> norm(x - y) <= r`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[DIST_PASTECART_CANCEL; PASTECART_IN_PCROSS] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[extreme_point_of]) THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    TRANS_TAC REAL_LET_TRANS `diameter(c:real^N->bool)` THEN
    ASM_SIMP_TAC[dist] THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_BOUNDED];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\t:real^1. T`;
    `\a b. brouwer_degree2(t,(h:real^(1,N)finite_sum->real^N) o pastecart a) =
           brouwer_degree2(t,(h:real^(1,N)finite_sum->real^N) o pastecart b)`;
    `interval[vec 0:real^1,vec 1]`]
   CONNECTED_EQUIVALENCE_RELATION_GEN) THEN
  REWRITE_TAC[CONNECTED_INTERVAL] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPECL [`vec 0:real^1`; `vec 1:real^1`]) THEN
    ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; o_DEF; ETA_AX]] THEN
  REPEAT(CONJ_TAC THENL [MESON_TAC[]; ALL_TAC]) THEN
  X_GEN_TAC `a:real^1` THEN STRIP_TAC THEN
  ABBREV_TAC
   `z = @x. !k. k IN t ==> ~(x IN frontier (conic hull vertex_image
                     ((h:real^(1,N)finite_sum->real^N) o pastecart a) k))` THEN
  MP_TAC(ISPECL
   [`(h:real^(1,N)finite_sum->real^N) o pastecart a`;
    `t:(real^N->bool)->bool`; `z:real^N`]
   BROUWER_DEGREE3_PERTURB) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN EXPAND_TAC "z" THEN CONV_TAC SELECT_CONV THEN
    ONCE_REWRITE_TAC[SET_RULE `(?x. P x) <=> ~({x | P x} = {})`] THEN
    MATCH_MP_TAC(MESON[CLOSURE_EMPTY; UNIV_NOT_EMPTY]
     `closure s = (:real^N) ==> ~(s = {})`) THEN
    MATCH_MP_TAC CLOSURE_CONIC_HULL_VERTEX_IMAGE_NONFRONTIERS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [uniformly_continuous_on]) THEN
  DISCH_THEN(MP_TAC o SPEC `m:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `interval[vec 0,vec 1] INTER ball(a:real^1,d)` THEN
  SIMP_TAC[OPEN_IN_OPEN_INTER; IN_INTER; OPEN_BALL; CENTRE_IN_BALL] THEN
  ASM_REWRITE_TAC[IN_BALL] THEN
  MAP_EVERY X_GEN_TAC [`b:real^1`; `c:real^1`] THEN STRIP_TAC THEN
  REWRITE_TAC[brouwer_degree2] THEN MAP_EVERY ABBREV_TAC
   [`x = @x. !k. k IN t ==> ~(x IN frontier (conic hull vertex_image
                    ((h:real^(1,N)finite_sum->real^N) o pastecart b) k))`;
    `y = @x. !k. k IN t ==> ~(x IN frontier (conic hull vertex_image
                    ((h:real^(1,N)finite_sum->real^N) o pastecart c) k))`] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(CONJ (SPEC `(h:real^(1,N)finite_sum->real^N) o pastecart b` th)
          (SPEC `(h:real^(1,N)finite_sum->real^N) o pastecart c` th))) THEN
  MATCH_MP_TAC(TAUT
   `(p /\ q) /\ (r /\ s ==> t) ==> (p ==> r) /\ (q ==> s) ==> t`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[o_DEF; GSYM dist] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; DIST_PASTECART_CANCEL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[extreme_point_of]) THEN ASM SET_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `(!k. k IN t ==> ~(x IN frontier (conic hull vertex_image
                    ((h:real^(1,N)finite_sum->real^N) o pastecart b) k))) /\
    (!k. k IN t ==> ~(y IN frontier (conic hull vertex_image
                    ((h:real^(1,N)finite_sum->real^N) o pastecart c) k)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "x"; EXPAND_TAC "y"] THEN
    CONV_TAC SELECT_CONV THEN
    ONCE_REWRITE_TAC[SET_RULE `(?x. P x) <=> ~({x | P x} = {})`] THEN
    MATCH_MP_TAC(MESON[CLOSURE_EMPTY; UNIV_NOT_EMPTY]
     `closure s = (:real^N) ==> ~(s = {})`) THEN
    MATCH_MP_TAC CLOSURE_CONIC_HULL_VERTEX_IMAGE_NONFRONTIERS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `!z. brouwer_degree3(z,t,f) = brouwer_degree3(z,t,g) /\
        brouwer_degree3(x,t,f) = brouwer_degree3(z,t,f) /\
        brouwer_degree3(y,t,g) = brouwer_degree3(z,t,g)
        ==> brouwer_degree3 (x,t,f) = brouwer_degree3(y,t,g)`) THEN
  EXISTS_TAC `z:real^N` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; CONJ_TAC] THEN
  MATCH_MP_TAC BROUWER_DEGREE3_POINT_INDEPENDENCE THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:real^N->bool` THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence the key theorem about homotopy of linear maps.                      *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_LINEAR_MAPS_IMP = prove
 (`!f g:real^N->real^N.
     linear f /\ linear g /\
     homotopic_with (\x. T)
       (subtopology euclidean ((:real^N) DELETE vec 0),
        subtopology euclidean ((:real^N) DELETE vec 0)) f g
     ==> real_sgn(det(matrix f)) = real_sgn(det(matrix g))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `2 <= dimindex(:N)` THENL
   [MP_TAC(ISPECL
     [`f:real^N->real^N`; `g:real^N->real^N`]
       BROUWER_DEGREE2_HOMOTOPY_INVARIANCE_LEMMA) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; brouwer_degree2] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `t:(real^N->bool)->bool`] THEN
    MAP_EVERY ABBREV_TAC
     [`x = @x:real^N. !k. k IN t
                   ==> ~(x IN frontier (conic hull vertex_image f k))`;
      `y = @x:real^N. !k. k IN t
                   ==> ~(x IN frontier (conic hull vertex_image g k))`] THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
    MATCH_MP_TAC BROUWER_DEGREE3_LINEAR THEN
    EXISTS_TAC `u:real^N->bool` THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
    MAP_EVERY EXPAND_TAC ["x"; "y"] THEN CONV_TAC SELECT_CONV THEN
    ONCE_REWRITE_TAC[SET_RULE `(?x. P x) <=> ~({x | P x} = {})`] THEN
    MATCH_MP_TAC(MESON[CLOSURE_EMPTY; UNIV_NOT_EMPTY]
     `closure s = (:real^N) ==> ~(s = {})`) THEN
    MATCH_MP_TAC CLOSURE_CONIC_HULL_VERTEX_IMAGE_NONFRONTIERS THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[triangulation];
    FIRST_ASSUM(MP_TAC o MATCH_MP
     (ARITH_RULE `~(2 <= n) ==> (1 <= n ==> n = 1)`)) THEN
    REWRITE_TAC[DIMINDEX_GE_1] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMOTOPIC_WITH_EUCLIDEAN]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `h:real^(1,N)finite_sum->real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`(\x. lift(x$1)) o (h:real^(1,N)finite_sum->real^N) o
       (\t. pastecart t (basis 1))`;
      `interval[vec 0:real^1,vec 1]`]
     CONNECTED_CONTINUOUS_IMAGE) THEN
    REWRITE_TAC[CONNECTED_INTERVAL] THEN ANTS_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE; CONTINUOUS_ON_ID] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST;
               CONTINUOUS_ON_ID] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
      SIMP_TAC[IN_DELETE; IN_UNIV; BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL];
      ASM_SIMP_TAC[DET_1_GEN; matrix; LAMBDA_BETA; DIMINDEX_1; ARITH] THEN
      GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[REAL_SGN_EQ_INEQ; DE_MORGAN_THM; REAL_NOT_LT] THEN
      STRIP_TAC THEN
      REWRITE_TAC[GSYM CONVEX_CONNECTED_1; CONVEX_CONTAINS_SEGMENT] THEN
      REWRITE_TAC[FORALL_IN_IMAGE_2] THEN
      DISCH_THEN(MP_TAC o SPECL [`vec 0:real^1`; `vec 1:real^1`]) THEN
      ASM_REWRITE_TAC[o_THM; ENDS_IN_UNIT_INTERVAL] THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `vec 0:real^1`) THEN
      REWRITE_TAC[NOT_IMP; IN_IMAGE] THEN CONJ_TAC THENL
       [REWRITE_TAC[SEGMENT_1; LIFT_DROP] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> q ==> ~p`] THEN
        X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
        REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV; IN_DELETE] THEN
        DISCH_THEN(MP_TAC o SPEC `pastecart (t:real^1) (basis 1:real^N)`) THEN
        ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_DELETE] THEN
        SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL] THEN
        ASM_REWRITE_TAC[CART_EQ; FORALL_1; DIMINDEX_1] THEN
        REWRITE_TAC[VEC_COMPONENT; o_DEF; CONTRAPOS_THM] THEN
        REWRITE_TAC[GSYM drop; LIFT_DROP] THEN MESON_TAC[]]]]);;

let HOMOTOPIC_LINEAR_MAPS_ALT = prove
 (`!f g:real^N->real^N.
     linear f /\ linear g /\
     homotopic_with (\x. T)
        (subtopology euclidean ((:real^N) DELETE vec 0),
         subtopology euclidean ((:real^N) DELETE vec 0)) f g
     ==> &0 < det(matrix f) * det(matrix g)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_SGN_INEQS] THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `g:real^N->real^N`]
      HOMOTOPIC_LINEAR_MAPS_IMP) THEN
  ASM_SIMP_TAC[REAL_SGN_MUL; GSYM REAL_POW_2; REAL_LT_POW_2] THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_SGN_INEQS] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `IMAGE f (UNIV DELETE a) SUBSET UNIV DELETE a
    ==> !x. f x = a ==> x = a`)) THEN
  ASM_SIMP_TAC[GSYM LINEAR_INJECTIVE_0; MATRIX_INVERTIBLE;
               GSYM INVERTIBLE_DET_NZ] THEN
  ASM_MESON_TAC[LINEAR_INJECTIVE_LEFT_INVERSE; LINEAR_INVERSE_LEFT]);;

let HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_IMP = prove
 (`!f g:real^N->real^N.
        orthogonal_transformation f /\ orthogonal_transformation g /\
        homotopic_with (\x. T)
          (subtopology euclidean (sphere (vec 0,&1)),
           subtopology euclidean (sphere (vec 0,&1))) f g
        ==> det(matrix f) = det(matrix g)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [REAL_EQ_SGN_ABS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LINEAR_MAPS_IMP THEN
    ASM_SIMP_TAC[HOMOTOPIC_WITH; ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMOTOPIC_WITH_EUCLIDEAN]) THEN
    SIMP_TAC[HOMOTOPIC_WITH; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `h:real^(1,N)finite_sum->real^N` THEN STRIP_TAC THEN
    EXISTS_TAC
     `\z. norm(sndcart z) % (h:real^(1,N)finite_sum->real^N)
            (pastecart (fstcart z) (inv(norm(sndcart z)) % sndcart z))` THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_SIMP_TAC[LINEAR_CMUL; IN_UNIV; IN_DELETE;
                 ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; NORM_EQ_0] THEN
    REWRITE_TAC[VECTOR_MUL_LID] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      SIMP_TAC[o_DEF; CONTINUOUS_ON_LIFT_NORM_COMPOSE; LINEAR_SNDCART;
               LINEAR_CONTINUOUS_ON] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
        MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; o_DEF] THEN
        MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
        SIMP_TAC[o_DEF; CONTINUOUS_ON_LIFT_NORM_COMPOSE; LINEAR_SNDCART;
               LINEAR_CONTINUOUS_ON] THEN
        SIMP_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_DELETE;
                 SNDCART_PASTECART; NORM_EQ_0];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART] THEN
        REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART;
                    SNDCART_PASTECART] THEN
        SIMP_TAC[IN_DELETE; IN_SPHERE_0; NORM_MUL; REAL_ABS_INV;
                 REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0]];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_DELETE] THEN
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_DELETE] THEN
      SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; VECTOR_MUL_EQ_0;
               NORM_EQ_0] THEN
      DISCH_THEN(fun th -> REPEAT GEN_TAC THEN STRIP_TAC THEN
        W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o rand o snd)) THEN
      ASM_SIMP_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV;
                   REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0] THEN
      CONV_TAC NORM_ARITH];
    MATCH_MP_TAC(REAL_ARITH
     `(x = &1 \/ x = -- &1) /\ (y = &1 \/ y = -- &1)
      ==> abs x = abs y`) THEN
    CONJ_TAC THEN MATCH_MP_TAC DET_ORTHOGONAL_MATRIX THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_MATRIX]]);;

(* ------------------------------------------------------------------------- *)
(* Hairy ball theorem and relatives.                                         *)
(* ------------------------------------------------------------------------- *)

let FIXPOINT_HOMOTOPIC_IDENTITY_SPHERE = prove
 (`!f:real^N->real^N.
        ODD(dimindex(:N)) /\
        homotopic_with (\x. T)
         (subtopology euclidean (sphere(vec 0,&1)),
          subtopology euclidean (sphere(vec 0,&1))) (\x. x) f
        ==> ?x. x IN sphere(vec 0,&1) /\ f x = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `\x:real^N. --x`;
                 `sphere(vec 0:real^N,&1)`; `&1`]
        HOMOTOPIC_NON_ANTIPODAL_SPHEREMAPS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[CONTINUOUS_ON_NEG; CONTINUOUS_ON_ID];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; NORM_NEG];
    ASM_MESON_TAC[VECTOR_NEG_NEG];
    DISCH_THEN(MP_TAC o SPEC `\x:real^N. x` o
     MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        HOMOTOPIC_WITH_TRANS)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
     (REWRITE_RULE[CONJ_ASSOC]
        HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_IMP))) THEN
    SIMP_TAC[ORTHOGONAL_TRANSFORMATION_NEG; ORTHOGONAL_TRANSFORMATION_ID;
             MATRIX_NEG; LINEAR_ID; DET_NEG; MATRIX_ID; DET_I] THEN
    ASM_REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE; GSYM NOT_ODD] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let FIXPOINT_OR_NEG_MAPPING_SPHERE = prove
 (`!f:real^N->real^N.
        ODD(dimindex(:N)) /\
        f continuous_on sphere(vec 0,&1) /\
        IMAGE f (sphere(vec 0,&1)) SUBSET sphere(vec 0,&1)
        ==> ?x. x IN sphere(vec 0,&1) /\ (f x = --x \/ f x = x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LEFT_OR_DISTRIB; EXISTS_OR_THM] THEN
  MATCH_MP_TAC(TAUT `(~p ==> q) ==> p \/ q`) THEN DISCH_TAC THEN
  MATCH_MP_TAC FIXPOINT_HOMOTOPIC_IDENTITY_SPHERE THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_NON_ANTIPODAL_SPHEREMAPS THEN
  ASM_REWRITE_TAC[IMAGE_ID; SUBSET_REFL; CONTINUOUS_ON_ID] THEN
  ASM_MESON_TAC[VECTOR_NEG_NEG]);;

let HAIRY_BALL_THEOREM_ALT,HAIRY_BALL_THEOREM = (CONJ_PAIR o prove)
 (`(!r. (?f. f continuous_on sphere(vec 0:real^N,r) /\
             (!x. x IN sphere(vec 0,r)
                  ==> ~(f x = vec 0) /\ orthogonal x (f x))) <=>
        r <= &0 \/ EVEN(dimindex(:N))) /\
   (!r. (?f. f continuous_on sphere(vec 0:real^N,r) /\
             IMAGE f (sphere(vec 0,r)) SUBSET sphere(vec 0,r) /\
             (!x. x IN sphere(vec 0,r)
                  ==> ~(f x = vec 0) /\ orthogonal x (f x))) <=>
        r < &0 \/ &0 < r /\ EVEN(dimindex(:N)))`,
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `r:real` THEN
  ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[SPHERE_EMPTY; NOT_IN_EMPTY; IMAGE_CLAUSES; EMPTY_SUBSET;
               CONTINUOUS_ON_EMPTY; REAL_LT_IMP_LE] THEN
  ASM_CASES_TAC `r = &0` THEN ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_REFL] THENL
   [SIMP_TAC[SPHERE_SING; FORALL_IN_INSERT; NOT_IN_EMPTY; SUBSET;
             FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL [ALL_TAC; MESON_TAC[IN_SING]] THEN
    EXISTS_TAC `(\x. basis 1):real^N->real^N` THEN
    SIMP_TAC[CONTINUOUS_ON_CONST; ORTHOGONAL_0; BASIS_NONZERO; LE_REFL;
             DIMINDEX_GE_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[GSYM REAL_NOT_LT]] THEN
  MATCH_MP_TAC(TAUT
   `(q ==> p) /\ (p ==> r) /\ (r ==> q)
    ==> (p <=> r) /\ (q <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    REWRITE_TAC[GSYM NOT_ODD] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `\x. inv(norm(f(r % x))) % (f:real^N->real^N) (r % x)`
          FIXPOINT_OR_NEG_MAPPING_SPHERE) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF] THEN
        MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE;
          X_GEN_TAC `x:real^N` THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `r % x:real^N`) THEN
          ASM_SIMP_TAC[NORM_MUL; real_abs; REAL_LT_IMP_LE; NORM_EQ_0;
                       IN_SPHERE_0; REAL_MUL_RID]];
        ALL_TAC] THEN
      ONCE_REWRITE_TAC[GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC[GSYM SPHERE_SCALING; CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID;
                   VECTOR_MUL_RZERO; REAL_MUL_RID];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN
      ASM_SIMP_TAC[NORM_MUL; real_abs; REAL_LT_IMP_LE; NORM_EQ_0;
                   IN_SPHERE_0; REAL_MUL_RID];
      REWRITE_TAC[IN_SPHERE_0; VECTOR_ARITH `a:real^N = --x <=> --a = x`] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r % x:real^N`) THEN
      ASM_SIMP_TAC[NORM_MUL; real_abs; REAL_LT_IMP_LE; NORM_EQ_0;
                   IN_SPHERE_0; REAL_MUL_RID] THEN
      ASM_SIMP_TAC[ORTHOGONAL_MUL; REAL_LT_IMP_NZ] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[ORTHOGONAL_MUL; ORTHOGONAL_LNEG; ORTHOGONAL_REFL;
                  REAL_INV_EQ_0; NORM_EQ_0] THEN
      CONV_TAC TAUT];
    REWRITE_TAC[EVEN_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    EXISTS_TAC `(\x. lambda i. if EVEN(i) then --(x$(i-1)) else x$(i+1)):
                real^N->real^N` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
      SIMP_TAC[linear; CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
               LAMBDA_BETA; REAL_NEG_ADD; GSYM REAL_MUL_RNEG] THEN
      MESON_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; GSYM DOT_EQ_0] THEN
      SIMP_TAC[orthogonal; dot; LAMBDA_BETA; NORM_EQ_SQUARE]] THEN
    SUBGOAL_THEN `1..dimindex(:N) = 2*0+1..(2 * (n - 1) + 1) + 1`
    SUBST1_TAC THENL
     [BINOP_TAC THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `m = 2 * n ==> 1 <= m ==> m = (2 * (n - 1) + 1) + 1`)) THEN
      REWRITE_TAC[DIMINDEX_GE_1];
      REWRITE_TAC[SUM_OFFSET; SUM_PAIR]] THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH; ADD_SUB] THEN
    REWRITE_TAC[REAL_ARITH `a + --x * --y:real = x * y + a`] THEN
    ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[REAL_ARITH `x + y * --z = x - z * y`; REAL_SUB_REFL; SUM_0]]);;

let CONTINUOUS_FUNCTION_HAS_EIGENVALUES_ODD_DIM = prove
 (`!f:real^N->real^N.
        ODD(dimindex(:N)) /\ f continuous_on sphere(vec 0:real^N,&1)
        ==> ?v c. v IN sphere(vec 0,&1) /\ f v = c % v`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `!v. norm v = &1 ==> ~((f:real^N->real^N) v = vec 0)` THENL
   [ALL_TAC; ASM_MESON_TAC[VECTOR_MUL_LZERO; IN_SPHERE_0]] THEN
  MP_TAC(ISPEC `\x. inv(norm(f x)) % (f:real^N->real^N) x`
        FIXPOINT_OR_NEG_MAPPING_SPHERE) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF] THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_NORM_COMPOSE; IN_SPHERE_0];
      REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^N` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM
     `(%) (norm((f:real^N->real^N) v)):real^N->real^N`)] THEN
    ASM_SIMP_TAC[VECTOR_MUL_LID; VECTOR_MUL_ASSOC; REAL_MUL_RINV; NORM_EQ_0;
                 REAL_MUL_LINV] THEN
    ASM_MESON_TAC[VECTOR_MUL_RNEG; VECTOR_MUL_LNEG]);;

let EULER_ROTATION_THEOREM_GEN = prove
 (`!A:real^N^N.
        ODD(dimindex(:N)) /\ rotation_matrix A
        ==> ?v. norm v = &1 /\ A ** v = v`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rotation_matrix]) THEN
  ASM_CASES_TAC `!v:real^N. v IN sphere (vec 0,&1) ==> ~(A ** v = v)` THENL
   [ALL_TAC; ASM_MESON_TAC[IN_SPHERE_0]] THEN
  MP_TAC(ISPECL [`\x:real^N. (A:real^N^N) ** x`; `\x:real^N. --x`;
                 `sphere(vec 0:real^N,&1)`; `&1`]
        HOMOTOPIC_NON_ANTIPODAL_SPHEREMAPS) THEN
  ASM_REWRITE_TAC[VECTOR_NEG_NEG] THEN ANTS_TAC THENL
   [SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_COMPOSE_NEG; LINEAR_ID;
             MATRIX_VECTOR_MUL_LINEAR] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; NORM_NEG] THEN
    MATCH_MP_TAC(MESON[ORTHOGONAL_TRANSFORMATION]
     `orthogonal_transformation(f:real^N->real^N)
      ==> !x. norm x = a ==> norm(f x) = a`) THEN
    ASM_REWRITE_TAC[GSYM ORTHOGONAL_MATRIX_TRANSFORMATION];
    DISCH_THEN(MP_TAC o MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
     (REWRITE_RULE[CONJ_ASSOC] HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_IMP))) THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_NEG; ORTHOGONAL_TRANSFORMATION_ID;
                 GSYM ORTHOGONAL_MATRIX_TRANSFORMATION] THEN
    SIMP_TAC[MATRIX_NEG; LINEAR_ID; MATRIX_OF_MATRIX_VECTOR_MUL] THEN
    ASM_REWRITE_TAC[MATRIX_ID; DET_NEG; DET_I; REAL_POW_NEG; GSYM NOT_ODD] THEN
    REWRITE_TAC[REAL_POW_ONE] THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* Retractions.                                                              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("retract_of",(12,"right"));;

let retraction = new_definition
  `retraction (s,t) (r:real^N->real^N) <=>
        t SUBSET s /\ r continuous_on s /\ (IMAGE r s SUBSET t) /\
        (!x. x IN t ==> (r x = x))`;;

let retract_of = new_definition
  `t retract_of s <=> ?r. retraction (s,t) r`;;

let RETRACTION_MAPS_EUCLIDEAN = prove
 (`!r s t:real^N->bool.
        retraction_maps (subtopology euclidean s,subtopology euclidean t)
                        (r,I) <=>
   retraction (s,t) r`,
  REWRITE_TAC[retraction_maps; retraction; I_DEF] THEN
  REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[CONTINUOUS_ON_ID; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IMAGE_ID] THEN
  REWRITE_TAC[CONJ_ACI]);;

let RETRACT_OF_SPACE_EUCLIDEAN = prove
 (`!s t:real^N->bool.
        t retract_of_space (subtopology euclidean s) <=> t retract_of s`,
  REWRITE_TAC[retract_of; retract_of_space; retraction] THEN
  REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; SUBTOPOLOGY_SUBTOPOLOGY] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN SET_TAC[]);;

let RETRACTION = prove
 (`!s t r. retraction (s,t) r <=>
           t SUBSET s /\
           r continuous_on s /\
           IMAGE r s = t /\
           (!x. x IN t ==> r x = x)`,
  REWRITE_TAC[retraction] THEN SET_TAC[]);;

let RETRACT_OF_IMP_EXTENSIBLE = prove
 (`!f:real^M->real^N u s t.
        s retract_of t /\ f continuous_on s /\ IMAGE f s SUBSET u
        ==> ?g. g continuous_on t /\ IMAGE g t SUBSET u /\
                (!x. x IN s ==> g x = f x)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[RETRACTION; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^M->real^M` THEN STRIP_TAC THEN
  EXISTS_TAC `(f:real^M->real^N) o (r:real^M->real^M)` THEN
  REWRITE_TAC[IMAGE_o; o_THM] THEN
  CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE; ASM SET_TAC[]] THEN
  ASM_MESON_TAC[]);;

let RETRACTION_IDEMPOTENT = prove
 (`!r s t. retraction (s,t) r ==> !x. x IN s ==> (r(r(x)) = r(x))`,
  REWRITE_TAC[retraction; SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[]);;

let IDEMPOTENT_IMP_RETRACTION = prove
 (`!f:real^N->real^N s.
        f continuous_on s /\ IMAGE f s SUBSET s /\
        (!x. x IN s ==> f(f x) = f x)
        ==> retraction (s,IMAGE f s) f`,
  REWRITE_TAC[retraction] THEN SET_TAC[]);;

let RETRACTION_SUBSET = prove
 (`!r s s' t. retraction (s,t) r /\ t SUBSET s' /\ s' SUBSET s
              ==> retraction (s',t) r`,
  SIMP_TAC[retraction] THEN
  MESON_TAC[IMAGE_SUBSET; SUBSET_TRANS; CONTINUOUS_ON_SUBSET]);;

let RETRACT_OF_SUBSET = prove
 (`!s s' t. t retract_of s /\ t SUBSET s' /\ s' SUBSET s
            ==> t retract_of s'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[retract_of; LEFT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[RETRACTION_SUBSET]);;

let RETRACT_OF_TRANSLATION = prove
 (`!a t s:real^N->bool.
        t retract_of s
        ==> (IMAGE (\x. a + x) t) retract_of (IMAGE (\x. a + x) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of; retraction] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(\x:real^N. a + x) o r o (\x:real^N. --a + x)` THEN
  ASM_SIMP_TAC[IMAGE_SUBSET; FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
     SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]) THEN
    ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `--a + a + x:real^N = x`;
                    IMAGE_ID];
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
     [GSYM IMAGE_o] THEN
    ASM_REWRITE_TAC[o_DEF; VECTOR_ARITH `--a + a + x:real^N = x`; IMAGE_ID];
    ASM_SIMP_TAC[o_DEF; VECTOR_ARITH `--a + a + x:real^N = x`]]);;

let RETRACT_OF_TRANSLATION_EQ = prove
 (`!a t s:real^N->bool.
        (IMAGE (\x. a + x) t) retract_of (IMAGE (\x. a + x) s) <=>
        t retract_of s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[RETRACT_OF_TRANSLATION] THEN
  DISCH_THEN(MP_TAC o SPEC `--a:real^N` o MATCH_MP RETRACT_OF_TRANSLATION) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID;
              VECTOR_ARITH `--a + a + x:real^N = x`]);;

add_translation_invariants [RETRACT_OF_TRANSLATION_EQ];;

let RETRACT_OF_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y) /\ t retract_of s
        ==> (IMAGE f t) retract_of (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[retract_of; retraction] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^M->real^M` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f:real^M->real^N) o r o (g:real^N->real^M)` THEN
  UNDISCH_THEN `!x y. (f:real^M->real^N) x = f y ==> x = y` (K ALL_TAC) THEN
  ASM_SIMP_TAC[IMAGE_SUBSET; FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
           ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON]) THEN
    ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID];
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
     [GSYM IMAGE_o] THEN
    ASM_REWRITE_TAC[o_DEF; IMAGE_ID];
    ASM_SIMP_TAC[o_DEF]]);;

let RETRACT_OF_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> ((IMAGE f t) retract_of (IMAGE f s) <=> t retract_of s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC; ASM_MESON_TAC[RETRACT_OF_INJECTIVE_LINEAR_IMAGE]] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `h:real^N->real^M` STRIP_ASSUME_TAC o
        MATCH_MP LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE) THEN
  SUBGOAL_THEN
   `!s. s = IMAGE (h:real^N->real^M) (IMAGE (f:real^M->real^N) s)`
   (fun th -> ONCE_REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC RETRACT_OF_INJECTIVE_LINEAR_IMAGE THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

add_linear_invariants [RETRACT_OF_LINEAR_IMAGE_EQ];;

let RETRACTION_REFL = prove
 (`!s. retraction (s,s) (\x. x)`,
  REWRITE_TAC[retraction; IMAGE_ID; SUBSET_REFL; CONTINUOUS_ON_ID]);;

let RETRACT_OF_REFL = prove
 (`!s. s retract_of s`,
  REWRITE_TAC[retract_of] THEN MESON_TAC[RETRACTION_REFL]);;

let RETRACTION_CLOSEST_POINT = prove
 (`!s t:real^N->bool.
        convex t /\ closed t /\ ~(t = {}) /\ t SUBSET s
        ==> retraction (s,t) (closest_point t)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[retraction] THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; CLOSEST_POINT_SELF;
               CLOSEST_POINT_IN_SET; CONTINUOUS_ON_CLOSEST_POINT]);;

let RETRACT_OF_IMP_SUBSET = prove
 (`!s t. s retract_of t ==> s SUBSET t`,
  SIMP_TAC[retract_of; retraction] THEN MESON_TAC[]);;

let RETRACT_OF_EMPTY = prove
 (`(!s:real^N->bool. {} retract_of s <=> s = {}) /\
   (!s:real^N->bool. s retract_of {} <=> s = {})`,
  REWRITE_TAC[retract_of; retraction; SUBSET_EMPTY; IMAGE_CLAUSES] THEN
  CONJ_TAC THEN X_GEN_TAC `s:real^N->bool` THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; IMAGE_EQ_EMPTY; CONTINUOUS_ON_EMPTY;
                  SUBSET_REFL]);;

let RETRACT_OF_SING = prove
 (`!s x:real^N. {x} retract_of s <=> x IN s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of; RETRACTION] THEN EQ_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `(\y. x):real^N->real^N` THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN ASM SET_TAC[]);;

let RETRACT_OF_OPEN_UNION = prove
 (`!s t:real^N->bool.
        open_in (subtopology euclidean (s UNION t)) s /\
        open_in (subtopology euclidean (s UNION t)) t /\
        DISJOINT s t /\ (s = {} ==> t = {})
        ==> s retract_of (s UNION t)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[RETRACT_OF_EMPTY; UNION_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN STRIP_TAC THEN
  REWRITE_TAC[retract_of; retraction] THEN
  EXISTS_TAC `\x:real^N. if x IN s then x else a` THEN
  SIMP_TAC[SUBSET_UNION] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_UNION_LOCAL_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THENL
   [EXISTS_TAC `\x:real^N. x`;
    EXISTS_TAC `(\x. a):real^N->real^N`] THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN ASM SET_TAC[]);;

let RETRACT_OF_SEPARATED_UNION = prove
 (`!s t:real^N->bool.
        s INTER closure t = {} /\ t INTER closure s = {} /\
        (s = {} ==> t = {})
        ==> s retract_of (s UNION t)`,
  REWRITE_TAC[CONJ_ASSOC; SEPARATION_OPEN_IN_UNION] THEN
  MESON_TAC[RETRACT_OF_OPEN_UNION]);;

let RETRACT_OF_CLOSED_UNION = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        DISJOINT s t /\ (s = {} ==> t = {})
        ==> s retract_of (s UNION t)`,
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> (r /\ p /\ q) /\ s`] THEN
  REWRITE_TAC[GSYM SEPARATION_CLOSED_IN_UNION] THEN
  MESON_TAC[RETRACT_OF_SEPARATED_UNION]);;

let RETRACTION_o = prove
 (`!f g s t u:real^N->bool.
        retraction (s,t) f /\ retraction (t,u) g
        ==> retraction (s,u) (g o f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retraction] THEN REPEAT STRIP_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    REWRITE_TAC[o_THM] THEN ASM SET_TAC[]]);;

let RETRACT_OF_TRANS = prove
 (`!s t u:real^N->bool.
        s retract_of t /\ t retract_of u ==> s retract_of u`,
  REWRITE_TAC[retract_of] THEN MESON_TAC[RETRACTION_o]);;

let CLOSED_IN_RETRACT = prove
 (`!s t:real^N->bool.
        s retract_of t ==> closed_in (subtopology euclidean t) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of; retraction] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `s = {x:real^N | x IN t /\ lift(norm(r x - x)) = vec 0}`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP; NORM_EQ_0] THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_SIMP_TAC[CONTINUOUS_ON_ID]]);;

let RETRACT_OF_CONTRACTIBLE = prove
 (`!s t:real^N->bool. contractible t /\ s retract_of t ==> contractible s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contractible; retract_of] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC `r:real^N->real^N`)) THEN
  SIMP_TAC[HOMOTOPIC_WITH; PCROSS; LEFT_IMP_EXISTS_THM] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [retraction]) THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `h:real^(1,N)finite_sum->real^N`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`(r:real^N->real^N) a`;
    `(r:real^N->real^N) o (h:real^(1,N)finite_sum->real^N)`] THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o; SUBSET] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ]
           CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let RETRACT_OF_COMPACT = prove
 (`!s t:real^N->bool. compact t /\ s retract_of t ==> compact s`,
  REWRITE_TAC[retract_of; RETRACTION] THEN
  MESON_TAC[COMPACT_CONTINUOUS_IMAGE]);;

let RETRACT_OF_CLOSED = prove
 (`!s t. closed t /\ s retract_of t ==> closed s`,
  MESON_TAC[CLOSED_IN_CLOSED_EQ; CLOSED_IN_RETRACT]);;

let RETRACT_OF_CONNECTED = prove
 (`!s t:real^N->bool. connected t /\ s retract_of t ==> connected s`,
  REWRITE_TAC[retract_of; RETRACTION] THEN
  MESON_TAC[CONNECTED_CONTINUOUS_IMAGE]);;

let RETRACT_OF_PATH_CONNECTED = prove
 (`!s t:real^N->bool. path_connected t /\ s retract_of t ==> path_connected s`,
  REWRITE_TAC[retract_of; RETRACTION] THEN
  MESON_TAC[PATH_CONNECTED_CONTINUOUS_IMAGE]);;

let RETRACT_OF_SIMPLY_CONNECTED = prove
 (`!s t:real^N->bool.
       simply_connected t /\ s retract_of t ==> simply_connected s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
   (REWRITE_RULE[CONJ_ASSOC] SIMPLY_CONNECTED_RETRACTION_GEN)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[IMAGE_ID; CONTINUOUS_ON_ID]);;

let RETRACT_OF_HOMOTOPICALLY_TRIVIAL = prove
 (`!s t:real^N->bool u:real^M->bool.
        t retract_of s /\
        (!f g. f continuous_on u /\ IMAGE f u SUBSET s /\
               g continuous_on u /\ IMAGE g u SUBSET s
               ==> homotopic_with (\x. T)
                     (subtopology euclidean u,subtopology euclidean s)  f g)
        ==> (!f g. f continuous_on u /\ IMAGE f u SUBSET t /\
                   g continuous_on u /\ IMAGE g u SUBSET t
                   ==> homotopic_with (\x. T)
                       (subtopology euclidean u,subtopology euclidean t) f g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> p /\ q /\ T /\ r /\ s /\ T`] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
    HOMOTOPICALLY_TRIVIAL_RETRACTION_GEN) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID]);;

let RETRACT_OF_HOMOTOPICALLY_TRIVIAL_NULL = prove
 (`!s t:real^N->bool u:real^M->bool.
        t retract_of s /\
        (!f. f continuous_on u /\ IMAGE f u SUBSET s
             ==> ?c. homotopic_with (\x. T)
                      (subtopology euclidean u,subtopology euclidean s)
                      f (\x. c))
        ==> (!f. f continuous_on u /\ IMAGE f u SUBSET t
                 ==> ?c. homotopic_with (\x. T)
                          (subtopology euclidean u,subtopology euclidean t)
                          f (\x. c))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> p /\ q /\ T`] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
    HOMOTOPICALLY_TRIVIAL_RETRACTION_NULL_GEN) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID]);;

let RETRACT_OF_COHOMOTOPICALLY_TRIVIAL = prove
 (`!s t:real^N->bool u:real^M->bool.
        t retract_of s /\
        (!f g. f continuous_on s /\ IMAGE f s SUBSET u /\
               g continuous_on s /\ IMAGE g s SUBSET u
               ==> homotopic_with (\x. T)
                    (subtopology euclidean s,subtopology euclidean u)  f g)
        ==> (!f g. f continuous_on t /\ IMAGE f t SUBSET u /\
                   g continuous_on t /\ IMAGE g t SUBSET u
                   ==> homotopic_with (\x. T)
                       (subtopology euclidean t,subtopology euclidean u) f g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> p /\ q /\ T /\ r /\ s /\ T`] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
    COHOMOTOPICALLY_TRIVIAL_RETRACTION_GEN) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID]);;

let RETRACT_OF_COHOMOTOPICALLY_TRIVIAL_NULL = prove
 (`!s t:real^N->bool u:real^M->bool.
        t retract_of s /\
        (!f. f continuous_on s /\ IMAGE f s SUBSET u
             ==> ?c. homotopic_with (\x. T)
                      (subtopology euclidean s,subtopology euclidean u)
                      f (\x. c))
        ==> (!f. f continuous_on t /\ IMAGE f t SUBSET u
                 ==> ?c. homotopic_with (\x. T)
                          (subtopology euclidean t,subtopology euclidean u)
                          f (\x. c))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> p /\ q /\ T`] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
    COHOMOTOPICALLY_TRIVIAL_RETRACTION_NULL_GEN) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID]);;

let RETRACTION_IMP_QUOTIENT_MAP = prove
 (`!r s t:real^N->bool.
    retraction (s,t) r
    ==> !u. u SUBSET t
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ r x IN u} <=>
                 open_in (subtopology euclidean t) u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_RIGHT_INVERSE_IMP_QUOTIENT_MAP THEN
  EXISTS_TAC `\x:real^N. x` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; SUBSET_REFL; IMAGE_ID]);;

let RETRACT_OF_LOCALLY_CONNECTED = prove
 (`!s t:real^N->bool.
        s retract_of t /\ locally connected t ==> locally connected s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o el 2 o CONJUNCTS o GEN_REWRITE_RULE I
   [RETRACTION]) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LOCALLY_CONNECTED_QUOTIENT_IMAGE) THEN
  MATCH_MP_TAC RETRACTION_IMP_QUOTIENT_MAP THEN
  ASM_MESON_TAC[RETRACTION]);;

let RETRACT_OF_LOCALLY_PATH_CONNECTED = prove
 (`!s t:real^N->bool.
        s retract_of t /\ locally path_connected t
        ==> locally path_connected s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o el 2 o CONJUNCTS o GEN_REWRITE_RULE I
   [RETRACTION]) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
    LOCALLY_PATH_CONNECTED_QUOTIENT_IMAGE) THEN
  MATCH_MP_TAC RETRACTION_IMP_QUOTIENT_MAP THEN
  ASM_MESON_TAC[RETRACTION]);;

let RETRACT_OF_LOCALLY_COMPACT = prove
 (`!s t:real^N->bool.
        locally compact s /\ t retract_of s ==> locally compact t`,
  MESON_TAC[CLOSED_IN_RETRACT; LOCALLY_COMPACT_CLOSED_IN]);;

let RETRACT_OF_PCROSS = prove
 (`!s:real^M->bool s' t:real^N->bool t'.
        s retract_of s' /\ t retract_of t'
        ==> (s PCROSS t) retract_of (s' PCROSS t')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PCROSS] THEN
  REWRITE_TAC[retract_of; retraction; SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `f:real^M->real^M` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\z. pastecart ((f:real^M->real^M) (fstcart z))
                            ((g:real^N->real^N) (sndcart z))` THEN
  REWRITE_TAC[FORALL_PASTECART; IN_ELIM_PASTECART_THM] THEN
  ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
  CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
   CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART]);;

let RETRACT_OF_PCROSS_EQ = prove
 (`!s s':real^M->bool t t':real^N->bool.
        s PCROSS t retract_of s' PCROSS t' <=>
        (s = {} \/ t = {}) /\ (s' = {} \/ t' = {}) \/
        s retract_of s' /\ t retract_of t'`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC
   [`s:real^M->bool = {}`;
    `s':real^M->bool = {}`;
    `t:real^N->bool = {}`;
    `t':real^N->bool = {}`] THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; RETRACT_OF_EMPTY; PCROSS_EQ_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[RETRACT_OF_PCROSS] THEN
  REWRITE_TAC[retract_of; retraction; SUBSET; FORALL_IN_PCROSS;
              FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^(M,N)finite_sum->real^(M,N)finite_sum`
    STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `?b:real^N. b IN t` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `\x. fstcart((r:real^(M,N)finite_sum->real^(M,N)finite_sum)
                            (pastecart x b))` THEN
    ASM_SIMP_TAC[FSTCART_PASTECART] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_FSTCART; LINEAR_CONTINUOUS_ON] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
      ASM_MESON_TAC[MEMBER_NOT_EMPTY];
      ASM_MESON_TAC[PASTECART_FST_SND; PASTECART_IN_PCROSS; MEMBER_NOT_EMPTY]];
    SUBGOAL_THEN `?a:real^M. a IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `\x. sndcart((r:real^(M,N)finite_sum->real^(M,N)finite_sum)
                            (pastecart a x))` THEN
    ASM_SIMP_TAC[SNDCART_PASTECART] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_SNDCART; LINEAR_CONTINUOUS_ON] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
      ASM_MESON_TAC[MEMBER_NOT_EMPTY];
      ASM_MESON_TAC[PASTECART_FST_SND; PASTECART_IN_PCROSS;
                    MEMBER_NOT_EMPTY]]]);;

let HOMOTOPIC_INTO_RETRACT = prove
 (`!f:real^M->real^N g s t u.
        IMAGE f s SUBSET t /\ IMAGE g s SUBSET t /\ t retract_of u /\
        homotopic_with (\x. T)
         (subtopology euclidean s,subtopology euclidean u) f g
        ==> homotopic_with (\x. T)
             (subtopology euclidean s,subtopology euclidean t) f g`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMOTOPIC_WITH_EUCLIDEAN]) THEN
  SIMP_TAC[HOMOTOPIC_WITH; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h:real^(1,M)finite_sum->real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^N->real^N` THEN STRIP_TAC THEN
  EXISTS_TAC `(r:real^N->real^N) o (h:real^(1,M)finite_sum->real^N)` THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE; ASM SET_TAC[]] THEN
  CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    CONTINUOUS_ON_SUBSET)) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Brouwer fixed-point theorem and related results.                          *)
(* ------------------------------------------------------------------------- *)

let CONTRACTIBLE_SPHERE = prove
 (`!a:real^N r. contractible(sphere(a,r)) <=> r <= &0`,
  GEOM_ORIGIN_TAC `a:real^N` THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[SPHERE_EMPTY; CONTRACTIBLE_EMPTY; REAL_LT_IMP_LE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `b:real^N` (SUBST1_TAC o SYM) o
        MATCH_MP VECTOR_CHOOSE_SIZE) THEN
  REWRITE_TAC[NORM_ARITH `norm(b:real^N) <= &0 <=> b = vec 0`] THEN
  GEOM_NORMALIZE_TAC `b:real^N` THEN
  SIMP_TAC[NORM_0; SPHERE_SING; CONTRACTIBLE_SING] THEN
  X_GEN_TAC `b:real^N` THEN ASM_CASES_TAC `b:real^N = vec 0` THEN
  ASM_REWRITE_TAC[NORM_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  DISCH_THEN(K ALL_TAC) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCH_THEN(MP_TAC o ISPEC `I:real^N->real^N` o
   MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
   (REWRITE_RULE[CONJ_ASSOC] HOMOTOPIC_INTO_CONTRACTIBLE))) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`reflect_along (basis 1:real^N)`; `sphere(vec 0:real^N,&1)`]) THEN
  REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID; I_DEF; NOT_IMP] THEN
  SIMP_TAC[SUBSET_REFL; LINEAR_CONTINUOUS_ON; LINEAR_REFLECT_ALONG;
           ORTHOGONAL_TRANSFORMATION_SPHERE;
           ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
   (REWRITE_RULE[CONJ_ASSOC] HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_IMP))) THEN
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG;
              ORTHOGONAL_TRANSFORMATION_ID] THEN
  REWRITE_TAC[DET_MATRIX_REFLECT_ALONG; MATRIX_ID; DET_I] THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let NO_RETRACTION_CBALL = prove
 (`!a:real^N e. &0 < e ==> ~(sphere(a,e) retract_of cball(a,e))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
    RETRACT_OF_CONTRACTIBLE)) THEN
  SIMP_TAC[CONVEX_IMP_CONTRACTIBLE; CONVEX_CBALL; CONTRACTIBLE_SPHERE] THEN
  ASM_REWRITE_TAC[REAL_NOT_LE]);;

let BROUWER_BALL = prove
 (`!f:real^N->real^N a e.
        &0 < e /\
        f continuous_on cball(a,e) /\
        IMAGE f (cball(a,e)) SUBSET cball(a,e)
        ==> ?x. x IN cball(a,e) /\ f x = x`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MESON[]
   `(?x. P x /\ Q x) <=> ~(!x. P x ==> ~Q x)`] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPEC `a:real^N` o MATCH_MP NO_RETRACTION_CBALL) THEN
  REWRITE_TAC[retract_of; retraction; SPHERE_SUBSET_CBALL] THEN
  ABBREV_TAC
   `s = \x:real^N.  &4 * ((a - x:real^N) dot (f x - x)) pow 2 +
                &4 * (e pow 2 - norm(a - x) pow 2) * norm(f x - x) pow 2` THEN
  SUBGOAL_THEN `!x:real^N. x IN cball(a,e) ==> &0 <= s x` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_CBALL; dist] THEN DISCH_TAC THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS; REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2; REAL_SUB_LE] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  EXISTS_TAC `\x:real^N. x + (&2 * ((a - x) dot (f x - x)) - sqrt(s x)) /
                             (&2 * ((f x - x) dot (f x - x))) % (f x - x)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; o_DEF] THEN
    REWRITE_TAC[real_div; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_CMUL; LIFT_SUB] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID;
        CONTINUOUS_ON_CONST; CONTINUOUS_ON_LIFT_DOT2] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN
      ASM_REWRITE_TAC[o_DEF] THEN EXPAND_TAC "s" THEN
      REWRITE_TAC[LIFT_ADD; LIFT_CMUL; LIFT_SUB; NORM_POW_2; REAL_POW_2] THEN
      REPEAT((MATCH_MP_TAC CONTINUOUS_ON_ADD ORELSE
              MATCH_MP_TAC CONTINUOUS_ON_SUB ORELSE
              MATCH_MP_TAC CONTINUOUS_ON_MUL) THEN
             CONJ_TAC THEN REWRITE_TAC[o_DEF; LIFT_SUB]);
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
      ASM_SIMP_TAC[REAL_ENTIRE; DOT_EQ_0; VECTOR_SUB_EQ] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LIFT_CMUL]] THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID;
      CONTINUOUS_ON_CONST; CONTINUOUS_ON_LIFT_DOT2];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_SPHERE; IN_CBALL; dist; NORM_EQ_SQUARE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[VECTOR_ARITH `a - (x + y):real^N = (a - x) - y`] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `(x - y:real^N) dot (x - y) = (x dot x + y dot y) - &2 * x dot y`] THEN
    REWRITE_TAC[DOT_LMUL] THEN REWRITE_TAC[DOT_RMUL] THEN REWRITE_TAC[REAL_RING
     `(a + u * u * b) - &2 * u * c = d <=>
      b * u pow 2 - (&2 * c) * u + (a - d) = &0`] THEN
    SUBGOAL_THEN `sqrt(s(x:real^N)) pow 2 = s x` MP_TAC THENL
     [ASM_SIMP_TAC[SQRT_POW_2; IN_CBALL; dist]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_FIELD
     `~(a = &0) /\ e = b pow 2 - &4 * a * c /\ x = (b - s) / (&2 * a)
      ==> s pow 2 = e ==> a * x pow 2 - b * x + c = &0`) THEN
    ASM_SIMP_TAC[DOT_EQ_0; VECTOR_SUB_EQ; IN_CBALL; dist] THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[NORM_POW_2] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_SPHERE; dist] THEN DISCH_TAC THEN
    EXPAND_TAC "s" THEN ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    REWRITE_TAC[VECTOR_ARITH `x + a:real^N = x <=> a = vec 0`] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_DIV_EQ_0] THEN REPEAT DISJ1_TAC THEN
    REWRITE_TAC[REAL_ARITH `&2 * a - s = &0 <=> s = &2 * a`] THEN
    MATCH_MP_TAC SQRT_UNIQUE THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= &2 * x <=> &0 <= x`] THEN
    REWRITE_TAC[DOT_NORM_SUB; REAL_ARITH `&0 <= x / &2 <=> &0 <= x`] THEN
    REWRITE_TAC[VECTOR_ARITH `a - x - (y - x):real^N = a - y`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `&0 <= b /\ x <= a ==> &0 <= (a + b) - x`) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_CBALL; FORALL_IN_IMAGE; NORM_POS_LE] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[dist] THEN
    CONV_TAC NORM_ARITH]);;

let BROUWER = prove
 (`!f:real^N->real^N s.
        compact s /\ convex s /\ ~(s = {}) /\
        f continuous_on s /\ IMAGE f s SUBSET s
        ==> ?x. x IN s /\ f x = x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?e. &0 < e /\ s SUBSET cball(vec 0:real^N,e)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; NORM_ARITH `dist(vec 0,x) = norm(x)`] THEN
    ASM_MESON_TAC[BOUNDED_POS; COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?x:real^N. x IN cball(vec 0,e) /\ (f o closest_point s) x = x`
  MP_TAC THENL
   [MATCH_MP_TAC BROUWER_BALL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_CLOSEST_POINT; COMPACT_IMP_CLOSED] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN
      REPEAT STRIP_TAC THEN
      REPEAT(FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET])) THEN
      REWRITE_TAC[o_THM; IN_IMAGE] THEN
      EXISTS_TAC `closest_point s x:real^N` THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSEST_POINT_IN_SET]] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSEST_POINT_IN_SET];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_MESON_TAC[CLOSEST_POINT_SELF;
                  CLOSEST_POINT_IN_SET; COMPACT_IMP_CLOSED]]);;

let BROUWER_WEAK = prove
 (`!f:real^N->real^N s.
        compact s /\ convex s /\ ~(interior s = {}) /\
        f continuous_on s /\ IMAGE f s SUBSET s
        ==> ?x. x IN s /\ f x = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BROUWER THEN
  ASM_MESON_TAC[INTERIOR_EMPTY]);;

let BROUWER_CUBE = prove
 (`!f:real^N->real^N.
        f continuous_on (interval [vec 0,vec 1]) /\
        IMAGE f (interval [vec 0,vec 1]) SUBSET (interval [vec 0,vec 1])
        ==> ?x. x IN interval[vec 0,vec 1] /\ f x = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BROUWER THEN
  ASM_REWRITE_TAC[CONVEX_INTERVAL; COMPACT_INTERVAL; UNIT_INTERVAL_NONEMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Now we can finally deduce what the topological dimension of R^n is.       *)
(* Proof following Hurewicz & Wallman's "dimension theory".                  *)
(* ------------------------------------------------------------------------- *)

let DIMENSION_EQ_AFF_DIM = prove
 (`!s:real^N->bool. convex s ==> dimension s = aff_dim s`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[GSYM INT_LE_ANTISYM; DIMENSION_LE_AFF_DIM] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[DIMENSION_EMPTY; AFF_DIM_EMPTY; INT_LE_REFL] THEN
  ASM_CASES_TAC `aff_dim(s:real^N->bool) = &0` THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [AFF_DIM_EQ_0]) THEN
    SIMP_TAC[LEFT_IMP_EXISTS_THM; DIMENSION_SING; INT_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= aff_dim(s:real^N->bool) /\ &1 <= aff_dim s` MP_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_GE) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
    [GSYM AFF_DIM_EQ_MINUS1]) THEN
    ASM_INT_ARITH_TAC;
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ)] THEN
  ABBREV_TAC `nn = aff_dim(s:real^N->bool)` THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC[TAUT
   `d ==> p ==> q /\ r ==> s <=> q ==> d /\ p /\ r ==> s`] THEN
  SPEC_TAC(`nn:int`,`nn:int`) THEN
  REWRITE_TAC[GSYM INT_FORALL_POS; INT_OF_NUM_EQ; INT_OF_NUM_LE] THEN
  REPEAT STRIP_TAC THEN
  TRANS_TAC INT_LE_TRANS `dimension(relative_interior s:real^N->bool)` THEN
  ASM_SIMP_TAC[DIMENSION_SUBSET; RELATIVE_INTERIOR_SUBSET] THEN
  MP_TAC(ISPEC `s:real^N->bool` OPEN_IN_RELATIVE_INTERIOR) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_RELATIVE_INTERIOR) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP AFFINE_HULL_RELATIVE_INTERIOR) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RELATIVE_INTERIOR_EQ_EMPTY) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CONVEX_RELATIVE_INTERIOR) THEN
  UNDISCH_TAC `1 <= n` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`relative_interior s:real^N->bool`,`t:real^N->bool`) THEN
  X_GEN_TAC `u:real^N->bool` THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^N->bool`;
                 `span(IMAGE basis (1..n)):real^N->bool`]
        HOMEOMORPHIC_RELATIVELY_OPEN_CONVEX_SETS) THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; AFF_DIM_DIM_0; HULL_INC; SPAN_0] THEN
  ASM_REWRITE_TAC[SPAN_SPAN; OPEN_IN_REFL; CONVEX_SPAN] THEN
  MP_TAC(ISPEC `u:real^N->bool` AFF_DIM_LE_UNIV) THEN
  ASM_REWRITE_TAC[DIM_SPAN; INT_OF_NUM_EQ; INT_OF_NUM_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `dim(IMAGE basis (1..n):real^N->bool) = n` ASSUME_TAC THENL
   [REWRITE_TAC[DIM_BASIS_IMAGE] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_1] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_NUMSEG] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP HOMEOMORPHIC_DIMENSION)] THEN
  ABBREV_TAC
   `box = {x:real^N | (!i. 1 <= i /\ i <= dimindex(:N)
                           ==> &0 <= x$i /\ x$i <= &1) /\
                      (!i. n < i /\ i <= dimindex(:N) ==> x$i = &0)}` THEN
  TRANS_TAC INT_LE_TRANS `dimension(box:real^N->bool)` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC DIMENSION_SUBSET THEN EXPAND_TAC "box" THEN
    REWRITE_TAC[SUBSET; IN_SPAN_IMAGE_BASIS; IN_NUMSEG; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (free_in `box:real^N->bool` o concl)) THEN
  MAP_EVERY UNDISCH_TAC [`n <= dimindex(:N)`; `1 <= n`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[INT_ARITH `n:int <= d <=> ~(d <= n - &1)`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `~(box:real^N->bool = {}) /\ convex(box:real^N->bool) /\ compact box`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "box" THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `vec 0:real^N` THEN
      REWRITE_TAC[VEC_COMPONENT; REAL_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `box = interval[vec 0:real^N,vec 1] INTER span(IMAGE basis (1..n))`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_SPAN_IMAGE_BASIS; IN_INTERVAL] THEN
      EXPAND_TAC "box" THEN REWRITE_TAC[IN_ELIM_THM; VEC_COMPONENT] THEN
      GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      EQ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      SIMP_TAC[CONVEX_INTER; CONVEX_INTERVAL; CONVEX_SPAN] THEN
      SIMP_TAC[COMPACT_INTER_CLOSED; COMPACT_INTERVAL; CLOSED_SPAN]];
    ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`l = \i. box INTER {x:real^N | x$i = &0}`;
    `r = \i. box INTER {x:real^N | x$i = &1}`] THEN
  SUBGOAL_THEN
   `(!i:num. 1 <= i /\ i <= n ==> ~(l i:real^N->bool = {})) /\
    (!i:num. 1 <= i /\ i <= n ==> ~(r i:real^N->bool = {}))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["l"; "r"; "box"] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; GSYM MEMBER_NOT_EMPTY] THEN
    CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THENL
     [EXISTS_TAC `vec 0:real^N`;
      EXISTS_TAC `(lambda j. if j = i then &1 else &0):real^N`] THEN
    SIMP_TAC[VEC_COMPONENT; REAL_POS; LAMBDA_BETA] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
      [MESON_TAC[REAL_POS; REAL_LE_REFL]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) LAMBDA_BETA o lhand o snd) THEN
    (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST_ALL_TAC]) THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?b:num->real^N->bool.
       (!i. closed_in (subtopology euclidean box) (b i)) /\
       (!i. 1 <= i /\ i <= n
            ==> dimension(box INTER INTERS (IMAGE b (1..i))) <= &n - &i - &1 /\
                ?u v. open_in (subtopology euclidean box) u /\
                      open_in (subtopology euclidean box) v /\
                      DISJOINT u v /\
                      u UNION v = box DIFF b i /\
                      l i SUBSET u /\
                      r i SUBSET v)`
  MP_TAC THENL
   [SIMP_TAC[GSYM NUMSEG_RREC] THEN
    REWRITE_TAC[IMAGE_CLAUSES; INTERS_INSERT] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN
    MATCH_MP_TAC(MATCH_MP WF_REC_EXISTS WF_num) THEN CONJ_TAC THENL
     [SIMP_TAC[numseg; ARITH_RULE `1 <= i ==> (x <= i - 1 <=> x < i)`] THEN
      REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN  AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`b:num->real^N->bool`; `i:num`] THEN
    DISCH_TAC THEN
    ASM_CASES_TAC `1 <= i /\ i <= n` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC; ASM_MESON_TAC[CLOSED_IN_REFL]] THEN
    ONCE_REWRITE_TAC[SET_RULE `b INTER s INTER t = s INTER b INTER t`] THEN
    MATCH_MP_TAC DIMENSION_SEPARATION_THEOREM THEN
    ASM_REWRITE_TAC[INT_SUB_LE; INT_OF_NUM_LE; INTER_SUBSET] THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `i = 1` THENL
       [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        CONV_TAC(ONCE_DEPTH_CONV NUMSEG_CONV) THEN
        ASM_REWRITE_TAC[IMAGE_CLAUSES; INTERS_0; INTER_UNIV];
        FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
        ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; INT_ARITH
         `n - (i - w) - w:int = n - i`] THEN
        ASM_SIMP_TAC[GSYM NUMSEG_RREC; ARITH_RULE
         `1 <= i /\ ~(i = 1) ==> 1 <= i - 1`] THEN
        REWRITE_TAC[IMAGE_CLAUSES; INTERS_INSERT; INTER_ACI]];
      MAP_EVERY EXPAND_TAC ["l"; "r"] THEN
      SIMP_TAC[CLOSED_IN_CLOSED_INTER; CLOSED_STANDARD_HYPERPLANE] THEN
      MATCH_MP_TAC(SET_RULE
        `(!x. P x /\ Q x ==> F)
         ==> DISJOINT (b INTER {x | P x}) (b INTER {x | Q x})`) THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; SKOLEM_THM; RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC
   [`b:num->real^N->bool`; `u:num->real^N->bool`; `v:num->real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `n:num`) STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[LE_REFL; INT_ARITH `n - n - w:int = --w`] THEN
  REWRITE_TAC[DIMENSION_LE_MINUS1] THEN
  MATCH_MP_TAC(SET_RULE `t SUBSET s /\ ~(t = {}) ==> ~(s INTER t = {})`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTERS_SUBSET THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; NUMSEG_EMPTY; NOT_LT] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG] THEN
    ASM_MESON_TAC[CLOSED_IN_IMP_SUBSET];
    DISCH_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= n ==> ~(b i:real^N->bool = {})`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONVEX_CONNECTED) THEN
    REWRITE_TAC[CONNECTED_OPEN_IN] THEN MAP_EVERY EXISTS_TAC
     [`(u:num->real^N->bool) i`; `(v:num->real^N->bool) i`] THEN
    ASM_SIMP_TAC[GSYM DISJOINT; DIFF_EMPTY; SUBSET_REFL] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `(f:real^N->real^N) =
      \x. x +
          lambda i. if n < i then &0
                    else if x IN v i then --setdist({x},b i)
                    else setdist({x},b i)` THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `box:real^N->bool`] BROUWER) THEN
  ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
    EXPAND_TAC "f" THEN SIMP_TAC[VECTOR_ADD_COMPONENT; LAMBDA_BETA] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[LIFT_ADD] THEN
    REWRITE_TAC[GSYM NOT_LE] THEN
    ASM_CASES_TAC `m:num <= n` THEN
    ASM_SIMP_TAC[LIFT_NUM; VECTOR_ADD_RID; CONTINUOUS_ON_LIFT_COMPONENT] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT] THEN
    REWRITE_TAC[COND_RAND] THEN
    SUBGOAL_THEN
     `box = (box DIFF (u:num->real^N->bool) m) UNION (box DIFF v m)`
     (fun th -> SUBST1_TAC th THEN
                MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
                SUBST1_TAC(SYM th))
    THENL [ASM SET_TAC[]; ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL]] THEN
    SIMP_TAC[LIFT_NEG; CONTINUOUS_ON_NEG; CONTINUOUS_ON_LIFT_SETDIST] THEN
    X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `x IN (b:num->real^N->bool) m` THENL
     [ASM_SIMP_TAC[SETDIST_SING_IN_SET]; ASM SET_TAC[]] THEN
    REWRITE_TAC[LIFT_NUM; VECTOR_NEG_0; VECTOR_MUL_RZERO];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    EXPAND_TAC "box" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN EXPAND_TAC "f" THEN
    SUBGOAL_THEN `!i. n < i ==> 1 <= i` MP_TAC THENL
     [ASM_ARITH_TAC; SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT]] THEN
    DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[REAL_ADD_RID] THEN
    X_GEN_TAC `m:num` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ADD_RID] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN STRIP_TAC THEN
    ASM_CASES_TAC `x IN (b:num->real^N->bool) m` THEN
    ASM_SIMP_TAC[SETDIST_SING_IN_SET] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[COND_ID; REAL_ADD_RID] THEN
    SUBGOAL_THEN
     `x IN (u:num->real^N->bool) m /\ ~(x IN v m) \/
      x IN v m /\ ~(x IN u m)`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC; ONCE_REWRITE_TAC[CONJ_SYM]] THEN
    (MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SETDIST_POS_LE; REAL_LE_ADD; REAL_ARITH
       `x <= &1 /\ &0 <= y ==> x + --y <= &1`];
      DISCH_TAC]) THEN
    ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
     [ABBREV_TAC `y:real^N = lambda i. if i = m then &1 else (x:real^N)$i` THEN
      SUBGOAL_THEN `y IN (r:num->real^N->bool) m` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN box` THEN
        MAP_EVERY EXPAND_TAC ["y"; "r"; "box"] THEN
        REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
        SUBGOAL_THEN `!i. n < i ==> 1 <= i` MP_TAC THENL
         [ASM_ARITH_TAC; ASM_SIMP_TAC[LAMBDA_BETA]] THEN
        REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[REAL_POS; REAL_LE_REFL] THEN ASM_ARITH_TAC;
        ALL_TAC];
      ABBREV_TAC `y:real^N = lambda i. if i = m then &0 else (x:real^N)$i` THEN
      SUBGOAL_THEN `y IN (l:num->real^N->bool) m` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN box` THEN
        MAP_EVERY EXPAND_TAC ["y"; "l"; "box"] THEN
        REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
        SUBGOAL_THEN `!i. n < i ==> 1 <= i` MP_TAC THENL
         [ASM_ARITH_TAC; ASM_SIMP_TAC[LAMBDA_BETA]] THEN
        REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[REAL_POS; REAL_LE_REFL] THEN ASM_ARITH_TAC;
        ALL_TAC]] THEN
   (SUBGOAL_THEN `segment[x:real^N,y] SUBSET box` ASSUME_TAC THENL
     [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`x:real^N`; `y:real^N`]
     (CONJUNCT1 CONNECTED_SEGMENT)) THEN
    REWRITE_TAC[CONNECTED_OPEN_IN] THEN MAP_EVERY EXISTS_TAC
     [`segment[x,y] INTER (u:num->real^N->bool) m`;
      `segment[x,y] INTER (v:num->real^N->bool) m`] THEN
    ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
      EXISTS_TAC `box:real^N->bool` THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; OPEN_IN_REFL];
      ASM_SIMP_TAC[GSYM UNION_OVER_INTER]] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_INTER; SUBSET_REFL; SET_RULE
       `s SUBSET t DIFF u <=> s SUBSET t /\ !x y. x IN s ==> ~(x IN u)`];
      MP_TAC(ISPECL [`x:real^N`; `y:real^N`] ENDS_IN_SEGMENT) THEN
      ASM SET_TAC[]] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `z:real^N = x` THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `z:real^N = y` THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `z IN segment(x:real^N,y)` MP_TAC THENL
     [REWRITE_TAC[open_segment] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP DIST_IN_OPEN_SEGMENT) THEN
    GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
    TRANS_TAC REAL_LE_TRANS `setdist(b(m:num),{x:real^N})` THEN
    ASM_SIMP_TAC[SETDIST_LE_DIST; IN_SING] THEN EXPAND_TAC "y" THEN
    ONCE_REWRITE_TAC[SETDIST_SYM]) THENL
     [TRANS_TAC REAL_LE_TRANS `&1 - (x:real^N)$m`;
      TRANS_TAC REAL_LE_TRANS `(x:real^N)$m`] THEN
   (CONJ_TAC THENL [EXPAND_TAC "y"; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[dist] THEN
    REWRITE_TAC[NORM_EQ_SQUARE] THEN
    SIMP_TAC[dot; LAMBDA_BETA; VECTOR_SUB_COMPONENT] THEN
    REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[REAL_SUB_REFL; SUM_DELTA; REAL_MUL_LZERO] THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN box` MP_TAC THENL
     [ASM SET_TAC[]; EXPAND_TAC "box"] THEN
    REWRITE_TAC[IN_ELIM_THM; REAL_SUB_LE] THEN ASM_MESON_TAC[]);
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` MP_TAC) THEN EXPAND_TAC "f" THEN
    SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; LAMBDA_BETA] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [INTERS_IMAGE]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN
    REWRITE_TAC[IN_NUMSEG; CONTRAPOS_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `m:num` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM NOT_LE; REAL_ARITH
      `a + (if p then --x else x) = a <=> x = &0`] THEN
    ASM_MESON_TAC[SETDIST_EQ_0_CLOSED_IN]]);;

let AFF_DIM_DIMENSION = prove
 (`!s:real^N->bool. aff_dim s = dimension(affine hull s)`,
  SIMP_TAC[DIMENSION_EQ_AFF_DIM; AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL] THEN
  REWRITE_TAC[AFF_DIM_AFFINE_HULL]);;

let AFF_DIM_DIMENSION_ALT = prove
 (`!s:real^N->bool. aff_dim s = dimension(convex hull s)`,
  SIMP_TAC[DIMENSION_EQ_AFF_DIM; CONVEX_CONVEX_HULL] THEN
  REWRITE_TAC[AFF_DIM_CONVEX_HULL]);;

let DIMENSION_SUBSPACE = prove
 (`!s:real^N->bool. subspace s ==> dimension s = &(dim s)`,
  SIMP_TAC[DIMENSION_EQ_AFF_DIM; SUBSPACE_IMP_CONVEX; AFF_DIM_DIM_SUBSPACE]);;

let DIM_DIMENSION = prove
 (`!s:real^N->bool. &(dim s) = dimension(span s)`,
  SIMP_TAC[DIMENSION_SUBSPACE; DIM_SPAN; SUBSPACE_SPAN]);;

let DIMENSION_OPEN_IN_CONVEX = prove
 (`!u s:real^N->bool.
        convex u /\ open_in (subtopology euclidean u) s
        ==> dimension s = if s = {} then -- &1 else aff_dim u`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM DIMENSION_EQ_AFF_DIM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DIMENSION_EMPTY] THEN
  REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[DIMENSION_SUBSET; OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `s:real^N->bool`]
        OPEN_IN_CONVEX_MEETS_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_CONTAINS_BALL]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `a:real^N`)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  TRANS_TAC INT_LE_TRANS
   `dimension(affine hull u INTER ball(a:real^N,min d e))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[DIMENSION_EQ_AFF_DIM; CONVEX_INTER; AFFINE_IMP_CONVEX;
                 AFFINE_AFFINE_HULL; CONVEX_BALL] THEN
    MATCH_MP_TAC INT_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM AFF_DIM_AFFINE_HULL] THEN
    MATCH_MP_TAC AFF_DIM_CONVEX_INTER_OPEN THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; AFFINE_IMP_CONVEX; OPEN_BALL] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `a:real^N` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL; REAL_LT_MIN; HULL_INC];
    MATCH_MP_TAC DIMENSION_SUBSET THEN REWRITE_TAC[BALL_MIN_INTER] THEN
    ASM SET_TAC[]]);;

let DIMENSION_OPEN = prove
 (`!s:real^N->bool.
        open s ==> dimension s = if s = {} then -- &1 else &(dimindex(:N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM AFF_DIM_UNIV] THEN
  MATCH_MP_TAC DIMENSION_OPEN_IN_CONVEX THEN
  ASM_REWRITE_TAC[CONVEX_UNIV; SUBTOPOLOGY_UNIV; GSYM OPEN_IN]);;

let DIMENSION_UNIV = prove
 (`dimension(:real^N) = &(dimindex(:N))`,
  SIMP_TAC[DIMENSION_OPEN; OPEN_UNIV; UNIV_NOT_EMPTY]);;

let DIMENSION_NONEMPTY_INTERIOR = prove
 (`!s:real^N->bool. ~(interior s = {}) ==> dimension s = &(dimindex(:N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN
  SIMP_TAC[GSYM DIMENSION_UNIV; DIMENSION_SUBSET; SUBSET_UNIV] THEN
  TRANS_TAC INT_LE_TRANS `dimension(interior(s:real^N->bool))` THEN
  SIMP_TAC[DIMENSION_SUBSET; INTERIOR_SUBSET] THEN
  ASM_SIMP_TAC[INT_LE_REFL; DIMENSION_OPEN; OPEN_INTERIOR; DIMENSION_UNIV]);;

let DIMENSION_ATMOST_RATIONAL_COORDINATES = prove
 (`!n. n <= dimindex(:N)
       ==> dimension
           {x:real^N | CARD {i | i IN 1..dimindex(:N) /\ rational(x$i)} <= n} =
           &n`,
  REWRITE_TAC[GSYM INT_LE_ANTISYM; FORALL_AND_THM; TAUT
   `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[LE; LE_0] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `0` DIMENSION_LE_RATIONAL_COORDINATES) THEN
      ASM_SIMP_TAC[HAS_SIZE; FINITE_RESTRICT; FINITE_NUMSEG; CONJUNCT1 LE];
      X_GEN_TAC `n:num` THEN
      DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
      REWRITE_TAC[LE; SET_RULE
       `{x | Q x \/ R x} = {x | Q x} UNION {x | R x}`] THEN
      W(MP_TAC o PART_MATCH lhand DIMENSION_UNION_LE_BASIC o lhand o snd) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_LE_TRANS) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN
      MATCH_MP_TAC(INT_ARITH
       `x:int <= &0 /\ y <= n ==> x + y + &1 <= n + &1`) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `SUC n` DIMENSION_LE_RATIONAL_COORDINATES) THEN
      ASM_SIMP_TAC[HAS_SIZE; FINITE_RESTRICT; FINITE_NUMSEG]];
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `n = dimindex(:N) - (dimindex(:N) - n)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ARITH_RULE `dimindex(:N) - n <= dimindex(:N)`) THEN
    POP_ASSUM(K ALL_TAC) THEN SPEC_TAC(`dimindex(:N) - n`,`n:num`) THEN
    SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
    MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[LE; LE_0] THEN CONJ_TAC THENL
     [REWRITE_TAC[INT_SUB_RZERO; SUB_0] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM DIMENSION_UNIV] THEN
      MATCH_MP_TAC INT_EQ_IMP_LE THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_UNIV; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_1] THEN
      MATCH_MP_TAC CARD_SUBSET THEN
      SIMP_TAC[FINITE_RESTRICT; SUBSET_RESTRICT; FINITE_NUMSEG];
      X_GEN_TAC `n:num` THEN
      DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM INT_NOT_LT; CONTRAPOS_THM] THEN DISCH_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE
       `SUC n <= N ==> (a <= N - n <=> a = N - n \/ a <= N - SUC n)`] THEN
      REWRITE_TAC[LE; SET_RULE
       `{x | Q x \/ R x} = {x | Q x} UNION {x | R x}`] THEN
      W(MP_TAC o PART_MATCH lhand DIMENSION_UNION_LE_BASIC o lhand o snd) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_LET_TRANS) THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
       `d2:int < n2 ==> d1 < N - n2 ==> d1 + d2 + &1 < N`)) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_SUC; INT_ARITH
       `x:int < N - n - (N - (n + &1)) <=> x <= &0`] THEN
      MP_TAC(SPEC `dimindex(:N) - n` DIMENSION_LE_RATIONAL_COORDINATES) THEN
      SIMP_TAC[HAS_SIZE; FINITE_RESTRICT; FINITE_NUMSEG; LE]]]);;

let DIMENSION_COMPLEMENT_RATIONAL_COORDINATES = prove
 (`dimension((:real^N) DIFF
             { x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i)}) =
   &(dimindex(:N)) - &1`,
  MP_TAC(SPEC `dimindex(:N) - 1` DIMENSION_ATMOST_RATIONAL_COORDINATES) THEN
  REWRITE_TAC[ARITH_RULE `n - 1 <= n`] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB; DIMINDEX_GE_1] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_UNIV; IN_DIFF; IN_ELIM_THM] THEN
  REWRITE_TAC[GSYM IN_NUMSEG; SET_RULE
   `(!x. P x ==> Q x) <=> {x | P x /\ Q x} = {x | P x}`] THEN
  SIMP_TAC[GSYM SUBSET_CARD_EQ; FINITE_RESTRICT; FINITE_NUMSEG;
           CARD_NUMSEG_1; SUBSET_RESTRICT; SET_RULE `{x | x IN s} = s`] THEN
  MATCH_MP_TAC(ARITH_RULE
   `1 <= N /\ n <= N ==> (~(n = N) <=> n <= N - 1)`) THEN
  REWRITE_TAC[DIMINDEX_GE_1] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_1] THEN
  MATCH_MP_TAC CARD_SUBSET THEN
  REWRITE_TAC[SUBSET_RESTRICT; FINITE_NUMSEG]);;

let DIMENSION_EQ_FULL_GEN = prove
 (`!s:real^N->bool.
        dimension s = aff_dim s <=> s = {} \/ ~(relative_interior s = {})`,
  let lemma1 = prove
   (`closure(span(IMAGE basis (1..n)) INTER
             {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i)}) =
     span(IMAGE basis (1..n))`,
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    SIMP_TAC[CLOSURE_MINIMAL; CLOSED_SPAN; INTER_SUBSET] THEN
    REWRITE_TAC[SUBSET; IN_SPAN_IMAGE_BASIS] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(SET_RULE `x IN (:real^N)`) THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
     [GSYM CLOSURE_RATIONAL_COORDINATES] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
    ASM_CASES_TAC `&0 < e` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_SPAN_IMAGE_BASIS] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(lambda i. if i IN 1..n then (y:real^N)$i else &0):real^N` THEN
    SIMP_TAC[LAMBDA_BETA] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[RATIONAL_NUM]; ALL_TAC] THEN
    TRANS_TAC REAL_LET_TRANS `dist(y:real^N,x)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[dist] THEN MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
    X_GEN_TAC `i:num` THEN SIMP_TAC[LAMBDA_BETA; VECTOR_SUB_COMPONENT] THEN
    STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC)
  and lemma2 = prove
   (`!n. n <= dimindex(:N)
          ==> dimension(span(IMAGE basis (1..n)) DIFF
                {x:real^N | !i. i IN 1..dimindex(:N) ==> rational(x$i)}) < &n`,
    REPEAT STRIP_TAC THEN
    TRANS_TAC INT_LET_TRANS
      `dimension(UNIONS
         {{x:real^N |
             {i | i IN 1..dimindex (:N) /\ rational (x$i)} HAS_SIZE m} |
          m IN (dimindex(:N)-n)..dimindex(:N)-1})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DIMENSION_SUBSET THEN REWRITE_TAC[UNIONS_GSPEC; SUBSET] THEN
      SIMP_TAC[HAS_SIZE; FINITE_NUMSEG; FINITE_RESTRICT] THEN
      REWRITE_TAC[IN_SPAN_IMAGE_BASIS; IN_DIFF; IN_ELIM_THM; IN_NUMSEG] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[CONJ_SYM] THEN
      REWRITE_TAC[UNWIND_THM1] THEN CONJ_TAC THENL
       [TRANS_TAC LE_TRANS `CARD(n+1..dimindex(:N))` THEN CONJ_TAC THENL
         [REWRITE_TAC[CARD_NUMSEG] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC CARD_SUBSET THEN
        SIMP_TAC[GSYM IN_NUMSEG; FINITE_RESTRICT; FINITE_NUMSEG] THEN
        REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        SIMP_TAC[RATIONAL_NUM] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC(ARITH_RULE `c < n ==> c <= n - 1`) THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_1] THEN
        MATCH_MP_TAC CARD_PSUBSET THEN REWRITE_TAC[FINITE_NUMSEG] THEN
        REWRITE_TAC[numseg] THEN ASM SET_TAC[]];
      W(MP_TAC o PART_MATCH (lhand o rand)
        DIMENSION_LE_UNIONS_ZERODIMENSIONAL o lhand o snd) THEN
      SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; DIMENSION_LE_RATIONAL_COORDINATES] THEN
      MATCH_MP_TAC(INT_ARITH `c:int <= n ==> d <= c - &1 ==> d < n`) THEN
      REWRITE_TAC[INT_OF_NUM_LE] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_LE o lhand o snd) THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS) THEN
      REWRITE_TAC[CARD_NUMSEG] THEN MATCH_MP_TAC(ARITH_RULE
       `1 <= N /\ n <= N ==> (N - 1 + 1) - (N - n) <= n`) THEN
      ASM_REWRITE_TAC[DIMINDEX_GE_1]]) in
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[DIMENSION_EMPTY; AFF_DIM_EMPTY] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [DISCH_TAC;
    MP_TAC(ISPECL
     [`affine hull s:real^N->bool`; `relative_interior s:real^N->bool`]
      DIMENSION_OPEN_IN_CONVEX) THEN
    ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL; OPEN_IN_RELATIVE_INTERIOR] THEN
    SIMP_TAC[AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL] THEN
    MATCH_MP_TAC(INT_ARITH `i:int <= s /\ s <= u ==> i = u ==> s = u`) THEN
    REWRITE_TAC[DIMENSION_LE_AFF_DIM] THEN
    SIMP_TAC[DIMENSION_SUBSET; RELATIVE_INTERIOR_SUBSET]] THEN
  MP_TAC(ISPEC `affine hull s DIFF s:real^N->bool` SEPARABLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `closure c:real^N->bool = affine hull s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    SIMP_TAC[CLOSURE_MINIMAL_EQ; CLOSED_AFFINE_HULL] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV
     [RELATIVE_INTERIOR_INTERIOR_OF]) THEN
    REWRITE_TAC[INTERIOR_OF_CLOSURE_OF; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    MATCH_MP_TAC(SET_RULE `t SUBSET u ==> s DIFF t = {} ==> s SUBSET u`) THEN
    REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
    MATCH_MP_TAC(SET_RULE `t SUBSET u ==> s INTER t SUBSET u`) THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull c:real^N->bool = affine hull s` ASSUME_TAC THENL
   [ASM_MESON_TAC[HULL_HULL; AFFINE_HULL_CLOSURE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `aff_dim c <= dimension(affine hull c DIFF c:real^N->bool)`
  MP_TAC THENL
   [TRANS_TAC INT_LE_TRANS `dimension(s:real^N->bool)` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[INT_LE_REFL; AFF_DIM_AFFINE_HULL];
      MATCH_MP_TAC DIMENSION_SUBSET THEN
      SUBGOAL_THEN `(s:real^N->bool) SUBSET affine hull s` MP_TAC THENL
       [REWRITE_TAC[HULL_SUBSET]; ASM SET_TAC[]]];
    REWRITE_TAC[INT_NOT_LE] THEN
    SUBGOAL_THEN `closure c:real^N->bool = affine hull c` MP_TAC THENL
     [ASM MESON_TAC[]; UNDISCH_TAC `COUNTABLE(c:real^N->bool)`] THEN
    SUBGOAL_THEN `~(c:real^N->bool = {})` MP_TAC THENL
     [ASM_MESON_TAC[AFFINE_HULL_EQ_EMPTY]; POP_ASSUM_LIST(K ALL_TAC)]] THEN
  SPEC_TAC(`c:real^N->bool`,`c:real^N->bool`) THEN
  X_GEN_TAC `s:real^N->bool` THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM AFF_DIM_POS_LE]) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`s:real^N->bool`;
    `span(IMAGE basis (1..n)) INTER
     {x:real^N | !i. i IN 1..dimindex(:N) ==> rational(x$i)}`]
   HOMEOMORPHISM_MOVING_DENSE_COUNTABLE_SUBSETS_EXISTS) THEN
  ASM_SIMP_TAC[COUNTABLE_INTER; COUNTABLE_RATIONAL_COORDINATES; IN_NUMSEG] THEN
  ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  ONCE_REWRITE_TAC[GSYM AFFINE_HULL_CLOSURE] THEN
  REWRITE_TAC[lemma1] THEN
  SIMP_TAC[HULL_P; SUBSPACE_SPAN; SUBSPACE_IMP_AFFINE] THEN
  SIMP_TAC[AFF_DIM_DIM_SUBSPACE; SUBSPACE_SPAN] THEN
  SIMP_TAC[DIM_SPAN; DIM_BASIS_IMAGE] THEN
  MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_LE_UNIV) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[SUBSET_NUMSEG; LE_REFL; CARD_NUMSEG_1; LEFT_IMP_EXISTS_THM;
               HULL_HULL; SET_RULE `t SUBSET s ==> s INTER t = t`] THEN
  MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
  STRIP_TAC THEN MP_TAC(ISPEC `n:num` lemma2) THEN
  ASM_REWRITE_TAC[HULL_HULL] THEN MATCH_MP_TAC(INT_ARITH
   `d':int = d ==> d < n ==> d' < n`) THEN
  MATCH_MP_TAC HOMEOMORPHIC_DIMENSION THEN
  REWRITE_TAC[homeomorphic] THEN
  MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    HOMEOMORPHISM_OF_SUBSETS)) THEN
  REPEAT(CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IMAGE_DIFF_INJ_ALT o lhand o snd) THEN
  REWRITE_TAC[HULL_SUBSET] THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN
  ASM_REWRITE_TAC[IN_NUMSEG] THEN ASM SET_TAC[]);;

let DIMENSION_LT_FULL_GEN = prove
 (`!s:real^N->bool. dimension s < aff_dim s <=>
                    ~(s = {}) /\ relative_interior s = {}`,
  REWRITE_TAC[INT_ARITH `s:int < a <=> s <= a /\ ~(s = a)`] THEN
  REWRITE_TAC[DIMENSION_EQ_FULL_GEN; DIMENSION_LE_AFF_DIM] THEN
  CONV_TAC TAUT);;

let DIMENSION_EQ_FULL_ALT = prove
 (`!u s:real^N->bool.
        convex u /\ s SUBSET u
        ==> (dimension s = aff_dim u <=>
             s = {} /\ u = {} \/
             ~(subtopology euclidean u interior_of s = {}))`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `u:real^N->bool = {}` THEN
  ASM_SIMP_TAC[AFF_DIM_EMPTY; SUBSET_EMPTY; DIMENSION_EMPTY] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[DIMENSION_EMPTY; INTERIOR_OF_EMPTY] THENL
    [ASM_MESON_TAC[AFF_DIM_EQ_MINUS1]; STRIP_TAC] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `aff_dim(s:real^N->bool)` o MATCH_MP (INT_ARITH
     `s = u ==> !a:int. s <= a /\ a <= u ==> a = u /\ s = a`)) THEN
    REWRITE_TAC[DIMENSION_EQ_FULL_GEN; DIMENSION_LE_AFF_DIM] THEN
    ASM_SIMP_TAC[AFF_DIM_SUBSET] THEN ASM_SIMP_TAC[AFF_DIM_EQ_FULL_GEN] THEN
    REWRITE_TAC[RELATIVE_INTERIOR_INTERIOR_OF] THEN
    SIMP_TAC[IMP_CONJ] THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> ~(s = {}) ==> ~(t = {})`) THEN
    MATCH_MP_TAC INTERIOR_OF_SUBTOPOLOGY_MONO THEN
    ASM_REWRITE_TAC[HULL_SUBSET];
    ASM_SIMP_TAC[GSYM DIMENSION_EQ_AFF_DIM; GSYM INT_LE_ANTISYM;
                 DIMENSION_SUBSET] THEN
    TRANS_TAC INT_LE_TRANS
     `dimension(subtopology euclidean u interior_of s:real^N->bool)` THEN
    SIMP_TAC[DIMENSION_SUBSET; INTERIOR_OF_SUBSET] THEN
    MP_TAC(ISPECL [`u:real^N->bool`;
                   `subtopology euclidean u interior_of s:real^N->bool`]
        DIMENSION_OPEN_IN_CONVEX) THEN
    ASM_SIMP_TAC[OPEN_IN_INTERIOR_OF; DIMENSION_LE_AFF_DIM]]);;

let DIMENSION_LT_FULL_ALT = prove
 (`!u s:real^N->bool.
        convex u /\ s SUBSET u
        ==> (dimension s < aff_dim u <=>
             ~(u = {}) /\ subtopology euclidean u interior_of s = {})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_LT_LE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIMENSION_SUBSET) THEN
  ASM_SIMP_TAC[DIMENSION_EQ_AFF_DIM; DIMENSION_EQ_FULL_ALT] THEN
  ASM_CASES_TAC `u:real^N->bool = {}` THEN
  ASM_SIMP_TAC[AFF_DIM_EMPTY; DIMENSION_LE_MINUS1]);;

let DIMENSION_EQ_FULL = prove
 (`!s:real^N->bool. dimension s = &(dimindex(:N)) <=> ~(interior s = {})`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[DIMENSION_NONEMPTY_INTERIOR] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[DIMENSION_EMPTY; INT_ARITH `~(-- &1:int = &n)`] THEN
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `aff_dim(s:real^N->bool)` o
   MATCH_MP (INT_ARITH `!a. d:int = n ==> d <= a /\ a <= n ==> a = n`)) THEN
  REWRITE_TAC[DIMENSION_LE_AFF_DIM; AFF_DIM_LE_UNIV] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` DIMENSION_EQ_FULL_GEN) THEN
  ASM_REWRITE_TAC[CONTRAPOS_THM] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
  ASM_REWRITE_TAC[GSYM AFF_DIM_EQ_FULL]);;

let DIMENSION_LT_FULL = prove
 (`!s:real^N->bool. dimension s < &(dimindex(:N)) <=> interior s = {}`,
  REWRITE_TAC[INT_LT_LE; DIMENSION_LE_DIMINDEX; DIMENSION_EQ_FULL]);;

let DIMENSION_RELATIVE_FRONTIER_BOUNDED_OPEN = prove
 (`!u s:real^N->bool.
        affine u /\ open_in (subtopology euclidean u) s /\ bounded s
        ==> dimension(relative_frontier s) =
            if s = {} then -- &1 else aff_dim u - &1`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[RELATIVE_FRONTIER_EMPTY; DIMENSION_EMPTY] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->bool`] AFF_DIM_OPEN_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `aff_dim(u:real^N->bool) <= &0` THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
      `s:int <= &0 ==> -- &1 <= s /\ ~(s = -- &1) ==> s = &0`)) THEN
    ASM_REWRITE_TAC[AFF_DIM_GE] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[AFF_DIM_EQ_MINUS1] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[AFF_DIM_EQ_0]] THEN
    SIMP_TAC[AFF_DIM_EQ_0; LEFT_IMP_EXISTS_THM; RELATIVE_FRONTIER_SING] THEN
    REWRITE_TAC[DIMENSION_EMPTY; AFF_DIM_SING] THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC(INT_ARITH `d:int < n /\ ~(d <= n - &2) ==> d = n - &1`) THEN
  CONJ_TAC THENL
   [TRANS_TAC INT_LTE_TRANS `aff_dim(relative_frontier s:real^N->bool)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[DIMENSION_LT_FULL_GEN] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[RELATIVE_FRONTIER_EQ_EMPTY; AFFINE_BOUNDED_EQ_LOWDIM];
        ALL_TAC] THEN
      REWRITE_TAC[RELATIVE_INTERIOR_INTERIOR_OF] THEN
      ASM_SIMP_TAC[AFFINE_HULL_RELATIVE_FRONTIER_BOUNDED;
                   GSYM AFF_DIM_EQ_0;
                   INT_ARITH `~(u:int <= &0) ==> ~(u = &0)`] THEN
      REWRITE_TAC[RELATIVE_FRONTIER_FRONTIER_OF] THEN
      MATCH_MP_TAC INTERIOR_OF_FRONTIER_OF_EMPTY THEN DISJ1_TAC THEN
      ASM_MESON_TAC[AFFINE_HULL_OPEN_IN_CONVEX; AFFINE_IMP_CONVEX;
                    HULL_P];
      MATCH_MP_TAC AFF_DIM_SUBSET THEN REWRITE_TAC[relative_frontier] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s DIFF t SUBSET u`) THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN
      ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; CLOSED_AFFINE]];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier s:real^N->bool =
    subtopology euclidean u frontier_of s`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[RELATIVE_FRONTIER_FRONTIER_OF] THEN
    ASM_MESON_TAC[AFFINE_HULL_OPEN_IN_AFFINE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `s:real^N->bool`]
    DIMENSION_OPEN_IN_CONVEX) THEN
  ASM_SIMP_TAC[AFFINE_IMP_CONVEX] THEN
  MATCH_MP_TAC(INT_ARITH `x:int <= n - &1 ==> ~(x = n)`) THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `s:real^N->bool`;
                 `aff_dim(u:real^N->bool) - &1`] DIMENSION_LE_EQ_GENERAL) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; DISCH_THEN SUBST1_TAC] THEN
  CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:real^N->bool`; `a:real^N`] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(vec 0:real^N) IN u` ASSUME_TAC THENL
   [ASM_MESON_TAC[REWRITE_RULE[SUBSET] OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `affine(u:real^N->bool)` THEN
  ASM_SIMP_TAC[AFFINE_EQ_SUBSPACE] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?c. &0 < c /\
        IMAGE (\x:real^N. c % x) (subtopology euclidean u closure_of s)
        SUBSET s /\
        IMAGE (\x:real^N. c % x) (subtopology euclidean u closure_of s)
        SUBSET v`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_CLOSURE) THEN
    DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_SUBSET_CBALL) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC o
      SPEC `vec 0:real^N`) THEN
    MP_TAC(ISPECL [`s INTER v:real^N->bool`; `u:real^N->bool`]
      OPEN_IN_CONTAINS_CBALL) THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `vec 0:real^N`)) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; GSYM SUBSET_INTER] THEN
    X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    EXISTS_TAC `d / r:real` THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
    TRANS_TAC SUBSET_TRANS `cball(vec 0:real^N,d) INTER u` THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC SUBSET_TRANS
     `IMAGE (\x. d / r % x) (cball(vec 0:real^N,r)) INTER u` THEN
    CONJ_TAC THENL
      [REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
        [MATCH_MP_TAC IMAGE_SUBSET THEN
         TRANS_TAC SUBSET_TRANS `closure s:real^N->bool` THEN
         ASM_REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
         MATCH_MP_TAC(SET_RULE `u SUBSET s ==> t INTER u SUBSET s`) THEN
         SIMP_TAC[SUBSET_CLOSURE; INTER_SUBSET];
         REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
         REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSPACE_MUL THEN
         ASM_MESON_TAC[REWRITE_RULE[SUBSET] CLOSURE_OF_SUBSET_SUBTOPOLOGY]];
       ASM_SIMP_TAC[GSYM CBALL_SCALING; REAL_LT_DIV] THEN
       ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ;
                    VECTOR_MUL_RZERO; SUBSET_REFL]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (\x:real^N. c % x) s` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^N` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [TRANS_TAC SUBSET_TRANS
     `IMAGE (\x:real^N. c % x) (subtopology euclidean u closure_of s)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_MESON_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `u = IMAGE (\x:real^N. c % x) u`
   (fun th -> SUBST1_TAC th THEN ASSUME_TAC(SYM th))
  THENL [ASM_MESON_TAC[CONIC_IMAGE_MULTIPLE; SUBSPACE_IMP_CONIC]; ALL_TAC] THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) OPEN_IN_INJECTIVE_LINEAR_IMAGE o
      snd) THEN
    ASM_REWRITE_TAC[LINEAR_SCALING] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ];
    W(MP_TAC o PART_MATCH (lhand o rand) FRONTIER_OF_INJECTIVE_LINEAR_IMAGE o
        rand o rand o lhand o snd) THEN
    ASM_SIMP_TAC[LINEAR_SCALING; VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `d:int <= n - &2 ==> d' = d ==> d' <= n - &1 - &1`)) THEN
    ASM_SIMP_TAC[frontier_of; SET_RULE
     `IMAGE f c SUBSET s
      ==> s INTER (IMAGE f (c DIFF i)) = IMAGE f (c DIFF i)`] THEN
    REWRITE_TAC[GSYM frontier_of] THEN
    MATCH_MP_TAC DIMENSION_LINEAR_IMAGE THEN
    ASM_SIMP_TAC[LINEAR_SCALING; VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ]]);;

let DIMENSION_FRONTIER_BOUNDED_OPEN = prove
 (`!u:real^N->bool.
        open u /\ bounded u
        ==> dimension(frontier u) =
            if u = {} then -- &1 else &(dimindex(:N)) - &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `u:real^N->bool`]
        DIMENSION_RELATIVE_FRONTIER_BOUNDED_OPEN) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OPEN] THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; AFFINE_UNIV; AFF_DIM_UNIV]);;

let DIMENSION_RELATIVE_FRONTIER_NONDENSE_OPEN = prove
 (`!u s:real^N->bool.
        affine u /\ open_in (subtopology euclidean u) s /\
        ~(s = {}) /\ ~(subtopology euclidean u closure_of s = u)
        ==> dimension(relative_frontier s) = aff_dim u - &1`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `bounded(s:real^N->bool)` THEN
  ASM_SIMP_TAC[DIMENSION_RELATIVE_FRONTIER_BOUNDED_OPEN] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  SUBGOAL_THEN
    `?z:real^N. z IN u /\ ~(z IN subtopology euclidean u closure_of s)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `s SUBSET u /\ ~(s = u) ==> ?x. x IN u /\ ~(x IN s)`) THEN
    ASM_REWRITE_TAC[CLOSURE_OF_SUBSET_SUBTOPOLOGY];
    ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  GEOM_ORIGIN_TAC `z:real^N` THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `affine(u:real^N->bool)` THEN
  ASM_SIMP_TAC[AFFINE_EQ_SUBSPACE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`u DIFF subtopology euclidean u closure_of s:real^N->bool`;
    `u:real^N->bool`]
   OPEN_IN_CONTAINS_CBALL) THEN
  SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL; CLOSED_IN_CLOSURE_OF] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^N` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_DIFF] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ABBREV_TAC `i = \x:real^N. r pow 2 / norm x pow 2 % x` THEN
  MP_TAC(ISPECL [`i:real^N->real^N`; `u DELETE (vec 0:real^N)`]
                INVOLUTION_IMP_HOMEOMORPHISM) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "i" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      REWRITE_TAC[real_div; o_DEF; LIFT_CMUL; CONTINUOUS_ON_ID] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      REWRITE_TAC[REAL_INV_POW] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
      REWRITE_TAC[IN_DELETE; IN_UNIV; NORM_EQ_0] THEN
      SIMP_TAC[CONTINUOUS_ON_LIFT_NORM_COMPOSE; CONTINUOUS_ON_ID];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_UNIV] THEN
      ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_DIV_EQ_0; NORM_EQ_0; REAL_POW_EQ_0;
                   REAL_LT_IMP_NZ; ARITH_EQ; SUBSPACE_MUL] THEN
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
      DISCH_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NORM] THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN UNDISCH_TAC `&0 < r` THEN
      SIMP_TAC[real_abs; REAL_LT_IMP_LE] THEN CONV_TAC REAL_FIELD];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `IMAGE (i:real^N->real^N) s`]
    DIMENSION_RELATIVE_FRONTIER_BOUNDED_OPEN) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM_SIMP_TAC[AFFINE_EQ_SUBSPACE] THEN
  SUBGOAL_THEN `s SUBSET u DELETE (vec 0:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_DELETE] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
      `~(x IN s) ==> t SUBSET s ==> ~(x IN t)`)) THEN
    MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  ASM_CASES_TAC `(vec 0:real^N) IN s` THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean u) (IMAGE (i:real^N->real^N) s)`
  ASSUME_TAC THENL
   [TRANS_TAC OPEN_IN_TRANS `u DELETE (vec 0:real^N)` THEN
    SIMP_TAC[OPEN_IN_DELETE; OPEN_IN_REFL] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        HOMEOMORPHISM_IMP_OPEN_MAP)) THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
      OPEN_IN_SUBSET_TRANS)) THEN
    ASM SET_TAC[];
    ASM_REWRITE_TAC[]] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `cball(vec 0:real^N,r) INTER u` THEN
    SIMP_TAC[BOUNDED_CBALL; BOUNDED_INTER; SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [ALL_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHISM]) THEN ASM SET_TAC[]] THEN
    SUBGOAL_THEN `x IN (:real^N) DIFF cball(vec 0,r)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `b INTER u SUBSET u DIFF c
        ==> c SUBSET u /\ x IN c ==> x IN UNIV DIFF b`)) THEN
      REWRITE_TAC[CLOSURE_OF_SUBSET_SUBTOPOLOGY] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `x IN s ==> s SUBSET t ==> x IN t`)) THEN
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
      EXPAND_TAC "i" THEN REWRITE_TAC[IN_UNIV; IN_DIFF; IN_CBALL_0]] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_NOT_LE; real_abs; REAL_LT_IMP_LE] THEN
    ASM_CASES_TAC `x:real^N = vec 0` THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[NORM_EQ_0; REAL_FIELD
     `~(x = &0) ==> r pow 2 / x pow 2 * x = (r * r) / x`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_LMUL_EQ; NORM_POS_LT] THEN
    REWRITE_TAC[REAL_LT_IMP_LE];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[RELATIVE_FRONTIER_FRONTIER_OF] THEN
  SUBGOAL_THEN `affine hull s:real^N->bool = u` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_HULL_OPEN_IN_AFFINE; SUBSPACE_IMP_AFFINE; HULL_P];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull (IMAGE (i:real^N->real^N) s) = u`
  ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_HULL_OPEN_IN_AFFINE THEN
    ASM_SIMP_TAC[IMAGE_EQ_EMPTY; SUBSPACE_IMP_AFFINE];
    ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o
    SPECL [`subtopology euclidean u frontier_of s:real^N->bool`;
          `IMAGE (i:real^N->real^N) (subtopology euclidean u frontier_of s)`] o
    MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ] HOMEOMORPHISM_OF_SUBSETS)) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[frontier_of] THEN
    SUBGOAL_THEN `subtopology euclidean u closure_of s SUBSET (u:real^N->bool)`
    MP_TAC THENL [REWRITE_TAC[CLOSURE_OF_SUBSET_SUBTOPOLOGY]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHISM]) THEN ASM SET_TAC[];
    DISCH_THEN(SUBST1_TAC o MATCH_MP HOMEOMORPHIC_DIMENSION o
        MATCH_MP HOMEOMORPHISM_IMP_HOMEOMORPHIC)] THEN
  MATCH_MP_TAC(MESON[DIMENSION_INSERT]
   `(?a:real^N. ~(s = {}) /\ ~(t = {}) /\ (a INSERT s = a INSERT t))
    ==> dimension s = dimension t`) THEN
  EXISTS_TAC `vec 0:real^N` THEN REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
  SUBGOAL_THEN `connected(u:real^N->bool)` MP_TAC THENL
   [ASM_SIMP_TAC[SUBSPACE_IMP_CONVEX; CONVEX_CONNECTED]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [CONNECTED_CLOPEN] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[CONJ_SYM] CLOPEN_IN_EQ_FRONTIER_OF] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REWRITE_TAC[TAUT `~p ==> ~(q /\ r) <=> ~p /\ r ==> ~q`] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHISM]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[frontier_of; INTERIOR_OF_OPEN_IN] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> i(i x) = x) /\
    t SUBSET s /\ a INSERT (IMAGE i s) = a INSERT u
    ==> a INSERT IMAGE i (s DIFF t) = a INSERT (u DIFF IMAGE i t)`) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXPAND_TAC "i" THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NORM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM NORM_EQ_0]) THEN
    UNDISCH_TAC `&0 < r` THEN
    SIMP_TAC[real_abs; REAL_LT_IMP_LE] THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_MESON_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:real^N->bool` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] HOMEOMORPHISM_CLOSURE_OF)) THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[SET_RULE `s DELETE a = s INTER (s DELETE a)`] THEN
  REWRITE_TAC[GSYM SUBTOPOLOGY_SUBTOPOLOGY] THEN
  SIMP_TAC[CLOSURE_OF_SUBTOPOLOGY_OPEN; OPEN_IN_DELETE; OPEN_IN_REFL] THEN
  SIMP_TAC[SET_RULE `c SUBSET u ==> (u DELETE z) INTER c = c DELETE z`;
           CLOSURE_OF_SUBSET_SUBTOPOLOGY] THEN
  MATCH_MP_TAC(SET_RULE
   `z INSERT w = z INSERT y
    ==> w = x DELETE z ==> z INSERT y = z INSERT x`) THEN
  MATCH_MP_TAC(SET_RULE
   `i z = z ==> z INSERT IMAGE i (s DELETE z) = z INSERT IMAGE i s`) THEN
  EXPAND_TAC "i" THEN REWRITE_TAC[VECTOR_MUL_RZERO]);;

let DIMENSION_FRONTIER_NONDENSE_OPEN = prove
 (`!u:real^N->bool.
        open u /\ ~(u = {}) /\ ~(closure u = (:real^N))
        ==> dimension(frontier u) = &(dimindex(:N)) - &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `u:real^N->bool`]
        DIMENSION_RELATIVE_FRONTIER_NONDENSE_OPEN) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OPEN] THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; AFFINE_UNIV; AFF_DIM_UNIV;
                  EUCLIDEAN_CLOSURE_OF]);;

let DIMENSION_RELATIVE_FRONTIER_CONVEX = prove
 (`!s:real^N->bool.
        convex s /\ bounded s /\ ~(s = {})
        ==> dimension(relative_frontier s) = aff_dim s - &1`,
  REPEAT STRIP_TAC THEN  MP_TAC(ISPECL
   [`affine hull s:real^N->bool`; `relative_interior s:real^N->bool`]
   DIMENSION_RELATIVE_FRONTIER_BOUNDED_OPEN) THEN
  REWRITE_TAC[AFFINE_AFFINE_HULL; OPEN_IN_RELATIVE_INTERIOR] THEN
  ASM_SIMP_TAC[BOUNDED_RELATIVE_INTERIOR; RELATIVE_FRONTIER_RELATIVE_INTERIOR;
               AFF_DIM_AFFINE_HULL; RELATIVE_INTERIOR_EQ_EMPTY]);;

let DIMENSION_SPHERE_INTER_AFFINE = prove
 (`!a:real^N r t.
        &0 < r /\ affine t /\ a IN t
        ==> dimension(sphere(a,r) INTER t) = aff_dim t - &1`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM FRONTIER_CBALL] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RELATIVE_FRONTIER_CONVEX_INTER_AFFINE o
    rand o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_CBALL; INTERIOR_CBALL; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) DIMENSION_RELATIVE_FRONTIER_CONVEX o
    lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[BOUNDED_INTER; BOUNDED_CBALL] THEN
    ASM_SIMP_TAC[CONVEX_INTER; CONVEX_CBALL; AFFINE_IMP_CONVEX] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    ASM_MESON_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE];
    DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC] THEN
  ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[HULL_P] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
  MATCH_MP_TAC AFFINE_HULL_AFFINE_INTER_NONEMPTY_INTERIOR THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; INTERIOR_CBALL; IN_INTER] THEN
  ASM_MESON_TAC[CENTRE_IN_BALL]);;

let DIMENSION_SPHERE = prove
 (`!a:real^N r. dimension(sphere(a,r)) =
                if &0 < r then &(dimindex(:N)) - &1
                else if r = &0 then &0 else -- &1`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r:real = &0` THEN
  ASM_SIMP_TAC[REAL_LT_REFL; SPHERE_SING; DIMENSION_SING] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[DIMENSION_EQ_MINUS1; SPHERE_EQ_EMPTY] THENL
   [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
   [SET_RULE `s = s INTER UNIV`] THEN
  ASM_SIMP_TAC[DIMENSION_SPHERE_INTER_AFFINE; AFFINE_UNIV; IN_UNIV] THEN
  REWRITE_TAC[AFF_DIM_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Nonseparation: a "simple" set of dimension n can't be separated by sets   *)
(* of dimension <= n - 2.                                                    *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_OPEN_IN_CONVEX_DIFF_LOWDIM = prove
 (`!c s t:real^N->bool.
        convex c /\ open_in (subtopology euclidean c) s /\
        connected s /\ dimension t <= aff_dim c - &2
        ==> connected(s DIFF t)`,
  let lemma1 = prove
   (`!u s:real^N->bool.
          affine u /\ dimension s <= aff_dim u - &2 ==> connected(u DIFF s)`,
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `d:real^N->bool`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `subtopology euclidean u interior_of d:real^N->bool = {}`
    ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[INTERIOR_OF_RESTRICT] THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      MP_TAC(ISPECL [`u:real^N->bool`; `u INTER d:real^N->bool`]
        DIMENSION_LT_FULL_ALT) THEN
      ASM_SIMP_TAC[AFFINE_IMP_CONVEX; INTER_SUBSET] THEN
      MATCH_MP_TAC(TAUT `p ==> (p <=> q /\ r) ==> r`) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
       `d:int <= u - &2 ==> d' <= d ==> d' < u`)) THEN
      SIMP_TAC[DIMENSION_SUBSET; INTER_SUBSET];
      ALL_TAC] THEN
    REWRITE_TAC[CONNECTED_SEPARATION; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u1:real^N->bool`; `u2:real^N->bool`] THEN
    STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (SET_RULE
     `u1 UNION u2 = u DIFF d ==> u INTER u1 = u1 /\ u INTER u2 = u2`)) THEN
    SUBGOAL_THEN `(u:real^N->bool) SUBSET closure u1 UNION closure u2`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o
        GEN_REWRITE_RULE I [INTERIOR_OF_EQ_EMPTY_COMPLEMENT]) THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      SUBST1_TAC(SYM(ASSUME `u1 UNION u2:real^N->bool = u DIFF d`)) THEN
      REWRITE_TAC[CLOSURE_OF_UNION] THEN
      ASM_REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
      SET_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `v:real^N->bool = u DIFF closure u1` THEN
    MP_TAC(ISPECL [`u:real^N->bool`; `v:real^N->bool`]
      DIMENSION_RELATIVE_FRONTIER_NONDENSE_OPEN) THEN
    SUBGOAL_THEN `~(v:real^N->bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `open_in (subtopology euclidean u) (v:real^N->bool)`
    ASSUME_TAC THENL
     [EXPAND_TAC "v" THEN SIMP_TAC[OPEN_IN_DIFF_CLOSED; CLOSED_CLOSURE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`u:real^N->bool`; `v:real^N->bool`]
      AFFINE_HULL_OPEN_IN_AFFINE) THEN
    ASM_REWRITE_TAC[RELATIVE_FRONTIER_FRONTIER_OF] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `!t. s SUBSET t /\ t SUBSET u /\ ~(t = u)
        ==> ~(s = u)`) THEN
      EXISTS_TAC `subtopology euclidean u closure_of u2:real^N->bool` THEN
      REWRITE_TAC[CLOSURE_OF_SUBSET_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC(INT_ARITH
       `!x. d:int <= x /\ x < n ==> ~(d = n)`) THEN
      EXISTS_TAC `dimension(d:real^N->bool)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC DIMENSION_SUBSET; ASM_INT_ARITH_TAC] THEN
      ASM_SIMP_TAC[frontier_of; INTERIOR_OF_OPEN_IN] THEN
      MP_TAC(ISPECL [`subtopology euclidean (u:real^N->bool)`;
            `u DIFF subtopology euclidean u closure_of u1:real^N->bool`;
            `subtopology euclidean u closure_of u2:real^N->bool`]
          CLOSURE_OF_MONO) THEN
      REWRITE_TAC[CLOSURE_OF_CLOSURE_OF] THEN
      ASM_REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
      ASM_REWRITE_TAC[SET_RULE `u DIFF u INTER s = u DIFF s`] THEN
      ASM SET_TAC[]]) in
  let lemma2 = prove
   (`!u s t:real^N->bool.
          affine u /\ open_in (subtopology euclidean u) s /\
          connected s /\ dimension t <= aff_dim u - &2
          ==> connected(s DIFF t)`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    MATCH_MP_TAC CONNECTED_CONNECTED_DIFF THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`;
                     `u DIFF t:real^N->bool`; `u:real^N->bool`]
        CLOSURE_OPEN_IN_INTER_CLOSURE) THEN
      ASM_REWRITE_TAC[SUBSET_DIFF] THEN
      MP_TAC(ISPECL
       [`u:real^N->bool`; `u DIFF closure(u DIFF t):real^N->bool`]
       DIMENSION_OPEN_IN_CONVEX) THEN
      ASM_SIMP_TAC[AFFINE_IMP_CONVEX; OPEN_IN_DIFF_CLOSED; CLOSED_CLOSURE] THEN
      COND_CASES_TAC THENL
       [DISCH_THEN(K ALL_TAC) THEN
        ASM_SIMP_TAC[SET_RULE
         `s SUBSET u /\ u DIFF closure(u DIFF t) = {}
          ==> s INTER closure (u DIFF t) = s`] THEN
        ASM_SIMP_TAC[SET_RULE
         `s SUBSET u ==> s INTER (u DIFF t) = s DIFF t`] THEN
        MESON_TAC[CLOSURE_SUBSET];
        MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
         `d:int <= u - &2 ==> d' <= d ==> ~(d' = u)`)) THEN
        MATCH_MP_TAC DIMENSION_SUBSET THEN
        MP_TAC(ISPEC `u DIFF t:real^N->bool` CLOSURE_SUBSET) THEN SET_TAC[]];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_CONTAINS_BALL]) THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `ball(x:real^N,r) INTER u` THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL; IN_INTER] THEN
      CONJ_TAC THENL[ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[INTER_COMM; OPEN_BALL; OPEN_IN_OPEN_INTER;
                      OPEN_IN_SUBSET_TRANS];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`ball(x:real^N,r) INTER u`; `u:real^N->bool`]
          HOMEOMORPHIC_RELATIVELY_OPEN_CONVEX_SETS) THEN
      ASM_SIMP_TAC[CONVEX_BALL; CONVEX_INTER; AFFINE_IMP_CONVEX] THEN
      ASM_SIMP_TAC[HULL_P; OPEN_IN_REFL] THEN
      ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
      ONCE_REWRITE_TAC[INTER_COMM] THEN
      SUBGOAL_THEN `affine hull (u INTER ball(x:real^N,r)) = affine hull u`
      SUBST1_TAC THENL
       [MATCH_MP_TAC AFFINE_HULL_CONVEX_INTER_OPEN THEN
        ASM_SIMP_TAC[AFFINE_IMP_CONVEX; OPEN_BALL; GSYM MEMBER_NOT_EMPTY] THEN
        EXISTS_TAC `x:real^N` THEN
        ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN
        ASM SET_TAC[];
        ASM_SIMP_TAC[HULL_P; OPEN_IN_OPEN_INTER; OPEN_BALL]] THEN
      REWRITE_TAC[homeomorphic; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`u:real^N->bool`;
                     `IMAGE (f:real^N->real^N) (ball(x,r) INTER u INTER t)`]
          lemma1) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [TRANS_TAC INT_LE_TRANS `dimension(t:real^N->bool)` THEN
        ASM_REWRITE_TAC[] THEN
        TRANS_TAC INT_LE_TRANS
          `dimension(ball(x:real^N,r) INTER u INTER t)` THEN
        ASM_SIMP_TAC[DIMENSION_SUBSET; INTER_SUBSET; GSYM INTER_ASSOC] THEN
        MATCH_MP_TAC INT_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC HOMEOMORPHIC_DIMENSION;
        MATCH_MP_TAC EQ_IMP THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC HOMEOMORPHIC_CONNECTEDNESS] THEN
      REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
       (ONCE_REWRITE_RULE[IMP_CONJ] HOMEOMORPHISM_OF_SUBSETS)) THEN
      REWRITE_TAC[INTER_SUBSET; SUBSET_DIFF; SUBSET_UNIV] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHISM]) THEN ASM SET_TAC[]]) in
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[CONNECTED_EMPTY; EMPTY_DIFF] THEN
  MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
  EXISTS_TAC `(relative_interior c INTER s) DIFF t:real^N->bool` THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (affine hull c))
            (relative_interior c INTER s:real^N->bool)`
  ASSUME_TAC THENL
   [TRANS_TAC OPEN_IN_TRANS `relative_interior c:real^N->bool` THEN
    ASM_REWRITE_TAC[OPEN_IN_RELATIVE_INTERIOR] THEN
    MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
    EXISTS_TAC `c:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; OPEN_IN_REFL; RELATIVE_INTERIOR_SUBSET];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC lemma2 THEN
    EXISTS_TAC `affine hull s:real^N->bool` THEN
    REWRITE_TAC[OPEN_IN_RELATIVE_INTERIOR] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_HULL; AFFINE_AFFINE_HULL] THEN
    MP_TAC(ISPECL [`c:real^N->bool`; `s:real^N->bool`]
        AFFINE_HULL_OPEN_IN_CONVEX) THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
    MATCH_MP_TAC CONNECTED_WITH_RELATIVE_INTERIOR_OPEN_IN_CONVEX THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `c:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
    MP_TAC(ISPECL
     [`relative_interior c INTER s:real^N->bool`;
      `affine hull c DIFF t:real^N->bool`;
      `affine hull c:real^N->bool`] CLOSURE_OPEN_IN_INTER_CLOSURE) THEN
    ASM_REWRITE_TAC[SUBSET_DIFF] THEN
    MP_TAC(ISPECL
     [`affine hull c:real^N->bool`;
      `affine hull c DIFF closure(affine hull c DIFF t):real^N->bool`]
     DIMENSION_OPEN_IN_CONVEX) THEN
    ASM_SIMP_TAC[AFFINE_IMP_CONVEX; OPEN_IN_DIFF_CLOSED; CLOSED_CLOSURE;
                 AFFINE_AFFINE_HULL] THEN
    COND_CASES_TAC THENL
     [DISCH_THEN(K ALL_TAC) THEN
      ASM_SIMP_TAC[RELATIVE_INTERIOR_SUBSET; HULL_SUBSET; SET_RULE
       `relative_interior c SUBSET c /\ c SUBSET u /\
        u DIFF closure(u DIFF t) = {}
        ==> (relative_interior c INTER s) INTER closure (u DIFF t) =
            relative_interior c INTER s /\
            (relative_interior c INTER s) INTER (u DIFF t) =
            (relative_interior c INTER s) DIFF t`] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ONCE_REWRITE_TAC[INTER_COMM] THEN
      MP_TAC(ISPECL
       [`s:real^N->bool`; `relative_interior c:real^N->bool`; `c:real^N->bool`]
       CLOSURE_OPEN_IN_INTER_CLOSURE) THEN
      REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN
      ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      TRANS_TAC SUBSET_TRANS `s:real^N->bool` THEN
      REWRITE_TAC[SUBSET_DIFF] THEN
      TRANS_TAC SUBSET_TRANS `closure s:real^N->bool` THEN
      REWRITE_TAC[CLOSURE_SUBSET] THEN MATCH_MP_TAC SUBSET_CLOSURE THEN
      MATCH_MP_TAC(SET_RULE
       `c SUBSET closure c /\ s SUBSET c ==> s SUBSET s INTER closure c`) THEN
      ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; CLOSURE_SUBSET];
      MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
      REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
       `d:int <= u - &2 ==> d' <= d ==> ~(d' = u)`)) THEN
      MATCH_MP_TAC DIMENSION_SUBSET THEN
      MP_TAC(ISPEC `affine hull c DIFF t:real^N->bool` CLOSURE_SUBSET) THEN
      SET_TAC[]]]);;

let CONNECTED_CONVEX_DIFF_LOWDIM = prove
 (`!s t:real^N->bool.
        convex s /\ dimension t <= aff_dim s - &2 ==> connected(s DIFF t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_OPEN_IN_CONVEX_DIFF_LOWDIM THEN
  EXISTS_TAC `s:real^N->bool` THEN
  ASM_SIMP_TAC[CONVEX_CONNECTED; OPEN_IN_REFL]);;

let CONNECTED_OPEN_IN_DIFF_LOWDIM = prove
 (`!s t:real^N->bool.
        open_in (subtopology euclidean (affine hull s)) s /\
        connected s /\
        dimension t <= aff_dim s - &2
        ==> connected(s DIFF t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_OPEN_IN_CONVEX_DIFF_LOWDIM THEN
  EXISTS_TAC `affine hull s:real^N->bool` THEN
  ASM_SIMP_TAC[AFFINE_IMP_CONVEX; AFF_DIM_AFFINE_HULL; AFFINE_AFFINE_HULL]);;

let CONNECTED_OPEN_DIFF_LOWDIM = prove
 (`!s t:real^N->bool.
        open s /\ connected s /\ dimension t <= &(dimindex(:N)) - &2
        ==> connected(s DIFF t)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[EMPTY_DIFF; CONNECTED_EMPTY] THEN
  MATCH_MP_TAC CONNECTED_OPEN_IN_DIFF_LOWDIM THEN
  ASM_SIMP_TAC[OPEN_SUBSET; HULL_SUBSET; AFF_DIM_OPEN]);;

let CONNECTED_FULL_CONVEX_DIFF_LOWDIM = prove
 (`!s:real^N->bool t.
        convex s /\ ~(interior s = {}) /\ dimension t <= &(dimindex(:N)) - &2
        ==> connected(s DIFF t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_CONVEX_DIFF_LOWDIM THEN
  ASM_SIMP_TAC[AFF_DIM_NONEMPTY_INTERIOR]);;

let CONNECTED_UNIV_DIFF_LOWDIM = prove
 (`!s:real^N->bool.
        dimension s <= &(dimindex(:N)) - &2 ==> connected((:real^N) DIFF s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_FULL_CONVEX_DIFF_LOWDIM THEN
  ASM_REWRITE_TAC[CONVEX_UNIV; INTERIOR_UNIV; UNIV_NOT_EMPTY]);;

let CONNECTED_FULL_REGULAR_DIFF_LOWDIM = prove
 (`!s:real^N->bool t.
        s SUBSET closure(interior s) /\
        connected(interior s) /\
        dimension t <= &(dimindex(:N)) - &2
        ==> connected(s DIFF t)`,
  let lemma = prove
   (`!s t:real^N->bool.
          open s /\ interior t = {} ==> s SUBSET closure(s DIFF t)`,
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
    ONCE_REWRITE_TAC[SET_RULE `s SUBSET t <=> s INTER t = s`] THEN
    W(MP_TAC o PART_MATCH (rand o rand) OPEN_INTER_CLOSURE_EQ o
      lhand o snd) THEN
    ASM_REWRITE_TAC[CLOSURE_COMPLEMENT] THEN SET_TAC[]) in
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
  EXISTS_TAC `interior s DIFF t:real^N->bool` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_OPEN_DIFF_LOWDIM THEN
    ASM_REWRITE_TAC[OPEN_INTERIOR];
    MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    TRANS_TAC SUBSET_TRANS `closure(interior s):real^N->bool` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
    MATCH_MP_TAC lemma THEN REWRITE_TAC[OPEN_INTERIOR] THEN
    MP_TAC(SPEC `t:real^N->bool` DIMENSION_NONEMPTY_INTERIOR) THEN
    ASM_CASES_TAC `interior t:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Absolute retracts (AR), absolute neighbourhood retracts (ANR) and also    *)
(* Euclidean neighbourhood retracts (ENR). We define AR and ANR by           *)
(* specializing the standard definitions for a set in R^n to embedding in    *)
(* spaces inside R^{n+1}. This turns out to be sufficient (since any set in  *)
(* R^n can be embedded as a closed subset of a convex subset of R^{n+1}) to  *)
(* derive the usual definitions, but we need to split them into two          *)
(* implications because of the lack of type quantifiers. Then ENR turns out  *)
(* to be equivalent to ANR plus local compactness.                           *)
(* ------------------------------------------------------------------------- *)

let AR = new_definition
 `AR(s:real^N->bool) <=>
        !u s':real^(N,1)finite_sum->bool.
                s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
                ==> s' retract_of u`;;

let ANR = new_definition
 `ANR(s:real^N->bool) <=>
        !u s':real^(N,1)finite_sum->bool.
                s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
                ==> ?t. open_in (subtopology euclidean u) t /\
                        s' retract_of t`;;

let ENR = new_definition
 `ENR s <=> ?u. open u /\ s retract_of u`;;

(* ------------------------------------------------------------------------- *)
(* First, show that we do indeed get the "usual" properties of ARs and ANRs. *)
(* ------------------------------------------------------------------------- *)

let AR_IMP_ABSOLUTE_EXTENSOR = prove
 (`!f:real^M->real^N u t s.
        AR s /\ f continuous_on t /\ IMAGE f t SUBSET s /\
        closed_in (subtopology euclidean u) t
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET s /\
                !x. x IN t ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?c s':real^(N,1)finite_sum->bool.
        convex c /\ ~(c = {}) /\ closed_in (subtopology euclidean c) s' /\
        (s:real^N->bool) homeomorphic s'`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_CLOSED_IN_CONVEX THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; GSYM INT_OF_NUM_ADD] THEN
    REWRITE_TAC[INT_ARITH `x:int < y + &1 <=> x <= y`; AFF_DIM_LE_UNIV];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [AR]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`c:real^(N,1)finite_sum->bool`; `s':real^(N,1)finite_sum->bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`g:real^N->real^(N,1)finite_sum`; `h:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN MP_TAC(ISPECL
   [`(g:real^N->real^(N,1)finite_sum) o (f:real^M->real^N)`;
    `c:real^(N,1)finite_sum->bool`; `u:real^M->bool`; `t:real^M->bool`]
        DUGUNDJI) THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^(N,1)finite_sum`
    STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^(N,1)finite_sum->real^(N,1)finite_sum` THEN
  STRIP_TAC THEN
  EXISTS_TAC `(h:real^(N,1)finite_sum->real^N) o r o
              (f':real^M->real^(N,1)finite_sum)` THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let AR_IMP_ABSOLUTE_RETRACT = prove
 (`!s:real^N->bool u s':real^M->bool.
        AR s /\ s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
        ==> s' retract_of u`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:real^N->real^M`; `h:real^M->real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^M->real^N`; `u:real^M->bool`; `s':real^M->bool`;
                 `s:real^N->bool`] AR_IMP_ABSOLUTE_EXTENSOR) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `h':real^M->real^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[retract_of; retraction] THEN
  EXISTS_TAC `(g:real^N->real^M) o (h':real^M->real^N)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let AR_IMP_ABSOLUTE_RETRACT_UNIV = prove
 (`!s:real^N->bool s':real^M->bool.
    AR s /\ s homeomorphic s' /\ closed s' ==> s' retract_of (:real^M)`,
  MESON_TAC[AR_IMP_ABSOLUTE_RETRACT;
            TOPSPACE_EUCLIDEAN; SUBTOPOLOGY_UNIV; OPEN_IN; CLOSED_IN]);;

let ABSOLUTE_EXTENSOR_IMP_AR = prove
 (`!s:real^N->bool.
        (!f:real^(N,1)finite_sum->real^N u t.
             f continuous_on t /\ IMAGE f t SUBSET s /\
             closed_in (subtopology euclidean u) t
             ==> ?g. g continuous_on u /\ IMAGE g u SUBSET s /\
                     !x. x IN t ==> g x = f x)
        ==> AR s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AR] THEN MAP_EVERY X_GEN_TAC
   [`u:real^(N,1)finite_sum->bool`; `t:real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`g:real^N->real^(N,1)finite_sum`; `h:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o ISPECL
    [`h:real^(N,1)finite_sum->real^N`;
     `u:real^(N,1)finite_sum->bool`; `t:real^(N,1)finite_sum->bool`]) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN(X_CHOOSE_THEN
    `h':real^(N,1)finite_sum->real^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[retract_of; retraction] THEN
  EXISTS_TAC `(g:real^N->real^(N,1)finite_sum) o
              (h':real^(N,1)finite_sum->real^N)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let AR_EQ_ABSOLUTE_EXTENSOR = prove
 (`!s:real^N->bool.
        AR s <=>
        (!f:real^(N,1)finite_sum->real^N u t.
             f continuous_on t /\ IMAGE f t SUBSET s /\
             closed_in (subtopology euclidean u) t
             ==> ?g. g continuous_on u /\ IMAGE g u SUBSET s /\
                     !x. x IN t ==> g x = f x)`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[AR_IMP_ABSOLUTE_EXTENSOR; ABSOLUTE_EXTENSOR_IMP_AR]);;

let AR_IMP_RETRACT = prove
 (`!s u:real^N->bool.
        AR s /\ closed_in (subtopology euclidean u) s ==> s retract_of u`,
  MESON_TAC[AR_IMP_ABSOLUTE_RETRACT; HOMEOMORPHIC_REFL]);;

let HOMEOMORPHIC_ARNESS = prove
 (`!s:real^M->bool t:real^N->bool.
      s homeomorphic t ==> (AR s <=> AR t)`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool.
      s homeomorphic t /\ AR t ==> AR s`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[AR] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ]
      AR_IMP_ABSOLUTE_RETRACT)) THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC HOMEOMORPHIC_TRANS `s:real^M->bool` THEN
    ASM_MESON_TAC[HOMEOMORPHIC_SYM]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN POP_ASSUM MP_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM]; ALL_TAC] THEN
  ASM_MESON_TAC[lemma]);;

let AR_TRANSLATION = prove
 (`!a:real^N s. AR(IMAGE (\x. a + x) s) <=> AR s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ARNESS THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION_SELF]);;

add_translation_invariants [AR_TRANSLATION];;

let AR_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (AR(IMAGE f s) <=> AR s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ARNESS THEN
  ASM_MESON_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF]);;

add_linear_invariants [AR_LINEAR_IMAGE_EQ];;

let HOMEOMORPHISM_ARNESS = prove
 (`!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (AR(IMAGE f k) <=> AR k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ARNESS THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
          HOMEOMORPHISM_OF_SUBSETS)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[]);;

let ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR = prove
 (`!f:real^M->real^N u t s.
        ANR s /\ f continuous_on t /\ IMAGE f t SUBSET s /\
        closed_in (subtopology euclidean u) t
        ==> ?v g. t SUBSET v /\ open_in (subtopology euclidean u) v /\
                  g continuous_on v /\ IMAGE g v SUBSET s /\
                  !x. x IN t ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?c s':real^(N,1)finite_sum->bool.
        convex c /\ ~(c = {}) /\ closed_in (subtopology euclidean c) s' /\
        (s:real^N->bool) homeomorphic s'`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_CLOSED_IN_CONVEX THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; GSYM INT_OF_NUM_ADD] THEN
    REWRITE_TAC[INT_ARITH `x:int < y + &1 <=> x <= y`; AFF_DIM_LE_UNIV];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ANR]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`c:real^(N,1)finite_sum->bool`; `s':real^(N,1)finite_sum->bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN
   `d:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`g:real^N->real^(N,1)finite_sum`; `h:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN MP_TAC(ISPECL
   [`(g:real^N->real^(N,1)finite_sum) o (f:real^M->real^N)`;
    `c:real^(N,1)finite_sum->bool`; `u:real^M->bool`; `t:real^M->bool`]
        DUGUNDJI) THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^(N,1)finite_sum`
    STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^(N,1)finite_sum->real^(N,1)finite_sum` THEN
  STRIP_TAC THEN
  EXISTS_TAC `{x | x IN u /\ (f':real^M->real^(N,1)finite_sum) x IN d}` THEN
  EXISTS_TAC `(h:real^(N,1)finite_sum->real^N) o r o
              (f':real^M->real^(N,1)finite_sum)` THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN REPEAT CONJ_TAC THENL
   [REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET)) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN ASM_MESON_TAC[];
    REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
    REWRITE_TAC[IMAGE_o] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT = prove
 (`!s:real^N->bool u s':real^M->bool.
        ANR s /\ s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
        ==> ?v. open_in (subtopology euclidean u) v /\
                s' retract_of v`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:real^N->real^M`; `h:real^M->real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^M->real^N`; `u:real^M->bool`; `s':real^M->bool`;
                `s:real^N->bool`] ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^M->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `h':real^M->real^N` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[retract_of; retraction] THEN
  EXISTS_TAC `(g:real^N->real^M) o (h':real^M->real^N)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT_UNIV = prove
 (`!s:real^N->bool s':real^M->bool.
    ANR s /\ s homeomorphic s' /\ closed s' ==> ?v. open v /\ s' retract_of v`,
  MESON_TAC[ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT;
            TOPSPACE_EUCLIDEAN; SUBTOPOLOGY_UNIV; OPEN_IN; CLOSED_IN]);;

let ABSOLUTE_NEIGHBOURHOOD_EXTENSOR_IMP_ANR = prove
 (`!s:real^N->bool.
        (!f:real^(N,1)finite_sum->real^N u t.
             f continuous_on t /\ IMAGE f t SUBSET s /\
             closed_in (subtopology euclidean u) t
             ==> ?v g. t SUBSET v /\ open_in  (subtopology euclidean u) v /\
                       g continuous_on v /\ IMAGE g v SUBSET s /\
                       !x. x IN t ==> g x = f x)
        ==> ANR s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ANR] THEN MAP_EVERY X_GEN_TAC
   [`u:real^(N,1)finite_sum->bool`; `t:real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`g:real^N->real^(N,1)finite_sum`; `h:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o ISPECL
    [`h:real^(N,1)finite_sum->real^N`;
     `u:real^(N,1)finite_sum->bool`; `t:real^(N,1)finite_sum->bool`]) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^(N,1)finite_sum->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `h':real^(N,1)finite_sum->real^N`
    STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[retract_of; retraction] THEN
  EXISTS_TAC `(g:real^N->real^(N,1)finite_sum) o
              (h':real^(N,1)finite_sum->real^N)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let ANR_EQ_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR = prove
 (`!s:real^N->bool.
        ANR s <=>
        (!f:real^(N,1)finite_sum->real^N u t.
             f continuous_on t /\ IMAGE f t SUBSET s /\
             closed_in (subtopology euclidean u) t
             ==> ?v g. t SUBSET v /\ open_in  (subtopology euclidean u) v /\
                       g continuous_on v /\ IMAGE g v SUBSET s /\
                       !x. x IN t ==> g x = f x)`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR;
           ABSOLUTE_NEIGHBOURHOOD_EXTENSOR_IMP_ANR]);;

let ANR_IMP_ABSOLUTE_CLOSED_NEIGHBOURHOOD_RETRACT = prove
 (`!s:real^N->bool u s':real^M->bool.
        ANR s /\ s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
        ==> ?v w. open_in (subtopology euclidean u) v /\
                  closed_in (subtopology euclidean u) w /\
                  s' SUBSET v /\ v SUBSET w /\ s' retract_of w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?z. open_in (subtopology euclidean u) z /\
                    (s':real^M->bool) retract_of z`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
    [`s':real^M->bool`; `u DIFF z:real^M->bool`; `u:real^M->bool`]
    SEPARATION_NORMAL_LOCAL) THEN
  ASM_SIMP_TAC[CLOSED_IN_INTER; CLOSED_IN_REFL; CLOSED_IN_DIFF] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `v:real^M->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u DIFF w:real^M->bool` THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] RETRACT_OF_SUBSET)) THEN
  ASM SET_TAC[]);;

let ANR_IMP_ABSOLUTE_CLOSED_NEIGHBOURHOOD_EXTENSOR = prove
 (`!f:real^M->real^N u t s.
        ANR s /\ f continuous_on t /\ IMAGE f t SUBSET s /\
        closed_in (subtopology euclidean u) t
        ==> ?v w g. open_in (subtopology euclidean u) v /\
                    closed_in (subtopology euclidean u) w /\
                    t SUBSET v /\ v SUBSET w /\
                    g continuous_on w /\ IMAGE g w SUBSET s /\
                    !x. x IN t ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?v g. t SUBSET v /\ open_in (subtopology euclidean u) v /\
          g continuous_on v /\ IMAGE g v SUBSET s /\
          !x. x IN t ==> g x = (f:real^M->real^N) x`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
    [`t:real^M->bool`; `u DIFF v:real^M->bool`; `u:real^M->bool`]
    SEPARATION_NORMAL_LOCAL) THEN
  ASM_SIMP_TAC[CLOSED_IN_INTER; CLOSED_IN_REFL; CLOSED_IN_DIFF] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `w:real^M->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u DIFF z:real^M->bool` THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
  EXISTS_TAC `g:real^M->real^N` THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
  ASM SET_TAC[]);;

let ANR_IMP_NEIGHBOURHOOD_RETRACT = prove
 (`!s:real^N->bool u.
        ANR s /\ closed_in (subtopology euclidean u) s
        ==> ?v. open_in (subtopology euclidean u) v /\
                s retract_of v`,
  MESON_TAC[ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT; HOMEOMORPHIC_REFL]);;

let ANR_IMP_CLOSED_NEIGHBOURHOOD_RETRACT = prove
 (`!s:real^N->bool u.
        ANR s /\ closed_in (subtopology euclidean u) s
        ==> ?v w. open_in (subtopology euclidean u) v /\
                  closed_in (subtopology euclidean u) w /\
                  s SUBSET v /\ v SUBSET w /\ s retract_of w`,
  MESON_TAC[ANR_IMP_ABSOLUTE_CLOSED_NEIGHBOURHOOD_RETRACT;
            HOMEOMORPHIC_REFL]);;

let HOMEOMORPHIC_ANRNESS = prove
 (`!s:real^M->bool t:real^N->bool.
      s homeomorphic t ==> (ANR s <=> ANR t)`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool.
      s homeomorphic t /\ ANR t ==> ANR s`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[ANR] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ]
      ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT)) THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC HOMEOMORPHIC_TRANS `s:real^M->bool` THEN
    ASM_MESON_TAC[HOMEOMORPHIC_SYM]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN POP_ASSUM MP_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM]; ALL_TAC] THEN
  ASM_MESON_TAC[lemma]);;

let ANR_TRANSLATION = prove
 (`!a:real^N s. ANR(IMAGE (\x. a + x) s) <=> ANR s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ANRNESS THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION_SELF]);;

add_translation_invariants [ANR_TRANSLATION];;

let ANR_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (ANR(IMAGE f s) <=> ANR s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ANRNESS THEN
  ASM_MESON_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF]);;

add_linear_invariants [ANR_LINEAR_IMAGE_EQ];;

let HOMEOMORPHISM_ANRNESS = prove
 (`!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (ANR(IMAGE f k) <=> ANR k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ANRNESS THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
          HOMEOMORPHISM_OF_SUBSETS)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[]);;

let HOMOTOPIC_ON_NEIGHBOURHOOD_INTO_ANR = prove
 (`!f g:real^M->real^N s t v.
        ANR v /\
        f continuous_on s /\ IMAGE f s SUBSET v /\
        g continuous_on s /\ IMAGE g s SUBSET v /\
        t SUBSET s /\ (!x. x IN t ==> f x = g x)
        ==> ?u. open_in (subtopology euclidean s) u /\ t SUBSET u /\
                homotopic_with (\h. !x. x IN t ==> h x = f x)
                 (subtopology euclidean u,subtopology euclidean v) f g`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `c = {x | x IN s /\ (f:real^M->real^N) x = g x}` THEN
  SUBGOAL_THEN `closed_in (subtopology euclidean s) (c:real^M->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_SUB];
    ALL_TAC] THEN
  ABBREV_TAC `fg:real^(1,M)finite_sum->real^N =
        \x. if fstcart x = vec 1 then g(sndcart x) else f(sndcart x)` THEN
  MP_TAC(ISPECL
   [`fg:real^(1,M)finite_sum->real^N`;
    `(interval[vec 0,vec 1] PCROSS s):real^(1,M)finite_sum->bool`;
    `interval[vec 0,vec 1] PCROSS c UNION
     {vec 0:real^1,vec 1} PCROSS (s:real^M->bool)`;
    `v:real^N->bool`]
   ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
  ASM_SIMP_TAC[CLOSED_IN_PCROSS_EQ; CLOSED_IN_REFL; CLOSED_IN_INSERT;
               CLOSED_IN_EMPTY; ENDS_IN_UNIT_INTERVAL; CLOSED_IN_UNION] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `{a,b} = {a} UNION {b}`] THEN
      REWRITE_TAC[PCROSS_UNION] THEN REWRITE_TAC[GSYM UNION_ASSOC] THEN
      ONCE_REWRITE_TAC[UNION_COMM] THEN
      EXPAND_TAC "fg" THEN MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
      ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1] PCROSS (s:real^M->bool)` THEN
        ASM_SIMP_TAC[CLOSED_IN_PCROSS_EQ; CLOSED_IN_REFL; CLOSED_IN_INSERT;
                 CLOSED_IN_EMPTY; ENDS_IN_UNIT_INTERVAL; CLOSED_IN_UNION] THEN
        REWRITE_TAC[SUBSET_UNION] THEN
        REWRITE_TAC[SUBSET_PCROSS; UNION_SUBSET; UNIT_INTERVAL_NONEMPTY;
                    INSERT_SUBSET; EMPTY_SUBSET; ENDS_IN_UNIT_INTERVAL;
                    NOT_INSERT_EMPTY; SUBSET_REFL] THEN
        ASM_MESON_TAC[CLOSED_IN_IMP_SUBSET];
        ONCE_REWRITE_TAC[CONJ_ASSOC]] THEN
      CONJ_TAC THENL
       [CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[LINEAR_SNDCART; LINEAR_CONTINUOUS_ON] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_UNION] THEN
        SIMP_TAC[FORALL_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS] THEN
        ASM SET_TAC[];
        REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
        REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNION] THEN
        REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
        X_GEN_TAC `x:real^1` THEN
        ASM_CASES_TAC `x:real^1 = vec 1` THEN
        ASM_REWRITE_TAC[VEC_EQ; IN_INSERT; NOT_IN_EMPTY] THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM SET_TAC[]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_UNION] THEN
      SIMP_TAC[FORALL_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS] THEN
      EXPAND_TAC "fg" THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
      ASM SET_TAC[]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`u2:real^(1,M)finite_sum->bool`; `h:real^(1,M)finite_sum->real^N`] THEN
    REWRITE_TAC[UNION_SUBSET; FORALL_IN_UNION] THEN
    REWRITE_TAC[FORALL_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`interval[vec 0:real^1,vec 1]`;
                   `c:real^M->bool`; `s:real^M->bool`;
                   `u2:real^(1,M)finite_sum->bool`]
        TUBE_LEMMA_GEN) THEN
    ASM_REWRITE_TAC[COMPACT_INTERVAL; UNIT_INTERVAL_NONEMPTY] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
    X_GEN_TAC `u:real^M->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) HOMOTOPIC_WITH o snd) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    EXISTS_TAC `h:real^(1,M)finite_sum->real^N` THEN
    ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         CONTINUOUS_ON_SUBSET));
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `IMAGE h u2 SUBSET v ==> u SUBSET u2 ==> IMAGE h u SUBSET v`))] THEN
      ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[CONJ_ASSOC]] THEN
    SUBGOAL_THEN `!x:real^M. x IN u ==> x IN s` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `!x:real^M. x IN t ==> x IN c` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[IN_INSERT] THEN REPEAT DISCH_TAC THEN EXPAND_TAC "fg" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; VEC_EQ; ARITH_EQ] THEN
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Analogous properties of ENRs.                                             *)
(* ------------------------------------------------------------------------- *)

let ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT = prove
 (`!s:real^M->bool s':real^N->bool u.
        ENR s /\ s homeomorphic s' /\ s' SUBSET u
        ==> ?t'. open_in (subtopology euclidean u) t' /\ s' retract_of t'`,
  REWRITE_TAC[ENR; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`X:real^M->bool`; `Y:real^N->bool`;
    `K:real^N->bool`; `U:real^M->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `locally compact (Y:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RETRACT_OF_LOCALLY_COMPACT;
                  OPEN_IMP_LOCALLY_COMPACT; HOMEOMORPHIC_LOCAL_COMPACTNESS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?W:real^N->bool.
        open_in (subtopology euclidean K) W /\
        closed_in (subtopology euclidean W) Y`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC o
        MATCH_MP LOCALLY_COMPACT_CLOSED_IN_OPEN) THEN
    EXISTS_TAC `K INTER W:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; CLOSED_IN_CLOSED] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSED_IN_CLOSED]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`f:real^M->real^N`; `g:real^N->real^M`] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^N->real^M`; `W:real^N->bool`; `Y:real^N->bool`]
        TIETZE_UNBOUNDED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{x | x IN W /\ (h:real^N->real^M) x IN U}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `(:real^M)` THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; SUBSET_UNIV];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; retract_of; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^M->real^M` THEN STRIP_TAC THEN
  EXISTS_TAC `(f:real^M->real^N) o r o (h:real^N->real^M)` THEN
  SUBGOAL_THEN
   `(W:real^N->bool) SUBSET K /\ Y SUBSET W`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; CLOSED_IN_IMP_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o; o_THM] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
  REWRITE_TAC[IMAGE_o] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
  ASM SET_TAC[]);;

let ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT_UNIV = prove
 (`!s:real^M->bool s':real^N->bool.
        ENR s /\ s homeomorphic s' ==> ?t'. open t' /\ s' retract_of t'`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_IN] THEN
  ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
  MATCH_MP_TAC ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT THEN
  ASM_MESON_TAC[SUBSET_UNIV]);;

let HOMEOMORPHIC_ENRNESS = prove
 (`!s:real^M->bool t:real^N->bool.
      s homeomorphic t ==> (ENR s <=> ENR t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ENR] THENL
   [MP_TAC(ISPECL [`s:real^M->bool`; `t:real^N->bool`]
        ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT_UNIV);
    MP_TAC(ISPECL [`t:real^N->bool`; `s:real^M->bool`]
        ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT_UNIV)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[HOMEOMORPHIC_SYM]);;

let ENR_TRANSLATION = prove
 (`!a:real^N s. ENR(IMAGE (\x. a + x) s) <=> ENR s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ENRNESS THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION_SELF]);;

add_translation_invariants [ENR_TRANSLATION];;

let ENR_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (ENR(IMAGE f s) <=> ENR s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ENRNESS THEN
  ASM_MESON_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF]);;

add_linear_invariants [ENR_LINEAR_IMAGE_EQ];;

let HOMEOMORPHISM_ENRNESS = prove
 (`!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (ENR(IMAGE f k) <=> ENR k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ENRNESS THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
          HOMEOMORPHISM_OF_SUBSETS)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some relations among the concepts. We also relate AR to being a retract   *)
(* of UNIV, which is often a more convenient proxy in the closed case.       *)
(* ------------------------------------------------------------------------- *)

let AR_IMP_ANR = prove
 (`!s:real^N->bool. AR s ==> ANR s`,
  REWRITE_TAC[AR; ANR] THEN MESON_TAC[OPEN_IN_REFL; CLOSED_IN_IMP_SUBSET]);;

let ENR_IMP_ANR = prove
 (`!s:real^N->bool. ENR s ==> ANR s`,
  REWRITE_TAC[ANR] THEN
  MESON_TAC[ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT; CLOSED_IN_IMP_SUBSET]);;

let ENR_ANR = prove
 (`!s:real^N->bool. ENR s <=> ANR s /\ locally compact s`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN ASM_SIMP_TAC[ENR_IMP_ANR] THENL
   [ASM_MESON_TAC[ENR; RETRACT_OF_LOCALLY_COMPACT; OPEN_IMP_LOCALLY_COMPACT];
    SUBGOAL_THEN
     `?t. closed t /\
          (s:real^N->bool) homeomorphic (t:real^(N,1)finite_sum->bool)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC LOCALLY_COMPACT_HOMEOMORPHIC_CLOSED THEN
      ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ANR]) THEN
      DISCH_THEN(MP_TAC o SPECL
       [`(:real^(N,1)finite_sum)`; `t:real^(N,1)finite_sum->bool`]) THEN
      ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; GSYM OPEN_IN] THEN
      REWRITE_TAC[GSYM ENR] THEN ASM_MESON_TAC[HOMEOMORPHIC_ENRNESS]]]);;

let AR_ANR = prove
 (`!s:real^N->bool. AR s <=> ANR s /\ contractible s /\ ~(s = {})`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[AR_IMP_ANR] THENL
   [CONJ_TAC THENL
     [ALL_TAC;
      ASM_MESON_TAC[AR; HOMEOMORPHIC_EMPTY; RETRACT_OF_EMPTY;
           FORALL_UNWIND_THM2; CLOSED_IN_EMPTY; UNIV_NOT_EMPTY]] THEN
    SUBGOAL_THEN
     `?c s':real^(N,1)finite_sum->bool.
          convex c /\ ~(c = {}) /\ closed_in (subtopology euclidean c) s' /\
          (s:real^N->bool) homeomorphic s'`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_CLOSED_IN_CONVEX THEN
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; GSYM INT_OF_NUM_ADD] THEN
      REWRITE_TAC[INT_ARITH `x:int < y + &1 <=> x <= y`; AFF_DIM_LE_UNIV];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [AR]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`c:real^(N,1)finite_sum->bool`; `s':real^(N,1)finite_sum->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[HOMEOMORPHIC_SYM; HOMEOMORPHIC_CONTRACTIBLE;
                  RETRACT_OF_CONTRACTIBLE; CONVEX_IMP_CONTRACTIBLE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [contractible]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; HOMOTOPIC_WITH_EUCLIDEAN] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `h:real^(1,N)finite_sum->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[AR_EQ_ABSOLUTE_EXTENSOR] THEN
  MAP_EVERY X_GEN_TAC
   [`f:real^(N,1)finite_sum->real^N`; `w:real^(N,1)finite_sum->bool`;
    `t:real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o  ISPECL
    [`f:real^(N,1)finite_sum->real^N`; `w:real^(N,1)finite_sum->bool`;
     `t:real^(N,1)finite_sum->bool`]  o
    REWRITE_RULE[ANR_EQ_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
    [`u:real^(N,1)finite_sum->bool`; `g:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`t:real^(N,1)finite_sum->bool`; `w DIFF u:real^(N,1)finite_sum->bool`;
    `w:real^(N,1)finite_sum->bool`] SEPARATION_NORMAL_LOCAL) THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC
   [`v:real^(N,1)finite_sum->bool`; `v':real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`t:real^(N,1)finite_sum->bool`; `w DIFF v:real^(N,1)finite_sum->bool`;
    `w:real^(N,1)finite_sum->bool`; `vec 0:real^1`; `vec 1:real^1`]
        URYSOHN_LOCAL) THEN
  ASM_SIMP_TAC[SEGMENT_1; CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  REWRITE_TAC[DROP_VEC; REAL_POS] THEN
  X_GEN_TAC `e:real^(N,1)finite_sum->real^1` THEN STRIP_TAC THEN
  EXISTS_TAC
   `\x. if (x:real^(N,1)finite_sum) IN w DIFF v then a
        else (h:real^(1,N)finite_sum->real^N) (pastecart (e x) (g x))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `w:real^(N,1)finite_sum->bool = (w DIFF v) UNION (w DIFF v')`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th ->
        GEN_REWRITE_TAC RAND_CONV [th] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
        REWRITE_TAC[GSYM th]) THEN
    ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL; CONTINUOUS_ON_CONST] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
    ASM SET_TAC[];
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN RULE_ASSUM_TAC
     (REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS]) THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN
    COND_CASES_TAC THEN ASM SET_TAC[]]);;

let ANR_RETRACT_OF_ANR = prove
 (`!s t:real^N->bool. ANR t /\ s retract_of t ==> ANR s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[ANR_EQ_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^N->real^N` THEN STRIP_TAC THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^(N,1)finite_sum->real^N`
        STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(r:real^N->real^N) o (g:real^(N,1)finite_sum->real^N)` THEN
  ASM_SIMP_TAC[IMAGE_o; o_THM] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
  ASM SET_TAC[]);;

let AR_RETRACT_OF_AR = prove
 (`!s t:real^N->bool. AR t /\ s retract_of t ==> AR s`,
  REWRITE_TAC[AR_ANR] THEN
  MESON_TAC[ANR_RETRACT_OF_ANR; RETRACT_OF_CONTRACTIBLE; RETRACT_OF_EMPTY]);;

let ENR_RETRACT_OF_ENR = prove
 (`!s t:real^N->bool. ENR t /\ s retract_of t ==> ENR s`,
  REWRITE_TAC[ENR] THEN MESON_TAC[RETRACT_OF_TRANS]);;

let RETRACT_OF_UNIV = prove
 (`!s:real^N->bool. s retract_of (:real^N) <=> AR s /\ closed s`,
  GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC AR_RETRACT_OF_AR THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ABSOLUTE_EXTENSOR_IMP_AR THEN
    MESON_TAC[DUGUNDJI; CONVEX_UNIV; UNIV_NOT_EMPTY];
    MATCH_MP_TAC RETRACT_OF_CLOSED THEN ASM_MESON_TAC[CLOSED_UNIV];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        AR_IMP_ABSOLUTE_RETRACT)) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; HOMEOMORPHIC_REFL]]);;

let COMPACT_AR = prove
 (`!s. compact s /\ AR s <=> compact s /\ s retract_of (:real^N)`,
  REWRITE_TAC[RETRACT_OF_UNIV] THEN MESON_TAC[COMPACT_IMP_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* More properties of ARs, ANRs and ENRs.                                    *)
(* ------------------------------------------------------------------------- *)

let NOT_AR_EMPTY = prove
 (`~(AR({}:real^N->bool))`,
  REWRITE_TAC[AR_ANR]);;

let AR_IMP_NONEMPTY = prove
 (`!s:real^N->bool. AR s ==> ~(s = {})`,
  MESON_TAC[NOT_AR_EMPTY]);;

let ENR_EMPTY = prove
 (`ENR {}`,
  REWRITE_TAC[ENR; RETRACT_OF_EMPTY] THEN MESON_TAC[OPEN_EMPTY]);;

let ANR_EMPTY = prove
 (`ANR {}`,
  SIMP_TAC[ENR_EMPTY; ENR_IMP_ANR]);;

let CONVEX_IMP_AR = prove
 (`!s:real^N->bool. convex s /\ ~(s = {}) ==> AR s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTE_EXTENSOR_IMP_AR THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DUGUNDJI THEN
  ASM_REWRITE_TAC[]);;

let CONVEX_IMP_ANR = prove
 (`!s:real^N->bool. convex s ==> ANR s`,
  MESON_TAC[ANR_EMPTY; CONVEX_IMP_AR; AR_IMP_ANR]);;

let IS_INTERVAL_IMP_ENR = prove
 (`!s:real^N->bool. is_interval s ==> ENR s`,
  SIMP_TAC[ENR_ANR; IS_INTERVAL_IMP_LOCALLY_COMPACT] THEN
  SIMP_TAC[CONVEX_IMP_ANR; IS_INTERVAL_CONVEX]);;

let ENR_CONVEX_CLOSED = prove
 (`!s:real^N->bool. closed s /\ convex s ==> ENR s`,
  MESON_TAC[CONVEX_IMP_ANR; ENR_ANR; CLOSED_IMP_LOCALLY_COMPACT]);;

let AR_UNIV = prove
 (`AR(:real^N)`,
  MESON_TAC[CONVEX_IMP_AR; CONVEX_UNIV; UNIV_NOT_EMPTY]);;

let ANR_UNIV = prove
 (`ANR(:real^N)`,
  MESON_TAC[CONVEX_IMP_ANR; CONVEX_UNIV]);;

let ENR_UNIV = prove
 (`ENR(:real^N)`,
  MESON_TAC[ENR_CONVEX_CLOSED; CONVEX_UNIV; CLOSED_UNIV]);;

let AR_SING = prove
 (`!a:real^N. AR {a}`,
  SIMP_TAC[CONVEX_IMP_AR; CONVEX_SING; NOT_INSERT_EMPTY]);;

let ANR_SING = prove
 (`!a:real^N. ANR {a}`,
  SIMP_TAC[AR_IMP_ANR; AR_SING]);;

let ENR_SING = prove
 (`!a:real^N. ENR {a}`,
  SIMP_TAC[ENR_ANR; ANR_SING; CLOSED_IMP_LOCALLY_COMPACT; CLOSED_SING]);;

let ANR_OPEN_IN = prove
 (`!s t:real^N->bool.
        open_in (subtopology euclidean t) s /\ ANR t ==> ANR s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[ANR_EQ_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^(N,1)finite_sum->real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^(N,1)finite_sum->bool`
        STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{x | x IN w /\ (g:real^(N,1)finite_sum->real^N) x IN s}` THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN
    EXISTS_TAC `w:real^(N,1)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN ASM_MESON_TAC[];
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]]);;

let ENR_OPEN_IN = prove
 (`!s t:real^N->bool.
        open_in (subtopology euclidean t) s /\ ENR t ==> ENR s`,
  REWRITE_TAC[ENR_ANR] THEN MESON_TAC[ANR_OPEN_IN; LOCALLY_OPEN_SUBSET]);;

let ANR_NEIGHBORHOOD_RETRACT = prove
 (`!s t u:real^N->bool.
        s retract_of t /\ open_in (subtopology euclidean u) t /\ ANR u
        ==> ANR s`,
  MESON_TAC[ANR_OPEN_IN; ANR_RETRACT_OF_ANR]);;

let ENR_NEIGHBORHOOD_RETRACT = prove
 (`!s t u:real^N->bool.
        s retract_of t /\ open_in (subtopology euclidean u) t /\ ENR u
        ==> ENR s`,
  MESON_TAC[ENR_OPEN_IN; ENR_RETRACT_OF_ENR]);;

let ANR_RELATIVE_INTERIOR = prove
 (`!s. ANR(s) ==> ANR(relative_interior s)`,
  MESON_TAC[OPEN_IN_SET_RELATIVE_INTERIOR; ANR_OPEN_IN]);;

let ANR_DELETE = prove
 (`!s a:real^N. ANR(s) ==> ANR(s DELETE a)`,
  MESON_TAC[ANR_OPEN_IN; OPEN_IN_DELETE; OPEN_IN_REFL]);;

let ENR_RELATIVE_INTERIOR = prove
 (`!s. ENR(s) ==> ENR(relative_interior s)`,
  MESON_TAC[OPEN_IN_SET_RELATIVE_INTERIOR; ENR_OPEN_IN]);;

let ENR_DELETE = prove
 (`!s a:real^N. ENR(s) ==> ENR(s DELETE a)`,
  MESON_TAC[ENR_OPEN_IN; OPEN_IN_DELETE; OPEN_IN_REFL]);;

let OPEN_IMP_ENR = prove
 (`!s:real^N->bool. open s ==> ENR s`,
  REWRITE_TAC[OPEN_IN] THEN
  ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
  MESON_TAC[ENR_UNIV; ENR_OPEN_IN]);;

let OPEN_IMP_ANR = prove
 (`!s:real^N->bool. open s ==> ANR s`,
  SIMP_TAC[OPEN_IMP_ENR; ENR_IMP_ANR]);;

let ANR_BALL = prove
 (`!a:real^N r. ANR(ball(a,r))`,
  MESON_TAC[CONVEX_IMP_ANR; CONVEX_BALL]);;

let ENR_BALL = prove
 (`!a:real^N r. ENR(ball(a,r))`,
  SIMP_TAC[ENR_ANR; ANR_BALL; OPEN_IMP_LOCALLY_COMPACT; OPEN_BALL]);;

let AR_BALL = prove
 (`!a:real^N r. AR(ball(a,r)) <=> &0 < r`,
  SIMP_TAC[AR_ANR; BALL_EQ_EMPTY; ANR_BALL; CONVEX_BALL;
           CONVEX_IMP_CONTRACTIBLE; REAL_NOT_LE]);;

let ANR_CBALL = prove
 (`!a:real^N r. ANR(cball(a,r))`,
  MESON_TAC[CONVEX_IMP_ANR; CONVEX_CBALL]);;

let ENR_CBALL = prove
 (`!a:real^N r. ENR(cball(a,r))`,
  SIMP_TAC[ENR_ANR; ANR_CBALL; CLOSED_IMP_LOCALLY_COMPACT; CLOSED_CBALL]);;

let AR_CBALL = prove
 (`!a:real^N r. AR(cball(a,r)) <=> &0 <= r`,
  SIMP_TAC[AR_ANR; CBALL_EQ_EMPTY; ANR_CBALL; CONVEX_CBALL;
           CONVEX_IMP_CONTRACTIBLE; REAL_NOT_LT]);;

let ANR_INTERVAL = prove
 (`(!a b:real^N. ANR(interval[a,b])) /\ (!a b:real^N. ANR(interval(a,b)))`,
  SIMP_TAC[CONVEX_IMP_ANR; CONVEX_INTERVAL; CLOSED_INTERVAL;
           OPEN_IMP_ANR; OPEN_INTERVAL]);;

let ENR_INTERVAL = prove
 (`(!a b:real^N. ENR(interval[a,b])) /\ (!a b:real^N. ENR(interval(a,b)))`,
  SIMP_TAC[ENR_CONVEX_CLOSED; CONVEX_INTERVAL; CLOSED_INTERVAL;
           OPEN_IMP_ENR; OPEN_INTERVAL]);;

let AR_INTERVAL = prove
 (`(!a b:real^N. AR(interval[a,b]) <=> ~(interval[a,b] = {})) /\
   (!a b:real^N. AR(interval(a,b)) <=> ~(interval(a,b) = {}))`,
  SIMP_TAC[AR_ANR; ANR_INTERVAL; CONVEX_IMP_CONTRACTIBLE; CONVEX_INTERVAL]);;

let ANR_INTERIOR = prove
 (`!s. ANR(interior s)`,
  SIMP_TAC[OPEN_INTERIOR; OPEN_IMP_ANR]);;

let ENR_INTERIOR = prove
 (`!s. ENR(interior s)`,
  SIMP_TAC[OPEN_INTERIOR; OPEN_IMP_ENR]);;

let AR_IMP_CONTRACTIBLE = prove
 (`!s:real^N->bool. AR s ==> contractible s`,
  SIMP_TAC[AR_ANR]);;

let AR_IMP_PATH_CONNECTED = prove
 (`!s:real^N->bool. AR s ==> path_connected s`,
  MESON_TAC[AR_IMP_CONTRACTIBLE; CONTRACTIBLE_IMP_PATH_CONNECTED]);;

let AR_IMP_CONNECTED = prove
 (`!s:real^N->bool. AR s ==> connected s`,
  MESON_TAC[AR_IMP_CONTRACTIBLE; CONTRACTIBLE_IMP_CONNECTED]);;

let ENR_IMP_LOCALLY_COMPACT = prove
 (`!s:real^N->bool. ENR s ==> locally compact s`,
  SIMP_TAC[ENR_ANR]);;

let ANR_IMP_LOCALLY_PATH_CONNECTED = prove
 (`!s:real^N->bool. ANR s ==> locally path_connected s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?c s':real^(N,1)finite_sum->bool.
        convex c /\ ~(c = {}) /\ closed_in (subtopology euclidean c) s' /\
        (s:real^N->bool) homeomorphic s'`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_CLOSED_IN_CONVEX THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; GSYM INT_OF_NUM_ADD] THEN
    REWRITE_TAC[INT_ARITH `x:int < y + &1 <=> x <= y`; AFF_DIM_LE_UNIV];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ANR]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`c:real^(N,1)finite_sum->bool`; `s':real^(N,1)finite_sum->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[HOMEOMORPHIC_SYM; HOMEOMORPHIC_LOCAL_PATH_CONNECTEDNESS;
                RETRACT_OF_LOCALLY_PATH_CONNECTED;
                CONVEX_IMP_LOCALLY_PATH_CONNECTED;
                LOCALLY_OPEN_SUBSET]);;

let ANR_IMP_LOCALLY_CONNECTED = prove
 (`!s:real^N->bool. ANR s ==> locally connected s`,
  SIMP_TAC[ANR_IMP_LOCALLY_PATH_CONNECTED;
           LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED]);;

let AR_IMP_LOCALLY_PATH_CONNECTED = prove
 (`!s:real^N->bool. AR s ==> locally path_connected s`,
  SIMP_TAC[AR_IMP_ANR; ANR_IMP_LOCALLY_PATH_CONNECTED]);;

let AR_IMP_LOCALLY_CONNECTED = prove
 (`!s:real^N->bool. AR s ==> locally connected s`,
  SIMP_TAC[AR_IMP_LOCALLY_PATH_CONNECTED;
           LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED]);;

let ENR_IMP_LOCALLY_PATH_CONNECTED = prove
 (`!s:real^N->bool. ENR s ==> locally path_connected s`,
  SIMP_TAC[ANR_IMP_LOCALLY_PATH_CONNECTED; ENR_IMP_ANR]);;

let ENR_IMP_LOCALLY_CONNECTED = prove
 (`!s:real^N->bool. ENR s ==> locally connected s`,
  SIMP_TAC[ANR_IMP_LOCALLY_CONNECTED; ENR_IMP_ANR]);;

let COUNTABLE_ANR_COMPONENTS = prove
 (`!s:real^N->bool. ANR s ==> COUNTABLE(components s)`,
  SIMP_TAC[ANR_IMP_LOCALLY_CONNECTED; COUNTABLE_COMPONENTS]);;

let COUNTABLE_ANR_CONNECTED_COMPONENTS = prove
 (`!s:real^N->bool t.
        ANR s ==> COUNTABLE {connected_component s x | x IN t}`,
  SIMP_TAC[ANR_IMP_LOCALLY_CONNECTED; COUNTABLE_CONNECTED_COMPONENTS]);;

let COUNTABLE_ANR_PATH_COMPONENTS = prove
 (`!s:real^N->bool t.
        ANR s ==> COUNTABLE {path_component s x | x IN t}`,
  SIMP_TAC[ANR_IMP_LOCALLY_PATH_CONNECTED; COUNTABLE_PATH_COMPONENTS]);;

let FINITE_ANR_COMPONENTS = prove
 (`!s:real^N->bool. ANR s /\ compact s ==> FINITE(components s)`,
  SIMP_TAC[FINITE_COMPONENTS; ANR_IMP_LOCALLY_CONNECTED]);;

let FINITE_ENR_COMPONENTS = prove
 (`!s:real^N->bool. ENR s /\ compact s ==> FINITE(components s)`,
  SIMP_TAC[FINITE_COMPONENTS; ENR_IMP_LOCALLY_CONNECTED]);;

let ANR_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool. ANR s /\ ANR t ==> ANR(s PCROSS t)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[ANR_EQ_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR] THEN
  MAP_EVERY X_GEN_TAC
   [`f:real^((M,N)finite_sum,1)finite_sum->real^(M,N)finite_sum`;
    `u:real^((M,N)finite_sum,1)finite_sum->bool`;
    `c:real^((M,N)finite_sum,1)finite_sum->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`fstcart o (f:real^((M,N)finite_sum,1)finite_sum->real^(M,N)finite_sum)`;
    `u:real^((M,N)finite_sum,1)finite_sum->bool`;
    `c:real^((M,N)finite_sum,1)finite_sum->bool`;
    `s:real^M->bool`] ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
  MP_TAC(ISPECL
   [`sndcart o (f:real^((M,N)finite_sum,1)finite_sum->real^(M,N)finite_sum)`;
    `u:real^((M,N)finite_sum,1)finite_sum->bool`;
    `c:real^((M,N)finite_sum,1)finite_sum->bool`;
    `t:real^N->bool`] ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_COMPOSE; LINEAR_CONTINUOUS_ON;
               LINEAR_FSTCART; LINEAR_SNDCART; IMAGE_o] THEN
  RULE_ASSUM_TAC
   (REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; PCROSS; IN_ELIM_THM]) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[SNDCART_PASTECART]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC
   [`w2:real^((M,N)finite_sum,1)finite_sum->bool`;
    `h:real^((M,N)finite_sum,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN ANTS_TAC THENL
   [ASM_MESON_TAC[FSTCART_PASTECART]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC
   [`w1:real^((M,N)finite_sum,1)finite_sum->bool`;
    `g:real^((M,N)finite_sum,1)finite_sum->real^M`] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`w1 INTER w2:real^((M,N)finite_sum,1)finite_sum->bool`;
    `\x:real^((M,N)finite_sum,1)finite_sum.
        pastecart (g x:real^M) (h x:real^N)`] THEN
  ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER; o_DEF; PASTECART_IN_PCROSS;
               PASTECART_FST_SND] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTER_SUBSET]);;

let ANR_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        ANR(s PCROSS t) <=> s = {} \/ t = {} \/ ANR s /\ ANR t`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; ANR_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; ANR_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[ANR_PCROSS] THEN REPEAT STRIP_TAC THENL
   [UNDISCH_TAC `~(t:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ANR ((s:real^M->bool) PCROSS {b:real^N})` MP_TAC THENL
     [ALL_TAC; MESON_TAC[HOMEOMORPHIC_PCROSS_SING; HOMEOMORPHIC_ANRNESS]];
    UNDISCH_TAC `~(s:real^M->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `a:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ANR ({a:real^M} PCROSS (t:real^N->bool))` MP_TAC THENL
     [ALL_TAC; MESON_TAC[HOMEOMORPHIC_PCROSS_SING; HOMEOMORPHIC_ANRNESS]]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        ANR_RETRACT_OF_ANR)) THEN
  REWRITE_TAC[retract_of; retraction] THENL
   [EXISTS_TAC`\x:real^(M,N)finite_sum. pastecart (fstcart x) (b:real^N)`;
    EXISTS_TAC`\x:real^(M,N)finite_sum. pastecart (a:real^M) (sndcart x)`] THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_PCROSS; FORALL_IN_IMAGE; IN_SING;
               FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS;
               CONTINUOUS_ON_PASTECART; LINEAR_FSTCART; LINEAR_SNDCART;
               LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST]);;

let AR_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool. AR s /\ AR t ==> AR(s PCROSS t)`,
  SIMP_TAC[AR_ANR; ANR_PCROSS; CONTRACTIBLE_PCROSS; PCROSS_EQ_EMPTY]);;

let ENR_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool. ENR s /\ ENR t ==> ENR(s PCROSS t)`,
  SIMP_TAC[ENR_ANR; ANR_PCROSS; LOCALLY_COMPACT_PCROSS]);;

let ENR_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        ENR(s PCROSS t) <=> s = {} \/ t = {} \/ ENR s /\ ENR t`,
  REWRITE_TAC[ENR_ANR; ANR_PCROSS_EQ; LOCALLY_COMPACT_PCROSS_EQ] THEN
  CONV_TAC TAUT);;

let AR_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        AR(s PCROSS t) <=> AR s /\ AR t /\ ~(s = {}) /\ ~(t = {})`,
  SIMP_TAC[AR_ANR; ANR_PCROSS_EQ; CONTRACTIBLE_PCROSS_EQ; PCROSS_EQ_EMPTY] THEN
  CONV_TAC TAUT);;

let AR_CLOSED_UNION_LOCAL = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        AR(s) /\ AR(t) /\ AR(s INTER t)
        ==> AR(s UNION t)`,
  let lemma = prove
   (`!s t u:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        AR s /\ AR t /\ AR(s INTER t)
        ==> (s UNION t) retract_of u`,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `s INTER t:real^N->bool = {}` THENL
     [ASM_MESON_TAC[NOT_AR_EMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET u /\ t SUBSET u` STRIP_ASSUME_TAC
    THENL [ASM_MESON_TAC[CLOSED_IN_IMP_SUBSET]; ALL_TAC] THEN
    MAP_EVERY ABBREV_TAC
     [`s' = {x:real^N | x IN u /\ setdist({x},s) <= setdist({x},t)}`;
      `t' = {x:real^N | x IN u /\ setdist({x},t) <= setdist({x},s)}`;
      `w = {x:real^N | x IN u /\ setdist({x},s) = setdist({x},t)}`] THEN
    SUBGOAL_THEN `closed_in (subtopology euclidean u) (s':real^N->bool) /\
                  closed_in (subtopology euclidean u) (t':real^N->bool)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["s'"; "t'"] THEN
      ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
      ONCE_REWRITE_TAC[GSYM LIFT_DROP] THEN REWRITE_TAC[SET_RULE
       `a <= drop(lift x) <=> lift x IN {x | a <= drop x}`] THEN
      REWRITE_TAC[LIFT_DROP; LIFT_SUB] THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
      SIMP_TAC[CLOSED_SING; CONTINUOUS_ON_SUB; CONTINUOUS_ON_LIFT_SETDIST;
               drop; CLOSED_HALFSPACE_COMPONENT_LE;
               REWRITE_RULE[real_ge] CLOSED_HALFSPACE_COMPONENT_GE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(s:real^N->bool) SUBSET s' /\ (t:real^N->bool) SUBSET t'`
    STRIP_ASSUME_TAC THENL
      [MAP_EVERY EXPAND_TAC ["s'"; "t'"] THEN
       SIMP_TAC[SUBSET; IN_ELIM_THM; SETDIST_SING_IN_SET; SETDIST_POS_LE] THEN
       ASM SET_TAC[];
       ALL_TAC] THEN
    SUBGOAL_THEN `(s INTER t:real^N->bool) retract_of w` MP_TAC THENL
     [MATCH_MP_TAC AR_IMP_ABSOLUTE_RETRACT THEN
      EXISTS_TAC `s INTER t:real^N->bool` THEN
      ASM_REWRITE_TAC[HOMEOMORPHIC_REFL] THEN
      MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
      EXISTS_TAC `u:real^N->bool` THEN
      ASM_SIMP_TAC[CLOSED_IN_INTER] THEN
      CONJ_TAC THENL [EXPAND_TAC "w"; ASM SET_TAC[]] THEN
      SIMP_TAC[SUBSET; IN_INTER; IN_ELIM_THM; SETDIST_SING_IN_SET] THEN
      ASM SET_TAC[];
      GEN_REWRITE_TAC LAND_CONV [retract_of] THEN
      REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `r0:real^N->real^N` THEN STRIP_TAC] THEN
    SUBGOAL_THEN
     `!x:real^N. x IN w ==> (x IN s <=> x IN t)`
    ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN
      DISCH_THEN(fun th -> EQ_TAC THEN DISCH_TAC THEN MP_TAC th) THEN
      ASM_SIMP_TAC[SETDIST_SING_IN_SET] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `&0 = setdist p <=> setdist p = &0`] THEN
      MATCH_MP_TAC(SET_RULE
       `~(s = {}) /\ (p <=> s = {} \/ x IN s) ==> p ==> x IN s`) THEN
      (CONJ_TAC THENL
       [ASM SET_TAC[]; MATCH_MP_TAC SETDIST_EQ_0_CLOSED_IN]) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `s' INTER t':real^N->bool = w` ASSUME_TAC THENL
     [ASM SET_TAC[REAL_LE_ANTISYM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `closed_in (subtopology euclidean u) (w:real^N->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[CLOSED_IN_INTER]; ALL_TAC] THEN
    ABBREV_TAC `r = \x:real^N. if x IN w then r0 x else x` THEN
    SUBGOAL_THEN
     `IMAGE (r:real^N->real^N) (w UNION s) SUBSET s /\
      IMAGE (r:real^N->real^N) (w UNION t) SUBSET t`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(r:real^N->real^N) continuous_on  (w UNION s UNION t)`
    ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
      EXISTS_TAC `u:real^N->bool` THEN
      ASM_SIMP_TAC[CLOSED_IN_UNION] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?g:real^N->real^N.
          g continuous_on u /\
          IMAGE g u SUBSET s /\
          !x. x IN w UNION s ==> g x = r x`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC AR_IMP_ABSOLUTE_EXTENSOR THEN
      ASM_SIMP_TAC[CLOSED_IN_UNION] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET; IN_UNION];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?h:real^N->real^N.
          h continuous_on u /\
          IMAGE h u SUBSET t /\
          !x. x IN w UNION t ==> h x = r x`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC AR_IMP_ABSOLUTE_EXTENSOR THEN
      ASM_SIMP_TAC[CLOSED_IN_UNION] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET; IN_UNION];
      ALL_TAC] THEN
    REWRITE_TAC[retract_of; retraction] THEN
    EXISTS_TAC `\x. if x IN s' then (g:real^N->real^N) x else h x` THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ALL_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION] THEN ASM SET_TAC[];
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNION] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[IN_UNION; COND_ID] THENL
       [COND_CASES_TAC THENL [EXPAND_TAC "r"; ASM SET_TAC[]];
        COND_CASES_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        TRANS_TAC EQ_TRANS `(r:real^N->real^N) x` THEN
        CONJ_TAC THENL [ASM SET_TAC[]; EXPAND_TAC "r"]] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]] THEN
    SUBGOAL_THEN
     `u:real^N->bool = s' UNION t'`
     (fun th -> ONCE_REWRITE_TAC[th] THEN
                MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
                REWRITE_TAC[GSYM th])
    THENL [ASM SET_TAC[REAL_LE_TOTAL]; ASM_SIMP_TAC[]] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]) THEN
    REWRITE_TAC[TAUT `p /\ ~p \/ q /\ p <=> p /\ q`] THEN
    ASM_SIMP_TAC[GSYM IN_INTER; IN_UNION]) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[AR] THEN MAP_EVERY X_GEN_TAC
   [`u:real^(N,1)finite_sum->bool`; `c:real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`f:real^N->real^(N,1)finite_sum`; `g:real^(N,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `closed_in (subtopology euclidean u)
              {x | x IN c /\ (g:real^(N,1)finite_sum->real^N) x IN s} /\
    closed_in (subtopology euclidean u)
              {x | x IN c /\ (g:real^(N,1)finite_sum->real^N) x IN t}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_TRANS THEN
    EXISTS_TAC `c:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `s UNION t:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN c /\ (g:real^(N,1)finite_sum->real^N) x IN s} UNION
    {x | x IN c /\ (g:real^(N,1)finite_sum->real^N) x IN t} = c`
   (fun th -> SUBST1_TAC(SYM th)) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `AR(s:real^N->bool)`;
    UNDISCH_TAC `AR(t:real^N->bool)`;
    UNDISCH_TAC `AR(s INTER t:real^N->bool)`] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HOMEOMORPHIC_ARNESS THEN
  REWRITE_TAC[homeomorphic; homeomorphism] THEN MAP_EVERY EXISTS_TAC
   [`f:real^N->real^(N,1)finite_sum`; `g:real^(N,1)finite_sum->real^N`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET))) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* General ANR union lemma (Kuratowski).                                     *)
(* ------------------------------------------------------------------------- *)

let ANR_UNION_EXTENSION_LEMMA = prove
 (`!f:real^M->real^N s t u s1 s2 u1 u2.
        f continuous_on t /\ IMAGE f t SUBSET u /\
        ANR u1 /\ ANR u2 /\ ANR(u1 INTER u2) /\ u1 UNION u2 = u /\
        closed_in (subtopology euclidean s) t /\
        closed_in (subtopology euclidean s) s1 /\
        closed_in (subtopology euclidean s) s2 /\
        s1 UNION s2 = s /\
        IMAGE f (t INTER s1) SUBSET u1 /\
        IMAGE f (t INTER s2) SUBSET u2
        ==> ?v g. t SUBSET v /\
                  open_in (subtopology euclidean s) v /\
                  g continuous_on v /\ IMAGE g v SUBSET u /\
                  !x. x IN t ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?v v' h.
        t INTER s1 INTER s2 SUBSET v /\ v SUBSET v' /\
        open_in (subtopology euclidean (s1 INTER s2)) v /\
        closed_in (subtopology euclidean (s1 INTER s2)) v' /\
        h continuous_on v' /\ IMAGE h v' SUBSET u1 INTER u2 /\
        !x. x IN v' INTER t ==> (h:real^M->real^N) x = f x`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`f:real^M->real^N`; `s:real^M->bool`;
      `t INTER s1 INTER s2:real^M->bool`; `u1 INTER u2:real^N->bool`]
      ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
    ASM_SIMP_TAC[CLOSED_IN_INTER] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [`v:real^M->bool`; `g:real^M->real^N`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`t INTER s1 INTER s2:real^M->bool`; `s DIFF v:real^M->bool`;
                   `s:real^M->bool`] SEPARATION_NORMAL_LOCAL) THEN
    ASM_SIMP_TAC[CLOSED_IN_INTER; CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [`w:real^M->bool`; `w':real^M->bool`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `(s1 INTER s2) INTER w:real^M->bool` THEN
    EXISTS_TAC `(s1 INTER s2) DIFF w':real^M->bool` THEN
    EXISTS_TAC `g:real^M->real^N` THEN
    ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM SET_TAC[];
      MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
      EXISTS_TAC `s:real^M->bool` THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; OPEN_IN_REFL] THEN ASM SET_TAC[];
      ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s DIFF (s INTER t)`] THEN
      MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL] THEN
      MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
      EXISTS_TAC `s:real^M->bool` THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; OPEN_IN_REFL] THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
      ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `k:real^M->bool = (s1 INTER s2) DIFF v` THEN
  SUBGOAL_THEN
   `closed_in (subtopology euclidean (s1 INTER s2)) (k:real^M->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closed_in (subtopology euclidean s) (k:real^M->bool)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_TRANS; CLOSED_IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `k INTER t:real^M->bool = {}` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`subtopology euclidean ((t INTER s2) UNION v':real^M->bool)`;
    `euclidean:(real^N)topology`;
    `\i. if i = 0 then (f:real^M->real^N) else h`;
    `\i. if i = 0 then t INTER s2:real^M->bool else v'`;
    `{0,1}`] PASTING_LEMMA_EXISTS_CLOSED) THEN
  MP_TAC(ISPECL
   [`subtopology euclidean ((t INTER s1) UNION v':real^M->bool)`;
    `euclidean:(real^N)topology`;
    `\i. if i = 0 then (f:real^M->real^N) else h`;
    `\i. if i = 0 then t INTER s1:real^M->bool else v'`;
    `{0,1}`] PASTING_LEMMA_EXISTS_CLOSED) THEN
  REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
              SUBTOPOLOGY_SUBTOPOLOGY] THEN
  ONCE_REWRITE_TAC[TAUT `closed_in a b /\ c <=> ~(closed_in a b ==> ~c)`] THEN
  SIMP_TAC[ISPEC `euclidean` CLOSED_IN_IMP_SUBSET;
           SET_RULE `s SUBSET u ==> u INTER s = s`] THEN
  REWRITE_TAC[NOT_IMP] THEN REWRITE_TAC[SUBSET_UNIV] THEN
  MAP_EVERY (fun x ->
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN ANTS_TAC THENL
     [REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_2] THEN
      ASM_REWRITE_TAC[ARITH_EQ; SUBSET_REFL;
        FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[TAUT `(p /\ q) /\ r <=> q /\ p /\ r`] THEN
        CONJ_TAC THENL
         [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTER_SUBSET]; ALL_TAC] THEN
        ASM_REWRITE_TAC[SET_RULE `(s UNION t) INTER t = t`] THEN

        CONJ_TAC THEN
        MATCH_MP_TAC(MESON[]
         `u INTER s = s /\ closed_in (subtopology top u) (u INTER s)
          ==> closed_in (subtopology top u) s`) THEN
        (CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
        MATCH_MP_TAC CLOSED_IN_SUBTOPOLOGY_INTER_SUBSET THEN
        EXISTS_TAC `s:real^M->bool` THEN
        ASM_SIMP_TAC[CLOSED_IN_INTER; CLOSED_IN_REFL] THEN
        TRY(CONJ_TAC THENL
         [ASM_MESON_TAC[CLOSED_IN_TRANS; CLOSED_IN_INTER; CLOSED_IN_REFL];
          ALL_TAC]) THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET)) THEN
        ASM SET_TAC[];
        MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
        CONJ_TAC THENL [MESON_TAC[INTER_COMM]; ALL_TAC] THEN
        MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
        REWRITE_TAC[CONJ_ASSOC] THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
        ONCE_REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
        REWRITE_TAC[IMP_IMP; IN_INSERT; NOT_IN_EMPTY] THEN
        REWRITE_TAC[ARITH_RULE
         `m < n /\ (m = 0 \/ m = 1) /\ (n = 0 \/ n = 1) <=>
          m = 0 /\ n = 1`] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN ASM SET_TAC[]];
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SWAP_FORALL_THM] THEN
      GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
       [IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
       [FORALL_IN_INSERT; NOT_IN_EMPTY; ARITH_EQ] THEN
      REWRITE_TAC[SET_RULE
       `(s UNION t) INTER s = s /\ (s UNION t) INTER t = t`] THEN
      DISCH_THEN(X_CHOOSE_THEN x STRIP_ASSUME_TAC)])
    [`f1:real^M->real^N`; `f2:real^M->real^N`] THEN
  MP_TAC(ISPECL
   [`f1:real^M->real^N`; `s:real^M->bool`;
    `t INTER s1 UNION v':real^M->bool`; `u1:real^N->bool`]
    ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_UNION THEN
    ASM_MESON_TAC[CLOSED_IN_TRANS; CLOSED_IN_INTER];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`v1:real^M->bool`; `g1:real^M->real^N`] THEN
    STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`f2:real^M->real^N`; `s:real^M->bool`;
    `t INTER s2 UNION v':real^M->bool`; `u2:real^N->bool`]
    ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_UNION THEN
    ASM_MESON_TAC[CLOSED_IN_TRANS; CLOSED_IN_INTER];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`v2:real^M->bool`; `g2:real^M->real^N`] THEN
    STRIP_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`w1:real^M->bool = s1 DIFF v1`; `w2:real^M->bool = s2 DIFF v2`] THEN
  SUBGOAL_THEN
   `closed_in (subtopology euclidean s) (w1:real^M->bool) /\
    closed_in (subtopology euclidean s) (w2:real^M->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[CLOSED_IN_DIFF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `t INTER w1 = {} /\ v' INTER w1:real^M->bool = {} /\
    t INTER w2 = {} /\ v' INTER w2 = {}`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `n:real^M->bool = s DIFF (k UNION w1 UNION w2)` THEN
  EXISTS_TAC `n:real^M->bool` THEN REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET)) THEN
    ASM SET_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [EXPAND_TAC "n" THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
    ASM_SIMP_TAC[OPEN_IN_REFL; CLOSED_IN_UNION];
    DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`subtopology euclidean (n:real^M->bool)`;
    `euclidean:(real^N)topology`;
    `\i. if i = 0 then (g1:real^M->real^N) else g2`;
    `\i. if i = 0 then s1 INTER n:real^M->bool else s2 INTER n`;
    `{0,1}`] PASTING_LEMMA_EXISTS_CLOSED) THEN
  REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
              SUBTOPOLOGY_SUBTOPOLOGY] THEN
  ONCE_REWRITE_TAC[TAUT `closed_in a b /\ c <=> ~(closed_in a b ==> ~c)`] THEN
  SIMP_TAC[ISPEC `euclidean` CLOSED_IN_IMP_SUBSET;
           SET_RULE `s SUBSET u ==> u INTER s = s`] THEN
  REWRITE_TAC[NOT_IMP] THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; SUBSET_UNIV] THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; IMP_CONJ] THEN
  REWRITE_TAC[ARITH_EQ; IMP_IMP; FORALL_AND_THM] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_2; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[ARITH_EQ] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ONCE_REWRITE_TAC[INTER_COMM] THEN
      MATCH_MP_TAC CLOSED_IN_SUBTOPOLOGY_INTER_SUBSET THEN
      EXISTS_TAC `s:real^M->bool` THEN
      ASM_SIMP_TAC[CLOSED_IN_INTER; CLOSED_IN_REFL] THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
      ONCE_REWRITE_TAC[INTER_COMM] THEN
      MATCH_MP_TAC CLOSED_IN_SUBTOPOLOGY_INTER_SUBSET THEN
      EXISTS_TAC `s:real^M->bool` THEN
      ASM_SIMP_TAC[CLOSED_IN_INTER; CLOSED_IN_REFL] THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
      MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL [MESON_TAC[INTER_COMM]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
      REWRITE_TAC[CONJ_ASSOC] THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
      ONCE_REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[IMP_IMP; IN_INSERT; NOT_IN_EMPTY] THEN
      REWRITE_TAC[ARITH_RULE
       `m < n /\ (m = 0 \/ m = 1) /\ (n = 0 \/ n = 1) <=>
        m = 0 /\ n = 1`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
      X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^M) IN v` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET)) THEN
      ASM SET_TAC[]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f':real^M->real^N` THEN
    REWRITE_TAC[SET_RULE `n INTER s INTER n = n INTER s`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE]; ALL_TAC] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    (SUBGOAL_THEN `(x:real^M) IN s1 \/ x IN s2` MP_TAC THENL
      [ASM SET_TAC[];
       STRIP_TAC THEN ASM_SIMP_TAC[IN_INTER] THEN ASM SET_TAC[]])]);;

(* ------------------------------------------------------------------------- *)
(* Application to closed union.                                              *)
(* ------------------------------------------------------------------------- *)

let ANR_CLOSED_UNION_LOCAL = prove
 (`!s t:real^N->bool u.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        ANR(s) /\ ANR(t) /\ ANR(s INTER t)
        ==> ANR(s UNION t)`,
  MAP_EVERY X_GEN_TAC
   [`y1:real^N->bool`; `y2:real^N->bool`; `yn:real^N->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `closed_in (subtopology euclidean (y1 UNION y2)) (y1:real^N->bool) /\
    closed_in (subtopology euclidean (y1 UNION y2)) (y2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_SUBSET_TRANS; SUBSET_UNION; UNION_SUBSET;
                  CLOSED_IN_IMP_SUBSET];
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o
      check (free_in `yn:real^N->bool` o concl)))] THEN
  MATCH_MP_TAC ABSOLUTE_NEIGHBOURHOOD_EXTENSOR_IMP_ANR THEN
  MAP_EVERY X_GEN_TAC
   [`f:real^(N,1)finite_sum->real^N`;
    `s:real^(N,1)finite_sum->bool`; `t:real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `IMAGE (f:real^(N,1)finite_sum->real^N) t SUBSET y1` THENL
   [MP_TAC(ISPECL
     [`f:real^(N,1)finite_sum->real^N`; `s:real^(N,1)finite_sum->bool`;
      `t:real^(N,1)finite_sum->bool`; `y1:real^N->bool`]
      ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `IMAGE (f:real^(N,1)finite_sum->real^N) t SUBSET y2` THENL
   [MP_TAC(ISPECL
     [`f:real^(N,1)finite_sum->real^N`; `s:real^(N,1)finite_sum->bool`;
      `t:real^(N,1)finite_sum->bool`; `y2:real^N->bool`]
      ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC ANR_UNION_EXTENSION_LEMMA THEN MAP_EVERY ABBREV_TAC
   [`b1 = {x | x IN s /\
               setdist({x},
                   {x | x IN t /\ (f:real^(N,1)finite_sum->real^N) x IN y1})
             <= setdist({x},{x | x IN t /\ f x IN y2})}`;
    `b2 = {x | x IN s /\
               setdist({x},
                   {x | x IN t /\ (f:real^(N,1)finite_sum->real^N) x IN y2})
             <= setdist({x},{x | x IN t /\ f x IN y1})}`] THEN
  MAP_EVERY EXISTS_TAC
   [`b1:real^(N,1)finite_sum->bool`;
    `b2:real^(N,1)finite_sum->bool`;
    `y1:real^N->bool`;
    `y2:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "b1"; EXPAND_TAC "b2"] THEN
    ONCE_REWRITE_TAC[MESON[LIFT_DROP; REAL_SUB_LE]
     `x <= y <=> &0 <= drop(lift(y - x))`] THEN
    ONCE_REWRITE_TAC[SET_RULE
     `&0 <= drop x <=> x IN {y | &0 <= drop y}`] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
    REWRITE_TAC[drop; GSYM real_ge; CLOSED_HALFSPACE_COMPONENT_GE] THEN
    SIMP_TAC[LIFT_SUB; CONTINUOUS_ON_SUB; CONTINUOUS_ON_LIFT_SETDIST;
             CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["b1"; "b2"] THEN
    MP_TAC REAL_LE_TOTAL THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
  MAP_EVERY EXPAND_TAC ["b1"; "b2"] THEN
  X_GEN_TAC `x:real^(N,1)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THENL
   [SUBGOAL_THEN `(f:real^(N,1)finite_sum->real^N) x IN y2` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC];
    SUBGOAL_THEN `(f:real^(N,1)finite_sum->real^N) x IN y1` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_NOT_LT]) THEN
  ASM_SIMP_TAC[SETDIST_SING_IN_SET; IN_ELIM_THM] THEN
  REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
  REWRITE_TAC[SETDIST_POS_LE] THEN
  MP_TAC(ISPEC `s:real^(N,1)finite_sum->bool` SETDIST_EQ_0_CLOSED_IN) THEN
  DISCH_THEN(fun th ->
    W(MP_TAC o PART_MATCH (lhand o rand) th o rand o snd)) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  (ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]]) THEN
  MATCH_MP_TAC CLOSED_IN_TRANS THEN
  EXISTS_TAC `t:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_GEN THEN
  EXISTS_TAC `y1 UNION y2:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let ENR_CLOSED_UNION_LOCAL = prove
 (`!s t u:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        ENR(s) /\ ENR(t) /\ ENR(s INTER t)
        ==> ENR(s UNION t)`,
  REWRITE_TAC[ENR_ANR] THEN
  MESON_TAC[ANR_CLOSED_UNION_LOCAL; LOCALLY_COMPACT_CLOSED_UNION]);;

let AR_CLOSED_UNION = prove
 (`!s t:real^N->bool.
        closed s /\ closed t /\ AR(s) /\ AR(t) /\ AR(s INTER t)
        ==> AR(s UNION t)`,
  MESON_TAC[AR_CLOSED_UNION_LOCAL; CLOSED_SUBSET; SUBSET_UNION]);;

let ANR_CLOSED_UNION = prove
 (`!s t:real^N->bool.
        closed s /\ closed t /\ ANR(s) /\ ANR(t) /\ ANR(s INTER t)
        ==> ANR(s UNION t)`,
  MESON_TAC[ANR_CLOSED_UNION_LOCAL; CLOSED_SUBSET; SUBSET_UNION]);;

let ENR_CLOSED_UNION = prove
 (`!s t:real^N->bool.
        closed s /\ closed t /\ ENR(s) /\ ENR(t) /\ ENR(s INTER t)
        ==> ENR(s UNION t)`,
  MESON_TAC[ENR_CLOSED_UNION_LOCAL; CLOSED_SUBSET; SUBSET_UNION]);;

let ABSOLUTE_RETRACT_UNION = prove
 (`!s t. s retract_of (:real^N) /\
         t retract_of (:real^N) /\
         (s INTER t) retract_of (:real^N)
         ==> (s UNION t) retract_of (:real^N)`,
  SIMP_TAC[RETRACT_OF_UNIV; AR_CLOSED_UNION; CLOSED_UNION]);;

let RETRACT_FROM_UNION_AND_INTER = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        (s UNION t) retract_of u /\ (s INTER t) retract_of t
        ==> s retract_of u`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(s UNION t) retract_of (u:real^N->bool)` THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] RETRACT_OF_TRANS) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; retract_of] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x:real^N. if x IN s then x else r x` THEN
  SIMP_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN ASM SET_TAC[]);;

let AR_FROM_UNION_AND_INTER_LOCAL = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        AR(s UNION t) /\ AR(s INTER t)
        ==> AR(s) /\ AR(t)`,
  SUBGOAL_THEN
   `!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        AR(s UNION t) /\ AR(s INTER t)
        ==> AR(s)`
  MP_TAC THENL [ALL_TAC; MESON_TAC[UNION_COMM; INTER_COMM]] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC AR_RETRACT_OF_AR THEN
  EXISTS_TAC `s UNION t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RETRACT_FROM_UNION_AND_INTER THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[RETRACT_OF_REFL] THEN
  MATCH_MP_TAC RETRACT_OF_SUBSET THEN EXISTS_TAC `s UNION t:real^N->bool` THEN
  REWRITE_TAC[INTER_SUBSET; SUBSET_UNION] THEN
  MATCH_MP_TAC AR_IMP_RETRACT THEN ASM_SIMP_TAC[CLOSED_IN_INTER]);;

let AR_FROM_UNION_AND_INTER = prove
 (`!s t:real^N->bool.
        closed s /\ closed t /\ AR(s UNION t) /\ AR(s INTER t)
        ==> AR(s) /\ AR(t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC AR_FROM_UNION_AND_INTER_LOCAL THEN
  ASM_MESON_TAC[CLOSED_SUBSET; SUBSET_UNION]);;

let ANR_FROM_UNION_AND_INTER_LOCAL = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        ANR(s UNION t) /\ ANR(s INTER t)
        ==> ANR(s) /\ ANR(t)`,
  SUBGOAL_THEN
   `!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        ANR(s UNION t) /\ ANR(s INTER t)
        ==> ANR(s)`
  MP_TAC THENL [ALL_TAC; MESON_TAC[UNION_COMM; INTER_COMM]] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ANR_NEIGHBORHOOD_RETRACT THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  EXISTS_TAC `s UNION t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s INTER t:real^N->bool`; `s UNION t:real^N->bool`]
        ANR_IMP_NEIGHBOURHOOD_RETRACT) THEN
  ASM_SIMP_TAC[CLOSED_IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
  EXISTS_TAC `s UNION u:real^N->bool` THEN CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `s UNION u:real^N->bool =
      ((s UNION t) DIFF t) UNION u`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_IN_UNION; OPEN_IN_DIFF; OPEN_IN_REFL]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retract_of; retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^N->real^N` THEN STRIP_TAC THEN
  EXISTS_TAC `\x:real^N. if x IN s then x else r x` THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  SUBGOAL_THEN `s UNION u:real^N->bool = s UNION (u INTER t)`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; CONJ_ASSOC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTER_SUBSET]] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC
     `closed_in(subtopology euclidean (s UNION t)) (s:real^N->bool)`;
    UNDISCH_TAC
       `closed_in(subtopology euclidean (s UNION t)) (t:real^N->bool)`] THEN
  REWRITE_TAC[CLOSED_IN_CLOSED] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM SET_TAC[]);;

let ANR_FROM_UNION_AND_INTER = prove
 (`!s t:real^N->bool.
        closed s /\ closed t /\ ANR(s UNION t) /\ ANR(s INTER t)
        ==> ANR(s) /\ ANR(t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ANR_FROM_UNION_AND_INTER_LOCAL THEN
  ASM_MESON_TAC[CLOSED_SUBSET; SUBSET_UNION]);;

let ANR_FINITE_UNIONS_CONVEX_CLOSED = prove
 (`!t:(real^N->bool)->bool.
        FINITE t /\ (!c. c IN t ==> closed c /\ convex c) ==> ANR(UNIONS t)`,
  GEN_TAC THEN WF_INDUCT_TAC `CARD(t:(real^N->bool)->bool)` THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[TAUT `p ==> q /\ r ==> s <=> q ==> p ==> r ==> s`] THEN
  SPEC_TAC(`t:(real^N->bool)->bool`,`t:(real^N->bool)->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; FORALL_IN_INSERT] THEN
  REWRITE_TAC[ANR_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N->bool`; `t:(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IMP_IMP] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ANR_CLOSED_UNION THEN ASM_SIMP_TAC[CLOSED_UNIONS] THEN
  ASM_SIMP_TAC[CONVEX_IMP_ANR] THEN REWRITE_TAC[INTER_UNIONS] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[CARD_CLAUSES] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; LT_SUC_LE; LE_REFL] THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; CLOSED_INTER; CONVEX_INTER] THEN
  ASM_SIMP_TAC[CARD_IMAGE_LE]);;

let FINITE_IMP_ANR = prove
 (`!s:real^N->bool. FINITE s ==> ANR s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s = UNIONS {{a:real^N} | a IN s}` SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[];
    MATCH_MP_TAC ANR_FINITE_UNIONS_CONVEX_CLOSED THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE; SIMPLE_IMAGE; FINITE_IMAGE] THEN
    REWRITE_TAC[CLOSED_SING; CONVEX_SING]]);;

let ANR_INSERT = prove
 (`!s a:real^N. closed s /\ ANR s ==> ANR(a INSERT s)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  MATCH_MP_TAC ANR_CLOSED_UNION THEN
  ASM_MESON_TAC[CLOSED_SING; ANR_SING; ANR_EMPTY;
                SET_RULE `{a} INTER s = {a} \/ {a} INTER s = {}`]);;

let ANR_TRIANGULATION = prove
 (`!tr. triangulation tr ==> ANR(UNIONS tr)`,
  REWRITE_TAC[triangulation] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ANR_FINITE_UNIONS_CONVEX_CLOSED THEN
  ASM_MESON_TAC[SIMPLEX_IMP_CLOSED; SIMPLEX_IMP_CONVEX]);;

let ANR_SIMPLICIAL_COMPLEX = prove
 (`!c. simplicial_complex c ==>  ANR(UNIONS c)`,
  MESON_TAC[ANR_TRIANGULATION; SIMPLICIAL_COMPLEX_IMP_TRIANGULATION]);;

let ANR_PATH_COMPONENT_ANR = prove
 (`!s x:real^N. ANR(s) ==> ANR(path_component s x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    ANR_OPEN_IN)) THEN
  MATCH_MP_TAC OPEN_IN_PATH_COMPONENT_LOCALLY_PATH_CONNECTED THEN
  ASM_SIMP_TAC[ANR_IMP_LOCALLY_PATH_CONNECTED]);;

let ANR_CONNECTED_COMPONENT_ANR = prove
 (`!s x:real^N. ANR(s) ==> ANR(connected_component s x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    ANR_OPEN_IN)) THEN
  MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENT_LOCALLY_CONNECTED THEN
  ASM_SIMP_TAC[ANR_IMP_LOCALLY_CONNECTED]);;

let ANR_COMPONENT_ANR = prove
 (`!s:real^N->bool.
        ANR s /\ c IN components s ==> ANR c`,
  REWRITE_TAC[IN_COMPONENTS] THEN MESON_TAC[ANR_CONNECTED_COMPONENT_ANR]);;

(* ------------------------------------------------------------------------- *)
(* Application to open union.                                                *)
(* ------------------------------------------------------------------------- *)

let ANR_OPEN_UNION = prove
 (`!s t u:real^N->bool.
        open_in (subtopology euclidean u) s /\
        open_in (subtopology euclidean u) t /\
        ANR(s) /\ ANR(t)
        ==> ANR(s UNION t)`,
  MAP_EVERY X_GEN_TAC
   [`u1:real^N->bool`; `u2:real^N->bool`; `un:real^N->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (u1 UNION u2)) (u1:real^N->bool) /\
    open_in (subtopology euclidean (u1 UNION u2)) (u2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET_TRANS; SUBSET_UNION; UNION_SUBSET;
                  OPEN_IN_IMP_SUBSET];
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o
      check (free_in `un:real^N->bool` o concl)))] THEN
  MATCH_MP_TAC ABSOLUTE_NEIGHBOURHOOD_EXTENSOR_IMP_ANR THEN
  MAP_EVERY X_GEN_TAC
   [`f:real^(N,1)finite_sum->real^N`;
    `s:real^(N,1)finite_sum->bool`; `t:real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC ANR_UNION_EXTENSION_LEMMA THEN MAP_EVERY ABBREV_TAC
   [`t1 = {x | x IN t /\ ~((f:real^(N,1)finite_sum->real^N)(x) IN u1)}`;
    `t2 = {x | x IN t /\ ~((f:real^(N,1)finite_sum->real^N)(x) IN u2)}`] THEN
  MP_TAC(ISPECL
   [`t1:real^(N,1)finite_sum->bool`;
    `t2:real^(N,1)finite_sum->bool`;
    `s:real^(N,1)finite_sum->bool`;
    `vec 1:real^1`; `vec 0:real^1`]
   URYSOHN_LOCAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONJ_ASSOC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_TRANS THEN
    EXISTS_TAC `t:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THENL
     [EXPAND_TAC "t1"; EXPAND_TAC "t2"] THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC
     [MATCH_MP (SET_RULE
       `IMAGE f s SUBSET t
        ==> {x | x IN s /\ ~(f x IN u)} =
            {x | x IN s /\ f x IN t DIFF u}`) th]) THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `u1 UNION u2:real^N->bool` THEN
    ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL];
    DISCH_THEN(X_CHOOSE_THEN `l:real^(N,1)finite_sum->real^1`
      STRIP_ASSUME_TAC)] THEN
  MAP_EVERY EXISTS_TAC
   [`{ x:real^(N,1)finite_sum | x IN s /\ l x IN {y | drop y <= &1 / &2}}`;
    `{ x:real^(N,1)finite_sum | x IN s /\ l x IN {y | drop y >= &1 / &2}}`;
    `u1:real^N->bool`; `u2:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ANR_OPEN_IN THEN
    EXISTS_TAC `u1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
    EXISTS_TAC `u1 UNION u2:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; OPEN_IN_REFL] THEN SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
    ASM_REWRITE_TAC[drop; CLOSED_HALFSPACE_COMPONENT_LE];
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
    ASM_REWRITE_TAC[drop; CLOSED_HALFSPACE_COMPONENT_GE];
    MP_TAC(REAL_ARITH `!x. x <= &1 / &2 \/ x >= &1 / &2`) THEN SET_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^(N,1)finite_sum` THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_CASES_TAC `(x:real^(N,1)finite_sum) IN t1` THENL
     [ASM_SIMP_TAC[DROP_VEC] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ASM SET_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^(N,1)finite_sum` THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_CASES_TAC `(x:real^(N,1)finite_sum) IN t2` THENL
     [ASM_SIMP_TAC[DROP_VEC] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ASM SET_TAC[]]]);;

let ENR_OPEN_UNION = prove
 (`!s t u:real^N->bool.
        open_in (subtopology euclidean u) s /\
        open_in (subtopology euclidean u) t /\
        ENR(s) /\ ENR(t)
        ==> ENR(s UNION t)`,
  REWRITE_TAC[ENR_ANR] THEN
  ASM_MESON_TAC[ANR_OPEN_UNION; LOCALLY_COMPACT_OPEN_UNION]);;

let ANR_OPEN_UNIONS = prove
 (`!f:(real^N->bool)->bool u.
        (!s. s IN f ==> ANR s) /\
        (!s. s IN f ==> open_in (subtopology euclidean u) s)
        ==> ANR(UNIONS f)`,
  let lemma1 = prove
   (`!f:(real^N->bool)->bool.
          pairwise DISJOINT f /\
          (!u. u IN f ==> ANR u) /\
          (!u. u IN f ==> open_in (subtopology euclidean (UNIONS f)) u)
          ==> ANR(UNIONS f)`,
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTE_NEIGHBOURHOOD_EXTENSOR_IMP_ANR THEN
    MAP_EVERY X_GEN_TAC
     [`g:real^(N,1)finite_sum->real^N`;
      `s:real^(N,1)finite_sum->bool`; `t:real^(N,1)finite_sum->bool`] THEN
    STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
    ABBREV_TAC
     `a = \u. {x | x IN t /\ (g:real^(N,1)finite_sum->real^N) x IN u}` THEN
    ASM_CASES_TAC
     `?u. u IN f /\ (a:(real^N->bool)->real^(N,1)finite_sum->bool) u = t`
    THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `ANR(u:real^N->bool)` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o ISPEC `g:real^(N,1)finite_sum->real^N` o
        MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
          ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR)) THEN
      DISCH_THEN(MP_TAC o SPECL
       [`s:real^(N,1)finite_sum->bool`; `t:real^(N,1)finite_sum->bool`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [UNDISCH_TAC `(a:(real^N->bool)->real^(N,1)finite_sum->bool) u = t` THEN
        EXPAND_TAC "a" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
        REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!u. u IN f
          ==> closed_in (subtopology euclidean s)
                        ((a:(real^N->bool)->real^(N,1)finite_sum->bool) u)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "a" THEN
      MATCH_MP_TAC CLOSED_IN_TRANS THEN
      EXISTS_TAC `t:real^(N,1)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_GEN THEN
      EXISTS_TAC `UNIONS f:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `u:real^N->bool = UNIONS f DIFF UNIONS(f DELETE u)`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[DIFF_UNIONS_PAIRWISE_DISJOINT; DELETE_SUBSET] THEN
        ASM SET_TAC[];
        MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL] THEN
        MATCH_MP_TAC OPEN_IN_UNIONS THEN ASM_SIMP_TAC[IN_DELETE]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `pairwise (\i j. DISJOINT
                  ((a:(real^N->bool)->real^(N,1)finite_sum->bool) i) (a j))
               f`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
      EXPAND_TAC "a" THEN REWRITE_TAC[pairwise] THEN SET_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC
     `v = \u. if a u = {} then {}
              else { x:real^(N,1)finite_sum |
                     x IN s /\
                     setdist({x},a(u:real^N->bool)) < setdist({x},t DIFF a u)}`
    THEN
    SUBGOAL_THEN
     `!u. u IN f
          ==> open_in (subtopology euclidean s)
                      ((v:(real^N->bool)->real^(N,1)finite_sum->bool) u)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "v" THEN
      COND_CASES_TAC THEN REWRITE_TAC[OPEN_IN_EMPTY] THEN
      ONCE_REWRITE_TAC[MESON[LIFT_DROP; REAL_SUB_LT]
       `x < y <=> &0 < drop(lift(y - x))`] THEN
      ONCE_REWRITE_TAC[SET_RULE `&0 < drop x <=> x IN {y | &0 < drop y}`] THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
      REWRITE_TAC[drop; GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT] THEN
      SIMP_TAC[LIFT_SUB; CONTINUOUS_ON_SUB; CONTINUOUS_ON_LIFT_SETDIST];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!u. u IN f
          ==> (a:(real^N->bool)->real^(N,1)finite_sum->bool) u SUBSET v u`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "v" THEN REWRITE_TAC[SUBSET] THEN
      X_GEN_TAC `x:real^(N,1)finite_sum` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
      SIMP_TAC[IN_ELIM_THM; SETDIST_SING_IN_SET; SUBSET] THEN
      REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[CLOSED_IN_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
      REWRITE_TAC[SETDIST_POS_LE] THEN
      MP_TAC(ISPEC `t:real^(N,1)finite_sum->bool` SETDIST_EQ_0_CLOSED_IN) THEN
      DISCH_THEN(fun th ->
       W(MP_TAC o PART_MATCH (lhand o rand) th o rand o snd)) THEN
      ASM_REWRITE_TAC[IN_DIFF] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL] THEN
          EXPAND_TAC "a" THEN
          MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
          EXISTS_TAC `UNIONS f:real^N->bool` THEN ASM_SIMP_TAC[];
          UNDISCH_TAC
           `x IN (a:(real^N->bool)->real^(N,1)finite_sum->bool) u` THEN
          EXPAND_TAC "a" THEN SIMP_TAC[IN_ELIM_THM]];
        DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC(SET_RULE
         `s SUBSET t /\ ~(s = t) ==> ~(t DIFF s = {})`) THEN
        CONJ_TAC THENL [EXPAND_TAC "a" THEN SET_TAC[]; ASM_MESON_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `pairwise (\i j. DISJOINT
                  ((v:(real^N->bool)->real^(N,1)finite_sum->bool) i) (v j))
               f`
    ASSUME_TAC THENL
     [EXPAND_TAC "v" THEN REWRITE_TAC[pairwise] THEN
      MAP_EVERY X_GEN_TAC [`u1:real^N->bool`; `u2:real^N->bool`] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[DISJOINT_EMPTY]) THEN
      STRIP_TAC THEN REWRITE_TAC[DISJOINT; EXTENSION] THEN
      X_GEN_TAC `x:real^(N,1)finite_sum` THEN
      REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY; IN_INTER] THEN
      ASM_CASES_TAC `(x:real^(N,1)finite_sum) IN s` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `b <= c /\ d <= a ==> ~(a < b /\ c < d)`) THEN
      CONJ_TAC THEN MATCH_MP_TAC SETDIST_SUBSET_RIGHT THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE
       `s SUBSET t /\ DISJOINT s u ==> s SUBSET t DIFF u`) THEN
      (CONJ_TAC THENL [EXPAND_TAC "a" THEN SET_TAC[]; ALL_TAC]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[pairwise]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!u. u IN (f:(real^N->bool)->bool)
          ==> ?v h. a u SUBSET v /\
                    open_in (subtopology euclidean s) v /\
                    (h:real^(N,1)finite_sum->real^N) continuous_on v /\
                    IMAGE h v SUBSET u /\
                    (!x. x IN a u ==> h x = g x)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR THEN
      ASM_SIMP_TAC[] THEN EXPAND_TAC "a" THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN SET_TAC[];
        ASM SET_TAC[]];
      GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC
     [`w:(real^N->bool)->real^(N,1)finite_sum->bool`;
      `h:(real^N->bool)->real^(N,1)finite_sum->real^N`] THEN
    REWRITE_TAC[TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`subtopology euclidean
        (UNIONS(IMAGE (\u. v u INTER
                         (w:(real^N->bool)->real^(N,1)finite_sum->bool) u)
                    f))`;
      `euclidean:(real^N)topology`;
      `h:(real^N->bool)->real^(N,1)finite_sum->real^N`;
      `\u. v u INTER (w:(real^N->bool)->real^(N,1)finite_sum->bool) u`;
      `f:(real^N->bool)->bool`]
    PASTING_LEMMA_EXISTS) THEN
    REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                SUBTOPOLOGY_SUBTOPOLOGY] THEN
    ONCE_REWRITE_TAC[TAUT `open_in a b /\ c <=> ~(open_in a b ==> ~c)`] THEN
    SIMP_TAC[ISPEC `euclidean` OPEN_IN_IMP_SUBSET;
             SET_RULE `s SUBSET u ==> u INTER s = s`] THEN
    REWRITE_TAC[NOT_IMP] THEN
    REWRITE_TAC[SIMPLE_IMAGE; SUBSET_REFL; SUBSET_UNIV] THEN ANTS_TAC THENL
     [CONJ_TAC THEN X_GEN_TAC `u:real^N->bool` THENL
       [DISCH_TAC THEN CONJ_TAC THENL
         [ALL_TAC; ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTER_SUBSET]] THEN
        MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
        EXISTS_TAC `s:real^(N,1)finite_sum->bool` THEN
        REPEAT CONJ_TAC THENL
         [ASM_SIMP_TAC[OPEN_IN_INTER];
          REWRITE_TAC[UNIONS_IMAGE] THEN ASM SET_TAC[];
          REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
          ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; SUBSET_TRANS; INTER_SUBSET]];
        X_GEN_TAC `u':real^N->bool` THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
        DISCH_THEN(MP_TAC o SPECL [`u:real^N->bool`; `u':real^N->bool`]) THEN
        ASM_CASES_TAC `u:real^N->bool = u'` THEN ASM_REWRITE_TAC[] THEN
        SET_TAC[]];
      GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `h:real^(N,1)finite_sum->real^N` THEN
      STRIP_TAC THEN EXISTS_TAC
       `UNIONS(IMAGE (\u. v u INTER
                          (w:(real^N->bool)->real^(N,1)finite_sum->bool) u)
                     f)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `IMAGE g t SUBSET u
          ==> {x | x IN t /\ g x IN u} SUBSET x ==> t SUBSET x`)) THEN
        REWRITE_TAC[UNIONS_IMAGE; SUBSET; IN_ELIM_THM] THEN
        X_GEN_TAC `x:real^(N,1)finite_sum` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        REWRITE_TAC[IN_UNIONS; IN_INTER] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->bool` THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `x IN (a:(real^N->bool)->real^(N,1)finite_sum->bool) u`
        MP_TAC THENL
         [EXPAND_TAC "a" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
          ASM SET_TAC[]];
        MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
        ASM_SIMP_TAC[OPEN_IN_INTER];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_UNIONS;
                    IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
        X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
        X_GEN_TAC `x:real^(N,1)finite_sum` THEN
        REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL
         [`x:real^(N,1)finite_sum`; `u:real^N->bool`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[IN_INTER; UNIONS_IMAGE; IN_ELIM_THM] THEN
          ASM_MESON_TAC[];
          ASM SET_TAC[]];
        X_GEN_TAC `x:real^(N,1)finite_sum` THEN DISCH_TAC THEN
        SUBGOAL_THEN `?u. u IN f /\ x IN
                          (a:(real^N->bool)->real^(N,1)finite_sum->bool) u`
        STRIP_ASSUME_TAC THENL
         [EXPAND_TAC "a" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
          ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL
         [`x:real^(N,1)finite_sum`; `u:real^N->bool`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[IN_INTER; UNIONS_IMAGE; IN_ELIM_THM] THEN
          ASM_MESON_TAC[SUBSET];
          ASM SET_TAC[]]]]) in
  let lemma2 = prove
   (`!f:(real^N->bool)->bool.
          FINITE f /\
          (!u. u IN f ==> ANR u) /\
          (!u. u IN f ==> open_in (subtopology euclidean (UNIONS f)) u)
          ==> ANR(UNIONS f)`,
    ONCE_REWRITE_TAC[IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC[UNIONS_0; ANR_EMPTY; FORALL_IN_INSERT; UNIONS_INSERT] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `f:(real^N->bool)->bool`] THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN MATCH_MP_TAC ANR_OPEN_UNION THEN
    EXISTS_TAC `u UNION UNIONS f:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_UNIONS; FORALL_IN_INSERT] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    X_GEN_TAC `v:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
    EXISTS_TAC `u UNION UNIONS f:real^N->bool` THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[]) in
  let lemma3 = prove
   (`!v:num->real^N->bool.
          (!n. v(n) SUBSET v(SUC n)) /\
          (!n. open_in
                (subtopology euclidean (UNIONS(IMAGE v (:num)))) (v n)) /\
          (!n. ANR(v n))
          ==> ANR(UNIONS(IMAGE v (:num)))`,
    REPEAT STRIP_TAC THEN
    ABBREV_TAC `s:real^N->bool = UNIONS(IMAGE v (:num))` THEN
    ASM_CASES_TAC `?n:num. s:real^N->bool = v n` THENL
     [ASM_MESON_TAC[]; RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM])] THEN
    ABBREV_TAC
     `w = \n:num. {x:real^N | x IN s /\
                              inv(&2 pow n) < setdist({x},s DIFF v n)}` THEN
    SUBGOAL_THEN
     `!n. open_in (subtopology euclidean s) ((w:num->real^N->bool) n)`
    ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "w" THEN
      ONCE_REWRITE_TAC[MESON[LIFT_DROP; REAL_SUB_LT]
       `x < y <=> &0 < drop(lift(y - x))`] THEN
      ONCE_REWRITE_TAC[SET_RULE `&0 < drop x <=> x IN {y | &0 < drop y}`] THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
      REWRITE_TAC[drop; GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT] THEN
      SIMP_TAC[LIFT_SUB; CONTINUOUS_ON_SUB; CONTINUOUS_ON_LIFT_SETDIST;
               CONTINUOUS_ON_CONST];
      ALL_TAC] THEN
    SUBGOAL_THEN `!n. (w:num->real^N->bool) n SUBSET v n` ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "w" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN
      ONCE_REWRITE_TAC[TAUT `p /\ q ==> r <=> p /\ ~r ==> ~q`] THEN
      SIMP_TAC[SETDIST_SING_IN_SET; IN_DIFF; REAL_NOT_LT; REAL_LE_INV_EQ] THEN
      SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_POW2];
      ALL_TAC] THEN
    SUBGOAL_THEN `!n. ANR((w:num->real^N->bool) n)` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC ANR_OPEN_IN THEN
      EXISTS_TAC `(v:num->real^N->bool) n` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!n. s INTER closure(w n) SUBSET (w:num->real^N->bool)(SUC n)`
    ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "w" THEN
      TRANS_TAC SUBSET_TRANS
       `{x:real^N | x IN s /\ inv(&2 pow n) <= setdist({x},s DIFF v n)}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL_LOCAL THEN
        SIMP_TAC[SUBSET; IN_ELIM_THM; REAL_LT_IMP_LE] THEN
        ONCE_REWRITE_TAC[MESON[LIFT_DROP; REAL_SUB_LE]
         `x <= y <=> &0 <= drop(lift(y - x))`] THEN
        ONCE_REWRITE_TAC[SET_RULE
         `&0 <= drop x <=> x IN {y | &0 <= drop y}`] THEN
        MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
        REWRITE_TAC[drop; GSYM real_ge; CLOSED_HALFSPACE_COMPONENT_GE] THEN
        SIMP_TAC[LIFT_SUB; CONTINUOUS_ON_SUB; CONTINUOUS_ON_LIFT_SETDIST;
                 CONTINUOUS_ON_CONST];
        REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
        REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
         `b < a /\ x <= y ==> a <= x ==> b < y`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV2 THEN REWRITE_TAC[REAL_LT_POW2] THEN
          MATCH_MP_TAC REAL_POW_MONO_LT THEN
          REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
          MATCH_MP_TAC SETDIST_SUBSET_RIGHT THEN ASM SET_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `s:real^N->bool = UNIONS(IMAGE w (:num))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; UNIONS_SUBSET] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; UNIONS_IMAGE; IN_UNIV] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]] THEN
      EXPAND_TAC "w" THEN REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?n:num. (x:real^N) IN v n` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < setdist ({x:real^N},s DIFF v(n:num))` MP_TAC THENL
       [REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
        REWRITE_TAC[SETDIST_POS_LE] THEN
        MP_TAC(ISPEC `s:real^N->bool` SETDIST_EQ_0_CLOSED_IN) THEN
        DISCH_THEN(fun th ->
         W(MP_TAC o PART_MATCH (lhand o rand) th o rand o snd)) THEN
        ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_REFL] THEN
        DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[];
        DISCH_THEN(MP_TAC o SPEC `inv(&2)` o
          MATCH_MP (REWRITE_RULE[IMP_CONJ] REAL_ARCH_POW_INV)) THEN
        ANTS_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
        X_GEN_TAC `m:num` THEN REWRITE_TAC[REAL_POW_INV] THEN DISCH_TAC THEN
        EXISTS_TAC `m + n:num` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `a < b ==> x <= a /\ b <= y ==> x < y`)) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_LT_POW2] THEN
          MATCH_MP_TAC REAL_POW_MONO THEN
          REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
          MATCH_MP_TAC SETDIST_SUBSET_RIGHT THEN
          CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          MATCH_MP_TAC(SET_RULE
           `s SUBSET t ==> u DIFF t SUBSET u DIFF s`) THEN
          MATCH_MP_TAC(MESON[LE_ADD; ADD_SYM]
           `(!m n:num. m <= n ==> v m SUBSET v n)
            ==> v b SUBSET v(a + b)`) THEN
          MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM SET_TAC[]]];
      ALL_TAC] THEN
    (STRIP_ASSUME_TAC o prove_general_recursive_function_exists)
     `?r:num->real^N->bool.
          r 0 = w 0 /\
          r 1 = w 1 /\
          (!n. r(n + 2) = w(n + 2) DIFF (s INTER closure(w n)))` THEN
    SUBGOAL_THEN
     `!n. open_in (subtopology euclidean (w n)) ((r:num->real^N->bool) n)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC num_INDUCTION THEN ASM_REWRITE_TAC[OPEN_IN_REFL] THEN
      MATCH_MP_TAC num_INDUCTION THEN ASM_REWRITE_TAC[ARITH; OPEN_IN_REFL] THEN
      X_GEN_TAC `n:num` THEN REPLICATE_TAC 2 (DISCH_THEN(K ALL_TAC)) THEN
      ASM_REWRITE_TAC[ARITH_RULE `SUC(SUC n) = n + 2`] THEN
      ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s DIFF (s INTER t)`] THEN
      MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
      MATCH_MP_TAC(MESON[CLOSED_IN_CLOSED_INTER]
       `closed u /\ s INTER t INTER u = s INTER u
        ==> closed_in (subtopology euclidean s) (s INTER t INTER u)`) THEN
      REWRITE_TAC[CLOSED_CLOSURE] THEN MATCH_MP_TAC
       (SET_RULE `s SUBSET t ==> s INTER t INTER u = s INTER u`) THEN
      ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!n. open_in (subtopology euclidean s) ((r:num->real^N->bool) n)`
    ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_TRANS]; ALL_TAC] THEN
    SUBGOAL_THEN `!n. ANR((r:num->real^N->bool) n)` ASSUME_TAC THENL
     [ASM_MESON_TAC[ANR_OPEN_IN]; ALL_TAC] THEN
    SUBGOAL_THEN
     `UNIONS (IMAGE w (:num)):real^N->bool = UNIONS(IMAGE r (:num))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
       [REWRITE_TAC[UNIONS_IMAGE; IN_UNIV; SUBSET; IN_ELIM_THM] THEN
        X_GEN_TAC `x:real^N` THEN GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
        MATCH_MP_TAC MONO_EXISTS THEN
        MATCH_MP_TAC num_INDUCTION THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC num_INDUCTION THEN ASM_SIMP_TAC[ARITH] THEN
        X_GEN_TAC `n:num` THEN REPLICATE_TAC 2 (DISCH_THEN(K ALL_TAC)) THEN
        ASM_REWRITE_TAC[ARITH_RULE `SUC(SUC n) = n + 2`] THEN
        SIMP_TAC[IN_DIFF; IN_INTER] THEN
        DISCH_THEN(MP_TAC o SPEC `SUC n` o CONJUNCT2) THEN
        ANTS_TAC THENL [ARITH_TAC; ASM SET_TAC[]];
        MATCH_MP_TAC UNIONS_MONO_IMAGE THEN REWRITE_TAC[IN_UNIV] THEN
        MATCH_MP_TAC num_INDUCTION THEN ASM_SIMP_TAC[SUBSET_REFL] THEN
        MATCH_MP_TAC num_INDUCTION THEN ASM_SIMP_TAC[ARITH; SUBSET_REFL] THEN
        ASM_REWRITE_TAC[ARITH_RULE `SUC(SUC n) = n + 2`] THEN SET_TAC[]];
      ALL_TAC] THEN
    EXPAND_TAC "s" THEN
    SUBGOAL_THEN
     `(:num) = IMAGE (\n. 2 * n) (:num) UNION IMAGE (\n. 2 * n + 1) (:num)`
     (fun th -> ONCE_REWRITE_TAC[th] THEN ASSUME_TAC(SYM th))
    THENL
     [REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE; IN_UNION] THEN
      REWRITE_TAC[GSYM EVEN_EXISTS; GSYM ADD1; GSYM ODD_EXISTS] THEN
      REWRITE_TAC[EVEN_OR_ODD];
      REWRITE_TAC[IMAGE_UNION; GSYM IMAGE_o; o_DEF; UNIONS_UNION]] THEN
    MATCH_MP_TAC ANR_OPEN_UNION THEN
    EXISTS_TAC
     `UNIONS (IMAGE (\x. r (2 * x)) (:num)) UNION
      UNIONS (IMAGE (\x. r (2 * x + 1)) (:num)):real^N->bool` THEN
    ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
      EXISTS_TAC `s:real^N->bool` THEN REWRITE_TAC[SUBSET_UNION] THEN
      ASM_SIMP_TAC[OPEN_IN_UNIONS; FORALL_IN_IMAGE; UNION_SUBSET] THEN
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
      ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC lemma1 THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
    (CONJ_TAC THENL
      [ALL_TAC;
       X_GEN_TAC `n:num` THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
       EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[UNIONS_SUBSET] THEN
       REWRITE_TAC[FORALL_IN_IMAGE] THEN
       CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]]]) THEN
    REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_UNIV] THEN MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
    (CONJ_TAC THENL [MESON_TAC[DISJOINT_SYM]; ALL_TAC]) THEN
    X_GEN_TAC `m:num` THEN MATCH_MP_TAC num_INDUCTION THEN
    ASM_REWRITE_TAC[CONJUNCT1 LT; ARITH_RULE `2 * SUC n = 2 * n + 2`;
                    ARITH_RULE `(2 * n + 2) + 1 = (2 * n + 1) + 2`] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[LT_SUC_LE] THEN DISCH_TAC THEN DISCH_THEN(K ALL_TAC) THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP
       (ARITH_RULE `m <= n ==> 2 * m <= 2 * n`)) THEN
      SPEC_TAC(`2 * n`,`n:num`) THEN SPEC_TAC(`2 * m`,`m:num`);
      FIRST_X_ASSUM(MP_TAC o MATCH_MP
       (ARITH_RULE `m <= n ==> 2 * m + 1 <= 2 * n + 1`)) THEN
      SPEC_TAC(`2 * n + 1`,`n:num`) THEN SPEC_TAC(`2 * m + 1`,`m:num`)] THEN
    (REPEAT STRIP_TAC THEN
     MATCH_MP_TAC(SET_RULE
      `r m SUBSET s /\ r m SUBSET w m /\
       w m SUBSET w n /\ w n SUBSET closure(w n)
       ==> DISJOINT (r m) (w(n + 2) DIFF s INTER closure(w n))`) THEN
     REWRITE_TAC[CLOSURE_SUBSET] THEN REPEAT CONJ_TAC THENL
      [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
       SPEC_TAC(`m:num`,`p:num`) THEN
       MATCH_MP_TAC num_INDUCTION THEN ASM_SIMP_TAC[SUBSET_REFL] THEN
       MATCH_MP_TAC num_INDUCTION THEN ASM_SIMP_TAC[ARITH; SUBSET_REFL] THEN
       ASM_REWRITE_TAC[ARITH_RULE `SUC(SUC n) = n + 2`] THEN SET_TAC[];
       UNDISCH_TAC `m:num <= n` THEN
       MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`n:num`;` m:num`] THEN
       MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
       REWRITE_TAC[SUBSET_REFL; SUBSET_TRANS] THEN
       X_GEN_TAC `p:num` THEN
       TRANS_TAC SUBSET_TRANS `s INTER closure((w:num->real^N->bool) p)` THEN
       ASM_REWRITE_TAC[SUBSET_INTER; CLOSURE_SUBSET] THEN
       ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]])) in
  let lemma4 = prove
   (`!v:num->real^N->bool.
          (!n. open_in
                (subtopology euclidean (UNIONS(IMAGE v (:num)))) (v n)) /\
          (!n. ANR(v n))
          ==> ANR(UNIONS(IMAGE v (:num)))`,
    GEN_TAC THEN
    ABBREV_TAC `u:num->real^N->bool = \n. UNIONS (IMAGE v (0..n))` THEN
    SUBGOAL_THEN `UNIONS(IMAGE v (:num)):real^N->bool = UNIONS(IMAGE u (:num))`
     (fun th -> ONCE_REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]))
    THENL
     [EXPAND_TAC "u" THEN
      REWRITE_TAC[EXTENSION; UNIONS_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
      REWRITE_TAC[IN_NUMSEG; LE_0] THEN MESON_TAC[LE_REFL];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma3 THEN
      EXPAND_TAC "u" THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET_NUMSEG] THEN
        ARITH_TAC;
        GEN_TAC THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
        REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
        GEN_TAC THEN MATCH_MP_TAC lemma2 THEN
        ASM_SIMP_TAC[FORALL_IN_IMAGE; FINITE_IMAGE; FINITE_NUMSEG] THEN
        X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN STRIP_TAC THEN
        REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SPEC `k:num`)) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
          OPEN_IN_SUBSET_TRANS)) THEN
        CONJ_TAC THENL
         [REWRITE_TAC[UNIONS_IMAGE; IN_NUMSEG; LE_0] THEN ASM SET_TAC[];
          REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE; IN_NUMSEG; LE_0] THEN
          X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[UNIONS_IMAGE] THEN
          EXPAND_TAC "u" THEN
          REWRITE_TAC[UNIONS_IMAGE; IN_UNIV; IN_NUMSEG; LE_0] THEN
          REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]]]]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:(real^N->bool)->bool`; `u:real^N->bool`]
        LINDELOF_OPEN_IN) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:(real^N->bool)->bool` THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_CASES_TAC `g:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[UNIONS_0; ANR_EMPTY] THEN
  MP_TAC(ISPEC `g:(real^N->bool)->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h:num->real^N->bool` THEN DISCH_THEN SUBST_ALL_TAC THEN
  MATCH_MP_TAC lemma4 THEN
  CONJ_TAC THENL [GEN_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
  EXISTS_TAC `u:real^N->bool` THEN REWRITE_TAC[UNIONS_IMAGE] THEN
  REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[SUBSET; IN_UNIV; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `(h:num->real^N->bool) n`)) THEN
  REPEAT(ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC]) THEN
  ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; SUBSET]);;

let ENR_OPEN_UNIONS = prove
 (`!f:(real^N->bool)->bool u.
        (!s. s IN f ==> ENR s) /\
        (!s. s IN f ==> open_in (subtopology euclidean u) s)
        ==> ENR(UNIONS f)`,
  REWRITE_TAC[ENR_ANR] THEN
  MESON_TAC[ANR_OPEN_UNIONS; LOCALLY_COMPACT_OPEN_UNIONS]);;

let LOCALLY_ANR_ALT = prove
 (`!s:real^N->bool.
        locally ANR s <=>
        !v x. open_in (subtopology euclidean s) v /\ x IN v
              ==> ?u. open_in (subtopology euclidean s) u /\ ANR u /\
                      x IN u /\ u SUBSET v`,
  GEN_TAC THEN REWRITE_TAC[locally] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[SUBSET_REFL]] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `v:real^N->bool` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `u:real^N->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC ANR_OPEN_IN THEN EXISTS_TAC  `w:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
  EXISTS_TAC `s:real^N->bool` THEN
  ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; SUBSET_TRANS]);;

let LOCALLY_ANR = prove
 (`!s:real^N->bool.
        locally ANR s <=>
        !x. x IN s
            ==> ?v. x IN v /\ open_in (subtopology euclidean s) v /\ ANR v`,
  GEN_TAC THEN REWRITE_TAC[LOCALLY_ANR_ALT] THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
  EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^N` THENL
   [DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC(SPEC `s:real^N->bool` th)) THEN
    ASM_REWRITE_TAC[OPEN_IN_REFL] THEN MESON_TAC[];
    DISCH_THEN(fun th ->
      X_GEN_TAC `v:real^N->bool` THEN STRIP_TAC THEN MP_TAC th) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC `w:real^N->bool` THEN STRIP_TAC THEN
    EXISTS_TAC `v INTER w:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER; INTER_SUBSET] THEN
    MATCH_MP_TAC ANR_OPEN_IN THEN EXISTS_TAC  `w:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
    EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[INTER_SUBSET; OPEN_IN_INTER] THEN
    ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]]);;

let ANR_LOCALLY = prove
 (`!s:real^N->bool. locally ANR s <=> ANR s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LOCALLY_ANR] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[OPEN_IN_REFL]] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:real^N->real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `UNIONS (IMAGE (f:real^N->real^N->bool) s) = s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
    EXPAND_TAC "s" THEN MATCH_MP_TAC ANR_OPEN_UNIONS THEN
    ASM_MESON_TAC[FORALL_IN_IMAGE]]);;

let LOCALLY_ENR_ALT = prove
 (`!s:real^N->bool.
        locally ENR s <=>
        !v x. open_in (subtopology euclidean s) v /\ x IN v
              ==> ?u. open_in (subtopology euclidean s) u /\ ENR u /\
                      x IN u /\ u SUBSET v`,
  GEN_TAC THEN REWRITE_TAC[locally] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[SUBSET_REFL]] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `v:real^N->bool` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `u:real^N->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC ENR_OPEN_IN THEN EXISTS_TAC  `w:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
  EXISTS_TAC `s:real^N->bool` THEN
  ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; SUBSET_TRANS]);;

let LOCALLY_ENR = prove
 (`!s:real^N->bool.
        locally ENR s <=>
        !x. x IN s
            ==> ?v. x IN v /\ open_in (subtopology euclidean s) v /\ ENR v`,
  GEN_TAC THEN REWRITE_TAC[LOCALLY_ENR_ALT] THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
  EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^N` THENL
   [DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC(SPEC `s:real^N->bool` th)) THEN
    ASM_REWRITE_TAC[OPEN_IN_REFL] THEN MESON_TAC[];
    DISCH_THEN(fun th ->
      X_GEN_TAC `v:real^N->bool` THEN STRIP_TAC THEN MP_TAC th) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC `w:real^N->bool` THEN STRIP_TAC THEN
    EXISTS_TAC `v INTER w:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER; INTER_SUBSET] THEN
    MATCH_MP_TAC ENR_OPEN_IN THEN EXISTS_TAC  `w:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
    EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[INTER_SUBSET; OPEN_IN_INTER] THEN
    ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]]);;

let ENR_LOCALLY = prove
 (`!s:real^N->bool. locally ENR s <=> ENR s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LOCALLY_ENR] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[OPEN_IN_REFL]] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:real^N->real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `UNIONS (IMAGE (f:real^N->real^N->bool) s) = s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
    EXPAND_TAC "s" THEN MATCH_MP_TAC ENR_OPEN_UNIONS THEN
    ASM_MESON_TAC[FORALL_IN_IMAGE]]);;

let ANR_COVERING_SPACE_EQ = prove
 (`!p:real^M->real^N s c.
        covering_space (c,p) s ==> (ANR s <=> ANR c)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  ONCE_REWRITE_TAC[GSYM ANR_LOCALLY] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_LOCALLY_HOMEOMORPHIC_EQ)) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_ANRNESS THEN
  REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[]);;

let ANR_COVERING_SPACE = prove
 (`!p:real^M->real^N s c.
        covering_space (c,p) s /\ ANR c ==> ANR s`,
  MESON_TAC[ANR_COVERING_SPACE_EQ]);;

let ENR_COVERING_SPACE_EQ = prove
 (`!p:real^M->real^N s c.
        covering_space (c,p) s ==> (ENR s <=> ENR c)`,
  REWRITE_TAC[ENR_ANR] THEN
  MESON_TAC[ANR_COVERING_SPACE_EQ; COVERING_SPACE_LOCALLY_COMPACT_EQ]);;

let ENR_COVERING_SPACE = prove
 (`!p:real^M->real^N s c.
        covering_space (c,p) s /\ ENR c ==> ENR s`,
  MESON_TAC[ENR_COVERING_SPACE_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Original ANR material, now for ENRs. Eventually more of this will be      *)
(* updated and generalized for AR and ANR as well.                           *)
(* ------------------------------------------------------------------------- *)

let ENR_BOUNDED = prove
 (`!s:real^N->bool.
        bounded s
        ==> (ENR s <=> ?u. open u /\ bounded u /\ s retract_of u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ENR] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^N` o MATCH_MP BOUNDED_SUBSET_BALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ball(vec 0:real^N,r) INTER u` THEN
  ASM_SIMP_TAC[BOUNDED_INTER; OPEN_INTER; OPEN_BALL; BOUNDED_BALL] THEN
  MATCH_MP_TAC RETRACT_OF_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
  ASM SET_TAC[]);;

let ABSOLUTE_RETRACT_IMP_AR_GEN = prove
 (`!s:real^M->bool s':real^N->bool t u.
      s retract_of t /\ convex t /\ ~(t = {}) /\
      s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
      ==> s' retract_of u`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`s:real^M->bool`; `t:real^M->bool`]
    AR_RETRACT_OF_AR) THEN ASM_SIMP_TAC[CONVEX_IMP_AR] THEN
  ASM_MESON_TAC[AR_IMP_ABSOLUTE_RETRACT]);;

let ABSOLUTE_RETRACT_IMP_AR = prove
 (`!s s'. s retract_of (:real^M) /\ s homeomorphic s' /\ closed s'
          ==> s' retract_of (:real^N)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTE_RETRACT_IMP_AR_GEN THEN
  MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `(:real^M)`] THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN
  REWRITE_TAC[CONVEX_UNIV; CLOSED_UNIV; UNIV_NOT_EMPTY]);;

let HOMEOMORPHIC_COMPACT_ARNESS = prove
 (`!s s'. s homeomorphic s'
          ==> (compact s /\ s retract_of (:real^M) <=>
               compact s' /\ s' retract_of (:real^N))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `compact(s:real^M->bool) /\ compact(s':real^N->bool)` THENL
   [ALL_TAC; ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS]] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] ABSOLUTE_RETRACT_IMP_AR) THEN
  ASM_MESON_TAC[HOMEOMORPHIC_SYM; COMPACT_IMP_CLOSED]);;

let EXTENSION_INTO_AR_LOCAL = prove
 (`!f:real^M->real^N c s t.
        f continuous_on c /\ IMAGE f c SUBSET t /\ t retract_of (:real^N) /\
        closed_in (subtopology euclidean s) c
        ==> ?g. g continuous_on s /\ IMAGE g (:real^M) SUBSET t /\
                !x. x IN c ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`; `c:real^M->bool`]
        TIETZE_UNBOUNDED) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:real^M->real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(r:real^N->real^N) o (g:real^M->real^N)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    REWRITE_TAC[o_THM] THEN ASM SET_TAC[]]);;

let EXTENSION_INTO_AR = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ t retract_of (:real^N) /\
        closed s
        ==> ?g. g continuous_on (:real^M) /\ IMAGE g (:real^M) SUBSET t /\
                !x. x IN s ==> g x = f x`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`f:real^M->real^N`; `s:real^M->bool`; `(:real^M)`; `t:real^N->bool`]
   EXTENSION_INTO_AR_LOCAL) THEN
  REWRITE_TAC[GSYM OPEN_IN; GSYM CLOSED_IN; SUBTOPOLOGY_UNIV]);;

let NEIGHBOURHOOD_EXTENSION_INTO_ANR = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ ANR t /\ closed s
        ==> ?v g. s SUBSET v /\ open v /\ g continuous_on v /\
                  IMAGE g v SUBSET t /\ !x. x IN s ==> g x = f x`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`f:real^M->real^N`; `(:real^M)`; `s:real^M->bool`; `t:real^N->bool`]
   ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
  REWRITE_TAC[GSYM OPEN_IN; GSYM CLOSED_IN; SUBTOPOLOGY_UNIV] THEN
  CONV_TAC TAUT);;

let EXTENSION_FROM_COMPONENT = prove
 (`!f:real^M->real^N s c u.
        (locally connected s \/ compact s /\ ANR u) /\
        c IN components s /\
        f continuous_on c /\ IMAGE f c SUBSET u
        ==> ?g. g continuous_on s /\ IMAGE g s SUBSET u /\
                !x. x IN c ==> g x = f x`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?t g. open_in (subtopology euclidean s) t /\
          closed_in (subtopology euclidean s) t /\
          c SUBSET t /\
          (g:real^M->real^N) continuous_on t /\ IMAGE g t SUBSET u /\
          !x. x IN c ==> g x = f x`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [MAP_EVERY EXISTS_TAC [`c:real^M->bool`; `f:real^M->real^N`] THEN
      ASM_SIMP_TAC[SUBSET_REFL; CLOSED_IN_COMPONENT;
                   OPEN_IN_COMPONENTS_LOCALLY_CONNECTED];
      MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`; `c:real^M->bool`;
                     `u:real^N->bool`]
       ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
      ASM_SIMP_TAC[CLOSED_IN_COMPONENT; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`w:real^M->bool`; `g:real^M->real^N`] THEN
      STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^M->bool` (STRIP_ASSUME_TAC o GSYM)) THEN
      MP_TAC(ISPECL [`s:real^M->bool`; `c:real^M->bool`; `v:real^M->bool`]
        SURA_BURA_CLOPEN_SUBSET) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_IMP_LOCALLY_COMPACT] THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC[COMPACT_COMPONENTS]; ASM SET_TAC[]];
        MATCH_MP_TAC MONO_EXISTS] THEN
      X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
      EXISTS_TAC `g:real^M->real^N` THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_SUBSET THEN
        ASM_MESON_TAC[COMPACT_IMP_CLOSED; OPEN_IN_IMP_SUBSET];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
        ASM SET_TAC[];
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
        ASM SET_TAC[]]];
    MP_TAC(ISPECL [`g:real^M->real^N`; `s:real^M->bool`;
                   `t:real^M->bool`; `u:real^N->bool`]
      EXTENSION_FROM_CLOPEN) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
    ASM SET_TAC[]]);;

let ABSOLUTE_RETRACT_FROM_UNION_AND_INTER = prove
 (`!s t. (s UNION t) retract_of (:real^N) /\
         (s INTER t) retract_of (:real^N) /\
         closed s /\ closed t
         ==> s retract_of (:real^N)`,
  MESON_TAC[RETRACT_OF_UNIV; AR_FROM_UNION_AND_INTER]);;

let COUNTABLE_ENR_COMPONENTS = prove
 (`!s:real^N->bool. ENR s ==> COUNTABLE(components s)`,
  SIMP_TAC[ENR_IMP_ANR; COUNTABLE_ANR_COMPONENTS]);;

let COUNTABLE_ENR_CONNECTED_COMPONENTS = prove
 (`!s:real^N->bool t.
        ENR s ==> COUNTABLE {connected_component s x | x | x IN t}`,
  SIMP_TAC[ENR_IMP_ANR; COUNTABLE_ANR_CONNECTED_COMPONENTS]);;

let COUNTABLE_ENR_PATH_COMPONENTS = prove
 (`!s:real^N->bool.
        ENR s ==> COUNTABLE {path_component s x | x | x IN s}`,
  SIMP_TAC[ENR_IMP_ANR; COUNTABLE_ANR_PATH_COMPONENTS]);;

let ENR_FROM_UNION_AND_INTER_GEN = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        ENR(s UNION t) /\ ENR(s INTER t)
        ==> ENR s`,
  REWRITE_TAC[ENR_ANR] THEN
  MESON_TAC[LOCALLY_COMPACT_CLOSED_IN; ANR_FROM_UNION_AND_INTER_LOCAL]);;

let ENR_FROM_UNION_AND_INTER = prove
 (`!s t:real^N->bool.
        closed s /\ closed t /\ ENR(s UNION t) /\ ENR(s INTER t)
        ==> ENR s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENR_FROM_UNION_AND_INTER_GEN THEN
  ASM_MESON_TAC[CLOSED_SUBSET; SUBSET_UNION]);;

let ENR_CLOSURE_FROM_FRONTIER = prove
 (`!s:real^N->bool. ENR(frontier s) ==> ENR(closure s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENR_FROM_UNION_AND_INTER THEN
  EXISTS_TAC `closure((:real^N) DIFF s)` THEN
  ASM_REWRITE_TAC[CLOSED_CLOSURE; GSYM FRONTIER_CLOSURES] THEN
  SUBGOAL_THEN
   `closure s UNION closure ((:real^N) DIFF s) = (:real^N)`
   (fun th -> REWRITE_TAC[th; ENR_UNIV]) THEN
  MATCH_MP_TAC(SET_RULE
   `s SUBSET closure s /\ (:real^N) DIFF s SUBSET closure((:real^N) DIFF s)
    ==> closure s UNION closure ((:real^N) DIFF s) = (:real^N)`) THEN
  REWRITE_TAC[CLOSURE_SUBSET]);;

let ANR_CLOSURE_FROM_FRONTIER = prove
 (`!s:real^N->bool. ANR(frontier s) ==> ANR(closure s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENR_IMP_ANR THEN
  MATCH_MP_TAC ENR_CLOSURE_FROM_FRONTIER THEN
  ASM_SIMP_TAC[ENR_ANR; FRONTIER_CLOSED; CLOSED_IMP_LOCALLY_COMPACT]);;

let ENR_FINITE_UNIONS_CONVEX_CLOSED = prove
 (`!t:(real^N->bool)->bool.
        FINITE t /\ (!c. c IN t ==> closed c /\ convex c) ==> ENR(UNIONS t)`,
  SIMP_TAC[ENR_ANR; ANR_FINITE_UNIONS_CONVEX_CLOSED] THEN
  SIMP_TAC[CLOSED_IMP_LOCALLY_COMPACT; CLOSED_UNIONS]);;

let FINITE_IMP_ENR = prove
 (`!s:real^N->bool. FINITE s ==> ENR s`,
  SIMP_TAC[FINITE_IMP_ANR; FINITE_IMP_CLOSED; ENR_ANR;
           CLOSED_IMP_LOCALLY_COMPACT]);;

let ENR_INSERT = prove
 (`!s a:real^N. closed s /\ ENR s ==> ENR(a INSERT s)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  MATCH_MP_TAC ENR_CLOSED_UNION THEN
  ASM_MESON_TAC[CLOSED_SING; ENR_SING; ENR_EMPTY;
                SET_RULE `{a} INTER s = {a} \/ {a} INTER s = {}`]);;

let ENR_TRIANGULATION = prove
 (`!tr. triangulation tr ==> ENR(UNIONS tr)`,
  REWRITE_TAC[triangulation] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ENR_FINITE_UNIONS_CONVEX_CLOSED THEN
  ASM_MESON_TAC[SIMPLEX_IMP_CLOSED; SIMPLEX_IMP_CONVEX]);;

let ENR_SIMPLICIAL_COMPLEX = prove
 (`!c. simplicial_complex c ==>  ENR(UNIONS c)`,
  MESON_TAC[ENR_TRIANGULATION; SIMPLICIAL_COMPLEX_IMP_TRIANGULATION]);;

let ENR_PATH_COMPONENT_ENR = prove
 (`!s x:real^N. ENR(s) ==> ENR(path_component s x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    ENR_OPEN_IN)) THEN
  MATCH_MP_TAC OPEN_IN_PATH_COMPONENT_LOCALLY_PATH_CONNECTED THEN
  MATCH_MP_TAC RETRACT_OF_LOCALLY_PATH_CONNECTED THEN
  ASM_MESON_TAC[ENR; OPEN_IMP_LOCALLY_PATH_CONNECTED]);;

let ENR_CONNECTED_COMPONENT_ENR = prove
 (`!s x:real^N. ENR(s) ==> ENR(connected_component s x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    ENR_OPEN_IN)) THEN
  MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENT_LOCALLY_CONNECTED THEN
  MATCH_MP_TAC RETRACT_OF_LOCALLY_CONNECTED THEN
  ASM_MESON_TAC[ENR; OPEN_IMP_LOCALLY_CONNECTED]);;

let ENR_COMPONENT_ENR = prove
 (`!s:real^N->bool.
        ENR s /\ c IN components s ==> ENR c`,
  REWRITE_TAC[IN_COMPONENTS] THEN MESON_TAC[ENR_CONNECTED_COMPONENT_ENR]);;

let ENR_INTER_CLOSED_OPEN = prove
 (`!s:real^N->bool. ENR s ==> ?t u. closed t /\ open u /\ s = t INTER u`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[ENR] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->bool` THEN
  STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_RETRACT) THEN
  REWRITE_TAC[CLOSED_IN_CLOSED] THEN ASM_MESON_TAC[INTER_COMM]);;

let ENR_IMP_FSGIMA = prove
 (`!s:real^N->bool. ENR s ==> fsigma s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ENR_INTER_CLOSED_OPEN) THEN
  ASM_SIMP_TAC[CLOSED_IMP_FSIGMA; OPEN_IMP_FSIGMA; FSIGMA_INTER]);;

let ENR_IMP_GDELTA = prove
 (`!s:real^N->bool. ENR s ==> gdelta s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ENR_INTER_CLOSED_OPEN) THEN
  ASM_SIMP_TAC[CLOSED_IMP_GDELTA; OPEN_IMP_GDELTA; GDELTA_INTER]);;

let IS_INTERVAL_IMP_FSIGMA = prove
 (`!s:real^N->bool. is_interval s ==> fsigma s`,
  SIMP_TAC[IS_INTERVAL_IMP_ENR; ENR_IMP_FSGIMA]);;

let IS_INTERVAL_IMP_GDELTA = prove
 (`!s:real^N->bool. is_interval s ==> gdelta s`,
  SIMP_TAC[IS_INTERVAL_IMP_ENR; ENR_IMP_GDELTA]);;

let IS_INTERVAL_IMP_BAIRE1_INDICATOR = prove
 (`!s. is_interval s ==> baire 1 (:real^N) (indicator s)`,
  SIMP_TAC[BAIRE1_INDICATOR; IS_INTERVAL_IMP_FSIGMA; IS_INTERVAL_IMP_GDELTA]);;

let ANR_COMPONENTWISE = prove
 (`!s:real^N->bool.
        ANR s <=>
        COUNTABLE(components s) /\
        !c. c IN components s
            ==> open_in (subtopology euclidean s) c /\ ANR c`,
  GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(r ==> p) /\ (p ==> q) /\ (p ==> r) ==> (p <=> q /\ r)`) THEN
  REWRITE_TAC[COUNTABLE_ANR_COMPONENTS] THEN CONJ_TAC THENL
   [DISCH_TAC THEN GEN_REWRITE_TAC RAND_CONV [UNIONS_COMPONENTS] THEN
    MATCH_MP_TAC ANR_OPEN_UNIONS THEN
    ASM_MESON_TAC[GSYM UNIONS_COMPONENTS];
    ASM_MESON_TAC[OPEN_IN_COMPONENTS_LOCALLY_CONNECTED;
                  ANR_IMP_LOCALLY_CONNECTED; ANR_OPEN_IN]]);;

let ENR_COMPONENTWISE = prove
 (`!s:real^N->bool.
        ENR s <=>
        COUNTABLE(components s) /\
        !c. c IN components s
            ==> open_in (subtopology euclidean s) c /\ ENR c`,
  GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(r ==> p) /\ (p ==> q) /\ (p ==> r) ==> (p <=> q /\ r)`) THEN
  REWRITE_TAC[COUNTABLE_ENR_COMPONENTS] THEN CONJ_TAC THENL
   [DISCH_TAC THEN GEN_REWRITE_TAC RAND_CONV [UNIONS_COMPONENTS] THEN
    MATCH_MP_TAC ENR_OPEN_UNIONS THEN
    ASM_MESON_TAC[GSYM UNIONS_COMPONENTS];
    ASM_MESON_TAC[OPEN_IN_COMPONENTS_LOCALLY_CONNECTED;
                  ENR_IMP_LOCALLY_CONNECTED; ENR_OPEN_IN]]);;

let ABSOLUTE_RETRACT_HOMEOMORPHIC_CONVEX_COMPACT = prove
 (`!s:real^N->bool t u:real^M->bool.
        s homeomorphic u /\ ~(s = {}) /\ s SUBSET t /\ convex u /\ compact u
        ==> s retract_of t`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`u:real^M->bool`; `t:real^N->bool`; `s:real^N->bool`]
        AR_IMP_ABSOLUTE_RETRACT) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[CONVEX_IMP_AR; HOMEOMORPHIC_EMPTY; HOMEOMORPHIC_SYM;
                CLOSED_SUBSET; COMPACT_IMP_CLOSED; HOMEOMORPHIC_COMPACTNESS]);;

let ABSOLUTE_RETRACT_PATH_IMAGE_ARC = prove
 (`!g s:real^N->bool.
        arc g /\ path_image g SUBSET s ==> (path_image g) retract_of s`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPECL [`path_image g:real^N->bool`; `s:real^N->bool`;
            `interval[vec 0:real^1,vec 1:real^1]`]
        ABSOLUTE_RETRACT_HOMEOMORPHIC_CONVEX_COMPACT) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[PATH_IMAGE_NONEMPTY] THEN
  REWRITE_TAC[COMPACT_INTERVAL; CONVEX_INTERVAL] THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN
  EXISTS_TAC `g:real^1->real^N` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[arc; path; path_image]) THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL; path_image]);;

let AR_ARC_IMAGE = prove
 (`!g:real^1->real^N. arc g ==> AR(path_image g)`,
  MESON_TAC[RETRACT_OF_UNIV; SUBSET_UNIV; ABSOLUTE_RETRACT_PATH_IMAGE_ARC]);;

let RELATIVE_FRONTIER_DEFORMATION_RETRACT_OF_PUNCTURED_CONVEX = prove
 (`!s t a:real^N.
        convex s /\ convex t /\ bounded s /\ a IN relative_interior s /\
        relative_frontier s SUBSET t /\ t SUBSET affine hull s
        ==> ?r. homotopic_with (\x. T)
                 (subtopology euclidean (t DELETE a),
                  subtopology euclidean (t DELETE a)) (\x. x) r /\
                retraction (t DELETE a,relative_frontier s) r /\
                (!x. ?c. &0 < c /\ r(x) - a = c % (x - a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`]
    RAY_TO_RELATIVE_FRONTIER) THEN
  ASM_SIMP_TAC[relative_frontier; VECTOR_ADD_LID] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[REAL_LT_01]
   `(!x. P x ==> ?d. &0 < d /\ R d x)
    ==> !x. ?d. &0 < d /\ (P x ==> R d x)`)) THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  REWRITE_TAC[TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; retraction] THEN
  X_GEN_TAC `dd:real^N->real` THEN STRIP_TAC THEN
  EXISTS_TAC `\x:real^N. a + dd(x - a) % (x - a)` THEN
  SUBGOAL_THEN
   `((\x:real^N. a + dd x % x) o (\x. x - a)) continuous_on t DELETE a`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `affine hull s DELETE (a:real^N)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    SIMP_TAC[VECTOR_ARITH `x - a:real^N = y - a <=> x = y`; VECTOR_SUB_REFL;
             SET_RULE `(!x y. f x = f y <=> x = y)
                       ==> IMAGE f (s DELETE a) = IMAGE f s DELETE f a`] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPACT_SURFACE_PROJECTION THEN
    EXISTS_TAC `relative_frontier (IMAGE (\x:real^N. x - a) s)` THEN
    ASM_SIMP_TAC[COMPACT_RELATIVE_FRONTIER_BOUNDED;
                 VECTOR_ARITH `x - a:real^N = --a + x`;
                 RELATIVE_FRONTIER_TRANSLATION; COMPACT_TRANSLATION_EQ] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `s SUBSET t /\ ~(a IN IMAGE f s)
        ==> IMAGE f s SUBSET IMAGE f t DELETE a`) THEN
      REWRITE_TAC[IN_IMAGE; UNWIND_THM2;
                  VECTOR_ARITH `vec 0:real^N = --a + x <=> x = a`] THEN
      ASM_REWRITE_TAC[relative_frontier; IN_DIFF] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s DIFF u SUBSET t`) THEN
      REWRITE_TAC[CLOSURE_SUBSET_AFFINE_HULL];
      MATCH_MP_TAC SUBSPACE_IMP_CONIC THEN
      MATCH_MP_TAC AFFINE_IMP_SUBSPACE THEN
      SIMP_TAC[AFFINE_TRANSLATION; AFFINE_AFFINE_HULL; IN_IMAGE] THEN
      REWRITE_TAC[UNWIND_THM2;
                  VECTOR_ARITH `vec 0:real^N = --a + x <=> x = a`] THEN
      ASM_MESON_TAC[SUBSET; HULL_SUBSET; RELATIVE_INTERIOR_SUBSET];
      ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      REWRITE_TAC[IN_DELETE; IMP_CONJ; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[VECTOR_ARITH `--a + x:real^N = vec 0 <=> x = a`] THEN
      MAP_EVERY X_GEN_TAC [`k:real`; `x:real^N`] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[IN_IMAGE; UNWIND_THM2; relative_frontier; VECTOR_ARITH
       `y:real^N = --a + x <=> x = a + y`] THEN
      EQ_TAC THENL
       [STRIP_TAC;
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[VECTOR_ARITH `a + --a + x:real^N = x`;
                        VECTOR_ARITH `--a + x:real^N = vec 0 <=> x = a`]] THEN
      MATCH_MP_TAC(REAL_ARITH `~(a < b) /\ ~(b < a) ==> a = b`) THEN
      CONJ_TAC THEN DISCH_TAC THENL
       [ALL_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `x IN c DIFF i ==> x IN i ==> F`)) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; VECTOR_ARITH `a + --a + x:real^N = x`;
                     VECTOR_ARITH `--a + x:real^N = vec 0 <=> x = a`]] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`; `a + k % (--a + x):real^N`]
        IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_DIFF]) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SEGMENT; NOT_FORALL_THM] THEN
      EXISTS_TAC `a + dd(--a + x) % (--a + x):real^N` THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `a:real^N = a + k % (--a + x) <=>
                                    k % (x - a) = vec 0`] THEN
      ASM_SIMP_TAC[VECTOR_SUB_EQ; VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
       [EXISTS_TAC `(dd:real^N->real) (--a + x) / k` THEN
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
        REWRITE_TAC[VECTOR_ARITH `a + b:real^N = (&1 - u) % a + u % c <=>
                                  b = u % (c - a)`] THEN
        ASM_SIMP_TAC[VECTOR_MUL_ASSOC; VECTOR_ADD_SUB; REAL_DIV_RMUL;
                     REAL_LT_IMP_NZ] THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(SET_RULE
         `a IN closure s /\ ~(a IN relative_interior s)
          ==> ~(a IN relative_interior s)`)] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `a + --a + x:real^N = x`;
                      VECTOR_ARITH `--a + x:real^N = vec 0 <=> x = a`]];
    REWRITE_TAC[o_DEF] THEN STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    REWRITE_TAC[segment; SUBSET; FORALL_IN_GSPEC; IN_DELETE] THEN
    REPEAT(GEN_TAC THEN STRIP_TAC) THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
      ASM_REWRITE_TAC[REAL_ARITH `&1 - u + u = &1`; REAL_SUB_LE] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      REWRITE_TAC[relative_frontier] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `a + x - a:real^N = x`; VECTOR_SUB_EQ] THEN
      ASM_MESON_TAC[HULL_SUBSET; RELATIVE_INTERIOR_SUBSET; SUBSET];
      ASM_SIMP_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; VECTOR_ARITH
       `(&1 - u) % x + u % (a + d % (x - a)):real^N = a <=>
        (&1 - u + u * d) % (x - a) = vec 0`] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= x /\ &0 <= u /\ u <= &1 /\ ~(x = &0 /\ u = &1)
        ==> ~(&1 - u + x = &0)`) THEN
      ASM_SIMP_TAC[REAL_ENTIRE; REAL_ARITH
       `(u = &0 \/ d = &0) /\ u = &1 <=> d = &0 /\ u = &1`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE;
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0 /\ u = &1)`)] THEN
      ASM_REWRITE_TAC[]];
    RULE_ASSUM_TAC(REWRITE_RULE[relative_frontier]) THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(SET_RULE
     `!s t. s SUBSET t /\ IMAGE f (t DELETE a) SUBSET u
            ==> IMAGE f (s DELETE a) SUBSET u`) THEN
    EXISTS_TAC `affine hull s:real^N->bool` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_SUB_EQ; VECTOR_ARITH `a + x - a:real^N = x`];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x:real^N = a` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `dd(x - a:real^N) = &1`
     (fun th -> REWRITE_TAC[th] THEN CONV_TAC VECTOR_ARITH) THEN
    MATCH_MP_TAC(REAL_ARITH `~(d < &1) /\ ~(&1 < d) ==> d = &1`) THEN
    CONJ_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`]
        IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT)
    THENL
     [DISCH_THEN(MP_TAC o SPEC `x:real^N`);
      DISCH_THEN(MP_TAC o SPEC `a + dd(x - a) % (x - a):real^N`)] THEN
    ASM_REWRITE_TAC[SUBSET; NOT_IMP; IN_SEGMENT; NOT_FORALL_THM] THENL
     [EXISTS_TAC `a + dd(x - a) % (x - a):real^N` THEN
      ASM_REWRITE_TAC[VECTOR_SUB_EQ; VECTOR_MUL_EQ_0; REAL_SUB_0; VECTOR_ARITH
       `a + d % (x - a):real^N = (&1 - u) % a + u % x <=>
        (u - d) % (x - a) = vec 0`] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `(dd:real^N->real)(x - a)` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(SET_RULE
         `x IN closure s DIFF relative_interior s
          ==> ~(x IN relative_interior s)`)] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[VECTOR_SUB_EQ; VECTOR_ARITH `a + x - a:real^N = x`] THEN
      ASM_MESON_TAC[CLOSURE_SUBSET_AFFINE_HULL; SUBSET];
      CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `x IN closure s DIFF relative_interior s
          ==> x IN closure s`) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC[VECTOR_SUB_EQ; VECTOR_ARITH `a + x - a:real^N = x`] THEN
        ASM_MESON_TAC[CLOSURE_SUBSET_AFFINE_HULL; SUBSET];
        EXISTS_TAC `x:real^N` THEN
        ASM_SIMP_TAC[VECTOR_SUB_EQ; VECTOR_MUL_EQ_0;
                     VECTOR_ARITH `a = a + d <=> d:real^N = vec 0`;
           VECTOR_ARITH `x:real^N = (&1 - u) % a + u % (a + d % (x - a)) <=>
                         (u * d - &1) % (x - a) = vec 0`] THEN
        MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
        EXISTS_TAC `inv((dd:real^N->real)(x - a))` THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_SUB_REFL; REAL_LT_INV_EQ] THEN
        ASM_SIMP_TAC[REAL_INV_LT_1] THEN ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[VECTOR_ADD_SUB] THEN
    EXISTS_TAC `\x. (dd:real^N->real)(x - a)` THEN
    ASM_REWRITE_TAC[]]);;

let RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL = prove
 (`!s a:real^N.
        convex s /\ bounded s /\ a IN relative_interior s
        ==> relative_frontier s retract_of (affine hull s DELETE a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `affine hull s:real^N->bool`; `a:real^N`]
      RELATIVE_FRONTIER_DEFORMATION_RETRACT_OF_PUNCTURED_CONVEX) THEN
  ASM_SIMP_TAC[AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL; SUBSET_REFL] THEN
  REWRITE_TAC[retract_of] THEN ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  REWRITE_TAC[relative_frontier] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s DIFF t SUBSET u`) THEN
  REWRITE_TAC[CLOSURE_SUBSET_AFFINE_HULL]);;

let RELATIVE_BOUNDARY_RETRACT_OF_PUNCTURED_AFFINE_HULL = prove
 (`!s a:real^N.
        convex s /\ compact s /\ a IN relative_interior s
        ==> (s DIFF relative_interior s) retract_of
            (affine hull s DELETE a)`,
  MP_TAC RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[relative_frontier; COMPACT_IMP_BOUNDED; COMPACT_IMP_CLOSED;
               CLOSURE_CLOSED]);;

let PATH_CONNECTED_SPHERE_GEN = prove
 (`!s:real^N->bool.
        convex s /\ bounded s /\ ~(aff_dim s = &1)
        ==> path_connected(relative_frontier s)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `relative_interior s:real^N->bool = {}` THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; PATH_CONNECTED_EMPTY;
                  RELATIVE_FRONTIER_EMPTY];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC RETRACT_OF_PATH_CONNECTED THEN
    EXISTS_TAC `affine hull s DELETE (a:real^N)` THEN
    ASM_SIMP_TAC[PATH_CONNECTED_PUNCTURED_CONVEX; AFFINE_AFFINE_HULL;
                 AFFINE_IMP_CONVEX; AFF_DIM_AFFINE_HULL;
                 RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL]]);;

let CONNECTED_SPHERE_GEN = prove
 (`!s:real^N->bool.
        convex s /\ bounded s /\ ~(aff_dim s = &1)
        ==> connected(relative_frontier s)`,
  SIMP_TAC[PATH_CONNECTED_SPHERE_GEN; PATH_CONNECTED_IMP_CONNECTED]);;

let ENR_RELATIVE_FRONTIER_CONVEX = prove
 (`!s:real^N->bool. bounded s /\ convex s ==> ENR(relative_frontier s)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[ENR; RELATIVE_FRONTIER_EMPTY] THENL
   [ASM_MESON_TAC[RETRACT_OF_REFL; OPEN_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior s:real^N->bool = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  EXISTS_TAC `{x | x IN (:real^N) /\
                   closest_point (affine hull s) x IN
                   ((:real^N) DELETE a)}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `(:real^N)` THEN
    SIMP_TAC[OPEN_IN_DELETE; OPEN_IN_REFL; SUBSET_UNIV; ETA_AX];
    MATCH_MP_TAC RETRACT_OF_TRANS THEN
    EXISTS_TAC `(affine hull s) DELETE (a:real^N)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[retract_of; retraction] THEN
      EXISTS_TAC `closest_point (affine hull s:real^N->bool)` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE] THEN
      ASM_SIMP_TAC[IN_ELIM_THM; IN_UNIV; CLOSEST_POINT_SELF;
                   CLOSEST_POINT_IN_SET; AFFINE_HULL_EQ_EMPTY;
                   CLOSED_AFFINE_HULL]]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CLOSEST_POINT THEN
  ASM_SIMP_TAC[AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL;
               CLOSED_AFFINE_HULL; AFFINE_HULL_EQ_EMPTY]);;

let ANR_RELATIVE_FRONTIER_CONVEX = prove
 (`!s:real^N->bool. bounded s /\ convex s ==> ANR(relative_frontier s)`,
  SIMP_TAC[ENR_IMP_ANR; ENR_RELATIVE_FRONTIER_CONVEX]);;

let FRONTIER_RETRACT_OF_PUNCTURED_UNIVERSE = prove
 (`!s a. convex s /\ bounded s /\ a IN interior s
         ==> (frontier s) retract_of ((:real^N) DELETE a)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP (SET_RULE
   `a IN s ==> ~(s = {})`)) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`]
        RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR;
               RELATIVE_INTERIOR_NONEMPTY_INTERIOR;
               AFFINE_HULL_NONEMPTY_INTERIOR]);;

let SPHERE_RETRACT_OF_PUNCTURED_UNIVERSE_GEN = prove
 (`!a r b:real^N.
      b IN ball(a,r) ==> sphere(a,r) retract_of ((:real^N) DELETE b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FRONTIER_CBALL] THEN
  MATCH_MP_TAC FRONTIER_RETRACT_OF_PUNCTURED_UNIVERSE THEN
  ASM_REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; INTERIOR_CBALL]);;

let SPHERE_RETRACT_OF_PUNCTURED_UNIVERSE = prove
 (`!a r. &0 < r ==> sphere(a,r) retract_of ((:real^N) DELETE a)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SPHERE_RETRACT_OF_PUNCTURED_UNIVERSE_GEN THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL]);;

let ENR_SPHERE = prove
 (`!a:real^N r. ENR(sphere(a,r))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 < r` THENL
   [REWRITE_TAC[ENR] THEN EXISTS_TAC `(:real^N) DELETE a` THEN
    ASM_SIMP_TAC[SPHERE_RETRACT_OF_PUNCTURED_UNIVERSE;
                 OPEN_DELETE; OPEN_UNIV];
    ASM_MESON_TAC[FINITE_IMP_ENR; REAL_NOT_LE; FINITE_SPHERE]]);;

let ANR_SPHERE = prove
 (`!a:real^N r. ANR(sphere(a,r))`,
  SIMP_TAC[ENR_SPHERE; ENR_IMP_ANR]);;

let LOCALLY_PATH_CONNECTED_SPHERE_GEN = prove
 (`!s:real^N->bool.
       bounded s /\ convex s ==> locally path_connected (relative_frontier s)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `relative_interior(s:real^N->bool) = {}` THENL
   [UNDISCH_TAC `relative_interior(s:real^N->bool) = {}` THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN
    REWRITE_TAC[LOCALLY_EMPTY; RELATIVE_FRONTIER_EMPTY];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    MATCH_MP_TAC RETRACT_OF_LOCALLY_PATH_CONNECTED THEN
    EXISTS_TAC `(affine hull s) DELETE (a:real^N)` THEN
    ASM_SIMP_TAC[RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL] THEN
    MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
    EXISTS_TAC `affine hull s:real^N->bool` THEN
    SIMP_TAC[OPEN_IN_DELETE; OPEN_IN_REFL] THEN
    SIMP_TAC[CONVEX_IMP_LOCALLY_PATH_CONNECTED; AFFINE_IMP_CONVEX;
             AFFINE_AFFINE_HULL]]);;

let LOCALLY_CONNECTED_SPHERE_GEN = prove
 (`!s:real^N->bool.
       bounded s /\ convex s ==> locally connected (relative_frontier s)`,
  SIMP_TAC[LOCALLY_PATH_CONNECTED_SPHERE_GEN;
           LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED]);;

let LOCALLY_PATH_CONNECTED_SPHERE = prove
 (`!a:real^N r. locally path_connected (sphere(a,r))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `cball(a:real^N,r)` LOCALLY_PATH_CONNECTED_SPHERE_GEN) THEN
  MP_TAC(ISPECL [`a:real^N`; `r:real`] RELATIVE_FRONTIER_CBALL) THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[SPHERE_SING; LOCALLY_SING; PATH_CONNECTED_SING;
               BOUNDED_CBALL; CONVEX_CBALL]);;

let LOCALLY_CONNECTED_SPHERE = prove
 (`!a:real^N r. locally connected(sphere(a,r))`,
  SIMP_TAC[LOCALLY_PATH_CONNECTED_SPHERE;
           LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED]);;

let ABSOLUTE_RETRACTION_CONVEX_CLOSED_RELATIVE = prove
 (`!s:real^N->bool t.
        convex s /\ closed s /\ ~(s = {}) /\ s SUBSET t
        ==> ?r. retraction (t,s) r /\
                !x. x IN (affine hull s) DIFF (relative_interior s)
                    ==> r(x) IN relative_frontier s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[retraction] THEN
  EXISTS_TAC `closest_point(s:real^N->bool)` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_CLOSEST_POINT; CLOSEST_POINT_SELF] THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; CLOSEST_POINT_IN_SET] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSEST_POINT_IN_RELATIVE_FRONTIER THEN
  ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]);;

let ABSOLUTE_RETRACTION_CONVEX_CLOSED = prove
 (`!s:real^N->bool t.
        convex s /\ closed s /\ ~(s = {}) /\ s SUBSET t
        ==> ?r. retraction (t,s) r /\
                (!x. ~(x IN s) ==> r(x) IN frontier s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[retraction] THEN
  EXISTS_TAC `closest_point(s:real^N->bool)` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_CLOSEST_POINT; CLOSEST_POINT_SELF] THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; CLOSEST_POINT_IN_SET] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSEST_POINT_IN_FRONTIER THEN
  ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET]);;

let ABSOLUTE_RETRACT_CONVEX_CLOSED = prove
 (`!s:real^N->bool t.
        convex s /\ closed s /\ ~(s = {}) /\ s SUBSET t
        ==> s retract_of t`,
  REWRITE_TAC[retract_of] THEN MESON_TAC[ABSOLUTE_RETRACTION_CONVEX_CLOSED]);;

let ABSOLUTE_RETRACT_CONVEX = prove
 (`!s u:real^N->bool.
        convex s /\ ~(s = {}) /\ closed_in (subtopology euclidean u) s
        ==> s retract_of u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[retract_of; retraction] THEN
  MP_TAC(ISPECL [`\x:real^N. x`; `s:real^N->bool`; `u:real^N->bool`;
                 `s:real^N->bool`] DUGUNDJI) THEN
  ASM_MESON_TAC[CONTINUOUS_ON_ID; IMAGE_ID; SUBSET_REFL;
                CLOSED_IN_IMP_SUBSET]);;

let ENR_PATH_IMAGE_SIMPLE_PATH = prove
 (`!g:real^1->real^N. simple_path g ==> ENR(path_image g)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `pathfinish g:real^N = pathstart g` THENL
   [MP_TAC(ISPECL [`g:real^1->real^N`; `vec 0:real^2`; `&1`]
        HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE) THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP HOMEOMORPHIC_ENRNESS) THEN
    REWRITE_TAC[ENR_SPHERE];
    REWRITE_TAC[ENR] THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC ABSOLUTE_RETRACT_PATH_IMAGE_ARC THEN
    ASM_REWRITE_TAC[ARC_SIMPLE_PATH; SUBSET_UNIV]]);;

let ANR_PATH_IMAGE_SIMPLE_PATH = prove
 (`!g:real^1->real^N. simple_path g ==> ANR(path_image g)`,
  SIMP_TAC[ENR_PATH_IMAGE_SIMPLE_PATH; ENR_IMP_ANR]);;

(* ------------------------------------------------------------------------- *)
(* Borsuk homotopy extension thorem. It's only this late so we can use the   *)
(* concept of retraction, saying that the domain sets or range set are ANRs. *)
(* ------------------------------------------------------------------------- *)

let BORSUK_HOMOTOPY_EXTENSION_HOMOTOPIC = prove
 (`!f:real^M->real^N g s t u.
        closed_in (subtopology euclidean t) s /\
        (ANR s /\ ANR t \/ ANR u) /\
        f continuous_on t /\ IMAGE f t SUBSET u /\
        homotopic_with (\x. T)
          (subtopology euclidean s,subtopology euclidean u) f g
        ==> ?g'. homotopic_with (\x. T)
                  (subtopology euclidean t,subtopology euclidean u) f g' /\
                 g' continuous_on t /\ IMAGE g' t SUBSET u /\
                 !x. x IN s ==> g'(x) = g(x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMOTOPIC_WITH_EUCLIDEAN]) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N`
    STRIP_ASSUME_TAC) THEN
  MAP_EVERY ABBREV_TAC
   [`h' = \z. if sndcart z IN s then (h:real^(1,M)finite_sum->real^N) z
              else f(sndcart z)`;
    `B:real^(1,M)finite_sum->bool =
       {vec 0} PCROSS t UNION interval[vec 0,vec 1] PCROSS s`] THEN
  SUBGOAL_THEN
   `closed_in (subtopology euclidean (interval[vec 0:real^1,vec 1] PCROSS t))
              ({vec 0} PCROSS (t:real^M->bool)) /\
    closed_in (subtopology euclidean (interval[vec 0:real^1,vec 1] PCROSS t))
              (interval[vec 0,vec 1] PCROSS s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_PCROSS THEN
    ASM_REWRITE_TAC[CLOSED_IN_SING; CLOSED_IN_REFL; ENDS_IN_UNIT_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h':real^(1,M)finite_sum->real^N) continuous_on B`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h'"; "B"] THEN ONCE_REWRITE_TAC[UNION_COMM] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
        (ONCE_REWRITE_RULE[IMP_CONJ] CLOSED_IN_SUBSET_TRANS)) THEN
      REWRITE_TAC[SUBSET_UNION; UNION_SUBSET; SUBSET_PCROSS] THEN
      ASM_REWRITE_TAC[SING_SUBSET; SUBSET_REFL; ENDS_IN_UNIT_INTERVAL];
     ASM_SIMP_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SING;
                   SNDCART_PASTECART; TAUT `(p /\ q) /\ ~q <=> F`] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC[LINEAR_SNDCART; LINEAR_CONTINUOUS_ON;
                   IMAGE_SNDCART_PCROSS; NOT_INSERT_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h':real^(1,M)finite_sum->real^N) B SUBSET u`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h'"; "B"] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART;
           SNDCART_PASTECART; PASTECART_IN_PCROSS; IN_UNION; IN_SING] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[COND_ID] THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o SIMP_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?V k:real^(1,M)finite_sum->real^N.
        B SUBSET V /\
        open_in (subtopology euclidean (interval [vec 0,vec 1] PCROSS t)) V /\
        k continuous_on V /\
        IMAGE k V SUBSET u /\
        (!x. x IN B ==> k x = h' x)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [SUBGOAL_THEN `ANR(B:real^(1,M)finite_sum->bool)` MP_TAC THENL
       [EXPAND_TAC "B" THEN MATCH_MP_TAC ANR_CLOSED_UNION_LOCAL THEN
        EXISTS_TAC
         `{vec 0:real^1} PCROSS (t:real^M->bool) UNION
          interval[vec 0,vec 1] PCROSS s` THEN
        ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
         [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
           (ONCE_REWRITE_RULE[IMP_CONJ] CLOSED_IN_SUBSET_TRANS)) THEN
          REWRITE_TAC[SUBSET_UNION; UNION_SUBSET; SUBSET_PCROSS] THEN
          ASM_REWRITE_TAC[SING_SUBSET; SUBSET_REFL; ENDS_IN_UNIT_INTERVAL];
          ASM_SIMP_TAC[INTER_PCROSS; SET_RULE `s SUBSET t ==> t INTER s = s`;
                       ENDS_IN_UNIT_INTERVAL;
                       SET_RULE `a IN s ==> {a} INTER s = {a}`] THEN
          REPEAT CONJ_TAC THEN MATCH_MP_TAC ANR_PCROSS THEN
          ASM_REWRITE_TAC[ANR_INTERVAL; ANR_SING]];
        DISCH_THEN(MP_TAC o SPEC
          `interval[vec 0:real^1,vec 1] PCROSS (t:real^M->bool)` o
         MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ]
           ANR_IMP_NEIGHBOURHOOD_RETRACT)) THEN
        ANTS_TAC THENL
         [EXPAND_TAC "B" THEN MATCH_MP_TAC CLOSED_IN_UNION THEN
          CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_PCROSS THEN
          ASM_REWRITE_TAC[CLOSED_IN_REFL; CLOSED_IN_SING;
                          ENDS_IN_UNIT_INTERVAL];
          MATCH_MP_TAC MONO_EXISTS] THEN
        X_GEN_TAC `V:real^(1,M)finite_sum->bool` THEN STRIP_TAC THEN
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
        FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
        REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC `r:real^(1,M)finite_sum->real^(1,M)finite_sum` THEN
        STRIP_TAC THEN
        EXISTS_TAC `(h':real^(1,M)finite_sum->real^N) o
                    (r:real^(1,M)finite_sum->real^(1,M)finite_sum)` THEN
        ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN
        CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]];
      MATCH_MP_TAC ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR THEN
      ASM_SIMP_TAC[] THEN EXPAND_TAC "B" THEN
      ASM_SIMP_TAC[CLOSED_IN_UNION]];
    ABBREV_TAC `s' = {x | ?u. u IN interval[vec 0,vec 1] /\
                              pastecart (u:real^1) (x:real^M) IN
                              interval [vec 0,vec 1] PCROSS t DIFF V}` THEN
    SUBGOAL_THEN `closed_in (subtopology euclidean t) (s':real^M->bool)`
    ASSUME_TAC THENL
     [EXPAND_TAC "s'" THEN MATCH_MP_TAC CLOSED_IN_COMPACT_PROJECTION THEN
      REWRITE_TAC[COMPACT_INTERVAL] THEN MATCH_MP_TAC CLOSED_IN_DIFF THEN
      ASM_REWRITE_TAC[CLOSED_IN_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `s':real^M->bool`; `t:real^M->bool`;
                   `vec 1:real^1`; `vec 0:real^1`] URYSOHN_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [EXPAND_TAC "s'" THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
      REWRITE_TAC[NOT_IN_EMPTY; IN_DIFF; PASTECART_IN_PCROSS] THEN
      X_GEN_TAC `x:real^M` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^1` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      EXPAND_TAC "B" THEN REWRITE_TAC[IN_UNION; PASTECART_IN_PCROSS] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
    REWRITE_TAC[SEGMENT_1; DROP_VEC; REAL_POS] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^M->real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC
     `(\x. (k:real^(1,M)finite_sum->real^N) (pastecart (a x) x))` THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC[HOMOTOPIC_WITH] THEN
      EXISTS_TAC `(k:real^(1,M)finite_sum->real^N) o
          (\z. pastecart (drop(fstcart z) % a(sndcart z)) (sndcart z))` THEN
      REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
          SIMP_TAC[LINEAR_SNDCART; LINEAR_CONTINUOUS_ON] THEN
          MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
          SIMP_TAC[o_DEF; LIFT_DROP; LINEAR_FSTCART; LINEAR_CONTINUOUS_ON;
                   ETA_AX] THEN
          GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
          SIMP_TAC[LINEAR_SNDCART; LINEAR_CONTINUOUS_ON] THEN
          ASM_SIMP_TAC[IMAGE_SNDCART_PCROSS; UNIT_INTERVAL_NONEMPTY];
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET))];
        REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (SET_RULE `IMAGE k t SUBSET u
                    ==> s SUBSET t ==> IMAGE k s SUBSET u`));
        X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
        SUBGOAL_THEN `pastecart (vec 0:real^1) (x:real^M) IN B` MP_TAC THENL
         [EXPAND_TAC "B" THEN
          ASM_REWRITE_TAC[IN_UNION; PASTECART_IN_PCROSS; IN_SING];
          DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
           `(h':real^(1,M)finite_sum->real^N) (pastecart (vec 0) x)` THEN
          CONJ_TAC THENL [ASM_MESON_TAC[]; EXPAND_TAC "h'"] THEN
          ASM_REWRITE_TAC[SNDCART_PASTECART; COND_ID]]] THEN
      (REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
       MAP_EVERY X_GEN_TAC [`p:real^1`; `x:real^M`] THEN STRIP_TAC THEN
       REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
       ASM_CASES_TAC `(x:real^M) IN s'` THENL
        [ASM_SIMP_TAC[VECTOR_MUL_RZERO] THEN
         FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
         EXPAND_TAC "B" THEN REWRITE_TAC[IN_UNION; PASTECART_IN_PCROSS] THEN
         ASM_REWRITE_TAC[IN_SING];
         UNDISCH_TAC `~((x:real^M) IN s')` THEN
         EXPAND_TAC "s'" THEN
         REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM]  THEN
         DISCH_THEN(MP_TAC o SPEC `drop p % (a:real^M->real^1) x`) THEN
         REWRITE_TAC[PASTECART_IN_PCROSS; IN_DIFF] THEN
         ASM_REWRITE_TAC[CONJ_ASSOC] THEN
         MATCH_MP_TAC(TAUT `p ==> ~(p /\ ~q) ==> q`) THEN
         REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC] THEN
         RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
         ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_LMUL; REAL_ARITH
          `p * a <= p * &1 /\ p <= &1 ==> p * a <= &1`]]);
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC;
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]);
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `(h':real^(1,M)finite_sum->real^N) (pastecart (vec 1) x)` THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC; EXPAND_TAC "h'"] THEN
      ASM_REWRITE_TAC[SNDCART_PASTECART] THEN
      EXPAND_TAC "B" THEN REWRITE_TAC[IN_UNION; PASTECART_IN_PCROSS] THEN
      ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]] THEN
    (ASM_CASES_TAC `(x:real^M) IN s'` THEN ASM_SIMP_TAC[] THENL
      [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
       EXPAND_TAC "B" THEN REWRITE_TAC[IN_UNION; PASTECART_IN_PCROSS] THEN
       ASM SET_TAC[];
       UNDISCH_TAC `~((x:real^M) IN s')` THEN EXPAND_TAC "s'" THEN
       REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM]  THEN
       DISCH_THEN(MP_TAC o SPEC `(a:real^M->real^1) x`) THEN
       ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_DIFF] THEN ASM SET_TAC[]])]);;

let BORSUK_HOMOTOPY_EXTENSION = prove
 (`!f:real^M->real^N g s t u.
        closed_in (subtopology euclidean t) s /\
        (ANR s /\ ANR t \/ ANR u) /\
        f continuous_on t /\ IMAGE f t SUBSET u /\
        homotopic_with (\x. T)
         (subtopology euclidean s,subtopology euclidean u) f g
        ==> ?g'. g' continuous_on t /\ IMAGE g' t SUBSET u /\
                 !x. x IN s ==> g'(x) = g(x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP BORSUK_HOMOTOPY_EXTENSION_HOMOTOPIC) THEN
  MESON_TAC[]);;

let NULLHOMOTOPIC_INTO_ANR_EXTENSION = prove
 (`!f:real^M->real^N s t.
      closed s /\ f continuous_on s /\ ~(s = {}) /\ IMAGE f s SUBSET t /\ ANR t
      ==> ((?c. homotopic_with (\x. T)
                 (subtopology euclidean s,subtopology euclidean t)
                 f (\x. c)) <=>
           (?g. g continuous_on (:real^M) /\
                IMAGE g (:real^M) SUBSET t /\
                !x. x IN s ==> g x = f x))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC BORSUK_HOMOTOPY_EXTENSION THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
    EXISTS_TAC `(\x. c):real^M->real^N` THEN
    ASM_REWRITE_TAC[CLOSED_UNIV; CONTINUOUS_ON_CONST] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
    ASM SET_TAC[];
    MP_TAC(ISPECL [`g:real^M->real^N`; `(:real^M)`; `t:real^N->bool`]
         NULLHOMOTOPIC_FROM_CONTRACTIBLE) THEN
    ASM_REWRITE_TAC[CONTRACTIBLE_UNIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N` THEN
    DISCH_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
    MAP_EVERY EXISTS_TAC [`g:real^M->real^N`; `(\x. c):real^M->real^N`] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_WITH_SUBSET_LEFT THEN
    EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]]);;

let NULLHOMOTOPIC_INTO_RELATIVE_FRONTIER_EXTENSION = prove
 (`!f:real^M->real^N s t.
        closed s /\ f continuous_on s /\ ~(s = {}) /\
        IMAGE f s SUBSET relative_frontier t /\ convex t /\ bounded t
        ==> ((?c. homotopic_with (\x. T)
                   (subtopology euclidean s,
                    subtopology euclidean  (relative_frontier t)) f (\x. c)) <=>
             (?g. g continuous_on (:real^M) /\
                  IMAGE g (:real^M) SUBSET relative_frontier t /\
                  !x. x IN s ==> g x = f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NULLHOMOTOPIC_INTO_ANR_EXTENSION THEN
  MP_TAC(ISPEC `t:real^N->bool` ANR_RELATIVE_FRONTIER_CONVEX) THEN
  ASM_REWRITE_TAC[]);;

let NULLHOMOTOPIC_INTO_SPHERE_EXTENSION = prove
 (`!f:real^M->real^N s a r.
     closed s /\ f continuous_on s /\ ~(s = {}) /\ IMAGE f s SUBSET sphere(a,r)
     ==> ((?c. homotopic_with (\x. T)
                (subtopology euclidean s,
                 subtopology euclidean (sphere(a,r))) f (\x. c)) <=>
          (?g. g continuous_on (:real^M) /\
               IMAGE g (:real^M) SUBSET sphere(a,r) /\
               !x. x IN s ==> g x = f x))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `r:real`] RELATIVE_FRONTIER_CBALL) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[SPHERE_SING] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `p /\ q ==> (p <=> q)`) THEN CONJ_TAC THENL
     [EXISTS_TAC `a:real^N` THEN SIMP_TAC[HOMOTOPIC_WITH; PCROSS] THEN
      EXISTS_TAC `\y:real^(1,M)finite_sum. (a:real^N)`;
      EXISTS_TAC `(\x. a):real^M->real^N`] THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN ASM SET_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM) THEN STRIP_TAC THEN
    MATCH_MP_TAC NULLHOMOTOPIC_INTO_RELATIVE_FRONTIER_EXTENSION THEN
    ASM_REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL]]);;

let ABSOLUTE_RETRACT_CONTRACTIBLE_ANR = prove
 (`!s u:real^N->bool.
      closed_in (subtopology euclidean u) s /\
      contractible s /\ ~(s = {}) /\ ANR s
      ==> s retract_of u`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC AR_IMP_RETRACT THEN
  ASM_SIMP_TAC[AR_ANR]);;

(* ------------------------------------------------------------------------- *)
(* More homotopy extension results and relations to components.              *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_ON_COMPONENTS = prove
 (`!s t f g:real^M->real^N.
        locally connected s /\
        (!c. c IN components s
             ==> homotopic_with (\x. T)
                   (subtopology euclidean c,subtopology euclidean t) f g)
        ==> homotopic_with (\x. T)
             (subtopology euclidean s,subtopology euclidean t) f g`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC
   (RATOR_CONV o LAND_CONV o LAND_CONV o RAND_CONV) [UNIONS_COMPONENTS] THEN
  MATCH_MP_TAC HOMOTOPIC_ON_CLOPEN_UNIONS THEN
  X_GEN_TAC `c:real^M->bool` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[GSYM UNIONS_COMPONENTS] THEN
  ASM_MESON_TAC[CLOSED_IN_COMPONENT; OPEN_IN_COMPONENTS_LOCALLY_CONNECTED]);;

let INESSENTIAL_ON_COMPONENTS = prove
 (`!f:real^M->real^N s t.
        locally connected s /\ path_connected t /\
        (!c. c IN components s
             ==> ?a. homotopic_with (\x. T)
                       (subtopology euclidean c,subtopology euclidean t)
                       f (\x. a))
        ==> ?a. homotopic_with (\x. T)
                  (subtopology euclidean s,subtopology euclidean t)
                  f (\x. a)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `components(s:real^M->bool) = {}` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[COMPONENTS_EQ_EMPTY]) THEN
    ASM_REWRITE_TAC[HOMOTOPIC_ON_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^N. a IN t` MP_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
     DISCH_THEN(X_CHOOSE_TAC `c:real^M->bool`) THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `c:real^M->bool`) THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
     GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
     FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN SET_TAC[];
     MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_ON_COMPONENTS THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:real^M->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real^M->bool`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `b:real^N` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_TRANS) THEN
  REWRITE_TAC[HOMOTOPIC_CONSTANT_MAPS] THEN DISJ2_TAC THEN FIRST_X_ASSUM
   (MATCH_MP_TAC o REWRITE_RULE[PATH_CONNECTED_IFF_PATH_COMPONENT]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN ASM SET_TAC[]);;

let HOMOTOPIC_NEIGHBOURHOOD_EXTENSION = prove
 (`!f g:real^M->real^N s t u.
        f continuous_on s /\ IMAGE f s SUBSET u /\
        g continuous_on s /\ IMAGE g s SUBSET u /\
        closed_in (subtopology euclidean s) t /\ ANR u /\
        homotopic_with (\x. T)
         (subtopology euclidean t,subtopology euclidean u) f g
        ==> ?v. t SUBSET v /\
                open_in (subtopology euclidean s) v /\
                homotopic_with (\x. T)
                 (subtopology euclidean v,subtopology euclidean u) f g`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMOTOPIC_WITH_EUCLIDEAN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N`
        STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `h' = \z. if fstcart z IN {vec 0} then f(sndcart z)
             else if fstcart z IN {vec 1} then g(sndcart z)
             else (h:real^(1,M)finite_sum->real^N) z` THEN
  MP_TAC(ISPECL
   [`h':real^(1,M)finite_sum->real^N`;
    `interval[vec 0:real^1,vec 1] PCROSS (s:real^M->bool)`;
    `{vec 0:real^1,vec 1} PCROSS (s:real^M->bool) UNION
     interval[vec 0,vec 1] PCROSS t`;
    `u:real^N->bool`] ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR) THEN
  ASM_SIMP_TAC[ENR_IMP_ANR] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SET_RULE `{a,b} = {a} UNION {b}`] THEN
      REWRITE_TAC[PCROSS_UNION; UNION_ASSOC] THEN EXPAND_TAC "h'" THEN
      REPLICATE_TAC 2 (MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
       REPLICATE_TAC 2 (CONJ_TAC THENL
        [MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
         EXISTS_TAC `interval[vec 0:real^1,vec 1] PCROSS (s:real^M->bool)` THEN
         REWRITE_TAC[SET_RULE `t UNION u SUBSET s UNION t UNION u`] THEN
         REWRITE_TAC[SUBSET_UNION; UNION_SUBSET; SUBSET_PCROSS] THEN
         REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; ENDS_IN_UNIT_INTERVAL] THEN
         ASM_REWRITE_TAC[SUBSET_REFL] THEN
         TRY(MATCH_MP_TAC CLOSED_IN_UNION THEN CONJ_TAC) THEN
         MATCH_MP_TAC CLOSED_IN_PCROSS THEN
         ASM_REWRITE_TAC[CLOSED_IN_REFL] THEN MATCH_MP_TAC CLOSED_SUBSET THEN
         REWRITE_TAC[SING_SUBSET; ENDS_IN_UNIT_INTERVAL; CLOSED_SING];
         ALL_TAC]) THEN
       REPEAT CONJ_TAC THENL
        [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
         MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
         SIMP_TAC[LINEAR_SNDCART; LINEAR_CONTINUOUS_ON] THEN
         ASM_REWRITE_TAC[IMAGE_SNDCART_PCROSS; NOT_INSERT_EMPTY];
         ASM_REWRITE_TAC[];
         REWRITE_TAC[FORALL_PASTECART; IN_UNION; PASTECART_IN_PCROSS] THEN
         REWRITE_TAC[FSTCART_PASTECART; IN_SING; SNDCART_PASTECART] THEN
         MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^M`] THEN
         ASM_CASES_TAC `x:real^1 = vec 0` THEN ASM_REWRITE_TAC[] THEN
         REWRITE_TAC[VEC_EQ; ARITH_EQ; ENDS_IN_UNIT_INTERVAL] THEN
          ASM_CASES_TAC `x:real^1 = vec 1` THEN ASM_REWRITE_TAC[]]);
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART] THEN
      REWRITE_TAC[IN_UNION; PASTECART_IN_PCROSS; IN_SING; NOT_IN_EMPTY] THEN
      MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^M`] THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      EXPAND_TAC "h'" THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_SING] THEN
      REPEAT(COND_CASES_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]]) THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE f s SUBSET u ==> b IN s ==> f b IN u`)) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
      MATCH_MP_TAC CLOSED_IN_UNION THEN CONJ_TAC THEN
      MATCH_MP_TAC CLOSED_IN_PCROSS THEN
      ASM_REWRITE_TAC[CLOSED_IN_REFL] THEN
      MATCH_MP_TAC CLOSED_SUBSET THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; ENDS_IN_UNIT_INTERVAL] THEN
      SIMP_TAC[CLOSED_INSERT; CLOSED_EMPTY]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [`w:real^(1,M)finite_sum->bool`; `k:real^(1,M)finite_sum->real^N`] THEN
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`interval[vec 0:real^1,vec 1]`;
                 `t:real^M->bool`; `s:real^M->bool`;
                 `w:real^(1,M)finite_sum->bool`]
        TUBE_LEMMA_GEN) THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL; UNIT_INTERVAL_NONEMPTY] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `t':real^M->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[HOMOTOPIC_WITH] THEN
  EXISTS_TAC `k:real^(1,M)finite_sum->real^N` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    W(MP_TAC o PART_MATCH (lhs o snd o dest_imp) th o lhs o snd)) THEN
  REWRITE_TAC[IN_UNION; PASTECART_IN_PCROSS; IN_INSERT] THEN
  (ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
  EXPAND_TAC "h'" THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_SING] THEN
  REWRITE_TAC[VEC_EQ; ARITH_EQ]);;

let HOMOTOPIC_ON_COMPONENTS_EQ = prove
 (`!s t f g:real^M->real^N.
        (locally connected s \/ compact s /\ ANR t)
        ==> (homotopic_with (\x. T)
               (subtopology euclidean s,subtopology euclidean t) f g <=>
             f continuous_on s /\ IMAGE f s SUBSET t /\
             g continuous_on s /\ IMAGE g s SUBSET t /\
             !c. c IN components s
                 ==> homotopic_with (\x. T)
                      (subtopology euclidean c,subtopology euclidean t) f g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT `(q ==> r) /\ (r ==> (q <=> s)) ==> (q <=> r /\ s)`) THEN
  CONJ_TAC THENL
   [MESON_TAC[HOMOTOPIC_WITH_IMP_CONTINUOUS; HOMOTOPIC_WITH_IMP_SUBSET];
    ALL_TAC] THEN
  STRIP_TAC THEN EQ_TAC THENL
   [MESON_TAC[HOMOTOPIC_WITH_SUBSET_LEFT; IN_COMPONENTS_SUBSET];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!c. c IN components s
        ==> ?u. c SUBSET u /\
                closed_in (subtopology euclidean s) u /\
                open_in (subtopology euclidean s) u /\
                homotopic_with (\x. T)
                 (subtopology euclidean u,subtopology euclidean t)
                 (f:real^M->real^N) g`
  MP_TAC THENL
   [X_GEN_TAC `c:real^M->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [EXISTS_TAC `c:real^M->bool` THEN
      ASM_SIMP_TAC[CLOSED_IN_COMPONENT; SUBSET_REFL;
                   OPEN_IN_COMPONENTS_LOCALLY_CONNECTED];
      FIRST_X_ASSUM(MP_TAC o SPEC `c:real^M->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC(ISPECL
       [`f:real^M->real^N`; `g:real^M->real^N`;
        `s:real^M->bool`; `c:real^M->bool`; `t:real^N->bool`]
        HOMOTOPIC_NEIGHBOURHOOD_EXTENSION) THEN
      ASM_SIMP_TAC[CLOSED_IN_COMPONENT] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^M->bool` (STRIP_ASSUME_TAC o GSYM)) THEN
      MP_TAC(ISPECL [`s:real^M->bool`; `c:real^M->bool`; `v:real^M->bool`]
        SURA_BURA_CLOPEN_SUBSET) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_IMP_LOCALLY_COMPACT] THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC[COMPACT_COMPONENTS]; ASM SET_TAC[]];
        MATCH_MP_TAC MONO_EXISTS] THEN
      X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_SUBSET THEN
        ASM_MESON_TAC[COMPACT_IMP_CLOSED; OPEN_IN_IMP_SUBSET];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (REWRITE_RULE[IMP_CONJ] HOMOTOPIC_WITH_SUBSET_LEFT)) THEN
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
        ASM SET_TAC[]]];
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `k:(real^M->bool)->(real^M->bool)` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `s = UNIONS (IMAGE k (components(s:real^M->bool)))`
     (fun th -> SUBST1_TAC th THEN ASSUME_TAC(SYM th))
    THENL
      [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
        [GEN_REWRITE_TAC LAND_CONV [UNIONS_COMPONENTS] THEN
         MATCH_MP_TAC UNIONS_MONO THEN REWRITE_TAC[EXISTS_IN_IMAGE] THEN
         ASM_MESON_TAC[];
         REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
         ASM_MESON_TAC[CLOSED_IN_IMP_SUBSET]];
       MATCH_MP_TAC HOMOTOPIC_ON_CLOPEN_UNIONS THEN
       ASM_SIMP_TAC[FORALL_IN_IMAGE]]]);;

let INESSENTIAL_ON_COMPONENTS_EQ = prove
 (`!s t f:real^M->real^N.
        (locally connected s \/ compact s /\ ANR t) /\
        path_connected t
        ==> ((?a. homotopic_with (\x. T)
                   (subtopology euclidean s,subtopology euclidean t)
                   f (\x. a)) <=>
             f continuous_on s /\ IMAGE f s SUBSET t /\
             !c. c IN components s
                 ==> ?a. homotopic_with (\x. T)
                          (subtopology euclidean c,subtopology euclidean t)
                          f (\x. a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC(TAUT `(q ==> r) /\ (r ==> (q <=> s)) ==> (q <=> r /\ s)`) THEN
  CONJ_TAC THENL
   [MESON_TAC[HOMOTOPIC_WITH_IMP_CONTINUOUS; HOMOTOPIC_WITH_IMP_SUBSET];
    STRIP_TAC] THEN
  FIRST_ASSUM(fun th ->
       REWRITE_TAC[MATCH_MP HOMOTOPIC_ON_COMPONENTS_EQ th]) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_SIMP_TAC[COMPONENTS_EMPTY; IMAGE_CLAUSES; NOT_IN_EMPTY;
               EMPTY_SUBSET] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?c:real^M->bool. c IN components s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY; COMPONENTS_EQ_EMPTY]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `c:real^M->bool`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `a:real^N` THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; X_GEN_TAC `d:real^M->bool`] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `d:real^M->bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `b:real^N` MP_TAC) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET th) THEN
        MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_TRANS) THEN
  REWRITE_TAC[HOMOTOPIC_CONSTANT_MAPS] THEN DISJ2_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o
    REWRITE_RULE[PATH_CONNECTED_IFF_PATH_COMPONENT]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY)) THEN
  ASM SET_TAC[]);;

let COHOMOTOPICALLY_TRIVIAL_ON_COMPONENTS = prove
 (`!s:real^M->bool t:real^N->bool.
        (locally connected s \/ compact s /\ ANR t)
         ==> ((!f g. f continuous_on s /\ IMAGE f s SUBSET t /\
                     g continuous_on s /\ IMAGE g s SUBSET t
                     ==> homotopic_with (\x. T)
                          (subtopology euclidean s,subtopology euclidean t)
                          f g) <=>
              (!c. c IN components s
                   ==> (!f g. f continuous_on c /\ IMAGE f c SUBSET t /\
                              g continuous_on c /\ IMAGE g c SUBSET t
                              ==> homotopic_with (\x. T)
                                   (subtopology euclidean c,
                                    subtopology euclidean t) f g)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`g:real^M->real^N`; `s:real^M->bool`;
                   `c:real^M->bool`; `t:real^N->bool`]
        EXTENSION_FROM_COMPONENT) THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`;
                   `c:real^M->bool`; `t:real^N->bool`]
        EXTENSION_FROM_COMPONENT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ENR_IMP_ANR]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^N` STRIP_ASSUME_TAC) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ENR_IMP_ANR]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g':real^M->real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`f':real^M->real^N`; `g':real^M->real^N`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `c:real^M->bool` o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] HOMOTOPIC_WITH_SUBSET_LEFT)) THEN
    ASM_SIMP_TAC[IN_COMPONENTS_SUBSET] THEN MATCH_MP_TAC
     (ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
    ASM_SIMP_TAC[];
    FIRST_ASSUM(fun th ->
       REWRITE_TAC[MATCH_MP HOMOTOPIC_ON_COMPONENTS_EQ th]) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:real^M->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^M->bool`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
    REPEAT CONJ_TAC THEN
    TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET))) THEN
    ASM SET_TAC[]]);;

let COHOMOTOPICALLY_TRIVIAL_ON_COMPONENTS_NULL = prove
 (`!s:real^M->bool t:real^N->bool.
        (locally connected s \/ compact s /\ ANR t) /\ path_connected t
         ==> ((!f. f continuous_on s /\ IMAGE f s SUBSET t
                   ==> ?a. homotopic_with (\x. T)
                            (subtopology euclidean s,
                             subtopology euclidean t) f (\x. a)) <=>
              (!c. c IN components s
                   ==> (!f. f continuous_on c /\ IMAGE f c SUBSET t
                            ==> ?a. homotopic_with (\x. T)
                                     (subtopology euclidean c,
                                      subtopology euclidean t) f (\x. a))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COHOMOTOPICALLY_TRIVIAL_ON_COMPONENTS) THEN
  ASM_SIMP_TAC[HOMOTOPIC_TRIVIALITY]);;

let COHOMOTOPICALLY_TRIVIAL_1D = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        ANR t /\ connected t /\
        (dimindex(:M) = 1 \/ ?r:real^1->bool. s homeomorphic r)
        ==> ?a. homotopic_with (\x. T)
                 (subtopology euclidean s,subtopology euclidean t) f (\x. a)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `path_connected(t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ANR_IMP_LOCALLY_PATH_CONNECTED;
                  PATH_CONNECTED_EQ_CONNECTED_LPC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[]
    `p \/ q ==> (p ==> q) ==> q`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM DIMINDEX_1; GSYM DIM_UNIV] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
     (REWRITE_RULE[CONJ_ASSOC] HOMEOMORPHIC_SUBSPACES))) THEN
    REWRITE_TAC[SUBSPACE_UNIV; homeomorphic] THEN
    GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^M->real^1` THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^1->real^M` THEN
    DISCH_TAC THEN EXISTS_TAC `IMAGE (f:real^M->real^1) s` THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
      HOMEOMORPHISM_OF_SUBSETS)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `r:real^1->bool`)] THEN
  SUBGOAL_THEN
   `!c. c IN components s
        ==> ?u. closed_in (subtopology euclidean s) u /\
                open_in (subtopology euclidean s) u /\
                c SUBSET u /\
                ?a. homotopic_with (\x. T)
                     (subtopology euclidean u,subtopology euclidean t)
                     (f:real^M->real^N) (\x. a)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `c:real^M->bool`; `t:real^N->bool`]
        NULLHOMOTOPIC_FROM_CONTRACTIBLE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`g:real^M->real^1`; `h:real^1->real^M`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `contractible(IMAGE (g:real^M->real^1) c)` MP_TAC THENL
       [SIMP_TAC[GSYM IS_INTERVAL_CONTRACTIBLE_1; IS_INTERVAL_CONNECTED_1] THEN
        MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_CONNECTED) THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; homeomorphism];
        MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HOMEOMORPHIC_CONTRACTIBLE_EQ THEN
        ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
        MAP_EVERY EXISTS_TAC [`g:real^M->real^1`; `h:real^1->real^M`] THEN
        FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
          HOMEOMORPHISM_OF_SUBSETS)) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[]];
      DISCH_THEN(X_CHOOSE_TAC `a:real^N`)] THEN
    MP_TAC(ISPECL
     [`f:real^M->real^N`; `(\x. a):real^M->real^N`;
      `s:real^M->bool`; `c:real^M->bool`; `t:real^N->bool`]
       HOMOTOPIC_NEIGHBOURHOOD_EXTENSION) THEN
     ASM_REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
     ASM_SIMP_TAC[CLOSED_IN_COMPONENT] THEN ANTS_TAC THENL
      [FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
       FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
       ASM SET_TAC[];
       DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC)] THEN
     MP_TAC(ISPECL
      [`s:real^M->bool`; `c:real^M->bool`; `u:real^M->bool`]
        COMPONENT_INTERMEDIATE_CLOPEN) THEN
     ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^M->bool` THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `a:real^N` THEN
     ASM_MESON_TAC[HOMOTOPIC_WITH_SUBSET_LEFT];
     GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
     REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
     X_GEN_TAC `u:(real^M->bool)->real^M->bool` THEN STRIP_TAC THEN
     SUBGOAL_THEN
      `s = UNIONS (IMAGE (u:(real^M->bool)->real^M->bool) (components s))`
      (fun th -> SUBST1_TAC th THEN ASSUME_TAC (SYM th))
     THENL
      [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
        [GEN_REWRITE_TAC LAND_CONV [UNIONS_COMPONENTS] THEN
         GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM IMAGE_ID] THEN
         MATCH_MP_TAC UNIONS_MONO_IMAGE THEN ASM_SIMP_TAC[];
         REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
         ASM_MESON_TAC[CLOSED_IN_IMP_SUBSET]];
       MATCH_MP_TAC INESSENTIAL_ON_CLOPEN_UNIONS THEN
       ASM_SIMP_TAC[FORALL_IN_IMAGE]]]);;

(* ------------------------------------------------------------------------- *)
(* A few simple lemmas about deformation retracts.                           *)
(* ------------------------------------------------------------------------- *)

let DEFORMATION_RETRACTION_COMPOSE = prove
 (`!s t u r1 r2:real^N->real^N.
        homotopic_with (\x. T)
          (subtopology euclidean s,subtopology euclidean s) (\x. x) r1 /\
        retraction (s,t) r1 /\
        homotopic_with (\x. T)
          (subtopology euclidean t,subtopology euclidean t) (\x. x) r2 /\
        retraction (t,u) r2
        ==> homotopic_with (\x. T)
             (subtopology euclidean s,subtopology euclidean s)
             (\x. x) (r2 o r1) /\
            retraction (s,u) (r2 o r1)`,
  REPEAT STRIP_TAC THENL [ALL_TAC; ASM_MESON_TAC[RETRACTION_o]] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
  EXISTS_TAC `(\x. x) o (r1:real^N->real^N)` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[o_DEF; ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_COMPOSE_CONTINUOUS_RIGHT THEN
  EXISTS_TAC `t:real^N->bool` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_WITH_RESTRICT));
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[retraction]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let DEFORMATION_RETRACT_TRANS = prove
 (`!s t u:real^N->bool.
        (?r. homotopic_with (\x. T)
              (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
             retraction (s,t) r) /\
        (?r. homotopic_with (\x. T)
              (subtopology euclidean t,subtopology euclidean t) (\x. x) r /\
             retraction (t,u) r)
        ==> ?r. homotopic_with (\x. T)
                 (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
                retraction (s,u) r`,
  MESON_TAC[DEFORMATION_RETRACTION_COMPOSE]);;

let DEFORMATION_RETRACT_IMP_HOMOTOPY_EQUIVALENT = prove
 (`!s t:real^N->bool.
        (?r. homotopic_with (\x. T)
              (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
             retraction(s,t) r)
        ==> s homotopy_equivalent t`,
  REWRITE_TAC[GSYM I_DEF; GSYM RETRACTION_MAPS_EUCLIDEAN] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM HOMOTOPY_EQUIVALENT_SPACE_EUCLIDEAN] THEN
  MATCH_MP_TAC DEFORMATION_RETRACTION_IMP_HOMOTOPY_EQUIVALENT_SPACE THEN
  ASM_MESON_TAC[I_O_ID; HOMOTOPIC_WITH_SYM]);;

let DEFORMATION_RETRACT = prove
 (`!s t:real^N->bool.
        (?r. homotopic_with (\x. T)
              (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
             retraction(s,t) r) <=>
        t retract_of s /\
        ?f. homotopic_with (\x. T)
             (subtopology euclidean s,subtopology euclidean s) (\x. x) f /\
            IMAGE f s SUBSET t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retract_of; retraction] THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `r:real^N->real^N` THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `r:real^N->real^N` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) MP_TAC) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `f:real^N->real^N` THEN
    STRIP_TAC THEN EXISTS_TAC `r:real^N->real^N` THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC HOMOTOPIC_WITH_TRANS `f:real^N->real^N` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`(r:real^N->real^N) o (f:real^N->real^N)`;
      `(r:real^N->real^N) o (\x. x)`] THEN
    ASM_SIMP_TAC[o_THM] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[HOMOTOPIC_WITH_SYM]; ASM SET_TAC[]]]);;

let ANR_STRONG_DEFORMATION_RETRACTION = prove
 (`!s t:real^N->bool.
        ANR s /\
        (?r. homotopic_with (\x. T)
              (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
             retraction(s,t) r)
        ==> ?r. homotopic_with (\h. !x. x IN t ==> h x = x)
                 (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
                retraction(s,t) r`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMOTOPIC_WITH_EUCLIDEAN]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:real^(1,N)finite_sum->real^N` THEN STRIP_TAC THEN
  ABBREV_TAC
   `g:real^(1,(1,N)finite_sum)finite_sum->real^N =
     \z. if fstcart(sndcart z) = vec 0 then (sndcart(sndcart z))
         else if fstcart(sndcart z) = vec 1
              then f(pastecart (vec 1 - fstcart z)
                               (f(pastecart (vec 1) (sndcart(sndcart z)))))
         else f(pastecart (lift(drop(fstcart(sndcart z)) *
                                    (&1 - drop (fstcart z))))
                          (sndcart(sndcart z)))` THEN
  MP_TAC(ISPECL
   [`f:real^(1,N)finite_sum->real^N`;
    `\x. (g:real^(1,(1,N)finite_sum)finite_sum->real^N) (pastecart (vec 1) x)`;
    `{vec 0:real^1,vec 1} PCROSS (s:real^N->bool) UNION
     interval[vec 0:real^1,vec 1] PCROSS (t:real^N->bool)`;
    `interval[vec 0:real^1,vec 1] PCROSS (s:real^N->bool)`;
    `s:real^N->bool`] BORSUK_HOMOTOPY_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_UNION THEN CONJ_TAC THEN
      MATCH_MP_TAC CLOSED_IN_PCROSS THEN REWRITE_TAC[CLOSED_IN_REFL] THENL
       [ALL_TAC; ASM_MESON_TAC[CLOSED_IN_RETRACT; retract_of]] THEN
      ONCE_REWRITE_TAC[SET_RULE `{a,b} = {a} UNION {b}`] THEN
      MATCH_MP_TAC CLOSED_IN_UNION THEN
      REWRITE_TAC[CLOSED_IN_SING; ENDS_IN_UNIT_INTERVAL];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) HOMOTOPIC_WITH o snd) THEN
    ANTS_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retraction]) THEN SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    EXISTS_TAC `g:real^(1,(1,N)finite_sum)finite_sum->real^N` THEN
    EXPAND_TAC "g" THEN
    REWRITE_TAC[FORALL_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_REWRITE_TAC[DROP_VEC; REAL_SUB_RZERO; REAL_MUL_RID; LIFT_DROP;
                    VECTOR_SUB_RZERO; PASTECART_FST_SND; CONJ_ASSOC] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[IN_UNION; PASTECART_IN_PCROSS; IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retraction]) THEN
      SET_TAC[]] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN EXPAND_TAC "g" THEN
      REWRITE_TAC[FORALL_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      ASM_REWRITE_TAC[DROP_VEC; REAL_SUB_RZERO; REAL_MUL_RID; LIFT_DROP;
                   VECTOR_SUB_RZERO; PASTECART_FST_SND; CONJ_ASSOC;
                   PASTECART_IN_PCROSS; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
      MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`; `y:real^N`] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retraction]) THEN SET_TAC[];
        ALL_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE f s SUBSET t ==> x IN s ==> f x IN t`)) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN
      (CONJ_TAC THENL
        [ALL_TAC;
         FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retraction]) THEN
         ASM SET_TAC[]]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC; DROP_SUB;
                      REAL_SUB_LE; REAL_ARITH `&1 - x <= &1 <=> &0 <= x`] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC] THEN
    EXPAND_TAC "g" THEN
    REWRITE_TAC[MESON[] `(if p then x else if q then y else r) =
        (if p \/ q then if p then x else y else r)`] THEN
    REWRITE_TAC[PCROSS_UNION] THEN MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CLOSED_IN_CLOSED] THEN
      EXISTS_TAC `(:real^1) PCROSS {vec 0:real^1,vec 1} PCROSS (:real^N)` THEN
      SIMP_TAC[CLOSED_PCROSS_EQ; CLOSED_UNIV; CLOSED_INSERT; CLOSED_EMPTY] THEN
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNION; IN_INTER;
                  EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY] THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retraction]) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o REWRITE_RULE[SUBSET]) THEN
      MESON_TAC[ENDS_IN_UNIT_INTERVAL];
      SUBGOAL_THEN `closed_in (subtopology euclidean s) (t:real^N->bool)`
      MP_TAC THENL [ASM_MESON_TAC[CLOSED_IN_RETRACT; retract_of]; ALL_TAC] THEN
      REWRITE_TAC[CLOSED_IN_CLOSED] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(:real^1) PCROSS (:real^1) PCROSS (c:real^N->bool)` THEN
      ASM_REWRITE_TAC[CLOSED_PCROSS_EQ; CLOSED_UNIV] THEN
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNION; IN_INTER;
                  EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY] THEN
      MESON_TAC[ENDS_IN_UNIT_INTERVAL];
      ONCE_REWRITE_TAC[SET_RULE `{a,b} = {a} UNION {b}`] THEN
      REWRITE_TAC[PCROSS_UNION] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC
         `(:real^1) PCROSS {vec 0:real^1} PCROSS (:real^N)` THEN
        ASM_REWRITE_TAC[CLOSED_PCROSS_EQ; CLOSED_UNIV] THEN
        REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNION; IN_INTER;
                EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY; CLOSED_SING] THEN
        MESON_TAC[ENDS_IN_UNIT_INTERVAL];
        REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC
         `(:real^1) PCROSS {vec 1:real^1} PCROSS (:real^N)` THEN
        ASM_REWRITE_TAC[CLOSED_PCROSS_EQ; CLOSED_UNIV] THEN
        REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNION; IN_INTER;
                EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY; CLOSED_SING] THEN
        MESON_TAC[ENDS_IN_UNIT_INTERVAL];
        SIMP_TAC[CONTINUOUS_ON_SNDCART; LINEAR_CONTINUOUS_ON;
                 LINEAR_SNDCART];
        ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
          SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST;
                   LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
          GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
          SIMP_TAC[CONTINUOUS_ON_SNDCART; LINEAR_CONTINUOUS_ON;
                   LINEAR_SNDCART] THEN
          FIRST_X_ASSUM(STRIP_ASSUME_TAC o
            GEN_REWRITE_RULE I [retraction]) THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS;
                      FORALL_PASTECART; SNDCART_PASTECART] THEN
          SIMP_TAC[];
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS;
            FORALL_PASTECART; SNDCART_PASTECART; FSTCART_PASTECART] THEN
          SIMP_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN
          SIMP_TAC[REAL_ARITH `&1 - x <= &1 <=> &0 <= x`; REAL_SUB_LE] THEN
          FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retraction]) THEN
          SET_TAC[]];
        REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS;
                    FSTCART_PASTECART; SNDCART_PASTECART; IN_SING] THEN
        MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`; `y:real^N`] THEN
        ASM_CASES_TAC `v:real^1 = vec 0` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[VEC_EQ; ARITH_EQ]];
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        SIMP_TAC[CONTINUOUS_ON_SNDCART; LINEAR_CONTINUOUS_ON;
                   LINEAR_SNDCART] THEN
        REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
        SIMP_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_FSTCART;
                 LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
        SIMP_TAC[LIFT_SUB; LIFT_DROP; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST;
                 LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS;
          FORALL_PASTECART; SNDCART_PASTECART; FSTCART_PASTECART] THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC; LIFT_DROP] THEN
        SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE] THEN
        REPEAT STRIP_TAC THENL
         [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
          FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retraction]) THEN
          ASM SET_TAC[]]];
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS;
                    FSTCART_PASTECART; SNDCART_PASTECART; IN_SING] THEN
      MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`; `y:real^N`] THEN
      COND_CASES_TAC THEN
      ASM_REWRITE_TAC[IN_INSERT; LIFT_DROP; REAL_MUL_LZERO; DROP_VEC;
                      LIFT_NUM] THEN
      ASM_CASES_TAC `v:real^1 = vec 1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC[DROP_VEC; REAL_MUL_LID;
                      LIFT_SUB; LIFT_NUM; LIFT_DROP] THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retraction]) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,N)finite_sum->real^N`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(h:real^(1,N)finite_sum->real^N) o pastecart (vec 1)` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) HOMOTOPIC_WITH o snd) THEN
    ANTS_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retraction]) THEN SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    EXISTS_TAC `h:real^(1,N)finite_sum->real^N` THEN
    ASM_SIMP_TAC[IN_UNION; PASTECART_IN_PCROSS; IN_INSERT; o_THM] THEN
    EXPAND_TAC "g" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_REWRITE_TAC[DROP_VEC; VECTOR_SUB_REFL; REAL_SUB_REFL; REAL_MUL_RZERO;
                    LIFT_NUM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retraction]) THEN SET_TAC[];
    REWRITE_TAC[retraction; o_THM] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retraction]) THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
        SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST;
                 CONTINUOUS_ON_ID];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
        SIMP_TAC[ENDS_IN_UNIT_INTERVAL]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM];
      ALL_TAC] THEN
    ASM_SIMP_TAC[IN_UNION; IN_INSERT; PASTECART_IN_PCROSS;
       ENDS_IN_UNIT_INTERVAL] THEN
    EXPAND_TAC "g" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; VEC_EQ; ARITH_EQ] THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retraction]) THEN SET_TAC[]]);;

let DEFORMATION_RETRACT_OF_CONTRACTIBLE = prove
 (`!s t:real^N->bool.
        contractible s /\ t retract_of s
        ==> ?r. homotopic_with (\x. T)
                 (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
                retraction(s,t) r`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_SIMP_TAC[RETRACT_OF_EMPTY; HOMOTOPIC_ON_EMPTY] THENL
   [MESON_TAC[RETRACTION_REFL]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DEFORMATION_RETRACT] THEN
  SUBGOAL_THEN `?a:real^N. a IN t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY; AR_ANR]; ALL_TAC] THEN
  EXISTS_TAC `(\x. a):real^N->real^N` THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [contractible]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `b:real^N` THEN
  DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  SUBGOAL_THEN `(a:real^N) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[RETRACT_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^N) IN s` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_WITH_TRANS)) THEN
  REWRITE_TAC[HOMOTOPIC_CONSTANT_MAPS] THEN
  ASM_MESON_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT;
                CONTRACTIBLE_IMP_PATH_CONNECTED]);;

let AR_DEFORMATION_RETRACT_OF_CONTRACTIBLE = prove
 (`!s t:real^N->bool.
        contractible s /\ AR t /\ closed_in (subtopology euclidean s) t
        ==> ?r. homotopic_with (\x. T)
                 (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
                retraction(s,t) r`,
  MESON_TAC[DEFORMATION_RETRACT_OF_CONTRACTIBLE; AR_IMP_RETRACT]);;

let DEFORMATION_RETRACT_OF_CONTRACTIBLE_SING = prove
 (`!s a:real^N.
        contractible s /\ a IN s
        ==> ?r. homotopic_with (\x. T)
                 (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
                retraction(s,{a}) r`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC AR_DEFORMATION_RETRACT_OF_CONTRACTIBLE THEN
  ASM_REWRITE_TAC[CLOSED_IN_SING; AR_SING]);;

let STRONG_DEFORMATION_RETRACT_OF_AR = prove
 (`!s t:real^N->bool.
        AR s /\ t retract_of s
        ==> ?r. homotopic_with (\h. !x. x IN t ==> h x = x)
                 (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
                retraction(s,t) r`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ANR_STRONG_DEFORMATION_RETRACTION THEN
  ASM_SIMP_TAC[AR_IMP_ANR] THEN
  MATCH_MP_TAC DEFORMATION_RETRACT_OF_CONTRACTIBLE THEN
  ASM_SIMP_TAC[AR_IMP_CONTRACTIBLE]);;

let AR_STRONG_DEFORMATION_RETRACT_OF_AR = prove
 (`!s t:real^N->bool.
        AR s /\ AR t /\ closed_in (subtopology euclidean s) t
        ==> ?r. homotopic_with (\h. !x. x IN t ==> h x = x)
                 (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
                retraction(s,t) r`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ANR_STRONG_DEFORMATION_RETRACTION THEN
  ASM_SIMP_TAC[AR_IMP_ANR] THEN
  MATCH_MP_TAC AR_DEFORMATION_RETRACT_OF_CONTRACTIBLE THEN
  ASM_SIMP_TAC[AR_IMP_CONTRACTIBLE]);;

let SING_STRONG_DEFORMATION_RETRACT_OF_AR = prove
 (`!s a:real^N.
        AR s /\ a IN s
        ==> ?r. homotopic_with (\h. h a = a)
                 (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
                retraction(s,{a}) r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `{a:real^N}`]
        AR_STRONG_DEFORMATION_RETRACT_OF_AR) THEN
  ASM_REWRITE_TAC[AR_SING; CLOSED_IN_SING] THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY]);;

let HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_CONVEX = prove
 (`!s t a:real^N.
      convex s /\ bounded s /\ a IN relative_interior s /\
      convex t /\ relative_frontier s SUBSET t /\ t SUBSET affine hull s
      ==> (relative_frontier s) homotopy_equivalent (t DELETE a)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[HOMOTOPY_EQUIVALENT_SYM] THEN
  MATCH_MP_TAC DEFORMATION_RETRACT_IMP_HOMOTOPY_EQUIVALENT THEN
  ASM_MESON_TAC[RELATIVE_FRONTIER_DEFORMATION_RETRACT_OF_PUNCTURED_CONVEX]);;

let HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_AFFINE_HULL = prove
 (`!s a:real^N.
      convex s /\ bounded s /\ a IN relative_interior s
      ==> (relative_frontier s) homotopy_equivalent (affine hull s DELETE a)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_CONVEX THEN
  ASM_SIMP_TAC[AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL; SUBSET_REFL] THEN
  REWRITE_TAC[relative_frontier] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s DIFF t SUBSET u`) THEN
  REWRITE_TAC[CLOSURE_SUBSET_AFFINE_HULL]);;

let HOMOTOPY_EQUIVALENT_PUNCTURED_UNIV_SPHERE = prove
 (`!c a:real^N r.
        &0 < r ==> ((:real^N) DELETE c) homotopy_equivalent sphere(a,r)`,
  REPEAT GEN_TAC THEN GEN_GEOM_ORIGIN_TAC `c:real^N` ["a"] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[HOMOTOPY_EQUIVALENT_SYM] THEN
  TRANS_TAC HOMOTOPY_EQUIVALENT_TRANS `sphere(vec 0:real^N,r)` THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_SPHERES; HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT] THEN
  MP_TAC(ISPECL [`cball(vec 0:real^N,r)`; `vec 0:real^N`]
    HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_AFFINE_HULL) THEN
  REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; RELATIVE_FRONTIER_CBALL;
              RELATIVE_INTERIOR_CBALL] THEN
  ASM_SIMP_TAC[CENTRE_IN_BALL; REAL_LT_IMP_NZ; AFFINE_HULL_NONEMPTY_INTERIOR;
               INTERIOR_CBALL; BALL_EQ_EMPTY; REAL_NOT_LE]);;

(* ------------------------------------------------------------------------- *)
(* Preservation of fixpoints under (more general notion of) retraction.      *)
(* ------------------------------------------------------------------------- *)

let INVERTIBLE_FIXPOINT_PROPERTY = prove
 (`!s:real^M->bool t:real^N->bool i r.
     i continuous_on t /\ IMAGE i t SUBSET s /\
     r continuous_on s /\ IMAGE r s SUBSET t /\
     (!y. y IN t ==> (r(i(y)) = y))
     ==> (!f. f continuous_on s /\ IMAGE f s SUBSET s
              ==> ?x. x IN s /\ (f x = x))
         ==> !g. g continuous_on t /\ IMAGE g t SUBSET t
                 ==> ?y. y IN t /\ (g y = y)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `(i:real^N->real^M) o (g:real^N->real^N) o (r:real^M->real^N)`) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; CONTINUOUS_ON_COMPOSE; IMAGE_SUBSET;
                  SUBSET_TRANS; IMAGE_o];
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
    REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]]);;

let HOMEOMORPHIC_FIXPOINT_PROPERTY = prove
 (`!s t. s homeomorphic t
         ==> ((!f. f continuous_on s /\ IMAGE f s SUBSET s
                   ==> ?x. x IN s /\ (f x = x)) <=>
              (!g. g continuous_on t /\ IMAGE g t SUBSET t
                   ==> ?y. y IN t /\ (g y = y)))`,
  REWRITE_TAC[homeomorphic; homeomorphism] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN MATCH_MP_TAC INVERTIBLE_FIXPOINT_PROPERTY THEN
  ASM_MESON_TAC[SUBSET_REFL]);;

let RETRACT_FIXPOINT_PROPERTY = prove
 (`!s t:real^N->bool.
        t retract_of s /\
        (!f. f continuous_on s /\ IMAGE f s SUBSET s
             ==> ?x. x IN s /\ (f x = x))
        ==> !g. g continuous_on t /\ IMAGE g t SUBSET t
                ==> ?y. y IN t /\ (g y = y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC INVERTIBLE_FIXPOINT_PROPERTY THEN
  EXISTS_TAC `\x:real^N. x` THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[retract_of] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN REWRITE_TAC[retraction] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE]);;

let FRONTIER_SUBSET_RETRACTION = prove
 (`!s:real^N->bool t r.
        bounded s /\
        frontier s SUBSET t /\
        r continuous_on (closure s) /\
        IMAGE r s SUBSET t /\
        (!x. x IN t ==> r x = x)
        ==> s SUBSET t`,
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[SET_RULE `~(s SUBSET t) <=> ?x. x IN s /\ ~(x IN t)`] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
  REPLICATE_TAC 3 GEN_TAC THEN X_GEN_TAC `a:real^N` THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `q = \z:real^N. if z IN closure s then r(z) else z` THEN
  SUBGOAL_THEN
    `(q:real^N->real^N) continuous_on
      closure(s) UNION closure((:real^N) DIFF s)`
  MP_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    ASM_REWRITE_TAC[CLOSED_CLOSURE; CONTINUOUS_ON_ID] THEN
    REWRITE_TAC[TAUT `p /\ ~p <=> F`] THEN X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[CLOSURE_COMPLEMENT; IN_DIFF; IN_UNIV] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; frontier; IN_DIFF]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(s) UNION closure((:real^N) DIFF s) = (:real^N)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `s SUBSET closure s /\ t SUBSET closure t /\ s UNION t = UNIV
      ==> closure s UNION closure t = UNIV`) THEN
    REWRITE_TAC[CLOSURE_SUBSET] THEN SET_TAC[];
    DISCH_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o SPEC `a:real^N` o
    MATCH_MP BOUNDED_SUBSET_BALL o MATCH_MP BOUNDED_CLOSURE) THEN
  SUBGOAL_THEN `!x. ~((q:real^N->real^N) x = a)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "q" THEN COND_CASES_TAC THENL
     [ASM_CASES_TAC `(x:real^N) IN s` THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^N) IN t` (fun th -> ASM_MESON_TAC[th]) THEN
      UNDISCH_TAC `frontier(s:real^N->bool) SUBSET t` THEN
      REWRITE_TAC[SUBSET; frontier; IN_DIFF] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET];
      ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET; CLOSURE_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N`; `B:real`] NO_RETRACTION_CBALL) THEN
  ASM_REWRITE_TAC[retract_of; GSYM FRONTIER_CBALL] THEN
  EXISTS_TAC `(\y. a + B / norm(y - a) % (y - a)) o (q:real^N->real^N)` THEN
  REWRITE_TAC[retraction; FRONTIER_SUBSET_EQ; CLOSED_CBALL] THEN
  REWRITE_TAC[FRONTIER_CBALL; SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_SPHERE; DIST_0] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[o_DEF; real_div; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; NORM_EQ_0; VECTOR_SUB_EQ] THEN
    SUBGOAL_THEN `(\x:real^N. lift(norm(x - a))) = (lift o norm) o (\x. x - a)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM];
    REWRITE_TAC[o_THM; NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM;
                NORM_ARITH `dist(a,a + b) = norm b`] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; VECTOR_SUB_EQ; NORM_EQ_0] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    EXPAND_TAC "q" THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_BALL]) THEN
      ASM_MESON_TAC[REAL_LT_REFL];
      REWRITE_TAC[NORM_ARITH `norm(x - a) = dist(a,x)`] THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
      VECTOR_ARITH_TAC]]);;

let NO_RETRACTION_FRONTIER_BOUNDED = prove
 (`!s:real^N->bool.
        bounded s /\ ~(interior s = {}) ==> ~((frontier s) retract_of s)`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[retract_of; retraction] THEN
  REWRITE_TAC[FRONTIER_SUBSET_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `frontier s:real^N->bool`;
                 `r:real^N->real^N`] FRONTIER_SUBSET_RETRACTION) THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED; SUBSET_REFL] THEN REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]);;

let COMPACT_SUBSET_FRONTIER_RETRACTION = prove
 (`!f:real^N->real^N s.
        compact s /\ f continuous_on s /\ (!x. x IN frontier s ==> f x = x)
        ==> s SUBSET IMAGE f s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s UNION (IMAGE f s):real^N->bool`; `vec 0:real^N`]
    BOUNDED_SUBSET_BALL) THEN
  ASM_SIMP_TAC[BOUNDED_UNION; COMPACT_IMP_BOUNDED;
               COMPACT_CONTINUOUS_IMAGE; UNION_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `g = \x:real^N. if x IN s then f(x) else x` THEN
  SUBGOAL_THEN `(g:real^N->real^N) continuous_on (:real^N)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(:real^N) = s UNION closure((:real^N) DIFF s)` SUBST1_TAC
    THENL
     [MATCH_MP_TAC(SET_RULE `UNIV DIFF s SUBSET t ==> UNIV = s UNION t`) THEN
      REWRITE_TAC[CLOSURE_SUBSET];
      ALL_TAC] THEN
    EXPAND_TAC "g" THEN MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    ASM_SIMP_TAC[CLOSED_CLOSURE; CONTINUOUS_ON_ID; COMPACT_IMP_CLOSED] THEN
    REWRITE_TAC[CLOSURE_COMPLEMENT; IN_DIFF; IN_UNIV] THEN
    REWRITE_TAC[TAUT `p /\ ~p <=> F`] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[frontier; IN_DIFF] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?h:real^N->real^N.
        retraction (UNIV DELETE p,sphere(vec 0,r)) h`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM retract_of] THEN
    MATCH_MP_TAC SPHERE_RETRACT_OF_PUNCTURED_UNIVERSE_GEN THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `r:real`] NO_RETRACTION_CBALL) THEN
  ASM_REWRITE_TAC[retract_of; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^N) o (g:real^N->real^N)`) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[retraction] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retraction]) THEN
  SIMP_TAC[SUBSET; IN_SPHERE; IN_CBALL; REAL_EQ_IMP_LE] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_DELETE; IN_UNIV; o_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN cball (vec 0,r) ==> ~((g:real^N->real^N) x = p)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXPAND_TAC "g" THEN
    COND_CASES_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_DELETE];
    SUBGOAL_THEN `(g:real^N->real^N) x = x` (fun th -> ASM_SIMP_TAC[th]) THEN
    EXPAND_TAC "g" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[IN_BALL; REAL_LT_REFL; SUBSET]]);;

let NOT_ABSOLUTE_RETRACT_COBOUNDED = prove
 (`!s. bounded s /\ ((:real^N) DIFF s) retract_of (:real^N) ==> s = {}`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(SET_RULE `(!x. x IN s ==> F) ==> s = {}`) THEN
  X_GEN_TAC `a:real^N` THEN POP_ASSUM MP_TAC THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^N` o
    MATCH_MP BOUNDED_SUBSET_BALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^N` o MATCH_MP NO_RETRACTION_CBALL) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC RETRACT_OF_SUBSET THEN
  EXISTS_TAC `(:real^N)` THEN SIMP_TAC[SUBSET_UNIV; SPHERE_SUBSET_CBALL] THEN
  MATCH_MP_TAC RETRACT_OF_TRANS THEN EXISTS_TAC `(:real^N) DIFF s` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RETRACT_OF_SUBSET THEN
  EXISTS_TAC `(:real^N) DELETE (vec 0)` THEN
  ASM_SIMP_TAC[SPHERE_RETRACT_OF_PUNCTURED_UNIVERSE] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_SPHERE; IN_DIFF; IN_UNIV] THEN
  MESON_TAC[REAL_LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Bohl-type fixed point theorems.                                           *)
(* ------------------------------------------------------------------------- *)

let BOHL = prove
 (`!f s a:real^N.
        f continuous_on s /\ convex s /\ compact s /\ a IN interior s
        ==> (?x. x IN s /\ f x = x) \/
            (?x. x IN frontier s /\ x IN segment(a,f x))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; INTERIOR_EMPTY] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `affine hull s:real^N->bool`; `a:real^N`]
        RELATIVE_FRONTIER_DEFORMATION_RETRACT_OF_PUNCTURED_CONVEX) THEN
  ASM_SIMP_TAC[AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL; COMPACT_IMP_BOUNDED] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (SET_RULE `a IN s ==> ~(s = {})`)) THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_NONEMPTY_INTERIOR;
                RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN
  SIMP_TAC[SUBSET_REFL; frontier; CLOSURE_SUBSET_AFFINE_HULL;
           SET_RULE `s SUBSET u ==> s DIFF t SUBSET u`] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retraction]) THEN
  ASM_SIMP_TAC[AFFINE_HULL_NONEMPTY_INTERIOR; GSYM frontier] THEN
  STRIP_TAC THEN MP_TAC(ISPECL
   [`(\x. if x IN s then x else r x) o (f:real^N->real^N)`;
    `s:real^N->bool`] BROUWER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `IMAGE (f:real^N->real^N) s =
                s INTER IMAGE f s UNION
                ((:real^N) DIFF interior s) INTER IMAGE f s`
      SUBST1_TAC THENL
       [MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
      ASM_SIMP_TAC[CLOSED_INTER_COMPACT; COMPACT_CONTINUOUS_IMAGE;
                   COMPACT_IMP_CLOSED; GSYM OPEN_CLOSED; OPEN_INTERIOR] THEN
      REWRITE_TAC[CONTINUOUS_ON_ID] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
        REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[frontier] THEN
        MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN
      DISCH_TAC THEN REWRITE_TAC[o_DEF] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE r t SUBSET u ==> u SUBSET s /\ y IN t ==> r y IN s`)) THEN
      ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
      MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]];
    REWRITE_TAC[OR_EXISTS_THM; o_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `x:real^N` THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `f(x:real^N) = x` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((f:real^N->real^N) x = a)` ASSUME_TAC THENL
     [MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[IN_SEGMENT]] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `c:real` MP_TAC o
        SPEC `(f:real^N->real^N) x`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[VECTOR_ARITH
     `x:real^N = (&1 - c) % a + c % y <=> x - a = c % (y - a)`] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((f:real^N->real^N) x IN s)` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`a:real^N`; `x:real^N`; `&1 - inv c`; `inv(c):real`]) THEN
    FIRST_ASSUM(ASSUME_TAC o
      MATCH_MP(REWRITE_RULE[SUBSET] INTERIOR_SUBSET)) THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_SUB_LE; REAL_LT_IMP_LE;
                 REAL_INV_LE_1; REAL_ARITH `(&1 - u) + u = &1`] THEN
    FIRST_ASSUM(fun th ->
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
      [MATCH_MP (VECTOR_ARITH `x - a:real^N = y ==> x = a + y`) th]) THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_ARITH `&1 <= c ==> ~(c = &0)`] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC VECTOR_ARITH]);;

let BOHL_ALT = prove
 (`!f s a.
        f continuous_on s /\ convex s /\ compact s /\ a IN interior s /\
        IMAGE f s SUBSET (:real^N) DELETE a
        ==> ?x. x IN frontier s /\ a IN segment(x,f x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x:real^N. x + (a - f(x))`; `s:real^N->bool`; `a:real^N`]
        BOHL) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST;
               CONTINUOUS_ON_ID] THEN
  REWRITE_TAC[VECTOR_ARITH `x + a - y:real^N = x <=> y = a`] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[IN_SEGMENT; VECTOR_ARITH `a:real^N = x + a - y <=> y = x`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[]) THEN
  CONV_TAC VECTOR_ARITH);;

let BOHL_SIMPLE = prove
 (`!f:real^N->real^N s a.
       compact s /\ a IN s /\
       f continuous_on s /\ IMAGE f s SUBSET (:real^N) DELETE a
       ==> ?x. x IN frontier s /\ ~(f x = x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `s:real^N->bool`]
        COMPACT_SUBSET_FRONTIER_RETRACTION) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some more theorems about connectivity of retract complements.             *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_COMPONENT_RETRACT_COMPLEMENT_MEETS = prove
 (`!s t c. closed s /\ s retract_of t /\
           c IN components((:real^N) DIFF s) /\ bounded c
           ==> ~(c SUBSET t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
  SUBGOAL_THEN `frontier(c:real^N->bool) SUBSET s` ASSUME_TAC THENL
   [TRANS_TAC SUBSET_TRANS `frontier((:real^N) DIFF s)` THEN
    ASM_SIMP_TAC[FRONTIER_OF_COMPONENTS_SUBSET] THEN
    REWRITE_TAC[FRONTIER_COMPLEMENT] THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(c:real^N->bool) SUBSET t` ASSUME_TAC THENL
   [REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^N->bool) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC FRONTIER_SUBSET_RETRACTION THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
    REWRITE_TAC[retraction] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `r:real^N->real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]];
    FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
    ASM SET_TAC[]]);;

let COMPONENT_RETRACT_COMPLEMENT_MEETS = prove
 (`!s t c. closed s /\ s retract_of t /\ bounded t /\
           c IN components((:real^N) DIFF s)
           ==> ~(c SUBSET t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
  ASM_CASES_TAC `bounded(c:real^N->bool)` THENL
   [ASM_MESON_TAC[BOUNDED_COMPONENT_RETRACT_COMPLEMENT_MEETS];
    ASM_MESON_TAC[BOUNDED_SUBSET]]);;

let FINITE_COMPLEMENT_ENR_COMPONENTS = prove
 (`!s. compact s /\ ENR s ==> FINITE(components((:real^N) DIFF s))`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_SIMP_TAC[DIFF_EMPTY] THEN
    MESON_TAC[COMPONENTS_EQ_SING; CONNECTED_UNIV; UNIV_NOT_EMPTY; FINITE_SING];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[ENR_BOUNDED; COMPACT_IMP_BOUNDED] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!c. c IN components((:real^N) DIFF s) ==> ~(c SUBSET u)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC COMPONENT_RETRACT_COMPLEMENT_MEETS THEN
    ASM_MESON_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `vec 0:real^N`]
        BOUNDED_SUBSET_CBALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
  MP_TAC(ISPECL [`cball(vec 0:real^N,r) DIFF u`; `(:real^N) DIFF s`]
        FINITE_COMPONENTS_MEETING_COMPACT_SUBSET) THEN
  ASM_SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_IMP_LOCALLY_CONNECTED;
     GSYM closed; COMPACT_IMP_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `(!c. c IN s ==> P c) ==> {c | c IN s /\ P c} = s`) THEN
  X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(c INTER frontier(u:real^N->bool) = {})` MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_INTER_FRONTIER THEN
    CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
    ASM_SIMP_TAC[SET_RULE `s DIFF t = {} <=> s SUBSET t`] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    W(MP_TAC o PART_MATCH (rand o rand)
      OPEN_INTER_CLOSURE_EQ_EMPTY o rand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN
    MATCH_MP_TAC(SET_RULE
     `~(t = {}) /\ t SUBSET u
      ==> ~(u INTER (s UNION t) = {})`) THEN
    ASM_REWRITE_TAC[FRONTIER_EQ_EMPTY; DE_MORGAN_THM; GSYM CONJ_ASSOC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]; ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    TRANS_TAC SUBSET_TRANS `frontier((:real^N) DIFF s)` THEN
    ASM_SIMP_TAC[FRONTIER_OF_COMPONENTS_SUBSET] THEN
    REWRITE_TAC[FRONTIER_COMPLEMENT] THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC(SET_RULE `s SUBSET t
      ==> ~(c INTER s = {}) ==> ~(c INTER t = {})`) THEN
    ASM_SIMP_TAC[frontier; INTERIOR_OPEN] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s DIFF u SUBSET t DIFF u`) THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[CLOSED_CBALL]]);;

let FINITE_COMPLEMENT_ANR_COMPONENTS = prove
 (`!s. compact s /\ ANR s ==> FINITE(components((:real^N) DIFF s))`,
  MESON_TAC[FINITE_COMPLEMENT_ENR_COMPONENTS; ENR_ANR;
            COMPACT_IMP_CLOSED; CLOSED_IMP_LOCALLY_COMPACT]);;

let CARD_LE_RETRACT_COMPLEMENT_COMPONENTS = prove
 (`!s t. compact s /\ s retract_of t /\ bounded t
         ==> components((:real^N) DIFF s) <=_c components((:real^N) DIFF t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RETRACT_OF_IMP_SUBSET) THEN
  MATCH_MP_TAC(ISPEC `SUBSET` CARD_LE_RELATIONAL_FULL) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC
     [`d:real^N->bool`; `c:real^N->bool`; `c':real^N->bool`] THEN
    STRIP_TAC THEN MP_TAC(ISPEC `(:real^N) DIFF s` COMPONENTS_EQ) THEN
    ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `d:real^N->bool = {}` THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]] THEN
  X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((u:real^N->bool) SUBSET t)` MP_TAC THENL
   [MATCH_MP_TAC COMPONENT_RETRACT_COMPLEMENT_MEETS THEN
    ASM_MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `~(s SUBSET t) <=> ?p. p IN s /\ ~(p IN t)`] THEN
  REWRITE_TAC[components; EXISTS_IN_GSPEC; IN_UNIV; IN_DIFF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `u = connected_component ((:real^N) DIFF s) p`
  SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`(:real^N) DIFF s`; `u:real^N->bool`]
      COMPONENTS_EQ) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[components; FORALL_IN_GSPEC; IN_DIFF; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `p:real^N` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN REWRITE_TAC[IN] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN ASM SET_TAC[];
    MATCH_MP_TAC CONNECTED_COMPONENT_MONO THEN ASM SET_TAC[]]);;

let CONNECTED_RETRACT_COMPLEMENT = prove
 (`!s t. compact s /\ s retract_of t /\ bounded t /\
         connected((:real^N) DIFF t)
         ==> connected((:real^N) DIFF s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONNECTED_EQ_COMPONENTS_SUBSET_SING_EXISTS] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_TAC `u:real^N->bool`) THEN
  SUBGOAL_THEN `FINITE(components((:real^N) DIFF t))` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_SING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`]
        CARD_LE_RETRACT_COMPLEMENT_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `FINITE(components((:real^N) DIFF s)) /\
    CARD(components((:real^N) DIFF s)) <= CARD(components((:real^N) DIFF t))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CARD_LE_CARD_IMP; CARD_LE_FINITE]; ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `s SUBSET {a} <=> s = {} \/ s = {a}`] THEN
  REWRITE_TAC[EXISTS_OR_THM] THEN
  REWRITE_TAC[GSYM HAS_SIZE_0; GSYM(HAS_SIZE_CONV `s HAS_SIZE 1`)] THEN
  ASM_REWRITE_TAC[HAS_SIZE; ARITH_RULE `n = 0 \/ n = 1 <=> n <= 1`] THEN
  TRANS_TAC LE_TRANS `CARD{u:real^N->bool}` THEN CONJ_TAC THENL
   [TRANS_TAC LE_TRANS `CARD(components((:real^N) DIFF t))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[FINITE_SING];
    SIMP_TAC[CARD_CLAUSES; FINITE_EMPTY; NOT_IN_EMPTY] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* We also get fixpoint properties for suitable ANRs.                        *)
(* ------------------------------------------------------------------------- *)

let BROUWER_INESSENTIAL_ANR = prove
 (`!f:real^N->real^N s.
        compact s /\ ~(s = {}) /\ ANR s /\
        f continuous_on s /\ IMAGE f s SUBSET s /\
        (?a. homotopic_with (\x. T)
              (subtopology euclidean s,subtopology euclidean s) f (\x. a))
        ==> ?x. x IN s /\ f x = x`,
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `r:real` o SPEC `vec 0:real^N` o
    MATCH_MP BOUNDED_SUBSET_CBALL o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  MP_TAC(ISPECL
   [`(\x. a):real^N->real^N`; `f:real^N->real^N`;
    `s:real^N->bool`; `cball(vec 0:real^N,r)`; `s:real^N->bool`]
    BORSUK_HOMOTOPY_EXTENSION) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_SUBSET;
               CONTINUOUS_ON_CONST; CLOSED_CBALL] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real^N->real^N`; `cball(vec 0:real^N,r)`]
        BROUWER) THEN
  ASM_SIMP_TAC[COMPACT_CBALL; CONVEX_CBALL; CBALL_EQ_EMPTY] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> ~(r < &0)`] THEN ASM SET_TAC[]);;

let BROUWER_CONTRACTIBLE_ANR = prove
 (`!f:real^N->real^N s.
        compact s /\ contractible s /\ ~(s = {}) /\ ANR s /\
        f continuous_on s /\ IMAGE f s SUBSET s
        ==> ?x. x IN s /\ f x = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BROUWER_INESSENTIAL_ANR THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NULLHOMOTOPIC_FROM_CONTRACTIBLE THEN ASM_REWRITE_TAC[]);;

let FIXED_POINT_INESSENTIAL_SPHERE_MAP = prove
 (`!f a:real^N r c.
     &0 < r /\
     homotopic_with (\x. T)
      (subtopology euclidean (sphere(a,r)),
       subtopology euclidean (sphere(a,r))) f (\x. c)
     ==> ?x. x IN sphere(a,r) /\ f x = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BROUWER_INESSENTIAL_ANR THEN
  REWRITE_TAC[ANR_SPHERE] THEN
  ASM_SIMP_TAC[SPHERE_EQ_EMPTY; COMPACT_SPHERE; OPEN_DELETE; OPEN_UNIV] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  ASM_SIMP_TAC[REAL_NOT_LT; REAL_LT_IMP_LE] THEN ASM_MESON_TAC[]);;

let BROUWER_AR = prove
 (`!f s:real^N->bool.
        compact s /\ AR s /\ f continuous_on s /\ IMAGE f s SUBSET s
         ==> ?x. x IN s /\ f x = x`,
  REWRITE_TAC[AR_ANR] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BROUWER_CONTRACTIBLE_ANR THEN
  ASM_REWRITE_TAC[]);;

let BROUWER_ABSOLUTE_RETRACT = prove
 (`!f s. compact s /\ s retract_of (:real^N) /\
         f continuous_on s /\ IMAGE f s SUBSET s
         ==> ?x. x IN s /\ f x = x`,
  REWRITE_TAC[RETRACT_OF_UNIV; AR_ANR] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BROUWER_CONTRACTIBLE_ANR THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* This interesting lemma is no longer used for Schauder but we keep it.     *)
(* ------------------------------------------------------------------------- *)

let SCHAUDER_PROJECTION = prove
 (`!s:real^N->bool e.
        compact s /\ &0 < e
        ==> ?t f. FINITE t /\ t SUBSET s /\
                  f continuous_on s /\ IMAGE f s SUBSET (convex hull t) /\
                  (!x. x IN s ==> norm(f x - x) < e)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC o SPEC `e:real` o MATCH_MP COMPACT_IMP_TOTALLY_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `g = \p x:real^N. max (&0) (e - norm(x - p))` THEN
  SUBGOAL_THEN
   `!x. x IN s ==> &0 < sum t (\p. (g:real^N->real^N->real) p x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LT THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "g" THEN
    REWRITE_TAC[REAL_ARITH `&0 <= max (&0) b`] THEN
    REWRITE_TAC[REAL_ARITH `&0 < max (&0) b <=> &0 < b`; REAL_SUB_LT] THEN
    UNDISCH_TAC `s SUBSET UNIONS (IMAGE (\x:real^N. ball(x,e)) t)` THEN
    REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_BALL; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[dist; NORM_SUB];
    ALL_TAC] THEN
  EXISTS_TAC
   `(\x. inv(sum t (\p. g p x)) % vsum t (\p. g p x % p)):real^N->real^N` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ; LIFT_SUM; o_DEF];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THENL
     [ALL_TAC; MATCH_MP_TAC CONTINUOUS_ON_MUL] THEN
    REWRITE_TAC[o_DEF; CONTINUOUS_ON_CONST] THEN
    EXPAND_TAC "g" THEN
    (SUBGOAL_THEN
      `(\x. lift (max (&0) (e - norm (x - y:real^N)))) =
       (\x. (lambda i. max (lift(&0)$i) (lift(e - norm (x - y))$i)))`
     SUBST1_TAC THENL
      [SIMP_TAC[CART_EQ; LAMBDA_BETA; FUN_EQ_THM] THEN
       REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop; LIFT_DROP];
       MATCH_MP_TAC CONTINUOUS_ON_MAX] THEN
     REWRITE_TAC[CONTINUOUS_ON_CONST; LIFT_SUB] THEN
     MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
     REWRITE_TAC[ONCE_REWRITE_RULE[NORM_SUB] (GSYM dist)] THEN
     REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_DIST]);
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GSYM VSUM_LMUL; VECTOR_MUL_ASSOC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC CONVEX_VSUM THEN
    ASM_SIMP_TAC[HULL_INC; CONVEX_CONVEX_HULL; SUM_LMUL] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_MUL_LINV] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    EXPAND_TAC "g" THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    REWRITE_TAC[REWRITE_RULE[dist] (GSYM IN_BALL)] THEN
    REWRITE_TAC[GSYM VSUM_LMUL; VECTOR_MUL_ASSOC] THEN
    MATCH_MP_TAC CONVEX_VSUM_STRONG THEN
    ASM_REWRITE_TAC[CONVEX_BALL; SUM_LMUL; REAL_ENTIRE] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_MUL_LINV; REAL_LT_INV_EQ;
                 REAL_LE_MUL_EQ] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[IN_BALL; dist; NORM_SUB] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Some other related fixed-point theorems.                                  *)
(* ------------------------------------------------------------------------- *)

let BROUWER_FACTOR_THROUGH_AR = prove
 (`!f:real^M->real^N g:real^N->real^M s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET s /\
        compact s /\ AR t
        ==> ?x. x IN s /\ g(f x) = x`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [COMPACT_EQ_BOUNDED_CLOSED]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:real^M` o MATCH_MP BOUNDED_SUBSET_CBALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `(:real^M)`;
                 `s:real^M->bool`; `t:real^N->bool`]
        AR_IMP_ABSOLUTE_EXTENSOR) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(g:real^N->real^M) o (h:real^M->real^N)`;
                 `a:real^M`; `r:real`] BROUWER_BALL) THEN
  ASM_REWRITE_TAC[o_THM; IMAGE_o] THEN
  ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV; IMAGE_SUBSET]);;

let BROUWER_ABSOLUTE_RETRACT_GEN = prove
 (`!f s:real^N->bool.
           s retract_of (:real^N) /\
           f continuous_on s /\ IMAGE f s SUBSET s /\ bounded(IMAGE f s)
           ==> ?x. x IN s /\ f x = x`,
  REWRITE_TAC[RETRACT_OF_UNIV] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. x`; `f:real^N->real^N`;
                 `closure(IMAGE (f:real^N->real^N) s)`; `s:real^N->bool`]
        BROUWER_FACTOR_THROUGH_AR) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; COMPACT_CLOSURE; IMAGE_ID] THEN
  REWRITE_TAC[CLOSURE_SUBSET] THEN
  MATCH_MP_TAC(TAUT `(p /\ q ==> r) /\ p ==> (p ==> q) ==> r`) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC CLOSURE_MINIMAL] THEN
  ASM_MESON_TAC[RETRACT_OF_CLOSED; CLOSED_UNIV]);;

let SCHAUDER_GEN = prove
 (`!f s t:real^N->bool.
     AR s /\ f continuous_on s /\ IMAGE f s SUBSET t /\ t SUBSET s /\ compact t
     ==> ?x. x IN t /\ f x = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. x`; `f:real^N->real^N`;
                 `t:real^N->bool`; `s:real^N->bool`]
        BROUWER_FACTOR_THROUGH_AR) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID]);;

let SCHAUDER = prove
 (`!f s t:real^N->bool.
        convex s /\ ~(s = {}) /\ t SUBSET s /\ compact t /\
        f continuous_on s /\ IMAGE f s SUBSET t
        ==> ?x. x IN s /\ f x = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `s:real^N->bool`; `t:real^N->bool`]
        SCHAUDER_GEN) THEN
  ASM_SIMP_TAC[CONVEX_IMP_AR] THEN ASM SET_TAC[]);;

let SCHAUDER_UNIV = prove
 (`!f:real^N->real^N.
        f continuous_on (:real^N) /\ bounded (IMAGE f (:real^N))
        ==> ?x. f x = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `(:real^N)`;
                 `closure(IMAGE (f:real^N->real^N) (:real^N))`] SCHAUDER) THEN
  ASM_REWRITE_TAC[UNIV_NOT_EMPTY; CONVEX_UNIV; COMPACT_CLOSURE; IN_UNIV] THEN
  REWRITE_TAC[SUBSET_UNIV; CLOSURE_SUBSET]);;

let ROTHE = prove
 (`!f s:real^N->bool.
        closed s /\ convex s /\ ~(s = {}) /\
        f continuous_on s /\ bounded(IMAGE f s) /\
        IMAGE f (frontier s) SUBSET s
        ==> ?x. x IN s /\ f x = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `(:real^N)`]
    ABSOLUTE_RETRACTION_CONVEX_CLOSED) THEN
  ASM_REWRITE_TAC[retraction; SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`(r:real^N->real^N) o (f:real^N->real^N)`; `s:real^N->bool`;
    `IMAGE (r:real^N->real^N) (closure(IMAGE (f:real^N->real^N) s))`]
   SCHAUDER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSURE_SUBSET; IMAGE_SUBSET; IMAGE_o] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[COMPACT_CLOSURE];
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN
    REWRITE_TAC[o_THM] THEN STRIP_TAC THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Perron-Frobenius theorem.                                                 *)
(* ------------------------------------------------------------------------- *)

let PERRON_FROBENIUS = prove
 (`!A:real^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> &0 <= A$i$j)
        ==> ?v c. norm v = &1 /\ &0 <= c /\ A ** v = c % v`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?v. ~(v = vec 0) /\ (A:real^N^N) ** v = vec 0` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `inv(norm v) % v:real^N` THEN EXISTS_TAC `&0` THEN
    ASM_SIMP_TAC[REAL_LE_REFL; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM;
                 REAL_MUL_LINV; NORM_EQ_0; MATRIX_VECTOR_MUL_RMUL] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_RZERO];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    REWRITE_TAC[TAUT `~(~p /\ q) <=> q ==> p`] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`\x:real^N. inv(vec 1 dot (A ** x)) % ((A:real^N^N) ** x)`;
    `{x:real^N | vec 1 dot x = &1} INTER
     {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i}`]
   BROUWER) THEN
  SIMP_TAC[CONVEX_INTER; CONVEX_POSITIVE_ORTHANT; CONVEX_HYPERPLANE] THEN
  SUBGOAL_THEN
   `!x. (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i)
        ==> !i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= ((A:real^N^N) ** x)$i`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN SIMP_TAC[matrix_vector_mul; LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    ASM_MESON_TAC[REAL_LE_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i) /\ vec 1 dot x = &1
        ==> &0 < vec 1 dot ((A:real^N^N) ** x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
    ASM_REWRITE_TAC[DOT_RZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
    DISCH_TAC THEN REWRITE_TAC[dot; VEC_COMPONENT; REAL_MUL_LID] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[];
      DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        SUM_POS_EQ_0_NUMSEG)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[CART_EQ; VEC_COMPONENT]) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_INTER; CLOSED_HYPERPLANE;
               CLOSED_POSITIVE_ORTHANT] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^N,vec 1]` THEN
      SIMP_TAC[BOUNDED_INTERVAL; SUBSET; IN_INTER; IN_ELIM_THM; IN_INTERVAL;
               dot; VEC_COMPONENT; REAL_MUL_LID] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      TRANS_TAC REAL_LE_TRANS `sum {i} (\i. (x:real^N)$i)` THEN
      CONJ_TAC THENL [REWRITE_TAC[SUM_SING; REAL_LE_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_SING; FINITE_NUMSEG] THEN
      ASM_SIMP_TAC[SING_SUBSET; IN_SING; IN_DIFF; IN_NUMSEG];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `basis 1:real^N` THEN
      SIMP_TAC[IN_INTER; IN_ELIM_THM; BASIS_COMPONENT] THEN
      CONJ_TAC THENL [ALL_TAC; MESON_TAC[REAL_POS]] THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_GE_1; LE_REFL; VEC_COMPONENT];
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; MATRIX_VECTOR_MUL_LINEAR; o_DEF] THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
      SIMP_TAC[CONTINUOUS_ON_LIFT_DOT2; MATRIX_VECTOR_MUL_LINEAR;
               CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON] THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      ASM_MESON_TAC[REAL_LT_REFL];
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      REWRITE_TAC[DOT_RMUL] THEN REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
        REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_MESON_TAC[REAL_LT_IMP_LE]]];
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
    ASM_REWRITE_TAC[DOT_RZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    STRIP_TAC THEN EXISTS_TAC `inv(norm x) % x:real^N` THEN
    EXISTS_TAC `vec 1 dot ((A:real^N^N) ** x)` THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
      ASM_MESON_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o AP_TERM
        `(%) (vec 1 dot ((A:real^N^N) ** x)):real^N->real^N`) THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_EQ_0; VECTOR_ARITH
       `v:real^N = c % v <=> (c - &1) % v = vec 0`] THEN
      DISJ1_TAC THEN REWRITE_TAC[REAL_SUB_0] THEN
      MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Bijections between intervals.                                             *)
(* ------------------------------------------------------------------------- *)

let interval_bij = new_definition
 `interval_bij (a:real^N,b:real^N) (u:real^N,v:real^N) (x:real^N) =
    (lambda i. u$i + (x$i - a$i) / (b$i - a$i) * (v$i - u$i)):real^N`;;

let INTERVAL_BIJ_AFFINE = prove
 (`interval_bij (a,b) (u,v) =
        \x. (lambda i. (v$i - u$i) / (b$i - a$i) * x$i) +
            (lambda i. u$i - (v$i - u$i) / (b$i - a$i) * a$i)`,
  SIMP_TAC[FUN_EQ_THM; CART_EQ; VECTOR_ADD_COMPONENT; LAMBDA_BETA;
           interval_bij] THEN
  REAL_ARITH_TAC);;

let CONTINUOUS_INTERVAL_BIJ = prove
 (`!a b u v x. (interval_bij (a:real^N,b:real^N) (u:real^N,v:real^N))
                  continuous at x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INTERVAL_BIJ_AFFINE] THEN
  MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  SIMP_TAC[linear; CART_EQ; LAMBDA_BETA;
           VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let CONTINUOUS_ON_INTERVAL_BIJ = prove
 (`!a b u v s. interval_bij (a,b) (u,v) continuous_on s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REWRITE_TAC[CONTINUOUS_INTERVAL_BIJ]);;

let IN_INTERVAL_INTERVAL_BIJ = prove
 (`!a b u v x:real^N.
        x IN interval[a,b] /\ ~(interval[u,v] = {})
        ==> (interval_bij (a,b) (u,v) x) IN interval[u,v]`,
  SIMP_TAC[IN_INTERVAL; interval_bij; LAMBDA_BETA; INTERVAL_NE_EMPTY] THEN
  REWRITE_TAC[REAL_ARITH `u <= u + x <=> &0 <= x`;
              REAL_ARITH `u + x <= v <=> x <= &1 * (v - u)`] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_DIV) THEN
    ASM_SIMP_TAC[REAL_SUB_LE] THEN ASM_MESON_TAC[REAL_LE_TRANS];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_SUB_LE] THEN
    SUBGOAL_THEN `(a:real^N)$i <= (b:real^N)$i` MP_TAC THENL
     [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN STRIP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN
      ASM_SIMP_TAC[REAL_ARITH `a <= x /\ x <= b ==> x - a <= &1 * (b - a)`];
      ASM_REWRITE_TAC[real_div; REAL_SUB_REFL; REAL_INV_0] THEN
      REAL_ARITH_TAC]]);;

let INTERVAL_BIJ_BIJ = prove
 (`!a b u v x:real^N.
        (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i /\ u$i < v$i)
        ==> interval_bij (a,b) (u,v) (interval_bij (u,v) (a,b) x) = x`,
  SIMP_TAC[interval_bij; CART_EQ; LAMBDA_BETA; REAL_ADD_SUB] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Fashoda meet theorem.                                                     *)
(* ------------------------------------------------------------------------- *)

let INFNORM_2 = prove
 (`infnorm (x:real^2) = max (abs(x$1)) (abs(x$2))`,
  REWRITE_TAC[infnorm; INFNORM_SET_IMAGE; NUMSEG_CONV `1..2`; DIMINDEX_2] THEN
  REWRITE_TAC[IMAGE_CLAUSES; GSYM REAL_MAX_SUP]);;

let INFNORM_EQ_1_2 = prove
 (`infnorm (x:real^2) = &1 <=>
        abs(x$1) <= &1 /\ abs(x$2) <= &1 /\
        (x$1 = -- &1 \/ x$1 = &1 \/ x$2 = -- &1 \/ x$2 = &1)`,
  REWRITE_TAC[INFNORM_2] THEN REAL_ARITH_TAC);;

let INFNORM_EQ_1_IMP = prove
 (`infnorm (x:real^2) = &1 ==> abs(x$1) <= &1 /\ abs(x$2) <= &1`,
  SIMP_TAC[INFNORM_EQ_1_2]);;

let FASHODA_UNIT = prove
 (`!f:real^1->real^2 g:real^1->real^2.
        IMAGE f (interval[--vec 1,vec 1]) SUBSET interval[--vec 1,vec 1] /\
        IMAGE g (interval[--vec 1,vec 1]) SUBSET interval[--vec 1,vec 1] /\
        f continuous_on interval[--vec 1,vec 1] /\
        g continuous_on interval[--vec 1,vec 1] /\
        f(--vec 1)$1 = -- &1 /\ f(vec 1)$1 = &1 /\
        g(--vec 1)$2 = -- &1 /\ g(vec 1)$2 = &1
        ==> ?s t. s IN interval[--vec 1,vec 1] /\
                  t IN interval[--vec 1,vec 1] /\
                  f(s) = g(t)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN DISCH_TAC THEN
  ABBREV_TAC `sqprojection = \z:real^2. inv(infnorm z) % z` THEN
  ABBREV_TAC `(negatex:real^2->real^2) = \x. vector[--(x$1); x$2]` THEN
  SUBGOAL_THEN `!z:real^2. infnorm(negatex z:real^2) = infnorm z` ASSUME_TAC
  THENL
   [EXPAND_TAC "negatex" THEN SIMP_TAC[VECTOR_2; INFNORM_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. ~(z = vec 0) ==> infnorm((sqprojection:real^2->real^2) z) = &1`
  ASSUME_TAC THENL
   [EXPAND_TAC "sqprojection" THEN
    REWRITE_TAC[INFNORM_MUL; REAL_ABS_INFNORM; REAL_ABS_INV] THEN
    SIMP_TAC[REAL_MUL_LINV; INFNORM_EQ_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(\w. (negatex:real^2->real^2)
                       (sqprojection(f(lift(w$1)) - g(lift(w$2)):real^2)))
                  :real^2->real^2`;
                 `interval[--vec 1,vec 1]:real^2->bool`]
         BROUWER_WEAK) THEN
  REWRITE_TAC[NOT_IMP; COMPACT_INTERVAL; CONVEX_INTERVAL] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY] THEN
    SIMP_TAC[VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN EXPAND_TAC "negatex" THEN
      SIMP_TAC[linear; VECTOR_2; CART_EQ; FORALL_2; DIMINDEX_2;
               VECTOR_MUL_COMPONENT; VECTOR_NEG_COMPONENT;
               VECTOR_ADD_COMPONENT; ARITH] THEN
      REAL_ARITH_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
      SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[--vec 1:real^1,vec 1]`;
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      EXPAND_TAC "sqprojection" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      MATCH_MP_TAC CONTINUOUS_MUL THEN REWRITE_TAC[CONTINUOUS_AT_ID] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_AT_INV THEN
      REWRITE_TAC[CONTINUOUS_AT_LIFT_INFNORM; INFNORM_EQ_0; VECTOR_SUB_EQ] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL])] THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1] THEN
    SIMP_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT; ARITH;
             VECTOR_NEG_COMPONENT; DROP_NEG; DROP_VEC; LIFT_DROP];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    SIMP_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; REAL_BOUNDS_LE;
             VECTOR_NEG_COMPONENT; VEC_COMPONENT; ARITH] THEN
    MATCH_MP_TAC INFNORM_EQ_1_IMP THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL]) THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1] THEN
    SIMP_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT; ARITH;
             VECTOR_NEG_COMPONENT; DROP_NEG; DROP_VEC; LIFT_DROP];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `infnorm(x:real^2) = &1` MP_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
     [SYM th]) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL]) THEN
    SIMP_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT; ARITH;
             VECTOR_NEG_COMPONENT; DROP_NEG; DROP_VEC; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x i. 1 <= i /\ i <= 2 /\ ~(x = vec 0)
           ==> (&0 < ((sqprojection:real^2->real^2) x)$i <=> &0 < x$i)) /\
    (!x i. 1 <= i /\ i <= 2 /\ ~(x = vec 0)
           ==> ((sqprojection x)$i < &0 <=> x$i < &0))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sqprojection" THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div)] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; INFNORM_POS_LT] THEN
    REWRITE_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  REWRITE_TAC[INFNORM_EQ_1_2; CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
   (REPEAT_TCL DISJ_CASES_THEN (fun th -> ASSUME_TAC th THEN MP_TAC th))) THEN
  MAP_EVERY EXPAND_TAC ["x"; "negatex"] THEN REWRITE_TAC[VECTOR_2] THENL
   [DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `--x = -- &1 ==> &0 < x`));
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `--x = &1 ==> x < &0`));
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `x = -- &1 ==> x < &0`));
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `x = &1 ==> &0 < x`))] THEN
  W(fun (_,w) -> FIRST_X_ASSUM(fun th ->
   MP_TAC(PART_MATCH (lhs o rand) th (lhand w)))) THEN
  (ANTS_TAC THENL
    [REWRITE_TAC[VECTOR_SUB_EQ; ARITH] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL]) THEN
     ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1] THEN
     SIMP_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT; ARITH;
              VECTOR_NEG_COMPONENT; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
     REAL_ARITH_TAC;
     DISCH_THEN SUBST1_TAC]) THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; DIMINDEX_2; ARITH;
               LIFT_NEG; LIFT_NUM]
  THENL
   [MATCH_MP_TAC(REAL_ARITH
     `abs(x$1) <= &1 /\ abs(x$2) <= &1 ==> ~(&0 < -- &1 - x$1)`);
    MATCH_MP_TAC(REAL_ARITH
     `abs(x$1) <= &1 /\ abs(x$2) <= &1 ==> ~(&1 - x$1 < &0)`);
    MATCH_MP_TAC(REAL_ARITH
     `abs(x$1) <= &1 /\ abs(x$2) <= &1 ==> ~(x$2 - -- &1 < &0)`);
    MATCH_MP_TAC(REAL_ARITH
     `abs(x$1) <= &1 /\ abs(x$2) <= &1 ==> ~(&0 < x$2 - &1)`)] THEN
  (SUBGOAL_THEN `!z:real^2. abs(z$1) <= &1 /\ abs(z$2) <= &1 <=>
                           z IN interval[--vec 1,vec 1]`
    (fun th -> REWRITE_TAC[th]) THENL
    [SIMP_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VEC_COMPONENT; ARITH;
              VECTOR_NEG_COMPONENT; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
     REAL_ARITH_TAC;
     ALL_TAC]) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `IMAGE f s SUBSET t ==> x IN s ==> f x IN t`)) THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
  ASM_REWRITE_TAC[REAL_BOUNDS_LE]);;

let FASHODA_UNIT_PATH = prove
 (`!f:real^1->real^2 g:real^1->real^2.
        path f /\ path g /\
        path_image f SUBSET interval[--vec 1,vec 1] /\
        path_image g SUBSET interval[--vec 1,vec 1] /\
        (pathstart f)$1 = -- &1 /\ (pathfinish f)$1 = &1 /\
        (pathstart g)$2 = -- &1 /\ (pathfinish g)$2 = &1
        ==> ?z. z IN path_image f /\ z IN path_image g`,
  SIMP_TAC[path; path_image; pathstart; pathfinish] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `iscale = \z:real^1. inv(&2) % (z + vec 1)` THEN
  MP_TAC(ISPECL
   [`(f:real^1->real^2) o (iscale:real^1->real^1)`;
    `(g:real^1->real^2) o (iscale:real^1->real^1)`]
   FASHODA_UNIT) THEN
  SUBGOAL_THEN
   `IMAGE (iscale:real^1->real^1) (interval[--vec 1,vec 1])
    SUBSET interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN EXPAND_TAC "iscale" THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; DROP_VEC; DROP_CMUL; DROP_ADD] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(iscale:real^1->real^1) continuous_on interval [--vec 1,vec 1]`
  ASSUME_TAC THENL
   [EXPAND_TAC "iscale" THEN
    SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID; CONTINUOUS_ON_ADD;
             CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN ANTS_TAC THENL
   [REPLICATE_TAC 2 (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ALL_TAC]) THEN
    EXPAND_TAC "iscale" THEN REWRITE_TAC[o_THM] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `inv(&2) % (--x + x) = vec 0`;
                    VECTOR_ARITH `inv(&2) % (x + x) = x`];
    REWRITE_TAC[o_THM; LEFT_IMP_EXISTS_THM; IN_IMAGE] THEN ASM SET_TAC[]]);;

let FASHODA = prove
 (`!f g a b:real^2.
        path f /\ path g /\
        path_image f SUBSET interval[a,b] /\
        path_image g SUBSET interval[a,b] /\
        (pathstart f)$1 = a$1 /\ (pathfinish f)$1 = b$1 /\
        (pathstart g)$2 = a$2 /\ (pathfinish g)$2 = b$2
        ==> ?z. z IN path_image f /\ z IN path_image g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(interval[a:real^2,b] = {})` MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(s = {}) ==> ~(t = {})`)) THEN
    REWRITE_TAC[PATH_IMAGE_NONEMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `(a:real^2)$1 <= (b:real^2)$1`) THEN
  REWRITE_TAC[REAL_ARITH `a <= b <=> b = a \/ a < b`] THEN STRIP_TAC THENL
   [SUBGOAL_THEN
      `?z:real^2. z IN path_image g /\ z$2 = (pathstart f:real^2)$2`
    MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_IVT_COMPONENT THEN
      MAP_EVERY EXISTS_TAC [`pathstart(g:real^1->real^2)`;
                            `pathfinish(g:real^1->real^2)`] THEN
      ASM_SIMP_TAC[CONNECTED_PATH_IMAGE; PATHSTART_IN_PATH_IMAGE; REAL_LE_REFL;
                   PATHFINISH_IN_PATH_IMAGE; DIMINDEX_2; ARITH] THEN
      UNDISCH_TAC `path_image f SUBSET interval[a:real^2,b]` THEN
      REWRITE_TAC[SUBSET; path_image; IN_INTERVAL_1; FORALL_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `vec 0:real^1`) THEN SIMP_TAC[pathstart] THEN
      SIMP_TAC[DROP_VEC; REAL_POS; IN_INTERVAL; FORALL_2; DIMINDEX_2];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^2` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[path_image; IN_IMAGE] THEN
    EXISTS_TAC `vec 0:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS] THEN
    ASM_REWRITE_TAC[CART_EQ; FORALL_2; DIMINDEX_2; pathstart] THEN
    SUBGOAL_THEN
     `(z:real^2) IN interval[a,b] /\ f(vec 0:real^1) IN interval[a,b]`
    MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; path_image; IN_IMAGE; PATHSTART_IN_PATH_IMAGE;
                    pathstart];
      ASM_REWRITE_TAC[IN_INTERVAL; FORALL_2; DIMINDEX_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ASSUME `(a:real^2)$2 <= (b:real^2)$2`) THEN
  REWRITE_TAC[REAL_ARITH `a <= b <=> b = a \/ a < b`] THEN STRIP_TAC THENL
   [SUBGOAL_THEN
      `?z:real^2. z IN path_image f /\ z$1 = (pathstart g:real^2)$1`
    MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_IVT_COMPONENT THEN
      MAP_EVERY EXISTS_TAC [`pathstart(f:real^1->real^2)`;
                            `pathfinish(f:real^1->real^2)`] THEN
      ASM_SIMP_TAC[CONNECTED_PATH_IMAGE; PATHSTART_IN_PATH_IMAGE; REAL_LE_REFL;
                   PATHFINISH_IN_PATH_IMAGE; DIMINDEX_2; ARITH] THEN
      UNDISCH_TAC `path_image g SUBSET interval[a:real^2,b]` THEN
      REWRITE_TAC[SUBSET; path_image; IN_INTERVAL_1; FORALL_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `vec 0:real^1`) THEN SIMP_TAC[pathstart] THEN
      SIMP_TAC[DROP_VEC; REAL_POS; IN_INTERVAL; FORALL_2; DIMINDEX_2];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^2` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[path_image; IN_IMAGE] THEN
    EXISTS_TAC `vec 0:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS] THEN
    ASM_REWRITE_TAC[CART_EQ; FORALL_2; DIMINDEX_2; pathstart] THEN
    SUBGOAL_THEN
     `(z:real^2) IN interval[a,b] /\ g(vec 0:real^1) IN interval[a,b]`
    MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; path_image; IN_IMAGE; PATHSTART_IN_PATH_IMAGE;
                    pathstart];
      ASM_REWRITE_TAC[IN_INTERVAL; FORALL_2; DIMINDEX_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`interval_bij (a,b) (--vec 1,vec 1) o (f:real^1->real^2)`;
    `interval_bij (a,b) (--vec 1,vec 1) o (g:real^1->real^2)`]
   FASHODA_UNIT_PATH) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[path; path_image; pathstart; pathfinish]) THEN
  ASM_REWRITE_TAC[path; path_image; pathstart; pathfinish; o_THM] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONTINUOUS_ON_COMPOSE; CONTINUOUS_ON_INTERVAL_BIJ] THEN
    REWRITE_TAC[IMAGE_o] THEN REPLICATE_TAC 2 (CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN ONCE_REWRITE_TAC[FORALL_IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_INTERVAL_INTERVAL_BIJ THEN
      SIMP_TAC[INTERVAL_NE_EMPTY; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM SET_TAC[];
      ALL_TAC]) THEN
    ASM_SIMP_TAC[interval_bij; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; REAL_SUB_LT] THEN
    REWRITE_TAC[real_div; REAL_SUB_REFL; REAL_MUL_LZERO] THEN
    SIMP_TAC[VECTOR_NEG_COMPONENT; VEC_COMPONENT; DIMINDEX_2; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^2`
   (fun th -> EXISTS_TAC `interval_bij (--vec 1,vec 1) (a,b) (z:real^2)` THEN
              MP_TAC th)) THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN REWRITE_TAC[IMAGE_o] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> g(f(x)) = x) ==> x IN IMAGE f s ==> g x IN s`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERVAL_BIJ_BIJ THEN
  ASM_SIMP_TAC[FORALL_2; DIMINDEX_2; VECTOR_NEG_COMPONENT; VEC_COMPONENT;
               ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Some slightly ad hoc lemmas I use below                                   *)
(* ------------------------------------------------------------------------- *)

let SEGMENT_VERTICAL = prove
 (`!a:real^2 b:real^2 x:real^2.
      a$1 = b$1
      ==> (x IN segment[a,b] <=>
           x$1 = a$1 /\ x$1 = b$1 /\
           (a$2 <= x$2 /\ x$2 <= b$2 \/ b$2 <= x$2 /\ x$2 <= a$2))`,
  GEOM_ORIGIN_TAC `a:real^2` THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VEC_COMPONENT; REAL_LE_LADD;
              REAL_EQ_ADD_LCANCEL] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBST1_TAC(SYM(ISPEC `b:real^2` BASIS_EXPANSION)) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; VSUM_2; VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
  SUBST1_TAC(VECTOR_ARITH `vec 0:real^2 = &0 % basis 2`) THEN
  REWRITE_TAC[SEGMENT_SCALAR_MULTIPLE; IN_ELIM_THM; CART_EQ] THEN
  REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH;
           REAL_MUL_RZERO; REAL_MUL_RID] THEN MESON_TAC[]);;

let SEGMENT_HORIZONTAL = prove
 (`!a:real^2 b:real^2 x:real^2.
      a$2 = b$2
      ==> (x IN segment[a,b] <=>
           x$2 = a$2 /\ x$2 = b$2 /\
           (a$1 <= x$1 /\ x$1 <= b$1 \/ b$1 <= x$1 /\ x$1 <= a$1))`,
  GEOM_ORIGIN_TAC `a:real^2` THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VEC_COMPONENT; REAL_LE_LADD;
              REAL_EQ_ADD_LCANCEL] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBST1_TAC(SYM(ISPEC `b:real^2` BASIS_EXPANSION)) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; VSUM_2; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  SUBST1_TAC(VECTOR_ARITH `vec 0:real^2 = &0 % basis 1`) THEN
  REWRITE_TAC[SEGMENT_SCALAR_MULTIPLE; IN_ELIM_THM; CART_EQ] THEN
  REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH;
           REAL_MUL_RZERO; REAL_MUL_RID] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Useful Fashoda corollary pointed out to me by Tom Hales.                  *)
(* ------------------------------------------------------------------------- *)

let FASHODA_INTERLACE = prove
 (`!f g a b:real^2.
        path f /\ path g /\
        path_image f SUBSET interval[a,b] /\
        path_image g SUBSET interval[a,b] /\
        (pathstart f)$2 = a$2 /\ (pathfinish f)$2 = a$2 /\
        (pathstart g)$2 = a$2 /\ (pathfinish g)$2 = a$2 /\
        (pathstart f)$1 < (pathstart g)$1 /\
        (pathstart g)$1 < (pathfinish f)$1 /\
        (pathfinish f)$1 < (pathfinish g)$1
        ==> ?z. z IN path_image f /\ z IN path_image g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(interval[a:real^2,b] = {})` MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(s = {}) ==> ~(t = {})`)) THEN
    REWRITE_TAC[PATH_IMAGE_NONEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pathstart (f:real^1->real^2) IN interval[a,b] /\
    pathfinish f IN interval[a,b] /\
    pathstart g IN interval[a,b] /\
    pathfinish g IN interval[a,b]`
  MP_TAC THENL
   [ASM_MESON_TAC[SUBSET; PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
    ALL_TAC] THEN
  REWRITE_TAC[INTERVAL_NE_EMPTY; IN_INTERVAL; FORALL_2; DIMINDEX_2] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL
   [`linepath(vector[a$1 - &2;a$2 - &2],vector[(pathstart f)$1;a$2 - &2]) ++
     linepath(vector[(pathstart f)$1;(a:real^2)$2 - &2],pathstart f) ++
     (f:real^1->real^2) ++
     linepath(pathfinish f,vector[(pathfinish f)$1;a$2 - &2]) ++
     linepath(vector[(pathfinish f)$1;a$2 - &2],
              vector[(b:real^2)$1 + &2;a$2 - &2])`;
    `linepath(vector[(pathstart g)$1; (pathstart g)$2 - &3],pathstart g) ++
     (g:real^1->real^2) ++
     linepath(pathfinish g,vector[(pathfinish g)$1;(a:real^2)$2 - &1]) ++
     linepath(vector[(pathfinish g)$1;a$2 - &1],vector[b$1 + &1;a$2 - &1]) ++
     linepath(vector[b$1 + &1;a$2 - &1],vector[(b:real^2)$1 + &1;b$2 + &3])`;
    `vector[(a:real^2)$1 - &2; a$2 - &3]:real^2`;
    `vector[(b:real^2)$1 + &2; b$2 + &3]:real^2`]
   FASHODA) THEN
  ASM_SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN;
               PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_LINEPATH] THEN
  REWRITE_TAC[VECTOR_2] THEN ANTS_TAC THENL
   [CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC
            (SET_RULE `s SUBSET u /\ t SUBSET u ==> (s UNION t) SUBSET u`) THEN
           CONJ_TAC) THEN
    TRY(REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
        MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT]
           (CONJUNCT1 (SPEC_ALL CONVEX_INTERVAL))) THEN
        ASM_REWRITE_TAC[IN_INTERVAL; FORALL_2; DIMINDEX_2; VECTOR_2] THEN
        ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interval[a:real^2,b:real^2]` THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET_INTERVAL; FORALL_2; DIMINDEX_2; VECTOR_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^2` THEN
  REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
  SUBGOAL_THEN
   `!f s:real^2->bool. path_image f UNION s =
                       path_image f UNION (s DIFF {pathstart f,pathfinish f})`
   (fun th -> ONCE_REWRITE_TAC[th] THEN
              REWRITE_TAC[GSYM UNION_ASSOC] THEN
              ONCE_REWRITE_TAC[SET_RULE `(s UNION t) UNION u =
                                         u UNION t UNION s`] THEN
              ONCE_REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNION; IN_DIFF; GSYM DISJ_ASSOC; LEFT_OR_DISTRIB;
              RIGHT_OR_DISTRIB; GSYM CONJ_ASSOC;
              SET_RULE `~(z IN {x,y}) <=> ~(z = x) /\ ~(z = y)`] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN MP_TAC) THEN
  ASM_SIMP_TAC[SEGMENT_VERTICAL; SEGMENT_HORIZONTAL; VECTOR_2] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `path_image (f:real^1->real^2) SUBSET interval [a,b]` THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
  UNDISCH_TAC `path_image (g:real^1->real^2) SUBSET interval [a,b]` THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
  ASM_REWRITE_TAC[IN_INTERVAL; FORALL_2; DIMINDEX_2] THEN
  REPEAT(DISCH_THEN(fun th -> if is_imp(concl th) then ALL_TAC else
    ASSUME_TAC th)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN TRY REAL_ARITH_TAC THEN
  REWRITE_TAC[CART_EQ; FORALL_2; DIMINDEX_2] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Complement in dimension N >= 2 of set homeomorphic to any interval in     *)
(* any dimension is (path-)connected. This naively generalizes the argument  *)
(* in Ryuji Maehara's paper "The Jordan curve theorem via the Brouwer        *)
(* fixed point theorem", American Mathematical Monthly 1984.                 *)
(* ------------------------------------------------------------------------- *)

let UNBOUNDED_COMPONENTS_COMPLEMENT_ABSOLUTE_RETRACT = prove
 (`!s c. compact s /\ AR s /\ c IN components((:real^N) DIFF s)
         ==> ~bounded c`,
  REWRITE_TAC[CONJ_ASSOC; COMPACT_AR] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; components; FORALL_IN_GSPEC] THEN
  GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open((:real^N) DIFF s)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^N->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`connected_component ((:real^N) DIFF s) y`;
                 `s:real^N->bool`;
                 `r:real^N->real^N`]
                FRONTIER_SUBSET_RETRACTION) THEN
  ASM_SIMP_TAC[NOT_IMP; INTERIOR_OPEN; OPEN_CONNECTED_COMPONENT] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[frontier] THEN
    ASM_SIMP_TAC[INTERIOR_OPEN; OPEN_CONNECTED_COMPONENT] THEN
    REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `z:real^N` THEN
    ASM_CASES_TAC `(z:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[IN_CLOSURE_CONNECTED_COMPONENT; IN_UNIV; IN_DIFF] THEN
    CONV_TAC TAUT;
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ASM SET_TAC[];
    MATCH_MP_TAC(SET_RULE
     `~(c = {}) /\ c SUBSET (:real^N) DIFF s ==> ~(c SUBSET s)`) THEN
    REWRITE_TAC[CONNECTED_COMPONENT_SUBSET; CONNECTED_COMPONENT_EQ_EMPTY] THEN
    ASM_REWRITE_TAC[IN_UNIV; IN_DIFF]]);;

let CONNECTED_COMPLEMENT_ABSOLUTE_RETRACT = prove
 (`!s. 2 <= dimindex(:N) /\ compact s /\ AR s
       ==> connected((:real^N) DIFF s)`,
  REWRITE_TAC[COMPACT_AR] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONNECTED_EQ_CONNECTED_COMPONENT_EQ] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COBOUNDED_UNIQUE_UNBOUNDED_COMPONENT THEN
  ASM_SIMP_TAC[COMPL_COMPL; COMPACT_IMP_BOUNDED] THEN
  CONJ_TAC THEN
  MATCH_MP_TAC UNBOUNDED_COMPONENTS_COMPLEMENT_ABSOLUTE_RETRACT THEN
  EXISTS_TAC `s:real^N->bool` THEN REWRITE_TAC[CONJ_ASSOC; COMPACT_AR] THEN
  ASM_REWRITE_TAC[IN_COMPONENTS] THEN ASM_MESON_TAC[]);;

let PATH_CONNECTED_COMPLEMENT_ABSOLUTE_RETRACT = prove
 (`!s:real^N->bool.
        2 <= dimindex(:N) /\ compact s /\ AR s
        ==> path_connected((:real^N) DIFF s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM
   (MP_TAC o MATCH_MP CONNECTED_COMPLEMENT_ABSOLUTE_RETRACT) THEN
  MATCH_MP_TAC EQ_IMP THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC PATH_CONNECTED_EQ_CONNECTED THEN
  REWRITE_TAC[GSYM closed] THEN
  ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_INTERVAL;
                COMPACT_IMP_CLOSED]);;

let CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT = prove
 (`!s:real^N->bool t:real^M->bool.
        2 <= dimindex(:N) /\ s homeomorphic t /\ convex t /\ compact t
        ==> connected((:real^N) DIFF s)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[DIFF_EMPTY; CONNECTED_UNIV] THEN
  MATCH_MP_TAC CONNECTED_COMPLEMENT_ABSOLUTE_RETRACT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_ARNESS) THEN
  ASM_MESON_TAC[CONVEX_IMP_AR; HOMEOMORPHIC_EMPTY]);;

let PATH_CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT = prove
 (`!s:real^N->bool t:real^M->bool.
        2 <= dimindex(:N) /\ s homeomorphic t /\ convex t /\ compact t
        ==> path_connected((:real^N) DIFF s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM
   (MP_TAC o MATCH_MP CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT) THEN
  MATCH_MP_TAC EQ_IMP THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC PATH_CONNECTED_EQ_CONNECTED THEN
  REWRITE_TAC[GSYM closed] THEN
  ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_INTERVAL;
                COMPACT_IMP_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* In particular, apply all these to the special case of an arc.             *)
(* ------------------------------------------------------------------------- *)

let RETRACTION_ARC = prove
 (`!p. arc p
       ==> ?f. f continuous_on (:real^N) /\
               IMAGE f (:real^N) SUBSET path_image p /\
               (!x. x IN path_image p ==> f x = x)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(:real^N)` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        ABSOLUTE_RETRACT_PATH_IMAGE_ARC)) THEN
  REWRITE_TAC[SUBSET_UNIV; retract_of; retraction]);;

let PATH_CONNECTED_ARC_COMPLEMENT = prove
 (`!p. 2 <= dimindex(:N) /\ arc p
       ==> path_connected((:real^N) DIFF path_image p)`,
  REWRITE_TAC[arc; path] THEN REPEAT STRIP_TAC THEN SIMP_TAC[path_image] THEN
  MP_TAC(ISPECL [`path_image p:real^N->bool`; `interval[vec 0:real^1,vec 1]`]
        PATH_CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT) THEN
  ASM_REWRITE_TAC[CONVEX_INTERVAL; COMPACT_INTERVAL; path_image] THEN
  DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN
  EXISTS_TAC `p:real^1->real^N` THEN ASM_REWRITE_TAC[COMPACT_INTERVAL]);;

let CONNECTED_ARC_COMPLEMENT = prove
 (`!p. 2 <= dimindex(:N) /\ arc p
       ==> connected((:real^N) DIFF path_image p)`,
  SIMP_TAC[PATH_CONNECTED_ARC_COMPLEMENT; PATH_CONNECTED_IMP_CONNECTED]);;

let INSIDE_ARC_EMPTY = prove
 (`!p:real^1->real^N. arc p ==> inside(path_image p) = {}`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `dimindex(:N) = 1` THENL
   [MATCH_MP_TAC INSIDE_CONVEX THEN
    ASM_SIMP_TAC[CONVEX_CONNECTED_1_GEN; CONNECTED_PATH_IMAGE; ARC_IMP_PATH];
    MATCH_MP_TAC INSIDE_BOUNDED_COMPLEMENT_CONNECTED_EMPTY THEN
    ASM_SIMP_TAC[BOUNDED_PATH_IMAGE; ARC_IMP_PATH] THEN
    MATCH_MP_TAC CONNECTED_ARC_COMPLEMENT THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 <= n <=> 1 <= n /\ ~(n = 1)`] THEN
    REWRITE_TAC[DIMINDEX_GE_1]]);;

let INSIDE_SIMPLE_CURVE_IMP_CLOSED = prove
 (`!g x:real^N.
        simple_path g /\ x IN inside(path_image g)
        ==> pathfinish g = pathstart g`,
  MESON_TAC[ARC_SIMPLE_PATH; INSIDE_ARC_EMPTY; NOT_IN_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Some nice theorems giving accessibility for ANR complement components     *)
(* (from Hu's "Theory of Retracts", apparently originally from Borsuk).      *)
(* ------------------------------------------------------------------------- *)

let FINITE_ANR_COMPLEMENT_COMPONENTS_CONCENTRIC = prove
 (`!s p:real^N a b.
        compact s /\ ANR s /\ a < b
        ==> FINITE {c | c IN components(cball(p,b) DIFF s) /\
                        ~(closure c INTER cball(p,a) = {})}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `(:real^N)`]
        ANR_IMP_NEIGHBOURHOOD_RETRACT) THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; GSYM CLOSED_IN] THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^N->real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?d. &0 < d /\ {x + e:real^N | x IN s /\ e IN cball(vec 0,d)} SUBSET u /\
        !w. w IN {x + e:real^N | x IN s /\ e IN cball(vec 0,d)}
            ==> dist(w,r w) <= (b - a) / &4`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `?d. &0 < d /\ {x + e:real^N | x IN s /\ e IN cball(vec 0,d)} SUBSET u`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `s:real^N->bool = {}` THEN
      ASM_REWRITE_TAC[SET_RULE `{f x y | x IN {} /\ P y} SUBSET u`] THENL
       [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
      ASM_CASES_TAC `u = (:real^N)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THENL
       [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
      EXISTS_TAC `setdist(s,(:real^N) DIFF u) / &2` THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_HALF; SETDIST_POS_LT] THEN
        ASM_SIMP_TAC[SETDIST_EQ_0_COMPACT_CLOSED; GSYM OPEN_CLOSED] THEN
        ASM SET_TAC[];
        REWRITE_TAC[REAL_HALF; SUBSET; FORALL_IN_GSPEC] THEN DISCH_TAC THEN
        MAP_EVERY X_GEN_TAC [`x:real^N`; `e:real^N`] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[IN_CBALL_0] THEN
        DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
         `&0 < s /\ s <= e ==> ~(e <= s / &2)`) THEN
        ASM_REWRITE_TAC[] THEN
        SUBST1_TAC(NORM_ARITH `norm(e:real^N) = dist(x,x + e)`) THEN
        MATCH_MP_TAC SETDIST_LE_DIST THEN ASM SET_TAC[]];
      SUBGOAL_THEN
       `(r:real^N->real^N) uniformly_continuous_on
        {x + e | x IN s /\ e IN cball(vec 0,d)}`
      MP_TAC THENL
       [MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN
        ASM_SIMP_TAC[COMPACT_SUMS; COMPACT_CBALL] THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        REWRITE_TAC[uniformly_continuous_on]] THEN
      DISCH_THEN(MP_TAC o SPEC `(b - a) / &8`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min d (min (e / &2) ((b - a) / &8))` THEN
      ASM_REWRITE_TAC[REAL_LT_MIN; REAL_HALF] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [REWRITE_TAC[CBALL_MIN_INTER] THEN ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IN_CBALL_0; REAL_LE_MIN] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
      MATCH_MP_TAC(NORM_ARITH
       `dist(r x,r(x + y)) < e / &8 /\ norm y <= e / &8 /\ r x = x
        ==> dist(x + y:real^N,r(x + y)) <= e / &4`) THEN
      REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC[NORM_ARITH
         `&0 < e /\ norm y <= e / &2 ==> dist(x:real^N,x + y) < e`] THEN
        REWRITE_TAC[IN_ELIM_THM; IN_CBALL_0] THEN
        CONJ_TAC THEN EXISTS_TAC `x:real^N` THENL
         [EXISTS_TAC `y:real^N`; EXISTS_TAC `vec 0:real^N`] THEN
        ASM_SIMP_TAC[NORM_0; VECTOR_ADD_RID; REAL_LT_IMP_LE];
        FIRST_ASSUM ACCEPT_TAC;
        ASM_SIMP_TAC[]]];
    ABBREV_TAC `sd = {x + e:real^N | x IN s /\ e IN cball(vec 0,d)}`] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET interior sd` ASSUME_TAC THENL
   [TRANS_TAC SUBSET_TRANS
     `{x + e:real^N | x IN s /\ e IN ball(vec 0,d)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `vec 0 IN t /\ (!x:real^N. f x (vec 0) = x)
        ==> s SUBSET {f x y | x IN s /\ y IN t}`) THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL; VECTOR_ADD_RID];
      SIMP_TAC[INTERIOR_MAXIMAL_EQ; OPEN_SUMS; OPEN_BALL] THEN
      EXPAND_TAC "sd" THEN REWRITE_TAC[GSYM BALL_UNION_SPHERE] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET sd` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS; INTERIOR_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(sd:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "sd" THEN ASM_SIMP_TAC[COMPACT_SUMS; COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {c | c IN components(cball(p:real^N,b) DIFF s) /\
                ~(c INTER (cball(p,b) DIFF interior sd) = {})}`
  MP_TAC THENL
   [MATCH_MP_TAC FINITE_COMPONENTS_MEETING_COMPACT_SUBSET THEN
    REPEAT CONJ_TAC THENL
     [SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_INTERIOR];
      MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN EXISTS_TAC `cball(p:real^N,b)` THEN
      SIMP_TAC[CONVEX_IMP_LOCALLY_CONNECTED; CONVEX_CBALL] THEN
      ASM_SIMP_TAC[OPEN_IN_DIFF_CLOSED; COMPACT_IMP_CLOSED];
      ASM SET_TAC[]];
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `c:real^N->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
    ASM_CASES_TAC `(c:real^N->bool) SUBSET interior sd` THENL
     [DISCH_THEN(K ALL_TAC); ASM SET_TAC[]]] THEN
  SUBGOAL_THEN `closure c SUBSET (sd:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier c SUBSET (sd:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[frontier] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `h = cball(p:real^N,a + &3 / &4 * (b - a))` THEN
  SUBGOAL_THEN `(h:real^N->bool) INTER frontier c SUBSET s` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP FRONTIER_OF_COMPONENTS_SUBSET) THEN
    MATCH_MP_TAC(SET_RULE
      `h INTER g SUBSET s ==> f SUBSET g ==> h INTER f SUBSET s`) THEN
    ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
    W(MP_TAC o PART_MATCH lhand FRONTIER_INTER_SUBSET o
      rand o lhand o snd) THEN
    MATCH_MP_TAC(SET_RULE
      `h INTER g SUBSET s ==> f SUBSET g ==> h INTER f SUBSET s`) THEN
    REWRITE_TAC[FRONTIER_CBALL; UNION_OVER_INTER; UNION_SUBSET] THEN
    REWRITE_TAC[FRONTIER_COMPLEMENT] THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    CONJ_TAC THENL [EXPAND_TAC "h"; SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; IN_CBALL; IN_SPHERE; IN_INTER] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?g. g continuous_on (h UNION frontier c) /\
        (!x. x IN h ==> (g:real^N->real^N) x = vec 0) /\
        (!x. x IN frontier c ==> g x = r x - x)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\x:real^N. if x IN frontier c then r x - x else vec 0` THEN
    SIMP_TAC[] THEN REWRITE_TAC[COND_RAND; COND_RATOR; VECTOR_SUB_EQ] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    GEN_REWRITE_TAC RAND_CONV [UNION_COMM] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN  EXPAND_TAC "h" THEN
    SIMP_TAC[CLOSED_SUBSET_EQ; CLOSED_CBALL; FRONTIER_CLOSED] THEN
    ASM_REWRITE_TAC[VECTOR_SUB_EQ; SUBSET_UNION; CONTINUOUS_ON_CONST] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `D = cball(vec 0:real^N,(b - a) / &4)` THEN
  SUBGOAL_THEN
   `IMAGE (g:real^N->real^N) (h UNION frontier c) SUBSET D`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_UNION; UNION_SUBSET] THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[CENTRE_IN_CBALL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[IN_CBALL_0]] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] (GSYM dist)] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`g:real^N->real^N`; `cball(p:real^N,b)`; `h UNION frontier c:real^N->bool`;
    `D:real^N->bool`]
        AR_IMP_ABSOLUTE_EXTENSOR) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN REWRITE_TAC[AR_CBALL] THEN
  REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CLOSED_SUBSET THEN EXPAND_TAC "h" THEN
    SIMP_TAC[CLOSED_UNION; FRONTIER_CLOSED; CLOSED_CBALL; UNION_SUBSET] THEN
    REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[frontier] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s DIFF u SUBSET t`) THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_CBALL] THEN
    ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `g':real^N->real^N` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `f:real^N->real^N = \x. r x - g' x` THEN
  SUBGOAL_THEN `!x:real^N. x IN frontier c ==> f x = x` (LABEL_TAC "1") THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[IN_UNION] THEN
    REPEAT STRIP_TAC THEN CONV_TAC VECTOR_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN closure c INTER h ==> (f:real^N->real^N) x = r x`
  (LABEL_TAC "2") THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[IN_UNION; IN_INTER] THEN
    REPEAT STRIP_TAC THEN CONV_TAC VECTOR_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN closure c ==> dist(x,f x) <= (b - a) / &2`
  (LABEL_TAC "3") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[] THEN MATCH_MP_TAC(NORM_ARITH
     `dist(x:real^N,r x) <= e / &4 /\ norm(g x) <= e / &4
      ==> dist(x,r x - g x) <= e / &2`) THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; IN_CBALL_0]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `x IN s ==> s SUBSET t ==> x IN t`)) THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_CBALL] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(closure c INTER cball(p:real^N,a) = {})` THEN
  PURE_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSURE_APPROACHABLE]) THEN
  DISCH_THEN(MP_TAC o SPEC `(b - a) / &5`) THEN REWRITE_TAC[NOT_IMP] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `setdist({q},(:real^N) DIFF h) > (b - a) / &2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^N) DIFF h`; `q:real^N`; `l:real^N`]
        SETDIST_SING_TRIANGLE) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `d < (b - a) / &5 ==> &3 / &4 * (b - a) <= l
      ==> abs(q - l) <= d ==> q > (b - a) / &2`)) THEN
    MATCH_MP_TAC REAL_LE_SETDIST THEN REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    REWRITE_TAC[SET_RULE `s DIFF t = {} <=> s SUBSET t`; IN_SING] THEN
    EXPAND_TAC "h" THEN CONJ_TAC THENL
     [MESON_TAC[BOUNDED_SUBSET; NOT_BOUNDED_UNIV; BOUNDED_CBALL];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
      UNDISCH_TAC `l IN cball(p:real^N,a)` THEN
      REWRITE_TAC[IN_DIFF; IN_UNIV; IN_CBALL] THEN CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(q IN IMAGE (f:real^N->real^N) (closure c))`
  (LABEL_TAC "4") THENL
   [REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_CASES_TAC `(x:real^N) IN h` THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "3" (MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `d > e ==> d <= x ==> ~(x <= e)`)) THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN MATCH_MP_TAC SETDIST_LE_DIST THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `closure c:real^N->bool`]
    COMPACT_SUBSET_FRONTIER_RETRACTION) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[COMPACT_CLOSURE] THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `cball(p:real^N,b) DIFF s` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[BOUNDED_DIFF; BOUNDED_CBALL];
    EXPAND_TAC "f" THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET))
    THENL [ASM SET_TAC[]; MATCH_MP_TAC CLOSURE_MINIMAL] THEN
    REWRITE_TAC[CLOSED_CBALL] THEN ASM SET_TAC[];
    MP_TAC(ISPEC `c:real^N->bool` FRONTIER_CLOSURE_SUBSET) THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `q:real^N`) THEN
    ASM_SIMP_TAC[CLOSURE_INC]]);;

let ACCESSIBLE_FRONTIER_ANR_INTER_COMPLEMENT_COMPONENT = prove
 (`!s c p:real^N b.
        compact s /\ ANR s /\
        c IN components(b DIFF s) /\ p IN frontier c /\ p IN interior b
        ==> ?g. arc g /\ pathfinish g = p /\
                !t. t IN interval[vec 0,vec 1] DELETE (vec 1) ==> g(t) IN c`,
  let lemma = prove
   (`!s p:real^N a b c.
          compact s /\ ANR s /\
          &0 < a /\ cball(p,a) SUBSET b /\
          c IN components(b DIFF s) /\
          p IN frontier c
          ==> ?d. d IN components(cball(p,a) INTER c) /\ p IN frontier d`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `p:real^N`; `a / &2`; `a:real`]
          FINITE_ANR_COMPLEMENT_COMPONENTS_CONCENTRIC) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC
     `{d | d IN components(cball(p,a) INTER c) /\
           ~(closure d INTER cball(p:real^N,a / &2) = {})}` o
     MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `d:real^N->bool` THEN
      MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(ISPECL
       [`b DIFF s:real^N->bool`; `cball(p:real^N,a)`;
        `c:real^N->bool`; `d:real^N->bool`] COMPONENTS_INTER_COMPONENTS) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP CLOSURE_UNIONS) THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^N` o MATCH_MP (SET_RULE
     `s = t ==> !x. x IN s ==> x IN t`)) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN
       `p IN closure
         (UNIONS {d | d IN components (cball(p:real^N,a) INTER c) /\
                      ~(closure d INTER cball (p,a / &2) = {})} UNION
          UNIONS {d | d IN components (cball(p,a) INTER c) /\
                      closure d INTER cball (p,a / &2) = {}})`
      MP_TAC THENL
       [REWRITE_TAC[GSYM UNIONS_UNION; GSYM UNIONS_COMPONENTS; SET_RULE
         `{x | x IN s /\ ~P x} UNION {x | x IN s /\ P x} = s`] THEN
        MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ x IN s ==> x IN t`) THEN
        EXISTS_TAC `closure(ball(p:real^N,a) INTER c)` THEN
        SIMP_TAC[SUBSET_CLOSURE; BALL_SUBSET_CBALL; SET_RULE
          `s SUBSET t ==> s INTER c SUBSET t INTER c`] THEN
        W(MP_TAC o PART_MATCH (rand o rand) OPEN_INTER_CLOSURE_SUBSET o
          rand o snd) THEN
        REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC(SET_RULE
         `x IN s ==> s SUBSET t ==> x IN t`) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[frontier; IN_DIFF]) THEN
        ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
        REWRITE_TAC[CLOSURE_UNION; IN_UNION] THEN
        MATCH_MP_TAC(TAUT `~p ==> q \/ p ==> q`) THEN
        MATCH_MP_TAC(SET_RULE
         `!t. ~(x IN t) /\ s SUBSET t ==> ~(x IN s)`) THEN
        EXISTS_TAC `(:real^N) DIFF ball(p,a / &2)` THEN
        ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; CENTRE_IN_BALL; REAL_HALF] THEN
        MATCH_MP_TAC CLOSURE_MINIMAL THEN
        REWRITE_TAC[GSYM OPEN_CLOSED; OPEN_BALL] THEN
        REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
        X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
          `d INTER cball(x:real^N,r) = {} ==> ball(x,r) SUBSET cball(x,r)
                  ==> ball(x,r) INTER d = {}`)) THEN
        SIMP_TAC[BALL_SUBSET_CBALL; OPEN_INTER_CLOSURE_EQ_EMPTY; OPEN_BALL] THEN
        SET_TAC[]];
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^N->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[frontier; IN_DIFF] THEN
      UNDISCH_TAC `(p:real^N) IN frontier c` THEN
      REWRITE_TAC[frontier] THEN MATCH_MP_TAC(SET_RULE
       `d SUBSET c ==> p IN s DIFF c ==> ~(p IN d)`) THEN
      MATCH_MP_TAC SUBSET_INTERIOR THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
      SET_TAC[]]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR_CBALL]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?u. (!n. u n IN
             components(cball(p:real^N,min a (inv(&2 pow n))) INTER c) /\
             p IN frontier(u n)) /\
        (!n. u(SUC n) SUBSET u n)`
  MP_TAC THENL
   [MATCH_MP_TAC DEPENDENT_CHOICE THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN MP_TAC(ISPECL
       [`s:real^N->bool`; `p:real^N`; `min a (&1)`; `b:real^N->bool`;
        `c:real^N->bool`] lemma) THEN
      ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[CBALL_MIN_INTER] THEN ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`n:num`; `d:real^N->bool`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL
       [`s:real^N->bool`; `p:real^N`;
        `min a (inv(&2 pow (SUC n)))`; `cball(p:real^N,min a (inv(&2 pow n)))`;
        `d:real^N->bool`] lemma) THEN
      ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_LT_POW2; REAL_LT_MIN] THEN
      SIMP_TAC[REAL_LT_INV2; REAL_LT_INV_EQ; REAL_LT_POW2; REAL_POW_MONO_LT;
               REAL_ARITH `&1 < &2`; ARITH_RULE `n < SUC n`; SUBSET_BALLS;
               DIST_REFL; REAL_ADD_LID;
               REAL_ARITH `x < y ==> min a x <= min a y`] THEN
      ANTS_TAC THENL
       [MP_TAC(ISPECL
         [`b DIFF s:real^N->bool`;
          `cball(p:real^N,min a (inv(&2 pow n)))`;
          `c:real^N->bool`; `d:real^N->bool`]
         COMPONENTS_INTER_COMPONENTS) THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[CBALL_MIN_INTER] THEN ASM SET_TAC[];
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real^N->bool` THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
         [MP_TAC(ISPECL
           [`cball(p:real^N,min a (inv(&2 pow n))) INTER c`;
            `cball(p:real^N,min a (inv(&2 pow SUC n)))`;
            `d:real^N->bool`; `e:real^N->bool`]
           COMPONENTS_INTER_COMPONENTS) THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN
          REWRITE_TAC[CBALL_MIN_INTER] THEN MATCH_MP_TAC(SET_RULE
           `n SUBSET s
            ==> (b INTER n) INTER (b INTER s) INTER c =
                (b INTER n) INTER c`) THEN
          MATCH_MP_TAC SUBSET_CBALL THEN
          MATCH_MP_TAC REAL_LE_INV2 THEN
          REWRITE_TAC[REAL_LT_POW2] THEN MATCH_MP_TAC REAL_POW_MONO THEN
          REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
          REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
          ASM SET_TAC[]]]];
    REWRITE_TAC[FORALL_AND_THM; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `u:num->real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. (u:num->real^N->bool) n SUBSET c` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET_TRANS; SUBSET_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. u n IN components(cball(p:real^N,min a (inv(&2 pow n))) DIFF s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL
         [`b DIFF s:real^N->bool`;
          `cball(p:real^N,min a (inv(&2 pow n)))`;
          `c:real^N->bool`; `(u:num->real^N->bool) n`]
         COMPONENTS_INTER_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[CBALL_MIN_INTER] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~((u:num->real^N->bool) n = {})` MP_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; SKOLEM_THM]] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n. ?f. (f:real^1->real^N) continuous_on
            interval[lift(inv(&2 pow (SUC n))),lift(inv(&2 pow n))] /\
            IMAGE f (interval[lift(inv(&2 pow (SUC n))),lift(inv(&2 pow n))])
            SUBSET u n /\
            f(lift(inv(&2 pow n))) = q n /\
            f(lift(inv(&2 pow (SUC n)))) = q(SUC n)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `path_component (u n) (q n:real^N) (q(SUC n))` MP_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand)
        PATH_COMPONENT_EQ_CONNECTED_COMPONENT o rator o snd) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
        EXISTS_TAC `cball(p:real^N,min a (inv(&2 pow n))) DIFF s` THEN
        CONJ_TAC THENL
         [ALL_TAC;
          MATCH_MP_TAC OPEN_IN_COMPONENTS_LOCALLY_CONNECTED THEN
          ASM_REWRITE_TAC[]] THEN
        MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
        EXISTS_TAC `cball(p:real^N,min a (inv(&2 pow n)))` THEN
        ASM_SIMP_TAC[OPEN_IN_DIFF_CLOSED; COMPACT_IMP_CLOSED] THEN
        SIMP_TAC[CONVEX_IMP_LOCALLY_PATH_CONNECTED; CONVEX_CBALL;
                 CONVEX_IMP_LOCALLY_CONNECTED];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[connected_component] THEN
        EXISTS_TAC `(u:num->real^N->bool) n` THEN CONJ_TAC THENL
         [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ASM SET_TAC[]]];
      ONCE_REWRITE_TAC[PATH_COMPONENT_SYM_EQ] THEN
      REWRITE_TAC[path_component; path; path_image; pathstart; pathfinish] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real^1->real^N` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(f:real^1->real^N) o
                  (\x. &2 pow (SUC n) % (x - lift(inv(&2 pow (SUC n)))))` THEN
      ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
          SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_SUB;
                   CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
           (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET));
          REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
           (SET_RULE
             `IMAGE f i SUBSET u ==> s SUBSET i ==> IMAGE f s SUBSET u`))] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; FORALL_LIFT] THEN
        REWRITE_TAC[LIFT_DROP; DROP_VEC; DROP_CMUL; DROP_SUB] THEN
        SIMP_TAC[REAL_LT_POW2; REAL_SUB_LDISTRIB;
                 REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
        REWRITE_TAC[REAL_SUB_LE; REAL_ARITH `x - &1 <= &1 <=> x <= &2`] THEN
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        SIMP_TAC[REAL_LT_POW2; GSYM REAL_LE_LDIV_EQ; GSYM REAL_LE_RDIV_EQ] THEN
        REWRITE_TAC[real_pow; REAL_INV_MUL; real_div] THEN REAL_ARITH_TAC;
        REWRITE_TAC[o_THM; GSYM LIFT_SUB; GSYM LIFT_CMUL] THEN
        ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; LIFT_NUM] THEN
        REWRITE_TAC[real_pow; REAL_INV_MUL] THEN
        ASM_SIMP_TAC[REAL_LT_POW2; LIFT_NUM;
          REAL_FIELD `&0 < x ==> (&2 * x) * (inv x - inv(&2) * inv x) = &1`]]];
    REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:num->real^1->real^N` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL
   [`subtopology euclidean (interval[vec 0:real^1,vec 1] DELETE (vec 0))`;
    `subtopology euclidean (c:real^N->bool)`;
    `f:num->real^1->real^N`;
    `\n. interval[lift(inv(&2 pow (SUC n))),lift(inv(&2 pow n))]`;
    `(:num)`] PASTING_LEMMA_EXISTS_LOCALLY_FINITE) THEN
  REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
              SUBTOPOLOGY_SUBTOPOLOGY] THEN
  ONCE_REWRITE_TAC[TAUT `closed_in a b /\ c <=> ~(closed_in a b ==> ~c)`] THEN
  SIMP_TAC[ISPEC `euclidean` CLOSED_IN_IMP_SUBSET;
           SET_RULE `s SUBSET u ==> u INTER s = s`] THEN
  REWRITE_TAC[NOT_IMP] THEN
  REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; IN_DELETE] THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`inv(&2)`; `drop x / &9`] REAL_ARCH_POW_INV) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_INV] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
      EXISTS_TAC
        `(interval[vec 0,vec 1] DELETE vec 0) INTER
         ball(x:real^1,inv(&2 pow n))` THEN
      SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL; IN_INTER; CENTRE_IN_BALL] THEN
      REWRITE_TAC[IN_DELETE; IN_INTERVAL_1; REAL_LT_INV_EQ] THEN
      ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; REAL_LT_POW2] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
       `{i | ~(interval[lift(inv(&2 pow SUC i)),lift(inv(&2 pow i))] INTER
               ball(x:real^1,inv(&2 pow n)) = {})}` THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      REWRITE_TAC[BALL_1; DISJOINT_INTERVAL_1] THEN
      REWRITE_TAC[DE_MORGAN_THM; DROP_ADD; DROP_SUB; LIFT_DROP] THEN
      REWRITE_TAC[REAL_NOT_LT; REAL_NOT_LE] THEN
      MATCH_MP_TAC(MESON[FINITE_SUBSET; FINITE_INSERT; FINITE_EMPTY]
        `(?a b. s SUBSET {a,b}) ==> FINITE s`) THEN
      MATCH_MP_TAC(SET_RULE
       `~(?a b c. a IN s /\ b IN s /\ c IN s /\
                  ~(a = b) /\ ~(a = c) /\ ~(b = c))
        ==> ?a b. s SUBSET {a,b}`) THEN
      MATCH_MP_TAC(MESON[]
       `(!a b c. a IN s /\ b IN s /\ c IN s /\ ~(a = b) /\ ~(a = c) /\ ~(b = c)
                 ==> ?x y. x IN s /\ y IN s /\ x + 2 <= y) /\
        (!x y. x IN s /\ y IN s /\ x + 2 <= y ==> F)
        ==> ~(?a b c. a IN s /\ b IN s /\ c IN s /\
                  ~(a = b) /\ ~(a = c) /\ ~(b = c))`) THEN
      CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `c:num`] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `?x y. x IN {a,b,c} /\ y IN {a,b,c} /\ x + 2 <= y`
        MP_TAC THENL
         [SIMP_TAC[RIGHT_EXISTS_AND_THM; EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
          ASM_ARITH_TAC;
          REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN ASM SET_TAC[]];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `r:num`] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `&2 * drop x - &2 / &2 pow n < drop x + inv(&2 pow n)`
      MP_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      TRANS_TAC REAL_LET_TRANS `inv(&2 pow (SUC m))` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `x - inv i < a ==> a <= inv(&2) * b ==> &2 * x - &2 / i <= b`)) THEN
      REWRITE_TAC[GSYM REAL_INV_MUL; GSYM(CONJUNCT2 real_pow)] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_LT_POW2] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM; IN_DELETE] THEN
      X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; DIST_1; REAL_SUB_RZERO] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[real_abs] THEN STRIP_TAC THEN
      MP_TAC(fst(EQ_IMP_RULE(ISPEC`\n. drop y <= inv(&2 pow n)` num_MAX))) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [EXISTS_TAC `0` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          ASM_REWRITE_TAC[];
          MP_TAC(ISPECL [`inv(&2)`; `drop y`] REAL_ARCH_POW_INV) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
          REWRITE_TAC[REAL_POW_INV] THEN DISCH_TAC THEN
          X_GEN_TAC `m':num` THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
          REWRITE_TAC[NOT_LE; REAL_NOT_LE] THEN DISCH_TAC THEN
          TRANS_TAC REAL_LT_TRANS `inv(&2 pow m)` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LT_INV2 THEN REWRITE_TAC[REAL_LT_POW2] THEN
          MATCH_MP_TAC REAL_POW_MONO_LT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          ASM_REWRITE_TAC[]];
        MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[LIFT_DROP] THEN
        X_GEN_TAC `m:num` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        DISCH_THEN(MP_TAC o SPEC `m + 1`) THEN
        ASM_REWRITE_TAC[ADD1; ARITH_RULE `~(m + 1 <= m)`] THEN
        REAL_ARITH_TAC];
      X_GEN_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[CLOSED_INTERVAL] THEN
      REWRITE_TAC[SET_RULE
       `s SUBSET t DELETE a <=> ~(a IN s) /\ s SUBSET t`] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      SIMP_TAC[DE_MORGAN_THM; REAL_NOT_LE; REAL_LT_INV_EQ;
               REAL_LE_INV_EQ; REAL_LT_POW2; REAL_LT_IMP_LE] THEN
      DISJ2_TAC THEN SIMP_TAC[REAL_INV_LE_1; REAL_LE_POW2] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_LT_POW2] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
      MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
      MATCH_MP_TAC(SET_RULE
       `(~(t = {}) ==> !x. x IN s /\ x IN t ==> P x)
        ==> !x. x IN s INTER t ==> P x`) THEN
      REWRITE_TAC[DISJOINT_INTERVAL_1; DE_MORGAN_THM; LIFT_DROP] THEN
      ASM_CASES_TAC `SUC m < n` THEN
      ASM_SIMP_TAC[REAL_LT_INV2; REAL_LT_POW2; REAL_POW_MONO_LT;
                   REAL_ARITH `&1 < &2`] THEN
      DISCH_THEN(K ALL_TAC) THEN
      SUBGOAL_THEN `n = SUC m` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IN_INTER; IN_DELETE; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
      SUBGOAL_THEN `drop x = inv(&2 pow (SUC m))` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; REWRITE_TAC[GSYM LIFT_EQ; LIFT_DROP]] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `g = \x. if x = vec 0 then p else (h:real^1->real^N) x` THEN
  SUBGOAL_THEN
   `path g /\ pathstart g = (p:real^N) /\
    (!t. t IN interval[vec 0,vec 1] DELETE vec 0 ==> g t IN c)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[pathstart; IN_DELETE] THEN
    SIMP_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    SIMP_TAC[path; CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:real^1 = vec 0` THEN ASM_SIMP_TAC[] THENL
     [REWRITE_TAC[LIM_WITHIN_LE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`inv(&2)`; `e:real`] REAL_ARCH_POW_INV) THEN
      ASM_REWRITE_TAC[REAL_POW_INV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `inv(&2 pow n)` THEN
      REWRITE_TAC[REAL_LT_POW2; REAL_LT_INV_EQ; GSYM DIST_NZ] THEN
      EXPAND_TAC "g" THEN SIMP_TAC[] THEN
      X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; DIST_1; REAL_SUB_RZERO] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[real_abs] THEN STRIP_TAC THEN
      MP_TAC(fst(EQ_IMP_RULE(ISPEC`\n. drop y <= inv(&2 pow n)` num_MAX))) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`inv(&2)`; `drop y`] REAL_ARCH_POW_INV) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
        REWRITE_TAC[REAL_POW_INV] THEN DISCH_TAC THEN
        X_GEN_TAC `m':num` THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
        REWRITE_TAC[NOT_LE; REAL_NOT_LE] THEN DISCH_TAC THEN
        TRANS_TAC REAL_LT_TRANS `inv(&2 pow m)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_INV2 THEN REWRITE_TAC[REAL_LT_POW2] THEN
        MATCH_MP_TAC REAL_POW_MONO_LT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `m:num`
          (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(fun th ->
          MP_TAC(SPEC `n:num` th) THEN MP_TAC(SPEC `m + 1` th)) THEN
        ASM_REWRITE_TAC[REAL_NOT_LE; ARITH_RULE `~(m + 1 <= m)`] THEN
        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `h y = (f:num->real^1->real^N) m y` SUBST1_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; IN_DELETE; IN_INTER] THEN
          ASM_REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP; ADD1; DROP_VEC] THEN
          ASM_SIMP_TAC[REAL_LT_IMP_LE];
          TRANS_TAC REAL_LET_TRANS `inv(&2 pow n)` THEN ASM_REWRITE_TAC[] THEN
          TRANS_TAC REAL_LE_TRANS `inv(&2 pow m)` THEN
          ASM_SIMP_TAC[REAL_LE_INV2; REAL_LT_INV_EQ; REAL_LT_POW2;
                       REAL_POW_MONO; REAL_ARITH `&1 <= &2`] THEN
          TRANS_TAC REAL_LE_TRANS `min a (inv(&2 pow m))` THEN
          CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
          REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] (GSYM IN_CBALL)] THEN
          MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ x IN s ==> x IN t`) THEN
          EXISTS_TAC `cball(p:real^N,min a (inv(&2 pow m))) DIFF s` THEN
          REWRITE_TAC[SUBSET_DIFF] THEN
          MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ x IN s ==> x IN t`) THEN
          EXISTS_TAC `(u:num->real^N->bool) m` THEN
          ASM_SIMP_TAC[IN_COMPONENTS_SUBSET] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
          ASM_SIMP_TAC[ADD1; REAL_LT_IMP_LE]]];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^1`) THEN
      ASM_REWRITE_TAC[IN_DELETE; CONTINUOUS_WITHIN] THEN
      REWRITE_TAC[tendsto] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[EVENTUALLY_WITHIN_IMP] THEN
      MP_TAC(ISPECL [`(:real^1) DELETE vec 0`; `x:real^1`]
        EVENTUALLY_IN_OPEN) THEN
      ASM_SIMP_TAC[IN_DELETE; IN_UNIV; OPEN_DELETE; OPEN_UNIV] THEN
      REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
      EXPAND_TAC "g" THEN SIMP_TAC[IMP_CONJ]];
    MP_TAC(ISPECL [`reversepath g:real^1->real^N`;
                   `pathfinish g:real^N`; `p:real^N`]
        PATH_CONTAINS_ARC) THEN
    REWRITE_TAC[PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
    ASM_REWRITE_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH] THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `vec 1:real^1`) THEN
      REWRITE_TAC[IN_DELETE; ENDS_IN_UNIT_INTERVAL; VEC_EQ; ARITH_EQ] THEN
      REWRITE_TAC[pathfinish] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP FRONTIER_OF_COMPONENTS_SUBSET) THEN
      ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
      DISCH_THEN(MP_TAC o SPEC `p:real^N` o REWRITE_RULE[SUBSET]) THEN
      ASM_REWRITE_TAC[FRONTIER_INTER; IN_INTER] THEN
      REWRITE_TAC[IN_UNION; FRONTIER_CBALL; FRONTIER_COMPLEMENT] THEN
      ASM_SIMP_TAC[IN_SPHERE; DIST_REFL; REAL_LT_IMP_NZ] THEN
      ASM_SIMP_TAC[frontier; IN_DIFF; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^1->real^N` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [arc]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `(!x y. x IN i /\ y IN i /\ f x = f y ==> x = y)
        ==> z IN i /\ IMAGE f i DELETE f z SUBSET c
            ==> (!x. x IN i DELETE z ==> f x IN c)`)) THEN
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; GSYM path_image] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `a SUBSET g ==> g DELETE z SUBSET u ==> a DELETE z SUBSET u`)) THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM pathfinish] THEN
      ASM_REWRITE_TAC[path_image] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `(!x. x IN i DELETE z ==> g x IN c)
        ==> g z = p ==> IMAGE g i DELETE p SUBSET c`)) THEN
      ASM_MESON_TAC[pathstart]]]);;

let ACCESSIBLE_FRONTIER_ANR_COMPLEMENT_COMPONENT = prove
 (`!s c x y.
        compact s /\ ANR s /\
        c IN components((:real^N) DIFF s) /\ x IN c /\ y IN frontier c
        ==> ?g. arc g /\ pathstart g = x /\ pathfinish g = y /\
                !t. t IN interval[vec 0,vec 1] DELETE (vec 1) ==> g(t) IN c`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        OPEN_COMPONENTS)) THEN
  ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c:real^N->bool`; `y:real^N`;
                 `(:real^N)`]
        ACCESSIBLE_FRONTIER_ANR_INTER_COMPLEMENT_COMPONENT) THEN
  ASM_REWRITE_TAC[INTERIOR_UNIV; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `path_component c (x:real^N) (pathstart g2)` MP_TAC THENL
   [ASM_SIMP_TAC[OPEN_PATH_CONNECTED_COMPONENT] THEN
    REWRITE_TAC[connected_component] THEN EXISTS_TAC `c:real^N->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
    ASM_REWRITE_TAC[SUBSET_REFL; pathstart] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; IN_DELETE; VEC_EQ; ARITH_EQ];
    REWRITE_TAC[path_component] THEN
    DISCH_THEN(X_CHOOSE_THEN `g1:real^1->real^N` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `g:real^1->real^N = g1 ++ g2` THEN
  SUBGOAL_THEN `pathstart g:real^N = x /\ pathfinish g = y`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path(g:real^1->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN ASM_SIMP_TAC[PATH_JOIN; ARC_IMP_PATH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN interval[vec 0,vec 1] DELETE vec 1
        ==> (g:real^1->real^N) t IN c`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_DELETE; DROP_VEC; GSYM DROP_EQ] THEN
    STRIP_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC[joinpaths] THEN
    COND_CASES_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[path_image] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_INTERVAL_1; IN_DELETE; DROP_SUB;
                  DROP_CMUL; GSYM DROP_EQ; DROP_VEC] THEN
      ASM_REAL_ARITH_TAC];
    MP_TAC(ISPECL [`g:real^1->real^N`; `x:real^N`; `y:real^N`]
        PATH_CONTAINS_ARC) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [GSYM FRONTIER_DISJOINT_EQ]) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^1->real^N` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [arc])) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `(!x y. x IN i /\ y IN i /\ f x = f y ==> x = y)
        ==> z IN i /\ IMAGE f i DELETE f z SUBSET c
            ==> (!x. x IN i DELETE z ==> f x IN c)`)) THEN
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; GSYM path_image] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `a SUBSET g ==> g DELETE z SUBSET u ==> a DELETE z SUBSET u`)) THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM pathfinish] THEN
      ASM_REWRITE_TAC[path_image] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `(!x. x IN i DELETE z ==> g x IN c)
        ==> g z = p ==> IMAGE g i DELETE p SUBSET c`)) THEN
      ASM_MESON_TAC[pathfinish]]]);;

(* ------------------------------------------------------------------------- *)
(* Some simple consequences for complement connectivity.                     *)
(* ------------------------------------------------------------------------- *)

let LPC_INTERMEDIATE_CLOSURE_ANR_COMPLEMENT_COMPONENT = prove
 (`!s c t.
        compact s /\
        ANR s /\
        c IN components ((:real^N) DIFF s) /\
        c SUBSET t /\
        t SUBSET closure c
        ==> locally path_connected t`,
  let lemma = prove
   (`!s c u p.
          compact s /\ ANR s /\ c IN components((:real^N) DIFF s) /\
          p IN frontier c /\ open u /\ p IN u
          ==> ?v. open v /\ p IN v /\ v SUBSET u /\
                  !y. y IN c INTER v
                      ==> path_component ((p INSERT c) INTER u) p y`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `b:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `open(c:real^N->bool)` ASSUME_TAC THENL
     [REPEAT(FIRST_X_ASSUM((MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          OPEN_COMPONENTS)))) THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?a. &0 < a /\ a < b /\
          !d x. d IN components(cball(p,b) DIFF s) /\
                x IN d /\ x IN ball(p:real^N,a)
                ==> p IN closure d`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC
       `inf ((b / &2) INSERT
             IMAGE (\c. setdist({p:real^N},c))
                   {c | c IN components (cball (p,b) DIFF s) /\
                        ~(closure c INTER cball (p,b / &2) = {}) /\
                        ~(p IN closure c)})` THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `p:real^N`; `b / &2`; `b:real`]
        FINITE_ANR_COMPLEMENT_COMPONENTS_CONCENTRIC) THEN
      ASM_REWRITE_TAC[REAL_ARITH `e / &2 < e <=> &0 < e`] THEN
      DISCH_TAC THEN REWRITE_TAC[IN_BALL] THEN
      ONCE_REWRITE_TAC[SET_RULE
        `{x | P x /\ Q x /\ R x} = {x | x IN {y | P y /\ Q y} /\ R x}`] THEN
      ASM_SIMP_TAC[REAL_LT_INF_FINITE; NOT_INSERT_EMPTY; FINITE_INSERT;
                   FINITE_IMAGE; FINITE_RESTRICT; REAL_INF_LT_FINITE] THEN
      REWRITE_TAC[EXISTS_IN_INSERT; FORALL_IN_INSERT] THEN
      ASM_REWRITE_TAC[REAL_HALF; REAL_ARITH `e / &2 < e <=> &0 < e`] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      ASM_REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC] THEN
      SIMP_TAC[SETDIST_POS_LT; SETDIST_EQ_0_SING] THEN
      CONJ_TAC THENL [MESON_TAC[IN_COMPONENTS_NONEMPTY]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`d:real^N->bool`; `x:real^N`] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `d:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `p /\ ~q ==> (p ==> ~r ==> q) ==> r`) THEN
      ASM_SIMP_TAC[REAL_NOT_LT; SETDIST_LE_DIST; IN_SING] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_CBALL] THEN
      EXISTS_TAC `x:real^N` THEN ASM_SIMP_TAC[CLOSURE_INC; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    EXISTS_TAC `ball(p:real^N,a)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN CONJ_TAC THENL
     [TRANS_TAC SUBSET_TRANS `cball(p:real^N,b)` THEN
      ASM_REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    ABBREV_TAC `d = connected_component (cball(p:real^N,b) DIFF s) x` THEN
    SUBGOAL_THEN `d IN components(cball(p:real^N,b) DIFF s)` ASSUME_TAC THENL
     [REWRITE_TAC[components; IN_ELIM_THM; IN_DIFF] THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[IN_CBALL] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_BALL]) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN d` ASSUME_TAC THENL
     [EXPAND_TAC "d" THEN REWRITE_TAC[IN] THEN
      REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN
      ASM_REWRITE_TAC[IN_CBALL; IN_DIFF] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_BALL]) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(d:real^N->bool) SUBSET c` ASSUME_TAC THENL
     [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
      EXISTS_TAC `(:real^N) DIFF s` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`s:real^N->bool`; `d:real^N->bool`; `p:real^N`; `cball(p:real^N,b)`]
          ACCESSIBLE_FRONTIER_ANR_INTER_COMPLEMENT_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[INTERIOR_CBALL; CENTRE_IN_BALL] THEN
      REWRITE_TAC[frontier; IN_DIFF] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[SUBSET] INTERIOR_SUBSET)) THEN
      UNDISCH_TAC `(p:real^N) IN frontier c` THEN
      ASM_SIMP_TAC[frontier; INTERIOR_OPEN] THEN ASM SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC PATH_COMPONENT_TRANS THEN
      EXISTS_TAC `pathstart g:real^N` THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[PATH_COMPONENT_SYM_EQ] THEN
        REWRITE_TAC[path_component] THEN
        EXISTS_TAC `g:real^1->real^N` THEN
        ASM_SIMP_TAC[ARC_IMP_PATH] THEN
        REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
        ASM_CASES_TAC `r:real^1 = vec 1` THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[pathfinish]) THEN
          ASM_REWRITE_TAC[IN_INTER; IN_INSERT];
          FIRST_X_ASSUM(MP_TAC o SPEC `r:real^1`) THEN
          ASM_REWRITE_TAC[IN_DELETE] THEN
          REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
          ASM SET_TAC[]];
        MATCH_MP_TAC PATH_COMPONENT_OF_SUBSET THEN
        EXISTS_TAC `c INTER u:real^N->bool` THEN
        CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[OPEN_PATH_CONNECTED_COMPONENT; OPEN_INTER] THEN
        REWRITE_TAC[connected_component] THEN EXISTS_TAC `d:real^N->bool` THEN
        ASM_REWRITE_TAC[SUBSET_INTER] THEN REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
          REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
          ASM SET_TAC[];
          REWRITE_TAC[pathstart] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[IN_DELETE; ENDS_IN_UNIT_INTERVAL; VEC_EQ] THEN
          CONV_TAC NUM_REDUCE_CONV]]]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(c:real^N->bool)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM((MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        OPEN_COMPONENTS)))) THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[LOCALLY_PATH_CONNECTED_IM_KLEINEN] THEN
  MAP_EVERY X_GEN_TAC [`uu:real^N->bool`; `p:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o REWRITE_RULE[IN_INTER]) THEN
  SUBGOAL_THEN `(p:real^N) IN closure c` MP_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[CLOSURE_UNION_FRONTIER; IN_UNION]] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPEC `c INTER u:real^N->bool` OPEN_IMP_LOCALLY_PATH_CONNECTED) THEN
    ASM_SIMP_TAC[OPEN_INTER; LOCALLY_PATH_CONNECTED_IM_KLEINEN] THEN
    DISCH_THEN(MP_TAC o SPECL [`c INTER u:real^N->bool`; `p:real^N`]) THEN
    ASM_REWRITE_TAC[OPEN_IN_REFL; IN_INTER] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; OPEN_INTER] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC OPEN_SUBSET THEN ASM SET_TAC[];
    REWRITE_TAC[GSYM path_component] THEN
    MP_TAC(ISPECL
     [`s:real^N->bool`; `c:real^N->bool`; `u:real^N->bool`; `p:real^N`]
     lemma) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t INTER v:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_INTER] THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    X_GEN_TAC `q:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(q:real^N) IN closure c` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[CLOSURE_UNION_FRONTIER; IN_UNION]] THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC PATH_COMPONENT_OF_SUBSET THEN
      EXISTS_TAC `(p:real^N) INSERT c INTER u` THEN ASM SET_TAC[];
      MP_TAC(ISPECL
       [`s:real^N->bool`; `c:real^N->bool`; `v:real^N->bool`; `q:real^N`]
       lemma) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:real^N->bool`; `w:real^N->bool`]
        FRONTIER_OPEN_STRADDLE_INTER) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM; IN_INTER] THEN
      X_GEN_TAC `r:real^N` THEN STRIP_TAC THEN
      MATCH_MP_TAC PATH_COMPONENT_TRANS THEN EXISTS_TAC `r:real^N` THEN
      CONJ_TAC THEN MATCH_MP_TAC PATH_COMPONENT_OF_SUBSET THENL
       [EXISTS_TAC `(p:real^N) INSERT c INTER u` THEN ASM SET_TAC[];
        EXISTS_TAC `(q:real^N) INSERT c INTER v` THEN
        ONCE_REWRITE_TAC[PATH_COMPONENT_SYM_EQ] THEN ASM SET_TAC[]]]]);;

let LPC_INTERMEDIATE_CLOSURE_ANR_COMPLEMENT = prove
 (`!s t. compact s /\ ANR s /\
         (:real^N) DIFF s SUBSET t /\ DISJOINT t (interior s)
         ==> locally path_connected t`,
  let lemma = prove
   (`!s u p:real^N.
          compact s /\ ANR s /\ p IN frontier s /\ open u /\ p IN u
          ==> ?v. open v /\ p IN v /\ v SUBSET u /\
                  !y. y IN v DIFF s
                      ==> path_component (p INSERT (u DIFF s)) p y`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `b:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?a. &0 < a /\ a < b /\
          !d x. d IN components(cball(p,b) DIFF s) /\
                x IN d /\ x IN ball(p:real^N,a)
                ==> p IN closure d`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC
       `inf ((b / &2) INSERT
             IMAGE (\c. setdist({p:real^N},c))
                   {c | c IN components (cball (p,b) DIFF s) /\
                        ~(closure c INTER cball (p,b / &2) = {}) /\
                        ~(p IN closure c)})` THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `p:real^N`; `b / &2`; `b:real`]
        FINITE_ANR_COMPLEMENT_COMPONENTS_CONCENTRIC) THEN
      ASM_REWRITE_TAC[REAL_ARITH `e / &2 < e <=> &0 < e`] THEN
      DISCH_TAC THEN REWRITE_TAC[IN_BALL] THEN
      ONCE_REWRITE_TAC[SET_RULE
        `{x | P x /\ Q x /\ R x} = {x | x IN {y | P y /\ Q y} /\ R x}`] THEN
      ASM_SIMP_TAC[REAL_LT_INF_FINITE; NOT_INSERT_EMPTY; FINITE_INSERT;
                   FINITE_IMAGE; FINITE_RESTRICT; REAL_INF_LT_FINITE] THEN
      REWRITE_TAC[EXISTS_IN_INSERT; FORALL_IN_INSERT] THEN
      ASM_REWRITE_TAC[REAL_HALF; REAL_ARITH `e / &2 < e <=> &0 < e`] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      ASM_REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC] THEN
      SIMP_TAC[SETDIST_POS_LT; SETDIST_EQ_0_SING] THEN
      CONJ_TAC THENL [MESON_TAC[IN_COMPONENTS_NONEMPTY]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`d:real^N->bool`; `x:real^N`] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `d:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `p /\ ~q ==> (p ==> ~r ==> q) ==> r`) THEN
      ASM_SIMP_TAC[REAL_NOT_LT; SETDIST_LE_DIST; IN_SING] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_CBALL] THEN
      EXISTS_TAC `x:real^N` THEN ASM_SIMP_TAC[CLOSURE_INC; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    EXISTS_TAC `ball(p:real^N,a)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN CONJ_TAC THENL
     [TRANS_TAC SUBSET_TRANS `cball(p:real^N,b)` THEN
      ASM_REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `x IN UNIONS(components(cball(p:real^N,b) DIFF s))`
    MP_TAC THENL
     [ASM_REWRITE_TAC[GSYM UNIONS_COMPONENTS; IN_DIFF] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `x IN b ==> b SUBSET c ==> x IN c`)) THEN
      REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_UNIONS; LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^N->bool`; `x:real^N`]) THEN
    ASM_REWRITE_TAC[CLOSURE_UNION_FRONTIER; IN_UNION] THEN STRIP_TAC THENL
     [UNDISCH_TAC `(p:real^N) IN frontier s` THEN
      ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`s:real^N->bool`; `c:real^N->bool`; `p:real^N`; `cball(p:real^N,b)`]
          ACCESSIBLE_FRONTIER_ANR_INTER_COMPLEMENT_COMPONENT) THEN
    ASM_REWRITE_TAC[INTERIOR_CBALL; CENTRE_IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC PATH_COMPONENT_OF_SUBSET THEN
    EXISTS_TAC `(p:real^N) INSERT c` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC PATH_COMPONENT_TRANS THEN
    EXISTS_TAC `pathstart g:real^N` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[PATH_COMPONENT_SYM_EQ] THEN
      REWRITE_TAC[path_component] THEN
      EXISTS_TAC `g:real^1->real^N` THEN
      ASM_SIMP_TAC[ARC_IMP_PATH] THEN
      REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
      ASM_CASES_TAC `r:real^1 = vec 1` THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[pathfinish]) THEN
        ASM_REWRITE_TAC[IN_INTER; IN_INSERT];
        FIRST_X_ASSUM(MP_TAC o SPEC `r:real^1`) THEN
        ASM_REWRITE_TAC[IN_DELETE] THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
        ASM SET_TAC[]];
      MATCH_MP_TAC PATH_COMPONENT_OF_SUBSET THEN
      EXISTS_TAC `c:real^N->bool` THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand)
        PATH_COMPONENT_EQ_CONNECTED_COMPONENT o rator o snd) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          LOCALLY_PATH_CONNECTED_COMPONENTS)) THEN
        MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
        EXISTS_TAC `cball(p:real^N,b)` THEN
        SIMP_TAC[CONVEX_IMP_LOCALLY_PATH_CONNECTED; CONVEX_CBALL] THEN
        ASM_SIMP_TAC[OPEN_IN_DIFF_CLOSED; COMPACT_IMP_CLOSED];
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[connected_component] THEN EXISTS_TAC `c:real^N->bool` THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
      REWRITE_TAC[pathstart] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_DELETE; ENDS_IN_UNIT_INTERVAL; VEC_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV]) in
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LOCALLY_PATH_CONNECTED_IM_KLEINEN] THEN
  MAP_EVERY X_GEN_TAC [`uu:real^N->bool`; `p:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o REWRITE_RULE[IN_INTER]) THEN
  ASM_CASES_TAC `(p:real^N) IN s` THENL
   [ALL_TAC;
    MP_TAC(ISPEC `u DIFF s:real^N->bool` OPEN_IMP_LOCALLY_PATH_CONNECTED) THEN
    ASM_SIMP_TAC[OPEN_DIFF; COMPACT_IMP_CLOSED] THEN
    REWRITE_TAC[LOCALLY_PATH_CONNECTED_IM_KLEINEN] THEN
    DISCH_THEN(MP_TAC o SPECL [`u DIFF s:real^N->bool`; `p:real^N`]) THEN
    ASM_REWRITE_TAC[OPEN_IN_REFL; IN_DIFF] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; OPEN_DIFF; COMPACT_IMP_CLOSED] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC OPEN_SUBSET THEN ASM SET_TAC[]] THEN
  REWRITE_TAC[GSYM path_component] THEN
  MP_TAC(ISPECL
   [`s:real^N->bool`; `u:real^N->bool`; `p:real^N`] lemma) THEN
  ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t INTER v:real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_INTER] THEN
  REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  X_GEN_TAC `q:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(q:real^N) IN s` THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `v:real^N->bool`; `q:real^N`] lemma) THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `w:real^N->bool`]
      FRONTIER_OPEN_STRADDLE_INTER) THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM; IN_DIFF] THEN
    X_GEN_TAC `r:real^N` THEN STRIP_TAC THEN
    MATCH_MP_TAC PATH_COMPONENT_TRANS THEN EXISTS_TAC `r:real^N` THEN
    CONJ_TAC THEN MATCH_MP_TAC PATH_COMPONENT_OF_SUBSET THENL
     [EXISTS_TAC `(p:real^N) INSERT (u DIFF s)` THEN ASM SET_TAC[];
      EXISTS_TAC `(q:real^N) INSERT (v DIFF s)` THEN
      ONCE_REWRITE_TAC[PATH_COMPONENT_SYM_EQ] THEN ASM SET_TAC[]];
    MATCH_MP_TAC PATH_COMPONENT_OF_SUBSET THEN
    EXISTS_TAC `(p:real^N) INSERT (u DIFF s)` THEN
    ASM SET_TAC[]]);;

let LPC_SUPERSET_COMPLEMENT_SIMPLE_PATH_IMAGE = prove
 (`!g s:real^N->bool.
        2 <= dimindex(:N) /\ simple_path g /\
        (:real^N) DIFF path_image g SUBSET s
        ==> locally path_connected s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LPC_INTERMEDIATE_CLOSURE_ANR_COMPLEMENT THEN
  EXISTS_TAC `path_image g:real^N->bool` THEN
  ASM_SIMP_TAC[COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH] THEN
  ASM_SIMP_TAC[ANR_PATH_IMAGE_SIMPLE_PATH; INTERIOR_SIMPLE_PATH_IMAGE] THEN
  SET_TAC[]);;

let LPC_OPEN_SIMPLE_PATH_COMPLEMENT = prove
 (`!g. simple_path g
       ==> locally path_connected
            ((:real^N) DIFF (path_image g DIFF {pathstart g,pathfinish g}))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LPC_INTERMEDIATE_CLOSURE_ANR_COMPLEMENT THEN
  EXISTS_TAC `path_image g:real^N->bool` THEN
  ASM_SIMP_TAC[COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH] THEN
  ASM_SIMP_TAC[ANR_PATH_IMAGE_SIMPLE_PATH] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `i SUBSET p /\ DISJOINT {a,b} i
    ==> DISJOINT (UNIV DIFF (p DIFF {a,b})) i`) THEN
  ASM_SIMP_TAC[INTERIOR_SUBSET; ENDPOINTS_NOT_IN_INTERIOR_SIMPLE_PATH_IMAGE]);;

let PATH_CONNECTED_INTERMEDIATE_CLOSURE_ANR_COMPLEMENT_COMPONENT = prove
 (`!s c t.
        compact s /\ ANR s /\ c IN components((:real^N) DIFF s) /\
        c SUBSET t /\ t SUBSET closure c
        ==> path_connected t`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PATH_CONNECTED_EQ_CONNECTED_LPC o
    snd) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LPC_INTERMEDIATE_CLOSURE_ANR_COMPLEMENT_COMPONENT THEN
    ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
    EXISTS_TAC `c:real^N->bool` THEN ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]]);;

let PATH_CONNECTED_SUPERSET_COMPLEMENT_ARC_IMAGE = prove
 (`!g s:real^N->bool.
        2 <= dimindex(:N) /\ arc g /\ (:real^N) DIFF path_image g SUBSET s
        ==> path_connected s`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PATH_CONNECTED_EQ_CONNECTED_LPC o
    snd) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LPC_SUPERSET_COMPLEMENT_SIMPLE_PATH_IMAGE THEN
    ASM_MESON_TAC[ARC_IMP_SIMPLE_PATH];
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
    EXISTS_TAC `(:real^N) DIFF path_image g` THEN
    ASM_SIMP_TAC[CONNECTED_ARC_COMPLEMENT; CLOSURE_COMPLEMENT] THEN
    ASM_SIMP_TAC[INTERIOR_ARC_IMAGE] THEN SET_TAC[]]);;

let PATH_CONNECTED_OPEN_ARC_COMPLEMENT = prove
 (`!g. 2 <= dimindex(:N) /\ arc g
       ==> path_connected
            ((:real^N) DIFF (path_image g DIFF {pathstart g,pathfinish g}))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PATH_CONNECTED_SUPERSET_COMPLEMENT_ARC_IMAGE THEN
  EXISTS_TAC `g:real^1->real^N` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;
