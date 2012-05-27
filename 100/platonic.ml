(* ========================================================================= *)
(* The five Platonic solids exist and there are no others.                   *)
(* ========================================================================= *)

needs "100/polyhedron.ml";;
needs "Multivariate/cross.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Some standard regular polyhedra (vertex coordinates from Wikipedia).      *)
(* ------------------------------------------------------------------------- *)

let std_tetrahedron = new_definition
 `std_tetrahedron =
     convex hull
       {vector[&1;&1;&1],vector[-- &1;-- &1;&1],
        vector[-- &1;&1;-- &1],vector[&1;-- &1;-- &1]}:real^3->bool`;;

let std_cube = new_definition
 `std_cube =
     convex hull
       {vector[&1;&1;&1],vector[&1;&1;-- &1],
        vector[&1;-- &1;&1],vector[&1;-- &1;-- &1],
        vector[-- &1;&1;&1],vector[-- &1;&1;-- &1],
        vector[-- &1;-- &1;&1],vector[-- &1;-- &1;-- &1]}:real^3->bool`;;

let std_octahedron = new_definition
 `std_octahedron =
      convex hull
       {vector[&1;&0;&0],vector[-- &1;&0;&0],
        vector[&0;&0;&1],vector[&0;&0;-- &1],
        vector[&0;&1;&0],vector[&0;-- &1;&0]}:real^3->bool`;;

let std_dodecahedron = new_definition
 `std_dodecahedron =
      let p = (&1 + sqrt(&5)) / &2 in
      convex hull
       {vector[&1;&1;&1],vector[&1;&1;-- &1],
        vector[&1;-- &1;&1],vector[&1;-- &1;-- &1],
        vector[-- &1;&1;&1],vector[-- &1;&1;-- &1],
        vector[-- &1;-- &1;&1],vector[-- &1;-- &1;-- &1],
        vector[&0;inv p;p],vector[&0;inv p;--p],
        vector[&0;--inv p;p],vector[&0;--inv p;--p],
        vector[inv p;p;&0],vector[inv p;--p;&0],
        vector[--inv p;p;&0],vector[--inv p;--p;&0],
        vector[p;&0;inv p],vector[--p;&0;inv p],
        vector[p;&0;--inv p],vector[--p;&0;--inv p]}:real^3->bool`;;

let std_icosahedron = new_definition
 `std_icosahedron =
      let p = (&1 + sqrt(&5)) / &2 in
      convex hull
       {vector[&0; &1; p],vector[&0; &1; --p],
        vector[&0; -- &1; p],vector[&0; -- &1; --p],
        vector[&1; p; &0],vector[&1; --p; &0],
        vector[-- &1; p; &0],vector[-- &1; --p; &0],
        vector[p; &0; &1],vector[--p; &0; &1],
        vector[p; &0; -- &1],vector[--p; &0; -- &1]}:real^3->bool`;;

(* ------------------------------------------------------------------------- *)
(* Slightly ad hoc conversions for computation in Q[sqrt(5)].                *)
(* Numbers are canonically represented as either a rational constant r or an *)
(* expression r1 + r2 * sqrt(5) where r2 is nonzero but r1 may be zero and   *)
(* must be present.                                                          *)
(* ------------------------------------------------------------------------- *)

let REAL_RAT5_OF_RAT_CONV =
  let pth = prove
   (`p = p + &0 * sqrt(&5)`,
    REAL_ARITH_TAC) in
  let conv = REWR_CONV pth in
  fun tm -> if is_ratconst tm then conv tm else REFL tm;;

let REAL_RAT_OF_RAT5_CONV =
  let pth = prove
   (`p + &0 * sqrt(&5) = p`,
    REAL_ARITH_TAC) in
  GEN_REWRITE_CONV TRY_CONV [pth];;

let REAL_RAT5_ADD_CONV =
  let pth = prove
    (`(a1 + b1 * sqrt(&5)) + (a2 + b2 * sqrt(&5)) =
      (a1 + a2) + (b1 + b2) * sqrt(&5)`,
     REAL_ARITH_TAC) in
  REAL_RAT_ADD_CONV ORELSEC
  (BINOP_CONV REAL_RAT5_OF_RAT_CONV THENC
   GEN_REWRITE_CONV I [pth] THENC
   LAND_CONV REAL_RAT_ADD_CONV THENC
   RAND_CONV(LAND_CONV REAL_RAT_ADD_CONV) THENC
   REAL_RAT_OF_RAT5_CONV);;

let REAL_RAT5_SUB_CONV =
  let pth = prove
    (`(a1 + b1 * sqrt(&5)) - (a2 + b2 * sqrt(&5)) =
      (a1 - a2) + (b1 - b2) * sqrt(&5)`,
     REAL_ARITH_TAC) in
  REAL_RAT_SUB_CONV ORELSEC
  (BINOP_CONV REAL_RAT5_OF_RAT_CONV THENC
   GEN_REWRITE_CONV I [pth] THENC
   LAND_CONV REAL_RAT_SUB_CONV THENC
   RAND_CONV(LAND_CONV REAL_RAT_SUB_CONV) THENC
   REAL_RAT_OF_RAT5_CONV);;

let REAL_RAT5_MUL_CONV =
  let pth = prove
    (`(a1 + b1 * sqrt(&5)) * (a2 + b2 * sqrt(&5)) =
      (a1 * a2 + &5 * b1 * b2) + (a1 * b2 + a2 * b1) * sqrt(&5)`,
     MP_TAC(ISPEC `&5` SQRT_POW_2) THEN CONV_TAC REAL_FIELD) in
  REAL_RAT_MUL_CONV ORELSEC
  (BINOP_CONV REAL_RAT5_OF_RAT_CONV THENC
   GEN_REWRITE_CONV I [pth] THENC
   LAND_CONV(COMB_CONV (RAND_CONV REAL_RAT_MUL_CONV) THENC
             RAND_CONV REAL_RAT_MUL_CONV THENC
             REAL_RAT_ADD_CONV) THENC
   RAND_CONV(LAND_CONV
    (BINOP_CONV REAL_RAT_MUL_CONV THENC REAL_RAT_ADD_CONV)) THENC
   REAL_RAT_OF_RAT5_CONV);;

let REAL_RAT5_INV_CONV =
  let pth = prove
   (`~(a pow 2 = &5 * b pow 2)
     ==> inv(a + b * sqrt(&5)) =
         a / (a pow 2 - &5 * b pow 2) +
         --b / (a pow 2 - &5 * b pow 2) * sqrt(&5)`,
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_SUB_0] THEN
    SUBGOAL_THEN
     `a pow 2 - &5 * b pow 2 = (a + b * sqrt(&5)) * (a - b * sqrt(&5))`
    SUBST1_TAC THENL
     [MP_TAC(SPEC `&5` SQRT_POW_2) THEN CONV_TAC REAL_FIELD;
      REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN CONV_TAC REAL_FIELD]) in
  fun tm ->
    try REAL_RAT_INV_CONV tm with Failure _ ->
    let th1 = PART_MATCH (lhs o rand) pth tm in
    let th2 = MP th1 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th1)))) in
    let th3 = CONV_RULE(funpow 2 RAND_CONV (funpow 2 LAND_CONV
                REAL_RAT_NEG_CONV)) th2 in
    let th4 = CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV
               (RAND_CONV(LAND_CONV REAL_RAT_POW_CONV THENC
                          RAND_CONV(RAND_CONV REAL_RAT_POW_CONV THENC
                                    REAL_RAT_MUL_CONV) THENC
                          REAL_RAT_SUB_CONV) THENC
                REAL_RAT_DIV_CONV)))) th3 in
    let th5 = CONV_RULE(RAND_CONV(LAND_CONV
               (RAND_CONV(LAND_CONV REAL_RAT_POW_CONV THENC
                          RAND_CONV(RAND_CONV REAL_RAT_POW_CONV THENC
                                    REAL_RAT_MUL_CONV) THENC
                          REAL_RAT_SUB_CONV) THENC
                REAL_RAT_DIV_CONV))) th4 in
    th5;;

let REAL_RAT5_DIV_CONV =
  GEN_REWRITE_CONV I [real_div] THENC
  RAND_CONV REAL_RAT5_INV_CONV THENC
  REAL_RAT5_MUL_CONV;;

let REAL_RAT5_LE_CONV =
  let lemma = prove
   (`!x y. x <= y * sqrt(&5) <=>
           x <= &0 /\ &0 <= y \/
           &0 <= x /\ &0 <= y /\ x pow 2 <= &5 * y pow 2 \/
           x <= &0 /\ y <= &0 /\ &5 * y pow 2 <= x pow 2`,
    REPEAT GEN_TAC THEN MP_TAC(ISPEC `&5` SQRT_POW_2) THEN
    REWRITE_TAC[REAL_POS] THEN DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
    REWRITE_TAC[GSYM REAL_POW_MUL; GSYM REAL_LE_SQUARE_ABS] THEN
    MP_TAC(ISPECL [`sqrt(&5)`; `y:real`] (CONJUNCT1 REAL_LE_MUL_EQ)) THEN
    SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH] THEN REAL_ARITH_TAC) in
  let pth = prove
   (`(a1 + b1 * sqrt(&5)) <= (a2 + b2 * sqrt(&5)) <=>
        a1 <= a2 /\ b1 <= b2 \/
        a2 <= a1 /\ b1 <= b2 /\ (a1 - a2) pow 2 <= &5 * (b2 - b1) pow 2 \/
        a1 <= a2 /\ b2 <= b1 /\ &5 * (b2 - b1) pow 2 <= (a1 - a2) pow 2`,
    REWRITE_TAC[REAL_ARITH
     `a + b * x <= a' + b' * x <=> a - a' <= (b' - b) * x`] THEN
    REWRITE_TAC[lemma] THEN REAL_ARITH_TAC) in
  REAL_RAT_LE_CONV ORELSEC
  (BINOP_CONV REAL_RAT5_OF_RAT_CONV THENC
   GEN_REWRITE_CONV I [pth] THENC
   REAL_RAT_REDUCE_CONV);;

let REAL_RAT5_EQ_CONV =
  GEN_REWRITE_CONV I [GSYM REAL_LE_ANTISYM] THENC
  BINOP_CONV REAL_RAT5_LE_CONV THENC
  GEN_REWRITE_CONV I [AND_CLAUSES];;

(* ------------------------------------------------------------------------- *)
(* Conversions for operations on 3D vectors with coordinates in Q[sqrt(5)]   *)
(* ------------------------------------------------------------------------- *)

let VECTOR3_SUB_CONV =
  let pth = prove
   (`vector[x1;x2;x3] - vector[y1;y2;y3]:real^3 =
     vector[x1-y1; x2-y2; x3-y3]`,
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
    REWRITE_TAC[VECTOR_3; VECTOR_SUB_COMPONENT]) in
  GEN_REWRITE_CONV I [pth] THENC RAND_CONV(LIST_CONV REAL_RAT5_SUB_CONV);;

let VECTOR3_CROSS_CONV =
  let pth = prove
   (`(vector[x1;x2;x3]) cross (vector[y1;y2;y3]) =
     vector[x2 * y3 - x3 * y2; x3 * y1 - x1 * y3; x1 * y2 - x2 * y1]`,
    REWRITE_TAC[cross; VECTOR_3]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(LIST_CONV(BINOP_CONV REAL_RAT5_MUL_CONV THENC REAL_RAT5_SUB_CONV));;

let VECTOR3_EQ_0_CONV =
  let pth = prove
   (`vector[x1;x2;x3]:real^3 = vec 0 <=>
        x1 = &0 /\ x2 = &0 /\ x3 = &0`,
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
    REWRITE_TAC[VECTOR_3; VEC_COMPONENT]) in
  GEN_REWRITE_CONV I [pth] THENC
  DEPTH_BINOP_CONV `(/\)` REAL_RAT5_EQ_CONV THENC
  REWRITE_CONV[];;

let VECTOR3_DOT_CONV =
  let pth = prove
   (`(vector[x1;x2;x3]:real^3) dot (vector[y1;y2;y3]) =
        x1*y1 + x2*y2 + x3*y3`,
    REWRITE_TAC[DOT_3; VECTOR_3]) in
  GEN_REWRITE_CONV I [pth] THENC
  DEPTH_BINOP_CONV `(+):real->real->real` REAL_RAT5_MUL_CONV THENC
  RAND_CONV REAL_RAT5_ADD_CONV THENC
  REAL_RAT5_ADD_CONV;;

(* ------------------------------------------------------------------------- *)
(* Put any irrational coordinates in our standard form.                      *)
(* ------------------------------------------------------------------------- *)

let STD_DODECAHEDRON = prove
 (`std_dodecahedron =
   convex hull
    { vector[&1; &1; &1],
      vector[&1; &1; -- &1],
      vector[&1; -- &1; &1],
      vector[&1; -- &1; -- &1],
      vector[-- &1; &1; &1],
      vector[-- &1; &1; -- &1],
      vector[-- &1; -- &1; &1],
      vector[-- &1; -- &1; -- &1],
      vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0],
      vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0],
      vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0],
      vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0],
      vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)]}`,
  let golden_inverse = prove
   (`inv((&1 + sqrt(&5)) / &2) = -- &1 / &2 + &1 / &2 * sqrt(&5)`,
    MP_TAC(ISPEC `&5` SQRT_POW_2) THEN CONV_TAC REAL_FIELD) in
  REWRITE_TAC[std_dodecahedron] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[golden_inverse] THEN
  REWRITE_TAC[REAL_ARITH `(&1 + s) / &2 = &1 / &2 + &1 / &2 * s`] THEN
  REWRITE_TAC[REAL_ARITH `--(a + b * sqrt(&5)) = --a + --b * sqrt(&5)`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

let STD_ICOSAHEDRON = prove
 (`std_icosahedron =
   convex hull
    { vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0],
      vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0],
      vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0],
      vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0],
      vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1],
      vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1],
      vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1],
      vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1]}`,
  REWRITE_TAC[std_icosahedron] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[REAL_ARITH `(&1 + s) / &2 = &1 / &2 + &1 / &2 * s`] THEN
  REWRITE_TAC[REAL_ARITH `--(a + b * sqrt(&5)) = --a + --b * sqrt(&5)`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Explicit computation of facets.                                           *)
(* ------------------------------------------------------------------------- *)

let COMPUTE_FACES_2 = prove
 (`!f s:real^3->bool.
        FINITE s
        ==> (f face_of (convex hull s) /\ aff_dim f = &2 <=>
             ?x y z. x IN s /\ y IN s /\ z IN s /\
                     let a = (z - x) cross (y - x) in
                     ~(a = vec 0) /\
                     let b = a dot x in
                     ((!w. w IN s ==> a dot w <= b) \/
                      (!w. w IN s ==> a dot w >= b)) /\
                     f = convex hull (s INTER {x | a dot x = b}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `?t:real^3->bool. t SUBSET s /\ f = convex hull t`
    MP_TAC THENL
     [MATCH_MP_TAC FACE_OF_CONVEX_HULL_SUBSET THEN
      ASM_SIMP_TAC[FINITE_IMP_COMPACT];
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` MP_TAC)] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_CONVEX_HULL]) THEN
    MP_TAC(ISPEC `t:real^3->bool` AFFINE_BASIS_EXISTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(u:real^3->bool) HAS_SIZE 3` MP_TAC THENL
     [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN MATCH_MP_TAC(INT_ARITH
       `aff_dim(u:real^3->bool) = &2 /\ aff_dim u = &(CARD u) - &1
        ==> &(CARD u):int = &3`) THEN CONJ_TAC
      THENL [ASM_MESON_TAC[AFF_DIM_AFFINE_HULL]; ASM_MESON_TAC[AFF_DIM_UNIQUE]];
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`; `z:real^3`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC  [`x:real^3`; `y:real^3`; `z:real^3`] THEN
    REPLICATE_TAC 3 (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    REPEAT LET_TAC THEN
    SUBGOAL_THEN `~collinear{x:real^3,y,z}` MP_TAC THENL
     [ASM_REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[SET_RULE `{x,y,z} = {z,x,y}`] THEN
    ONCE_REWRITE_TAC[COLLINEAR_3] THEN ASM_REWRITE_TAC[GSYM CROSS_EQ_0] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a:real^3) dot y = b /\ (a:real^3) dot z = b`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(z - x) cross (y - x) = a`; `(a:real^3) dot x = b`] THEN VEC3_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`convex hull s:real^3->bool`; `convex hull t:real^3->bool`]
        EXPOSED_FACE_OF_POLYHEDRON) THEN
    ASM_SIMP_TAC[POLYHEDRON_CONVEX_HULL; exposed_face_of] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a':real^3`; `b':real`] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    SUBGOAL_THEN
     `aff_dim(t:real^3->bool)
      <= aff_dim({x:real^3 | a dot x = b} INTER {x | a' dot x = b'})`
    MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM AFF_DIM_AFFINE_HULL] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
       [SYM th]) THEN
      REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN MATCH_MP_TAC AFF_DIM_SUBSET THEN
      REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `convex hull t:real^3->bool` THEN
        REWRITE_TAC[HULL_SUBSET] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INTER_HYPERPLANE; AFF_DIM_HYPERPLANE;
                 AFFINE_HYPERPLANE; DIMINDEX_3] THEN
    REPEAT(COND_CASES_TAC THEN CONV_TAC INT_REDUCE_CONV) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [SUBSET_HYPERPLANES]) THEN
    ASM_REWRITE_TAC[HYPERPLANE_EQ_EMPTY] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (MP_TAC o SYM)) THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[INTER_UNIV]) THEN
      SUBGOAL_THEN `s SUBSET {x:real^3 | a dot x = b}` ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `convex hull s:real^3->bool` THEN
        REWRITE_TAC[HULL_SUBSET] THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `affine hull t:real^3->bool` THEN
        REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
        ASM_SIMP_TAC[real_ge; REAL_LE_REFL];
        ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s INTER t = s`]];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; real_ge; REAL_NOT_LE] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_TAC `u:real^3`) (X_CHOOSE_TAC `v:real^3`)) THEN
      SUBGOAL_THEN `(a':real^3) dot u < b' /\ a' dot v < b'` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_LT_LE] THEN REWRITE_TAC
         [SET_RULE `f x <= b /\ ~(f x = b) <=>
                    x IN {x | f x <= b} /\ ~(x IN {x | f x = b})`] THEN
        ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[IN_ELIM_THM; REAL_LT_IMP_NE] THEN
        SUBGOAL_THEN `(u:real^3) IN convex hull s /\ v IN convex hull s`
        MP_TAC THENL [ASM_SIMP_TAC[HULL_INC]; ASM SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `?w:real^3. w IN segment[u,v] /\ w IN {w | a' dot w = b'}`
      MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        MATCH_MP_TAC CONNECTED_IVT_HYPERPLANE THEN
        MAP_EVERY EXISTS_TAC [`v:real^3`; `u:real^3`] THEN
        ASM_SIMP_TAC[ENDS_IN_SEGMENT; CONNECTED_SEGMENT; REAL_LT_IMP_LE];
        REWRITE_TAC[IN_SEGMENT; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
        ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
        REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
        REWRITE_TAC[UNWIND_THM2; DOT_RADD; DOT_RMUL; CONJ_ASSOC] THEN
        DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
        MATCH_MP_TAC(REAL_ARITH `a < b ==> a = b ==> F`) THEN
        MATCH_MP_TAC REAL_CONVEX_BOUND_LT THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[SUBSET_INTER] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `convex hull t:real^3->bool` THEN
        REWRITE_TAC[HULL_SUBSET] THEN ASM SET_TAC[];
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
        REWRITE_TAC[SUBSET_INTER] THEN
        SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `convex hull {x:real^3 | a dot x = b}` THEN
        SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
        MATCH_MP_TAC(SET_RULE `s = t ==> s SUBSET t`) THEN
        REWRITE_TAC[CONVEX_HULL_EQ; CONVEX_HYPERPLANE]]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`; `z:real^3`] THEN
    REPEAT LET_TAC THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `convex hull (s INTER {x:real^3 | a dot x = b}) =
        (convex hull s) INTER {x | a dot x = b}`
      SUBST1_TAC THENL
       [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [SIMP_TAC[SUBSET_INTER; HULL_MONO; INTER_SUBSET] THEN
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `convex hull {x:real^3 | a dot x = b}` THEN
          SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
          MATCH_MP_TAC(SET_RULE `s = t ==> s SUBSET t`) THEN
          REWRITE_TAC[CONVEX_HULL_EQ; CONVEX_HYPERPLANE];
        ALL_TAC] THEN
      ASM_CASES_TAC `s SUBSET {x:real^3 | a dot x = b}` THENL
       [ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s INTER t = s`] THEN SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
       `convex hull (convex hull (s INTER {x:real^3 | a dot x = b}) UNION
                     convex hull (s DIFF {x | a dot x = b})) INTER
        {x | a dot x = b}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `s SUBSET t ==> (s INTER u) SUBSET (t INTER u)`) THEN
        MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC(SET_RULE
         `s INTER t SUBSET (P hull (s INTER t)) /\
          s DIFF t SUBSET (P hull (s DIFF t))
          ==> s SUBSET (P hull (s INTER t)) UNION (P hull (s DIFF t))`) THEN
        REWRITE_TAC[HULL_SUBSET];
        ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) CONVEX_HULL_UNION_NONEMPTY_EXPLICIT o
        lhand o lhand o snd) THEN
      ANTS_TAC THENL
       [SIMP_TAC[CONVEX_CONVEX_HULL; CONVEX_HULL_EQ_EMPTY] THEN ASM SET_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[SUBSET; IN_INTER; IMP_CONJ; FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`p:real^3`; `u:real`; `q:real^3`] THEN
      REPLICATE_TAC 4 DISCH_TAC THEN ASM_CASES_TAC `u = &0` THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(&1 - &0) % p + &0 % q:real^N = p`] THEN
      MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `x < y ==> ~(x = y)`) THEN
        MATCH_MP_TAC(REAL_ARITH
         `(&1 - u) * p = (&1 - u) * b /\ u * q < u * b
          ==> (&1 - u) * p + u * q < b`) THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `p IN {x:real^3 | a dot x = b}` MP_TAC THENL
           [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
             `x IN s ==> s SUBSET t ==> x IN t`)) THEN
            MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HYPERPLANE] THEN
            SET_TAC[];
            SIMP_TAC[IN_ELIM_THM]];
          MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          ONCE_REWRITE_TAC[SET_RULE
           `(a:real^3) dot q < b <=> q IN {x | a dot x < b}`] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `x IN s ==> s SUBSET t ==> x IN t`)) THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_LT] THEN
          ASM_SIMP_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; REAL_LT_LE]];
        MATCH_MP_TAC(REAL_ARITH `x > y ==> ~(x = y)`) THEN
        MATCH_MP_TAC(REAL_ARITH
         `(&1 - u) * p = (&1 - u) * b /\ u * b < u * q
          ==> (&1 - u) * p + u * q > b`) THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `p IN {x:real^3 | a dot x = b}` MP_TAC THENL
           [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
             `x IN s ==> s SUBSET t ==> x IN t`)) THEN
            MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HYPERPLANE] THEN
            SET_TAC[];
            SIMP_TAC[IN_ELIM_THM]];
          MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; REWRITE_TAC[GSYM real_gt]] THEN
          ONCE_REWRITE_TAC[SET_RULE
           `(a:real^3) dot q > b <=> q IN {x | a dot x > b}`] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `x IN s ==> s SUBSET t ==> x IN t`)) THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_GT] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THEN
          ASM_SIMP_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; real_gt; REAL_LT_LE]]];
        ALL_TAC] THEN
      FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
        REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
        SIMP_TAC[SET_RULE `(!x. x IN s ==> P x) <=> s SUBSET {x | P x}`] THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_LE] THEN
        ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
        MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE THEN
        REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
        SIMP_TAC[SET_RULE `(!x. x IN s ==> P x) <=> s SUBSET {x | P x}`] THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_GE] THEN
        ASM_SIMP_TAC[SUBSET; IN_ELIM_THM]];
      REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC INT_LE_TRANS THEN
        EXISTS_TAC `aff_dim {x:real^3 | a dot x = b}` THEN CONJ_TAC THENL
         [MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HYPERPLANE] THEN
          SET_TAC[];
          ASM_SIMP_TAC[AFF_DIM_HYPERPLANE; DIMINDEX_3] THEN INT_ARITH_TAC];
        MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim {x:real^3,y,z}` THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `~collinear{x:real^3,y,z}` MP_TAC THENL
           [ONCE_REWRITE_TAC[SET_RULE `{x,y,z} = {z,x,y}`] THEN
            ONCE_REWRITE_TAC[COLLINEAR_3] THEN
            ASM_REWRITE_TAC[GSYM CROSS_EQ_0];
            REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN
            STRIP_TAC] THEN
          ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
          SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
          ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
          CONV_TAC INT_REDUCE_CONV;
          MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM_REWRITE_TAC[INSERT_SUBSET] THEN
          REWRITE_TAC[EMPTY_SUBSET] THEN REPEAT CONJ_TAC THEN
          MATCH_MP_TAC HULL_INC THEN
          ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
          MAP_EVERY UNDISCH_TAC
           [`(z - x) cross (y - x) = a`; `(a:real^3) dot x = b`] THEN
          VEC3_TAC]]]]);;

let COMPUTE_FACES_2_STEP_1 = prove
 (`!f v s t:real^3->bool.
       (?x y z. x IN (v INSERT s) /\ y IN (v INSERT s) /\ z IN (v INSERT s) /\
                let a = (z - x) cross (y - x) in
                ~(a = vec 0) /\
                let b = a dot x in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b})) <=>
       (?y z. y IN s /\ z IN s /\
                let a = (z - v) cross (y - v) in
                ~(a = vec 0) /\
                let b = a dot v in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b})) \/
       (?x y z. x IN s /\ y IN s /\ z IN s /\
                let a = (z - x) cross (y - x) in
                ~(a = vec 0) /\
                let b = a dot x in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INSERT] THEN MATCH_MP_TAC(MESON[]
       `(!x y z. Q x y z ==> Q x z y) /\
        (!x y z. Q x y z ==> Q y x z) /\
        (!x z. ~(Q x x z))
        ==> ((?x y z. (x = v \/ P x) /\ (y = v \/ P y) /\ (z = v \/ P z) /\
             Q x y z) <=>
            (?y z. P y /\ P z /\ Q v y z) \/
            (?x y z. P x /\ P y /\ P z /\ Q x y z))`) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[VECTOR_SUB_REFL; CROSS_0] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  MAP_EVERY (SUBST1_TAC o VEC3_RULE)
   [`(z - y) cross (x - y) = --((z - x) cross (y - x))`;
    `(y - x) cross (z - x) =  --((z - x) cross (y - x))`] THEN
  REWRITE_TAC[VECTOR_NEG_EQ_0; DOT_LNEG; REAL_EQ_NEG2; REAL_LE_NEG2;
              real_ge] THEN
  REWRITE_TAC[DISJ_ACI] THEN
  REWRITE_TAC[VEC3_RULE
   `((z - x) cross (y - x)) dot y = ((z - x) cross (y - x)) dot x`]);;

let COMPUTE_FACES_2_STEP_2 = prove
 (`!f u v s:real^3->bool.
         (?y z. y IN (u INSERT s) /\ z IN (u INSERT s) /\
                let a = (z - v) cross (y - v) in
                ~(a = vec 0) /\
                let b = a dot v in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b})) <=>
         (?z. z IN s /\
              let a = (z - v) cross (u - v) in
              ~(a = vec 0) /\
              let b = a dot v in
              ((!w. w IN t ==> a dot w <= b) \/
               (!w. w IN t ==> a dot w >= b)) /\
              f = convex hull (t INTER {x | a dot x = b})) \/
         (?y z. y IN s /\ z IN s /\
                let a = (z - v) cross (y - v) in
                ~(a = vec 0) /\
                let b = a dot v in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INSERT] THEN MATCH_MP_TAC(MESON[]
       `(!x y. Q x y ==> Q y x) /\
        (!x. ~(Q x x))
        ==> ((?y z. (y = u \/ P y) /\ (z = u \/ P z) /\
             Q y z) <=>
            (?z. P z /\ Q u z) \/
            (?y z. P y /\ P z /\ Q y z))`) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CROSS_REFL] THEN REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN SUBST1_TAC
   (VEC3_RULE `(x - v) cross (y - v) = --((y - v) cross (x - v))`) THEN
  REWRITE_TAC[VECTOR_NEG_EQ_0; DOT_LNEG; REAL_EQ_NEG2; REAL_LE_NEG2;
              real_ge] THEN REWRITE_TAC[DISJ_ACI]);;

let COMPUTE_FACES_TAC =
  let lemma = prove
   (`(x INSERT s) INTER {x | P x} =
                        if P x then x INSERT (s INTER {x | P x})
                        else s INTER {x | P x}`,
    COND_CASES_TAC THEN ASM SET_TAC[]) in
  SIMP_TAC[COMPUTE_FACES_2; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[COMPUTE_FACES_2_STEP_1] THEN
  REWRITE_TAC[COMPUTE_FACES_2_STEP_2] THEN
  REWRITE_TAC[NOT_IN_EMPTY] THEN
  REWRITE_TAC[EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_CROSS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV) THEN
  REWRITE_TAC[real_ge] THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_DOT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_LE_CONV) THEN
  REWRITE_TAC[INSERT_AC] THEN REWRITE_TAC[DISJ_ACI] THEN
  REPEAT(CHANGED_TAC
   (ONCE_REWRITE_TAC[lemma] THEN
    CONV_TAC(ONCE_DEPTH_CONV
     (LAND_CONV VECTOR3_DOT_CONV THENC REAL_RAT5_EQ_CONV))) THEN
    REWRITE_TAC[]) THEN
  REWRITE_TAC[INTER_EMPTY] THEN
  REWRITE_TAC[INSERT_AC] THEN REWRITE_TAC[DISJ_ACI];;

(* ------------------------------------------------------------------------- *)
(* Apply this to our standard Platonic solids to derive facets.              *)
(* Note: this is quite slow and can take a couple of hours.                  *)
(* ------------------------------------------------------------------------- *)

let TETRAHEDRON_FACETS = time prove
 (`!f:real^3->bool.
        f face_of std_tetrahedron /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1]} \/
        f = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[-- &1; -- &1; &1], vector[&1; -- &1; -- &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1], vector[&1; &1; &1]}`,
  GEN_TAC THEN REWRITE_TAC[std_tetrahedron] THEN COMPUTE_FACES_TAC);;

let CUBE_FACETS = time prove
 (`!f:real^3->bool.
        f face_of std_cube /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1], vector[-- &1; &1; &1]} \/
        f = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1], vector[&1; -- &1; -- &1], vector[&1; -- &1; &1]} \/
        f = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1], vector[&1; &1; -- &1]} \/
        f = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; &1], vector[&1; -- &1; &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[-- &1; &1; -- &1], vector[-- &1; &1; &1], vector[&1; &1; -- &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[&1; -- &1; -- &1], vector[&1; -- &1; &1], vector[&1; &1; -- &1], vector[&1; &1; &1]}`,
  GEN_TAC THEN REWRITE_TAC[std_cube] THEN COMPUTE_FACES_TAC);;

let OCTAHEDRON_FACETS = time prove
 (`!f:real^3->bool.
        f face_of std_octahedron /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1; &0; &0], vector[&0; -- &1; &0], vector[&0; &0; -- &1]} \/
        f = convex hull {vector[-- &1; &0; &0], vector[&0; -- &1; &0], vector[&0; &0; &1]} \/
        f = convex hull {vector[-- &1; &0; &0], vector[&0; &1; &0], vector[&0; &0; -- &1]} \/
        f = convex hull {vector[-- &1; &0; &0], vector[&0; &1; &0], vector[&0; &0; &1]} \/
        f = convex hull {vector[&1; &0; &0], vector[&0; -- &1; &0], vector[&0; &0; -- &1]} \/
        f = convex hull {vector[&1; &0; &0], vector[&0; -- &1; &0], vector[&0; &0; &1]} \/
        f = convex hull {vector[&1; &0; &0], vector[&0; &1; &0], vector[&0; &0; -- &1]} \/
        f = convex hull {vector[&1; &0; &0], vector[&0; &1; &0], vector[&0; &0; &1]}`,
  GEN_TAC THEN REWRITE_TAC[std_octahedron] THEN COMPUTE_FACES_TAC);;

let ICOSAHEDRON_FACETS = time prove
 (`!f:real^3->bool.
        f face_of std_icosahedron /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]}`,
  GEN_TAC THEN REWRITE_TAC[STD_ICOSAHEDRON] THEN COMPUTE_FACES_TAC);;

let DODECAHEDRON_FACETS = time prove
 (`!f:real^3->bool.
        f face_of std_dodecahedron /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[-- &1; &1; -- &1], vector[-- &1; &1; &1]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[-- &1; -- &1; &1], vector[-- &1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[-- &1; -- &1; -- &1], vector[-- &1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[-- &1; -- &1; -- &1], vector[&1; -- &1; -- &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[-- &1; -- &1; &1], vector[&1; -- &1; &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1; -- &1; -- &1], vector[&1; -- &1; &1]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[-- &1; &1; -- &1], vector[&1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[-- &1; &1; &1], vector[&1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1; &1; -- &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[&1; -- &1; &1], vector[&1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1; -- &1; -- &1], vector[&1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]}`,
  GEN_TAC THEN REWRITE_TAC[STD_DODECAHEDRON] THEN COMPUTE_FACES_TAC);;

(* ------------------------------------------------------------------------- *)
(* Given a coplanar set, return a hyperplane containing it.                  *)
(* Maps term s to theorem |- !x. x IN s ==> n dot x = d                      *)
(* Currently assumes |s| >= 3 but it would be trivial to do other cases.     *)
(* ------------------------------------------------------------------------- *)

let COPLANAR_HYPERPLANE_RULE =
  let rec allsets m l =
    if m = 0 then [[]] else
    match l with
      [] -> []
    | h::t -> map (fun g -> h::g) (allsets (m - 1) t) @ allsets m t in
  let mk_sub = mk_binop `(-):real^3->real^3->real^3`
  and mk_cross = mk_binop `cross`
  and mk_dot = mk_binop `(dot):real^3->real^3->real`
  and zerovec_tm = `vector[&0;&0;&0]:real^3`
  and template = `(!x:real^3. x IN s ==> n dot x = d)`
  and s_tm = `s:real^3->bool`
  and n_tm = `n:real^3`
  and d_tm = `d:real` in
  let mk_normal [x;y;z] = mk_cross (mk_sub y x) (mk_sub z x) in
  let eval_normal t =
    (BINOP_CONV VECTOR3_SUB_CONV THENC VECTOR3_CROSS_CONV) (mk_normal t) in
  let check_normal t =
    let th = eval_normal t in
    let n = rand(concl th) in
    if n = zerovec_tm then failwith "check_normal" else n in
  fun tm ->
    let s = dest_setenum tm in
    if length s < 3 then failwith "COPLANAR_HYPERPLANE_RULE: trivial" else
    let n = tryfind check_normal (allsets 3 s) in
    let d = rand(concl(VECTOR3_DOT_CONV(mk_dot n (hd s)))) in
    let ptm = vsubst [tm,s_tm; n,n_tm; d,d_tm] template in
    EQT_ELIM
    ((REWRITE_CONV[FORALL_IN_INSERT; NOT_IN_EMPTY] THENC
      DEPTH_BINOP_CONV `/\`
       (LAND_CONV VECTOR3_DOT_CONV THENC REAL_RAT5_EQ_CONV) THENC
      GEN_REWRITE_CONV DEPTH_CONV [AND_CLAUSES]) ptm);;

(* ------------------------------------------------------------------------- *)
(* Explicit computation of edges, assuming hyperplane containing the set.    *)
(* ------------------------------------------------------------------------- *)

let COMPUTE_FACES_1 = prove
 (`!s:real^3->bool n d.
        (!x. x IN s ==> n dot x = d)
        ==> FINITE s /\ ~(n = vec 0)
            ==> !f. f face_of (convex hull s) /\ aff_dim f = &1 <=>
                    ?x y. x IN s /\ y IN s /\
                          let a = n cross (y - x) in
                          ~(a = vec 0) /\
                          let b = a dot x in
                          ((!w. w IN s ==> a dot w <= b) \/
                           (!w. w IN s ==> a dot w >= b)) /\
                          f = convex hull (s INTER {x | a dot x = b})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `?t:real^3->bool. t SUBSET s /\ f = convex hull t`
    MP_TAC THENL
     [MATCH_MP_TAC FACE_OF_CONVEX_HULL_SUBSET THEN
      ASM_SIMP_TAC[FINITE_IMP_COMPACT];
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` MP_TAC)] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_CONVEX_HULL]) THEN
    MP_TAC(ISPEC `t:real^3->bool` AFFINE_BASIS_EXISTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(u:real^3->bool) HAS_SIZE 2` MP_TAC THENL
     [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN MATCH_MP_TAC(INT_ARITH
       `aff_dim(u:real^3->bool) = &1 /\ aff_dim u = &(CARD u) - &1
        ==> &(CARD u):int = &2`) THEN CONJ_TAC
      THENL [ASM_MESON_TAC[AFF_DIM_AFFINE_HULL]; ASM_MESON_TAC[AFF_DIM_UNIQUE]];
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
    MAP_EVERY EXISTS_TAC  [`x:real^3`; `y:real^3`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    SUBGOAL_THEN `(x:real^3) IN s /\ y IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT LET_TAC THEN
    MP_TAC(ISPECL [`n:real^3`; `y - x:real^3`] NORM_AND_CROSS_EQ_0) THEN
    ASM_SIMP_TAC[DOT_RSUB; VECTOR_SUB_EQ; REAL_SUB_0] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:real^3) dot y = b` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`n cross (y - x) = a`; `(a:real^3) dot x = b`] THEN VEC3_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`convex hull s:real^3->bool`; `convex hull t:real^3->bool`]
        EXPOSED_FACE_OF_POLYHEDRON) THEN
    ASM_SIMP_TAC[POLYHEDRON_CONVEX_HULL; EXPOSED_FACE_OF_PARALLEL] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a':real^3`; `b':real`] THEN
    SUBGOAL_THEN `~(convex hull t:real^3->bool = {})` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:real^3` THEN
      MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[]] THEN
    ASM_CASES_TAC `convex hull t:real^3->bool = convex hull s` THEN
    ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE RAND_CONV
        [GSYM AFFINE_HULL_CONVEX_HULL]) THEN
      UNDISCH_THEN `convex hull t:real^3->bool = convex hull s`
       (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[AFFINE_HULL_CONVEX_HULL]) THEN
      REWRITE_TAC[SET_RULE `s = s INTER t <=> s SUBSET t`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `s SUBSET {x:real^3 | a dot x = b}` ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `affine hull s:real^3->bool` THEN
        REWRITE_TAC[HULL_SUBSET] THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
        ASM SET_TAC[];
        CONJ_TAC THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
          ASM_SIMP_TAC[real_ge; REAL_LE_REFL];
          AP_TERM_TAC THEN ASM SET_TAC[]]];
      STRIP_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[AFFINE_HULL_CONVEX_HULL]) THEN
    SUBGOAL_THEN
     `aff_dim(t:real^3->bool)
      <= aff_dim(({x:real^3 | a dot x = b} INTER {x:real^3 | a' dot x = b'})
                 INTER {x | n dot x = d})`
    MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM AFF_DIM_AFFINE_HULL] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
       [SYM th]) THEN
      REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN MATCH_MP_TAC AFF_DIM_SUBSET THEN
      REWRITE_TAC[SUBSET_INTER; INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `(x:real^3) IN convex hull t /\ y IN convex hull t`
      MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INTER_HYPERPLANE; AFF_DIM_HYPERPLANE;
                 AFFINE_HYPERPLANE; DIMINDEX_3; AFFINE_INTER] THEN
    ASM_CASES_TAC `{x:real^3 | a dot x = b} SUBSET {v | a' dot v = b'}` THEN
    ASM_REWRITE_TAC[] THENL
     [ALL_TAC;
      REPEAT(COND_CASES_TAC THEN CONV_TAC INT_REDUCE_CONV) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
       `s INTER t SUBSET u ==> !x. x IN s /\ x IN t ==> x IN u`)) THEN
      DISCH_THEN(MP_TAC o SPEC `x + n:real^3`) THEN
      MATCH_MP_TAC(TAUT `p /\ q /\ ~r ==> (p /\ q ==> r) ==> s`) THEN
      ASM_SIMP_TAC[IN_ELIM_THM; DOT_RADD] THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "a" THEN VEC3_TAC;
        ALL_TAC;
        ASM_REWRITE_TAC[REAL_EQ_ADD_LCANCEL_0; DOT_EQ_0]] THEN
      SUBGOAL_THEN `a' dot (x:real^3) = b'` SUBST1_TAC THENL
       [SUBGOAL_THEN `(x:real^3) IN convex hull t` MP_TAC THENL
         [MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]; ASM SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(n:real^3) dot (x + a') = n dot x` MP_TAC THENL
       [ALL_TAC;
        SIMP_TAC[DOT_RADD] THEN REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `x:real = d /\ y = d ==> x = y`) THEN
      SUBGOAL_THEN
       `affine hull s SUBSET {x:real^3 | n dot x = d}`
      MP_TAC THENL
       [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
        ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_SIMP_TAC[HULL_INC]]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_HYPERPLANES]) THEN
    ASM_REWRITE_TAC[HYPERPLANE_EQ_EMPTY; HYPERPLANE_EQ_UNIV] THEN
    DISCH_THEN(fun th -> DISCH_THEN(K ALL_TAC) THEN MP_TAC(SYM th)) THEN
    DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; real_ge; REAL_NOT_LE] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_TAC `u:real^3`) (X_CHOOSE_TAC `v:real^3`)) THEN
      SUBGOAL_THEN `(a':real^3) dot u < b' /\ a' dot v < b'` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_LT_LE] THEN REWRITE_TAC
         [SET_RULE `f x <= b /\ ~(f x = b) <=>
                    x IN {x | f x <= b} /\ ~(x IN {x | f x = b})`] THEN
        ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[IN_ELIM_THM; REAL_LT_IMP_NE] THEN
        SUBGOAL_THEN `(u:real^3) IN convex hull s /\ v IN convex hull s`
        MP_TAC THENL [ASM_SIMP_TAC[HULL_INC]; ASM SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `?w:real^3. w IN segment[u,v] /\ w IN {w | a' dot w = b'}`
      MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        MATCH_MP_TAC CONNECTED_IVT_HYPERPLANE THEN
        MAP_EVERY EXISTS_TAC [`v:real^3`; `u:real^3`] THEN
        ASM_SIMP_TAC[ENDS_IN_SEGMENT; CONNECTED_SEGMENT; REAL_LT_IMP_LE];
        REWRITE_TAC[IN_SEGMENT; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
        ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
        REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
        REWRITE_TAC[UNWIND_THM2; DOT_RADD; DOT_RMUL; CONJ_ASSOC] THEN
        DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
        MATCH_MP_TAC(REAL_ARITH `a < b ==> a = b ==> F`) THEN
        MATCH_MP_TAC REAL_CONVEX_BOUND_LT THEN ASM_REAL_ARITH_TAC];
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[SUBSET_INTER] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `convex hull t:real^3->bool` THEN
        REWRITE_TAC[HULL_SUBSET] THEN ASM SET_TAC[];
        ASM_REWRITE_TAC[SUBSET_INTER] THEN
        SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `convex hull {x:real^3 | a dot x = b}` THEN
        SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
        MATCH_MP_TAC(SET_RULE `s = t ==> s SUBSET t`) THEN
        REWRITE_TAC[CONVEX_HULL_EQ; CONVEX_HYPERPLANE]]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
    REPEAT LET_TAC THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `convex hull (s INTER {x:real^3 | a dot x = b}) =
        (convex hull s) INTER {x | a dot x = b}`
      SUBST1_TAC THENL
       [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [SIMP_TAC[SUBSET_INTER; HULL_MONO; INTER_SUBSET] THEN
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `convex hull {x:real^3 | a dot x = b}` THEN
          SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
          MATCH_MP_TAC(SET_RULE `s = t ==> s SUBSET t`) THEN
          REWRITE_TAC[CONVEX_HULL_EQ; CONVEX_HYPERPLANE];
          ALL_TAC] THEN
      ASM_CASES_TAC `s SUBSET {x:real^3 | a dot x = b}` THENL
       [ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s INTER t = s`] THEN SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
       `convex hull (convex hull (s INTER {x:real^3 | a dot x = b}) UNION
                     convex hull (s DIFF {x | a dot x = b})) INTER
        {x | a dot x = b}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `s SUBSET t ==> (s INTER u) SUBSET (t INTER u)`) THEN
        MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC(SET_RULE
         `s INTER t SUBSET (P hull (s INTER t)) /\
          s DIFF t SUBSET (P hull (s DIFF t))
          ==> s SUBSET (P hull (s INTER t)) UNION (P hull (s DIFF t))`) THEN
        REWRITE_TAC[HULL_SUBSET];
        ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) CONVEX_HULL_UNION_NONEMPTY_EXPLICIT o
        lhand o lhand o snd) THEN
      ANTS_TAC THENL
       [SIMP_TAC[CONVEX_CONVEX_HULL; CONVEX_HULL_EQ_EMPTY] THEN ASM SET_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[SUBSET; IN_INTER; IMP_CONJ; FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`p:real^3`; `u:real`; `q:real^3`] THEN
      REPLICATE_TAC 4 DISCH_TAC THEN ASM_CASES_TAC `u = &0` THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(&1 - &0) % p + &0 % q:real^N = p`] THEN
      MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `x < y ==> ~(x = y)`) THEN
        MATCH_MP_TAC(REAL_ARITH
         `(&1 - u) * p = (&1 - u) * b /\ u * q < u * b
          ==> (&1 - u) * p + u * q < b`) THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `p IN {x:real^3 | a dot x = b}` MP_TAC THENL
           [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
             `x IN s ==> s SUBSET t ==> x IN t`)) THEN
            MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HYPERPLANE] THEN
            SET_TAC[];
            SIMP_TAC[IN_ELIM_THM]];
          MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          ONCE_REWRITE_TAC[SET_RULE
           `(a:real^3) dot q < b <=> q IN {x | a dot x < b}`] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `x IN s ==> s SUBSET t ==> x IN t`)) THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_LT] THEN
          ASM_SIMP_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; REAL_LT_LE]];
        MATCH_MP_TAC(REAL_ARITH `x > y ==> ~(x = y)`) THEN
        MATCH_MP_TAC(REAL_ARITH
         `(&1 - u) * p = (&1 - u) * b /\ u * b < u * q
          ==> (&1 - u) * p + u * q > b`) THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `p IN {x:real^3 | a dot x = b}` MP_TAC THENL
           [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
             `x IN s ==> s SUBSET t ==> x IN t`)) THEN
            MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HYPERPLANE] THEN
            SET_TAC[];
            SIMP_TAC[IN_ELIM_THM]];
          MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; REWRITE_TAC[GSYM real_gt]] THEN
          ONCE_REWRITE_TAC[SET_RULE
           `(a:real^3) dot q > b <=> q IN {x | a dot x > b}`] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `x IN s ==> s SUBSET t ==> x IN t`)) THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_GT] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THEN
          ASM_SIMP_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; real_gt; REAL_LT_LE]]];
        ALL_TAC] THEN
      FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
        REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
        SIMP_TAC[SET_RULE `(!x. x IN s ==> P x) <=> s SUBSET {x | P x}`] THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_LE] THEN
        ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
        MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE THEN
        REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
        SIMP_TAC[SET_RULE `(!x. x IN s ==> P x) <=> s SUBSET {x | P x}`] THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_GE] THEN
        ASM_SIMP_TAC[SUBSET; IN_ELIM_THM]];
      ASM_REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim{x:real^3,y}` THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC[AFF_DIM_2] THEN
          ASM_MESON_TAC[CROSS_0; VECTOR_SUB_REFL; INT_LE_REFL];
          MATCH_MP_TAC AFF_DIM_SUBSET THEN
          REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
          CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN
          ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
          MAP_EVERY UNDISCH_TAC
           [`n cross (y - x) = a`; `(a:real^3) dot x = b`] THEN
          VEC3_TAC]] THEN
      REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC
       `aff_dim({x:real^3 | a dot x = b} INTER {x | n dot x = d})` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[AFF_DIM_AFFINE_INTER_HYPERPLANE; AFFINE_HYPERPLANE;
                   AFF_DIM_HYPERPLANE; DIMINDEX_3] THEN
      REPEAT(COND_CASES_TAC THEN CONV_TAC INT_REDUCE_CONV) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x + n:real^3` o
        GEN_REWRITE_RULE I [SUBSET]) THEN
      ASM_SIMP_TAC[IN_ELIM_THM; DOT_RADD; REAL_EQ_ADD_LCANCEL_0; DOT_EQ_0] THEN
      EXPAND_TAC "a" THEN VEC3_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Given a coplanar set, return exhaustive edge case theorem.                *)
(* ------------------------------------------------------------------------- *)

let COMPUTE_EDGES_CONV =
  let lemma = prove
   (`(x INSERT s) INTER {x | P x} =
                        if P x then x INSERT (s INTER {x | P x})
                        else s INTER {x | P x}`,
    COND_CASES_TAC THEN ASM SET_TAC[]) in
  fun tm ->
    let th1 = MATCH_MP COMPUTE_FACES_1 (COPLANAR_HYPERPLANE_RULE tm) in
    let th2 = MP (CONV_RULE(LAND_CONV
     (COMB2_CONV (RAND_CONV(PURE_REWRITE_CONV[FINITE_INSERT; FINITE_EMPTY]))
                 (RAND_CONV VECTOR3_EQ_0_CONV THENC
                  GEN_REWRITE_CONV I [NOT_CLAUSES]) THENC
      GEN_REWRITE_CONV I [AND_CLAUSES])) th1) TRUTH in
    CONV_RULE
     (BINDER_CONV(RAND_CONV
        (REWRITE_CONV[RIGHT_EXISTS_AND_THM] THENC
         REWRITE_CONV[EXISTS_IN_INSERT; NOT_IN_EMPTY] THENC
         REWRITE_CONV[FORALL_IN_INSERT; NOT_IN_EMPTY] THENC
         ONCE_DEPTH_CONV VECTOR3_SUB_CONV THENC
         ONCE_DEPTH_CONV VECTOR3_CROSS_CONV THENC
         ONCE_DEPTH_CONV let_CONV THENC
         ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV THENC
         REWRITE_CONV[real_ge] THENC
         ONCE_DEPTH_CONV VECTOR3_DOT_CONV THENC
         ONCE_DEPTH_CONV let_CONV THENC
         ONCE_DEPTH_CONV REAL_RAT5_LE_CONV THENC
         REWRITE_CONV[INSERT_AC] THENC REWRITE_CONV[DISJ_ACI] THENC
         REPEATC(CHANGED_CONV
          (ONCE_REWRITE_CONV[lemma] THENC
           ONCE_DEPTH_CONV(LAND_CONV VECTOR3_DOT_CONV THENC
                           REAL_RAT5_EQ_CONV) THENC
           REWRITE_CONV[])) THENC
         REWRITE_CONV[INTER_EMPTY] THENC
         REWRITE_CONV[INSERT_AC] THENC REWRITE_CONV[DISJ_ACI]
        ))) th2;;

(* ------------------------------------------------------------------------- *)
(* Use this to prove the number of edges per face for each Platonic solid.   *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_LEMMA = prove
 (`!x s n. 0 < n /\ ~(x IN s) /\ s HAS_SIZE (n - 1)
           ==> (x INSERT s) HAS_SIZE n`,
  REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT] THEN ASM_ARITH_TAC);;

let EDGES_PER_FACE_TAC th =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD  {e:real^3->bool | e face_of f /\ aff_dim(e) = &1}` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[FACE_OF_FACE; FACE_OF_TRANS; FACE_OF_IMP_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPEC `f:real^3->bool` th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  W(fun (_,w) -> REWRITE_TAC[COMPUTE_EDGES_CONV(find_term is_setenum w)]) THEN
  REWRITE_TAC[SET_RULE `x = a \/ x = b <=> x IN {a,b}`] THEN
  REWRITE_TAC[GSYM IN_INSERT; SET_RULE `{x | x IN s} = s`] THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC
   (MESON[HAS_SIZE] `s HAS_SIZE n ==> CARD s = n`) THEN
  REPEAT
  (MATCH_MP_TAC CARD_EQ_LEMMA THEN REPEAT CONJ_TAC THENL
    [CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
     REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; SEGMENT_EQ; DE_MORGAN_THM] THEN
     REPEAT CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
      `~(a = c /\ b = d) /\ ~(a = d /\ b = c) /\ ~(a = b /\ c = d)
       ==> ~({a,b} = {c,d})`) THEN
     PURE_ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
     CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
     CONV_TAC(ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV) THEN
     REWRITE_TAC[] THEN NO_TAC;
     ALL_TAC]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CONJUNCT1 HAS_SIZE_CLAUSES];;

let TETRAHEDRON_EDGES_PER_FACE = prove
 (`!f. f face_of std_tetrahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_tetrahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 3`,
  EDGES_PER_FACE_TAC TETRAHEDRON_FACETS);;

let CUBE_EDGES_PER_FACE = prove
 (`!f. f face_of std_cube /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_cube /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 4`,
  EDGES_PER_FACE_TAC CUBE_FACETS);;

let OCTAHEDRON_EDGES_PER_FACE = prove
 (`!f. f face_of std_octahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_octahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 3`,
  EDGES_PER_FACE_TAC OCTAHEDRON_FACETS);;

let DODECAHEDRON_EDGES_PER_FACE = prove
 (`!f. f face_of std_dodecahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_dodecahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 5`,
  EDGES_PER_FACE_TAC DODECAHEDRON_FACETS);;

let ICOSAHEDRON_EDGES_PER_FACE = prove
 (`!f. f face_of std_icosahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_icosahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 3`,
  EDGES_PER_FACE_TAC ICOSAHEDRON_FACETS);;

(* ------------------------------------------------------------------------- *)
(* Show that the Platonic solids are all full-dimensional.                   *)
(* ------------------------------------------------------------------------- *)

let POLYTOPE_3D_LEMMA = prove
 (`(let a = (z - x) cross (y - x) in
    ~(a = vec 0) /\ ?w. w IN s /\ ~(a dot w = a dot x))
   ==> aff_dim(convex hull (x INSERT y INSERT z INSERT s:real^3->bool)) = &3`,
  REPEAT GEN_TAC THEN LET_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM DIMINDEX_3; AFF_DIM_LE_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `aff_dim {w:real^3,x,y,z}` THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM SET_TAC[]] THEN
  ONCE_REWRITE_TAC[AFF_DIM_INSERT] THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `w IN {w:real^3 | a dot w = a dot x}` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `x IN s ==> s SUBSET t ==> x IN t`)) THEN
      MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
      UNDISCH_TAC `~(a:real^3 = vec 0)` THEN EXPAND_TAC "a" THEN VEC3_TAC;
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    UNDISCH_TAC `~(a:real^3 = vec 0)` THEN EXPAND_TAC "a" THEN
    REWRITE_TAC[CROSS_EQ_0; GSYM COLLINEAR_3] THEN
    REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; INSERT_AC; DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN INT_ARITH_TAC]);;

let POLYTOPE_FULLDIM_TAC =
  MATCH_MP_TAC POLYTOPE_3D_LEMMA THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_CROSS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN CONJ_TAC THENL
   [CONV_TAC(RAND_CONV VECTOR3_EQ_0_CONV) THEN REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV VECTOR3_DOT_CONV) THEN
    REWRITE_TAC[EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC(ONCE_DEPTH_CONV VECTOR3_DOT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_EQ_CONV) THEN
    REWRITE_TAC[]];;

let STD_TETRAHEDRON_FULLDIM = prove
 (`aff_dim std_tetrahedron = &3`,
  REWRITE_TAC[std_tetrahedron] THEN POLYTOPE_FULLDIM_TAC);;

let STD_CUBE_FULLDIM = prove
 (`aff_dim std_cube = &3`,
  REWRITE_TAC[std_cube] THEN POLYTOPE_FULLDIM_TAC);;

let STD_OCTAHEDRON_FULLDIM = prove
 (`aff_dim std_octahedron = &3`,
  REWRITE_TAC[std_octahedron] THEN POLYTOPE_FULLDIM_TAC);;

let STD_DODECAHEDRON_FULLDIM = prove
 (`aff_dim std_dodecahedron = &3`,
  REWRITE_TAC[STD_DODECAHEDRON] THEN POLYTOPE_FULLDIM_TAC);;

let STD_ICOSAHEDRON_FULLDIM = prove
 (`aff_dim std_icosahedron = &3`,
  REWRITE_TAC[STD_ICOSAHEDRON] THEN POLYTOPE_FULLDIM_TAC);;

(* ------------------------------------------------------------------------- *)
(* Complete list of edges for each Platonic solid.                           *)
(* ------------------------------------------------------------------------- *)

let COMPUTE_EDGES_TAC defn fulldim facets =
  GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   (vsubst[lhs(concl defn),`p:real^3->bool`]
      `?f:real^3->bool. (f face_of p /\ aff_dim f = &2) /\
                        (e face_of f /\ aff_dim e = &1)`) THEN
  CONJ_TAC THENL
   [EQ_TAC THENL [STRIP_TAC; MESON_TAC[FACE_OF_TRANS]] THEN
    MP_TAC(ISPECL [lhs(concl defn); `e:real^3->bool`]
        FACE_OF_POLYHEDRON_SUBSET_FACET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[defn] THEN
        MATCH_MP_TAC POLYHEDRON_CONVEX_HULL THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
        CONJ_TAC THEN
        DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^3->bool)->int`) THEN
        ASM_REWRITE_TAC[fulldim; AFF_DIM_EMPTY] THEN
        CONV_TAC INT_REDUCE_CONV];
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[facet_of] THEN
      REWRITE_TAC[fulldim] THEN CONV_TAC INT_REDUCE_CONV THEN
      ASM_MESON_TAC[FACE_OF_FACE]];
    REWRITE_TAC[facets] THEN
    REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
    REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2] THEN
    CONV_TAC(LAND_CONV(DEPTH_BINOP_CONV `\/`
     (fun tm -> REWR_CONV (COMPUTE_EDGES_CONV(rand(rand(lhand tm)))) tm))) THEN
    REWRITE_TAC[INSERT_AC] THEN REWRITE_TAC[DISJ_ACI]];;

let TETRAHEDRON_EDGES = prove
 (`!e. e face_of std_tetrahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[&1; &1; &1]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1; -- &1; -- &1], vector[&1; &1; &1]}`,
  COMPUTE_EDGES_TAC
    std_tetrahedron STD_TETRAHEDRON_FULLDIM TETRAHEDRON_FACETS);;

let CUBE_EDGES = prove
 (`!e. e face_of std_cube /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1]} \/
       e = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; -- &1], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; &1]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[&1; -- &1; &1]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[-- &1; &1; &1]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[&1; &1; -- &1]} \/
       e = convex hull {vector[-- &1; &1; &1], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1; -- &1; -- &1], vector[&1; -- &1; &1]} \/
       e = convex hull {vector[&1; -- &1; -- &1], vector[&1; &1; -- &1]} \/
       e = convex hull {vector[&1; -- &1; &1], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1; &1; -- &1], vector[&1; &1; &1]}`,
  COMPUTE_EDGES_TAC
    std_cube STD_CUBE_FULLDIM CUBE_FACETS);;

let OCTAHEDRON_EDGES = prove
 (`!e. e face_of std_octahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1; &0; &0], vector[&0; -- &1; &0]} \/
       e = convex hull {vector[-- &1; &0; &0], vector[&0; &1; &0]} \/
       e = convex hull {vector[-- &1; &0; &0], vector[&0; &0; -- &1]} \/
       e = convex hull {vector[-- &1; &0; &0], vector[&0; &0; &1]} \/
       e = convex hull {vector[&1; &0; &0], vector[&0; -- &1; &0]} \/
       e = convex hull {vector[&1; &0; &0], vector[&0; &1; &0]} \/
       e = convex hull {vector[&1; &0; &0], vector[&0; &0; -- &1]} \/
       e = convex hull {vector[&1; &0; &0], vector[&0; &0; &1]} \/
       e = convex hull {vector[&0; -- &1; &0], vector[&0; &0; -- &1]} \/
       e = convex hull {vector[&0; -- &1; &0], vector[&0; &0; &1]} \/
       e = convex hull {vector[&0; &1; &0], vector[&0; &0; -- &1]} \/
       e = convex hull {vector[&0; &1; &0], vector[&0; &0; &1]}`,
   COMPUTE_EDGES_TAC
     std_octahedron STD_OCTAHEDRON_FULLDIM OCTAHEDRON_FACETS);;

let DODECAHEDRON_EDGES = prove
 (`!e. e face_of std_dodecahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[-- &1; -- &1; &1]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[-- &1; &1; &1]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[-- &1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[-- &1; &1; -- &1]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1; -- &1; &1]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1; &1; -- &1]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[-- &1; -- &1; -- &1]} \/
       e = convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[-- &1; -- &1; &1]} \/
       e = convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[-- &1; &1; -- &1]} \/
       e = convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[-- &1; &1; &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[&1; -- &1; &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&1; &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; -- &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; -- &1; -- &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; -- &1; &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]}`,
  COMPUTE_EDGES_TAC
    STD_DODECAHEDRON STD_DODECAHEDRON_FULLDIM DODECAHEDRON_FACETS);;

let ICOSAHEDRON_EDGES = prove
 (`!e. e face_of std_icosahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]}`,
  COMPUTE_EDGES_TAC
    STD_ICOSAHEDRON STD_ICOSAHEDRON_FULLDIM ICOSAHEDRON_FACETS);;

(* ------------------------------------------------------------------------- *)
(* Enumerate all the vertices.                                               *)
(* ------------------------------------------------------------------------- *)

let COMPUTE_VERTICES_TAC defn fulldim edges =
  GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   (vsubst[lhs(concl defn),`p:real^3->bool`]
      `?e:real^3->bool. (e face_of p /\ aff_dim e = &1) /\
                        (v face_of e /\ aff_dim v = &0)`) THEN
  CONJ_TAC THENL
   [EQ_TAC THENL [STRIP_TAC; MESON_TAC[FACE_OF_TRANS]] THEN
    MP_TAC(ISPECL [lhs(concl defn); `v:real^3->bool`]
        FACE_OF_POLYHEDRON_SUBSET_FACET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[defn] THEN
        MATCH_MP_TAC POLYHEDRON_CONVEX_HULL THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
        CONJ_TAC THEN
        DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^3->bool)->int`) THEN
        ASM_REWRITE_TAC[fulldim; AFF_DIM_EMPTY] THEN
        CONV_TAC INT_REDUCE_CONV];
      REWRITE_TAC[facet_of] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real^3->bool` STRIP_ASSUME_TAC)] THEN
    MP_TAC(ISPECL [`f:real^3->bool`; `v:real^3->bool`]
        FACE_OF_POLYHEDRON_SUBSET_FACET) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FACE_OF_POLYHEDRON_POLYHEDRON THEN
        FIRST_ASSUM(fun th ->
          EXISTS_TAC (rand(concl th)) THEN
          CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC th]) THEN
        REWRITE_TAC[defn] THEN
        MATCH_MP_TAC POLYHEDRON_CONVEX_HULL THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
        ASM_MESON_TAC[FACE_OF_FACE];
        DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^3->bool)->int`) THEN
        ASM_REWRITE_TAC[fulldim; AFF_DIM_EMPTY] THEN
        CONV_TAC INT_REDUCE_CONV;
        DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^3->bool)->int`) THEN
        ASM_REWRITE_TAC[fulldim; AFF_DIM_EMPTY] THEN
        CONV_TAC INT_REDUCE_CONV];
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[facet_of] THEN
      ASM_REWRITE_TAC[fulldim] THEN CONV_TAC INT_REDUCE_CONV THEN
      ASM_MESON_TAC[FACE_OF_FACE; FACE_OF_TRANS]];
    REWRITE_TAC[edges] THEN
    REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
    REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2] THEN
    REWRITE_TAC[AFF_DIM_EQ_0; RIGHT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[MESON[]
     `v face_of s /\ v = {a} <=> {a} face_of s /\ v = {a}`] THEN
    REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; FACE_OF_SING] THEN
    REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN
    REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
    REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2] THEN
    REWRITE_TAC[DISJ_ACI]];;

let TETRAHEDRON_VERTICES = prove
 (`!v. v face_of std_tetrahedron /\ aff_dim v = &0 <=>
       v = {vector [-- &1; -- &1; &1]} \/
       v = {vector [-- &1; &1; -- &1]} \/
       v = {vector [&1; -- &1; -- &1]} \/
       v = {vector [&1; &1; &1]}`,
  COMPUTE_VERTICES_TAC
    std_tetrahedron STD_TETRAHEDRON_FULLDIM TETRAHEDRON_EDGES);;

let CUBE_VERTICES = prove
 (`!v. v face_of std_cube /\ aff_dim v = &0 <=>
       v = {vector [-- &1; -- &1; -- &1]} \/
       v = {vector [-- &1; -- &1; &1]} \/
       v = {vector [-- &1; &1; -- &1]} \/
       v = {vector [-- &1; &1; &1]} \/
       v = {vector [&1; -- &1; -- &1]} \/
       v = {vector [&1; -- &1; &1]} \/
       v = {vector [&1; &1; -- &1]} \/
       v = {vector [&1; &1; &1]}`,
  COMPUTE_VERTICES_TAC
    std_cube STD_CUBE_FULLDIM CUBE_EDGES);;

let OCTAHEDRON_VERTICES = prove
 (`!v. v face_of std_octahedron /\ aff_dim v = &0 <=>
       v = {vector [-- &1; &0; &0]} \/
       v = {vector [&1; &0; &0]} \/
       v = {vector [&0; -- &1; &0]} \/
       v = {vector [&0; &1; &0]} \/
       v = {vector [&0; &0; -- &1]} \/
       v = {vector [&0; &0; &1]}`,
   COMPUTE_VERTICES_TAC
     std_octahedron STD_OCTAHEDRON_FULLDIM OCTAHEDRON_EDGES);;

let DODECAHEDRON_VERTICES = prove
 (`!v. v face_of std_dodecahedron /\ aff_dim v = &0 <=>
       v = {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       v = {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       v = {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       v = {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       v = {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       v = {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       v = {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector[-- &1; -- &1; -- &1]} \/
       v = {vector[-- &1; -- &1; &1]} \/
       v = {vector[-- &1; &1; -- &1]} \/
       v = {vector[-- &1; &1; &1]} \/
       v = {vector[&1; -- &1; -- &1]} \/
       v = {vector[&1; -- &1; &1]} \/
       v = {vector[&1; &1; -- &1]} \/
       v = {vector[&1; &1; &1]} \/
       v = {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       v = {vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]}`,
  COMPUTE_VERTICES_TAC
    STD_DODECAHEDRON STD_DODECAHEDRON_FULLDIM DODECAHEDRON_EDGES);;

let ICOSAHEDRON_VERTICES = prove
 (`!v. v face_of std_icosahedron /\ aff_dim v = &0 <=>
       v = {vector [-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1]} \/
       v = {vector [-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1]} \/
       v = {vector [&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1]} \/
       v = {vector [&1 / &2 + &1 / &2 * sqrt (&5); &0; &1]} \/
       v = {vector [-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       v = {vector [-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       v = {vector [&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       v = {vector [&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       v = {vector [&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector [&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       v = {vector [&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector [&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]}`,
  COMPUTE_VERTICES_TAC
    STD_ICOSAHEDRON STD_ICOSAHEDRON_FULLDIM ICOSAHEDRON_EDGES);;

(* ------------------------------------------------------------------------- *)
(* Number of edges meeting at each vertex.                                   *)
(* ------------------------------------------------------------------------- *)

let EDGES_PER_VERTEX_TAC defn edges verts =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   (vsubst[lhs(concl defn),`p:real^3->bool`]
     `CARD {e | (e face_of p /\ aff_dim(e) = &1) /\
                (v:real^3->bool) face_of e}`) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[FACE_OF_FACE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `v:real^3->bool` verts) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[edges] THEN
  REWRITE_TAC[SET_RULE
   `{e | (P e \/ Q e) /\ R e} =
    {e | P e /\ R e} UNION {e | Q e /\ R e}`] THEN
  REWRITE_TAC[MESON[FACE_OF_SING]
   `e = a /\ {x} face_of e <=> e = a /\ x extreme_point_of a`] THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; EXTREME_POINT_OF_SEGMENT] THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV) THEN
  REWRITE_TAC[EMPTY_GSPEC; UNION_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{x | x = a} = {a}`] THEN
  REWRITE_TAC[SET_RULE `{x} UNION s = x INSERT s`] THEN MATCH_MP_TAC
   (MESON[HAS_SIZE] `s HAS_SIZE n ==> CARD s = n`) THEN
  REPEAT
  (MATCH_MP_TAC CARD_EQ_LEMMA THEN REPEAT CONJ_TAC THENL
    [CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
     REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM; SEGMENT_EQ] THEN
     REPEAT CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
      `~(a = c /\ b = d) /\ ~(a = d /\ b = c) /\ ~(a = b /\ c = d)
       ==> ~({a,b} = {c,d})`) THEN
     PURE_ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
     CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
     CONV_TAC(ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV) THEN
     REWRITE_TAC[] THEN NO_TAC;
     ALL_TAC]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CONJUNCT1 HAS_SIZE_CLAUSES];;

let TETRAHEDRON_EDGES_PER_VERTEX = prove
 (`!v. v face_of std_tetrahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_tetrahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 3`,
  EDGES_PER_VERTEX_TAC
    std_tetrahedron TETRAHEDRON_EDGES TETRAHEDRON_VERTICES);;

let CUBE_EDGES_PER_VERTEX = prove
 (`!v. v face_of std_cube /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_cube /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 3`,
  EDGES_PER_VERTEX_TAC
    std_cube CUBE_EDGES CUBE_VERTICES);;

let OCTAHEDRON_EDGES_PER_VERTEX = prove
 (`!v. v face_of std_octahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_octahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 4`,
  EDGES_PER_VERTEX_TAC
    std_octahedron OCTAHEDRON_EDGES OCTAHEDRON_VERTICES);;

let DODECAHEDRON_EDGES_PER_VERTEX = prove
 (`!v. v face_of std_dodecahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_dodecahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 3`,
  EDGES_PER_VERTEX_TAC
    STD_DODECAHEDRON DODECAHEDRON_EDGES DODECAHEDRON_VERTICES);;

let ICOSAHEDRON_EDGES_PER_VERTEX = prove
 (`!v. v face_of std_icosahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_icosahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 5`,
  EDGES_PER_VERTEX_TAC
    STD_ICOSAHEDRON ICOSAHEDRON_EDGES ICOSAHEDRON_VERTICES);;

(* ------------------------------------------------------------------------- *)
(* Number of Platonic solids.                                                *)
(* ------------------------------------------------------------------------- *)

let MULTIPLE_COUNTING_LEMMA = prove
 (`!R:A->B->bool s t.
        FINITE s /\ FINITE t /\
        (!x. x IN s ==> CARD {y | y IN t /\ R x y} = m) /\
        (!y. y IN t ==> CARD {x | x IN s /\ R x y} = n)
        ==> m * CARD s = n * CARD t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`R:A->B->bool`; `\x:A y:B. 1`; `s:A->bool`; `t:B->bool`]
        NSUM_NSUM_RESTRICT) THEN
  ASM_SIMP_TAC[NSUM_CONST; FINITE_RESTRICT] THEN ARITH_TAC);;

let SIZE_ZERO_DIMENSIONAL_FACES = prove
 (`!s:real^N->bool.
        polyhedron s
        ==> CARD {f | f face_of s /\ aff_dim f = &0} =
            CARD {v | v extreme_point_of s} /\
            (FINITE {f | f face_of s /\ aff_dim f = &0} <=>
             FINITE {v | v extreme_point_of s}) /\
            (!n. {f | f face_of s /\ aff_dim f = &0} HAS_SIZE n <=>
                 {v | v extreme_point_of s} HAS_SIZE n)`,
  REWRITE_TAC[RIGHT_AND_FORALL_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `{f | f face_of s /\ aff_dim f = &0} =
                IMAGE (\v:real^N. {v}) {v | v extreme_point_of s}`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC[AFF_DIM_SING; FACE_OF_SING; IN_ELIM_THM] THEN
    REWRITE_TAC[AFF_DIM_EQ_0] THEN MESON_TAC[];
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC CARD_IMAGE_INJ;
      MATCH_MP_TAC FINITE_IMAGE_INJ_EQ;
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ_EQ] THEN
    ASM_SIMP_TAC[FINITE_POLYHEDRON_EXTREME_POINTS] THEN SET_TAC[]]);;

let PLATONIC_SOLIDS_LIMITS = prove
 (`!p:real^3->bool m n.
    polytope p /\ aff_dim p = &3 /\
    (!f. f face_of p /\ aff_dim(f) = &2
         ==> CARD {e | e face_of p /\ aff_dim(e) = &1 /\ e SUBSET f} = m) /\
    (!v. v face_of p /\ aff_dim(v) = &0
         ==> CARD {e | e face_of p /\ aff_dim(e) = &1 /\ v SUBSET e} = n)
    ==> m = 3 /\ n = 3 \/       // Tetrahedron
        m = 4 /\ n = 3 \/       // Cube
        m = 3 /\ n = 4 \/       // Octahedron
        m = 5 /\ n = 3 \/       // Dodecahedron
        m = 3 /\ n = 5          // Icosahedron`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `p:real^3->bool` EULER_RELATION) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `m * CARD {f:real^3->bool | f face_of p /\ aff_dim f = &2} =
    2 * CARD {e | e face_of p /\ aff_dim e = &1} /\
    n * CARD {v | v face_of p /\ aff_dim v = &0} =
    2 * CARD {e | e face_of p /\ aff_dim e = &1}`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MULTIPLE_COUNTING_LEMMA THENL
     [EXISTS_TAC `\(f:real^3->bool) (e:real^3->bool). e SUBSET f`;
      EXISTS_TAC `\(v:real^3->bool) (e:real^3->bool). v SUBSET e`] THEN
    ONCE_REWRITE_TAC[SET_RULE `f face_of s <=> f IN {f | f face_of s}`] THEN
    ASM_SIMP_TAC[FINITE_POLYTOPE_FACES; FINITE_RESTRICT] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
    X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`p:real^3->bool`; `e:real^3->bool`]
          POLYHEDRON_RIDGE_TWO_FACETS) THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_POLYHEDRON] THEN ANTS_TAC THENL
       [CONV_TAC INT_REDUCE_CONV THEN DISCH_THEN SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN ASM_INT_ARITH_TAC;
        CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [`f1:real^3->bool`; `f2:real^3->bool`] THEN
        STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `CARD {f1:real^3->bool,f2}` THEN CONJ_TAC THENL
         [AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
          REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
          ASM_MESON_TAC[];
          ASM_SIMP_TAC[CARD_CLAUSES; IN_INSERT; FINITE_RULES;
                       NOT_IN_EMPTY; ARITH]]];
      SUBGOAL_THEN `?a b:real^3. e = segment[a,b]` STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC COMPACT_CONVEX_COLLINEAR_SEGMENT THEN
        REPEAT CONJ_TAC THENL
         [DISCH_THEN SUBST_ALL_TAC THEN
          RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN ASM_INT_ARITH_TAC;
          MATCH_MP_TAC FACE_OF_IMP_COMPACT THEN
          EXISTS_TAC `p:real^3->bool` THEN
          ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_COMPACT];
          ASM_MESON_TAC[FACE_OF_IMP_CONVEX];
          MP_TAC(ISPEC `e:real^3->bool` AFF_DIM) THEN
          DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` MP_TAC) THEN
          ASM_REWRITE_TAC[INT_ARITH `&1:int = b - &1 <=> b = &2`] THEN
          DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC) THEN
          ASM_CASES_TAC `FINITE(b:real^3->bool)` THENL
           [ALL_TAC; ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]] THEN
          REWRITE_TAC[INT_OF_NUM_EQ] THEN STRIP_TAC THEN
          SUBGOAL_THEN `(b:real^3->bool) HAS_SIZE 2` MP_TAC THENL
           [ASM_REWRITE_TAC[HAS_SIZE]; CONV_TAC(LAND_CONV HAS_SIZE_CONV)] THEN
          REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
          REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
          ASM_MESON_TAC[HULL_SUBSET]];
        ASM_CASES_TAC `a:real^3 = b` THENL
         [UNDISCH_TAC `aff_dim(e:real^3->bool) = &1` THEN
          ASM_REWRITE_TAC[SEGMENT_REFL; AFF_DIM_SING; INT_OF_NUM_EQ; ARITH_EQ];
          ALL_TAC] THEN
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `CARD {v:real^3 | v extreme_point_of segment[a,b]}` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN
          EXISTS_TAC `\v:real^3. {v}` THEN
          REWRITE_TAC[IN_ELIM_THM; FACE_OF_SING; AFF_DIM_SING] THEN
          REPEAT CONJ_TAC THENL
           [ASM_REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN
            REWRITE_TAC[SET_RULE `{x | x = a \/ x = b} = {a,b}`] THEN
            REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
            X_GEN_TAC `v:real^3` THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
            ASM_MESON_TAC[FACE_OF_TRANS; FACE_OF_IMP_SUBSET];
            X_GEN_TAC `s:real^3->bool` THEN REWRITE_TAC[AFF_DIM_EQ_0] THEN
            DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
            DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
            DISCH_THEN(X_CHOOSE_THEN `v:real^3` SUBST_ALL_TAC) THEN
            REWRITE_TAC[EXISTS_UNIQUE] THEN EXISTS_TAC `v:real^3` THEN
            ASM_REWRITE_TAC[GSYM FACE_OF_SING] THEN CONJ_TAC THENL
             [ASM_MESON_TAC[FACE_OF_FACE]; SET_TAC[]]];
          ASM_REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN
          REWRITE_TAC[SET_RULE `{x | x = a \/ x = b} = {a,b}`] THEN
          ASM_SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; FINITE_EMPTY] THEN
          ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY; ARITH]]]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (ARITH_RULE
   `(a + b) - c = 2 ==> a + b = c + 2`)) THEN
  SUBGOAL_THEN `4 <= CARD {v:real^3->bool | v face_of p /\ aff_dim v = &0}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[SIZE_ZERO_DIMENSIONAL_FACES; POLYTOPE_IMP_POLYHEDRON] THEN
    MP_TAC(ISPEC `p:real^3->bool` POLYTOPE_VERTEX_LOWER_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[INT_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `4 <= CARD {f:real^3->bool | f face_of p /\ aff_dim f = &2}`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `p:real^3->bool` POLYTOPE_FACET_LOWER_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[INT_OF_NUM_LE; facet_of] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONV_TAC INT_REDUCE_CONV THEN GEN_TAC THEN EQ_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[INT_ARITH `~(&2:int = -- &1)`; AFF_DIM_EMPTY];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `v + f = e + 2 ==> 4 <= v /\ 4 <= f ==> 6 <= e`)) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC
   `CARD {e:real^3->bool | e face_of p /\ aff_dim e = &1} = 0` THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `3 <= m` ASSUME_TAC THENL
   [ASM_CASES_TAC `{f:real^3->bool | f face_of p /\ aff_dim f = &2} = {}` THENL
     [UNDISCH_TAC
       `4 <= CARD {f:real^3->bool | f face_of p /\ aff_dim f = &2}` THEN
      ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY])] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^3->bool` MP_TAC) THEN
    DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
     FIRST_X_ASSUM(SUBST1_TAC o SYM o C MATCH_MP th)) THEN
    MP_TAC(ISPEC `f:real^3->bool` POLYTOPE_FACET_LOWER_BOUND) THEN
    ASM_REWRITE_TAC[facet_of] THEN CONV_TAC INT_REDUCE_CONV THEN
    ANTS_TAC THENL [ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE]; ALL_TAC] THEN
    REWRITE_TAC[INT_OF_NUM_LE] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONV_TAC INT_REDUCE_CONV THEN X_GEN_TAC `e:real^3->bool` THEN
    EQ_TAC THEN ASM_CASES_TAC `e:real^3->bool = {}` THEN
    ASM_SIMP_TAC[AFF_DIM_EMPTY] THEN CONV_TAC INT_REDUCE_CONV THENL
     [ASM_MESON_TAC[FACE_OF_TRANS; FACE_OF_IMP_SUBSET];
      ASM_MESON_TAC[FACE_OF_FACE]];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `3 <= m ==> ~(m = 0)`)) THEN
  ASM_CASES_TAC `n = 0` THENL
   [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `0 * x = 2 * e ==> e = 0`)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (NUM_RING
    `v + f = e + 2 ==> !m n. m * n * v + n * m * f = m * n * (e + 2)`)) THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num`; `n:num`]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `m * 2 * e + n * 2 * e = m * n * (e + 2) <=>
                          e * 2 * (m + n) = m * n * (e + 2)`] THEN
  ABBREV_TAC `E = CARD {e:real^3->bool | e face_of p /\ aff_dim e = &1}` THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; ARITH_RULE
     `E * 2 * (n + 1) = n * (E + 2) <=> E * (n + 2) = 2 * n`] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    MATCH_MP_TAC(ARITH_RULE `n:num < m ==> ~(m = n)`) THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 * (m + 2)` THEN
    CONJ_TAC THENL [ARITH_TAC; MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 2` THENL
   [ASM_REWRITE_TAC[ARITH_RULE `E * 2 * (n + 2) = n * 2 * (E + 2) <=>
                                E = n`] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (NUM_RING
     `E * c = 2 * E ==> E = 0 \/ c = 2`)) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `3 <= n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `m * n < 2 * (m + n)` THENL
   [DISCH_TAC;
    DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
    SUBGOAL_THEN `E * 2 * (m + n) <= E * m * n` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[ARITH_RULE `m * n * (E + 2) <= E * m * n <=>
                                  2 * m * n = 0`] THEN
      MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
      REWRITE_TAC[MULT_EQ_0] THEN ASM_ARITH_TAC]] THEN
  SUBGOAL_THEN `&m - &2:real < &4 /\ &n - &2 < &4` MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC `&n - &2`;
      MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&m - &2`] THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_OF_NUM_LT;
                 ARITH_RULE `2 < n <=> 3 <= n`] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&4` THEN
    REWRITE_TAC[REAL_ARITH `(m - &2) * (n - &2) < &4 <=>
                            m * n < &2 * (m + n)`] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_SUB_RDISTRIB; REAL_LE_SUB_LADD] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_SUB_RADD; REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN
  REWRITE_TAC[ARITH_RULE `m < 4 + 2 <=> m <= 5`] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `3 <= m ==> (m <= 5 <=> m = 3 \/ m = 4 \/ m = 5)`] THEN
  STRIP_TAC THEN UNDISCH_TAC `E * 2 * (m + n) = m * n * (E + 2)` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* If-and-only-if version.                                                   *)
(* ------------------------------------------------------------------------- *)

let PLATONIC_SOLIDS = prove
 (`!m n.
   (?p:real^3->bool.
     polytope p /\ aff_dim p = &3 /\
     (!f. f face_of p /\ aff_dim(f) = &2
          ==> CARD {e | e face_of p /\ aff_dim(e) = &1 /\ e SUBSET f} = m) /\
     (!v. v face_of p /\ aff_dim(v) = &0
          ==> CARD {e | e face_of p /\ aff_dim(e) = &1 /\ v SUBSET e} = n)) <=>
     m = 3 /\ n = 3 \/       // Tetrahedron
     m = 4 /\ n = 3 \/       // Cube
     m = 3 /\ n = 4 \/       // Octahedron
     m = 5 /\ n = 3 \/       // Dodecahedron
     m = 3 /\ n = 5          // Icosahedron`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; PLATONIC_SOLIDS_LIMITS] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `std_tetrahedron` THEN
    ASM_REWRITE_TAC[TETRAHEDRON_EDGES_PER_VERTEX; TETRAHEDRON_EDGES_PER_FACE;
                    STD_TETRAHEDRON_FULLDIM] THEN
    REWRITE_TAC[std_tetrahedron] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    EXISTS_TAC `std_cube` THEN
    ASM_REWRITE_TAC[CUBE_EDGES_PER_VERTEX; CUBE_EDGES_PER_FACE;
                    STD_CUBE_FULLDIM] THEN
    REWRITE_TAC[std_cube] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    EXISTS_TAC `std_octahedron` THEN
    ASM_REWRITE_TAC[OCTAHEDRON_EDGES_PER_VERTEX; OCTAHEDRON_EDGES_PER_FACE;
                    STD_OCTAHEDRON_FULLDIM] THEN
    REWRITE_TAC[std_octahedron] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    EXISTS_TAC `std_dodecahedron` THEN
    ASM_REWRITE_TAC[DODECAHEDRON_EDGES_PER_VERTEX; DODECAHEDRON_EDGES_PER_FACE;
                    STD_DODECAHEDRON_FULLDIM] THEN
    REWRITE_TAC[STD_DODECAHEDRON] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    EXISTS_TAC `std_icosahedron` THEN
    ASM_REWRITE_TAC[ICOSAHEDRON_EDGES_PER_VERTEX; ICOSAHEDRON_EDGES_PER_FACE;
                    STD_ICOSAHEDRON_FULLDIM] THEN
    REWRITE_TAC[STD_ICOSAHEDRON] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY]]);;

(* ------------------------------------------------------------------------- *)
(* Show that the regular polyhedra do have all edges and faces congruent.    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("congruent",(12,"right"));;

let congruent = new_definition
 `(s:real^N->bool) congruent (t:real^N->bool) <=>
        ?c f. orthogonal_transformation f /\ t = IMAGE (\x. c + f x) s`;;

let CONGRUENT_SIMPLE = prove
 (`(?A:real^3^3. orthogonal_matrix A /\ IMAGE (\x:real^3. A ** x) s = t)
   ==> (convex hull s) congruent (convex hull t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN
  SIMP_TAC[CONVEX_HULL_LINEAR_IMAGE; MATRIX_VECTOR_MUL_LINEAR] THEN
  REWRITE_TAC[congruent] THEN EXISTS_TAC `vec 0:real^3` THEN
  EXISTS_TAC `\x:real^3. (A:real^3^3) ** x` THEN
  REWRITE_TAC[VECTOR_ADD_LID; ORTHOGONAL_TRANSFORMATION_MATRIX] THEN
  ASM_SIMP_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; MATRIX_VECTOR_MUL_LINEAR]);;

let CONGRUENT_SEGMENTS = prove
 (`!a b c d:real^N.
        dist(a,b) = dist(c,d)
        ==> segment[a,b] congruent segment[c,d]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b - a:real^N`; `d - c:real^N`]
    ORTHOGONAL_TRANSFORMATION_EXISTS) THEN
  ANTS_TAC THENL [POP_ASSUM MP_TAC THEN NORM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[congruent] THEN
  EXISTS_TAC `c - (f:real^N->real^N) a` THEN
  EXISTS_TAC `f:real^N->real^N` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  SUBGOAL_THEN
   `(\x. (c - f a) + (f:real^N->real^N) x) = (\x. (c - f a) + x) o f`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM CONVEX_HULL_LINEAR_IMAGE; SEGMENT_CONVEX_HULL; IMAGE_o;
               GSYM CONVEX_HULL_TRANSLATION] THEN
  REWRITE_TAC[IMAGE_CLAUSES] THEN
  AP_TERM_TAC THEN BINOP_TAC THENL
   [VECTOR_ARITH_TAC; AP_THM_TAC THEN AP_TERM_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `d:real^N = c - a + b <=> b - a = d - c`] THEN
  ASM_MESON_TAC[LINEAR_SUB]);;

let compute_dist =
  let mk_sub = mk_binop `(-):real^3->real^3->real^3`
  and dot_tm = `(dot):real^3->real^3->real` in
  fun v1 v2 -> let vth = VECTOR3_SUB_CONV(mk_sub v1 v2) in
               let dth = CONV_RULE(RAND_CONV VECTOR3_DOT_CONV)
                          (MK_COMB(AP_TERM dot_tm vth,vth)) in
               rand(concl dth);;

let le_rat5 =
  let mk_le = mk_binop `(<=):real->real->bool` and t_tm = `T` in
  fun r1 r2 -> rand(concl(REAL_RAT5_LE_CONV(mk_le r1 r2))) = t_tm;;

let three_adjacent_points s =
  match s with
  | x::t -> let (y,_)::(z,_)::_ =
              sort (fun (_,r1) (_,r2) -> le_rat5 r1 r2)
                   (map (fun y -> y,compute_dist x y) t) in
            x,y,z
  | _ -> failwith "three_adjacent_points: no points";;

let mk_33matrix =
  let a11_tm = `a11:real`
  and a12_tm = `a12:real`
  and a13_tm = `a13:real`
  and a21_tm = `a21:real`
  and a22_tm = `a22:real`
  and a23_tm = `a23:real`
  and a31_tm = `a31:real`
  and a32_tm = `a32:real`
  and a33_tm = `a33:real`
  and pat_tm =
   `vector[vector[a11; a12; a13];
           vector[a21; a22; a23];
           vector[a31; a32; a33]]:real^3^3` in
  fun [a11;a12;a13;a21;a22;a23;a31;a32;a33] ->
    vsubst[a11,a11_tm;
           a12,a12_tm;
           a13,a13_tm;
           a21,a21_tm;
           a22,a22_tm;
           a23,a23_tm;
           a31,a31_tm;
           a32,a32_tm;
           a33,a33_tm] pat_tm;;

let MATRIX_VECTOR_MUL_3 = prove
 (`(vector[vector[a11;a12;a13];
           vector[a21; a22; a23];
           vector[a31; a32; a33]]:real^3^3) **
   (vector[x1;x2;x3]:real^3) =
   vector[a11 * x1 + a12 * x2 + a13 * x3;
          a21 * x1 + a22 * x2 + a23 * x3;
          a31 * x1 + a32 * x2 + a33 * x3]`,
  SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA] THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3; SUM_3; VECTOR_3]);;

let MATRIX_LEMMA = prove
 (`!A:real^3^3.
   A ** x1 = x2 /\
   A ** y1 = y2 /\
   A ** z1 = z2 <=>
   (vector [x1; y1; z1]:real^3^3) ** (row 1 A:real^3) =
   vector [x2$1; y2$1; z2$1] /\
   (vector [x1; y1; z1]:real^3^3) ** (row 2 A:real^3) =
   vector [x2$2; y2$2; z2$2] /\
   (vector [x1; y1; z1]:real^3^3) ** (row 3 A:real^3) =
   vector [x2$3; y2$3; z2$3]`,
  SIMP_TAC[CART_EQ; transp; matrix_vector_mul; row; VECTOR_3; LAMBDA_BETA] THEN
  REWRITE_TAC[FORALL_3; DIMINDEX_3; VECTOR_3; SUM_3] THEN REAL_ARITH_TAC);;

let MATRIX_BY_CRAMER_LEMMA = prove
 (`!A:real^3^3.
        ~(det(vector[x1; y1; z1]:real^3^3) = &0)
        ==> (A ** x1 = x2 /\
             A ** y1 = y2 /\
             A ** z1 = z2 <=>
             A = lambda m k. det((lambda i j.
                                  if j = k
                                  then (vector[x2$m; y2$m; z2$m]:real^3)$i
                                  else (vector[x1; y1; z1]:real^3^3)$i$j)
                                 :real^3^3) /
                             det(vector[x1;y1;z1]:real^3^3))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [MATRIX_LEMMA] THEN
  ASM_SIMP_TAC[CRAMER] THEN REWRITE_TAC[CART_EQ; row] THEN
  SIMP_TAC[LAMBDA_BETA] THEN REWRITE_TAC[DIMINDEX_3; FORALL_3]);;

let MATRIX_BY_CRAMER = prove
 (`!A:real^3^3 x1 y1 z1 x2 y2 z2.
        let d = det(vector[x1; y1; z1]:real^3^3) in
        ~(d = &0)
        ==> (A ** x1 = x2 /\
             A ** y1 = y2 /\
             A ** z1 = z2 <=>
               A$1$1 =
               (x2$1 * y1$2 * z1$3 +
                x1$2 * y1$3 * z2$1 +
                x1$3 * y2$1 * z1$2 -
                x2$1 * y1$3 * z1$2 -
                x1$2 * y2$1 * z1$3 -
                x1$3 * y1$2 * z2$1) / d /\
               A$1$2 =
               (x1$1 * y2$1 * z1$3 +
                x2$1 * y1$3 * z1$1 +
                x1$3 * y1$1 * z2$1 -
                x1$1 * y1$3 * z2$1 -
                x2$1 * y1$1 * z1$3 -
                x1$3 * y2$1 * z1$1) / d /\
               A$1$3 =
               (x1$1 * y1$2 * z2$1 +
                x1$2 * y2$1 * z1$1 +
                x2$1 * y1$1 * z1$2 -
                x1$1 * y2$1 * z1$2 -
                x1$2 * y1$1 * z2$1 -
                x2$1 * y1$2 * z1$1) / d /\
               A$2$1 =
               (x2$2 * y1$2 * z1$3 +
                x1$2 * y1$3 * z2$2 +
                x1$3 * y2$2 * z1$2 -
                x2$2 * y1$3 * z1$2 -
                x1$2 * y2$2 * z1$3 -
                x1$3 * y1$2 * z2$2) / d /\
               A$2$2 =
               (x1$1 * y2$2 * z1$3 +
                x2$2 * y1$3 * z1$1 +
                x1$3 * y1$1 * z2$2 -
                x1$1 * y1$3 * z2$2 -
                x2$2 * y1$1 * z1$3 -
                x1$3 * y2$2 * z1$1) / d /\
               A$2$3 =
               (x1$1 * y1$2 * z2$2 +
                x1$2 * y2$2 * z1$1 +
                x2$2 * y1$1 * z1$2 -
                x1$1 * y2$2 * z1$2 -
                x1$2 * y1$1 * z2$2 -
                x2$2 * y1$2 * z1$1) / d /\
               A$3$1 =
               (x2$3 * y1$2 * z1$3 +
                x1$2 * y1$3 * z2$3 +
                x1$3 * y2$3 * z1$2 -
                x2$3 * y1$3 * z1$2 -
                x1$2 * y2$3 * z1$3 -
                x1$3 * y1$2 * z2$3) / d /\
               A$3$2 =
               (x1$1 * y2$3 * z1$3 +
                x2$3 * y1$3 * z1$1 +
                x1$3 * y1$1 * z2$3 -
                x1$1 * y1$3 * z2$3 -
                x2$3 * y1$1 * z1$3 -
                x1$3 * y2$3 * z1$1) / d /\
               A$3$3 =
               (x1$1 * y1$2 * z2$3 +
                x1$2 * y2$3 * z1$1 +
                x2$3 * y1$1 * z1$2 -
                x1$1 * y2$3 * z1$2 -
                x1$2 * y1$1 * z2$3 -
                x2$3 * y1$2 * z1$1) / d)`,
  REPEAT GEN_TAC THEN CONV_TAC let_CONV THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MATRIX_BY_CRAMER_LEMMA] THEN
  REWRITE_TAC[DET_3; CART_EQ] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; ARITH; VECTOR_3] THEN
  REWRITE_TAC[FORALL_3; ARITH; VECTOR_3] THEN REWRITE_TAC[CONJ_ACI]);;

let CONGRUENT_EDGES_TAC edges =
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REWRITE_TAC[IMP_IMP] THEN
  REWRITE_TAC[edges] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
  MATCH_MP_TAC CONGRUENT_SEGMENTS THEN REWRITE_TAC[DIST_EQ] THEN
  REWRITE_TAC[dist; NORM_POW_2] THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_DOT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_EQ_CONV) THEN
  REWRITE_TAC[];;

let CONGRUENT_FACES_TAC facets =
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REWRITE_TAC[IMP_IMP] THEN
  REWRITE_TAC[facets] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  W(fun (asl,w) ->
        let t1 = rand(lhand w) and t2 = rand(rand w) in
        let (x1,y1,z1) = three_adjacent_points (dest_setenum t1)
        and (x2,y2,z2) = three_adjacent_points (dest_setenum t2) in
        let th1 = SPECL [`A:real^3^3`;x1;y1;z1;x2;y2;z2] MATRIX_BY_CRAMER in
        let th2 = REWRITE_RULE[VECTOR_3; DET_3] th1 in
        let th3 = CONV_RULE (DEPTH_CONV REAL_RAT5_MUL_CONV) th2 in
        let th4 = CONV_RULE (DEPTH_CONV
         (REAL_RAT5_ADD_CONV ORELSEC REAL_RAT5_SUB_CONV)) th3 in
        let th5 = CONV_RULE let_CONV th4 in
        let th6 = CONV_RULE(ONCE_DEPTH_CONV REAL_RAT5_DIV_CONV) th5 in
        let th7 = CONV_RULE(ONCE_DEPTH_CONV REAL_RAT5_EQ_CONV) th6 in
        let th8 = MP th7 (EQT_ELIM(REWRITE_CONV[] (lhand(concl th7)))) in
        let tms = map rhs (conjuncts(rand(concl th8))) in
        let matt = mk_33matrix tms in
        MATCH_MP_TAC CONGRUENT_SIMPLE THEN EXISTS_TAC matt THEN CONJ_TAC THENL
         [REWRITE_TAC[ORTHOGONAL_MATRIX; CART_EQ] THEN
          SIMP_TAC[transp; LAMBDA_BETA; matrix_mul; mat] THEN
          REWRITE_TAC[DIMINDEX_3; SUM_3; FORALL_3; VECTOR_3; ARITH] THEN
          CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_MUL_CONV) THEN
          CONV_TAC(DEPTH_CONV REAL_RAT5_ADD_CONV) THEN
          CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_EQ_CONV) THEN
          REWRITE_TAC[] THEN NO_TAC;
          REWRITE_TAC[IMAGE_CLAUSES; MATRIX_VECTOR_MUL_3] THEN
          CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_MUL_CONV) THEN
          CONV_TAC(DEPTH_CONV REAL_RAT5_ADD_CONV) THEN
          REWRITE_TAC[INSERT_AC]]);;

let TETRAHEDRON_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_tetrahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_tetrahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC TETRAHEDRON_EDGES);;

let TETRAHEDRON_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_tetrahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_tetrahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC TETRAHEDRON_FACETS);;

let CUBE_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_cube /\ aff_dim e1 = &1 /\
           e2 face_of std_cube /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC CUBE_EDGES);;

let CUBE_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_cube /\ aff_dim f1 = &2 /\
           f2 face_of std_cube /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC CUBE_FACETS);;

let OCTAHEDRON_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_octahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_octahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC OCTAHEDRON_EDGES);;

let OCTAHEDRON_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_octahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_octahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC OCTAHEDRON_FACETS);;

let DODECAHEDRON_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_dodecahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_dodecahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC DODECAHEDRON_EDGES);;

let DODECAHEDRON_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_dodecahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_dodecahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC DODECAHEDRON_FACETS);;

let ICOSAHEDRON_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_icosahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_icosahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC ICOSAHEDRON_EDGES);;

let ICOSAHEDRON_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_icosahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_icosahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC ICOSAHEDRON_FACETS);;
