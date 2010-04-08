(* ========================================================================= *)
(* Pick's theorem.                                                           *)
(* ========================================================================= *)

needs "Multivariate/polytope.ml";;
needs "Multivariate/measure.ml";;
needs "Multivariate/transcendentals.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Misc lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let COLLINEAR_IMP_NEGLIGIBLE = prove
 (`!s:real^2->bool. collinear s ==> negligible s`,
  REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
  MESON_TAC[NEGLIGIBLE_AFFINE_HULL_2; NEGLIGIBLE_SUBSET]);;

let CONVEX_HULL_3_0 = prove
 (`!a b:real^N.
        convex hull {vec 0,a,b} =
        {x % a + y % b | &0 <= x /\ &0 <= y /\ x + y <= &1}`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[SET_RULE `{c,a,b} = {a,b,c}`] THEN
  REWRITE_TAC[CONVEX_HULL_3; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real` THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real` THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_ARITH_TAC; EXISTS_TAC `&1 - x - y` THEN ASM_ARITH_TAC]);;

let INTERIOR_CONVEX_HULL_3_0 = prove
 (`!a b:real^2.
        ~(collinear {vec 0,a,b})
        ==> interior(convex hull {vec 0,a,b}) =
              {x % a + y % b | &0 < x /\ &0 < y /\ x + y < &1}`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[SET_RULE `{c,a,b} = {a,b,c}`] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3] THEN
  REWRITE_TAC[TAUT `a /\ x = &1 /\ b <=> x = &1 /\ a /\ b`] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
  REWRITE_TAC[REAL_ARITH `x + y + z = &1 <=> &1 - x - y = z`; UNWIND_THM1] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  GEN_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let MEASURE_CONVEX_HULL_2_TRIVIAL = prove
 (`(!a:real^2. measure(convex hull {a}) = &0) /\
   (!a b:real^2. measure(convex hull {a,b}) = &0)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURE_EQ_0 THEN
  MATCH_MP_TAC COLLINEAR_IMP_NEGLIGIBLE THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; CONVEX_HULL_SING] THEN
  REWRITE_TAC[COLLINEAR_SING; COLLINEAR_SEGMENT]);;

let NEGLIGIBLE_SEGMENT_2 = prove
 (`!a b:real^2. negligible(segment[a,b])`,
  SIMP_TAC[COLLINEAR_IMP_NEGLIGIBLE; COLLINEAR_SEGMENT]);;

(* ------------------------------------------------------------------------- *)
(* Decomposing an additive function on a triangle.                           *)
(* ------------------------------------------------------------------------- *)

let TRIANGLE_DECOMPOSITION = prove
 (`!a b c d:real^2.
        d IN convex hull {a,b,c}
        ==> (convex hull {a,b,c} =
             convex hull {d,b,c} UNION
             convex hull {d,a,c} UNION
             convex hull {d,a,b})`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[UNION_SUBSET] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`{a:real^2,b,c}`; `d:real^2`; `x:real^2`]
     IN_CONVEX_HULL_EXCHANGE) THEN
    ASM_REWRITE_TAC[EXISTS_IN_INSERT; NOT_IN_EMPTY; IN_UNION] THEN
    REPEAT(MATCH_MP_TAC MONO_OR THEN CONJ_TAC) THEN
    SPEC_TAC(`x:real^2`,`x:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    SIMP_TAC[SUBSET_HULL; CONVEX_CONVEX_HULL] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_SIMP_TAC[HULL_INC; IN_INSERT]]);;

let TRIANGLE_ADDITIVE_DECOMPOSITION = prove
 (`!f:(real^2->bool)->real a b c d.
        (!s t. compact s /\ compact t
               ==> f(s UNION t) = f(s) + f(t) - f(s INTER t)) /\
        ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
        ~affine_dependent {a,b,c} /\ d IN convex hull {a,b,c}
        ==> f(convex hull {a,b,c}) =
            (f(convex hull {a,b,d}) +
             f(convex hull {a,c,d}) +
             f(convex hull {b,c,d})) -
            (f(convex hull {a,d}) +
             f(convex hull {b,d}) +
             f(convex hull {c,d})) +
            f(convex hull {d})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP TRIANGLE_DECOMPOSITION) THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [COMPACT_UNION; COMPACT_INTER; COMPACT_CONVEX_HULL;
               FINITE_IMP_COMPACT; FINITE_INSERT; FINITE_EMPTY;
               UNION_OVER_INTER] THEN
  MP_TAC(ISPECL [`{a:real^2,b,c}`; `d:real^2`]
        CONVEX_HULL_EXCHANGE_INTER) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT; NOT_IN_EMPTY;
           SET_RULE `s SUBSET u /\ t SUBSET u ==> (s INTER t) SUBSET u`] THEN
  ASM_REWRITE_TAC[INSERT_INTER; IN_INSERT; NOT_IN_EMPTY; INTER_EMPTY] THEN
  DISCH_TAC THEN REWRITE_TAC[INSERT_AC] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Vectors all of whose coordinates are integers.                            *)
(* ------------------------------------------------------------------------- *)

let integral_vector = define
 `integral_vector(x:real^N) <=>
        !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i)`;;

let INTEGRAL_VECTOR_VEC = prove
 (`!n. integral_vector(vec n)`,
  REWRITE_TAC[integral_vector; VEC_COMPONENT; INTEGER_CLOSED]);;

let INTEGRAL_VECTOR_STDBASIS = prove
 (`!i. integral_vector(basis i:real^N)`,
  REWRITE_TAC[integral_vector] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BASIS_COMPONENT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[INTEGER_CLOSED]);;

let INTEGRAL_VECTOR_ADD = prove
 (`!x y:real^N.
        integral_vector x /\ integral_vector y ==> integral_vector(x + y)`,
  SIMP_TAC[integral_vector; VECTOR_ADD_COMPONENT; INTEGER_CLOSED]);;

let INTEGRAL_VECTOR_SUB = prove
 (`!x y:real^N.
        integral_vector x /\ integral_vector y ==> integral_vector(x - y)`,
  SIMP_TAC[integral_vector; VECTOR_SUB_COMPONENT; INTEGER_CLOSED]);;

let INTEGRAL_VECTOR_ADD_LCANCEL = prove
 (`!x y:real^N.
        integral_vector x ==> (integral_vector(x + y) <=> integral_vector y)`,
  MESON_TAC[INTEGRAL_VECTOR_ADD; INTEGRAL_VECTOR_SUB;
            VECTOR_ARITH `(x + y) - x:real^N = y`]);;

let FINITE_BOUNDED_INTEGER_POINTS = prove
 (`!s:real^N->bool. bounded s ==> FINITE {x | x IN s /\ integral_vector x}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  REWRITE_TAC[SUBSET; IN_INTERVAL; integral_vector] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                       ==> integer(x$i) /\
                           (a:real^N)$i <= x$i /\ x$i <= (b:real^N)$i}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_CART THEN REWRITE_TAC[FINITE_INTSEG];
    ASM SET_TAC[]]);;

let FINITE_TRIANGLE_INTEGER_POINTS = prove
 (`!a b c:real^N. FINITE {x | x IN convex hull {a,b,c} /\ integral_vector x}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_BOUNDED_INTEGER_POINTS THEN
  SIMP_TAC[FINITE_IMP_BOUNDED_CONVEX_HULL; FINITE_INSERT; FINITE_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Properties of a basis for the integer lattice.                            *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INTEGRAL_VECTOR = prove
 (`!f:real^N->real^N.
        linear f
        ==> ((!x. integral_vector x ==> integral_vector(f x)) <=>
             (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N)
                    ==> integer(matrix f$i$j)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  ABBREV_TAC `M = matrix(f:real^N->real^N)` THEN
  SIMP_TAC[integral_vector; matrix_vector_mul; LAMBDA_BETA] THEN
  EQ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `basis j:real^N`) THEN
    REWRITE_TAC[GSYM integral_vector; INTEGRAL_VECTOR_STDBASIS] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[BASIS_COMPONENT; COND_RAND; COND_RATOR] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; SUM_DELTA; IN_NUMSEG; REAL_MUL_RID];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC INTEGER_SUM THEN
    ASM_SIMP_TAC[INTEGER_CLOSED; IN_NUMSEG]]);;

let INTEGRAL_BASIS_UNIMODULAR = prove
 (`!f:real^N->real^N.
        linear f /\ IMAGE f integral_vector = integral_vector
        ==> abs(det(matrix f)) = &1`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE] THEN REWRITE_TAC[IN] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\
          1 <= j /\ j <= dimindex(:N)
          ==> integer(matrix(f:real^N->real^N)$i$j)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[GSYM LINEAR_INTEGRAL_VECTOR]; ALL_TAC] THEN
  SUBGOAL_THEN
    `?g:real^N->real^N. linear g /\ (!x. g(f x) = x) /\ (!y. f(g y) = y)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(TAUT `(b ==> a) /\ b ==> a /\ b`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[LINEAR_SURJECTIVE_IMP_INJECTIVE]; ALL_TAC] THEN
    SUBGOAL_THEN `!y. y:real^N IN span(IMAGE f (:real^N))` MP_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC[SPAN_LINEAR_IMAGE; SPAN_UNIV] THEN SET_TAC[]] THEN
    GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
    MATCH_MP_TAC SPAN_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
    ASM_MESON_TAC[INTEGRAL_VECTOR_STDBASIS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\
          1 <= j /\ j <= dimindex(:N)
          ==> integer(matrix(g:real^N->real^N)$i$j)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM LINEAR_INTEGRAL_VECTOR] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `det(matrix(f:real^N->real^N)) * det(matrix(g:real^N->real^N)) =
    det(matrix(I:real^N->real^N))`
  MP_TAC THENL
   [ASM_SIMP_TAC[GSYM DET_MUL; GSYM MATRIX_COMPOSE] THEN
    REPEAT AP_TERM_TAC THEN ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `abs:real->real`) THEN
  REWRITE_TAC[MATRIX_I; DET_I; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[INTEGER_DET; INTEGER_ABS_MUL_EQ_1]);;

(* ------------------------------------------------------------------------- *)
(* Pick's theorem for an elementary triangle.                                *)
(* ------------------------------------------------------------------------- *)

let PICK_ELEMENTARY_TRIANGLE_0 = prove
 (`!a b:real^2.
        {x | x IN convex hull {vec 0,a,b} /\ integral_vector x} = {vec 0,a,b}
        ==> measure(convex hull {vec 0,a,b}) =
               if collinear {vec 0,a,b} then &0 else &1 / &2`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[MEASURE_EQ_0; COLLINEAR_IMP_NEGLIGIBLE;
               COLLINEAR_CONVEX_HULL_COLLINEAR] THEN
  POP_ASSUM MP_TAC THEN
  MAP_EVERY (fun t ->
    ASM_CASES_TAC t THENL [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC])
   [`a:real^2 = vec 0`; `b:real^2 = vec 0`; `a:real^2 = b`] THEN
  DISCH_TAC THEN SUBGOAL_THEN `independent {a:real^2,b}` ASSUME_TAC THENL
   [UNDISCH_TAC `~collinear{vec 0:real^2, a, b}` THEN
    REWRITE_TAC[independent; CONTRAPOS_THM] THEN
    REWRITE_TAC[dependent; EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `{c,a,b} = {c,b,a}`]; ALL_TAC] THEN
    ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL] THEN
    ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; IN_INSERT] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (SET_RULE `a IN s ==> s SUBSET t ==> a IN t`)) THEN
    MATCH_MP_TAC SPAN_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `span{a,b} = (:real^2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^2)`; `{a:real^2,b}`] CARD_EQ_DIM) THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; SUBSET; EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[HAS_SIZE; FINITE_INSERT; FINITE_EMPTY] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; DIM_UNIV; DIMINDEX_2; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_INSERT;
              FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY; IN_INSERT] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\x:real^2. transp(vector[a;b]:real^2^2) ** x`
        INTEGRAL_BASIS_UNIMODULAR) THEN
  REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; MATRIX_VECTOR_MUL_LINEAR] THEN
  REWRITE_TAC[DET_2; MEASURE_TRIANGLE; VECTOR_2; DET_TRANSP; VEC_COMPONENT] THEN
  ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN] THEN
    SIMP_TAC[LINEAR_INTEGRAL_VECTOR; MATRIX_VECTOR_MUL_LINEAR; LAMBDA_BETA;
             MATRIX_OF_MATRIX_VECTOR_MUL; transp; DIMINDEX_2; ARITH] THEN
    MAP_EVERY UNDISCH_TAC
     [`integral_vector(a:real^2)`; `integral_vector(b:real^2)`] THEN
    REWRITE_TAC[integral_vector; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[IMP_IMP; FORALL_2; DIMINDEX_2; VECTOR_2] THEN
    REWRITE_TAC[CONJ_ACI];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN REWRITE_TAC[IN] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[EXISTS_VECTOR_2] THEN
  REWRITE_TAC[MATRIX_VECTOR_COLUMN; TRANSP_TRANSP] THEN
  REWRITE_TAC[DIMINDEX_2; VSUM_2; VECTOR_2; integral_vector; FORALL_2] THEN
  SUBGOAL_THEN `(x:real^2) IN span{a,b}` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[SPAN_2; IN_UNIV; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real` THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `frac u % a + frac v % b:real^2`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `(&1 - frac u) % a + (&1 - frac v) % b:real^2`) THEN
  MATCH_MP_TAC(TAUT
   `b' /\ (b' ==> b) /\ (a \/ a') /\ (c \/ c' ==> x)
    ==> (a /\ b ==> c) ==> (a' /\ b' ==> c') ==> x`) THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `integral_vector(floor u % a + floor v % b:real^2)`
    MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`integral_vector(a:real^2)`; `integral_vector(b:real^2)`] THEN
      SIMP_TAC[integral_vector; DIMINDEX_2; FORALL_2;
               VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC[FLOOR; INTEGER_CLOSED];
      UNDISCH_TAC `integral_vector(x:real^2)` THEN REWRITE_TAC[IMP_IMP] THEN
      DISCH_THEN(MP_TAC o MATCH_MP INTEGRAL_VECTOR_SUB) THEN
      ASM_REWRITE_TAC[VECTOR_ARITH
       `(x % a + y % b) - (u % a + v % b) = (x - u) % a + (y - v) % b`] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN BINOP_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_ARITH `u - x:real = y <=> u = x + y`] THEN
      REWRITE_TAC[GSYM FLOOR_FRAC]];
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % a + (&1 - v) % b = (a + b) - (u % a + v % b)`] THEN
    ASM_SIMP_TAC[INTEGRAL_VECTOR_ADD; INTEGRAL_VECTOR_SUB];
    REWRITE_TAC[CONVEX_HULL_3_0; IN_ELIM_THM] THEN
    SUBGOAL_THEN
     `&0 <= frac u /\ &0 <= frac v /\ frac u + frac v <= &1 \/
      &0 <= &1 - frac u /\ &0 <= &1 - frac v /\
      (&1 - frac u) + (&1 - frac v) <= &1`
    MP_TAC THENL
     [MP_TAC(SPEC `u:real` FLOOR_FRAC) THEN
      MP_TAC(SPEC `v:real` FLOOR_FRAC) THEN REAL_ARITH_TAC;
      MESON_TAC[]];
    REWRITE_TAC
     [VECTOR_ARITH `x % a + y % b = a <=> (x - &1) % a + y % b = vec 0`;
      VECTOR_ARITH `x % a + y % b = b <=> x % a + (y - &1) % b = vec 0`] THEN
    ASM_SIMP_TAC[INDEPENDENT_2; GSYM REAL_FRAC_EQ_0] THEN
    MP_TAC(SPEC `u:real` FLOOR_FRAC) THEN
    MP_TAC(SPEC `v:real` FLOOR_FRAC) THEN REAL_ARITH_TAC]);;

let PICK_ELEMENTARY_TRIANGLE = prove
 (`!a b c:real^2.
        {x | x IN convex hull {a,b,c} /\ integral_vector x} = {a,b,c}
        ==> measure(convex hull {a,b,c}) =
               if collinear {a,b,c} then &0 else &1 / &2`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `s = t ==> (!x. x IN s <=> x IN t) /\ s = t`)) THEN
  REWRITE_TAC[IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPEC `a:real^2`) THEN
  REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN
  GEOM_ORIGIN_TAC `a:real^2`THEN
  SIMP_TAC[INTEGRAL_VECTOR_ADD_LCANCEL; VECTOR_ADD_RID] THEN
  REWRITE_TAC[PICK_ELEMENTARY_TRIANGLE_0]);;

(* ------------------------------------------------------------------------- *)
(* Our form of Pick's theorem holds degenerately for a flat triangle.        *)
(* ------------------------------------------------------------------------- *)

let PICK_TRIANGLE_FLAT = prove
 (`!a b c:real^2.
        integral_vector a /\ integral_vector b /\ integral_vector c /\
        c IN segment[a,b]
        ==> measure(convex hull {a,b,c}) =
             &(CARD {x | x IN convex hull {a,b,c} /\ integral_vector x}) -
             (&(CARD {x | x IN convex hull {b,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,b} /\ integral_vector x})) / &2 +
             &1 / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
  SUBGOAL_THEN `convex hull {a:real^2,b,c} = segment[a,b]` SUBST1_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC CONVEX_HULLS_EQ THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; INSERT_SUBSET; EMPTY_SUBSET] THEN
    SIMP_TAC[ENDS_IN_SEGMENT; HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `measure(segment[a:real^2,b]) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC MEASURE_EQ_0 THEN
    MATCH_MP_TAC COLLINEAR_IMP_NEGLIGIBLE THEN
    REWRITE_TAC[COLLINEAR_SEGMENT];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `&0 = c - (a + b + c) / &2 + &1 / &2 <=> a + b = c + &1`] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
  SUBGOAL_THEN
   `segment[a:real^2,b] = segment[b,c] UNION segment[a,c]`
  SUBST1_TAC THENL [ASM_MESON_TAC[SEGMENT_SYM; UNION_SEGMENT]; ALL_TAC] THEN
  REWRITE_TAC[SET_RULE
    `{x | x IN (s UNION t) /\ P x} =
     {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`] THEN
  SIMP_TAC[CARD_UNION_GEN; FINITE_BOUNDED_INTEGER_POINTS; BOUNDED_SEGMENT] THEN
  MATCH_MP_TAC(ARITH_RULE
   `z:num <= x /\ z = 1 ==> x + y = (x + y) - z + 1`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    SIMP_TAC[FINITE_BOUNDED_INTEGER_POINTS; BOUNDED_SEGMENT] THEN SET_TAC[];
    REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} INTER {x | x IN t /\ P x} =
                          {x | x IN (s INTER t) /\ P x}`] THEN
    SUBGOAL_THEN
     `segment[b:real^2,c] INTER segment[a,c] = {c}`
    SUBST1_TAC THENL [ASM_MESON_TAC[INTER_SEGMENT; SEGMENT_SYM]; ALL_TAC] THEN
    SUBGOAL_THEN `{x:real^2 | x IN {c} /\ integral_vector x} = {c}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_EMPTY; ARITH; NOT_IN_EMPTY]]);;

(* ------------------------------------------------------------------------- *)
(* Pick's theorem for a triangle.                                            *)
(* ------------------------------------------------------------------------- *)

let PICK_TRIANGLE_ALT = prove
 (`!a b c:real^2.
        integral_vector a /\ integral_vector b /\ integral_vector c
        ==> measure(convex hull {a,b,c}) =
             &(CARD {x | x IN convex hull {a,b,c} /\ integral_vector x}) -
             (&(CARD {x | x IN convex hull {b,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,b} /\ integral_vector x})) / &2 +
             &1 / &2`,
  let tac a bc =
    MATCH_MP_TAC CARD_PSUBSET THEN
    REWRITE_TAC[FINITE_TRIANGLE_INTEGER_POINTS] THEN
    REWRITE_TAC[PSUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `s SUBSET t ==> {x | x IN s /\ P x} SUBSET {x | x IN t /\ P x}`) THEN
      MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
      ASM_SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT; HULL_INC];
      DISCH_TAC] THEN
    SUBGOAL_THEN(subst[bc,`bc:real^2->bool`]
        `convex hull {a:real^2,b,c} = convex hull bc`)
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONVEX_HULLS_EQ THEN
      ASM_SIMP_TAC[HULL_INC; IN_INSERT; INSERT_SUBSET; EMPTY_SUBSET] THEN
      SUBGOAL_THEN(subst [a,`x:real^2`] `x IN convex hull {a:real^2,b,c}`)
      MP_TAC THENL
       [SIMP_TAC[HULL_INC; IN_INSERT]; ASM SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`{a:real^2,b,c}`; a]
      EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EXTREME_POINT_OF_CONVEX_HULL) THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] in
  REPEAT GEN_TAC THEN
  WF_INDUCT_TAC `CARD {x:real^2 | x IN convex hull {a,b,c} /\
                                  integral_vector x}` THEN
  ASM_CASES_TAC `collinear{a:real^2,b,c}` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COLLINEAR_BETWEEN_CASES]) THEN
    REWRITE_TAC[BETWEEN_IN_SEGMENT] THEN REPEAT STRIP_TAC THENL
     [MP_TAC(ISPECL [`b:real^2`; `c:real^2`; `a:real^2`] PICK_TRIANGLE_FLAT);
      MP_TAC(ISPECL [`a:real^2`; `c:real^2`; `b:real^2`] PICK_TRIANGLE_FLAT);
      MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `c:real^2`]
       PICK_TRIANGLE_FLAT)] THEN
    (ANTS_TAC THENL [ASM_MESON_TAC[SEGMENT_SYM]; ALL_TAC] THEN
     REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER P`] THEN
     REWRITE_TAC[INSERT_AC; REAL_ADD_AC]);
    ALL_TAC] THEN
  UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN
  MAP_EVERY
   (fun t -> ASM_CASES_TAC t THENL
     [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC])
   [`a:real^2 = b`; `a:real^2 = c`; `b:real^2 = c`] THEN
  DISCH_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `{x:real^2 | x IN convex hull {a, b, c} /\ integral_vector x} =
    {a,b,c}`
  THENL
   [ASM_SIMP_TAC[PICK_ELEMENTARY_TRIANGLE] THEN
    SUBGOAL_THEN
     `{x | x IN convex hull {b,c} /\ integral_vector x} = {b,c} /\
      {x | x IN convex hull {a,c} /\ integral_vector x} = {a,c} /\
      {x | x IN convex hull {a,b} /\ integral_vector x} = {a:real^2,b}`
    (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
     [REPEAT CONJ_TAC THEN
      (FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `{x | x IN cs /\ P x} = s
         ==> t SUBSET s /\ t SUBSET ct /\ ct SUBSET cs /\
                (s DIFF t) INTER ct = {}
             ==> {x | x IN ct /\ P x} = t`)) THEN
       REPEAT CONJ_TAC THENL
        [SET_TAC[];
         MATCH_ACCEPT_TAC HULL_SUBSET;
         MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
         ASM_REWRITE_TAC[INSERT_DIFF; IN_INSERT; NOT_IN_EMPTY; EMPTY_DIFF] THEN
         MATCH_MP_TAC(SET_RULE `~(x IN s) ==> {x} INTER s = {}`) THEN
         REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; GSYM BETWEEN_IN_SEGMENT] THEN
         DISCH_THEN(MP_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR) THEN
         UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN REWRITE_TAC[INSERT_AC]]);
       SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
       ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
       CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV];
     ALL_TAC] THEN
  SUBGOAL_THEN
   `?d:real^2. d IN convex hull {a, b, c} /\ integral_vector d /\
               ~(d = a) /\ ~(d = b) /\ ~(d = c)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `~(s = t) ==> t SUBSET s ==> ?d. d IN s /\ ~(d IN t)`)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_INSERT; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM; GSYM CONJ_ASSOC] THEN
    DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
   [COLLINEAR_3_EQ_AFFINE_DEPENDENT]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`measure:(real^2->bool)->real`;
    `a:real^2`; `b:real^2`; `c:real^2`; `d:real^2`]
   TRIANGLE_ADDITIVE_DECOMPOSITION) THEN
  SIMP_TAC[MEASURE_UNION; MEASURABLE_COMPACT] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MEASURE_CONVEX_HULL_2_TRIVIAL; REAL_ADD_RID; REAL_SUB_RZERO] THEN
  MP_TAC(ISPECL
   [`\s. &(CARD {x:real^2 | x IN s /\ integral_vector x})`;
    `a:real^2`; `b:real^2`; `c:real^2`; `d:real^2`]
   TRIANGLE_ADDITIVE_DECOMPOSITION) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[SET_RULE `{x | x IN (s UNION t) /\ P x} =
                          {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`;
                SET_RULE `{x | x IN (s INTER t) /\ P x} =
                          {x | x IN s /\ P x} INTER {x | x IN t /\ P x}`] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `x:real = y + z - w <=> x + w = y + z`] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC(ARITH_RULE
     `x:num = (y + z) - w /\ w <= z ==> x + w = y + z`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_UNION_GEN;
      MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[INTER_SUBSET]] THEN
    ASM_SIMP_TAC[FINITE_BOUNDED_INTEGER_POINTS; COMPACT_IMP_BOUNDED];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(fun th ->
   MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `d:real^2`] th) THEN
   MP_TAC(ISPECL [`a:real^2`; `c:real^2`; `d:real^2`] th) THEN
   MP_TAC(ISPECL [`b:real^2`; `c:real^2`; `d:real^2`] th)) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [tac `a:real^2` `{b:real^2,c,d}`; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [tac `b:real^2` `{a:real^2,c,d}`; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [tac `c:real^2` `{a:real^2,b,d}`; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `{x:real^2 | x IN convex hull {d} /\ integral_vector x} = {d}`
  SUBST1_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_SING] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER P`] THEN
  REWRITE_TAC[INSERT_AC] THEN REAL_ARITH_TAC);;

let PICK_TRIANGLE = prove
 (`!a b c:real^2.
        integral_vector a /\ integral_vector b /\ integral_vector c
        ==> measure(convex hull {a,b,c}) =
                if collinear {a,b,c} then &0
                else &(CARD {x | x IN interior(convex hull {a,b,c}) /\
                                 integral_vector x}) +
                     &(CARD {x | x IN frontier(convex hull {a,b,c}) /\
                                 integral_vector x}) / &2 - &1`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[MEASURE_EQ_0; COLLINEAR_IMP_NEGLIGIBLE;
               COLLINEAR_CONVEX_HULL_COLLINEAR] THEN
  ASM_SIMP_TAC[PICK_TRIANGLE_ALT] THEN
  REWRITE_TAC[INTERIOR_OF_TRIANGLE; FRONTIER_OF_TRIANGLE] THEN
  REWRITE_TAC[SET_RULE
   `{x | x IN (s DIFF t) /\ P x} =
    {x | x IN s /\ P x} DIFF {x | x IN t /\ P x}`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `i + c = s /\ ccc = c + &3
    ==> s - ccc / &2 + &1 / &2 = i + c / &2 - &1`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC(ARITH_RULE `y:num <= x /\ x - y = z ==> z + y = x`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET; MATCH_MP_TAC(GSYM CARD_DIFF)] THEN
    ASM_SIMP_TAC[FINITE_BOUNDED_INTEGER_POINTS;
      FINITE_IMP_BOUNDED_CONVEX_HULL; FINITE_INSERT; FINITE_EMPTY] THEN
    MATCH_MP_TAC(SET_RULE
     `s SUBSET t ==> {x | x IN s /\ P x} SUBSET {x | x IN t /\ P x}`) THEN
    REWRITE_TAC[UNION_SUBSET; SEGMENT_CONVEX_HULL] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    REWRITE_TAC[SET_RULE
     `{x | x IN (s UNION t) /\ P x} =
      {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`] THEN
    SIMP_TAC[CARD_UNION_GEN; FINITE_BOUNDED_INTEGER_POINTS;
      FINITE_INTER; FINITE_UNION; BOUNDED_SEGMENT; UNION_OVER_INTER] THEN
    REWRITE_TAC[SET_RULE
     `{x | x IN s /\ P x} INTER {x | x IN t /\ P x} =
      {x | x IN (s INTER t) /\ P x}`] THEN
    SUBGOAL_THEN
     `segment[b:real^2,c] INTER segment [c,a] = {c} /\
      segment[a,b] INTER segment [b,c] = {b} /\
      segment[a,b] INTER segment [c,a] = {a}`
    (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_MESON_TAC[INTER_SEGMENT; SEGMENT_SYM; INSERT_AC]; ALL_TAC] THEN
    ASM_SIMP_TAC[SET_RULE `P a ==> {x | x IN {a} /\ P x} = {a}`] THEN
    ASM_CASES_TAC `b:real^2 = a` THENL
     [ASM_MESON_TAC[COLLINEAR_2; INSERT_AC]; ALL_TAC] THEN
    ASM_SIMP_TAC[SET_RULE `~(a = b) ==> {b} INTER {a} = {}`] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; CARD_CLAUSES; SUB_0] THEN
    MATCH_MP_TAC(ARITH_RULE
     `c:num <= ca /\ a <= ab /\ b <= bc /\
      bc' + ac' + ab' + a + b + c = ab + bc + ca + 3
      ==> bc' + ac' + ab' = (ab + (bc + ca) - c) - (b + a) + 3`) THEN
    ASM_SIMP_TAC[CARD_SUBSET; SING_SUBSET; IN_ELIM_THM; ENDS_IN_SEGMENT;
                 FINITE_BOUNDED_INTEGER_POINTS; BOUNDED_SEGMENT] THEN
    SIMP_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; CARD_CLAUSES; FINITE_INSERT;
             FINITE_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER P`] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL; INSERT_AC] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Parity lemma for segment crossing a polygon.                              *)
(* ------------------------------------------------------------------------- *)

let PARITY_LEMMA = prove
 (`!a b c d p x:real^2.
        simple_path(p ++ linepath(a,b)) /\
        pathstart p = b /\ pathfinish p = a /\
        segment(a,b) INTER segment(c,d) = {x} /\
        segment[c,d] INTER path_image p = {}
        ==> (c IN inside(path_image(p ++ linepath(a,b))) <=>
             d IN outside(path_image(p ++ linepath(a,b))))`,
  let lemma = prove
   (`!a b x y:real^N.
          collinear{y,a,b} /\ between x (a,b) /\
          dist(y,x) < dist(x,b) /\ dist(y,x) < dist(x,a)
          ==> y IN segment(a,b)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC COLLINEAR_DIST_IN_OPEN_SEGMENT THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[between; DIST_SYM] THEN
    NORM_ARITH_TAC)
  and symlemma = prove
   (`(!n. P(--n) <=> P (n)) /\ (!n. &0 < n dot x ==> P n)
     ==> !n:real^N. ~(n dot x = &0) ==> P n`,
    STRIP_TAC THEN GEN_TAC THEN
    REWRITE_TAC[REAL_ARITH `~(x = &0) <=> &0 < x \/ &0 < --x`] THEN
    REWRITE_TAC[GSYM DOT_LNEG] THEN ASM_MESON_TAC[]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^1->real^2`; `linepath(a:real^2,b)`]
        SIMPLE_PATH_JOIN_LOOP_EQ) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SIMPLE_PATH_IMP_PATH) THEN
  ASM_SIMP_TAC[PATH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(a:real^2) INSERT b INSERT c INSERT d INSERT path_image p`;
                 `x:real^2`]
        DISTANCE_ATTAINS_INF) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  ONCE_REWRITE_TAC[SET_RULE `a INSERT b INSERT c INSERT d INSERT s =
                             {a,b,c,d} UNION s`] THEN
  ASM_SIMP_TAC[CLOSED_UNION; FINITE_IMP_CLOSED; CLOSED_PATH_IMAGE;
               FINITE_INSERT; FINITE_EMPTY] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cp:real^2` MP_TAC) THEN
  DISJ_CASES_TAC(NORM_ARITH `cp = x \/ &0 < dist(x:real^2,cp)`) THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC(TAUT `~a ==> a /\ b ==> c`) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE `a = {x} ==> x IN a`)) THEN
    REWRITE_TAC[open_segment; IN_DIFF; IN_UNION; IN_INSERT; NOT_IN_EMPTY;
                IN_INTER; DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `p INTER s SUBSET u ==> x IN (s DIFF u) ==> ~(x IN p)`)) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; PATH_IMAGE_LINEPATH];
    ALL_TAC] THEN
  ABBREV_TAC `e = dist(x:real^2,cp)` THEN FIRST_X_ASSUM(K ALL_TAC o SYM) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARC_LINEPATH_EQ]) THEN
  MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `c:real^2`; `d:real^2`]
        FINITE_INTER_COLLINEAR_OPEN_SEGMENTS) THEN
  MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `d:real^2`; `c:real^2`]
        FINITE_INTER_COLLINEAR_OPEN_SEGMENTS) THEN
  SUBST1_TAC(MESON[SEGMENT_SYM] `segment(d:real^2,c) = segment(c,d)`) THEN
  ASM_REWRITE_TAC[FINITE_SING; NOT_INSERT_EMPTY] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~(a IN segment[c:real^2,d]) /\ ~(b IN segment[c,d])`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE;
                  IN_INTER; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c:real^2 = a) /\ ~(c = b) /\ ~(d = a) /\ ~(d = b)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `x IN segment(a:real^2,b) /\ x IN segment(c,d)` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_OPEN_SEGMENT_ALT] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{c,d} INTER path_image(p ++ linepath(a:real^2,b)) = {}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_LINEPATH; PATHSTART_LINEPATH] THEN
    REWRITE_TAC[SET_RULE
     `{c,d} INTER (s UNION t) = {} <=>
      (~(c IN s) /\ ~(d IN s)) /\ ~(c IN t) /\ ~(d IN t)`] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[ENDS_IN_SEGMENT; IN_INTER; NOT_IN_EMPTY];
      REWRITE_TAC[PATH_IMAGE_LINEPATH; GSYM BETWEEN_IN_SEGMENT] THEN
      CONJ_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INSERT_AC]) THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `b - x:real^2` ORTHOGONAL_TO_VECTOR_EXISTS) THEN
  REWRITE_TAC[DIMINDEX_2; LE_REFL; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `n:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN segment(a,b) /\ x IN segment(c,d)` MP_TAC THENL
   [ASM SET_TAC[];
    SIMP_TAC[IN_OPEN_SEGMENT_ALT; GSYM BETWEEN_IN_SEGMENT] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `~collinear{a:real^2, b, c, d}` ASSUME_TAC THENL
   [UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COLLINEAR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n dot (d - x:real^2) = &0)` MP_TAC THENL
   [REWRITE_TAC[GSYM orthogonal] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:real^2`; `d - x:real^2`; `b - x:real^2`]
      ORTHOGONAL_TO_ORTHOGONAL_2D) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ORTHOGONAL_SYM]; ALL_TAC] THEN
    REWRITE_TAC[GSYM COLLINEAR_3] THEN DISCH_TAC THEN
    UNDISCH_TAC `~collinear{a:real^2, b, c, d}` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SET_RULE `{a,b,c,d} = {b,d,a,c}`] THEN
    ASM_SIMP_TAC[COLLINEAR_4_3] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COLLINEAR_SUBSET THEN EXISTS_TAC `{b:real^2,x,a,d}` THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[COLLINEAR_4_3]; SET_TAC[]] THEN
      ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {c,b,a}`] THEN
      ASM_SIMP_TAC[BETWEEN_IMP_COLLINEAR];
      MATCH_MP_TAC COLLINEAR_SUBSET THEN EXISTS_TAC `{d:real^2,x,b,c}` THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[COLLINEAR_4_3]; SET_TAC[]] THEN
      ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {c,b,a}`] THEN
      ASM_SIMP_TAC[BETWEEN_IMP_COLLINEAR]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
                       MP_TAC th) THEN
  SPEC_TAC(`n:real^2`,`n:real^2`) THEN
  MATCH_MP_TAC symlemma THEN CONJ_TAC THENL
   [REWRITE_TAC[ORTHOGONAL_RNEG; VECTOR_NEG_EQ_0]; ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n dot (c - x:real^2) < &0` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < n dot (d - x:real^2)` THEN
    SUBGOAL_THEN `(x:real^2) IN segment(c,d)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH
      `d - ((&1 - u) % c + u % d):real^N = (&1 - u) % (d - c) /\
       c - ((&1 - u) % c + u % d) = --u % (d - c)`] THEN
    REWRITE_TAC[DOT_RMUL; REAL_MUL_LNEG; REAL_ARITH `--x < &0 <=> &0 < x`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL_EQ; REAL_SUB_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ball(x:real^2,e)
        ==> y IN segment(a,b) \/
            &0 < n dot (y - x) \/
            n dot (y - x) < &0`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~c /\ ~b ==> a) ==> a \/ b \/ c`) THEN
    REWRITE_TAC[REAL_ARITH `~(x < &0) /\ ~(&0 < x) <=> x = &0`] THEN
    REWRITE_TAC[GSYM orthogonal] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:real^2`; `y - x:real^2`; `b - x:real^2`]
      ORTHOGONAL_TO_ORTHOGONAL_2D) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ORTHOGONAL_SYM]; ALL_TAC] THEN
    REWRITE_TAC[GSYM COLLINEAR_3] THEN DISCH_TAC THEN
    MATCH_MP_TAC lemma THEN EXISTS_TAC `x:real^2` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[REAL_LTE_TRANS; DIST_SYM]] THEN
    ONCE_REWRITE_TAC[SET_RULE `{y,a,b} = {a,b,y}`] THEN
    MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `x:real^2` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `collinear{y:real^2, x, b}` THEN
    MP_TAC(MATCH_MP BETWEEN_IMP_COLLINEAR (ASSUME
     `between (x:real^2) (a,b)`)) THEN
    SIMP_TAC[INSERT_AC];
    ALL_TAC] THEN
  MP_TAC(SPEC `p ++ linepath(a:real^2,b)` JORDAN_INSIDE_OUTSIDE) THEN
  ASM_REWRITE_TAC[PATHFINISH_JOIN; PATHSTART_JOIN; PATHFINISH_LINEPATH] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `~(connected_component((:real^2) DIFF path_image(p ++ linepath (a,b))) c d)`
  MP_TAC THENL
   [DISCH_TAC;
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `path_image(p ++ linepath(a:real^2,b))` o
      MATCH_MP (SET_RULE
     `~(x IN s <=> y IN t)
      ==> !p. s UNION t = (:real^2) DIFF p /\ {x,y} INTER p = {}
              ==> x IN s /\ y IN s \/ x IN t /\ y IN t`)) THEN
    ASM_REWRITE_TAC[connected_component] THEN
    ASM_REWRITE_TAC[SET_RULE `t SUBSET UNIV DIFF s <=> t INTER s = {}`] THEN
    ASM_MESON_TAC[INSIDE_NO_OVERLAP; OUTSIDE_NO_OVERLAP]] THEN
  MP_TAC(SPEC `p ++ linepath(a:real^2,b)` JORDAN_DISCONNECTED) THEN
  ASM_REWRITE_TAC[PATHFINISH_JOIN; PATHSTART_JOIN; PATHFINISH_LINEPATH] THEN
  REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT] THEN
  SUBGOAL_THEN
   `!u v. u IN inside(path_image(p ++ linepath(a,b))) /\
          v IN outside(path_image(p ++ linepath(a,b)))
          ==> connected_component
              ((:real^2) DIFF path_image (p ++ linepath (a,b))) u v`
  ASSUME_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [SYM(ASSUME `inside (path_image (p ++ linepath (a,b))) UNION
                  outside (path_image (p ++ linepath (a,b))) =
                  (:real^2) DIFF path_image (p ++ linepath (a,b))`)] THEN
    REWRITE_TAC[IN_UNION; CONNECTED_IFF_CONNECTED_COMPONENT] THEN
    STRIP_TAC THENL
     [REWRITE_TAC[connected_component] THEN
      EXISTS_TAC `inside(path_image(p ++ linepath(a:real^2,b)))`;
      ASM_MESON_TAC[];
      ASM_MESON_TAC[CONNECTED_COMPONENT_SYM];
      REWRITE_TAC[connected_component] THEN
      EXISTS_TAC `outside(path_image(p ++ linepath(a:real^2,b)))`] THEN
    ASM_REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> s INTER t = {}`] THEN
    REWRITE_TAC[OUTSIDE_NO_OVERLAP; INSIDE_NO_OVERLAP]] THEN
  SUBGOAL_THEN `(x:real^2) IN path_image(p ++ linepath(a,b))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATHSTART_LINEPATH; PATH_IMAGE_JOIN; PATH_LINEPATH] THEN
    REWRITE_TAC[IN_UNION; PATH_IMAGE_LINEPATH] THEN DISJ2_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[open_segment]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `frontier(inside(path_image(p ++ linepath(a:real^2,b)))) =
    path_image(p ++ linepath(a,b))` THEN
  REWRITE_TAC[EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[frontier] THEN
  REWRITE_TAC[IN_DIFF; CLOSURE_APPROACHABLE] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `w:real^2` THEN STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC `w:real^2` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `inside(path_image(p ++ linepath(a:real^2,b)))` THEN
    ASM_REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> s INTER t = {}`] THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP];
    ALL_TAC] THEN
  UNDISCH_TAC
   `frontier(outside(path_image(p ++ linepath(a:real^2,b)))) =
    path_image(p ++ linepath(a,b))` THEN
  REWRITE_TAC[EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[frontier] THEN
  REWRITE_TAC[IN_DIFF; CLOSURE_APPROACHABLE] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC `z:real^2` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `outside(path_image(p ++ linepath(a:real^2,b)))` THEN
    ASM_REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> s INTER t = {}`] THEN
    REWRITE_TAC[OUTSIDE_NO_OVERLAP]] THEN
  SUBGOAL_THEN
   `!y. dist(y,x) < e /\ ~(y IN path_image(p ++ linepath (a,b)))
        ==> connected_component
             ((:real^2) DIFF path_image(p ++ linepath(a,b))) c y`
  ASSUME_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC `c:real^2` THEN
    CONJ_TAC THENL [MATCH_MP_TAC CONNECTED_COMPONENT_SYM; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[INSIDE_NO_OVERLAP; OUTSIDE_NO_OVERLAP; IN_INTER;
                  NOT_IN_EMPTY]] THEN
  X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[c,d] INTER path_image(p ++ linepath(a,b)) = {x:real^2}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `{c,d} INTER p = {} /\ (segment[c,d] DIFF {c,d}) INTER p = {x}
      ==> segment[c,d] INTER p = {x}`) THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATH_LINEPATH] THEN
    MATCH_MP_TAC(SET_RULE
     `cd INTER p = {} /\ l INTER (cd DIFF {c,d}) = {x}
      ==> (cd DIFF {c,d}) INTER (p UNION l) = {x}`) THEN
    ASM_REWRITE_TAC[GSYM open_segment; PATH_IMAGE_LINEPATH] THEN
    MATCH_MP_TAC(SET_RULE
     `~(a IN segment[c,d]) /\ ~(b IN segment[c,d]) /\
      segment(a,b) INTER segment(c,d) = {x} /\
      segment(a,b) = segment[a,b] DIFF {a,b} /\
      segment(c,d) = segment[c,d] DIFF {c,d}
      ==> segment[a,b] INTER segment(c,d) = {x}`) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[open_segment];
    ALL_TAC] THEN
  UNDISCH_THEN
    `!y. y IN ball(x:real^2,e)
          ==> y IN segment(a,b) \/ &0 < n dot (y - x) \/ n dot (y - x) < &0`
    (MP_TAC o SPEC `y:real^2`) THEN
  REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN MP_TAC) THENL
   [MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    UNDISCH_TAC `~(y IN path_image(p ++ linepath(a:real^2,b)))` THEN
    ASM_SIMP_TAC[PATHSTART_LINEPATH; PATH_IMAGE_JOIN; PATH_LINEPATH] THEN
    SIMP_TAC[CONTRAPOS_THM; open_segment; IN_DIFF; IN_UNION;
             PATH_IMAGE_LINEPATH];
    DISCH_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN
    EXISTS_TAC `d:real^2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN
    EXISTS_TAC `x + min (&1 / &2) (e / &2 / norm(d - x)) % (d - x):real^2` THEN
    REWRITE_TAC[connected_component] THEN CONJ_TAC THENL
     [EXISTS_TAC `segment[x:real^2,d] DELETE x` THEN
      SIMP_TAC[CONVEX_SEMIOPEN_SEGMENT; CONVEX_CONNECTED] THEN
      ASM_REWRITE_TAC[IN_DELETE; ENDS_IN_SEGMENT] THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `cd INTER p = {x}
          ==> xd SUBSET cd
              ==> (xd DELETE x) SUBSET (UNIV DIFF p)`)) THEN
        REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT] THEN
        UNDISCH_TAC `segment (a,b) INTER segment (c,d) = {x:real^2}` THEN
        REWRITE_TAC[open_segment] THEN SET_TAC[];
        REWRITE_TAC[IN_SEGMENT; VECTOR_ARITH
         `x + a % (y - x):real^N = (&1 - a) % x + a % y`] THEN
        EXISTS_TAC `min (&1 / &2) (e / &2 / norm(d - x:real^2))` THEN
        REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
        REWRITE_TAC[REAL_LE_MIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; NORM_POS_LE; REAL_LT_IMP_LE];
        ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ;
                        VECTOR_ARITH `x + a:real^N = x <=> a = vec 0`] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(min (&1 / &2) x = &0)`) THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_HALF] THEN
        ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]];
      EXISTS_TAC `ball(x,e) INTER {w:real^2 | &0 < n dot (w - x)}` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
        REWRITE_TAC[CONVEX_BALL; DOT_RSUB; REAL_SUB_LT] THEN
        REWRITE_TAC[GSYM real_gt; CONVEX_HALFSPACE_GT];
        ASM_SIMP_TAC[PATHSTART_LINEPATH; PATH_IMAGE_JOIN; PATH_LINEPATH] THEN
        MATCH_MP_TAC(SET_RULE
         `p SUBSET (UNIV DIFF b) /\ l INTER w = {}
          ==> (b INTER w) SUBSET (UNIV DIFF (p UNION l))`) THEN
        ASM_REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_BALL; REAL_NOT_LT] THEN
        MATCH_MP_TAC(SET_RULE
         `!t. t INTER u = {} /\ s SUBSET t ==> s INTER u = {}`) THEN
        EXISTS_TAC `affine hull {x:real^2,b}` THEN CONJ_TAC THENL
         [REWRITE_TAC[AFFINE_HULL_2; FORALL_IN_GSPEC; SET_RULE
           `s INTER t = {} <=> !x. x IN s ==> ~(x IN t)`] THEN
          REWRITE_TAC[IN_ELIM_THM] THEN
          SIMP_TAC[REAL_ARITH `u + v = &1 <=> u = &1 - v`] THEN
          REWRITE_TAC[DOT_RMUL; VECTOR_ARITH
           `((&1 - v) % x + v % b) - x:real^N = v % (b - x)`] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[orthogonal]) THEN
          ONCE_REWRITE_TAC[DOT_SYM] THEN
          ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL];
          REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_CONVEX_HULL] THEN
          SIMP_TAC[SUBSET_HULL; AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL] THEN
          REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
          SIMP_TAC[HULL_INC; IN_INSERT] THEN
          ASM_SIMP_TAC[GSYM COLLINEAR_3_AFFINE_HULL] THEN
          ONCE_REWRITE_TAC[SET_RULE `{x,b,a} = {a,x,b}`] THEN
          MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[IN_BALL; IN_INTER; IN_ELIM_THM; dist] THEN
        REWRITE_TAC[NORM_ARITH `norm(x - (x + a):real^N) = norm a`] THEN
        REWRITE_TAC[VECTOR_ARITH `(x + a) - x:real^N = a`] THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LT_RDIV_EQ; NORM_POS_LT;
                       VECTOR_SUB_EQ] THEN
          MATCH_MP_TAC(REAL_ARITH
           `&0 < x /\ x < e ==> abs(min (&1 / &2) x) < e`) THEN
          ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ;
                       REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[DOT_RMUL] THEN MATCH_MP_TAC REAL_LT_MUL THEN
          ASM_REWRITE_TAC[REAL_LT_MIN] THEN
          ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ;
                       REAL_LT_01]];
        REWRITE_TAC[IN_BALL; IN_INTER; IN_ELIM_THM] THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]]];
    DISCH_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN
    EXISTS_TAC `x + min (&1 / &2) (e / &2 / norm(c - x)) % (c - x):real^2` THEN
    REWRITE_TAC[connected_component] THEN CONJ_TAC THENL
     [EXISTS_TAC `segment[x:real^2,c] DELETE x` THEN
      SIMP_TAC[CONVEX_SEMIOPEN_SEGMENT; CONVEX_CONNECTED] THEN
      ASM_REWRITE_TAC[IN_DELETE; ENDS_IN_SEGMENT] THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `cd INTER p = {x}
          ==> xd SUBSET cd
              ==> (xd DELETE x) SUBSET (UNIV DIFF p)`)) THEN
        REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT] THEN
        UNDISCH_TAC `segment (a,b) INTER segment (c,d) = {x:real^2}` THEN
        REWRITE_TAC[open_segment] THEN SET_TAC[];
        REWRITE_TAC[IN_SEGMENT; VECTOR_ARITH
         `x + a % (y - x):real^N = (&1 - a) % x + a % y`] THEN
        EXISTS_TAC `min (&1 / &2) (e / &2 / norm(c - x:real^2))` THEN
        REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
        REWRITE_TAC[REAL_LE_MIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; NORM_POS_LE; REAL_LT_IMP_LE];
        ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ;
                        VECTOR_ARITH `x + a:real^N = x <=> a = vec 0`] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(min (&1 / &2) x = &0)`) THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_HALF] THEN
        ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]];
      EXISTS_TAC `ball(x,e) INTER {w:real^2 | n dot (w - x) < &0}` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
        REWRITE_TAC[CONVEX_BALL; DOT_RSUB; REAL_ARITH `a - b < &0 <=> a < b`;
                    CONVEX_HALFSPACE_LT];
        ASM_SIMP_TAC[PATHSTART_LINEPATH; PATH_IMAGE_JOIN; PATH_LINEPATH] THEN
        MATCH_MP_TAC(SET_RULE
         `p SUBSET (UNIV DIFF b) /\ l INTER w = {}
          ==> (b INTER w) SUBSET (UNIV DIFF (p UNION l))`) THEN
        ASM_REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_BALL; REAL_NOT_LT] THEN
        MATCH_MP_TAC(SET_RULE
         `!t. t INTER u = {} /\ s SUBSET t ==> s INTER u = {}`) THEN
        EXISTS_TAC `affine hull {x:real^2,b}` THEN CONJ_TAC THENL
         [REWRITE_TAC[AFFINE_HULL_2; FORALL_IN_GSPEC; SET_RULE
           `s INTER t = {} <=> !x. x IN s ==> ~(x IN t)`] THEN
          REWRITE_TAC[IN_ELIM_THM] THEN
          SIMP_TAC[REAL_ARITH `u + v = &1 <=> u = &1 - v`] THEN
          REWRITE_TAC[DOT_RMUL; VECTOR_ARITH
           `((&1 - v) % x + v % b) - x:real^N = v % (b - x)`] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[orthogonal]) THEN
          ONCE_REWRITE_TAC[DOT_SYM] THEN
          ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL];
          REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_CONVEX_HULL] THEN
          SIMP_TAC[SUBSET_HULL; AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL] THEN
          REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
          SIMP_TAC[HULL_INC; IN_INSERT] THEN
          ASM_SIMP_TAC[GSYM COLLINEAR_3_AFFINE_HULL] THEN
          ONCE_REWRITE_TAC[SET_RULE `{x,b,a} = {a,x,b}`] THEN
          MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[IN_BALL; IN_INTER; IN_ELIM_THM; dist] THEN
        REWRITE_TAC[NORM_ARITH `norm(x - (x + a):real^N) = norm a`] THEN
        REWRITE_TAC[VECTOR_ARITH `(x + a) - x:real^N = a`] THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LT_RDIV_EQ; NORM_POS_LT;
                       VECTOR_SUB_EQ] THEN
          MATCH_MP_TAC(REAL_ARITH
           `&0 < x /\ x < e ==> abs(min (&1 / &2) x) < e`) THEN
          ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ;
                       REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[DOT_RMUL; REAL_ARITH `x * y < &0 <=> &0 < x * --y`] THEN
          MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
          ASM_REWRITE_TAC[REAL_ARITH `&0 < --x <=> x < &0`] THEN
          ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ;
                       REAL_LT_01]];
        REWRITE_TAC[IN_BALL; IN_INTER; IN_ELIM_THM] THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* Polygonal path; 0 in the empty case is just for linear invariance.        *)
(* Note that we *are* forced to assume non-emptiness for translation.        *)
(* ------------------------------------------------------------------------- *)

let polygonal_path = define
 `polygonal_path[] = linepath(vec 0,vec 0) /\
  polygonal_path[a] = linepath(a,a) /\
  polygonal_path [a;b] = linepath(a,b) /\
  polygonal_path (CONS a (CONS b (CONS c l))) =
       linepath(a,b) ++ polygonal_path(CONS b (CONS c l))`;;

let POLYGONAL_PATH_CONS_CONS = prove
 (`!a b p. ~(p = [])
           ==> polygonal_path(CONS a (CONS b p)) =
               linepath(a,b) ++ polygonal_path(CONS b p)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[polygonal_path]);;

let POLYGONAL_PATH_TRANSLATION = prove
 (`!a b p. polygonal_path (MAP (\x. a + x) (CONS b p)) =
         (\x. a + x) o (polygonal_path (CONS b p))`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[MAP; polygonal_path; LINEPATH_TRANSLATION] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC list_INDUCT THEN
  ASM_SIMP_TAC[MAP; polygonal_path; LINEPATH_TRANSLATION] THEN
  REWRITE_TAC[JOINPATHS_TRANSLATION]);;

add_translation_invariants [POLYGONAL_PATH_TRANSLATION];;

let POLYGONAL_PATH_LINEAR_IMAGE = prove
 (`!f p. linear f ==> polygonal_path (MAP f p) = f o polygonal_path p`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; MAP] THEN CONJ_TAC THENL
   [REWRITE_TAC[LINEPATH_REFL; o_DEF; FUN_EQ_THM] THEN ASM_MESON_TAC[LINEAR_0];
    ONCE_REWRITE_TAC[SWAP_FORALL_THM]] THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[polygonal_path; MAP] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[LINEPATH_LINEAR_IMAGE];
    ONCE_REWRITE_TAC[SWAP_FORALL_THM]] THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[polygonal_path; MAP] THEN
  ASM_SIMP_TAC[GSYM JOINPATHS_LINEAR_IMAGE; GSYM LINEPATH_LINEAR_IMAGE]);;

add_linear_invariants [POLYGONAL_PATH_LINEAR_IMAGE];;

let PATHSTART_POLYGONAL_PATH = prove
 (`!p. pathstart(polygonal_path p) = if p = [] then vec 0 else HD p`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; NOT_CONS_NIL; HD] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; HD; PATHSTART_JOIN]);;

let PATHFINISH_POLYGONAL_PATH = prove
 (`!p. pathfinish(polygonal_path p) = if p = [] then vec 0 else LAST p`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHFINISH_LINEPATH] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHFINISH_LINEPATH; NOT_CONS_NIL; LAST] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHFINISH_LINEPATH; PATHFINISH_JOIN]);;

let VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH = prove
 (`!p:(real^N)list. set_of_list p SUBSET path_image (polygonal_path p)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[set_of_list; EMPTY_SUBSET] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[set_of_list; polygonal_path; PATH_IMAGE_LINEPATH] THEN
  REWRITE_TAC[SEGMENT_REFL; INSERT_AC; SUBSET_REFL] THEN
   GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[set_of_list; polygonal_path] THEN CONJ_TAC THENL
   [REWRITE_TAC[PATH_IMAGE_LINEPATH; INSERT_SUBSET; ENDS_IN_SEGMENT] THEN
    REWRITE_TAC[EMPTY_SUBSET];
    REPEAT GEN_TAC THEN REPLICATE_TAC 3 DISCH_TAC THEN
    ONCE_REWRITE_TAC[INSERT_SUBSET] THEN
    SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
        HD; NOT_CONS_NIL; IN_UNION; ENDS_IN_SEGMENT; PATH_IMAGE_LINEPATH] THEN
    ASM SET_TAC[]]);;

let ARC_POLYGONAL_PATH_IMP_DISTINCT = prove
 (`!p:(real^N)list. arc(polygonal_path p) ==> PAIRWISE (\x y. ~(x = y)) p`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; ARC_LINEPATH_EQ] THEN
  X_GEN_TAC `a:real^N` THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; ARC_LINEPATH_EQ] THEN
  X_GEN_TAC `b:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; ARC_LINEPATH_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[PAIRWISE; ALL]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N`; `p:(real^N)list`] THEN
  REPLICATE_TAC 3 DISCH_TAC THEN
  SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
           HD; NOT_CONS_NIL; ARC_LINEPATH_EQ] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[PAIRWISE] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[ALL] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_SING; ENDS_IN_SEGMENT; PATH_IMAGE_LINEPATH] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM]
    (REWRITE_RULE[SUBSET] VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH))) THEN
  ASM_REWRITE_TAC[IN_SET_OF_LIST; MEM; DE_MORGAN_THM; GSYM ALL_MEM] THEN
  MESON_TAC[]);;

let PATH_POLYGONAL_PATH = prove
 (`!p:(real^N)list. path(polygonal_path p)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATH_LINEPATH] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATH_LINEPATH] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATH_LINEPATH] THEN
  SIMP_TAC[PATH_JOIN; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
           NOT_CONS_NIL; HD; PATH_LINEPATH]);;

let PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL = prove
 (`!p. ~(p = [])
       ==> path_image(polygonal_path p) SUBSET convex hull (set_of_list p)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[] THEN GEN_TAC THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[NOT_CONS_NIL] THEN CONJ_TAC THENL
   [REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH; set_of_list] THEN
    REWRITE_TAC[SEGMENT_REFL; CONVEX_HULL_SING] THEN SET_TAC[];
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[polygonal_path] THEN CONJ_TAC THENL
     [REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH; set_of_list] THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL; SUBSET_REFL];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN
      REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_CONVEX_HULL; set_of_list] THEN
      SIMP_TAC[HULL_MONO; INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
      MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[set_of_list] THEN
      SET_TAC[]]]);;

let PATH_IMAGE_POLYGONAL_PATH_SUBSET_SEGMENTS = prove
 (`!p x:real^N.
        arc(polygonal_path p) /\ 3 <= LENGTH p /\
        x IN path_image(polygonal_path p)
        ==> ?a b. MEM a p /\ MEM b p /\ x IN segment[a,b] /\
                  segment[a,b] SUBSET path_image(polygonal_path p) /\
                  ~(pathstart(polygonal_path p) IN segment[a,b] /\
                    pathfinish(polygonal_path p) IN segment[a,b])`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `a:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `b:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `c:real^N` THEN X_GEN_TAC `p:(real^N)list` THEN
  REPEAT DISCH_TAC THEN REWRITE_TAC[polygonal_path] THEN
  X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
           ARC_JOIN_EQ; NOT_CONS_NIL; HD] THEN
  REWRITE_TAC[PATHSTART_LINEPATH; PATH_IMAGE_LINEPATH; ARC_LINEPATH] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC LAND_CONV [IN_UNION] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
    ASM_REWRITE_TAC[MEM; SUBSET_UNION; ENDS_IN_SEGMENT] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP ARC_DISTINCT_ENDS) THEN
    REWRITE_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL] THEN
    DISCH_TAC THEN REWRITE_TAC[ARC_LINEPATH_EQ] THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `!p b. (s INTER p) SUBSET {b} /\
      x IN p /\ b IN s /\ ~(x = b)
      ==> ~(x IN s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`path_image(polygonal_path (CONS (b:real^N) (CONS c p)))`;
      `b:real^N`] THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT; PATHFINISH_IN_PATH_IMAGE];
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `3 <= SUC(SUC p) <=> ~(p = 0)`] THEN
    REWRITE_TAC[LENGTH_EQ_NIL] THEN ASM_CASES_TAC `p:(real^N)list = []` THENL
     [ASM_REWRITE_TAC[LENGTH; polygonal_path] THEN
      REWRITE_TAC[PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
      UNDISCH_TAC
       `x IN path_image(polygonal_path (CONS (b:real^N) (CONS c p)))` THEN
      ASM_REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH] THEN
      DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`b:real^N`; `c:real^N`] THEN
      ASM_REWRITE_TAC[MEM; SUBSET_UNION; ENDS_IN_SEGMENT] THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH] THEN
      REWRITE_TAC[ARC_LINEPATH_EQ] THEN
      MP_TAC(ISPECL [`a:real^N`; `b:real^N`] ENDS_IN_SEGMENT) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP ARC_DISTINCT_ENDS) THEN
      REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN SET_TAC[];
      ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^N` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real^N` THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[MEM];
        ASM_MESON_TAC[MEM];
        ASM_REWRITE_TAC[];
        ASM SET_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `(sab INTER p) SUBSET {b}
          ==> !sde a. sde SUBSET p /\
              ~(b IN sde) /\ d IN sde /\ a IN sde /\ a IN sab
              ==> F`) o el 2 o CONJUNCTS) THEN
        MAP_EVERY EXISTS_TAC [`segment[d:real^N,e]`; `a:real^N`] THEN
        ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* Rotating the starting point to move a preferred vertex forward.           *)
(* ------------------------------------------------------------------------- *)

let SET_OF_LIST_POLYGONAL_PATH_ROTATE = prove
 (`!p. ~(p = []) ==> set_of_list(CONS (LAST p) (BUTLAST p)) = set_of_list p`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [GSYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN SET_TAC[]);;

let PROPERTIES_POLYGONAL_PATH_SNOC = prove
 (`!p d:real^N.
        2 <= LENGTH p
        ==> path_image(polygonal_path(APPEND p [d])) =
            path_image(polygonal_path p ++ linepath(LAST p,d)) /\
            (arc(polygonal_path(APPEND p [d])) <=>
             arc(polygonal_path p ++ linepath(LAST p,d))) /\
            (simple_path(polygonal_path(APPEND p [d])) <=>
             simple_path(polygonal_path p ++ linepath(LAST p,d)))`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `a:real^N` THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[LENGTH; ARITH] THEN X_GEN_TAC `b:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[APPEND; polygonal_path; LAST; NOT_CONS_NIL]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N`; `p:(real^N)list`] THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `d:real^N` THEN DISCH_TAC THEN REWRITE_TAC[APPEND] THEN
  ONCE_REWRITE_TAC[LAST] THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  ONCE_REWRITE_TAC[polygonal_path] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:real^N`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[APPEND; LENGTH; ARITH_RULE `2 <= SUC(SUC n)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SIMP_TAC[GSYM ARC_ASSOC; GSYM SIMPLE_PATH_ASSOC; PATHSTART_JOIN;
           PATHFINISH_JOIN; PATHSTART_POLYGONAL_PATH;
           PATHFINISH_POLYGONAL_PATH;
           PATHSTART_LINEPATH; PATHFINISH_LINEPATH; NOT_CONS_NIL; HD] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
           PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
           PATHSTART_LINEPATH; PATHFINISH_LINEPATH; NOT_CONS_NIL; HD] THEN
    REWRITE_TAC[UNION_ACI];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:real^N = d` THENL
   [MATCH_MP_TAC(TAUT
     `(~p /\ ~p') /\ (q <=> q') ==> (p <=> p') /\ (q <=> q')`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARC_SIMPLE_PATH; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
      REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      ASM_REWRITE_TAC[PATHFINISH_POLYGONAL_PATH; NOT_CONS_NIL; LAST;
                      APPEND_EQ_NIL; LAST_APPEND];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SIMPLE_PATH_JOIN_LOOP_EQ o
     lhs o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_LINEPATH] THEN
      REWRITE_TAC[PATHFINISH_POLYGONAL_PATH; PATHSTART_LINEPATH] THEN
      REWRITE_TAC[NOT_CONS_NIL; HD; LAST; LAST_APPEND; APPEND_EQ_NIL];
      DISCH_THEN SUBST1_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SIMPLE_PATH_JOIN_LOOP_EQ o
     rhs o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
                  PATHFINISH_POLYGONAL_PATH] THEN
      REWRITE_TAC[NOT_CONS_NIL; HD; LAST; LAST_APPEND; APPEND_EQ_NIL];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD];
    MATCH_MP_TAC(TAUT
     `((q <=> p) /\ (q' <=> p')) /\ (p <=> p')
      ==> (p <=> p') /\ (q <=> q')`) THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SIMPLE_PATH_EQ_ARC THEN
      REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
                  PATHFINISH_POLYGONAL_PATH] THEN
      ASM_REWRITE_TAC[NOT_CONS_NIL; HD; LAST; LAST_APPEND; APPEND_EQ_NIL];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) ARC_JOIN_EQ o lhs o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_LINEPATH] THEN
      REWRITE_TAC[NOT_CONS_NIL; HD];
      DISCH_THEN SUBST1_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) ARC_JOIN_EQ o rhs o snd) THEN
    ANTS_TAC THENL
     [SIMP_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_LINEPATH; PATHSTART_JOIN;
               NOT_CONS_NIL; HD];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD]]);;

let PATH_IMAGE_POLYGONAL_PATH_ROTATE = prove
 (`!p:(real^N)list.
        2 <= LENGTH p /\ LAST p = HD p
        ==> path_image(polygonal_path(APPEND (TL p) [HD(TL p)])) =
            path_image(polygonal_path p)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `a:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `b:real^N` THEN REWRITE_TAC[HD; TL] THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN CONJ_TAC THENL
   [REWRITE_TAC[LAST; APPEND; NOT_CONS_NIL] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N`; `p:(real^N)list`] THEN
  REPLICATE_TAC 3 (DISCH_THEN(K ALL_TAC)) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[LAST; NOT_CONS_NIL] THEN ONCE_REWRITE_TAC[GSYM LAST] THEN
  DISCH_TAC THEN
  SIMP_TAC[PROPERTIES_POLYGONAL_PATH_SNOC; LENGTH;
           ARITH_RULE `2 <= SUC(SUC n)`] THEN
  ONCE_REWRITE_TAC[LAST] THEN ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [polygonal_path] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LAST]) THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
           PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
           LAST; NOT_CONS_NIL; HD] THEN
  REWRITE_TAC[UNION_ACI]);;

let SIMPLE_PATH_POLYGONAL_PATH_ROTATE = prove
 (`!p:(real^N)list.
        2 <= LENGTH p /\ LAST p = HD p
        ==> (simple_path(polygonal_path(APPEND (TL p) [HD(TL p)])) =
             simple_path(polygonal_path p))`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `a:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `b:real^N` THEN REWRITE_TAC[HD; TL] THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN CONJ_TAC THENL
   [REWRITE_TAC[LAST; APPEND; NOT_CONS_NIL] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N`; `p:(real^N)list`] THEN
  REPLICATE_TAC 3 (DISCH_THEN(K ALL_TAC)) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[LAST; NOT_CONS_NIL] THEN ONCE_REWRITE_TAC[GSYM LAST] THEN
  DISCH_TAC THEN
  SIMP_TAC[PROPERTIES_POLYGONAL_PATH_SNOC; LENGTH;
           ARITH_RULE `2 <= SUC(SUC n)`] THEN
  ONCE_REWRITE_TAC[LAST] THEN ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [polygonal_path] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LAST]) THEN
  ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
               PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
               PATHFINISH_POLYGONAL_PATH; LAST; NOT_CONS_NIL; HD] THEN
  REWRITE_TAC[INSERT_AC; INTER_ACI; CONJ_ACI]);;

let ROTATE_LIST_TO_FRONT_1 = prove
 (`!P l a:A.
      (!l. P(l) ==> 3 <= LENGTH l /\ LAST l = HD l) /\
      (!l. P(l) ==> P(APPEND (TL l) [HD(TL l)])) /\
      P l /\ MEM a l
      ==> ?l'. EL 1 l' = a /\ P l'`,
  let lemma0 = prove
     (`!P. (!i. P i /\ 0 < i ==> P(i - 1)) /\ (?k. 0 < k /\ P k)
             ==> P 1`,
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `!i:num. i < k ==> P(k - i)` MP_TAC THENL
       [INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_0] THEN DISCH_TAC THEN
        REWRITE_TAC[ARITH_RULE `k - SUC i = k - i - 1`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        CONJ_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_ARITH_TAC;
        DISCH_THEN(MP_TAC o SPEC `k - 1`) THEN
        ASM_SIMP_TAC[ARITH_RULE `0 < k ==> k - 1 < k /\ k - (k - 1) = 1`]]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?i l'. 0 < i /\ i < LENGTH l' /\ P l' /\ EL i l' = (a:A)`
  MP_TAC THENL
   [SUBGOAL_THEN `~(l:A list = [])` ASSUME_TAC THENL
     [ASM_MESON_TAC[LENGTH; ARITH_RULE `~(3 <= 0)`]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MEM_EXISTS_EL]) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC (ARITH_RULE `i = 0 \/ 0 < i`)
    THENL
     [EXISTS_TAC `LENGTH(l:A list) - 2` THEN
      EXISTS_TAC `(APPEND (TL l) [HD(TL l):A])` THEN
      ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_TL; EL_APPEND] THEN
      REWRITE_TAC[LT_REFL; LENGTH; SUB_REFL; EL; HD] THEN
      SUBGOAL_THEN `3 <= LENGTH(l:A list)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
      ASM_SIMP_TAC[ARITH_RULE `3 <= n ==> n - 2 < n - 1`] THEN
      ASM_SIMP_TAC[EL_TL; ARITH_RULE `3 <= n ==> n - 2 + 1 = n - 1`] THEN
      ASM_MESON_TAC[LAST_EL];
      MAP_EVERY EXISTS_TAC [`i:num`; `l:A list`] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT] lemma0)) THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN X_GEN_TAC `k:num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:A list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `APPEND (TL m) [HD(TL m):A]` THEN
    SUBGOAL_THEN `~(m:A list = [])` ASSUME_TAC THENL
     [ASM_MESON_TAC[LENGTH; ARITH_RULE `~(3 <= 0)`]; ALL_TAC] THEN
    ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_TL; EL_APPEND] THEN
    ASM_REWRITE_TAC[LENGTH] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    ASM_SIMP_TAC[EL_TL; ARITH_RULE `0 < k ==> k - 1 + 1 = k`]]);;

let ROTATE_LIST_TO_FRONT_0 = prove
 (`!P l a:A.
      (!l. P(l) ==> 3 <= LENGTH l /\ LAST l = HD l) /\
      (!l. P(l) ==> P(APPEND (TL l) [HD(TL l)])) /\
      P l /\ MEM a l
      ==> ?l'. HD l' = a /\ P l'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`P:A list->bool`; `l:A list`; `a:A`]
    ROTATE_LIST_TO_FRONT_1) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `l':A list` THEN
  STRIP_TAC THEN EXISTS_TAC `APPEND (TL l') [HD(TL l'):A]` THEN
  ASM_SIMP_TAC[] THEN UNDISCH_TAC `EL 1 l' = (a:A)` THEN
  SUBGOAL_THEN `3 <= LENGTH(l':A list)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`l':A list`,`p:A list`) THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  REWRITE_TAC[APPEND; HD; TL; num_CONV `1`; EL]);;

(* ------------------------------------------------------------------------- *)
(* We can pick a transformation to make all y coordinates distinct.          *)
(* ------------------------------------------------------------------------- *)

let DISTINGUISHING_ROTATION_EXISTS_PAIR = prove
 (`!x y. ~(x = y)
         ==> FINITE {t | &0 <= t /\ t < &2 * pi /\
                         (rotate2d t x)$2 = (rotate2d t y)$2}`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
  ONCE_REWRITE_TAC[GSYM ROTATE2D_SUB] THEN
  REWRITE_TAC[GSYM IM_DEF; GSYM real; GSYM ARG_EQ_0_PI] THEN
  REWRITE_TAC[FINITE_UNION; SET_RULE
   `{x | p x /\ q x /\ (r x \/ s x)} =
    {x | p x /\ q x /\ r x} UNION {x | p x /\ q x /\ s x}`] THEN
  CONJ_TAC THEN
  MATCH_MP_TAC(MESON[FINITE_SING; FINITE_SUBSET]
       `(?a. s SUBSET {a}) ==> FINITE s`) THEN
  MATCH_MP_TAC(SET_RULE
   `(!x y. x IN s /\ y IN s ==> x = y) ==> ?a. s SUBSET {a}`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ARG_ROTATE2D_UNIQUE_2PI THEN EXISTS_TAC `x - y:complex` THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_0]);;

let DISTINGUISHING_ROTATION_EXISTS = prove
 (`!s. FINITE s ==> ?t. pairwise (\x y. ~(x$2 = y$2)) (IMAGE (rotate2d t) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `INFINITE ({t | &0 <= t /\ t < &2 * pi} DIFF
              UNIONS (IMAGE (\(x,y). {t | &0 <= t /\ t < &2 * pi /\
                                          (rotate2d t x)$2 = (rotate2d t y)$2})
                            ({(x,y) | x IN s /\ y IN s /\ ~(x = y)})))`
  MP_TAC THENL
   [MATCH_MP_TAC INFINITE_DIFF_FINITE THEN
    REWRITE_TAC[INFINITE; FINITE_REAL_INTERVAL; REAL_NOT_LE] THEN
    CONJ_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{(x:real^2,y:real^2) | x IN s /\ y IN s}` THEN
      ASM_SIMP_TAC[FINITE_PRODUCT_DEPENDENT] THEN SET_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      ASM_SIMP_TAC[DISTINGUISHING_ROTATION_EXISTS_PAIR]];
    DISCH_THEN(MP_TAC o MATCH_MP (MESON[FINITE_EMPTY; INFINITE]
     `INFINITE s ==> ~(s = {})`)) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[UNIONS_IMAGE; EXISTS_IN_GSPEC] THEN
    REWRITE_TAC[pairwise; IN_ELIM_THM] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC[ROTATE2D_EQ] THEN MESON_TAC[]]);;

let DISTINGUISHING_ROTATION_EXISTS_POLYGON = prove
 (`!p:(real^2)list.
        ?f q. (?g. orthogonal_transformation g /\ f = MAP g) /\
              (!x y. MEM x q /\ MEM y q /\ ~(x = y) ==> ~(x$2 = y$2)) /\
              f q = p`,
  GEN_TAC THEN MP_TAC(ISPEC
   `set_of_list(p:(real^2)list)` DISTINGUISHING_ROTATION_EXISTS) THEN
  REWRITE_TAC[FINITE_SET_OF_LIST; pairwise] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_SET_OF_LIST; ROTATE2D_EQ] THEN
  REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `MAP (rotate2d(--t))` THEN
  EXISTS_TAC `MAP (rotate2d t) p` THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF; GSYM ROTATE2D_ADD] THEN
  REWRITE_TAC[REAL_ADD_LINV; ROTATE2D_ZERO; MAP_ID] THEN
  CONJ_TAC THENL [MESON_TAC[ORTHOGONAL_TRANSFORMATION_ROTATE2D]; ALL_TAC] THEN
  REWRITE_TAC[GSYM IN_SET_OF_LIST; SET_OF_LIST_MAP] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[IN_SET_OF_LIST; ROTATE2D_EQ] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Proof that we can chop a polygon's inside in two.                         *)
(* ------------------------------------------------------------------------- *)

let POLYGON_CHOP_IN_TWO = prove
 (`!p:(real^2)list.
        simple_path(polygonal_path p) /\
        pathfinish(polygonal_path p) = pathstart(polygonal_path p) /\
        5 <= LENGTH p
        ==> ?a b. ~(a = b) /\ MEM a p /\ MEM b p /\
                  segment(a,b) SUBSET inside(path_image(polygonal_path p))`,
  let wlog_lemma = MESON[]
   `(!x. ?f:A->A y. transform f /\ nice y /\ f y = x)
    ==> !P. (!f x. transform f ==> (P(f x) <=> P x)) /\
            (!x. nice x ==> P x)
            ==> !x. P x` in
  let between_lemma = prove
   (`!a c u v m:real^N.
          collinear {a,c,u,v,m} /\ m IN segment[u,v] /\ m IN segment(a,c)
          ==> u IN segment(a,c) \/ v IN segment(a,c) \/
              segment[a,c] SUBSET segment[u,v]`,
    REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
    REWRITE_TAC[INSERT_SUBSET; LEFT_IMP_EXISTS_THM; EMPTY_SUBSET] THEN
    MAP_EVERY X_GEN_TAC [`origin:real^N`; `dir:real^N`] THEN
    GEOM_ORIGIN_TAC `origin:real^N` THEN
    REWRITE_TAC[AFFINE_HULL_2; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `dir:real^N = vec 0` THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_RZERO; SEGMENT_REFL; SUBSET_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET_SEGMENT] THEN
    ASM_SIMP_TAC[SEGMENT_SCALAR_MULTIPLE; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RCANCEL] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1] THEN
    REAL_ARITH_TAC) in
  MATCH_MP_TAC(MATCH_MP wlog_lemma DISTINGUISHING_ROTATION_EXISTS_POLYGON) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MESON[] `(!x y. (?z. P z /\ x = f z) ==> Q x y) <=>
                         (!z y. P z ==> Q (f z) y)`] THEN
    REWRITE_TAC[ORTHOGONAL_TRANSFORMATION] THEN
    GEOM_TRANSFORM_TAC [];
    ALL_TAC] THEN
  X_GEN_TAC `q:(real^2)list` THEN DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?b:real^2. MEM b q /\ !d. MEM d q ==> b$2 <= d$2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (\x:real^2. x$2) (set_of_list q)`
        INF_FINITE) THEN
    SIMP_TAC[FINITE_SET_OF_LIST; FINITE_IMAGE] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; SET_OF_LIST_EQ_EMPTY] THEN
    UNDISCH_TAC `5 <= LENGTH(q:(real^2)list)` THEN
    ASM_CASES_TAC `q:(real^2)list = []` THEN
    ASM_REWRITE_TAC[LENGTH; ARITH; FORALL_IN_IMAGE] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_IMAGE; LEFT_AND_EXISTS_THM; IN_SET_OF_LIST] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^2` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?p:(real^2)list.
        EL 1 p = b /\ LAST p = HD p /\
        LENGTH p = LENGTH q /\ set_of_list p = set_of_list q /\
        path_image(polygonal_path p) = path_image(polygonal_path q) /\
        simple_path(polygonal_path p) /\
        pathfinish(polygonal_path p) = pathstart(polygonal_path p)`
  MP_TAC THENL
   [MATCH_MP_TAC ROTATE_LIST_TO_FRONT_1 THEN EXISTS_TAC `q:(real^2)list` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`pathfinish(polygonal_path(q:(real^2)list)) =
       pathstart(polygonal_path q)`;
      `5 <= LENGTH(q:(real^2)list)`] THEN
    ASM_CASES_TAC `q:(real^2)list = []` THEN
    ASM_REWRITE_TAC[LENGTH; ARITH] THEN
    ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
    DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `l:(real^2)list` THEN
    REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL] THEN
    ASM_CASES_TAC `l:(real^2)list = []` THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(TL l:(real^2)list = [])` ASSUME_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(real^2)list->num`) THEN
      ASM_SIMP_TAC[LENGTH; LENGTH_TL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LAST_APPEND; LENGTH_APPEND; LENGTH_TL; NOT_CONS_NIL] THEN
    ASM_REWRITE_TAC[LAST; HD_APPEND; LENGTH] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`HD(l:(real^2)list) = LAST l`; `5 <= LENGTH(q:(real^2)list)`;
        `~(l:(real^2)list = [])`] THEN
      ASM_REWRITE_TAC[] THEN
      SPEC_TAC(`l:(real^2)list`,`l:(real^2)list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[HD; TL; APPEND] THEN
      REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
       `a IN s /\ b IN s ==> s UNION {a} = b INSERT s`) THEN
      ASM_REWRITE_TAC[LAST] THEN ONCE_ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LAST] THEN UNDISCH_TAC `5 <= LENGTH(CONS (h:real^2) t)` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH] THEN
      REWRITE_TAC[IN_SET_OF_LIST; MEM_EXISTS_EL; LENGTH] THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `0` THEN REWRITE_TAC[EL] THEN ASM_ARITH_TAC;
        EXISTS_TAC `LENGTH(t:(real^2)list) - 1` THEN
        ASM_SIMP_TAC[LAST_EL] THEN ASM_ARITH_TAC];
      MATCH_MP_TAC PATH_IMAGE_POLYGONAL_PATH_ROTATE THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MP_TAC(ISPEC `l:(real^2)list` SIMPLE_PATH_POLYGONAL_PATH_ROTATE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_THEN `pathfinish(polygonal_path(q:(real^2)list)) =
                pathstart(polygonal_path q)` (K ALL_TAC) THEN
  UNDISCH_THEN `simple_path(polygonal_path(q:(real^2)list))` (K ALL_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(real^2)list` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [EXTENSION] THEN
  REWRITE_TAC[IN_SET_OF_LIST] THEN DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> REWRITE_TAC[GSYM th] THEN
              RULE_ASSUM_TAC(REWRITE_RULE[GSYM th])) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) STRIP_ASSUME_TAC) THEN
  UNDISCH_THEN `MEM (b:real^2) r` (K ALL_TAC) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`r:(real^2)list`,`r:(real^2)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `a:real^2` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `b':real^2` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `c:real^2` THEN X_GEN_TAC `p:(real^2)list` THEN
  REPLICATE_TAC 3 (DISCH_THEN(K ALL_TAC)) THEN
  REWRITE_TAC[num_CONV `1`; EL; HD; TL] THEN
  ASM_CASES_TAC `b':real^2 = b` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(K ALL_TAC) THEN
  REWRITE_TAC[ARITH_RULE `5 <= SUC(SUC(SUC n)) <=> ~(n = 0) /\ 2 <= n`] THEN
  ASM_CASES_TAC `p:(real^2)list = []` THEN ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN
  ASM_SIMP_TAC[POLYGONAL_PATH_CONS_CONS; LAST; NOT_CONS_NIL] THEN
  REWRITE_TAC[PATHSTART_JOIN; PATHSTART_LINEPATH] THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:real^2`) THEN
  REWRITE_TAC[MESON[MEM] `MEM b (CONS a (CONS b l))`] THEN
  DISCH_THEN(ASSUME_TAC o GSYM) THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`linepath(a:real^2,b)`;
    `polygonal_path(CONS (b:real^2) (CONS c p))`]
   SIMPLE_PATH_JOIN_IMP) THEN
  ASM_SIMP_TAC[POLYGONAL_PATH_CONS_CONS] THEN
  REWRITE_TAC[PATHFINISH_LINEPATH; PATHSTART_JOIN; PATHSTART_LINEPATH] THEN
  REWRITE_TAC[ARC_LINEPATH_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN MP_TAC th)
                MP_TAC) THEN
  SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
           NOT_CONS_NIL; HD] THEN
  REWRITE_TAC[ARC_LINEPATH_EQ; GSYM CONJ_ASSOC; PATH_IMAGE_LINEPATH] THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
           HD; NOT_CONS_NIL] THEN
  REWRITE_TAC[SET_RULE `s INTER (t UNION u) SUBSET v <=>
                        s INTER t SUBSET v /\ s INTER u SUBSET v`] THEN
  ASM_CASES_TAC `a:real^2 = c` THENL
   [DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_SYM; INTER_ACI] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE [IMP_CONJ_ALT]
        FINITE_SUBSET)) THEN
    REWRITE_TAC[FINITE_SEGMENT; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `CONS (b:real^2) (CONS c p)`
    ARC_POLYGONAL_PATH_IMP_DISTINCT) THEN
  ASM_SIMP_TAC[POLYGONAL_PATH_CONS_CONS] THEN
  REWRITE_TAC[PAIRWISE; ALL] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  REWRITE_TAC[MESON[] `(!x. P x ==> ~(a = x)) <=> ~(P a)`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(b:real^2)$2 < (a:real^2)$2 /\
                (b:real^2)$2 < (c:real^2)$2 /\
                (!v. MEM v p ==> (b:real^2)$2 < (v:real^2)$2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear{a:real^2,b,c}` ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_BETWEEN_CASES; BETWEEN_IN_SEGMENT] THEN
    SUBGOAL_THEN `FINITE(segment[a:real^2,b] INTER segment[b,c])` MP_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{a:real^2,b}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `segment[a:real^2,b] INTER segment[b,c] = segment[a,b]`
       (fun th -> ASM_REWRITE_TAC[FINITE_SEGMENT; th]) THEN
      REWRITE_TAC[SET_RULE `s INTER t = s <=> s SUBSET t`] THEN
      ASM_REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT];
      DISCH_TAC THEN UNDISCH_TAC `b IN segment[c:real^2,a]` THEN
      ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT] THEN
      ASM_REWRITE_TAC[IN_SEGMENT; NOT_IN_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(MP_TAC o AP_TERM `\x:real^2. x$2`) THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      MATCH_MP_TAC(REAL_ARITH
       `(&1 - u) * b < (&1 - u) * c /\ u * b < u * a
        ==> ~(b = (&1 - u) * c + u * a)`) THEN
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_SUB_LT];
      SUBGOAL_THEN `segment[a:real^2,b] INTER segment[b,c] = segment[b,c]`
       (fun th -> ASM_REWRITE_TAC[FINITE_SEGMENT; th]) THEN
      REWRITE_TAC[SET_RULE `s INTER t = t <=> t SUBSET s`] THEN
      ASM_REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?e. &0 < e /\
         e <= (a:real^2)$2 - (b:real^2)$2 /\
         e <= (c:real^2)$2 - (b:real^2)$2 /\
         !v. MEM v p ==> e <= (v:real^2)$2 - (b:real^2)$2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (\v. (v:real^2)$2 - (b:real^2)$2)
                        (set_of_list(CONS a (CONS b (CONS c p)))
                          DELETE b)`
                INF_FINITE) THEN
    ASM_SIMP_TAC[FINITE_SET_OF_LIST; FINITE_IMAGE; FINITE_DELETE] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[set_of_list; GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `a:real^2` THEN ASM_REWRITE_TAC[IN_DELETE; IN_INSERT];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[IN_IMAGE] THEN
    ASM_REWRITE_TAC[set_of_list; FORALL_IN_INSERT; IMP_CONJ; IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real^2` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
    DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC[IN_SET_OF_LIST] THEN
    DISCH_TAC THEN EXISTS_TAC `(d:real^2)$2 - (b:real^2)$2` THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INSERT; IN_SET_OF_LIST]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`a':real^2 = (&1 - e / (a$2 - b$2)) % b + e / (a$2 - b$2) % a`;
    `c':real^2 = (&1 - e / (c$2 - b$2)) % b + e / (c$2 - b$2) % c`] THEN
  SUBGOAL_THEN
   `a' IN segment[b:real^2,a] /\ c' IN segment[b,c]`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a'"; "c'"] THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % a + u % b = (&1 - v) % a + v % b <=>
      (u - v) % (b - a) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; REAL_SUB_0] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> r /\ p /\ q`] THEN
    REWRITE_TAC[UNWIND_THM1] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_DIV; REAL_SUB_LE;
                 REAL_LE_LDIV_EQ; REAL_SUB_LT; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a':real^2 = b) /\ ~(c':real^2 = b)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a'"; "c'"] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % a + u % b = a <=> u % (b - a) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_SUB_LT] THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear{a':real^2,b,c'}` ASSUME_TAC THENL
   [UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN ONCE_REWRITE_TAC[COLLINEAR_3] THEN
    MAP_EVERY EXPAND_TAC ["a'"; "c'"] THEN
    REWRITE_TAC[VECTOR_ARITH `((&1 - u) % b + u % a) - b = u % (a - b)`] THEN
    REWRITE_TAC[GSYM DOT_CAUCHY_SCHWARZ_EQUAL; DOT_LMUL; DOT_RMUL] THEN
    MATCH_MP_TAC(REAL_FIELD
     `~(a = &0) /\ ~(c = &0)
      ==> (a * c * x) pow 2 = (a * a * y) * (c * c * z)
          ==> x pow 2 = y * z`) THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_SUB_LT] THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a':real^2 = c')` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~collinear{a':real^2,b,c'}` THEN
    ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent{a':real^2,b,c'}` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_DEPENDENT_IMP_COLLINEAR_3]; ALL_TAC] THEN
  MP_TAC(ISPEC `{a':real^2,b,c'}` INTERIOR_CONVEX_HULL_EQ_EMPTY) THEN
  REWRITE_TAC[DIMINDEX_2; HAS_SIZE; ARITH; FINITE_INSERT; FINITE_EMPTY] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex hull {a,b,c} INTER {x:real^2 | x$2 - b$2 <= e} =
                convex hull {a',b,c'}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {b,a,c}`] THEN
      REWRITE_TAC[CONVEX_HULL_3_ALT] THEN
      REWRITE_TAC[SUBSET; IN_INTER; FORALL_IN_GSPEC; IMP_CONJ] THEN
      REWRITE_TAC[IN_ELIM_THM; VECTOR_ARITH
       `a + x:real^N = a + y <=> x = y`] THEN
      MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN
      REPLICATE_TAC 3 DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["a'"; "c'"] THEN
      REWRITE_TAC[VECTOR_ARITH
       `((&1 - u) % b + u % a) - b:real^N = u % (a - b)`] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REWRITE_TAC[REAL_ADD_SUB; VECTOR_SUB_COMPONENT] THEN STRIP_TAC THEN
      EXISTS_TAC `(s * ((a:real^2)$2 - (b:real^2)$2)) / e` THEN
      EXISTS_TAC `(t * ((c:real^2)$2 - (b:real^2)$2)) / e` THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_SUB_LT; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REAL_ARITH `a / e + b / e:real = (a + b) / e`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC] THEN BINOP_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC(REAL_FIELD
       `y < x /\ &0 < e ==> s = (s * (x - y)) / e * e / (x - y)`) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTER; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[HULL_INC; IN_INSERT; REAL_SUB_REFL; REAL_LT_IMP_LE] THEN
      SIMP_TAC[REAL_LE_SUB_RADD; CONVEX_INTER; CONVEX_HALFSPACE_COMPONENT_LE;
               CONVEX_CONVEX_HULL] THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `a' IN segment[b:real^2,a]` THEN
        SPEC_TAC(`a':real^2`,`x:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[];
        EXPAND_TAC "a'";
        UNDISCH_TAC `c' IN segment[b:real^2,c]` THEN
        SPEC_TAC(`c':real^2`,`x:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[];
        EXPAND_TAC "c'"] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REWRITE_TAC[REAL_ARITH
       `(&1 - u) * b + u * a <= e + b <=> (a - b) * u <= e`] THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_SUB_LT] THEN
      REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interior(convex hull {a,b,c}) INTER {x:real^2 | x$2 - b$2 < e} =
    interior(convex hull {a',b,c'})`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_SUB_RADD; GSYM INTERIOR_HALFSPACE_COMPONENT_LE] THEN
    ASM_REWRITE_TAC[GSYM INTERIOR_INTER; GSYM REAL_LE_SUB_RADD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d:real^2. d IN interior(convex hull {a',b,c'}) /\ ~(d$1 = b$1)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(interior(convex hull {a':real^2,b,c'}) = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^2)$1 = (b:real^2)$1` THENL
     [ALL_TAC; EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(MP_TAC o SPEC `x + k / &2 % basis 1:real^2`) THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x,x + e) = norm e`] THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; ARITH] THEN
      UNDISCH_TAC `&0 < k` THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    EXISTS_TAC `x + k / &2 % basis 1:real^2` THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_GE_1; ARITH; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> ~(b + k / &2 = b)`] THEN
    REWRITE_TAC[IN_INTERIOR] THEN EXISTS_TAC `k / &2` THEN
    ASM_REWRITE_TAC[REAL_HALF; SUBSET] THEN X_GEN_TAC `y:real^2` THEN
    REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_BALL] THEN MATCH_MP_TAC(NORM_ARITH
     `!a. dist(x + a,y) < k / &2 /\ norm(a) = k / &2 ==> dist(x,y) < k`) THEN
    EXISTS_TAC `k / &2 % basis 1:real^2` THEN ASM_REWRITE_TAC[NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    UNDISCH_TAC `&0 < k` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `path_image(polygonal_path(CONS a (CONS b (CONS c p))))
     SUBSET {x:real^2 | x$2 >= b$2}`
  MP_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC
     `convex hull(set_of_list(CONS (a:real^2) (CONS b (CONS c p))))` THEN
    SIMP_TAC[PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL; NOT_CONS_NIL] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GE] THEN
    REWRITE_TAC[set_of_list; INSERT_SUBSET; IN_ELIM_THM; EMPTY_SUBSET] THEN
    ASM_SIMP_TAC[SUBSET; IN_SET_OF_LIST; real_ge; IN_ELIM_THM; REAL_LT_IMP_LE;
                 REAL_LE_REFL];
    GEN_REWRITE_TAC LAND_CONV [SUBSET] THEN
    ASM_SIMP_TAC[POLYGONAL_PATH_CONS_CONS; NOT_CONS_NIL] THEN
    REWRITE_TAC[IN_ELIM_THM; real_ge] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `(:real^2) DIFF {x | x$2 >= b$2} SUBSET
    outside(path_image
                 (linepath(a,b) ++ linepath(b,c) ++ polygonal_path(CONS c p)))`
  MP_TAC THENL
   [MATCH_MP_TAC OUTSIDE_SUBSET_CONVEX THEN
    REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GE] THEN
    ASM_REWRITE_TAC[SUBSET; real_ge; IN_ELIM_THM];
    REWRITE_TAC[SUBSET; real_ge; IN_ELIM_THM; IN_UNIV;
                IN_DIFF; REAL_NOT_LE] THEN
    DISCH_TAC] THEN
  ABBREV_TAC
   `d':real^2 = d - (&1 + (d:real^2)$2 - (b:real^2)$2) % basis 2` THEN
  SUBGOAL_THEN `(d':real^2) IN outside(path_image
        (linepath(a,b) ++ linepath(b,c) ++ polygonal_path(CONS c p)))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "d'" THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a':real^2)$2 - (b:real^2)$2 = e /\
                (c':real^2)$2 - (b:real^2)$2 = e`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a'"; "c'"] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC[REAL_ARITH `((&1 - u) * b + u * a) - b = u * (a - b)`] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_ARITH `b < a ==> ~(a - b = &0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^2)$2 < (d:real^2)$2 /\ (d:real^2)$2 < (b:real^2)$2 + e`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(d:real^2) IN interior(convex hull {a',b,c'})` THEN
    ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3_MINIMAL] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:real`; `s:real`; `t:real`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_EQ_SUB_RADD]) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `r + s + t = &1 ==> s = &1 - (r + t)`)) THEN
    REWRITE_TAC[REAL_ARITH
     `b < r * x + (&1 - (r + t)) * b + t * x <=> (r + t) * b < (r + t) * x`;
                REAL_ARITH
     `r * (e + b) + (&1 - (r + t)) * b + t * (e + b) < b + e <=>
      (r + t) * e < &1 * e`] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_ADD; REAL_LT_RMUL_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(d':real^2)$2 + &1 = (b:real^2)$2` ASSUME_TAC THENL
   [EXPAND_TAC "d'" THEN REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {a':real^2,b,c'} SUBSET convex hull {a,b,c}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL; INSERT_SUBSET; EMPTY_SUBSET] THEN
    SIMP_TAC[HULL_INC; IN_INSERT] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(a':real^2) IN segment[b,a]` THEN
      SPEC_TAC(`a':real^2`,`x:real^2`);
      UNDISCH_TAC `(c':real^2) IN segment[b,c]` THEN
      SPEC_TAC(`c':real^2`,`x:real^2`)] THEN
    REWRITE_TAC[GSYM SUBSET] THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(d' IN convex hull {a:real^2,b,c})` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!t. s SUBSET t /\ ~(x IN t) ==> ~(x IN s)`) THEN
    EXISTS_TAC `{x | (x:real^2)$2 >= (b:real^2)$2}` THEN
    SIMP_TAC[SUBSET_HULL; CONVEX_HALFSPACE_COMPONENT_GE] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM; real_ge] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(d' IN convex hull {a':real^2,b,c'})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(segment[d:real^2,d'] INTER frontier(convex hull {a',b,c'}) = {})`
  MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_INTER_FRONTIER THEN
    REWRITE_TAC[CONNECTED_SEGMENT; GSYM MEMBER_NOT_EMPTY] THEN CONJ_TAC THENL
     [EXISTS_TAC `d:real^2` THEN REWRITE_TAC[ENDS_IN_SEGMENT; IN_INTER] THEN
      ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
      EXISTS_TAC `d':real^2` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT; IN_DIFF]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2` MP_TAC) THEN REWRITE_TAC[IN_INTER] THEN
  ASM_CASES_TAC `x:real^2 = d` THENL
   [ASM_REWRITE_TAC[IN_DIFF; frontier]; ALL_TAC] THEN
  ASM_CASES_TAC `x:real^2 = d'` THENL
   [ASM_REWRITE_TAC[IN_DIFF; frontier] THEN
    SUBGOAL_THEN `closure(convex hull {a':real^2,b,c'}) = convex hull {a',b,c'}`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MESON_TAC[COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT; FINITE_RULES];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(d':real^2)$1 = (d:real^2)$1` ASSUME_TAC THENL
   [EXPAND_TAC "d'" THEN REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2)$1 = (d:real^2)$1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:real^2`; `d':real^2`; `x:real^2`] SEGMENT_VERTICAL) THEN
    ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^2 = b)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2)$2 < (b:real^2)$2 + e` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:real^2`; `d':real^2`; `x:real^2`] SEGMENT_VERTICAL) THEN
    ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^2 = a) /\ ~(x = c)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN (segment(b,a) UNION segment(b,c))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN frontier(convex hull {a':real^2,b,c'})` THEN
    ASM_SIMP_TAC[open_segment; IN_UNION; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[FRONTIER_OF_TRIANGLE] THEN MATCH_MP_TAC(SET_RULE
     `~(x IN u) /\ s SUBSET s' /\ t SUBSET t'
      ==> x IN (s UNION t UNION u) ==> x IN s' \/ x IN t'`) THEN
    ASM_REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c':real^2`; `a':real^2`; `x:real^2`]
      SEGMENT_HORIZONTAL) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[d:real^2,d'] INTER path_image(polygonal_path(CONS c p)) = {}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!u. t SUBSET u /\ s INTER u = {} ==> s INTER t = {}`) THEN
    EXISTS_TAC `{x:real^2 | x$2 >= (b:real^2)$2 + e}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `convex hull(set_of_list(CONS c p)) :real^2->bool` THEN
      SIMP_TAC[PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL; NOT_CONS_NIL] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GE;
                  set_of_list; INSERT_SUBSET] THEN
      REWRITE_TAC[SUBSET; IN_SET_OF_LIST; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[real_ge; REAL_ARITH `b + e <= x <=> e <= x - b`];
      REWRITE_TAC[SET_RULE `s INTER t = {} <=> !x. x IN s ==> ~(x IN t)`] THEN
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL[`d:real^2`; `d':real^2`; `y:real^2`] SEGMENT_VERTICAL) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; real_ge] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^2) IN interior(convex hull {a,b,c})` ASSUME_TAC THENL
   [UNDISCH_TAC `(d:real^2) IN interior(convex hull {a', b, c'})` THEN
    SPEC_TAC(`d:real^2`,`d:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC SUBSET_INTERIOR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(d':real^2 = d)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. y IN segment[d,d'] /\
               y IN (segment (b,a) UNION segment (b,c))
               ==> y = x`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `collinear {d:real^2,x,y}` MP_TAC THENL
     [REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
      MAP_EVERY EXISTS_TAC [`d:real^2`; `d':real^2`] THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC
       (REWRITE_RULE[SUBSET] CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
      ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; ENDS_IN_SEGMENT] THEN
      ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION];
      ALL_TAC] THEN
    REWRITE_TAC[COLLINEAR_BETWEEN_CASES; BETWEEN_IN_SEGMENT] THEN
    ASM_SIMP_TAC[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_CASES_TAC `x:real^2 = y` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(x:real^2) IN frontier(convex hull {a,b,c}) /\
      (y:real^2) IN frontier(convex hull {a,b,c})`
    MP_TAC THENL
     [REWRITE_TAC[FRONTIER_OF_TRIANGLE] THEN
      REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_UNION]) THEN ASM_MESON_TAC[SEGMENT_SYM];
      REWRITE_TAC[frontier; IN_DIFF]] THEN
    ASM_CASES_TAC `y:real^2 = d` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(d:real^2) IN segment (x,y)`;
        `(y:real^2) IN segment [d,d']`;
        `(x:real^2) IN segment(d,d')`] THEN
      ASM_REWRITE_TAC[IN_SEGMENT] THEN
      REPLICATE_TAC 2 (STRIP_TAC THEN ASM_REWRITE_TAC[]) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; VECTOR_ARITH
       `d = (&1 - w) % ((&1 - u) % d + u % d') + w % ((&1 - v) % d + v % d') <=>
        ((&1 - w) * u + w * v) % (d' - d) = vec 0`] THEN
      DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_MUL; REAL_LT_IMP_LE; REAL_ARITH
       `&0 <= x /\ &0 <= y ==> (x + y = &0 <=> x = &0 /\ y = &0)`] THEN
      REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `~(x IN interior(convex hull {a:real^2, b, c}))` THEN
      UNDISCH_TAC `x IN segment (y:real^2,d)` THEN
      SPEC_TAC(`x:real^2`,`x:real^2`) THEN ASM_REWRITE_TAC[GSYM SUBSET] THEN
      ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
      MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
      ASM_REWRITE_TAC[CONVEX_CONVEX_HULL];
      UNDISCH_TAC `~(y IN interior(convex hull {a:real^2, b, c}))` THEN
      UNDISCH_TAC `y IN segment (d:real^2,x)` THEN
      SPEC_TAC(`y:real^2`,`y:real^2`) THEN ASM_REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
      ASM_REWRITE_TAC[CONVEX_CONVEX_HULL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathfinish(polygonal_path p) = (a:real^2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHFINISH_POLYGONAL_PATH]; ALL_TAC] THEN
  SUBGOAL_THEN `segment(a:real^2,b) INTER segment(b,c) = {}` ASSUME_TAC THENL
   [UNDISCH_TAC `segment[a:real^2,b] INTER segment[b,c] SUBSET {a, b}` THEN
    REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    MATCH_MP_TAC MONO_FORALL THEN
    REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(d:real^2) IN inside(path_image
      (linepath(a,b) ++ linepath(b,c) ++ polygonal_path(CONS c p)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `x IN segment(b:real^2,a) UNION segment (b,c)` THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `d:real^2`; `d':real^2`;
                 `linepath(b:real^2,c) ++ polygonal_path(CONS c p)`;
                 `x:real^2`] PARITY_LEMMA) THEN
      SUBGOAL_THEN
       `path_image((linepath(b:real^2,c) ++ polygonal_path(CONS c p)) ++
                   linepath(a,b)) =
        path_image(linepath(a,b) ++ linepath(b:real^2,c) ++
                   polygonal_path(CONS c p))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC PATH_IMAGE_SYM THEN
        REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
        REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
        UNDISCH_TAC `pathfinish(linepath(a,b) ++
          linepath (b,c) ++ polygonal_path(CONS c p)):real^2 = a` THEN
        ASM_REWRITE_TAC[PATHFINISH_JOIN; PATHFINISH_POLYGONAL_PATH];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [W(MP_TAC o PART_MATCH (lhs o rand) SIMPLE_PATH_SYM o snd) THEN
        ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
        ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
        REWRITE_TAC[PATHFINISH_POLYGONAL_PATH] THEN
        ASM_REWRITE_TAC[NOT_CONS_NIL; LAST];
        REWRITE_TAC[PATHSTART_JOIN; PATHSTART_LINEPATH];
        REWRITE_TAC[PATHFINISH_JOIN; PATHFINISH_POLYGONAL_PATH] THEN
        ASM_REWRITE_TAC[NOT_CONS_NIL; LAST];
        MATCH_MP_TAC(SET_RULE
         `x IN s /\ x IN t /\ (!y. y IN s /\ y IN t ==> y = x)
          ==> s INTER t = {x}`) THEN
        SUBST1_TAC(ISPECL[`a:real^2`; `b:real^2`] (CONJUNCT2 SEGMENT_SYM)) THEN
        ASM_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[SEGMENT_CLOSED_OPEN]) THEN ASM SET_TAC[];
        SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH;
                 PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
        ASM_REWRITE_TAC[SET_RULE `s INTER (t UNION u) = {} <=>
                        s INTER t = {} /\ s INTER u = {}`] THEN
        REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        X_GEN_TAC `y:real^2` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        SUBGOAL_THEN `(y:real^2)$1 = (d:real^2)$1` ASSUME_TAC THENL
         [MP_TAC(ISPECL [`d:real^2`; `d':real^2`; `y:real^2`]
             SEGMENT_VERTICAL) THEN
          ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION;
                        IN_INSERT; NOT_IN_EMPTY] THEN
        ASM_CASES_TAC `y:real^2 = b` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        RULE_ASSUM_TAC(SUBS[ISPECL [`a:real^2`; `b:real^2`]
         (CONJUNCT2 SEGMENT_SYM)]) THEN
        ASM_CASES_TAC `y:real^2 = c` THENL [ALL_TAC; ASM SET_TAC[]] THEN
        UNDISCH_THEN `y:real^2 = c` SUBST_ALL_TAC THEN
        MP_TAC(ISPECL [`d:real^2`; `d':real^2`; `c:real^2`]
         SEGMENT_VERTICAL) THEN
        ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION] THEN
        ASM_REAL_ARITH_TAC];
      MP_TAC(ISPECL [`b:real^2`; `c:real^2`; `d:real^2`; `d':real^2`;
                 `polygonal_path(CONS c p) ++ linepath(a:real^2,b)`;
                 `x:real^2`] PARITY_LEMMA) THEN
      SUBGOAL_THEN
       `path_image((polygonal_path (CONS c p) ++ linepath (a,b)) ++
                   linepath(b:real^2,c)) =
        path_image(linepath(a,b) ++ linepath(b:real^2,c) ++
                   polygonal_path(CONS c p))`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                     PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                     PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
                     NOT_CONS_NIL; HD; LAST] THEN
        REWRITE_TAC[UNION_ACI];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [W(MP_TAC o PART_MATCH (lhs o rand) (GSYM SIMPLE_PATH_ASSOC) o snd) THEN
        ANTS_TAC THENL
         [ALL_TAC;
          DISCH_THEN SUBST1_TAC THEN
          W(MP_TAC o PART_MATCH (lhs o rand) SIMPLE_PATH_SYM o snd) THEN
          ANTS_TAC THENL
           [ALL_TAC;
            DISCH_THEN SUBST1_TAC THEN
            W(MP_TAC o PART_MATCH (lhs o rand) (GSYM SIMPLE_PATH_ASSOC) o
              snd) THEN
            ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC]] THEN
        ASM_SIMP_TAC[GSYM SIMPLE_PATH_ASSOC;PATHSTART_JOIN;
                     PATHFINISH_JOIN;
                     PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                     PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
                     NOT_CONS_NIL; HD; LAST];
        REWRITE_TAC[PATHSTART_JOIN; PATHSTART_POLYGONAL_PATH] THEN
        REWRITE_TAC[NOT_CONS_NIL; HD];
        REWRITE_TAC[PATHFINISH_JOIN; PATHFINISH_LINEPATH];
        MATCH_MP_TAC(SET_RULE
         `x IN s /\ x IN t /\ (!y. y IN s /\ y IN t ==> y = x)
          ==> s INTER t = {x}`) THEN
        SUBST1_TAC(ISPECL[`a:real^2`; `b:real^2`] (CONJUNCT2 SEGMENT_SYM)) THEN
        ASM_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[SEGMENT_CLOSED_OPEN]) THEN ASM SET_TAC[];
        ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; NOT_CONS_NIL; HD;
                     PATH_IMAGE_LINEPATH; PATHFINISH_POLYGONAL_PATH; LAST] THEN
        ASM_REWRITE_TAC[SET_RULE `s INTER (t UNION u) = {} <=>
                        s INTER t = {} /\ s INTER u = {}`] THEN
        REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        X_GEN_TAC `y:real^2` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        SUBGOAL_THEN `(y:real^2)$1 = (d:real^2)$1` ASSUME_TAC THENL
         [MP_TAC(ISPECL [`d:real^2`; `d':real^2`; `y:real^2`]
             SEGMENT_VERTICAL) THEN
          ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION;
                        IN_INSERT; NOT_IN_EMPTY] THEN
        ASM_CASES_TAC `y:real^2 = b` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        RULE_ASSUM_TAC(SUBS[ISPECL [`a:real^2`; `b:real^2`]
         (CONJUNCT2 SEGMENT_SYM)]) THEN
        ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
        ASM_CASES_TAC `y:real^2 = a` THENL [ALL_TAC; ASM SET_TAC[]] THEN
        UNDISCH_THEN `y:real^2 = a` SUBST_ALL_TAC THEN
        MP_TAC(ISPECL [`d:real^2`; `d':real^2`; `a:real^2`]
         SEGMENT_VERTICAL) THEN
        ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent{a:real^2,b,c}` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_DEPENDENT_IMP_COLLINEAR_3]; ALL_TAC] THEN
  ASM_CASES_TAC
   `path_image(polygonal_path(CONS c p)) INTER
    convex hull {a,b,c} SUBSET {a:real^2,c}`
  THENL
   [MAP_EVERY EXISTS_TAC [`a:real^2`; `c:real^2`] THEN
    ASM_REWRITE_TAC[MEM] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC INSIDE_SAME_COMPONENT THEN
    EXISTS_TAC `d:real^2` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `segment[d:real^2,y]` THEN
    REWRITE_TAC[CONNECTED_SEGMENT; ENDS_IN_SEGMENT] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
     `convex hull {a:real^2,b,c} DIFF (segment[a,b] UNION segment[b,c])` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_LINEPATH;
        PATHSTART_LINEPATH; PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `t INTER s SUBSET c
        ==> c SUBSET (a UNION b)
            ==> s DIFF (a UNION b) SUBSET UNIV DIFF (a UNION b UNION t)`)) THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_UNION; ENDS_IN_SEGMENT]] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `~(d IN frontier(convex hull {a:real^2,b,c}))` MP_TAC THENL
       [ASM_REWRITE_TAC[frontier; IN_DIFF];
        REWRITE_TAC[FRONTIER_OF_TRIANGLE; SEGMENT_CONVEX_HULL] THEN SET_TAC[]];
      REWRITE_TAC[IN_DIFF; IN_UNION] THEN REPEAT STRIP_TAC THENL
       [UNDISCH_TAC `y IN segment(a:real^2,c)` THEN
        REWRITE_TAC[open_segment; IN_DIFF; SEGMENT_CONVEX_HULL] THEN
        MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s /\ P x ==> x IN t`) THEN
        MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
        UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {b,a,c}`] THEN
        MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `y:real^2` THEN
        MAP_EVERY UNDISCH_TAC
         [`y IN convex hull {a:real^2, b}`; `y IN segment(a:real^2,c)`] THEN
        REWRITE_TAC[open_segment; GSYM SEGMENT_CONVEX_HULL; IN_DIFF] THEN
        REWRITE_TAC[DE_MORGAN_THM; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[IMP_IMP; GSYM BETWEEN_IN_SEGMENT] THEN
        DISCH_THEN(CONJUNCTS_THEN(MP_TAC o
          MATCH_MP BETWEEN_IMP_COLLINEAR)) THEN
        REWRITE_TAC[INSERT_AC; IMP_IMP];
        UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {b,c,a}`] THEN
        MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `y:real^2` THEN
        MAP_EVERY UNDISCH_TAC
         [`y IN convex hull {b:real^2, c}`; `y IN segment(a:real^2,c)`] THEN
        REWRITE_TAC[open_segment; GSYM SEGMENT_CONVEX_HULL; IN_DIFF] THEN
        REWRITE_TAC[DE_MORGAN_THM; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[IMP_IMP; GSYM BETWEEN_IN_SEGMENT] THEN
        DISCH_THEN(CONJUNCTS_THEN(MP_TAC o
          MATCH_MP BETWEEN_IMP_COLLINEAR)) THEN
        REWRITE_TAC[INSERT_AC; IMP_IMP]];
      REWRITE_TAC[SET_RULE
       `s DIFF (t UNION u) = (s DIFF t) INTER (s DIFF u)`] THEN
      MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`convex hull {a:real^2,b,c}`; `convex hull{a:real^2,b}`]
          FACE_OF_STILLCONVEX) THEN
        REWRITE_TAC[CONVEX_CONVEX_HULL] THEN MATCH_MP_TAC(TAUT
         `p ==> (p <=> q /\ r /\ s) ==> r`) THEN
        ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
        EXISTS_TAC `{a:real^2,b}` THEN SET_TAC[];
        MP_TAC(ISPECL [`convex hull {a:real^2,b,c}`; `convex hull{b:real^2,c}`]
          FACE_OF_STILLCONVEX) THEN
        REWRITE_TAC[CONVEX_CONVEX_HULL] THEN MATCH_MP_TAC(TAUT
         `p ==> (p <=> q /\ r /\ s) ==> r`) THEN
        ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
        EXISTS_TAC `{b:real^2,c}` THEN SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?n:real^2.
        ~(n = vec 0) /\ orthogonal n (c - a) /\
        &0 < n dot (c - b)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `?n:real^2. ~(n = vec 0) /\ orthogonal n (c - a)`
    STRIP_ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[ORTHOGONAL_SYM] THEN
      MATCH_MP_TAC ORTHOGONAL_TO_VECTOR_EXISTS THEN
      REWRITE_TAC[DIMINDEX_2; LE_REFL];
      ALL_TAC] THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH
     `&0 < n dot (c - b) \/ &0 < --(n dot (c - b)) \/
      (n:real^2) dot (c - b) = &0`)
    THENL
     [EXISTS_TAC `n:real^2` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `--n:real^2` THEN ASM_REWRITE_TAC[DOT_LNEG] THEN
      ASM_REWRITE_TAC[VECTOR_NEG_EQ_0; ORTHOGONAL_LNEG];
      UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN
      ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {a,c,b}`] THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      ONCE_REWRITE_TAC[COLLINEAR_3] THEN
      MATCH_MP_TAC ORTHOGONAL_TO_ORTHOGONAL_2D THEN
      EXISTS_TAC `n:real^2` THEN
      ONCE_REWRITE_TAC[GSYM ORTHOGONAL_RNEG] THEN
      ASM_REWRITE_TAC[VECTOR_NEG_SUB] THEN
      ASM_REWRITE_TAC[orthogonal]];
    ALL_TAC] THEN
  SUBGOAL_THEN `n dot (a - b:real^2) = n dot (c - b)` ASSUME_TAC THENL
   [REWRITE_TAC[DOT_RSUB; real_sub; REAL_EQ_ADD_RCANCEL] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x = y <=> y - x = &0`] THEN
    ASM_REWRITE_TAC[GSYM DOT_RSUB; GSYM orthogonal];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. y IN convex hull {a,b,c} /\ ~(y = b) ==> &0 < n dot (y - b)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_3_ALT; FORALL_IN_GSPEC; IMP_CONJ] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(a + u % (b - a) + v % (c - a)) - b =
      (&1 - u - v) % (a - b) + v % (c - b)`] THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
    MAP_EVERY X_GEN_TAC [`r:real`; `s:real`] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `(&1 - u - v) * x + v * x = (&1 - u) * x`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `r = &1 /\ s = &0` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    UNDISCH_TAC `~(a + r % (b - a) + s % (c - a):real^2 = b)` THEN
    ASM_REWRITE_TAC[REAL_LT_REFL; REAL_SUB_LT] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. y IN convex hull {a,b,c} ==> &0 <= n dot (y - b)`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `y:real^2 = b` THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; DOT_RZERO; REAL_LE_REFL] THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. y IN convex hull {a,b,c} ==> n dot (y - b) <= n dot (c - b)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_3_ALT; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(a + u % (b - a) + v % (c - a)) - b =
      (&1 - u - v) % (a - b) + v % (c - b)`] THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_ARITH
     `(&1 - u - v) * x + v * x <= x <=> &0 <= u * x`] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^2. n dot (x - b)`;
  `path_image (polygonal_path(CONS c p)) INTER convex hull {a:real^2,b,c}`]
        CONTINUOUS_ATTAINS_INF) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_INTER THEN
      SIMP_TAC[COMPACT_PATH_IMAGE; PATH_POLYGONAL_PATH] THEN
      SIMP_TAC[COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT;
               FINITE_INSERT; FINITE_EMPTY];
      ASM SET_TAC[];
      SUBGOAL_THEN
       `(\x:real^2. n dot (x - b)) = (\x. n dot x) o (\x. x - b)`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      REWRITE_TAC[CONTINUOUS_ON_LIFT_DOT] THEN
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `?mx:real^2.
      ~(mx = a) /\ ~(mx = c) /\
      mx IN path_image(polygonal_path(CONS c p)) INTER convex hull {a, b, c} /\
      (!y. y IN
           path_image(polygonal_path(CONS c p)) INTER convex hull {a, b, c}
           ==> n dot (mx - b) <= n dot (y - b))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `mx:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `n dot (mx - b:real^2) <= n dot (c - b)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN STRIP_TAC THENL
     [EXISTS_TAC `mx:real^2` THEN ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
    UNDISCH_TAC `~(path_image(polygonal_path(CONS c p)) INTER
                   convex hull {a, b, c} SUBSET {a:real^2, c})` THEN
    REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP; IN_INSERT; NOT_IN_EMPTY] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `my:real^2` THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `n dot (mx - b:real^2)` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    FIRST_X_ASSUM(CHOOSE_THEN (K ALL_TAC))] THEN
  ABBREV_TAC `m = (n:real^2) dot (mx - b)` THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST_ALL_TAC] THEN
    UNDISCH_TAC
     `segment[b:real^2,c] INTER path_image (polygonal_path (CONS c p))
      SUBSET {c}` THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `b:real^2`) THEN
    ASM_REWRITE_TAC[IN_SING; ENDS_IN_SEGMENT] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?z:real^2. MEM z p /\
               z IN (convex hull {a,b,c} DIFF {a,c}) /\
               n dot (z - b) = m`
  STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`b:real^2`; `z:real^2`] THEN
    ASM_REWRITE_TAC[MEM] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_REFL]; DISCH_TAC] THEN
    X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC INSIDE_SAME_COMPONENT THEN
    EXISTS_TAC `d:real^2` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(z:real^2 = a) /\ ~(z = c)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(z:real^2) IN path_image(polygonal_path(CONS c p)) /\
      (z:real^2) IN path_image(polygonal_path p)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC
       (REWRITE_RULE[SUBSET] VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
      ASM_REWRITE_TAC[IN_SET_OF_LIST; MEM];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(z IN segment[a:real^2,b]) /\ ~(z IN segment[b,c])`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~collinear{b:real^2,a,z} /\ ~collinear{b,c,z}`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL] THEN
      MATCH_MP_TAC(SET_RULE
       `!c. x IN c /\ ~(x IN (a INTER c)) /\ ~(x IN (b INTER c))
            ==> ~(x IN a) /\ ~(x IN b)`) THEN
      EXISTS_TAC `convex hull {a:real^2,b,c}` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM AFFINE_INDEPENDENT_CONVEX_AFFINE_HULL;
                   INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT] THEN
      ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
      ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `segment(b:real^2,z) INTER segment[a,b] = {} /\
      segment(b,z) INTER segment[b,c] = {}`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      CONJ_TAC THEN X_GEN_TAC `v:real^2` THEN STRIP_TAC THENL
       [UNDISCH_TAC `~collinear{b:real^2,a,z}`;
        UNDISCH_TAC `~collinear{b:real^2,c,z}`] THEN
      REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {b,a,c}`] THEN
      MATCH_MP_TAC COLLINEAR_3_TRANS THEN
      EXISTS_TAC `v:real^2` THEN
      UNDISCH_TAC `v IN segment(b:real^2,z)` THEN
      REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
      REWRITE_TAC[DE_MORGAN_THM; IMP_CONJ] THENL
       [UNDISCH_TAC `v IN segment[a:real^2,b]`;
        UNDISCH_TAC `v IN segment[b:real^2,c]`] THEN
      ONCE_REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT] THEN
      DISCH_THEN(CONJUNCTS_THEN(MP_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR)) THEN
      REWRITE_TAC[INSERT_AC] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[b:real^2,z] SUBSET convex hull {a,b,c}`
    ASSUME_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[CONVEX_CONVEX_HULL; INSERT_SUBSET; EMPTY_SUBSET] THEN
      SIMP_TAC[HULL_INC; IN_INSERT] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment(b:real^2,z) SUBSET convex hull {a,b,c}`
    ASSUME_TAC THENL
     [REWRITE_TAC[open_segment] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `segment(b:real^2,z) INTER path_image(polygonal_path(CONS c p)) = {}`
    ASSUME_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      X_GEN_TAC `v:real^2` THEN STRIP_TAC THEN
      SUBGOAL_THEN `m <= n dot (v - b:real^2)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_NOT_LE] THEN
      UNDISCH_TAC `v IN segment(b:real^2,z)` THEN REWRITE_TAC[IN_SEGMENT] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[DOT_RMUL; VECTOR_ARITH
       `((&1 - t) % a + t % b) - a:real^N = t % (b - a)`] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `t * m < m <=> &0 < m * (&1 - t)`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_SUB_LT];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment(b:real^2,z) SUBSET interior(convex hull {a,b,c})`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
       `(convex hull {a:real^2,b,c}) DIFF frontier(convex hull {a,b,c})` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[frontier] THEN MATCH_MP_TAC(SET_RULE
         `s SUBSET u ==> s DIFF (u DIFF t) SUBSET t`) THEN
        REWRITE_TAC[CLOSURE_SUBSET]] THEN
      REWRITE_TAC[FRONTIER_OF_TRIANGLE] THEN MATCH_MP_TAC(SET_RULE
       `s INTER a = {} /\ s INTER b = {} /\ s INTER c = {} /\ s SUBSET u
        ==> s SUBSET u DIFF (a UNION b UNION c)`) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      X_GEN_TAC `v:real^2` THEN REWRITE_TAC[IN_SEGMENT] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) MP_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `t:real` THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(MP_TAC o AP_TERM `\x:real^2. n dot (x - b)`) THEN
      REWRITE_TAC[VECTOR_ARITH
         `((&1 - u) % c + u % a) - b =
          (&1 - u) % (c - b) + u % (a - b)`] THEN
      ASM_REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_ADD_LID; VECTOR_MUL_RZERO] THEN
      ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN MATCH_MP_TAC(REAL_ARITH
       `&0 < m * (&1 - t) /\ m <= x ==> ~((&1 - s) * x + s * x = t * m)`) THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_SUB_LT] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      SIMP_TAC[IN_INTER; IN_INSERT; HULL_INC] THEN MATCH_MP_TAC
       (REWRITE_RULE[SUBSET] VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
      REWRITE_TAC[set_of_list; IN_INSERT];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?y:real^2. y IN segment(b,z) /\ y IN interior(convex hull {a',b,c'})`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[INTER; GSYM(ASSUME
       `interior(convex hull {a, b, c}) INTER {x:real^2 | x$2 - b$2 < e} =
        interior(convex hull {a', b, c'})`)] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC(SET_RULE
       `(?y. y IN s /\ P y) /\ s SUBSET t
        ==> ?y. y IN s /\ y IN t /\ P y`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC
       `b + min (&1 / &2) (e / &2 / norm(z - b)) % (z - b):real^2` THEN
      CONJ_TAC THENL
       [EXISTS_TAC `min (&1 / &2) (e / &2 / norm (z - b:real^2))` THEN
        REPEAT CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC; VECTOR_ARITH_TAC] THEN
        REWRITE_TAC[REAL_LT_MIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ];
        REWRITE_TAC[VECTOR_ADD_COMPONENT; REAL_ADD_SUB] THEN
        MATCH_MP_TAC(REAL_ARITH
         `abs(x$2) <= norm x /\ norm x <= e / &2 /\ &0 < e ==> x$2 < e`) THEN
        SIMP_TAC[COMPONENT_LE_NORM; DIMINDEX_2; ARITH] THEN
        ASM_REWRITE_TAC[NORM_MUL] THEN
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs(min (&1 / &2) x) <= x`) THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_DIV THEN
        ASM_REWRITE_TAC[REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ]];
      ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC `y:real^2` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[connected_component] THEN
      EXISTS_TAC `interior(convex hull {a':real^2,b,c'})` THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERIOR; CONVEX_CONVEX_HULL] THEN
      SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHSTART_LINEPATH;
         PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF (a UNION b UNION c) <=>
        s INTER a = {} /\ s INTER b = {} /\ s INTER c = {}`] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `!t. s SUBSET t /\ t INTER u = {} ==> s INTER u = {}`) THEN
        EXISTS_TAC `interior(convex hull {a:real^2,b,c})` THEN
        ASM_SIMP_TAC[SUBSET_INTERIOR] THEN
        MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `c:real^2`]
         FRONTIER_OF_TRIANGLE) THEN
        REWRITE_TAC[PATH_IMAGE_LINEPATH; frontier] THEN
        MATCH_MP_TAC(SET_RULE
         `!s. i SUBSET s /\ s SUBSET c
          ==> c DIFF i = a UNION b ==> i INTER a = {}`) THEN
        EXISTS_TAC `convex hull {a:real^2,b,c}` THEN
        REWRITE_TAC[INTERIOR_SUBSET; CLOSURE_SUBSET];
        MATCH_MP_TAC(SET_RULE
         `!t. s SUBSET t /\ t INTER u = {} ==> s INTER u = {}`) THEN
        EXISTS_TAC `interior(convex hull {a:real^2,b,c})` THEN
        ASM_SIMP_TAC[SUBSET_INTERIOR] THEN
        MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `c:real^2`]
         FRONTIER_OF_TRIANGLE) THEN
        REWRITE_TAC[PATH_IMAGE_LINEPATH; frontier] THEN
        MATCH_MP_TAC(SET_RULE
         `!s. i SUBSET s /\ s SUBSET c
          ==> c DIFF i = a UNION b UNION d ==> i INTER b = {}`) THEN
        EXISTS_TAC `convex hull {a:real^2,b,c}` THEN
        REWRITE_TAC[INTERIOR_SUBSET; CLOSURE_SUBSET];
        MATCH_MP_TAC(SET_RULE
         `!t. s SUBSET t /\ u INTER t = {} ==> s INTER u = {}`) THEN
        EXISTS_TAC `{x | (x:real^2)$2 - (b:real^2)$2 < e}` THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[SET_RULE `s INTER t = {} <=> s SUBSET (UNIV DIFF t)`] THEN
        REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; REAL_NOT_LT; IN_UNIV] THEN
        MP_TAC(ISPEC `CONS (c:real^2) p`
                PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL) THEN
        REWRITE_TAC[NOT_CONS_NIL] THEN
        MATCH_MP_TAC(SET_RULE
         `t SUBSET {x | P x} ==> s SUBSET t ==> !x. x IN s ==> P x`) THEN
        REWRITE_TAC[REAL_ARITH `e <= x - b <=> x >= b + e`] THEN
        SIMP_TAC[SUBSET_HULL; CONVEX_HALFSPACE_COMPONENT_GE] THEN
        REWRITE_TAC[set_of_list; REAL_ARITH `x >= b + e <=> e <= x - b`] THEN
        ASM_REWRITE_TAC[INSERT_SUBSET; IN_ELIM_THM] THEN
        ASM_REWRITE_TAC[SUBSET; IN_SET_OF_LIST; IN_ELIM_THM]];
      REWRITE_TAC[connected_component] THEN
      EXISTS_TAC `segment(b:real^2,z)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CONNECTED_SEGMENT] THEN
      SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHSTART_LINEPATH;
         PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN ASM SET_TAC[]]] THEN
  SUBGOAL_THEN
   `?u v:real^2.
        MEM u (CONS c p) /\ MEM v (CONS c p) /\
        mx IN segment[u,v] /\
        segment[u,v] SUBSET path_image(polygonal_path(CONS c p)) /\
        ~(a IN segment[u,v] /\ c IN segment[u,v]) /\
        n dot (u - b) <= m`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`CONS (c:real^2) p`; `mx:real^2`]
      PATH_IMAGE_POLYGONAL_PATH_SUBSET_SEGMENTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LENGTH; ARITH_RULE `3 <= SUC n <=> 2 <= n`] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN
    ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
    ASM_REWRITE_TAC[NOT_CONS_NIL; LAST; HD] THEN STRIP_TAC THEN
    SUBGOAL_THEN `n dot (u - b) <= m \/ n dot (v - b:real^2) <= m`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT; GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
      UNDISCH_TAC `n dot (mx - b:real^2) = m` THEN
      UNDISCH_TAC `(mx:real^2) IN segment[u,v]` THEN
      REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_ARITH
       `((&1 - u) % x + u % y) - a:real^N =
        (&1 - u) % (x - a) + u % (y - a)`] THEN
      MATCH_MP_TAC(REAL_ARITH `--x < --m ==> ~(x = m)`) THEN
      REWRITE_TAC[GSYM DOT_LNEG] THEN REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
      MATCH_MP_TAC REAL_CONVEX_BOUND_LT THEN
      ASM_REWRITE_TAC[DOT_LNEG; REAL_LT_NEG2] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`u:real^2`; `v:real^2`] THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[CONJ_SYM] THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`v:real^2`; `u:real^2`] THEN
      ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[CONJ_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `n dot (u - b:real^2) < n dot (c - b)` THENL
   [SUBGOAL_THEN `~(u:real^2 = a) /\ ~(u = c)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
    UNDISCH_TAC `MEM (u:real^2) (CONS c p)` THEN
    ASM_REWRITE_TAC[MEM] THEN DISCH_TAC THEN EXISTS_TAC `u:real^2` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_CASES_TAC `mx:real^2 = u` THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN CONJ_TAC THENL
     [DISCH_TAC THEN ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET]
        VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
      ASM_REWRITE_TAC[IN_SET_OF_LIST; MEM];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`segment(u:real^2,mx)`; `convex hull {a:real^2,b,c}`]
        CONNECTED_INTER_FRONTIER) THEN
    REWRITE_TAC[CONNECTED_SEGMENT] THEN MATCH_MP_TAC(SET_RULE
     `(s SUBSET c ==> u IN c) /\ s INTER f = {} /\ ~(s INTER c = {})
      ==> (~(s INTER c = {}) /\ ~(s DIFF c = {}) ==> ~(s INTER f = {}))
          ==> u IN c`) THEN
    REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `closure(segment(u:real^2,mx)) SUBSET convex hull {a,b,c}`
      MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
        SIMP_TAC[FINITE_IMP_COMPACT; FINITE_INSERT; FINITE_EMPTY];
        ASM_REWRITE_TAC[SUBSET; CLOSURE_SEGMENT] THEN
        DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT]];
      REWRITE_TAC[FRONTIER_OF_TRIANGLE] THEN
      MATCH_MP_TAC(SET_RULE
       `!a b c t u.
                s SUBSET t /\ t SUBSET u /\
                a IN ca /\ c IN ca /\
                ab INTER u SUBSET {a,b} /\ bc INTER u SUBSET {c} /\
                ~(b IN u) /\ s INTER ca = {}
                ==> s INTER (ab UNION bc UNION ca) = {}`) THEN
      MAP_EVERY EXISTS_TAC
       [`a:real^2`; `b:real^2`; `c:real^2`; `segment[u:real^2,v]`;
        `path_image(polygonal_path(CONS (c:real^2) p))`] THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT; SUBSET_SEGMENT] THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `CONS (c:real^2) p`
                  PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL) THEN
        REWRITE_TAC[NOT_CONS_NIL] THEN MATCH_MP_TAC(SET_RULE
         `~(x IN t) ==> s SUBSET t ==> ~(x IN s)`) THEN
        MATCH_MP_TAC(SET_RULE
         `!t. ~(b IN t) /\ s SUBSET t ==> ~(b IN s)`) THEN
        EXISTS_TAC `{x:real^2 | (x:real^2)$2 >= (b:real^2)$2 + e}` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; real_ge; REAL_NOT_LE; REAL_LT_ADDR] THEN
        MATCH_MP_TAC HULL_MINIMAL THEN
        REWRITE_TAC[GSYM real_ge; CONVEX_HALFSPACE_COMPONENT_GE] THEN
        REWRITE_TAC[SUBSET; set_of_list; FORALL_IN_INSERT; IN_ELIM_THM] THEN
        ASM_REWRITE_TAC[IN_SET_OF_LIST; REAL_ARITH
         `x >= b + e <=> e <= x - b`];
        REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_SEGMENT] THEN
        DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
        DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `t:real` THEN
        REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(MP_TAC o AP_TERM `\x:real^2. n dot (x - b)`) THEN
        REWRITE_TAC[VECTOR_ARITH
           `((&1 - u) % c + u % a) - b =
            (&1 - u) % (c - b) + u % (a - b)`] THEN
        ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN MATCH_MP_TAC(REAL_ARITH
         `(&1 - t) * a < (&1 - t) * m /\ t * b <= t * m
          ==> ~((&1 - s) * m + s * m = (&1 - t) * a + t * b)`) THEN
        ASM_SIMP_TAC[REAL_LT_LMUL; REAL_SUB_LT] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC] THEN
        SIMP_TAC[IN_INTER; HULL_INC; IN_INSERT] THEN
        MATCH_MP_TAC(REWRITE_RULE[SUBSET]
          VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
        REWRITE_TAC[set_of_list; IN_INSERT]];
      ALL_TAC] THEN
    ASM_CASES_TAC `mx IN interior(convex hull {a:real^2,b,c})` THENL
     [UNDISCH_TAC `mx IN interior(convex hull {a:real^2,b,c})` THEN
      REWRITE_TAC[IN_INTERIOR_CBALL; SUBSET; IN_CBALL] THEN
      DISCH_THEN(X_CHOOSE_THEN `ee:real` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[IN_SEGMENT] THEN
      REWRITE_TAC[MESON[]
       `(?x. (?u. P u /\ Q u /\ x = f u) /\ R x) <=>
        (?u. P u /\ Q u /\ R(f u))`] THEN
      EXISTS_TAC `min (&1 / &2) (ee / norm(u - mx:real^2))` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < min (&1 / &2) x`) THEN
        ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ];
        REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[dist; VECTOR_ARITH
         `a - ((&1 - u) % a + u % b):real^N = u % (a - b)`] THEN
        ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LE_RDIV_EQ; NORM_POS_LT;
                     VECTOR_SUB_EQ] THEN
        REWRITE_TAC[NORM_SUB] THEN MATCH_MP_TAC(REAL_ARITH
         `&0 < x ==> abs(min (&1 / &2) x) <= x`) THEN
        ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ]];
      ALL_TAC] THEN
    MP_TAC(ISPEC `{a:real^2,b,c}` AFFINE_INDEPENDENT_SPAN_EQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DIMINDEX_2] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
    REWRITE_TAC[AFFINE_HULL_3; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^2`) THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:real`; `s:real`; `t:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `mx IN convex hull {a:real^2,b,c}` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN REWRITE_TAC[CONVEX_HULL_3] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    REWRITE_TAC[IN_INTER; EXISTS_IN_GSPEC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`rx:real`; `sx:real`; `tx:real`] THEN
    ASM_CASES_TAC `rx = &0` THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ADD_LID] THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN STRIP_TAC THEN
      UNDISCH_TAC
        `segment[b:real^2,c] INTER path_image(polygonal_path(CONS c p))
         SUBSET {c}` THEN
      REWRITE_TAC[SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `mx:real^2`) THEN
      MATCH_MP_TAC(TAUT `~q /\ p ==> (p ==> q) ==> r`) THEN
      REWRITE_TAC[IN_SING] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_INTER; SEGMENT_CONVEX_HULL] THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      REWRITE_TAC[CONVEX_HULL_2; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `rx = &1` THENL
     [ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      SUBGOAL_THEN `sx = &0 /\ tx = &0` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_RID];
      ALL_TAC] THEN
    ASM_CASES_TAC `tx = &0` THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ADD_RID] THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN STRIP_TAC THEN
      UNDISCH_TAC
        `segment[a:real^2,b] INTER path_image(polygonal_path(CONS c p))
         SUBSET {a,b}` THEN
      REWRITE_TAC[SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `mx:real^2`) THEN
      MATCH_MP_TAC(TAUT `~q /\ p ==> (p ==> q) ==> r`) THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST_ALL_TAC] THEN
        UNDISCH_TAC `n dot (b - b:real^2) = m` THEN
        REWRITE_TAC[VECTOR_SUB_REFL; DOT_RZERO] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[IN_INTER; SEGMENT_CONVEX_HULL] THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      REWRITE_TAC[CONVEX_HULL_2; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `tx = &1` THENL
     [ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      SUBGOAL_THEN `sx = &0 /\ rx = &0` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
     ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID];
     ALL_TAC] THEN
    ASM_CASES_TAC `sx = &1` THENL
     [ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      SUBGOAL_THEN `rx = &0 /\ tx = &0` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
     ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID;
                     VECTOR_ADD_RID] THEN
     DISCH_THEN SUBST_ALL_TAC THEN
     UNDISCH_TAC `n dot (b - b:real^2) = m` THEN
     REWRITE_TAC[VECTOR_SUB_REFL; DOT_RZERO] THEN
     ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    ASM_CASES_TAC `sx = &0` THENL
     [ALL_TAC;
      STRIP_TAC THEN
      UNDISCH_TAC `~(mx IN interior(convex hull {a:real^2, b, c}))` THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`rx:real`; `sx:real`; `tx:real`] THEN
      REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
    UNDISCH_THEN `sx = &0` SUBST_ALL_TAC THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; REAL_LE_REFL] THEN
    REWRITE_TAC[REAL_ADD_LID] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `&0 < rx /\ rx < &1 /\ &0 < tx /\ tx < &1`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_SEGMENT] THEN
    SUBGOAL_THEN
     `?q. q * (rx - r) <= rx /\
          q * (tx - t) <= tx /\
          &0 < q /\ q < &1`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC
       `min (&1 / &2)
            (min (if rx:real = r then &1 / &2 else rx / abs(rx - r))
                 (if tx:real = t then &1 / &2 else tx / abs(tx - t)))` THEN
      REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LT] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
       [ASM_CASES_TAC `r:real = rx` THENL
         [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO]; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN
        REWRITE_TAC[REAL_ABS_MUL] THEN
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH
         `~(x = y) ==> &0 < abs(x - y)`] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= a /\ &0 <= x /\ &0 <= b ==> abs(min a (min x b)) <= x`) THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_ABS_POS] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        ASM_CASES_TAC `t:real = tx` THENL
         [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO]; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN
        REWRITE_TAC[REAL_ABS_MUL] THEN
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH
         `~(x = y) ==> &0 < abs(x - y)`] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= a /\ &0 <= x /\ &0 <= b ==> abs(min a (min b x)) <= x`) THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_ABS_POS] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`(&1 - q) * rx + q * r`;
      `q * s:real`;
      `(&1 - q) * tx + q * t:real`] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [ALL_TAC;
      EXISTS_TAC `q:real` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `((&1 - q) * rx + q * r) +
      q * s +
      ((&1 - q) * tx + q * t) =
      (rx + tx) + q * ((r + s + t) - (rx + tx))`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `&0 <= (&1 - q) * r + q * s <=> q * (r - s) <= r`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `n dot (u - b:real^2) < n dot (c - b)` THEN
    ASM_REWRITE_TAC[VECTOR_ARITH
     `(r % a + s % b + t % c) - b =
      r % (a - b) + t % (c - b) + ((r + s + t) - &1) % b`] THEN
    REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
    REWRITE_TAC[REAL_ARITH
     `r * x + s * x < x <=> &0 < (&1 - r - s) * x`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n dot (u - b) = m /\ n dot (c - b) = m` MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `!mx. n dot (u - b) <= m /\
           ~(n dot (u - b) < n dot (c - b)) /\
           n dot (mx - b) = m /\
           n dot (mx - b) <= n dot (c - b)
           ==> n dot (u - b) = m /\ n dot (c - b) = m`) THEN
    EXISTS_TAC `mx:real^2` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[IN_INTER; HULL_INC; IN_INSERT] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET]
     VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
    REWRITE_TAC[set_of_list; IN_INSERT];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)) THEN
  MAP_EVERY (C UNDISCH_THEN (K ALL_TAC)) [`m <= m`; `~(m < m)`] THEN
  SUBGOAL_THEN
   `collinear {a:real^2,mx,c} /\ collinear {a,u,c}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!y:real^2. n dot (y - b) = m ==> collinear {a,y,c}`
     (fun th -> CONJ_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]) THEN
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {a,c,b}`] THEN
    ONCE_REWRITE_TAC[COLLINEAR_3] THEN
    MATCH_MP_TAC ORTHOGONAL_TO_ORTHOGONAL_2D THEN
    EXISTS_TAC `n:real^2` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM ORTHOGONAL_RNEG] THEN
    ASM_REWRITE_TAC[VECTOR_NEG_SUB] THEN
    MAP_EVERY UNDISCH_TAC
     [`n dot (y - b:real^2) = m`; `n dot (c - b:real^2) = m`] THEN
    REWRITE_TAC[orthogonal; DOT_RSUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `mx:real^2 = u` THENL
   [UNDISCH_THEN `mx:real^2 = u` SUBST_ALL_TAC THEN
    UNDISCH_TAC `MEM (u:real^2) (CONS c p)` THEN
    ASM_REWRITE_TAC[MEM] THEN DISCH_TAC THEN EXISTS_TAC `u:real^2` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `mx:real^2 = v` THENL
   [UNDISCH_THEN `mx:real^2 = v` SUBST_ALL_TAC THEN
    UNDISCH_TAC `MEM (v:real^2) (CONS c p)` THEN
    ASM_REWRITE_TAC[MEM] THEN DISCH_TAC THEN EXISTS_TAC `v:real^2` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `collinear {a:real^2,c,mx,u}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COLLINEAR_4_3] THEN
    ONCE_REWRITE_TAC[SET_RULE `{a,c,b} = {a,b,c}`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `collinear {a:real^2,u,v}` ASSUME_TAC THENL
   [MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `mx:real^2` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COLLINEAR_SUBSET THEN
      EXISTS_TAC `{a:real^2,c,mx,u}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN
      ASM_REWRITE_TAC[BETWEEN_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `collinear {c:real^2,u,v}` ASSUME_TAC THENL
   [MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `mx:real^2` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COLLINEAR_SUBSET THEN
      EXISTS_TAC `{a:real^2,c,mx,u}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN
      ASM_REWRITE_TAC[BETWEEN_IN_SEGMENT]];
    ALL_TAC] THEN
  ASM_CASES_TAC `u:real^2 = v` THENL
   [UNDISCH_THEN `u:real^2 = v` SUBST_ALL_TAC THEN
    ASM_MESON_TAC[SEGMENT_REFL; IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `collinear {a:real^2,v,c}` ASSUME_TAC THENL
   [MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `u:real^2` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INSERT_AC]) THEN
    ASM_REWRITE_TAC[INSERT_AC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `c:real^2`; `u:real^2`; `v:real^2`;
                 `mx:real^2`] between_lemma) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (lhs o rand) COLLINEAR_TRIPLES o snd) THEN
      ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
      DISCH_THEN SUBST1_TAC THEN
      ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {a,c,b}`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
      MP_TAC(ISPECL [`{a:real^2,b,c}`; `{a:real^2,c}`]
                AFFINE_INDEPENDENT_CONVEX_AFFINE_HULL) THEN
      ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      ANTS_TAC THENL [SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      ASM_SIMP_TAC[GSYM COLLINEAR_3_AFFINE_HULL] THEN
      MATCH_MP_TAC COLLINEAR_SUBSET THEN
      EXISTS_TAC `{a:real^2,c,mx,u}` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `u:real^2` THEN
    MP_TAC(ASSUME `u IN segment(a:real^2,c)`) THEN
    REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
    UNDISCH_TAC `MEM (u:real^2) (CONS c p)` THEN
    ASM_REWRITE_TAC[MEM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(u:real^2) IN segment[a,c]` THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SPEC_TAC(`u:real^2`,`u:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    EXISTS_TAC `v:real^2` THEN
    MP_TAC(ASSUME `v IN segment(a:real^2,c)`) THEN
    REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
    UNDISCH_TAC `MEM (v:real^2) (CONS c p)` THEN
    ASM_REWRITE_TAC[MEM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(v:real^2) IN segment[a,c]` THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      SPEC_TAC(`v:real^2`,`v:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      UNDISCH_TAC `collinear {a:real^2, v, c}` THEN
      ONCE_REWRITE_TAC[SET_RULE `{a,v,c} = {a,c,v}`] THEN
      ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL] THEN
      REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_ARITH
       `(u % a + v % c) - b:real^N =
        u % (a - b) + v % (c - b) + ((u + v) - &1) % b`] THEN
      ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_SUB_REFL] THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; GSYM REAL_ADD_RDISTRIB;
                      REAL_MUL_LID]];
    UNDISCH_TAC `segment[a:real^2,c] SUBSET segment[u,v]` THEN
    ASM_REWRITE_TAC[SUBSET_SEGMENT]]);;

(* ------------------------------------------------------------------------- *)
(* Hence the final Pick theorem by induction on number of polygon segments.  *)
(* ------------------------------------------------------------------------- *)

let PICK = prove
 (`!p:(real^2)list.
        (!x. MEM x p ==> integral_vector x) /\
        simple_path (polygonal_path p) /\
        pathfinish (polygonal_path p) = pathstart (polygonal_path p)
        ==> measure(inside(path_image(polygonal_path p))) =
                &(CARD {x | x IN inside(path_image(polygonal_path p)) /\
                            integral_vector x}) +
                &(CARD {x | x IN path_image(polygonal_path p) /\
                            integral_vector x}) / &2 - &1`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH(p:(real^2)list)` THEN DISJ_CASES_TAC
  (ARITH_RULE `LENGTH(p:(real^2)list) <= 4 \/ 5 <= LENGTH p`) THENL
   [UNDISCH_TAC `LENGTH(p:(real^2)list) <= 4` THEN
    POP_ASSUM(K ALL_TAC) THEN SPEC_TAC(`p:(real^2)list`,`p:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[polygonal_path; SIMPLE_PATH_LINEPATH_EQ] THEN
    X_GEN_TAC `a:real^2` THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[polygonal_path; SIMPLE_PATH_LINEPATH_EQ] THEN
    X_GEN_TAC `b:real^2` THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC[polygonal_path; SIMPLE_PATH_LINEPATH_EQ;
                  PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `c:real^2` THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [REPLICATE_TAC 4 (DISCH_THEN(K ALL_TAC)) THEN
      REWRITE_TAC[polygonal_path] THEN
      REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH] THEN
      ASM_CASES_TAC `c:real^2 = a` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
                   PATHFINISH_LINEPATH] THEN
      REWRITE_TAC[ARC_LINEPATH_EQ] THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
      SUBST1_TAC(ISPECL [`b:real^2`; `a:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
      REWRITE_TAC[INTER_IDEMPOT] THEN DISCH_THEN(MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET)) THEN
      ASM_REWRITE_TAC[FINITE_SEGMENT; FINITE_INSERT; FINITE_EMPTY];
      ALL_TAC] THEN
    X_GEN_TAC `d:real^2` THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [REPLICATE_TAC 5 (DISCH_THEN(K ALL_TAC));
      REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC(SUC(SUC(SUC(SUC n)))) <= 4)`]] THEN
    REWRITE_TAC[polygonal_path; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    REWRITE_TAC[GSYM IN_SET_OF_LIST; set_of_list] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ASM_CASES_TAC `d:real^2 = a` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATH_IMAGE_JOIN; PATHSTART_LINEPATH;
      ARC_JOIN_EQ; PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
    REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN REWRITE_TAC[INSIDE_OF_TRIANGLE] THEN
    REWRITE_TAC[GSYM FRONTIER_OF_TRIANGLE] THEN
    SIMP_TAC[MEASURE_INTERIOR; NEGLIGIBLE_CONVEX_FRONTIER;
             CONVEX_CONVEX_HULL; FINITE_IMP_BOUNDED_CONVEX_HULL;
             FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_SIMP_TAC[PICK_TRIANGLE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ARC_LINEPATH_EQ] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[UNION_OVER_INTER] THEN
    REWRITE_TAC[UNION_SUBSET] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `segment[b:real^2,c] INTER segment [c,a] = segment[b,c] \/
      segment[b,c] INTER segment [c,a] = segment[c,a] \/
      segment[a,b] INTER segment [b,c] = segment[b,c]`
    (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [REWRITE_TAC[SET_RULE `s INTER t = s <=> s SUBSET t`;
                  SET_RULE `s INTER t = t <=> t SUBSET s`] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COLLINEAR_BETWEEN_CASES]) THEN
      REWRITE_TAC[SUBSET_SEGMENT; BETWEEN_IN_SEGMENT; ENDS_IN_SEGMENT] THEN
      REWRITE_TAC[SEGMENT_SYM; DISJ_ACI];
      UNDISCH_TAC `segment [b,c] SUBSET {c:real^2}`;
      UNDISCH_TAC `segment [c,a] SUBSET {c:real^2}`;
      UNDISCH_TAC `segment [b,c] SUBSET {a:real^2, b}`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[FINITE_SEGMENT; FINITE_INSERT; FINITE_EMPTY];
    STRIP_TAC] THEN
  MP_TAC(ISPEC `p:(real^2)list` POLYGON_CHOP_IN_TWO) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`;`b:real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?p':(real^2)list.
        HD p' = a /\
        LENGTH p' = LENGTH p /\
        path_image(polygonal_path p') = path_image(polygonal_path p) /\
        set_of_list p' = set_of_list p /\
        simple_path(polygonal_path p') /\
        pathfinish(polygonal_path p') = pathstart(polygonal_path p')`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC ROTATE_LIST_TO_FRONT_0 THEN
    EXISTS_TAC `p:(real^2)list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `5 <= p ==> 3 <= p`] THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
      GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[LENGTH] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`pathfinish(polygonal_path(p:(real^2)list)) =
       pathstart(polygonal_path p)`;
      `5 <= LENGTH(p:(real^2)list)`] THEN
    ASM_CASES_TAC `p:(real^2)list = []` THEN
    ASM_REWRITE_TAC[LENGTH; ARITH] THEN
    ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
    DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `l:(real^2)list` THEN
    REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL] THEN
    ASM_CASES_TAC `l:(real^2)list = []` THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(TL l:(real^2)list = [])` ASSUME_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(real^2)list->num`) THEN
      ASM_SIMP_TAC[LENGTH; LENGTH_TL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LAST_APPEND; LENGTH_APPEND; LENGTH_TL; NOT_CONS_NIL] THEN
    ASM_REWRITE_TAC[LAST; HD_APPEND; LENGTH] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC PATH_IMAGE_POLYGONAL_PATH_ROTATE THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`HD(l:(real^2)list) = LAST l`; `5 <= LENGTH(p:(real^2)list)`;
        `~(l:(real^2)list = [])`] THEN
      ASM_REWRITE_TAC[] THEN
      SPEC_TAC(`l:(real^2)list`,`l:(real^2)list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[HD; TL; APPEND] THEN
      REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
       `a IN s /\ b IN s ==> s UNION {a} = b INSERT s`) THEN
      ASM_REWRITE_TAC[LAST] THEN ONCE_ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LAST] THEN UNDISCH_TAC `5 <= LENGTH(CONS (h:real^2) t)` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH] THEN
      REWRITE_TAC[IN_SET_OF_LIST; MEM_EXISTS_EL; LENGTH] THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `0` THEN REWRITE_TAC[EL] THEN ASM_ARITH_TAC;
        EXISTS_TAC `LENGTH(t:(real^2)list) - 1` THEN
        ASM_SIMP_TAC[LAST_EL] THEN ASM_ARITH_TAC];
      MP_TAC(ISPEC `l:(real^2)list` SIMPLE_PATH_POLYGONAL_PATH_ROTATE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. MEM x p <=> MEM x p'`
   (fun th -> REWRITE_TAC[th] THEN
              RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL [ASM_REWRITE_TAC[GSYM IN_SET_OF_LIST]; ALL_TAC] THEN
  MAP_EVERY (C UNDISCH_THEN (SUBST_ALL_TAC o SYM))
   [`set_of_list(p':(real^2)list) = set_of_list p`;
    `path_image(polygonal_path(p':(real^2)list)) =
     path_image (polygonal_path p)`;
    `LENGTH(p':(real^2)list) = LENGTH(p:(real^2)list)`] THEN
  MAP_EVERY (C UNDISCH_THEN (K ALL_TAC))
   [`simple_path(polygonal_path(p:(real^2)list))`;
    `pathfinish(polygonal_path(p:(real^2)list)) =
     pathstart(polygonal_path p)`] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`p':(real^2)list`,`p:(real^2)list`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?q r. 2 <= LENGTH q /\ 2 <= LENGTH r /\
          LENGTH q + LENGTH r = LENGTH p + 1 /\
          set_of_list q UNION set_of_list r = set_of_list p /\
          pathstart(polygonal_path q) = pathstart(polygonal_path p) /\
          pathfinish(polygonal_path q) = (b:real^2) /\
          pathstart(polygonal_path r) = b /\
          pathfinish(polygonal_path r) = pathfinish(polygonal_path p) /\
          simple_path(polygonal_path q ++ polygonal_path r) /\
          path_image(polygonal_path q ++ polygonal_path r) =
          path_image(polygonal_path p)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `simple_path(polygonal_path p) /\
      2 <= LENGTH p /\ MEM (b:real^2) p /\
      ~(pathstart(polygonal_path p) = b) /\
      ~(pathfinish(polygonal_path p) = b)`
    MP_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `5 <= p ==> 2 <= p`] THEN
      ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; CONJ_ASSOC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM];
      POP_ASSUM_LIST(K ALL_TAC)] THEN
    WF_INDUCT_TAC `LENGTH(p:(real^2)list)` THEN POP_ASSUM MP_TAC THEN
    SPEC_TAC(`p:(real^2)list`,`p:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `x:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                  MEM] THEN
      MESON_TAC[];
      REWRITE_TAC[LENGTH; ARITH]] THEN
    MAP_EVERY X_GEN_TAC [`y:real^2`; `l:(real^2)list`] THEN
    REPLICATE_TAC 3 (DISCH_THEN(K ALL_TAC)) THEN DISCH_TAC THEN
    REWRITE_TAC[polygonal_path] THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ONCE_REWRITE_TAC[MEM] THEN
    ASM_CASES_TAC `a:real^2 = b` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[MEM] THEN
    ASM_CASES_TAC `x:real^2 = b` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(K ALL_TAC o check is_forall o concl) THEN STRIP_TAC THEN
      EXISTS_TAC `[a:real^2;b]` THEN
      EXISTS_TAC `CONS (b:real^2) (CONS y l)` THEN
      ASM_REWRITE_TAC[polygonal_path; LENGTH] THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      REPEAT(CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
      REWRITE_TAC[set_of_list] THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `CONS (x:real^2) (CONS y l)`) THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `n < SUC n`] THEN ANTS_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 <= SUC(SUC n)`] THEN
      ONCE_REWRITE_TAC[MEM] THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        SIMPLE_PATH_JOIN_IMP)) THEN
      ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      SIMP_TAC[PATHFINISH_LINEPATH; ARC_IMP_SIMPLE_PATH];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:(real^2)list`; `r:(real^2)list`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`CONS (a:real^2) q`; `r:(real^2)list`] THEN
    ASM_REWRITE_TAC[LENGTH; NOT_CONS_NIL; HD] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[set_of_list; SET_RULE
       `(a INSERT s) UNION t = a INSERT (s UNION t)`];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `pathfinish(polygonal_path q) = (b:real^2)` THEN
      REWRITE_TAC[PATHFINISH_POLYGONAL_PATH; LAST; NOT_CONS_NIL] THEN
      UNDISCH_TAC `2 <= LENGTH(q:(real^2)list)` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `polygonal_path(CONS (a:real^2) q) =
      linepath(a,x) ++ polygonal_path q`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`pathstart(polygonal_path q) =
         pathstart(polygonal_path (CONS (x:real^2) (CONS y l)))`;
        `2 <= LENGTH(q:(real^2)list)`] THEN
      SPEC_TAC(`q:(real^2)list`,`q:(real^2)list`) THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
      GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
      REWRITE_TAC[LENGTH; ARITH; polygonal_path] THEN
      SIMP_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `pathstart(polygonal_path(CONS x (CONS y l))) = (x:real^2)`
     (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
     [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD]; ALL_TAC] THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (rand o rand) SIMPLE_PATH_ASSOC o snd) THEN
      ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `simple_path(linepath(a:real^2,x) ++
                               polygonal_path (CONS x (CONS y l)))` THEN
      ASM_CASES_TAC `pathfinish(polygonal_path r) = (a:real^2)` THENL
       [SUBGOAL_THEN
         `pathfinish(polygonal_path(CONS (x:real^2) (CONS y l))) = a`
        ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHFINISH_LINEPATH;
                     PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH] THEN
        STRIP_TAC THEN MATCH_MP_TAC SIMPLE_PATH_IMP_ARC THEN
        ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
        ASM_MESON_TAC[ARC_LINEPATH_EQ];
        SUBGOAL_THEN
         `~(pathfinish(polygonal_path(CONS (x:real^2) (CONS y l))) = a)`
        ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[SIMPLE_PATH_EQ_ARC; PATHSTART_JOIN; PATHSTART_LINEPATH;
                     PATHFINISH_JOIN] THEN
        ASM_SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_JOIN] THEN
        REWRITE_TAC[ARC_LINEPATH_EQ] THEN STRIP_TAC THEN
        SUBGOAL_THEN
         `arc(polygonal_path q ++ polygonal_path r:real^1->real^2)`
        MP_TAC THENL
         [ALL_TAC;
          ASM_SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_JOIN]] THEN
        MATCH_MP_TAC SIMPLE_PATH_IMP_ARC THEN
        ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP ARC_DISTINCT_ENDS) THEN
        REWRITE_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL]];
      ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
      SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; NOT_CONS_NIL; HD;
               PATHSTART_POLYGONAL_PATH] THEN
      UNDISCH_THEN
       `path_image(polygonal_path q ++ polygonal_path r) =
        path_image(polygonal_path(CONS (x:real^2) (CONS y l)))`
       (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathstart(polygonal_path p) = (a:real^2)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `5 <= LENGTH(p:(real^2)list)` THEN
    REWRITE_TAC[PATHSTART_POLYGONAL_PATH] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH];
    ALL_TAC] THEN
  UNDISCH_THEN `pathfinish (polygonal_path p) = (a:real^2)` SUBST_ALL_TAC THEN
  UNDISCH_THEN `path_image(polygonal_path q ++ polygonal_path r):real^2->bool =
                path_image(polygonal_path p)` (SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN
   `(!x:real^2. MEM x q ==> integral_vector x) /\
    (!x:real^2. MEM x r ==> integral_vector x)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GSYM IN_SET_OF_LIST; IN_UNION] THEN
    UNDISCH_THEN
     `(set_of_list q UNION set_of_list r):real^2->bool = set_of_list p`
     (SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[IN_UNION];
    ALL_TAC] THEN
  ABBREV_TAC `n = LENGTH(p:(real^2)list)` THEN
  SUBGOAL_THEN `integral_vector(a:real^2) /\ integral_vector(b:real^2)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY (C UNDISCH_THEN (K ALL_TAC))
   [`!x:real^2. MEM x p ==> integral_vector x`;
    `MEM (a:real^2) p`;
    `MEM (b:real^2) p`;
    `HD p = (a:real^2)`;
    `(set_of_list q UNION set_of_list r):real^2->bool = set_of_list p`;
    `simple_path(polygonal_path p :real^1->real^2)`] THEN
  SUBGOAL_THEN `3 <= LENGTH(q:(real^2)list)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(K ALL_TAC o check is_forall o concl)) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    SPEC_TAC(`q:(real^2)list`,`q:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a0:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a1:real^2` THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[LENGTH; ARITH; ARITH_RULE `3 <= SUC(SUC(SUC n))`] THEN
    REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_THEN `a0:real^2 = a` SUBST_ALL_TAC THEN
    UNDISCH_THEN `a1:real^2 = b` SUBST_ALL_TAC THEN
    UNDISCH_TAC `segment(a:real^2,b) SUBSET
                 inside(path_image(linepath(a,b) ++ polygonal_path r))` THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH; PATHFINISH_LINEPATH] THEN
    MATCH_MP_TAC(SET_RULE
     `inside(s' UNION t) INTER (s' UNION t) = {} /\ ~(s = {}) /\ s SUBSET s'
      ==> ~(s SUBSET inside(s' UNION t))`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
    ASM_REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SEGMENT_EQ_EMPTY];
    UNDISCH_THEN `2 <= LENGTH(q:(real^2)list)` (K ALL_TAC)] THEN
  SUBGOAL_THEN `3 <= LENGTH(r:(real^2)list)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(K ALL_TAC o check is_forall o concl)) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    SPEC_TAC(`r:(real^2)list`,`r:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a0:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a1:real^2` THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[LENGTH; ARITH; ARITH_RULE `3 <= SUC(SUC(SUC n))`] THEN
    REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_THEN `a0:real^2 = b` SUBST_ALL_TAC THEN
    UNDISCH_THEN `a1:real^2 = a` SUBST_ALL_TAC THEN
    UNDISCH_TAC `segment(a:real^2,b) SUBSET
                 inside(path_image(polygonal_path q ++ linepath(b,a)))` THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH] THEN
    ONCE_REWRITE_TAC[CONJUNCT1 SEGMENT_SYM] THEN
    MATCH_MP_TAC(SET_RULE
     `inside(t UNION s') INTER (t UNION s') = {} /\ ~(s = {}) /\ s SUBSET s'
      ==> ~(s SUBSET inside(t UNION s'))`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
    ASM_REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SEGMENT_EQ_EMPTY];
    UNDISCH_THEN `2 <= LENGTH(r:(real^2)list)` (K ALL_TAC)] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(ISPEC `CONS (a:real^2) r` th) THEN
    MP_TAC(ISPEC `CONS (b:real^2) q` th)) THEN
  REWRITE_TAC[LENGTH] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `polygonal_path(CONS (b:real^2) q) = linepath(b,a) ++ polygonal_path q`
  SUBST_ALL_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    SPEC_TAC(`q:(real^2)list`,`q:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[LENGTH; ARITH; polygonal_path] THEN
    SIMP_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEM; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[PATHSTART_LINEPATH]] THEN
    UNDISCH_TAC
     `simple_path(polygonal_path q ++ polygonal_path r :real^1->real^2)` THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
                 PATHFINISH_LINEPATH; ARC_LINEPATH_EQ] THEN
    STRIP_TAC THEN REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
    REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET i
      ==> c INTER i = {}
          ==> (s UNION {a,b}) INTER c SUBSET {b,a}`)) THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN] THEN
    MATCH_MP_TAC(SET_RULE
     `inside(s UNION t) INTER (s UNION t) = {}
      ==> s INTER inside(s UNION t) = {}`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP];
    STRIP_TAC] THEN
  REWRITE_TAC[LENGTH] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `polygonal_path(CONS (a:real^2) r) = linepath(a,b) ++ polygonal_path r`
  SUBST_ALL_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    SPEC_TAC(`r:(real^2)list`,`r:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[LENGTH; ARITH; polygonal_path] THEN
    SIMP_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEM; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[PATHSTART_LINEPATH]] THEN
    UNDISCH_TAC
     `simple_path(polygonal_path q ++ polygonal_path r :real^1->real^2)` THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
                 PATHFINISH_LINEPATH; ARC_LINEPATH_EQ] THEN
    STRIP_TAC THEN REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
    REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET i
      ==> c INTER i = {}
          ==> (s UNION {a,b}) INTER c SUBSET {a,b}`)) THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN] THEN
    MATCH_MP_TAC(SET_RULE
     `inside(s UNION t) INTER (s UNION t) = {}
      ==> t INTER inside(s UNION t) = {}`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`polygonal_path q:real^1->real^2`;
                 `reversepath(polygonal_path r):real^1->real^2`;
                 `linepath(a:real^2,b)`; `a:real^2`; `b:real^2`]
        SPLIT_INSIDE_SIMPLE_CLOSED_CURVE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                    PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                    SIMPLE_PATH_LINEPATH_EQ] THEN
    UNDISCH_TAC
     `simple_path(polygonal_path q ++ polygonal_path r :real^1->real^2)` THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATH_IMAGE_LINEPATH] THEN
    ASM_SIMP_TAC[PATH_IMAGE_REVERSEPATH; ARC_IMP_SIMPLE_PATH;
     SIMPLE_PATH_REVERSEPATH] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `s INTER t SUBSET {a,b} /\
        a IN s /\ b IN s /\ a IN t /\ b IN t
        ==> s INTER t = {a,b}`) THEN
      ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
      REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      UNDISCH_TAC
       `segment(a:real^2,b) SUBSET
        inside(path_image(polygonal_path q ++ polygonal_path r))` THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN] THEN MATCH_MP_TAC(SET_RULE
       `a IN t /\ b IN t /\ inside(t UNION u) INTER (t UNION u) = {}
        ==> s SUBSET inside(t UNION u)
            ==> t INTER (s UNION {a,b}) = {a,b}`) THEN
      REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
      ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
      REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      UNDISCH_TAC
       `segment(a:real^2,b) SUBSET
        inside(path_image(polygonal_path q ++ polygonal_path r))` THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN] THEN MATCH_MP_TAC(SET_RULE
       `a IN u /\ b IN u /\ inside(t UNION u) INTER (t UNION u) = {}
        ==> s SUBSET inside(t UNION u)
            ==> u INTER (s UNION {a,b}) = {a,b}`) THEN
      REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
      ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
      REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `s SUBSET i
        ==> inside(q UNION r) INTER (q UNION r) = {} /\
            inside(q UNION r) = i /\
            ~(s = {})
            ==> ~((s UNION {a,b}) INTER inside(q UNION r) = {})`)) THEN
      ASM_REWRITE_TAC[INSIDE_NO_OVERLAP; SEGMENT_EQ_EMPTY] THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN]];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
   check (free_in `measure:(real^2->bool)->real` o concl))) THEN
  UNDISCH_TAC
   `segment(a:real^2,b) SUBSET
    inside(path_image (polygonal_path q ++ polygonal_path r))` THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  REWRITE_TAC[PATH_IMAGE_REVERSEPATH; PATH_IMAGE_LINEPATH] THEN
  SUBST1_TAC(ISPECL [`b:real^2`; `a:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
  REPEAT STRIP_TAC THEN SUBST1_TAC(SYM(ASSUME
   `inside(path_image(polygonal_path q) UNION segment [a,b]) UNION
    inside(path_image(polygonal_path r) UNION segment [a,b]) UNION
    (segment [a:real^2,b] DIFF {a, b}) =
    inside
     (path_image(polygonal_path q) UNION path_image(polygonal_path r))`)) THEN
  REWRITE_TAC[SET_RULE
   `{x | x IN (s UNION t) /\ P x} =
    {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `measure(inside(path_image(polygonal_path q) UNION segment[a:real^2,b])) +
    measure(inside(path_image (polygonal_path r) UNION segment [a,b]) UNION
            segment [a,b] DIFF {a, b})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_INSIDE THEN
      MATCH_MP_TAC COMPACT_UNION THEN
      SIMP_TAC[COMPACT_PATH_IMAGE; COMPACT_SEGMENT; PATH_POLYGONAL_PATH];
      MATCH_MP_TAC MEASURABLE_UNION THEN CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_INSIDE THEN
        MATCH_MP_TAC COMPACT_UNION THEN
        SIMP_TAC[COMPACT_PATH_IMAGE; COMPACT_SEGMENT; PATH_POLYGONAL_PATH];
        MATCH_MP_TAC MEASURABLE_DIFF THEN CONJ_TAC THEN
        MATCH_MP_TAC MEASURABLE_COMPACT THEN REWRITE_TAC[COMPACT_SEGMENT] THEN
        MATCH_MP_TAC FINITE_IMP_COMPACT THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY]];
      ASM_REWRITE_TAC[UNION_OVER_INTER; UNION_EMPTY] THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `segment[a:real^2,b]` THEN
      REWRITE_TAC[NEGLIGIBLE_SEGMENT_2] THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `measure(inside(path_image(polygonal_path q) UNION segment[a:real^2,b])) +
    measure(inside(path_image(polygonal_path r) UNION segment[a,b]))` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `segment[a:real^2,b]` THEN
    REWRITE_TAC[NEGLIGIBLE_SEGMENT_2] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[SET_RULE `s UNION segment[a,b] = segment[a,b] UNION s`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `CARD({x | x IN inside(segment[a,b] UNION path_image(polygonal_path q)) /\
              integral_vector x} UNION
         {x | x IN inside(segment[a,b] UNION path_image(polygonal_path r)) /\
              integral_vector x} UNION
         {x | x IN segment[a,b] DIFF {a, b} /\ integral_vector x}) =
    CARD {x | x IN inside(segment[a,b] UNION path_image(polygonal_path q)) /\
              integral_vector x} +
    CARD {x | x IN inside(segment[a,b] UNION path_image(polygonal_path r)) /\
              integral_vector x} +
    CARD {x:real^2 | x IN segment[a,b] DIFF {a, b} /\ integral_vector x}`
  SUBST1_TAC THENL
   [(CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
     [CARD_UNION_GEN; FINITE_BOUNDED_INTEGER_POINTS; FINITE_UNION;
      BOUNDED_INSIDE; BOUNDED_UNION; BOUNDED_SEGMENT;
      BOUNDED_PATH_IMAGE; BOUNDED_DIFF; PATH_POLYGONAL_PATH] THEN
    MATCH_MP_TAC(ARITH_RULE
     `pr = 0 /\ qrp = 0 ==> (q + (r + p) - pr) - qrp = q + r + p`) THEN
    REWRITE_TAC[UNION_OVER_INTER] THEN
    REWRITE_TAC[SET_RULE
     `{x | x IN s /\ P x} INTER {x | x IN t /\ P x} =
      {x | x IN (s INTER t) /\ P x}`] THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE
     [SET_RULE `s UNION segment[a,b] = segment[a,b] UNION s`]) THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; UNION_EMPTY] THEN CONJ_TAC THEN
    MATCH_MP_TAC(MESON[CARD_CLAUSES] `s = {} ==> CARD s = 0`) THEN
    MATCH_MP_TAC(SET_RULE
     `inside(s UNION t) INTER (s UNION t) = {}
      ==> {x | x IN inside(s UNION t) INTER (s DIFF ab) /\ P x} = {}`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN MATCH_MP_TAC(REAL_ARITH
   `q + r = &2 * x + y + &2
    ==> (iq + q / &2 - &1) + (ir + r / &2 - &1) =
        ((iq + ir + x) + y / &2 - &1)`) THEN
  REWRITE_TAC[SET_RULE
   `{x | x IN (s UNION t) /\ P x} =
    {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`] THEN
  (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [CARD_UNION_GEN; FINITE_BOUNDED_INTEGER_POINTS; BOUNDED_SEGMENT;
    BOUNDED_PATH_IMAGE; PATH_POLYGONAL_PATH; GSYM REAL_OF_NUM_SUB;
    INTER_SUBSET; CARD_SUBSET; ARITH_RULE `x:num <= y ==> x <= y + z`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN MATCH_MP_TAC(REAL_ARITH
   `&2 * ab + qr = &2 * x + qab + rab + &2
    ==> ((ab + q) - qab) + ((ab + r) - rab) =
        &2 * x + ((q + r) - qr) + &2`) THEN
  SUBGOAL_THEN
   `{x | x IN segment[a,b] /\ integral_vector x} INTER
    {x | x IN path_image(polygonal_path q) /\ integral_vector x} = {a,b} /\
    {x:real^2 | x IN segment[a,b] /\ integral_vector x} INTER
    {x | x IN path_image(polygonal_path r) /\ integral_vector x} = {a,b}`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET inside(q UNION r)
      ==> s = c DIFF {a,b} /\ a IN q /\ b IN q /\ a IN r /\ b IN r /\
          inside(q UNION r) INTER (q UNION r) = {} /\
          P a /\ P b /\ a IN c /\ b IN c
          ==> {x | x IN c /\ P x} INTER {x | x IN q /\ P x} = {a,b} /\
              {x | x IN c /\ P x} INTER {x | x IN r /\ P x} = {a,b}`)) THEN
    ASM_REWRITE_TAC[open_segment; INSIDE_NO_OVERLAP; ENDS_IN_SEGMENT] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x:real^2 | x IN path_image(polygonal_path q) /\ integral_vector x} INTER
    {x | x IN path_image(polygonal_path r) /\ integral_vector x} = {a,b}`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      SIMPLE_PATH_JOIN_IMP)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    MATCH_MP_TAC(SET_RULE
     `P a /\ P b /\ a IN q /\ b IN q /\ a IN r /\ b IN r
      ==> (q INTER r) SUBSET {a,b}
          ==> {x | x IN q /\ P x} INTER {x | x IN r /\ P x} = {a,b}`) THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
    ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH
   `x = y + &2 ==> &2 * x + &2 = &2 * y + &2 + &2 + &2`) THEN
  REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
  SUBGOAL_THEN `(segment(a,b) UNION {a, b}) DIFF {a, b} = segment(a:real^2,b)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `~(a IN s) /\ ~(b IN s) ==> (s UNION {a,b}) DIFF {a,b} = s`) THEN
    REWRITE_TAC[open_segment; IN_DIFF] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SET_RULE
   `P a /\ P b
    ==> {x | x IN s UNION {a,b} /\ P x} =
        a INSERT b INSERT {x | x IN s /\ P x}`] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_BOUNDED_INTEGER_POINTS;
           BOUNDED_SEGMENT; FINITE_INSERT] THEN
  ASM_REWRITE_TAC[IN_INSERT; IN_ELIM_THM; ENDS_NOT_IN_SEGMENT] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; ARITH_RULE `SUC(SUC n) = n + 2`]);;
