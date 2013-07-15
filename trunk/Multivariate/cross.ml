(* ========================================================================= *)
(* Cross products in real^3.                                                 *)
(* ========================================================================= *)

needs "Multivariate/topology.ml";;

prioritize_vector();;

(* ------------------------------------------------------------------------- *)
(* The definition.                                                           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("cross",(20,"right"));;

let cross = new_definition
 `(a:real^3) cross (b:real^3) =
    vector [a$2 * b$3 - a$3 * b$2;
            a$3 * b$1 - a$1 * b$3;
            a$1 * b$2 - a$2 * b$1] :real^3`;;

(* ------------------------------------------------------------------------- *)
(* Some simple automation.                                                   *)
(* ------------------------------------------------------------------------- *)

let VEC3_TAC =
  SIMP_TAC[CART_EQ; LAMBDA_BETA; FORALL_3; SUM_3; DIMINDEX_3; VECTOR_3;
           vector_add; vec; dot; cross; orthogonal; basis; DET_3;
           vector_neg; vector_sub; vector_mul; ARITH] THEN
  CONV_TAC REAL_RING;;

let VEC3_RULE tm = prove(tm,VEC3_TAC);;

(* ------------------------------------------------------------------------- *)
(* Basic lemmas.                                                             *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_CROSS = prove
 (`!x y. orthogonal (x cross y) x /\ orthogonal (x cross y) y /\
         orthogonal x (x cross y) /\ orthogonal y (x cross y)`,
  VEC3_TAC);;

let CROSS_LZERO = prove
 (`!x. (vec 0) cross x = vec 0`,
  VEC3_TAC);;

let CROSS_RZERO = prove
 (`!x. x cross (vec 0) = vec 0`,
  VEC3_TAC);;

let CROSS_SKEW = prove
 (`!x y. (x cross y) = --(y cross x)`,
  VEC3_TAC);;

let CROSS_REFL = prove
 (`!x. x cross x = vec 0`,
  VEC3_TAC);;

let CROSS_LADD = prove
 (`!x y z. (x + y) cross z = (x cross z) + (y cross z)`,
  VEC3_TAC);;

let CROSS_RADD = prove
 (`!x y z. x cross (y + z) = (x cross y) + (x cross z)`,
  VEC3_TAC);;

let CROSS_LMUL = prove
 (`!c x y. (c % x) cross y = c % (x cross y)`,
  VEC3_TAC);;

let CROSS_RMUL = prove
 (`!c x y. x cross (c % y) = c % (x cross y)`,
  VEC3_TAC);;

let CROSS_LNEG = prove
 (`!x y. (--x) cross y = --(x cross y)`,
  VEC3_TAC);;

let CROSS_RNEG = prove
 (`!x y. x cross (--y) = --(x cross y)`,
  VEC3_TAC);;

let CROSS_LSUB = prove
 (`!x y z. (x - y) cross z = x cross z - y cross z`,
  VEC3_TAC);;

let CROSS_RSUB = prove
 (`!x y z. x cross (y - z) = x cross y - x cross z`,
  VEC3_TAC);;

let CROSS_JACOBI = prove
 (`!x y z.
    x cross (y cross z) + y cross (z cross x) + z cross (x cross y) = vec 0`,
  VEC3_TAC);;

let CROSS_LAGRANGE = prove
 (`!x y z. x cross (y cross z) = (x dot z) % y - (x dot y) % z`,
  VEC3_TAC);;

let CROSS_TRIPLE = prove
 (`!x y z.  (x cross y) dot z = (y cross z) dot x`,
  VEC3_TAC);;

let DOT_CROSS_SELF = prove
 (`(!x y. x dot (x cross y) = &0) /\
   (!x y. x dot (y cross x) = &0) /\
   (!x y. (x cross y) dot y = &0) /\
   (!x y. (y cross x) dot y = &0)`,
  VEC3_TAC);;

let CROSS_COMPONENTS = prove
 (`!x y. (x cross y)$1 = x$2 * y$3 - y$2 * x$3 /\
         (x cross y)$2 = x$3 * y$1 - y$3 * x$1 /\
         (x cross y)$3 = x$1 * y$2 - y$1 * x$2`,
  VEC3_TAC);;

let CROSS_BASIS = prove
 (`(basis 1) cross (basis 2) = basis 3 /\
   (basis 2) cross (basis 1) = --(basis 3) /\
   (basis 2) cross (basis 3) = basis 1 /\
   (basis 3) cross (basis 2) = --(basis 1) /\
   (basis 3) cross (basis 1) = basis 2 /\
   (basis 1) cross (basis 3) = --(basis 2)`,
  VEC3_TAC);;

let CROSS_BASIS_NONZERO = prove
 (`!u. ~(u = vec 0)
       ==> ~(u cross basis 1 = vec 0) \/
           ~(u cross basis 2 = vec 0) \/
           ~(u cross basis 3 = vec 0)`,
  VEC3_TAC);;

let CROSS_DOT_CANCEL = prove
 (`!x y z.
     x dot y = x dot z /\ x cross y = x cross z /\ ~(x = vec 0) ==> y = z`,
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN REWRITE_TAC[GSYM DOT_EQ_0] THEN
  VEC3_TAC);;

let NORM_CROSS_DOT = prove
 (`!x y. norm(x cross y) pow 2 + (x dot y) pow 2 = (norm(x) * norm y) pow 2`,
  REWRITE_TAC[REAL_POW_MUL; NORM_POW_2] THEN VEC3_TAC);;

let DOT_CROSS_DET = prove
 (`!x y z. x dot (y cross z) = det(vector[x;y;z]:real^3^3)`,
  VEC3_TAC);;

let CROSS_CROSS_DET = prove
 (`!w x y z. (w cross x) cross (y cross z) =
                det(vector[w;x;z]:real^3^3) % y -
                det(vector[w;x;y]:real^3^3) % z`,
  VEC3_TAC);;

let DOT_CROSS = prove
 (`!w x y z. (w cross x) dot (y cross z) =
                (w dot y) * (x dot z) - (w dot z) * (x dot y)`,
  VEC3_TAC);;

let NORM_CROSS = prove
 (`!x y. norm(x cross y) pow 2 =
           norm(x) pow 2 * norm(y) pow 2 - (x dot y) pow 2`,
  REWRITE_TAC[NORM_POW_2] THEN VEC3_TAC);;

let CROSS_EQ_0 = prove
 (`!x y. x cross y = vec 0 <=> collinear{vec 0,x,y}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
  ONCE_REWRITE_TAC[REAL_RING `x = &0 <=> x pow 2 = &0`] THEN
  REWRITE_TAC[NORM_CROSS; REAL_SUB_0; GSYM REAL_POW_MUL] THEN
  REWRITE_TAC[GSYM REAL_EQ_SQUARE_ABS; GSYM NORM_CAUCHY_SCHWARZ_EQUAL] THEN
  SIMP_TAC[real_abs; REAL_LE_MUL; NORM_POS_LE; EQ_SYM_EQ]);;

let CROSS_0 = prove
 (`(!x. vec 0 cross x = vec 0) /\
   (!x. x cross vec 0 = vec 0)`,
  VEC3_TAC);;

let CROSS_EQ_SELF = prove
 (`(!x y. x cross y = x <=> x = vec 0) /\
   (!x y. x cross y = y <=> y = vec 0)`,
  MESON_TAC[ORTHOGONAL_CROSS; CROSS_0; ORTHOGONAL_REFL]);;

let NORM_AND_CROSS_EQ_0 = prove
 (`!x y. x dot y = &0 /\ x cross y = vec 0 <=> x = vec 0 \/ y = vec 0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:real^3 = vec 0` THEN
  ASM_REWRITE_TAC[CROSS_0; DOT_LZERO] THEN ASM_CASES_TAC `y:real^3 = vec 0` THEN
  ASM_REWRITE_TAC[CROSS_0; DOT_RZERO] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[GSYM DOT_EQ_0; DOT_CROSS; REAL_MUL_LZERO] THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_ENTIRE; DOT_EQ_0]);;

let BILINEAR_CROSS = prove
 (`bilinear(cross)`,
  REWRITE_TAC[linear; bilinear; CROSS_LADD; CROSS_RADD;
              CROSS_LMUL; CROSS_RMUL]);;

(* ------------------------------------------------------------------------- *)
(* Preservation by rotation, or other orthogonal transformation up to sign.  *)
(* ------------------------------------------------------------------------- *)

let CROSS_MATRIX_MUL = prove
 (`!A x y. transp A ** ((A ** x) cross (A ** y)) = det A % (x cross y)`,
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; SUM_3; matrix_vector_mul;
           CROSS_COMPONENTS; LAMBDA_BETA; ARITH; transp; DET_3;
           VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let CROSS_ORTHOGONAL_MATRIX = prove
 (`!A x y. orthogonal_matrix A
           ==> (A ** x) cross (A ** y) = det A % (A ** (x cross y))`,
  MP_TAC CROSS_MATRIX_MUL THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  REWRITE_TAC[orthogonal_matrix] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o AP_TERM `matrix_vector_mul (A:real^3^3)`) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL]);;

let CROSS_ROTATION_MATRIX = prove
 (`!A x y. rotation_matrix A
           ==> (A ** x) cross (A ** y) =  A ** (x cross y)`,
  SIMP_TAC[rotation_matrix; CROSS_ORTHOGONAL_MATRIX; VECTOR_MUL_LID]);;

let CROSS_ROTOINVERSION_MATRIX = prove
 (`!A x y. rotoinversion_matrix A
           ==> (A ** x) cross (A ** y) =  --(A ** (x cross y))`,
  SIMP_TAC[rotoinversion_matrix; CROSS_ORTHOGONAL_MATRIX; VECTOR_MUL_LID;
           VECTOR_MUL_LNEG]);;

let CROSS_ORTHOGONAL_TRANSFORMATION = prove
 (`!f x y.
        orthogonal_transformation f
        ==> (f x) cross (f y) = det(matrix f) % f(x cross y)`,
  GEN_TAC THEN
  MP_TAC(ISPEC `matrix(f:real^3->real^3)` CROSS_ORTHOGONAL_MATRIX) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX;
                  ORTHOGONAL_TRANSFORMATION_LINEAR];
    ASM_SIMP_TAC[MATRIX_WORKS; ORTHOGONAL_TRANSFORMATION_LINEAR]]);;

let CROSS_LINEAR_IMAGE = prove
 (`!f x y. linear f /\ (!x. norm(f x) = norm x) /\ det(matrix f) = &1
           ==> (f x) cross (f y) = f(x cross y)`,
  SIMP_TAC[ORTHOGONAL_TRANSFORMATION; CONJ_ASSOC; VECTOR_MUL_LID;
           CROSS_ORTHOGONAL_TRANSFORMATION]);;

(* ------------------------------------------------------------------------- *)
(* Continuity.                                                               *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_CROSS = prove
 (`!net:(A)net f g.
        f continuous net /\ g continuous net
        ==> (\x. (f x) cross (g x)) continuous net`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CONTINUOUS_COMPONENTWISE_LIFT] THEN
  REWRITE_TAC[cross; VECTOR_3; DIMINDEX_3; FORALL_3; LIFT_SUB] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_SUB THEN
  REWRITE_TAC[LIFT_CMUL] THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
  ASM_SIMP_TAC[o_DEF; CONTINUOUS_LIFT_COMPONENT_COMPOSE]);;

let CONTINUOUS_ON_CROSS = prove
 (`!f:real^N->real^3 g s.
        f continuous_on s /\ g continuous_on s
        ==> (\x. (f x) cross (g x)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_CROSS]);;

(* ------------------------------------------------------------------------- *)
(* Prove a weaker variant for more convenient interface with functions       *)
(* intended to work in 1 dimension.                                          *)
(* ------------------------------------------------------------------------- *)

let CROSS_LINEAR_IMAGE_WEAK = prove
 (`!f x y. linear f /\ (!x. norm(f x) = norm x) /\
           (2 <= dimindex(:3) ==> det(matrix f) = &1)
           ==> (f x) cross (f y) = f(x cross y)`,
  REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  SIMP_TAC[ORTHOGONAL_TRANSFORMATION; CONJ_ASSOC; VECTOR_MUL_LID;
           CROSS_ORTHOGONAL_TRANSFORMATION]);;

add_linear_invariants [CROSS_LINEAR_IMAGE_WEAK];;
