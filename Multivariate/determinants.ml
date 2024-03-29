(* ========================================================================= *)
(* Determinant and trace of a square matrix.                                 *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

needs "Multivariate/vectors.ml";;
needs "Library/permutations.ml";;
needs "Library/floor.ml";;
needs "Library/products.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Trace of a matrix (this is relatively easy).                              *)
(* ------------------------------------------------------------------------- *)

let trace = new_definition
  `(trace:real^N^N->real) A = sum(1..dimindex(:N)) (\i. A$i$i)`;;

let TRACE_0 = prove
 (`trace(mat 0) = &0`,
  SIMP_TAC[trace; mat; LAMBDA_BETA; SUM_0]);;

let TRACE_I = prove
 (`trace(mat 1 :real^N^N) = &(dimindex(:N))`,
  SIMP_TAC[trace; mat; LAMBDA_BETA; SUM_CONST_NUMSEG; REAL_MUL_RID] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let TRACE_ADD = prove
 (`!A B:real^N^N. trace(A + B) = trace(A) + trace(B)`,
  SIMP_TAC[trace; matrix_add; SUM_ADD_NUMSEG; LAMBDA_BETA]);;

let TRACE_SUB = prove
 (`!A B:real^N^N. trace(A - B) = trace(A) - trace(B)`,
  SIMP_TAC[trace; matrix_sub; SUM_SUB_NUMSEG; LAMBDA_BETA]);;

let TRACE_CMUL = prove
 (`!c A:real^N^N. trace(c %% A) = c * trace A`,
  REWRITE_TAC[trace; MATRIX_CMUL_COMPONENT; SUM_LMUL]);;

let TRACE_NEG = prove
 (`!A:real^N^N. trace(--A) = --(trace A)`,
  REWRITE_TAC[trace; MATRIX_NEG_COMPONENT; SUM_NEG]);;

let TRACE_MUL_SYM = prove
 (`!A B:real^N^M. trace(A ** B) = trace(B ** A)`,
  REPEAT GEN_TAC THEN SIMP_TAC[trace; matrix_mul; LAMBDA_BETA] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[REAL_MUL_SYM]);;

let TRACE_TRANSP = prove
 (`!A:real^N^N. trace(transp A) = trace A`,
  SIMP_TAC[trace; transp; LAMBDA_BETA]);;

let TRACE_SIMILAR = prove
 (`!A:real^N^N U:real^N^N.
        invertible U ==> trace(matrix_inv U ** A ** U) = trace A`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[TRACE_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_INV; MATRIX_MUL_RID]);;

let TRACE_MUL_CYCLIC = prove
 (`!A:real^P^M B C:real^M^N. trace(A ** B ** C) = trace(B ** C ** A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [TRACE_MUL_SYM] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Definition of determinant.                                                *)
(* ------------------------------------------------------------------------- *)

let det = new_definition
 `det(A:real^N^N) =
        sum { p | p permutes 1..dimindex(:N) }
            (\p. sign(p) * product (1..dimindex(:N)) (\i. A$i$(p i)))`;;

(* ------------------------------------------------------------------------- *)
(* A few general lemmas we need below.                                       *)
(* ------------------------------------------------------------------------- *)

let IN_DIMINDEX_SWAP = prove
 (`!m n j. 1 <= m /\ m <= dimindex(:N) /\
             1 <= n /\ n <= dimindex(:N) /\
             1 <= j /\ j <= dimindex(:N)
           ==> 1 <= swap(m,n) j /\ swap(m,n) j <= dimindex(:N)`,
  REWRITE_TAC[swap] THEN ARITH_TAC);;

let LAMBDA_BETA_PERM = prove
 (`!p i. p permutes 1..dimindex(:N) /\ 1 <= i /\ i <= dimindex(:N)
         ==> ((lambda) g :A^N) $ p(i) = g(p i)`,
  ASM_MESON_TAC[LAMBDA_BETA; PERMUTES_IN_IMAGE; IN_NUMSEG]);;

let PRODUCT_PERMUTE = prove
 (`!f p s. p permutes s ==> product s f = product s (f o p)`,
  REWRITE_TAC[product] THEN MATCH_MP_TAC ITERATE_PERMUTE THEN
  REWRITE_TAC[MONOIDAL_REAL_MUL]);;

let PRODUCT_PERMUTE_NUMSEG = prove
 (`!f p m n. p permutes m..n ==> product(m..n) f = product(m..n) (f o p)`,
  MESON_TAC[PRODUCT_PERMUTE; FINITE_NUMSEG]);;

let REAL_MUL_SUM = prove
 (`!s t f g.
        FINITE s /\ FINITE t
        ==> sum s f * sum t g = sum s (\i. sum t (\j. f(i) * g(j)))`,
  SIMP_TAC[SUM_LMUL] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN SIMP_TAC[SUM_LMUL]);;

let REAL_MUL_SUM_NUMSEG = prove
 (`!m n p q. sum(m..n) f * sum(p..q) g =
             sum(m..n) (\i. sum(p..q) (\j. f(i) * g(j)))`,
  SIMP_TAC[REAL_MUL_SUM; FINITE_NUMSEG]);;

(* ------------------------------------------------------------------------- *)
(* Basic determinant properties.                                             *)
(* ------------------------------------------------------------------------- *)

let DET_CMUL = prove
 (`!A:real^N^N c. det(c %% A) = c pow dimindex(:N) * det A`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[det; MATRIX_CMUL_COMPONENT; PRODUCT_MUL; FINITE_NUMSEG] THEN
  SIMP_TAC[PRODUCT_CONST_NUMSEG_1; GSYM SUM_LMUL] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let DET_NEG = prove
 (`!A:real^N^N. det(--A) = --(&1) pow dimindex(:N) * det A`,
  REWRITE_TAC[MATRIX_NEG_MINUS1; DET_CMUL]);;

let DET_TRANSP = prove
 (`!A:real^N^N. det(transp A) = det A`,
  GEN_TAC THEN REWRITE_TAC[det] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_PERMUTATIONS_INVERSE] THEN
  MATCH_MP_TAC SUM_EQ THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN X_GEN_TAC `p:num->num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BINOP_TAC THENL
   [ASM_MESON_TAC[SIGN_INVERSE; PERMUTATION_PERMUTES; FINITE_NUMSEG];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
    [GSYM(MATCH_MP PERMUTES_IMAGE th)]) THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `product(1..dimindex(:N))
       ((\i. (transp A:real^N^N)$i$inverse p(i)) o p)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_IMAGE THEN
    ASM_MESON_TAC[FINITE_NUMSEG; PERMUTES_INJECTIVE; PERMUTES_INVERSE];
    MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    SIMP_TAC[transp; LAMBDA_BETA; o_THM] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
    SIMP_TAC[FUN_EQ_THM; I_THM; o_THM] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[PERMUTES_IN_NUMSEG; LAMBDA_BETA_PERM; LAMBDA_BETA]]);;

let DET_LOWERTRIANGULAR = prove
 (`!A:real^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ i < j ==> A$i$j = &0)
        ==> det(A) = product(1..dimindex(:N)) (\i. A$i$i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[det] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {I}
     (\p. sign p * product(1..dimindex(:N)) (\i. (A:real^N^N)$i$p(i)))` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_SING; SIGN_I; REAL_MUL_LID; I_THM]] THEN
  MATCH_MP_TAC SUM_SUPERSET THEN
  SIMP_TAC[IN_SING; FINITE_RULES; SUBSET; IN_ELIM_THM; PERMUTES_I] THEN
  X_GEN_TAC `p:num->num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PRODUCT_EQ_0_NUMSEG; REAL_ENTIRE; SIGN_NZ] THEN
  MP_TAC(SPECL [`p:num->num`; `1..dimindex(:N)`] PERMUTES_NUMSET_LE) THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG; NOT_LT]);;

let DET_UPPERTRIANGULAR = prove
 (`!A:real^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ j < i ==> A$i$j = &0)
        ==> det(A) = product(1..dimindex(:N)) (\i. A$i$i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[det] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {I}
     (\p. sign p * product(1..dimindex(:N)) (\i. (A:real^N^N)$i$p(i)))` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_SING; SIGN_I; REAL_MUL_LID; I_THM]] THEN
  MATCH_MP_TAC SUM_SUPERSET THEN
  SIMP_TAC[IN_SING; FINITE_RULES; SUBSET; IN_ELIM_THM; PERMUTES_I] THEN
  X_GEN_TAC `p:num->num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PRODUCT_EQ_0_NUMSEG; REAL_ENTIRE; SIGN_NZ] THEN
  MP_TAC(SPECL [`p:num->num`; `1..dimindex(:N)`] PERMUTES_NUMSET_GE) THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG; NOT_LT]);;

let DET_I = prove
 (`det(mat 1 :real^N^N) = &1`,
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `product(1..dimindex(:N)) (\i. (mat 1:real^N^N)$i$i)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DET_LOWERTRIANGULAR;
    MATCH_MP_TAC PRODUCT_EQ_1_NUMSEG] THEN
  SIMP_TAC[mat; LAMBDA_BETA] THEN MESON_TAC[LT_REFL]);;

let DET_0 = prove
 (`det(mat 0 :real^N^N) = &0`,
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `product(1..dimindex(:N)) (\i. (mat 0:real^N^N)$i$i)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DET_LOWERTRIANGULAR;
    REWRITE_TAC[PRODUCT_EQ_0_NUMSEG] THEN EXISTS_TAC `1`] THEN
  SIMP_TAC[mat; LAMBDA_BETA; COND_ID; DIMINDEX_GE_1; LE_REFL]);;

let DET_PERMUTE_ROWS = prove
 (`!A:real^N^N p.
        p permutes 1..dimindex(:N)
        ==> det(lambda i. A$p(i)) = sign(p) * det(A)`,
  REWRITE_TAC[det] THEN SIMP_TAC[LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[GSYM SUM_LMUL; FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
    [MATCH_MP SUM_PERMUTATIONS_COMPOSE_R th]) THEN
  MATCH_MP_TAC SUM_EQ THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN X_GEN_TAC `q:num->num` THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_MUL_ASSOC] THEN DISCH_TAC THEN BINOP_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_MESON_TAC[SIGN_COMPOSE; PERMUTATION_PERMUTES; FINITE_NUMSEG];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP PERMUTES_INVERSE (ASSUME `p permutes 1..dimindex(:N)`)) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV
    [MATCH_MP PRODUCT_PERMUTE_NUMSEG th]) THEN
  MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
  ASM_MESON_TAC[PERMUTES_INVERSES]);;

let DET_PERMUTE_COLUMNS = prove
 (`!A:real^N^N p.
        p permutes 1..dimindex(:N)
        ==> det((lambda i j. A$i$p(j)):real^N^N) = sign(p) * det(A)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (funpow 2 RAND_CONV) [GSYM DET_TRANSP] THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC
   [GSYM(MATCH_MP DET_PERMUTE_ROWS th)]) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM DET_TRANSP] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[CART_EQ; transp; LAMBDA_BETA; LAMBDA_BETA_PERM]);;

let DET_IDENTICAL_ROWS = prove
 (`!A:real^N^N i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j) /\
                    row i A = row j A
                    ==> det A = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`A:real^N^N`; `swap(i:num,j:num)`] DET_PERMUTE_ROWS) THEN
  ASM_SIMP_TAC[PERMUTES_SWAP; IN_NUMSEG; SIGN_SWAP] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> b = -- &1 * a ==> a = &0`) THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM(MP_TAC o SYM) THEN
  SIMP_TAC[row; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[swap] THEN ASM_MESON_TAC[]);;

let DET_IDENTICAL_COLUMNS = prove
 (`!A:real^N^N i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j) /\
                    column i A = column j A
                    ==> det A = &0`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM DET_TRANSP] THEN
  MATCH_MP_TAC DET_IDENTICAL_ROWS THEN ASM_MESON_TAC[ROW_TRANSP]);;

let DET_ZERO_ROW = prove
 (`!A:real^N^N i.
       1 <= i /\ i <= dimindex(:N) /\ row i A = vec 0  ==> det A = &0`,
  SIMP_TAC[det; row; CART_EQ; LAMBDA_BETA; VEC_COMPONENT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_0 THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_ENTIRE; SIGN_NZ] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[PRODUCT_EQ_0; FINITE_NUMSEG; IN_NUMSEG] THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]);;

let DET_ZERO_COLUMN = prove
 (`!A:real^N^N i.
       1 <= i /\ i <= dimindex(:N) /\ column i A = vec 0  ==> det A = &0`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM DET_TRANSP] THEN
  MATCH_MP_TAC DET_ZERO_ROW THEN ASM_MESON_TAC[ROW_TRANSP]);;

let DET_ROW_ADD = prove
 (`!a b c k.
         1 <= k /\ k <= dimindex(:N)
         ==> det((lambda i. if i = k then a + b else c i):real^N^N) =
             det((lambda i. if i = k then a else c i):real^N^N) +
             det((lambda i. if i = k then b else c i):real^N^N)`,
  SIMP_TAC[det; LAMBDA_BETA; GSYM SUM_ADD;
           FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN
  X_GEN_TAC `p:num->num` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `1..dimindex(:N) = k INSERT ((1..dimindex(:N)) DELETE k)`
  SUBST1_TAC THENL [ASM_MESON_TAC[INSERT_DELETE; IN_NUMSEG]; ALL_TAC] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; FINITE_NUMSEG; IN_DELETE] THEN
  MATCH_MP_TAC(REAL_RING
   `c = a + b /\ y = x:real /\ z = x ==> c * x = a * y + b * z`) THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT] THEN
  CONJ_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
  SIMP_TAC[IN_DELETE; FINITE_DELETE; FINITE_NUMSEG]);;

let DET_ROW_MUL = prove
 (`!a b c k.
        1 <= k /\ k <= dimindex(:N)
        ==> det((lambda i. if i = k then c % a else b i):real^N^N) =
            c * det((lambda i. if i = k then a else b i):real^N^N)`,
  SIMP_TAC[det; LAMBDA_BETA; GSYM SUM_LMUL;
           FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN
  X_GEN_TAC `p:num->num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `1..dimindex(:N) = k INSERT ((1..dimindex(:N)) DELETE k)`
  SUBST1_TAC THENL [ASM_MESON_TAC[INSERT_DELETE; IN_NUMSEG]; ALL_TAC] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; FINITE_NUMSEG; IN_DELETE] THEN
  MATCH_MP_TAC(REAL_RING
   `cp = c * p /\ p1 = p2:real ==> s * cp * p1 = c * s * p * p2`) THEN
  REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN MATCH_MP_TAC PRODUCT_EQ THEN
  SIMP_TAC[IN_DELETE; FINITE_DELETE; FINITE_NUMSEG]);;

let DET_ROW_OPERATION = prove
 (`!A:real^N^N i.
        1 <= i /\ i <= dimindex(:N) /\
        1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
        ==> det(lambda k. if k = i then row i A + c % row j A else row k A) =
            det A`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DET_ROW_ADD; DET_ROW_MUL] THEN
  MATCH_MP_TAC(REAL_RING `a = b /\ d = &0 ==> a + c * d = b`) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA; CART_EQ] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[row; LAMBDA_BETA; CART_EQ];
    MATCH_MP_TAC DET_IDENTICAL_ROWS THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN
    ASM_SIMP_TAC[row; LAMBDA_BETA; CART_EQ]]);;

let DET_ROW_SPAN = prove
 (`!A:real^N^N i x.
        1 <= i /\ i <= dimindex(:N) /\
        x IN span {row j A | 1 <= j /\ j <= dimindex(:N) /\ ~(j = i)}
        ==> det(lambda k. if k = i then row i A + x else row k A) =
            det A`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC SPAN_INDUCT_ALT THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_ADD_RID] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[row; LAMBDA_BETA];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `j:num`) (SUBST_ALL_TAC o SYM)) THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH
     `a + c % x + y:real^N = (a + y) + c % x`] THEN
  ABBREV_TAC `z = row i (A:real^N^N) + y` THEN
  ASM_SIMP_TAC[DET_ROW_MUL; DET_ROW_ADD] THEN
  MATCH_MP_TAC(REAL_RING `d = &0 ==> a + c * d = a`) THEN
  MATCH_MP_TAC DET_IDENTICAL_ROWS THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN
  ASM_SIMP_TAC[row; LAMBDA_BETA; CART_EQ]);;

(* ------------------------------------------------------------------------- *)
(* May as well do this, though it's a bit unsatisfactory since it ignores    *)
(* exact duplicates by considering the rows/columns as a set.                *)
(* ------------------------------------------------------------------------- *)

let DET_DEPENDENT_ROWS = prove
 (`!A:real^N^N. dependent(rows A) ==> det A = &0`,
  GEN_TAC THEN
  REWRITE_TAC[dependent; rows; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN GEN_TAC THEN X_GEN_TAC `i:num` THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_CASES_TAC
   `?i j. 1 <= i /\ i <= dimindex(:N) /\
          1 <= j /\ j <= dimindex(:N) /\ ~(i = j) /\
          row i (A:real^N^N) = row j A`
  THENL [ASM_MESON_TAC[DET_IDENTICAL_ROWS]; ALL_TAC] THEN
  MP_TAC(SPECL [`A:real^N^N`; `i:num`; `--(row i (A:real^N^N))`]
    DET_ROW_SPAN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SPAN_NEG THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN]) THEN
    MATCH_MP_TAC(TAUT `a = b ==> a ==> b`) THEN
    REWRITE_TAC[IN] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_DELETE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC DET_ZERO_ROW THEN
    EXISTS_TAC `i:num` THEN
    ASM_SIMP_TAC[row; LAMBDA_BETA; CART_EQ; VECTOR_ADD_COMPONENT;
                 VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    REAL_ARITH_TAC]);;

let DET_DEPENDENT_COLUMNS = prove
 (`!A:real^N^N. dependent(columns A) ==> det A = &0`,
  MESON_TAC[DET_DEPENDENT_ROWS; ROWS_TRANSP; DET_TRANSP]);;

(* ------------------------------------------------------------------------- *)
(* Multilinearity and the multiplication formula.                            *)
(* ------------------------------------------------------------------------- *)

let DET_LINEAR_ROW_VSUM = prove
 (`!a c s k.
         FINITE s /\ 1 <= k /\ k <= dimindex(:N)
         ==> det((lambda i. if i = k then vsum s a else c i):real^N^N) =
             sum s
               (\j. det((lambda i. if i = k then a(j) else c i):real^N^N))`,
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; SUM_CLAUSES; DET_ROW_ADD] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DET_ZERO_ROW THEN EXISTS_TAC `k:num` THEN
  ASM_SIMP_TAC[row; LAMBDA_BETA; CART_EQ; VEC_COMPONENT]);;

let BOUNDED_FUNCTIONS_BIJECTIONS_1 = prove
 (`!p. p IN {(y,g) | y IN s /\
                     g IN {f | (!i. 1 <= i /\ i <= k ==> f i IN s) /\
                               (!i. ~(1 <= i /\ i <= k) ==> f i = i)}}
       ==> (\(y,g) i. if i = SUC k then y else g(i)) p IN
             {f | (!i. 1 <= i /\ i <= SUC k ==> f i IN s) /\
                  (!i. ~(1 <= i /\ i <= SUC k) ==> f i = i)} /\
           (\h. h(SUC k),(\i. if i = SUC k then i else h(i)))
            ((\(y,g) i. if i = SUC k then y else g(i)) p) = p`,
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  CONV_TAC(REDEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`y:num`; `h:num->num`] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[LE];
    ASM_MESON_TAC[LE; ARITH_RULE `~(1 <= i /\ i <= SUC k) ==> ~(i = SUC k)`];
    REWRITE_TAC[PAIR_EQ; FUN_EQ_THM] THEN
    ASM_MESON_TAC[ARITH_RULE `~(SUC k <= k)`]]);;

let BOUNDED_FUNCTIONS_BIJECTIONS_2 = prove
 (`!h. h IN {f | (!i. 1 <= i /\ i <= SUC k ==> f i IN s) /\
                 (!i. ~(1 <= i /\ i <= SUC k) ==> f i = i)}
       ==> (\h. h(SUC k),(\i. if i = SUC k then i else h(i))) h IN
           {(y,g) | y IN s /\
                     g IN {f | (!i. 1 <= i /\ i <= k ==> f i IN s) /\
                               (!i. ~(1 <= i /\ i <= k) ==> f i = i)}} /\
           (\(y,g) i. if i = SUC k then y else g(i))
              ((\h. h(SUC k),(\i. if i = SUC k then i else h(i))) h) = h`,
  REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
  CONV_TAC(REDEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `h:num->num` THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ASM_MESON_TAC[ARITH_RULE `i <= k ==> i <= SUC k /\ ~(i = SUC k)`];
    ASM_MESON_TAC[ARITH_RULE `i <= SUC k /\ ~(i = SUC k) ==> i <= k`];
    REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[LE_REFL]]);;

let FINITE_BOUNDED_FUNCTIONS = prove
 (`!s k. FINITE s
         ==> FINITE {f | (!i. 1 <= i /\ i <= k ==> f(i) IN s) /\
                         (!i. ~(1 <= i /\ i <= k) ==> f(i) = i)}`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `~(1 <= i /\ i <= 0)`] THEN
    SIMP_TAC[GSYM FUN_EQ_THM; SET_RULE `{x | x = y} = {y}`; FINITE_RULES];
    ALL_TAC] THEN
  UNDISCH_TAC `FINITE(s:num->bool)` THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_PRODUCT) THEN
  DISCH_THEN(MP_TAC o ISPEC `\(y:num,g) i. if i = SUC k then y else g(i)` o
                      MATCH_MP FINITE_IMAGE) THEN
  MATCH_MP_TAC(TAUT `a = b ==> a ==> b`) THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
  X_GEN_TAC `h:num->num` THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_SIMP_TAC[BOUNDED_FUNCTIONS_BIJECTIONS_1]; ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC
    `(\h. h(SUC k),(\i. if i = SUC k then i else h(i))) h` THEN
  PURE_ONCE_REWRITE_TAC[CONJ_SYM] THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
  MATCH_MP_TAC BOUNDED_FUNCTIONS_BIJECTIONS_2 THEN ASM_REWRITE_TAC[]);;

let DET_LINEAR_ROWS_VSUM_LEMMA = prove
 (`!s k a c.
         FINITE s /\ k <= dimindex(:N)
         ==> det((lambda i. if i <= k then vsum s (a i) else c i):real^N^N) =
             sum {f | (!i. 1 <= i /\ i <= k ==> f(i) IN s) /\
                      !i. ~(1 <= i /\ i <= k) ==> f(i) = i}
                 (\f. det((lambda i. if i <= k then a i (f i) else c i)
                          :real^N^N))`,
  let lemma = prove
   (`(lambda i. if i <= 0 then x(i) else y(i)) = (lambda i. y i)`,
    SIMP_TAC[CART_EQ; ARITH; LAMBDA_BETA; ARITH_RULE
                 `1 <= k ==> ~(k <= 0)`]) in
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[lemma; LE_0] THEN GEN_TAC THEN
    REWRITE_TAC[ARITH_RULE `~(1 <= i /\ i <= 0)`] THEN
    REWRITE_TAC[GSYM FUN_EQ_THM; SET_RULE `{x | x = y} = {y}`] THEN
    REWRITE_TAC[SUM_SING];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC k <= n ==> k <= n`] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [LE] THEN
  REWRITE_TAC[TAUT
   `(if a \/ b then c else d) = (if a then c else if b then c else d)`] THEN
  ASM_SIMP_TAC[DET_LINEAR_ROW_VSUM; ARITH_RULE `1 <= SUC k`] THEN
  ONCE_REWRITE_TAC[TAUT
    `(if a then b else if c then d else e) =
     (if c then (if a then b else d) else (if a then b else e))`] THEN
  ASM_SIMP_TAC[ARITH_RULE `i <= k ==> ~(i = SUC k)`] THEN
  ASM_SIMP_TAC[SUM_SUM_PRODUCT; FINITE_BOUNDED_FUNCTIONS] THEN
  MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
  EXISTS_TAC `\(y:num,g) i. if i = SUC k then y else g(i)` THEN
  EXISTS_TAC `\h. h(SUC k),(\i. if i = SUC k then i else h(i))` THEN
  CONJ_TAC THENL [ACCEPT_TAC BOUNDED_FUNCTIONS_BIJECTIONS_2; ALL_TAC] THEN
  X_GEN_TAC `p:num#(num->num)` THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP BOUNDED_FUNCTIONS_BIJECTIONS_1) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`p:num#(num->num)`,`q:num#(num->num)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  MAP_EVERY X_GEN_TAC [`y:num`; `g:num->num`] THEN AP_TERM_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_MESON_TAC[LE; ARITH_RULE `~(SUC k <= k)`]);;

let DET_LINEAR_ROWS_VSUM = prove
 (`!s a.
         FINITE s
         ==> det((lambda i. vsum s (a i)):real^N^N) =
             sum {f | (!i. 1 <= i /\ i <= dimindex(:N) ==> f(i) IN s) /\
                      !i. ~(1 <= i /\ i <= dimindex(:N)) ==> f(i) = i}
                 (\f. det((lambda i. a i (f i)):real^N^N))`,
  let lemma = prove
   (`(lambda i. if i <= dimindex(:N) then x(i) else y(i)):real^N^N =
     (lambda i. x(i))`,
    SIMP_TAC[CART_EQ; LAMBDA_BETA]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:num->bool`; `dimindex(:N)`] DET_LINEAR_ROWS_VSUM_LEMMA) THEN
  ASM_REWRITE_TAC[LE_REFL; lemma] THEN SIMP_TAC[]);;

let MATRIX_MUL_VSUM_ALT = prove
 (`!A:real^N^N B:real^N^N. A ** B =
                  lambda i. vsum (1..dimindex(:N)) (\k. A$i$k % B$k)`,
  SIMP_TAC[matrix_mul; CART_EQ; LAMBDA_BETA; VECTOR_MUL_COMPONENT;
           VSUM_COMPONENT]);;

let DET_ROWS_MUL = prove
 (`!a c. det((lambda i. c(i) % a(i)):real^N^N) =
         product(1..dimindex(:N)) (\i. c(i)) *
         det((lambda i. a(i)):real^N^N)`,
  REPEAT GEN_TAC THEN SIMP_TAC[det; LAMBDA_BETA] THEN
  SIMP_TAC[GSYM SUM_LMUL; FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN
  X_GEN_TAC `p:num->num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_RING `b = c * d ==> s * b = c * s * d`) THEN
  SIMP_TAC[GSYM PRODUCT_MUL_NUMSEG] THEN
  MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG; VECTOR_MUL_COMPONENT]);;

let DET_MUL = prove
 (`!A B:real^N^N. det(A ** B) = det(A) * det(B)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MATRIX_MUL_VSUM_ALT] THEN
  SIMP_TAC[DET_LINEAR_ROWS_VSUM; FINITE_NUMSEG] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {p | p permutes 1..dimindex(:N)}
            (\f. det (lambda i. (A:real^N^N)$i$f i % (B:real^N^N)$f i))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[DET_ROWS_MUL] THEN
    MATCH_MP_TAC SUM_SUPERSET THEN
    SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MESON_TAC[permutes; IN_NUMSEG]; ALL_TAC] THEN
    X_GEN_TAC `f:num->num` THEN REWRITE_TAC[permutes; IN_NUMSEG] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
    MATCH_MP_TAC DET_IDENTICAL_ROWS THEN
    MP_TAC(ISPECL [`1..dimindex(:N)`; `f:num->num`]
       SURJECTIVE_IFF_INJECTIVE) THEN
    ASM_REWRITE_TAC[SUBSET; IN_NUMSEG; FINITE_NUMSEG; FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC(TAUT `(~b ==> c) /\ (b ==> ~a) ==> (a <=> b) ==> c`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NOT_FORALL_THM] THEN
      REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      SIMP_TAC[CART_EQ; LAMBDA_BETA; row; NOT_IMP];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `!x y. (f:num->num)(x) = f(y) ==> x = y` ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN
      ASM_CASES_TAC `1 <= x /\ x <= dimindex(:N)` THEN
      ASM_CASES_TAC `1 <= y /\ y <= dimindex(:N)` THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[det; REAL_MUL_SUM; FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN
  X_GEN_TAC `p:num->num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
    [MATCH_MP SUM_PERMUTATIONS_COMPOSE_R (MATCH_MP PERMUTES_INVERSE th)]) THEN
  MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN
  X_GEN_TAC `q:num->num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM] THEN ONCE_REWRITE_TAC[AC REAL_MUL_AC
   `(p * x) * (q * y) = (p * q) * (x * y)`] THEN
  BINOP_TAC THENL
   [SUBGOAL_THEN `sign(q o inverse p) = sign(p:num->num) * sign(q:num->num)`
     (fun t -> SIMP_TAC[REAL_MUL_ASSOC; SIGN_IDEMPOTENT; REAL_MUL_LID; t]) THEN
    ASM_MESON_TAC[SIGN_COMPOSE; PERMUTES_INVERSE; PERMUTATION_PERMUTES;
                  FINITE_NUMSEG; SIGN_INVERSE; REAL_MUL_SYM];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [MATCH_MP PRODUCT_PERMUTE_NUMSEG (ASSUME `p permutes 1..dimindex(:N)`)] THEN
  SIMP_TAC[GSYM PRODUCT_MUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
  ASM_SIMP_TAC[LAMBDA_BETA; LAMBDA_BETA_PERM; o_THM] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(A:real^N^N)$i$p(i) * (B:real^N^N)$p(i)$q(i)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[VECTOR_MUL_COMPONENT; PERMUTES_IN_IMAGE; IN_NUMSEG];
    ASM_MESON_TAC[PERMUTES_INVERSES]]);;

let DET_LINEAR_ROWS = prove
 (`!f:real^N->real^N A:real^N^N.
        linear f ==> det(lambda i. f(A$i)) = det(matrix f) * det A`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM DET_TRANSP] THEN
  REWRITE_TAC[GSYM DET_MUL] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM DET_TRANSP] THEN
  REWRITE_TAC[matrix_mul; matrix_vector_mul; transp] THEN
  AP_TERM_TAC THEN SIMP_TAC[CART_EQ; LAMBDA_BETA]);;

(* ------------------------------------------------------------------------- *)
(* Relation to invertibility.                                                *)
(* ------------------------------------------------------------------------- *)

let INVERTIBLE_DET_NZ = prove
 (`!A:real^N^N. invertible(A) <=> ~(det A = &0)`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[INVERTIBLE_RIGHT_INVERSE; LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `det:real^N^N->real`) THEN
    REWRITE_TAC[DET_MUL; DET_I] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[INVERTIBLE_RIGHT_INVERSE] THEN
  REWRITE_TAC[MATRIX_RIGHT_INVERTIBLE_INDEPENDENT_ROWS] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:num->real`; `i:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`A:real^N^N`; `i:num`; `--(row i (A:real^N^N))`]
    DET_ROW_SPAN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
      `--(row i (A:real^N^N)) =
       vsum ((1..dimindex(:N)) DELETE i) (\j. inv(c i) % c j % row j A)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[VSUM_DELETE_CASES; FINITE_NUMSEG; IN_NUMSEG; VSUM_LMUL] THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SPAN_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; FINITE_DELETE; IN_DELETE] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REPEAT(MATCH_MP_TAC SPAN_MUL) THEN
    MATCH_MP_TAC(CONJUNCT1 SPAN_CLAUSES) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC DET_ZERO_ROW THEN
  EXISTS_TAC `i:num` THEN
  ASM_SIMP_TAC[row; CART_EQ; LAMBDA_BETA; VEC_COMPONENT;
               VECTOR_ARITH `x + --x:real^N = vec 0`]);;

let DET_EQ_0 = prove
 (`!A:real^N^N. det(A) = &0 <=> ~invertible(A)`,
  REWRITE_TAC[INVERTIBLE_DET_NZ]);;

let DET_MATRIX_INV = prove
 (`!A:real^N^N. det(matrix_inv A) = inv(det A)`,
  GEN_TAC THEN ASM_CASES_TAC `invertible(A:real^N^N)` THENL
   [MATCH_MP_TAC(REAL_FIELD `a * b = &1 ==> a = inv b`) THEN
    ASM_SIMP_TAC[GSYM DET_MUL; MATRIX_INV; DET_I];
    ASM_MESON_TAC[DET_EQ_0; INVERTIBLE_MATRIX_INV; REAL_INV_0]]);;

let MATRIX_MUL_LINV = prove
 (`!A:real^N^N. ~(det A = &0) ==> matrix_inv A ** A = mat 1`,
  SIMP_TAC[MATRIX_INV; DET_EQ_0]);;

let MATRIX_MUL_RINV = prove
 (`!A:real^N^N. ~(det A = &0) ==> A ** matrix_inv A = mat 1`,
  SIMP_TAC[MATRIX_INV; DET_EQ_0]);;

let DET_MATRIX_EQ_0 = prove
 (`!f:real^N->real^N.
        linear f
        ==> (det(matrix f) = &0 <=>
             ~(?g. linear g /\ f o g = I /\ g o f = I))`,
  SIMP_TAC[DET_EQ_0; MATRIX_INVERTIBLE]);;

let DET_MATRIX_EQ_0_LEFT = prove
 (`!f:real^N->real^N.
        linear f
        ==> (det(matrix f) = &0 <=>
             ~(?g. linear g /\ g o f = I))`,
   SIMP_TAC[DET_MATRIX_EQ_0] THEN MESON_TAC[LINEAR_INVERSE_LEFT]);;

let DET_MATRIX_EQ_0_RIGHT = prove
 (`!f:real^N->real^N.
        linear f
        ==> (det(matrix f) = &0 <=>
             ~(?g. linear g /\ f o g = I))`,
   SIMP_TAC[DET_MATRIX_EQ_0] THEN MESON_TAC[LINEAR_INVERSE_LEFT]);;

let DET_EQ_0_RANK = prove
 (`!A:real^N^N. det A = &0 <=> rank A < dimindex(:N)`,
  REWRITE_TAC[DET_EQ_0; INVERTIBLE_LEFT_INVERSE; GSYM FULL_RANK_INJECTIVE;
              MATRIX_LEFT_INVERTIBLE_INJECTIVE] THEN
  GEN_TAC THEN MP_TAC(ISPEC `A:real^N^N` RANK_BOUND) THEN
  ARITH_TAC);;

let RANK_EQ_FULL_DET = prove
 (`!A:real^N^N. rank A = dimindex(:N) <=> ~(det A = &0)`,
  GEN_TAC THEN MP_TAC(ISPEC `A:real^N^N` RANK_BOUND) THEN
  SIMP_TAC[DET_EQ_0_RANK; NOT_LT; GSYM LE_ANTISYM; ARITH_RULE `MIN n n = n`]);;

let INVERTIBLE_COVARIANCE_RANK = prove
 (`!A:real^N^M. invertible(transp A ** A) <=> rank A = dimindex(:N)`,
  REWRITE_TAC[INVERTIBLE_DET_NZ; GSYM RANK_EQ_FULL_DET; RANK_GRAM]);;

let HOMOGENEOUS_LINEAR_EQUATIONS_DET = prove
 (`!A:real^N^N. (?x. ~(x = vec 0) /\ A ** x = vec 0) <=> det A = &0`,
  GEN_TAC THEN
  REWRITE_TAC[MATRIX_NONFULL_LINEAR_EQUATIONS_EQ; DET_EQ_0_RANK] THEN
  MATCH_MP_TAC(ARITH_RULE `r <= MIN N N ==> (~(r = N) <=> r < N)`) THEN
  REWRITE_TAC[RANK_BOUND]);;

let INVERTIBLE_MATRIX_MUL = prove
 (`!A:real^N^N B:real^N^N.
        invertible(A ** B) <=> invertible A /\ invertible B`,
  REWRITE_TAC[INVERTIBLE_DET_NZ; DET_MUL; DE_MORGAN_THM; REAL_ENTIRE]);;

let MATRIX_INV_MUL = prove
 (`!A:real^N^N B:real^N^N.
        invertible A /\ invertible B
        ==> matrix_inv(A ** B) = matrix_inv B ** matrix_inv A`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
  ONCE_REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o LAND_CONV)
   [GSYM MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_MUL_LINV; DET_EQ_0; MATRIX_MUL_RID; MATRIX_MUL_RINV]);;

let DET_SIMILAR = prove
 (`!S:real^N^N A. invertible S ==> det(matrix_inv S ** A ** S) = det A`,
  REWRITE_TAC[INVERTIBLE_DET_NZ; DET_MUL; DET_MATRIX_INV] THEN
  CONV_TAC REAL_FIELD);;

let INVERTIBLE_NEARBY_ONORM = prove
 (`!A B:real^N^N.
        invertible A /\
        onorm(\x. (B - A) ** x) < inv(onorm(\x. matrix_inv A ** x))
        ==> invertible B`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM ONORM_NEG] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_LNEG; MATRIX_NEG_SUB] THEN DISCH_TAC THEN
  ABBREV_TAC `S = matrix_inv(A:real^N^N) ** (A - B)` THEN
  SUBGOAL_THEN `B = (A:real^N^N) ** (mat 1 - S:real^N^N)` SUBST1_TAC THENL
   [EXPAND_TAC "S" THEN
    REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_RID; MATRIX_MUL_LID] THEN
    REWRITE_TAC[MATRIX_SUB; MATRIX_NEG_ADD] THEN
    REWRITE_TAC[MATRIX_ADD_RNEG; MATRIX_ADD_ASSOC; MATRIX_ADD_LID] THEN
    REWRITE_TAC[MATRIX_NEG_NEG];
    ASM_REWRITE_TAC[INVERTIBLE_MATRIX_MUL]] THEN
  REWRITE_TAC[INVERTIBLE_LEFT_INVERSE; MATRIX_LEFT_INVERTIBLE_KER] THEN
  X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; VECTOR_SUB_EQ] THEN
  CONV_TAC(LAND_CONV SYM_CONV) THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN
  DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\x:real^N. matrix_inv(A:real^N^N) ** x`;
    `\x:real^N. (A - B:real^N^N) ** x`]
   ONORM_COMPOSE) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_LINEAR; o_DEF; MATRIX_VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN TRANS_TAC REAL_LTE_TRANS `&1` THEN
  CONJ_TAC THENL
    [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
     W(MP_TAC o PART_MATCH (rand o rand) REAL_LT_RDIV_EQ o snd) THEN
     ASM_REWRITE_TAC[real_div; REAL_MUL_LID] THEN
     DISCH_THEN MATCH_MP_TAC THEN
     SIMP_TAC[ONORM_POS_LT; MATRIX_VECTOR_MUL_LINEAR] THEN
     REWRITE_TAC[GSYM MATRIX_EQ_0; MATRIX_INV_EQ_0] THEN
     ASM_MESON_TAC[INVERTIBLE_MAT];
     MP_TAC(ISPEC `\x:real^N. (S:real^N^N) ** x` ONORM) THEN
     REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
     DISCH_THEN(MP_TAC o SPEC `x:real^N` o CONJUNCT1) THEN
     ASM_REWRITE_TAC[] THEN
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM REAL_MUL_LID] THEN
     ASM_SIMP_TAC[REAL_LE_RMUL_EQ; NORM_POS_LT]]);;

let INVERTIBLE_NEARBY = prove
 (`!A:real^N^N.
        invertible A
        ==> ?e. &0 < e /\ !B. onorm(\x. (B - A) ** x) < e ==> invertible B`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `inv(onorm(\x. matrix_inv(A:real^N^N) ** x))` THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[INVERTIBLE_NEARBY_ONORM]] THEN
  SIMP_TAC[REAL_LT_INV_EQ; ONORM_POS_LT; MATRIX_VECTOR_MUL_LINEAR] THEN
  REWRITE_TAC[GSYM MATRIX_EQ_0; MATRIX_INV_EQ_0] THEN
  ASM_MESON_TAC[INVERTIBLE_MAT]);;

(* ------------------------------------------------------------------------- *)
(* Cramer's rule.                                                            *)
(* ------------------------------------------------------------------------- *)

let CRAMER_LEMMA_TRANSP = prove
 (`!A:real^N^N x:real^N.
        1 <= k /\ k <= dimindex(:N)
        ==> det((lambda i. if i = k
                           then vsum(1..dimindex(:N)) (\i. x$i % row i A)
                           else row i A):real^N^N) =
            x$k * det A`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1..dimindex(:N) = k INSERT ((1..dimindex(:N)) DELETE k)`
  SUBST1_TAC THENL [ASM_MESON_TAC[INSERT_DELETE; IN_NUMSEG]; ALL_TAC] THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_NUMSEG; FINITE_DELETE; IN_DELETE] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(x:real^N)$k % row k (A:real^N^N) + s =
    (x$k - &1) % row k A + row k A + s`] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) DET_ROW_ADD o lhand o snd) THEN
  ASM_SIMP_TAC[DET_ROW_MUL] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC(REAL_RING `d = d' /\ e = d' ==> (c - &1) * d + e = c * d'`) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA; row];
    MATCH_MP_TAC DET_ROW_SPAN THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SPAN_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; FINITE_DELETE; IN_DELETE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC(CONJUNCT1 SPAN_CLAUSES) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

let CRAMER_LEMMA = prove
 (`!A:real^N^N x:real^N.
        1 <= k /\ k <= dimindex(:N)
        ==> det((lambda i j. if j = k then (A**x)$i else A$i$j):real^N^N) =
            x$k * det(A)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MATRIX_MUL_VSUM] THEN
  FIRST_ASSUM(MP_TAC o SYM o SPECL [`transp(A:real^N^N)`; `x:real^N`] o
              MATCH_MP CRAMER_LEMMA_TRANSP) THEN
  REWRITE_TAC[DET_TRANSP] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM DET_TRANSP] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[CART_EQ; transp; LAMBDA_BETA; MATRIX_MUL_VSUM; row; column;
        COND_COMPONENT; VECTOR_MUL_COMPONENT; VSUM_COMPONENT]);;

let CRAMER = prove
 (`!A:real^N^N x b.
        ~(det(A) = &0)
        ==> (A ** x = b <=>
             x = lambda k.
                   det((lambda i j. if j = k then b$i else A$i$j):real^N^N) /
                   det(A))`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC(MESON[]
   `(?x. p(x)) /\ (!x. p(x) ==> x = a) ==> !x. p(x) <=> x = a`) THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `A:real^N^N` INVERTIBLE_DET_NZ) THEN
    ASM_MESON_TAC[invertible; MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[CART_EQ; CRAMER_LEMMA; LAMBDA_BETA; REAL_FIELD
    `~(z = &0) ==> (x = y / z <=> x * z = y)`]]);;

(* ------------------------------------------------------------------------- *)
(* Variants of Cramer's rule for matrix-matrix multiplication.               *)
(* ------------------------------------------------------------------------- *)

let CRAMER_MATRIX_LEFT = prove
 (`!A:real^N^N X:real^N^N B:real^N^N.
        ~(det A = &0)
        ==> (X ** A = B <=>
             X = lambda k l.
                   det((lambda i j. if j = l then B$k$i else A$j$i):real^N^N) /
                   det A)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CART_EQ] THEN
  ASM_SIMP_TAC[MATRIX_MUL_COMPONENT; CRAMER; DET_TRANSP] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
  REPLICATE_TAC 2 (AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC) THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; transp]);;

let CRAMER_MATRIX_RIGHT = prove
 (`!A:real^N^N X:real^N^N B:real^N^N.
        ~(det A = &0)
        ==> (A ** X = B <=>
             X = lambda k l.
                   det((lambda i j. if j = k then B$i$l else A$i$j):real^N^N) /
                   det A)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM TRANSP_EQ] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL] THEN
  ASM_SIMP_TAC[CRAMER_MATRIX_LEFT; DET_TRANSP] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM TRANSP_EQ] THEN
  REWRITE_TAC[TRANSP_TRANSP] THEN AP_TERM_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; transp] THEN
  REPEAT(GEN_TAC THEN STRIP_TAC) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; transp]);;

let CRAMER_MATRIX_RIGHT_INVERSE = prove
 (`!A:real^N^N A':real^N^N.
        A ** A' = mat 1 <=>
        ~(det A = &0) /\
        A' = lambda k l.
                det((lambda i j. if j = k then if i = l then &1 else &0
                                 else A$i$j):real^N^N) /
                det A`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `det(A:real^N^N) = &0` THENL
   [ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `det:real^N^N->real`) THEN
    ASM_REWRITE_TAC[DET_MUL; DET_I] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[CRAMER_MATRIX_RIGHT] THEN AP_TERM_TAC THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
    REPEAT(GEN_TAC THEN STRIP_TAC) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; mat]]);;

let CRAMER_MATRIX_LEFT_INVERSE = prove
 (`!A:real^N^N A':real^N^N.
        A' ** A = mat 1 <=>
        ~(det A = &0) /\
        A' = lambda k l.
                det((lambda i j. if j = l then if i = k then &1 else &0
                                 else A$j$i):real^N^N) /
                det A`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `det(A:real^N^N) = &0` THENL
   [ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `det:real^N^N->real`) THEN
    ASM_REWRITE_TAC[DET_MUL; DET_I] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[CRAMER_MATRIX_LEFT] THEN AP_TERM_TAC THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
    REPEAT(GEN_TAC THEN STRIP_TAC) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; mat] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Cofactors and their relationship to inverse matrices.                     *)
(* ------------------------------------------------------------------------- *)

let cofactor = new_definition
  `(cofactor:real^N^N->real^N^N) A =
        lambda i j. det((lambda k l. if k = i /\ l = j then &1
                                     else if k = i \/ l = j then &0
                                     else A$k$l):real^N^N)`;;

let COFACTOR_TRANSP = prove
 (`!A:real^N^N. cofactor(transp A) = transp(cofactor A)`,
  SIMP_TAC[cofactor; CART_EQ; LAMBDA_BETA; transp] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM DET_TRANSP] THEN
  AP_TERM_TAC THEN SIMP_TAC[cofactor; CART_EQ; LAMBDA_BETA; transp] THEN
  MESON_TAC[]);;

let COFACTOR_COLUMN = prove
 (`!A:real^N^N.
        cofactor A =
        lambda i j. det((lambda k l. if l = j then if k = i then &1 else &0
                                     else A$k$l):real^N^N)`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN
  SIMP_TAC[cofactor; CART_EQ; LAMBDA_BETA] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[det] THEN MATCH_MP_TAC SUM_EQ THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN GEN_TAC THEN
  DISCH_TAC THEN AP_TERM_TAC THEN
  ASM_CASES_TAC `(p:num->num) i = j` THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN
    X_GEN_TAC `k:num` THEN SIMP_TAC[IN_NUMSEG; LAMBDA_BETA] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(p:num->num) k IN 1..dimindex(:N)` MP_TAC THENL
     [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG];
      SIMP_TAC[LAMBDA_BETA; IN_NUMSEG] THEN STRIP_TAC] THEN
    ASM_CASES_TAC `(p:num->num) k = j` THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC(REAL_ARITH `s = &0 /\ t = &0 ==> s = t`) THEN
    ASM_SIMP_TAC[PRODUCT_EQ_0; FINITE_NUMSEG] THEN CONJ_TAC THEN
    EXISTS_TAC `inverse (p:num->num) j` THEN
    ASM_SIMP_TAC[IN_NUMSEG; LAMBDA_BETA] THEN
    (SUBGOAL_THEN `inverse(p:num->num) j IN 1..dimindex(:N)` MP_TAC THENL
      [ASM_MESON_TAC[PERMUTES_IN_IMAGE; PERMUTES_INVERSE; IN_NUMSEG];
       SIMP_TAC[LAMBDA_BETA; IN_NUMSEG] THEN STRIP_TAC] THEN
     SUBGOAL_THEN `(p:num->num)(inverse p j) = j` SUBST1_TAC THENL
      [ASM_MESON_TAC[PERMUTES_INVERSES; IN_NUMSEG];
       ASM_SIMP_TAC[LAMBDA_BETA] THEN
        ASM_MESON_TAC[PERMUTES_INVERSE_EQ]])]);;

let COFACTOR_ROW = prove
 (`!A:real^N^N.
        cofactor A =
        lambda i j. det((lambda k l. if k = i then if l = j then &1 else &0
                                     else A$k$l):real^N^N)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM TRANSP_EQ] THEN
  REWRITE_TAC[GSYM COFACTOR_TRANSP] THEN
  SIMP_TAC[COFACTOR_COLUMN; CART_EQ; LAMBDA_BETA; transp] THEN
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM DET_TRANSP] THEN
  AP_TERM_TAC THEN SIMP_TAC[cofactor; CART_EQ; LAMBDA_BETA; transp]);;

let MATRIX_RIGHT_INVERSE_COFACTOR = prove
 (`!A:real^N^N A':real^N^N.
        A ** A' = mat 1 <=>
        ~(det A = &0) /\ A' = inv(det A) %% transp(cofactor A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CRAMER_MATRIX_RIGHT_INVERSE] THEN
  ASM_CASES_TAC `det(A:real^N^N) = &0` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_CMUL_COMPONENT] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[transp; COFACTOR_COLUMN; LAMBDA_BETA] THEN
  AP_TERM_TAC THEN SIMP_TAC[CART_EQ; LAMBDA_BETA]);;

let MATRIX_LEFT_INVERSE_COFACTOR = prove
 (`!A:real^N^N A':real^N^N.
        A' ** A = mat 1 <=>
        ~(det A = &0) /\ A' = inv(det A) %% transp(cofactor A)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[MATRIX_LEFT_RIGHT_INVERSE] THEN
  REWRITE_TAC[MATRIX_RIGHT_INVERSE_COFACTOR]);;

let MATRIX_INV_COFACTOR = prove
 (`!A. ~(det A = &0) ==> matrix_inv A = inv(det A) %% transp(cofactor A)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MATRIX_MUL_LINV) THEN
  SIMP_TAC[MATRIX_LEFT_INVERSE_COFACTOR]);;

let COFACTOR_MATRIX_INV = prove
 (`!A:real^N^N. ~(det A = &0) ==> cofactor A = det(A) %% transp(matrix_inv A)`,
  SIMP_TAC[MATRIX_INV_COFACTOR; TRANSP_MATRIX_CMUL; TRANSP_TRANSP] THEN
  SIMP_TAC[MATRIX_CMUL_ASSOC; REAL_MUL_RINV; MATRIX_CMUL_LID]);;

let COFACTOR_I = prove
 (`cofactor(mat 1:real^N^N) = mat 1`,
  SIMP_TAC[COFACTOR_MATRIX_INV; DET_I; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[MATRIX_INV_I; MATRIX_CMUL_LID; TRANSP_MAT]);;

let DET_COFACTOR_EXPANSION = prove
 (`!A:real^N^N i.
        1 <= i /\ i <= dimindex(:N)
        ==> det A = sum (1..dimindex(:N))
                        (\j. A$i$j * (cofactor A)$i$j)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COFACTOR_COLUMN; LAMBDA_BETA; det] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o rand o snd) THEN
  ANTS_TAC THENL [SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
  GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * s * p:real = s * a * p`] THEN
  REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum (1..dimindex (:N))
        (\j. (A:real^N^N)$i$j *
             product
              (inverse p j INSERT ((1..dimindex(:N)) DELETE (inverse p j)))
              (\k. if k = inverse p j then if k = i then &1 else &0
                   else A$k$(p k)))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; FINITE_PERMUTATIONS;
             FINITE_NUMSEG; IN_DELETE] THEN
    SUBGOAL_THEN `!j. inverse (p:num->num) j = i <=> j = p i`
     (fun th -> REWRITE_TAC[th])
    THENL [ASM_MESON_TAC[PERMUTES_INVERSES; IN_NUMSEG]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `x * (if p then &1 else &0) * y = if p then x * y else &0`] THEN
    SIMP_TAC[SUM_DELTA] THEN COND_CASES_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]] THEN
    SUBGOAL_THEN
     `1..dimindex(:N) = i INSERT ((1..dimindex(:N)) DELETE i)`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
    THENL
     [ASM_SIMP_TAC[IN_NUMSEG; SET_RULE `s = x INSERT (s DELETE x) <=> x IN s`];
      SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; FINITE_NUMSEG; IN_DELETE] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC(MESON[PRODUCT_EQ]
       `s = t /\ (!x. x IN t ==> f x = g x) ==> product s f = product t g`) THEN
      SIMP_TAC[IN_DELETE] THEN ASM_MESON_TAC[PERMUTES_INVERSES; IN_NUMSEG]];
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC(MESON[PRODUCT_EQ]
     `s = t /\ (!x. x IN t ==> f x = g x) ==> product s f = product t g`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SET_RULE `x INSERT (s DELETE x) = s <=> x IN s`] THEN
      ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG; PERMUTES_INVERSE];
      X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(p:num->num) k IN 1..dimindex(:N)` MP_TAC THENL
       [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
      SIMP_TAC[LAMBDA_BETA; IN_NUMSEG] THEN
      ASM_MESON_TAC[PERMUTES_INVERSES; IN_NUMSEG]]]);;

let MATRIX_MUL_RIGHT_COFACTOR = prove
 (`!A:real^N^N. A ** transp(cofactor A) = det(A) %% mat 1`,
  GEN_TAC THEN
  SIMP_TAC[CART_EQ; MATRIX_CMUL_COMPONENT; mat;
           matrix_mul; LAMBDA_BETA; transp] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `i':num` THEN STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[GSYM DET_COFACTOR_EXPANSION; REAL_MUL_RID] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `det((lambda k l. if k = i' then (A:real^N^N)$i$l
                               else A$k$l):real^N^N)` THEN
  CONJ_TAC THENL
   [MP_TAC(GEN `A:real^N^N`
     (ISPECL [`A:real^N^N`; `i':num`] DET_COFACTOR_EXPANSION)) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[cofactor; LAMBDA_BETA] THEN AP_TERM_TAC THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN ASM_MESON_TAC[];
    REWRITE_TAC[REAL_MUL_RZERO] THEN MATCH_MP_TAC DET_IDENTICAL_ROWS THEN
    MAP_EVERY EXISTS_TAC [`i:num`;` i':num`] THEN
    ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; row]]);;

let MATRIX_MUL_LEFT_COFACTOR = prove
 (`!A:real^N^N. transp(cofactor A) ** A = det(A) %% mat 1`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM TRANSP_EQ] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL] THEN
  ONCE_REWRITE_TAC[GSYM COFACTOR_TRANSP] THEN
  REWRITE_TAC[MATRIX_MUL_RIGHT_COFACTOR; TRANSP_MATRIX_CMUL] THEN
  REWRITE_TAC[DET_TRANSP; TRANSP_MAT]);;

let COFACTOR_CMUL = prove
 (`!A:real^N^N c. cofactor(c %% A) = c pow (dimindex(:N) - 1) %% cofactor A`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CART_EQ; cofactor; LAMBDA_BETA; MATRIX_CMUL_COMPONENT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[det; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
  X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * b * c:real = b * a * c`] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `1..dimindex (:N) = i INSERT ((1..dimindex (:N)) DELETE i)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_NUMSEG; IN_DELETE] THEN ASM_ARITH_TAC;
    SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; FINITE_NUMSEG; IN_DELETE]] THEN
  SUBGOAL_THEN
   `1 <= (p:num->num) i /\ p i <= dimindex(:N)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PERMUTES_IMAGE) THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_NUMSEG] THEN ASM SET_TAC[];
    ASM_SIMP_TAC[LAMBDA_BETA]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  SUBGOAL_THEN
   `dimindex(:N) - 1 = CARD((1..dimindex(:N)) DELETE i)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[CARD_DELETE; FINITE_NUMSEG; IN_NUMSEG; CARD_NUMSEG_1];
    ASM_SIMP_TAC[REAL_MUL_LID; GSYM PRODUCT_CONST; FINITE_NUMSEG;
                 FINITE_DELETE; GSYM PRODUCT_MUL]] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_DELETE; IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `1 <= (p:num->num) k /\ p k <= dimindex(:N)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PERMUTES_IMAGE) THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_NUMSEG] THEN ASM SET_TAC[];
    ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC]);;

let COFACTOR_0 = prove
 (`cofactor(mat 0:real^N^N) = if dimindex(:N) = 1 then mat 1 else mat 0`,
  MP_TAC(ISPECL [`mat 1:real^N^N`; `&0`] COFACTOR_CMUL) THEN
  REWRITE_TAC[MATRIX_CMUL_LZERO; COFACTOR_I; REAL_POW_ZERO] THEN
  DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> (n - 1 = 0 <=> n = 1)`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[MATRIX_CMUL_LZERO; MATRIX_CMUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Explicit formulas for low dimensions.                                     *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_1 = prove
 (`product(1..1) f = f(1)`,
  REWRITE_TAC[PRODUCT_SING_NUMSEG]);;

let PRODUCT_2 = prove
 (`!t. product(1..2) t = t(1) * t(2)`,
  REWRITE_TAC[num_CONV `2`; PRODUCT_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[PRODUCT_SING_NUMSEG; ARITH; REAL_MUL_ASSOC]);;

let PRODUCT_3 = prove
 (`!t. product(1..3) t = t(1) * t(2) * t(3)`,
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; PRODUCT_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[PRODUCT_SING_NUMSEG; ARITH; REAL_MUL_ASSOC]);;

let PRODUCT_4 = prove
 (`!t. product(1..4) t = t(1) * t(2) * t(3) * t(4)`,
  REWRITE_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`;
              PRODUCT_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[PRODUCT_SING_NUMSEG; ARITH; REAL_MUL_ASSOC]);;

let DET_1_GEN = prove
 (`!A:real^N^N. dimindex(:N) = 1 ==> det A = A$1$1`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[det; PERMUTES_SING; NUMSEG_SING] THEN
  REWRITE_TAC[SUM_SING; SET_RULE `{x | x = a} = {a}`; PRODUCT_SING] THEN
  REWRITE_TAC[SIGN_I; I_THM] THEN REAL_ARITH_TAC);;

let DET_1 = prove
 (`!A:real^1^1. det A = A$1$1`,
  SIMP_TAC[DET_1_GEN; DIMINDEX_1]);;

let DET_2 = prove
 (`!A:real^2^2. det A = A$1$1 * A$2$2 - A$1$2 * A$2$1`,
  GEN_TAC THEN REWRITE_TAC[det; DIMINDEX_2] THEN
  CONV_TAC(LAND_CONV(RATOR_CONV(ONCE_DEPTH_CONV NUMSEG_CONV))) THEN
  SIMP_TAC[SUM_OVER_PERMUTATIONS_INSERT; FINITE_INSERT; FINITE_EMPTY;
           ARITH_EQ; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[PERMUTES_EMPTY; SUM_SING; SET_RULE `{x | x = a} = {a}`] THEN
  REWRITE_TAC[SWAP_REFL; I_O_ID] THEN
  REWRITE_TAC[GSYM(NUMSEG_CONV `1..2`); SUM_2] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
           ARITH_EQ; IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[SIGN_COMPOSE; PERMUTATION_SWAP] THEN
  REWRITE_TAC[SIGN_SWAP; ARITH] THEN REWRITE_TAC[PRODUCT_2] THEN
  REWRITE_TAC[o_THM; swap; ARITH] THEN REAL_ARITH_TAC);;

let DET_3 = prove
 (`!A:real^3^3.
        det(A) = A$1$1 * A$2$2 * A$3$3 +
                 A$1$2 * A$2$3 * A$3$1 +
                 A$1$3 * A$2$1 * A$3$2 -
                 A$1$1 * A$2$3 * A$3$2 -
                 A$1$2 * A$2$1 * A$3$3 -
                 A$1$3 * A$2$2 * A$3$1`,
  GEN_TAC THEN REWRITE_TAC[det; DIMINDEX_3] THEN
  CONV_TAC(LAND_CONV(RATOR_CONV(ONCE_DEPTH_CONV NUMSEG_CONV))) THEN
  SIMP_TAC[SUM_OVER_PERMUTATIONS_INSERT; FINITE_INSERT; FINITE_EMPTY;
           ARITH_EQ; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[PERMUTES_EMPTY; SUM_SING; SET_RULE `{x | x = a} = {a}`] THEN
  REWRITE_TAC[SWAP_REFL; I_O_ID] THEN
  REWRITE_TAC[GSYM(NUMSEG_CONV `1..3`); SUM_3] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
           ARITH_EQ; IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[SIGN_COMPOSE; PERMUTATION_SWAP] THEN
  REWRITE_TAC[SIGN_SWAP; ARITH] THEN REWRITE_TAC[PRODUCT_3] THEN
  REWRITE_TAC[o_THM; swap; ARITH] THEN REAL_ARITH_TAC);;

let DET_4 = prove
 (`!A:real^4^4.
        det(A) = A$1$1 * A$2$2 * A$3$3 * A$4$4 +
                 A$1$1 * A$2$3 * A$3$4 * A$4$2 +
                 A$1$1 * A$2$4 * A$3$2 * A$4$3 +
                 A$1$2 * A$2$1 * A$3$4 * A$4$3 +
                 A$1$2 * A$2$3 * A$3$1 * A$4$4 +
                 A$1$2 * A$2$4 * A$3$3 * A$4$1 +
                 A$1$3 * A$2$1 * A$3$2 * A$4$4 +
                 A$1$3 * A$2$2 * A$3$4 * A$4$1 +
                 A$1$3 * A$2$4 * A$3$1 * A$4$2 +
                 A$1$4 * A$2$1 * A$3$3 * A$4$2 +
                 A$1$4 * A$2$2 * A$3$1 * A$4$3 +
                 A$1$4 * A$2$3 * A$3$2 * A$4$1 -
                 A$1$1 * A$2$2 * A$3$4 * A$4$3 -
                 A$1$1 * A$2$3 * A$3$2 * A$4$4 -
                 A$1$1 * A$2$4 * A$3$3 * A$4$2 -
                 A$1$2 * A$2$1 * A$3$3 * A$4$4 -
                 A$1$2 * A$2$3 * A$3$4 * A$4$1 -
                 A$1$2 * A$2$4 * A$3$1 * A$4$3 -
                 A$1$3 * A$2$1 * A$3$4 * A$4$2 -
                 A$1$3 * A$2$2 * A$3$1 * A$4$4 -
                 A$1$3 * A$2$4 * A$3$2 * A$4$1 -
                 A$1$4 * A$2$1 * A$3$2 * A$4$3 -
                 A$1$4 * A$2$2 * A$3$3 * A$4$1 -
                 A$1$4 * A$2$3 * A$3$1 * A$4$2`,
  let lemma = prove
   (`(sum {3,4} f = f 3 + f 4) /\
     (sum {2,3,4} f = f 2 + f 3 + f 4)`,
    SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[ARITH_EQ; IN_INSERT; NOT_IN_EMPTY] THEN REAL_ARITH_TAC) in
  GEN_TAC THEN REWRITE_TAC[det; DIMINDEX_4] THEN
  CONV_TAC(LAND_CONV(RATOR_CONV(ONCE_DEPTH_CONV NUMSEG_CONV))) THEN
  SIMP_TAC[SUM_OVER_PERMUTATIONS_INSERT; FINITE_INSERT; FINITE_EMPTY;
           ARITH_EQ; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[PERMUTES_EMPTY; SUM_SING; SET_RULE `{x | x = a} = {a}`] THEN
  REWRITE_TAC[SWAP_REFL; I_O_ID] THEN
  REWRITE_TAC[GSYM(NUMSEG_CONV `1..4`); SUM_4; lemma] THEN
  SIMP_TAC[SIGN_COMPOSE; PERMUTATION_SWAP; PERMUTATION_COMPOSE] THEN
  REWRITE_TAC[SIGN_SWAP; ARITH] THEN REWRITE_TAC[PRODUCT_4] THEN
  REWRITE_TAC[o_THM; swap; ARITH] THEN REAL_ARITH_TAC);;

let COFACTOR_1_GEN = prove
 (`!A:real^N^N. dimindex(:N) = 1 ==> cofactor A = mat 1`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CART_EQ; mat; cofactor; LAMBDA_BETA; DET_1_GEN; ARITH] THEN
  REWRITE_TAC[LE_ANTISYM] THEN MESON_TAC[]);;

let COFACTOR_1 = prove
 (`!A:real^1^1. cofactor A = mat 1`,
  SIMP_TAC[COFACTOR_1_GEN; DIMINDEX_1]);;

(* ------------------------------------------------------------------------- *)
(* Disjoint or subset-related halfspaces and hyperplanes are parallel.       *)
(* ------------------------------------------------------------------------- *)

let DISJOINT_HYPERPLANES_IMP_COLLINEAR = prove
 (`!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `DISJOINT {x:real^N | a dot x = c} {x | b dot x = d}
    ==> !u v. a dot (u % a + v % b) = c /\
              b dot (u % a + v % b) = d ==> F`)) THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
  GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  MP_TAC(ISPECL
   [`vector[vector[(a:real^N) dot a; a dot b];
            vector[a dot b; b dot b]]:real^2^2`;
    `vector[c;d]:real^2`] MATRIX_FULL_LINEAR_EQUATIONS) THEN
  REWRITE_TAC[RANK_EQ_FULL_DET] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; MATRIX_VECTOR_MUL_COMPONENT; ARITH;
           VECTOR_2; FORALL_2; DOT_2; EXISTS_VECTOR_2; DET_2] THEN
  MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTRAPOS_THM]; MESON_TAC[DOT_SYM; REAL_MUL_SYM]] THEN
  REWRITE_TAC[REAL_ARITH `a - b * b = &0 <=> b pow 2 = a`] THEN
  REWRITE_TAC[DOT_CAUCHY_SCHWARZ_EQUAL]);;

let DISJOINT_HALFSPACES_IMP_COLLINEAR = prove
 (`(!a b:real^N c d.
        DISJOINT {x | a dot x < c} {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x < c} {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x < c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x < c} {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x < c} {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x <= c} {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x <= c} {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x <= c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x <= c} {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x <= c} {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x >= c} {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x >= c} {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x >= c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x >= c} {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x >= c} {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x > c} {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x > c} {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x > c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x > c} {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x > c} {x | b dot x > d}
        ==> collinear {vec 0, a, b})`,
  let lemma = prove
   (`(!a b:real^N. collinear {vec 0,--a,b} <=> collinear{vec 0,a,b}) /\
     (!a b:real^N. collinear {vec 0,a,--b} <=> collinear{vec 0,a,b})`,
    REWRITE_TAC[COLLINEAR_LEMMA_ALT; VECTOR_NEG_EQ_0] THEN
    REWRITE_TAC[VECTOR_ARITH `b:real^N = c % --a <=> b = --c % a`;
                VECTOR_ARITH `--b:real^N = c % a <=> b = --c % a`] THEN
    REWRITE_TAC[MESON[REAL_NEG_NEG] `(?x:real. P(--x)) <=> ?x. P x`]) in
  REWRITE_TAC[REAL_ARITH `x >= d <=> --x <= --d`;
              REAL_ARITH `x > d <=> --x < --d`] THEN
  REWRITE_TAC[GSYM DOT_LNEG] THEN REPEAT STRIP_TAC THEN
  REPLICATE_TAC 2
  (TRY(FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `DISJOINT {x | a dot x <= b} t
      ==> (!x y. x < y ==> x <= y) ==> DISJOINT {x | a dot x < b} t`)) THEN
    REWRITE_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[DISJOINT_SYM])) THEN
  REPLICATE_TAC 2
  (TRY(FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
      `DISJOINT {x | a dot x < b} t
       ==> b - &1 < b ==> DISJOINT {x | a dot x = b - &1} t`)) THEN
     REWRITE_TAC[ARITH_RULE `c - &1 < c`] THEN DISCH_TAC) THEN
   RULE_ASSUM_TAC(ONCE_REWRITE_RULE[DISJOINT_SYM])) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP DISJOINT_HYPERPLANES_IMP_COLLINEAR) THEN
  REWRITE_TAC[lemma]);;

let SUBSET_HALFSPACES_IMP_COLLINEAR = prove
 (`(!a b:real^N c d.
        {x | a dot x < c} SUBSET {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x < c} SUBSET {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x < c} SUBSET {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x < c} SUBSET {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x < c} SUBSET {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x <= c} SUBSET {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x <= c} SUBSET {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x <= c} SUBSET {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x <= c} SUBSET {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x <= c} SUBSET {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x = c} SUBSET {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x = c} SUBSET {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x = c} SUBSET {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x = c} SUBSET {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x = c} SUBSET {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x >= c} SUBSET {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x >= c} SUBSET {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x >= c} SUBSET {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x >= c} SUBSET {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x >= c} SUBSET {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x > c} SUBSET {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x > c} SUBSET {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x > c} SUBSET {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x > c} SUBSET {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x > c} SUBSET {x | b dot x > d}
        ==> collinear {vec 0, a, b})`,
  REWRITE_TAC[SET_RULE `s SUBSET {x | P x} <=> DISJOINT s {x | ~P x}`] THEN
  REWRITE_TAC[REAL_ARITH
    `(~(x < a) <=> x >= a) /\ (~(x <= a) <=> x > a) /\
     (~(x = a) <=> x > a \/ x < a) /\
     (~(x > a) <=> x <= a) /\ (~(x >= a) <=> x < a)`] THEN
  REWRITE_TAC[SET_RULE
   `DISJOINT s {x | P x \/ Q x} <=>
    DISJOINT s {x | P x} /\ DISJOINT s {x | Q x}`] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(DISCH_THEN(MP_TAC o CONJUNCT1)) THEN
  REWRITE_TAC[DISJOINT_HALFSPACES_IMP_COLLINEAR]);;

let SUBSET_HYPERPLANES = prove
 (`!a b a' b'.
        {x | a dot x = b} SUBSET {x | a' dot x = b'} <=>
        {x | a dot x = b} = {} \/ {x | a' dot x = b'} = (:real^N) \/
        {x | a dot x = b} = {x | a' dot x = b'}`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `{x:real^N | a dot x = b} = {}` THEN
  ASM_REWRITE_TAC[EMPTY_SUBSET] THEN
  ASM_CASES_TAC `{x | a' dot x = b'} = (:real^N)` THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [HYPERPLANE_EQ_EMPTY; HYPERPLANE_EQ_UNIV]) THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  ASM_CASES_TAC `{x:real^N | a dot x = b} SUBSET {x | a' dot x = b'}` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`a:real^N`; `a':real^N`; `b:real`; `b':real`]
   (el 12 (CONJUNCTS SUBSET_HALFSPACES_IMP_COLLINEAR))) THEN
  ASM_REWRITE_TAC[COLLINEAR_LEMMA_ALT] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  ASM_CASES_TAC `a:real^N = vec 0` THEN ASM_SIMP_TAC[DOT_LZERO] THENL
   [SET_TAC[]; STRIP_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` SUBST_ALL_TAC) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  ASM_CASES_TAC `c % a:real^N = vec 0` THEN ASM_SIMP_TAC[DOT_LZERO] THENL
   [SET_TAC[]; POP_ASSUM MP_TAC] THEN
  SIMP_TAC[VECTOR_MUL_EQ_0; DE_MORGAN_THM; DOT_LMUL; REAL_FIELD
   `~(c = &0) ==> (c * a = b <=> a = b / c)`] THEN
  STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(b / (a dot a)) % a:real^N`) THEN
  ASM_SIMP_TAC[DOT_RMUL; REAL_DIV_RMUL; DOT_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Existence of the characteristic polynomial.                               *)
(* ------------------------------------------------------------------------- *)

let EIGENVALUES_CHARACTERISTIC_ALT = prove
 (`!A:real^N^N c.
        (?v. ~(v = vec 0) /\ A ** v = c % v) <=> det(A - c %% mat 1) = &0`,
  REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; VECTOR_SUB_EQ; MATRIX_VECTOR_MUL_LID]);;

let EIGENVALUES_CHARACTERISTIC = prove
 (`!A:real^N^N c.
        (?v. ~(v = vec 0) /\ A ** v = c % v) <=> det(c %% mat 1 - A) = &0`,
  ONCE_REWRITE_TAC[GSYM MATRIX_NEG_SUB] THEN
  ASM_REWRITE_TAC[EIGENVALUES_CHARACTERISTIC_ALT; DET_NEG] THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let INVERTIBLE_EIGENVALUES = prove
 (`!A:real^N^N.
        invertible(A) <=> !c v. A ** v = c % v /\ ~(v = vec 0) ==> ~(c = &0)`,
  GEN_TAC THEN REWRITE_TAC[LEFT_FORALL_IMP_THM] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[EIGENVALUES_CHARACTERISTIC_ALT; INVERTIBLE_DET_NZ] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; MATRIX_CMUL_LZERO; MATRIX_SUB_RZERO]);;

let CHARACTERISTIC_POLYNOMIAL = prove
 (`!A:real^N^N.
        ?a. a(dimindex(:N)) = &1 /\
            !x. det(x %% mat 1 - A) =
                sum (0..dimindex(:N)) (\i. a i * x pow i)`,
  GEN_TAC THEN REWRITE_TAC[det] THEN
  SUBGOAL_THEN
   `!p n. IMAGE p (1..dimindex(:N)) SUBSET 1..dimindex(:N) /\
          n <= dimindex(:N)
          ==> ?a. a n = (if !i. 1 <= i /\ i <= n ==> p i = i then &1 else &0) /\
                  !x. product (1..n) (\i. (x %% mat 1 - A:real^N^N)$i$p i) =
                      sum (0..n) (\i. a i * x pow i)`
  MP_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    DISCH_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[LE_0; ARITH_EQ; ARITH_RULE `1 <= SUC n`] THENL
     [EXISTS_TAC `\i. if i = 0 then &1 else &0` THEN
      SIMP_TAC[real_pow; REAL_MUL_LID; ARITH_RULE `1 <= i ==> ~(i <= 0)`;
               SUM_CLAUSES_NUMSEG];
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ASM_SIMP_TAC[ARITH_RULE `SUC n <= N ==> n <= N`] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:num->real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MATRIX_SUB_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
      ASSUME_TAC(ARITH_RULE `1 <= SUC n`) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG] THEN
      DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[MAT_COMPONENT] THEN
      ASM_CASES_TAC `p(SUC n) = SUC n` THEN ASM_REWRITE_TAC[] THENL
       [ALL_TAC;
        EXISTS_TAC `\i. if i <= n
                        then --((A:real^N^N)$(SUC n)$(p(SUC n))) * a i
                        else &0` THEN
        SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0; ARITH_RULE `~(SUC n <= n)`] THEN
        CONJ_TAC THENL
         [COND_CASES_TAC THEN REWRITE_TAC[] THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
          ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
          REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; GSYM SUM_RMUL] THEN
          GEN_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN REWRITE_TAC[] THEN
          REAL_ARITH_TAC]] THEN
      REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_MUL_RID] THEN
      REWRITE_TAC[GSYM SUM_RMUL] THEN EXISTS_TAC
      `\i. (if i = 0 then &0 else a(i - 1)) -
           (if i = SUC n then &0 else (A:real^N^N)$(SUC n)$(SUC n) * a i)` THEN
      ASM_REWRITE_TAC[NOT_SUC; LE; SUC_SUB1; REAL_SUB_RZERO] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
      REWRITE_TAC[REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG] THEN
      GEN_TAC THEN BINOP_TAC THENL
       [SIMP_TAC[SUM_CLAUSES_LEFT; ARITH_RULE `0 <= SUC n`] THEN
        REWRITE_TAC[ADD1; SUM_OFFSET; ARITH_RULE `~(i + 1 = 0)`; ADD_SUB] THEN
        REWRITE_TAC[REAL_MUL_LZERO; REAL_POW_ADD; REAL_POW_1; REAL_ADD_LID];
        SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0; REAL_MUL_LZERO; REAL_ADD_RID] THEN
        SIMP_TAC[ARITH_RULE `i <= n ==> ~(i = SUC n)`]] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN REWRITE_TAC[REAL_ADD_LID; REAL_MUL_AC]];
    GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `dimindex(:N)`) THEN REWRITE_TAC[LE_REFL] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `a:(num->num)->num->real` THEN DISCH_TAC] THEN
  EXISTS_TAC
   `\i:num. sum {p | p permutes 1..dimindex(:N)} (\p. sign p * a p i)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\p:num->num. sign p * a p (dimindex(:N))`;
      `{p | p permutes 1..dimindex(:N)}`;
      `I:num->num`] SUM_DELETE) THEN
    SIMP_TAC[IN_ELIM_THM; PERMUTES_I; FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN
    MATCH_MP_TAC(REAL_ARITH `k = &1 /\ s' = &0 ==> s' = s - k ==> s = &1`) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `I:num->num`) THEN
      SIMP_TAC[IMAGE_I; SUBSET_REFL; SIGN_I; I_THM; REAL_MUL_LID];
      MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `p:num->num` THEN
      REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:num->num`) THEN ANTS_TAC THENL
       [ASM_MESON_TAC[PERMUTES_IMAGE; SUBSET_REFL]; ALL_TAC] THEN
      COND_CASES_TAC THEN SIMP_TAC[REAL_MUL_RZERO] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [permutes]) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [FUN_EQ_THM]) THEN
      REWRITE_TAC[IN_NUMSEG; I_THM] THEN ASM_MESON_TAC[]];
    X_GEN_TAC `x:real` THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SUM_SWAP o rand o snd) THEN
    SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `p:num->num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; SUM_LMUL] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num->num`) THEN ANTS_TAC THENL
     [ASM_MESON_TAC[PERMUTES_IMAGE; SUBSET_REFL]; SIMP_TAC[]]]);;

let FINITE_EIGENVALUES = prove
 (`!A:real^N^N. FINITE {c | ?v. ~(v = vec 0) /\ A ** v = c % v}`,
  GEN_TAC THEN REWRITE_TAC[EIGENVALUES_CHARACTERISTIC] THEN
  MP_TAC(ISPEC `A:real^N^N` CHARACTERISTIC_POLYNOMIAL) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_POLYFUN_FINITE_ROOTS] THEN EXISTS_TAC `dimindex(:N)` THEN
  ASM_REWRITE_TAC[IN_NUMSEG; LE_0; LE_REFL] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Grassmann-Plucker relations for n = 2, n = 3 and n = 4.                   *)
(* I have a proof of the general n case but the proof is a bit long and the  *)
(* result doesn't seem generally useful enough to go in the main theories.   *)
(* ------------------------------------------------------------------------- *)

let GRASSMANN_PLUCKER_2 = prove
 (`!x1 x2 y1 y2:real^2.
        det(vector[x1;x2]) * det(vector[y1;y2]) =
          det(vector[y1;x2]) * det(vector[x1;y2]) +
          det(vector[y2;x2]) * det(vector[y1;x1])`,
  REWRITE_TAC[DET_2; VECTOR_2] THEN REAL_ARITH_TAC);;

let GRASSMANN_PLUCKER_3 = prove
 (`!x1 x2 x3 y1 y2 y3:real^3.
        det(vector[x1;x2;x3]) * det(vector[y1;y2;y3]) =
          det(vector[y1;x2;x3]) * det(vector[x1;y2;y3]) +
          det(vector[y2;x2;x3]) * det(vector[y1;x1;y3]) +
          det(vector[y3;x2;x3]) * det(vector[y1;y2;x1])`,
  REWRITE_TAC[DET_3; VECTOR_3] THEN REAL_ARITH_TAC);;

let GRASSMANN_PLUCKER_4 = prove
 (`!x1 x2 x3 x4:real^4 y1 y2 y3 y4:real^4.
        det(vector[x1;x2;x3;x4]) * det(vector[y1;y2;y3;y4]) =
          det(vector[y1;x2;x3;x4]) * det(vector[x1;y2;y3;y4]) +
          det(vector[y2;x2;x3;x4]) * det(vector[y1;x1;y3;y4]) +
          det(vector[y3;x2;x3;x4]) * det(vector[y1;y2;x1;y4]) +
          det(vector[y4;x2;x3;x4]) * det(vector[y1;y2;y3;x1])`,
  REWRITE_TAC[DET_4; VECTOR_4] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Determinants of integer matrices.                                         *)
(* ------------------------------------------------------------------------- *)

let INTEGER_PRODUCT = prove
 (`!f s. (!x. x IN s ==> integer(f x)) ==> integer(product s f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_CLOSED THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED]);;

let INTEGER_SIGN = prove
 (`!p. integer(sign p)`,
  SIMP_TAC[sign; COND_RAND; INTEGER_CLOSED; COND_ID]);;

let INTEGER_DET = prove
 (`!M:real^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N)
               ==> integer(M$i$j))
        ==> integer(det M)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[det] THEN
  MATCH_MP_TAC INTEGER_SUM THEN X_GEN_TAC `p:num->num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC INTEGER_MUL THEN REWRITE_TAC[INTEGER_SIGN] THEN
  MATCH_MP_TAC INTEGER_PRODUCT THEN REWRITE_TAC[IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[IN_NUMSEG; permutes]);;

(* ------------------------------------------------------------------------- *)
(* Diagonal matrices (for arbitrary rectangular matrix, not just square).    *)
(* ------------------------------------------------------------------------- *)

let diagonal_matrix = new_definition
 `diagonal_matrix(A:real^N^M) <=>
        !i j. 1 <= i /\ i <= dimindex(:M) /\
              1 <= j /\ j <= dimindex(:N) /\
              ~(i = j)
              ==> A$i$j = &0`;;

let DIAGONAL_MATRIX = prove
 (`!A:real^N^N.
     diagonal_matrix A <=> A = (lambda i j. if i = j then A$i$j else &0)`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; diagonal_matrix] THEN MESON_TAC[]);;

let DIAGONAL_MATRIX_MAT = prove
 (`!m. diagonal_matrix(mat m:real^N^N)`,
  SIMP_TAC[mat; diagonal_matrix; LAMBDA_BETA]);;

let TRANSP_DIAGONAL_MATRIX = prove
 (`!A:real^N^N. diagonal_matrix A ==> transp A = A`,
  GEN_TAC THEN REWRITE_TAC[diagonal_matrix; CART_EQ; TRANSP_COMPONENT] THEN
  STRIP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN
  STRIP_TAC THEN ASM_CASES_TAC `i:num = j` THEN ASM_SIMP_TAC[]);;

let DIAGONAL_IMP_SYMMETRIC_MATRIX = prove
 (`!A:real^N^N. diagonal_matrix A ==> symmetric_matrix A`,
  REWRITE_TAC[symmetric_matrix; TRANSP_DIAGONAL_MATRIX]);;

let DIAGONAL_MATRIX_ADD = prove
 (`!A B:real^N^M.
        diagonal_matrix A /\ diagonal_matrix B
        ==> diagonal_matrix(A + B)`,
  SIMP_TAC[diagonal_matrix; MATRIX_ADD_COMPONENT;
           REAL_ADD_LID; REAL_ADD_RID]);;

let DIAGONAL_MATRIX_CMUL = prove
 (`!A:real^N^M c.
        diagonal_matrix A ==> diagonal_matrix(c %% A)`,
  SIMP_TAC[diagonal_matrix; MATRIX_CMUL_COMPONENT; REAL_MUL_RZERO]);;

let MATRIX_MUL_DIAGONAL = prove
 (`!A:real^N^N B:real^N^N.
        diagonal_matrix A /\ diagonal_matrix B
        ==> A ** B = lambda i j. A$i$j * B$i$j`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I [DIAGONAL_MATRIX])) THEN
  SIMP_TAC[CART_EQ; matrix_mul; LAMBDA_BETA] THEN
  ONCE_REWRITE_TAC[MESON[REAL_MUL_LZERO; REAL_MUL_RZERO]
   `(if p then a else &0) * (if q then b else &0) =
    if q then (if p then a * b else &0) else &0`] THEN
  SIMP_TAC[SUM_DELTA; IN_NUMSEG; COND_ID; SUM_0]);;

let DIAGONAL_MATRIX_MUL_COMPONENT = prove
 (`!A:real^N^N B:real^N^N i j.
        diagonal_matrix A /\ diagonal_matrix B /\
        1 <= i /\ i <= dimindex(:N) /\
        1 <= j /\ j <= dimindex(:N)
        ==> (A ** B)$i$j = A$i$j * B$i$j`,
  ASM_SIMP_TAC[MATRIX_MUL_DIAGONAL; LAMBDA_BETA]);;

let DIAGONAL_MATRIX_MUL = prove
 (`!A:real^N^N B:real^N^N.
        diagonal_matrix A /\ diagonal_matrix B
        ==> diagonal_matrix(A ** B)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [diagonal_matrix] THEN
  SIMP_TAC[DIAGONAL_MATRIX_MUL_COMPONENT] THEN
  SIMP_TAC[diagonal_matrix; REAL_MUL_LZERO]);;

let DIAGONAL_MATRIX_MUL_EQ = prove
 (`!A:real^M^N B:real^N^M.
        diagonal_matrix (A ** B) <=>
        pairwise (\i j. orthogonal (row i A) (column j B)) (1..dimindex(:N))`,
  REWRITE_TAC[diagonal_matrix; matrix_mul; pairwise] THEN
  SIMP_TAC[LAMBDA_BETA; IN_NUMSEG; orthogonal; dot; row; column] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC]);;

let DIAGONAL_MATRIX_INV_EXPLICIT = prove
 (`!A:real^N^N. diagonal_matrix A ==> matrix_inv A = lambda i j. inv(A$i$j)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
  REWRITE_TAC[symmetric_matrix] THEN
  SUBGOAL_THEN
   `diagonal_matrix((lambda i j. inv((A:real^N^N)$i$j)):real^N^N)`
  ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[diagonal_matrix]) THEN
    ASM_SIMP_TAC[diagonal_matrix; LAMBDA_BETA; REAL_INV_0];
    ASM_SIMP_TAC[DIAGONAL_MATRIX_MUL_COMPONENT; CART_EQ; LAMBDA_BETA;
                 TRANSP_COMPONENT; DIAGONAL_MATRIX_MUL]] THEN
  MP_TAC(ISPEC `A:real^N^N` DIAGONAL_MATRIX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN SIMP_TAC[LAMBDA_BETA] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_INV_0; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  REWRITE_TAC[REAL_INV_EQ_0; REAL_RING
    `a * b * a = a <=> b * a = &1 \/ a = &0`] THEN
  CONV_TAC REAL_FIELD);;

let DIAGONAL_MATRIX_INV_COMPONENT = prove
 (`!A:real^N^N i j.
        diagonal_matrix A /\
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> (matrix_inv A)$i$j = inv(A$i$j)`,
  ASM_SIMP_TAC[DIAGONAL_MATRIX_INV_EXPLICIT; LAMBDA_BETA]);;

let DIAGONAL_MATRIX_INV = prove
 (`!A:real^N^N. diagonal_matrix(matrix_inv A) <=> diagonal_matrix A`,
  SUBGOAL_THEN
   `!A:real^N^N. diagonal_matrix A ==> diagonal_matrix(matrix_inv A)`
  MP_TAC THENL [REPEAT STRIP_TAC; MESON_TAC[MATRIX_INV_INV]] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP DIAGONAL_MATRIX_INV_EXPLICIT) THEN
  POP_ASSUM MP_TAC THEN SIMP_TAC[diagonal_matrix; LAMBDA_BETA] THEN
  REWRITE_TAC[REAL_INV_0]);;

let DET_DIAGONAL = prove
 (`!A:real^N^N.
        diagonal_matrix A
        ==> det(A) = product(1..dimindex(:N)) (\i. A$i$i)`,
  REWRITE_TAC[diagonal_matrix] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DET_LOWERTRIANGULAR THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LT_REFL]);;

let INVERTIBLE_DIAGONAL_MATRIX = prove
 (`!D:real^N^N.
        diagonal_matrix D
        ==> (invertible D <=>
             !i. 1 <= i /\ i <= dimindex(:N) ==> ~(D$i$i = &0))`,
  SIMP_TAC[INVERTIBLE_DET_NZ; DET_DIAGONAL] THEN
  SIMP_TAC[PRODUCT_EQ_0; FINITE_NUMSEG; IN_NUMSEG] THEN MESON_TAC[]);;

let COMMUTING_WITH_DIAGONAL_MATRIX = prove
 (`!A D:real^N^N.
        diagonal_matrix D
        ==> (A ** D = D ** A <=>
             !i j. 1 <= i /\ i <= dimindex(:N) /\
                   1 <= j /\ j <= dimindex(:N)
                   ==> A$i$j = &0 \/ D$i$i = D$j$j)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o REWRITE_RULE[DIAGONAL_MATRIX]) THEN
  SIMP_TAC[CART_EQ; matrix_mul; LAMBDA_BETA] THEN
  REWRITE_TAC[MESON[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_MUL_SYM]
   `(if a = b then x else &0) * y = (if b = a then x * y else &0) /\
    y * (if a = b then x else &0) = (if a = b then x * y else &0)`] THEN
  SIMP_TAC[SUM_DELTA; IN_NUMSEG; REAL_EQ_MUL_RCANCEL] THEN MESON_TAC[]);;

let RANK_DIAGONAL_MATRIX = prove
 (`!A:real^N^N.
        diagonal_matrix A
        ==> rank A = CARD {i | i IN 1..dimindex(:N) /\ ~(A$i$i = &0)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RANK_DIM_IM; GSYM SPAN_STDBASIS] THEN
  SIMP_TAC[GSYM SPAN_LINEAR_IMAGE; MATRIX_VECTOR_MUL_LINEAR; DIM_SPAN] THEN
  REWRITE_TAC[GSYM IN_NUMSEG; SIMPLE_IMAGE; GSYM IMAGE_o; o_DEF] THEN
  TRANS_TAC EQ_TRANS
    `dim {(A:real^N^N)$i$i % basis i:real^N | i IN 1..dimindex(:N)}` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> f x = g x) ==> IMAGE f s = {g x | x IN s}`) THEN
    FIRST_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I [DIAGONAL_MATRIX]) THEN
    SIMP_TAC[matrix_vector_mul; LAMBDA_BETA; IN_NUMSEG; CART_EQ] THEN
    ONCE_REWRITE_TAC[MESON[REAL_MUL_LZERO]
     `(if i = j then a else &0) * b = if j = i then a * b else &0`] THEN
    SIMP_TAC[SUM_DELTA; IN_NUMSEG; BASIS_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    MESON_TAC[REAL_MUL_RZERO];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `dim {(A:real^N^N)$i$i % basis i:real^N |i|
          i IN 1..dimindex(:N) /\ ~(A$i$i = &0)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(MESON[DIM_INSERT_0]
    `(vec 0:real^N) INSERT s = (vec 0:real^N) INSERT t ==> dim s = dim t`) THEN
    MATCH_MP_TAC(SET_RULE
     `t SUBSET s /\ (!x. x IN s ==> ~(x IN t) ==> x = a)
      ==> a INSERT s = a INSERT t`) THEN
    CONJ_TAC THENL [SET_TAC[]; REWRITE_TAC[FORALL_IN_GSPEC]] THEN
    SIMP_TAC[VECTOR_MUL_EQ_0; IN_ELIM_THM; BASIS_NONZERO; IN_NUMSEG] THEN
    SET_TAC[];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
  `dim{basis i:real^N | i IN 1..dimindex(:N) /\ ~((A:real^N^N)$i$i = &0)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_EQ_DIM THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
    CONJ_TAC THEN MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
    REWRITE_TAC[SUBSPACE_SPAN] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; SUBSET; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THENL
     [ALL_TAC;
      SUBGOAL_THEN
       `basis i:real^N = inv((A:real^N^N)$i$i) % A$i$i % basis i`
       (fun th -> GEN_REWRITE_TAC LAND_CONV [th])
      THENL [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID];
             ALL_TAC]] THEN
    MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN ASM SET_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) DIM_EQ_CARD o lhand o snd) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] INDEPENDENT_MONO)
        INDEPENDENT_STDBASIS) THEN
    REWRITE_TAC[IN_NUMSEG] THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SIMPLE_IMAGE_GEN] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN
  SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG; IN_ELIM_THM; IN_NUMSEG] THEN
  REWRITE_TAC[IMP_CONJ] THEN SIMP_TAC[BASIS_INJ_EQ]);;

let ONORM_DIAGONAL_MATRIX = prove
 (`!A:real^N^N.
       diagonal_matrix A
       ==> onorm(\x. A ** x) = sup {abs(A$i$i) | 1 <= i /\ i <= dimindex(:N)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[onorm] THEN MATCH_MP_TAC SUP_EQ THEN
  X_GEN_TAC `b:real` THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `basis i:real^N`) THEN
    ASM_SIMP_TAC[NORM_BASIS; MATRIX_VECTOR_MUL_BASIS] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (MESON[COMPONENT_LE_NORM; REAL_LE_TRANS]
     `norm(x) <= b ==> !i. abs(x$i) <= b`)) THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[column; LAMBDA_BETA];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    TRANS_TAC REAL_LE_TRANS `norm(b % x:real^N)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o GEN_REWRITE_RULE I [DIAGONAL_MATRIX]) THEN
      FIRST_X_ASSUM(K ALL_TAC o SYM) THEN POP_ASSUM MP_TAC THEN
      SIMP_TAC[LAMBDA_BETA; MATRIX_VECTOR_MUL_COMPONENT; dot] THEN
      REWRITE_TAC[COND_RAND; COND_RATOR; REAL_MUL_LZERO] THEN
      CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
      SIMP_TAC[SUM_DELTA; IN_NUMSEG] THEN
      REWRITE_TAC[REAL_ABS_MUL; VECTOR_MUL_COMPONENT] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b`) THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[NORM_MUL] THEN FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN
      ASM_REWRITE_TAC[DIMINDEX_GE_1; LE_REFL] THEN REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Positive semidefinite matrices.                                           *)
(* ------------------------------------------------------------------------- *)

let positive_semidefinite = new_definition
 `positive_semidefinite(A:real^N^N) <=>
    symmetric_matrix A /\ !x. &0 <= x dot (A ** x)`;;

let POSITIVE_SEMIDEFINITE_IMP_SYMMETRIC_MATRIX = prove
 (`!A:real^N^N. positive_semidefinite A ==> symmetric_matrix A`,
  SIMP_TAC[positive_semidefinite]);;

let POSITIVE_SEMIDEFINITE_IMP_SYMMETRIC = prove
 (`!A:real^N^N. positive_semidefinite A ==> transp A = A`,
  REWRITE_TAC[GSYM symmetric_matrix;
             POSITIVE_SEMIDEFINITE_IMP_SYMMETRIC_MATRIX]);;

let POSITIVE_SEMIDEFINITE_ADD = prove
 (`!A B:real^N^N.
        positive_semidefinite A /\ positive_semidefinite B
        ==> positive_semidefinite(A + B)`,
  SIMP_TAC[positive_semidefinite; SYMMETRIC_MATRIX_ADD] THEN
  SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; DOT_RADD; REAL_LE_ADD]);;

let POSITIVE_SEMIDEFINITE_CMUL = prove
 (`!c A:real^N^N.
        positive_semidefinite A /\ &0 <= c
        ==> positive_semidefinite(c %% A)`,
  SIMP_TAC[positive_semidefinite; SYMMETRIC_MATRIX_CMUL] THEN
  SIMP_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL; REAL_LE_MUL]);;

let POSITIVE_SEMIDEFINITE_TRANSP = prove
 (`!A:real^N^N. positive_semidefinite(transp A) <=> positive_semidefinite A`,
  REWRITE_TAC[positive_semidefinite; symmetric_matrix] THEN
  MESON_TAC[TRANSP_TRANSP]);;

let POSITIVE_SEMIDEFINITE_COVARIANCE = prove
 (`!A:real^N^M. positive_semidefinite(transp A ** A)`,
  REWRITE_TAC[positive_semidefinite; symmetric_matrix;
              MATRIX_TRANSP_MUL; TRANSP_TRANSP] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM DOT_LMUL_MATRIX] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_TRANSP; DOT_POS_LE]);;

let POSITIVE_SEMIDEFINITE_SIMILAR = prove
 (`!A B:real^N^M.
        positive_semidefinite A
        ==> positive_semidefinite(transp B ** A ** B)`,
  REWRITE_TAC[positive_semidefinite; symmetric_matrix] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; GSYM MATRIX_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM DOT_LMUL_MATRIX; GSYM MATRIX_VECTOR_MUL_TRANSP] THEN
  ASM_REWRITE_TAC[DOT_LMUL_MATRIX]);;

let POSITIVE_SEMIDEFINITE_SIMILAR_EQ = prove
 (`!A B:real^N^N.
        invertible B
        ==> (positive_semidefinite (transp B ** A ** B) <=>
             positive_semidefinite A)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[POSITIVE_SEMIDEFINITE_SIMILAR] THEN
  DISCH_THEN(MP_TAC o ISPEC `matrix_inv B:real^N^N` o MATCH_MP
    POSITIVE_SEMIDEFINITE_SIMILAR) THEN
  ASM_SIMP_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_INV; MATRIX_MUL_RID] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN
  ASM_SIMP_TAC[MATRIX_INV; TRANSP_MAT; MATRIX_MUL_LID]);;

let POSITIVE_SEMIDEFINITE_DIAGONAL_MATRIX = prove
 (`!D:real^N^N.
        diagonal_matrix D /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= D$i$i)
        ==> positive_semidefinite D`,
  SIMP_TAC[positive_semidefinite; DIAGONAL_IMP_SYMMETRIC_MATRIX] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I [DIAGONAL_MATRIX]) THEN
  SIMP_TAC[matrix_vector_mul; LAMBDA_BETA; dot] THEN
  SIMP_TAC[COND_RATOR; COND_RAND; REAL_MUL_LZERO] THEN
  CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  SIMP_TAC[SUM_DELTA] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `x * d * x:real = d * x * x`] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_SIMP_TAC[REAL_LE_SQUARE]);;

let POSITIVE_SEMIDEFINITE_DIAGONAL_MATRIX_EQ = prove
 (`!D:real^N^N.
        diagonal_matrix D
        ==> (positive_semidefinite D <=>
             !i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= D$i$i)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[POSITIVE_SEMIDEFINITE_DIAGONAL_MATRIX] THEN
  REWRITE_TAC[positive_semidefinite] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `basis i:real^N`) THEN
  ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA]);;

let DIAGONAL_POSITIVE_SEMIDEFINITE = prove
 (`!A:real^N^N i.
        positive_semidefinite A /\ 1 <= i /\ i <= dimindex(:N)
        ==> &0 <= A$i$i`,
  REWRITE_TAC[positive_semidefinite] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `basis i:real^N`) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; DOT_BASIS; LAMBDA_BETA]);;

let TRACE_POSITIVE_SEMIDEFINITE = prove
 (`!A:real^N^N. positive_semidefinite A ==> &0 <= trace A`,
  SIMP_TAC[trace; SUM_POS_LE_NUMSEG; DIAGONAL_POSITIVE_SEMIDEFINITE]);;

let TRACE_LE_MUL_SQUARES = prove
 (`!A B:real^N^N.
        symmetric_matrix A /\ symmetric_matrix B
        ==> trace((A ** B) ** (A ** B)) <= trace((A ** A) ** (B ** B))`,
  REWRITE_TAC[symmetric_matrix] THEN REPEAT STRIP_TAC THEN MP_TAC
   (ISPEC `A ** B - B ** A:real^N^N` POSITIVE_SEMIDEFINITE_COVARIANCE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP TRACE_POSITIVE_SEMIDEFINITE) THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_MATRIX_SUB; MATRIX_SUB_LDISTRIB] THEN
  ASM_REWRITE_TAC[MATRIX_SUB_RDISTRIB; TRACE_SUB] THEN MATCH_MP_TAC(REAL_ARITH
  `a = y /\ d = y /\ b = x /\ c = x ==> &0 <= a - b - (c - d) ==> x <= y`) THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN REPEAT CONJ_TAC THEN
  REPEAT(GEN_REWRITE_TAC LAND_CONV [TRACE_MUL_SYM] THEN
         REWRITE_TAC[GSYM MATRIX_MUL_ASSOC]));;

let POSITIVE_SEMIDEFINITE_ZERO_FORM = prove
 (`!A:real^N^N. positive_semidefinite A /\ x dot (A ** x) = &0
                ==> A ** x = vec 0`,
  let lemma = prove
   (`(!t. &0 <= a + b * t) ==> b = &0`,
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `--(a + &1) / b`) THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL] THEN REAL_ARITH_TAC) in
  REWRITE_TAC[positive_semidefinite; symmetric_matrix] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN `t:real` o SPEC `(A:real^N^N) ** x + t % x`) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_RADD] THEN
  REWRITE_TAC[DOT_LADD; MATRIX_VECTOR_MUL_RMUL; DOT_LMUL] THEN
  REWRITE_TAC[DOT_RMUL] THEN
  SUBGOAL_THEN `x dot (A ** A ** x) = ((A:real^N^N) ** x) dot (A ** x)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[GSYM DOT_LMUL_MATRIX; VECTOR_MATRIX_MUL_TRANSP];
    ASM_REWRITE_TAC[REAL_ARITH `(a + t * b) + t * b + t * t * &0 =
                                a + (&2 * b) * t`]] THEN
  DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
  REWRITE_TAC[REAL_ENTIRE; DOT_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ]);;

let POSITIVE_SEMIDEFINITE_ZERO_FORM_EQ = prove
 (`!A:real^N^N. positive_semidefinite A
                ==> (x dot (A ** x) = &0 <=> A ** x = vec 0)`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN
  ASM_SIMP_TAC[DOT_RZERO; POSITIVE_SEMIDEFINITE_ZERO_FORM]);;

let POSITIVE_SEMIDEFINITE_1_GEN = prove
 (`!A:real^N^N.
        dimindex(:N) = 1 ==> (positive_semidefinite A <=> &0 <= A$1$1)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[positive_semidefinite; symmetric_matrix; transp; CART_EQ; dot] THEN
  ASM_SIMP_TAC[LAMBDA_BETA; ARITH; MATRIX_VECTOR_MUL_COMPONENT] THEN
  ASM_REWRITE_TAC[FORALL_1; SUM_1; dot] THEN
  REWRITE_TAC[REAL_ARITH `x * a * x:real = a * x pow 2`] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[REAL_LE_MUL; REAL_LE_POW_2]] THEN
  DISCH_THEN(MP_TAC o SPEC `basis 1:real^N`) THEN
  SIMP_TAC[BASIS_COMPONENT; ARITH; DIMINDEX_GE_1; LE_REFL] THEN
  REAL_ARITH_TAC);;

let POSITIVE_SEMIDEFINITE_1 = prove
 (`!A:real^1^1. positive_semidefinite A <=> &0 <= A$1$1`,
  GEN_TAC THEN MATCH_MP_TAC POSITIVE_SEMIDEFINITE_1_GEN THEN
  REWRITE_TAC[DIMINDEX_1]);;

let POSITIVE_SEMIDEFINITE_SUBMATRIX_2 = prove
 (`!A:real^N^N i j.
        positive_semidefinite A /\
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> positive_semidefinite
              (vector[vector[A$i$i;A$i$j];
                      vector[A$j$i;A$j$j]]:real^2^2)`,
  REWRITE_TAC[positive_semidefinite; symmetric_matrix] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CART_EQ]) THEN
    SIMP_TAC[CART_EQ; transp; LAMBDA_BETA; DIMINDEX_2; VECTOR_2; ARITH;
             FORALL_2] THEN
    ASM_MESON_TAC[];
    SIMP_TAC[DOT_2; VECTOR_2; matrix_vector_mul; DIMINDEX_2; LAMBDA_BETA;
             ARITH; SUM_2]] THEN
  ASM_CASES_TAC `j:num = i` THENL
   [ASM_REWRITE_TAC[REAL_ARITH
     `x * (a * x + a * y) + y * (a * x + a * y):real =
      a * (x + y) pow 2`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC DIAGONAL_POSITIVE_SEMIDEFINITE THEN
    ASM_REWRITE_TAC[positive_semidefinite; symmetric_matrix];
    FIRST_X_ASSUM(MP_TAC o SPEC
     `(lambda m. if m = i then (x:real^2)$1
                 else if m = j then (x:real^2)$2  else &0):real^N`) THEN
    SIMP_TAC[matrix_vector_mul; LAMBDA_BETA] THEN
    REPLICATE_TAC 2
     (REPLICATE_TAC 2 (ONCE_REWRITE_TAC[COND_RAND]) THEN
      SIMP_TAC[SUM_CASES; FINITE_NUMSEG; SUM_DELTA; REAL_MUL_RZERO] THEN
      ASM_SIMP_TAC[SET_RULE `P a ==> {x | P x /\ x = a} = {a}`;
                   IN_NUMSEG; IN_ELIM_THM; SUM_SING] THEN
      SIMP_TAC[dot; LAMBDA_BETA] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM])]);;

(* ------------------------------------------------------------------------- *)
(* The Frobenius norm and associated inner product, which turn out to be the *)
(* usual Euclidean versions modulo flattening.                               *)
(* ------------------------------------------------------------------------- *)

let DOT_VECTORIZE = prove
 (`!A B:real^N^M. vectorize A dot vectorize B = trace(transp A ** B)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[dot; trace; matrix_mul; transp; LAMBDA_BETA] THEN
  SIMP_TAC[SUM_SUM_PRODUCT; FINITE_NUMSEG] THEN
  SIMP_TAC[VECTORIZE_COMPONENT; DIMINDEX_FINITE_PROD] THEN
  MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  EXISTS_TAC
   `\k. (1 + (k - 1) MOD dimindex(:N)),(1 + (k - 1) DIV dimindex(:N))` THEN
  EXISTS_TAC `\(i,j). (j - 1) * dimindex(:N) + i` THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; PAIR_EQ; IN_NUMSEG] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN CONJ_TAC THENL
     [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      TRANS_TAC LE_TRANS `(j - 1) * dimindex(:N) + dimindex(:N)` THEN
      ASM_REWRITE_TAC[LE_ADD_LCANCEL] THEN
      REWRITE_TAC[ARITH_RULE `x * n + n = (x + 1) * n`] THEN
      ASM_SIMP_TAC[SUB_ADD; LE_MULT_RCANCEL];
      CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
       `1 <= i /\ j = i - 1 ==> 1 + j = i`) THEN
      ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `j - 1` THEN ASM_ARITH_TAC;
        MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i - 1` THEN ASM_ARITH_TAC]];
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[LE_ADD] THEN
    SIMP_TAC[DIVISION; DIMINDEX_GE_1; LE_1; ADD_SUB2; RDIV_LT_EQ; ARITH_RULE
      `1 <= n ==> (1 + m <= n <=> m < n)`] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE
     `1 <= x /\ x - 1 = q * n + r /\ r < n ==> q * n + 1 + r = x`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIVISION THEN
    SIMP_TAC[DIMINDEX_GE_1; LE_1]]);;

let NORM_VECTORIZE_TRANSP = prove
 (`!A:real^N^M. norm(vectorize(transp A)) = norm(vectorize A)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NORM_EQ; DOT_VECTORIZE; TRANSP_TRANSP] THEN
  MATCH_ACCEPT_TAC TRACE_MUL_SYM);;

let COMPATIBLE_NORM_VECTORIZE = prove
 (`!A:real^N^M x. norm(A ** x) <= norm(vectorize A) * norm x`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[NORM_LE_SQUARE; REAL_LE_MUL; NORM_POS_LE] THEN
  REWRITE_TAC[dot] THEN SIMP_TAC[MATRIX_MUL_DOT; LAMBDA_BETA] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum (1..dimindex(:M))
        (\i. norm((A:real^N^M)$i) pow 2 * norm(x:real^N) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_POW_MUL; GSYM REAL_POW_2] THEN
    REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS; REAL_ABS_MUL; REAL_ABS_NORM] THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS];
    REWRITE_TAC[SUM_RMUL; REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_LE_POW_2; NORM_POW_2; DOT_VECTORIZE] THEN
    ONCE_REWRITE_TAC[TRACE_MUL_SYM] THEN
    REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    SIMP_TAC[transp; matrix_mul; LAMBDA_BETA; dot; REAL_LE_REFL]]);;

let ONORM_LE_NORM_VECTORIZE = prove
 (`!A:real^M^N. onorm(\x. A ** x) <= norm(vectorize A)`,
  GEN_TAC THEN MATCH_MP_TAC
   (CONJUNCT2(MATCH_MP ONORM (SPEC_ALL MATRIX_VECTOR_MUL_LINEAR))) THEN
  REWRITE_TAC[COMPATIBLE_NORM_VECTORIZE]);;

let NORM_VECTORIZE_POW_2 = prove
 (`!A:real^N^M.
    norm(vectorize A) pow 2 = sum(1..dimindex(:M)) (\i. norm(A$i) pow 2)`,
  GEN_TAC THEN
  REWRITE_TAC[NORM_POW_2; DOT_VECTORIZE] THEN
  SIMP_TAC[trace; transp; matrix_mul; dot; LAMBDA_BETA] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[]);;

let NORM_VECTORIZE_MUL_LE = prove
 (`!A:real^N^P B:real^M^N.
    norm(vectorize(A ** B)) <= norm(vectorize A) * norm(vectorize B)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[NORM_LE_SQUARE; REAL_LE_MUL; NORM_POS_LE] THEN
  REWRITE_TAC[GSYM NORM_POW_2; NORM_VECTORIZE_POW_2] THEN
  SIMP_TAC[MATRIX_MUL_COMPONENT; REAL_POW_MUL] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [NORM_VECTORIZE_POW_2] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM REAL_POW_MUL] THEN
  REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS; REAL_ABS_MUL; REAL_ABS_NORM] THEN
  MESON_TAC[COMPATIBLE_NORM_VECTORIZE; NORM_VECTORIZE_TRANSP; REAL_MUL_SYM]);;

let NORM_VECTORIZE_HADAMARD_LE = prove
 (`!A:real^N^M B:real^N^M.
        norm(vectorize((lambda i j. A$i$j * B$i$j):real^N^M))
        <= norm(vectorize A) * norm(vectorize B)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[NORM_LE_SQUARE; REAL_LE_MUL; NORM_POS_LE] THEN
  REWRITE_TAC[DOT_VECTORIZE; REAL_POW_MUL; NORM_POW_2] THEN
  SIMP_TAC[transp; matrix_mul; trace; LAMBDA_BETA] THEN
  SIMP_TAC[SUM_SUM_PRODUCT; FINITE_NUMSEG] THEN
  W(MP_TAC o PART_MATCH (rand o rand) SUM_MUL_BOUND o rand o snd) THEN
  SIMP_TAC[FINITE_PRODUCT_DEPENDENT; FINITE_NUMSEG; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[REAL_LE_SQUARE] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN REWRITE_TAC[REAL_MUL_AC]);;

let TRACE_COVARIANCE_POS_LE = prove
 (`!A:real^M^N. &0 <= trace(transp A ** A)`,
  SIMP_TAC[POSITIVE_SEMIDEFINITE_COVARIANCE; TRACE_POSITIVE_SEMIDEFINITE]);;

let TRACE_COVARIANCE_EQ_0 = prove
 (`!A:real^M^N. trace(transp A ** A) = &0 <=> A = mat 0`,
  REWRITE_TAC[GSYM DOT_VECTORIZE; DOT_EQ_0; VECTORIZE_EQ_0]);;

let TRACE_COVARIANCE_POS_LT = prove
 (`!A:real^M^N. &0 < trace(transp A ** A) <=> ~(A = mat 0)`,
  MESON_TAC[REAL_LT_LE; TRACE_COVARIANCE_POS_LE; TRACE_COVARIANCE_EQ_0]);;

let TRACE_COVARIANCE_CAUCHY_SCHWARZ = prove
 (`!A B:real^M^N.
        trace(transp A ** B)
         <= sqrt(trace(transp A ** A)) * sqrt(trace(transp B ** B))`,
  REWRITE_TAC[GSYM DOT_VECTORIZE; GSYM vector_norm; NORM_CAUCHY_SCHWARZ]);;

let TRACE_COVARIANCE_CAUCHY_SCHWARZ_ABS = prove
 (`!A B:real^M^N.
        abs(trace(transp A ** B))
         <= sqrt(trace(transp A ** A)) * sqrt(trace(transp B ** B))`,
  REWRITE_TAC[GSYM DOT_VECTORIZE; GSYM vector_norm; NORM_CAUCHY_SCHWARZ_ABS]);;

let TRACE_COVARIANCE_CAUCHY_SCHWARZ_SQUARE = prove
 (`!A B:real^M^N.
        trace(transp A ** B) pow 2
        <= trace(transp A ** A) * trace(transp B ** B)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_RSQRT_LE THEN
  SIMP_TAC[REAL_ABS_POS; REAL_LE_MUL; TRACE_COVARIANCE_POS_LE] THEN
  REWRITE_TAC[TRACE_COVARIANCE_CAUCHY_SCHWARZ_ABS; SQRT_MUL]);;

(* ------------------------------------------------------------------------- *)
(* Positive definite matrices.                                               *)
(* ------------------------------------------------------------------------- *)

let positive_definite = new_definition
 `positive_definite(A:real^N^N) <=>
         symmetric_matrix A /\ !x. ~(x = vec 0) ==> &0 < x dot (A ** x)`;;

let POSITIVE_DEFINITE_IMP_SYMMETRIC_MATRIX = prove
 (`!A:real^N^N. positive_definite A ==> symmetric_matrix A`,
  SIMP_TAC[positive_definite]);;

let POSITIVE_DEFINITE_IMP_SYMMETRIC = prove
 (`!A:real^N^N. positive_definite A ==> transp A = A`,
  REWRITE_TAC[GSYM symmetric_matrix; POSITIVE_DEFINITE_IMP_SYMMETRIC_MATRIX]);;

let POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE = prove
 (`!A:real^N^N.
        positive_definite A <=> positive_semidefinite A /\ invertible A`,
  GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`; positive_definite;
        FORALL_AND_THM; TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  SIMP_TAC[MESON[] `P a ==> ((!x:real^N. ~(x = a) ==> P x) <=> (!x. P x))`;
           DOT_LZERO; REAL_LE_REFL] THEN
  REWRITE_TAC[CONJ_ASSOC; GSYM positive_semidefinite] THEN
  ASM_CASES_TAC `positive_semidefinite(A:real^N^N)` THEN
  ASM_SIMP_TAC[POSITIVE_SEMIDEFINITE_ZERO_FORM_EQ] THEN
  REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET; INVERTIBLE_DET_NZ] THEN
  MESON_TAC[]);;

let POSITIVE_DEFINITE_SIMILAR_EQ = prove
 (`!A B:real^N^N.
        positive_definite(transp B ** A ** B) <=>
        invertible B /\ positive_definite A`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE] THEN
  REWRITE_TAC[INVERTIBLE_MATRIX_MUL; INVERTIBLE_TRANSP] THEN
  MESON_TAC[POSITIVE_SEMIDEFINITE_SIMILAR_EQ]);;

let POSITIVE_DEFINITE_1_GEN = prove
 (`!A:real^N^N.
        dimindex(:N) = 1 ==> (positive_definite A <=> &0 < A$1$1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[positive_definite; symmetric_matrix; transp; CART_EQ; dot] THEN
  ASM_SIMP_TAC[LAMBDA_BETA; ARITH; MATRIX_VECTOR_MUL_COMPONENT] THEN
  ASM_REWRITE_TAC[FORALL_1; SUM_1; dot; VEC_COMPONENT] THEN
  REWRITE_TAC[REAL_ARITH `x * a * x:real = a * x pow 2`] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[REAL_LT_MUL; REAL_LT_POW_2]] THEN
  DISCH_THEN(MP_TAC o SPEC `basis 1:real^N`) THEN
  SIMP_TAC[BASIS_COMPONENT; ARITH; DIMINDEX_GE_1; LE_REFL] THEN
  REAL_ARITH_TAC);;

let POSITIVE_DEFINITE_1 = prove
 (`!A:real^1^1. positive_definite A <=> &0 < A$1$1`,
  GEN_TAC THEN MATCH_MP_TAC POSITIVE_DEFINITE_1_GEN THEN
  REWRITE_TAC[DIMINDEX_1]);;

let POSITIVE_DEFINITE_IMP_INVERTIBLE = prove
 (`!A:real^N^N. positive_definite A ==> invertible A`,
  SIMP_TAC[POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE]);;

let POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE = prove
 (`!A:real^N^N. positive_definite A ==> positive_semidefinite A`,
  SIMP_TAC[POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE]);;

let POSITIVE_SEMIDEFINITE_POSITIVE_DEFINITE_ADD = prove
 (`!A B:real^N^N.
        positive_semidefinite A /\ positive_definite B
        ==> positive_definite(A + B)`,
  SIMP_TAC[positive_definite; positive_semidefinite; SYMMETRIC_MATRIX_ADD] THEN
  SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; DOT_RADD; REAL_LET_ADD]);;

let POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE_ADD = prove
 (`!A B:real^N^N.
        positive_definite A /\ positive_semidefinite B
        ==> positive_definite(A + B)`,
  SIMP_TAC[positive_definite; positive_semidefinite; SYMMETRIC_MATRIX_ADD] THEN
  SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; DOT_RADD; REAL_LTE_ADD]);;

let POSITIVE_DEFINITE_ADD = prove
 (`!A B:real^N^N.
        positive_definite A /\ positive_definite B
        ==> positive_definite(A + B)`,
  SIMP_TAC[positive_definite; SYMMETRIC_MATRIX_ADD] THEN
  SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; DOT_RADD; REAL_LT_ADD]);;

let POSITIVE_DEFINITE_CMUL = prove
 (`!c A:real^N^N.
        positive_definite A /\ &0 < c
        ==> positive_definite(c %% A)`,
  SIMP_TAC[positive_definite; SYMMETRIC_MATRIX_CMUL] THEN
  SIMP_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL; REAL_LT_MUL]);;

let NEARBY_POSITIVE_DEFINITE_MATRIX_GEN = prove
 (`!A:real^N^N B x.
        positive_semidefinite A /\ positive_definite B /\ &0 < x
        ==> positive_definite(A + x %% B)`,
  SIMP_TAC[POSITIVE_SEMIDEFINITE_POSITIVE_DEFINITE_ADD;
           POSITIVE_DEFINITE_CMUL]);;

let POSITIVE_DEFINITE_TRANSP = prove
 (`!A:real^N^N. positive_definite(transp A) <=> positive_definite A`,
  REWRITE_TAC[positive_definite; symmetric_matrix] THEN
  MESON_TAC[TRANSP_TRANSP]);;

let POSITIVE_DEFINITE_COVARIANCE = prove
 (`!A:real^N^N. positive_definite(transp A ** A) <=> invertible A`,
  REWRITE_TAC[POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE;
              POSITIVE_SEMIDEFINITE_COVARIANCE] THEN
  REWRITE_TAC[INVERTIBLE_MATRIX_MUL; INVERTIBLE_TRANSP]);;

let POSITIVE_DEFINITE_SIMILAR = prove
 (`!A B:real^N^N.
        positive_definite A /\ invertible B
        ==> positive_definite(transp B ** A ** B)`,
  SIMP_TAC[POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE;
           POSITIVE_SEMIDEFINITE_SIMILAR; INVERTIBLE_MATRIX_MUL;
           INVERTIBLE_TRANSP]);;

let POSITIVE_DEFINITE_DIAGONAL_MATRIX = prove
 (`!D:real^N^N.
        diagonal_matrix D /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 < D$i$i)
        ==> positive_definite D`,
  SIMP_TAC[positive_definite; DIAGONAL_IMP_SYMMETRIC_MATRIX] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I [DIAGONAL_MATRIX]) THEN
  SIMP_TAC[matrix_vector_mul; LAMBDA_BETA; dot] THEN
  SIMP_TAC[COND_RATOR; COND_RAND; REAL_MUL_LZERO] THEN
  CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  SIMP_TAC[SUM_DELTA] THEN MATCH_MP_TAC SUM_POS_LT THEN
  REWRITE_TAC[REAL_ARITH `x * d * x:real = d * x * x`] THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_LE_MUL; REAL_LE_SQUARE;
               REAL_LT_IMP_LE] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; VEC_COMPONENT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; REAL_LT_MUL; REAL_LT_POW_2]);;

let POSITIVE_DEFINITE_DIAGONAL_MATRIX_EQ = prove
 (`!D:real^N^N.
        diagonal_matrix D
        ==> (positive_definite D <=>
             !i. 1 <= i /\ i <= dimindex(:N) ==> &0 < D$i$i)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[POSITIVE_DEFINITE_DIAGONAL_MATRIX] THEN
  REWRITE_TAC[positive_definite] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `basis i:real^N`) THEN
  ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA;
               BASIS_NONZERO]);;

let DIAGONAL_POSITIVE_DEFINITE = prove
 (`!A:real^N^N i.
        positive_definite A /\ 1 <= i /\ i <= dimindex(:N)
        ==> &0 < A$i$i`,
  REWRITE_TAC[positive_definite] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `basis i:real^N`) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; DOT_BASIS; LAMBDA_BETA;
               BASIS_NONZERO]);;

let TRACE_POSITIVE_DEFINITE = prove
 (`!A:real^N^N. positive_definite A ==> &0 < trace A`,
  SIMP_TAC[trace; SUM_POS_LT_ALL; DIAGONAL_POSITIVE_DEFINITE;
           IN_NUMSEG; FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT; DIMINDEX_GE_1]);;

let POSITIVE_DEFINITE_MAT = prove
 (`!m. positive_definite(mat m:real^N^N) <=> 0 < m`,
  SIMP_TAC[POSITIVE_DEFINITE_DIAGONAL_MATRIX_EQ; DIAGONAL_MATRIX_MAT] THEN
  SIMP_TAC[mat; LAMBDA_BETA; REAL_OF_NUM_LT] THEN
  MESON_TAC[LE_REFL; DIMINDEX_GE_1]);;

let POSITIVE_DEFINITE_ID = prove
 (`positive_definite(mat 1:real^N^N)`,
  REWRITE_TAC[POSITIVE_DEFINITE_MAT; ARITH]);;

let POSITIVE_SEMIDEFINITE_MAT = prove
 (`!m. positive_semidefinite(mat m:real^N^N)`,
  SIMP_TAC[POSITIVE_SEMIDEFINITE_DIAGONAL_MATRIX_EQ; DIAGONAL_MATRIX_MAT] THEN
  SIMP_TAC[mat; LAMBDA_BETA; REAL_POS] THEN
  MESON_TAC[LE_REFL; DIMINDEX_GE_1]);;

let NEARBY_POSITIVE_DEFINITE_MATRIX = prove
 (`!A:real^N^N x.
      positive_semidefinite A /\ &0 < x ==> positive_definite(A + x %% mat 1)`,
  SIMP_TAC[NEARBY_POSITIVE_DEFINITE_MATRIX_GEN; POSITIVE_DEFINITE_ID]);;

let POSITIVE_SEMIDEFINITE_ANTISYM = prove
 (`!A:real^N^N. positive_semidefinite A /\ positive_semidefinite(--A) <=>
                A = mat 0`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[POSITIVE_SEMIDEFINITE_MAT; MATRIX_NEG_0] THEN
  ASM_SIMP_TAC[MATRIX_EQ_0; GSYM POSITIVE_SEMIDEFINITE_ZERO_FORM_EQ] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[positive_semidefinite] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LNEG; DOT_RNEG; IMP_IMP] THEN
  DISCH_THEN(CONJUNCTS_THEN (MP_TAC o CONJUNCT2)) THEN
  REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let LOEWNER_ORDER_ANTISYM = prove
 (`!(A:real^N^N) B.
        positive_semidefinite(A - B) /\ positive_semidefinite(B - A) <=>
        A = B`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM MATRIX_SUB_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM POSITIVE_SEMIDEFINITE_ANTISYM] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC MATRIX_ARITH);;

(* ------------------------------------------------------------------------- *)
(* Hadamard's inequality.                                                    *)
(* ------------------------------------------------------------------------- *)

let HADAMARD_INEQUALITY_ROW = prove
 (`!A:real^N^N. abs(det A) <= product(1..dimindex(:N)) (\i. norm(row i A))`,
  GEN_TAC THEN
  ABBREV_TAC `a = \i. (A:real^N^N)$i` THEN
  (MP_TAC o DISCH_ALL o instantiate_casewise_recursion)
  `?b. !j. b j :real^N =
            a j - vsum(1..j-1) (\i. (a j dot b i) / (b i dot b i) % b i)` THEN
  ANTS_TAC THENL
   [EXISTS_TAC `(<):num->num->bool` THEN REWRITE_TAC[WF_num] THEN
    MATCH_MP_TAC ADMISSIBLE_IMP_SUPERADMISSIBLE THEN
    REWRITE_TAC[admissible] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
    ASM_SIMP_TAC[IN_NUMSEG; ARITH_RULE `1 <= x /\ x <= y - 1 ==> x < y`];
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM)] THEN
  ABBREV_TAC `B:real^N^N = lambda i. b i` THEN
  TRANS_TAC REAL_LE_TRANS `abs(det(B:real^N^N))` THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `!n. det((lambda i. if i <= n then b i else a i):real^N^N) =
          det(A:real^N^N)`
     (MP_TAC o SPEC `dimindex(:N)`)
    THENL
     [MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
       [AP_TERM_TAC THEN EXPAND_TAC "a" THEN SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
        SIMP_TAC[ARITH_RULE `1 <= n ==> ~(n <= 0)`];
        X_GEN_TAC `n:num` THEN DISCH_THEN(SUBST1_TAC o SYM)] THEN
      ASM_CASES_TAC `dimindex(:N) <= n` THENL
       [AP_TERM_TAC THEN SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
        REPEAT STRIP_TAC THEN
        REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC;
        FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
         `~(n <= k) ==> SUC k <= n`))] THEN
      MP_TAC(ISPECL
       [`(lambda i. if i <= n then b i else a i):real^N^N`;
        `SUC n`;
        `--vsum (1..SUC n - 1)
                (\i. (a (SUC n) dot b i) / (b i dot b i) % b i):real^N`]
        DET_ROW_SPAN) THEN
      ASM_REWRITE_TAC[row; LAMBDA_ETA; ARITH_RULE `1 <= SUC n`] THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC SPAN_NEG THEN MATCH_MP_TAC SPAN_VSUM THEN
        REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
        MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_ELIM_THM] THEN
        EXISTS_TAC `i:num` THEN
        MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN
        SIMP_TAC[LAMBDA_BETA] THEN ASM_ARITH_TAC;
        DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
        GEN_REWRITE_TAC I [CART_EQ] THEN X_GEN_TAC `k:num` THEN
        SIMP_TAC[LAMBDA_BETA] THEN STRIP_TAC THEN
        ASM_CASES_TAC `SUC n = k` THEN
        ASM_SIMP_TAC[LE_REFL; LAMBDA_BETA; GSYM VECTOR_SUB; ARITH_RULE
         `SUC n = k ==> ~(k <= n)`] THEN
        REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC];
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC I [CART_EQ] THEN EXPAND_TAC "B" THEN
      SIMP_TAC[LAMBDA_BETA]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
          ~(i = j)
          ==> orthogonal (b i:real^N) (b j)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [MESON_TAC[ORTHOGONAL_SYM]; ALL_TAC] THEN
    GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN REWRITE_TAC[IMP_IMP] THEN
    REWRITE_TAC[ARITH_RULE
     `j < n /\ 1 <= n /\ n <= N /\ 1 <= j /\ j <= N /\ ~(n = j) <=>
      (1 <= n /\ n <= N) /\ (1 <= j /\ j <= N /\ j < n)`] THEN
    MATCH_MP_TAC num_WF THEN CONV_TAC NUM_REDUCE_CONV THEN
    X_GEN_TAC `n:num` THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_FORALL_THM] THEN
    REWRITE_TAC[IMP_IMP] THEN DISCH_TAC THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `n:num`) THEN
    REWRITE_TAC[orthogonal; DOT_LSUB; REAL_SUB_0] THEN
    SIMP_TAC[DOT_LSUM; FINITE_NUMSEG; DOT_LMUL] THEN TRANS_TAC EQ_TRANS
     `sum(1..n-1) (\j. if j = m then (a n:real^N) dot (b m) else &0)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [ASM_CASES_TAC `(b:num->real^N) m = vec 0` THEN
        ASM_REWRITE_TAC[DOT_RZERO; REAL_MUL_RZERO] THEN
        ASM_SIMP_TAC[DOT_EQ_0; REAL_DIV_RMUL];
        CONV_TAC SYM_CONV THEN REWRITE_TAC[REAL_ENTIRE] THEN
        DISJ2_TAC THEN REWRITE_TAC[GSYM orthogonal] THEN
        FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
         `~(m:num = n) ==> n < m \/ m < n`))
        THENL [ALL_TAC; ONCE_REWRITE_TAC[ORTHOGONAL_SYM]] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N) ==> norm(b i:real^N) <= norm(a i:real^N)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `i:num`) THEN
    REWRITE_TAC[NORM_LE; VECTOR_ARITH
     `(x - y:real^N) dot (x - y) = (x dot x + y dot y) - &2 * x dot y`] THEN
    REWRITE_TAC[REAL_ARITH `(a + b) - x <= a <=> b <= x`] THEN
    SIMP_TAC[DOT_RSUM; FINITE_NUMSEG; DOT_RMUL; GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ x = y ==> y <= &2 * x`) THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ARITH `x / y * x:real = (x * x) / y`] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_SQUARE; DOT_POS_LE];
      AP_TERM_TAC] THEN
    TRANS_TAC EQ_TRANS
      `sum(1..i-1) (\k. if k = j then (a i:real^N) dot (b j) else &0)` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[SUM_DELTA; IN_NUMSEG]; ALL_TAC] THEN
    SIMP_TAC[DOT_LSUM; FINITE_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[DOT_LMUL] THEN
    ASM_CASES_TAC `(b:num->real^N) j = vec 0` THEN
    ASM_REWRITE_TAC[DOT_RZERO; REAL_MUL_RZERO; COND_ID] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[DOT_EQ_0; REAL_DIV_RMUL] THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[REAL_ENTIRE] THEN
    DISJ2_TAC THEN REWRITE_TAC[GSYM orthogonal] THEN
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
     `~(m:num = n) ==> n < m \/ m < n`))
    THENL [ALL_TAC; ONCE_REWRITE_TAC[ORTHOGONAL_SYM]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `product(1..dimindex(:N)) (\i. norm(b i:real^N))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN
    REWRITE_TAC[NORM_POS_LE; row; LAMBDA_ETA] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    TRANS_TAC REAL_LE_TRANS `norm((a:num->real^N) i)` THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "a" THEN REWRITE_TAC[REAL_LE_REFL]] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ abs x <= abs y ==> abs x <= y`) THEN
  SIMP_TAC[PRODUCT_POS_LE_NUMSEG; NORM_POS_LE; REAL_LE_SQUARE_ABS] THEN
  REWRITE_TAC[REAL_POW_2; GSYM PRODUCT_MUL_NUMSEG] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM DET_TRANSP] THEN
  REWRITE_TAC[GSYM DET_MUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) DET_DIAGONAL o lhand o snd) THEN
  SIMP_TAC[DIAGONAL_MATRIX_MUL_EQ; pairwise; GSYM ROW_TRANSP; IN_NUMSEG] THEN
  EXPAND_TAC "B" THEN
  SIMP_TAC[TRANSP_TRANSP; row; LAMBDA_ETA; LAMBDA_BETA] THEN
  ASM_REWRITE_TAC[GSYM CONJ_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
  EXPAND_TAC "B" THEN REWRITE_TAC[transp; GSYM REAL_POW_2] THEN
  SIMP_TAC[matrix_mul; NORM_POW_2; dot; LAMBDA_BETA; dot]);;

let HADAMARD_INEQUALITY_COLUMN = prove
 (`!A:real^N^N. abs(det A) <= product(1..dimindex(:N)) (\i. norm(column i A))`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM DET_TRANSP] THEN
  SIMP_TAC[GSYM ROW_TRANSP; HADAMARD_INEQUALITY_ROW]);;

(* ------------------------------------------------------------------------- *)
(* Orthogonality of a transformation and matrix.                             *)
(* ------------------------------------------------------------------------- *)

let orthogonal_transformation = new_definition
 `orthogonal_transformation(f:real^N->real^N) <=>
        linear f /\ !v w. f(v) dot f(w) = v dot w`;;

let ORTHOGONAL_TRANSFORMATION = prove
 (`!f. orthogonal_transformation f <=> linear f /\ !v. norm(f v) = norm(v)`,
  GEN_TAC THEN REWRITE_TAC[orthogonal_transformation] THEN EQ_TAC THENL
   [MESON_TAC[vector_norm]; SIMP_TAC[DOT_NORM] THEN MESON_TAC[LINEAR_ADD]]);;

let ORTHOGONAL_ORTHOGONAL_TRANSFORMATION = prove
 (`!f x y:real^N.
        orthogonal_transformation f
        ==> (orthogonal (f x) (f y) <=> orthogonal x y)`,
  SIMP_TAC[orthogonal; orthogonal_transformation]);;

let ORTHOGONAL_TRANSFORMATION_COMPOSE = prove
 (`!f g. orthogonal_transformation f /\ orthogonal_transformation g
         ==> orthogonal_transformation(f o g)`,
  SIMP_TAC[orthogonal_transformation; LINEAR_COMPOSE; o_THM]);;

let ORTHOGONAL_TRANSFORMATION_NEG = prove
 (`!f:real^N->real^N.
     orthogonal_transformation(\x. --(f x)) <=> orthogonal_transformation f`,
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION; LINEAR_COMPOSE_NEG_EQ; NORM_NEG]);;

let ORTHOGONAL_TRANSFORMATION_LINEAR = prove
 (`!f:real^N->real^N. orthogonal_transformation f ==> linear f`,
  SIMP_TAC[orthogonal_transformation]);;

let ORTHOGONAL_TRANSFORMATION_INJECTIVE = prove
 (`!f:real^N->real^N.
        orthogonal_transformation f ==> !x y. f x = f y ==> x = y`,
  SIMP_TAC[LINEAR_INJECTIVE_0; ORTHOGONAL_TRANSFORMATION; GSYM NORM_EQ_0]);;

let ORTHOGONAL_TRANSFORMATION_SURJECTIVE = prove
 (`!f:real^N->real^N.
        orthogonal_transformation f ==> !y. ?x. f x = y`,
  MESON_TAC[LINEAR_INJECTIVE_IMP_SURJECTIVE;
            ORTHOGONAL_TRANSFORMATION_INJECTIVE; orthogonal_transformation]);;

let orthogonal_matrix = new_definition
 `orthogonal_matrix(Q:real^N^N) <=>
      transp(Q) ** Q = mat 1 /\ Q ** transp(Q) = mat 1`;;

let ORTHOGONAL_MATRIX = prove
 (`orthogonal_matrix(Q:real^N^N) <=> transp(Q) ** Q = mat 1`,
  MESON_TAC[MATRIX_LEFT_RIGHT_INVERSE; orthogonal_matrix]);;

let ORTHOGONAL_MATRIX_ALT = prove
 (`!A:real^N^N. orthogonal_matrix A <=> A ** transp A = mat 1`,
  MESON_TAC[MATRIX_LEFT_RIGHT_INVERSE; orthogonal_matrix]);;

let ORTHOGONAL_MATRIX_TRANSP = prove
 (`!A:real^N^N. orthogonal_matrix(transp A) <=> orthogonal_matrix A`,
  REWRITE_TAC[orthogonal_matrix; TRANSP_TRANSP; CONJ_ACI]);;

let ORTHOGONAL_MATRIX_TRANSP_LMUL = prove
 (`!P:real^N^N. orthogonal_matrix P ==> transp P ** P = mat 1`,
  REWRITE_TAC[ORTHOGONAL_MATRIX]);;

let ORTHOGONAL_MATRIX_TRANSP_RMUL = prove
 (`!P:real^N^N. orthogonal_matrix P ==> P ** transp P = mat 1`,
  REWRITE_TAC[ORTHOGONAL_MATRIX_ALT]);;

let NORM_VECTORIZE_ORTHOGONAL_MATRIX_RMUL = prove
 (`!A:real^N^N P:real^N^N.
       orthogonal_matrix P ==> norm(vectorize(A ** P)) = norm(vectorize A)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NORM_EQ; DOT_VECTORIZE; MATRIX_TRANSP_MUL] THEN
  GEN_REWRITE_TAC LAND_CONV [TRACE_MUL_SYM] THEN
  ONCE_REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
   [GSYM MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[ORTHOGONAL_MATRIX_TRANSP_RMUL; MATRIX_MUL_RID] THEN
  MATCH_ACCEPT_TAC TRACE_MUL_SYM);;

let NORM_VECTORIZE_ORTHOGONAL_MATRIX_LMUL = prove
 (`!A:real^N^N P:real^N^N.
       orthogonal_matrix P ==> norm(vectorize(P ** A)) = norm(vectorize A)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM NORM_VECTORIZE_TRANSP] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL] THEN
  MATCH_MP_TAC NORM_VECTORIZE_ORTHOGONAL_MATRIX_RMUL THEN
  ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_TRANSP]);;

let ORTHOGONAL_MATRIX_ID = prove
 (`orthogonal_matrix(mat 1)`,
  REWRITE_TAC[orthogonal_matrix; TRANSP_MAT; MATRIX_MUL_LID]);;

let ORTHOGONAL_MATRIX_MUL = prove
 (`!A B. orthogonal_matrix A /\ orthogonal_matrix B
         ==> orthogonal_matrix(A ** B)`,
  REWRITE_TAC[orthogonal_matrix; MATRIX_TRANSP_MUL] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MATRIX_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[MATRIX_MUL_LID; MATRIX_MUL_RID]);;

let ORTHOGONAL_TRANSFORMATION_MATRIX = prove
 (`!f:real^N->real^N.
     orthogonal_transformation f <=> linear f /\ orthogonal_matrix(matrix f)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[orthogonal_transformation; ORTHOGONAL_MATRIX] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`basis i:real^N`; `basis j:real^N`]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
    REWRITE_TAC[DOT_MATRIX_VECTOR_MUL] THEN
    ABBREV_TAC `A = transp (matrix f) ** matrix(f:real^N->real^N)` THEN
    ASM_SIMP_TAC[matrix_mul; columnvector; rowvector; basis; LAMBDA_BETA;
             SUM_DELTA; DIMINDEX_1; LE_REFL; dot; IN_NUMSEG; mat;
             MESON[REAL_MUL_LID; REAL_MUL_LZERO; REAL_MUL_RID; REAL_MUL_RZERO]
              `(if b then &1 else &0) * x = (if b then x else &0) /\
               x * (if b then &1 else &0) = (if b then x else &0)`];
    REWRITE_TAC[orthogonal_matrix; ORTHOGONAL_TRANSFORMATION; NORM_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
    ASM_REWRITE_TAC[DOT_MATRIX_VECTOR_MUL] THEN
    SIMP_TAC[DOT_MATRIX_PRODUCT; MATRIX_MUL_LID]]);;

let ORTHOGONAL_MATRIX_TRANSFORMATION = prove
 (`!A:real^N^N. orthogonal_matrix A <=> orthogonal_transformation(\x. A ** x)`,
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX; MATRIX_VECTOR_MUL_LINEAR] THEN
  REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL]);;

let ORTHOGONAL_MATRIX_MATRIX = prove
 (`!f:real^N->real^N.
    orthogonal_transformation f ==> orthogonal_matrix(matrix f)`,
  SIMP_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX]);;

let ORTHOGONAL_MATRIX_NORM_EQ = prove
 (`!A. orthogonal_matrix A <=> !x. norm(A ** x) = norm x`,
  REWRITE_TAC[ORTHOGONAL_MATRIX_TRANSFORMATION; MATRIX_VECTOR_MUL_LINEAR;
              ORTHOGONAL_TRANSFORMATION]);;

let ORTHOGONAL_MATRIX_NORM = prove
 (`!A x:real^N. orthogonal_matrix A ==> norm(A ** x) = norm x`,
  SIMP_TAC[ORTHOGONAL_MATRIX_TRANSFORMATION; ORTHOGONAL_TRANSFORMATION]);;

let DET_ORTHOGONAL_MATRIX = prove
 (`!Q. orthogonal_matrix Q ==> det(Q) = &1 \/ det(Q) = -- &1`,
  GEN_TAC THEN REWRITE_TAC[REAL_RING `x = &1 \/ x = -- &1 <=> x * x = &1`] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM DET_TRANSP] THEN
  SIMP_TAC[GSYM DET_MUL; orthogonal_matrix; DET_I]);;

let ORTHOGONAL_MATRIX_IMP_INVERTIBLE = prove
 (`!A:real^N^N. orthogonal_matrix A ==> invertible A`,
  GEN_TAC THEN REWRITE_TAC[INVERTIBLE_DET_NZ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DET_ORTHOGONAL_MATRIX) THEN
  REAL_ARITH_TAC);;

let MATRIX_MUL_LTRANSP_DOT_COLUMN = prove
 (`!A:real^N^M. transp A ** A = (lambda i j. (column i A) dot (column j A))`,
  SIMP_TAC[matrix_mul; CART_EQ; LAMBDA_BETA; transp; dot; column]);;

let MATRIX_MUL_RTRANSP_DOT_ROW = prove
 (`!A:real^N^M. A ** transp A = (lambda i j. (row i A) dot (row j A))`,
  SIMP_TAC[matrix_mul; CART_EQ; LAMBDA_BETA; transp; dot; row]);;

let ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS = prove
 (`!A:real^N^N.
        orthogonal_matrix A <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(column i A) = &1) /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
               ==> orthogonal (column i A) (column j A))`,
  REWRITE_TAC[ORTHOGONAL_MATRIX] THEN
  SIMP_TAC[MATRIX_MUL_LTRANSP_DOT_COLUMN; CART_EQ; mat; LAMBDA_BETA] THEN
  REWRITE_TAC[orthogonal; NORM_EQ_1] THEN MESON_TAC[]);;

let ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS = prove
 (`!A:real^N^N.
        orthogonal_matrix A <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(row i A) = &1) /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
               ==> orthogonal (row i A) (row j A))`,
  ONCE_REWRITE_TAC[GSYM ORTHOGONAL_MATRIX_TRANSP] THEN
  SIMP_TAC[ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS; COLUMN_TRANSP]);;

let ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_INDEXED = prove
 (`!A:real^N^N.
        orthogonal_matrix A <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(row i A) = &1) /\
        pairwise (\i j. orthogonal (row i A) (row j A)) (1..dimindex(:N))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ORTHOGONAL_MATRIX_ALT] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; pairwise; MAT_COMPONENT] THEN
  SIMP_TAC[MATRIX_MUL_RTRANSP_DOT_ROW; IN_NUMSEG; LAMBDA_BETA] THEN
  REWRITE_TAC[NORM_EQ_SQUARE; REAL_POS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[orthogonal] THEN
  MESON_TAC[]);;

let ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_PAIRWISE = prove
 (`!A:real^N^N.
        orthogonal_matrix A <=>
        CARD(rows A) = dimindex(:N) /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(row i A) = &1) /\
        pairwise orthogonal (rows A)`,
  REWRITE_TAC[rows; ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_INDEXED] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[PAIRWISE_IMAGE; GSYM numseg] THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r /\ s)) ==> (p /\ q <=> r /\ p /\ s)`) THEN
  DISCH_TAC THEN GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
    [GSYM CARD_NUMSEG_1] THEN
  SIMP_TAC[CARD_IMAGE_EQ_INJ; FINITE_NUMSEG] THEN
  REWRITE_TAC[pairwise; IN_NUMSEG] THEN
  ASM_MESON_TAC[ORTHOGONAL_REFL; NORM_ARITH `~(norm(vec 0:real^N) = &1)`]);;

let ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_SPAN = prove
 (`!A:real^N^N.
        orthogonal_matrix A <=>
        span(rows A) = (:real^N) /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(row i A) = &1) /\
        pairwise orthogonal (rows A)`,
  GEN_TAC THEN REWRITE_TAC[ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_PAIRWISE] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(SET_RULE `UNIV SUBSET s ==> s = UNIV`) THEN
    MATCH_MP_TAC CARD_GE_DIM_INDEPENDENT THEN
    ASM_REWRITE_TAC[DIM_UNIV; SUBSET_UNIV; LE_REFL];
    CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM DIM_UNIV] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[DIM_SPAN] THEN
    MATCH_MP_TAC DIM_EQ_CARD] THEN
  MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
  ASM_REWRITE_TAC[rows; IN_ELIM_THM] THEN
  ASM_MESON_TAC[NORM_ARITH `~(norm(vec 0:real^N) = &1)`]);;

let ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS_INDEXED = prove
 (`!A:real^N^N.
      orthogonal_matrix A <=>
      (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(column i A) = &1) /\
      pairwise (\i j. orthogonal (column i A) (column j A)) (1..dimindex(:N))`,
  ONCE_REWRITE_TAC[GSYM ORTHOGONAL_MATRIX_TRANSP] THEN
  REWRITE_TAC[ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_INDEXED] THEN
  SIMP_TAC[ROW_TRANSP; ROWS_TRANSP; pairwise; IN_NUMSEG]);;

let ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS_PAIRWISE = prove
 (`!A:real^N^N.
        orthogonal_matrix A <=>
        CARD(columns A) = dimindex(:N) /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(column i A) = &1) /\
        pairwise orthogonal (columns A)`,
  ONCE_REWRITE_TAC[GSYM ORTHOGONAL_MATRIX_TRANSP] THEN
  REWRITE_TAC[ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_PAIRWISE] THEN
  SIMP_TAC[ROW_TRANSP; ROWS_TRANSP]);;

let ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS_SPAN = prove
 (`!A:real^N^N.
        orthogonal_matrix A <=>
        span(columns A) = (:real^N) /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(column i A) = &1) /\
        pairwise orthogonal (columns A)`,
  ONCE_REWRITE_TAC[GSYM ORTHOGONAL_MATRIX_TRANSP] THEN
  REWRITE_TAC[ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_SPAN] THEN
  SIMP_TAC[ROW_TRANSP; ROWS_TRANSP]);;

let ORTHOGONAL_MATRIX_2 = prove
 (`!A:real^2^2. orthogonal_matrix A <=>
                A$1$1 pow 2 + A$2$1 pow 2 = &1 /\
                A$1$2 pow 2 + A$2$2 pow 2 = &1 /\
                A$1$1 * A$1$2 + A$2$1 * A$2$2 = &0`,
  SIMP_TAC[orthogonal_matrix; CART_EQ; matrix_mul; LAMBDA_BETA;
           TRANSP_COMPONENT; MAT_COMPONENT] THEN
  REWRITE_TAC[DIMINDEX_2; FORALL_2; SUM_2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING);;

let ORTHOGONAL_MATRIX_2_ALT = prove
 (`!A:real^2^2. orthogonal_matrix A <=>
                A$1$1 pow 2 + A$2$1 pow 2 = &1 /\
                (A$1$1 = A$2$2 /\ A$1$2 = --(A$2$1) \/
                 A$1$1 = --(A$2$2) /\ A$1$2 = A$2$1)`,
  REWRITE_TAC[ORTHOGONAL_MATRIX_2] THEN CONV_TAC REAL_RING);;

let ORTHOGONAL_MATRIX_INV = prove
 (`!A:real^N^N. orthogonal_matrix A ==> matrix_inv A = transp A`,
  MESON_TAC[orthogonal_matrix; MATRIX_INV_UNIQUE]);;

let ORTHOGONAL_MATRIX_INV_EQ = prove
 (`!A:real^N^N. orthogonal_matrix(matrix_inv A) <=> orthogonal_matrix A`,
  MATCH_MP_TAC(MESON[]
   `(!x. f(f x) = x) /\ (!x. P x ==> P(f x)) ==> (!x. P(f x) <=> P x)`) THEN
  REWRITE_TAC[MATRIX_INV_INV] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP ORTHOGONAL_MATRIX_INV) THEN
  ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_TRANSP]);;

let ORTHOGONAL_TRANSFORMATION_ORTHOGONAL_EIGENVECTORS = prove
 (`!f:real^N->real^N v w a b.
        orthogonal_transformation f /\ f v = a % v /\ f w = b % w /\ ~(a = b)
        ==> orthogonal v w`,
  REWRITE_TAC[orthogonal_transformation] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPECL [`v:real^N`; `v:real^N`] th) THEN
    MP_TAC(SPECL [`v:real^N`; `w:real^N`] th) THEN
    MP_TAC(SPECL [`w:real^N`; `w:real^N`] th)) THEN
  ASM_REWRITE_TAC[DOT_LMUL; DOT_RMUL; orthogonal] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; REAL_RING `x * y = y <=> x = &1 \/ y = &0`] THEN
  REWRITE_TAC[DOT_EQ_0] THEN
  ASM_CASES_TAC `v:real^N = vec 0` THEN ASM_REWRITE_TAC[DOT_LZERO] THEN
  ASM_CASES_TAC `w:real^N = vec 0` THEN ASM_REWRITE_TAC[DOT_RZERO] THEN
  ASM_CASES_TAC `(v:real^N) dot w = &0` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(a:real = b)` THEN CONV_TAC REAL_RING);;

let ORTHOGONAL_MATRIX_ORTHOGONAL_EIGENVECTORS = prove
 (`!A:real^N^N v w a b.
        orthogonal_matrix A /\ A ** v = a % v /\ A ** w = b % w /\ ~(a = b)
        ==> orthogonal v w`,
  REWRITE_TAC[ORTHOGONAL_MATRIX_TRANSFORMATION;
              ORTHOGONAL_TRANSFORMATION_ORTHOGONAL_EIGENVECTORS]);;

let ORTHOGONAL_TRANSFORMATION_ID = prove
 (`orthogonal_transformation(\x. x)`,
  REWRITE_TAC[orthogonal_transformation; LINEAR_ID]);;

let ORTHOGONAL_TRANSFORMATION_I = prove
 (`orthogonal_transformation I`,
  REWRITE_TAC[I_DEF; ORTHOGONAL_TRANSFORMATION_ID]);;

let ORTHOGONAL_TRANSFORMATION_NEGATION = prove
 (`orthogonal_transformation(--)`,
  REWRITE_TAC[orthogonal_transformation; LINEAR_NEGATION; DOT_LNEG; DOT_RNEG;
              REAL_NEG_NEG]);;

let ORTHOGONAL_TRANSFORMATION_1_GEN = prove
 (`!f:real^N->real^N.
        dimindex(:N) = 1
        ==> (orthogonal_transformation f <=> f = I \/ f = (--))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[I_DEF] THEN
  GEN_REWRITE_TAC (funpow 3 RAND_CONV) [GSYM ETA_AX] THEN
  EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_ID;
                  ORTHOGONAL_TRANSFORMATION_NEG] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ORTHOGONAL_TRANSFORMATION]) THEN
  ASM_SIMP_TAC[LINEAR_1_GEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[NORM_MUL] THEN
  DISCH_THEN(MP_TAC o SPEC `basis 1:real^N`) THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL; DIMINDEX_1] THEN
  REWRITE_TAC[REAL_ARITH `abs x * &1 = &1 <=> x = &1 \/ x = -- &1`] THEN
  MATCH_MP_TAC MONO_OR THEN SIMP_TAC[FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN CONV_TAC VECTOR_ARITH);;

let ORTHOGONAL_MATRIX_1 = prove
 (`!m:real^N^N.
        dimindex(:N) = 1
        ==> (orthogonal_matrix m <=> m = mat 1 \/ m = --mat 1)`,
  REWRITE_TAC[ORTHOGONAL_MATRIX_TRANSFORMATION] THEN
  SIMP_TAC[ORTHOGONAL_TRANSFORMATION_1_GEN] THEN
  REWRITE_TAC[MATRIX_EQ; FUN_EQ_THM] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LID; MATRIX_VECTOR_MUL_LNEG] THEN
  REWRITE_TAC[I_THM]);;

let MATRIX_INV_ORTHOGONAL_LMUL = prove
 (`!U A:real^M^N.
        orthogonal_matrix U
        ==> matrix_inv(U ** A) = matrix_inv A ** matrix_inv U`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
  REWRITE_TAC[symmetric_matrix] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; GSYM MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[ORTHOGONAL_MATRIX_INV; TRANSP_TRANSP] THEN
  REWRITE_TAC[MESON[MATRIX_MUL_ASSOC]
   `(A:real^M^N) ** transp U ** U ** (B:real^P^M) =
    A ** (transp U ** U) ** B`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[orthogonal_matrix]) THEN
  ASM_REWRITE_TAC[MATRIX_MUL_LID] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM orthogonal_matrix]) THEN
  ASM_SIMP_TAC[MATRIX_MUL_LCANCEL; ORTHOGONAL_MATRIX_IMP_INVERTIBLE] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_MUL_RCANCEL; ORTHOGONAL_MATRIX_IMP_INVERTIBLE;
               ORTHOGONAL_MATRIX_TRANSP] THEN
  REWRITE_TAC[GSYM MATRIX_TRANSP_MUL; GSYM MATRIX_MUL_ASSOC] THEN
  REWRITE_TAC[REWRITE_RULE[symmetric_matrix] SYMMETRIC_MATRIX_INV_LMUL;
              REWRITE_RULE[symmetric_matrix] SYMMETRIC_MATRIX_INV_RMUL;
              MATRIX_INV_MUL_INNER; MATRIX_INV_MUL_OUTER]);;

let MATRIX_INV_ORTHOGONAL_RMUL = prove
 (`!U A:real^M^N.
        orthogonal_matrix U
        ==> matrix_inv(A ** U) = matrix_inv U ** matrix_inv A`,
  ONCE_REWRITE_TAC[GSYM TRANSP_EQ; GSYM ORTHOGONAL_MATRIX_TRANSP] THEN
  SIMP_TAC[TRANSP_MATRIX_INV; MATRIX_TRANSP_MUL; MATRIX_INV_ORTHOGONAL_LMUL]);;

let ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_LEFT = prove
 (`!f:real^N->real^N.
        orthogonal_transformation f <=> linear f /\ adjoint f o f = I`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; I_THM; o_THM] THEN EQ_TAC THENL
   [REWRITE_TAC[orthogonal_transformation] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ADJOINT_WORKS th]) THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN REWRITE_TAC[VECTOR_EQ_LDOT];
    STRIP_TAC THEN ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION] THEN
    REWRITE_TAC[NORM_EQ] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ADJOINT_WORKS th]) THEN
    ASM_REWRITE_TAC[]]);;

let ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_RIGHT = prove
 (`!f:real^N->real^N.
        orthogonal_transformation f <=> linear f /\ f o adjoint f = I`,
  GEN_TAC THEN REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_LEFT] THEN
  MESON_TAC[ADJOINT_LINEAR; LINEAR_INVERSE_LEFT]);;

let ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT = prove
 (`!f:real^N->real^N.
        orthogonal_transformation f <=>
        linear f /\ adjoint f o f = I /\ f o adjoint f = I`,
  MESON_TAC[ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_LEFT;
            ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_RIGHT]);;

let ORTHOGONAL_TRANSFORMATION_ADJOINT = prove
 (`!f:real^N->real^N.
        orthogonal_transformation f ==> orthogonal_transformation(adjoint f)`,
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_LEFT] THEN
  SIMP_TAC[ADJOINT_ADJOINT; ADJOINT_LINEAR] THEN
  MESON_TAC[ADJOINT_LINEAR; LINEAR_INVERSE_LEFT]);;

let ORTHOGONAL_TRANSFORMATION_ADJOINT_EQ =
 (`!f:real^N->real^N.
        linear f
        ==> (orthogonal_transformation(adjoint f) <=>
             orthogonal_transformation f)`,
  MESON_TAC[ORTHOGONAL_TRANSFORMATION_ADJOINT; ADJOINT_LINEAR;
            ADJOINT_ADJOINT]);;

let ONORM_ORTHOGONAL_TRANSFORMATION = prove
 (`!f:real^N->real^N. orthogonal_transformation f ==> onorm f = &1`,
  SIMP_TAC[ORTHOGONAL_TRANSFORMATION; onorm] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUP_UNIQUE THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  X_GEN_TAC `c:real` THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(MP_TAC o SPEC `basis 1:real^N`) THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL]);;

let ONORM_ORTHOGONAL_MATRIX = prove
 (`!A:real^N^N. orthogonal_matrix A ==> onorm(\x. A ** x) = &1`,
  REWRITE_TAC[ORTHOGONAL_MATRIX_TRANSFORMATION] THEN
  REWRITE_TAC[ONORM_ORTHOGONAL_TRANSFORMATION]);;

(* ------------------------------------------------------------------------- *)
(* Linearity of scaling, and hence isometry, that preserves origin.          *)
(* ------------------------------------------------------------------------- *)

let SCALING_LINEAR = prove
 (`!f:real^M->real^N c.
        (f(vec 0) = vec 0) /\ (!x y. dist(f x,f y) = c * dist(x,y))
        ==> linear(f)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!v w. ((f:real^M->real^N) v) dot (f w) = c pow 2 * (v dot w)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN `v:real^M` o
      SPECL [`v:real^M`; `vec 0 :real^M`]) THEN
    REWRITE_TAC[dist] THEN ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[DOT_NORM_SUB; GSYM dist] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[linear; VECTOR_EQ] THEN
  ASM_REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  REAL_ARITH_TAC);;

let ISOMETRY_LINEAR = prove
 (`!f:real^M->real^N.
        (f(vec 0) = vec 0) /\ (!x y. dist(f x,f y) = dist(x,y))
        ==> linear(f)`,
  MESON_TAC[SCALING_LINEAR; REAL_MUL_LID]);;

let ISOMETRY_IMP_AFFINITY = prove
 (`!f:real^M->real^N.
        (!x y. dist(f x,f y) = dist(x,y))
        ==> ?h. linear h /\ !x. f(x) = f(vec 0) + h(x)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\x. (f:real^M->real^N) x - f(vec 0)` THEN
  REWRITE_TAC[VECTOR_ARITH `a + (x - a):real^N = x`] THEN
  MATCH_MP_TAC ISOMETRY_LINEAR THEN REWRITE_TAC[VECTOR_SUB_REFL] THEN
  ASM_REWRITE_TAC[NORM_ARITH `dist(x - a:real^N,y - a) = dist(x,y)`]);;

(* ------------------------------------------------------------------------- *)
(* An orthogonality-preserving linear map is a similarity.                   *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONALITY_PRESERVING_IMP_SCALING = prove
 (`!f:real^M->real^N.
        linear f /\ (!x y. orthogonal x y ==> orthogonal (f x) (f y))
        ==> ?c. &0 <= c /\ !x. norm(f x) = c * norm(x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?c. &0 <= c /\
        !i. 1 <= i /\ i <= dimindex(:M)
            ==> norm((f:real^M->real^N)(basis i)) = c`
  MP_TAC THENL
   [MATCH_MP_TAC(MESON[]
     `(!x. A(f x)) /\ (?x. P x) /\ (!i j. P i /\ P j ==> f i = f j)
      ==> ?c. A c /\ !x. P x ==> f x = c`) THEN
    REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [EXISTS_TAC `1` THEN REWRITE_TAC[LE_REFL; DIMINDEX_GE_1]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o ISPECL
     [`basis i + basis j:real^M`; `basis i - basis j:real^M`]) THEN
    ASM_SIMP_TAC[orthogonal; LINEAR_ADD; LINEAR_SUB; VECTOR_ARITH
     `(x + y:real^M) dot (x - y) = x dot x - y dot y`] THEN

    ASM_SIMP_TAC[GSYM NORM_POW_2; REAL_SUB_0; NORM_BASIS] THEN
    REWRITE_TAC[NORM_POW_2; GSYM NORM_EQ];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[NORM_EQ_SQUARE; NORM_POS_LE; REAL_LE_MUL]  THEN
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[GSYM NORM_POW_2] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV)
     [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      NORM_VSUM_PYTHAGOREAN o lhand o snd) THEN
    REWRITE_TAC[pairwise; IN_NUMSEG; ORTHOGONAL_MUL; FINITE_NUMSEG] THEN
    ASM_SIMP_TAC[ORTHOGONAL_BASIS_BASIS] THEN DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_POW_MUL; SUM_RMUL; REAL_POW2_ABS] THEN
    REWRITE_TAC[REAL_POW_2; GSYM dot; GSYM NORM_POW_2]]);;

let ORTHOGONALITY_PRESERVING_EQ_SIMILARITY_ALT,
    ORTHOGONALITY_PRESERVING_EQ_SIMILARITY =
  (CONJ_PAIR o prove)
 (`(!f:real^N->real^N.
        linear f /\ (!x y. orthogonal x y ==> orthogonal (f x) (f y)) <=>
        ?c g. &0 <= c /\ orthogonal_transformation g /\ f = \z. c % g z) /\
   (!f:real^N->real^N.
        linear f /\ (!x y. orthogonal x y ==> orthogonal (f x) (f y)) <=>
        ?c g. orthogonal_transformation g /\ f = \z. c % g z)`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC(TAUT
   `(q ==> r) /\ (r ==> p) /\ (p ==> q)
    ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    STRIP_TAC THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR; LINEAR_COMPOSE_CMUL] THEN
    ASM_SIMP_TAC[ORTHOGONAL_MUL; ORTHOGONAL_ORTHOGONAL_TRANSFORMATION];
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ORTHOGONALITY_PRESERVING_IMP_SCALING) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real` THEN
    ASM_CASES_TAC `c = &0` THENL
     [ASM_SIMP_TAC[REAL_MUL_LZERO; FUN_EQ_THM; NORM_EQ_0] THEN
      DISCH_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; ORTHOGONAL_TRANSFORMATION_ID];
      STRIP_TAC THEN EXISTS_TAC `\x. inv(c) % (f:real^N->real^N) x` THEN
      ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION; FUN_EQ_THM] THEN
      ASM_SIMP_TAC[LINEAR_COMPOSE_CMUL; NORM_MUL; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID; REAL_ABS_INV] THEN
      ASM_REWRITE_TAC[real_abs; REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_LID]]]);;

(* ------------------------------------------------------------------------- *)
(* Hence another formulation of orthogonal transformation.                   *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_TRANSFORMATION_ISOMETRY = prove
 (`!f:real^N->real^N.
        orthogonal_transformation f <=>
        (f(vec 0) = vec 0) /\ (!x y. dist(f x,f y) = dist(x,y))`,
  GEN_TAC THEN REWRITE_TAC[ORTHOGONAL_TRANSFORMATION] THEN EQ_TAC THENL
   [MESON_TAC[LINEAR_0; LINEAR_SUB; dist]; STRIP_TAC] THEN
  ASM_SIMP_TAC[ISOMETRY_LINEAR] THEN X_GEN_TAC `x:real^N` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `vec 0:real^N`]) THEN
  ASM_REWRITE_TAC[dist; VECTOR_SUB_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Can extend an isometry from unit sphere.                                  *)
(* ------------------------------------------------------------------------- *)

let ISOMETRY_SPHERE_EXTEND = prove
 (`!f:real^N->real^N.
        (!x. norm(x) = &1 ==> norm(f x) = &1) /\
        (!x y. norm(x) = &1 /\ norm(y) = &1 ==> dist(f x,f y) = dist(x,y))
        ==> ?g. orthogonal_transformation g /\
                (!x. norm(x) = &1 ==> g(x) = f(x))`,
  let lemma = prove
   (`!x:real^N y:real^N x':real^N y':real^N x0 y0 x0' y0'.
          x = norm(x) % x0 /\ y = norm(y) % y0 /\
          x' = norm(x) % x0' /\ y' = norm(y) % y0' /\
          norm(x0) = &1 /\ norm(x0') = &1 /\ norm(y0) = &1 /\ norm(y0') = &1 /\
          norm(x0' - y0') = norm(x0 - y0)
          ==> norm(x' - y') = norm(x - y)`,
    REPEAT GEN_TAC THEN
    MAP_EVERY ABBREV_TAC [`a = norm(x:real^N)`; `b = norm(y:real^N)`] THEN
    REPLICATE_TAC 4 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[NORM_EQ; NORM_EQ_1] THEN
    REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
    REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_RING) in
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\x. if x = vec 0 then vec 0
                  else norm(x) % (f:real^N->real^N)(inv(norm x) % x)` THEN
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_ISOMETRY] THEN
  SIMP_TAC[VECTOR_MUL_LID; REAL_INV_1] THEN CONJ_TAC THENL
   [ALL_TAC; MESON_TAC[NORM_0; REAL_ARITH `~(&1 = &0)`]] THEN
  REPEAT GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[dist; VECTOR_SUB_LZERO; VECTOR_SUB_RZERO; NORM_NEG; NORM_MUL;
              REAL_ABS_NORM] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_EQ_RDIV_EQ; NORM_POS_LT] THEN
  ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; NORM_EQ_0] THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0] THEN
  MATCH_MP_TAC lemma THEN MAP_EVERY EXISTS_TAC
   [`inv(norm x) % x:real^N`; `inv(norm y) % y:real^N`;
    `(f:real^N->real^N) (inv (norm x) % x)`;
    `(f:real^N->real^N) (inv (norm y) % y)`] THEN
  REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RINV; NORM_EQ_0] THEN
  ASM_REWRITE_TAC[GSYM dist; VECTOR_MUL_LID] THEN
  REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RINV; NORM_EQ_0]);;

let ORTHOGONAL_TRANSFORMATION_INVERSE_o = prove
 (`!f:real^N->real^N.
        orthogonal_transformation f
        ==> ?g. orthogonal_transformation g /\ g o f = I /\ f o g = I`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_INJECTIVE) THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `g:real^N->real^N` THEN  STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `g:real^N->real^N`]
    LINEAR_INVERSE_LEFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION] THEN X_GEN_TAC `v:real^N` THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `norm((f:real^N->real^N)((g:real^N->real^N) v))` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM]) THEN
  ASM_REWRITE_TAC[]);;

let ORTHOGONAL_TRANSFORMATION_INVERSE = prove
 (`!f:real^N->real^N.
        orthogonal_transformation f
        ==> ?g. orthogonal_transformation g /\
                (!x. g(f x) = x) /\ (!y. f(g y) = y)`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_INVERSE_o) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM]);;

let ONORM_COMPOSE_ORTHOGONAL_TRANSFORMATION_LEFT = prove
 (`!f g. orthogonal_transformation f ==> onorm(f o g) = onorm g`,
  SIMP_TAC[ORTHOGONAL_TRANSFORMATION; onorm; o_DEF]);;

let ONORM_COMPOSE_ORTHOGONAL_TRANSFORMATION_RIGHT = prove
 (`!f g. orthogonal_transformation g ==> onorm(f o g) = onorm f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[onorm; o_DEF] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_INVERSE_o) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Reading operator norms off eigenvalue bases or diagonalizations.          *)
(* ------------------------------------------------------------------------- *)

let SQNORM_LE_MAX_EIGENVECTOR_SPAN = prove
 (`!(f:real^N->real^N) b c x l.
        linear f /\
        pairwise orthogonal b /\
        (!x. x IN b ==> f x = c x % x /\ c x pow 2 <= l) /\
        x IN span b
        ==> norm(f x) pow 2 <= l * norm x pow 2`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PAIRWISE_ORTHOGONAL_IMP_FINITE) THEN
  ASM_SIMP_TAC[SPAN_FINITE; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `v:real^N->real` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[LINEAR_VSUM; o_DEF; LINEAR_CMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NORM_VSUM_PYTHAGOREAN o
    lhand o snd) THEN
  W(MP_TAC o PART_MATCH(lhand o rand) NORM_VSUM_PYTHAGOREAN o
    rand o rand o rand o snd) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    REWRITE_TAC[pairwise; ORTHOGONAL_MUL] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC]) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [NORM_MUL] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_POW2_ABS; REAL_LE_POW_2]);;

let NORM_LE_MAX_EIGENVECTOR_SPAN = prove
 (`!(f:real^N->real^N) b c x l.
        linear f /\
        pairwise orthogonal b /\
        (!x. x IN b ==> f x = c x % x /\ abs(c x) <= l) /\
        x IN span b
        ==> norm(f x) <= l * norm x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[SPAN_EMPTY; IN_SING] THEN
    MESON_TAC[LINEAR_0; NORM_0; REAL_MUL_RZERO; REAL_LE_REFL];
    STRIP_TAC] THEN
  GEN_REWRITE_TAC I [NORM_LE_SQUARE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS; MEMBER_NOT_EMPTY];
    REWRITE_TAC[REAL_POW_MUL; GSYM NORM_POW_2]] THEN
  MATCH_MP_TAC SQNORM_LE_MAX_EIGENVECTOR_SPAN THEN
  MAP_EVERY EXISTS_TAC [`b:real^N->bool`; `c:real^N->real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS; REAL_ABS_ABS] THEN ASM_REAL_ARITH_TAC);;

let ONORM_EQ_MAX_EIGENVECTOR = prove
 (`!(f:real^N->real^N) b c.
        linear f /\
        pairwise orthogonal b /\
        span b = (:real^N) /\
        ~(vec 0 IN b) /\
        (!x. x IN b ==> f x = c x % x)
        ==> onorm f = sup {abs(c x) | x IN b}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[SPAN_EMPTY] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s = UNIV ==> (?x. ~(x IN s)) ==> P`)) THEN
    EXISTS_TAC `vec 1:real^N` THEN REWRITE_TAC[VEC_EQ; IN_SING; ARITH_EQ];
    STRIP_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM]] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[ONORM_LE_EQ] THEN GEN_TAC THEN
    MATCH_MP_TAC NORM_LE_MAX_EIGENVECTOR_SPAN THEN
    MAP_EVERY EXISTS_TAC [`b:real^N->bool`; `c:real^N->real`] THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_LE_SUP_FINITE; SIMPLE_IMAGE; FINITE_IMAGE;
                 IMAGE_EQ_EMPTY; PAIRWISE_ORTHOGONAL_IMP_FINITE] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE] THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    MATCH_MP_TAC REAL_SUP_LE THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `norm(x:real^N)` THEN
    REWRITE_TAC[NORM_POS_LT] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `norm((f:real^N->real^N) x)` THEN
    ASM_SIMP_TAC[ONORM; NORM_MUL; REAL_LE_REFL]]);;

let ONORM_ORTHOGONAL_MATRIX_MUL_LEFT = prove
 (`!(A:real^N^N) (P:real^N^N).
        orthogonal_matrix P ==> onorm (\x. (P ** A) ** x) = onorm(\x. A ** x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. ((P:real^N^N) ** (A:real^N^N)) ** x) = (\x. P ** x) o (\x. A ** x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF; MATRIX_VECTOR_MUL_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC ONORM_COMPOSE_ORTHOGONAL_TRANSFORMATION_LEFT THEN
  ASM_REWRITE_TAC[GSYM ORTHOGONAL_MATRIX_TRANSFORMATION]);;

let ONORM_ORTHOGONAL_MATRIX_MUL_RIGHT = prove
 (`!(A:real^N^N) (P:real^N^N).
        orthogonal_matrix P ==> onorm (\x. (A ** P) ** x) = onorm(\x. A ** x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. ((A:real^N^N) ** (P:real^N^N)) ** x) =
    (\x. A ** x) o (\x. P ** x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF; MATRIX_VECTOR_MUL_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC ONORM_COMPOSE_ORTHOGONAL_TRANSFORMATION_RIGHT THEN
  ASM_REWRITE_TAC[GSYM ORTHOGONAL_MATRIX_TRANSFORMATION]);;

let ONORM_DIAGONALIZED_MATRIX = prove
 (`!(A:real^N^N) D P.
      orthogonal_matrix P /\
      diagonal_matrix D /\
      transp P ** D ** P = A
      ==> onorm(\x. A ** x) = sup {abs(D$i$i) | 1 <= i /\ i <= dimindex (:N)}`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[ONORM_ORTHOGONAL_MATRIX_MUL_LEFT; ORTHOGONAL_MATRIX_TRANSP;
               ONORM_ORTHOGONAL_MATRIX_MUL_RIGHT] THEN
  ASM_SIMP_TAC[ONORM_DIAGONAL_MATRIX]);;

let ONORM_DIAGONALIZED_COVARIANCE_MATRIX = prove
 (`!(A:real^N^N) D P.
      orthogonal_matrix P /\
      diagonal_matrix D /\
      transp P ** D ** P = transp A ** A
      ==> onorm(\x. A ** x) =
          sqrt(sup {abs(D$i$i) | 1 <= i /\ i <= dimindex (:N)})`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SQRT_UNIQUE THEN
  SIMP_TAC[ONORM_POS_LE; MATRIX_VECTOR_MUL_LINEAR] THEN
  REWRITE_TAC[GSYM ONORM_COVARIANCE] THEN
  MATCH_MP_TAC ONORM_DIAGONALIZED_MATRIX THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* We can find an orthogonal matrix taking any unit vector to any other.     *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_MATRIX_EXISTS_BASIS = prove
 (`!a:real^N.
        norm(a) = &1
        ==> ?A. orthogonal_matrix A /\ A**(basis 1) = a`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP VECTOR_IN_ORTHONORMAL_BASIS) THEN
  REWRITE_TAC[HAS_SIZE] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`]
   FINITE_INDEX_NUMSEG_SPECIAL) THEN ASM_REWRITE_TAC[IN_NUMSEG] THEN
  REWRITE_TAC[TAUT `a /\ b ==> c <=> c \/ ~a \/ ~b`] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->real^N`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
     ASSUME_TAC))) THEN
  EXISTS_TAC `(lambda i j. ((f j):real^N)$i):real^N^N` THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; matrix_vector_mul; BASIS_COMPONENT;
           IN_NUMSEG] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN SIMP_TAC[REAL_MUL_RZERO; SUM_DELTA] THEN
  ASM_REWRITE_TAC[IN_NUMSEG; REAL_MUL_RID; LE_REFL; DIMINDEX_GE_1] THEN
  REWRITE_TAC[ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS] THEN
  SIMP_TAC[column; LAMBDA_BETA] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `norm((f:num->real^N) i)` THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA];
      ASM_MESON_TAC[IN_IMAGE; IN_NUMSEG]];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `orthogonal ((f:num->real^N) i) (f j)` MP_TAC THENL
     [ASM_MESON_TAC[pairwise; IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
    ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA]]);;

let ORTHOGONAL_TRANSFORMATION_EXISTS_1 = prove
 (`!a b:real^N.
        norm(a) = &1 /\ norm(b) = &1
        ==> ?f. orthogonal_transformation f /\ f a = b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `b:real^N` ORTHOGONAL_MATRIX_EXISTS_BASIS) THEN
  MP_TAC(ISPEC `a:real^N` ORTHOGONAL_MATRIX_EXISTS_BASIS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N^N` (STRIP_ASSUME_TAC o GSYM)) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real^N^N` (STRIP_ASSUME_TAC o GSYM)) THEN
  EXISTS_TAC `\x:real^N. ((B:real^N^N) ** transp(A:real^N^N)) ** x` THEN
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX; MATRIX_VECTOR_MUL_LINEAR;
              MATRIX_OF_MATRIX_VECTOR_MUL] THEN
  ASM_SIMP_TAC[ORTHOGONAL_MATRIX_MUL; ORTHOGONAL_MATRIX_TRANSP] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN AP_TERM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ORTHOGONAL_MATRIX]) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]);;

let ORTHOGONAL_TRANSFORMATION_EXISTS = prove
 (`!a b:real^N.
        norm(a) = norm(b) ==> ?f. orthogonal_transformation f /\ f a = b`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:real^N = vec 0` THEN
  ASM_SIMP_TAC[NORM_0; NORM_EQ_0] THENL
   [MESON_TAC[ORTHOGONAL_TRANSFORMATION_ID]; ALL_TAC] THEN
  ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_MESON_TAC[NORM_0; NORM_EQ_0]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`inv(norm a) % a:real^N`; `inv(norm b) % b:real^N`]
                ORTHOGONAL_TRANSFORMATION_EXISTS_1) THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[NORM_EQ_0; REAL_MUL_LINV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^N->real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_CMUL o
              MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
    `a % x:real^N = a % y <=> a % (x - y) = vec 0`] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; NORM_EQ_0; VECTOR_SUB_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Or indeed, taking any subspace to another of suitable dimension.          *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_TRANSFORMATION_INTO_SUBSPACE = prove
 (`!s t:real^N->bool.
        subspace s /\ subspace t /\ dim s <= dim t
        ==> ?f. orthogonal_transformation f /\ IMAGE f s SUBSET t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t:real^N->bool` ORTHONORMAL_BASIS_SUBSPACE) THEN
  MP_TAC(ISPEC `s:real^N->bool` ORTHONORMAL_BASIS_SUBSPACE) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:real^N->bool`; `(:real^N)`] ORTHONORMAL_EXTENSION) THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `(:real^N)`] ORTHONORMAL_EXTENSION) THEN
  ASM_REWRITE_TAC[UNION_UNIV; SPAN_UNIV; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `b':real^N->bool` THEN STRIP_TAC THEN
  X_GEN_TAC `c':real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `independent(b UNION b':real^N->bool) /\
    independent(c UNION c':real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
    ASM_REWRITE_TAC[IN_UNION] THEN
    ASM_MESON_TAC[NORM_ARITH `~(norm(vec 0:real^N) = &1)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(b UNION b':real^N->bool) /\
                FINITE(c UNION c':real^N->bool)`
  MP_TAC THENL
   [ASM_SIMP_TAC[PAIRWISE_ORTHOGONAL_IMP_FINITE];
    REWRITE_TAC[FINITE_UNION] THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `?f:real^N->real^N.
        (!x y. x IN b UNION b' /\ y IN b UNION b' ==> (f x = f y <=> x = y)) /\
        IMAGE f b SUBSET c /\
        IMAGE f (b UNION b') SUBSET c UNION c'`
   (X_CHOOSE_THEN `fb:real^N->real^N` STRIP_ASSUME_TAC)
  THENL
   [MP_TAC(ISPECL [`b:real^N->bool`; `c:real^N->bool`]
        CARD_LE_INJ) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; INJECTIVE_ON_ALT] THEN
    X_GEN_TAC `f:real^N->real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`b':real^N->bool`;
                   `(c UNION c') DIFF IMAGE (f:real^N->real^N) b`]
        CARD_LE_INJ) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_UNION; FINITE_DIFF] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) CARD_DIFF o rand o snd) THEN
      ASM_REWRITE_TAC[FINITE_UNION] THEN
      ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC(ARITH_RULE `a + b:num = c ==> a <= c - b`) THEN
      W(MP_TAC o PART_MATCH (lhs o rand) CARD_IMAGE_INJ o
        rand o lhs o snd) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      W(MP_TAC o PART_MATCH (rhs o rand) CARD_UNION o lhs o snd) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [UNION_COMM] THEN
      MATCH_MP_TAC(MESON[LE_ANTISYM]
       `(FINITE s /\ CARD s <= CARD t) /\
        (FINITE t /\ CARD t <= CARD s) ==> CARD s = CARD t`) THEN
      CONJ_TAC THEN MATCH_MP_TAC INDEPENDENT_SPAN_BOUND THEN
      ASM_REWRITE_TAC[FINITE_UNION; SUBSET_UNIV];
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `\x. if x IN b then (f:real^N->real^N) x else g x` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`fb:real^N->real^N`; `b UNION b':real^N->bool`]
    LINEAR_INDEPENDENT_EXTEND) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^N->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION];
    REWRITE_TAC[SYM(ASSUME `span b:real^N->bool = s`)] THEN
    ASM_SIMP_TAC[GSYM SPAN_LINEAR_IMAGE] THEN
    REWRITE_TAC[SYM(ASSUME `span c:real^N->bool = t`)] THEN
    MATCH_MP_TAC SPAN_MONO THEN ASM SET_TAC[]] THEN
  SUBGOAL_THEN
   `!v. v IN UNIV ==> norm((f:real^N->real^N) v) = norm v`
   (fun th -> ASM_MESON_TAC[th; IN_UNIV]) THEN
  UNDISCH_THEN `span (b UNION b') = (:real^N)` (SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[SPAN_FINITE; FINITE_UNION; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`z:real^N`; `u:real^N->real`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[LINEAR_VSUM; FINITE_UNION] THEN
  REWRITE_TAC[o_DEF; NORM_EQ_SQUARE; NORM_POS_LE; GSYM NORM_POW_2] THEN
  ASM_SIMP_TAC[LINEAR_CMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
    NORM_VSUM_PYTHAGOREAN o rand o snd) THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
    NORM_VSUM_PYTHAGOREAN o lhand o rand o snd) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
  ASM_SIMP_TAC[pairwise; ORTHOGONAL_CLAUSES; FINITE_UNION] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[ORTHOGONAL_MUL] THEN
    REPEAT DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    REPEAT(DISCH_THEN SUBST1_TAC) THEN ASM_SIMP_TAC[NORM_MUL] THEN
    MATCH_MP_TAC SUM_EQ THEN ASM SET_TAC[]]);;

let ORTHOGONAL_TRANSFORMATION_ONTO_SUBSPACE = prove
 (`!s t:real^N->bool.
        subspace s /\ subspace t /\ dim s = dim t
        ==> ?f. orthogonal_transformation f /\ IMAGE f s = t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`]
        ORTHOGONAL_TRANSFORMATION_INTO_SUBSPACE) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `f:real^N->real^N` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `span(IMAGE (f:real^N->real^N) s) = span t` MP_TAC THENL
   [MATCH_MP_TAC DIM_EQ_SPAN THEN ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) DIM_INJECTIVE_LINEAR_IMAGE o
      rand o snd) THEN
    ASM_MESON_TAC[LE_REFL; orthogonal_transformation;
                  ORTHOGONAL_TRANSFORMATION_INJECTIVE];
    ASM_SIMP_TAC[SPAN_LINEAR_IMAGE; ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
    ASM_SIMP_TAC[SPAN_OF_SUBSPACE]]);;

(* ------------------------------------------------------------------------- *)
(* Rotation, reflection, rotoinversion.                                      *)
(* ------------------------------------------------------------------------- *)

let rotation_matrix = new_definition
 `rotation_matrix Q <=> orthogonal_matrix Q /\ det(Q) = &1`;;

let rotoinversion_matrix = new_definition
 `rotoinversion_matrix Q <=> orthogonal_matrix Q /\ det(Q) = -- &1`;;

let ORTHOGONAL_ROTATION_OR_ROTOINVERSION = prove
 (`!Q. orthogonal_matrix Q <=> rotation_matrix Q \/ rotoinversion_matrix Q`,
  MESON_TAC[rotation_matrix; rotoinversion_matrix; DET_ORTHOGONAL_MATRIX]);;

let ROTATION_MATRIX_1 = prove
 (`!m:real^N^N.
        dimindex(:N) = 1 ==> (rotation_matrix m <=> m = mat 1)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ORTHOGONAL_MATRIX_1; rotation_matrix] THEN
  ASM_CASES_TAC `m:real^N^N = mat 1` THEN ASM_REWRITE_TAC[DET_I] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[DET_NEG; REAL_POW_ONE; DET_I] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let ROTOINVERSION_MATRIX_1 = prove
 (`!m:real^N^N.
        dimindex(:N) = 1 ==> (rotoinversion_matrix m <=> m = --mat 1)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ORTHOGONAL_MATRIX_1; rotoinversion_matrix] THEN
  ASM_CASES_TAC `m:real^N^N = --mat 1` THEN
  ASM_REWRITE_TAC[DET_NEG; DET_I; REAL_POW_ONE] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[DET_I] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let ROTATION_MATRIX_2 = prove
 (`!A:real^2^2. rotation_matrix A <=>
                A$1$1 pow 2 + A$2$1 pow 2 = &1 /\
                A$1$1 = A$2$2 /\ A$1$2 = --(A$2$1)`,
  REWRITE_TAC[rotation_matrix; ORTHOGONAL_MATRIX_2; DET_2] THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Slightly stronger results giving rotation, but only in >= 2 dimensions.   *)
(* ------------------------------------------------------------------------- *)

let ROTATION_MATRIX_EXISTS_BASIS = prove
 (`!a:real^N.
        2 <= dimindex(:N) /\ norm(a) = &1
        ==> ?A. rotation_matrix A /\ A**(basis 1) = a`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `A:real^N^N` STRIP_ASSUME_TAC o
   MATCH_MP ORTHOGONAL_MATRIX_EXISTS_BASIS) THEN
  FIRST_ASSUM(DISJ_CASES_TAC o GEN_REWRITE_RULE I
   [ORTHOGONAL_ROTATION_OR_ROTOINVERSION])
  THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `transp(lambda i. if i = dimindex(:N) then -- &1 % transp A$i
                               else (transp A:real^N^N)$i):real^N^N` THEN
  REWRITE_TAC[rotation_matrix; DET_TRANSP] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ORTHOGONAL_MATRIX_TRANSP];
    SIMP_TAC[DET_ROW_MUL; DIMINDEX_GE_1; LE_REFL] THEN
    MATCH_MP_TAC(REAL_ARITH `x = -- &1 ==> -- &1 * x = &1`) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rotoinversion_matrix]) THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM DET_TRANSP] THEN
    AP_TERM_TAC THEN SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN MESON_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    SIMP_TAC[matrix_vector_mul; LAMBDA_BETA; CART_EQ; transp;
             BASIS_COMPONENT] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
      `x * (if p then &1 else &0) = if p then x else &0`] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> ~(1 = n)`; LAMBDA_BETA]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
   [GSYM ORTHOGONAL_MATRIX_TRANSP]) THEN
  SPEC_TAC(`transp(A:real^N^N)`,`B:real^N^N`) THEN GEN_TAC THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= dimindex(:N)
                    ==> row i ((lambda i. if i = dimindex(:N) then -- &1 % B$i
                                else (B:real^N^N)$i):real^N^N) =
                        if i = dimindex(:N) then --(row i B) else row i B`
  ASSUME_TAC THENL
   [SIMP_TAC[row; LAMBDA_BETA; LAMBDA_ETA; VECTOR_MUL_LID; VECTOR_MUL_LNEG];
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS] THEN
    ASM_MESON_TAC[ORTHOGONAL_LNEG; ORTHOGONAL_RNEG; NORM_NEG]]);;

let ROTATION_EXISTS_1 = prove
 (`!a b:real^N.
        2 <= dimindex(:N) /\ norm(a) = &1 /\ norm(b) = &1
        ==> ?f. orthogonal_transformation f /\ det(matrix f) = &1 /\ f a = b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `b:real^N` ROTATION_MATRIX_EXISTS_BASIS) THEN
  MP_TAC(ISPEC `a:real^N` ROTATION_MATRIX_EXISTS_BASIS) THEN
  ASM_REWRITE_TAC[rotation_matrix] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N^N`
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real^N^N`
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  EXISTS_TAC `\x:real^N. ((B:real^N^N) ** transp(A:real^N^N)) ** x` THEN
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX; MATRIX_VECTOR_MUL_LINEAR;
              MATRIX_OF_MATRIX_VECTOR_MUL; DET_MUL; DET_TRANSP] THEN
  ASM_SIMP_TAC[ORTHOGONAL_MATRIX_MUL; ORTHOGONAL_MATRIX_TRANSP] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; REAL_MUL_LID] THEN AP_TERM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ORTHOGONAL_MATRIX]) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]);;

let ROTATION_EXISTS = prove
 (`!a b:real^N.
        2 <= dimindex(:N) /\ norm(a) = norm(b)
        ==> ?f. orthogonal_transformation f /\ det(matrix f) = &1 /\ f a = b`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:real^N = vec 0` THEN
  ASM_SIMP_TAC[NORM_0; NORM_EQ_0] THENL
   [MESON_TAC[ORTHOGONAL_TRANSFORMATION_ID; MATRIX_ID; DET_I]; ALL_TAC] THEN
  ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_ID; MATRIX_ID; DET_I; NORM_0;
                  NORM_EQ_0]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`inv(norm a) % a:real^N`; `inv(norm b) % b:real^N`]
                ROTATION_EXISTS_1) THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[NORM_EQ_0; REAL_MUL_LINV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^N->real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_CMUL o
              MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
   `a % x:real^N = a % y <=> a % (x - y) = vec 0`] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; NORM_EQ_0; VECTOR_SUB_EQ]);;

let ROTATION_RIGHTWARD_LINE = prove
 (`!a:real^N k.
        1 <= k /\ k <= dimindex(:N)
        ==> ?b f. orthogonal_transformation f /\
                  (2 <= dimindex(:N) ==> det(matrix f) = &1) /\
                  f(b % basis k) = a /\
                  &0 <= b`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `norm(a:real^N)` THEN
  ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; LE_REFL; DIMINDEX_GE_1;
               REAL_MUL_RID; NORM_POS_LE; LT_IMP_LE; LTE_ANTISYM] THEN
  REWRITE_TAC[ARITH_RULE `2 <= n <=> 1 <= n /\ ~(n = 1)`; DIMINDEX_GE_1] THEN
  ASM_CASES_TAC `dimindex(:N) = 1` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC ORTHOGONAL_TRANSFORMATION_EXISTS;
    MATCH_MP_TAC ROTATION_EXISTS] THEN
   ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; LE_REFL; DIMINDEX_GE_1] THEN
   REWRITE_TAC[REAL_ABS_NORM; REAL_MUL_RID] THEN
   MATCH_MP_TAC(ARITH_RULE `~(n = 1) /\ 1 <= n ==> 2 <= n`) THEN
   ASM_REWRITE_TAC[DIMINDEX_GE_1]);;

(* ------------------------------------------------------------------------- *)
(* In 3 dimensions, a rotation is indeed about an "axis".                    *)
(* ------------------------------------------------------------------------- *)

let EULER_ROTATION_THEOREM = prove
 (`!A:real^3^3. rotation_matrix A ==> ?v:real^3. ~(v = vec 0) /\ A ** v = v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `A - mat 1:real^3^3` HOMOGENEOUS_LINEAR_EQUATIONS_DET) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB;
              VECTOR_SUB_EQ; MATRIX_VECTOR_MUL_LID] THEN
  DISCH_THEN SUBST1_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[rotation_matrix; orthogonal_matrix; DET_3] THEN
  SIMP_TAC[CART_EQ; FORALL_3; MAT_COMPONENT; DIMINDEX_3; LAMBDA_BETA; ARITH;
           MATRIX_SUB_COMPONENT; MAT_COMPONENT; SUM_3;
           matrix_mul; transp; matrix_vector_mul] THEN
  CONV_TAC REAL_RING);;

let EULER_ROTOINVERSION_THEOREM = prove
 (`!A:real^3^3.
     rotoinversion_matrix A ==> ?v:real^3. ~(v = vec 0) /\ A ** v = --v`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `a:real^N = --v <=> a + v = vec 0`] THEN
  MP_TAC(ISPEC `A + mat 1:real^3^3` HOMOGENEOUS_LINEAR_EQUATIONS_DET) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_LID] THEN
  DISCH_THEN SUBST1_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[rotoinversion_matrix; orthogonal_matrix; DET_3] THEN
  SIMP_TAC[CART_EQ; FORALL_3; MAT_COMPONENT; DIMINDEX_3; LAMBDA_BETA; ARITH;
           MATRIX_ADD_COMPONENT; MAT_COMPONENT; SUM_3;
           matrix_mul; transp; matrix_vector_mul] THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* We can always rotate so that a hyperplane is "horizontal".                *)
(* ------------------------------------------------------------------------- *)

let ROTATION_LOWDIM_HORIZONTAL = prove
 (`!s:real^N->bool.
        dim s < dimindex(:N)
        ==> ?f. orthogonal_transformation f /\ det(matrix f) = &1 /\
               (IMAGE f s) SUBSET {z | z$(dimindex(:N)) = &0}`,
  GEN_TAC THEN ASM_CASES_TAC `dim(s:real^N->bool) = 0` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[DIM_EQ_0]) THEN DISCH_TAC THEN
    EXISTS_TAC `\x:real^N. x` THEN
    REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_ID; MATRIX_ID; DET_I] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET {a} ==> a IN t ==> IMAGE (\x. x) s SUBSET t`)) THEN
    SIMP_TAC[IN_ELIM_THM; VEC_COMPONENT; LE_REFL; DIMINDEX_GE_1];
    DISCH_TAC] THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC o MATCH_MP
    LOWDIM_SUBSET_HYPERPLANE) THEN
  MP_TAC(ISPECL [`a:real^N`; `norm(a:real^N) % basis(dimindex(:N)):real^N`]
        ROTATION_EXISTS) THEN
  ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; LE_REFL; DIMINDEX_GE_1] THEN
  REWRITE_TAC[REAL_ABS_NORM; REAL_MUL_RID] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^N->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^N) x dot (f a) = &0` MP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[orthogonal_transformation]) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    ASM_SIMP_TAC[SPAN_SUPERSET; IN_ELIM_THM];
    ASM_SIMP_TAC[DOT_BASIS; LE_REFL; DIMINDEX_GE_1; DOT_RMUL] THEN
    ASM_REWRITE_TAC[REAL_ENTIRE; NORM_EQ_0]]);;

let ORTHOGONAL_TRANSFORMATION_LOWDIM_HORIZONTAL = prove
 (`!s:real^N->bool.
        dim s < dimindex(:N)
        ==> ?f. orthogonal_transformation f /\
               (IMAGE f s) SUBSET {z | z$(dimindex(:N)) = &0}`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ROTATION_LOWDIM_HORIZONTAL) THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]);;

let ORTHOGONAL_TRANSFORMATION_BETWEEN_ORTHOGONAL_SETS = prove
 (`!v:num->real^N w k.
        pairwise (\i j. orthogonal (v i) (v j)) k /\
        pairwise (\i j. orthogonal (w i) (w j)) k /\
        (!i. i IN k ==> norm(v i) = norm(w i))
        ==> ?f. orthogonal_transformation f /\
                (!i. i IN k ==> f(v i) = w i)`,
  let lemma1 = prove
   (`!v:num->real^N n.
          pairwise (\i j. orthogonal (v i) (v j)) (1..n) /\
          (!i. 1 <= i /\ i <= n ==> norm(v i) = &1)
          ==> ?f. orthogonal_transformation f /\
                  (!i. 1 <= i /\ i <= n ==> f(basis i) = v i)`,
    REWRITE_TAC[pairwise; IN_NUMSEG; GSYM CONJ_ASSOC] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `pairwise orthogonal (IMAGE (v:num->real^N) (1..n))`
    ASSUME_TAC THENL
     [REWRITE_TAC[PAIRWISE_IMAGE] THEN ASM_SIMP_TAC[pairwise; IN_NUMSEG];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          PAIRWISE_ORTHOGONAL_INDEPENDENT)) THEN
    REWRITE_TAC[SET_RULE
     `~(a IN IMAGE f s) <=> !x. x IN s ==> ~(f x = a)`] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_NUMSEG] THEN
      ASM_MESON_TAC[NORM_0; REAL_ARITH `~(&1 = &0)`];
      DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP INDEPENDENT_BOUND)] THEN
    SUBGOAL_THEN
     `!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n /\ ~(i = j)
            ==> ~(v i:real^N = v j)`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[ORTHOGONAL_REFL; NORM_0; REAL_ARITH `~(&1 = &0)`];
      ALL_TAC] THEN
    SUBGOAL_THEN `CARD(IMAGE (v:num->real^N) (1..n)) = n` ASSUME_TAC THENL
     [W(MP_TAC o PART_MATCH (lhs o rand) CARD_IMAGE_INJ o lhs o snd) THEN
      ASM_REWRITE_TAC[CARD_NUMSEG_1; IN_NUMSEG; FINITE_NUMSEG] THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
    SUBGOAL_THEN
     `?w:num->real^N.
          pairwise (\i j. orthogonal (w i) (w j)) (1..dimindex(:N)) /\
          (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(w i) = &1) /\
          (!i. 1 <= i /\ i <= n ==> w i = v i)`
    STRIP_ASSUME_TAC THENL
     [ALL_TAC;
      EXISTS_TAC
       `(\x. vsum(1..dimindex(:N)) (\i. x$i % w i)):real^N->real^N` THEN
      SIMP_TAC[BASIS_COMPONENT; IN_NUMSEG; COND_RATOR; COND_RAND] THEN
      REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO; VSUM_DELTA] THEN
      ASM_SIMP_TAC[IN_NUMSEG] THEN CONJ_TAC THENL
       [ALL_TAC; ASM_MESON_TAC[LE_TRANS]] THEN
      REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN
        REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
        REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[matrix; column; ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS] THEN
      SIMP_TAC[LAMBDA_BETA; LAMBDA_ETA; BASIS_COMPONENT; IN_NUMSEG] THEN
      SIMP_TAC[COND_RATOR; COND_RAND; VECTOR_MUL_LZERO; VSUM_DELTA] THEN
      SIMP_TAC[IN_NUMSEG; orthogonal; dot; LAMBDA_BETA; NORM_EQ_SQUARE] THEN
      REWRITE_TAC[VECTOR_MUL_LID; GSYM dot; GSYM NORM_EQ_SQUARE] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[pairwise; IN_NUMSEG; orthogonal]) THEN
      ASM_SIMP_TAC[]] THEN
    FIRST_ASSUM(MP_TAC o SPEC `(:real^N)` o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] ORTHONORMAL_EXTENSION)) THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG; UNION_UNIV; SPAN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`n+1..dimindex(:N)`; `t:real^N->bool`]
          CARD_EQ_BIJECTION) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG] THEN
      MP_TAC(ISPECL [`(:real^N)`; `IMAGE v (1..n) UNION t:real^N->bool`]
          BASIS_CARD_EQ_DIM) THEN
      ASM_REWRITE_TAC[SUBSET_UNIV] THEN ANTS_TAC THENL
       [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
        ASM_REWRITE_TAC[IN_UNION; DE_MORGAN_THM; IN_NUMSEG] THEN
        ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG; SET_RULE
         `~(x IN s) <=> !y. y IN s ==> ~(y = x)`] THEN
        ASM_MESON_TAC[NORM_0; REAL_ARITH `~(&1 = &0)`];
        ALL_TAC] THEN
      ASM_SIMP_TAC[FINITE_UNION; IMP_CONJ; FINITE_IMAGE; CARD_UNION;
                   SET_RULE `t INTER s = {} <=> DISJOINT s t`] THEN
      DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC[CARD_NUMSEG; DIM_UNIV] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CONJ_ASSOC; SET_RULE
     `(!x. x IN s ==> f x IN t) /\ (!y. y IN t ==> ?x. x IN s /\ f x = y) <=>
      t = IMAGE f s`] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; LEFT_IMP_EXISTS_THM; IN_NUMSEG] THEN
    X_GEN_TAC `w:num->real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    REWRITE_TAC[ARITH_RULE `n + 1 <= x <=> n < x`; CONJ_ASSOC] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q ==> r <=> p /\ ~r ==> ~q`] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN STRIP_TAC THEN
    REWRITE_TAC[TAUT `p /\ ~r ==> ~q <=> p /\ q ==> r`] THEN
    EXISTS_TAC `\i. if i <= n then (v:num->real^N) i else w i` THEN
    SIMP_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FORALL_IN_IMAGE; IN_NUMSEG]) THEN
    CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[ARITH_RULE `~(i <= n) ==> n + 1 <= i`]] THEN
    REWRITE_TAC[pairwise] THEN MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [MESON_TAC[ORTHOGONAL_SYM]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `j:num <= n` THEN ASM_REWRITE_TAC[IN_NUMSEG] THENL
     [COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `i:num <= n` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC
     `pairwise orthogonal
        (IMAGE (v:num->real^N) (1..n) UNION IMAGE w (n+1..dimindex (:N)))` THEN
    REWRITE_TAC[pairwise] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `(w:num->real^N) j`) THENL
     [DISCH_THEN(MP_TAC o SPEC `(v:num->real^N) i`);
      DISCH_THEN(MP_TAC o SPEC `(w:num->real^N) i`)] THEN
    ASM_REWRITE_TAC[IN_UNION; IN_IMAGE; IN_NUMSEG] THEN
    DISCH_THEN MATCH_MP_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[ARITH_RULE `~(x <= n) ==> n + 1 <= x`]; ALL_TAC];
      ASM_MESON_TAC[ARITH_RULE `~(x <= n) ==> n + 1 <= x /\ n < x`]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DISJOINT]) THEN
    REWRITE_TAC[SET_RULE `IMAGE w t INTER IMAGE v s = {} <=>
      !i j. i IN s /\ j IN t ==> ~(v i = w j)`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG] THEN
    ASM_ARITH_TAC) in
  let lemma2 = prove
   (`!v:num->real^N w k.
          pairwise (\i j. orthogonal (v i) (v j)) k /\
          pairwise (\i j. orthogonal (w i) (w j)) k /\
          (!i. i IN k ==> norm(v i) = norm(w i)) /\
          (!i. i IN k ==> ~(v i = vec 0) /\ ~(w i = vec 0))
          ==> ?f. orthogonal_transformation f /\
                  (!i. i IN k ==> f(v i) = w i)`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `FINITE(k:num->bool)` MP_TAC THENL
     [SUBGOAL_THEN `pairwise orthogonal (IMAGE (v:num->real^N) k)`
      ASSUME_TAC THENL
       [REWRITE_TAC[PAIRWISE_IMAGE] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN ASM_SIMP_TAC[pairwise];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        PAIRWISE_ORTHOGONAL_INDEPENDENT)) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP INDEPENDENT_IMP_FINITE) THEN
      MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
      RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
      ASM_MESON_TAC[ORTHOGONAL_REFL];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r ==> s <=> p /\ q /\ ~s ==> ~r`] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num->num` MP_TAC) THEN
    REWRITE_TAC[IN_NUMSEG] THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN
    DISCH_THEN(fun th -> DISCH_THEN SUBST_ALL_TAC THEN ASSUME_TAC th) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [PAIRWISE_IMAGE; FORALL_IN_IMAGE; IN_NUMSEG]) THEN
    MP_TAC(ISPECL
     [`\i. inv(norm(w(n i))) % (w:num->real^N) ((n:num->num) i)`;
      `CARD(k:num->bool)`] lemma1) THEN
    MP_TAC(ISPECL
     [`\i. inv(norm(v(n i))) % (v:num->real^N) ((n:num->num) i)`;
      `CARD(k:num->bool)`] lemma1) THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_MUL_LINV; NORM_EQ_0; REAL_ABS_INV;
                 REAL_ABS_NORM; pairwise; orthogonal; IN_NUMSEG] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pairwise; orthogonal; IN_NUMSEG]) THEN
    ASM_SIMP_TAC[DOT_LMUL; DOT_RMUL; REAL_ENTIRE; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `f:real^N->real^N` ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':real^N->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(g:real^N->real^N) o (f':real^N->real^N)` THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_COMPOSE; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `(g:real^N->real^N) (norm((w:num->real^N)(n(i:num))) % basis i)` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
       `(!x. f'(f x) = x) ==> f x = y ==> f' y = x`));
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[orthogonal_transformation]) THEN
    ASM_SIMP_TAC[LINEAR_CMUL; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID]) in
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`v:num->real^N`; `w:num->real^N`;
    `{i | i IN k /\ ~((v:num->real^N) i = vec 0)}`] lemma2) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; CONJ_ASSOC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[NORM_EQ_0]] THEN
    CONJ_TAC THEN MATCH_MP_TAC PAIRWISE_MONO THEN EXISTS_TAC `k:num->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[orthogonal_transformation] THEN
    GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(v:num->real^N) i = vec 0` THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[LINEAR_0; NORM_EQ_0]]);;

(* ------------------------------------------------------------------------- *)
(* Reflection of a vector about 0 along a line.                              *)
(* ------------------------------------------------------------------------- *)

let reflect_along = new_definition
 `reflect_along v (x:real^N) = x - (&2 * (x dot v) / (v dot v)) % v`;;

let REFLECT_ALONG_ADD = prove
 (`!v x y:real^N.
      reflect_along v (x + y) = reflect_along v x + reflect_along v y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[reflect_along; VECTOR_ARITH
   `x - a % v + y - b % v:real^N = (x + y) - (a + b) % v`] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[DOT_LADD] THEN REAL_ARITH_TAC);;

let REFLECT_ALONG_MUL = prove
 (`!v a x:real^N. reflect_along v (a % x) = a % reflect_along v x`,
  REWRITE_TAC[reflect_along; DOT_LMUL; REAL_ARITH
   `&2 * (a * x) / y = a * &2 * x / y`] THEN
  REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC]);;

let LINEAR_REFLECT_ALONG = prove
 (`!v:real^N. linear(reflect_along v)`,
  REWRITE_TAC[linear; REFLECT_ALONG_ADD; REFLECT_ALONG_MUL]);;

let REFLECT_ALONG_0 = prove
 (`!v:real^N. reflect_along v (vec 0) = vec 0`,
  REWRITE_TAC[MATCH_MP LINEAR_0 (SPEC_ALL LINEAR_REFLECT_ALONG)]);;

let REFLECT_ALONG_NEG = prove
 (`!v x:real^N. reflect_along v (--x) = --(reflect_along v x)`,
  MESON_TAC[LINEAR_REFLECT_ALONG; LINEAR_NEG]);;

let REFLECT_ALONG_REFL = prove
 (`!v:real^N. reflect_along v v = --v`,
  GEN_TAC THEN ASM_CASES_TAC `v:real^N = vec 0` THEN
  ASM_REWRITE_TAC[VECTOR_NEG_0; REFLECT_ALONG_0] THEN
  REWRITE_TAC[reflect_along] THEN
  ASM_SIMP_TAC[REAL_DIV_REFL; DOT_EQ_0] THEN VECTOR_ARITH_TAC);;

let REFLECT_ALONG_INVOLUTION = prove
 (`!v x:real^N. reflect_along v (reflect_along v x) = x`,
  REWRITE_TAC[reflect_along; DOT_LSUB; VECTOR_MUL_EQ_0; VECTOR_ARITH
   `x - a % v - b % v:real^N = x <=> (a + b) % v = vec 0`] THEN
  REWRITE_TAC[DOT_LMUL; GSYM DOT_EQ_0] THEN CONV_TAC REAL_FIELD);;

let REFLECT_ALONG_GALOIS = prove
 (`!v p q:real^N. reflect_along v p = q <=> p = reflect_along v q`,
  MESON_TAC[REFLECT_ALONG_INVOLUTION]);;

let REFLECT_ALONG_EQ_0 = prove
 (`!v x:real^N. reflect_along v x = vec 0 <=> x = vec 0`,
  MESON_TAC[REFLECT_ALONG_0; REFLECT_ALONG_INVOLUTION]);;

let ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG = prove
 (`!v:real^N. orthogonal_transformation(reflect_along v)`,
  GEN_TAC THEN ASM_CASES_TAC `v:real^N = vec 0` THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
    ASM_REWRITE_TAC[reflect_along; VECTOR_MUL_RZERO; VECTOR_SUB_RZERO;
                    ORTHOGONAL_TRANSFORMATION_ID];
    REWRITE_TAC[ORTHOGONAL_TRANSFORMATION] THEN
    REWRITE_TAC[LINEAR_REFLECT_ALONG; NORM_EQ] THEN
    REWRITE_TAC[reflect_along; VECTOR_ARITH
      `(a - b:real^N) dot (a - b) = (a dot a + b dot b) - &2 * a dot b`] THEN
    REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN X_GEN_TAC `w:real^N` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM DOT_EQ_0]) THEN
    CONV_TAC REAL_FIELD]);;

let REFLECT_ALONG_EQ_SELF = prove
 (`!v x:real^N. reflect_along v x = x <=> orthogonal v x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[reflect_along; orthogonal] THEN
  REWRITE_TAC[VECTOR_ARITH `x - a:real^N = x <=> a = vec 0`] THEN
  REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
  ASM_CASES_TAC `v:real^N = vec 0` THEN ASM_SIMP_TAC[DOT_LZERO; DOT_SYM] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM DOT_EQ_0]) THEN
  CONV_TAC REAL_FIELD);;

let REFLECT_ALONG_ZERO = prove
 (`reflect_along (vec 0:real^N) = I`,
  REWRITE_TAC[FUN_EQ_THM; I_THM; REFLECT_ALONG_EQ_SELF; ORTHOGONAL_0]);;

let REFLECT_ALONG_LINEAR_IMAGE = prove
 (`!f:real^M->real^N v x.
        linear f /\ (!x. norm(f x) = norm x)
        ==> reflect_along (f v) (f x) = f(reflect_along v x)`,
  REWRITE_TAC[reflect_along] THEN
  SIMP_TAC[PRESERVES_NORM_PRESERVES_DOT; LINEAR_SUB; LINEAR_CMUL]);;

add_linear_invariants [REFLECT_ALONG_LINEAR_IMAGE];;

let REFLECT_ALONG_SCALE = prove
 (`!c v x:real^N. ~(c = &0) ==> reflect_along (c % v) x = reflect_along v x`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `v:real^N = vec 0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO; REFLECT_ALONG_ZERO] THEN
  REWRITE_TAC[reflect_along; VECTOR_MUL_ASSOC] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[DOT_RMUL] THEN REWRITE_TAC[DOT_LMUL] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM DOT_EQ_0]) THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD);;

let REFLECT_ALONG_NEGATION = prove
 (`!v:real^N. reflect_along (--v) = reflect_along v`,
  REWRITE_TAC[FUN_EQ_THM; VECTOR_NEG_MINUS1] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC REFLECT_ALONG_SCALE THEN REAL_ARITH_TAC);;

let REFLECT_ALONG_1D = prove
 (`!v x:real^N.
        dimindex(:N) = 1 ==> reflect_along v x = if v = vec 0 then x else --x`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[reflect_along; dot; SUM_1; CART_EQ; FORALL_1] THEN
  REWRITE_TAC[VEC_COMPONENT; COND_RATOR; COND_RAND] THEN
  SIMP_TAC[VECTOR_NEG_COMPONENT; VECTOR_MUL_COMPONENT;
           VECTOR_SUB_COMPONENT; REAL_MUL_RZERO] THEN
  CONV_TAC REAL_FIELD);;

let REFLECT_ALONG_BASIS = prove
 (`!x:real^N k.
        1 <= k /\ k <= dimindex(:N)
        ==> reflect_along (basis k) x = x - (&2 * x$k) % basis k`,
  SIMP_TAC[reflect_along; DOT_BASIS; BASIS_COMPONENT; REAL_DIV_1]);;

let MATRIX_REFLECT_ALONG_BASIS = prove
 (`!k. 1 <= k /\ k <= dimindex(:N)
       ==> matrix(reflect_along (basis k)):real^N^N =
           lambda i j. if i = k /\ j = k then --(&1)
                       else if i = j then &1
                       else &0`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; matrix; REFLECT_ALONG_BASIS;
           VECTOR_SUB_COMPONENT; BASIS_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC);;

let ROTOINVERSION_MATRIX_REFLECT_ALONG = prove
 (`!v:real^N. ~(v = vec 0) ==> rotoinversion_matrix(matrix(reflect_along v))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rotoinversion_matrix] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX;
                ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG];
    ALL_TAC] THEN
  ABBREV_TAC `w:real^N = inv(norm v) % v` THEN
  SUBGOAL_THEN `reflect_along (v:real^N) = reflect_along w` SUBST1_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[FUN_EQ_THM] THEN
    ASM_SIMP_TAC[REFLECT_ALONG_SCALE; REAL_INV_EQ_0; NORM_EQ_0];
    SUBGOAL_THEN `norm(w:real^N) = &1` MP_TAC THENL
     [EXPAND_TAC "w" THEN SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
      POP_ASSUM_LIST(K ALL_TAC) THEN SPEC_TAC(`w:real^N`,`v:real^N`)]] THEN
  X_GEN_TAC `v:real^N` THEN ASM_CASES_TAC `v:real^N = vec 0` THEN
  ASM_REWRITE_TAC[NORM_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`v:real^N`; `basis 1:real^N`]
        ORTHOGONAL_TRANSFORMATION_EXISTS) THEN
  ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `matrix(reflect_along v) =
    transp(matrix(f:real^N->real^N)) ** matrix(reflect_along (f v)) ** matrix f`
  SUBST1_TAC THENL
   [UNDISCH_THEN `(f:real^N->real^N) v = basis 1` (K ALL_TAC) THEN
    REWRITE_TAC[MATRIX_EQ; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_WORKS; LINEAR_REFLECT_ALONG;
                 ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
    X_GEN_TAC `x:real^N` THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(transp(matrix(f:real^N->real^N)) ** matrix f) **
                (reflect_along v x:real^N)` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[ORTHOGONAL_MATRIX; MATRIX_VECTOR_MUL_LID;
                ORTHOGONAL_TRANSFORMATION_MATRIX];
      REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[MATRIX_WORKS; ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC REFLECT_ALONG_LINEAR_IMAGE THEN
      ASM_REWRITE_TAC[GSYM ORTHOGONAL_TRANSFORMATION]];
    ASM_REWRITE_TAC[DET_MUL; DET_TRANSP] THEN
    MATCH_MP_TAC(REAL_RING
     `(x = &1 \/ x = -- &1) /\ y = a ==> x * y * x = a`) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[DET_ORTHOGONAL_MATRIX; ORTHOGONAL_TRANSFORMATION_MATRIX];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) DET_UPPERTRIANGULAR o lhand o snd) THEN
    SIMP_TAC[MATRIX_REFLECT_ALONG_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    SIMP_TAC[LAMBDA_BETA; ARITH_RULE
     `j < i ==> ~(i = j) /\ ~(i = 1 /\ j = 1)`] THEN
    DISCH_THEN(K ALL_TAC) THEN
    SIMP_TAC[PRODUCT_CLAUSES_LEFT; DIMINDEX_GE_1] THEN
    MATCH_MP_TAC(REAL_RING `x = &1 ==> a * x = a`) THEN
    MATCH_MP_TAC PRODUCT_EQ_1 THEN
    REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let DET_MATRIX_REFLECT_ALONG = prove
 (`!v:real^N. det(matrix(reflect_along v)) =
                if v = vec 0 then &1 else --(&1)`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[REFLECT_ALONG_ZERO] THEN
  REWRITE_TAC[MATRIX_I; DET_I] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ROTOINVERSION_MATRIX_REFLECT_ALONG) THEN
  SIMP_TAC[rotoinversion_matrix]);;

let REFLECT_ALONG_BASIS_COMPONENT = prove
 (`!x:real^N i j.
       1 <= i /\ i <= dimindex(:N) /\
       1 <= j /\ j <= dimindex(:N)
       ==> reflect_along (basis i) x$j = if j = i then --(x$j) else x$j`,
  SIMP_TAC[REFLECT_ALONG_BASIS; VECTOR_SUB_COMPONENT] THEN
  SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
  REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let REFLECT_BASIS_ALONG_BASIS = prove
 (`!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
         ==> reflect_along (basis i:real^N) (basis j) =
             if i = j then --(basis j) else basis j`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CART_EQ; REFLECT_ALONG_BASIS_COMPONENT; BASIS_COMPONENT;
               VECTOR_NEG_COMPONENT] THEN
  ASM_MESON_TAC[REAL_NEG_0]);;

let NORM_REFLECT_ALONG = prove
 (`!v x:real^N. norm(reflect_along v x) = norm x`,
  MESON_TAC[ORTHOGONAL_TRANSFORMATION;
            ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG]);;

let REFLECT_ALONG_EQ = prove
 (`!v x y:real^N. reflect_along v x = reflect_along v y <=> x = y`,
  MESON_TAC[ORTHOGONAL_TRANSFORMATION_INJECTIVE;
            ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG]);;

let REFLECT_ALONG_SURJECTIVE = prove
 (`!v y:real^N. ?x. reflect_along v x = y`,
  MESON_TAC[REFLECT_ALONG_INVOLUTION]);;

let REFLECT_ALONG_SWITCH = prove
 (`!a b:real^N.
        norm a = norm b /\ ~(a = b)
        ==> reflect_along (b - a) a = b /\ reflect_along (b - a) b = a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC[reflect_along; DOT_RSUB] THEN
  REWRITE_TAC[real_div; VECTOR_ARITH
    `(a - c % (b - a):real^N = b <=> (&1 + c) % (b - a) = vec 0) /\
     (b - c % (b - a):real^N = a <=> (&1 - c) % (b - a) = vec 0)`] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
  MATCH_MP_TAC(REAL_FIELD
   `~(d = &0) /\ x + y = &0 /\ y - x = d
    ==> &1 + &2 * x * inv d = &0 /\ &1 - &2 * y * inv d = &0`) THEN
  ASM_REWRITE_TAC[GSYM DOT_RSUB; DOT_EQ_0; VECTOR_SUB_EQ] THEN
  ASM_REWRITE_TAC[DOT_RSUB; GSYM NORM_POW_2; DOT_LSUB] THEN
  REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC);;

let ROTOINVERSION_EXISTS_GEN = prove
 (`!s a b:real^N.
        subspace s /\ a IN s /\ b IN s /\ ~(a = b) /\ norm a = norm b
         ==> ?f. orthogonal_transformation f /\ IMAGE f s = s /\
                 (!x. orthogonal a x /\ orthogonal b x ==> f x = x) /\
                 det (matrix f) = -- &1 /\
                 f a = b /\ f b = a`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `reflect_along (b - a:real^N)` THEN
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG] THEN
  ASM_REWRITE_TAC[DET_MATRIX_REFLECT_ALONG; VECTOR_SUB_EQ] THEN
  ASM_SIMP_TAC[REFLECT_ALONG_SWITCH] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x. f(f x) = x) /\ (!x. x IN s ==> f x IN s) ==> IMAGE f s = s`) THEN
    REWRITE_TAC[REFLECT_ALONG_INVOLUTION] THEN REWRITE_TAC[reflect_along] THEN
    ASM_SIMP_TAC[SUBSPACE_SUB; SUBSPACE_MUL];
    REWRITE_TAC[ONCE_REWRITE_RULE[DOT_SYM] orthogonal] THEN
    SIMP_TAC[reflect_along; DOT_RSUB] THEN
    REWRITE_TAC[real_div; REAL_SUB_REFL; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
    REWRITE_TAC[VECTOR_ARITH `x - &0 % y:real^N = x`]]);;

let ORTHOGONAL_TRANSFORMATION_EXISTS_GEN = prove
 (`!s a b:real^N.
        subspace s /\ a IN s /\ b IN s /\ norm a = norm b
         ==> ?f. orthogonal_transformation f /\ IMAGE f s = s /\
                 (!x. orthogonal a x /\ orthogonal b x ==> f x = x) /\
                 f a = b /\ f b = a`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `b:real^N = a` THENL
   [EXISTS_TAC `\x:real^N. x` THEN
    ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_ID; IMAGE_ID];
    MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`; `b:real^N`]
        ROTOINVERSION_EXISTS_GEN) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* All orthogonal transformations are a composition of reflections.          *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_TRANSFORMATION_GENERATED_BY_REFLECTIONS = prove
 (`!f:real^N->real^N n.
        orthogonal_transformation f /\
        dimindex(:N) <= dim {x | f x = x} + n
        ==> ?l. LENGTH l <= n /\ ALL (\v. ~(v = vec 0)) l /\
                f = ITLIST (\v h. reflect_along v o h) l I`,
  ONCE_REWRITE_TAC[GSYM SWAP_FORALL_THM] THEN INDUCT_TAC THENL
   [REWRITE_TAC[CONJUNCT1 LE; LENGTH_EQ_NIL; ADD_CLAUSES; UNWIND_THM2] THEN
    SIMP_TAC[DIM_SUBSET_UNIV; ARITH_RULE `a:num <= b ==> (b <= a <=> a = b)`;
             ITLIST; DIM_EQ_FULL; orthogonal_transformation] THEN
    SIMP_TAC[SPAN_OF_SUBSPACE; SUBSPACE_LINEAR_FIXED_POINTS; IMP_CONJ] THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_ELIM_THM] THEN
    SIMP_TAC[FUN_EQ_THM; I_THM; ALL];
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `!x:real^N. f x = x` THENL
     [EXISTS_TAC `[]:(real^N) list` THEN
      ASM_REWRITE_TAC[ITLIST; FUN_EQ_THM; I_THM; ALL; LENGTH; LE_0];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM])] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    ABBREV_TAC `v:real^N = inv(&2) % (f a - a)` THEN FIRST_X_ASSUM
      (MP_TAC o SPEC `reflect_along v o (f:real^N->real^N)`) THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG;
                 ORTHOGONAL_TRANSFORMATION_COMPOSE] THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
       `a <= d + SUC n ==> d < d' ==> a <= d' + n`)) THEN
      MATCH_MP_TAC DIM_PSUBSET THEN REWRITE_TAC[PSUBSET_ALT] THEN
      SUBGOAL_THEN
       `!y:real^N. dist(y,f a) = dist(y,a) ==> reflect_along v y = y`
      ASSUME_TAC THENL
       [REWRITE_TAC[dist; NORM_EQ_SQUARE; NORM_POS_LE; NORM_POW_2] THEN
        REWRITE_TAC[VECTOR_ARITH
         `(y - b:real^N) dot (y - b) =
          (y dot y + b dot b) - &2 * y dot b`] THEN
        REWRITE_TAC[REAL_ARITH `(y + aa) - &2 * a = (y + bb) - &2 * b <=>
                                a - b = inv(&2) * (aa - bb)`] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[orthogonal_transformation]) THEN
        ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO] THEN
        EXPAND_TAC "v" THEN REWRITE_TAC[GSYM DOT_RSUB; reflect_along] THEN
        SIMP_TAC[DOT_RMUL; real_div; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
        REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SPAN_MONO THEN SIMP_TAC[SUBSET; IN_ELIM_THM; o_THM] THEN
        ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_ISOMETRY];
        ALL_TAC] THEN
      EXISTS_TAC `a:real^N` THEN
      ASM_SIMP_TAC[SUBSPACE_LINEAR_FIXED_POINTS; SPAN_OF_SUBSPACE;
                   ORTHOGONAL_TRANSFORMATION_LINEAR; IN_ELIM_THM] THEN
      MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `reflect_along (v:real^N) (midpoint(f a,a) + v)` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC;
        REWRITE_TAC[REFLECT_ALONG_ADD] THEN
        ASM_SIMP_TAC[DIST_MIDPOINT; REFLECT_ALONG_REFL]] THEN
      EXPAND_TAC "v" THEN REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `l:(real^N)list` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `CONS (v:real^N) l` THEN
      ASM_REWRITE_TAC[ALL; LENGTH; LE_SUC; VECTOR_SUB_EQ; ITLIST] THEN
      EXPAND_TAC "v" THEN ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM
       `(o)(reflect_along (v:real^N)):(real^N->real^N)->(real^N->real^N)`) THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM; REFLECT_ALONG_INVOLUTION]]]);;

let ORTHOGONAL_TRANSFORMATION_REFLECT_INDUCT = prove
 (`!P:(real^N->real^N)->bool.
        P I /\
        (!f a. orthogonal_transformation f /\ ~(a = vec 0) /\ P f
               ==> P(reflect_along a o f))
        ==> !f. orthogonal_transformation f ==> P f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `dimindex(:N)`]
        ORTHOGONAL_TRANSFORMATION_GENERATED_BY_REFLECTIONS) THEN
  ASM_REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] LE_ADD] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(real^N)list` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `orthogonal_transformation(f:real^N->real^N)` THEN
  MATCH_MP_TAC(TAUT `p /\ q ==> p ==> q`) THEN FIRST_X_ASSUM SUBST1_TAC THEN
  UNDISCH_TAC `ALL (\v:real^N. ~(v = vec 0)) l` THEN
  UNDISCH_THEN `LENGTH(l:(real^N)list) <= dimindex(:N)` (K ALL_TAC) THEN
  SPEC_TAC(`l:(real^N)list`,`l:(real^N)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[ALL; ITLIST] THEN
  ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_I] THEN
  ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_COMPOSE;
               ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG]);;

(* ------------------------------------------------------------------------- *)
(* Extract scaling, translation and linear invariance theorems.              *)
(* For the linear case, chain through some basic consequences automatically, *)
(* e.g. norm-preserving and linear implies injective.                        *)
(* ------------------------------------------------------------------------- *)

let SCALING_THEOREMS v =
  let th1 = UNDISCH(snd(EQ_IMP_RULE(ISPEC v NORM_POS_LT))) in
  let t = rand(concl th1) in
  end_itlist CONJ (map (C MP th1 o SPEC t) (!scaling_theorems));;

let TRANSLATION_INVARIANTS x =
  end_itlist CONJ (mapfilter (ISPEC x) (!invariant_under_translation));;

let USABLE_CONCLUSION f ths th =
  let ith = PURE_REWRITE_RULE[RIGHT_FORALL_IMP_THM] (ISPEC f th) in
  let bod = concl ith in
  let cjs = conjuncts(fst(dest_imp bod)) in
  let ths = map (fun t -> find(fun th -> aconv (concl th) t) ths) cjs in
  GEN_ALL(MP ith (end_itlist CONJ ths));;

let LINEAR_INVARIANTS =
  let sths = (CONJUNCTS o prove)
   (`(!f:real^M->real^N.
         linear f /\ (!x. norm(f x) = norm x)
         ==> (!x y. f x = f y ==> x = y)) /\
     (!f:real^N->real^N.
         linear f /\ (!x. norm(f x) = norm x) ==> (!y. ?x. f x = y)) /\
     (!f:real^N->real^N. linear f /\ (!x y. f x = f y ==> x = y)
                         ==> (!y. ?x. f x = y)) /\
     (!f:real^N->real^N. linear f /\ (!y. ?x. f x = y)
                         ==> (!x y. f x = f y ==> x = y))`,
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
      SIMP_TAC[GSYM LINEAR_SUB; GSYM NORM_EQ_0];
      MESON_TAC[ORTHOGONAL_TRANSFORMATION_SURJECTIVE;
                ORTHOGONAL_TRANSFORMATION_INJECTIVE; ORTHOGONAL_TRANSFORMATION;
                LINEAR_SURJECTIVE_IFF_INJECTIVE]]) in
  fun f ths ->
    let ths' = ths @ mapfilter (USABLE_CONCLUSION f ths) sths in
    end_itlist CONJ
     (mapfilter (USABLE_CONCLUSION f ths') (!invariant_under_linear));;

(* ------------------------------------------------------------------------- *)
(* Tactic to pick WLOG a particular point as the origin. The conversion form *)
(* assumes it's the outermost universal variable; the tactic is more general *)
(* and allows any free or outer universally quantified variable. The list    *)
(* "avoid" is the points not to translate. There is also a tactic to help in *)
(* proving new translation theorems, which uses similar machinery.           *)
(* ------------------------------------------------------------------------- *)

let GEOM_ORIGIN_CONV,GEOM_TRANSLATE_CONV =
  let pth = prove
   (`!a:real^N. a = a + vec 0 /\
                {} = IMAGE (\x. a + x) {} /\
                {} = IMAGE (IMAGE (\x. a + x)) {} /\
                (:real^N) = IMAGE (\x. a + x) (:real^N) /\
                (:real^N->bool) = IMAGE (IMAGE (\x. a + x)) (:real^N->bool) /\
                [] = MAP (\x. a + x) []`,
    REWRITE_TAC[IMAGE_CLAUSES; VECTOR_ADD_RID; MAP] THEN
    REWRITE_TAC[SET_RULE `UNIV = IMAGE f UNIV <=> !y. ?x. f x = y`] THEN
    REWRITE_TAC[SURJECTIVE_IMAGE] THEN
    REWRITE_TAC[VECTOR_ARITH `a + y:real^N = x <=> y = x - a`; EXISTS_REFL])
  and qth = prove
   (`!a:real^N.
        ((!P. (!x. P x) <=> (!x. P (a + x))) /\
         (!P. (?x. P x) <=> (?x. P (a + x))) /\
         (!Q. (!s. Q s) <=> (!s. Q(IMAGE (\x. a + x) s))) /\
         (!Q. (?s. Q s) <=> (?s. Q(IMAGE (\x. a + x) s))) /\
         (!Q. (!s. Q s) <=> (!s. Q(IMAGE (IMAGE (\x. a + x)) s))) /\
         (!Q. (?s. Q s) <=> (?s. Q(IMAGE (IMAGE (\x. a + x)) s))) /\
         (!P. (!g:real^1->real^N. P g) <=> (!g. P ((\x. a + x) o g))) /\
         (!P. (?g:real^1->real^N. P g) <=> (?g. P ((\x. a + x) o g))) /\
         (!P. (!g:num->real^N. P g) <=> (!g. P ((\x. a + x) o g))) /\
         (!P. (?g:num->real^N. P g) <=> (?g. P ((\x. a + x) o g))) /\
         (!Q. (!l. Q l) <=> (!l. Q(MAP (\x. a + x) l))) /\
         (!Q. (?l. Q l) <=> (?l. Q(MAP (\x. a + x) l)))) /\
        ((!P. {x | P x} = IMAGE (\x. a + x) {x | P(a + x)}) /\
         (!Q. {s | Q s} =
              IMAGE (IMAGE (\x. a + x)) {s | Q(IMAGE (\x. a + x) s)}) /\
         (!R. {l | R l} = IMAGE (MAP (\x. a + x)) {l | R(MAP (\x. a + x) l)}))`,
    GEN_TAC THEN MATCH_MP_TAC QUANTIFY_SURJECTION_HIGHER_THM THEN
    X_GEN_TAC `y:real^N` THEN EXISTS_TAC `y - a:real^N` THEN
    VECTOR_ARITH_TAC) in
  let GEOM_ORIGIN_CONV avoid tm =
    let x,tm0 = dest_forall tm in
    let th0 = ISPEC x pth in
    let x' = genvar(type_of x) in
    let ith = ISPEC x' qth in
    let th1 = PARTIAL_EXPAND_QUANTS_CONV avoid (ASSUME(concl ith)) tm0 in
    let th2 = CONV_RULE(RAND_CONV(SUBS_CONV(CONJUNCTS th0))) th1 in
    let th3 = INST[x,x'] (PROVE_HYP ith th2) in
    let ths = TRANSLATION_INVARIANTS x in
    let thr = REFL x in
    let th4 = GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV)
      [BETA_THM;ADD_ASSUM(concl thr) ths] th3 in
    let th5 = MK_FORALL x (PROVE_HYP thr th4) in
    GEN_REWRITE_RULE (RAND_CONV o TRY_CONV) [FORALL_SIMP] th5
  and GEOM_TRANSLATE_CONV avoid a tm =
    let cth = CONJUNCT2(ISPEC a pth)
    and vth = ISPEC a qth in
    let th1 = PARTIAL_EXPAND_QUANTS_CONV avoid (ASSUME(concl vth)) tm in
    let th2 = CONV_RULE(RAND_CONV(SUBS_CONV(CONJUNCTS cth))) th1 in
    let th3 = PROVE_HYP vth th2 in
    let ths = TRANSLATION_INVARIANTS a in
    let thr = REFL a in
    let th4 = GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV)
        [BETA_THM;ADD_ASSUM(concl thr) ths] th3 in
    PROVE_HYP thr th4 in
  GEOM_ORIGIN_CONV,GEOM_TRANSLATE_CONV;;

let GEN_GEOM_ORIGIN_TAC x avoid (asl,w as gl) =
  let avs,bod = strip_forall w
  and avs' = subtract (frees w) (freesl(map (concl o snd) asl)) in
  (MAP_EVERY X_GEN_TAC avs THEN
   MAP_EVERY (fun t -> SPEC_TAC(t,t)) (rev(subtract (avs@avs') [x])) THEN
   SPEC_TAC(x,x) THEN CONV_TAC(GEOM_ORIGIN_CONV avoid)) gl;;

let GEOM_ORIGIN_TAC x = GEN_GEOM_ORIGIN_TAC x [];;

let GEOM_TRANSLATE_TAC avoid (asl,w) =
  let a,bod = dest_forall w in
  let n = length(fst(strip_forall bod)) in
  (X_GEN_TAC a THEN
   CONV_TAC(funpow n BINDER_CONV (LAND_CONV(GEOM_TRANSLATE_CONV avoid a))) THEN
   REWRITE_TAC[]) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Rename existential variables in conclusion to fresh genvars.              *)
(* ------------------------------------------------------------------------- *)

let EXISTS_GENVAR_RULE =
  let rec rule vs th =
    match vs with
      [] -> th
    | v::ovs -> let x,bod = dest_exists(concl th) in
                let th1 = rule ovs (ASSUME bod) in
                let th2 = SIMPLE_CHOOSE x (SIMPLE_EXISTS x th1) in
                PROVE_HYP th (CONV_RULE (GEN_ALPHA_CONV v) th2) in
  fun th -> rule (map (genvar o type_of) (fst(strip_exists(concl th)))) th;;

(* ------------------------------------------------------------------------- *)
(* Rotate so that WLOG some point is a +ve multiple of basis vector k.       *)
(* For general N, it's better to use k = 1 so the side-condition can be      *)
(* discharged. For dimensions 1, 2 and 3 anything will work automatically.   *)
(* Could generalize by asking the user to prove theorem 1 <= k <= N.         *)
(* ------------------------------------------------------------------------- *)

let GEOM_BASIS_MULTIPLE_RULE =
  let pth = prove
   (`!f. orthogonal_transformation (f:real^N->real^N)
         ==> (vec 0 = f(vec 0) /\
              {} = IMAGE f {} /\
              {} = IMAGE (IMAGE f) {} /\
              (:real^N) = IMAGE f (:real^N) /\
              (:real^N->bool) = IMAGE (IMAGE f) (:real^N->bool) /\
              [] = MAP f []) /\
             ((!P. (!x. P x) <=> (!x. P (f x))) /\
              (!P. (?x. P x) <=> (?x. P (f x))) /\
              (!Q. (!s. Q s) <=> (!s. Q (IMAGE f s))) /\
              (!Q. (?s. Q s) <=> (?s. Q (IMAGE f s))) /\
              (!Q. (!s. Q s) <=> (!s. Q (IMAGE (IMAGE f) s))) /\
              (!Q. (?s. Q s) <=> (?s. Q (IMAGE (IMAGE f) s))) /\
              (!P. (!g:real^1->real^N. P g) <=> (!g. P (f o g))) /\
              (!P. (?g:real^1->real^N. P g) <=> (?g. P (f o g))) /\
              (!P. (!g:num->real^N. P g) <=> (!g. P (f o g))) /\
              (!P. (?g:num->real^N. P g) <=> (?g. P (f o g))) /\
              (!Q. (!l. Q l) <=> (!l. Q(MAP f l))) /\
              (!Q. (?l. Q l) <=> (?l. Q(MAP f l)))) /\
             ((!P. {x | P x} = IMAGE f {x | P(f x)}) /\
              (!Q. {s | Q s} = IMAGE (IMAGE f) {s | Q(IMAGE f s)}) /\
              (!R. {l | R l} = IMAGE (MAP f) {l | R(MAP f l)}))`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o
          MATCH_MP ORTHOGONAL_TRANSFORMATION_SURJECTIVE) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IMAGE_CLAUSES; MAP] THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
      CONJ_TAC THENL [ASM_MESON_TAC[LINEAR_0]; ALL_TAC] THEN
      REWRITE_TAC[SET_RULE `UNIV = IMAGE f UNIV <=> !y. ?x. f x = y`] THEN
      ASM_REWRITE_TAC[SURJECTIVE_IMAGE];
      MATCH_MP_TAC QUANTIFY_SURJECTION_HIGHER_THM THEN ASM_REWRITE_TAC[]])
  and oth = prove
   (`!f:real^N->real^N.
        orthogonal_transformation f /\
        (2 <= dimindex(:N) ==> det(matrix f) = &1)
        ==> linear f /\
            (!x y. f x = f y ==> x = y) /\
            (!y. ?x. f x = y) /\
            (!x. norm(f x) = norm x) /\
            (2 <= dimindex(:N) ==> det(matrix f) = &1)`,
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR];
      ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_INJECTIVE];
      ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_SURJECTIVE];
      ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]])
  and arithconv = REWRITE_CONV[DIMINDEX_1; DIMINDEX_2; DIMINDEX_3;
                               ARITH_RULE `1 <= 1`; DIMINDEX_GE_1] THENC
                  NUM_REDUCE_CONV in
  fun k tm ->
    let x,bod = dest_forall tm in
    let th0 = ISPECL [x; mk_small_numeral k] ROTATION_RIGHTWARD_LINE in
    let th1 = EXISTS_GENVAR_RULE
     (MP th0 (EQT_ELIM(arithconv(lhand(concl th0))))) in
    let [a;f],tm1 = strip_exists(concl th1) in
    let th_orth,th2 = CONJ_PAIR(ASSUME tm1) in
    let th_det,th2a = CONJ_PAIR th2 in
    let th_works,th_zero = CONJ_PAIR th2a in
    let thc,thq = CONJ_PAIR(PROVE_HYP th2 (UNDISCH(ISPEC f pth))) in
    let th3 = CONV_RULE(RAND_CONV(SUBS_CONV(GSYM th_works::CONJUNCTS thc)))
               (EXPAND_QUANTS_CONV(ASSUME(concl thq)) bod) in
    let th4 = PROVE_HYP thq th3 in
    let thps = CONJUNCTS(MATCH_MP oth (CONJ th_orth th_det)) in
    let th5 = LINEAR_INVARIANTS f thps in
    let th6 = PROVE_HYP th_orth
     (GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV) [BETA_THM; th5] th4) in
    let ntm = mk_forall(a,mk_imp(concl th_zero,rand(concl th6))) in
    let th7 = MP(SPEC a (ASSUME ntm)) th_zero in
    let th8 = DISCH ntm (EQ_MP (SYM th6) th7) in
    if intersect (frees(concl th8)) [a;f] = [] then
      let th9 = PROVE_HYP th1 (itlist SIMPLE_CHOOSE [a;f] th8) in
      let th10 = DISCH ntm (GEN x (UNDISCH th9)) in
      let a' = variant (frees(concl th10))
                (mk_var(fst(dest_var x),snd(dest_var a))) in
      CONV_RULE(LAND_CONV (GEN_ALPHA_CONV a')) th10
    else
      let mtm = list_mk_forall([a;f],mk_imp(hd(hyp th8),rand(concl th6))) in
      let th9 = EQ_MP (SYM th6) (UNDISCH(SPECL [a;f] (ASSUME mtm))) in
      let th10 = itlist SIMPLE_CHOOSE [a;f] (DISCH mtm th9) in
      let th11 = GEN x (PROVE_HYP th1 th10) in
      MATCH_MP MONO_FORALL th11;;

let GEOM_BASIS_MULTIPLE_TAC k l (asl,w as gl) =
  let avs,bod = strip_forall w
  and avs' = subtract (frees w) (freesl(map (concl o snd) asl)) in
  (MAP_EVERY X_GEN_TAC avs THEN
   MAP_EVERY (fun t -> SPEC_TAC(t,t)) (rev(subtract (avs@avs') [l])) THEN
   SPEC_TAC(l,l) THEN
   W(MATCH_MP_TAC o GEOM_BASIS_MULTIPLE_RULE k o snd)) gl;;

(* ------------------------------------------------------------------------- *)
(* Create invariance theorems automatically, in simple cases. If there are   *)
(* any nested quantifiers, this will need surjectivity. It's often possible  *)
(* to prove a stronger theorem by more delicate manual reasoning, so this    *)
(* isn't used nearly as often as GEOM_TRANSLATE_CONV / GEOM_TRANSLATE_TAC.   *)
(* As a small step, some ad-hoc rewrites analogous to FORALL_IN_IMAGE are    *)
(* tried if the first step doesn't finish the goal, but it's very ad hoc.    *)
(* ------------------------------------------------------------------------- *)

let GEOM_TRANSFORM_TAC =
  let cth0 = prove
   (`!f:real^M->real^N.
          linear f
          ==> vec 0 = f(vec 0) /\
              {} = IMAGE f {} /\
              {} = IMAGE (IMAGE f) {}`,
    REWRITE_TAC[IMAGE_CLAUSES] THEN MESON_TAC[LINEAR_0])
  and cth1 = prove
   (`!f:real^M->real^N.
          (!y. ?x. f x = y)
          ==> (:real^N) = IMAGE f (:real^M) /\
              (:real^N->bool) = IMAGE (IMAGE f) (:real^M->bool)`,
    REWRITE_TAC[SET_RULE `UNIV = IMAGE f UNIV <=> !y. ?x. f x = y`] THEN
    REWRITE_TAC[SURJECTIVE_IMAGE])
  and sths = (CONJUNCTS o prove)
   (`(!f:real^M->real^N.
         linear f /\ (!x. norm(f x) = norm x)
         ==> (!x y. f x = f y ==> x = y)) /\
     (!f:real^N->real^N.
         linear f /\ (!x. norm(f x) = norm x) ==> (!y. ?x. f x = y)) /\
     (!f:real^N->real^N. linear f /\ (!x y. f x = f y ==> x = y)
                         ==> (!y. ?x. f x = y)) /\
     (!f:real^N->real^N. linear f /\ (!y. ?x. f x = y)
                         ==> (!x y. f x = f y ==> x = y))`,
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
      SIMP_TAC[GSYM LINEAR_SUB; GSYM NORM_EQ_0];
      MESON_TAC[ORTHOGONAL_TRANSFORMATION_SURJECTIVE;
                ORTHOGONAL_TRANSFORMATION_INJECTIVE; ORTHOGONAL_TRANSFORMATION;
                LINEAR_SURJECTIVE_IFF_INJECTIVE]])
  and aths = (CONJUNCTS o prove)
   (`(!f s P. (!y. y IN IMAGE f s ==> P y) <=> (!x. x IN s ==> P(f x))) /\
     (!f s P. (!u. u IN IMAGE (IMAGE f) s ==> P u) <=>
              (!t. t IN s ==> P(IMAGE f t))) /\
     (!f s P. (?y. y IN IMAGE f s /\ P y) <=> (?x. x IN s /\ P(f x))) /\
     (!f s P. (?u. u IN IMAGE (IMAGE f) s /\ P u) <=>
              (?t. t IN s /\ P(IMAGE f t)))`,
    SET_TAC[]) in
  fun avoid (asl,w as gl) ->
    let f,wff = dest_forall w in
    let vs,bod = strip_forall wff in
    let ant,cons = dest_imp bod in
    let hths = CONJUNCTS(ASSUME ant) in
    let fths = hths @ mapfilter (USABLE_CONCLUSION f hths) sths in
    let cths = mapfilter (USABLE_CONCLUSION f fths) [cth0; cth1]
    and vconv =
      try let vth = USABLE_CONCLUSION f fths QUANTIFY_SURJECTION_HIGHER_THM in
          PROVE_HYP vth o PARTIAL_EXPAND_QUANTS_CONV avoid (ASSUME(concl vth))
      with Failure _ -> ALL_CONV
    and bths = LINEAR_INVARIANTS f fths in
    (MAP_EVERY X_GEN_TAC (f::vs) THEN DISCH_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) cths THEN
     CONV_TAC(LAND_CONV vconv) THEN
     GEN_REWRITE_TAC (LAND_CONV o REDEPTH_CONV) [bths] THEN
     REWRITE_TAC[] THEN
     REWRITE_TAC(mapfilter (ADD_ASSUM ant o ISPEC f) aths) THEN
     GEN_REWRITE_TAC (LAND_CONV o REDEPTH_CONV) [bths] THEN
     REWRITE_TAC[]) gl;;

(* ------------------------------------------------------------------------- *)
(* Scale so that a chosen vector has size 1. Generates a conjunction of      *)
(* two formulas, one for the zero case (which one hopes is trivial) and      *)
(* one just like the original goal but with a norm(...) = 1 assumption.      *)
(* ------------------------------------------------------------------------- *)

let GEOM_NORMALIZE_RULE =
  let pth = prove
   (`!a:real^N. ~(a = vec 0)
                ==> vec 0 = norm(a) % vec 0 /\
                    a = norm(a) % inv(norm a) % a /\
                    {} = IMAGE (\x. norm(a) % x) {} /\
                    {} = IMAGE (IMAGE (\x. norm(a) % x)) {} /\
                    (:real^N) = IMAGE (\x. norm(a) % x) (:real^N) /\
                    (:real^N->bool) =
                    IMAGE (IMAGE (\x. norm(a) % x)) (:real^N->bool) /\
                    [] = MAP (\x. norm(a) % x) []`,
    REWRITE_TAC[IMAGE_CLAUSES; VECTOR_MUL_ASSOC; VECTOR_MUL_RZERO; MAP] THEN
    SIMP_TAC[NORM_EQ_0; REAL_MUL_RINV; VECTOR_MUL_LID] THEN
    GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[SET_RULE `UNIV = IMAGE f UNIV <=> !y. ?x. f x = y`] THEN
    ASM_REWRITE_TAC[SURJECTIVE_IMAGE] THEN
    X_GEN_TAC `y:real^N` THEN EXISTS_TAC `inv(norm(a:real^N)) % y:real^N` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; NORM_EQ_0; REAL_MUL_RINV; VECTOR_MUL_LID])
  and qth = prove
   (`!a:real^N.
        ~(a = vec 0)
        ==> ((!P. (!r:real. P r) <=> (!r. P(norm a * r))) /\
             (!P. (?r:real. P r) <=> (?r. P(norm a * r))) /\
             (!P. (!x:real^N. P x) <=> (!x. P (norm(a) % x))) /\
             (!P. (?x:real^N. P x) <=> (?x. P (norm(a) % x))) /\
             (!Q. (!s:real^N->bool. Q s) <=>
                  (!s. Q(IMAGE (\x. norm(a) % x) s))) /\
             (!Q. (?s:real^N->bool. Q s) <=>
                  (?s. Q(IMAGE (\x. norm(a) % x) s))) /\
             (!Q. (!s:(real^N->bool)->bool. Q s) <=>
                  (!s. Q(IMAGE (IMAGE (\x. norm(a) % x)) s))) /\
             (!Q. (?s:(real^N->bool)->bool. Q s) <=>
                  (?s. Q(IMAGE (IMAGE (\x. norm(a) % x)) s))) /\
             (!P. (!g:real^1->real^N. P g) <=>
                  (!g. P ((\x. norm(a) % x) o g))) /\
             (!P. (?g:real^1->real^N. P g) <=>
                  (?g. P ((\x. norm(a) % x) o g))) /\
             (!P. (!g:num->real^N. P g) <=>
                  (!g. P ((\x. norm(a) % x) o g))) /\
             (!P. (?g:num->real^N. P g) <=>
                  (?g. P ((\x. norm(a) % x) o g))) /\
             (!Q. (!l. Q l) <=> (!l. Q(MAP (\x:real^N. norm(a) % x) l))) /\
             (!Q. (?l. Q l) <=> (?l. Q(MAP (\x:real^N. norm(a) % x) l)))) /\
            ((!P. {x:real^N | P x} =
                  IMAGE (\x. norm(a) % x) {x | P(norm(a) % x)}) /\
             (!Q. {s:real^N->bool | Q s} =
                  IMAGE (IMAGE (\x. norm(a) % x))
                       {s | Q(IMAGE (\x. norm(a) % x) s)}) /\
             (!R. {l:(real^N)list | R l} =
                  IMAGE (MAP (\x:real^N. norm(a) % x))
                        {l | R(MAP (\x:real^N. norm(a) % x) l)}))`,
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC(TAUT
     `(a /\ b) /\ c /\ d ==> (a /\ b /\ c) /\ d`) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[NORM_EQ_0; REAL_FIELD `~(x = &0) ==> x * inv x * a = a`];
      MP_TAC(ISPEC `\x:real^N. norm(a:real^N) % x`
        (INST_TYPE [`:real^1`,`:C`] QUANTIFY_SURJECTION_HIGHER_THM)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[SURJECTIVE_SCALING; NORM_EQ_0]])
  and lth = prove
   (`(!b:real^N. ~(b = vec 0) ==> (P(b) <=> Q(inv(norm b) % b)))
     ==> P(vec 0) /\ (!b. norm(b) = &1 ==> Q b) ==> (!b. P b)`,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `b:real^N = vec 0` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM;
                 REAL_MUL_LINV; NORM_EQ_0]) in
  fun avoid tm ->
    let x,tm0 = dest_forall tm in
    let cth = UNDISCH(ISPEC x pth)
    and vth = UNDISCH(ISPEC x qth) in
    let th1 = ONCE_REWRITE_CONV[cth] tm0 in
    let th2 = CONV_RULE (RAND_CONV
     (PARTIAL_EXPAND_QUANTS_CONV avoid vth)) th1 in
    let th3 = SCALING_THEOREMS x in
    let th3' = (end_itlist CONJ (map
       (fun th -> let avs,_ = strip_forall(concl th) in
                  let gvs = map (genvar o type_of) avs in
                  GENL gvs (SPECL gvs th))
       (CONJUNCTS th3))) in
    let th4 = GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV)
               [BETA_THM; th3'] th2 in
    MATCH_MP lth (GEN x (DISCH_ALL th4));;

let GEN_GEOM_NORMALIZE_TAC x avoid (asl,w as gl) =
  let avs,bod = strip_forall w
  and avs' = subtract (frees w) (freesl(map (concl o snd) asl)) in
  (MAP_EVERY X_GEN_TAC avs THEN
   MAP_EVERY (fun t -> SPEC_TAC(t,t)) (rev(subtract (avs@avs') [x])) THEN
   SPEC_TAC(x,x) THEN
   W(MATCH_MP_TAC o GEOM_NORMALIZE_RULE avoid o snd)) gl;;

let GEOM_NORMALIZE_TAC x = GEN_GEOM_NORMALIZE_TAC x [];;

(* ------------------------------------------------------------------------- *)
(* Add invariance theorems for collinearity.                                 *)
(* ------------------------------------------------------------------------- *)

let COLLINEAR_TRANSLATION_EQ = prove
 (`!a s. collinear (IMAGE (\x. a + x) s) <=> collinear s`,
  REWRITE_TAC[collinear] THEN GEOM_TRANSLATE_TAC["u"]);;

add_translation_invariants [COLLINEAR_TRANSLATION_EQ];;

let COLLINEAR_TRANSLATION = prove
 (`!s a. collinear s ==> collinear (IMAGE (\x. a + x) s)`,
  REWRITE_TAC[COLLINEAR_TRANSLATION_EQ]);;

let COLLINEAR_LINEAR_IMAGE = prove
 (`!f s. collinear s /\ linear f ==> collinear(IMAGE f s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[collinear; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  ASM_MESON_TAC[LINEAR_SUB; LINEAR_CMUL]);;

let COLLINEAR_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (collinear (IMAGE f s) <=> collinear s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE COLLINEAR_LINEAR_IMAGE));;

add_linear_invariants [COLLINEAR_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Take a theorem "th" with outer universal quantifiers involving real^N     *)
(* and a theorem "dth" asserting |- dimindex(:M) <= dimindex(:N) and         *)
(* return a theorem replacing type :N by :M in th. Neither N or M need be a  *)
(* type variable.                                                            *)
(* ------------------------------------------------------------------------- *)

let GEOM_DROP_DIMENSION_RULE =
  let oth = prove
   (`!f:real^M->real^N.
          linear f /\ (!x. norm(f x) = norm x)
          ==> linear f /\
              (!x y. f x = f y ==> x = y) /\
              (!x. norm(f x) = norm x)`,
    MESON_TAC[PRESERVES_NORM_INJECTIVE])
  and cth = prove
   (`linear(f:real^M->real^N)
     ==> vec 0 = f(vec 0) /\
         {} = IMAGE f {} /\
         {} = IMAGE (IMAGE f) {} /\
         [] = MAP f []`,
    REWRITE_TAC[IMAGE_CLAUSES; MAP; GSYM LINEAR_0]) in
  fun dth th ->
    let ath = GEN_ALL th
    and eth = MATCH_MP ISOMETRY_UNIV_UNIV dth
    and avoid = variables(concl th) in
    let f,bod = dest_exists(concl eth) in
    let fimage = list_mk_icomb "IMAGE" [f]
    and fmap = list_mk_icomb "MAP" [f]
    and fcompose = list_mk_icomb "o" [f] in
    let fimage2 = list_mk_icomb "IMAGE" [fimage] in
    let lin,iso = CONJ_PAIR(ASSUME bod) in
    let olduniv = rand(rand(concl dth))
    and newuniv = rand(lhand(concl dth)) in
    let oldty = fst(dest_fun_ty(type_of olduniv))
    and newty = fst(dest_fun_ty(type_of newuniv)) in
    let newvar v =
       let n,t = dest_var v in
       variant avoid (mk_var(n,tysubst[newty,oldty] t)) in
    let newterm v =
      try let v' = newvar v in
          tryfind (fun f -> mk_comb(f,v')) [f;fimage;fmap;fcompose;fimage2]
      with Failure _ -> v in
    let specrule th =
      let v = fst(dest_forall(concl th)) in SPEC (newterm v) th in
    let sth = SUBS(CONJUNCTS(MATCH_MP cth lin)) ath in
    let fth = SUBS[SYM(MATCH_MP LINEAR_0 lin)] (repeat specrule sth) in
    let thps = CONJUNCTS(MATCH_MP oth (ASSUME bod)) in
    let th5 = LINEAR_INVARIANTS f thps in
    let th6 = GEN_REWRITE_RULE REDEPTH_CONV [th5] fth in
    let th7 = PROVE_HYP eth (SIMPLE_CHOOSE f th6) in
    GENL (map newvar (fst(strip_forall(concl ath)))) th7;;

(* ------------------------------------------------------------------------- *)
(* Transfer theorems automatically between same-dimension spaces.            *)
(* Given dth = A |- dimindex(:M) = dimindex(:N)                              *)
(* and a theorem th involving variables of type real^N                       *)
(* returns a corresponding theorem mapped to type real^M with assumptions A. *)
(* ------------------------------------------------------------------------- *)

let GEOM_EQUAL_DIMENSION_RULE =
  let bth = prove
   (`dimindex(:M) = dimindex(:N)
     ==> ?f:real^M->real^N.
             (linear f /\ (!y. ?x. f x = y)) /\
             (!x. norm(f x) = norm x)`,
    REWRITE_TAC[SET_RULE `(!y. ?x. f x = y) <=> IMAGE f UNIV = UNIV`] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC ISOMETRY_UNIV_SUBSPACE THEN
    REWRITE_TAC[SUBSPACE_UNIV; DIM_UNIV] THEN FIRST_ASSUM ACCEPT_TAC)
  and pth = prove
   (`!f:real^M->real^N.
        linear f /\ (!y. ?x. f x = y)
         ==> (vec 0 = f(vec 0) /\
              {} = IMAGE f {} /\
              {} = IMAGE (IMAGE f) {} /\
              (:real^N) = IMAGE f (:real^M) /\
              (:real^N->bool) = IMAGE (IMAGE f) (:real^M->bool) /\
              [] = MAP f []) /\
             ((!P. (!x. P x) <=> (!x. P (f x))) /\
              (!P. (?x. P x) <=> (?x. P (f x))) /\
              (!Q. (!s. Q s) <=> (!s. Q (IMAGE f s))) /\
              (!Q. (?s. Q s) <=> (?s. Q (IMAGE f s))) /\
              (!Q. (!s. Q s) <=> (!s. Q (IMAGE (IMAGE f) s))) /\
              (!Q. (?s. Q s) <=> (?s. Q (IMAGE (IMAGE f) s))) /\
              (!P. (!g:real^1->real^N. P g) <=> (!g. P (f o g))) /\
              (!P. (?g:real^1->real^N. P g) <=> (?g. P (f o g))) /\
              (!P. (!g:num->real^N. P g) <=> (!g. P (f o g))) /\
              (!P. (?g:num->real^N. P g) <=> (?g. P (f o g))) /\
              (!Q. (!l. Q l) <=> (!l. Q(MAP f l))) /\
              (!Q. (?l. Q l) <=> (?l. Q(MAP f l)))) /\
             ((!P. {x | P x} = IMAGE f {x | P(f x)}) /\
              (!Q. {s | Q s} = IMAGE (IMAGE f) {s | Q(IMAGE f s)}) /\
              (!R. {l | R l} = IMAGE (MAP f) {l | R(MAP f l)}))`,
    GEN_TAC THEN
    SIMP_TAC[SET_RULE `UNIV = IMAGE f UNIV <=> (!y. ?x. f x = y)`;
             SURJECTIVE_IMAGE] THEN
    MATCH_MP_TAC MONO_AND THEN
    REWRITE_TAC[QUANTIFY_SURJECTION_HIGHER_THM] THEN
    REWRITE_TAC[IMAGE_CLAUSES; MAP] THEN MESON_TAC[LINEAR_0]) in
  fun dth th ->
    let eth = EXISTS_GENVAR_RULE (MATCH_MP bth dth) in
    let f,bod = dest_exists(concl eth) in
    let lsth,neth = CONJ_PAIR(ASSUME bod) in
    let cth,qth = CONJ_PAIR(MATCH_MP pth lsth) in
    let th1 = CONV_RULE
     (EXPAND_QUANTS_CONV qth THENC SUBS_CONV(CONJUNCTS cth)) th in
    let ith = LINEAR_INVARIANTS f (neth::CONJUNCTS lsth) in
    let th2 = GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV) [BETA_THM;ith] th1 in
    let th3 = GEN f (DISCH bod th2) in
    MP (CONV_RULE (REWR_CONV LEFT_FORALL_IMP_THM) th3) eth;;
