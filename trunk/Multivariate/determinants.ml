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

let TRACE_MUL_SYM = prove
 (`!A B:real^N^N. trace(A ** B) = trace(B ** A)`,
  REPEAT GEN_TAC THEN SIMP_TAC[trace; matrix_mul; LAMBDA_BETA] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[REAL_MUL_SYM]);;

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

let DET_DIAGONAL = prove
 (`!A:real^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ ~(i = j) ==> A$i$j = &0)
        ==> det(A) = product(1..dimindex(:N)) (\i. A$i$i)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DET_LOWERTRIANGULAR THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LT_REFL]);;

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

let HOMOGENEOUS_LINEAR_EQUATIONS_DET = prove
 (`!A:real^N^N. (?x. ~(x = vec 0) /\ A ** x = vec 0) <=> det A = &0`,
  GEN_TAC THEN
  REWRITE_TAC[MATRIX_NONFULL_LINEAR_EQUATIONS_EQ; DET_EQ_0_RANK] THEN
  MATCH_MP_TAC(ARITH_RULE `r <= MIN N N ==> (~(r = N) <=> r < N)`) THEN
  REWRITE_TAC[RANK_BOUND]);;

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

let DET_1 = prove
 (`!A:real^1^1. det A = A$1$1`,
  REWRITE_TAC[det; DIMINDEX_1; PERMUTES_SING; NUMSEG_SING] THEN
  REWRITE_TAC[SUM_SING; SET_RULE `{x | x = a} = {a}`; PRODUCT_SING] THEN
  REWRITE_TAC[SIGN_I; I_THM] THEN REAL_ARITH_TAC);;

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

(* ------------------------------------------------------------------------- *)
(* Grassmann-Plucker relations for n = 2 and n = 3.                          *)
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
(* Orthogonality of a transformation and matrix.                             *)
(* ------------------------------------------------------------------------- *)

let orthogonal_transformation = new_definition
 `orthogonal_transformation(f:real^N->real^N) <=>
        linear f /\ !v w. f(v) dot f(w) = v dot w`;;

let ORTHOGONAL_TRANSFORMATION = prove
 (`!f. orthogonal_transformation f <=> linear f /\ !v. norm(f v) = norm(v)`,
  GEN_TAC THEN REWRITE_TAC[orthogonal_transformation] THEN EQ_TAC THENL
   [MESON_TAC[vector_norm]; SIMP_TAC[DOT_NORM] THEN MESON_TAC[LINEAR_ADD]]);;

let orthogonal_matrix = new_definition
 `orthogonal_matrix(Q:real^N^N) <=>
      transp(Q) ** Q = mat 1 /\ Q ** transp(Q) = mat 1`;;

let ORTHOGONAL_MATRIX = prove
 (`orthogonal_matrix(Q:real^N^N) <=> transp(Q) ** Q = mat 1`,
  MESON_TAC[MATRIX_LEFT_RIGHT_INVERSE; orthogonal_matrix]);;

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

let DET_ORTHOGONAL_MATRIX = prove
 (`!Q. orthogonal_matrix Q ==> det(Q) = &1 \/ det(Q) = -- &1`,
  GEN_TAC THEN REWRITE_TAC[REAL_RING `x = &1 \/ x = -- &1 <=> x * x = &1`] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM DET_TRANSP] THEN
  SIMP_TAC[GSYM DET_MUL; orthogonal_matrix; DET_I]);;

let ORTHOGONAL_MATRIX_TRANSP = prove
 (`!A:real^N^N. orthogonal_matrix(transp A) <=> orthogonal_matrix A`,
  REWRITE_TAC[orthogonal_matrix; TRANSP_TRANSP; CONJ_ACI]);;

let MATRIX_MUL_LTRANSP_DOT_COLUMN = prove
 (`!A:real^N^N. transp A ** A = (lambda i j. (column i A) dot (column j A))`,
  SIMP_TAC[matrix_mul; CART_EQ; LAMBDA_BETA; transp; dot; column]);;

let MATRIX_MUL_RTRANSP_DOT_ROW = prove
 (`!A:real^N^N. A ** transp A = (lambda i j. (row i A) dot (row j A))`,
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
    DISCH_TAC THEN ASM_REWRITE_TAC[DOT_NORM_NEG; GSYM dist] THEN
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

let ORTHOGONAL_TRANSFORMATION_ID = prove
 (`orthogonal_transformation(\x. x)`,
  REWRITE_TAC[orthogonal_transformation; LINEAR_ID]);;

let ORTHOGONAL_TRANSFORMATION_I = prove
 (`orthogonal_transformation I`,
  REWRITE_TAC[I_DEF; ORTHOGONAL_TRANSFORMATION_ID]);;

(* ------------------------------------------------------------------------- *)
(* We can find an orthogonal matrix taking any unit vector to any other.     *)
(* ------------------------------------------------------------------------- *)

let FINITE_INDEX_NUMSEG_SPECIAL = prove
 (`!s a:A.
        FINITE s /\ a IN s
        ==> ?f. (!i j. i IN 1..CARD s /\ j IN 1..CARD s /\ f i = f j
                       ==> i = j) /\
                s = IMAGE f (1..CARD s) /\
                f 1 = a`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?k. k IN 1..CARD(s:A->bool) /\ (a:A) = f k`
  STRIP_ASSUME_TAC THENL[ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(f:num->A) o swap(1,k)` THEN
  SUBGOAL_THEN `1 IN 1..CARD(s:A->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG; LE_REFL; ARITH_RULE `1 <= x <=> ~(x = 0)`] THEN
    ASM_SIMP_TAC[CARD_EQ_0; ARITH_EQ] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM; swap] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_THEN `s = IMAGE (f:num->A) (1..CARD(s:A->bool))`
   (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM] THEN
  X_GEN_TAC `b:A` THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `swap(1,k) i` THEN
  REWRITE_TAC[swap] THEN ASM_MESON_TAC[swap]);;

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
(* Rotation, reflection, rotoinversion.                                      *)
(* ------------------------------------------------------------------------- *)

let rotation_matrix = new_definition
 `rotation_matrix Q <=> orthogonal_matrix Q /\ det(Q) = &1`;;

let rotoinversion_matrix = new_definition
 `rotoinversion_matrix Q <=> orthogonal_matrix Q /\ det(Q) = -- &1`;;

let ORTHOGONAL_ROTATION_OR_ROTOINVERSION = prove
 (`!Q. orthogonal_matrix Q <=> rotation_matrix Q \/ rotoinversion_matrix Q`,
  MESON_TAC[rotation_matrix; rotoinversion_matrix; DET_ORTHOGONAL_MATRIX]);;

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
    let th1 = CONV_RULE (EXPAND_QUANTS_CONV qth) th in
    let ith = LINEAR_INVARIANTS f (neth::CONJUNCTS lsth) in
    let th2 = GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV) [BETA_THM;ith] th1 in
    PROVE_HYP eth (SIMPLE_CHOOSE f th2);;
