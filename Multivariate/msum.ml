(* ========================================================================= *)
(* Sums of matrices over an indexing set.                                    *)
(*                                                                           *)
(* (c) Copyright, Andrea Gabrielli, Marco Maggesi 2016-2017                  *)
(* ========================================================================= *)

needs "Multivariate/vectors.ml";;

let () = prioritize_vector();;
         prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Matrix norm (vector norm of "flattened" form).                            *)
(* ------------------------------------------------------------------------- *)

overload_interface("norm",`matrix_norm:real^M^N->real`);;

let matrix_norm = new_definition
  `matrix_norm (m:real^M^N) = norm(vectorize m)`;;

(* ------------------------------------------------------------------------- *)
(* Sums over matrices.                                                       *)
(* ------------------------------------------------------------------------- *)

let NEUTRAL_MATRIX_ADD = prove
 (`neutral(+) = mat 0:real^M^N`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  REWRITE_TAC[MATRIX_ARITH `x + y = y <=> x = mat 0:real^M^N`;
              MATRIX_ARITH `x + y = x <=> y = mat 0:real^M^N`]);;

let MONOIDAL_MATRIX_ADD = prove
 (`monoidal((+):real^M^N->real^M^N->real^M^N)`,
  REWRITE_TAC[monoidal; NEUTRAL_MATRIX_ADD] THEN
  REPEAT CONJ_TAC THEN MATRIX_ARITH_TAC);;

let msum = new_definition
  `msum s (f:A->real^M^N):real^M^N = (lambda i j. sum s (\x. f x$i$j))`;;

let MSUM_COMPONENT = prove
 (`!s (f:A->real^M^N) i j. msum s f$i$j = sum s (\x. f x$i$j)`,
  REPEAT GEN_TAC THEN C SUBGOAL_THEN (CONJUNCTS_THEN CHOOSE_TAC)
    `(?h. 1 <= h /\ h <= dimindex(:N) /\ !z:real^M^N. z$i = z$h) /\
     (?k. 1 <= k /\ k <= dimindex(:M) /\ !z:real^M. z$j = z$k)` THENL
  [REWRITE_TAC[FINITE_INDEX_INRANGE];
   ASM_SIMP_TAC[msum; LAMBDA_BETA]]);;

let MSUM_ROW = prove
 (`!s f:A->real^M^N i. msum s f$i = vsum s (\x. f x$i)`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; VSUM_COMPONENT]);;

let MSUM_CLAUSES = prove
 (`(!f:A->real^M^N. msum {} f = mat 0) /\
   (!x:A f s. FINITE s
            ==> msum (x INSERT s) f : real^M^N=
                if x IN s then msum s f else f(x) + msum s f)`,
  SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MATRIX_ADD_COMPONENT; SUM_CLAUSES] THEN
  SIMP_TAC[MAT_0_COMPONENT] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA; MATRIX_ADD_COMPONENT]);;

let MSUM = prove
 (`!f:A->real^M^N s. FINITE s ==> msum s f = iterate (+) s f`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[MSUM_CLAUSES; ITERATE_CLAUSES; MONOIDAL_MATRIX_ADD] THEN
  REWRITE_TAC[NEUTRAL_MATRIX_ADD]);;

let MSUM_EQ_0 = prove
 (`!f:A->real^M^N s. (!x. x IN s ==> (f(x) = mat 0)) ==> (msum s f = mat 0)`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MAT_0_COMPONENT] THEN
  SIMP_TAC[SUM_EQ_0]);;

let MSUM_0 = prove
 (`msum s (\x:A. mat 0) = mat 0:real^M^N`,
  SIMP_TAC[MSUM_EQ_0]);;

let MSUM_LMUL = prove
 (`!f:A->real^M^N c s.  msum s (\x. c %% f(x)) = c %% msum s f`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MATRIX_CMUL_COMPONENT; SUM_LMUL]);;

let MSUM_RMUL = prove
 (`!c:A->real s v:real^M^N. msum s (\x. c x %% v) = (sum s c) %% v`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MATRIX_CMUL_COMPONENT; SUM_RMUL]);;

let MSUM_ADD = prove
 (`!f g:A->real^M^N s.
     FINITE s ==> (msum s (\x. f x + g x) = msum s f + msum s g)`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MATRIX_ADD_COMPONENT] THEN
  SIMP_TAC[SUM_ADD]);;

let MSUM_SUB = prove
 (`!f g:A->real^M^N s.
     FINITE s ==> (msum s (\x. f x - g x) = msum s f - msum s g)`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MATRIX_SUB_COMPONENT] THEN
  SIMP_TAC[SUM_SUB]);;

let MSUM_CONST = prove
 (`!c:real^M^N s. FINITE s ==> (msum s (\n:A. c) = &(CARD s) %% c)`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
  SIMP_TAC[SUM_CONST]);;

let MSUM_IMAGE = prove
 (`!f:A->B g:B->real^M^N s.
     FINITE s /\ (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
     ==> (msum (IMAGE f s) g = msum s (g o f))`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (fun th -> REWRITE_TAC[MATCH_MP SUM_IMAGE th; o_DEF]));;

let MSUM_UNION = prove
 (`!f:A->real^M^N s t.
     FINITE s /\ FINITE t /\ DISJOINT s t
     ==> (msum (s UNION t) f = msum s f + msum t f)`,
  REWRITE_TAC[CART_EQ_FULL; MATRIX_ADD_COMPONENT; MSUM_COMPONENT] THEN
  SIMP_TAC[SUM_UNION]);;

let MSUM_DIFF = prove
 (`!f:A->real^M^N s t. FINITE s /\ t SUBSET s
           ==> (msum (s DIFF t) f = msum s f - msum t f)`,
  REWRITE_TAC[CART_EQ_FULL; MATRIX_SUB_COMPONENT; MSUM_COMPONENT] THEN
  SIMP_TAC[SUM_DIFF]);;

let MSUM_DELETE = prove
 (`!f:A->real^M^N s a.
     FINITE s /\ a IN s
     ==> msum (s DELETE a) f = msum s f - f a`,
  REWRITE_TAC[CART_EQ_FULL; MATRIX_SUB_COMPONENT; MSUM_COMPONENT] THEN
  SIMP_TAC[SUM_DELETE]);;

let MSUM_INCL_EXCL = prove
 (`!s t (f:A->real^M^N).
     FINITE s /\ FINITE t
     ==> msum s f + msum t f = msum (s UNION t) f + msum (s INTER t) f`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MATRIX_ADD_COMPONENT] THEN
  SIMP_TAC[SUM_INCL_EXCL]);;

let MSUM_NEG = prove
 (`!f:A->real^M^N s. msum s (\x. --f x) = --msum s f`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MATRIX_NEG_COMPONENT; SUM_NEG]);;

let MSUM_EQ = prove
 (`!f g:A->real^M^N s. (!x. x IN s ==> (f x = g x)) ==> (msum s f = msum s g)`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT] THEN SIMP_TAC[SUM_EQ]);;

let MSUM_SUPERSET = prove
 (`!f:A->real^M^N u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = mat 0))
        ==> (msum v f = msum u f)`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MAT_0_COMPONENT] THEN
  SIMP_TAC[SUM_SUPERSET]);;

let MSUM_SUPPORT = prove
 (`!f:A->real^M^N s. msum {x | x IN s /\ ~(f x = mat 0)} f = msum s f`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MSUM_SUPERSET THEN
  SET_TAC[]);;

let MSUM_UNIV = prove
 (`!f:A->real^M^N s.
     support (+) f (:A) SUBSET s ==> msum s f = msum (:A) f`,
  REWRITE_TAC[support; NEUTRAL_MATRIX_ADD] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM MSUM_SUPPORT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let MSUM_EQ_SUPERSET = prove
 (`!(f:A->real^M^N) s t.
        FINITE t /\ t SUBSET s /\
        (!x. x IN t ==> (f x = g x)) /\
        (!x. x IN s /\ ~(x IN t) ==> f(x) = mat 0)
        ==> msum s f = msum t g`,
  MESON_TAC[MSUM_SUPERSET; MSUM_EQ]);;

let MSUM_UNION_RZERO = prove
 (`!f:A->real^M^N u v.
        (!x. x IN v /\ ~(x IN u) ==> (f(x) = mat 0))
        ==> (msum (u UNION v) f = msum u f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MSUM_SUPERSET THEN ASM SET_TAC[]);;

let MSUM_UNION_LZERO = prove
 (`!f:A->real^M^N u v.
        (!x. x IN u /\ ~(x IN v) ==> (f(x) = mat 0))
        ==> (msum (u UNION v) f = msum v f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MSUM_SUPERSET THEN ASM SET_TAC[]);;

let MSUM_RESTRICT = prove
 (`!f:A->real^M^N s. msum s (\x. if x IN s then f(x) else mat 0) = msum s f`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MSUM_EQ THEN SIMP_TAC[]);;

let MSUM_RESTRICT_SET = prove
 (`!P s f:A->real^M^N. msum {x | x IN s /\ P x} f =
                       msum s (\x. if P x then f x else mat 0)`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MAT_0_COMPONENT;
              COND_COMPONENT] THEN
  SIMP_TAC[SUM_RESTRICT_SET; COND_COMPONENT]);;

let MSUM_CASES = prove
 (`!s P f g. FINITE s
             ==> msum s (\x:A. if P x then (f x):real^M^N else g x) =
                 msum {x | x IN s /\ P x} f + msum {x | x IN s /\ ~P x} g`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MATRIX_ADD_COMPONENT;
              COND_COMPONENT] THEN
  SIMP_TAC[SUM_CASES]);;

let MSUM_SING = prove
 (`!f:A->real^M^N x. msum {x} f = f(x)`,
  SIMP_TAC[MSUM_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; MATRIX_ADD_RID]);;

let VECTORIZE_MSUM = prove
 (`!s f:A->real^M^N. vectorize (msum s f) = vsum s (\x. vectorize (f x))`,
  SIMP_TAC[CART_EQ; VECTORIZE_COMPONENT; DIMINDEX_FINITE_PROD;
           VSUM_COMPONENT; MSUM_COMPONENT]);;

let MSUM_NORM = prove
 (`!s f:A->real^M^N. FINITE s ==> norm(msum s f) <= sum s (\x. norm(f x))`,
  REWRITE_TAC[matrix_norm; VECTORIZE_MSUM] THEN SIMP_TAC[VSUM_NORM]);;

let MSUM_NORM_LE = prove
 (`!s f:A->real^M^N g. FINITE s /\ (!x. x IN s ==> norm(f x) <= g(x))
                       ==> norm(msum s f) <= sum s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s (\x:A. norm(f x:real^M^N))` THEN
  ASM_SIMP_TAC[MSUM_NORM; SUM_LE]);;

let MSUM_NORM_TRIANGLE = prove
 (`!s f:A->real^M^N b. FINITE s /\ sum s (\a. norm(f a)) <= b
                       ==> norm(msum s f) <= b`,
  MESON_TAC[MSUM_NORM; REAL_LE_TRANS]);;

let MSUM_NORM_BOUND = prove
 (`!s f:A->real^M^N b. FINITE s /\ (!x. x IN s ==> norm(f(x)) <= b)
                       ==> norm(msum s f) <= &(CARD s) * b`,
  SIMP_TAC[GSYM SUM_CONST; MSUM_NORM_LE]);;

let MSUM_CLAUSES_NUMSEG = prove
 (`(!m. msum(m..0) f = if m = 0 then f(0) else mat 0:real^M^N) /\
   (!m n. msum(m..SUC n) f = if m <= SUC n then msum(m..n) f + f(SUC n)
                             else msum(m..n) f)`,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[MSUM_SING; MSUM_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`; MATRIX_ADD_AC]);;

let MSUM_CLAUSES_RIGHT = prove
 (`!f m n. 0 < n /\ m <= n ==> msum(m..n) f = msum(m..n-1) f + (f n):real^M^N`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC[LT_REFL; MSUM_CLAUSES_NUMSEG; SUC_SUB1]);;

let MSUM_CMUL_NUMSEG = prove
 (`!f c m n. msum (m..n) (\x. c %% f x) = c %% msum (m..n) f:real^M^N`,
  SIMP_TAC[MSUM_LMUL; FINITE_NUMSEG]);;

let MSUM_EQ_NUMSEG = prove
 (`!f g m n.
         (!x. m <= x /\ x <= n ==> (f x = g x:real^M^N))
         ==> (msum(m .. n) f = msum(m .. n) g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MSUM_EQ THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG]);;

let MSUM_IMAGE_GEN = prove
 (`!f:A->B (g:A->real^M^N) s.
        FINITE s
        ==> (msum s g =
             msum (IMAGE f s) (\y. msum {x | x IN s /\ (f(x) = y)} g))`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT] THEN SIMP_TAC[SUM_IMAGE_GEN]);;

let MSUM_GROUP = prove
 (`!f:A->B (g:A->real^M^N) s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> msum t (\y. msum {x | x IN s /\ f(x) = y} g) = msum s g`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT] THEN SIMP_TAC[SUM_GROUP]);;

let MSUM_GROUP_RELATION = prove
 (`!R:A->B->bool (g:A->real^M^N) s t.
         FINITE s /\
         (!x. x IN s ==> ?!y. y IN t /\ R x y)
         ==> msum t (\y. msum {x | x IN s /\ R x y} g) = msum s g`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT] THEN
  SIMP_TAC[SUM_GROUP_RELATION]);;

let MSUM_VMUL = prove
 (`!f v:real^M^N s. (sum s f) %% v = msum s (\x:A. f(x) %% v)`,
  REWRITE_TAC[MSUM_RMUL]);;

let MSUM_DELTA = prove
 (`!s a. msum s (\x:A. if x = a then b else mat 0:real^M^N) =
         if a IN s then b else mat 0`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; COND_COMPONENT] THEN
  SIMP_TAC[MAT_0_COMPONENT; SUM_DELTA]);;

let MSUM_ADD_NUMSEG = prove
 (`!f g m n.
     msum(m..n) (\i. f i + g i) = msum(m..n) f + msum(m..n) g:real^M^N`,
  SIMP_TAC[MSUM_ADD; FINITE_NUMSEG]);;

let MSUM_SUB_NUMSEG = prove
 (`!f g m n.
     msum(m..n) (\i. f i - g i) = msum(m..n) f - msum(m..n) g:real^M^N`,
  SIMP_TAC[MSUM_SUB; FINITE_NUMSEG]);;

let MSUM_ADD_SPLIT = prove
 (`!f m n p.
       m <= n + 1
       ==> msum(m..n + p) f = msum(m..n) f + msum(n + 1..n + p) f:real^M^N`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MATRIX_ADD_COMPONENT] THEN
  SIMP_TAC[SUM_ADD_SPLIT]);;

let MSUM_MSUM_PRODUCT = prove
 (`!s:A->bool t:A->B->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> msum s (\i. msum (t i) (x i)) =
            msum {i,j | i IN s /\ j IN t i} (\(i,j). x i j):real^M^N`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; COND_COMPONENT] THEN
  SIMP_TAC[SUM_SUM_PRODUCT] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let MSUM_IMAGE_NONZERO = prove
 (`!d:B->real^M^N i:A->B s.
     FINITE s /\
     (!x y. x IN s /\ y IN s /\ ~(x = y) /\ i x = i y ==> d(i x) = mat 0)
     ==> msum (IMAGE i s) d = msum s (d o i):real^M^N`,
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IMAGE_CLAUSES; MSUM_CLAUSES; FINITE_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `msum s ((d:B->real^M^N) o (i:A->B)) = msum (IMAGE i s) d`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[o_THM] THEN
  REWRITE_TAC[MATRIX_ARITH `a = x + a <=> x = mat 0:real^M^N`] THEN
  ASM_MESON_TAC[IN_IMAGE]);;

let MSUM_UNION_NONZERO = prove
 (`!f:A->real^M^N s t.
     FINITE s /\ FINITE t /\ (!x. x IN s INTER t ==> f(x) = mat 0)
     ==> msum (s UNION t) f = msum s f + msum t f`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MATRIX_ADD_COMPONENT;
              MAT_0_COMPONENT] THEN
  SIMP_TAC[SUM_UNION_NONZERO]);;

let MSUM_UNIONS_NONZERO = prove
 (`!f:A->real^M^N s.
     FINITE s /\ (!t. t IN s ==> FINITE t) /\
     (!t1 t2 x. t1 IN s /\ t2 IN s /\ ~(t1 = t2) /\ x IN t1 /\ x IN t2
                ==> f x = mat 0)
     ==> msum (UNIONS s) f = msum s (\t. msum t f)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; MSUM_CLAUSES; IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`t:A->bool`; `s:(A->bool)->bool`] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN ASM_SIMP_TAC[MSUM_CLAUSES] THEN
  ANTS_TAC THENL  [ASM_MESON_TAC[]; DISCH_THEN(SUBST_ALL_TAC o SYM)] THEN
  STRIP_TAC THEN MATCH_MP_TAC MSUM_UNION_NONZERO THEN
  ASM_SIMP_TAC[FINITE_UNIONS; IN_INTER; IN_UNIONS] THEN ASM_MESON_TAC[]);;

let MSUM_CLAUSES_LEFT = prove
 (`!f m n. m <= n ==> msum(m..n) f = f m + msum(m + 1..n) f:real^M^N`,
  SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MATRIX_ADD_COMPONENT] THEN
  SIMP_TAC[VEC_COMPONENT; SUM_CLAUSES_LEFT]);;

let MSUM_DIFFS = prove
 (`!m n. msum(m..n) (\k. f(k) - f(k + 1)) =
          if m <= n then f(m) - f(n + 1) else mat 0:real^M^N`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[MSUM_CLAUSES_NUMSEG; LE] THEN
  ASM_CASES_TAC `m = SUC n` THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`; MATRIX_ADD_LID] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ADD1] THEN MATRIX_ARITH_TAC);;

let MSUM_DIFFS_ALT = prove
 (`!m n. msum(m..n) (\k. f(k + 1) - f(k)) =
         if m <= n then f(n + 1) - f(m) else mat 0:real^M^N`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM MATRIX_NEG_SUB] THEN
  SIMP_TAC[MSUM_NEG; MSUM_DIFFS] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MATRIX_NEG_SUB; MATRIX_NEG_0]);;

let MSUM_DELETE_CASES = prove
 (`!x f:A->real^M^N s.
        FINITE s
        ==> msum(s DELETE x) f = if x IN s then msum s f - f x else msum s f`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[SET_RULE `~(x:A IN s) ==> s DELETE x = s`] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [MATCH_MP (SET_RULE `x:A IN s ==> s = x INSERT (s DELETE x)`) th]) THEN
  ASM_SIMP_TAC[MSUM_CLAUSES; FINITE_DELETE; IN_DELETE] THEN MATRIX_ARITH_TAC);;

let MSUM_EQ_GENERAL = prove
  (`!s:A->bool t:B->bool (f:A->real^M^N) g h.
        (!y. y IN t ==> ?!x. x IN s /\ h x = y) /\
        (!x. x IN s ==> h x IN t /\ g(h x) = f x)
        ==> msum s f = msum t g`,
   SIMP_TAC[msum; CART_EQ; LAMBDA_BETA] THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_GENERAL THEN
   EXISTS_TAC `h:A->B` THEN ASM_MESON_TAC[]);;

let MSUM_EQ_GENERAL_INVERSES = prove
 (`!s t (f:A->real^M^N) (g:B->real^M^N) h k.
        (!y. y IN t ==> k y IN s /\ h (k y) = y) /\
        (!x. x IN s ==> h x IN t /\ k (h x) = x /\ g (h x) = f x)
        ==> msum s f = msum t g`,
  SIMP_TAC[msum; CART_EQ; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
  MAP_EVERY EXISTS_TAC [`h:A->B`; `k:B->A`] THEN ASM_MESON_TAC[]);;

let MSUM_OFFSET = prove
 (`!p f m n. msum(m + p..n + p) f = msum(m..n) (\i. f (i + p)):real^M^N`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT] THEN SIMP_TAC[SUM_OFFSET]);;

let MSUM_OFFSET_0 = prove
 (`!f m n. m <= n ==> msum(m..n) f = msum(0..n - m) (\i. f (i + m)):real^M^N`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT] THEN SIMP_TAC[SUM_OFFSET_0]);;

let MSUM_TRIV_NUMSEG = prove
 (`!f m n. n < m ==> msum(m..n) f = mat 0:real^M^N`,
  SIMP_TAC[GSYM NUMSEG_EMPTY; MSUM_CLAUSES]);;

let MSUM_CONST_NUMSEG = prove
 (`!c m n. msum(m..n) (\n. c) = &((n + 1) - m) %% c:real^M^N`,
  SIMP_TAC[MSUM_CONST; FINITE_NUMSEG; CARD_NUMSEG]);;

let MSUM_SUC = prove
 (`!f m n. msum (SUC n..SUC m) f = msum (n..m) (f o SUC):real^M^N`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `SUC n..SUC m = IMAGE SUC (n..m)` SUBST1_TAC THENL
   [REWRITE_TAC [ADD1; NUMSEG_OFFSET_IMAGE] THEN
    REWRITE_TAC [ONE; ADD_SUC; ADD_0; ETA_AX];
    SIMP_TAC [MSUM_IMAGE; FINITE_NUMSEG; SUC_INJ]]);;

let MSUM_BIJECTION = prove
 (`!f:A->real^M^N p s:A->bool.
                (!x. x IN s ==> p(x) IN s) /\
                (!y. y IN s ==> ?!x. x IN s /\ p(x) = y)
                ==> msum s f = msum s (f o p)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MSUM_EQ_GENERAL THEN EXISTS_TAC `p:A->A` THEN
  ASM_REWRITE_TAC[o_THM]);;

let MSUM_PARTIAL_SUC = prove
 (`!f g:num->real^M^N m n.
        msum (m..n) (\k. f(k) %% (g(k + 1) - g(k))) =
            if m <= n then f(n + 1) %% g(n + 1) - f(m) %% g(m) -
                           msum (m..n) (\k. (f(k + 1) - f(k)) %% g(k + 1))
            else mat 0`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[MSUM_TRIV_NUMSEG; GSYM NOT_LE] THEN
  ASM_REWRITE_TAC[MSUM_CLAUSES_NUMSEG] THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[ARITH] THENL
     [MATRIX_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE]) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_SIMP_TAC[GSYM NOT_LT; MSUM_TRIV_NUMSEG; ARITH_RULE `n < SUC n`] THEN
  ASM_SIMP_TAC[GSYM ADD1; ADD_CLAUSES] THEN MATRIX_ARITH_TAC);;

let MSUM_PARTIAL_PRE = prove
 (`!f g:num->real^M^N m n.
        msum (m..n) (\k. f(k) %% (g(k) - g(k - 1))) =
            if m <= n then f(n + 1) %% g(n) - f(m) %% g(m - 1) -
                           msum (m..n) (\k. (f(k + 1) - f(k)) %% g(k))
            else mat 0`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:num->real`; `\k. (g:num->real^M^N)(k - 1)`;
                 `m:num`; `n:num`] MSUM_PARTIAL_SUC) THEN
  REWRITE_TAC[ADD_SUB] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let MSUM_COMBINE_L = prove
 (`!f m n p.
        0 < n /\ m <= n /\ n <= p + 1
        ==> msum(m..n - 1) f + msum(n..p) f = msum(m..p) f:real^M^N`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MATRIX_ADD_COMPONENT] THEN
  SIMP_TAC[SUM_COMBINE_L]);;

let MSUM_COMBINE_R = prove
 (`!f m n p.
        m <= n + 1 /\ n <= p
        ==> msum(m..n) f + msum(n + 1..p) f = msum(m..p) f:real^M^N`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MATRIX_ADD_COMPONENT] THEN
  SIMP_TAC[SUM_COMBINE_R]);;

let MSUM_INJECTION = prove
 (`!f:A->real^M^N p:A->A s.
     FINITE s /\
     (!x. x IN s ==> p x IN s) /\
     (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y)
     ==> msum s (f o p) = msum s f`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SUM_INJECTION) THEN
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; o_DEF] THEN SIMP_TAC[]);;

let MSUM_SWAP = prove
 (`!f:A->B->real^M^N s t.
     FINITE s /\ FINITE t
     ==> msum s (\i. msum t (f i)) = msum t (\j. msum s (\i. f i j))`,
   REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT] THEN REPEAT STRIP_TAC THEN
   W(MP_TAC o PART_MATCH (lhs o rand) SUM_SWAP o lhs o snd) THEN
   ASM_REWRITE_TAC[]);;

let MSUM_SWAP_NUMSEG = prove
  (`!a b c d f.
         msum (a..b) (\i. msum (c..d) (f i)) =
         msum (c..d) (\j. msum (a..b) (\i. f i j)):real^M^N`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MSUM_SWAP THEN REWRITE_TAC[FINITE_NUMSEG]);;

let MSUM_ADD_GEN = prove
 (`!f g:A->real^M^N s.
       FINITE {x | x IN s /\ ~(f x = mat 0)} /\
       FINITE {x | x IN s /\ ~(g x = mat 0)}
       ==> msum s (\x. f x + g x) = msum s f + msum s g`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MATRIX_ADD_COMPONENT] THEN
  SIMP_TAC[CART_EQ; msum; LAMBDA_BETA; MATRIX_ADD_COMPONENT] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_ADD_GEN THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_AND THEN
  CONJ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[MAT_0_COMPONENT]);;

let MSUM_CASES_1 = prove
 (`!s a:A. FINITE s /\ a IN s
           ==> msum s (\x. if x = a then y else f(x)) =
               msum s f + (y - f a):real^M^N`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MSUM_CASES] THEN
  ASM_SIMP_TAC[GSYM DELETE; MSUM_DELETE] THEN
  ASM_SIMP_TAC[SET_RULE `a:A IN s ==> {x | x IN s /\ x = a} = {a}`] THEN
  REWRITE_TAC[MSUM_SING] THEN MATRIX_ARITH_TAC);;

let MSUM_SING_NUMSEG = prove
 (`msum(n..n) f = f n:real^M^N`,
  REWRITE_TAC[NUMSEG_SING; MSUM_SING]);;

let MSUM_1 = prove
 (`msum(1..1) f = f(1):real^M^N`,
  REWRITE_TAC[MSUM_SING_NUMSEG]);;

let MSUM_2 = prove
 (`!t. msum(1..2) t = t(1) + t(2):real^M^N`,
  REWRITE_TAC[num_CONV `2`; MSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[MSUM_SING_NUMSEG; ARITH; REAL_ADD_ASSOC]);;

let MSUM_3 = prove
 (`!t. msum(1..3) t = t(1) + t(2) + t(3):real^M^N`,
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; MSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[MSUM_SING_NUMSEG; ARITH; MATRIX_ADD_ASSOC]);;

let MSUM_4 = prove
 (`!t. msum(1..4) t = t(1) + t(2) + t(3) + t(4):real^M^N`,
  SIMP_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`; MSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[MSUM_SING_NUMSEG; ARITH; MATRIX_ADD_ASSOC]);;

let MSUM_PAIR = prove
 (`!f:num->real^M^N m n.
        msum(2*m..2*n+1) f = msum(m..n) (\i. f(2*i) + f(2*i+1))`,
  REWRITE_TAC[CART_EQ_FULL; MSUM_COMPONENT; MATRIX_ADD_COMPONENT; SUM_PAIR]);;

let MSUM_PAIR_0 = prove
 (`!f:num->real^M^N n. msum(0..2*n+1) f = msum(0..n) (\i. f(2*i) + f(2*i+1))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:num->real^M^N`; `0`; `n:num`] MSUM_PAIR) THEN
  ASM_REWRITE_TAC[ARITH]);;

let MSUM_REFLECT = prove
 (`!x m n. msum(m..n) x =
           if n < m then mat 0 else msum(0..n-m) (\i. x(n - i)):real^M^N`,
  REPEAT GEN_TAC THEN SIMP_TAC[MSUM; FINITE_NUMSEG] THEN
  GEN_REWRITE_TAC LAND_CONV [MATCH_MP ITERATE_REFLECT MONOIDAL_MATRIX_ADD] THEN
  REWRITE_TAC[NEUTRAL_MATRIX_ADD]);;
