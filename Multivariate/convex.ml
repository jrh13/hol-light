(* ========================================================================= *)
(* Convex sets, functions and related things.                                *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*                 (c) Copyright, Lars Schewe 2007                           *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

needs "Multivariate/topology.ml";;

(* ------------------------------------------------------------------------- *)
(* Some miscelleneous things that are convenient to prove here.              *)
(* ------------------------------------------------------------------------- *)

let TRANSLATION_GALOIS = prove
 (`!s t a:real^N. s = IMAGE (\x. a + x) t <=> t = IMAGE (\x. --a + x) s`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  REWRITE_TAC[VECTOR_ARITH `--a + a + x:real^N = x`;
              VECTOR_ARITH `a + --a + x:real^N = x`] THEN
  REWRITE_TAC[IMAGE_ID]);;

let TRANSLATION_EQ_IMP = prove
 (`!P:(real^N->bool)->bool.
        (!a s. P(IMAGE (\x. a + x) s) <=> P s) <=>
        (!a s. P s ==> P (IMAGE (\x. a + x) s))`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `s:real^N->bool`] THEN
  EQ_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FIRST_X_ASSUM
   (MP_TAC o SPECL [`--a:real^N`; `IMAGE (\x:real^N. a + x) s`]) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID;
                  VECTOR_ARITH `--a + a + x:real^N = x`]);;

let DIM_HYPERPLANE = prove
 (`!a:real^N. ~(a = vec 0) ==> dim {x | a dot x = &0} = dimindex(:N) - 1`,
  GEOM_BASIS_MULTIPLE_TAC 1 `a:real^N` THEN
  SIMP_TAC[VECTOR_MUL_EQ_0; DE_MORGAN_THM; DOT_LMUL; DOT_BASIS;
           DIMINDEX_GE_1; LE_REFL; REAL_ENTIRE; DIM_SPECIAL_HYPERPLANE]);;

let LOWDIM_EQ_HYPERPLANE = prove
 (`!s. dim s = dimindex(:N) - 1
       ==> ?a:real^N. ~(a = vec 0) /\ span s = {x | a dot x = &0}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` LOWDIM_SUBSET_HYPERPLANE) THEN
  ASM_SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= a ==> a - 1 < a`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `a:real^N` SUBSPACE_HYPERPLANE) THEN
  ONCE_REWRITE_TAC[GSYM SPAN_EQ_SELF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC DIM_EQ_SPAN THEN
  ASM_SIMP_TAC[DIM_HYPERPLANE; LE_REFL] THEN
  ASM_MESON_TAC[SUBSET_TRANS; SPAN_INC]);;

let DIM_EQ_HYPERPLANE = prove
 (`!s. dim s = dimindex(:N) - 1 <=>
       ?a:real^N. ~(a = vec 0) /\ span s = {x | a dot x = &0}`,
  MESON_TAC[DIM_HYPERPLANE; LOWDIM_EQ_HYPERPLANE; DIM_SPAN]);;

(* ------------------------------------------------------------------------- *)
(* Affine set and affine hull.                                               *)
(* ------------------------------------------------------------------------- *)

let affine = new_definition
  `affine s <=> !x y u v. x IN s /\ y IN s /\ (u + v = &1)
                          ==> (u % x + v % y) IN s`;;

let AFFINE_ALT = prove
 (`affine s <=> !x y u. x IN s /\ y IN s ==> ((&1 - u) % x + u % y) IN s`,
  REWRITE_TAC[affine] THEN
  MESON_TAC[REAL_ARITH `(u + v = &1) <=> (u = &1 - v)`]);;

let AFFINE_SCALING = prove
 (`!s c. affine s ==> affine (IMAGE (\x. c % x) s)`,
  REWRITE_TAC[affine; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
   `u % c % x + v % c % y = c % (u % x + v % y)`] THEN
  ASM_MESON_TAC[]);;

let AFFINE_SCALING_EQ = prove
 (`!s c. ~(c = &0) ==> (affine (IMAGE (\x. c % x) s) <=> affine s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[AFFINE_SCALING] THEN
  DISCH_THEN(MP_TAC o SPEC `inv c` o MATCH_MP AFFINE_SCALING) THEN
  ASM_SIMP_TAC[GSYM IMAGE_o; o_DEF; VECTOR_MUL_ASSOC;
               REAL_MUL_LINV; VECTOR_MUL_LID; IMAGE_ID]);;

let AFFINE_NEGATIONS = prove
 (`!s. affine s ==> affine (IMAGE (--) s)`,
  REWRITE_TAC[affine; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
   `u % --x + v % --y = --(u % x + v % y)`] THEN
  ASM_MESON_TAC[]);;

let AFFINE_SUMS = prove
 (`!s t. affine s /\ affine t ==> affine {x + y | x IN s /\ y IN t}`,
  REWRITE_TAC[affine; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
    `u % (a + b) + v % (c + d) = (u % a + v % c) + (u % b + v % d)`] THEN
  ASM_MESON_TAC[]);;

let AFFINE_DIFFERENCES = prove
 (`!s t. affine s /\ affine t ==> affine {x - y | x IN s /\ y IN t}`,
  REWRITE_TAC[affine; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
    `u % (a - b) + v % (c - d) = (u % a + v % c) - (u % b + v % d)`] THEN
  ASM_MESON_TAC[]);;

let AFFINE_TRANSLATION_EQ = prove
 (`!a:real^N s. affine (IMAGE (\x. a + x) s) <=> affine s`,
  REWRITE_TAC[AFFINE_ALT; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE; UNWIND_THM1; VECTOR_ARITH
   `(&1 - u) % (a + x) + u % (a + y) = a + z <=> (&1 - u) % x + u % y = z`]);;

add_translation_invariants [AFFINE_TRANSLATION_EQ];;

let AFFINE_TRANSLATION = prove
 (`!s a:real^N. affine s ==> affine (IMAGE (\x. a + x) s)`,
  REWRITE_TAC[AFFINE_TRANSLATION_EQ]);;

let AFFINE_AFFINITY = prove
 (`!s a:real^N c.
        affine s ==> affine (IMAGE (\x. a + c % x) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. a + c % x) = (\x. a + x) o (\x. c % x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  ASM_SIMP_TAC[IMAGE_o; AFFINE_TRANSLATION; AFFINE_SCALING]);;

let AFFINE_LINEAR_IMAGE = prove
 (`!f s. affine s /\ linear f ==> affine(IMAGE f s)`,
  REWRITE_TAC[affine; FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IN_IMAGE; linear] THEN MESON_TAC[]);;

let AFFINE_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (affine (IMAGE f s) <=> affine s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE AFFINE_LINEAR_IMAGE));;

add_linear_invariants [AFFINE_LINEAR_IMAGE_EQ];;

let AFFINE_EMPTY = prove
 (`affine {}`,
  REWRITE_TAC[affine; NOT_IN_EMPTY]);;

let AFFINE_SING = prove
 (`!x. affine {x}`,
  SIMP_TAC[AFFINE_ALT; IN_SING] THEN
  REWRITE_TAC[GSYM VECTOR_ADD_RDISTRIB] THEN
  REWRITE_TAC[REAL_SUB_ADD; VECTOR_MUL_LID]);;

let AFFINE_UNIV = prove
 (`affine(UNIV:real^N->bool)`,
  REWRITE_TAC[affine; IN_UNIV]);;

let AFFINE_HYPERPLANE = prove
 (`!a b. affine {x | a dot x = b}`,
  REWRITE_TAC[affine; IN_ELIM_THM; DOT_RADD; DOT_RMUL] THEN
  CONV_TAC REAL_RING);;

let AFFINE_STANDARD_HYPERPLANE = prove
 (`!a b k. affine {x:real^N | x$k = b}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `b:real`] AFFINE_HYPERPLANE) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let AFFINE_INTERS = prove
 (`(!s. s IN f ==> affine s) ==> affine(INTERS f)`,
  REWRITE_TAC[affine; IN_INTERS] THEN MESON_TAC[]);;

let AFFINE_INTER = prove
 (`!s t. affine s /\ affine t ==> affine(s INTER t)`,
  REWRITE_TAC[affine; IN_INTER] THEN MESON_TAC[]);;

let AFFINE_AFFINE_HULL = prove
 (`!s. affine(affine hull s)`,
  SIMP_TAC[P_HULL; AFFINE_INTERS]);;

let AFFINE_HULL_EQ = prove
 (`!s. (affine hull s = s) <=> affine s`,
  SIMP_TAC[HULL_EQ; AFFINE_INTERS]);;

let IS_AFFINE_HULL = prove
 (`!s. affine s <=> ?t. s = affine hull t`,
  GEN_TAC THEN MATCH_MP_TAC IS_HULL THEN SIMP_TAC[AFFINE_INTERS]);;

let AFFINE_HULL_UNIV = prove
 (`affine hull (:real^N) = (:real^N)`,
  REWRITE_TAC[AFFINE_HULL_EQ; AFFINE_UNIV]);;

let AFFINE_HULLS_EQ = prove
 (`!s t. s SUBSET affine hull t /\ t SUBSET affine hull s
         ==> affine hull s = affine hull t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULLS_EQ THEN
  ASM_SIMP_TAC[AFFINE_INTERS]);;

let AFFINE_HULL_TRANSLATION = prove
 (`!a s. affine hull (IMAGE (\x. a + x) s) =
         IMAGE (\x. a + x) (affine hull s)`,
  REWRITE_TAC[hull] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [AFFINE_HULL_TRANSLATION];;

let AFFINE_HULL_LINEAR_IMAGE = prove
 (`!f s. linear f
         ==> affine hull (IMAGE f s) = IMAGE f (affine hull s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  CONJ_TAC THEN MATCH_MP_TAC HULL_INDUCT THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN SIMP_TAC[FUN_IN_IMAGE; HULL_INC] THEN
  REWRITE_TAC[affine; IN_ELIM_THM] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_CMUL th)]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_ADD th)]) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    MESON_TAC[REWRITE_RULE[affine] AFFINE_AFFINE_HULL];
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
    MESON_TAC[REWRITE_RULE[affine] AFFINE_AFFINE_HULL]]);;

add_linear_invariants [AFFINE_HULL_LINEAR_IMAGE];;

let IN_AFFINE_HULL_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s x.
        linear f /\ x IN affine hull s ==> (f x) IN affine hull (IMAGE f s)`,
  SIMP_TAC[AFFINE_HULL_LINEAR_IMAGE] THEN SET_TAC[]);;

let SAME_DISTANCES_TO_AFFINE_HULL = prove
 (`!s a b:real^N.
        (!x. x IN s ==> dist(x,a) = dist(x,b))
        ==> (!x. x IN affine hull s ==> dist(x,a) = dist(x,b))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HULL_INDUCT THEN
  ASM_REWRITE_TAC[AFFINE_ALT; IN_ELIM_THM] THEN
  REWRITE_TAC[dist; NORM_EQ_SQUARE; NORM_POS_LE; VECTOR_ARITH
   `((&1 - u) % x + u % y) - a:real^N = (&1 - u) % (x - a) + u % (y - a)`] THEN
  REWRITE_TAC[NORM_POW_2; DOT_LMUL; DOT_RMUL; VECTOR_ARITH
   `(x + y) dot (x + y):real^N = (x dot x + y dot y) + &2 * x dot y`] THEN
  SIMP_TAC[DOT_LSUB; DOT_RSUB; DOT_SYM] THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Some convenient lemmas about common affine combinations.                  *)
(* ------------------------------------------------------------------------- *)

let IN_AFFINE_ADD_MUL = prove
 (`!s a x:real^N d. affine s /\ a IN s /\ (a + x) IN s ==> (a + d % x) IN s`,
  REWRITE_TAC[affine] THEN REPEAT STRIP_TAC THEN
  SUBST1_TAC(VECTOR_ARITH `a + d % x:real^N = (&1 - d) % a + d % (a + x)`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let IN_AFFINE_ADD_MUL_DIFF = prove
 (`!s a x y z:real^N.
        affine s /\ x IN s /\ y IN s /\ z IN s ==> (x + a % (y - z)) IN s`,
  REWRITE_TAC[affine] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[VECTOR_ARITH
   `x + a % (y - z):real^N =
    &1 / &2 % ((&1 - &2 * a) % x + (&2 * a) % y) +
    &1 / &2 % ((&1 + &2 * a) % x + (-- &2 * a) % z)`] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let IN_AFFINE_MUL_DIFF_ADD = prove
 (`!s a x y z:real^N.
        affine s /\ x IN s /\ y IN s /\ z IN s ==> a % (x - y) + z IN s`,
  ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
  SIMP_TAC[IN_AFFINE_ADD_MUL_DIFF]);;

let IN_AFFINE_SUB_MUL_DIFF = prove
 (`!s a x y z:real^N.
        affine s /\ x IN s /\ y IN s /\ z IN s ==> x - a % (y - z) IN s`,
  REWRITE_TAC[VECTOR_ARITH `x - a % (y - z):real^N = x + a % (z - y)`] THEN
  SIMP_TAC[IN_AFFINE_ADD_MUL_DIFF]);;

let AFFINE_DIFFS_SUBSPACE = prove
 (`!s:real^N->bool a.
        affine s /\ a IN s ==> subspace {x - a | x IN s}`,
  REWRITE_TAC[subspace; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[VECTOR_ARITH `vec 0:real^N = x - a <=> x = a`;
              VECTOR_ARITH `x - a + y - a:real^N = z - a <=>
                            z = (a + &1 % (x - a)) + &1 % (y - a)`;
              VECTOR_ARITH `c % (x - a):real^N = y - a <=>
                            y = a + c % (x - a)`] THEN
  MESON_TAC[IN_AFFINE_ADD_MUL_DIFF]);;

(* ------------------------------------------------------------------------- *)
(* Explicit formulations for affine combinations.                            *)
(* ------------------------------------------------------------------------- *)

let AFFINE_VSUM = prove
 (`!s k u x:A->real^N.
        FINITE k /\ affine s /\ sum k u = &1 /\ (!i. i IN k ==> x i IN s)
        ==> vsum k (\i. u i % x i) IN s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; GSYM NOT_EXISTS_THM; MEMBER_NOT_EMPTY] THEN
    ASM_CASES_TAC `k:A->bool = {}` THEN ASM_REWRITE_TAC[SUM_CLAUSES] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`] AFFINE_DIFFS_SUBSPACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{x - a:real^N | x IN s}`;
                 `(\i. u i % (x i - a)):A->real^N`;
                 `k:A->bool`] SUBSPACE_VSUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBSPACE_MUL THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM_SIMP_TAC[VSUM_SUB; IN_ELIM_THM; VECTOR_SUB_LDISTRIB; VSUM_RMUL] THEN
    REWRITE_TAC[VECTOR_ARITH `x - &1 % a:real^N = y - a <=> x = y`] THEN
    ASM_MESON_TAC[]]);;

let AFFINE_VSUM_STRONG = prove
 (`!s k u x:A->real^N.
        affine s /\
        sum k u = &1 /\
        (!i. i IN k ==> u i = &0 \/ x i IN s)
        ==> vsum k (\i. u i % x i) IN s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `vsum k (\i. u i % (x:A->real^N) i) =
    vsum {i | i IN k /\ ~(u i = &0)} (\i. u i % x i)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
    SET_TAC[];
    MATCH_MP_TAC AFFINE_VSUM THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SUM_DEGENERATE; REAL_ARITH `~(&1 = &0)`];
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN ASM SET_TAC[];
      ASM SET_TAC[]]]);;

let AFFINE_INDEXED = prove
 (`!s:real^N->bool.
        affine s <=>
            !k u x. (!i:num. 1 <= i /\ i <= k ==> x(i) IN s) /\
                    (sum (1..k) u = &1)
                    ==> vsum (1..k) (\i. u(i) % x(i)) IN s`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC AFFINE_VSUM THEN
    ASM_REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG];
    DISCH_TAC THEN REWRITE_TAC[affine] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN
    DISCH_THEN(MP_TAC o SPEC `\n. if n = 1 then u else v:real`) THEN
    DISCH_THEN(MP_TAC o SPEC `\n. if n = 1 then x else y:real^N`) THEN
    REWRITE_TAC[num_CONV `2`; SUM_CLAUSES_NUMSEG; VSUM_CLAUSES_NUMSEG;
      NUMSEG_SING; VSUM_SING; SUM_SING] THEN REWRITE_TAC[ARITH] THEN
    ASM_MESON_TAC[]]);;

let AFFINE_HULL_INDEXED = prove
 (`!s. affine hull s =
        {y:real^N | ?k u x. (!i. 1 <= i /\ i <= k ==> x i IN s) /\
                            (sum (1..k) u = &1) /\
                            (vsum (1..k) (\i. u i % x i) = y)}`,
  GEN_TAC THEN MATCH_MP_TAC HULL_UNIQUE THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`1`; `\i:num. &1`; `\i:num. x:real^N`] THEN
    ASM_SIMP_TAC[FINITE_RULES; IN_SING; SUM_SING; VECTOR_MUL_LID; VSUM_SING;
                 REAL_POS; NUMSEG_SING];
    ALL_TAC;
    REWRITE_TAC[AFFINE_INDEXED; SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MESON_TAC[]] THEN
  REWRITE_TAC[affine; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`k1:num`; `u1:num->real`; `x1:num->real^N`;
    `k2:num`; `u2:num->real`; `x2:num->real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `k1 + k2:num` THEN
  EXISTS_TAC `\i:num. if i <= k1 then u * u1(i) else v * u2(i - k1):real` THEN
  EXISTS_TAC `\i:num. if i <= k1 then x1(i) else x2(i - k1):real^N` THEN
  ASM_SIMP_TAC[NUMSEG_ADD_SPLIT; ARITH_RULE `1 <= x + 1 /\ x < x + 1`;
   IN_NUMSEG; SUM_UNION; VSUM_UNION; FINITE_NUMSEG; DISJOINT_NUMSEG;
   ARITH_RULE `k1 + 1 <= i ==> ~(i <= k1)`] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] NUMSEG_OFFSET_IMAGE] THEN
  ASM_SIMP_TAC[SUM_IMAGE; VSUM_IMAGE; EQ_ADD_LCANCEL; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[o_DEF; ADD_SUB2; SUM_LMUL; VSUM_LMUL; GSYM VECTOR_MUL_ASSOC;
               FINITE_NUMSEG; REAL_MUL_RID] THEN
  ASM_MESON_TAC[REAL_LE_MUL; ARITH_RULE
    `i <= k1 + k2 /\ ~(i <= k1) ==> 1 <= i - k1 /\ i - k1 <= k2`]);;

let AFFINE = prove
 (`!V:real^N->bool.
     affine V <=>
         !(s:real^N->bool) (u:real^N->real).
             FINITE s /\ ~(s = {}) /\ s SUBSET V /\ sum s u = &1
             ==> vsum s (\x. u x % x) IN V`,
  GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC AFFINE_VSUM THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[affine] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
    STRIP_TAC THEN ASM_CASES_TAC `x:real^N = y` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_REWRITE_TAC[GSYM VECTOR_ADD_RDISTRIB;VECTOR_MUL_LID];ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `{x:real^N,y}`) THEN
    DISCH_THEN(MP_TAC o SPEC `\w. if w = x:real^N then u else v:real`) THEN
    ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_RULES; NUMSEG_SING;
                 VSUM_SING; SUM_SING;SUBSET;IN_INSERT;NOT_IN_EMPTY] THEN
    ASM SET_TAC[]]);;

let AFFINE_EXPLICIT = prove
 (`!s:real^N->bool.
        affine s <=>
            !t u. FINITE t /\ t SUBSET s /\ sum t u = &1
                  ==> vsum t (\x. u(x) % x) IN s`,
  GEN_TAC THEN REWRITE_TAC[AFFINE] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `t:real^N->bool` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SUM_CLAUSES] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let AFFINE_HULL_EXPLICIT = prove
 (`!(p:real^N -> bool).
        affine hull p =
         {y | ?s u. FINITE s /\ ~(s = {}) /\ s SUBSET p /\
                    sum s u = &1 /\ vsum s (\v. u v % v) = y}`,
  GEN_TAC THEN MATCH_MP_TAC HULL_UNIQUE THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET;IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`{x:real^N}`;`\v:real^N. &1:real`] THEN
    ASM_SIMP_TAC[FINITE_RULES;IN_SING;SUM_SING;VSUM_SING;VECTOR_MUL_LID] THEN
    SET_TAC[];
    REWRITE_TAC[affine;IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `(s UNION s'):real^N->bool` THEN
    EXISTS_TAC
      `\a:real^N. (\b:real^N.if (b IN s) then (u * (u' b)) else &0) a +
                  (\b:real^N.if (b IN s') then v * (u'' b) else &0) a` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[FINITE_UNION];
      ASM SET_TAC[];
      ASM_REWRITE_TAC[UNION_SUBSET];
      ASM_SIMP_TAC[REWRITE_RULE[REAL_ARITH `a + b = c + d <=> c = a + b - d`]
                   SUM_INCL_EXCL; GSYM SUM_RESTRICT_SET;
                   SET_RULE `{a | a IN (s:A->bool) /\ a IN s'} = s INTER s'`;
                   SUM_ADD;SUM_LMUL;REAL_MUL_RID;
                   FINITE_INTER;INTER_IDEMPOT] THEN
    ASM_REWRITE_TAC[SET_RULE `(a INTER b) INTER a = a INTER b`;
                    SET_RULE `(a INTER b) INTER b = a INTER b`;
                    REAL_ARITH `(a + b) + (c + d) - (e + b) = (a + d) + c - e`;
                    REAL_ARITH `a + b - c = a <=> b = c`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[INTER_COMM];
    ASM_SIMP_TAC[REWRITE_RULE
                  [VECTOR_ARITH `(a:real^N) + b = c + d <=> c = a + b - d`]
                  VSUM_INCL_EXCL;GSYM VSUM_RESTRICT_SET;
                 SET_RULE `{a | a IN (s:A->bool) /\ a IN s'} = s INTER s'`;
                 VSUM_ADD;FINITE_INTER;INTER_IDEMPOT;VECTOR_ADD_RDISTRIB;
                 GSYM VECTOR_MUL_ASSOC;VSUM_LMUL;
                 MESON[] `(if P then a else b) % (x:real^N) =
                          (if P then a % x else b % x)`;
                 VECTOR_MUL_LZERO;GSYM VSUM_RESTRICT_SET] THEN
    ASM_REWRITE_TAC[SET_RULE `(a INTER b) INTER a = a INTER b`;
                    SET_RULE `(a INTER b) INTER b = a INTER b`;
                    VECTOR_ARITH
                     `((a:real^N) + b) + (c + d) - (e + b) = (a + d) + c - e`;
                    VECTOR_ARITH `(a:real^N) + b - c = a <=> b = c`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[INTER_COMM]];
    ASM_CASES_TAC `(p:real^N->bool) = {}` THENL
      [FIRST_X_ASSUM SUBST_ALL_TAC THEN
       REWRITE_TAC[SUBSET_EMPTY;EMPTY_SUBSET] THEN ASM SET_TAC[];
       ALL_TAC] THEN
    REWRITE_TAC[AFFINE; SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    ASM SET_TAC[]]);;

let AFFINE_HULL_EXPLICIT_ALT = prove
 (`!(p:real^N -> bool).
        affine hull p =
         {y | ?s u. FINITE s /\ s SUBSET p /\
                    sum s u = &1 /\ vsum s (\v. u v % v) = y}`,
  GEN_TAC THEN REWRITE_TAC[AFFINE_HULL_EXPLICIT] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  GEN_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  SIMP_TAC[SUM_CLAUSES; REAL_OF_NUM_EQ; ARITH_EQ]);;

let AFFINE_HULL_FINITE = prove
 (`!s:real^N->bool.
        affine hull s = {y | ?u. sum s u = &1 /\ vsum s (\v. u v % v) = y}`,
  GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[AFFINE_HULL_EXPLICIT; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `f:real^N->real`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `\x:real^N. if x IN t then f x else &0` THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; VECTOR_MUL_LZERO] THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET; GSYM VSUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC[SET_RULE `t SUBSET s ==> {x | x IN s /\ x IN t} = t`];
    X_GEN_TAC `f:real^N->real` THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[SUM_CLAUSES; REAL_OF_NUM_EQ; ARITH] THEN STRIP_TAC THEN
    EXISTS_TAC `support (+) (f:real^N->real) s` THEN
    EXISTS_TAC `f:real^N->real` THEN
    MP_TAC(ASSUME `sum s (f:real^N->real) = &1`) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [sum] THEN
    REWRITE_TAC[iterate] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[NEUTRAL_REAL_ADD; REAL_OF_NUM_EQ; ARITH] THEN
    DISCH_THEN(K ALL_TAC) THEN
    UNDISCH_TAC `sum s (f:real^N->real) = &1` THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM SUM_SUPPORT] THEN
    ASM_CASES_TAC `support (+) (f:real^N->real) s = {}` THEN
    ASM_SIMP_TAC[SUM_CLAUSES; REAL_OF_NUM_EQ; ARITH] THEN
    DISCH_TAC THEN REWRITE_TAC[SUPPORT_SUBSET] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    REWRITE_TAC[SUPPORT_SUBSET] THEN
    REWRITE_TAC[support; IN_ELIM_THM; NEUTRAL_REAL_ADD] THEN
    MESON_TAC[VECTOR_MUL_LZERO]]);;

(* ------------------------------------------------------------------------- *)
(* Stepping theorems and hence small special cases.                          *)
(* ------------------------------------------------------------------------- *)

let AFFINE_HULL_EMPTY = prove
 (`affine hull {} = {}`,
  MATCH_MP_TAC HULL_UNIQUE THEN
  REWRITE_TAC[SUBSET_REFL; AFFINE_EMPTY; EMPTY_SUBSET]);;

let AFFINE_HULL_EQ_EMPTY = prove
 (`!s. (affine hull s = {}) <=> (s = {})`,
  GEN_TAC THEN EQ_TAC THEN
  MESON_TAC[SUBSET_EMPTY; HULL_SUBSET; AFFINE_HULL_EMPTY]);;

let AFFINE_HULL_FINITE_STEP_GEN = prove
 (`!P:real^N->real->bool.
        ((?u. (!x. x IN {} ==> P x (u x)) /\
              sum {} u = w /\ vsum {} (\x. u(x) % x) = y) <=>
         w = &0 /\ y = vec 0) /\
        (FINITE(s:real^N->bool) /\
         (!y. a IN s /\ P a y ==> P a (y / &2)) /\
         (!x y. a IN s /\ P a x /\ P a y ==> P a (x + y))
         ==> ((?u. (!x. x IN (a INSERT s) ==> P x (u x)) /\
                   sum (a INSERT s) u = w /\
                   vsum (a INSERT s) (\x. u(x) % x) = y) <=>
              ?v u. P a v /\ (!x. x IN s ==> P x (u x)) /\
                    sum s u = w - v /\
                    vsum s (\x. u(x) % x) = y - v % a))`,
  GEN_TAC THEN SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  ASM_CASES_TAC `(a:real^N) IN s` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[SET_RULE `a IN s ==> a INSERT s = s`] THEN EQ_TAC THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
     [X_GEN_TAC `u:real^N->real` THEN STRIP_TAC THEN
      EXISTS_TAC `(u:real^N->real) a / &2` THEN
      EXISTS_TAC `\x:real^N. if x = a then u x / &2 else u x`;
      MAP_EVERY X_GEN_TAC [`v:real`; `u:real^N->real`] THEN
      STRIP_TAC THEN
      EXISTS_TAC `\x:real^N. if x = a then u x + v else u x`] THEN
    ASM_SIMP_TAC[] THEN (CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ASM_SIMP_TAC[VSUM_CASES; SUM_CASES] THEN
    ASM_SIMP_TAC[GSYM DELETE; SUM_DELETE; VSUM_DELETE] THEN
    ASM_SIMP_TAC[SET_RULE `a IN s ==> {x | x IN s /\ x = a} = {a}`] THEN
    REWRITE_TAC[SUM_SING; VSUM_SING] THEN
    (CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]);
    EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
     [X_GEN_TAC `u:real^N->real` THEN STRIP_TAC THEN
      EXISTS_TAC `(u:real^N->real) a` THEN
      EXISTS_TAC `u:real^N->real` THEN ASM_SIMP_TAC[IN_INSERT] THEN
      REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`v:real`; `u:real^N->real`] THEN
      STRIP_TAC THEN
      EXISTS_TAC `\x:real^N. if x = a then v:real else u x` THEN
      ASM_SIMP_TAC[IN_INSERT] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
      ASM_SIMP_TAC[VSUM_CASES; SUM_CASES] THEN
      ASM_SIMP_TAC[GSYM DELETE; SUM_DELETE; VSUM_DELETE] THEN
      ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> {x | x IN s /\ x = a} = {}`] THEN
      ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> s DELETE a = s`] THEN
      REWRITE_TAC[SUM_CLAUSES; VSUM_CLAUSES] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]]]);;

let AFFINE_HULL_FINITE_STEP = prove
 (`((?u. sum {} u = w /\ vsum {} (\x. u(x) % x) = y) <=>
    w = &0 /\ y = vec 0) /\
   (FINITE(s:real^N->bool)
    ==> ((?u. sum (a INSERT s) u = w /\
              vsum (a INSERT s) (\x. u(x) % x) = y) <=>
         ?v u.  sum s u = w - v /\
                vsum s (\x. u(x) % x) = y - v % a))`,
  MATCH_ACCEPT_TAC (REWRITE_RULE[]
   (ISPEC `\x:real^N y:real. T` AFFINE_HULL_FINITE_STEP_GEN)));;

let AFFINE_HULL_2 = prove
 (`!a b. affine hull {a,b} =
         {u % a + v % b | u + v = &1}`,
  SIMP_TAC[AFFINE_HULL_FINITE; FINITE_INSERT; FINITE_RULES] THEN
  SIMP_TAC[AFFINE_HULL_FINITE_STEP; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[REAL_ARITH `x - y = z:real <=> x = y + z`;
              VECTOR_ARITH `x - y = z:real^N <=> x = y + z`] THEN
  REWRITE_TAC[VECTOR_ADD_RID; REAL_ADD_RID] THEN SET_TAC[]);;

let AFFINE_HULL_2_ALT = prove
 (`!a b. affine hull {a,b} = {a + u % (b - a) | u IN (:real)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AFFINE_HULL_2] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV; ARITH_RULE `u + v = &1 <=> v = &1 - u`;
    FORALL_UNWIND_THM2; UNWIND_THM2] THEN
  CONJ_TAC THEN X_GEN_TAC `u:real` THEN EXISTS_TAC `&1 - u` THEN
  VECTOR_ARITH_TAC);;

let AFFINE_HULL_3 = prove
 (`affine hull {a,b,c} =
    { u % a + v % b + w % c | u + v + w = &1}`,
  SIMP_TAC[AFFINE_HULL_FINITE; FINITE_INSERT; FINITE_RULES] THEN
  SIMP_TAC[AFFINE_HULL_FINITE_STEP; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[REAL_ARITH `x - y = z:real <=> x = y + z`;
              VECTOR_ARITH `x - y = z:real^N <=> x = y + z`] THEN
  REWRITE_TAC[VECTOR_ADD_RID; REAL_ADD_RID] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some relations between affine hull and subspaces.                         *)
(* ------------------------------------------------------------------------- *)

let AFFINE_HULL_INSERT_SUBSET_SPAN = prove
 (`!a:real^N s.
     affine hull (a INSERT s) SUBSET {a + v | v | v IN span {x - a | x IN s}}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [SUBSET] THEN
  REWRITE_TAC[AFFINE_HULL_EXPLICIT; SPAN_EXPLICIT; IN_ELIM_THM] THEN
  REWRITE_TAC[SIMPLE_IMAGE; CONJ_ASSOC; FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[MESON[]
   `(?s u. (?t. P t /\ s = f t) /\ Q s u) <=>
    (?t u. P t /\ Q (f t) u)`] THEN
  REWRITE_TAC[MESON[]
   `(?v. (?s u. P s /\ f s u = v) /\ (x = g a v)) <=>
    (?s u. ~(P s ==> ~(g a (f s u) = x)))`] THEN
  SIMP_TAC[VSUM_IMAGE; VECTOR_ARITH `x - a:real^N = y - a <=> x = y`] THEN
  REWRITE_TAC[o_DEF] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MAP_EVERY EXISTS_TAC
   [`t DELETE (a:real^N)`; `\x. (u:real^N->real)(x + a)`] THEN
  ASM_SIMP_TAC[FINITE_DELETE; VECTOR_SUB_ADD; SET_RULE
   `t SUBSET (a INSERT s) ==> t DELETE a SUBSET s`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `a + vsum t (\x. u x % (x - a)):real^N` THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN SET_TAC[];
    ASM_SIMP_TAC[VECTOR_SUB_LDISTRIB; FINITE_DELETE; VSUM_SUB] THEN
    ASM_REWRITE_TAC[VSUM_RMUL] THEN
    REWRITE_TAC[VECTOR_ARITH `a + x - &1 % a:real^N = x`]]);;

let AFFINE_HULL_INSERT_SPAN = prove
 (`!a:real^N s.
        ~(a IN s)
        ==> affine hull (a INSERT s) =
            {a + v | v | v IN span {x - a | x IN s}}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[AFFINE_HULL_INSERT_SUBSET_SPAN] THEN REWRITE_TAC[SUBSET] THEN
  REWRITE_TAC[AFFINE_HULL_EXPLICIT; SPAN_EXPLICIT; IN_ELIM_THM] THEN
  REWRITE_TAC[SIMPLE_IMAGE; CONJ_ASSOC; FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[MESON[]
   `(?s u. (?t. P t /\ s = f t) /\ Q s u) <=>
    (?t u. P t /\ Q (f t) u)`] THEN
  REWRITE_TAC[MESON[]
   `(?v. (?s u. P s /\ f s u = v) /\ (x = g a v)) <=>
    (?s u. ~(P s ==> ~(g a (f s u) = x)))`] THEN
  SIMP_TAC[VSUM_IMAGE; VECTOR_ARITH `x - a:real^N = y - a <=> x = y`] THEN
  REWRITE_TAC[o_DEF] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MAP_EVERY EXISTS_TAC
   [`(a:real^N) INSERT t`;
    `\x. if x = a then &1 - sum t (\x. u(x - a))
         else (u:real^N->real)(x - a)`] THEN
  ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES] THEN
  ASM_CASES_TAC `(a:real^N) IN t` THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_INSERT; NOT_INSERT_EMPTY;
               SET_RULE `s SUBSET t ==> (a INSERT s) SUBSET (a INSERT t)`] THEN
  SUBGOAL_THEN `!x:real^N. x IN t ==> ~(x = a)` MP_TAC THENL
   [ASM SET_TAC[]; SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC)] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[VECTOR_SUB_LDISTRIB; FINITE_DELETE; VSUM_SUB] THEN
  ASM_REWRITE_TAC[VSUM_RMUL] THEN VECTOR_ARITH_TAC);;

let AFFINE_HULL_SPAN = prove
 (`!a:real^N s.
        a IN s
        ==> (affine hull s =
             {a + v | v | v IN span {x - a | x | x IN (s DELETE a)}})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `s DELETE (a:real^N)`]
    AFFINE_HULL_INSERT_SPAN) THEN
  ASM_REWRITE_TAC[IN_DELETE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let DIFFS_AFFINE_HULL_SPAN = prove
 (`!a:real^N s.
        a IN s ==> {x - a | x IN affine hull s} = span {x - a | x IN s}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFFINE_HULL_SPAN) THEN
  REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o; o_DEF; VECTOR_ADD_SUB; IMAGE_ID] THEN
  SIMP_TAC[IMAGE_DELETE_INJ;
           VECTOR_ARITH `x - a:real^N = y - a <=> x = y`] THEN
  REWRITE_TAC[VECTOR_SUB_REFL; SPAN_DELETE_0]);;

let AFFINE_HULL_SING = prove
 (`!a. affine hull {a} = {a}`,
  SIMP_TAC[AFFINE_HULL_INSERT_SPAN; NOT_IN_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{f x | x | F} = {}`; SPAN_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{f x | x IN {a}} = {f a}`; VECTOR_ADD_RID]);;

let AFFINE_HULL_EQ_SING = prove
 (`!s a:real^N. affine hull s = {a} <=> s = {a}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[AFFINE_HULL_EMPTY] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[AFFINE_HULL_SING] THEN
  MATCH_MP_TAC(SET_RULE `~(s = {}) /\ s SUBSET {a} ==> s = {a}`) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[HULL_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Convexity.                                                                *)
(* ------------------------------------------------------------------------- *)

let convex = new_definition
  `convex s <=>
        !x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
                  ==> (u % x + v % y) IN s`;;

let CONVEX_ALT = prove
 (`convex s <=> !x y u. x IN s /\ y IN s /\ &0 <= u /\ u <= &1
                        ==> ((&1 - u) % x + u % y) IN s`,
  REWRITE_TAC[convex] THEN
  MESON_TAC[REAL_ARITH `&0 <= u /\ &0 <= v /\ (u + v = &1)
                        ==> v <= &1 /\ (u = &1 - v)`;
            REAL_ARITH `u <= &1 ==> &0 <= &1 - u /\ ((&1 - u) + u = &1)`]);;

let IN_CONVEX_SET = prove
 (`!s a b u.
        convex s /\ a IN s /\ b IN s /\ &0 <= u /\ u <= &1
        ==> ((&1 - u) % a + u % b) IN s`,
  MESON_TAC[CONVEX_ALT]);;

let MIDPOINT_IN_CONVEX = prove
 (`!s x y:real^N.
        convex s /\ x IN s /\ y IN s ==> midpoint(x,y) IN s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`; `y:real^N`; `&1 / &2`]
        IN_CONVEX_SET) THEN
  ASM_REWRITE_TAC[midpoint] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC VECTOR_ARITH);;

let CONVEX_CONTAINS_SEGMENT = prove
 (`!s. convex s <=> !a b. a IN s /\ b IN s ==> segment[a,b] SUBSET s`,
  REWRITE_TAC[CONVEX_ALT; segment; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let CONVEX_CONTAINS_OPEN_SEGMENT = prove
 (`!s. convex s <=> !a b. a IN s /\ b IN s ==> segment(a,b) SUBSET s`,
  ONCE_REWRITE_TAC[segment] THEN REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
  SET_TAC[]);;

let CONVEX_CONTAINS_SEGMENT_EQ = prove
 (`!s:real^N->bool.
        convex s <=> !a b. segment[a,b] SUBSET s <=> a IN s /\ b IN s`,
  REWRITE_TAC[CONVEX_CONTAINS_SEGMENT; SUBSET] THEN
  MESON_TAC[ENDS_IN_SEGMENT]);;

let CONVEX_CONTAINS_SEGMENT_IMP = prove
 (`!s a b. convex s ==> (segment[a,b] SUBSET s <=> a IN s /\ b IN s)`,
  SIMP_TAC[CONVEX_CONTAINS_SEGMENT_EQ]);;

let CONVEX_EMPTY = prove
 (`convex {}`,
  REWRITE_TAC[convex; NOT_IN_EMPTY]);;

let CONVEX_SING = prove
 (`!a. convex {a}`,
  SIMP_TAC[convex; IN_SING; GSYM VECTOR_ADD_RDISTRIB; VECTOR_MUL_LID]);;

let CONVEX_UNIV = prove
 (`convex(UNIV:real^N->bool)`,
  REWRITE_TAC[convex; IN_UNIV]);;

let CONVEX_INTERS = prove
 (`(!s. s IN f ==> convex s) ==> convex(INTERS f)`,
  REWRITE_TAC[convex; IN_INTERS] THEN MESON_TAC[]);;

let CONVEX_INTER = prove
 (`!s t. convex s /\ convex t ==> convex(s INTER t)`,
  REWRITE_TAC[convex; IN_INTER] THEN MESON_TAC[]);;

let CONVEX_HALFSPACE_LE = prove
 (`!a b. convex {x | a dot x <= b}`,
  REWRITE_TAC[convex; IN_ELIM_THM; DOT_RADD; DOT_RMUL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(u + v) * b` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_ADD_RDISTRIB; REAL_LE_ADD2; REAL_LE_LMUL];
    ASM_MESON_TAC[REAL_MUL_LID; REAL_LE_REFL]]);;

let CONVEX_HALFSPACE_COMPONENT_LE = prove
 (`!a k. convex {x:real^N | x$k <= a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CONVEX_HALFSPACE_LE) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let CONVEX_HALFSPACE_GE = prove
 (`!a b. convex {x:real^N | a dot x >= b}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{x:real^N | a dot x >= b} = {x | --a dot x <= --b}`
   (fun th -> REWRITE_TAC[th; CONVEX_HALFSPACE_LE]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_LNEG] THEN REAL_ARITH_TAC);;

let CONVEX_HALFSPACE_COMPONENT_GE = prove
 (`!a k. convex {x:real^N | x$k >= a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CONVEX_HALFSPACE_GE) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let CONVEX_HYPERPLANE = prove
 (`!a b. convex {x:real^N | a dot x = b}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `{x:real^N | a dot x = b} = {x | a dot x <= b} INTER {x | a dot x >= b}`
   (fun th -> SIMP_TAC[th; CONVEX_INTER;
                       CONVEX_HALFSPACE_LE; CONVEX_HALFSPACE_GE]) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let CONVEX_STANDARD_HYPERPLANE = prove
 (`!k a. convex {x:real^N | x$k = a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CONVEX_HYPERPLANE) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let CONVEX_HALFSPACE_LT = prove
 (`!a b. convex {x | a dot x < b}`,
  REWRITE_TAC[convex; IN_ELIM_THM; DOT_RADD; DOT_RMUL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONVEX_BOUND_LT THEN
  ASM_REWRITE_TAC[]);;

let CONVEX_HALFSPACE_COMPONENT_LT = prove
 (`!a k. convex {x:real^N | x$k < a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CONVEX_HALFSPACE_LT) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let CONVEX_HALFSPACE_GT = prove
 (`!a b. convex {x | a dot x > b}`,
  REWRITE_TAC[REAL_ARITH `ax > b <=> --ax < --b`] THEN
  REWRITE_TAC[GSYM DOT_LNEG; CONVEX_HALFSPACE_LT]);;

let CONVEX_HALFSPACE_COMPONENT_GT = prove
 (`!a k. convex {x:real^N | x$k > a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CONVEX_HALFSPACE_GT) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let CONVEX_POSITIVE_ORTHANT = prove
 (`convex {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                          ==> &0 <= x$i}`,
  SIMP_TAC[convex; IN_ELIM_THM; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           REAL_LE_MUL; REAL_LE_ADD]);;

let LIMPT_OF_CONVEX = prove
 (`!s x:real^N.
        convex s /\ x IN s ==> (x limit_point_of s <=> ~(s = {x}))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s = {x:real^N}` THEN ASM_REWRITE_TAC[LIMPT_SING] THEN
  SUBGOAL_THEN `?y:real^N. y IN s /\ ~(y = x)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIMPT_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `u = min (&1 / &2) (e / &2 / norm(y - x:real^N))` THEN
  SUBGOAL_THEN `&0 < u /\ u < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ];
    ALL_TAC] THEN
  EXISTS_TAC `(&1 - u) % x + u % y:real^N` THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; VECTOR_ARITH
     `(&1 - u) % x + u % y:real^N = x <=> u % (y - x) = vec 0`] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[dist; NORM_MUL; VECTOR_ARITH
     `((&1 - u) % x + u % y) - x:real^N = u % (y - x)`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < u ==> abs u = u`] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= e / &2 /\ &0 < e ==> x < e`) THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    ASM_REAL_ARITH_TAC]);;

let TRIVIAL_LIMIT_WITHIN_CONVEX = prove
 (`!s x:real^N.
        convex s /\ x IN s ==> (trivial_limit(at x within s) <=> s = {x})`,
  SIMP_TAC[TRIVIAL_LIMIT_WITHIN; LIMPT_OF_CONVEX]);;

(* ------------------------------------------------------------------------- *)
(* Some invariance theorems for convex sets.                                 *)
(* ------------------------------------------------------------------------- *)

let CONVEX_TRANSLATION_EQ = prove
 (`!a:real^N s. convex (IMAGE (\x. a + x) s) <=> convex s`,
  REWRITE_TAC[CONVEX_ALT; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE; UNWIND_THM1; VECTOR_ARITH
   `(&1 - u) % (a + x) + u % (a + y) = a + z <=> (&1 - u) % x + u % y = z`]);;

add_translation_invariants [CONVEX_TRANSLATION_EQ];;

let CONVEX_TRANSLATION = prove
 (`!s a:real^N. convex s ==> convex (IMAGE (\x. a + x) s)`,
  REWRITE_TAC[CONVEX_TRANSLATION_EQ]);;

let CONVEX_LINEAR_IMAGE = prove
 (`!f s. convex s /\ linear f ==> convex(IMAGE f s)`,
  REWRITE_TAC[convex; FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IN_IMAGE; linear] THEN MESON_TAC[]);;

let CONVEX_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (convex (IMAGE f s) <=> convex s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE CONVEX_LINEAR_IMAGE));;

add_linear_invariants [CONVEX_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Explicit expressions for convexity in terms of arbitrary sums.            *)
(* ------------------------------------------------------------------------- *)

let CONVEX_VSUM = prove
 (`!s k u x:A->real^N.
        FINITE k /\ convex s /\ sum k u = &1 /\
        (!i. i IN k ==> &0 <= u i /\ x i IN s)
        ==> vsum k (\i. u i % x i) IN s`,
  GEN_TAC THEN ASM_CASES_TAC `convex(s:real^N->bool)` THEN
  ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FORALL_IN_INSERT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MAP_EVERY X_GEN_TAC [`i:A`; `k:A->bool`] THEN
  GEN_REWRITE_TAC (BINOP_CONV o DEPTH_CONV) [RIGHT_IMP_FORALL_THM] THEN
  REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`u:A->real`; `x:A->real^N`] THEN
  ASM_CASES_TAC `(u:A->real) i = &1` THENL
   [ASM_REWRITE_TAC[REAL_ARITH `&1 + a  = &1 <=> a = &0`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `vsum k (\i:A. u i % x(i):real^N) = vec 0`
     (fun th -> ASM_SIMP_TAC[th; VECTOR_ADD_RID; VECTOR_MUL_LID]) THEN
    MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
    REPEAT STRIP_TAC THEN DISJ1_TAC THEN
    ASM_MESON_TAC[SUM_POS_EQ_0];
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\j:A. u(j) / (&1 - u(i))`) THEN
    ASM_REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[SUM_LMUL; VSUM_LMUL; GSYM VECTOR_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    SUBGOAL_THEN `&0 < &1 - u(i:A)` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUM_POS_LE; REAL_ADD_SYM; REAL_ARITH
       `&0 <= a /\ &0 <= b /\ b + a = &1 /\ ~(a = &1) ==> &0 < &1 - a`];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_MUL_LID; REAL_EQ_SUB_LADD] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`vsum k (\j. (u j / (&1 - u(i:A))) % x(j) :real^N)`;
      `x(i:A):real^N`; `&1 - u(i:A)`; `u(i:A):real`]) THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM VECTOR_MUL_ASSOC; VSUM_LMUL] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; VSUM_LMUL] THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC; REAL_ARITH_TAC] THEN
    ASM_MESON_TAC[REAL_ADD_SYM]]);;

let CONVEX_VSUM_STRONG = prove
 (`!s k u x:A->real^N.
        convex s /\
        sum k u = &1 /\
        (!i. i IN k ==> &0 <= u i /\ (u i = &0 \/ x i IN s))
        ==> vsum k (\i. u i % x i) IN s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `vsum k (\i. u i % (x:A->real^N) i) =
    vsum {i | i IN k /\ ~(u i = &0)} (\i. u i % x i)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
    SET_TAC[];
    MATCH_MP_TAC CONVEX_VSUM THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SUM_DEGENERATE; REAL_ARITH `~(&1 = &0)`];
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN ASM SET_TAC[];
      ASM SET_TAC[]]]);;

let CONVEX_INDEXED = prove
 (`!s:real^N->bool.
        convex s <=>
            !k u x. (!i:num. 1 <= i /\ i <= k ==> &0 <= u(i) /\ x(i) IN s) /\
                    (sum (1..k) u = &1)
                    ==> vsum (1..k) (\i. u(i) % x(i)) IN s`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_VSUM THEN
    ASM_REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG];
    DISCH_TAC THEN REWRITE_TAC[convex] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN
    DISCH_THEN(MP_TAC o SPEC `\n. if n = 1 then u else v:real`) THEN
    DISCH_THEN(MP_TAC o SPEC `\n. if n = 1 then x else y:real^N`) THEN
    REWRITE_TAC[num_CONV `2`; SUM_CLAUSES_NUMSEG; VSUM_CLAUSES_NUMSEG;
      NUMSEG_SING; VSUM_SING; SUM_SING] THEN REWRITE_TAC[ARITH] THEN
    ASM_MESON_TAC[]]);;

let CONVEX_EXPLICIT = prove
 (`!s:real^N->bool.
        convex s <=>
        !t u. FINITE t /\ t SUBSET s /\ (!x. x IN t ==> &0 <= u x) /\
              sum t u = &1
              ==> vsum t (\x. u(x) % x) IN s`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_VSUM THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_TAC THEN REWRITE_TAC[convex] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
    ASM_CASES_TAC `x:real^N = y` THENL
     [ASM_SIMP_TAC[GSYM VECTOR_ADD_RDISTRIB; VECTOR_MUL_LID]; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `{x:real^N,y}`) THEN
    DISCH_THEN(MP_TAC o SPEC `\z:real^N. if z = x then u else v:real`) THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_RULES; SUM_CLAUSES; VSUM_CLAUSES;
                 NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; REAL_ADD_RID; SUBSET] THEN
    REWRITE_TAC[VECTOR_ADD_RID] THEN ASM_MESON_TAC[]]);;

let CONVEX = prove
 (`!V:real^N->bool.
     convex V <=>
         !(s:real^N->bool) (u:real^N->real).
             FINITE s /\ ~(s = {}) /\ s SUBSET V /\
             (!x. x IN s ==> &0 <= u x) /\ sum s u = &1
             ==> vsum s (\x. u x % x) IN V`,
  GEN_TAC THEN REWRITE_TAC[CONVEX_EXPLICIT] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `t:real^N->bool` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SUM_CLAUSES] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let CONVEX_FINITE = prove
 (`!s:real^N->bool.
        FINITE s
        ==> (convex s <=>
                !u. (!x. x IN s ==> &0 <= u x) /\
                    sum s u = &1
                    ==> vsum s (\x. u(x) % x) IN s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONVEX_EXPLICIT] THEN
  EQ_TAC THENL [ASM_MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\x:real^N. if x IN t then u x else &0`) THEN
  ASM_SIMP_TAC[GSYM SUM_RESTRICT_SET] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  ASM_SIMP_TAC[VECTOR_MUL_LZERO; REAL_LE_REFL; GSYM VSUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[COND_ID; SET_RULE `t SUBSET s ==> {x | x IN s /\ x IN t} = t`]);;

let AFFINE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        affine s /\ affine t ==> affine(s PCROSS t)`,
  REWRITE_TAC[affine; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  SIMP_TAC[FORALL_IN_PCROSS; GSYM PASTECART_CMUL; PASTECART_ADD] THEN
  SIMP_TAC[PASTECART_IN_PCROSS]);;

let AFFINE_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        affine(s PCROSS t) <=> s = {} \/ t = {} \/ affine s /\ affine t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; AFFINE_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; AFFINE_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[AFFINE_PCROSS] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
      `(s:real^M->bool) PCROSS (t:real^N->bool)`] AFFINE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART];
    MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
      `(s:real^M->bool) PCROSS (t:real^N->bool)`] AFFINE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

let CONVEX_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        convex s /\ convex t ==> convex(s PCROSS t)`,
  REWRITE_TAC[convex; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  SIMP_TAC[FORALL_IN_PCROSS; GSYM PASTECART_CMUL; PASTECART_ADD] THEN
  SIMP_TAC[PASTECART_IN_PCROSS]);;

let CONVEX_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        convex(s PCROSS t) <=> s = {} \/ t = {} \/ convex s /\ convex t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; CONVEX_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; CONVEX_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[CONVEX_PCROSS] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
      `(s:real^M->bool) PCROSS (t:real^N->bool)`] CONVEX_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART];
    MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
      `(s:real^M->bool) PCROSS (t:real^N->bool)`] CONVEX_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Conic sets and conic hull.                                                *)
(* ------------------------------------------------------------------------- *)

let conic = new_definition
  `conic s <=> !x c. x IN s /\ &0 <= c ==> (c % x) IN s`;;

let SUBSPACE_IMP_CONIC = prove
 (`!s. subspace s ==> conic s`,
  SIMP_TAC[subspace; conic]);;

let CONIC_EMPTY = prove
 (`conic {}`,
  REWRITE_TAC[conic; NOT_IN_EMPTY]);;

let CONIC_UNIV = prove
 (`conic (UNIV:real^N->bool)`,
  REWRITE_TAC[conic; IN_UNIV]);;

let CONIC_INTERS = prove
 (`(!s. s IN f ==> conic s) ==> conic(INTERS f)`,
  REWRITE_TAC[conic; IN_INTERS] THEN MESON_TAC[]);;

let CONIC_LINEAR_IMAGE = prove
 (`!f s. conic s /\ linear f ==> conic(IMAGE f s)`,
  REWRITE_TAC[conic; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[LINEAR_CMUL]);;

let CONIC_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (conic (IMAGE f s) <=> conic s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE CONIC_LINEAR_IMAGE));;

add_linear_invariants [CONIC_LINEAR_IMAGE_EQ];;

let CONIC_CONIC_HULL = prove
 (`!s. conic(conic hull s)`,
  SIMP_TAC[P_HULL; CONIC_INTERS]);;

let CONIC_HULL_EQ = prove
 (`!s. (conic hull s = s) <=> conic s`,
  SIMP_TAC[HULL_EQ; CONIC_INTERS]);;

let CONIC_NEGATIONS = prove
 (`!s. conic s ==> conic (IMAGE (--) s)`,
  REWRITE_TAC[conic; RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE; VECTOR_MUL_RNEG] THEN MESON_TAC[]);;

let CONIC_SPAN = prove
 (`!s. conic(span s)`,
  SIMP_TAC[SUBSPACE_IMP_CONIC; SUBSPACE_SPAN]);;

let CONIC_HULL_EXPLICIT = prove
 (`!s:real^N->bool. conic hull s = {c % x | &0 <= c /\ x IN s}`,
  GEN_TAC THEN MATCH_MP_TAC HULL_UNIQUE THEN
  REWRITE_TAC[conic; SUBSET; RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`&1`; `x:real^N`] THEN
    ASM_SIMP_TAC[REAL_POS; VECTOR_MUL_LID];
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN MESON_TAC[REAL_LE_MUL];
    MESON_TAC[]]);;

let CONIC_HULL_LINEAR_IMAGE = prove
 (`!f s. linear f ==> conic hull (IMAGE f s) = IMAGE f (conic hull s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONIC_HULL_EXPLICIT] THEN
  REWRITE_TAC[SET_RULE `IMAGE f {c % x | P c x} = {f(c % x) | P c x}`] THEN
  REWRITE_TAC[SET_RULE `{c % x | &0 <= c /\ x IN IMAGE f s} =
                        {c % f(x) | &0 <= c /\ x IN s}`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]));;

add_linear_invariants [CONIC_HULL_LINEAR_IMAGE];;

let CONVEX_CONIC_HULL = prove
 (`!s:real^N->bool. convex s ==> convex (conic hull s)`,
  REWRITE_TAC[CONIC_HULL_EXPLICIT] THEN
  REWRITE_TAC[CONVEX_ALT; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_ELIM_THM; IMP_IMP] THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`d:real`; `y:real^N`] THEN STRIP_TAC THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_CASES_TAC `(&1 - u) * c = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
    ASM_MESON_TAC[REAL_LE_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 - u) * c + u * d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_ADD THEN ASM_REWRITE_TAC[REAL_LT_LE] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(&1 - u) * c + u * d:real` THEN
  EXISTS_TAC `((&1 - u) * c) / ((&1 - u) * c + u * d) % x +
              (u * d) / ((&1 - u) * c + u * d) % y:real^N` THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
  ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_SUB_LE] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `&0 < u + v ==> u / (u + v) = &1 - (v / (u + v))`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
  ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_LE_MUL; REAL_MUL_LID; REAL_LE_ADDL;
               REAL_SUB_LE]);;

let CONIC_HALFSPACE_LE = prove
 (`!a. conic {x | a dot x <= &0}`,
  REWRITE_TAC[conic; IN_ELIM_THM; DOT_RMUL] THEN
  REWRITE_TAC[REAL_ARITH `a <= &0 <=> &0 <= --a`] THEN
  SIMP_TAC[GSYM REAL_MUL_RNEG; REAL_LE_MUL]);;

let CONIC_HALFSPACE_GE = prove
 (`!a. conic {x | a dot x >= &0}`,
  SIMP_TAC[conic; IN_ELIM_THM; DOT_RMUL; real_ge; REAL_LE_MUL]);;

let CONIC_HULL_EMPTY = prove
 (`conic hull {} = {}`,
  MATCH_MP_TAC HULL_UNIQUE THEN
  REWRITE_TAC[SUBSET_REFL; CONIC_EMPTY; EMPTY_SUBSET]);;

let CONIC_CONTAINS_0 = prove
 (`!s:real^N->bool. conic s ==> (vec 0 IN s <=> ~(s = {}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [conic]) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `&0`]) THEN
  ASM_REWRITE_TAC[REAL_POS; VECTOR_MUL_LZERO]);;

let CONIC_HULL_EQ_EMPTY = prove
 (`!s. (conic hull s = {}) <=> (s = {})`,
  GEN_TAC THEN EQ_TAC THEN
  MESON_TAC[SUBSET_EMPTY; HULL_SUBSET; CONIC_HULL_EMPTY]);;

let CONIC_SUMS = prove
 (`!s t. conic s /\ conic t ==> conic {x + y:real^N | x IN s /\ y IN t}`,
  REWRITE_TAC[conic; IN_ELIM_THM] THEN
  MESON_TAC[VECTOR_ADD_LDISTRIB]);;

let CONIC_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        conic s /\ conic t ==> conic(s PCROSS t)`,
  REWRITE_TAC[conic; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  SIMP_TAC[FORALL_IN_PCROSS; GSYM PASTECART_CMUL; PASTECART_ADD] THEN
  SIMP_TAC[PASTECART_IN_PCROSS]);;

let CONIC_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        conic(s PCROSS t) <=> s = {} \/ t = {} \/ conic s /\ conic t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; CONIC_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; CONIC_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[CONIC_PCROSS] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
      `(s:real^M->bool) PCROSS (t:real^N->bool)`] CONIC_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART];
    MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
      `(s:real^M->bool) PCROSS (t:real^N->bool)`] CONIC_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

let CONIC_POSITIVE_ORTHANT = prove
 (`conic {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i}`,
  SIMP_TAC[conic; IN_ELIM_THM; REAL_LE_MUL; VECTOR_MUL_COMPONENT]);;

let SEPARATE_CLOSED_CONES = prove
 (`!c d:real^N->bool.
        conic c /\ closed c /\ conic d /\ closed d /\ c INTER d SUBSET {vec 0}
        ==> ?e. &0 < e /\
                !x y. x IN c /\ y IN d
                      ==> dist(x,y) >= e * max (norm x) (norm y)`,
  SUBGOAL_THEN
   `!c d:real^N->bool.
        conic c /\ closed c /\ conic d /\ closed d /\ c INTER d SUBSET {vec 0}
        ==> ?e. &0 < e /\
                !x y. x IN c /\ y IN d ==> dist(x,y)
                      >= e * norm x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[real_ge] THEN
    MP_TAC(ISPECL [`c INTER sphere(vec 0:real^N,&1)`; `d:real^N->bool`]
      SEPARATE_COMPACT_CLOSED) THEN
    ASM_SIMP_TAC[CLOSED_INTER_COMPACT; COMPACT_SPHERE] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `c INTER d SUBSET {a} ==> ~(a IN s) ==> (c INTER s) INTER d = {}`)) THEN
      REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
      REWRITE_TAC[IN_INTER; IN_SPHERE_0] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
      ASM_CASES_TAC `x:real^N = vec 0` THEN
      ASM_REWRITE_TAC[DIST_POS_LE; REAL_MUL_RZERO; NORM_0] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`inv(norm x) % x:real^N`; `inv(norm(x:real^N)) % y:real^N`]) THEN
      REWRITE_TAC[dist; NORM_MUL; GSYM VECTOR_SUB_LDISTRIB] THEN
      REWRITE_TAC[REAL_ARITH `abs x * a = a * abs x`] THEN
      REWRITE_TAC[REAL_ABS_INV; GSYM real_div; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; NORM_POS_LT] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; NORM_EQ_0] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[conic]) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; NORM_POS_LE]];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
      MP_TAC(SPECL [`c:real^N->bool`; `d:real^N->bool`] th) THEN
      MP_TAC(SPECL [`d:real^N->bool`; `c:real^N->bool`] th)) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; real_ge] THEN
    X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    EXISTS_TAC `min d e:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `d * norm(y:real^N)` THEN ONCE_REWRITE_TAC[DIST_SYM];
      EXISTS_TAC `e * norm(x:real^N)`] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN NORM_ARITH_TAC]);;

let CONTINUOUS_ON_COMPACT_SURFACE_PROJECTION = prove
 (`!s:real^N->bool v d:real^N->real.
        compact s /\ s SUBSET (v DELETE (vec 0)) /\ conic v /\
        (!x k. x IN v DELETE (vec 0) ==> (&0 < k /\ (k % x) IN s <=> d x = k))
        ==> (\x. d x % x) continuous_on (v DELETE (vec 0))`,
  let lemma = prove
   (`!s:real^N->real^N p srf:real^N->bool pnc.
          compact srf /\ srf SUBSET pnc /\
          IMAGE s pnc SUBSET srf /\ (!x. x IN srf ==> s x = x) /\
          p continuous_on pnc /\
          (!x. x IN pnc ==> s(p x) = s x /\ p(s x) = p x)
          ==> s continuous_on pnc`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `(s:real^N->real^N) o (p:real^N->real^N)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE (p:real^N->real^N) pnc = IMAGE p srf` SUBST1_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_INVERSE THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]]]) in
  REWRITE_TAC[conic; IN_DELETE; SUBSET] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN
  MAP_EVERY EXISTS_TAC [`\x:real^N. inv(norm x) % x`; `s:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN SIMP_TAC[o_DEF; CONTINUOUS_ON_ID] THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
    SIMP_TAC[IN_DELETE; NORM_EQ_0; SIMP_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM];
    REWRITE_TAC[IN_UNIV; IN_DELETE]] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `&1`]) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; REAL_LT_01; IN_DELETE] THEN
    ASM_MESON_TAC[VECTOR_MUL_LID; SUBSET; IN_DELETE];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL
     [`inv(norm x) % x:real^N`; `norm x * (d:real^N->real) x`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `(d:real^N->real) x`]) THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; NORM_EQ_0] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; NORM_POS_LE; REAL_LT_MUL; NORM_POS_LT] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; NORM_EQ_0; REAL_FIELD
     `~(n = &0) ==> (n * d) * inv n = d`];
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `(d:real^N->real) x`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[NORM_MUL; VECTOR_MUL_ASSOC; REAL_INV_MUL] THEN
    ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < x ==> (inv(x) * y) * x = y`]]);;

(* ------------------------------------------------------------------------- *)
(* Affine dependence and consequential theorems (from Lars Schewe).          *)
(* ------------------------------------------------------------------------- *)

let affine_dependent = new_definition
 `affine_dependent (s:real^N -> bool) <=>
        ?x. x IN s /\ x IN (affine hull (s DELETE x))`;;

let AFFINE_DEPENDENT_EXPLICIT = prove
 (`!p. affine_dependent (p:real^N -> bool) <=>
            (?s u. FINITE s /\ s SUBSET p /\
                   sum s u = &0 /\
                   (?v. v IN s /\ ~(u v = &0)) /\
                   vsum s (\v. u v % v) = (vec 0):real^N)`,
  X_GEN_TAC `p:real^N->bool` THEN EQ_TAC THENL
   [REWRITE_TAC[affine_dependent;AFFINE_HULL_EXPLICIT;
                IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `(x:real^N) INSERT s` THEN
    EXISTS_TAC `\v:real^N.if v = x then -- &1 else u v` THEN
      ASM_SIMP_TAC[FINITE_INSERT;SUM_CLAUSES;VSUM_CLAUSES;INSERT_SUBSET] THEN
      REPEAT CONJ_TAC THENL
      [ASM SET_TAC[];
       COND_CASES_TAC THENL [ASM SET_TAC[];ALL_TAC] THEN
         ASM_SIMP_TAC[SUM_CASES; SUM_CLAUSES; SET_RULE
          `~((x:real^N) IN s) ==> {v | v IN s /\ v = x} = {} /\
                                  {v | v IN s /\ ~(v = x)} = s`] THEN
         REAL_ARITH_TAC;
       SET_TAC[REAL_ARITH `~(-- &1 = &0)`];
       MP_TAC (SET_RULE `s SUBSET p DELETE (x:real^N) ==> ~(x IN s)`) THEN
       ASM_REWRITE_TAC[] THEN
       DISCH_TAC THEN
       ASM_SIMP_TAC[VECTOR_ARITH
        `(-- &1 % (x:real^N)) + a = vec 0 <=> a = x`] THEN
       MATCH_MP_TAC EQ_TRANS THEN
       EXISTS_TAC `vsum s (\v:real^N. u v % v)` THEN
       CONJ_TAC THENL [
       MATCH_MP_TAC VSUM_EQ THEN
         ASM_SIMP_TAC[] THEN
         ASM SET_TAC[];
       ASM_REWRITE_TAC[]]];
       ALL_TAC] THEN
    REWRITE_TAC[affine_dependent;AFFINE_HULL_EXPLICIT;IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `v:real^N` THEN
    CONJ_TAC THENL [ASM SET_TAC[];ALL_TAC] THEN
    EXISTS_TAC `s DELETE (v:real^N)` THEN
    EXISTS_TAC `\x:real^N. -- (&1 / (u v)) * u x` THEN
    ASM_SIMP_TAC[FINITE_DELETE;SUM_DELETE;VSUM_DELETE_CASES] THEN
    ASM_SIMP_TAC[SUM_LMUL;GSYM VECTOR_MUL_ASSOC;VSUM_LMUL;
            VECTOR_MUL_RZERO;VECTOR_ARITH `vec 0 - -- a % x = a % x:real^N`;
            REAL_MUL_RZERO;REAL_ARITH `&0 - -- a * b = a * b`] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(x = &0) ==> &1 / x * x = &1`;
                 VECTOR_MUL_ASSOC;VECTOR_MUL_LID] THEN
    CONJ_TAC THENL [ALL_TAC;ASM SET_TAC[]] THEN
    ASM_SIMP_TAC[SET_RULE `v IN s ==> (s DELETE v = {} <=> s = {v})`] THEN
    ASM_CASES_TAC `s = {v:real^N}` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIND_ASSUM MP_TAC `sum {v:real^N} u = &0` THEN
    REWRITE_TAC[SUM_SING]
    THEN ASM_REWRITE_TAC[]);;

let AFFINE_DEPENDENT_EXPLICIT_FINITE = prove
 (`!s. FINITE(s:real^N -> bool)
       ==> (affine_dependent s <=>
            ?u. sum s u = &0 /\
                (?v. v IN s /\ ~(u v = &0)) /\
                vsum s (\v. u v % v) = vec 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AFFINE_DEPENDENT_EXPLICIT] THEN
  EQ_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET_REFL]] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool`
   (X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\x:real^N. if x IN t then u(x) else &0` THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; VECTOR_MUL_LZERO] THEN
  ASM_SIMP_TAC[GSYM SUM_RESTRICT_SET; GSYM VSUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[SET_RULE `t SUBSET s ==> {x | x IN s /\ x IN t} = t`] THEN
  ASM SET_TAC[]);;

let AFFINE_DEPENDENT_TRANSLATION_EQ = prove
 (`!a s. affine_dependent (IMAGE (\x. a + x) s) <=> affine_dependent s`,
  REWRITE_TAC[affine_dependent] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [AFFINE_DEPENDENT_TRANSLATION_EQ];;

let AFFINE_DEPENDENT_TRANSLATION = prove
 (`!s a. affine_dependent s ==> affine_dependent (IMAGE (\x. a + x) s)`,
  REWRITE_TAC[AFFINE_DEPENDENT_TRANSLATION_EQ]);;

let AFFINE_DEPENDENT_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (affine_dependent(IMAGE f s) <=> affine_dependent s)`,
  REWRITE_TAC[affine_dependent] THEN GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [AFFINE_DEPENDENT_LINEAR_IMAGE_EQ];;

let AFFINE_DEPENDENT_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        affine_dependent(s)
        ==> affine_dependent(IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[affine_dependent; EXISTS_IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^M` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) s DELETE f a = IMAGE f (s DELETE a)`
   (fun t -> ASM_SIMP_TAC[FUN_IN_IMAGE; AFFINE_HULL_LINEAR_IMAGE; t]) THEN
  ASM SET_TAC[]);;

let AFFINE_DEPENDENT_MONO = prove
 (`!s t:real^N->bool. affine_dependent s /\ s SUBSET t ==> affine_dependent t`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[affine_dependent] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `x:real^N` THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HULL_MONO o SPEC `x:real^N` o MATCH_MP
   (SET_RULE `!x. s SUBSET t ==> (s DELETE x) SUBSET (t DELETE x)`)) THEN
  ASM SET_TAC[]);;

let AFFINE_INDEPENDENT_EMPTY = prove
 (`~(affine_dependent {})`,
  REWRITE_TAC[affine_dependent; NOT_IN_EMPTY]);;

let AFFINE_INDEPENDENT_1 = prove
 (`!a:real^N. ~(affine_dependent {a})`,
  REWRITE_TAC[affine_dependent; EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{a} DELETE a = {}`; AFFINE_HULL_EMPTY; NOT_IN_EMPTY]);;

let AFFINE_INDEPENDENT_2 = prove
 (`!a b:real^N. ~(affine_dependent {a,b})`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:real^N = a` THENL
   [ASM_REWRITE_TAC[INSERT_AC; AFFINE_INDEPENDENT_1];
    REWRITE_TAC[affine_dependent; EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_SIMP_TAC[SET_RULE
     `~(a = b) ==> {a,b} DELETE a = {b} /\ {a,b} DELETE b = {a}`] THEN
    ASM_REWRITE_TAC[AFFINE_HULL_SING; IN_SING]]);;

let AFFINE_INDEPENDENT_SUBSET = prove
 (`!s t. ~affine_dependent t /\ s SUBSET t ==> ~affine_dependent s`,
  REWRITE_TAC[IMP_CONJ_ALT; CONTRAPOS_THM] THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT; AFFINE_DEPENDENT_MONO]);;

let AFFINE_INDEPENDENT_DELETE = prove
 (`!s a. ~affine_dependent s ==> ~affine_dependent(s DELETE a)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] AFFINE_INDEPENDENT_SUBSET) THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Coplanarity, and collinearity in terms of affine hull.                    *)
(* ------------------------------------------------------------------------- *)

let coplanar = new_definition
 `coplanar s <=> ?u v w. s SUBSET affine hull {u,v,w}`;;

let COLLINEAR_AFFINE_HULL = prove
 (`!s:real^N->bool. collinear s <=> ?u v. s SUBSET affine hull {u,v}`,
  GEN_TAC THEN REWRITE_TAC[collinear; AFFINE_HULL_2] THEN EQ_TAC THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[REAL_ARITH `u + v = &1 <=> &1 - u = v`; UNWIND_THM1] THENL
   [X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN EXISTS_TAC `x + u:real^N` THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `x - y:real^N = z <=> x = y + z`] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` SUBST1_TAC) THEN
    EXISTS_TAC `&1 + c` THEN VECTOR_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
    EXISTS_TAC `b - a:real^N` THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `y:real^N` th) THEN MP_TAC(SPEC `x:real^N` th)) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `r:real` THEN DISCH_THEN SUBST1_TAC THEN
    X_GEN_TAC `s:real` THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `s - r:real` THEN VECTOR_ARITH_TAC]);;

let COLLINEAR_IMP_COPLANAR = prove
 (`!s. collinear s ==> coplanar s`,
  REWRITE_TAC[coplanar; COLLINEAR_AFFINE_HULL] THEN MESON_TAC[INSERT_AC]);;

let COPLANAR_SMALL = prove
 (`!s. FINITE s /\ CARD s <= 3 ==> coplanar s`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `s <= 3 <=> s <= 2 \/ s = 3`] THEN
  REWRITE_TAC[LEFT_OR_DISTRIB; GSYM HAS_SIZE] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN
  SIMP_TAC[COLLINEAR_IMP_COPLANAR; COLLINEAR_SMALL] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN REWRITE_TAC[coplanar] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[HULL_INC; SUBSET]);;

let COPLANAR_EMPTY = prove
 (`coplanar {}`,
  SIMP_TAC[COLLINEAR_IMP_COPLANAR; COLLINEAR_EMPTY]);;

let COPLANAR_SING = prove
 (`!a. coplanar {a}`,
  SIMP_TAC[COLLINEAR_IMP_COPLANAR; COLLINEAR_SING]);;

let COPLANAR_2 = prove
 (`!a b. coplanar {a,b}`,
  SIMP_TAC[COLLINEAR_IMP_COPLANAR; COLLINEAR_2]);;

let COPLANAR_3 = prove
 (`!a b c. coplanar {a,b,c}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC COPLANAR_SMALL THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_RULES] THEN ARITH_TAC);;

let COLLINEAR_AFFINE_HULL_COLLINEAR = prove
 (`!s. collinear(affine hull s) <=> collinear s`,
  REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
  MESON_TAC[HULL_HULL; HULL_MONO; HULL_INC; SUBSET]);;

let COPLANAR_AFFINE_HULL_COPLANAR = prove
 (`!s. coplanar(affine hull s) <=> coplanar s`,
  REWRITE_TAC[coplanar] THEN
  MESON_TAC[HULL_HULL; HULL_MONO; HULL_INC; SUBSET]);;

let COPLANAR_TRANSLATION_EQ = prove
 (`!a:real^N s. coplanar(IMAGE (\x. a + x) s) <=> coplanar s`,
  REWRITE_TAC[coplanar] THEN GEOM_TRANSLATE_TAC[]);;

let COPLANAR_TRANSLATION = prove
 (`!a:real^N s. coplanar s ==> coplanar(IMAGE (\x. a + x) s)`,
  REWRITE_TAC[COPLANAR_TRANSLATION_EQ]);;

add_translation_invariants [COPLANAR_TRANSLATION_EQ];;

let COPLANAR_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s. coplanar s /\ linear f ==> coplanar(IMAGE f s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[coplanar; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `c:real^M`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
  [`(f:real^M->real^N) a`; `(f:real^M->real^N) b`; `(f:real^M->real^N) c`] THEN
  REWRITE_TAC[SET_RULE `{f a,f b,f c} = IMAGE f {a,b,c}`] THEN
  ASM_SIMP_TAC[AFFINE_HULL_LINEAR_IMAGE; IMAGE_SUBSET]);;

let COPLANAR_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (coplanar (IMAGE f s) <=> coplanar s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE COPLANAR_LINEAR_IMAGE));;

add_linear_invariants [COPLANAR_LINEAR_IMAGE_EQ];;

let COPLANAR_SUBSET = prove
 (`!s t. coplanar t /\ s SUBSET t ==> coplanar s`,
  REWRITE_TAC[coplanar] THEN SET_TAC[]);;

let AFFINE_HULL_3_IMP_COLLINEAR = prove
 (`!a b c. c IN affine hull {a,b} ==> collinear {a,b,c}`,
  ONCE_REWRITE_TAC[GSYM COLLINEAR_AFFINE_HULL_COLLINEAR] THEN
  SIMP_TAC[HULL_REDUNDANT_EQ; INSERT_AC] THEN
  REWRITE_TAC[COLLINEAR_AFFINE_HULL_COLLINEAR; COLLINEAR_2]);;

let COLLINEAR_3_AFFINE_HULL = prove
 (`!a b c:real^N.
        ~(a = b) ==> (collinear {a,b,c} <=> c IN affine hull {a,b})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[AFFINE_HULL_3_IMP_COLLINEAR] THEN
  REWRITE_TAC[collinear] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPECL [`b:real^N`; `a:real^N`] th) THEN
                        MP_TAC(SPECL [`c:real^N`; `a:real^N`] th)) THEN
  REWRITE_TAC[IN_INSERT; AFFINE_HULL_2; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[VECTOR_ARITH `a - b:real^N = c <=> a = b + c`] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN X_GEN_TAC `y:real` THEN
  ASM_CASES_TAC `y = &0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`&1 - x / y`; `x / y:real`] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL] THEN VECTOR_ARITH_TAC);;

let COLLINEAR_3_EQ_AFFINE_DEPENDENT = prove
 (`!a b c:real^N.
        collinear{a,b,c} <=>
                a = b \/ a = c \/ b = c \/ affine_dependent {a,b,c}`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t ->
    ASM_CASES_TAC t THENL [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC])
   [`a:real^N = b`; `a:real^N = c`; `b:real^N = c`] THEN
  ASM_REWRITE_TAC[affine_dependent] THEN EQ_TAC THENL
   [ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL] THEN DISCH_TAC THEN
    EXISTS_TAC `c:real^N` THEN REWRITE_TAC[IN_INSERT];
    REWRITE_TAC[EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {b,c,a}`];
      ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {c,a,b}`];
      ALL_TAC] THEN
    ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `x IN s ==> s SUBSET t ==> x IN t`)) THEN
  MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]);;

let AFFINE_DEPENDENT_IMP_COLLINEAR_3 = prove
 (`!a b c:real^N. affine_dependent {a,b,c} ==> collinear{a,b,c}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[affine_dependent] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; RIGHT_OR_DISTRIB] THEN
  REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2; COLLINEAR_AFFINE_HULL] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`b:real^N`; `c:real^N`];
    MAP_EVERY EXISTS_TAC [`a:real^N`; `c:real^N`];
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`]] THEN
  SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET; HULL_INC; IN_INSERT] THEN
  POP_ASSUM MP_TAC THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> a IN s ==> a IN t`) THEN
  MATCH_MP_TAC HULL_MONO THEN SET_TAC[]);;

let COLLINEAR_3_IN_AFFINE_HULL = prove
 (`!v0 v1 x:real^N.
        ~(v1 = v0)
        ==> (collinear {v0,v1,x} <=> x IN affine hull {v0,v1})`,
  REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC `v0:real^N` THEN
  REWRITE_TAC[COLLINEAR_LEMMA; AFFINE_HULL_2] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; IN_ELIM_THM] THEN
  ASM_CASES_TAC `x:real^N = vec 0` THEN ASM_REWRITE_TAC[] THENL
   [MAP_EVERY EXISTS_TAC [`&1`; `&0`] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    VECTOR_ARITH_TAC;
    MESON_TAC[REAL_ARITH `u + v = &1 <=> u = &1 - v`]]);;

(* ------------------------------------------------------------------------- *)
(* A general lemma.                                                          *)
(* ------------------------------------------------------------------------- *)

let CONVEX_CONNECTED = prove
 (`!s:real^N->bool. convex s ==> connected s`,
  REWRITE_TAC[CONVEX_ALT; connected; SUBSET; EXTENSION; IN_INTER;
              IN_UNION; NOT_IN_EMPTY; NOT_FORALL_THM; NOT_EXISTS_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  MAP_EVERY (K(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) (1--4) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x1:real^N` STRIP_ASSUME_TAC)
                         (X_CHOOSE_THEN `x2:real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`\u. (&1 - u) % x1 + u % (x2:real^N)`;
                 `&0`; `&1`; `e1:real^N->bool`; `e2:real^N->bool`]
         (REWRITE_RULE[GSYM open_def] CONNECTED_REAL_LEMMA)) THEN
  ASM_REWRITE_TAC[NOT_IMP; REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
                  REAL_SUB_REFL; VECTOR_ADD_RID; VECTOR_ADD_LID; REAL_POS] THEN
  REPEAT(CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[dist] THEN
  REWRITE_TAC[NORM_MUL; VECTOR_ARITH
   `((&1 - a) % x + a % y) - ((&1 - b) % x + b % y) = (a - b) % (y - x)`] THEN
  MP_TAC(ISPEC `(x2 - x1):real^N` NORM_POS_LE) THEN
  REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[REAL_MUL_RZERO; REAL_LT_01]] THEN
  EXISTS_TAC `e / norm((x2 - x1):real^N)` THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_DIV]);;

(* ------------------------------------------------------------------------- *)
(* Various topological facts are queued up here, just because they rely on   *)
(* CONNECTED_UNIV, which is a trivial consequence of CONVEX_UNIV. It would   *)
(* be fairly easy to prove it earlier and move these back to the topology.ml *)
(* file, which is a bit tidier intellectually.                               *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_UNIV = prove
 (`connected (UNIV:real^N->bool)`,
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_UNIV]);;

let CONNECTED_COMPONENT_UNIV = prove
 (`!x. connected_component(:real^N) x = (:real^N)`,
  MESON_TAC[CONNECTED_CONNECTED_COMPONENT_SET; CONNECTED_UNIV; IN_UNIV]);;

let CONNECTED_COMPONENT_EQ_UNIV = prove
 (`!s x. connected_component s x = (:real^N) <=> s = (:real^N)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[CONNECTED_COMPONENT_UNIV] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s = UNIV ==> t = UNIV`) THEN
  REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]);;

let COMPONENTS_UNIV = prove
 (`components(:real^N) = {(:real^N)}`,
  REWRITE_TAC[COMPONENTS_EQ_SING; CONNECTED_UNIV; UNIV_NOT_EMPTY]);;

let CLOPEN = prove
 (`!s. closed s /\ open s <=> s = {} \/ s = (:real^N)`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[CLOSED_EMPTY; OPEN_EMPTY; CLOSED_UNIV; OPEN_UNIV] THEN
  MATCH_MP_TAC(REWRITE_RULE[CONNECTED_CLOPEN] CONNECTED_UNIV) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; GSYM CLOSED_IN]);;

let COMPACT_OPEN = prove
 (`!s:real^N->bool. compact s /\ open s <=> s = {}`,
  MESON_TAC[COMPACT_EMPTY; OPEN_EMPTY; COMPACT_IMP_CLOSED; CLOPEN;
            COMPACT_IMP_BOUNDED; NOT_BOUNDED_UNIV]);;

let FRONTIER_NOT_EMPTY = prove
 (`!s. ~(s = {}) /\ ~(s = (:real^N)) ==> ~(frontier s = {})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `s:real^N->bool`] CONNECTED_INTER_FRONTIER) THEN
  REWRITE_TAC[CONNECTED_UNIV] THEN ASM SET_TAC[]);;

let FRONTIER_EQ_EMPTY = prove
 (`!s. frontier s = {} <=> s = {} \/ s = (:real^N)`,
  MESON_TAC[FRONTIER_NOT_EMPTY; FRONTIER_EMPTY; FRONTIER_UNIV]);;

let EQ_INTERVAL = prove
 (`(!a b c d:real^N.
        interval[a,b] = interval[c,d] <=>
        interval[a,b] = {} /\ interval[c,d] = {} \/ a = c /\ b = d) /\
   (!a b c d:real^N.
        interval[a,b] = interval(c,d) <=>
        interval[a,b] = {} /\ interval(c,d) = {}) /\
   (!a b c d:real^N.
        interval(a,b) = interval[c,d] <=>
        interval(a,b) = {} /\ interval[c,d] = {}) /\
   (!a b c d:real^N.
        interval(a,b) = interval(c,d) <=>
        interval(a,b) = {} /\ interval(c,d) = {} \/ a = c /\ b = d)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  (EQ_TAC THENL [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]]) THEN
  MATCH_MP_TAC(MESON[]
   `(p = {} /\ q = {} ==> r) /\ (~(p = {}) /\ ~(q = {}) ==> p = q ==> r)
    ==> p = q ==> r`) THEN
  SIMP_TAC[] THENL
   [REWRITE_TAC[INTERVAL_NE_EMPTY; CART_EQ] THEN
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
    SIMP_TAC[SUBSET_INTERVAL; GSYM REAL_LE_ANTISYM];
    STRIP_TAC THEN MATCH_MP_TAC(MESON[CLOPEN]
     `closed s /\ open t /\ ~(s = {}) /\ ~(s = UNIV) ==> ~(s = t)`) THEN
    ASM_REWRITE_TAC[CLOSED_INTERVAL; OPEN_INTERVAL; NOT_INTERVAL_UNIV];
    STRIP_TAC THEN MATCH_MP_TAC(MESON[CLOPEN]
     `closed s /\ open t /\ ~(s = {}) /\ ~(s = UNIV) ==> ~(t = s)`) THEN
    ASM_REWRITE_TAC[CLOSED_INTERVAL; OPEN_INTERVAL; NOT_INTERVAL_UNIV];
    REWRITE_TAC[INTERVAL_NE_EMPTY; CART_EQ] THEN
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
    SIMP_TAC[SUBSET_INTERVAL; GSYM REAL_LE_ANTISYM]]);;

let CLOSED_INTERVAL_EQ = prove
 (`(!a b:real^N. closed(interval[a,b])) /\
   (!a b:real^N. closed(interval(a,b)) <=> interval(a,b) = {})`,
  REWRITE_TAC[CLOSED_INTERVAL] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[CLOSED_EMPTY] THEN
  MP_TAC(ISPEC `interval(a:real^N,b)` CLOPEN) THEN
  ASM_REWRITE_TAC[OPEN_INTERVAL] THEN
  MESON_TAC[BOUNDED_INTERVAL; NOT_BOUNDED_UNIV]);;

let OPEN_INTERVAL_EQ = prove
 (`(!a b:real^N. open(interval[a,b]) <=> interval[a,b] = {}) /\
   (!a b:real^N. open(interval(a,b)))`,
  REWRITE_TAC[OPEN_INTERVAL] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[CLOSED_EMPTY] THEN
  MP_TAC(ISPEC `interval[a:real^N,b]` CLOPEN) THEN
  ASM_REWRITE_TAC[CLOSED_INTERVAL] THEN
  MESON_TAC[BOUNDED_INTERVAL; NOT_BOUNDED_UNIV]);;

let COMPACT_INTERVAL_EQ = prove
 (`(!a b:real^N. compact(interval[a,b])) /\
   (!a b:real^N. compact(interval(a,b)) <=> interval(a,b) = {})`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_INTERVAL] THEN
  REWRITE_TAC[CLOSED_INTERVAL_EQ]);;

let CONNECTED_CHAIN = prove
 (`!f:(real^N->bool)->bool.
        (!s. s IN f ==> compact s /\ connected s) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> connected(INTERS f)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[INTERS_0; CONNECTED_UNIV] THEN
  ABBREV_TAC `c:real^N->bool = INTERS f` THEN
  SUBGOAL_THEN `compact(c:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC COMPACT_INTERS THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONNECTED_CLOSED_SET; COMPACT_IMP_CLOSED; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `b:real^N->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N->bool`; `b:real^N->bool`] SEPARATION_NORMAL) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?k:real^N->bool. k IN f` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?n:real^N->bool. open n /\ k SUBSET n` MP_TAC THENL
   [ASM_MESON_TAC[BOUNDED_SUBSET_BALL; COMPACT_IMP_BOUNDED; OPEN_BALL];
    REWRITE_TAC[UNIONS_SUBSET] THEN STRIP_TAC] THEN
  MP_TAC(ISPEC `k:real^N->bool` COMPACT_IMP_HEINE_BOREL) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC
   `(u UNION v:real^N->bool) INSERT {n DIFF s | s IN f}`) THEN
  REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_INSERT; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[OPEN_UNION; OPEN_DIFF; COMPACT_IMP_CLOSED; NOT_IMP] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_INSERT] THEN REWRITE_TAC[SUBSET] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ONCE_REWRITE_TAC[IN_UNION] THEN
    ASM_CASES_TAC `(x:real^N) IN c` THENL [ASM SET_TAC[]; DISJ2_TAC] THEN
    REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM] THEN
    UNDISCH_TAC `~((x:real^N) IN c)` THEN
    SUBST1_TAC(SYM(ASSUME `INTERS f:real^N->bool = c`)) THEN
    REWRITE_TAC[IN_INTERS; NOT_FORALL_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SUBSET_INSERT_DELETE] THEN
  SUBGOAL_THEN `FINITE(g DELETE (u UNION v:real^N->bool))` MP_TAC THENL
   [ASM_REWRITE_TAC[FINITE_DELETE];
    REWRITE_TAC[TAUT `p ==> ~q <=> ~(p /\ q)`]] THEN
  REWRITE_TAC[FINITE_SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?j:real^N->bool. j IN f /\
                     UNIONS(IMAGE (\s. n DIFF s) f') SUBSET (n DIFF j)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `f':(real^N->bool)->bool = {}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; EMPTY_SUBSET] THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?j:real^N->bool. j IN f' /\
                       UNIONS(IMAGE (\s. n DIFF s) f') SUBSET (n DIFF j)`
    MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET]] THEN
    SUBGOAL_THEN
     `!s t:real^N->bool. s IN f' /\ t IN f' ==> s SUBSET t \/ t SUBSET s`
    MP_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `~(f':(real^N->bool)->bool = {})` THEN
    UNDISCH_TAC `FINITE(f':(real^N->bool)->bool)` THEN
    SPEC_TAC(`f':(real^N->bool)->bool`,`f':(real^N->bool)->bool`) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[] THEN
    REWRITE_TAC[EXISTS_IN_INSERT; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_IN_INSERT] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY X_GEN_TAC [`i:real^N->bool`; `f:(real^N->bool)->bool`] THEN
    ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT; NOT_IN_EMPTY;
                    UNIONS_0; UNION_EMPTY; SUBSET_REFL] THEN
    DISCH_THEN(fun th -> REPEAT DISCH_TAC THEN MP_TAC th) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(n DIFF j) SUBSET (n DIFF i) \/
                  (n DIFF i:real^N->bool) SUBSET (n DIFF j)`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:real^N->bool` o CONJUNCT2) THEN
      ASM SET_TAC[];
      DISJ1_TAC THEN ASM SET_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `j:real^N->bool` THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j INTER k:real^N->bool) SUBSET (u UNION v)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `k SUBSET (u UNION v) UNION (n DIFF j)
      ==> (j INTER k) SUBSET (u UNION v)`) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS g :real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
     `UNIONS((u UNION v:real^N->bool) INSERT (g DELETE (u UNION v)))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC SUBSET_UNIONS THEN SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[UNIONS_INSERT] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected(j INTER k:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[SET_RULE `s SUBSET t ==> s INTER t = s`; INTER_COMM];
    REWRITE_TAC[connected] THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let CONNECTED_CHAIN_GEN = prove
 (`!f:(real^N->bool)->bool.
       (!s. s IN f ==> closed s /\ connected s) /\
       (?s. s IN f /\ compact s) /\
       (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
       ==> connected(INTERS f)`,
  GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `INTERS f = INTERS(IMAGE (\t:real^N->bool. s INTER t) f)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; INTERS_IMAGE] THEN ASM SET_TAC[];
    MATCH_MP_TAC CONNECTED_CHAIN THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[COMPACT_INTER_CLOSED] THEN
    CONJ_TAC THENL [X_GEN_TAC `t:real^N->bool`; ASM SET_TAC[]] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `s INTER t:real^N->bool = s \/ s INTER t = t`
     (DISJ_CASES_THEN SUBST1_TAC) THEN
    ASM SET_TAC[]]);;

let CONNECTED_NEST = prove
 (`!s. (!n. compact(s n) /\ connected(s n)) /\
       (!m n. m <= n ==> s n SUBSET s m)
       ==> connected(INTERS {s n | n IN (:num)})`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CONNECTED_CHAIN THEN
  ASM_SIMP_TAC[FORALL_IN_GSPEC; IN_UNIV; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC WLOG_LE THEN ASM_MESON_TAC[]);;

let CONNECTED_NEST_GEN = prove
 (`!s. (!n. closed(s n) /\ connected(s n)) /\ (?n. compact(s n)) /\
       (!m n. m <= n ==> s n SUBSET s m)
       ==> connected(INTERS {s n | n IN (:num)})`,
  GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC CONNECTED_CHAIN_GEN THEN
  ASM_SIMP_TAC[FORALL_IN_GSPEC; IN_UNIV; IMP_CONJ; RIGHT_FORALL_IMP_THM;
               EXISTS_IN_GSPEC] THEN
  MATCH_MP_TAC WLOG_LE THEN ASM_MESON_TAC[]);;

let EQ_BALLS = prove
 (`(!a a':real^N r r'.
      ball(a,r) = ball(a',r') <=> a = a' /\ r = r' \/ r <= &0 /\ r' <= &0) /\
   (!a a':real^N r r'.
      ball(a,r) = cball(a',r') <=> r <= &0 /\ r' < &0) /\
   (!a a':real^N r r'.
      cball(a,r) = ball(a',r') <=> r < &0 /\ r' <= &0) /\
   (!a a':real^N r r'.
      cball(a,r) = cball(a',r') <=> a = a' /\ r = r' \/ r < &0 /\ r' < &0)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT STRIP_TAC THEN
  (EQ_TAC THENL
    [ALL_TAC; REWRITE_TAC[EXTENSION; IN_BALL; IN_CBALL] THEN NORM_ARITH_TAC])
  THENL
   [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_BALLS] THEN NORM_ARITH_TAC;
    ONCE_REWRITE_TAC[EQ_SYM_EQ];
    ALL_TAC;
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_BALLS] THEN NORM_ARITH_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[CLOPEN; BOUNDED_BALL; NOT_BOUNDED_UNIV]
    `s = t ==> closed s /\ open t /\ bounded t ==> s = {} /\ t = {}`)) THEN
  REWRITE_TAC[OPEN_BALL; CLOSED_CBALL; BOUNDED_BALL;
              BALL_EQ_EMPTY; CBALL_EQ_EMPTY] THEN
  REAL_ARITH_TAC);;

let FINITE_CBALL = prove
 (`!a:real^N r. FINITE(cball(a,r)) <=> r <= &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[CBALL_EMPTY; REAL_LT_IMP_LE; FINITE_EMPTY] THEN
  ASM_CASES_TAC `r = &0` THEN
  ASM_REWRITE_TAC[CBALL_TRIVIAL; FINITE_SING; REAL_LE_REFL] THEN
  EQ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP EMPTY_INTERIOR_FINITE) THEN
  REWRITE_TAC[INTERIOR_CBALL; BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC);;

let FINITE_BALL = prove
 (`!a:real^N r. FINITE(ball(a,r)) <=> r <= &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r <= &0` THEN
  ASM_SIMP_TAC[BALL_EMPTY; REAL_LT_IMP_LE; FINITE_EMPTY] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        FINITE_IMP_NOT_OPEN)) THEN
  REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Minimal continua.                                                         *)
(* ------------------------------------------------------------------------- *)

let MINIMAL_CONTINUUM = prove
 (`!t s:real^N->bool.
        t SUBSET s /\ compact s /\ connected s
        ==> ?u. t SUBSET u /\ u SUBSET s /\ compact u /\ connected u /\
                !v. v SUBSET u /\ t SUBSET v /\ compact v /\ connected v
                    ==> v = u`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [EXISTS_TAC `{}:real^N->bool` THEN
    ASM_MESON_TAC[COMPACT_EMPTY; CONNECTED_EMPTY; SUBSET_EMPTY; EMPTY_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u:real^N->bool. t SUBSET u /\ connected u`;
                 `s:real^N->bool`]
        BROUWER_REDUCTION_THEOREM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN GEN_TAC THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET_INTERS] THEN ASM SET_TAC[];
      MATCH_MP_TAC CONNECTED_NEST THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SET_RULE `(v SUBSET u /\ p ==> v = u) <=>
                          (v SUBSET u /\ p ==> ~(v PSUBSET u))`] THEN
    GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Convex functions into the reals.                                          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("convex_on",(12,"right"));;

let convex_on = new_definition
  `f convex_on s <=>
        !x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
                  ==> f(u % x + v % y) <= u * f(x) + v * f(y)`;;

let CONVEX_ON_SUBSET = prove
 (`!f s t. f convex_on t /\ s SUBSET t ==> f convex_on s`,
  REWRITE_TAC[convex_on; SUBSET] THEN MESON_TAC[]);;

let CONVEX_ON_EQ = prove
 (`!f g s. convex s /\ (!x. x IN s ==> f x = g x) /\ f convex_on s
           ==> g convex_on s`,
  REWRITE_TAC[convex_on; convex] THEN MESON_TAC[]);;

let CONVEX_ON_CONST = prove
 (`!s a. (\x. a) convex_on s`,
  SIMP_TAC[convex_on; GSYM REAL_ADD_RDISTRIB; REAL_MUL_LID; REAL_LE_REFL]);;

let CONVEX_ADD = prove
 (`!s f g. f convex_on s /\ g convex_on s ==> (\x. f(x) + g(x)) convex_on s`,
  REWRITE_TAC[convex_on; AND_FORALL_THM] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL ORELSE GEN_TAC) THEN
  MATCH_MP_TAC(TAUT
    `(b /\ c ==> d) ==> (a ==> b) /\ (a ==> c) ==> a ==> d`) THEN
  REAL_ARITH_TAC);;

let CONVEX_CMUL = prove
 (`!s c f. &0 <= c /\ f convex_on s ==> (\x. c * f(x)) convex_on s`,
  SIMP_TAC[convex_on; REAL_LE_LMUL;
           REAL_ARITH `u * c * fx + v * c * fy = c * (u * fx + v * fy)`]);;

let CONVEX_MAX = prove
 (`!f g s. f convex_on s /\ g convex_on s
           ==> (\x. max (f x) (g x)) convex_on s`,
  REWRITE_TAC[convex_on; REAL_MAX_LE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

let CONVEX_LOWER = prove
 (`!f s x y. f convex_on s /\
             x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
             ==> f(u % x + v % y) <= max (f(x)) (f(y))`,
  REWRITE_TAC[convex_on] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  ASM_MESON_TAC[REAL_LE_ADD2; REAL_LE_LMUL; REAL_MAX_MAX]);;

let CONVEX_LOWER_SEGMENT = prove
 (`!f s a b x:real^N.
        f convex_on s /\ a IN s /\ b IN s /\ x IN segment[a,b]
        ==> f(x) <= max (f a) (f b)`,
  REWRITE_TAC[IN_SEGMENT] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONVEX_LOWER THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CONVEX_LOWER_SEGMENT_LT = prove
 (`!f s a b x:real^N.
        f convex_on s /\ a IN s /\ b IN s /\
        x IN segment[a,b] /\ ~(x = b) /\ f a < f b
        ==> f x < f b`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (STRIP_ASSUME_TAC o GSYM)) THEN
  FIRST_X_ASSUM(MP_TAC o
   SPECL [`a:real^N`; `b:real^N`; `&1 - u:real`; `u:real`] o
   GEN_REWRITE_RULE I [convex_on]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LET_TRANS) THEN
  REWRITE_TAC[REAL_ARITH `a + u * b < b <=> a < (&1 - u) * b`] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  ASM_CASES_TAC `u = &1` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  UNDISCH_TAC `~(x:real^N = b)` THEN EXPAND_TAC "x" THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[ASSUME `u = &1`] THEN
  VECTOR_ARITH_TAC);;

let CONVEX_LOCAL_GLOBAL_MINIMUM_SEGMENT = prove
 (`!f s x:real^N.
        f convex_on s /\ x IN s /\
        (!z. z IN s /\ ~(z = x)
             ==> ?y. y IN segment[x,z] /\ y IN s /\ ~(y = x) /\ f(x) <= f(y))
        ==> !z. z IN s ==> f(x) <= f(z)`,
  REWRITE_TAC[IN_OPEN_SEGMENT] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN
  ASM_CASES_TAC `z:real^N = x` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^N->real`; `s:real^N->bool`; `z:real^N`; `x:real^N`;
                 `y:real^N`] CONVEX_LOWER_SEGMENT_LT) THEN
  ASM_SIMP_TAC[REWRITE_RULE[SUBSET] SEGMENT_OPEN_SUBSET_CLOSED] THEN
  ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let CONVEX_LOCAL_GLOBAL_MINIMUM_GEN = prove
 (`!f s t x:real^N.
       f convex_on s /\ x IN t /\
       open_in (subtopology euclidean (affine hull s)) t /\
       t SUBSET s /\
       (!y. y IN t ==> f(x) <= f(y))
       ==> !y. y IN s ==> f(x) <= f(y)`,
  REWRITE_TAC[open_in] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CONVEX_LOCAL_GLOBAL_MINIMUM_SEGMENT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `x:real^N` th) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `x + min (&1) (d / &2 / norm(z - x:real^N)) % (z - x)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN
    EXISTS_TAC `min (&1) (d / &2 / norm(z - x:real^N))` THEN
    REWRITE_TAC[REAL_MIN_LE; REAL_LE_MIN; REAL_LE_REFL; REAL_POS] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_DIV; REAL_POS; NORM_POS_LE] THEN
    VECTOR_ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]);
    REWRITE_TAC[VECTOR_ARITH `x + a:real^N = x <=> a = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(min (&1) x = &0)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ];
    FIRST_X_ASSUM MATCH_MP_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
  ASM_SIMP_TAC[IN_AFFINE_ADD_MUL_DIFF; HULL_INC; AFFINE_AFFINE_HULL] THEN
  REWRITE_TAC[NORM_ARITH `dist(x + a:real^N,x) = norm a`] THEN
  ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LT_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 < x /\ x < d ==> abs(min (&1) x) < d`) THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 < x / y ==> &0 < x / &2 / y /\ x / &2 / y < x / y`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ]);;

let CONVEX_LOCAL_GLOBAL_MINIMUM = prove
 (`!f s t x:real^N.
       f convex_on s /\ x IN t /\ open t /\ t SUBSET s /\
       (!y. y IN t ==> f(x) <= f(y))
       ==> !y. y IN s ==> f(x) <= f(y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CONVEX_LOCAL_GLOBAL_MINIMUM_GEN THEN
  EXISTS_TAC `t:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_SUBSET THEN
  ASM_REWRITE_TAC[] THEN TRANS_TAC SUBSET_TRANS `s:real^N->bool` THEN
  ASM_REWRITE_TAC[HULL_SUBSET]);;

let CONVEX_DISTANCE = prove
 (`!s a. (\x. dist(a,x)) convex_on s`,
  REWRITE_TAC[convex_on; dist] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
   [GSYM VECTOR_MUL_LID] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[VECTOR_ARITH
   `(u + v) % z - (u % x + v % y) = u % (z - x) + v % (z - y)`] THEN
  ASM_MESON_TAC[NORM_TRIANGLE; NORM_MUL; REAL_ABS_REFL]);;

let CONVEX_NORM = prove
 (`!s:real^N->bool. norm convex_on s`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `vec 0:real^N`] CONVEX_DISTANCE) THEN
  REWRITE_TAC[DIST_0; ETA_AX]);;

let CONVEX_ON_COMPOSE_LINEAR = prove
 (`!f g:real^M->real^N s.
        f convex_on (IMAGE g s) /\ linear g ==> (f o g) convex_on s`,
  REWRITE_TAC[convex_on; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  ASM_SIMP_TAC[]);;

let CONVEX_ON_TRANSLATION = prove
 (`!f a:real^N.
        f convex_on (IMAGE (\x. a + x) s) <=> (\x. f(a + x)) convex_on s`,
  REWRITE_TAC[convex_on; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN
  REWRITE_TAC[VECTOR_ARITH
   `u % (a + x) + v % (a + y):real^N = (u + v) % a + u % x + v % y`] THEN
  SIMP_TAC[VECTOR_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Open and closed balls are convex and hence connected.                     *)
(* ------------------------------------------------------------------------- *)

let CONVEX_BALL = prove
 (`!x:real^N e. convex(ball(x,e))`,
  let lemma = REWRITE_RULE[convex_on; IN_UNIV]
   (ISPEC `(:real^N)` CONVEX_DISTANCE) in
  REWRITE_TAC[convex; IN_BALL] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) lemma o lhand o snd) THEN
  ASM_MESON_TAC[REAL_LET_TRANS; REAL_CONVEX_BOUND_LT]);;

let CONNECTED_BALL = prove
 (`!x:real^N e. connected(ball(x,e))`,
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_BALL]);;

let CONVEX_CBALL = prove
 (`!x:real^N e. convex(cball(x,e))`,
  REWRITE_TAC[convex; IN_CBALL; dist] THEN MAP_EVERY X_GEN_TAC
   [`x:real^N`; `e:real`; `y:real^N`; `z:real^N`; `u:real`; `v:real`] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[VECTOR_ARITH `a - b = &1 % a - b`] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[VECTOR_ARITH
   `(a + b) % x - (a % y + b % z) = a % (x - y) + b % (x - z)`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(u % (x - y)) + norm(v % (x - z):real^N)` THEN
  REWRITE_TAC[NORM_TRIANGLE; NORM_MUL] THEN
  MATCH_MP_TAC REAL_CONVEX_BOUND_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  ASM_SIMP_TAC[REAL_ARITH
   `&0 <= u /\ &0 <= v /\ (u + v = &1) ==> (abs(u) + abs(v) = &1)`]);;

let CONNECTED_CBALL = prove
 (`!x:real^N e. connected(cball(x,e))`,
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_CBALL]);;

let CONVEX_INTERMEDIATE_BALL = prove
 (`!a:real^N r t. ball(a,r) SUBSET t /\ t SUBSET cball(a,r) ==> convex t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONVEX_CONTAINS_OPEN_SEGMENT] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    SUBSET_TRANS)) THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN GEN_TAC THEN DISCH_THEN
   (MP_TAC o SPEC `a:real^N` o MATCH_MP DIST_DECREASES_OPEN_SEGMENT) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  REWRITE_TAC[IN_CBALL] THEN ASM_MESON_TAC[REAL_LTE_TRANS]);;

let FRONTIER_OF_CONNECTED_COMPONENT_SUBSET = prove
 (`!s c x:real^N. frontier(connected_component s x) SUBSET frontier s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[frontier; SUBSET; IN_DIFF] THEN
  X_GEN_TAC `y:real^N` THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `y IN s ==> s SUBSET t ==> y IN t`)) THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN REWRITE_TAC[CONNECTED_COMPONENT_SUBSET];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `ball(y:real^N,e) SUBSET connected_component s y`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
      ASM_REWRITE_TAC[CONNECTED_BALL; CENTRE_IN_BALL];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSURE_APPROACHABLE]) THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
      ASM_REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] (GSYM IN_BALL)] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
      REWRITE_TAC[IN_INTERIOR] THEN EXISTS_TAC `e:real` THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`; `y:real^N`]
        CONNECTED_COMPONENT_OVERLAP) THEN
      MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
      ASM_SIMP_TAC[] THEN ASM SET_TAC[]]]);;

let FRONTIER_OF_COMPONENTS_SUBSET = prove
 (`!s c:real^N->bool.
        c IN components s ==> frontier c SUBSET frontier s`,
  SIMP_TAC[components; FORALL_IN_GSPEC;
           FRONTIER_OF_CONNECTED_COMPONENT_SUBSET]);;

let FRONTIER_OF_COMPONENTS_CLOSED_COMPLEMENT = prove
 (`!s c. closed s /\ c IN components ((:real^N) DIFF s)
         ==> frontier c SUBSET s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FRONTIER_OF_COMPONENTS_SUBSET) THEN
  REWRITE_TAC[FRONTIER_COMPLEMENT] THEN
  ASM_MESON_TAC[FRONTIER_SUBSET_EQ; SUBSET_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* A couple of lemmas about components (see Newman IV, 3.3 and 3.4).         *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_UNION_CLOPEN_IN_COMPLEMENT = prove
 (`!s t u:real^N->bool.
        connected s /\ connected u /\ s SUBSET u /\
        open_in (subtopology euclidean (u DIFF s)) t /\
        closed_in (subtopology euclidean (u DIFF s)) t
        ==> connected (s UNION t)`,
  MAP_EVERY X_GEN_TAC
   [`c:real^N->bool`; `h:real^N->bool`; `s:real^N->bool`] THEN
  STRIP_TAC THEN
  REWRITE_TAC[CONNECTED_CLOSED_IN_EQ; NOT_EXISTS_THM] THEN
  MATCH_MP_TAC(MESON[]
   `!Q. (!x y. P x y <=> P y x) /\
        (!x y. P x y ==> Q x \/ Q y) /\
        (!x y. P x y /\ Q x ==> F)
        ==> (!x y. ~(P x y))`) THEN
  EXISTS_TAC `\x:real^N->bool. c SUBSET x` THEN
  CONJ_TAC THENL [MESON_TAC[INTER_COMM; UNION_COMM]; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THEN
  MAP_EVERY X_GEN_TAC [`h1:real^N->bool`; `h2:real^N->bool`] THENL
   [STRIP_TAC THEN UNDISCH_TAC `connected(c:real^N->bool)` THEN
    REWRITE_TAC[CONNECTED_CLOSED_IN; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o
      SPECL [`c INTER h1:real^N->bool`; `c INTER h2:real^N->bool`]) THEN
    MATCH_MP_TAC(TAUT
     `(p /\ q) /\ (~r ==> s) ==> ~(p /\ q /\ r) ==> s`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN CONJ_TAC THENL
     [UNDISCH_TAC
        `closed_in(subtopology euclidean (c UNION h)) (h1:real^N->bool)`;
      UNDISCH_TAC
        `closed_in(subtopology euclidean (c UNION h)) (h2:real^N->bool)`] THEN
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM SET_TAC[];
    STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [open_in]) THEN
    SUBGOAL_THEN `(h2:real^N->bool) SUBSET h` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `connected(s:real^N->bool)` THEN
    REWRITE_TAC[CONNECTED_CLOPEN] THEN
    DISCH_THEN(MP_TAC o SPEC `h2:real^N->bool`) THEN REWRITE_TAC[NOT_IMP] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    SUBGOAL_THEN `s:real^N->bool = (s DIFF c) UNION (c UNION h)`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_UNION THEN
      MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `(c UNION h) DIFF h2:real^N->bool = h1`
         (fun th -> ASM_REWRITE_TAC[th]) THEN ASM SET_TAC[];
        DISCH_TAC THEN MATCH_MP_TAC OPEN_IN_TRANS THEN
        EXISTS_TAC `h:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC
         `open_in(subtopology euclidean (c UNION h)) (h2:real^N->bool)` THEN
        REWRITE_TAC[OPEN_IN_OPEN] THEN MATCH_MP_TAC MONO_EXISTS THEN
        ASM SET_TAC[]];
      MATCH_MP_TAC CLOSED_IN_SUBTOPOLOGY_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_IN_TRANS THEN EXISTS_TAC `h:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `closed_in(subtopology euclidean (c UNION h)) (h2:real^N->bool)` THEN
      REWRITE_TAC[CLOSED_IN_CLOSED] THEN MATCH_MP_TAC MONO_EXISTS THEN
      ASM SET_TAC[]]]);;

let COMPONENT_COMPLEMENT_CONNECTED = prove
 (`!s u c:real^N->bool.
        connected s /\ connected u /\ s SUBSET u /\ c IN components (u DIFF s)
        ==> connected(u DIFF c)`,
  MAP_EVERY X_GEN_TAC
   [`a:real^N->bool`; `s:real^N->bool`; `c:real^N->bool`] THEN
  STRIP_TAC THEN UNDISCH_TAC `connected(a:real^N->bool)` THEN
  REWRITE_TAC[CONNECTED_CLOSED_IN_EQ; NOT_EXISTS_THM] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC
   [`h3:real^N->bool`; `h4:real^N->bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`a INTER h3:real^N->bool`; `a INTER h4:real^N->bool`]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
  EVERY_ASSUM(fun th -> try
        MP_TAC(CONJUNCT1(GEN_REWRITE_RULE I [closed_in] th))
        with Failure _ -> ALL_TAC) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `closed_in (subtopology euclidean (s DIFF c))
                           (h3:real^N->bool)` THEN
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM SET_TAC[];
    UNDISCH_TAC `closed_in (subtopology euclidean (s DIFF c))
                           (h4:real^N->bool)` THEN
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`s DIFF a:real^N->bool`; `c UNION h3:real^N->bool`;
               `c:real^N->bool`] COMPONENTS_MAXIMAL) THEN
    ASM_REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONNECTED_UNION_CLOPEN_IN_COMPLEMENT THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      ASM SET_TAC[];
      REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `s DIFF c DIFF h3:real^N->bool = h4` SUBST1_TAC THEN
      ASM SET_TAC[]];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`s DIFF a:real^N->bool`; `c UNION h4:real^N->bool`;
               `c:real^N->bool`] COMPONENTS_MAXIMAL) THEN
    ASM_REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONNECTED_UNION_CLOPEN_IN_COMPLEMENT THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      ASM SET_TAC[];
      REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `s DIFF c DIFF h4:real^N->bool = h3` SUBST1_TAC THEN
      ASM SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Condition for an open map's image to contain a ball.                      *)
(* ------------------------------------------------------------------------- *)

let BALL_SUBSET_OPEN_MAP_IMAGE = prove
 (`!f:real^M->real^N s a r.
        bounded s /\ f continuous_on closure s /\ open(IMAGE f (interior s)) /\
        a IN s /\ &0 < r /\ (!z. z IN frontier s ==> r <= norm(f z - f a))
        ==> ball(f(a),r) SUBSET IMAGE f s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ball((f:real^M->real^N) a,r)`;
                 `(:real^N) DIFF IMAGE (f:real^M->real^N) s`]
    CONNECTED_INTER_FRONTIER) THEN
  REWRITE_TAC[CONNECTED_BALL] THEN MATCH_MP_TAC(SET_RULE
   `~(b INTER s = {}) /\ b INTER f = {} ==>
    (~(b INTER (UNIV DIFF s) = {}) /\ ~(b DIFF (UNIV DIFF s) = {})
     ==> ~(b INTER f = {}))
    ==> b SUBSET s`) THEN
  REWRITE_TAC[FRONTIER_COMPLEMENT] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(f:real^M->real^N) a` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ASM SET_TAC[];
    REWRITE_TAC[SET_RULE `s INTER t = {} <=> !x. x IN t ==> ~(x IN s)`] THEN
    REWRITE_TAC[IN_BALL; REAL_NOT_LT]] THEN
  MP_TAC(ISPECL[`frontier(IMAGE (f:real^M->real^N) s)`; `(f:real^M->real^N) a`]
    DISTANCE_ATTAINS_INF) THEN
  REWRITE_TAC[FRONTIER_CLOSED; FRONTIER_EQ_EMPTY] THEN ANTS_TAC THENL
   [SIMP_TAC[DE_MORGAN_THM] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[NOT_BOUNDED_UNIV] `bounded s ==> ~(s = UNIV)`) THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `IMAGE (f:real^M->real^N) (closure s)` THEN
    SIMP_TAC[IMAGE_SUBSET; CLOSURE_SUBSET] THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[COMPACT_CLOSURE];
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [frontier]) THEN
  REWRITE_TAC[IN_DIFF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[CLOSURE_SEQUENTIAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num->real^N`
   (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[IN_IMAGE; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `z:num->real^M` THEN REWRITE_TAC[FORALL_AND_THM] THEN
  ONCE_REWRITE_TAC[GSYM FUN_EQ_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM COMPACT_CLOSURE]) THEN
  REWRITE_TAC[compact] THEN
  DISCH_THEN(MP_TAC o SPEC `z:num->real^M`) THEN
  ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`y:real^M`; `r:num->num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(((\n. (f:real^M->real^N)(z n)) o (r:num->num)) --> w) sequentially`
  MP_TAC THENL
   [MATCH_MP_TAC LIM_SUBSEQUENCE THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN REWRITE_TAC[GSYM o_ASSOC]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!n. ((z:num->real^M) o (r:num->num)) n IN s` MP_TAC THENL
   [ASM_REWRITE_TAC[o_THM];
    UNDISCH_THEN `((\n. (f:real^M->real^N) ((z:num->real^M) n)) --> w)
                  sequentially` (K ALL_TAC) THEN
    UNDISCH_THEN `!n. (z:num->real^M) n IN s` (K ALL_TAC)] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`(z:num->real^M) o (r:num->num)`, `z:num->real^M`) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `w = (f:real^M->real^N) y` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `(f:real^M->real^N) o (z:num->real^M)` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_CLOSURE_SEQUENTIALLY];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(f y - (f:real^M->real^N) a)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC; ASM_MESON_TAC[dist; NORM_SUB]] THEN
  ASM_REWRITE_TAC[frontier; IN_DIFF] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[interior; IN_ELIM_THM] THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) (interior s)` THEN
  ASM_SIMP_TAC[IMAGE_SUBSET; INTERIOR_SUBSET] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations on sets preserve convexity.                         *)
(* ------------------------------------------------------------------------- *)

let CONVEX_SCALING = prove
 (`!s c. convex s ==> convex (IMAGE (\x. c % x) s)`,
  REWRITE_TAC[convex; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
   `u % c % x + v % c % y = c % (u % x + v % y)`] THEN
  ASM_MESON_TAC[]);;

let CONVEX_SCALING_EQ = prove
 (`!s c. ~(c = &0) ==> (convex (IMAGE (\x. c % x) s) <=> convex s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[CONVEX_SCALING] THEN
  DISCH_THEN(MP_TAC o SPEC `inv c` o MATCH_MP CONVEX_SCALING) THEN
  ASM_SIMP_TAC[GSYM IMAGE_o; o_DEF; VECTOR_MUL_ASSOC;
               REAL_MUL_LINV; VECTOR_MUL_LID; IMAGE_ID]);;

let CONVEX_NEGATIONS = prove
 (`!s. convex s ==> convex (IMAGE (--) s)`,
  REWRITE_TAC[convex; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
   `u % --x + v % --y = --(u % x + v % y)`] THEN
  ASM_MESON_TAC[]);;

let CONVEX_SUMS = prove
 (`!s t. convex s /\ convex t ==> convex {x + y | x IN s /\ y IN t}`,
  REWRITE_TAC[convex; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
    `u % (a + b) + v % (c + d) = (u % a + v % c) + (u % b + v % d)`] THEN
  ASM_MESON_TAC[]);;

let CONVEX_DIFFERENCES = prove
 (`!s t. convex s /\ convex t ==> convex {x - y | x IN s /\ y IN t}`,
  REWRITE_TAC[convex; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
    `u % (a - b) + v % (c - d) = (u % a + v % c) - (u % b + v % d)`] THEN
  ASM_MESON_TAC[]);;

let CONVEX_AFFINITY = prove
 (`!s a:real^N c.
        convex s ==> convex (IMAGE (\x. a + c % x) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. a + c % x) = (\x. a + x) o (\x. c % x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  ASM_SIMP_TAC[IMAGE_o; CONVEX_TRANSLATION; CONVEX_SCALING]);;

let CONVEX_LINEAR_PREIMAGE = prove
 (`!f:real^M->real^N.
     linear f /\ convex s ==> convex {x | f(x) IN s}`,
  REWRITE_TAC[CONVEX_ALT; IN_ELIM_THM] THEN
  SIMP_TAC[LINEAR_ADD; LINEAR_CMUL]);;

(* ------------------------------------------------------------------------- *)
(* Some interesting "cancellation" properties for sum-sets.                  *)
(* ------------------------------------------------------------------------- *)

let SUBSET_SUMS_LCANCEL = prove
 (`!s t u:real^N->bool.
        ~(s = {}) /\ bounded s /\ closed u /\ convex u /\
        {x + y | x IN s /\ y IN t} SUBSET {x + z | x IN s /\ z IN u}
        ==> t SUBSET u`,
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN X_GEN_TAC `b:real^N` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. ?w z:real^N. w IN s /\ z IN u /\ (&n + &1) % (b - z) = w - a`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
      ASM_REWRITE_TAC[REAL_ADD_LID; VECTOR_MUL_LID] THEN
      REWRITE_TAC[VECTOR_ARITH `b - z:real^N = w - a <=> a + b = w + z`] THEN
      MESON_TAC[];
      FIRST_X_ASSUM(X_CHOOSE_THEN `a':real^N` (X_CHOOSE_THEN `c':real^N`
        STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a':real^N`; `b:real^N`]) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`a'':real^N`; `c'':real^N`] THEN STRIP_TAC THEN
      EXISTS_TAC `a'':real^N` THEN EXISTS_TAC
       `(&1 - &1 / (&n + &2)) % c' + &1 / (&n + &2) % c'':real^N` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CONVEX_ALT]) THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ;
                     REAL_ARITH `&0 < &n + &2`] THEN
        REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I
         [VECTOR_ARITH `a' + b:real^N = a'' + c <=> a'' = (a' + b) - c`]) THEN
        REWRITE_TAC[VECTOR_ARITH
         `(&n + &1) % (b - c):real^N = (a' + b) - c'' - a <=>
          &n % b - (&n + &1) % c = (a' - c'') - a`] THEN
        SIMP_TAC[GSYM REAL_OF_NUM_SUC; VECTOR_MUL_ASSOC; VECTOR_ADD_LDISTRIB;
                 REAL_ARITH `(n + &1) + &1 = n + &2`] THEN
        REWRITE_TAC[VECTOR_MUL_LID; REAL_FIELD
         `(&n + &2) * (&1 - (&1 / (&n + &2))) = &n + &1 /\
          (&n + &2) * &1 / (&n + &2) = &1`] THEN
        ASM_REWRITE_TAC[VECTOR_ARITH
         `n % b - (n % c + d):real^N = n % (b - c) - d`] THEN
        CONV_TAC VECTOR_ARITH]];
      FIRST_X_ASSUM(K ALL_TAC o check is_forall o concl) THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `s:real^N->bool`] BOUNDED_DIFFS) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[BOUNDED_POS; FORALL_IN_GSPEC] THEN
      DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
      DISCH_TAC THEN FIRST_X_ASSUM(fun th ->
        ONCE_REWRITE_TAC[GSYM(MATCH_MP CLOSED_APPROACHABLE th)]) THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(SPEC `e:real` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `B:real`) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; X_GEN_TAC `n:num`] THEN
      DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `c:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real^N` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
      EXISTS_TAC `abs(&n + &1)` THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[dist]] THEN
      ASM_REWRITE_TAC[GSYM NORM_MUL] THEN
      REWRITE_TAC[REAL_ARITH `abs(&n + &1) = &n + &1`] THEN
      ASM_MESON_TAC[REAL_LET_TRANS]]);;

let SUBSET_SUMS_RCANCEL = prove
 (`!s t u:real^N->bool.
        closed t /\ convex t /\ bounded u /\ ~(u = {}) /\
        {x + z | x IN s /\ z IN u} SUBSET {y + z | y IN t /\ z IN u}
        ==> s SUBSET t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_SUMS_LCANCEL THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[SUMS_SYM] THEN ASM_REWRITE_TAC[]);;

let EQ_SUMS_LCANCEL = prove
 (`!s t u.
        ~(s = {}) /\ bounded s /\
        closed t /\ convex t /\ closed u /\ convex u /\
        {x + y | x IN s /\ y IN t} = {x + z | x IN s /\ z IN u}
        ==> t = u`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; EMPTY_SUBSET] THEN
  REWRITE_TAC[SUBSET_EMPTY] THEN MESON_TAC[SUBSET_SUMS_LCANCEL]);;

let EQ_SUMS_RCANCEL = prove
 (`!s t u.
        closed s /\ convex s /\ closed t /\ convex t /\
        bounded u /\ ~(u = {}) /\
        {x + z | x IN s /\ z IN u} = {y + z | y IN t /\ z IN u}
        ==> s = t`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; EMPTY_SUBSET] THEN
  REWRITE_TAC[SUBSET_EMPTY] THEN MESON_TAC[SUBSET_SUMS_RCANCEL]);;

(* ------------------------------------------------------------------------- *)
(* Convex hull.                                                              *)
(* ------------------------------------------------------------------------- *)

let CONVEX_CONVEX_HULL = prove
 (`!s. convex(convex hull s)`,
  SIMP_TAC[P_HULL; CONVEX_INTERS]);;

let CONVEX_HULL_EQ = prove
 (`!s. (convex hull s = s) <=> convex s`,
  SIMP_TAC[HULL_EQ; CONVEX_INTERS]);;

let CONVEX_HULLS_EQ = prove
 (`!s t. s SUBSET convex hull t /\ t SUBSET convex hull s
         ==> convex hull s = convex hull t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULLS_EQ THEN
  ASM_SIMP_TAC[CONVEX_INTERS]);;

let IS_CONVEX_HULL = prove
 (`!s. convex s <=> ?t. s = convex hull t`,
  GEN_TAC THEN MATCH_MP_TAC IS_HULL THEN SIMP_TAC[CONVEX_INTERS]);;

let MIDPOINTS_IN_CONVEX_HULL = prove
 (`!x:real^N s. x IN convex hull s /\ y IN convex hull s
         ==> midpoint(x,y) IN convex hull s`,
  MESON_TAC[MIDPOINT_IN_CONVEX; CONVEX_CONVEX_HULL]);;

let CONVEX_HULL_UNIV = prove
 (`convex hull (:real^N) = (:real^N)`,
  REWRITE_TAC[CONVEX_HULL_EQ; CONVEX_UNIV]);;

let BOUNDED_CONVEX_HULL = prove
 (`!s:real^N->bool. bounded s ==> bounded(convex hull s)`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [bounded] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `cball(vec 0:real^N,B)` THEN
  SIMP_TAC[BOUNDED_CBALL; SUBSET_HULL; CONVEX_CBALL] THEN
  ASM_REWRITE_TAC[IN_CBALL; SUBSET; dist; VECTOR_SUB_LZERO; NORM_NEG]);;

let BOUNDED_CONVEX_HULL_EQ = prove
 (`!s. bounded(convex hull s) <=> bounded s`,
  MESON_TAC[BOUNDED_CONVEX_HULL; HULL_SUBSET; BOUNDED_SUBSET]);;

let FINITE_IMP_BOUNDED_CONVEX_HULL = prove
 (`!s. FINITE s ==> bounded(convex hull s)`,
  SIMP_TAC[BOUNDED_CONVEX_HULL; FINITE_IMP_BOUNDED]);;

(* ------------------------------------------------------------------------- *)
(* Stepping theorems for convex hulls of finite sets.                        *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_EMPTY = prove
 (`convex hull {} = {}`,
  MATCH_MP_TAC HULL_UNIQUE THEN
  REWRITE_TAC[SUBSET_REFL; CONVEX_EMPTY; EMPTY_SUBSET]);;

let CONVEX_HULL_EQ_EMPTY = prove
 (`!s. (convex hull s = {}) <=> (s = {})`,
  GEN_TAC THEN EQ_TAC THEN
  MESON_TAC[SUBSET_EMPTY; HULL_SUBSET; CONVEX_HULL_EMPTY]);;

let CONVEX_HULL_SING = prove
 (`!a. convex hull {a} = {a}`,
  REWRITE_TAC[CONVEX_HULL_EQ; CONVEX_SING]);;

let CONVEX_HULL_EQ_SING = prove
 (`!s a:real^N. convex hull s = {a} <=> s = {a}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[CONVEX_HULL_EMPTY] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[CONVEX_HULL_SING] THEN
  MATCH_MP_TAC(SET_RULE `~(s = {}) /\ s SUBSET {a} ==> s = {a}`) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[HULL_SUBSET]);;

let CONVEX_HULL_INSERT = prove
 (`!s a. ~(s = {})
         ==> (convex hull (a INSERT s) =
                {x:real^N | ?u v b. &0 <= u /\ &0 <= v /\ (u + v = &1) /\
                                    b IN (convex hull s) /\
                                    (x = u % a + v % b)})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THENL
       [MAP_EVERY EXISTS_TAC [`&1`; `&0`];
        MAP_EVERY EXISTS_TAC [`&0`; `&1`]] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO] THEN
      ASM_REWRITE_TAC[VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_MESON_TAC[MEMBER_NOT_EMPTY; HULL_SUBSET; SUBSET];
      ALL_TAC];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[convex] CONVEX_CONVEX_HULL) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[HULL_SUBSET; SUBSET; IN_INSERT; HULL_MONO]] THEN
  REWRITE_TAC[convex; IN_ELIM_THM] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`x:real^N`; `y:real^N`; `u:real`; `v:real`; `u1:real`; `v1:real`;
    `b1:real^N`; `u2:real`; `v2:real`; `b2:real^N`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`u * u1 + v * u2`; `u * v1 + v * v2`] THEN
  REWRITE_TAC[VECTOR_ARITH
   `u % (u1 % a + v1 % b1) + v % (u2 % a + v2 % b2) =
    (u * u1 + v * u2) % a + (u * v1) % b1 + (v * v2) % b2`] THEN
  ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID; REAL_ARITH
   `(u * u1 + v * u2) + (u * v1 + v * v2) =
    u * (u1 + v1) + v * (u2 + v2)`] THEN
  ASM_CASES_TAC `u * v1 + v * v2 = &0` THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `(a + b = &0) ==> &0 <= a /\ &0 <= b ==> (a = &0) /\ (b = &0)`)) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_ADD_LID; VECTOR_MUL_LZERO;
                 VECTOR_ADD_RID] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(u * v1) / (u * v1 + v * v2) % b1 +
              (v * v2) / (u * v1 + v * v2) % b2 :real^N` THEN
  ASM_SIMP_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; REAL_DIV_LMUL] THEN
  MATCH_MP_TAC(REWRITE_RULE[convex] CONVEX_CONVEX_HULL) THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_LE_ADD] THEN
  ASM_SIMP_TAC[real_div; GSYM REAL_ADD_RDISTRIB; REAL_MUL_RINV]);;

let CONVEX_HULL_INSERT_ALT = prove
 (`!s a:real^N.
      convex hull (a INSERT s) =
      if s = {} then {a}
      else {(&1 - u) % a + u % x | &0 <= u /\ u <= &1 /\ x IN convex hull s}`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[CONVEX_HULL_SING] THEN
  ASM_SIMP_TAC[CONVEX_HULL_INSERT] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> b /\ c /\ a /\ d`] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2; REAL_SUB_LE;
              REAL_ARITH `u + v = &1 <=> u = &1 - v`] THEN
  SET_TAC[]);;

let CONVEX_HULL_INSERT_SEGMENTS = prove
 (`!s a:real^N.
        convex hull (a INSERT s) =
        if s = {} then {a} else  UNIONS {segment[a,x] | x IN convex hull s}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONVEX_HULL_INSERT_ALT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[UNIONS_GSPEC; IN_SEGMENT] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Explicit expression for convex hull.                                      *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_INDEXED = prove
 (`!s. convex hull s =
        {y:real^N | ?k u x. (!i. 1 <= i /\ i <= k ==> &0 <= u i /\ x i IN s) /\
                            (sum (1..k) u = &1) /\
                            (vsum (1..k) (\i. u i % x i) = y)}`,
  GEN_TAC THEN MATCH_MP_TAC HULL_UNIQUE THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`1`; `\i:num. &1`; `\i:num. x:real^N`] THEN
    ASM_SIMP_TAC[FINITE_RULES; IN_SING; SUM_SING; VECTOR_MUL_LID; VSUM_SING;
                 REAL_POS; NUMSEG_SING];
    ALL_TAC;
    REWRITE_TAC[CONVEX_INDEXED; SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MESON_TAC[]] THEN
  REWRITE_TAC[convex; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`k1:num`; `u1:num->real`; `x1:num->real^N`;
    `k2:num`; `u2:num->real`; `x2:num->real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `k1 + k2:num` THEN
  EXISTS_TAC `\i:num. if i <= k1 then u * u1(i) else v * u2(i - k1):real` THEN
  EXISTS_TAC `\i:num. if i <= k1 then x1(i) else x2(i - k1):real^N` THEN
  ASM_SIMP_TAC[NUMSEG_ADD_SPLIT; ARITH_RULE `1 <= x + 1 /\ x < x + 1`;
   IN_NUMSEG; SUM_UNION; VSUM_UNION; FINITE_NUMSEG; DISJOINT_NUMSEG;
   ARITH_RULE `k1 + 1 <= i ==> ~(i <= k1)`] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] NUMSEG_OFFSET_IMAGE] THEN
  ASM_SIMP_TAC[SUM_IMAGE; VSUM_IMAGE; EQ_ADD_LCANCEL; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[o_DEF; ADD_SUB2; SUM_LMUL; VSUM_LMUL; GSYM VECTOR_MUL_ASSOC;
               FINITE_NUMSEG; REAL_MUL_RID] THEN
  ASM_MESON_TAC[REAL_LE_MUL; ARITH_RULE
    `i <= k1 + k2 /\ ~(i <= k1) ==> 1 <= i - k1 /\ i - k1 <= k2`]);;

(* ------------------------------------------------------------------------- *)
(* Another formulation from Lars Schewe.                                     *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_EXPLICIT = prove
  (`!p. convex hull p =
        {y:real^N | ?s u. FINITE s /\ s SUBSET p /\
             (!x. x IN s ==> &0 <= u x) /\
             sum s u = &1 /\ vsum s (\v. u v % v) = y}`,
   REWRITE_TAC[CONVEX_HULL_INDEXED;EXTENSION;IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MAP_EVERY  EXISTS_TAC [`IMAGE (x':num->real^N) (1..k)`;
                           `\v:real^N.sum {i | i IN (1..k) /\ x' i = v} u`]
    THEN ASM_SIMP_TAC[FINITE_IMAGE;FINITE_NUMSEG;IN_IMAGE] THEN
    REPEAT STRIP_TAC THENL
    [REWRITE_TAC[IMAGE;SUBSET;IN_ELIM_THM;IN_NUMSEG] THEN
       ASM_MESON_TAC[];
     MATCH_MP_TAC SUM_POS_LE THEN
       ASM_SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;IN_ELIM_THM;IN_NUMSEG];
     ASM_SIMP_TAC[GSYM SUM_IMAGE_GEN;FINITE_IMAGE;FINITE_NUMSEG];
     FIRST_X_ASSUM (fun th -> REWRITE_TAC[GSYM th]) THEN
     ASM_SIMP_TAC[GSYM VSUM_IMAGE_GEN;FINITE_IMAGE;
                  FINITE_NUMSEG;VSUM_VMUL;FINITE_RESTRICT] THEN
       MP_TAC (ISPECL [`x':num->real^N`;`\i:num.u i % (x' i):real^N`;`(1..k)`]
                      (GSYM VSUM_IMAGE_GEN)) THEN
       ASM_SIMP_TAC[FINITE_NUMSEG]];ALL_TAC] THEN
   STRIP_ASSUME_TAC (ASM_REWRITE_RULE [ASSUME `FINITE (s:real^N->bool)`]
    (ISPEC `s:real^N->bool` FINITE_INDEX_NUMSEG)) THEN
   MAP_EVERY EXISTS_TAC [`CARD (s:real^N->bool)`;
                         `(u:real^N->real) o (f:num->real^N)`;
                         `(f:num->real^N)`] THEN
   REPEAT STRIP_TAC THENL
   [REWRITE_TAC[o_DEF] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM SUBST1_TAC THEN
      REWRITE_TAC[IN_IMAGE;IN_NUMSEG] THEN
      ASM_MESON_TAC[];
    MATCH_MP_TAC (REWRITE_RULE [SUBSET]
      (ASSUME `(s:real^N->bool) SUBSET p`)) THEN
      FIRST_ASSUM SUBST1_TAC THEN
      REWRITE_TAC[IN_IMAGE;IN_NUMSEG] THEN
      ASM_MESON_TAC[];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum (s:real^N->bool) u` THEN
      CONJ_TAC THENL [ALL_TAC;ASM_REWRITE_TAC[]] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
       [ASSUME `(s:real^N->bool) = IMAGE f (1..CARD s)`] THEN
      MATCH_MP_TAC (GSYM SUM_IMAGE) THEN
      ASM_MESON_TAC[];
    REWRITE_TAC[MESON [o_THM;FUN_EQ_THM]
     `(\i:num. (u o f) i % f i) = (\v:real^N. u v % v) o f`] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `vsum (s:real^N->bool) (\v. u v % v)` THEN
      CONJ_TAC THENL [ALL_TAC;ASM_REWRITE_TAC[]] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
       [ASSUME `(s:real^N->bool) = IMAGE f (1..CARD s)`] THEN
      MATCH_MP_TAC (GSYM VSUM_IMAGE) THEN
      ASM SET_TAC[FINITE_NUMSEG]]);;

let CONVEX_HULL_FINITE = prove
 (`!s:real^N->bool.
        convex hull s =
          {y | ?u. (!x. x IN s ==> &0 <= u x) /\
                   sum s u = &1 /\
                   vsum s (\x. u x % x) = y}`,
  GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `f:real^N->real`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `\x:real^N. if x IN t then f x else &0` THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; VECTOR_MUL_LZERO] THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET; GSYM VSUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC[SET_RULE `t SUBSET s ==> {x | x IN s /\ x IN t} = t`] THEN
    REWRITE_TAC[REAL_LE_REFL; COND_ID];
    X_GEN_TAC `f:real^N->real` THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[SUM_CLAUSES; REAL_OF_NUM_EQ; ARITH] THEN STRIP_TAC THEN
    EXISTS_TAC `support (+) (f:real^N->real) s` THEN
    EXISTS_TAC `f:real^N->real` THEN
    MP_TAC(ASSUME `sum s (f:real^N->real) = &1`) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [sum] THEN
    REWRITE_TAC[iterate] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[NEUTRAL_REAL_ADD; REAL_OF_NUM_EQ; ARITH] THEN
    DISCH_THEN(K ALL_TAC) THEN
    UNDISCH_TAC `sum s (f:real^N->real) = &1` THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM SUM_SUPPORT] THEN
    ASM_CASES_TAC `support (+) (f:real^N->real) s = {}` THEN
    ASM_SIMP_TAC[SUM_CLAUSES; REAL_OF_NUM_EQ; ARITH] THEN
    DISCH_TAC THEN REWRITE_TAC[SUPPORT_SUBSET] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[support; IN_ELIM_THM]; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    REWRITE_TAC[SUPPORT_SUBSET] THEN
    REWRITE_TAC[support; IN_ELIM_THM; NEUTRAL_REAL_ADD] THEN
    MESON_TAC[VECTOR_MUL_LZERO]]);;

let CONVEX_HULL_UNION_EXPLICIT = prove
 (`!s t:real^N->bool.
        convex s /\ convex t
        ==> convex hull (s UNION t) =
             s UNION t UNION
             {(&1 - u) % x + u % y | x IN s /\ y IN t /\ &0 <= u /\ u <= &1}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_EXPLICIT] THEN GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:real^N`; `u:real^N->bool`; `f:real^N->real`] THEN
    REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    SUBST1_TAC(SET_RULE `u:real^N->bool = (u INTER s) UNION (u DIFF s)`) THEN
    ASM_SIMP_TAC[SUM_UNION; VSUM_UNION; FINITE_INTER; FINITE_DIFF;
                 SET_RULE `DISJOINT (u INTER s) (u DIFF s)`] THEN
    ASM_CASES_TAC `sum (u INTER s) (f:real^N->real) = &0` THENL
     [SUBGOAL_THEN `!x. x IN (u INTER s) ==> (f:real^N->real) x = &0`
      ASSUME_TAC THENL
       [ASM_MESON_TAC[SUM_POS_EQ_0; FINITE_INTER; IN_INTER];
        ASM_SIMP_TAC[VECTOR_MUL_LZERO; VSUM_0] THEN
        REWRITE_TAC[VECTOR_ADD_LID; REAL_ADD_LID] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
        REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN DISJ1_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_EXPLICIT]) THEN
        ASM_SIMP_TAC[FINITE_DIFF; IN_DIFF] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `sum (u DIFF s) (f:real^N->real) = &0` THENL
     [SUBGOAL_THEN `!x. x IN (u DIFF s) ==> (f:real^N->real) x = &0`
      ASSUME_TAC THENL
       [ASM_MESON_TAC[SUM_POS_EQ_0; FINITE_DIFF; IN_DIFF];
        ASM_SIMP_TAC[VECTOR_MUL_LZERO; VSUM_0] THEN
        REWRITE_TAC[VECTOR_ADD_RID; REAL_ADD_RID] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
        REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_EXPLICIT]) THEN
        ASM_SIMP_TAC[FINITE_INTER; IN_INTER] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN DISJ2_TAC THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`vsum(u INTER s) (\v:real^N. (f v / sum(u INTER s) f) % v)`;
      `sum(u DIFF s) (f:real^N->real)`;
      `vsum(u DIFF s) (\v:real^N. (f v / sum(u DIFF s) f) % v)`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_EXPLICIT]) THEN
      ASM_SIMP_TAC[INTER_SUBSET; FINITE_INTER; SUM_POS_LE; REAL_LE_DIV;
                   IN_INTER; real_div; SUM_RMUL; REAL_MUL_RINV];
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_EXPLICIT]) THEN
      ASM_SIMP_TAC[SUBSET_DIFF; FINITE_DIFF; SUM_POS_LE; REAL_LE_DIV;
                   IN_DIFF; real_div; SUM_RMUL; REAL_MUL_RINV] THEN
      ASM SET_TAC[];
      ASM_SIMP_TAC[SUM_POS_LE; IN_DIFF; FINITE_DIFF];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `a + b = &1 ==> &0 <= a ==> b <= &1`)) THEN
      ASM_SIMP_TAC[SUM_POS_LE; IN_INTER; FINITE_INTER];
      ASM_SIMP_TAC[GSYM VSUM_LMUL; FINITE_INTER; FINITE_DIFF] THEN
      SIMP_TAC[VECTOR_MUL_ASSOC; REAL_ARITH `a * b / c:real = a / c * b`] THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `a + b = &1 ==> &1 - b = a`)) THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; REAL_MUL_LID]];
    REWRITE_TAC[GSYM UNION_ASSOC] THEN ONCE_REWRITE_TAC[UNION_SUBSET] THEN
    REWRITE_TAC[HULL_SUBSET] THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `u:real`; `y:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] CONVEX_CONVEX_HULL) THEN
    ASM_SIMP_TAC[HULL_INC; IN_UNION]]);;

let CONVEX_HULL_UNION_NONEMPTY_EXPLICIT = prove
 (`!s t:real^N->bool.
        convex s /\ ~(s = {}) /\ convex t /\ ~(t = {})
        ==> convex hull (s UNION t) =
             {(&1 - u) % x + u % y | x IN s /\ y IN t /\ &0 <= u /\ u <= &1}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CONVEX_HULL_UNION_EXPLICIT] THEN
  SIMP_TAC[SET_RULE `s UNION t UNION u = u <=> s SUBSET u /\ t SUBSET u`] THEN
  CONJ_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^N` THEN
  DISCH_TAC THENL
   [MAP_EVERY EXISTS_TAC [`z:real^N`; `&0`] THEN
    REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; REAL_POS; VECTOR_MUL_LZERO;
                VECTOR_ADD_RID] THEN
    ASM SET_TAC[];
    SUBGOAL_THEN `?a:real^N. a IN s` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`&1`; `z:real^N`] THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN VECTOR_ARITH_TAC]);;

let CONVEX_HULL_UNION_UNIONS = prove
 (`!f s:real^N->bool.
        convex(UNIONS f) /\ ~(f = {})
        ==> convex hull (s UNION UNIONS f) =
            UNIONS {convex hull (s UNION t) | t IN f}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_SIMP_TAC[UNION_EMPTY; HULL_P; UNIONS_SUBSET] THEN
    X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull u:real^N->bool` THEN
    REWRITE_TAC[HULL_SUBSET] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `UNIONS f :real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[UNION_EMPTY] THEN
    SUBGOAL_THEN `?u:real^N->bool. u IN f` CHOOSE_TAC THENL
     [ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `convex hull (s UNION u:real^N->bool)` THEN
    ASM_SIMP_TAC[HULL_MONO; SUBSET_UNION] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [HULL_UNION_LEFT] THEN
  ASM_SIMP_TAC[CONVEX_HULL_UNION_NONEMPTY_EXPLICIT; CONVEX_HULL_EQ_EMPTY;
               CONVEX_CONVEX_HULL] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_UNIONS] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `u:real^N->bool`] THEN DISCH_TAC THEN
  X_GEN_TAC `y:real^N` THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] CONVEX_CONVEX_HULL) THEN
  ASM_MESON_TAC[HULL_MONO; IN_UNION; SUBSET; HULL_INC]);;

(* ------------------------------------------------------------------------- *)
(* A stepping theorem for that expansion.                                    *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_FINITE_STEP = prove
 (`((?u. (!x. x IN {} ==> &0 <= u x) /\
         sum {} u = w /\
         vsum {} (\x. u(x) % x) = y) <=> w = &0 /\ y = vec 0) /\
   (FINITE(s:real^N->bool)
    ==> ((?u. (!x. x IN (a INSERT s) ==> &0 <= u x) /\
              sum (a INSERT s) u = w /\
              vsum (a INSERT s) (\x. u(x) % x) = y) <=>
         ?v. &0 <= v /\
             ?u. (!x. x IN s ==> &0 <= u x) /\
              sum s u = w - v /\
              vsum s (\x. u(x) % x) = y - v % a))`,
  MP_TAC(ISPEC `\x:real^N y:real. &0 <= y` AFFINE_HULL_FINITE_STEP_GEN) THEN
  SIMP_TAC[REAL_ARITH `&0 <= x / &2 <=> &0 <= x`; REAL_LE_ADD] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM]);;

(* ------------------------------------------------------------------------- *)
(* Hence some special cases.                                                 *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_2 = prove
 (`!a b. convex hull {a,b} =
         {u % a + v % b | &0 <= u /\ &0 <= v /\ u + v = &1}`,
  SIMP_TAC[CONVEX_HULL_FINITE; FINITE_INSERT; FINITE_RULES] THEN
  SIMP_TAC[CONVEX_HULL_FINITE_STEP; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[REAL_ARITH `x - y = z:real <=> x = y + z`;
              VECTOR_ARITH `x - y = z:real^N <=> x = y + z`] THEN
  REWRITE_TAC[VECTOR_ADD_RID; REAL_ADD_RID] THEN SET_TAC[]);;

let CONVEX_HULL_2_ALT = prove
 (`!a b. convex hull {a,b} = {a + u % (b - a) | &0 <= u /\ u <= &1}`,
  ONCE_REWRITE_TAC[SET_RULE `{a,b} = {b,a}`] THEN
  REWRITE_TAC[CONVEX_HULL_2; EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[REAL_ADD_ASSOC; CONJ_ASSOC] THEN
  REWRITE_TAC[TAUT `(a /\ x + y = &1) /\ b <=> x + y = &1 /\ a /\ b`] THEN
  REWRITE_TAC[REAL_ARITH `x + y = &1 <=> y = &1 - x`; UNWIND_THM2] THEN
  REPEAT GEN_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  BINOP_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let CONVEX_HULL_3 = prove
 (`convex hull {a,b,c} =
    { u % a + v % b + w % c |
      &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1}`,
  SIMP_TAC[CONVEX_HULL_FINITE; FINITE_INSERT; FINITE_RULES] THEN
  SIMP_TAC[CONVEX_HULL_FINITE_STEP; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[REAL_ARITH `x - y = z:real <=> x = y + z`;
              VECTOR_ARITH `x - y = z:real^N <=> x = y + z`] THEN
  REWRITE_TAC[VECTOR_ADD_RID; REAL_ADD_RID] THEN SET_TAC[]);;

let CONVEX_HULL_3_ALT = prove
 (`!a b c. convex hull {a,b,c} =
                {a + u % (b - a) + v % (c - a) |
                   &0 <= u /\ &0 <= v /\ u + v <= &1}`,
  ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {b,c,a}`] THEN
  REWRITE_TAC[CONVEX_HULL_3; EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[REAL_ADD_ASSOC; CONJ_ASSOC] THEN
  REWRITE_TAC[TAUT `(a /\ x + y = &1) /\ b <=> x + y = &1 /\ a /\ b`] THEN
  REWRITE_TAC[REAL_ARITH `x + y = &1 <=> y = &1 - x`; UNWIND_THM2] THEN
  REPEAT GEN_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  BINOP_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let CONVEX_HULL_SUMS = prove
 (`!s t:real^N->bool.
        convex hull {x + y | x IN s /\ y IN t} =
        {x + y | x IN convex hull s /\ y IN convex hull t}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN
    SIMP_TAC[CONVEX_SUMS; CONVEX_CONVEX_HULL] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[HULL_INC];
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [CONVEX_HULL_INDEXED] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`k1:num`; `u1:num->real`; `x1:num->real^N`;
      `k2:num`; `u2:num->real`; `x2:num->real^N`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `x + y:real^N =
      vsum(1..k1) (\i. vsum(1..k2) (\j. u1 i % u2 j % (x1 i + x2 j)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_LDISTRIB; VSUM_ADD_NUMSEG] THEN
      ASM_SIMP_TAC[VSUM_LMUL; VSUM_RMUL; VECTOR_MUL_LID];
      REWRITE_TAC[VSUM_LMUL] THEN MATCH_MP_TAC CONVEX_VSUM THEN
      ASM_SIMP_TAC[FINITE_NUMSEG; CONVEX_CONVEX_HULL; IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_VSUM THEN
      ASM_SIMP_TAC[FINITE_NUMSEG; CONVEX_CONVEX_HULL; IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]]]);;

let AFFINE_HULL_PCROSS,CONVEX_HULL_PCROSS = (CONJ_PAIR o prove)
 (`(!s:real^M->bool t:real^N->bool.
        affine hull (s PCROSS t) =
        (affine hull s) PCROSS (affine hull t)) /\
   (!s:real^M->bool t:real^N->bool.
        convex hull (s PCROSS t) =
        (convex hull s) PCROSS (convex hull t))`,
  let lemma1 = prove
   (`!u v x y:real^M z:real^N.
       u + v = &1
          ==> pastecart z (u % x + v % y) =
              u % pastecart z x + v % pastecart z y /\
              pastecart (u % x + v % y) z =
              u % pastecart x z + v % pastecart y z`,
    REWRITE_TAC[PASTECART_ADD; GSYM PASTECART_CMUL] THEN
    SIMP_TAC[GSYM VECTOR_ADD_RDISTRIB; VECTOR_MUL_LID])
  and lemma2 = prove
   (`INTERS {{x | pastecart x y IN u} | y IN t} =
     {x | !y. y IN t ==> pastecart x y IN u}`,
    REWRITE_TAC[INTERS_GSPEC; EXTENSION; IN_ELIM_THM] THEN SET_TAC[]) in
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN
      SIMP_TAC[AFFINE_PCROSS; AFFINE_AFFINE_HULL; HULL_SUBSET; PCROSS_MONO];
      REWRITE_TAC[SUBSET; FORALL_IN_PCROSS] THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      MATCH_MP_TAC HULL_INDUCT THEN CONJ_TAC THENL
       [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
        MATCH_MP_TAC HULL_INDUCT THEN CONJ_TAC THENL
         [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
          SUBGOAL_THEN `pastecart (x:real^M) (y:real^N) IN s PCROSS t` MP_TAC
          THENL [ASM_REWRITE_TAC[PASTECART_IN_PCROSS]; ALL_TAC] THEN
          REWRITE_TAC[HULL_INC];
          ALL_TAC];
        REWRITE_TAC[GSYM lemma2] THEN MATCH_MP_TAC AFFINE_INTERS THEN
        REWRITE_TAC[FORALL_IN_GSPEC]] THEN
      SIMP_TAC[affine; IN_ELIM_THM; lemma1;
               ONCE_REWRITE_RULE[affine] AFFINE_AFFINE_HULL]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN
      SIMP_TAC[CONVEX_PCROSS; CONVEX_CONVEX_HULL; HULL_SUBSET; PCROSS_MONO];
      REWRITE_TAC[SUBSET; FORALL_IN_PCROSS] THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      MATCH_MP_TAC HULL_INDUCT THEN CONJ_TAC THENL
       [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
        MATCH_MP_TAC HULL_INDUCT THEN CONJ_TAC THENL
         [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
          SUBGOAL_THEN `pastecart (x:real^M) (y:real^N) IN s PCROSS t` MP_TAC
          THENL [ASM_REWRITE_TAC[PASTECART_IN_PCROSS]; ALL_TAC] THEN
          REWRITE_TAC[HULL_INC];
          ALL_TAC];
        REWRITE_TAC[GSYM lemma2] THEN MATCH_MP_TAC CONVEX_INTERS THEN
        REWRITE_TAC[FORALL_IN_GSPEC]] THEN
      SIMP_TAC[convex; IN_ELIM_THM; lemma1;
               ONCE_REWRITE_RULE[convex] CONVEX_CONVEX_HULL]]]);;

(* ------------------------------------------------------------------------- *)
(* Relations among closure notions and corresponding hulls.                  *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_IMP_AFFINE = prove
 (`!s. subspace s ==> affine s`,
  REWRITE_TAC[subspace; affine] THEN MESON_TAC[]);;

let AFFINE_IMP_CONVEX = prove
 (`!s. affine s ==> convex s`,
  REWRITE_TAC[affine; convex] THEN MESON_TAC[]);;

let SUBSPACE_IMP_CONVEX = prove
 (`!s. subspace s ==> convex s`,
  MESON_TAC[SUBSPACE_IMP_AFFINE; AFFINE_IMP_CONVEX]);;

let AFFINE_HULL_SUBSET_SPAN = prove
 (`!s. (affine hull s) SUBSET (span s)`,
  GEN_TAC THEN REWRITE_TAC[span] THEN MATCH_MP_TAC HULL_ANTIMONO THEN
  REWRITE_TAC[SUBSET; IN; SUBSPACE_IMP_AFFINE]);;

let CONVEX_HULL_SUBSET_SPAN = prove
 (`!s. (convex hull s) SUBSET (span s)`,
  GEN_TAC THEN REWRITE_TAC[span] THEN MATCH_MP_TAC HULL_ANTIMONO THEN
  REWRITE_TAC[SUBSET; IN; SUBSPACE_IMP_CONVEX]);;

let CONVEX_HULL_SUBSET_AFFINE_HULL = prove
 (`!s. (convex hull s) SUBSET (affine hull s)`,
  GEN_TAC THEN REWRITE_TAC[span] THEN MATCH_MP_TAC HULL_ANTIMONO THEN
  REWRITE_TAC[SUBSET; IN; AFFINE_IMP_CONVEX]);;

let COLLINEAR_CONVEX_HULL_COLLINEAR = prove
 (`!s:real^N->bool. collinear(convex hull s) <=> collinear s`,
  MESON_TAC[COLLINEAR_SUBSET; HULL_SUBSET; SUBSET_TRANS;
            COLLINEAR_AFFINE_HULL_COLLINEAR; CONVEX_HULL_SUBSET_AFFINE_HULL]);;

let AFFINE_SPAN = prove
 (`!s. affine(span s)`,
  SIMP_TAC[SUBSPACE_IMP_AFFINE; SUBSPACE_SPAN]);;

let CONVEX_SPAN = prove
 (`!s. convex(span s)`,
  SIMP_TAC[SUBSPACE_IMP_CONVEX; SUBSPACE_SPAN]);;

let AFFINE_EQ_SUBSPACE = prove
 (`!s:real^N->bool. vec 0 IN s ==> (affine s <=> subspace s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[subspace; affine] THEN
  DISCH_TAC THEN MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN STRIP_TAC THEN
    SUBST1_TAC(VECTOR_ARITH `c % x:real^N = c % x + (&1 - c) % vec 0`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
    STRIP_TAC THEN SUBST1_TAC(VECTOR_ARITH
     `x + y:real^N = &2 % (&1 / &2 % x + &1 / &2 % y)`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let AFFINE_IMP_SUBSPACE = prove
 (`!s. affine s /\ vec 0 IN s ==> subspace s`,
  SIMP_TAC[GSYM AFFINE_EQ_SUBSPACE]);;

let AFFINE_HULL_EQ_SPAN = prove
 (`!s:real^N->bool. (vec 0) IN affine hull s ==> affine hull s = span s`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[AFFINE_HULL_SUBSET_SPAN] THEN
  REWRITE_TAC[SUBSET] THEN MATCH_MP_TAC SPAN_INDUCT THEN
  ASM_REWRITE_TAC[SUBSET; subspace; IN_ELIM_THM; HULL_INC] THEN
  REPEAT STRIP_TAC THENL
   [SUBST1_TAC(VECTOR_ARITH
     `x + y:real^N = &2 % (&1 / &2 % x + &1 / &2 % y) + --(&1) % vec 0`) THEN
    MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    SUBST1_TAC(VECTOR_ARITH
     `c % x:real^N = c % x + (&1 - c) % vec 0`) THEN
    MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let CLOSED_AFFINE = prove
 (`!s:real^N->bool. affine s ==> closed s`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[CLOSED_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  SUBGOAL_THEN `affine (IMAGE (\x:real^N. --a + x) s)
                ==> closed (IMAGE (\x:real^N. --a + x) s)`
  MP_TAC THENL
   [DISCH_THEN(fun th -> MATCH_MP_TAC CLOSED_SUBSPACE THEN MP_TAC th) THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC AFFINE_EQ_SUBSPACE THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `a:real^N` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[AFFINE_TRANSLATION_EQ; CLOSED_TRANSLATION_EQ]]);;

let CLOSED_AFFINE_HULL = prove
 (`!s. closed(affine hull s)`,
  SIMP_TAC[CLOSED_AFFINE; AFFINE_AFFINE_HULL]);;

let CLOSURE_SUBSET_AFFINE_HULL = prove
 (`!s. closure s SUBSET affine hull s`,
  GEN_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
  REWRITE_TAC[CLOSED_AFFINE_HULL; HULL_SUBSET]);;

let AFFINE_HULL_CLOSURE = prove
 (`!s:real^N->bool. affine hull (closure s) = affine hull s`,
  GEN_TAC THEN MATCH_MP_TAC HULL_UNIQUE THEN
  REWRITE_TAC[CLOSURE_SUBSET_AFFINE_HULL; AFFINE_AFFINE_HULL] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET]);;

let AFFINE_HULL_EQ_SPAN_EQ = prove
 (`!s:real^N->bool. (affine hull s = span s) <=> (vec 0) IN affine hull s`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[SPAN_0; AFFINE_HULL_EQ_SPAN]);;

let AFFINE_DEPENDENT_IMP_DEPENDENT = prove
 (`!s. affine_dependent s ==> dependent s`,
  REWRITE_TAC[affine_dependent; dependent] THEN
  MESON_TAC[SUBSET; AFFINE_HULL_SUBSET_SPAN]);;

let DEPENDENT_AFFINE_DEPENDENT_CASES = prove
 (`!s:real^N->bool.
        dependent s <=> affine_dependent s \/ (vec 0) IN affine hull s`,
  REWRITE_TAC[DEPENDENT_EXPLICIT; AFFINE_DEPENDENT_EXPLICIT;
              AFFINE_HULL_EXPLICIT_ALT; IN_ELIM_THM] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[OR_EXISTS_THM] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `t:real^N->bool` THEN
  ASM_CASES_TAC `FINITE(t:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN
   (X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC))
  THENL
   [ASM_CASES_TAC `sum t (u:real^N->real) = &0` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISJ2_TAC THEN EXISTS_TAC `\v:real^N. inv(sum t u) * u v` THEN
    ASM_SIMP_TAC[SUM_LMUL; VSUM_LMUL; GSYM VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[VECTOR_MUL_RZERO; REAL_MUL_LINV];
    EXISTS_TAC `u:real^N->real` THEN ASM_MESON_TAC[];
    EXISTS_TAC `u:real^N->real` THEN
    ASM_REWRITE_TAC[SET_RULE
     `(?v. v IN t /\ ~p v) <=> ~(!v. v IN t ==> p v)`] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x = &1 ==> x = &0 ==> F`)) THEN
    ASM_MESON_TAC[SUM_EQ_0]]);;

let DEPENDENT_IMP_AFFINE_DEPENDENT = prove
 (`!a:real^N s. dependent {x - a | x IN s} /\ ~(a IN s)
                ==> affine_dependent(a INSERT s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[DEPENDENT_EXPLICIT; AFFINE_DEPENDENT_EXPLICIT] THEN
  REWRITE_TAC[SIMPLE_IMAGE; CONJ_ASSOC; FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SWAP_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `a /\ x = IMAGE f s /\ b <=> x = IMAGE f s /\ a /\ b`] THEN
  REWRITE_TAC[UNWIND_THM2; EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` (X_CHOOSE_THEN `t:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  ASM_SIMP_TAC[VSUM_IMAGE; VECTOR_ARITH `x - a:real^N = y - a <=> x = y`] THEN
  ASM_SIMP_TAC[o_DEF; VECTOR_SUB_LDISTRIB; VSUM_SUB; VSUM_RMUL] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(a:real^N) INSERT t`;
    `\x. if x = a then --sum t (\x. u (x - a))
         else (u:real^N->real) (x - a)`] THEN
  ASM_REWRITE_TAC[FINITE_INSERT; SUBSET_REFL] THEN
  ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x = y ==> --x + y = &0`) THEN
    MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[];
    EXISTS_TAC `x:real^N` THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC(VECTOR_ARITH
     `!s. s - t % a = vec 0 /\ s = u ==> --t % a + u = vec 0`) THEN
    EXISTS_TAC `vsum t (\x:real^N. u(x - a) % x)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC VSUM_EQ THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let AFFINE_DEPENDENT_BIGGERSET = prove
 (`!s:real^N->bool.
        (FINITE s ==> CARD s >= dimindex(:N) + 2) ==> affine_dependent s`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[CARD_CLAUSES; ARITH_RULE `~(0 >= n + 2)`; FINITE_RULES] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `x IN s ==> s = x INSERT (s DELETE x)`)) THEN
  SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; IN_DELETE] THEN
  REWRITE_TAC[ARITH_RULE `SUC x >= n + 2 <=> x > n`] THEN DISCH_TAC THEN
  MATCH_MP_TAC DEPENDENT_IMP_AFFINE_DEPENDENT THEN
  REWRITE_TAC[IN_DELETE] THEN MATCH_MP_TAC DEPENDENT_BIGGERSET THEN
  REWRITE_TAC[SET_RULE `{x - a:real^N | x | x IN s /\ ~(x = a)} =
                        IMAGE (\x. x - a) (s DELETE a)`] THEN
  ASM_SIMP_TAC[FINITE_IMAGE_INJ_EQ;
               VECTOR_ARITH `x - a = y - a <=> x:real^N = y`;
               CARD_IMAGE_INJ]);;

let AFFINE_DEPENDENT_BIGGERSET_GENERAL = prove
 (`!s:real^N->bool. (FINITE s ==> CARD s >= dim s + 2) ==> affine_dependent s`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[CARD_CLAUSES; ARITH_RULE `~(0 >= n + 2)`; FINITE_RULES] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `x IN s ==> s = x INSERT (s DELETE x)`)) THEN
  SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; IN_DELETE] THEN
  REWRITE_TAC[ARITH_RULE `SUC x >= n + 2 <=> x > n`] THEN DISCH_TAC THEN
  MATCH_MP_TAC DEPENDENT_IMP_AFFINE_DEPENDENT THEN
  REWRITE_TAC[IN_DELETE] THEN
  MATCH_MP_TAC DEPENDENT_BIGGERSET_GENERAL THEN
  REWRITE_TAC[SET_RULE `{x - a:real^N | x | x IN s /\ ~(x = a)} =
                        IMAGE (\x. x - a) (s DELETE a)`] THEN
  ASM_SIMP_TAC[FINITE_IMAGE_INJ_EQ; FINITE_DELETE;
               VECTOR_ARITH `x - a = y - a <=> x:real^N = y`;
               CARD_IMAGE_INJ] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check(is_imp o concl)) THEN
  ASM_REWRITE_TAC[FINITE_DELETE] THEN
  MATCH_MP_TAC(ARITH_RULE `c:num <= b ==> (a > b ==> a > c)`) THEN
  MATCH_MP_TAC SUBSET_LE_DIM THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  SIMP_TAC[SPAN_SUB; SPAN_SUPERSET; IN_INSERT]);;

let AFFINE_INDEPENDENT_IMP_FINITE = prove
 (`!s:real^N->bool. ~(affine_dependent s) ==> FINITE s`,
  MESON_TAC[AFFINE_DEPENDENT_BIGGERSET]);;

let AFFINE_INDEPENDENT_CARD_LE = prove
 (`!s:real^N->bool. ~(affine_dependent s) ==> CARD s <= dimindex(:N) + 1`,
  REWRITE_TAC[ARITH_RULE `s <= n + 1 <=> ~(n + 2 <= s)`; CONTRAPOS_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC AFFINE_DEPENDENT_BIGGERSET THEN
  ASM_REWRITE_TAC[GE]);;

let AFFINE_INDEPENDENT_CONVEX_AFFINE_HULL = prove
 (`!s t:real^N->bool.
        ~affine_dependent s /\ t SUBSET s
        ==> convex hull t = affine hull t INTER convex hull s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  SUBGOAL_THEN `FINITE(t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `ct SUBSET a /\ ct SUBSET cs /\ a INTER cs SUBSET ct
    ==> ct = a INTER cs`) THEN
  ASM_SIMP_TAC[HULL_MONO; CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
  REWRITE_TAC[SUBSET; IN_INTER; CONVEX_HULL_FINITE; AFFINE_HULL_FINITE] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `v:real^N->real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `u:real^N->real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
    [AFFINE_DEPENDENT_EXPLICIT]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`;
        `\x:real^N. if x IN t then v x - u x:real else v x`]) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN REWRITE_TAC[MESON[]
   `(if p then a else b) % x = if p then a % x else b % x`] THEN
  ASM_SIMP_TAC[VSUM_CASES; SUM_CASES; SET_RULE
   `t SUBSET s ==> {x | x IN s /\ x IN t} = t`] THEN
  ASM_SIMP_TAC[GSYM DIFF; SUM_DIFF; VSUM_DIFF; VECTOR_SUB_RDISTRIB;
               SUM_SUB; VSUM_SUB] THEN
  REWRITE_TAC[REAL_ARITH `a - b + b - a = &0`; NOT_EXISTS_THM;
              VECTOR_ARITH `a - b + b - a:real^N = vec 0`] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  ASM_REWRITE_TAC[REAL_SUB_0] THEN ASM SET_TAC[]);;

let DISJOINT_AFFINE_HULL = prove
 (`!s t u:real^N->bool.
        ~affine_dependent s /\ t SUBSET s /\ u SUBSET s /\ DISJOINT t u
        ==> DISJOINT (affine hull t) (affine hull u)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  SUBGOAL_THEN `FINITE(t:real^N->bool) /\ FINITE (u:real^N->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[IN_DISJOINT; AFFINE_HULL_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `a:real^N->real` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `b:real^N->real` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
    [AFFINE_DEPENDENT_EXPLICIT]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY EXISTS_TAC
   [`s:real^N->bool`;
    `\x:real^N. if x IN t then a x else if x IN u then --(b x) else &0`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN REWRITE_TAC[MESON[]
   `(if p then a else b) % x = if p then a % x else b % x`] THEN
  ASM_SIMP_TAC[SUM_CASES; SUBSET_REFL; VSUM_CASES; GSYM DIFF; SUM_DIFF;
      VSUM_DIFF; SET_RULE `t SUBSET s ==> {x | x IN s /\ x IN t} = t`] THEN
  ASM_SIMP_TAC[SUM_0; VSUM_0; VECTOR_MUL_LZERO; SUM_NEG; VSUM_NEG;
    VECTOR_MUL_LNEG; SET_RULE `DISJOINT t u ==> ~(x IN t /\ x IN u)`] THEN
  REWRITE_TAC[EMPTY_GSPEC; SUM_CLAUSES; VSUM_CLAUSES] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
  UNDISCH_TAC `sum t (a:real^N->real) = &1` THEN
  ASM_CASES_TAC `!x:real^N. x IN t ==> a x = &0` THEN
  ASM_SIMP_TAC[SUM_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]);;

let AFFINE_INDEPENDENT_SPAN_EQ = prove
 (`!s. ~(affine_dependent s) /\ CARD s = dimindex(:N) + 1
       ==> affine hull s = (:real^N)`,
  MATCH_MP_TAC SET_PROVE_CASES THEN
  REWRITE_TAC[CARD_CLAUSES; ARITH_RULE `~(0 = n + 1)`] THEN
  SIMP_TAC[IMP_CONJ; AFFINE_INDEPENDENT_IMP_FINITE; MESON[HAS_SIZE]
   `FINITE s ==> (CARD s = n <=> s HAS_SIZE n)`] THEN
  X_GEN_TAC `orig:real^N` THEN GEOM_ORIGIN_TAC `orig:real^N` THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; IN_INSERT; SPAN_INSERT_0; HULL_INC] THEN
  SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_INSERT; IMP_CONJ] THEN
  REWRITE_TAC[ARITH_RULE `SUC n = m + 1 <=> n = m`; GSYM UNIV_SUBSET] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_GE_DIM_INDEPENDENT THEN
  ASM_REWRITE_TAC[DIM_UNIV; SUBSET_UNIV; LE_REFL; independent] THEN
  UNDISCH_TAC `~affine_dependent((vec 0:real^N) INSERT s)` THEN
  REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC DEPENDENT_IMP_AFFINE_DEPENDENT THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO; SET_RULE `{x | x IN s} = s`]);;

let AFFINE_INDEPENDENT_SPAN_GT = prove
 (`!s:real^N->bool.
        ~(affine_dependent s) /\ dimindex(:N) < CARD s
        ==> affine hull s = (:real^N)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC AFFINE_INDEPENDENT_SPAN_EQ THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `s:real^N->bool` AFFINE_DEPENDENT_BIGGERSET) THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN ASM_ARITH_TAC);;

let EMPTY_INTERIOR_AFFINE_HULL = prove
 (`!s:real^N->bool.
        FINITE s /\ CARD(s) <= dimindex(:N)
        ==> interior(affine hull s) = {}`,
  REWRITE_TAC[IMP_CONJ] THEN  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[AFFINE_HULL_EMPTY; INTERIOR_EMPTY] THEN
  SUBGOAL_THEN
   `!x s:real^N->bool n.
        ~(x IN s) /\ (x INSERT s) HAS_SIZE n /\ n <= dimindex(:N)
        ==> interior(affine hull(x INSERT s)) = {}`
   (fun th -> MESON_TAC[th; HAS_SIZE; FINITE_INSERT]) THEN
  X_GEN_TAC `orig:real^N` THEN GEOM_ORIGIN_TAC `orig:real^N` THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; IN_INSERT; SPAN_INSERT_0; HULL_INC] THEN
  REWRITE_TAC[HAS_SIZE; FINITE_INSERT; IMP_CONJ] THEN
  SIMP_TAC[CARD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EMPTY_INTERIOR_LOWDIM THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `CARD(s:real^N->bool)` THEN
  ASM_SIMP_TAC[DIM_LE_CARD; DIM_SPAN] THEN ASM_ARITH_TAC);;

let EMPTY_INTERIOR_CONVEX_HULL = prove
 (`!s:real^N->bool.
        FINITE s /\ CARD(s) <= dimindex(:N)
        ==> interior(convex hull s) = {}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!t. s SUBSET t /\ t = {} ==> s = {}`) THEN
  EXISTS_TAC `interior(affine hull s):real^N->bool` THEN
  SIMP_TAC[SUBSET_INTERIOR; CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
  ASM_SIMP_TAC[EMPTY_INTERIOR_AFFINE_HULL]);;

let AFFINE_DEPENDENT_CHOOSE = prove
 (`!s a:real^N.
       ~(affine_dependent s)
       ==> (affine_dependent(a INSERT s) <=> ~(a IN s) /\ a IN affine hull s)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(a:real^N) IN s` THEN
  ASM_SIMP_TAC[SET_RULE `a IN s ==> a INSERT s = s`] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  EQ_TAC THENL
   [UNDISCH_TAC `~(affine_dependent(s:real^N->bool))` THEN
    ASM_SIMP_TAC[AFFINE_DEPENDENT_EXPLICIT_FINITE; AFFINE_HULL_FINITE;
                 FINITE_INSERT; IN_ELIM_THM; SUM_CLAUSES; VSUM_CLAUSES] THEN
    DISCH_TAC THEN REWRITE_TAC[EXISTS_IN_INSERT] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` MP_TAC) THEN
    ASM_CASES_TAC `(u:real^N->real) a = &0` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[REAL_ADD_LID; VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
      DISCH_THEN(MP_TAC o SPEC `u:real^N->real`) THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[REAL_ARITH `ua + sa = &0 <=> sa = --ua`;
                   VECTOR_ARITH `va + sa:real^N = vec 0 <=> sa = --va`] THEN
      STRIP_TAC THEN EXISTS_TAC `(\x. --(inv(u a)) * u x):real^N->real` THEN
      ASM_SIMP_TAC[SUM_LMUL; GSYM VECTOR_MUL_ASSOC; VSUM_LMUL] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_MUL_LNEG] THEN
      REWRITE_TAC[REAL_ARITH `--a * --b:real = a * b`] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID]];
    DISCH_TAC THEN REWRITE_TAC[affine_dependent] THEN
    EXISTS_TAC `a:real^N` THEN
    ASM_SIMP_TAC[IN_INSERT; SET_RULE
     `~(a IN s) ==> (a INSERT s) DELETE a = s`]]);;

let AFFINE_INDEPENDENT_INSERT = prove
 (`!s a:real^N.
        ~(affine_dependent s) /\ ~(a IN affine hull s)
        ==> ~(affine_dependent(a INSERT s))`,
  SIMP_TAC[AFFINE_DEPENDENT_CHOOSE]);;

let AFFINE_HULL_EXPLICIT_UNIQUE = prove
 (`!s:real^N->bool u u'.
      ~(affine_dependent s) /\
      sum s u = &1 /\ sum s u' = &1 /\
      vsum s (\x. u x % x) = vsum s (\x. u' x % x)
      ==> !x. x IN s ==> u x = u' x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP AFFINE_DEPENDENT_EXPLICIT_FINITE) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(\x. u x - u' x):real^N->real`) THEN
  ASM_SIMP_TAC[VSUM_SUB; SUM_SUB; REAL_SUB_REFL; VECTOR_SUB_RDISTRIB;
               VECTOR_SUB_REFL; VECTOR_SUB_EQ; REAL_SUB_0] THEN
  MESON_TAC[]);;

let INDEPENDENT_IMP_AFFINE_DEPENDENT_0 = prove
 (`!s. independent s ==> ~(affine_dependent(vec 0 INSERT s))`,
  REWRITE_TAC[independent; DEPENDENT_AFFINE_DEPENDENT_CASES] THEN
  SIMP_TAC[DE_MORGAN_THM; AFFINE_INDEPENDENT_INSERT]);;

let AFFINE_INDEPENDENT_STDBASIS = prove
 (`~(affine_dependent
      ((vec 0:real^N) INSERT {basis i | 1 <= i /\ i <= dimindex (:N)}))`,
  SIMP_TAC[INDEPENDENT_IMP_AFFINE_DEPENDENT_0; INDEPENDENT_STDBASIS]);;

(* ------------------------------------------------------------------------- *)
(* Nonempty affine sets are translates of (unique) subspaces.                *)
(* ------------------------------------------------------------------------- *)

let AFFINE_TRANSLATION_SUBSPACE = prove
 (`!t:real^N->bool.
        affine t /\ ~(t = {}) <=> ?a s. subspace s /\ t = IMAGE (\x. a + x) s`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUBSPACE_IMP_NONEMPTY; IMAGE_EQ_EMPTY;
               AFFINE_TRANSLATION; SUBSPACE_IMP_AFFINE] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[TRANSLATION_GALOIS] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[UNWIND_THM2] THEN MATCH_MP_TAC AFFINE_IMP_SUBSPACE THEN
  ASM_REWRITE_TAC[AFFINE_TRANSLATION_EQ; IN_IMAGE] THEN
  EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let AFFINE_TRANSLATION_UNIQUE_SUBSPACE = prove
 (`!t:real^N->bool.
        affine t /\ ~(t = {}) <=>
        ?!s. ?a. subspace s /\ t = IMAGE (\x. a + x) s`,
  GEN_TAC THEN REWRITE_TAC[AFFINE_TRANSLATION_SUBSPACE] THEN
  MATCH_MP_TAC(MESON[]
   `(!a a' s s'. P s a /\ P s' a' ==> s = s')
    ==> ((?a s. P s a) <=> (?!s. ?a. P s a))`) THEN
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[TRANSLATION_GALOIS] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ADD_ASSOC] THEN
  MATCH_MP_TAC SUBSPACE_TRANSLATION_SELF THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `--a' + a:real^N = --(a' - a)`] THEN
  MATCH_MP_TAC SUBSPACE_NEG THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `t = IMAGE (\x:real^N. a' + x) s'` THEN
  DISCH_THEN(MP_TAC o AP_TERM `\s. (a':real^N) IN s`) THEN
  REWRITE_TAC[IN_IMAGE; VECTOR_ARITH `a:real^N = a + x <=> x = vec 0`] THEN
  ASM_SIMP_TAC[UNWIND_THM2; SUBSPACE_0] THEN
  REWRITE_TAC[IN_IMAGE; VECTOR_ARITH `a':real^N = a + x <=> x = a' - a`] THEN
  REWRITE_TAC[UNWIND_THM2]);;

let AFFINE_TRANSLATION_SUBSPACE_EXPLICIT = prove
 (`!t:real^N->bool a.
        affine t /\ a IN t
        ==> subspace {x - a | x IN t} /\
            t = IMAGE (\x. a + x) {x - a | x IN t}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[AFFINE_DIFFS_SUBSPACE] THEN
  ASM_REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o] THEN
  REWRITE_TAC[o_DEF; VECTOR_SUB_ADD2; IMAGE_ID]);;

(* ------------------------------------------------------------------------- *)
(* If we take a slice out of a set, we can do it perpendicularly,            *)
(* with the normal vector to the slice parallel to the affine hull.          *)
(* ------------------------------------------------------------------------- *)

let AFFINE_PARALLEL_SLICE = prove
  (`!s a:real^N b.
       affine s
       ==> s INTER {x | a dot x <= b} = {} \/ s SUBSET {x | a dot x <= b} \/
           ?a' b'. ~(a' = vec 0) /\

                   s INTER {x | a' dot x <= b'} = s INTER {x | a dot x <= b} /\
                   s INTER {x | a' dot x = b'} = s INTER {x | a dot x = b} /\
                   !w. w IN s ==> (w + a') IN s`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `s INTER {x:real^N | a dot x = b} = {}` THENL
    [MATCH_MP_TAC(TAUT `~(~p /\ ~q) ==> p \/ q \/ r`) THEN
     REPEAT STRIP_TAC THEN SUBGOAL_THEN
      `?u v:real^N. u IN s /\ v IN s /\
                    a dot u <= b /\ ~(a dot v <= b)`
     STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `(a:real^N) dot u < b` ASSUME_TAC THENL
      [ASM_REWRITE_TAC[REAL_LT_LE] THEN ASM SET_TAC[]; ALL_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
     REWRITE_TAC[NOT_IN_EMPTY; IN_INTER; NOT_FORALL_THM; IN_ELIM_THM] THEN
     EXISTS_TAC
      `u + (b - a dot u) / (a dot v - a dot u) % (v - u):real^N` THEN
     ASM_SIMP_TAC[IN_AFFINE_ADD_MUL_DIFF] THEN
     REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB] THEN
     REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
     DISCH_THEN(X_CHOOSE_THEN `z:real^N` MP_TAC) THEN
     REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN POP_ASSUM MP_TAC THEN
     GEN_GEOM_ORIGIN_TAC `z:real^N` ["a"; "a'"; "b'"; "w"] THEN
     REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
     REWRITE_TAC[VECTOR_ADD_RID; FORALL_IN_IMAGE] THEN
     REWRITE_TAC[DOT_RADD; REAL_ARITH `a + x <= a <=> x <= &0`] THEN
     SUBGOAL_THEN `subspace(s:real^N->bool) /\ span s = s`
     STRIP_ASSUME_TAC THENL
      [ASM_MESON_TAC[AFFINE_IMP_SUBSPACE; SPAN_EQ_SELF]; ALL_TAC] THEN
     MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`]
           ORTHOGONAL_SUBSPACE_DECOMP_EXISTS) THEN
     ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; orthogonal] THEN
     MAP_EVERY X_GEN_TAC [`a':real^N`; `a'':real^N`] THEN
     ASM_CASES_TAC `a':real^N = vec 0` THENL
      [ASM_REWRITE_TAC[VECTOR_ADD_LID] THEN
       ASM_CASES_TAC `a'':real^N = a` THEN ASM_REWRITE_TAC[] THEN
       SIMP_TAC[SUBSET; IN_ELIM_THM; REAL_LE_REFL];
       ALL_TAC] THEN
     STRIP_TAC THEN REPEAT DISJ2_TAC THEN
     EXISTS_TAC `a':real^N` THEN ASM_REWRITE_TAC[] THEN
     EXISTS_TAC `(a':real^N) dot z` THEN
     REPEAT(CONJ_TAC THENL
      [MATCH_MP_TAC(SET_RULE
        `(!x. x IN s ==> (p x <=> q x))
         ==> s INTER {x | p x} = s INTER {x | q x}`) THEN
       ASM_SIMP_TAC[DOT_LADD] THEN REAL_ARITH_TAC;
       ALL_TAC]) THEN
     X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
     EXISTS_TAC `x + a':real^N` THEN
     ASM_SIMP_TAC[SUBSPACE_ADD; VECTOR_ADD_ASSOC]]);;

(* ------------------------------------------------------------------------- *)
(* Affine dimension.                                                         *)
(* ------------------------------------------------------------------------- *)

let MAXIMAL_AFFINE_INDEPENDENT_SUBSET = prove
 (`!s b:real^N->bool.
        b SUBSET s /\ ~(affine_dependent b) /\
        (!b'. b SUBSET b' /\ b' SUBSET s /\ ~(affine_dependent b') ==> b' = b)
        ==> s SUBSET (affine hull b)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `(!a. a IN t /\ ~(a IN s) ==> F) ==> t SUBSET s`) THEN
  X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(a:real^N) INSERT b`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
   (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM] HULL_INC)) THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_INSERT; INSERT_SUBSET] THEN
  ASM SET_TAC[]);;

let MAXIMAL_AFFINE_INDEPENDENT_SUBSET_AFFINE = prove
 (`!s b:real^N->bool.
        affine s /\ b SUBSET s /\ ~(affine_dependent b) /\
        (!b'. b SUBSET b' /\ b' SUBSET s /\ ~(affine_dependent b') ==> b' = b)
        ==> affine hull b = s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HULL_MONO; HULL_P];
    ASM_MESON_TAC[MAXIMAL_AFFINE_INDEPENDENT_SUBSET]]);;

let EXTEND_TO_AFFINE_BASIS = prove
 (`!s u:real^N->bool.
        ~(affine_dependent s) /\ s SUBSET u
        ==> ?t. ~(affine_dependent t) /\ s SUBSET t /\ t SUBSET u /\
                affine hull t = affine hull u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\n. ?t:real^N->bool. ~(affine_dependent t) /\ s SUBSET t /\
                                    t SUBSET u /\ CARD t = n`
   num_MAX) THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[SUBSET_REFL; AFFINE_INDEPENDENT_CARD_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HULL_MONO; HULL_P]; ALL_TAC] THEN
  MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_AFFINE_HULL] THEN
  MATCH_MP_TAC MAXIMAL_AFFINE_INDEPENDENT_SUBSET THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CARD(c:real^N->bool)`) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^N->bool`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_LE THEN
  ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]);;

let AFFINE_BASIS_EXISTS = prove
 (`!s:real^N->bool.
      ?b. ~(affine_dependent b) /\ b SUBSET s /\
          affine hull b = affine hull s`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`{}:real^N->bool`; `s:real^N->bool`]
    EXTEND_TO_AFFINE_BASIS) THEN
  REWRITE_TAC[AFFINE_INDEPENDENT_EMPTY; EMPTY_SUBSET]);;

let aff_dim = new_definition
  `aff_dim s =
        @d:int. ?b. affine hull b = affine hull s /\ ~(affine_dependent b) /\
                    &(CARD b) = d + &1`;;

let AFF_DIM = prove
 (`!s. ?b. affine hull b = affine hull s /\
           ~(affine_dependent b) /\
           aff_dim s = &(CARD b) - &1`,
  GEN_TAC THEN
  REWRITE_TAC[aff_dim; INT_ARITH `y:int = x + &1 <=> x = y - &1`] THEN
  CONV_TAC SELECT_CONV THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_REFL] THEN
  MESON_TAC[AFFINE_BASIS_EXISTS]);;

let AFF_DIM_EMPTY = prove
 (`aff_dim {} = -- &1`,
  REWRITE_TAC[aff_dim; AFFINE_HULL_EMPTY; AFFINE_HULL_EQ_EMPTY] THEN
  REWRITE_TAC[UNWIND_THM2; AFFINE_INDEPENDENT_EMPTY; CARD_CLAUSES] THEN
  REWRITE_TAC[INT_ARITH `&0 = d + &1 <=> d:int = -- &1`; SELECT_REFL]);;

let AFF_DIM_AFFINE_HULL = prove
 (`!s. aff_dim(affine hull s) = aff_dim s`,
  REWRITE_TAC[aff_dim; HULL_HULL]);;

let AFF_DIM_TRANSLATION_EQ = prove
 (`!a:real^N s. aff_dim (IMAGE (\x. a + x) s) = aff_dim s`,
  REWRITE_TAC[aff_dim] THEN GEOM_TRANSLATE_TAC[] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(a /\ b ==> ~c)`] THEN
  SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE; CARD_IMAGE_INJ;
           VECTOR_ARITH `a + x:real^N = a + y <=> x = y`]);;

add_translation_invariants [AFF_DIM_TRANSLATION_EQ];;

let AFFINE_INDEPENDENT_CARD_DIM_DIFFS = prove
 (`!s a:real^N.
        ~affine_dependent s /\ a IN s
        ==> CARD s = dim {x - a | x IN s} + 1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  MATCH_MP_TAC(ARITH_RULE `~(s = 0) /\ v = s - 1 ==> s = v + 1`) THEN
  ASM_SIMP_TAC[CARD_EQ_0] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC DIM_UNIQUE THEN
  EXISTS_TAC `{b - a:real^N |b| b IN (s DELETE a)}` THEN REPEAT CONJ_TAC THENL
   [SET_TAC[];
    REWRITE_TAC[SIMPLE_IMAGE; SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_CASES_TAC `x:real^N = a` THENL
     [ASM_REWRITE_TAC[VECTOR_SUB_REFL; SPAN_0];
      MATCH_MP_TAC SPAN_SUPERSET THEN ASM SET_TAC[]];
    UNDISCH_TAC `~affine_dependent(s:real^N->bool)` THEN
    REWRITE_TAC[independent; CONTRAPOS_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `s = (a:real^N) INSERT (s DELETE a)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC DEPENDENT_IMP_AFFINE_DEPENDENT THEN
    ASM_REWRITE_TAC[IN_DELETE];
    REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    SIMP_TAC[VECTOR_ARITH `x - a:real^N = y - a <=> x = y`] THEN
    ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE]]);;

let AFF_DIM_DIM_AFFINE_DIFFS = prove
 (`!a:real^N s. affine s /\ a IN s ==> aff_dim s = &(dim {x - a | x IN s})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` AFF_DIM) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` MP_TAC) THEN
  ASM_CASES_TAC `b:real^N->bool = {}` THENL
   [ASM_MESON_TAC[AFFINE_HULL_EQ_EMPTY; NOT_IN_EMPTY]; ALL_TAC] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[INT_EQ_SUB_RADD; INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real^N`) THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `dim {x - c:real^N | x IN b} + 1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_CARD_DIM_DIFFS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `dim {x - c:real^N | x IN affine hull b} + 1` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[DIFFS_AFFINE_HULL_SPAN; DIM_SPAN]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `affine hull s:real^N->bool = s` SUBST1_TAC THENL
   [ASM_MESON_TAC[AFFINE_HULL_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^N) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_HULL_EQ; HULL_INC]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SIMP_TAC[VECTOR_ARITH `x - c:real^N = y - a <=> y = x + &1 % (a - c)`] THEN
  ASM_MESON_TAC[IN_AFFINE_ADD_MUL_DIFF]);;

let AFF_DIM_DIM_0 = prove
 (`!s:real^N->bool. vec 0 IN affine hull s ==> aff_dim s = &(dim s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `affine hull s:real^N->bool`]
    AFF_DIM_DIM_AFFINE_DIFFS) THEN
  ASM_REWRITE_TAC[AFFINE_AFFINE_HULL; VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[AFF_DIM_AFFINE_HULL; SET_RULE `{x | x IN s} = s`] THEN
  ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; DIM_SPAN]);;

let AFF_DIM_DIM_SUBSPACE = prove
 (`!s:real^N->bool. subspace s ==> aff_dim s = &(dim s)`,
  MESON_TAC[AFF_DIM_DIM_0; SUBSPACE_0; HULL_INC]);;

let AFF_DIM_LINEAR_IMAGE_LE = prove
 (`!f:real^M->real^N s. linear f ==> aff_dim(IMAGE f s) <= aff_dim s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  ASM_SIMP_TAC[AFFINE_HULL_LINEAR_IMAGE] THEN
  MP_TAC(ISPEC `s:real^M->bool` AFFINE_AFFINE_HULL) THEN
  SPEC_TAC(`affine hull s:real^M->bool`,`s:real^M->bool`) THEN
  GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; AFF_DIM_EMPTY; INT_LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^M`) THEN
  SUBGOAL_THEN `dim {x - f(a) |x| x IN IMAGE (f:real^M->real^N) s} <=
                dim {x - a | x IN s}`
  MP_TAC THENL
   [REWRITE_TAC[SET_RULE `{f x | x IN IMAGE g s} = {f (g x) | x IN s}`] THEN
    ASM_SIMP_TAC[GSYM LINEAR_SUB] THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN REWRITE_TAC[IMAGE_o] THEN
    MATCH_MP_TAC DIM_LINEAR_IMAGE_LE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    BINOP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC AFF_DIM_DIM_AFFINE_DIFFS THEN
    ASM_SIMP_TAC[AFFINE_LINEAR_IMAGE; FUN_IN_IMAGE]]);;

let AFF_DIM_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> aff_dim(IMAGE f s) = aff_dim s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[AFF_DIM_LINEAR_IMAGE_LE]; ALL_TAC] THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC
   `aff_dim(IMAGE (g:real^N->real^M) (IMAGE (f:real^M->real^N) s))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID; INT_LE_REFL];
    MATCH_MP_TAC AFF_DIM_LINEAR_IMAGE_LE THEN ASM_REWRITE_TAC[]]);;

add_linear_invariants [AFF_DIM_INJECTIVE_LINEAR_IMAGE];;

let AFF_DIM_AFFINE_INDEPENDENT = prove
 (`!b:real^N->bool.
        ~(affine_dependent b) ==> aff_dim b = &(CARD b) - &1`,
  GEN_TAC THEN ASM_CASES_TAC `b:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[CARD_CLAUSES; AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `a:real^N`]
   AFFINE_INDEPENDENT_CARD_DIM_DIFFS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; INT_ARITH `(a + b) - b:int = a`] THEN
  MP_TAC(ISPECL [`a:real^N`; `affine hull b:real^N->bool`]
   AFF_DIM_DIM_AFFINE_DIFFS) THEN
  ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC; AFF_DIM_AFFINE_HULL] THEN
  DISCH_THEN(K ALL_TAC) THEN AP_TERM_TAC THEN
  ASM_MESON_TAC[DIFFS_AFFINE_HULL_SPAN; DIM_SPAN]);;

let AFF_DIM_UNIQUE = prove
 (`!s b:real^N->bool.
        affine hull b = affine hull s /\ ~(affine_dependent b)
        ==> aff_dim s = &(CARD b) - &1`,
  MESON_TAC[AFF_DIM_AFFINE_HULL; AFF_DIM_AFFINE_INDEPENDENT]);;

let AFF_DIM_SING = prove
 (`!a:real^N. aff_dim {a} = &0`,
  GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `&(CARD {a:real^N}) - &1:int` THEN CONJ_TAC THENL
   [MATCH_MP_TAC AFF_DIM_AFFINE_INDEPENDENT THEN
    REWRITE_TAC[AFFINE_INDEPENDENT_1];
    SIMP_TAC[CARD_CLAUSES; FINITE_RULES; ARITH; NOT_IN_EMPTY; INT_SUB_REFL]]);;

let AFF_DIM_LE_CARD = prove
 (`!s:real^N->bool. FINITE s ==> aff_dim s <= &(CARD s) - &1`,
  MATCH_MP_TAC SET_PROVE_CASES THEN
  SIMP_TAC[AFF_DIM_EMPTY; CARD_CLAUSES] THEN CONV_TAC INT_REDUCE_CONV THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN
  SIMP_TAC[AFF_DIM_DIM_0; IN_INSERT; HULL_INC] THEN
  SIMP_TAC[CARD_IMAGE_INJ; VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
  SIMP_TAC[DIM_INSERT_0; INT_LE_SUB_LADD; CARD_CLAUSES; FINITE_INSERT] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_LE; ADD1; LE_ADD_RCANCEL] THEN
  SIMP_TAC[DIM_LE_CARD]);;

let AFF_DIM_GE = prove
 (`!s:real^N->bool. -- &1 <= aff_dim s`,
  GEN_TAC THEN MP_TAC(ISPEC `s:real^N->bool` AFF_DIM) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[INT_LE_SUB_LADD; INT_ADD_LINV; INT_POS]);;

let AFF_DIM_SUBSET = prove
 (`!s t:real^N->bool. s SUBSET t ==> aff_dim s <= aff_dim t`,
  MATCH_MP_TAC SET_PROVE_CASES THEN REWRITE_TAC[AFF_DIM_GE; AFF_DIM_EMPTY] THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(vec 0:real^N) IN t` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[AFF_DIM_DIM_0; IN_INSERT; HULL_INC; INT_OF_NUM_LE; DIM_SUBSET]);;

let AFF_DIM_LE_DIM = prove
 (`!s:real^N->bool. aff_dim s <= &(dim s)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN
  ASM_SIMP_TAC[GSYM AFF_DIM_DIM_SUBSPACE; SUBSPACE_SPAN] THEN
  MATCH_MP_TAC AFF_DIM_SUBSET THEN REWRITE_TAC[SPAN_INC]);;

let AFF_DIM_CONVEX_HULL = prove
 (`!s:real^N->bool. aff_dim(convex hull s) = aff_dim s`,
  GEN_TAC THEN MATCH_MP_TAC(INT_ARITH
   `!c:int. c = a /\ a <= b /\ b <= c ==> b = a`) THEN
  EXISTS_TAC `aff_dim(affine hull s:real^N->bool)` THEN
  SIMP_TAC[AFF_DIM_AFFINE_HULL; AFF_DIM_SUBSET; HULL_SUBSET;
           CONVEX_HULL_SUBSET_AFFINE_HULL]);;

let AFF_DIM_CLOSURE = prove
 (`!s:real^N->bool. aff_dim(closure s) = aff_dim s`,
  GEN_TAC THEN MATCH_MP_TAC(INT_ARITH
   `!h. h = s /\ s <= c /\ c <= h ==> c:int = s`) THEN
  EXISTS_TAC `aff_dim(affine hull s:real^N->bool)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[AFF_DIM_AFFINE_HULL];
    MATCH_MP_TAC AFF_DIM_SUBSET THEN REWRITE_TAC[CLOSURE_SUBSET];
    MATCH_MP_TAC AFF_DIM_SUBSET THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN
    REWRITE_TAC[CLOSED_AFFINE_HULL; HULL_SUBSET]]);;

let AFF_DIM_2 = prove
 (`!a b:real^N. aff_dim {a,b} = if a = b then &0 else &1`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[INSERT_AC; AFF_DIM_SING]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `&(CARD {a:real^N,b}) - &1:int` THEN
  ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT; AFFINE_INDEPENDENT_2] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RULES; IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC);;

let AFF_DIM_EQ_MINUS1 = prove
 (`!s:real^N->bool. aff_dim s = -- &1 <=> s = {}`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[AFF_DIM_EMPTY] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC(INT_ARITH `&0:int <= n ==> ~(n = -- &1)`) THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim {a:real^N}` THEN
  ASM_SIMP_TAC[AFF_DIM_SUBSET; SING_SUBSET] THEN
  REWRITE_TAC[AFF_DIM_SING; INT_LE_REFL]);;

let AFF_DIM_POS_LE = prove
 (`!s:real^N->bool. &0 <= aff_dim s <=> ~(s = {})`,
  GEN_TAC THEN REWRITE_TAC[GSYM AFF_DIM_EQ_MINUS1] THEN
  MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_GE) THEN INT_ARITH_TAC);;

let AFF_DIM_EQ_0 = prove
 (`!s:real^N->bool. aff_dim s = &0 <=> ?a. s = {a}`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[AFF_DIM_SING; LEFT_IMP_EXISTS_THM] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN
  CONV_TAC INT_REDUCE_CONV THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  MATCH_MP_TAC(SET_RULE
   `(!b. ~(b = a) /\ {a,b} SUBSET s ==> F) ==> a IN s ==> s = {a}`) THEN
  X_GEN_TAC `b:real^N` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SUBSET) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] AFF_DIM_2) THEN
  ASM_SIMP_TAC[] THEN INT_ARITH_TAC);;

let CONNECTED_IMP_PERFECT_AFF_DIM = prove
 (`!s x:real^N.
        connected s /\ ~(aff_dim s = &0) /\ x IN s ==> x limit_point_of s`,
  REWRITE_TAC[AFF_DIM_EQ_0; CONNECTED_IMP_PERFECT]);;

let AFF_DIM_UNIV = prove
 (`aff_dim(:real^N) = &(dimindex(:N))`,
  SIMP_TAC[AFF_DIM_DIM_SUBSPACE; SUBSPACE_UNIV; DIM_UNIV]);;

let AFF_DIM_EQ_AFFINE_HULL = prove
 (`!s t:real^N->bool.
        s SUBSET t /\ aff_dim t <= aff_dim s
        ==> affine hull s = affine hull t`,
  MATCH_MP_TAC SET_PROVE_CASES THEN
  SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_EQ_MINUS1; AFF_DIM_GE;
           INT_ARITH `a:int <= x ==> (x <= a <=> x = a)`] THEN
  X_GEN_TAC `a:real^N` THEN GEOM_ORIGIN_TAC `a:real^N` THEN
  SIMP_TAC[INSERT_SUBSET; IMP_CONJ; AFF_DIM_DIM_0; IN_INSERT; DIM_EQ_SPAN;
           HULL_INC; AFFINE_HULL_EQ_SPAN; INT_OF_NUM_LE]);;

let AFF_DIM_SUMS_INTER = prove
 (`!s t:real^N->bool.
        affine s /\ affine t /\ ~(s INTER t = {})
        ==> aff_dim {x + y | x IN s /\ y IN t} =
                (aff_dim s + aff_dim t) - aff_dim(s INTER t)`,
  REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> c ==> a /\ b ==> d`] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
  GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN X_GEN_TAC `a:real^N` THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN
  REWRITE_TAC[VECTOR_ARITH `(a + x) + (a + y):real^N = &2 % a + (x + y)`] THEN
  ONCE_REWRITE_TAC[SET_RULE `{a + x + y:real^N | x IN s /\ y IN t} =
                            IMAGE (\x. a + x) {x + y | x IN s /\ y IN t}`] THEN
  REWRITE_TAC[AFF_DIM_TRANSLATION_EQ; IN_INTER] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN STRIP_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(vec 0:real^N) IN {x + y | x IN s /\ y IN t}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT(EXISTS_TAC `vec 0:real^N`) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_LID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[AFF_DIM_DIM_0; HULL_INC; IN_INTER] THEN
  REWRITE_TAC[INT_EQ_SUB_LADD; INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
  MATCH_MP_TAC DIM_SUMS_INTER THEN ASM_SIMP_TAC[AFFINE_IMP_SUBSPACE]);;

let AFF_DIM_PSUBSET = prove
 (`!s t. (affine hull s) PSUBSET (affine hull t) ==> aff_dim s < aff_dim t`,
  ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  SIMP_TAC[PSUBSET; AFF_DIM_SUBSET; INT_LT_LE] THEN
  MESON_TAC[INT_EQ_IMP_LE; AFF_DIM_EQ_AFFINE_HULL; HULL_HULL]);;

let AFF_DIM_EQ_FULL = prove
 (`!s. aff_dim s = &(dimindex(:N)) <=> affine hull s = (:real^N)`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM AFFINE_HULL_UNIV] THEN
    MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; AFF_DIM_UNIV; INT_LE_REFL];
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
    SIMP_TAC[AFF_DIM_UNIV]]);;

let AFF_DIM_LE_UNIV = prove
 (`!s:real^N->bool. aff_dim s <= &(dimindex(:N))`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AFF_DIM_UNIV] THEN
  MATCH_MP_TAC AFF_DIM_SUBSET THEN REWRITE_TAC[SUBSET_UNIV]);;

let AFFINE_INDEPENDENT_IFF_CARD = prove
 (`!s:real^N->bool.
        ~affine_dependent s <=> FINITE s /\ aff_dim s = &(CARD s) - &1`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT; AFFINE_INDEPENDENT_IMP_FINITE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC
   (ISPEC `s:real^N->bool` AFFINE_BASIS_EXISTS) THEN
  MATCH_MP_TAC(ARITH_RULE `!b:int. a <= b - &1 /\ b < s ==> ~(a = s - &1)`) THEN
  EXISTS_TAC `&(CARD(b:real^N->bool)):int` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_LE_CARD; FINITE_SUBSET; AFF_DIM_AFFINE_HULL];
    REWRITE_TAC[INT_OF_NUM_LT] THEN MATCH_MP_TAC CARD_PSUBSET THEN
    ASM_REWRITE_TAC[PSUBSET] THEN ASM_MESON_TAC[]]);;

let AFFINE_HULL_CONVEX_INTER_NONEMPTY_INTERIOR = prove
 (`!s t:real^N->bool.
        convex s /\ ~(s INTER interior t = {})
        ==> affine hull (s INTER t) = affine hull s`,
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; RIGHT_AND_EXISTS_THM;
              LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`; `a:real^N`] THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN REWRITE_TAC[IN_INTER] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
  SIMP_TAC[SUBSET_HULL; AFFINE_AFFINE_HULL] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (SIMP_RULE[SUBSET] INTERIOR_SUBSET)) THEN
  ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; IN_INTER] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR_CBALL]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; SUBSET; IN_CBALL_0] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_UNIV] THEN
  X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
  ASM_SIMP_TAC[SPAN_SUPERSET; IN_INTER] THEN DISCH_TAC THEN
  ABBREV_TAC `k = min (&1 / &2) (e / norm(x:real^N))` THEN
  SUBGOAL_THEN `&0 < k /\ k < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN
    ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; NORM_POS_LT; REAL_MIN_LT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `x:real^N = inv k % k % x` SUBST1_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID;
                 REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN
  REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[VECTOR_ARITH
     `k % x:real^N = (&1 - k) % vec 0 + k % x`] THEN
    MATCH_MP_TAC IN_CONVEX_SET THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "k" THEN
    ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LE_RDIV_EQ; NORM_POS_LT] THEN
    ASM_REAL_ARITH_TAC]);;

let AFFINE_HULL_CONVEX_INTER_OPEN = prove
 (`!s t:real^N->bool.
        convex s /\ open t /\ ~(s INTER t = {})
        ==> affine hull (s INTER t) = affine hull s`,
  ASM_SIMP_TAC[AFFINE_HULL_CONVEX_INTER_NONEMPTY_INTERIOR; INTERIOR_OPEN]);;

let AFFINE_HULL_AFFINE_INTER_NONEMPTY_INTERIOR = prove
 (`!s t:real^N->bool.
        affine s /\ ~(s INTER interior t = {})
        ==> affine hull (s INTER t) = s`,
  SIMP_TAC[AFFINE_HULL_CONVEX_INTER_NONEMPTY_INTERIOR; AFFINE_IMP_CONVEX;
           HULL_P]);;

let AFFINE_HULL_AFFINE_INTER_OPEN = prove
 (`!s t:real^N->bool.
        affine s /\ open t /\ ~(s INTER t = {})
        ==> affine hull (s INTER t) = s`,
  SIMP_TAC[AFFINE_HULL_AFFINE_INTER_NONEMPTY_INTERIOR; INTERIOR_OPEN]);;

let CONVEX_AND_AFFINE_INTER_OPEN = prove
 (`!s t u:real^N->bool.
        convex s /\ affine t /\ open u /\
        s INTER u = t INTER u /\ ~(s INTER u = {})
        ==> affine hull s = t`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[] `!u v. x = u /\ u = v /\ v = y ==> x = y`) THEN
  MAP_EVERY EXISTS_TAC
   [`affine hull (s INTER u:real^N->bool)`;
    `affine hull t:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC AFFINE_HULL_CONVEX_INTER_OPEN THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC AFFINE_HULL_CONVEX_INTER_OPEN THEN
    ASM_SIMP_TAC[AFFINE_IMP_CONVEX] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[AFFINE_HULL_EQ]]);;

let AFFINE_HULL_CONVEX_INTER_OPEN_IN = prove
 (`!s t:real^N->bool.
        convex s /\ open_in (subtopology euclidean (affine hull s)) t /\
        ~(s INTER t = {})
        ==> affine hull (s INTER t) = affine hull s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s INTER t INTER u = s INTER u`;
               HULL_SUBSET] THEN
  MATCH_MP_TAC AFFINE_HULL_CONVEX_INTER_OPEN THEN ASM SET_TAC[]);;

let AFFINE_HULL_AFFINE_INTER_OPEN_IN = prove
 (`!s t:real^N->bool.
        affine s /\ open_in (subtopology euclidean s) t /\ ~(s INTER t = {})
        ==> affine hull (s INTER t) = s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`affine hull s:real^N->bool`; `t:real^N->bool`]
        AFFINE_HULL_CONVEX_INTER_OPEN_IN) THEN
  ASM_SIMP_TAC[HULL_HULL; AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL; HULL_P]);;

let AFFINE_HULL_OPEN_IN = prove
 (`!s t:real^N->bool.
        open_in (subtopology euclidean (affine hull t)) s /\ ~(s = {})
        ==> affine hull s = affine hull t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC AFFINE_HULL_AFFINE_INTER_OPEN THEN
  REWRITE_TAC[AFFINE_AFFINE_HULL] THEN ASM SET_TAC[]);;

let AFFINE_HULL_OPEN = prove
 (`!s. open s /\ ~(s = {}) ==> affine hull s = (:real^N)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBST1_TAC(SET_RULE `s = (:real^N) INTER s`) THEN
  ASM_SIMP_TAC[AFFINE_HULL_CONVEX_INTER_OPEN; CONVEX_UNIV] THEN
  REWRITE_TAC[AFFINE_HULL_UNIV]);;

let AFFINE_HULL_NONEMPTY_INTERIOR = prove
 (`!s. ~(interior s = {}) ==> affine hull s = (:real^N)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ s = UNIV ==> t = UNIV`) THEN
  EXISTS_TAC `affine hull (interior s:real^N->bool)` THEN
  SIMP_TAC[HULL_MONO; INTERIOR_SUBSET] THEN
  ASM_SIMP_TAC[AFFINE_HULL_OPEN; OPEN_INTERIOR]);;

let AFF_DIM_OPEN = prove
 (`!s:real^N->bool. open s /\ ~(s = {}) ==> aff_dim s = &(dimindex(:N))`,
  SIMP_TAC[AFF_DIM_EQ_FULL; AFFINE_HULL_OPEN]);;

let AFF_DIM_NONEMPTY_INTERIOR = prove
 (`!s:real^N->bool. ~(interior s = {}) ==> aff_dim s = &(dimindex(:N))`,
  SIMP_TAC[AFF_DIM_EQ_FULL; AFFINE_HULL_NONEMPTY_INTERIOR]);;

let SPAN_OPEN = prove
 (`!s. open s /\ ~(s = {}) ==> span s = (:real^N)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ s = UNIV ==> t = UNIV`) THEN
  EXISTS_TAC `affine hull s:real^N->bool` THEN
  ASM_SIMP_TAC[AFFINE_HULL_OPEN; AFFINE_HULL_SUBSET_SPAN]);;

let DIM_OPEN = prove
 (`!s:real^N->bool. open s /\ ~(s = {}) ==> dim s = dimindex(:N)`,
  SIMP_TAC[DIM_EQ_FULL; SPAN_OPEN]);;

let AFF_DIM_INSERT = prove
 (`!a:real^N s.
        aff_dim (a INSERT s) =
        if a IN affine hull s then aff_dim s else aff_dim s + &1`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC SET_PROVE_CASES THEN
  SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_SING; AFFINE_HULL_EMPTY; NOT_IN_EMPTY] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:real^N`; `s:real^N->bool`; `a:real^N`] THEN
  GEOM_ORIGIN_TAC `b:real^N` THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; AFF_DIM_DIM_0; HULL_INC; IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `s:real^N->bool`] THEN
  DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`(vec 0:real^N) INSERT s`,`s:real^N->bool`) THEN
  SIMP_TAC[DIM_INSERT; INT_OF_NUM_ADD] THEN MESON_TAC[]);;

let AFFINE_BOUNDED_EQ_TRIVIAL = prove
 (`!s:real^N->bool.
        affine s ==> (bounded s <=> s = {} \/ ?a. s = {a})`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[BOUNDED_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N` MP_TAC) THEN
  GEOM_ORIGIN_TAC `b:real^N` THEN SIMP_TAC[AFFINE_EQ_SUBSPACE] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUBSPACE_BOUNDED_EQ_TRIVIAL] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUBSPACE_0) THEN SET_TAC[]);;

let AFFINE_BOUNDED_EQ_LOWDIM = prove
 (`!s:real^N->bool.
        affine s ==> (bounded s <=> aff_dim s <= &0)`,
  SIMP_TAC[AFF_DIM_GE; INT_ARITH
   `--(&1):int <= x ==> (x <= &0 <=> x = --(&1) \/ x = &0)`] THEN
  SIMP_TAC[AFF_DIM_EQ_0; AFF_DIM_EQ_MINUS1; AFFINE_BOUNDED_EQ_TRIVIAL]);;

let COLLINEAR_AFF_DIM = prove
 (`!s:real^N->bool. collinear s <=> aff_dim s <= &1`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[COLLINEAR_AFFINE_HULL; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim{u:real^N,v}` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[AFF_DIM_SUBSET; AFF_DIM_AFFINE_HULL];
      MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC `&(CARD{u:real^N,v}) - &1:int` THEN
      SIMP_TAC[AFF_DIM_LE_CARD; FINITE_INSERT; FINITE_EMPTY] THEN
      REWRITE_TAC[INT_ARITH `x - &1:int <= &1 <=> x <= &2`; INT_OF_NUM_LE] THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN ARITH_TAC];
    ONCE_REWRITE_TAC[GSYM COLLINEAR_AFFINE_HULL_COLLINEAR;
                     GSYM AFF_DIM_AFFINE_HULL] THEN
    MP_TAC(ISPEC `s:real^N->bool` AFFINE_BASIS_EXISTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` (STRIP_ASSUME_TAC o GSYM)) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [AFFINE_INDEPENDENT_IFF_CARD]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[COLLINEAR_AFFINE_HULL_COLLINEAR;
                    AFF_DIM_AFFINE_HULL] THEN
    REWRITE_TAC[INT_ARITH `x - &1:int <= &1 <=> x <= &2`; INT_OF_NUM_LE] THEN
    ASM_SIMP_TAC[COLLINEAR_SMALL]]);;

let HOMEOMORPHIC_AFFINE_SETS = prove
 (`!s:real^M->bool t:real^N->bool.
        affine s /\ affine t /\ aff_dim s = aff_dim t ==> s homeomorphic t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_EQ_MINUS1; HOMEOMORPHIC_EMPTY] THEN
  POP_ASSUM MP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_EQ_MINUS1; HOMEOMORPHIC_EMPTY] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC
   [GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM; RIGHT_IMP_FORALL_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^N`] THEN
  GEOM_ORIGIN_TAC `a:real^M` THEN GEOM_ORIGIN_TAC `b:real^N` THEN
  SIMP_TAC[AFFINE_EQ_SUBSPACE; AFF_DIM_DIM_0; HULL_INC; INT_OF_NUM_EQ] THEN
  MESON_TAC[HOMEOMORPHIC_SUBSPACES]);;

let AFF_DIM_OPEN_IN = prove
 (`!s t:real^N->bool.
        ~(s = {}) /\ open_in (subtopology euclidean t) s /\ affine t
        ==> aff_dim s = aff_dim t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:real^N` THEN GEOM_ORIGIN_TAC `a:real^N` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  SUBGOAL_THEN `(vec 0:real^N) IN t` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[AFF_DIM_DIM_0; HULL_INC; AFFINE_EQ_SUBSPACE] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[GSYM LE_ANTISYM; DIM_SUBSET] THEN
  SUBGOAL_THEN `?e. &0 < e /\ cball(vec 0:real^N,e) INTER t SUBSET s`
  MP_TAC THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^N` o
      GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    ASM SET_TAC[];
    REWRITE_TAC[SUBSET; IN_INTER; IN_CBALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHONORMAL_BASIS_SUBSPACE) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `IMAGE (\x:real^N. e % x) b`]
   INDEPENDENT_CARD_LE_DIM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_SIMP_TAC[CARD_IMAGE_INJ; VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ] THEN
  ANTS_TAC THENL [REWRITE_TAC[SUBSET]; MESON_TAC[]] THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[NORM_MUL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SUBSPACE_MUL] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE THEN
    ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ; LINEAR_SCALING]]);;

let DIM_OPEN_IN = prove
 (`!s t:real^N->bool.
        ~(s = {}) /\ open_in (subtopology euclidean t) s /\ subspace t
        ==> dim s = dim t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  ASM_SIMP_TAC[GSYM LE_ANTISYM; DIM_SUBSET] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim(s:real^N->bool)` THEN
  REWRITE_TAC[AFF_DIM_LE_DIM] THEN ASM_SIMP_TAC[GSYM AFF_DIM_DIM_SUBSPACE] THEN
  MATCH_MP_TAC INT_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC AFF_DIM_OPEN_IN THEN ASM_SIMP_TAC[SUBSPACE_IMP_AFFINE]);;

let AFF_DIM_CONVEX_INTER_NONEMPTY_INTERIOR = prove
 (`!s t:real^N->bool.
        convex s /\ ~(s INTER interior t = {})
        ==> aff_dim(s INTER t) = aff_dim s`,
  ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  ASM_SIMP_TAC[AFFINE_HULL_CONVEX_INTER_NONEMPTY_INTERIOR] THEN
  REWRITE_TAC[AFF_DIM_AFFINE_HULL]);;

let AFF_DIM_CONVEX_INTER_OPEN = prove
 (`!s t:real^N->bool.
        convex s /\ open t /\ ~(s INTER t = {})
        ==> aff_dim(s INTER t) = aff_dim s`,
  ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  ASM_SIMP_TAC[AFFINE_HULL_CONVEX_INTER_OPEN] THEN
  REWRITE_TAC[AFF_DIM_AFFINE_HULL]);;

let AFFINE_HULL_HALFSPACE_LT = prove
 (`!a b. affine hull {x | a dot x < b} =
         if a = vec 0 /\ b <= &0 then {} else (:real^N)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[AFFINE_HULL_EQ_EMPTY; HALFSPACE_EQ_EMPTY_LT;
               AFFINE_HULL_OPEN; OPEN_HALFSPACE_LT]);;

let AFFINE_HULL_HALFSPACE_LE = prove
 (`!a b. affine hull {x | a dot x <= b} =
         if a = vec 0 /\ b < &0 then {} else (:real^N)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_SIMP_TAC[DOT_LZERO; SET_RULE `{x | p} = if p then UNIV else {}`] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[AFFINE_HULL_EMPTY; AFFINE_HULL_UNIV] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[GSYM CLOSURE_HALFSPACE_LT; AFFINE_HULL_CLOSURE] THEN
    ASM_REWRITE_TAC[AFFINE_HULL_HALFSPACE_LT]]);;

let AFFINE_HULL_HALFSPACE_GT = prove
 (`!a b. affine hull {x | a dot x > b} =
         if a = vec 0 /\ b >= &0 then {} else (:real^N)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[AFFINE_HULL_EQ_EMPTY; HALFSPACE_EQ_EMPTY_GT;
               AFFINE_HULL_OPEN; OPEN_HALFSPACE_GT]);;

let AFFINE_HULL_HALFSPACE_GE = prove
 (`!a b. affine hull {x | a dot x >= b} =
         if a = vec 0 /\ b > &0 then {} else (:real^N)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`--a:real^N`; `--b:real`] AFFINE_HULL_HALFSPACE_LE) THEN
  SIMP_TAC[real_ge; DOT_LNEG; REAL_LE_NEG2; VECTOR_NEG_EQ_0] THEN
  REWRITE_TAC[REAL_ARITH `--b < &0 <=> b > &0`]);;

let AFF_DIM_HALFSPACE_LT = prove
 (`!a:real^N b.
        aff_dim {x | a dot x < b} =
        if a = vec 0 /\ b <= &0 then --(&1) else &(dimindex(:N))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  SIMP_TAC[AFFINE_HULL_HALFSPACE_LT] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_UNIV]);;

let AFF_DIM_HALFSPACE_LE = prove
 (`!a:real^N b.
        aff_dim {x | a dot x <= b} =
        if a = vec 0 /\ b < &0 then --(&1) else &(dimindex(:N))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  SIMP_TAC[AFFINE_HULL_HALFSPACE_LE] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_UNIV]);;

let AFF_DIM_HALFSPACE_GT = prove
 (`!a:real^N b.
        aff_dim {x | a dot x > b} =
        if a = vec 0 /\ b >= &0 then --(&1) else &(dimindex(:N))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  SIMP_TAC[AFFINE_HULL_HALFSPACE_GT] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_UNIV]);;

let AFF_DIM_HALFSPACE_GE = prove
 (`!a:real^N b.
        aff_dim {x | a dot x >= b} =
        if a = vec 0 /\ b > &0 then --(&1) else &(dimindex(:N))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  SIMP_TAC[AFFINE_HULL_HALFSPACE_GE] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_UNIV]);;

let CHOOSE_AFFINE_SUBSET = prove
 (`!s:real^N->bool d.
        affine s /\ --(&1) <= d /\ d <= aff_dim s
        ==> ?t. affine t /\ t SUBSET s /\ aff_dim t = d`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `d:int = --(&1)` THENL
   [STRIP_TAC THEN EXISTS_TAC `{}:real^N->bool` THEN
    ASM_REWRITE_TAC[EMPTY_SUBSET; AFFINE_EMPTY; AFF_DIM_EMPTY];
    ASM_SIMP_TAC[INT_ARITH
     `~(d:int = --(&1)) ==> (--(&1) <= d <=> &0 <= d)`] THEN
    POP_ASSUM(K ALL_TAC)] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    POP_ASSUM MP_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` MP_TAC) THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN
  SIMP_TAC[IMP_CONJ; AFF_DIM_DIM_SUBSPACE; AFFINE_EQ_SUBSPACE] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
  REWRITE_TAC[INT_OF_NUM_LE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `n:num`]
        CHOOSE_SUBSPACE_OF_SUBSPACE) THEN
  ASM_SIMP_TAC[SPAN_OF_SUBSPACE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN
  ASM_SIMP_TAC[AFF_DIM_DIM_SUBSPACE; SUBSPACE_IMP_AFFINE]);;

(* ------------------------------------------------------------------------- *)
(* Existence of a rigid transform between congruent sets.                    *)
(* ------------------------------------------------------------------------- *)

let RIGID_TRANSFORMATION_BETWEEN_CONGRUENT_SETS = prove
 (`!x:A->real^N y:A->real^N s.
        (!i j. i IN s /\ j IN s ==> dist(x i,x j) = dist(y i,y j))
        ==> ?a f. orthogonal_transformation f /\
                  !i. i IN s ==> y i = a + f(x i)`,
  let lemma = prove
   (`!x:(real^N)^M y:(real^N)^M.
          (!i j. 1 <= i /\ i <= dimindex(:M) /\
                 1 <= j /\ j <= dimindex(:M)
                 ==> dist(x$i,x$j) = dist(y$i,y$j))
          ==> ?a f. orthogonal_transformation f /\
                    !i. 1 <= i /\ i <= dimindex(:M)
                        ==> y$i = a + f(x$i)`,
    REPEAT STRIP_TAC THEN
    ABBREV_TAC `(X:real^M^N) = lambda i j. (x:real^N^M)$j$i - x$1$i` THEN
    ABBREV_TAC `(Y:real^M^N) = lambda i j. (y:real^N^M)$j$i - y$1$i` THEN
    SUBGOAL_THEN `transp(X:real^M^N) ** X = transp(Y:real^M^N) ** Y`
    ASSUME_TAC THENL
     [REWRITE_TAC[MATRIX_MUL_LTRANSP_DOT_COLUMN] THEN
      MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN
      SIMP_TAC[CART_EQ; column; LAMBDA_BETA; dot] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT; GSYM dot] THEN
      REWRITE_TAC[DOT_NORM_SUB; VECTOR_ARITH
       `(x - a) - (y - a):real^N = x - y`] THEN
      ASM_SIMP_TAC[GSYM dist; DIMINDEX_GE_1; LE_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?M:real^N^N. orthogonal_matrix M /\ (Y:real^M^N) = M ** (X:real^M^N)`
    (CHOOSE_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THENL
     [ALL_TAC;
      GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [CART_EQ] THEN
      MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN
      SIMP_TAC[LAMBDA_BETA; matrix_mul] THEN
      REWRITE_TAC[REAL_ARITH `x - y:real = z <=> x = y + z`] THEN STRIP_TAC THEN
      EXISTS_TAC `(y:real^N^M)$1 - (M:real^N^N) ** (x:real^N^M)$1` THEN
      EXISTS_TAC `\x:real^N. (M:real^N^N) ** x` THEN
      ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX;
                   MATRIX_OF_MATRIX_VECTOR_MUL; MATRIX_VECTOR_MUL_LINEAR] THEN
      SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA;
               VECTOR_ADD_COMPONENT] THEN
      ASM_SIMP_TAC[REAL_SUB_LDISTRIB; SUM_SUB_NUMSEG] THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; REAL_ARITH
       `a + y - b:real = a - z + y <=> z = b`] THEN
      SIMP_TAC[LAMBDA_BETA]] THEN
    MP_TAC(ISPEC `transp(X:real^M^N) ** X`
      SYMMETRIC_MATRIX_DIAGONALIZABLE_EXPLICIT) THEN
    REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`P:real^M^M`; `d:num->real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(fun th -> MP_TAC th THEN ASM_REWRITE_TAC[] THEN MP_TAC th) THEN
    REWRITE_TAC[MATRIX_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[IMP_IMP] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [CART_EQ] THEN
    SIMP_TAC[MATRIX_MUL_LTRANSP_DOT_COLUMN; LAMBDA_BETA] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\i. column i ((X:real^M^N) ** (P:real^M^M))`;
                   `\i. column i ((Y:real^M^N) ** (P:real^M^M))`;
                   `1..dimindex(:M)`]
                  ORTHOGONAL_TRANSFORMATION_BETWEEN_ORTHOGONAL_SETS) THEN
    REWRITE_TAC[IN_NUMSEG] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[pairwise; IN_NUMSEG; NORM_EQ; orthogonal]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` (STRIP_ASSUME_TAC o GSYM)) THEN
    EXISTS_TAC `matrix(f:real^N->real^N)` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!M:real^M^N. M = M ** (P:real^M^M) ** transp P`
     (fun th -> GEN_REWRITE_TAC BINOP_CONV [th])
    THENL
     [ASM_MESON_TAC[orthogonal_matrix; MATRIX_MUL_RID];
      REWRITE_TAC[MATRIX_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_EQUAL_COLUMNS] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [orthogonal_transformation]) THEN
    DISCH_THEN(ASSUME_TAC o GSYM o MATCH_MP MATRIX_WORKS o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CART_EQ; matrix_vector_mul; column; LAMBDA_BETA] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [matrix_mul] THEN
    ASM_SIMP_TAC[LAMBDA_BETA]) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:A->bool = {}` THENL
   [REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `\x:real^N. x`] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; ORTHOGONAL_TRANSFORMATION_ID];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `m:A`) THEN DISCH_TAC] THEN
  SUBGOAL_THEN
    `?r. IMAGE r (1..dimindex(:(N,1)finite_sum)) SUBSET s /\
         affine hull (IMAGE (y o r) (1..dimindex(:(N,1)finite_sum))) =
         affine hull (IMAGE (y:A->real^N) s)`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
    SIMP_TAC[IMAGE_o; TAUT `p /\ q <=> ~(p ==> ~q)`;
             HULL_MONO; IMAGE_SUBSET] THEN REWRITE_TAC[NOT_IMP] THEN
    MP_TAC(ISPEC `IMAGE (y:A->real^N) s` AFFINE_BASIS_EXISTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [AFFINE_INDEPENDENT_IFF_CARD]) THEN
    STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:num->real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `CARD(b:real^N->bool) <= dimindex(:(N,1)finite_sum)`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
       `a:int = c - &1 ==> a + &1 <= n ==> c <= n`)) THEN
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; GSYM INT_OF_NUM_ADD] THEN
      REWRITE_TAC[INT_LE_RADD; AFF_DIM_LE_UNIV];
      ALL_TAC] THEN
    UNDISCH_TAC `b SUBSET IMAGE (y:A->real^N) s` THEN
    ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; IN_NUMSEG] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\i. if i <= CARD(b:real^N->bool) then r i else (m:A)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_THEN `affine hull b:real^N->bool = affine hull IMAGE y (s:A->bool)`
     (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM SUBSET] THEN MATCH_MP_TAC HULL_MONO THEN
    ONCE_ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN EXISTS_TAC `i:num` THEN
    ASM_REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[LE_TRANS];
    REWRITE_TAC[SUBSET; IN_NUMSEG; FORALL_IN_IMAGE] THEN
    STRIP_TAC THEN MP_TAC(ISPECL
     [`(lambda i. x(r i:A)):real^N^(N,1)finite_sum`;
      `(lambda i. y(r i:A)):real^N^(N,1)finite_sum`] lemma) THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^N->real^N` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!z. z IN
          affine hull IMAGE (y o (r:num->A)) (1..dimindex(:(N,1)finite_sum))
          ==> dist(z,y k) = dist(z,a + (f:real^N->real^N)(x k))`
    MP_TAC THENL
     [MATCH_MP_TAC SAME_DISTANCES_TO_AFFINE_HULL THEN
      REWRITE_TAC[FORALL_IN_IMAGE; o_THM; IN_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `dist(x(r(j:num)),(x:A->real^N) k)` THEN CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
        REWRITE_TAC[dist] THEN ASM_SIMP_TAC[NORM_ARITH
         `(a + x) - (a + y):real^N = x - y`] THEN
        ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION; LINEAR_SUB]];
      ASM_SIMP_TAC[NORM_ARITH
       `a:real^N = b <=> dist(a:real^N,a) = dist(a,b)`] THEN
      DISCH_THEN MATCH_MP_TAC THEN  MATCH_MP_TAC HULL_INC THEN
      REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN ASM_MESON_TAC[]]]);;

let RIGID_TRANSFORMATION_BETWEEN_CONGRUENT_SETS_STRONG = prove
 (`!x:A->real^N y:A->real^N s t.
        t SUBSET s /\ affine hull (IMAGE y t) = affine hull (IMAGE y s) /\
        (!i j. i IN s /\ j IN t ==> dist(x i,x j) = dist(y i,y j))
        ==> ?a f. orthogonal_transformation f /\
                  !i. i IN s ==> y i = a + f(x i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:A->real^N`; `y:A->real^N`; `t:A->bool`]
        RIGID_TRANSFORMATION_BETWEEN_CONGRUENT_SETS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^N->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!z. z IN affine hull (IMAGE (y:A->real^N) t)
        ==> dist(z,y i) = dist(z,a + (f:real^N->real^N)(x i))`
  MP_TAC THENL
   [MATCH_MP_TAC SAME_DISTANCES_TO_AFFINE_HULL THEN
    REWRITE_TAC[FORALL_IN_IMAGE; o_THM; IN_NUMSEG] THEN
    X_GEN_TAC `j:A` THEN STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `dist(a + f(x(j:A):real^N):real^N,a + f(x i))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[NORM_ARITH `dist(a + x:real^N,a + y) = dist(x,y)`] THEN
    ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_ISOMETRY; DIST_SYM];
    ASM_SIMP_TAC[NORM_ARITH
     `a:real^N = b <=> dist(a:real^N,a) = dist(a,b)`] THEN
    DISCH_THEN MATCH_MP_TAC THEN  MATCH_MP_TAC HULL_INC THEN
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]]);;

let RIGID_TRANSFORMATION_BETWEEN_3 = prove
 (`!a b c a' b' c':real^N.
        dist(a,b) = dist(a',b') /\
        dist(b,c) = dist(b',c') /\
        dist(c,a) = dist(c',a')
        ==> ?k f. orthogonal_transformation f /\
                  a' = k + f a /\ b' = k + f b /\ c' = k + f c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`FST:real^N#real^N->real^N`; `SND:real^N#real^N->real^N`;
    `{(a:real^N,a':real^N), (b,b'), (c,c')}`]
        RIGID_TRANSFORMATION_BETWEEN_CONGRUENT_SETS) THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT] THEN
  REWRITE_TAC[NOT_IN_EMPTY; IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[DIST_REFL; DIST_SYM]);;

let RIGID_TRANSFORMATION_BETWEEN_2 = prove
 (`!a b a' b':real^N.
        dist(a,b) = dist(a',b')
        ==> ?k f. orthogonal_transformation f /\
                  a' = k + f a /\ b' = k + f b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `a:real^N`;
                 `a':real^N`; `b':real^N`; `a':real^N`]
        RIGID_TRANSFORMATION_BETWEEN_3) THEN
  ASM_MESON_TAC[DIST_EQ_0; DIST_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Caratheodory's theorem.                                                   *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_CARATHEODORY_AFF_DIM = prove
 (`!p. convex hull p =
        {y:real^N | ?s u. FINITE s /\ s SUBSET p /\
                          &(CARD s) <= aff_dim p + &1 /\
                          (!x. x IN s ==> &0 <= u x) /\
                          sum s u = &1 /\ vsum s (\v. u v % v) = y}`,
  GEN_TAC THEN REWRITE_TAC[CONVEX_HULL_EXPLICIT] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  MATCH_MP_TAC(TAUT `!q. (p ==> q) /\ (q ==> r) ==> (p ==> r)`) THEN
  EXISTS_TAC `?n s u. CARD s = n /\
                      FINITE s /\ s SUBSET p /\
                      (!x. x IN s ==> &0 <= u x) /\
                      sum s u = &1 /\ vsum s (\v. u v % v) = (y:real^N)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [GSYM INT_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN REWRITE_TAC[NOT_IMP] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> n - 1 < n`) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim(p:real^N->bool) + &1 < &0` THEN
    REWRITE_TAC[INT_ARITH `p + &1:int < &0 <=> ~(-- &1 <= p)`] THEN
    REWRITE_TAC[AFF_DIM_GE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(aff_dim(s:real^N->bool) = &n - &1)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SUBSET) THEN

    UNDISCH_TAC `aff_dim(p:real^N->bool) + &1 < &n` THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[AFFINE_DEPENDENT_EXPLICIT_FINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?t. (!v:real^N. v IN s ==> u(v) + t * w(v) >= &0) /\
        ?a. a IN s /\ u(a) + t * w(a) = &0`
  STRIP_ASSUME_TAC THENL
   [ABBREV_TAC
     `i = IMAGE (\v. u(v) / --w(v)) {v:real^N | v IN s /\ w v < &0}` THEN
    EXISTS_TAC `inf i` THEN MP_TAC(SPEC `i:real->bool` INF_FINITE) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "i" THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_RESTRICT; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`w:real^N->real`; `s:real^N->bool`] SUM_ZERO_EXISTS) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `t = inf i` THEN
    EXPAND_TAC "i" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^N`
      STRIP_ASSUME_TAC) MP_TAC) THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `x < &0 ==> &0 < --x`; real_ge] THEN
    REWRITE_TAC[REAL_ARITH `t * --w <= u <=> &0 <= u + t * w`] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      DISJ_CASES_TAC(REAL_ARITH `(w:real^N->real) x < &0 \/ &0 <= w x`) THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `w < &0 ==> &0 <= --w`) THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `w(a:real^N) < &0` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`s DELETE (a:real^N)`; `(\v. u(v) + t * w(v)):real^N->real`] THEN
  ASM_SIMP_TAC[SUM_DELETE; VSUM_DELETE; CARD_DELETE; FINITE_DELETE] THEN
  ASM_SIMP_TAC[SUM_ADD; VECTOR_ADD_RDISTRIB; VSUM_ADD] THEN
  ASM_SIMP_TAC[GSYM VECTOR_MUL_ASSOC; SUM_LMUL; VSUM_LMUL] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[]; ASM SET_TAC[real_ge]; REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let CARATHEODORY_AFF_DIM = prove
 (`!p. convex hull p =
        {x:real^N | ?s. FINITE s /\ s SUBSET p /\
                         &(CARD s) <= aff_dim p + &1 /\
                        x IN convex hull s}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [CONVEX_HULL_CARATHEODORY_AFF_DIM] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_MESON_TAC[HULL_SUBSET; CONVEX_EXPLICIT; CONVEX_CONVEX_HULL];
    MESON_TAC[SUBSET; HULL_MONO]]);;

let CONVEX_HULL_CARATHEODORY = prove
 (`!p. convex hull p =
        {y:real^N | ?s u. FINITE s /\ s SUBSET p /\
                          CARD(s) <= dimindex(:N) + 1 /\
                          (!x. x IN s ==> &0 <= u x) /\
                          sum s u = &1 /\ vsum s (\v. u v % v) = y}`,

  GEN_TAC THEN REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
  EQ_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_CARATHEODORY_AFF_DIM; IN_ELIM_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_ADD] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `a:int <= x + &1 ==> x <= y ==> a <= y + &1`)) THEN
    REWRITE_TAC[AFF_DIM_LE_UNIV];
    REWRITE_TAC[CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN MESON_TAC[]]);;

let CARATHEODORY = prove
 (`!p. convex hull p =
        {x:real^N | ?s. FINITE s /\ s SUBSET p /\
                        CARD(s) <= dimindex(:N) + 1 /\
                        x IN convex hull s}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [CONVEX_HULL_CARATHEODORY] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_MESON_TAC[HULL_SUBSET; CONVEX_EXPLICIT; CONVEX_CONVEX_HULL];
    MESON_TAC[SUBSET; HULL_MONO]]);;

(* ------------------------------------------------------------------------- *)
(* Some results on decomposing convex hulls, e.g. simplicial subdivision.    *)
(* ------------------------------------------------------------------------- *)

let AFFINE_HULL_INTER,CONVEX_HULL_INTER = (CONJ_PAIR o prove)
 (`(!s t:real^N->bool.
        ~(affine_dependent(s UNION t))
        ==> affine hull s INTER affine hull t = affine hull (s INTER t)) /\
   (!s t:real^N->bool.
        ~(affine_dependent (s UNION t))
        ==> convex hull s INTER convex hull t = convex hull (s INTER t))`,
  CONJ_TAC THEN
  (REPEAT STRIP_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
   REWRITE_TAC[FINITE_UNION] THEN STRIP_TAC THEN
   MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET_INTER] THEN
   SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
   REWRITE_TAC[SUBSET; AFFINE_HULL_FINITE; CONVEX_HULL_FINITE;
               IN_ELIM_THM; IN_INTER] THEN
   X_GEN_TAC `y:real^N` THEN DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `v:real^N->real` STRIP_ASSUME_TAC)) THEN
   FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [AFFINE_DEPENDENT_EXPLICIT]) THEN
   REWRITE_TAC[NOT_EXISTS_THM] THEN
   DISCH_THEN(MP_TAC o SPEC `(s UNION t):real^N->bool`) THEN
   ASM_REWRITE_TAC[SUBSET_REFL] THEN
   DISCH_THEN(MP_TAC o SPEC
    `\x:real^N. (if x IN s then u x else &0) -
                (if x IN t then v x else &0)`) THEN
   ASM_SIMP_TAC[SUM_SUB; FINITE_UNION; VSUM_SUB; VECTOR_SUB_RDISTRIB] THEN
   REWRITE_TAC[MESON[]
    `(if p then a else b) % x = (if p then a % x else b % x)`] THEN
   ASM_SIMP_TAC[SUM_CASES; VSUM_CASES; VECTOR_MUL_LZERO; FINITE_UNION] THEN
   ASM_REWRITE_TAC[SUM_0; VSUM_0;
     SET_RULE `{x | x IN (s UNION t) /\ x IN s} = s`;
     SET_RULE `{x | x IN (s UNION t) /\ x IN t} = t`] THEN
   MATCH_MP_TAC(TAUT `a /\ c /\ (~b ==> d) ==> ~(a /\ b /\ c) ==> d`) THEN
   REPEAT CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC; ALL_TAC] THEN
   DISCH_TAC THEN EXISTS_TAC `u:real^N->real` THEN ASM_SIMP_TAC[] THEN
   CONJ_TAC THEN MATCH_MP_TAC EQ_TRANS THENL
    [EXISTS_TAC `sum s (u:real^N->real)`;
     EXISTS_TAC `vsum s (\x. (u:real^N->real) x % x)`] THEN
   (CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM ACCEPT_TAC]) THEN
   CONV_TAC SYM_CONV THENL
    [MATCH_MP_TAC SUM_EQ_SUPERSET; MATCH_MP_TAC VSUM_EQ_SUPERSET] THEN
   ASM_SIMP_TAC[FINITE_INTER; INTER_SUBSET; IN_INTER] THEN
   X_GEN_TAC `x:real^N` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
   DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
   ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN ASM SET_TAC[]));;

let AFFINE_HULL_INTERS = prove
 (`!s:(real^N->bool)->bool.
        ~(affine_dependent(UNIONS s))
        ==> affine hull (INTERS s) = INTERS {affine hull t | t IN s}`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
   MP_TAC th THEN MP_TAC(MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE th)) THEN
  SPEC_TAC(`s:(real^N->bool)->bool`,`s:(real^N->bool)->bool`) THEN
  REWRITE_TAC[FINITE_UNIONS; IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; INTERS_0; UNIONS_INSERT; INTERS_INSERT;
              SET_RULE `{f x | x IN {}} = {}`; AFFINE_HULL_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `~affine_dependent((s UNION UNIONS f):real^N->bool)` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] AFFINE_DEPENDENT_MONO) THEN
    SET_TAC[];
    DISCH_TAC] THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[INTERS_0; INTER_UNIV; IN_SING] THEN
    REWRITE_TAC[SET_RULE `{f x | x = a} = {f a}`; INTERS_1];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (rhs o rand) AFFINE_HULL_INTER o lhand o snd) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `~affine_dependent((s UNION UNIONS f):real^N->bool)` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] AFFINE_DEPENDENT_MONO) THEN
    UNDISCH_TAC `~(f:(real^N->bool)->bool = {})` THEN SET_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[SET_RULE
   `{f x | x IN (a INSERT s)} = (f a) INSERT {f x | x IN s}`] THEN
  ASM_REWRITE_TAC[INTERS_INSERT]);;

let CONVEX_HULL_INTERS = prove
 (`!s:(real^N->bool)->bool.
        ~(affine_dependent(UNIONS s))
        ==> convex hull (INTERS s) = INTERS {convex hull t | t IN s}`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
   MP_TAC th THEN MP_TAC(MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE th)) THEN
  SPEC_TAC(`s:(real^N->bool)->bool`,`s:(real^N->bool)->bool`) THEN
  REWRITE_TAC[FINITE_UNIONS; IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; INTERS_0; UNIONS_INSERT; INTERS_INSERT;
              SET_RULE `{f x | x IN {}} = {}`; CONVEX_HULL_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `~affine_dependent((s UNION UNIONS f):real^N->bool)` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] AFFINE_DEPENDENT_MONO) THEN
    SET_TAC[];
    DISCH_TAC] THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[INTERS_0; INTER_UNIV; IN_SING] THEN
    REWRITE_TAC[SET_RULE `{f x | x = a} = {f a}`; INTERS_1];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (rhs o rand) CONVEX_HULL_INTER o lhand o snd) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `~affine_dependent((s UNION UNIONS f):real^N->bool)` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] AFFINE_DEPENDENT_MONO) THEN
    UNDISCH_TAC `~(f:(real^N->bool)->bool = {})` THEN SET_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[SET_RULE
   `{f x | x IN (a INSERT s)} = (f a) INSERT {f x | x IN s}`] THEN
  ASM_REWRITE_TAC[INTERS_INSERT]);;

let IN_CONVEX_HULL_EXCHANGE = prove
 (`!s a x:real^N.
        a IN convex hull s /\ x IN convex hull s
        ==> ?b. b IN s /\ x IN convex hull (a INSERT (s DELETE b))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(a:real^N) IN s` THENL
   [EXISTS_TAC `a:real^N` THEN ASM_SIMP_TAC[INSERT_DELETE]; ALL_TAC] THEN
  ASM_CASES_TAC `FINITE(s:real^N->bool) /\ CARD s <= dimindex(:N) + 1` THENL
   [ALL_TAC;
    UNDISCH_TAC `(x:real^N) IN convex hull s` THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CARATHEODORY] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `t:real^N->bool = s` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?b:real^N. b IN s /\ ~(b IN t)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^N` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN convex hull t` THEN
    SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]] THEN
  MP_TAC(ASSUME `(a:real^N) IN convex hull s`) THEN
  MP_TAC(ASSUME `(x:real^N) IN convex hull s`) THEN
  REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `v:real^N->real` THEN STRIP_TAC THEN
  X_GEN_TAC `u:real^N->real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `?b. b IN s /\ (v:real^N->real) b = &0` THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC MONO_EXISTS) THEN
    X_GEN_TAC `b:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `\x:real^N. if x = a then &0 else v x` THEN
    ASM_SIMP_TAC[FORALL_IN_INSERT; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_DELETE] THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN
    ASM_SIMP_TAC[SUM_DELETE; VSUM_DELETE; COND_ID] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ASM_SIMP_TAC[SUM_CASES; VSUM_CASES; REAL_LE_REFL; COND_ID] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; SUM_0; VSUM_0] THEN
    ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> {x | x IN s /\ ~(x = a)} = s`] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
  REWRITE_TAC[TAUT `~(a /\ b) <=> a ==> ~b`] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `IMAGE (\b. (u:real^N->real) b / v b) s` SUP_FINITE) THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_MESON_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY]; ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `b:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!b. b IN s ==> &0 < (v:real^N->real) b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (u:real^N->real) b /\ &0 < v b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LE] THEN
    UNDISCH_TAC `!x. x IN s ==> (u:real^N->real) x / v x <= u b / v b` THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> (x <= &0 <=> x = &0)`] THEN
    DISCH_TAC THEN UNDISCH_TAC `sum s (u:real^N->real) = &1` THEN
    MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x = &1 ==> F`) THEN
    ASM_SIMP_TAC[SUM_EQ_0];
    ALL_TAC] THEN
  EXISTS_TAC `(\x. if x = a then v b / u b else v x - (v b / u b) * u x):
              real^N->real` THEN
  ASM_SIMP_TAC[FORALL_IN_INSERT; REAL_LE_DIV; REAL_LT_IMP_LE] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_DELETE] THEN
  ASM_SIMP_TAC[SUM_DELETE; VSUM_DELETE; IN_DELETE] THEN
  ASM_SIMP_TAC[SUM_CASES; VSUM_CASES; FINITE_DELETE] THEN
  ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> {x | x IN s /\ ~(x = a)} = s`;
               SET_RULE `~(a IN s) ==> {x | x IN s /\ x = a} = {}`] THEN
  REWRITE_TAC[VSUM_CLAUSES; SUM_CLAUSES] THEN
  ASM_CASES_TAC `b:real^N = a` THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[VECTOR_SUB_RDISTRIB; VSUM_SUB; SUM_SUB] THEN
  REWRITE_TAC[GSYM VECTOR_MUL_ASSOC; VECTOR_ADD_LID; REAL_ADD_LID] THEN
  ASM_SIMP_TAC[SUM_LMUL; VSUM_LMUL] THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC; REAL_ARITH_TAC; VECTOR_ARITH_TAC] THEN
  X_GEN_TAC `c:real^N` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_CASES_TAC `(u:real^N->real) c = &0` THENL
   [ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO]; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_LE] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_LE] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LE]);;

let IN_CONVEX_HULL_EXCHANGE_UNIQUE = prove
 (`!s t t' a x:real^N.
        ~(affine_dependent s) /\
        a IN convex hull s /\
        t SUBSET s /\ t' SUBSET s /\
        x IN convex hull (a INSERT t) /\
        x IN convex hull (a INSERT t')
        ==> x IN convex hull (a INSERT (t INTER t'))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(a:real^N) IN s` THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[SET_RULE
     `a INSERT (s INTER t) = (a INSERT s) INTER (a INSERT t)`] THEN
    W(MP_TAC o PART_MATCH (rand o rand)  CONVEX_HULL_INTER o rand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `~(affine_dependent(s:real^N->bool))` THEN
      REWRITE_TAC[CONTRAPOS_THM] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] AFFINE_DEPENDENT_MONO);
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:real^N->real` STRIP_ASSUME_TAC)
    MP_TAC) THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `~((a:real^N) IN t) /\ ~(a IN t')` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(t:real^N->bool) /\ FINITE(t':real^N->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[AFFINE_HULL_FINITE_STEP_GEN; REAL_LE_ADD;
               REAL_ARITH `&0 <= a / &2 <=> &0 <= a`] THEN
  REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u':real`; `u:real^N->real`] THEN REPEAT DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`v':real`; `v:real^N->real`] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
    [AFFINE_DEPENDENT_EXPLICIT]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(MP_TAC o SPEC
   `\x:real^N. (if x IN t then u x else &0) - (if x IN t' then v x else &0) +
               (u' - v') * b x`) THEN
  ASM_SIMP_TAC[SUM_ADD; VSUM_ADD; SUM_LMUL; VSUM_LMUL; VECTOR_ADD_RDISTRIB] THEN
  ASM_SIMP_TAC[SUM_SUB; VSUM_SUB; VECTOR_SUB_RDISTRIB] THEN
  REWRITE_TAC[MESON[]
   `(if p then a else b) % x = (if p then a % x else b % x)`] THEN
  ASM_SIMP_TAC[SUM_CASES; VSUM_CASES; VECTOR_MUL_LZERO; SUM_0; VSUM_0] THEN
  ASM_SIMP_TAC[SET_RULE `t SUBSET s ==> {x | x IN s /\ x IN t} = t`] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; VSUM_ADD; VSUM_LMUL; VECTOR_ADD_RDISTRIB;
               GSYM VECTOR_MUL_ASSOC] THEN
  MATCH_MP_TAC(TAUT `a /\ c /\ (~b ==> d) ==> ~(a /\ b /\ c) ==> d`) THEN
  REPEAT CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(!x. x IN s ==> (if x IN t then u x else &0) <=
                    (if x IN t' then v x else &0)) \/
    (!x:real^N. x IN s ==> (if x IN t' then v x else &0) <=
                           (if x IN t then u x else &0))`
  (DISJ_CASES_THEN(LABEL_TAC "*")) THENL
   [MP_TAC(REAL_ARITH `&0 <= (u' - v') \/ &0 <= (v' - u')`) THEN
    MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN
    DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= c ==> a - b + c = &0 ==> a <= b`);
      MATCH_MP_TAC(REAL_ARITH `&0 <= --c ==> a - b + c = &0 ==> b <= a`)] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; GSYM REAL_MUL_LNEG; REAL_NEG_SUB];
    EXISTS_TAC `(\x. if x = a then u' else u x):real^N->real`;
    EXISTS_TAC `(\x. if x = a then v' else v x):real^N->real`] THEN
  ASM_SIMP_TAC[FORALL_IN_INSERT] THEN
  (CONJ_TAC THENL [ASM_MESON_TAC[IN_INTER]; ALL_TAC]) THEN
  ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_INTER] THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  REWRITE_TAC[REAL_ARITH `u' + u = &1 <=> u = &1 - u'`;
              VECTOR_ARITH `u' + u:real^N = y <=> u = y - u'`] THEN
  (CONJ_TAC THEN
   FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
   CONV_TAC SYM_CONV THENL
    [MATCH_MP_TAC SUM_EQ_SUPERSET; MATCH_MP_TAC VSUM_EQ_SUPERSET]) THEN
  ASM_SIMP_TAC[FINITE_INTER; INTER_SUBSET; IN_INTER] THEN
  (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  X_GEN_TAC `y:real^N` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISCH_TAC THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM SET_TAC[]);;

let CONVEX_HULL_EXCHANGE_UNION = prove
 (`!s a:real^N.
        a IN convex hull s
        ==> convex hull s =
            UNIONS {convex hull (a INSERT (s DELETE b)) |b| b IN s}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[UNIONS_IMAGE] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[IN_CONVEX_HULL_EXCHANGE];
    REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; FORALL_IN_GSPEC;
                IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM SUBSET] THEN
    ASM_SIMP_TAC[SUBSET_HULL; CONVEX_CONVEX_HULL] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET] THEN
    MESON_TAC[HULL_INC; SUBSET; IN_DELETE]]);;

let CONVEX_HULL_EXCHANGE_INTER = prove
 (`!s a:real^N t t'.
         ~affine_dependent s /\
         a IN convex hull s /\
         t SUBSET s /\
         t' SUBSET s
         ==> (convex hull (a INSERT t)) INTER (convex hull (a INSERT t')) =
             convex hull (a INSERT (t INTER t'))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC IN_CONVEX_HULL_EXCHANGE_UNIQUE THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Representing affine hull as hyperplane or finite intersection of them.    *)
(* ------------------------------------------------------------------------- *)

let AFF_DIM_EQ_HYPERPLANE = prove
 (`!s. aff_dim s = &(dimindex(:N)) - &1 <=>
       ?a b. ~(a = vec 0) /\ affine hull s = {x:real^N | a dot x = b}`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY; INT_ARITH `--a:int = b - a <=> b = &0`] THEN
    SIMP_TAC[INT_OF_NUM_EQ; LE_1; DIMINDEX_GE_1; AFFINE_HULL_EMPTY] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `(b / (a dot a)) % a:real^N`) THEN
    ASM_SIMP_TAC[DOT_RMUL; REAL_DIV_RMUL; DOT_EQ_0];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `c:real^N` THEN
    GEN_GEOM_ORIGIN_TAC `c:real^N` ["a"] THEN
    SIMP_TAC[AFF_DIM_DIM_0; HULL_INC] THEN
    SIMP_TAC[INT_OF_NUM_SUB; DIMINDEX_GE_1; INT_OF_NUM_EQ] THEN
    SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; DIM_EQ_HYPERPLANE] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `a:real^N` THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `a:real^N = vec 0` THEN
    ASM_REWRITE_TAC[DOT_RADD; REAL_ARITH `a + b:real = c <=> b = c - a`] THEN
    EQ_TAC THEN STRIP_TAC THENL
     [EXISTS_TAC `(a:real^N) dot c` THEN ASM_REWRITE_TAC[REAL_SUB_REFL];
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `\s. (vec 0:real^N) IN s`) THEN
      ASM_SIMP_TAC[SPAN_SUPERSET; IN_ELIM_THM; DOT_RZERO]]]);;

let AFF_DIM_HYPERPLANE = prove
 (`!a b. ~(a = vec 0)
         ==> aff_dim {x:real^N | a dot x = b} = &(dimindex(:N)) - &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AFF_DIM_EQ_HYPERPLANE] THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real`] THEN
  ASM_REWRITE_TAC[AFFINE_HULL_EQ; AFFINE_HYPERPLANE]);;

let BOUNDED_HYPERPLANE_EQ_TRIVIAL = prove
 (`!a b. bounded {x:real^N | a dot x = b} <=>
         if a = vec 0 then ~(b = &0) else dimindex(:N) = 1`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_LZERO] THENL
   [ASM_CASES_TAC `b = &0` THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; BOUNDED_EMPTY] THEN
    REWRITE_TAC[NOT_BOUNDED_UNIV; SET_RULE `{x | T} = UNIV`];
    ASM_SIMP_TAC[AFFINE_BOUNDED_EQ_LOWDIM; AFF_DIM_HYPERPLANE;
                 AFFINE_HYPERPLANE] THEN
    REWRITE_TAC[INT_ARITH `a - &1:int <= &0 <=> a <= &1`; INT_OF_NUM_LE] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> (n <= 1 <=> n = 1)`) THEN
    REWRITE_TAC[DIMINDEX_GE_1]]);;

let AFFINE_HULL_FINITE_INTERSECTION_HYPERPLANES = prove
 (`!s:real^N->bool.
        ?f. FINITE f /\
            &(CARD f) + aff_dim s = &(dimindex(:N)) /\
            affine hull s = INTERS f /\
            (!h. h IN f ==> ?a b. ~(a = vec 0) /\ h = {x | a dot x = b})`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  MP_TAC(ISPEC `s:real^N->bool` AFFINE_BASIS_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `(:real^N)`] EXTEND_TO_AFFINE_BASIS) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; AFFINE_HULL_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE(c:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  REWRITE_TAC[GSYM AFF_DIM_UNIV] THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
  ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT; CARD_DIFF] THEN
  REWRITE_TAC[INT_ARITH `f + b - &1:int = c - &1 <=> f = c - b`] THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB; CARD_SUBSET; GSYM CARD_DIFF; INT_OF_NUM_EQ] THEN
  ASM_CASES_TAC `c:real^N->bool = b` THENL
   [EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; INTERS_0;
                    DIFF_EQ_EMPTY] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{affine hull (c DELETE a) |a| (a:real^N) IN (c DIFF b)}` THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DIFF] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_SIMP_TAC[FINITE_DIFF] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN REWRITE_TAC[IN_DIFF] THEN
    STRIP_TAC THEN ASM_CASES_TAC `x:real^N = y` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~affine_dependent(c:real^N->bool)` THEN
    REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[];
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN REWRITE_TAC[IMAGE_o] THEN
    ONCE_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
    W(MP_TAC o PART_MATCH (rhs o rand) AFFINE_HULL_INTERS o rand o snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
      EXISTS_TAC `c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; FORALL_IN_IMAGE;
                  IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_INTERS; FORALL_IN_IMAGE] THEN ASM SET_TAC[]];
    REWRITE_TAC[GSYM AFF_DIM_EQ_HYPERPLANE] THEN
    ASM_SIMP_TAC[IN_DIFF; AFFINE_INDEPENDENT_DELETE;
                 AFF_DIM_AFFINE_INDEPENDENT; CARD_DELETE] THEN
    REWRITE_TAC[GSYM AFF_DIM_UNIV] THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT; CARD_DIFF] THEN
    REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(GSYM INT_OF_NUM_SUB) THEN
    MATCH_MP_TAC(ARITH_RULE `~(c = 0) ==> 1 <= c`) THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN ASM SET_TAC[]]);;

let AFFINE_HYPERPLANE_SUMS_EQ_UNIV = prove
 (`!a b s.
        affine s /\
        ~(s INTER {v | a dot v = b} = {}) /\
        ~(s DIFF {v | a dot v = b} = {})
        ==> {x + y | x IN s /\ y IN {v | a dot v = b}} = (:real^N)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[DOT_LZERO] THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> b ==> a /\ c ==> d`] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MEMBER_NOT_EMPTY] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN X_GEN_TAC `c:real^N` THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{x + y:real^N | x IN s /\ P y} =
        {z | ?x y. x IN s /\ P y /\ z = x + y}`] THEN
  GEOM_ORIGIN_TAC `c:real^N` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[DOT_RADD; REAL_ARITH `b dot c + a = d <=> a = d - b dot c`] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM; DOT_RZERO] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  ASM_SIMP_TAC[AFFINE_EQ_SUBSPACE; HULL_INC] THEN STRIP_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `c + z:real^N = (c + x) + (c + y) <=>
                            z = c + x + y`] THEN
  REWRITE_TAC[SET_RULE
   `{z | ?x y. x IN s /\ P y /\ z = c + x + y} =
    IMAGE (\x. c + x) {x + y:real^N | x IN s /\ y IN {v | P v}}`] THEN
  MATCH_MP_TAC(SET_RULE
   `!f. (!x. g(f x) = x) /\ s = UNIV ==> IMAGE g s = UNIV`) THEN
  EXISTS_TAC `\x:real^N. x - c` THEN
  REWRITE_TAC[VECTOR_ARITH `c + x - c:real^N = x`] THEN
  MATCH_MP_TAC(MESON[SPAN_EQ_SELF] `subspace s /\ span s = t ==> s = t`) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBSPACE_SUMS; SUBSPACE_HYPERPLANE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM DIM_EQ_FULL] THEN
  REWRITE_TAC[GSYM LE_ANTISYM; DIM_SUBSET_UNIV] THEN
  MATCH_MP_TAC(ARITH_RULE `m - 1 < n ==> m <= n`) THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `dim {x:real^N | a dot x = &0}` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[DIM_HYPERPLANE; LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC DIM_PSUBSET THEN
  ASM_SIMP_TAC[snd(EQ_IMP_RULE(SPEC_ALL SPAN_EQ_SELF));
               SUBSPACE_SUMS; SUBSPACE_HYPERPLANE] THEN
  REWRITE_TAC[PSUBSET; SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `x:real^N`] THEN
    ASM_SIMP_TAC[SUBSPACE_0; VECTOR_ADD_LID];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[NOT_FORALL_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `x:real^N` THEN SIMP_TAC[IN_DIFF; IN_ELIM_THM] THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`x:real^N`; `vec 0:real^N`] THEN
    ASM_REWRITE_TAC[DOT_RZERO; VECTOR_ADD_RID]]);;

let AFF_DIM_AFFINE_INTER_HYPERPLANE = prove
 (`!a b s:real^N->bool.
        affine s
        ==> aff_dim(s INTER {x | a dot x = b}) =
                if s INTER {v | a dot v = b} = {} then -- &1
                else if s SUBSET {v | a dot v = b} then aff_dim s
                else aff_dim s - &1`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[DOT_LZERO] THEN ASM_CASES_TAC `b = &0` THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; INTER_EMPTY; AFF_DIM_EMPTY] THEN
    SIMP_TAC[SET_RULE `{x | T} = UNIV`; IN_UNIV; INTER_UNIV; SUBSET_UNIV] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY];
    STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN
    COND_CASES_TAC THENL [AP_TERM_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `{x:real^N | a dot x = b}`]
        AFF_DIM_SUMS_INTER) THEN
    ASM_SIMP_TAC[AFFINE_HYPERPLANE; AFF_DIM_HYPERPLANE] THEN
    ASM_SIMP_TAC[AFFINE_HYPERPLANE_SUMS_EQ_UNIV; AFF_DIM_UNIV;
                 SET_RULE `~(s SUBSET t) ==> ~(s DIFF t = {})`] THEN
    SPEC_TAC(`aff_dim (s INTER {x:real^N | a dot x = b})`,`i:int`) THEN
    INT_ARITH_TAC]);;

let AFF_DIM_LT_FULL = prove
 (`!s. aff_dim s < &(dimindex(:N)) <=> ~(affine hull s = (:real^N))`,
  GEN_TAC THEN REWRITE_TAC[GSYM AFF_DIM_EQ_FULL] THEN
  MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_LE_UNIV) THEN ARITH_TAC);;

let AFF_LOWDIM_SUBSET_HYPERPLANE = prove
 (`!s:real^N->bool.
        aff_dim s < &(dimindex(:N))
        ==> ?a b. ~(a = vec 0) /\ s SUBSET {x | a dot x = b}`,
  MATCH_MP_TAC SET_PROVE_CASES THEN CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `basis 1:real^N` THEN
    SIMP_TAC[EMPTY_SUBSET; BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1];
    MAP_EVERY X_GEN_TAC [`c:real^N`; `s:real^N->bool`] THEN
    CONV_TAC(ONCE_DEPTH_CONV(GEN_ALPHA_CONV `a:real^N`)) THEN
    GEN_GEOM_ORIGIN_TAC `c:real^N` ["a"] THEN
    SIMP_TAC[AFF_DIM_DIM_0; HULL_INC; IN_INSERT; INT_OF_NUM_LT] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP LOWDIM_SUBSET_HYPERPLANE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N` THEN
    STRIP_TAC THEN EXISTS_TAC `(u:real^N) dot c` THEN
    ASM_REWRITE_TAC[DOT_RADD; REAL_EQ_ADD_LCANCEL_0] THEN
    ASM_MESON_TAC[SPAN_INC; SUBSET_TRANS]]);;

(* ------------------------------------------------------------------------- *)
(* An additional lemma about hyperplanes.                                    *)
(* ------------------------------------------------------------------------- *)

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
  MP_TAC(ISPECL [`{x:real^N | a dot x = b}`; `{x:real^N | a' dot x = b'}`]
        AFF_DIM_PSUBSET) THEN
  ASM_SIMP_TAC[PSUBSET;
               REWRITE_RULE[GSYM AFFINE_HULL_EQ] AFFINE_HYPERPLANE] THEN
  ASM_CASES_TAC `{x:real^N | a dot x = b} = {x | a' dot x = b'}` THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_CASES_TAC `a':real^N = vec 0` THENL
   [ASM_CASES_TAC `b' = &0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_CASES_TAC `b = &0` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[AFF_DIM_HYPERPLANE; INT_LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Openness and compactness are preserved by convex hull operation.          *)
(* ------------------------------------------------------------------------- *)

let OPEN_CONVEX_HULL = prove
 (`!s:real^N->bool. open s ==> open(convex hull s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONVEX_HULL_EXPLICIT; OPEN_CONTAINS_CBALL] THEN
  REWRITE_TAC[IN_ELIM_THM; SUBSET; LEFT_IMP_EXISTS_THM] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `t:real^N->bool`; `u:real^N->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?b. !x:real^N. x IN t ==> &0 < b(x) /\ cball(x,b(x)) SUBSET s`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `i = IMAGE (b:real^N->real) t` THEN
  EXISTS_TAC `inf i` THEN MP_TAC(SPEC `i:real->bool` INF_FINITE) THEN
  EXPAND_TAC "i" THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_IMAGE] THEN
  ANTS_TAC THENL
   [EXPAND_TAC "i" THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE]; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    ASM_MESON_TAC[SUM_CLAUSES; REAL_ARITH `~(&1 = &0)`];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_CBALL; dist] THEN
  DISCH_TAC THEN EXISTS_TAC `IMAGE (\v:real^N. v + (y - a)) t` THEN
  EXISTS_TAC `\v. (u:real^N->real)(v - (y - a))` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; SUM_IMAGE; VSUM_IMAGE;
               VECTOR_ARITH `v + a:real^N = w + a <=> v = w`] THEN
  ASM_REWRITE_TAC[o_DEF; VECTOR_ARITH `(v + a) - a:real^N = v`] THEN
  ASM_REWRITE_TAC[VECTOR_ADD_LDISTRIB; ETA_AX] THEN
  ASM_SIMP_TAC[VSUM_ADD; VSUM_RMUL] THEN
  CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `z + (y - a) IN cball(z:real^N,b z)`
   (fun th -> ASM_MESON_TAC[th; SUBSET]) THEN
  REWRITE_TAC[IN_CBALL; dist; NORM_ARITH
   `norm(z - (z + a - y)) = norm(y - a)`] THEN
  ASM_MESON_TAC[REAL_LE_TRANS]);;

let COMPACT_CONVEX_COMBINATIONS = prove
 (`!s t. compact s /\ compact t
         ==> compact { (&1 - u) % x + u % y :real^N |
                      &0 <= u /\ u <= &1 /\ x IN s /\ y IN t}`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `{ (&1 - u) % x + u % y :real^N | &0 <= u /\ u <= &1 /\ x IN s /\ y IN t} =
    IMAGE (\z. (&1 - drop(fstcart z)) % fstcart(sndcart z) +
               drop(fstcart z) % sndcart(sndcart z))
          { pastecart u w | u IN interval[vec 0,vec 1] /\
                            w IN { pastecart x y | x IN s /\ y IN t} }`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV UNWIND_CONV) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[IN_INTERVAL_1; GSYM EXISTS_DROP; DROP_VEC] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[COMPACT_PCROSS; GSYM PCROSS; COMPACT_INTERVAL] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `z:real^(1,(N,N)finite_sum)finite_sum` THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[PCROSS] THEN
  MATCH_MP_TAC CONTINUOUS_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MUL THEN REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
  CONJ_TAC THEN TRY(MATCH_MP_TAC CONTINUOUS_SUB) THEN
  REWRITE_TAC[CONTINUOUS_CONST] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART; ETA_AX] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC LINEAR_COMPOSE THEN
  REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART]);;

let COMPACT_CONVEX_HULL = prove
 (`!s:real^N->bool. compact s ==> compact(convex hull s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CARATHEODORY] THEN
  SPEC_TAC(`dimindex(:N) + 1`,`n:num`) THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[SUBSET_EMPTY] THEN
    CONV_TAC(ONCE_DEPTH_CONV UNWIND_CONV) THEN
    REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY] THEN
    REWRITE_TAC[SET_RULE `{x | F} = {}`; COMPACT_EMPTY];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `w:real^N`) THEN INDUCT_TAC THENL
   [SUBGOAL_THEN
     `{x:real^N | ?t. FINITE t /\ t SUBSET s /\ CARD t <= 0 /\
                      x IN convex hull t} = {}`
     (fun th -> REWRITE_TAC[th; COMPACT_EMPTY]) THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; LE; IN_ELIM_THM] THEN
    MESON_TAC[CARD_EQ_0; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[ARITH_RULE `s <= SUC 0 <=> s = 0 \/ s = 1`] THEN
    UNDISCH_TAC `compact(s:real^N->bool)` THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    REWRITE_TAC[TAUT `a /\ b /\ (c \/ d) /\ e <=>
                      (a /\ c) /\ (b /\ e) \/ (a /\ d) /\ (b /\ e)`] THEN
    REWRITE_TAC[GSYM HAS_SIZE; num_CONV `1`; HAS_SIZE_CLAUSES] THEN
    REWRITE_TAC[EXISTS_OR_THM; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
    REWRITE_TAC[NOT_IN_EMPTY; CONVEX_HULL_EMPTY] THEN
    REWRITE_TAC[CONVEX_HULL_SING] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x:real^N | ?t. FINITE t /\ t SUBSET s /\ CARD t <= SUC n /\
                    x IN convex hull t} =
    { (&1 - u) % x + u % y :real^N |
                      &0 <= u /\ u <= &1 /\ x IN s /\
                      y IN {x | ?t. FINITE t /\ t SUBSET s /\
                                    CARD t <= n /\ x IN convex hull t}}`
   (fun th -> ASM_SIMP_TAC[th; COMPACT_CONVEX_COMBINATIONS]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM;
                LEFT_AND_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `c:real`; `v:real^N`;
                         `t:real^N->bool`] THEN
    STRIP_TAC THEN EXISTS_TAC `(u:real^N) INSERT t` THEN
    ASM_REWRITE_TAC[FINITE_INSERT; INSERT_SUBSET] THEN
    ASM_SIMP_TAC[CARD_CLAUSES] THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC IN_CONVEX_SET THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN CONJ_TAC THEN
    ASM_MESON_TAC[HULL_SUBSET; SUBSET; IN_INSERT; HULL_MONO]] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `CARD(t:real^N->bool) <= n` THENL
   [MAP_EVERY EXISTS_TAC [`w:real^N`; `&1`; `x:real^N`] THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^N->bool) HAS_SIZE (SUC n)` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[HAS_SIZE_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `u:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  UNDISCH_TAC `(x:real^N) IN convex hull (a INSERT u)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FINITE_INSERT]) THEN
  ASM_CASES_TAC `(u:real^N->bool) = {}` THENL
   [ASM_REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `&1`; `a:real^N`] THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
    CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `{a:real^N}` THEN SIMP_TAC[FINITE_RULES] THEN
    REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY] THEN
    UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_HULL_INSERT; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `d:real`; `z:real^N`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `d:real`; `z:real^N`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
   `c + d = &1 ==> c = (&1 - d)`)) THEN
  ASM_REWRITE_TAC[REAL_ARITH `d <= &1 <=> &0 <= &1 - d`] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `CARD ((a:real^N) INSERT u) <= SUC n` THEN
  ASM_SIMP_TAC[CARD_CLAUSES; LE_SUC]);;

let FINITE_IMP_COMPACT_CONVEX_HULL = prove
 (`!s:real^N->bool. FINITE s ==> compact(convex hull s)`,
  SIMP_TAC[FINITE_IMP_COMPACT; COMPACT_CONVEX_HULL]);;

let CONVEX_HULL_INTERIOR_SUBSET = prove
 (`!s:real^N->bool. convex hull (interior s) SUBSET interior (convex hull s)`,
  GEN_TAC THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN
  SIMP_TAC[OPEN_CONVEX_HULL; OPEN_INTERIOR; HULL_MONO; INTERIOR_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Extremal points of a simplex are some vertices.                           *)
(* ------------------------------------------------------------------------- *)

let DIST_INCREASES_ONLINE = prove
 (`!a b d. ~(d = vec 0)
           ==> dist(a,b + d) > dist(a,b) \/ dist(a,b - d) > dist(a,b)`,
  REWRITE_TAC[dist; vector_norm; real_gt; GSYM NORM_POS_LT] THEN
  SIMP_TAC[SQRT_MONO_LT_EQ; DOT_POS_LE; SQRT_LT_0] THEN
  REWRITE_TAC[DOT_RSUB; DOT_RADD; DOT_LSUB; DOT_LADD] THEN REAL_ARITH_TAC);;

let NORM_INCREASES_ONLINE = prove
 (`!a:real^N d. ~(d = vec 0)
                ==> norm(a + d) > norm(a) \/ norm(a - d) > norm(a)`,
  MP_TAC(ISPEC `vec 0 :real^N` DIST_INCREASES_ONLINE) THEN
  REWRITE_TAC[dist; VECTOR_SUB_LZERO; NORM_NEG]);;

let SIMPLEX_FURTHEST_LT = prove
 (`!a:real^N s.
        FINITE s
        ==> !x. x IN (convex hull s) /\ ~(x IN s)
                ==> ?y. y IN (convex hull s) /\ norm(x - a) < norm(y - a)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `s:real^N->bool`] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_HULL_INSERT] THEN
  STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real`; `v:real`; `b:real^N`] THEN
  ASM_CASES_TAC `y:real^N IN (convex hull s)` THENL
   [REWRITE_TAC[IN_INSERT; DE_MORGAN_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `c:real^N` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`; `c:real^N`] THEN
    ASM_REWRITE_TAC[REAL_ADD_LID; REAL_POS] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `u = &0` THENL
   [ASM_SIMP_TAC[REAL_ADD_LID; VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
    ASM_MESON_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_CASES_TAC `v = &0` THENL
   [ASM_SIMP_TAC[REAL_ADD_RID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    ASM_CASES_TAC `u = &1` THEN ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN
    ASM_CASES_TAC `y = a:real^N` THEN ASM_REWRITE_TAC[IN_INSERT] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; DE_MORGAN_THM] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:real`; `v:real`] REAL_DOWN2) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^N`; `y:real^N`; `w % (x - b):real^N`]
                DIST_INCREASES_ONLINE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[VECTOR_ARITH `(x - y = vec 0) <=> (x = y)`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(y:real^N IN convex hull s)` THEN
    ASM_REWRITE_TAC[GSYM VECTOR_ADD_RDISTRIB; VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[dist; real_gt] THEN
  REWRITE_TAC[VECTOR_ARITH
   `((u % x + v % b) + w % (x - b) = (u + w) % x + (v - w) % b) /\
    ((u % x + v % b) - w % (x - b) = (u - w) % x + (v + w) % b)`] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`(u + w) % x + (v - w) % b:real^N`; `u + w`; `v - w`; `b:real^N`];
    MAP_EVERY EXISTS_TAC
     [`(u - w) % x + (v + w) % b:real^N`; `u - w`; `v + w`; `b:real^N`]] THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_ADD; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
  UNDISCH_TAC `u + v = &1` THEN REAL_ARITH_TAC);;

let SIMPLEX_FURTHEST_LE = prove
 (`!a:real^N s.
        FINITE s /\ ~(s = {})
        ==> ?y. y IN s /\
                !x. x IN (convex hull s) ==> norm(x - a) <= norm(y - a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `convex hull (s:real^N->bool)` DISTANCE_ATTAINS_SUP) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMP_COMPACT_CONVEX_HULL] THEN
    ASM_MESON_TAC[SUBSET_EMPTY; HULL_SUBSET];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
  ASM_MESON_TAC[SIMPLEX_FURTHEST_LT; REAL_NOT_LE]);;

let SIMPLEX_FURTHEST_LE_EXISTS = prove
 (`!a:real^N s.
        FINITE s
        ==> !x. x IN (convex hull s)
                ==> ?y. y IN s /\ norm(x - a) <= norm(y - a)`,
  MESON_TAC[NOT_IN_EMPTY; CONVEX_HULL_EMPTY; SIMPLEX_FURTHEST_LE]);;

let SIMPLEX_EXTREMAL_LE = prove
 (`!s:real^N->bool.
        FINITE s /\ ~(s = {})
         ==> ?u v. u IN s /\ v IN s /\
                   !x y. x IN convex hull s /\ y IN convex hull s
                         ==> norm(x - y) <= norm(u - v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `convex hull (s:real^N->bool)` COMPACT_SUP_MAXDISTANCE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMP_COMPACT_CONVEX_HULL] THEN
    ASM_MESON_TAC[SUBSET_EMPTY; HULL_SUBSET];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  SIMP_TAC[] THEN ASM_MESON_TAC[SIMPLEX_FURTHEST_LT; REAL_NOT_LE; NORM_SUB]);;

let SIMPLEX_EXTREMAL_LE_EXISTS = prove
 (`!s:real^N->bool x y. FINITE s /\ x IN convex hull s /\ y IN convex hull s
                        ==> ?u v. u IN s /\ v IN s /\
                                  norm(x - y) <= norm(u - v)`,
  MESON_TAC[NOT_IN_EMPTY; CONVEX_HULL_EMPTY; SIMPLEX_EXTREMAL_LE]);;

let DIAMETER_CONVEX_HULL = prove
 (`!s:real^N->bool. diameter(convex hull s) = diameter s`,
  let lemma = prove
   (`!a b s. (!x. x IN s ==> dist(a,x) <= b)
             ==> (!x. x IN convex hull s ==> dist(a,x) <= b)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC HULL_INDUCT THEN ASM_REWRITE_TAC[GSYM cball; CONVEX_CBALL]) in
  GEN_TAC THEN REWRITE_TAC[diameter; CONVEX_HULL_EQ_EMPTY] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUP_EQ THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `b:real` THEN
  EQ_TAC THENL [MESON_TAC[SUBSET; HULL_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `!b. (a ==> b) /\ (b ==> c) ==> a ==> c`) THEN
  EXISTS_TAC `!x:real^N y. x IN s /\ y IN convex hull s ==> norm(x - y) <= b`
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM dist; lemma];
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `y:real^N` THEN
    ASM_CASES_TAC `(y:real^N) IN convex hull s` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[DIST_SYM] dist); lemma]]);;

let DIAMETER_SIMPLEX = prove
 (`!s:real^N->bool.
        ~(s = {})
        ==> diameter(convex hull s) = sup { dist(x,y) | x IN s /\ y IN s}`,
  REWRITE_TAC[DIAMETER_CONVEX_HULL] THEN SIMP_TAC[diameter; dist]);;

(* ------------------------------------------------------------------------- *)
(* Closest point of a convex set is unique, with a continuous projection.    *)
(* ------------------------------------------------------------------------- *)

let CLOSER_POINTS_LEMMA = prove
 (`!y:real^N z.
        y dot z > &0
        ==> ?u. &0 < u /\
                !v. &0 < v /\ v <= u ==> norm(v % z - y) < norm y`,
  REWRITE_TAC[NORM_LT; DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL;
              REAL_SUB_LDISTRIB; real_gt] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `(a - b) - (c - d) < d <=> a < b + c`] THEN
  STRIP_TAC THEN SUBST1_TAC(VECTOR_ARITH `(z:real^N) dot y = y dot z`) THEN
  SIMP_TAC[GSYM REAL_ADD_LDISTRIB; REAL_LT_LMUL_EQ] THEN
  EXISTS_TAC `(y dot (z:real^N)) / (z dot z)` THEN
  SUBGOAL_THEN `&0 < z dot (z:real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[DOT_POS_LT; DOT_RZERO; REAL_LT_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_RDIV_EQ] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < y /\ x <= y ==> x < y + y`; REAL_LT_MUL]);;

let CLOSER_POINT_LEMMA = prove
 (`!x y z. (y - x) dot (z - x) > &0
           ==> ?u. &0 < u /\ u <= &1 /\ dist(x + u % (z - x),y) < dist(x,y)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP CLOSER_POINTS_LEMMA) THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist; NORM_LT] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(y - (x + z)) dot (y - (x + z)) = (z - (y - x)) dot (z - (y - x))`] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min u (&1)` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LT_01; REAL_LE_REFL]);;

let ANY_CLOSEST_POINT_DOT = prove
 (`!s a x y:real^N.
        convex s /\ closed s /\ x IN s /\ y IN s /\
        (!z. z IN s ==> dist(a,x) <= dist(a,z))
        ==> (a - x) dot (y - x) <= &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ARITH `x <= &0 <=> ~(x > &0)`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CLOSER_POINT_LEMMA) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[REAL_NOT_LT] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `x + u % (y - x) = (&1 - u) % x + u % y`] THEN
  MATCH_MP_TAC IN_CONVEX_SET THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let ANY_CLOSEST_POINT_UNIQUE = prove
 (`!s a x y:real^N.
        convex s /\ closed s /\ x IN s /\ y IN s /\
        (!z. z IN s ==> dist(a,x) <= dist(a,z)) /\
        (!z. z IN s ==> dist(a,y) <= dist(a,z))
        ==> x = y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  REWRITE_TAC[GSYM NORM_LE_0; NORM_LE_SQUARE] THEN
  SUBGOAL_THEN `(a - x:real^N) dot (y - x) <= &0 /\ (a - y) dot (x - y) <= &0`
  MP_TAC THENL [ASM_MESON_TAC[ANY_CLOSEST_POINT_DOT]; ALL_TAC] THEN
  REWRITE_TAC[NORM_LT; DOT_LSUB; DOT_RSUB] THEN REAL_ARITH_TAC);;

let CLOSEST_POINT_UNIQUE = prove
 (`!s a x:real^N.
        convex s /\ closed s /\ x IN s /\
        (!z. z IN s ==> dist(a,x) <= dist(a,z))
        ==> x = closest_point s a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ANY_CLOSEST_POINT_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `a:real^N`] THEN
  ASM_MESON_TAC[CLOSEST_POINT_EXISTS; MEMBER_NOT_EMPTY]);;

let CLOSEST_POINT_DOT = prove
 (`!s a x:real^N.
        convex s /\ closed s /\ x IN s
        ==> (a - closest_point s a) dot (x - closest_point s a) <= &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ANY_CLOSEST_POINT_DOT THEN
  EXISTS_TAC `s:real^N->bool` THEN
  ASM_MESON_TAC[CLOSEST_POINT_EXISTS; MEMBER_NOT_EMPTY]);;

let CLOSEST_POINT_LT = prove
 (`!s a x. convex s /\ closed s /\ x IN s /\ ~(x = closest_point s a)
           ==> dist(a,closest_point s a) < dist(a,x)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE; CONTRAPOS_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC CLOSEST_POINT_UNIQUE THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[CLOSEST_POINT_LE; REAL_LE_TRANS]);;

let CLOSEST_POINT_LIPSCHITZ = prove
 (`!s x y:real^N.
        convex s /\ closed s /\ ~(s = {})
        ==> dist(closest_point s x,closest_point s y) <= dist(x,y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dist; NORM_LE] THEN
  SUBGOAL_THEN
   `(x - closest_point s x :real^N) dot
    (closest_point s y - closest_point s x) <= &0 /\
    (y - closest_point s y) dot
    (closest_point s x - closest_point s y) <= &0`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ANY_CLOSEST_POINT_DOT THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_MESON_TAC[CLOSEST_POINT_EXISTS];
    MP_TAC(ISPEC `(x - closest_point s x :real^N) - (y - closest_point s y)`
                 DOT_POS_LE) THEN
    REWRITE_TAC[NORM_LT; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN REAL_ARITH_TAC]);;

let CONTINUOUS_AT_CLOSEST_POINT = prove
 (`!s x. convex s /\ closed s /\ ~(s = {})
         ==> (closest_point s) continuous (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[continuous_at] THEN
  ASM_MESON_TAC[CLOSEST_POINT_LIPSCHITZ; REAL_LET_TRANS]);;

let CONTINUOUS_ON_CLOSEST_POINT = prove
 (`!s t. convex s /\ closed s /\ ~(s = {})
         ==> (closest_point s) continuous_on t`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_CLOSEST_POINT]);;

(* ------------------------------------------------------------------------- *)
(* Relating closest points and orthogonality.                                *)
(* ------------------------------------------------------------------------- *)

let ANY_CLOSEST_POINT_AFFINE_ORTHOGONAL = prove
 (`!s a b:real^N.
        affine s /\ b IN s /\ (!x. x IN s ==> dist(a,b) <= dist(a,x))
        ==> (!x. x IN s ==> orthogonal (x - b) (a - b))`,
  REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC `b:real^N` THEN
  REWRITE_TAC[DIST_0; VECTOR_SUB_RZERO; orthogonal; dist; NORM_LE] THEN
  REWRITE_TAC[DOT_LSUB] THEN REWRITE_TAC[DOT_RSUB] THEN
  REWRITE_TAC[DOT_SYM; REAL_ARITH `a <= a - y - (y - x) <=> &2 * y <= x`] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_RZERO] THEN FIRST_X_ASSUM(fun th ->
   MP_TAC(SPEC `vec 0 + --((a dot x) / (x dot x)) % (x - vec 0:real^N)` th) THEN
   MP_TAC(SPEC `vec 0 + (a dot x) / (x dot x) % (x - vec 0:real^N)` th)) THEN
  ASM_SIMP_TAC[IN_AFFINE_ADD_MUL_DIFF] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; VECTOR_ADD_LID; DOT_RMUL] THEN
  REWRITE_TAC[DOT_LMUL; IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `&2 * x * a <= b * c * z /\ &2 * --x * a <= --b * --c * z
    ==> &2 * abs(x * a) <= b * c * z`)) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_NOT_LE; REAL_DIV_RMUL; DOT_EQ_0] THEN
  MATCH_MP_TAC(REAL_ARITH `~(x = &0) ==> x < &2 * abs x`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM DOT_EQ_0]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let ORTHOGONAL_ANY_CLOSEST_POINT = prove
 (`!s a b:real^N.
        b IN s /\ (!x. x IN s ==> orthogonal (x - b) (a - b))
        ==> (!x. x IN s ==> dist(a,b) <= dist(a,x))`,
  REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC `b:real^N` THEN
  REWRITE_TAC[dist; NORM_LE; orthogonal; VECTOR_SUB_RZERO] THEN
  SIMP_TAC[DOT_LSUB; DOT_RSUB; DOT_SYM] THEN
  REWRITE_TAC[DOT_POS_LE; REAL_ARITH `a <= a - &0 - (&0 - x) <=> &0 <= x`]);;

let CLOSEST_POINT_AFFINE_ORTHOGONAL = prove
 (`!s a:real^N x.
        affine s /\ ~(s = {}) /\ x IN s
        ==> orthogonal (x - closest_point s a) (a - closest_point s a)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC ANY_CLOSEST_POINT_AFFINE_ORTHOGONAL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSEST_POINT_EXISTS THEN
  ASM_SIMP_TAC[CLOSED_AFFINE]);;

let CLOSEST_POINT_AFFINE_ORTHOGONAL_EQ = prove
 (`!s a b:real^N.
        affine s /\ b IN s
        ==> (closest_point s a = b <=>
             !x. x IN s ==> orthogonal (x - b) (a - b))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[CLOSEST_POINT_AFFINE_ORTHOGONAL; MEMBER_NOT_EMPTY];
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CLOSEST_POINT_UNIQUE THEN
    ASM_SIMP_TAC[CLOSED_AFFINE; AFFINE_IMP_CONVEX] THEN
    MATCH_MP_TAC ORTHOGONAL_ANY_CLOSEST_POINT THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Various point-to-set separating/supporting hyperplane theorems.           *)
(* ------------------------------------------------------------------------- *)

let SUPPORTING_HYPERPLANE_COMPACT_POINT_SUP = prove
 (`!a c s:real^N->bool.
        compact s /\ ~(s = {})
        ==> ?b y. y IN s /\ a dot (y - c) = b /\
                  (!x. x IN s ==> a dot (x - c) <= b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. a dot (x - c)`; `s:real^N->bool`]
        CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  SUBGOAL_THEN `(\x:real^N. a dot (x - c)) = (\x. a dot x) o (\x. x - c)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[CONTINUOUS_ON_LIFT_DOT; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST;
           CONTINUOUS_ON_ID]);;

let SUPPORTING_HYPERPLANE_COMPACT_POINT_INF = prove
 (`!a c s:real^N->bool.
        compact s /\ ~(s = {})
        ==> ?b y. y IN s /\ a dot (y - c) = b /\
                  (!x. x IN s ==> a dot (x - c) >= b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`--a:real^N`; `c:real^N`; `s:real^N->bool`]
    SUPPORTING_HYPERPLANE_COMPACT_POINT_SUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real`
   (fun th -> EXISTS_TAC `--b:real` THEN MP_TAC th)) THEN
  REWRITE_TAC[DOT_LNEG; REAL_ARITH `x >= -- b <=> --x <= b`] THEN
  REWRITE_TAC[REAL_NEG_EQ]);;

let SUPPORTING_HYPERPLANE_CLOSED_POINT = prove
 (`!s z:real^N. convex s /\ closed s /\ ~(s = {}) /\ ~(z IN s)
                ==> ?a b y. a dot z < b /\ y IN s /\ (a dot y = b) /\
                            (!x. x IN s ==> a dot x >= b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `z:real^N`] DISTANCE_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y - z:real^N` THEN EXISTS_TAC `(y - z:real^N) dot y` THEN
  EXISTS_TAC `y:real^N` THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  ASM_REWRITE_TAC[GSYM DOT_RSUB; DOT_POS_LT; VECTOR_SUB_EQ] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_TAC THEN SUBGOAL_THEN
   `!u. &0 <= u /\ u <= &1 ==> dist(z:real^N,y) <= dist(z,(&1 - u) % y + u % x)`
  MP_TAC THENL [ASM_MESON_TAC[CONVEX_ALT]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  REWRITE_TAC[real_ge; REAL_NOT_LE; NOT_FORALL_THM; NOT_IMP] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `x < y <=> y - x > &0`] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(a - b) dot x - (a - b) dot y = (b - a) dot (y - x)`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CLOSER_POINT_LEMMA) THEN
  REWRITE_TAC[VECTOR_ARITH `y + u % (x - y) = (&1 - u) % y + u % x`] THEN
  MESON_TAC[REAL_LT_IMP_LE]);;

let SEPARATING_HYPERPLANE_CLOSED_POINT_INSET = prove
 (`!s z:real^N. convex s /\ closed s /\ ~(s = {}) /\ ~(z IN s)
                ==> ?a b. a IN s /\
                          (a - z) dot z < b /\
                          (!x. x IN s ==> (a - z) dot x > b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `z:real^N`] DISTANCE_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(y - z:real^N) dot z + norm(y - z) pow 2 / &2` THEN
  SUBGOAL_THEN `&0 < norm(y - z:real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_ADDR; REAL_LT_DIV; REAL_POW_LT;
               REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[NORM_POW_2; REAL_ARITH `a > b + c <=> c < a - b`] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  REWRITE_TAC[VECTOR_ARITH
   `((y - z) dot x - (y - z) dot z) * &2 - (y - z) dot (y - z) =
    &2 * ((y - z) dot (x - y)) + (y - z) dot (y - z)`] THEN
  MATCH_MP_TAC(REAL_ARITH `~(--x > &0) /\ &0 < y ==> &0 < &2 * x + y`) THEN
  ASM_SIMP_TAC[GSYM NORM_POW_2; REAL_POW_LT] THEN
  REWRITE_TAC[GSYM DOT_LNEG; VECTOR_NEG_SUB] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CLOSER_POINT_LEMMA) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[REAL_NOT_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `y + u % (x - y) = (&1 - u) % y + u % x`] THEN
  ASM_MESON_TAC[CONVEX_ALT; REAL_LT_IMP_LE]);;

let SEPARATING_HYPERPLANE_CLOSED_0_INSET = prove
 (`!s:real^N->bool.
        convex s /\ closed s /\ ~(s = {}) /\ ~(vec 0 IN s)
        ==> ?a b. a IN s /\ ~(a = vec 0) /\ &0 < b /\
                  (!x. x IN s ==> a dot x > b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SEPARATING_HYPERPLANE_CLOSED_POINT_INSET) THEN
  REWRITE_TAC[DOT_RZERO; real_gt] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  SIMP_TAC[VECTOR_SUB_RZERO] THEN ASM_MESON_TAC[]);;

let SEPARATING_HYPERPLANE_CLOSED_POINT = prove
 (`!s z:real^N. convex s /\ closed s /\ ~(z IN s)
                ==> ?a b. a dot z < b /\ (!x. x IN s ==> a dot x > b)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`--z:real^N`; `&1`] THEN
    SIMP_TAC[DOT_LNEG; REAL_ARITH `&0 <= x ==> --x < &1`; DOT_POS_LE] THEN
    ASM_MESON_TAC[NOT_IN_EMPTY];
    ALL_TAC] THEN
  ASM_MESON_TAC[SEPARATING_HYPERPLANE_CLOSED_POINT_INSET]);;

let SEPARATING_HYPERPLANE_CLOSED_0 = prove
 (`!s:real^N->bool.
        convex s /\ closed s /\ ~(vec 0 IN s)
        ==> ?a b. ~(a = vec 0) /\ &0 < b /\ (!x. x IN s ==> a dot x > b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [EXISTS_TAC `basis 1:real^N` THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01; GSYM NORM_POS_LT] THEN
    ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL; REAL_LT_01];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP SEPARATING_HYPERPLANE_CLOSED_POINT) THEN
    REWRITE_TAC[DOT_RZERO; real_gt] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    ASM_MESON_TAC[MEMBER_NOT_EMPTY; DOT_LZERO; REAL_LT_ANTISYM]]);;

(* ------------------------------------------------------------------------- *)
(* Now set-to-set for closed/compact sets.                                   *)
(* ------------------------------------------------------------------------- *)

let SEPARATING_HYPERPLANE_CLOSED_COMPACT = prove
 (`!s t. convex s /\ closed s /\
         convex t /\ compact t /\ ~(t = {}) /\ DISJOINT s t
         ==> ?a:real^N b. (!x. x IN s ==> a dot x < b) /\
                          (!x. x IN t ==> a dot x > b)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?z:real^N. norm(z) = b + &1` CHOOSE_TAC THENL
     [ASM_SIMP_TAC[VECTOR_CHOOSE_SIZE; REAL_ARITH `&0 < b ==> &0 <= b + &1`];
      ALL_TAC] THEN
    MP_TAC(SPECL [`t:real^N->bool`; `z:real^N`]
       SEPARATING_HYPERPLANE_CLOSED_POINT) THEN
    ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    ASM_MESON_TAC[REAL_ARITH `~(b + &1 <= b)`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{x - y:real^N | x IN s /\ y IN t}`; `vec 0 :real^N`]
                SEPARATING_HYPERPLANE_CLOSED_POINT) THEN
  ASM_SIMP_TAC[CLOSED_COMPACT_DIFFERENCES; CONVEX_DIFFERENCES] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN
    ASM_MESON_TAC[DISJOINT; NOT_IN_EMPTY; IN_INTER; EXTENSION];
    ALL_TAC] THEN
  SIMP_TAC[DOT_RZERO; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SWAP_FORALL_THM] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL; DOT_RSUB] THEN
  REWRITE_TAC[real_gt; REAL_LT_SUB_LADD] THEN DISCH_TAC THEN
  EXISTS_TAC `--a:real^N` THEN
  MP_TAC(SPEC `IMAGE (\x:real^N. a dot x) t` SUP) THEN
  ABBREV_TAC `k = sup (IMAGE (\x:real^N. a dot x) t)` THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_ARITH `b + x < y ==> x <= y - b`; MEMBER_NOT_EMPTY];
    ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `--(k + b / &2)` THEN
  REWRITE_TAC[DOT_LNEG; REAL_LT_NEG2] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH;
               REAL_ARITH `&0 < b /\ x <= k ==> x < k + b`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k - b / &2`) THEN
  ASM_SIMP_TAC[REAL_ARITH `k <= k - b2 <=> ~(&0 < b2)`; REAL_LT_DIV;
     REAL_OF_NUM_LT; ARITH; NOT_FORALL_THM; LEFT_IMP_EXISTS_THM; NOT_IMP] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH
   `!b. (b2 + b2 = b) /\ b + ay < ax ==> ~(ay <= k - b2) ==> k + b2 < ax`) THEN
  ASM_MESON_TAC[REAL_HALF]);;

let SEPARATING_HYPERPLANE_COMPACT_CLOSED = prove
 (`!s t. convex s /\ compact s /\ ~(s = {}) /\
         convex t /\ closed t /\ DISJOINT s t
         ==> ?a:real^N b. (!x. x IN s ==> a dot x < b) /\
                          (!x. x IN t ==> a dot x > b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `s:real^N->bool`]
      SEPARATING_HYPERPLANE_CLOSED_COMPACT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DISJOINT_SYM]; ALL_TAC] THEN
  REWRITE_TAC[real_gt] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`--a:real^N`; `--b:real`] THEN
  ASM_REWRITE_TAC[REAL_LT_NEG2; DOT_LNEG]);;

let SEPARATING_HYPERPLANE_COMPACT_CLOSED_NONZERO = prove
 (`!s t:real^N->bool.
           convex s /\ compact s /\ ~(s = {}) /\
           convex t /\ closed t /\ DISJOINT s t
           ==> ?a b. ~(a = vec 0) /\
                     (!x. x IN s ==> a dot x < b) /\
                     (!x. x IN t ==> a dot x > b)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN STRIP_TAC THEN
    EXISTS_TAC `basis 1:real^N` THEN
    SUBGOAL_THEN
     `bounded(IMAGE (\x:real^N. lift(basis 1 dot x)) s)`
    MP_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_DOT];
      REWRITE_TAC[BOUNDED_POS_LT; FORALL_IN_IMAGE; NORM_LIFT] THEN
      SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL] THEN
      MESON_TAC[REAL_ARITH `abs x < b ==> x < b`]];
    STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`]
        SEPARATING_HYPERPLANE_COMPACT_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    ASM_CASES_TAC `a:real^N = vec 0` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DOT_LZERO; real_gt] THEN
    ASM_MESON_TAC[REAL_LT_ANTISYM; MEMBER_NOT_EMPTY]]);;

let SEPARATING_HYPERPLANE_COMPACT_COMPACT = prove
 (`!s t:real^N->bool.
           convex s /\ compact s /\ convex t /\ compact t /\ DISJOINT s t
           ==> ?a b. ~(a = vec 0) /\
                     (!x. x IN s ==> a dot x < b) /\
                     (!x. x IN t ==> a dot x > b)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN STRIP_TAC THEN
    EXISTS_TAC `--basis 1:real^N` THEN
    SUBGOAL_THEN
     `bounded(IMAGE (\x:real^N. lift(basis 1 dot x)) t)`
    MP_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_DOT];
      REWRITE_TAC[BOUNDED_POS_LT; FORALL_IN_IMAGE; NORM_LIFT] THEN
      SIMP_TAC[VECTOR_NEG_EQ_0; BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL] THEN
      DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `--b:real` THEN REWRITE_TAC[DOT_LNEG] THEN
      REWRITE_TAC[REAL_ARITH `--x > --y <=> x < y`] THEN
      ASM_MESON_TAC[REAL_ARITH `abs x < b ==> x < b`]];
    STRIP_TAC THEN
    MATCH_MP_TAC SEPARATING_HYPERPLANE_COMPACT_CLOSED_NONZERO THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]);;

(* ------------------------------------------------------------------------- *)
(* General case without assuming closure and getting non-strict separation.  *)
(* ------------------------------------------------------------------------- *)

let SEPARATING_HYPERPLANE_SET_0_INSPAN = prove
 (`!s:real^N->bool.
        convex s /\ ~(s = {}) /\ ~(vec 0 IN s)
        ==> ?a b. a IN span s /\ ~(a = vec 0) /\
                  !x. x IN s ==> &0 <= a dot x`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `k = \c:real^N. {x | &0 <= c dot x}` THEN
  SUBGOAL_THEN
   `~((span s INTER frontier(cball(vec 0:real^N,&1))) INTER
      (INTERS (IMAGE k (s:real^N->bool))) = {})`
  MP_TAC THENL
   [ALL_TAC;
    SIMP_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_INTERS; NOT_FORALL_THM;
             FORALL_IN_IMAGE; FRONTIER_CBALL; REAL_LT_01] THEN
    EXPAND_TAC "k" THEN REWRITE_TAC[IN_SPHERE_0; IN_ELIM_THM; NORM_NEG] THEN
    MESON_TAC[NORM_EQ_0; REAL_ARITH `~(&1 = &0)`; DOT_SYM]] THEN
  MATCH_MP_TAC COMPACT_IMP_FIP THEN
  SIMP_TAC[COMPACT_CBALL; COMPACT_FRONTIER; FORALL_IN_IMAGE;
           CLOSED_INTER_COMPACT; CLOSED_SPAN] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[GSYM real_ge; CLOSED_HALFSPACE_GE];
    ALL_TAC] THEN
  REWRITE_TAC[FINITE_SUBSET_IMAGE] THEN GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` MP_TAC) THEN
  ASM_CASES_TAC `c:real^N->bool = {}` THENL
   [ASM_SIMP_TAC[INTERS_0; INTER_UNIV; IMAGE_CLAUSES] THEN
    DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    SUBGOAL_THEN `~(a:real^N = vec 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `inv(norm a) % a:real^N` THEN
    ASM_SIMP_TAC[IN_INTER; FRONTIER_CBALL; SPAN_CLAUSES; IN_SPHERE_0] THEN
    REWRITE_TAC[DIST_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `convex hull (c:real^N->bool)`
      SEPARATING_HYPERPLANE_CLOSED_0_INSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN
    ASM_MESON_TAC[CONVEX_CONVEX_HULL; SUBSET; SUBSET_HULL; HULL_SUBSET;
                  FINITE_IMP_COMPACT_CONVEX_HULL; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_RZERO; real_gt] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_INTERS; FORALL_IN_IMAGE] THEN
  EXPAND_TAC "k" THEN SIMP_TAC[IN_ELIM_THM; FRONTIER_CBALL; REAL_LT_01] THEN
  REWRITE_TAC[dist; VECTOR_SUB_LZERO; NORM_NEG] THEN
  EXISTS_TAC `inv(norm(a)) % a:real^N` THEN REWRITE_TAC[DOT_RMUL] THEN
  SUBGOAL_THEN `(a:real^N) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; HULL_MINIMAL]; ASM_SIMP_TAC[SPAN_CLAUSES]] THEN
  REWRITE_TAC[IN_SPHERE_0; VECTOR_SUB_LZERO; NORM_NEG; NORM_MUL] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NORM] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_EQ_LDIV_EQ; NORM_POS_LT] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
  ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS; HULL_SUBSET; SUBSET; DOT_SYM]);;

let SEPARATING_HYPERPLANE_SET_POINT_INAFF = prove
 (`!s z:real^N.
        convex s /\ ~(s = {}) /\ ~(z IN s)
        ==> ?a b. (z + a) IN affine hull (z INSERT s) /\ ~(a = vec 0) /\
                  a dot z <= b /\ (!x. x IN s ==> a dot x >= b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (\x:real^N. --z + x) s`
     SEPARATING_HYPERPLANE_SET_0_INSPAN) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; CONVEX_TRANSLATION; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[IN_IMAGE; VECTOR_ARITH `vec 0:real^N = --z + x <=> x = z`] THEN
  ASM_SIMP_TAC[UNWIND_THM2; AFFINE_HULL_INSERT_SPAN; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  REWRITE_TAC[GSYM SIMPLE_IMAGE; VECTOR_ARITH `--x + y:real^N = y - x`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(a:real^N) dot z` THEN REWRITE_TAC[REAL_LE_REFL] THEN
  ASM_REWRITE_TAC[REAL_ARITH `x >= y <=> &0 <= x - y`; GSYM DOT_RSUB]);;

let SEPARATING_HYPERPLANE_SET_0 = prove
 (`!s:real^N->bool.
        convex s /\ ~(vec 0 IN s)
        ==> ?a b. ~(a = vec 0) /\ !x. x IN s ==> &0 <= a dot x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
    MESON_TAC[BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1];
    ASM_MESON_TAC[SEPARATING_HYPERPLANE_SET_0_INSPAN]]);;

let SEPARATING_HYPERPLANE_SETS = prove
 (`!s t. convex s /\ convex t /\ ~(s = {}) /\ ~(t = {}) /\ DISJOINT s t
         ==> ?a:real^N b. ~(a = vec 0) /\
                          (!x. x IN s ==> a dot x <= b) /\
                          (!x. x IN t ==> a dot x >= b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{y - x:real^N | y IN t /\ x IN s}`
                SEPARATING_HYPERPLANE_SET_0) THEN
  ASM_SIMP_TAC[CONVEX_DIFFERENCES] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN
    ASM_MESON_TAC[DISJOINT; NOT_IN_EMPTY; IN_INTER; EXTENSION];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  SIMP_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SWAP_FORALL_THM] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL; DOT_RSUB; REAL_SUB_LE] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `IMAGE (\x:real^N. a dot x) s` SUP) THEN
  ABBREV_TAC `k = sup (IMAGE (\x:real^N. a dot x) s)` THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY; real_ge] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* More convexity generalities.                                              *)
(* ------------------------------------------------------------------------- *)

let CONVEX_CLOSURE = prove
 (`!s:real^N->bool. convex s ==> convex(closure s)`,
  REWRITE_TAC[convex; CLOSURE_SEQUENTIAL] THEN
  GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:num->real^N`) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `b:num->real^N`) MP_TAC) THEN
  STRIP_TAC THEN EXISTS_TAC `\n:num. u % a(n) + v % b(n) :real^N` THEN
  ASM_SIMP_TAC[LIM_ADD; LIM_CMUL]);;

let CONVEX_INTERIOR = prove
 (`!s:real^N->bool. convex s ==> convex(interior s)`,
  REWRITE_TAC[CONVEX_ALT; IN_INTERIOR; SUBSET; IN_BALL; dist] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `d:real`) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `e:real`) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d e` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  SUBST1_TAC(VECTOR_ARITH `z:real^N =
   (&1 - u) % (z - u % (y - x)) + u % (z + (&1 - u) % (y - x))`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[VECTOR_ARITH `x - (z - u % (y - x)) =
                                ((&1 - u) % x + u % y) - z:real^N`;
                VECTOR_ARITH `y - (z + (&1 - u) % (y - x)) =
                                ((&1 - u) % x + u % y) - z:real^N`]);;

let CONVEX_ON_SETDIST = prove
 (`!s t:real^N->bool. convex t ==> (\x. setdist ({x},t)) convex_on s`,
  SUBGOAL_THEN
   `!s t:real^N->bool. convex t /\ closed t
                       ==> (\x. setdist ({x},t)) convex_on s`
  MP_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
      SPECL [`s:real^N->bool`; `closure t:real^N->bool`]) THEN
    ASM_SIMP_TAC[CLOSED_CLOSURE; SETDIST_CLOSURE; CONVEX_CLOSURE]] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[convex_on] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_SIMP_TAC[SETDIST_EMPTY; REAL_MUL_RZERO; REAL_ADD_RID; REAL_LE_REFL] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`{x:real^N}`; `t:real^N->bool`] SETDIST_COMPACT_CLOSED) THEN
  MP_TAC(ISPECL [`{y:real^N}`; `t:real^N->bool`] SETDIST_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY; COMPACT_SING; UNWIND_THM2; SETDIST_CLOSURE;
                  CLOSURE_EQ_EMPTY; RIGHT_EXISTS_AND_THM; IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `y':real^N` (STRIP_ASSUME_TAC o GSYM)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^N` (STRIP_ASSUME_TAC o GSYM)) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `dist(u % x + v % y:real^N,u % x' + v % y')` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SETDIST_LE_DIST THEN REWRITE_TAC[IN_SING] THEN
    ASM_MESON_TAC[convex];
    REWRITE_TAC[dist] THEN MATCH_MP_TAC(NORM_ARITH
     `norm(a - a':real^N) + norm(b - b') <= r
      ==> norm((a + b) - (a' + b')) <= r`) THEN
    ASM_REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; NORM_MUL; dist] THEN
    ASM_REWRITE_TAC[real_abs; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Moving and scaling convex hulls.                                          *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_TRANSLATION = prove
 (`!a:real^N s.
       convex hull (IMAGE (\x. a + x) s) = IMAGE (\x. a + x) (convex hull s)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HULL_IMAGE THEN
  REWRITE_TAC[CONVEX_TRANSLATION_EQ; CONVEX_CONVEX_HULL] THEN
  REWRITE_TAC[VECTOR_ARITH `a + x:real^N = y <=> x = y - a`; EXISTS_REFL] THEN
  VECTOR_ARITH_TAC);;

add_translation_invariants [CONVEX_HULL_TRANSLATION];;

let CONVEX_HULL_SCALING = prove
 (`!s:real^N->bool c.
       convex hull (IMAGE (\x. c % x) s) = IMAGE (\x. c % x) (convex hull s)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c = &0` THENL
   [ASM_SIMP_TAC[IMAGE_CONST; VECTOR_MUL_LZERO; CONVEX_HULL_EQ_EMPTY] THEN
    COND_CASES_TAC THEN REWRITE_TAC[CONVEX_HULL_EMPTY; CONVEX_HULL_SING];
    ALL_TAC] THEN
  MATCH_MP_TAC HULL_IMAGE THEN
  ASM_SIMP_TAC[CONVEX_SCALING_EQ; CONVEX_CONVEX_HULL] THEN
  REWRITE_TAC[VECTOR_ARITH `c % x = c % y <=> c % (x - y) = vec 0`] THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
  X_GEN_TAC `x:real^N` THEN EXISTS_TAC `inv c % x:real^N` THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID]);;

let CONVEX_HULL_AFFINITY = prove
 (`!s a:real^N c.
        convex hull (IMAGE (\x. a + c % x) s) =
        IMAGE (\x. a + c % x) (convex hull s)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\x:real^N. a + c % x) = (\x. a + x) o (\x. c % x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  ASM_SIMP_TAC[IMAGE_o; CONVEX_HULL_TRANSLATION; CONVEX_HULL_SCALING]);;

(* ------------------------------------------------------------------------- *)
(* Convex set as intersection of halfspaces.                                 *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HALFSPACE_INTERSECTION = prove
 (`!s. closed(s:real^N->bool) /\ convex s
       ==> s = INTERS {h | s SUBSET h /\ ?a b. h = {x | a dot x <= b}}`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INTERS] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[MESON[] `(!t. (P t /\ ?a b. t = x a b) ==> Q t) <=>
                       (!a b. P(x a b) ==> Q(x a b))`] THEN
  EQ_TAC THENL [SET_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`]
    SEPARATING_HYPERPLANE_CLOSED_POINT) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`--a:real^N`; `--b:real`]) THEN
  ASM_SIMP_TAC[SUBSET; IN_ELIM_THM; DOT_LNEG; NOT_IMP] THEN
  ASM_SIMP_TAC[REAL_LE_NEG2; REAL_LT_NEG2; REAL_NOT_LE;
               REAL_ARITH `a > b ==> b <= a`]);;

(* ------------------------------------------------------------------------- *)
(* Radon's theorem (from Lars Schewe).                                       *)
(* ------------------------------------------------------------------------- *)

let RADON_EX_LEMMA = prove
 (`!(c:real^N->bool).
        FINITE c /\ affine_dependent c
        ==> (?u. sum c u = &0 /\ (?v. v IN c /\ ~(u v = &0)) /\
                                      vsum c (\v. u v % v) = (vec 0):real^N)`,
  REWRITE_TAC[AFFINE_DEPENDENT_EXPLICIT] THEN
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\v:real^N. if v IN s then u v else &0` THEN
  ASM_SIMP_TAC[GSYM SUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[COND_RAND;COND_RATOR;
               VECTOR_MUL_LZERO;GSYM VSUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[SET_RULE `s SUBSET c ==> {x | x IN c /\ x IN s} = s`] THEN
  EXISTS_TAC `v:real^N` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let RADON_S_LEMMA = prove
 (`!(s:A->bool) f.
        FINITE s /\ sum s f = &0
        ==> sum {x | x IN s /\ &0 < f x} f =
            -- sum {x | x IN s /\ f x < &0} f`,
  REWRITE_TAC[REAL_ARITH `a = --b <=> a + b = &0`] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FINITE_RESTRICT;GSYM SUM_UNION;
    REWRITE_RULE [REAL_ARITH `&0 < f x ==> ~(f x < &0)`]
     (SET_RULE `(!x:A. &0 < f x ==> ~(f x < &0))
                ==>  DISJOINT {x | x IN s /\ &0 < f x}
                              {x | x IN s /\ f x < &0}`)] THEN
  MATCH_MP_TAC (REAL_ARITH `!a b.a = &0 /\ a + b = &0 ==> b = &0`) THEN
  EXISTS_TAC `sum {x:A | x IN s /\ f x = &0} f` THEN
  CONJ_TAC THENL
  [ASM_SIMP_TAC[SUM_RESTRICT_SET] THEN REWRITE_TAC[COND_ID;SUM_0];
   ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT {x:A | x IN s /\ f x = &0}
                         ({x | x IN s /\ &0 < f x} UNION
                          {x | x IN s /\ f x < &0})` ASSUME_TAC THENL
  [REWRITE_TAC[DISJOINT;UNION;INTER;IN_ELIM_THM;EXTENSION;NOT_IN_EMPTY] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
   ASM_SIMP_TAC[FINITE_UNION;FINITE_RESTRICT;GSYM SUM_UNION] THEN
  FIRST_X_ASSUM (SUBST1_TAC o GSYM) THEN
  MATCH_MP_TAC (MESON[] `a = b ==> sum a f = sum b f`) THEN
  REWRITE_TAC[EXTENSION;IN_ELIM_THM;UNION] THEN
  MESON_TAC[REAL_LT_TOTAL]);;

let RADON_V_LEMMA = prove
 (`!(s:A->bool) f g.
        FINITE s /\ vsum s f = vec 0 /\ (!x. g x = &0 ==> f x = vec 0)
        ==> (vsum {x | x IN s /\ &0 < g x} f) :real^N =
             -- vsum {x | x IN s /\ g x < &0} f`,
  REWRITE_TAC[VECTOR_ARITH `a:real^N = --b <=> a + b = vec 0`] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FINITE_RESTRICT;GSYM VSUM_UNION;
               REWRITE_RULE [REAL_ARITH `&0 < f x ==> ~(f x < &0)`]
                 (SET_RULE `(!x:A. &0 < f x ==> ~(f x < &0))
                            ==>  DISJOINT {x | x IN s /\ &0 < f x}
                                          {x | x IN s /\ f x < &0}`)] THEN
  MATCH_MP_TAC (VECTOR_ARITH
    `!a b. (a:real^N) = vec 0 /\ a + b = vec 0 ==> b = vec 0`) THEN
  EXISTS_TAC `(vsum {x:A | x IN s /\ g x = &0} f):real^N` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[VSUM_RESTRICT_SET;COND_ID;VSUM_0];ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT {x:A | x IN s /\ g x = &0}
                           ({x | x IN s /\ &0 < g x} UNION
                            {x | x IN s /\ g x < &0})` ASSUME_TAC THENL
     [REWRITE_TAC[DISJOINT;UNION;INTER;IN_ELIM_THM;EXTENSION;NOT_IN_EMPTY] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_UNION;FINITE_RESTRICT;GSYM VSUM_UNION] THEN
  FIRST_X_ASSUM (SUBST1_TAC o GSYM) THEN
  MATCH_MP_TAC (MESON[] `a = b ==> vsum a f = vsum b f`) THEN
  REWRITE_TAC[EXTENSION;IN_ELIM_THM;UNION] THEN
  MESON_TAC[REAL_LT_TOTAL]);;

let RADON_PARTITION = prove
 (`!(c:real^N->bool).
        FINITE c /\ affine_dependent c
        ==> ?(m:real^N->bool) (p:real^N->bool).
                (DISJOINT m p) /\
                (m UNION p = c) /\
                ~(DISJOINT (convex hull m) (convex hull p))`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPEC `c:real^N->bool` RADON_EX_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`{v:real^N | v IN c /\ u v <= &0}`;
                        `{v:real^N | v IN c /\ u v > &0}`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DISJOINT;INTER;
               IN_ELIM_THM;REAL_ARITH `x <= &0 <=> ~(x > &0)`] THEN
    SET_TAC[];
    REWRITE_TAC[UNION;IN_ELIM_THM;REAL_ARITH `x <= &0 <=> ~(x > &0)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(sum {x:real^N | x IN c /\ u x > &0} u = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC (REAL_ARITH `a > &0 ==> ~(a = &0)`) THEN
    REWRITE_TAC[REAL_ARITH `a > &0 <=> &0 < a`]        THEN
    MATCH_MP_TAC (REWRITE_RULE[SUM_0] (ISPEC `\x. &0` SUM_LT_ALL)) THEN
    ASM_SIMP_TAC[FINITE_RESTRICT;IN_ELIM_THM;EXTENSION;NOT_IN_EMPTY] THEN
    REWRITE_TAC[MESON[]`~(!x. ~(P x /\ Q x)) = ?x. P x /\ Q x`] THEN
       ASM_CASES_TAC `&0 < u (v:real^N)` THENL
    [ASM SET_TAC[];ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[IMP_IMP;REAL_ARITH `~(a = &0) /\ ~(&0 < a) <=> a < &0`] THEN
    DISCH_TAC THEN
    REWRITE_TAC[MESON[REAL_NOT_LT]
     `(?x:real^N. P x /\ &0 < u x) <=> (!x. P x ==> u x <= &0) ==> F`]  THEN
    DISCH_TAC THEN
       MP_TAC (ISPECL [`u:real^N->real`;`\x:real^N. &0`;`c:real^N->bool`]
                      SUM_LT) THEN
    ASM_REWRITE_TAC[SUM_0;REAL_ARITH `~(&0 < &0)`] THEN
    ASM_MESON_TAC[];ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `~DISJOINT a b <=> ?y. y IN a /\ y IN b`] THEN
  EXISTS_TAC `&1 / (sum {x:real^N | x IN c /\ u x > &0} u) %
              vsum {x:real^N | x IN c /\ u x > &0} (\x. u x % x)` THEN
  REWRITE_TAC[CONVEX_HULL_EXPLICIT;IN_ELIM_THM] THEN
  CONJ_TAC THENL
  [MAP_EVERY EXISTS_TAC [`{v:real^N | v IN c /\ u v < &0}`;
                         `\y:real^N.
                         &1 / (sum {x:real^N | x IN c /\ u x > &0} u) *
                           (--(u y))`] THEN
   ASM_SIMP_TAC[FINITE_RESTRICT;SUBSET;IN_ELIM_THM] THEN
   REPEAT CONJ_TAC THENL
    [REAL_ARITH_TAC;
     REPEAT STRIP_TAC THEN
     MATCH_MP_TAC REAL_LE_MUL THEN
     CONJ_TAC THENL [ALL_TAC;
                     ASM_REWRITE_TAC[REAL_NEG_GE0;REAL_LE_LT]] THEN
     MATCH_MP_TAC REAL_LE_DIV THEN
     REWRITE_TAC[REAL_LE_01] THEN
     MATCH_MP_TAC SUM_POS_LE THEN
     ASM_SIMP_TAC[FINITE_RESTRICT;IN_ELIM_THM] THEN
     REAL_ARITH_TAC;
     ASM_SIMP_TAC[FINITE_RESTRICT;SUM_LMUL] THEN
     MATCH_MP_TAC (REAL_FIELD `!a. ~(a = &0) /\ a * b = a * c ==> b = c`) THEN
     EXISTS_TAC `sum {x:real^N | x IN c /\ u x > &0} u` THEN
     REWRITE_TAC[SUM_LMUL] THEN
     ASM_SIMP_TAC[REAL_FIELD `~(a = &0) ==> a * &1 / a * b = b`]  THEN
     REWRITE_TAC[SUM_NEG;REAL_MUL_RID] THEN
     REWRITE_TAC[REAL_ARITH `a > &0 <=> &0 < a`] THEN
     MATCH_MP_TAC (GSYM RADON_S_LEMMA) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    REWRITE_TAC[GSYM VECTOR_MUL_ASSOC;VSUM_LMUL;VECTOR_MUL_LCANCEL] THEN
    REWRITE_TAC[VECTOR_MUL_LNEG;VSUM_NEG] THEN
    DISJ2_TAC THEN
    MATCH_MP_TAC (REWRITE_RULE[REAL_ARITH `&0 < a <=>  a > &0`]
     (GSYM RADON_V_LEMMA)) THEN
    ASM_REWRITE_TAC[] THEN
    MESON_TAC[VECTOR_MUL_LZERO];ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`{v:real^N | v IN c /\ u v > &0}`;
                        `\y:real^N.
                           &1 / (sum {x:real^N | x IN c /\ u x > &0} u) *
                           (u y)`] THEN
  ASM_SIMP_TAC[FINITE_RESTRICT;SUBSET;IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [ALL_TAC;
                    ASM_SIMP_TAC[REAL_ARITH `a > &0 ==> &0 <= a`]] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_LE_01] THEN
    MATCH_MP_TAC SUM_POS_LE THEN
    ASM_SIMP_TAC[FINITE_RESTRICT;IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[FINITE_RESTRICT;SUM_LMUL] THEN
    MATCH_MP_TAC (REAL_FIELD `!a. ~(a = &0) /\ a * b = a * c ==> b = c`) THEN
    EXISTS_TAC `sum {x:real^N | x IN c /\ u x > &0} u` THEN
    REWRITE_TAC[SUM_LMUL] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(a = &0) ==> a * &1 / a * b = b`]  THEN
    REWRITE_TAC[SUM_NEG;REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ARITH `a > &0 <=> &0 < a`] THEN
    MATCH_MP_TAC (GSYM RADON_S_LEMMA) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM VECTOR_MUL_ASSOC;VSUM_LMUL;VECTOR_MUL_LCANCEL] THEN
  REWRITE_TAC[VECTOR_MUL_LNEG;VSUM_NEG] THEN
  DISJ2_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[REAL_ARITH `&0 < a <=>  a > &0`]
    (GSYM RADON_V_LEMMA)) THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[VECTOR_MUL_LZERO]);;

let RADON = prove
 (`!(c:real^N->bool).
        affine_dependent c
        ==> ?(m:real^N->bool) (p:real^N->bool).
                m SUBSET c /\
                p SUBSET c /\
                DISJOINT m p /\
                ~(DISJOINT (convex hull m) (convex hull p))`,
  REPEAT STRIP_TAC THEN MP_TAC
    (ISPEC `c:real^N->bool` AFFINE_DEPENDENT_EXPLICIT) THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN MP_TAC
  (ISPEC `s:real^N->bool` RADON_PARTITION) THEN
  ANTS_TAC THENL
  [ASM_SIMP_TAC[AFFINE_DEPENDENT_EXPLICIT] THEN
     MAP_EVERY EXISTS_TAC [`s:real^N->bool`;`u:real^N->real`] THEN
     ASM SET_TAC[];ALL_TAC] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  MAP_EVERY EXISTS_TAC [`m:real^N->bool`;`p:real^N->bool`] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Helly's theorem.                                                          *)
(* ------------------------------------------------------------------------- *)

let HELLY_INDUCT = prove
 (`!n f. f HAS_SIZE n /\ n >= dimindex(:N) + 1 /\
         (!s:real^N->bool. s IN f ==> convex s) /\
         (!t. t SUBSET f /\ CARD(t) = dimindex(:N) + 1
              ==> ~(INTERS t = {}))
         ==> ~(INTERS f = {})`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH_RULE `~(0 >= n + 1)`] THEN GEN_TAC THEN
  POP_ASSUM(LABEL_TAC "*") THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_SIZE_SUC]) THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
    `SUC n >= m + 1 ==> m = n \/ n >= m + 1`))
  THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
    ASM_SIMP_TAC[CARD_CLAUSES; SUBSET_REFL] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?X. !s:real^N->bool. s IN f ==> X(s) IN INTERS (f DELETE s)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; MEMBER_NOT_EMPTY; RIGHT_EXISTS_IMP_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN REMOVE_THEN "*" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `?s t:real^N->bool. s IN f /\ t IN f /\ ~(s = t) /\ X s:real^N = X t`
  THENL
   [FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `(X:(real^N->bool)->real^N) t` THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC ONCE_DEPTH_CONV
     [MATCH_MP
       (SET_RULE`~(s = t)
               ==> INTERS f = INTERS(f DELETE s) INTER INTERS(f DELETE t)`)
       th]) THEN
    REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (X:(real^N->bool)->real^N) f` RADON_PARTITION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE] THEN
    MATCH_MP_TAC AFFINE_DEPENDENT_BIGGERSET THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN
    MATCH_MP_TAC(ARITH_RULE
     `!f n. n >= d + 1 /\ f = SUC n /\ c = f ==> c >= d + 2`) THEN
    MAP_EVERY EXISTS_TAC [`CARD(f:(real^N->bool)->bool)`; `n:num`] THEN
    REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `P /\ m UNION p = s /\ Q <=>
    m SUBSET s /\ p SUBSET s /\ m UNION p = s /\ P /\ Q`] THEN
  REWRITE_TAC[SUBSET_IMAGE; DISJOINT] THEN
  REWRITE_TAC[MESON[]
   `(?m p. (?u. P u /\ m = t u) /\ (?u. P u /\ p = t u) /\ Q m p) ==> r <=>
    (!u v. P u /\ P v /\ Q (t u) (t v) ==> r)`] THEN
  MAP_EVERY X_GEN_TAC [`g:(real^N->bool)->bool`; `h:(real^N->bool)->bool`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `(f:(real^N->bool)->bool) = h UNION g` SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[UNION_SUBSET] THEN
    REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `s:real^N->bool` THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(MP_TAC o ISPEC `X:(real^N->bool)->real^N` o
      MATCH_MP FUN_IN_IMAGE) THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
    ONCE_REWRITE_TAC[DISJ_SYM] THEN REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
    MATCH_MP_TAC MONO_OR THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `g SUBSET INTERS g' /\ h SUBSET INTERS h'
    ==> ~(g INTER h = {}) ==> ~(INTERS(g' UNION h') = {})`) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SET_RULE
   `IMAGE X s INTER IMAGE X t = {} ==> s INTER t = {}`)) THEN
  CONJ_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  (CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET; CONVEX_INTERS]]) THEN
  REWRITE_TAC[SUBSET; IN_INTERS; FORALL_IN_IMAGE] THEN ASM SET_TAC[]);;

let HELLY = prove
 (`!f:(real^N->bool)->bool.
        FINITE f /\ CARD(f) >= dimindex(:N) + 1 /\
        (!s. s IN f ==> convex s) /\
        (!t. t SUBSET f /\ CARD(t) = dimindex(:N) + 1 ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HELLY_INDUCT THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN ASM_MESON_TAC[]);;

let HELLY_ALT = prove
 (`!f:(real^N->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> convex s) /\
        (!t. t SUBSET f /\ CARD(t) <= dimindex(:N) + 1 ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `CARD(f:(real^N->bool)->bool) < dimindex(:N) + 1` THEN
  ASM_SIMP_TAC[SUBSET_REFL; LT_IMP_LE] THEN MATCH_MP_TAC HELLY THEN
  ASM_SIMP_TAC[GE; GSYM NOT_LT] THEN ASM_MESON_TAC[LE_REFL]);;

let HELLY_CLOSED_ALT = prove
 (`!f:(real^N->bool)->bool.
        (!s. s IN f ==> convex s /\ closed s) /\ (?s. s IN f /\ bounded s) /\
        (!t. t SUBSET f /\ FINITE t /\ CARD(t) <= dimindex(:N) + 1
             ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`,
  GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC CLOSED_FIP THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `g:(real^N->bool)->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC HELLY_ALT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM_MESON_TAC[SUBSET_TRANS; FINITE_SUBSET]]);;

let HELLY_COMPACT_ALT = prove
 (`!f:(real^N->bool)->bool.
        (!s. s IN f ==> convex s /\ compact s) /\
        (!t. t SUBSET f /\ FINITE t /\ CARD(t) <= dimindex(:N) + 1
             ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[INTERS_0; UNIV_NOT_EMPTY] THEN
  MATCH_MP_TAC HELLY_CLOSED_ALT THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY; COMPACT_IMP_BOUNDED]);;

let HELLY_CLOSED = prove
 (`!f:(real^N->bool)->bool.
        (FINITE f ==> CARD f >= dimindex (:N) + 1) /\
        (!s. s IN f ==> convex s /\ closed s) /\ (?s. s IN f /\ bounded s) /\
        (!t. t SUBSET f /\ FINITE t /\ CARD(t) = dimindex(:N) + 1
             ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`,
  GEN_TAC THEN REWRITE_TAC[GE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC HELLY_CLOSED_ALT THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `g:(real^N->bool)->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`dimindex(:N) + 1`; `g:(real^N->bool)->bool`;
                 `f:(real^N->bool)->bool`] CHOOSE_SUBSET_BETWEEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ ~(s = {}) ==> ~(t = {})`) THEN
  EXISTS_TAC `INTERS h: real^N->bool` THEN
  CONJ_TAC THENL [ASM SET_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC] THEN
  ASM_MESON_TAC[HAS_SIZE]);;

let HELLY_COMPACT = prove
 (`!f:(real^N->bool)->bool.
        (FINITE f ==> CARD f >= dimindex (:N) + 1) /\
        (!s. s IN f ==> convex s /\ compact s) /\
        (!t. t SUBSET f /\ FINITE t /\ CARD(t) = dimindex(:N) + 1
             ==> ~(INTERS t = {}))
        ==> ~(INTERS f = {})`,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[INTERS_0; UNIV_NOT_EMPTY] THEN
  MATCH_MP_TAC HELLY_CLOSED THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY; COMPACT_IMP_BOUNDED]);;

(* ------------------------------------------------------------------------- *)
(* Kirchberger's theorem                                                     *)
(* ------------------------------------------------------------------------- *)

let KIRCHBERGER = prove
 (`!s t:real^N->bool.
        compact s /\ compact t /\
        (!s' t'. s' SUBSET s /\ t' SUBSET t /\ FINITE s' /\ FINITE t' /\
                 CARD(s') + CARD(t') <= dimindex(:N) + 2
                 ==> ?a b. (!x. x IN s' ==> a dot x < b) /\
                           (!x. x IN t' ==> a dot x > b))
        ==> ?a b. ~(a = vec 0) /\
                  (!x. x IN s ==> a dot x < b) /\
                  (!x. x IN t ==> a dot x > b)`,
  let lemma = prove
   (`(!x. x IN convex hull s ==> a dot x < b) /\
     (!x. x IN convex hull t ==> a dot x > b) <=>
     (!x. x IN s ==> a dot x < b) /\ (!x. x IN t ==> a dot x > b)`,
    REWRITE_TAC[SET_RULE `(!x. x IN s ==> P x) <=> s SUBSET {x | P x}`] THEN
    SIMP_TAC[SUBSET_HULL; CONVEX_HALFSPACE_LT; CONVEX_HALFSPACE_GT])
  and KIRCH_LEMMA = prove
   (`!s t:real^N->bool.
          FINITE s /\ FINITE t /\
          (!s' t'. s' SUBSET s /\ t' SUBSET t /\
                   CARD(s') + CARD(t') <= dimindex(:N) + 2
                   ==> ?a b. (!x. x IN s' ==> a dot x < b) /\
                             (!x. x IN t' ==> a dot x > b))
          ==> ?a b. (!x. x IN s ==> a dot x < b) /\
                    (!x. x IN t ==> a dot x > b)`,
    REPEAT STRIP_TAC THEN MP_TAC(ISPECL
     [`IMAGE (\r. {z:real^(N,1)finite_sum |
                          fstcart z dot r < drop(sndcart z)}) s UNION
       IMAGE (\r. {z:real^(N,1)finite_sum |
                          fstcart z dot r > drop(sndcart z)}) t`]
     HELLY_ALT) THEN
    REWRITE_TAC[FORALL_SUBSET_UNION; IN_UNION; IMP_CONJ] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_SUBSET_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; INTERS_UNION] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; INTERS_IMAGE; IN_INTER;
                EXISTS_PASTECART; IN_ELIM_PASTECART_THM;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
    REWRITE_TAC[FORALL_AND_THM; FORALL_IN_IMAGE; RIGHT_IMP_FORALL_THM] THEN
    REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; GSYM EXISTS_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `a > b <=> --a < --b`; GSYM DOT_RNEG] THEN
      REWRITE_TAC[convex; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
      SIMP_TAC[PASTECART_ADD; GSYM PASTECART_CMUL; IN_ELIM_PASTECART_THM] THEN
      SIMP_TAC[DOT_LADD; DOT_LMUL; DROP_ADD; DROP_CMUL; GSYM FORALL_DROP] THEN
      REWRITE_TAC[REAL_ARITH `--(a * x + b * y):real = a * --x + b * --y`] THEN
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
       `u + v = &1
        ==> &0 <= u /\ &0 <= v
           ==> u = &0 /\ v = &1 \/ u = &1 /\ v = &0 \/ &0 < u /\ &0 < v`)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID;
                      REAL_ADD_LID; REAL_ADD_RID] THEN
      MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_SIMP_TAC[REAL_LT_LMUL_EQ];
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1;
                  ARITH_RULE `(n + 1) + 1 = n + 2`] THEN
      MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      SUBGOAL_THEN `FINITE(u:real^N->bool) /\ FINITE(v:real^N->bool)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) CARD_UNION o lhand o lhand o snd) THEN
      ASM_SIMP_TAC[FINITE_IMAGE] THEN ANTS_TAC THENL
       [REWRITE_TAC[SET_RULE `IMAGE f s INTER IMAGE g t = {} <=>
                              !x y. x IN s /\ y IN t ==> ~(f x = g y)`] THEN
        MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
        REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_ELIM_PASTECART_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `vec 0:real^N`) THEN
        REWRITE_TAC[GSYM FORALL_DROP; DOT_LZERO] THEN
        DISCH_THEN(MP_TAC o SPEC `&1`) THEN REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(ARITH_RULE
       `a = a' /\ b = b' ==> a + b <= n + 2 ==> a' + b' <= n + 2`) THEN
      CONJ_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
      ASM_REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_ELIM_PASTECART_THM] THEN
      SIMP_TAC[GSYM FORALL_DROP; real_gt; VECTOR_EQ_LDOT;
        MESON[REAL_LT_TOTAL; REAL_LT_REFL]
         `((!y:real. a < y <=> b < y) <=> a = b) /\
          ((!y:real. y < a <=> y < b) <=> a = b)`]]) in
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM lemma] THEN
  MATCH_MP_TAC SEPARATING_HYPERPLANE_COMPACT_COMPACT THEN
  ASM_SIMP_TAC[CONVEX_CONVEX_HULL; COMPACT_CONVEX_HULL;
               CONVEX_HULL_EQ_EMPTY] THEN
  SUBGOAL_THEN
   `!s' t'. (s':real^N->bool) SUBSET s /\ t' SUBSET t /\
            FINITE s' /\ CARD(s') <= dimindex(:N) + 1 /\
            FINITE t' /\ CARD(t') <= dimindex(:N) + 1
            ==> DISJOINT (convex hull s') (convex hull t')`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s':real^N->bool`; `t':real^N->bool`] KIRCH_LEMMA) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET; FINITE_SUBSET];
      ONCE_REWRITE_TAC[GSYM lemma] THEN SET_TAC[REAL_LT_ANTISYM; real_gt]];
    POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC THEN
    REWRITE_TAC[SET_RULE `DISJOINT s t <=> !x. x IN s /\ x IN t ==> F`] THEN
    X_GEN_TAC `x:real^N` THEN ONCE_REWRITE_TAC[CARATHEODORY] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s':real^N->bool`; `t':real^N->bool`]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Convex hull is "preserved" by a linear function.                          *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_LINEAR_IMAGE = prove
 (`!f s. linear f ==> convex hull (IMAGE f s) = IMAGE f (convex hull s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  CONJ_TAC THEN MATCH_MP_TAC HULL_INDUCT THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN SIMP_TAC[FUN_IN_IMAGE; HULL_INC] THEN
  REWRITE_TAC[convex; IN_ELIM_THM] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_CMUL th)]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_ADD th)]) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    MESON_TAC[REWRITE_RULE[convex] CONVEX_CONVEX_HULL];
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
    MESON_TAC[REWRITE_RULE[convex] CONVEX_CONVEX_HULL]]);;

add_linear_invariants [CONVEX_HULL_LINEAR_IMAGE];;

let IN_CONVEX_HULL_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s x.
        linear f /\ x IN convex hull s ==> (f x) IN convex hull (IMAGE f s)`,
  SIMP_TAC[CONVEX_HULL_LINEAR_IMAGE] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Convexity of general and special intervals.                               *)
(* ------------------------------------------------------------------------- *)

let IS_INTERVAL_CONVEX = prove
 (`!s:real^N->bool. is_interval s ==> convex s`,
  REWRITE_TAC[is_interval; convex] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`x:real^N`; `y:real^N`] THEN
  ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(SPECL [`(x:real^N)$i`; `(y:real^N)$i`] REAL_LE_TOTAL) THENL
   [DISJ1_TAC; DISJ2_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&1 * a <= b /\ b <= &1 * c ==> a <= b /\ b <= c`) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[GSYM VECTOR_MUL_COMPONENT;
               VECTOR_ADD_RDISTRIB; VECTOR_ADD_COMPONENT] THEN
  ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_LE_LMUL;
               REAL_LE_LADD; REAL_LE_RADD]);;

let IS_INTERVAL_CONNECTED = prove
 (`!s:real^N->bool. is_interval s ==> connected s`,
  MESON_TAC[IS_INTERVAL_CONVEX; CONVEX_CONNECTED]);;

let IS_INTERVAL_CONNECTED_1 = prove
 (`!s:real^1->bool. is_interval s <=> connected s`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[IS_INTERVAL_CONNECTED] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[IS_INTERVAL_1; connected; NOT_FORALL_THM; LEFT_IMP_EXISTS_THM;
              NOT_IMP; FORALL_LIFT; LIFT_DROP] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `x:real`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`{z:real^1 | basis 1 dot z < x}`; `{z:real^1 | basis 1 dot z > x}`] THEN
  REWRITE_TAC[OPEN_HALFSPACE_LT; OPEN_HALFSPACE_GT] THEN
  SIMP_TAC[SUBSET; EXTENSION; IN_UNION; IN_INTER; GSYM drop; NOT_FORALL_THM;
   real_gt; NOT_IN_EMPTY; IN_ELIM_THM; DOT_BASIS; DIMINDEX_1; ARITH] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LT_TOTAL; LIFT_DROP];
    REAL_ARITH_TAC;
    EXISTS_TAC `lift a`;
    EXISTS_TAC `lift b`] THEN
  ASM_REWRITE_TAC[REAL_LT_LE; LIFT_DROP] THEN ASM_MESON_TAC[]);;

let CONVEX_INTERVAL = prove
 (`!a b:real^N. convex(interval [a,b]) /\ convex(interval (a,b))`,
  SIMP_TAC[IS_INTERVAL_CONVEX; IS_INTERVAL_INTERVAL]);;

let CONNECTED_INTERVAL = prove
 (`(!a b:real^N. connected(interval[a,b])) /\
   (!a b:real^N. connected(interval(a,b)))`,
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERVAL]);;

let CONVEX_CONNECTED_COLLINEAR = prove
 (`!s:real^N->bool. collinear s ==> (convex s <=> connected s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[CONVEX_CONNECTED] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COLLINEAR_AFFINE_HULL]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
  GEOM_ORIGIN_TAC `u:real^N` THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; IN_INSERT; SPAN_INSERT_0] THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `v:real^N` THEN
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[SPAN_SPECIAL_SCALE] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[SPAN_EMPTY; SET_RULE `s SUBSET {a} <=> s = {} \/ s = {a}`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[CONVEX_EMPTY; CONVEX_SING];
    DISCH_TAC THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT; connected; NOT_EXISTS_THM] THEN
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `a:real^N = b` THEN
    ASM_REWRITE_TAC[SEGMENT_REFL; SING_SUBSET] THEN
    REWRITE_TAC[SUBSET; IN_SEGMENT; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `u:real`] THEN
    MAP_EVERY ASM_CASES_TAC [`u = &0`; `u = &1`] THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; REAL_SUB_REFL;
                    REAL_SUB_RZERO; VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
    ASM_REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`{y:real^N | basis 1 dot y < basis 1 dot (x:real^N)}`;
      `{y:real^N | basis 1 dot y > basis 1 dot (x:real^N)}`]) THEN
    REWRITE_TAC[OPEN_HALFSPACE_LT; OPEN_HALFSPACE_GT] THEN
    MATCH_MP_TAC(TAUT `q /\ r /\ (~p ==> s) ==> ~(p /\ q /\ r) ==> s`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      REWRITE_TAC[CONJ_ASSOC; REAL_ARITH `~(x:real < a /\ x > a)`];
      ALL_TAC] THEN
    REWRITE_TAC[real_gt] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
    REWRITE_TAC[GSYM DOT_RSUB; SET_RULE
     `~(s SUBSET {x | P x} UNION {x | Q x}) <=>
      ?x. x IN s /\ ~(P x \/ Q x)`] THEN
    SUBGOAL_THEN
     `!p q:real^N. p IN span {basis 1} /\ q IN span {basis 1} /\
                   basis 1 dot p = basis 1 dot q
                   ==> p = q`
    ASSUME_TAC THENL
     [SIMP_TAC[SPAN_SING; IMP_CONJ; LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN
      SIMP_TAC[DOT_RMUL; BASIS_NONZERO; DOT_BASIS_BASIS; DIMINDEX_GE_1;
               LE_REFL; REAL_MUL_RID];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN span {basis 1}` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SPAN_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC SPAN_MUL THEN ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
       `(a:real^N) IN s \/ b IN s ==> ~(s = {})`) THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; DOT_RADD; DOT_RMUL;
        VECTOR_ARITH `((&1 - u) % a + u % b) - b:real^N = (u - &1) % (b - a)`;
        VECTOR_ARITH `((&1 - u) % a + u % b) - a:real^N = u % (b - a)`;
        VECTOR_ARITH `b - ((&1 - u) % a + u % b):real^N = (u - &1) % (a - b)`;
        VECTOR_ARITH `a - ((&1 - u) % a + u % b):real^N = u % (a - b)`] THEN
      MATCH_MP_TAC(REAL_ARITH
       `(&0 < x ==> &0 < u * x) /\ (&0 < --x ==> &0 < (&1 - u) * --x) /\
        ~(x = &0)
        ==>  &0 < u * x \/ &0 < (u - &1) * x`) THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_SUB_LT] THEN
      REWRITE_TAC[DOT_RSUB; REAL_SUB_0];
      REWRITE_TAC[DOT_RSUB; REAL_ARITH
       `~(&0 < x - y \/ &0 < y - x) <=> y = x`]] THEN
    ASM SET_TAC[]]);;

let CONVEX_EQ_CONVEX_LINE_INTERSECTION = prove
 (`!s:real^N->bool. convex s <=> !a b. convex(s INTER affine hull {a,b})`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[CONVEX_INTER; AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL] THEN
  REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`a:real^N`; `b:real^N`; `a:real^N`; `b:real^N`]) THEN
  ASM_SIMP_TAC[IN_INTER; HULL_INC; IN_INSERT] THEN SET_TAC[]);;

let CONVEX_EQ_CONNECTED_LINE_INTERSECTION = prove
 (`!s:real^N->bool. convex s <=> !a b. connected(s INTER affine hull {a,b})`,
  GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [CONVEX_EQ_CONVEX_LINE_INTERSECTION] THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  MATCH_MP_TAC CONVEX_CONNECTED_COLLINEAR THEN
  MATCH_MP_TAC COLLINEAR_SUBSET THEN
  EXISTS_TAC `affine hull {a:real^N,b}` THEN
  REWRITE_TAC[COLLINEAR_AFFINE_HULL_COLLINEAR; COLLINEAR_2] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* On real^1, is_interval, convex and connected are all equivalent.          *)
(* ------------------------------------------------------------------------- *)

let IS_INTERVAL_CONVEX_1 = prove
 (`!s:real^1->bool. is_interval s <=> convex s`,
  MESON_TAC[IS_INTERVAL_CONVEX; CONVEX_CONNECTED; IS_INTERVAL_CONNECTED_1]);;

let CONVEX_CONNECTED_1 = prove
 (`!s:real^1->bool. convex s <=> connected s`,
  REWRITE_TAC[GSYM IS_INTERVAL_CONVEX_1; GSYM IS_INTERVAL_CONNECTED_1]);;

let CONNECTED_CONVEX_1 = prove
 (`!s:real^1->bool. connected s <=> convex s`,
  REWRITE_TAC[GSYM IS_INTERVAL_CONVEX_1; GSYM IS_INTERVAL_CONNECTED_1]);;

let CONNECTED_COMPACT_INTERVAL_1 = prove
 (`!s:real^1->bool. connected s /\ compact s <=> ?a b. s = interval[a,b]`,
  REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1; IS_INTERVAL_COMPACT]);;

let CONVEX_CONNECTED_1_GEN = prove
 (`!s:real^N->bool.
        dimindex(:N) = 1 ==> (convex s <=> connected s)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[GSYM DIMINDEX_1] THEN
  DISCH_THEN(ACCEPT_TAC o C GEOM_EQUAL_DIMENSION_RULE CONVEX_CONNECTED_1));;

let CONNECTED_CONVEX_1_GEN = prove
 (`!s:real^N->bool.
        dimindex(:N) = 1 ==> (convex s <=> connected s)`,
  SIMP_TAC[CONVEX_CONNECTED_1_GEN]);;

(* ------------------------------------------------------------------------- *)
(* Jung's theorem.                                                           *)
(* Proof taken from http://cstheory.wordpress.com/2010/08/07/jungs-theorem/  *)
(* ------------------------------------------------------------------------- *)

let JUNG = prove
 (`!s:real^N->bool r.
        bounded s /\
        sqrt(&(dimindex(:N)) / &(2 * dimindex(:N) + 2)) * diameter s <= r
        ==> ?a. s SUBSET cball(a,r)`,
  let lemma = prove
   (`&0 < x /\ x <= y ==> (x - &1) / x <= (y - &1) / y`,
    SIMP_TAC[REAL_LE_LDIV_EQ] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x / y * z:real = (x * z) / y`] THEN
    SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_RDIV_EQ]] THEN
    ASM_REAL_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= r` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        REAL_LE_TRANS)) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[DIAMETER_POS_LE] THEN
    SIMP_TAC[SQRT_POS_LE; REAL_LE_DIV; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\x:real^N. cball(x,r)) s` HELLY_COMPACT_ALT) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; COMPACT_CBALL; CONVEX_CBALL] THEN
  REWRITE_TAC[TAUT `p /\ q /\ r ==> s <=> q /\ p ==> r ==> s`] THEN
  REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[INTERS_IMAGE; GSYM MEMBER_NOT_EMPTY] THEN
  REWRITE_TAC[SUBSET; IN_CBALL; IN_ELIM_THM] THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[DIST_SYM]] THEN
  X_GEN_TAC `t:real^N->bool` THEN REWRITE_TAC[GSYM SUBSET] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_IMAGE_INJ; EQ_BALLS; GSYM REAL_NOT_LE] THEN
  UNDISCH_TAC `FINITE(t:real^N->bool)` THEN
  SUBGOAL_THEN `bounded(t:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[BOUNDED_SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= r` THEN
  SUBGOAL_THEN
   `sqrt(&(dimindex(:N)) / &(2 * dimindex(:N) + 2)) *
    diameter(t:real^N->bool) <= r`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        REAL_LE_TRANS)) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[DIAMETER_SUBSET; SQRT_POS_LE; REAL_POS; REAL_LE_DIV];
    POP_ASSUM_LIST(K ALL_TAC) THEN
    SPEC_TAC(`t:real^N->bool`,`s:real^N->bool`) THEN
    REPEAT STRIP_TAC] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  MP_TAC(ISPEC `{d | &0 <= d /\ ?a:real^N. s SUBSET cball(a,d)}` INF) THEN
  ABBREV_TAC `d = inf {d | &0 <= d /\ ?a:real^N. s SUBSET cball(a,d)}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    ASM_MESON_TAC[BOUNDED_SUBSET_CBALL; REAL_LT_IMP_LE];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "P") (LABEL_TAC "M"))] THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^N. s SUBSET cball(a,d)` MP_TAC THENL
   [SUBGOAL_THEN
     `!n. ?a:real^N. s SUBSET cball(a,d + inv(&n + &1))`
    MP_TAC THENL
     [X_GEN_TAC `n:num` THEN
      REMOVE_THEN "M" (MP_TAC o SPEC `d + inv(&n + &1)`) THEN
      REWRITE_TAC[REAL_ARITH `d + i <= d <=> ~(&0 < i)`] THEN
      REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
      MESON_TAC[SUBSET_CBALL; REAL_LT_IMP_LE; SUBSET_TRANS];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    X_GEN_TAC `aa:num->real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?t. compact t /\ !n. (aa:num->real^N) n IN t` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^N` o
        MATCH_MP BOUNDED_SUBSET_CBALL) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM; SUBSET; IN_CBALL_0] THEN
      X_GEN_TAC `B:real` THEN STRIP_TAC THEN
      EXISTS_TAC `cball(vec 0:real^N,B + d + &1)` THEN
      REWRITE_TAC[COMPACT_CBALL; IN_CBALL_0] THEN X_GEN_TAC `n:num` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_CBALL]) THEN
      MATCH_MP_TAC(NORM_ARITH
       `(?x:real^N. norm(x) <= B /\ dist(a,x) <= d) ==> norm(a) <= B + d`) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d + inv(&n + &1)` THEN
      ASM_SIMP_TAC[REAL_LE_LADD] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[compact; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `t:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `aa:num->real^N`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPEC `(dist(a:real^N,x) - d) / &2` REAL_ARCH_INV) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o SPEC `(dist(a:real^N,x) - d) / &2`) THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_HALF; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPECL [`(r:num->num)(N1 + N2)`; `x:real^N`]) THEN
    ASM_REWRITE_TAC[IN_CBALL; REAL_NOT_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num`) THEN
    ASM_REWRITE_TAC[LE_ADD] THEN
    SUBGOAL_THEN `inv(&(r (N1 + N2:num)) + &1) < (dist(a:real^N,x) - d) / &2`
    MP_TAC THENL [ALL_TAC; NORM_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC(ARITH_RULE
      `N1 + N2 <= r(N1 + N2) ==> N2 <= r(N1 + N2) + 1`) THEN
    ASM_MESON_TAC[MONOTONE_BIGGER];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN
  REWRITE_TAC[GSYM IN_CBALL; GSYM SUBSET] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
  MATCH_MP_TAC SUBSET_CBALL THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `a * s <= r ==> d <= a * s ==> d <= r`)) THEN
  UNDISCH_THEN `&0 <= r` (K ALL_TAC) THEN REMOVE_THEN "M" (K ALL_TAC) THEN
  FIRST_X_ASSUM(K ALL_TAC o SYM) THEN REMOVE_THEN "P" MP_TAC THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  ABBREV_TAC `n = CARD(s:real^N->bool)` THEN
  SUBGOAL_THEN `(s:real^N->bool) HAS_SIZE n` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
  UNDISCH_THEN `CARD(s:real^N->bool) = n` (K ALL_TAC) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`d:real`,`r:real`) THEN GEN_TAC THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN SIMP_TAC[HAS_SIZE] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ABBREV_TAC `t = {x:real^N | x IN s /\ norm(x) = r}` THEN
  SUBGOAL_THEN `FINITE(t:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^N) IN convex hull t` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPEC `convex hull t:real^N->bool`
      SEPARATING_HYPERPLANE_CLOSED_0) THEN
    ASM_SIMP_TAC[CONVEX_CONVEX_HULL; NOT_IMP; COMPACT_CONVEX_HULL;
                 FINITE_IMP_COMPACT; COMPACT_IMP_CLOSED] THEN
    REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
    X_GEN_TAC `v:real^N` THEN
    ABBREV_TAC `k = CARD(s:real^N->bool)` THEN
    SUBGOAL_THEN `(s:real^N->bool) HAS_SIZE k` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
    UNDISCH_THEN `CARD(s:real^N->bool) = k` (K ALL_TAC) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    GEOM_BASIS_MULTIPLE_TAC 1 `v:real^N` THEN X_GEN_TAC `m:real` THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
    ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL; REAL_LT_IMP_NZ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[HAS_SIZE] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN X_GEN_TAC `b:real` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[DOT_LMUL; DOT_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[real_gt; GSYM REAL_LT_LDIV_EQ] THEN
    SUBGOAL_THEN `&0 < b / m` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV];
      UNDISCH_THEN `&0 < b` (K ALL_TAC) THEN
      SPEC_TAC(`b / m:real`,`b:real`)] THEN
    X_GEN_TAC `b:real` THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!x:real^N e. &0 < e /\ e < b /\ x IN t ==> norm(x - e % basis 1) < r`
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:real^N`; `e:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `r = norm(x:real^N)` SUBST1_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[NORM_LT; dot]] THEN
      SIMP_TAC[SUM_CLAUSES_LEFT; DIMINDEX_GE_1] THEN
      SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
               BASIS_COMPONENT; DIMINDEX_GE_1; LE_REFL;
               ARITH_RULE `2 <= n ==> 1 <= n /\ ~(n = 1)`; ARITH] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_LT_RADD] THEN
      REWRITE_TAC[GSYM REAL_POW_2; GSYM REAL_LT_SQUARE_ABS] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!b. &0 < e /\ e < b /\ b < x ==> abs(x - e * &1) < abs x`) THEN
      EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[HULL_INC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?d. &0 < d /\
          !x:real^N a. x IN (s DIFF t) /\ norm(a) < d ==> norm(x - a) < r`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `s DIFF t:real^N->bool = {}` THENL
       [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
      EXISTS_TAC `inf (IMAGE (\x:real^N. r - norm x) (s DIFF t))` THEN
      SUBGOAL_THEN `FINITE(s DIFF t:real^N->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[FINITE_DIFF]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN SIMP_TAC
       [NORM_ARITH `norm a < r - norm x ==> norm(x - a:real^N) < r`] THEN
      EXPAND_TAC "t" THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM; REAL_SUB_LT] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_CBALL_0]) THEN
      ASM_MESON_TAC[REAL_LT_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?a. !x. x IN s ==> norm(x - a:real^N) < r`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `min (b / &2) (d / &2) % basis 1:real^N` THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(x:real^N) IN t` THENL
       [MATCH_MP_TAC(ASSUME
         `!x:real^N e. &0 < e /\ e < b /\ x IN t
                       ==> norm (x - e % basis 1) < r`) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(ASSUME
         `!x:real^N a. x IN s DIFF t /\ norm a < d ==> norm (x - a) < r`) THEN
        ASM_SIMP_TAC[IN_DIFF; NORM_MUL; LE_REFL; NORM_BASIS;
                     DIMINDEX_GE_1] THEN
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
       [ASM_MESON_TAC[MEMBER_NOT_EMPTY; NORM_ARITH
         `norm(x:real^N) < r ==> &0 < r`];
        ALL_TAC] THEN
      UNDISCH_THEN
        `!x a:real^N. &0 <= x /\ s SUBSET cball (a,x) ==> r <= x` (MP_TAC o
        SPECL [`max (&0) (r - inf (IMAGE (\x:real^N. r - norm(x - a)) s))`;
               `a:real^N`]) THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> (r <= max (&0) a <=> r <= a)`] THEN
      REWRITE_TAC[SUBSET; IN_CBALL; REAL_ARITH `a <= max a b`] THEN
      REWRITE_TAC[NOT_IMP; REAL_ARITH `~(r <= r - x) <=> &0 < x`] THEN
      ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
      ASM_REWRITE_TAC[FORALL_IN_IMAGE; REAL_SUB_LT] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `d <= b ==> d <= max a b`) THEN
      ONCE_REWRITE_TAC[REAL_ARITH `a <= b - c <=> c <= b - a`] THEN
      ASM_SIMP_TAC[REAL_INF_LE_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; ONCE_REWRITE_RULE[NORM_SUB] dist] THEN
      ASM_MESON_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY] THEN
  REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N->real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt((&(dimindex (:N)) / &(2 * dimindex (:N) + 2)) *
                   diameter(s:real^N->bool) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT;
    ASM_SIMP_TAC[SQRT_MUL; DIAMETER_POS_LE; REAL_POW_LE; REAL_LE_DIV;
                 REAL_POS; POW_2_SQRT; REAL_LE_REFL]] THEN

  SUBGOAL_THEN
   `sum t (\y:real^N. &2 * r pow 2) <=
    sum t (\y. (&1 - l y) * diameter(s:real^N->bool) pow 2)`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (t DELETE x) (\x:real^N. l(x)) *
                diameter(s:real^N->bool) pow 2` THEN CONJ_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC[SUM_DELETE; ETA_AX; REAL_LE_REFL]] THEN
    REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (t DELETE x) (\y:real^N. l y * norm(y - x) pow 2)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
      X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN ASM SET_TAC[]] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum t (\y:real^N. l y * norm (y - x) pow 2)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_SUPERSET THEN
      ASM_REWRITE_TAC[FINITE_DELETE] THEN
      CONJ_TAC THENL [SET_TAC[]; REWRITE_TAC[IN_DELETE]] THEN
      SIMP_TAC[TAUT `p /\ ~(p /\ ~q) <=> p /\ q`] THEN
      REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN REAL_ARITH_TAC] THEN
    REWRITE_TAC[NORM_POW_2; VECTOR_ARITH
     `(y - x:real^N) dot (y - x) = (x dot x + y dot y) - &2 * x dot y`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum t (\y:real^N. l y * (&2 * r pow 2 - &2 * (x dot y)))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
      UNDISCH_TAC `(x:real^N) IN t` THEN EXPAND_TAC "t" THEN
      REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN
      SIMP_TAC[NORM_EQ_SQUARE; NORM_POW_2] THEN REAL_ARITH_TAC] THEN
    REWRITE_TAC[REAL_ARITH `x * (&2 * y - &2 * z) = &2 * (x * y - x * z)`] THEN
    REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS] THEN
    ASM_SIMP_TAC[SUM_SUB; FINITE_DELETE; SUM_RMUL] THEN
    REWRITE_TAC[GSYM DOT_RMUL] THEN
    ASM_SIMP_TAC[GSYM DOT_RSUM; DOT_RZERO] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[SUM_CONST; SUM_RMUL; SUM_SUB] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; MULT_CLAUSES] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
    SUBGOAL_THEN `&0 < &(CARD(t:real^N->bool) * 2)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < n * 2 <=> ~(n = 0)`] THEN
      ASM_SIMP_TAC[CARD_EQ_0];
      ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      REWRITE_TAC[REAL_ARITH `(a * b) / c:real = a / c * b`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      REWRITE_TAC[ARITH_RULE `2 * n + 2 = (n + 1) * 2`; GSYM REAL_OF_NUM_MUL;
                  real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[GSYM real_div] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SUBGOAL_THEN `&(dimindex(:N)) = &(dimindex(:N) + 1) - &1`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC lemma THEN
        ASM_SIMP_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; CARD_EQ_0;
                     ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(s:real^N->bool)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_SUBSET THEN
        ASM SET_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* The Dugundji extension theorem, and Tietze variants as corollaries.       *)
(* ------------------------------------------------------------------------- *)

let DUGUNDJI = prove
 (`!f:real^M->real^N c u s.
        convex c /\ ~(c = {}) /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\ IMAGE f s SUBSET c
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\
                !x. x IN s ==> g x = f x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    EXISTS_TAC `(\x. y):real^M->real^N` THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u DIFF s:real^M->bool`;
                 `{ ball(x:real^M,setdist({x},s) / &2) |x| x IN u DIFF s}`]
        PARACOMPACT) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC; OPEN_BALL] THEN ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; UNIONS_GSPEC] THEN
    X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN EXISTS_TAC `x:real^M` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x / &2`) THEN
    ASM_MESON_TAC[SETDIST_POS_LE; SETDIST_EQ_0_CLOSED_IN];
    DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `!t. t IN c
        ==> ?v a:real^M. v IN u /\ ~(v IN s) /\ a IN s /\
                         t SUBSET ball(v,setdist({v},s) / &2) /\
                         dist(v,a) <= &2 * setdist({v},s)`
  MP_TAC THENL
   [X_GEN_TAC `t:real^M->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^M->bool`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^M` THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL[`{v:real^M}`; `s:real^M->bool`; `&2 * setdist({v:real^M},s)`]
        REAL_SETDIST_LT_EXISTS) THEN
    ASM_SIMP_TAC[NOT_INSERT_EMPTY; SETDIST_POS_LE; REAL_ARITH
      `&0 <= x ==> (x < &2 * x <=> ~(x = &0))`] THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE; IN_SING; SETDIST_EQ_0_CLOSED_IN];
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [`vv:(real^M->bool)->real^M`; `aa:(real^M->bool)->real^M`] THEN
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `!t v:real^M. t IN c /\ v IN t ==> setdist({vv t},s) <= &2 * setdist({v},s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^M->bool`) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o el 3 o CONJUNCTS) THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^M`) THEN ASM_REWRITE_TAC[IN_BALL] THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `(vv:(real^M->bool)->real^M) t`;
                   `v:real^M`] SETDIST_SING_TRIANGLE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t v a:real^M. t IN c /\ v IN t /\ a IN s
                   ==> dist(a,aa t) <= &6 * dist(a,v)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real^M->bool`; `v:real^M`]) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `t:real^M->bool`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o funpow 3 CONJUNCT2) THEN
    REWRITE_TAC[IMP_CONJ; SUBSET; IN_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^M`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`{v:real^M}`; `s:real^M->bool`; `v:real^M`; `a:real^M`]
        SETDIST_LE_DIST) THEN
    ASM_REWRITE_TAC[IN_SING] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^M->bool)->bool`; `u DIFF s:real^M->bool`]
        SUBORDINATE_PARTITION_OF_UNITY) THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h:(real^M->bool)->real^M->real` THEN STRIP_TAC THEN
  EXISTS_TAC
   `\x. if x IN s then (f:real^M->real^N) x
        else vsum c (\t:real^M->bool. h t x % f(aa t))` THEN
  SIMP_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONVEX_VSUM_STRONG THEN ASM SET_TAC[]] THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `a:real^M` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(a:real^M) IN s` THENL
   [ALL_TAC;
    MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN_OPEN_IN THEN
    MAP_EVERY EXISTS_TAC
     [`\x:real^M.
        vsum c (\t:real^M->bool. h t x % (f:real^M->real^N) (aa t))`;
      `u DIFF s:real^M->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL; IN_DIFF] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^M`) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:real^M->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN_OPEN_IN THEN MAP_EVERY EXISTS_TAC
     [`\x. vsum {u | u IN c /\ ~(!x:real^M. x IN n ==> h u x = &0)}
                (\t:real^M->bool. h t x % (f:real^M->real^N) (aa t))`;
      `(u DIFF s) INTER n:real^M->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL; OPEN_IN_INTER_OPEN;
                 IN_INTER; IN_DIFF] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC VSUM_SUPERSET THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0] THEN ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_VSUM THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_VMUL THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real^M->bool`) THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      DISCH_THEN(MP_TAC o SPEC `a:real^M` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[IN_DIFF; ETA_AX] THEN
      REWRITE_TAC[CONTINUOUS_WITHIN] THEN MATCH_MP_TAC EQ_IMP THEN
      MATCH_MP_TAC LIM_TRANSFORM_WITHIN_SET THEN
      SUBGOAL_THEN `open_in (subtopology euclidean u) (u DIFF s:real^M->bool)`
      MP_TAC THENL [ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL]; ALL_TAC] THEN
      REWRITE_TAC[EVENTUALLY_AT; OPEN_IN_CONTAINS_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `a:real^M` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[IN_DIFF] THEN MATCH_MP_TAC MONO_EXISTS THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_INTER; IN_DIFF] THEN
      MESON_TAC[DIST_SYM]]] THEN
  ASM_REWRITE_TAC[CONTINUOUS_WITHIN_OPEN] THEN
  X_GEN_TAC `w:real^N->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real^M->real^N) a`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
   [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^M`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[continuous_within] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ball(a:real^M,d / &6)` THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL; OPEN_BALL] THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < e / &6 <=> &0 < e`] THEN
  X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONVEX_VSUM_STRONG THEN
  ASM_SIMP_TAC[CONVEX_BALL; IN_DIFF] THEN
  X_GEN_TAC `t:real^M->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real^M) IN t` THENL [DISJ2_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[IN_BALL] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
   `dist(a:real^M,v) < d / &6
    ==> dist(a,a') <= &6 * dist(a,v) ==> dist(a',a) < d`)) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let TIETZE = prove
 (`!f:real^M->real^N u s B.
        &0 <= B /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\
        (!x. x IN s ==> norm(f x) <= B)
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x) /\
                (!x. x IN u ==> norm(g x) <= B)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `cball(vec 0:real^N,B)`; `u:real^M->bool`;
                 `s:real^M->bool`] DUGUNDJI) THEN
  ASM_REWRITE_TAC[CONVEX_CBALL; CBALL_EQ_EMPTY; REAL_NOT_LT] THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL_0] THEN
  MESON_TAC[]);;

let TIETZE_CLOSED_INTERVAL = prove
 (`!f:real^M->real^N u s a b.
        ~(interval[a,b] = {}) /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\
        (!x. x IN s ==> f x IN interval[a,b])
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x) /\
                (!x. x IN u ==> g(x) IN interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `interval[a:real^N,b]`; `u:real^M->bool`;
                 `s:real^M->bool`] DUGUNDJI) THEN
  ASM_REWRITE_TAC[CONVEX_INTERVAL; SUBSET; FORALL_IN_IMAGE] THEN
  MESON_TAC[]);;

let TIETZE_CLOSED_INTERVAL_1 = prove
 (`!f:real^N->real^1 u s a b.
        drop a <= drop b /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\
        (!x. x IN s ==> f x IN interval[a,b])
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x) /\
                (!x. x IN u ==> g(x) IN interval[a,b])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TIETZE_CLOSED_INTERVAL THEN
  ASM_REWRITE_TAC[INTERVAL_NE_EMPTY_1]);;

let TIETZE_OPEN_INTERVAL = prove
 (`!f:real^M->real^N u s a b.
        ~(interval(a,b) = {}) /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\
        (!x. x IN s ==> f x IN interval(a,b))
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x) /\
                (!x. x IN u ==> g(x) IN interval(a,b))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `interval(a:real^N,b)`; `u:real^M->bool`;
                 `s:real^M->bool`] DUGUNDJI) THEN
  ASM_REWRITE_TAC[CONVEX_INTERVAL; SUBSET; FORALL_IN_IMAGE] THEN
  MESON_TAC[]);;

let TIETZE_OPEN_INTERVAL_1 = prove
 (`!f:real^N->real^1 u s a b.
        drop a < drop b /\
        closed_in (subtopology euclidean u) s /\
        f continuous_on s /\
        (!x. x IN s ==> f x IN interval(a,b))
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x) /\
                (!x. x IN u ==> g(x) IN interval(a,b))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TIETZE_OPEN_INTERVAL THEN
  ASM_REWRITE_TAC[INTERVAL_NE_EMPTY_1]);;

let TIETZE_UNBOUNDED = prove
 (`!f:real^M->real^N u s.
        closed_in (subtopology euclidean u) s /\ f continuous_on s
        ==> ?g. g continuous_on u /\
                (!x. x IN s ==> g x = f x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `(:real^N)`; `u:real^M->bool`;
                 `s:real^M->bool`] DUGUNDJI) THEN
  ASM_REWRITE_TAC[CONVEX_UNIV; UNIV_NOT_EMPTY; SUBSET_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Convex cones and corresponding hulls.                                     *)
(* ------------------------------------------------------------------------- *)

let convex_cone = new_definition
 `convex_cone s <=> ~(s = {}) /\ convex s /\ conic s`;;

let CONVEX_CONE = prove
 (`!s:real^N->bool.
     convex_cone s <=>
        vec 0 IN s /\
        (!x y. x IN s /\ y IN s ==> (x + y) IN s) /\
        (!x c. x IN s /\ &0 <= c ==> (c % x) IN s)`,
  GEN_TAC THEN REWRITE_TAC[convex_cone; GSYM conic] THEN
  ASM_CASES_TAC `conic(s:real^N->bool)` THEN
  ASM_SIMP_TAC[CONIC_CONTAINS_0] THEN AP_TERM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[conic]) THEN
  REWRITE_TAC[convex] THEN EQ_TAC THEN
  ASM_SIMP_TAC[REAL_SUB_LE] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`&2 % (x:real^N)`; `&2 % (y:real^N)`; `&1 / &2`; `&1 / &2`]) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[VECTOR_MUL_LID; REAL_POS]);;

let CONVEX_CONE_ADD = prove
 (`!s x y. convex_cone s /\ x IN s /\ y IN s ==> (x + y) IN s`,
  MESON_TAC[CONVEX_CONE]);;

let CONVEX_CONE_MUL = prove
 (`!s c x. convex_cone s /\ &0 <= c /\ x IN s ==> (c % x) IN s`,
  MESON_TAC[CONVEX_CONE]);;

let CONVEX_CONE_NONEMPTY = prove
 (`!s. convex_cone s ==> ~(s = {})`,
  MESON_TAC[CONVEX_CONE; MEMBER_NOT_EMPTY]);;

let CONVEX_CONE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        convex_cone s /\ linear f ==> convex_cone(IMAGE f s)`,
  SIMP_TAC[convex_cone; CONVEX_LINEAR_IMAGE; IMAGE_EQ_EMPTY;
           CONIC_LINEAR_IMAGE]);;

let CONVEX_CONE_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (convex_cone(IMAGE f s) <=> convex_cone s)`,
  REWRITE_TAC[convex_cone] THEN
  MESON_TAC[IMAGE_EQ_EMPTY; CONVEX_LINEAR_IMAGE_EQ; CONIC_LINEAR_IMAGE_EQ]);;

add_linear_invariants [CONVEX_CONE_LINEAR_IMAGE_EQ];;

let CONVEX_CONE_HALFSPACE_GE = prove
 (`!a. convex_cone {x | a dot x >= &0}`,
  SIMP_TAC[CONVEX_CONE; real_ge; IN_ELIM_THM; DOT_RZERO; DOT_RADD; DOT_RMUL;
           REAL_LE_ADD; REAL_LE_MUL; REAL_LE_REFL]);;

let CONVEX_CONE_HALFSPACE_LE = prove
 (`!a. convex_cone {x | a dot x <= &0}`,
  REWRITE_TAC[REAL_ARITH `x <= &0 <=> &0 <= --x`; GSYM DOT_LNEG] THEN
  REWRITE_TAC[GSYM real_ge; CONVEX_CONE_HALFSPACE_GE]);;

let CONVEX_CONE_CONTAINS_0 = prove
 (`!s:real^N->bool. convex_cone s ==> vec 0 IN s`,
  SIMP_TAC[CONVEX_CONE]);;

let CONVEX_CONE_INTERS = prove
 (`!f. (!s:real^N->bool. s IN f ==> convex_cone s) ==> convex_cone(INTERS f)`,
  SIMP_TAC[convex_cone; CONIC_INTERS; CONVEX_INTERS] THEN
  REWRITE_TAC[GSYM convex_cone] THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^N` THEN
  ASM_SIMP_TAC[IN_INTERS; CONVEX_CONE_CONTAINS_0]);;

let CONVEX_CONE_CONVEX_CONE_HULL = prove
 (`!s. convex_cone(convex_cone hull s)`,
  SIMP_TAC[P_HULL; CONVEX_CONE_INTERS]);;

let CONVEX_CONVEX_CONE_HULL = prove
 (`!s. convex(convex_cone hull s)`,
  MESON_TAC[CONVEX_CONE_CONVEX_CONE_HULL; convex_cone]);;

let CONIC_CONVEX_CONE_HULL = prove
 (`!s. conic(convex_cone hull s)`,
  MESON_TAC[CONVEX_CONE_CONVEX_CONE_HULL; convex_cone]);;

let CONVEX_CONE_HULL_NONEMPTY = prove
 (`!s. ~(convex_cone hull s = {})`,
  MESON_TAC[CONVEX_CONE_CONVEX_CONE_HULL; convex_cone]);;

let CONVEX_CONE_HULL_CONTAINS_0 = prove
 (`!s. vec 0 IN convex_cone hull s`,
  MESON_TAC[CONVEX_CONE_CONVEX_CONE_HULL; CONVEX_CONE]);;

let CONVEX_CONE_HULL_ADD = prove
 (`!s x y:real^N.
        x IN convex_cone hull s /\ y IN convex_cone hull s
        ==> x + y IN convex_cone hull s`,
  MESON_TAC[CONVEX_CONE; CONVEX_CONE_CONVEX_CONE_HULL]);;

let CONVEX_CONE_HULL_MUL = prove
 (`!s c x:real^N.
        &0 <= c /\ x IN convex_cone hull s
        ==> (c % x) IN convex_cone hull s`,
  MESON_TAC[CONVEX_CONE; CONVEX_CONE_CONVEX_CONE_HULL]);;

let CONVEX_CONE_SUMS = prove
 (`!s t. convex_cone s /\ convex_cone t
         ==> convex_cone {x + y:real^N | x IN s /\ y IN t}`,
  SIMP_TAC[convex_cone; CONIC_SUMS; CONVEX_SUMS] THEN SET_TAC[]);;

let CONVEX_CONE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        convex_cone s /\ convex_cone t ==> convex_cone(s PCROSS t)`,
  SIMP_TAC[convex_cone; CONVEX_PCROSS; CONIC_PCROSS; PCROSS_EQ_EMPTY]);;

let CONVEX_CONE_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        convex_cone(s PCROSS t) <=> convex_cone s /\ convex_cone t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THENL
   [ASM_REWRITE_TAC[PCROSS_EMPTY; convex_cone]; ALL_TAC] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[PCROSS_EMPTY; convex_cone]; ALL_TAC] THEN
  EQ_TAC THEN REWRITE_TAC[CONVEX_CONE_PCROSS] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
     `(s:real^M->bool) PCROSS (t:real^N->bool)`] CONVEX_CONE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART];
    MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
     `(s:real^M->bool) PCROSS (t:real^N->bool)`] CONVEX_CONE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

let CONVEX_CONE_HULL_UNION = prove
 (`!s t. convex_cone hull(s UNION t) =
         {x + y:real^N | x IN convex_cone hull s /\ y IN convex_cone hull t}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN
    SIMP_TAC[CONVEX_CONE_SUMS; CONVEX_CONE_CONVEX_CONE_HULL] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`x:real^N`; `vec 0:real^N`] THEN
      ASM_SIMP_TAC[HULL_INC; CONVEX_CONE_HULL_CONTAINS_0; VECTOR_ADD_RID];
      MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `x:real^N`] THEN
      ASM_SIMP_TAC[HULL_INC; CONVEX_CONE_HULL_CONTAINS_0; VECTOR_ADD_LID]];
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_CONE_HULL_ADD THEN
    ASM_MESON_TAC[HULL_MONO; SUBSET_UNION; SUBSET]]);;

let CONVEX_CONE_SING = prove
 (`convex_cone {vec 0}`,
  SIMP_TAC[CONVEX_CONE; IN_SING; VECTOR_ADD_LID; VECTOR_MUL_RZERO]);;

let CONVEX_HULL_SUBSET_CONVEX_CONE_HULL = prove
 (`!s. convex hull s SUBSET convex_cone hull s`,
  GEN_TAC THEN MATCH_MP_TAC HULL_ANTIMONO THEN
  SIMP_TAC[convex_cone; SUBSET; IN]);;

let CONIC_HULL_SUBSET_CONVEX_CONE_HULL = prove
 (`!s. conic hull s SUBSET convex_cone hull s`,
  GEN_TAC THEN MATCH_MP_TAC HULL_ANTIMONO THEN
  SIMP_TAC[convex_cone; SUBSET; IN]);;

let CONVEX_CONE_HULL_SEPARATE_NONEMPTY = prove
 (`!s:real^N->bool.
    ~(s = {})
    ==> convex_cone hull s = conic hull (convex hull s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC HULL_MINIMAL THEN
  REWRITE_TAC[CONIC_CONVEX_CONE_HULL; CONVEX_HULL_SUBSET_CONVEX_CONE_HULL] THEN
  ASM_SIMP_TAC[CONVEX_CONIC_HULL; CONVEX_CONVEX_HULL; CONIC_CONIC_HULL;
               convex_cone; CONIC_HULL_EQ_EMPTY; CONVEX_HULL_EQ_EMPTY] THEN
  ASM_MESON_TAC[HULL_SUBSET; SUBSET_REFL; SUBSET_TRANS]);;

let CONVEX_CONE_HULL_EMPTY = prove
 (`convex_cone hull {} = {vec 0}`,
  MATCH_MP_TAC HULL_UNIQUE THEN
  REWRITE_TAC[CONVEX_CONE_CONTAINS_0; EMPTY_SUBSET; CONVEX_CONE_SING;
              SET_RULE `{a} SUBSET s <=> a IN s`; CONVEX_CONE_CONTAINS_0]);;

let CONVEX_CONE_HULL_SEPARATE = prove
 (`!s:real^N->bool.
    convex_cone hull s = vec 0 INSERT conic hull (convex hull s)`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[CONVEX_CONE_HULL_EMPTY; CONVEX_HULL_EMPTY; CONIC_HULL_EMPTY] THEN
  ASM_SIMP_TAC[CONVEX_CONE_HULL_SEPARATE_NONEMPTY] THEN
  MATCH_MP_TAC(SET_RULE `a IN s ==> s = a INSERT s`) THEN
  ASM_SIMP_TAC[CONIC_CONTAINS_0; CONIC_CONIC_HULL] THEN
  ASM_REWRITE_TAC[CONIC_HULL_EQ_EMPTY; CONVEX_HULL_EQ_EMPTY]);;

let CONVEX_CONE_HULL_CONVEX_HULL_NONEMPTY = prove
 (`!s:real^N->bool.
        ~(s = {})
        ==> convex_cone hull s = {c % x | &0 <= c /\ x IN convex hull s}`,
  SIMP_TAC[CONVEX_CONE_HULL_SEPARATE_NONEMPTY; CONIC_HULL_EXPLICIT]);;

let CONVEX_CONE_HULL_CONVEX_HULL = prove
 (`!s:real^N->bool.
        convex_cone hull s =
        vec 0 INSERT {c % x | &0 <= c /\ x IN convex hull s}`,
  REWRITE_TAC[CONVEX_CONE_HULL_SEPARATE; CONIC_HULL_EXPLICIT]);;

let CONVEX_CONE_HULL_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f
        ==> convex_cone hull (IMAGE f s) = IMAGE f (convex_cone hull s)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^M-> bool = {}` THEN
  ASM_SIMP_TAC[CONVEX_CONE_HULL_SEPARATE_NONEMPTY; IMAGE_EQ_EMPTY;
               CONVEX_HULL_LINEAR_IMAGE; CONIC_HULL_LINEAR_IMAGE] THEN
  REWRITE_TAC[IMAGE_CLAUSES; CONVEX_CONE_HULL_EMPTY] THEN
  MATCH_MP_TAC(SET_RULE `f x = y ==> {y} = {f x}`) THEN
  ASM_MESON_TAC[LINEAR_0]);;

add_linear_invariants [CONVEX_CONE_HULL_LINEAR_IMAGE];;

let SUBSPACE_IMP_CONVEX_CONE = prove
 (`!s. subspace s ==> convex_cone s`,
  SIMP_TAC[subspace; CONVEX_CONE]);;

let CONVEX_CONE_SPAN = prove
 (`!s. convex_cone(span s)`,
  SIMP_TAC[convex_cone; CONVEX_SPAN; CONIC_SPAN; GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[SPAN_0]);;

let CONVEX_CONE_NEGATIONS = prove
 (`!s. convex_cone s ==> convex_cone (IMAGE (--) s)`,
  SIMP_TAC[convex_cone; IMAGE_EQ_EMPTY; CONIC_NEGATIONS; CONVEX_NEGATIONS]);;

let SUBSPACE_CONVEX_CONE_SYMMETRIC = prove
 (`!s:real^N->bool.
        subspace s <=> convex_cone s /\ (!x. x IN s ==> --x IN s)`,
  GEN_TAC THEN REWRITE_TAC[subspace; CONVEX_CONE] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THENL
   [ASM_MESON_TAC[VECTOR_ARITH `--x:real^N = -- &1 % x`];
    MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN DISCH_TAC THEN
    DISJ_CASES_TAC(SPEC `c:real` REAL_LE_NEGTOTAL) THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[VECTOR_ARITH `c % x:real^N = --(--c % x)`]]);;

let SPAN_CONVEX_CONE_ALLSIGNS = prove
 (`!s:real^N->bool. span s = convex_cone hull (s UNION IMAGE (--) s)`,
  GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN CONJ_TAC THENL
     [MESON_TAC[HULL_SUBSET; SUBSET_UNION; SUBSET_TRANS]; ALL_TAC] THEN
    REWRITE_TAC[SUBSPACE_CONVEX_CONE_SYMMETRIC;
                CONVEX_CONE_CONVEX_CONE_HULL] THEN
    MATCH_MP_TAC HULL_INDUCT THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
      DISCH_TAC THEN MATCH_MP_TAC HULL_INC THEN
      REWRITE_TAC[IN_UNION; IN_IMAGE] THEN ASM_MESON_TAC[VECTOR_NEG_NEG];
      SUBGOAL_THEN `!s. {x:real^N | (--x) IN s} = IMAGE (--) s`
       (fun th -> SIMP_TAC[th; CONVEX_CONE_NEGATIONS;
                           CONVEX_CONE_CONVEX_CONE_HULL]) THEN
      GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[VECTOR_NEG_NEG]];
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONE_SPAN] THEN
    REWRITE_TAC[UNION_SUBSET; SPAN_INC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    MESON_TAC[SPAN_SUPERSET; SPAN_NEG]]);;

(* ------------------------------------------------------------------------- *)
(* Epigraphs of convex functions.                                            *)
(* ------------------------------------------------------------------------- *)

let epigraph = new_definition
  `epigraph s (f:real^N->real) =
       {xy:real^((N,1)finite_sum) |
             fstcart xy IN s /\ f(fstcart xy) <= drop(sndcart xy)}`;;

let IN_EPIGRAPH = prove
 (`!x y. (pastecart x (lift y)) IN epigraph s f <=> x IN s /\ f(x) <= y`,
  REWRITE_TAC[epigraph; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART;
              LIFT_DROP]);;

let CONVEX_EPIGRAPH = prove
 (`!f s. f convex_on s /\ convex s <=> convex(epigraph s f)`,
  REWRITE_TAC[convex; convex_on; IN_ELIM_THM; SNDCART_ADD; SNDCART_CMUL;
   epigraph; FSTCART_ADD; FSTCART_CMUL; FORALL_PASTECART; FSTCART_PASTECART;
   SNDCART_PASTECART] THEN
  REWRITE_TAC[GSYM FORALL_DROP; DROP_ADD; DROP_CMUL] THEN
  MESON_TAC[REAL_LE_REFL; REAL_LE_ADD2; REAL_LE_LMUL; REAL_LE_TRANS]);;

let CONVEX_EPIGRAPH_CONVEX = prove
 (`!f s. convex s ==> (f convex_on s <=> convex(epigraph s f))`,
  REWRITE_TAC[GSYM CONVEX_EPIGRAPH] THEN CONV_TAC TAUT);;

let CONVEX_ON_EPIGRAPH_SLICE_LE = prove
 (`!f:real^N->real s a.
        f convex_on s /\ convex s ==> convex {x | x IN s /\ f(x) <= a}`,
  SIMP_TAC[convex_on; convex; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  MATCH_MP_TAC REAL_CONVEX_BOUND_LE THEN ASM_REWRITE_TAC[]);;

let CONVEX_ON_EPIGRAPH_SLICE_LT = prove
 (`!f:real^N->real s a.
        f convex_on s /\ convex s ==> convex {x | x IN s /\ f(x) < a}`,
  SIMP_TAC[convex_on; convex; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LET_TRANS) THEN
  MATCH_MP_TAC REAL_CONVEX_BOUND_LT THEN ASM_REWRITE_TAC[]);;

let CONVEX_ON_SUP = prove
 (`!t:A->bool s:real^N->bool.
        convex s /\
        (!i. i IN t ==> f i convex_on s) /\
        (!x. x IN s ==> ?B. !i. i IN t ==> f i x <= B)
        ==> (\x. sup {f i x | i IN t}) convex_on s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `t:A->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; CONVEX_ON_CONST; SET_RULE
   `{f i x | i | F} = {}`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ASM_SIMP_TAC[CONVEX_EPIGRAPH_CONVEX] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `convex(INTERS {epigraph (s:real^N->bool) (f i) | (i:A) IN t})`
  MP_TAC THENL [ASM_SIMP_TAC[CONVEX_INTERS; FORALL_IN_GSPEC]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; INTERS_GSPEC; IN_ELIM_THM] THEN
  REWRITE_TAC[epigraph; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[GSYM FORALL_DROP] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real`] THEN
  ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THENL
   [CONV_TAC SYM_CONV; ASM_MESON_TAC[MEMBER_NOT_EMPTY]] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) REAL_SUP_LE_EQ o lhand o snd) THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Use this to derive general bound property of convex function.             *)
(* ------------------------------------------------------------------------- *)

let FORALL_OF_PASTECART = prove
 (`(!p. P (fstcart o p) (sndcart o p)) <=> (!x:A->B^M y:A->B^N. P x y)`,
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `\a:A. pastecart (x a :B^M) (y a :B^N)`) THEN
  REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART; ETA_AX]);;

let FORALL_OF_DROP = prove
 (`(!v. P (drop o v)) <=> (!x:A->real. P x)`,
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `\a:A. lift(x a)`) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX]);;

let CONVEX_ON_JENSEN = prove
 (`!f:real^N->real s.
        convex s
        ==> (f convex_on s <=>
                !k u x.
                   (!i:num. 1 <= i /\ i <= k ==> &0 <= u(i) /\ x(i) IN s) /\
                   (sum (1..k) u = &1)
                   ==> f(vsum (1..k) (\i. u(i) % x(i)))
                           <= sum (1..k) (\i. u(i) * f(x(i))))`,
  let lemma = prove
   (`(!x. P x ==> (Q x = R x)) ==> (!x. P x) ==> ((!x. Q x) <=> (!x. R x))`,
    MESON_TAC[]) in
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (fun th -> REWRITE_TAC[MATCH_MP CONVEX_EPIGRAPH_CONVEX th]) THEN
  REWRITE_TAC[CONVEX_INDEXED; epigraph] THEN
  SIMP_TAC[IN_ELIM_THM; SNDCART_ADD; SNDCART_CMUL; FINITE_NUMSEG;
           FSTCART_ADD; FSTCART_CMUL; FORALL_PASTECART; DROP_CMUL;
           FSTCART_PASTECART; SNDCART_PASTECART;
           FSTCART_VSUM; SNDCART_VSUM; DROP_VSUM; o_DEF] THEN
  REWRITE_TAC[GSYM(ISPEC `fstcart` o_THM); GSYM(ISPEC `sndcart` o_THM)] THEN
  REWRITE_TAC[GSYM(ISPEC `drop` o_THM)] THEN
  REWRITE_TAC[FORALL_OF_PASTECART; FORALL_OF_DROP] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONVEX_INDEXED]) THEN
  REPEAT(MATCH_MP_TAC lemma THEN GEN_TAC) THEN SIMP_TAC[] THEN
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN DISCH_THEN(K ALL_TAC) THEN
  EQ_TAC THEN SIMP_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  ASM_SIMP_TAC[SUM_LE_NUMSEG; REAL_LE_LMUL]);;

let CONVEX_ON_IMP_JENSEN = prove
 (`!f:real^N->real s k:A->bool u x.
        f convex_on s /\ convex s /\ FINITE k /\
        (!i. i IN k ==> &0 <= u i /\ x i IN s) /\ sum k u = &1
        ==> f(vsum k (\i. u i % x i)) <= sum k (\i. u i * f(x i))`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  ABBREV_TAC `n = CARD(k:A->bool)` THEN
  REWRITE_TAC[INJECTIVE_ON_ALT] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num->A`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  ASM_SIMP_TAC[VSUM_IMAGE; SUM_IMAGE; FINITE_NUMSEG; IMP_CONJ; o_DEF] THEN
  DISCH_TAC THEN MP_TAC(ISPECL [`f:real^N->real`; `s:real^N->bool`]
        CONVEX_ON_JENSEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[GSYM IN_NUMSEG] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Another intermediate value theorem formulation.                           *)
(* ------------------------------------------------------------------------- *)

let IVT_INCREASING_COMPONENT_ON_1 = prove
 (`!f:real^1->real^N a b y k.
        drop a <= drop b /\ 1 <= k /\ k <= dimindex(:N) /\
        f continuous_on interval[a,b] /\
        f(a)$k <= y /\ y <= f(b)$k
        ==> ?x. x IN interval[a,b] /\ f(x)$k = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (f:real^1->real^N) (interval[a,b])`]
        CONNECTED_IVT_COMPONENT) THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_IN_IMAGE] THEN
  ASM_SIMP_TAC[CONNECTED_CONTINUOUS_IMAGE; CONVEX_CONNECTED;
               CONVEX_INTERVAL] THEN
  EXISTS_TAC `a:real^1` THEN ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL] THEN
  EXISTS_TAC `b:real^1` THEN ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL]);;

let IVT_INCREASING_COMPONENT_1 = prove
 (`!f:real^1->real^N a b y k.
        drop a <= drop b /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> f continuous at x) /\
        f(a)$k <= y /\ y <= f(b)$k
        ==> ?x. x IN interval[a,b] /\ f(x)$k = y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IVT_INCREASING_COMPONENT_ON_1 THEN
  ASM_SIMP_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON]);;

let IVT_DECREASING_COMPONENT_ON_1 = prove
 (`!f:real^1->real^N a b y k.
        drop a <= drop b /\ 1 <= k /\ k <= dimindex(:N) /\
        f continuous_on interval[a,b] /\
        f(b)$k <= y /\ y <= f(a)$k
        ==> ?x. x IN interval[a,b] /\ f(x)$k = y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_EQ_NEG2] THEN
  ASM_SIMP_TAC[GSYM VECTOR_NEG_COMPONENT] THEN
  MATCH_MP_TAC IVT_INCREASING_COMPONENT_ON_1 THEN
  ASM_SIMP_TAC[VECTOR_NEG_COMPONENT; CONTINUOUS_ON_NEG; REAL_LE_NEG2]);;

let IVT_DECREASING_COMPONENT_1 = prove
 (`!f:real^1->real^N a b y k.
        drop a <= drop b /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> f continuous at x) /\
        f(b)$k <= y /\ y <= f(a)$k
        ==> ?x. x IN interval[a,b] /\ f(x)$k = y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IVT_DECREASING_COMPONENT_ON_1 THEN
  ASM_SIMP_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON]);;

(* ------------------------------------------------------------------------- *)
(* A bound within a convex hull, and so an interval.                         *)
(* ------------------------------------------------------------------------- *)

let CONVEX_ON_CONVEX_HULL_BOUND = prove
 (`!f s b. f convex_on (convex hull s) /\
           (!x:real^N. x IN s ==> f(x) <= b)
           ==> !x. x IN convex hull s ==> f(x) <= b`,
  REPEAT GEN_TAC THEN SIMP_TAC[CONVEX_ON_JENSEN; CONVEX_CONVEX_HULL] THEN
  STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[CONVEX_HULL_INDEXED] THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `u:num->real`; `v:num->real^N`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..k) (\i. u i * f(v i :real^N))` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET; HULL_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..k) (\i. u i * b)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[REAL_LE_LMUL];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[SUM_LMUL] THEN
  ASM_MESON_TAC[REAL_LE_REFL; REAL_MUL_RID]);;

let UNIT_INTERVAL_CONVEX_HULL = prove
 (`interval [vec 0,vec 1:real^N] =
     convex hull
       {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                           ==> ((x$i = &0) \/ (x$i = &1))}`,
  let lemma = prove
   (`FINITE {i | 1 <= i /\ i <= n /\ P(i)} /\
     CARD {i | 1 <= i /\ i <= n /\ P(i)} <= n`,
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..n`;
      GEN_REWRITE_TAC RAND_CONV [ARITH_RULE `x = (x + 1) - 1`] THEN
      REWRITE_TAC[GSYM CARD_NUMSEG] THEN MATCH_MP_TAC CARD_SUBSET] THEN
    SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; SUBSET; IN_ELIM_THM]) in
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[CONVEX_INTERVAL; SUBSET; IN_INTERVAL; IN_ELIM_THM] THEN
    SIMP_TAC[VEC_COMPONENT] THEN MESON_TAC[REAL_LE_REFL; REAL_POS]] THEN
  SUBGOAL_THEN
   `!n x:real^N.
        x IN interval[vec 0,vec 1] /\
        n <= dimindex(:N) /\
        CARD {i | 1 <= i /\ i <= dimindex(:N) /\ ~(x$i = &0)} <= n
        ==> x IN convex hull
                  {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                                  ==> ((x$i = &0) \/ (x$i = &1))}`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `dimindex(:N)` THEN
    ASM_REWRITE_TAC[LE_REFL; lemma]] THEN
  INDUCT_TAC THEN X_GEN_TAC `x:real^N` THENL
   [SIMP_TAC[LE; lemma; CARD_EQ_0] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; BETA_THM] THEN
    REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `x = vec 0:real^N` SUBST1_TAC THENL
     [ASM_SIMP_TAC[CART_EQ; VEC_COMPONENT]; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
    SIMP_TAC[IN_ELIM_THM; VEC_COMPONENT];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `{i | 1 <= i /\ i <= dimindex(:N) /\ ~((x:real^N)$i = &0)} = {}`
  THENL
   [DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; BETA_THM] THEN
    REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `x = vec 0:real^N` SUBST1_TAC THENL
     [ASM_SIMP_TAC[CART_EQ; VEC_COMPONENT]; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
    SIMP_TAC[IN_ELIM_THM; VEC_COMPONENT];
    ALL_TAC] THEN
  MP_TAC(ISPEC
   `IMAGE (\i. x$i)
      {i | 1 <= i /\ i <= dimindex(:N) /\ ~((x:real^N)$i = &0)}`
   INF_FINITE) THEN
  ABBREV_TAC `xi = inf
   (IMAGE (\i. x$i)
     {i | 1 <= i /\ i <= dimindex(:N) /\ ~((x:real^N)$i = &0)})` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; lemma] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [IN_IMAGE; IN_ELIM_THM] THEN
  REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (x:real^N)$i /\ x$i <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `x:real^N IN interval [vec 0,vec 1]` THEN
    ASM_SIMP_TAC[IN_INTERVAL; VEC_COMPONENT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `x <= &1 ==> (x = &1) \/ x < &1`))
  THENL
   [SUBGOAL_THEN
     `x = lambda i. if (x:real^N)$i = &0 then &0 else &1`
    SUBST1_TAC THENL
     [UNDISCH_TAC `x:real^N IN interval [vec 0,vec 1]` THEN
      ASM_SIMP_TAC[CART_EQ; IN_INTERVAL; VEC_COMPONENT; LAMBDA_BETA] THEN
      ASM_MESON_TAC[REAL_LE_ANTISYM];
      ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
    SIMP_TAC[IN_ELIM_THM; LAMBDA_BETA] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `x:real^N =
        x$i % (lambda j. if x$j = &0 then &0 else &1) +
        (&1 - x$i) %
        (lambda j. if x$j = &0 then &0 else (x$j - x$i) / (&1 - x$i))`
  SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             LAMBDA_BETA; VEC_COMPONENT] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; ARITH_RULE `x < &1 ==> ~(&1 - x = &0)`] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[convex] CONVEX_CONVEX_HULL) THEN
  ASM_SIMP_TAC[REAL_ARITH `x < &1 ==> &0 <= &1 - x`;
               REAL_ARITH `x + &1 - x = &1`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
    SIMP_TAC[LAMBDA_BETA; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC k <= n ==> k <= n`] THEN CONJ_TAC THENL
   [SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; VEC_COMPONENT] THEN
    GEN_TAC THEN STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_POS] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ;
                 REAL_ARITH `x < &1 ==> &0 < &1 - x`] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_LE; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_ARITH `a - b <= &1 - b <=> a <= &1`] THEN
    UNDISCH_TAC `x:real^N IN interval [vec 0,vec 1]` THEN
    ASM_SIMP_TAC[CART_EQ; IN_INTERVAL; VEC_COMPONENT; LAMBDA_BETA];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
   `CARD({i | 1 <= i /\ i <= dimindex(:N) /\ ~((x:real^N)$i = &0)}
         DELETE i)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[lemma; FINITE_DELETE] THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_ELIM_THM] THEN
    GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[CONTRAPOS_THM] THEN
    SIMP_TAC[real_div; REAL_SUB_REFL; REAL_MUL_LZERO];
    SIMP_TAC[lemma; CARD_DELETE] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `x <= SUC n ==> x - 1 <= n`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Some convexity-related properties of Hausdorff distance                   *)
(* ------------------------------------------------------------------------- *)

let HAUSDIST_CONVEX_HULLS = prove
 (`!s t:real^N->bool.
        bounded s /\ bounded t
        ==> hausdist(convex hull s,convex hull t) <= hausdist(s,t)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_MESON_TAC[HAUSDIST_EMPTY; CONVEX_HULL_EMPTY; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_MESON_TAC[HAUSDIST_EMPTY; CONVEX_HULL_EMPTY; REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_HAUSDIST_LE THEN ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN
  CONJ_TAC THEN MATCH_MP_TAC CONVEX_ON_CONVEX_HULL_BOUND THEN
  CONJ_TAC THEN SIMP_TAC[CONVEX_ON_SETDIST; CONVEX_CONVEX_HULL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_HAUSDIST THEN
  ASM_REWRITE_TAC[LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM; CONJ_ASSOC] THEN
  (CONJ_TAC THENL
    [CONJ_TAC; ASM_MESON_TAC[SETDIST_SUBSET_RIGHT; HULL_SUBSET]]) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] BOUNDED_DIFFS) THEN
  ASM_REWRITE_TAC[bounded; FORALL_IN_GSPEC; GSYM dist] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  ASM_MESON_TAC[SETDIST_LE_DIST; dist; DIST_SYM; REAL_LE_TRANS;
                MEMBER_NOT_EMPTY; IN_SING]);;

let HAUSDIST_SUMS = prove
 (`!s t:real^N->bool u.
        bounded s /\ bounded t /\ convex s /\ convex t /\ bounded u /\
        ~(s = {}) /\ ~(t = {}) /\ ~(u = {})
        ==> hausdist({x + e | x IN s /\ e IN u},
                     {y + e | y IN t /\ e IN u}) =
            hausdist(s,t)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[MESON[HAUSDIST_CLOSURE]
   `hausdist(s:real^N->bool,t) = hausdist(closure s,closure t)`] THEN
  SIMP_TAC[CLOSURE_SUMS] THEN
  SIMP_TAC[CLOSURE_CLOSED; CLOSED_CBALL; GSYM COMPACT_CLOSURE] THEN
  ONCE_REWRITE_TAC[GSYM CLOSURE_EQ_EMPTY] THEN
  ASM_CASES_TAC
   `convex(closure s:real^N->bool) /\ convex(closure t:real^N->bool)`
  THENL [POP_ASSUM MP_TAC; ASM_MESON_TAC[CONVEX_CLOSURE]] THEN
  ASM_CASES_TAC `convex(s:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `convex(t:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`closure u:real^N->bool`,`u:real^N->bool`) THEN
  SPEC_TAC(`closure t:real^N->bool`,`t:real^N->bool`) THEN
  SPEC_TAC(`closure s:real^N->bool`,`s:real^N->bool`) THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_HAUSDIST_LE_SUMS THEN
  MAP_EVERY ABBREV_TAC
   [`a = hausdist(s:real^N->bool,t)`;
    `b = hausdist({x + e:real^N | x IN s /\ e IN u},
                  {y + e | y IN t /\ e IN u})`] THEN
   ASM_REWRITE_TAC[CBALL_EQ_EMPTY; REAL_NOT_LT; SET_RULE
    `{f x y | x IN s /\ y IN t} = {} <=> s = {} \/ t = {}`]
  THENL
   [REWRITE_TAC[SUMS_ASSOC] THEN
    GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
      [SUMS_SYM] THEN
    REWRITE_TAC[GSYM SUMS_ASSOC] THEN CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `s SUBSET s'
      ==> {f x y | x IN s /\ y IN t} SUBSET {f x y | x IN s' /\ y IN t}`) THEN
    EXPAND_TAC "a" THENL
     [ALL_TAC; ONCE_REWRITE_TAC[HAUSDIST_SYM]] THEN
    MATCH_MP_TAC HAUSDIST_COMPACT_SUMS THEN ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
    CONJ_TAC THEN MATCH_MP_TAC SUBSET_SUMS_RCANCEL THEN
    EXISTS_TAC `u:real^N->bool` THEN
    ASM_SIMP_TAC[CLOSED_COMPACT_SUMS; COMPACT_CBALL; COMPACT_IMP_CLOSED;
      CONVEX_CBALL; COMPACT_IMP_BOUNDED; CONVEX_SUMS; REAL_NOT_LT] THEN
    REWRITE_TAC[SUMS_ASSOC] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [SUMS_SYM] THEN
    REWRITE_TAC[GSYM SUMS_ASSOC] THEN
    EXPAND_TAC "b" THENL
     [ALL_TAC; ONCE_REWRITE_TAC[HAUSDIST_SYM]] THEN
    MATCH_MP_TAC HAUSDIST_COMPACT_SUMS THEN
    ASM_SIMP_TAC[BOUNDED_SUMS; COMPACT_SUMS; COMPACT_CBALL;
     COMPACT_IMP_BOUNDED; CBALL_EQ_EMPTY; REAL_NOT_LT; SET_RULE
     `{f x y | x IN s /\ y IN t} = {} <=> s = {} \/ t = {}`]]);;

(* ------------------------------------------------------------------------- *)
(* Representation of any interval as a finite convex hull.                   *)
(* ------------------------------------------------------------------------- *)

let CLOSED_INTERVAL_AS_CONVEX_HULL = prove
 (`!a b:real^N. ?s. FINITE s /\ interval[a,b] = convex hull s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `interval[a:real^N,b] = {}` THENL
   [ASM_MESON_TAC[CONVEX_HULL_EMPTY; FINITE_EMPTY]; ALL_TAC] THEN
  ASM_SIMP_TAC[CLOSED_INTERVAL_IMAGE_UNIT_INTERVAL] THEN
  SUBGOAL_THEN
   `?s:real^N->bool. FINITE s /\ interval[vec 0,vec 1] = convex hull s`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC
     `{x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                      ==> ((x$i = &0) \/ (x$i = &1))}` THEN
    REWRITE_TAC[UNIT_INTERVAL_CONVEX_HULL] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     `IMAGE (\s. (lambda i. if i IN s then &1 else &0):real^N)
            {t | t SUBSET (1..dimindex(:N))}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET; FINITE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC
     `{i | 1 <= i /\ i <= dimindex(:N) /\ ((x:real^N)$i = &1)}` THEN
    SIMP_TAC[CART_EQ; IN_ELIM_THM; IN_NUMSEG; LAMBDA_BETA] THEN
    ASM_MESON_TAC[];
    EXISTS_TAC `IMAGE (\x:real^N. a + x)
                      (IMAGE (\x. (lambda i. ((b:real^N)$i - a$i) * x$i))
                             (s:real^N->bool))` THEN
    ASM_SIMP_TAC[FINITE_IMAGE; CONVEX_HULL_TRANSLATION] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC(GSYM CONVEX_HULL_LINEAR_IMAGE) THEN
    SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Characterizations of convex functions in terms of secants.                *)
(* ------------------------------------------------------------------------- *)

let CONVEX_ON_LEFT_SECANT_MUL,CONVEX_ON_RIGHT_SECANT_MUL = (CONJ_PAIR o prove)
 (`(!f s:real^N->bool.
        f convex_on s <=>
          !a b x. a IN s /\ b IN s /\ x IN segment[a,b]
                  ==> (f x - f a) * norm(b - a) <= (f b - f a) * norm(x - a)) /\
   (!f s:real^N->bool.
        f convex_on s <=>
          !a b x. a IN s /\ b IN s /\ x IN segment[a,b]
                  ==> (f b - f a) * norm(b - x) <= (f b - f x) * norm(b - a))`,
  CONJ_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[convex_on] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `a:real^N` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `b:real^N` THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `(a:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(b:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_SEGMENT; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `u:real` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[TAUT `a /\ x = y <=> x = y /\ a`;
              TAUT `a /\ x = y /\ b <=> x = y /\ a /\ b`] THEN
  REWRITE_TAC[REAL_ARITH `v + u = &1 <=> v = &1 - u`] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; IMP_CONJ] THEN
  REWRITE_TAC[REAL_SUB_LE] THEN
  ASM_CASES_TAC `&0 <= u` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `u <= &1` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_ARITH `((&1 - u) % a + u % b) - a:real^N = u % (b - a)`;
   VECTOR_ARITH `b - ((&1 - u) % a + u % b):real^N = (&1 - u) % (b - a)`] THEN
  REWRITE_TAC[NORM_MUL; REAL_MUL_ASSOC] THEN
  (ASM_CASES_TAC `b:real^N = a` THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_REFL; REAL_SUB_REFL;
                    VECTOR_ARITH `(&1 - u) % a + u % a:real^N = a`] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC[REAL_ARITH
     `&0 <= u /\ u <= &1 ==> abs u = u /\ abs(&1 - u) = &1 - u`] THEN
    REAL_ARITH_TAC]));;

let CONVEX_ON_LEFT_SECANT,CONVEX_ON_RIGHT_SECANT = (CONJ_PAIR o prove)
 (`(!f s:real^N->bool.
      f convex_on s <=>
        !a b x. a IN s /\ b IN s /\ x IN segment(a,b)
                ==> (f x - f a) / norm(x - a) <= (f b - f a) / norm(b - a)) /\
   (!f s:real^N->bool.
      f convex_on s <=>
        !a b x. a IN s /\ b IN s /\ x IN segment(a,b)
                ==> (f b - f a) / norm(b - a) <= (f b - f x) / norm(b - x))`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[CONVEX_ON_LEFT_SECANT_MUL];
    REWRITE_TAC[CONVEX_ON_RIGHT_SECANT_MUL]] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `a:real^N` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `b:real^N` THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `(a:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(b:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; NOT_IN_EMPTY; REAL_SUB_REFL; VECTOR_SUB_REFL;
                  NORM_0; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
  MAP_EVERY ASM_CASES_TAC [`x:real^N = a`; `x:real^N = b`] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_SUB_REFL; VECTOR_SUB_REFL; NORM_0;
                  REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; GSYM REAL_LE_LDIV_EQ; NORM_POS_LT;
               VECTOR_SUB_EQ] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Starlike sets and more stuff about line segments.                         *)
(* ------------------------------------------------------------------------- *)

let starlike = new_definition
 `starlike s <=> ?a. a IN s /\ !x. x IN s ==> segment[a,x] SUBSET s`;;

let CONVEX_IMP_STARLIKE = prove
 (`!s. convex s /\ ~(s = {}) ==> starlike s`,
  REWRITE_TAC[CONVEX_CONTAINS_SEGMENT; starlike; GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[]);;

let SEGMENT_CONVEX_HULL = prove
 (`!a b. segment[a,b] = convex hull {a,b}`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CONVEX_HULL_INSERT; CONVEX_HULL_SING; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[IN_SING; RIGHT_EXISTS_AND_THM; UNWIND_THM2] THEN
  REWRITE_TAC[segment; EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[REAL_ARITH `u + v = &1 <=> u = &1 - v`] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> c /\ a /\ b /\ d`] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  REWRITE_TAC[REAL_LE_SUB_LADD; REAL_ADD_LID] THEN MESON_TAC[]);;

let SEGMENT_FURTHEST_LE = prove
 (`!a b x y:real^N.
        x IN segment[a,b] ==> norm(y - x) <= norm(y - a) \/
                              norm(y - x) <= norm(y - b)`,
  REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`y:real^N`; `{a:real^N,b}`] SIMPLEX_FURTHEST_LE) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_RULES; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
  ASM_MESON_TAC[NORM_SUB]);;

let SEGMENT_BOUND = prove
 (`!a b x:real^N.
        x IN segment[a,b] ==> norm(x - a) <= norm(b - a) /\
                              norm(x - b) <= norm(b - a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real^N`; `b:real^N`; `x:real^N`] SEGMENT_FURTHEST_LE) THENL
   [DISCH_THEN(MP_TAC o SPEC `a:real^N`);
    DISCH_THEN(MP_TAC o SPEC `b:real^N`)] THEN
  REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
  ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS; NORM_SUB]);;

let BETWEEN_IN_CONVEX_HULL = prove
 (`!x a b:real^N. between x (a,b) <=> x IN convex hull {a,b}`,
  REWRITE_TAC[BETWEEN_IN_SEGMENT; SEGMENT_CONVEX_HULL]);;

let STARLIKE_LINEAR_IMAGE = prove
 (`!f s. starlike s /\ linear f ==> starlike(IMAGE f s)`,
  REWRITE_TAC[starlike; FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
  SIMP_TAC[CLOSED_SEGMENT_LINEAR_IMAGE] THEN SET_TAC[]);;

let STARLIKE_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (starlike (IMAGE f s) <=> starlike s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE STARLIKE_LINEAR_IMAGE));;

add_linear_invariants [STARLIKE_LINEAR_IMAGE_EQ];;

let STARLIKE_TRANSLATION_EQ = prove
 (`!a s. starlike (IMAGE (\x. a + x) s) <=> starlike s`,
  REWRITE_TAC[starlike] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [STARLIKE_TRANSLATION_EQ];;

let BETWEEN_LINEAR_IMAGE_EQ = prove
 (`!f x y z. linear f /\ (!x y. f x = f y ==> x = y)
             ==> (between (f x) (f y,f z) <=> between x (y,z))`,
  SIMP_TAC[BETWEEN_IN_SEGMENT; CLOSED_SEGMENT_LINEAR_IMAGE] THEN SET_TAC[]);;

add_linear_invariants [BETWEEN_LINEAR_IMAGE_EQ];;

let BETWEEN_TRANSLATION = prove
 (`!a x y. between (a + x) (a + y,a + z) <=> between x (y,z)`,
  REWRITE_TAC[between] THEN NORM_ARITH_TAC);;

add_translation_invariants [STARLIKE_TRANSLATION_EQ];;

let STARLIKE_CLOSURE = prove
 (`!s:real^N->bool. starlike s ==> starlike(closure s)`,
  GEN_TAC THEN REWRITE_TAC[starlike; SUBSET; segment; FORALL_IN_GSPEC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[SUBSET; CLOSURE_APPROACHABLE] THEN
  DISCH_TAC THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(&1 - u) % a + u % y:real^N` THEN
  ASM_SIMP_TAC[dist; NORM_MUL; VECTOR_ARITH
   `(v % a + u % y) - (v % a + u % z):real^N = u % (y - z)`] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        REAL_LET_TRANS)) THEN
  REWRITE_TAC[dist; REAL_ARITH `u * n <= n <=> &0 <= n * (&1 - u)`] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  ASM_REAL_ARITH_TAC);;

let STARLIKE_UNIV = prove
 (`starlike(:real^N)`,
  MESON_TAC[CONVEX_IMP_STARLIKE; CONVEX_UNIV;
            BOUNDED_EMPTY; NOT_BOUNDED_UNIV]);;

let STARLIKE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        starlike s /\ starlike t ==> starlike(s PCROSS t)`,
  SIMP_TAC[starlike; EXISTS_IN_PCROSS; SUBSET; IN_SEGMENT] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[FORALL_IN_PCROSS; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; IMP_IMP] THEN
  REWRITE_TAC[GSYM PASTECART_CMUL; PASTECART_ADD] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS] THEN MESON_TAC[]);;

let STARLIKE_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        starlike(s PCROSS t) <=> starlike s /\ starlike t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THENL
   [ASM_REWRITE_TAC[PCROSS_EMPTY] THEN MESON_TAC[starlike; NOT_IN_EMPTY];
    ALL_TAC] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[PCROSS_EMPTY] THEN MESON_TAC[starlike; NOT_IN_EMPTY];
    ALL_TAC] THEN
  EQ_TAC THEN REWRITE_TAC[STARLIKE_PCROSS] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
     `(s:real^M->bool) PCROSS (t:real^N->bool)`] STARLIKE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART];
    MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
     `(s:real^M->bool) PCROSS (t:real^N->bool)`] STARLIKE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

let BETWEEN_DIST_LT = prove
 (`!r a b c:real^N.
        dist(c,a) < r /\ dist(c,b) < r /\ between x (a,b) ==> dist(c,x) < r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex hull {a,b} SUBSET ball(c:real^N,r)` MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_REWRITE_TAC[CONVEX_BALL; INSERT_SUBSET; EMPTY_SUBSET; IN_BALL];
    ASM_SIMP_TAC[SUBSET; GSYM BETWEEN_IN_CONVEX_HULL; IN_BALL]]);;

let BETWEEN_DIST_LE = prove
 (`!r a b c:real^N.
      dist(c,a) <= r /\ dist(c,b) <= r /\ between x (a,b) ==> dist(c,x) <= r`,

  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex hull {a,b} SUBSET cball(c:real^N,r)` MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_REWRITE_TAC[CONVEX_CBALL; INSERT_SUBSET; EMPTY_SUBSET; IN_CBALL];
    ASM_SIMP_TAC[SUBSET; GSYM BETWEEN_IN_CONVEX_HULL; IN_CBALL]]);;

let BETWEEN_NORM_LT = prove
 (`!r a b x:real^N.
        norm a < r /\ norm b < r /\ between x (a,b) ==> norm x < r`,
  REWRITE_TAC[GSYM(CONJUNCT2(SPEC_ALL DIST_0)); BETWEEN_DIST_LT]);;

let BETWEEN_NORM_LE = prove
 (`!r a b x:real^N.
        norm a <= r /\ norm b <= r /\ between x (a,b) ==> norm x <= r`,
  REWRITE_TAC[GSYM(CONJUNCT2(SPEC_ALL DIST_0)); BETWEEN_DIST_LE]);;

let UNION_SEGMENT = prove
 (`!a b c:real^N.
        b IN segment[a,c]
        ==> segment[a,b] UNION segment[b,c] = segment[a,c]`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c:real^N = a` THENL
   [ASM_SIMP_TAC[SEGMENT_REFL; IN_SING; UNION_IDEMPOT];
    ONCE_REWRITE_TAC[UNION_COMM] THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP CONVEX_HULL_EXCHANGE_UNION) THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    REWRITE_TAC[IMAGE_CLAUSES; UNIONS_2] THEN
    BINOP_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Shrinking towards the interior of a convex set.                           *)
(* ------------------------------------------------------------------------- *)

let IN_INTERIOR_CONVEX_SHRINK = prove
 (`!s e x c:real^N.
     convex s /\ c IN interior s /\
     x IN s /\ &0 < e /\ e <= &1
     ==> x - e % (x - c) IN interior s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
  REWRITE_TAC[IN_INTERIOR; SUBSET; IN_BALL; dist] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e * d:real` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  X_GEN_TAC `y':real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(&1 / e) % y' - ((&1 - e) / e) % x:real^N`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `norm (x - e % (x - c) - y':real^N) < e * d` THEN
    SUBGOAL_THEN `x - e % (x - c) - y':real^N =
                  e % (c - (&1 / e % y' - (&1 - e) / e % x))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC;
                   REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC;
      ASM_SIMP_TAC[NORM_MUL; REAL_LT_LMUL_EQ; real_abs; REAL_LT_IMP_LE]];
    DISCH_TAC THEN
    SUBGOAL_THEN `y' = (&1 - (&1 - e)) % (&1 / e % y' - (&1 - e) / e % x) +
                       (&1 - e) % x:real^N`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `&1 - (&1 - e) = e`; VECTOR_SUB_LDISTRIB;
                   VECTOR_MUL_ASSOC; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
      VECTOR_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

let IN_INTERIOR_CLOSURE_CONVEX_SHRINK = prove
 (`!s e x c:real^N.
     convex s /\ c IN interior s /\
     x IN closure s /\ &0 < e /\ e <= &1
     ==> x - e % (x - c) IN interior s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?y:real^N. y IN s /\ norm(y - x) * (&1 - e) < e * d`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(x:real^N) IN s` THENL
     [EXISTS_TAC `x:real^N` THEN
      ASM_SIMP_TAC[REAL_LT_MUL; VECTOR_SUB_REFL; NORM_0; REAL_MUL_LZERO];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [closure]) THEN
    ASM_REWRITE_TAC[IN_UNION; IN_ELIM_THM; LIMPT_APPROACHABLE; dist] THEN
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
     `e <= &1 ==> e = &1 \/ e < &1`)) THEN
    ASM_SIMP_TAC[REAL_SUB_REFL; GSYM REAL_LT_RDIV_EQ; REAL_SUB_LT] THENL
     [DISCH_THEN(MP_TAC o SPEC `&1`) THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_01];
      DISCH_THEN(MP_TAC o SPEC `(e * d) / (&1 - e)`)] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_SUB_LT; REAL_MUL_LZERO; REAL_LT_MUL;
                 REAL_MUL_LID] THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `z:real^N = c + ((&1 - e) / e) % (x - y)` THEN
  SUBGOAL_THEN `x - e % (x - c):real^N = y - e % (y - z)` SUBST1_TAC THENL
   [EXPAND_TAC "z" THEN
    REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_ADD_LDISTRIB] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC IN_INTERIOR_CONVEX_SHRINK THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
     MATCH_MP SUBSET_INTERIOR) THEN
  SIMP_TAC[INTERIOR_OPEN; OPEN_BALL] THEN
  REWRITE_TAC[IN_BALL; dist] THEN EXPAND_TAC "z" THEN
  REWRITE_TAC[NORM_ARITH `norm(c - (c + x)) = norm(x)`] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_DIV] THEN
  ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN
  ASM_MESON_TAC[REAL_MUL_SYM; NORM_SUB]);;

let IN_INTERIOR_CLOSURE_CONVEX_SEGMENT = prove
 (`!s a b:real^N.
        convex s /\ a IN interior s /\ b IN closure s
        ==> segment(a,b) SUBSET interior s`,
  REWRITE_TAC[SUBSET; IN_SEGMENT] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
   `(&1 - u) % a + u % b:real^N = b - (&1 - u) % (b - a)`] THEN
  MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Relative interior of a set.                                               *)
(* ------------------------------------------------------------------------- *)

let relative_interior = new_definition
 `relative_interior s =
   {x | ?t. open_in (subtopology euclidean (affine hull s)) t /\
            x IN t /\ t SUBSET s}`;;

let relative_frontier = new_definition
 `relative_frontier s = closure s DIFF relative_interior s`;;

let RELATIVE_INTERIOR = prove
 (`!s. relative_interior s =
          {x | x IN s /\
               ?t. open t /\ x IN t /\ t INTER (affine hull s) SUBSET s}`,
  REWRITE_TAC[EXTENSION; relative_interior; IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> b /\ a /\ c /\ d`] THEN
  REWRITE_TAC[UNWIND_THM2; SUBSET; IN_INTER; RIGHT_AND_EXISTS_THM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN MESON_TAC[HULL_INC]);;

let RELATIVE_INTERIOR_EQ = prove
 (`!s. relative_interior s = s <=>
       open_in(subtopology euclidean (affine hull s)) s`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; relative_interior; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [OPEN_IN_SUBOPEN] THEN MESON_TAC[SUBSET]);;

let RELATIVE_INTERIOR_OPEN_IN = prove
 (`!s. open_in(subtopology euclidean (affine hull s)) s
       ==> relative_interior s = s`,
  REWRITE_TAC[RELATIVE_INTERIOR_EQ]);;

let RELATIVE_INTERIOR_EMPTY = prove
 (`relative_interior {} = {}`,
  SIMP_TAC[RELATIVE_INTERIOR_OPEN_IN; OPEN_IN_EMPTY]);;

let RELATIVE_FRONTIER_EMPTY = prove
 (`relative_frontier {} = {}`,
  REWRITE_TAC[relative_frontier; CLOSURE_EMPTY; EMPTY_DIFF]);;

let RELATIVE_INTERIOR_AFFINE = prove
 (`!s:real^N->bool. affine s ==> relative_interior s = s`,
  SIMP_TAC[RELATIVE_INTERIOR_EQ; OPEN_IN_SUBTOPOLOGY_REFL; HULL_P] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN; SUBSET_UNIV]);;

let RELATIVE_INTERIOR_UNIV = prove
 (`!s. relative_interior(affine hull s) = affine hull s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RELATIVE_INTERIOR_OPEN_IN THEN
  REWRITE_TAC[HULL_HULL; OPEN_IN_SUBTOPOLOGY_REFL] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN; SUBSET_UNIV]);;

let OPEN_IN_RELATIVE_INTERIOR = prove
 (`!s. open_in (subtopology euclidean (affine hull s))
               (relative_interior s)`,
  GEN_TAC THEN REWRITE_TAC[relative_interior] THEN
  GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let RELATIVE_INTERIOR_SUBSET = prove
 (`!s. (relative_interior s) SUBSET s`,
  REWRITE_TAC[SUBSET; relative_interior; IN_ELIM_THM] THEN MESON_TAC[]);;

let OPEN_IN_SET_RELATIVE_INTERIOR = prove
 (`!s:real^N->bool. open_in (subtopology euclidean s) (relative_interior s)`,
  GEN_TAC THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
  EXISTS_TAC `affine hull s:real^N->bool` THEN
  REWRITE_TAC[OPEN_IN_RELATIVE_INTERIOR; RELATIVE_INTERIOR_SUBSET;
              HULL_SUBSET]);;

let SUBSET_RELATIVE_INTERIOR = prove
 (`!s t. s SUBSET t /\ affine hull s = affine hull t
         ==> (relative_interior s) SUBSET (relative_interior t)`,
  REWRITE_TAC[relative_interior; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let RELATIVE_INTERIOR_MAXIMAL = prove
 (`!s t. t SUBSET s /\
         open_in(subtopology euclidean (affine hull s)) t
         ==> t SUBSET (relative_interior s)`,
  REWRITE_TAC[relative_interior; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let RELATIVE_INTERIOR_UNIQUE = prove
 (`!s t. t SUBSET s /\
         open_in(subtopology euclidean (affine hull s)) t /\
         (!t'. t' SUBSET s /\
               open_in(subtopology euclidean (affine hull s)) t'
               ==> t' SUBSET t)
         ==> (relative_interior s = t)`,
  MESON_TAC[SUBSET_ANTISYM; RELATIVE_INTERIOR_MAXIMAL; RELATIVE_INTERIOR_SUBSET;
            OPEN_IN_RELATIVE_INTERIOR]);;

let IN_RELATIVE_INTERIOR = prove
 (`!x:real^N s.
        x IN relative_interior s <=>
        x IN s /\ ?e. &0 < e /\ (ball(x,e) INTER (affine hull s)) SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[relative_interior; IN_ELIM_THM] THEN
  REWRITE_TAC[OPEN_IN_OPEN; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> b /\ a /\ c /\ d`] THEN
  REWRITE_TAC[UNWIND_THM2; SUBSET; IN_INTER] THEN EQ_TAC THENL
   [ASM_MESON_TAC[SUBSET; OPEN_CONTAINS_BALL];
    STRIP_TAC THEN EXISTS_TAC `ball(x:real^N,e)` THEN
    ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL; HULL_INC]]);;

let IN_RELATIVE_INTERIOR_CBALL = prove
 (`!x:real^N s.
        x IN relative_interior s <=>
        x IN s /\ ?e. &0 < e /\ (cball(x,e) INTER affine hull s) SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_RELATIVE_INTERIOR] THEN
  AP_TERM_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball(x:real^N,e) INTER affine hull s` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_CBALL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`];
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(x:real^N,e) INTER affine hull s` THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[SUBSET; IN_INTER; IN_BALL; IN_CBALL; REAL_LT_IMP_LE]]);;

let OPEN_IN_SUBSET_RELATIVE_INTERIOR = prove
 (`!s t. open_in(subtopology euclidean (affine hull t)) s
         ==> (s SUBSET relative_interior t <=> s SUBSET t)`,
  MESON_TAC[RELATIVE_INTERIOR_MAXIMAL; RELATIVE_INTERIOR_SUBSET;
            SUBSET_TRANS]);;

let RELATIVE_INTERIOR_TRANSLATION = prove
 (`!a:real^N s.
        relative_interior (IMAGE (\x. a + x) s) =
        IMAGE (\x. a + x) (relative_interior s)`,
  REWRITE_TAC[relative_interior; OPEN_IN_OPEN] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [RELATIVE_INTERIOR_TRANSLATION];;

let RELATIVE_FRONTIER_TRANSLATION = prove
 (`!a:real^N s.
        relative_frontier (IMAGE (\x. a + x) s) =
        IMAGE (\x. a + x) (relative_frontier s)`,
  REWRITE_TAC[relative_frontier] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [RELATIVE_FRONTIER_TRANSLATION];;

let RELATIVE_INTERIOR_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> relative_interior(IMAGE f s) = IMAGE f (relative_interior s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[relative_interior; AFFINE_HULL_LINEAR_IMAGE] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> c /\ a /\ b`] THEN
  REWRITE_TAC[EXISTS_SUBSET_IMAGE] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_INJECTIVE_LINEAR_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

add_linear_invariants [RELATIVE_INTERIOR_INJECTIVE_LINEAR_IMAGE];;

let RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> relative_frontier(IMAGE f s) = IMAGE f (relative_frontier s)`,
  REWRITE_TAC[relative_frontier] THEN GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE];;

let RELATIVE_INTERIOR_EQ_EMPTY = prove
 (`!s:real^N->bool.
        convex s ==> (relative_interior s = {} <=> s = {})`,
  SUBGOAL_THEN
   `!s:real^N->bool.
        vec 0 IN s /\ convex s ==> ~(relative_interior s = {})`
  ASSUME_TAC THENL
   [ALL_TAC;
    GEN_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_EMPTY] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (\x:real^N. --a + x) s`) THEN
    REWRITE_TAC[CONVEX_TRANSLATION_EQ; RELATIVE_INTERIOR_TRANSLATION] THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `a:real^N` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC] THEN
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_RELATIVE_INTERIOR] THEN
  ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC] THEN
  X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC
   (ISPEC `s:real^N->bool` BASIS_EXISTS) THEN
  SUBGOAL_THEN `span(s:real^N->bool) = span b` SUBST_ALL_TAC THENL
   [ASM_SIMP_TAC[SPAN_EQ] THEN ASM_MESON_TAC[SPAN_INC; SUBSET_TRANS];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ABBREV_TAC `n = dim(s:real^N->bool)` THEN
  SUBGOAL_THEN
   `!c. (!v. v IN b ==> &0 <= c(v)) /\ sum b c <= &1
        ==> vsum b (\v:real^N. c(v) % v) IN s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN SUBGOAL_THEN
     `vsum (vec 0 INSERT b :real^N->bool)
           (\v. (if v = vec 0 then &1 - sum b c else c v) % v) IN s`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_EXPLICIT]) THEN
      ASM_SIMP_TAC[INSERT_SUBSET; FINITE_INSERT; SUM_CLAUSES;
                   INDEPENDENT_NONZERO; IN_INSERT] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[REAL_SUB_LE]; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `&1 - x + y = &1 <=> x = y`] THEN
      MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[INDEPENDENT_NONZERO];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[VSUM_CLAUSES; INDEPENDENT_NONZERO] THEN
      REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
      MATCH_MP_TAC VSUM_EQ THEN ASM_MESON_TAC[INDEPENDENT_NONZERO]];
    ALL_TAC] THEN
  ABBREV_TAC `a:real^N = vsum b (\v. inv(&2 * &n + &1) % v)` THEN
  EXISTS_TAC `a:real^N` THEN CONJ_TAC THENL
   [EXPAND_TAC "a" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SUM_CONST; REAL_LE_INV_EQ; REAL_ARITH `&0 < &2 * &n + &1`;
                 GSYM real_div; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `inv(&2 * &n + &1)`]
        BASIS_COORDINATES_CONTINUOUS) THEN
  ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUBSET; IN_INTER; IMP_CONJ_ALT] THEN
  ASM_SIMP_TAC[SPAN_FINITE; LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN
  GEN_TAC THEN X_GEN_TAC `u:real^N->real` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_BALL; dist] THEN
  EXPAND_TAC "a" THEN ASM_SIMP_TAC[GSYM VSUM_SUB] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
  REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[REAL_ARITH `abs(x - y) < x <=> &0 < y /\ abs(y) < &2 * x`] THEN
  SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(b:real^N->bool)) * &2 * inv(&2 * &n + &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_BOUND THEN
    ASM_SIMP_TAC[REAL_ARITH `abs x < a ==> x <= a`];
    ASM_REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &2 * &n + &1`] THEN
    REAL_ARITH_TAC]);;

let RELATIVE_INTERIOR_INTERIOR = prove
 (`!s. affine hull s = (:real^N)
       ==> relative_interior s = interior s`,
  SIMP_TAC[relative_interior; interior; SUBTOPOLOGY_UNIV; OPEN_IN]);;

let RELATIVE_INTERIOR_OPEN = prove
 (`!s:real^N->bool. open s ==> relative_interior s = s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[RELATIVE_INTERIOR_EMPTY] THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_INTERIOR; AFFINE_HULL_OPEN; INTERIOR_EQ]);;

let RELATIVE_INTERIOR_NONEMPTY_INTERIOR = prove
 (`!s. ~(interior s = {}) ==> relative_interior s = interior s`,
  MESON_TAC[RELATIVE_INTERIOR_INTERIOR; AFFINE_HULL_NONEMPTY_INTERIOR]);;

let RELATIVE_FRONTIER_NONEMPTY_INTERIOR = prove
 (`!s. ~(interior s = {}) ==> relative_frontier s = frontier s`,
  SIMP_TAC[relative_frontier; frontier; RELATIVE_INTERIOR_NONEMPTY_INTERIOR]);;

let RELATIVE_FRONTIER_FRONTIER = prove
 (`!s. affine hull s = (:real^N) ==> relative_frontier s = frontier s`,
  SIMP_TAC[relative_frontier; frontier; RELATIVE_INTERIOR_INTERIOR]);;

let AFFINE_HULL_CONVEX_HULL = prove
 (`!s. affine hull (convex hull s) = affine hull s`,
  GEN_TAC THEN MATCH_MP_TAC HULL_UNIQUE THEN
  REWRITE_TAC[AFFINE_AFFINE_HULL; CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_MESON_TAC[SUBSET_TRANS; HULL_SUBSET]);;

let INTERIOR_SIMPLEX_NONEMPTY = prove
 (`!s:real^N->bool.
        independent s /\ s HAS_SIZE (dimindex(:N))
        ==> ?a. a IN interior(convex hull (vec 0 INSERT s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `convex hull (vec 0 INSERT s):real^N->bool`
    RELATIVE_INTERIOR_EQ_EMPTY) THEN
  ASM_SIMP_TAC[AFFINE_HULL_CONVEX_HULL] THEN
  REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; CONVEX_CONVEX_HULL; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[MEMBER_NOT_EMPTY] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; IN_INSERT; HULL_INC] THEN
  MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ s = UNIV ==> t = UNIV`) THEN
  EXISTS_TAC `span s:real^N->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_MONO THEN MATCH_MP_TAC(SET_RULE
     `(a INSERT s) SUBSET P hull (a INSERT s)
      ==> s SUBSET P hull (a INSERT s)`) THEN REWRITE_TAC[HULL_SUBSET];
    MATCH_MP_TAC(SET_RULE `UNIV SUBSET s ==> s = UNIV`) THEN
    MATCH_MP_TAC CARD_GE_DIM_INDEPENDENT THEN
    ASM_REWRITE_TAC[DIM_UNIV; SUBSET_UNIV] THEN
    ASM_MESON_TAC[LE_REFL;HAS_SIZE]]);;

let INTERIOR_SUBSET_RELATIVE_INTERIOR = prove
 (`!s. interior s SUBSET relative_interior s`,
  REWRITE_TAC[SUBSET; IN_INTERIOR; IN_RELATIVE_INTERIOR; IN_INTER] THEN
  MESON_TAC[CENTRE_IN_BALL]);;

let CONVEX_RELATIVE_INTERIOR = prove
 (`!s:real^N->bool. convex s ==> convex(relative_interior s)`,
  REWRITE_TAC[CONVEX_ALT; IN_RELATIVE_INTERIOR; IN_INTER;
              SUBSET; IN_BALL; dist] THEN
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT `(a /\ b) /\ (c /\ d) /\ e ==> f <=>
                    a /\ c /\ e ==> b /\ d ==> f`] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(MESON[] `(!d e. P d /\ Q e ==> R(min d e))
                        ==> (?e. P e) /\ (?e. Q e) ==> (?e. R e)`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  SUBST1_TAC(VECTOR_ARITH `z:real^N =
   (&1 - u) % (z - u % (y - x)) + u % (z + (&1 - u) % (y - x))`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN MATCH_MP_TAC MONO_AND THEN
  CONJ_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  (CONJ_TAC THENL
    [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
      `norm x < e ==> norm x = y ==> y < e`)) THEN
     AP_TERM_TAC THEN VECTOR_ARITH_TAC;
     REWRITE_TAC[VECTOR_ARITH `a - b % c:real^N = a + --b % c`] THEN
     MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
     ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC]]));;

let IN_RELATIVE_INTERIOR_CONVEX_SHRINK = prove
 (`!s e x c:real^N.
     convex s /\ c IN relative_interior s /\
     x IN s /\ &0 < e /\ e <= &1
     ==> x - e % (x - c) IN relative_interior s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR]) THEN
  REWRITE_TAC[IN_RELATIVE_INTERIOR; SUBSET; IN_INTER; IN_BALL; dist] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH
     `x - e % (x - c):real^N = (&1 - e) % x + e % c`] THEN
    FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `e * d:real` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  X_GEN_TAC `y':real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(&1 / e) % y' - ((&1 - e) / e) % x:real^N`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `norm (x - e % (x - c) - y':real^N) < e * d` THEN
      SUBGOAL_THEN `x - e % (x - c) - y':real^N =
                    e % (c - (&1 / e % y' - (&1 - e) / e % x))`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC;
                     REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC;
        ASM_SIMP_TAC[NORM_MUL; REAL_LT_LMUL_EQ; real_abs; REAL_LT_IMP_LE]];
      REWRITE_TAC[real_div; REAL_SUB_RDISTRIB] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[VECTOR_ARITH `a % y - (b - c) % x:real^N =
                                (c - b) % x + a % y`] THEN
      MATCH_MP_TAC(REWRITE_RULE[AFFINE_ALT] AFFINE_AFFINE_HULL) THEN
      ASM_SIMP_TAC[HULL_INC]];
    DISCH_TAC THEN
    SUBGOAL_THEN `y' = (&1 - (&1 - e)) % (&1 / e % y' - (&1 - e) / e % x) +
                       (&1 - e) % x:real^N`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `&1 - (&1 - e) = e`; VECTOR_SUB_LDISTRIB;
                   VECTOR_MUL_ASSOC; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
      VECTOR_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

let IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK = prove
 (`!s e x c:real^N.
     convex s /\ c IN relative_interior s /\
     x IN closure s /\ &0 < e /\ e <= &1
     ==> x - e % (x - c) IN relative_interior s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?y:real^N. y IN s /\ norm(y - x) * (&1 - e) < e * d`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(x:real^N) IN s` THENL
     [EXISTS_TAC `x:real^N` THEN
      ASM_SIMP_TAC[REAL_LT_MUL; VECTOR_SUB_REFL; NORM_0; REAL_MUL_LZERO];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [closure]) THEN
    ASM_REWRITE_TAC[IN_UNION; IN_ELIM_THM; LIMPT_APPROACHABLE; dist] THEN
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
     `e <= &1 ==> e = &1 \/ e < &1`)) THEN
    ASM_SIMP_TAC[REAL_SUB_REFL; GSYM REAL_LT_RDIV_EQ; REAL_SUB_LT] THENL
     [DISCH_THEN(MP_TAC o SPEC `&1`) THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_01];
      DISCH_THEN(MP_TAC o SPEC `(e * d) / (&1 - e)`)] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_SUB_LT; REAL_MUL_LZERO; REAL_LT_MUL;
                 REAL_MUL_LID] THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `z:real^N = c + ((&1 - e) / e) % (x - y)` THEN
  SUBGOAL_THEN `x - e % (x - c):real^N = y - e % (y - z)` SUBST1_TAC THENL
   [EXPAND_TAC "z" THEN
    REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_ADD_LDISTRIB] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC IN_RELATIVE_INTERIOR_CONVEX_SHRINK THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `dist(c:real^N,z) < d` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    REWRITE_TAC[NORM_ARITH `dist(c:real^N,c + x) = norm x`] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_DIV] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    REWRITE_TAC[REAL_ARITH `a / b * c:real = (c * a) / b`] THEN
    ASM_SIMP_TAC[real_abs; REAL_SUB_LE; REAL_LT_IMP_LE; REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN affine hull s` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC] THEN
    MATCH_MP_TAC(SET_RULE `!t. x IN t /\ t = s ==> x IN s`) THEN
    EXISTS_TAC `closure(affine hull s):real^N->bool` THEN
    SIMP_TAC[CLOSURE_EQ; CLOSED_AFFINE_HULL] THEN
    ASM_MESON_TAC[SUBSET_CLOSURE; HULL_INC; SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_RELATIVE_INTERIOR] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[IN_BALL; IN_INTER; SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `d - dist(c:real^N,z)` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS)) THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `dist(c:real^N,z) < d` THEN REWRITE_TAC[IN_BALL] THEN
  NORM_ARITH_TAC);;

let IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT = prove
 (`!s a b:real^N.
        convex s /\ a IN relative_interior s /\ b IN closure s
        ==> segment(a,b) SUBSET relative_interior s`,
  REWRITE_TAC[SUBSET; IN_SEGMENT] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
   `(&1 - u) % a + u % b:real^N = b - (&1 - u) % (b - a)`] THEN
  MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let INTER_CONVEX_HULL_INSERT_RELATIVE_EXTERIOR = prove
 (`!c t s z:real^N.
        convex c /\ t SUBSET c /\ z IN relative_interior c /\
        DISJOINT s (relative_interior c)
        ==> s INTER (convex hull (z INSERT t)) =
            s INTER (convex hull t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  SIMP_TAC[HULL_MONO; SET_RULE `s SUBSET a INSERT s`;
           SET_RULE `t SUBSET u ==> s INTER t SUBSET s INTER u`] THEN
  REWRITE_TAC[CONVEX_HULL_INSERT_SEGMENTS; SUBSET] THEN
  X_GEN_TAC `x:real^N` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN
  ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:real^N->bool`; `z:real^N`; `y:real^N`]
        IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    ASM_MESON_TAC[HULL_MINIMAL; SUBSET];
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ONCE_REWRITE_TAC[segment] THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN ASM SET_TAC[]]);;

let CONVEX_OPEN_SEGMENT_CASES = prove
 (`!s a b:real^N.
        convex s /\ a IN closure s /\ b IN closure s
        ==> segment(a,b) SUBSET relative_frontier s \/
            segment(a,b) SUBSET relative_interior s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[relative_frontier] THEN
  MATCH_MP_TAC(SET_RULE
   `s SUBSET c /\ (!a. a IN i /\ a IN s ==> s SUBSET i)
    ==> s SUBSET c DIFF i \/ s SUBSET i`) THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[CONVEX_CONTAINS_OPEN_SEGMENT; CONVEX_CLOSURE];
    X_GEN_TAC `c:real^N` THEN ONCE_REWRITE_TAC[segment]] THEN
  REWRITE_TAC[IN_DIFF; IN_INSERT; DE_MORGAN_THM; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP UNION_SEGMENT) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c:real^N`]
        IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `b:real^N` th) THEN MP_TAC(SPEC `a:real^N` th)) THEN
  ASM_REWRITE_TAC[SEGMENT_SYM; CONJUNCT2 segment] THEN ASM SET_TAC[]);;

let RELATIVE_INTERIOR_SING = prove
 (`!a. relative_interior {a} = {a}`,
  GEN_TAC THEN MATCH_MP_TAC(SET_RULE
   `s SUBSET {a} /\ ~(s = {}) ==> s = {a}`) THEN
  SIMP_TAC[RELATIVE_INTERIOR_SUBSET; RELATIVE_INTERIOR_EQ_EMPTY;
           CONVEX_SING] THEN
  SET_TAC[]);;

let RELATIVE_FRONTIER_SING = prove
 (`!a:real^N. relative_frontier {a} = {}`,
  REWRITE_TAC[relative_frontier; RELATIVE_INTERIOR_SING; CLOSURE_SING] THEN
  SET_TAC[]);;

let RELATIVE_INTERIOR_CBALL = prove
 (`!a r. relative_interior(cball(a,r)) = if r = &0 then {a} else ball(a,r)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NE; CBALL_EMPTY; BALL_EMPTY;
               RELATIVE_INTERIOR_EMPTY; REAL_LT_IMP_LE] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[CBALL_SING; RELATIVE_INTERIOR_SING] THEN
  REWRITE_TAC[GSYM INTERIOR_CBALL] THEN
  MATCH_MP_TAC RELATIVE_INTERIOR_NONEMPTY_INTERIOR THEN
  ASM_REWRITE_TAC[INTERIOR_CBALL; BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC);;

let RELATIVE_INTERIOR_BALL = prove
 (`!a r. relative_interior(ball(a,r)) = ball(a,r)`,
  SIMP_TAC[RELATIVE_INTERIOR_OPEN; OPEN_BALL]);;

let RELATIVE_FRONTIER_CBALL = prove
 (`!a:real^N r. relative_frontier(cball(a,r)) =
                if r = &0 then {} else sphere(a,r)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CBALL_SING; RELATIVE_FRONTIER_SING] THEN
  ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[CBALL_EMPTY; SPHERE_EMPTY; RELATIVE_FRONTIER_EMPTY] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; INTERIOR_CBALL;
               BALL_EQ_EMPTY; GSYM REAL_NOT_LT; FRONTIER_CBALL]);;

let RELATIVE_FRONTIER_BALL = prove
 (`!a:real^N r. relative_frontier(ball(a,r)) =
                if r = &0 then {} else sphere(a,r)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[BALL_EMPTY; REAL_LE_REFL; RELATIVE_FRONTIER_EMPTY] THEN
  ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[BALL_EMPTY; REAL_LT_IMP_LE; SPHERE_EMPTY;
               RELATIVE_FRONTIER_EMPTY] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; INTERIOR_OPEN; OPEN_BALL;
               BALL_EQ_EMPTY; GSYM REAL_NOT_LT; FRONTIER_BALL]);;

let STARLIKE_CONVEX_TWEAK_BOUNDARY_POINTS = prove
 (`!s t:real^N->bool.
        convex s /\ ~(s = {}) /\
        relative_interior s SUBSET t /\ t SUBSET closure s
        ==> starlike t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(relative_interior s:real^N->bool = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]; REWRITE_TAC[starlike]] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `a:real^N` THEN
  REPEAT STRIP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `a IN s /\ b IN s /\ segment[a,b] DIFF {a,b} SUBSET s
    ==> segment[a:real^N,b] SUBSET s`) THEN
  ASM_REWRITE_TAC[GSYM open_segment] THEN
  ASM_MESON_TAC[IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT; SUBSET]);;

let RELATIVE_INTERIOR_PROLONG = prove
 (`!s x y:real^N.
        x IN relative_interior s /\ y IN s
        ==> ?t. &1 < t /\ (y + t % (x - y)) IN s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_RELATIVE_INTERIOR_CBALL; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real`
  STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `y:real^N = x` THENL
   [ASM_REWRITE_TAC[VECTOR_ARITH `y + t % (x - x):real^N = y`] THEN
    EXISTS_TAC `&2` THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    EXISTS_TAC `&1 + e / norm(x - y:real^N)` THEN
    ASM_SIMP_TAC[REAL_LT_ADDR; REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    REWRITE_TAC[VECTOR_ARITH
     `y + (&1 + e) % (x - y):real^N = x + e % (x - y)`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; IN_INTER; IN_AFFINE_ADD_MUL_DIFF;
                 HULL_INC; IN_CBALL] THEN
    REWRITE_TAC[NORM_ARITH `dist(x:real^N,x + y) = norm y`] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
    ASM_REAL_ARITH_TAC]);;

let RELATIVE_INTERIOR_CONVEX_PROLONG = prove
 (`!s. convex s
       ==> relative_interior s =
           {x:real^N | x IN s /\
                       !y. y IN s ==> ?t. &1 < t /\ (y + t % (x - y)) IN s}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [SIMP_TAC[RELATIVE_INTERIOR_PROLONG] THEN
    MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
    STRIP_TAC THEN
    SUBGOAL_THEN `?y:real^N. y IN relative_interior s` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[MEMBER_NOT_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ANTS_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_CASES_TAC `y:real^N = x` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `y:real^N`; `y + t % (x - y):real^N`]
        IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[SUBSET; CLOSURE_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_SEGMENT; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `y:real^N = y + x <=> x = vec 0`;
      VECTOR_ARITH `(&1 - u) % y + u % (y + t % (x - y)):real^N =
                    y + t % u % (x - y)`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `inv t:real` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_INV_EQ;
      REAL_INV_LT_1; REAL_LT_IMP_NZ; REAL_ARITH `&1 < x ==> &0 < x`] THEN
    VECTOR_ARITH_TAC]);;

let RELATIVE_INTERIOR_EQ_CLOSURE = prove
 (`!s:real^N->bool.
        relative_interior s = closure s <=> affine s`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[RELATIVE_INTERIOR_EMPTY; CLOSURE_EMPTY; AFFINE_EMPTY] THEN
  EQ_TAC THEN
  SIMP_TAC[RELATIVE_INTERIOR_AFFINE; CLOSURE_CLOSED; CLOSED_AFFINE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `relative_interior s = closure s
    ==> relative_interior s SUBSET s /\ s SUBSET closure s
        ==> relative_interior s = s /\ closure s = s`)) THEN
  REWRITE_TAC[RELATIVE_INTERIOR_SUBSET; CLOSURE_SUBSET] THEN
  REWRITE_TAC[RELATIVE_INTERIOR_EQ; CLOSURE_EQ; GSYM AFFINE_HULL_EQ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `~(s = {}) ==> s = {} \/ s = a ==> a = s`)) THEN
  MP_TAC(ISPEC `affine hull s:real^N->bool` CONNECTED_CLOPEN) THEN
  SIMP_TAC[AFFINE_IMP_CONVEX; CONVEX_CONNECTED; AFFINE_AFFINE_HULL] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[HULL_SUBSET]);;

let RAY_TO_RELATIVE_FRONTIER = prove
 (`!s a l:real^N.
        bounded s /\ a IN relative_interior s /\
        (a + l) IN affine hull s /\ ~(l = vec 0)
        ==> ?d. &0 < d /\
                (a + d % l) IN relative_frontier s /\
                !e. &0 <= e /\ e < d ==> (a + e % l) IN relative_interior s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[relative_frontier] THEN
  MP_TAC(ISPEC
   `{d | &0 < d /\ ~((a + d % l:real^N) IN relative_interior(s))}` INF) THEN
  ABBREV_TAC
   `d = inf {d | &0 < d /\ ~((a + d % l:real^N) IN relative_interior(s))}` THEN
  SUBGOAL_THEN
   `?e. &0 < e /\ !d. &0 <= d /\ d < e
                      ==> (a + d % l:real^N) IN relative_interior s`
   (X_CHOOSE_THEN `k:real` (LABEL_TAC "0"))
  THENL
   [MP_TAC(ISPEC `s:real^N->bool` OPEN_IN_RELATIVE_INTERIOR) THEN
    REWRITE_TAC[open_in; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^N` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e / norm(l:real^N)` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT] THEN X_GEN_TAC `x:real` THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC IN_AFFINE_ADD_MUL THEN
      ASM_REWRITE_TAC[AFFINE_AFFINE_HULL] THEN
      ASM_MESON_TAC[SUBSET; HULL_SUBSET; RELATIVE_INTERIOR_SUBSET];
      REWRITE_TAC[NORM_ARITH `dist(a + x:real^N,a) = norm x`] THEN
      ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LT_RDIV_EQ; NORM_POS_LT] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_NOT_LT; REAL_LT_IMP_LE]] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N` o
       MATCH_MP BOUNDED_SUBSET_BALL) THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `B / norm(l:real^N)` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET)) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV
     [GSYM CONTRAPOS_THM]) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[NORM_ARITH `dist(a:real^N,a + x) = norm x`] THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM;
                 REAL_DIV_RMUL; NORM_EQ_0] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "1") (LABEL_TAC "2")) THEN
    EXISTS_TAC `d:real` THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `k:real` THEN
      ASM_MESON_TAC[REAL_NOT_LT; REAL_LT_IMP_LE];
      DISCH_TAC] THEN
    MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_LT] THEN
      ASM_MESON_TAC[VECTOR_ARITH `a + &0 % l:real^N = a`;
                    REAL_NOT_LT; REAL_LT_IMP_LE];
      DISCH_TAC] THEN
    REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
     [REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      EXISTS_TAC `a + (d - min d (x / &2 / norm(l:real^N))) % l` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x /\ &0 < d ==> d - min d x < d`) THEN
        ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; NORM_POS_LT];
        REWRITE_TAC[NORM_ARITH `dist(a + x:real^N,a + y) = norm(x - y)`] THEN
        REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB; NORM_MUL] THEN
        ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; NORM_POS_LT] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 < x /\ x < y /\ &0 < d ==> abs((d - min d x) - d) < y`) THEN
        REWRITE_TAC[REAL_ARITH `x / &2 / y < x / y <=> &0 < x / y`] THEN
        ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; NORM_POS_LT]];
      DISCH_TAC THEN
      MP_TAC(ISPEC `s:real^N->bool` OPEN_IN_RELATIVE_INTERIOR) THEN
      REWRITE_TAC[open_in; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `a + d % l:real^N` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real`
       (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "3"))) THEN
      REMOVE_THEN "2" (MP_TAC o SPEC `d + e / norm(l:real^N)`) THEN
      ASM_SIMP_TAC[NOT_IMP; REAL_ARITH `~(d + l <= d) <=> &0 < l`;
                   REAL_LT_DIV; NORM_POS_LT] THEN
      X_GEN_TAC `x:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
      ASM_CASES_TAC `x < d` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REMOVE_THEN "3" MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC IN_AFFINE_ADD_MUL THEN
        ASM_REWRITE_TAC[AFFINE_AFFINE_HULL] THEN
        ASM_MESON_TAC[SUBSET; HULL_SUBSET; RELATIVE_INTERIOR_SUBSET];
        REWRITE_TAC[NORM_ARITH `dist(a + x:real^N,a + y) = norm(x - y)`] THEN
        REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB; NORM_MUL] THEN
        ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; NORM_POS_LT] THEN
        ASM_REAL_ARITH_TAC]]]);;

let RAY_TO_FRONTIER = prove
 (`!s a l:real^N.
        bounded s /\ a IN interior s /\ ~(l = vec 0)
        ==> ?d. &0 < d /\ (a + d % l) IN frontier s /\
                !e. &0 <= e /\ e < d ==> (a + e % l) IN interior s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier] THEN
  SUBGOAL_THEN `interior s:real^N->bool = relative_interior s` SUBST1_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM relative_frontier] THEN
    MATCH_MP_TAC RAY_TO_RELATIVE_FRONTIER THEN ASM_REWRITE_TAC[]] THEN
  ASM_MESON_TAC[NOT_IN_EMPTY; RELATIVE_INTERIOR_NONEMPTY_INTERIOR; IN_UNIV;
                AFFINE_HULL_NONEMPTY_INTERIOR]);;

let SEGMENT_TO_RELATIVE_FRONTIER = prove
 (`!s x y:real^N.
        convex s /\ bounded s /\ x IN relative_interior s /\ y IN s /\
        ~(x = y /\ s = {x})
        ==> ?z. z IN relative_frontier s /\ y IN segment[x,z] /\
                segment(x,z) SUBSET relative_interior s`,
  SUBGOAL_THEN
   `!s x y:real^N.
        convex s /\ bounded s /\ x IN relative_interior s /\ y IN s /\ ~(x = y)
        ==> ?z. z IN relative_frontier s /\ y IN segment[x,z] /\
                segment(x,z) SUBSET relative_interior s`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN ASM_CASES_TAC `x:real^N = y` THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `~(s = {a}) ==> a IN s ==> ?b. ~(b = a) /\ b IN s`)) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`s:real^N->bool`; `y:real^N`; `w:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC[ENDS_IN_SEGMENT]] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:real^N->bool`; `x:real^N`; `y - x:real^N`]
        RAY_TO_RELATIVE_FRONTIER) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `x + (y - x):real^N = y`; VECTOR_SUB_EQ] THEN
  ASM_SIMP_TAC[HULL_INC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x + d % (y - x):real^N` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[relative_frontier; IN_DIFF]] THEN
  REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `inv(d:real)` THEN
  ASM_SIMP_TAC[VECTOR_ADD_LDISTRIB; REAL_LE_INV_EQ; REAL_LT_IMP_LE;
               VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_INV_LE_1; CONV_TAC VECTOR_ARITH] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`; `y:real^N`]
        IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
  ASM_SIMP_TAC[NOT_IMP; REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN
  REWRITE_TAC[SUBSET; IN_SEGMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `x + d % (y - x):real^N`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_DIFF; relative_frontier]) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `d:real` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC VECTOR_ARITH);;

let RELATIVE_FRONTIER_NOT_SING = prove
 (`!s a:real^N. bounded s ==> ~(relative_frontier s = {a})`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[RELATIVE_FRONTIER_EMPTY; NOT_INSERT_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN
  ASM_CASES_TAC `s = {z:real^N}` THEN
  ASM_REWRITE_TAC[RELATIVE_FRONTIER_SING; NOT_INSERT_EMPTY] THEN
  SUBGOAL_THEN `?w:real^N. w IN s /\ ~(w = z)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; REPEAT STRIP_TAC] THEN
  SUBGOAL_THEN
    `~((w:real^N) IN relative_frontier s /\ z IN relative_frontier s)`
  MP_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`relative_frontier s = {a:real^N}`; `bounded(s:real^N->bool)`;
    `~(w:real^N = z)`; `(z:real^N) IN s`; `(w:real^N) IN s`;
    `~((w:real^N) IN relative_frontier s /\ z IN relative_frontier s)`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[DE_MORGAN_THM] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`z:real^N`; `w:real^N`] THEN
  MATCH_MP_TAC(MESON[]
   `(!w z. Q w z <=> Q z w) /\ (!w z. P z ==> Q w z)
    ==> !w z. P w \/ P z ==> Q w z`) THEN
  CONJ_TAC THENL [MESON_TAC[]; REPEAT GEN_TAC] THEN
  DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
  REWRITE_TAC[relative_frontier; IN_DIFF] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUBSET; CLOSURE_SUBSET]; DISCH_TAC] THEN
  MP_TAC(GEN `d:real`
   (ISPECL [`s:real^N->bool`; `z:real^N`; `d % (w - z):real^N`]
   RAY_TO_RELATIVE_FRONTIER)) THEN
  ASM_SIMP_TAC[VECTOR_SUB_EQ; IN_AFFINE_ADD_MUL_DIFF; AFFINE_AFFINE_HULL;
               HULL_INC; VECTOR_MUL_EQ_0] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `&1` th) THEN MP_TAC(SPEC `--(&1)` th)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (STRIP_ASSUME_TAC o GSYM)) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RCANCEL; VECTOR_MUL_ASSOC; VECTOR_SUB_EQ;
                  VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
  ASM_REAL_ARITH_TAC);;

let RELATIVE_INTERIOR_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        relative_interior(s PCROSS t) =
        relative_interior s PCROSS relative_interior t`,
  REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`s:real^M->bool = {}`; `t:real^N->bool = {}`] THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; RELATIVE_INTERIOR_EMPTY] THEN
  REWRITE_TAC[relative_interior; AFFINE_HULL_PCROSS] THEN
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_ELIM_THM;
              PASTECART_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^N`] THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> r /\ q /\ p`] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^(M,N)finite_sum->bool`
     (CONJUNCTS_THEN ASSUME_TAC)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PASTECART_IN_INTERIOR_SUBTOPOLOGY) THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (funpow 3 rand) SUBSET_PCROSS o snd) THEN
    ASM SET_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `(v:real^M->bool) PCROSS (w:real^N->bool)` THEN
    ASM_SIMP_TAC[PASTECART_IN_PCROSS; SUBSET_PCROSS; OPEN_IN_PCROSS]]);;

let RELATIVE_FRONTIER_EQ_EMPTY = prove
 (`!s:real^N->bool. relative_frontier s = {} <=> affine s`,
  GEN_TAC THEN REWRITE_TAC[relative_frontier] THEN
  REWRITE_TAC[GSYM RELATIVE_INTERIOR_EQ_CLOSURE] THEN
  MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN SET_TAC[]);;

let DIAMETER_BOUNDED_BOUND_LT = prove
 (`!s x y:real^N.
        bounded s /\ x IN relative_interior s /\ y IN closure s /\
        ~(diameter s = &0)
        ==> norm(x - y) < diameter s`,
  let lemma = prove
   (`!s x y:real^N.
          bounded s /\ x IN relative_interior s /\ y IN s /\
          ~(diameter s = &0)
          ==> norm(x - y) < diameter s`,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM
     (MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR_CBALL]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real`
     STRIP_ASSUME_TAC)) THEN
    ASM_SIMP_TAC[REAL_LT_LE; DIAMETER_BOUNDED_BOUND] THEN
    ASM_CASES_TAC `y:real^N = x` THEN
    ASM_SIMP_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPEC `x + e / norm(x - y) % (x - y):real^N`) THEN
    REWRITE_TAC[NOT_IMP; IN_INTER] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_CBALL; NORM_ARITH `dist(x:real^M,x + y) = norm y`] THEN
      ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; REAL_DIV_RMUL;
                   NORM_EQ_0; VECTOR_SUB_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
      ASM_SIMP_TAC[HULL_INC; AFFINE_AFFINE_HULL];
      DISCH_TAC THEN MP_TAC(ISPECL
       [`s:real^N->bool`; `x + e / norm(x - y) % (x - y):real^N`; `y:real^N`]
          DIAMETER_BOUNDED_BOUND) THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[VECTOR_ARITH
       `(x + e % (x - y)) - y:real^N = (&1 + e) % (x - y)`] THEN
      SIMP_TAC[NORM_MUL; REAL_ARITH `~(a * n <= n) <=> &0 < n * (a - &1)`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e ==> &0 < abs(&1 + e) - &1`) THEN
      MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`closure s:real^N->bool`; `x:real^N`; `y:real^N`]
        lemma) THEN
  ASM_SIMP_TAC[DIAMETER_CLOSURE; BOUNDED_CLOSURE] THEN
  DISCH_THEN MATCH_MP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (SET_RULE `x IN s ==> s SUBSET t ==> x IN t`)) THEN
  MATCH_MP_TAC SUBSET_RELATIVE_INTERIOR THEN
  REWRITE_TAC[CLOSURE_SUBSET; AFFINE_HULL_CLOSURE]);;

let DIAMETER_ATTAINED_RELATIVE_FRONTIER = prove
 (`!s:real^N->bool.
        bounded s /\ ~(diameter s = &0)
        ==> ?x y. x IN relative_frontier s /\
                  y IN relative_frontier s /\
                  norm(x - y) = diameter s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[DIAMETER_EMPTY; relative_frontier] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `closure s:real^N->bool` DIAMETER_COMPACT_ATTAINED) THEN
  ASM_SIMP_TAC[COMPACT_CLOSURE; CLOSURE_EQ_EMPTY; DIAMETER_CLOSURE] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` DIAMETER_BOUNDED_BOUND_LT) THENL
   [DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `y:real^N`]);
    DISCH_THEN(MP_TAC o SPECL [`y:real^N`; `x:real^N`])] THEN
  ASM_MESON_TAC[REAL_LT_REFL; NORM_SUB]);;

let DIAMETER_RELATIVE_FRONTIER = prove
 (`!s:real^N->bool.
        bounded s /\ ~(?a. s = {a})
        ==> diameter(relative_frontier s) = diameter s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[RELATIVE_FRONTIER_EMPTY] THEN
  REWRITE_TAC[relative_frontier] THEN
  ASM_SIMP_TAC[GSYM DIAMETER_CLOSURE; GSYM REAL_LE_ANTISYM] THEN
  ASM_SIMP_TAC[SUBSET_DIFF; DIAMETER_SUBSET; BOUNDED_CLOSURE] THEN
  ASM_SIMP_TAC[DIAMETER_CLOSURE] THEN
  MP_TAC(ISPEC `s:real^N->bool` DIAMETER_ATTAINED_RELATIVE_FRONTIER) THEN
  ASM_SIMP_TAC[DIAMETER_EQ_0; relative_frontier] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
  ASM_SIMP_TAC[BOUNDED_CLOSURE; BOUNDED_DIFF]);;

let DIAMETER_ATTAINED_FRONTIER = prove
 (`!s:real^N->bool.
        bounded s /\ ~(diameter s = &0)
        ==> ?x y. x IN frontier s /\ y IN frontier s /\
                  norm(x - y) = diameter s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIAMETER_ATTAINED_RELATIVE_FRONTIER) THEN
  REWRITE_TAC[frontier; relative_frontier; IN_DIFF] THEN
  MESON_TAC[REWRITE_RULE[SUBSET] INTERIOR_SUBSET_RELATIVE_INTERIOR]);;

let DIAMETER_FRONTIER = prove
 (`!s:real^N->bool. bounded s ==> diameter(frontier s) = diameter s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `?a:real^N. s = {a}` THENL
   [ASM_MESON_TAC[FRONTIER_SING]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!r. r <= f /\ f <= s /\ r = s ==> f = s`) THEN
  EXISTS_TAC `diameter(closure s DIFF relative_interior s:real^N->bool)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM DIAMETER_CLOSURE] THEN MATCH_MP_TAC DIAMETER_SUBSET THEN
    ASM_SIMP_TAC[BOUNDED_FRONTIER] THEN REWRITE_TAC[frontier] THEN
    MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET_RELATIVE_INTERIOR) THEN
    SET_TAC[];
    ASM_SIMP_TAC[GSYM DIAMETER_CLOSURE] THEN MATCH_MP_TAC DIAMETER_SUBSET THEN
    ASM_SIMP_TAC[BOUNDED_CLOSURE; frontier; SUBSET_DIFF];
    ASM_SIMP_TAC[DIAMETER_RELATIVE_FRONTIER; GSYM relative_frontier]]);;

let DIAMETER_SPHERE = prove
 (`!a:real^N r. diameter(sphere(a,r)) = if r < &0 then &0 else &2 * r`,
  REWRITE_TAC[GSYM FRONTIER_CBALL] THEN
  ASM_SIMP_TAC[DIAMETER_FRONTIER; BOUNDED_CBALL; DIAMETER_CBALL]);;

let CLOSEST_POINT_IN_RELATIVE_INTERIOR = prove
 (`!s x:real^N.
        closed s /\ ~(s = {}) /\ x IN affine hull s
        ==> ((closest_point s x) IN relative_interior s <=>
             x IN relative_interior s)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x:real^N) IN s` THEN
  ASM_SIMP_TAC[CLOSEST_POINT_SELF] THEN
  MATCH_MP_TAC(TAUT `~q /\ ~p ==> (p <=> q)`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR_CBALL]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(closest_point s (x:real^N) = x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`;
   `closest_point s x -
    (min (&1) (e / norm(closest_point s x - x))) %
    (closest_point s x - x):real^N`]
    CLOSEST_POINT_LE) THEN
  ASM_REWRITE_TAC[dist; NOT_IMP; VECTOR_ARITH
   `x - (y - e % (y - x)):real^N = (&1 - e) % (x - y)`] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_CBALL; IN_INTER] THEN CONJ_TAC THENL
     [REWRITE_TAC[NORM_ARITH `dist(a:real^N,a - x) = norm x`] THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> abs(min (&1) a) <= a`) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_DIV; NORM_POS_LE];
      MATCH_MP_TAC IN_AFFINE_SUB_MUL_DIFF THEN
      ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC]];
    REWRITE_TAC[NORM_MUL; REAL_ARITH
     `~(n <= a * n) <=> &0 < (&1 - a) * n`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 < e /\ e <= &1 ==> &0 < &1 - abs(&1 - e)`) THEN
    REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN; REAL_LT_01; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ]]);;

let CLOSEST_POINT_IN_RELATIVE_FRONTIER = prove
 (`!s x:real^N.
        closed s /\ ~(s = {}) /\ x IN affine hull s DIFF relative_interior s
        ==> closest_point s x IN relative_frontier s`,
  SIMP_TAC[relative_frontier; IN_DIFF; CLOSEST_POINT_IN_RELATIVE_INTERIOR] THEN
  MESON_TAC[CLOSURE_SUBSET; CLOSEST_POINT_IN_SET; SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Interior, relative interior and closure interrelations.                   *)
(* ------------------------------------------------------------------------- *)

let CONVEX_CLOSURE_INTERIOR = prove
 (`!s:real^N->bool.
        convex s /\ ~(interior s = {})
        ==> closure(interior s) = closure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[SUBSET_CLOSURE; INTERIOR_SUBSET] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN ASM_CASES_TAC `b:real^N = a` THENL
   [ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[closure; IN_UNION; IN_ELIM_THM] THEN DISJ2_TAC THEN
  REWRITE_TAC[LIMPT_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `b - min (e / &2 / norm(b - a)) (&1) % (b - a):real^N` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
    ASM_REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN; REAL_LE_REFL; REAL_LT_01];
    REWRITE_TAC[VECTOR_ARITH `b - x:real^N = b <=> x = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(min x (&1) = &0)`);
    REWRITE_TAC[NORM_ARITH `dist(b - x:real^N,b) = norm x`] THEN
    REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `e / &2 / norm(b - a:real^N) * norm(b - a)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> abs(min x (&1)) <= x`);
      ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_POS_LT; REAL_LT_IMP_NZ;
                   VECTOR_SUB_EQ] THEN
      ASM_REAL_ARITH_TAC]] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; REAL_OF_NUM_LT;
                 VECTOR_SUB_EQ; ARITH]);;

let EMPTY_INTERIOR_SUBSET_HYPERPLANE = prove
 (`!s. convex s /\ interior s = {}
       ==> ?a:real^N b. ~(a = vec 0) /\ s SUBSET {x | a dot x = b}`,
  let lemma = prove
   (`!s. convex s /\ (vec 0) IN s /\ interior s = {}
         ==> ?a:real^N b. ~(a = vec 0) /\ s SUBSET {x | a dot x = b}`,
    GEN_TAC THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(relative_interior(s:real^N->bool) = {})` MP_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
    ASM_REWRITE_TAC[CONTRAPOS_THM] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
    ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC] THEN
    ONCE_REWRITE_TAC[GSYM SPAN_UNIV] THEN MATCH_MP_TAC DIM_EQ_SPAN THEN
    REWRITE_TAC[SUBSET_UNIV; DIM_UNIV; GSYM NOT_LT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LOWDIM_SUBSET_HYPERPLANE) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN EXISTS_TAC `&0` THEN
    ASM_MESON_TAC[SUBSET_TRANS; SPAN_INC]) in
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_MESON_TAC[EMPTY_SUBSET; BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  MP_TAC(ISPEC `IMAGE (\x:real^N. --a + x) s` lemma) THEN
  ASM_REWRITE_TAC[CONVEX_TRANSLATION_EQ; INTERIOR_TRANSLATION;
                  IMAGE_EQ_EMPTY; IN_IMAGE; UNWIND_THM2;
                  VECTOR_ARITH `vec 0:real^N = --a + x <=> x = a`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N` THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; DOT_RADD] THEN
  MESON_TAC[REAL_ARITH `a + x:real = b <=> x = b - a`]);;

let CONVEX_INTERIOR_CLOSURE = prove
 (`!s:real^N->bool. convex s ==> interior(closure s) = interior s`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `interior(s:real^N->bool) = {}` THENL
   [MP_TAC(ISPEC `s:real^N->bool` EMPTY_INTERIOR_SUBSET_HYPERPLANE) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!t. s SUBSET t /\ t = {} ==> s = {}`) THEN
    EXISTS_TAC `interior {x:real^N | a dot x = b}` THEN CONJ_TAC THENL
     [ALL_TAC;  ASM_SIMP_TAC[INTERIOR_HYPERPLANE]] THEN
    MATCH_MP_TAC SUBSET_INTERIOR THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_REWRITE_TAC[CLOSED_HYPERPLANE];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[SUBSET_INTERIOR; CLOSURE_SUBSET] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN
  MP_TAC(ASSUME `(b:real^N) IN interior(closure s)`) THEN
  GEN_REWRITE_TAC LAND_CONV [IN_INTERIOR_CBALL] THEN
  REWRITE_TAC[SUBSET; IN_CBALL; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `e:real` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `b:real^N = a` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `b + e / norm(b - a) % (b - a):real^N`) THEN
  ASM_SIMP_TAC[NORM_ARITH `dist(b:real^N,b + e) = norm e`; NORM_MUL;
    REAL_ABS_DIV; REAL_ABS_NORM; REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ;
    REAL_ARITH `&0 < e ==> abs e <= e`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `b = (b + e / norm(b - a) % (b - a)) -
        e / norm(b - a) / (&1 + e / norm(b - a)) %
        ((b + e / norm(b - a) % (b - a)) - a):real^N`
  SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH
     `b = (b + e % (b - a)) - d % ((b + e % (b - a)) - a) <=>
      (e - d * (&1 + e)) % (b - a) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_SUB_EQ; VECTOR_MUL_EQ_0];
    MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SHRINK] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_DIV; NORM_POS_LT;
               VECTOR_SUB_EQ; REAL_ARITH `&0 < x ==> &0 < &1 + x`;
               REAL_ARITH `&0 < x ==> ~(&1 + x = &0)`;
               REAL_MUL_LID; REAL_ADD_RDISTRIB; REAL_DIV_RMUL;
               REAL_LT_IMP_NZ; REAL_LE_ADDL; NORM_POS_LE; REAL_SUB_REFL]);;

let FRONTIER_CLOSURE_CONVEX = prove
 (`!s:real^N->bool. convex s ==> frontier(closure s) = frontier s`,
  SIMP_TAC[frontier; CLOSURE_CLOSURE; CONVEX_INTERIOR_CLOSURE]);;

let CONVEX_CLOSURE_RELATIVE_INTERIOR = prove
 (`!s:real^N->bool.
        convex s ==> closure(relative_interior s) = closure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[SUBSET_CLOSURE; RELATIVE_INTERIOR_SUBSET] THEN
  ASM_CASES_TAC `relative_interior(s:real^N->bool) = {}` THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; SUBSET_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN ASM_CASES_TAC `b:real^N = a` THENL
   [ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[closure; IN_UNION; IN_ELIM_THM] THEN DISJ2_TAC THEN
  REWRITE_TAC[LIMPT_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `b - min (e / &2 / norm(b - a)) (&1) % (b - a):real^N` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
    ASM_REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN; REAL_LE_REFL; REAL_LT_01];
    REWRITE_TAC[VECTOR_ARITH `b - x:real^N = b <=> x = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(min x (&1) = &0)`);
    REWRITE_TAC[NORM_ARITH `dist(b - x:real^N,b) = norm x`] THEN
    REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `e / &2 / norm(b - a:real^N) * norm(b - a)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> abs(min x (&1)) <= x`);
      ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_POS_LT; REAL_LT_IMP_NZ;
                   VECTOR_SUB_EQ] THEN
      ASM_REAL_ARITH_TAC]] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; REAL_OF_NUM_LT;
                 VECTOR_SUB_EQ; ARITH]);;

let AFFINE_HULL_RELATIVE_INTERIOR = prove
 (`!s. convex s
       ==> affine hull (relative_interior s) = affine hull s`,
  MESON_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; AFFINE_HULL_CLOSURE]);;

let AFF_DIM_RELATIVE_INTERIOR = prove
 (`!s:real^N->bool. convex s ==> aff_dim(relative_interior s) = aff_dim s`,
  ASM_MESON_TAC[AFF_DIM_AFFINE_HULL; AFFINE_HULL_RELATIVE_INTERIOR]);;

let CONVEX_RELATIVE_INTERIOR_CLOSURE = prove
 (`!s:real^N->bool.
        convex s ==> relative_interior(closure s) = relative_interior s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[CLOSURE_EMPTY; RELATIVE_INTERIOR_EMPTY] THEN
  SUBGOAL_THEN `?a:real^N. a IN relative_interior s` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEMBER_NOT_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IN_RELATIVE_INTERIOR; AFFINE_HULL_CLOSURE; SUBSET] THEN
    MESON_TAC[CLOSURE_SUBSET; SUBSET]] THEN
  X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN
  MP_TAC(ASSUME `(b:real^N) IN relative_interior(closure s)`) THEN
  GEN_REWRITE_TAC LAND_CONV [IN_RELATIVE_INTERIOR_CBALL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[SUBSET; IN_CBALL; IN_INTER; LEFT_IMP_EXISTS_THM;
              AFFINE_HULL_CLOSURE] THEN
  X_GEN_TAC `e:real` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `b:real^N = a` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `b + e / norm(b - a) % (b - a):real^N`) THEN
  ASM_SIMP_TAC[NORM_ARITH `dist(b:real^N,b + e) = norm e`; NORM_MUL;
    REAL_ABS_DIV; REAL_ABS_NORM; REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ;
    REAL_ARITH `&0 < e ==> abs e <= e`] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
    ASM_MESON_TAC[SUBSET; AFFINE_AFFINE_HULL; RELATIVE_INTERIOR_SUBSET;
                  CLOSURE_SUBSET_AFFINE_HULL; HULL_INC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `b = (b + e / norm(b - a) % (b - a)) -
        e / norm(b - a) / (&1 + e / norm(b - a)) %
        ((b + e / norm(b - a) % (b - a)) - a):real^N`
  SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH
     `b = (b + e % (b - a)) - d % ((b + e % (b - a)) - a) <=>
      (e - d * (&1 + e)) % (b - a) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_SUB_EQ; VECTOR_MUL_EQ_0];
    MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_DIV; NORM_POS_LT;
               VECTOR_SUB_EQ; REAL_ARITH `&0 < x ==> &0 < &1 + x`;
               REAL_ARITH `&0 < x ==> ~(&1 + x = &0)`;
               REAL_MUL_LID; REAL_ADD_RDISTRIB; REAL_DIV_RMUL;
               REAL_LT_IMP_NZ; REAL_LE_ADDL; NORM_POS_LE; REAL_SUB_REFL]);;

let RELATIVE_FRONTIER_CLOSURE = prove
 (`!s. convex s ==> relative_frontier(closure s) = relative_frontier s`,
  SIMP_TAC[relative_frontier; CLOSURE_CLOSURE;
           CONVEX_RELATIVE_INTERIOR_CLOSURE]);;

let RELATIVE_FRONTIER_RELATIVE_INTERIOR = prove
 (`!s:real^N->bool.
        convex s
        ==> relative_frontier(relative_interior s) = relative_frontier s`,
  ASM_MESON_TAC[RELATIVE_FRONTIER_CLOSURE; CONVEX_CLOSURE_RELATIVE_INTERIOR;
                CONVEX_RELATIVE_INTERIOR]);;

let CONNECTED_INTER_RELATIVE_FRONTIER = prove
 (`!s t:real^N->bool.
        connected s /\ s SUBSET affine hull t /\
        ~(s INTER t = {}) /\ ~(s DIFF t = {})
        ==> ~(s INTER relative_frontier t = {})`,
  REWRITE_TAC[relative_frontier] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_OPEN_IN]) THEN
  REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC
   [`s INTER relative_interior t:real^N->bool`;
    `s DIFF closure t:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
    EXISTS_TAC `affine hull t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN
    REWRITE_TAC[OPEN_IN_RELATIVE_INTERIOR; OPEN_IN_SUBTOPOLOGY_REFL] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
    ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    REWRITE_TAC[GSYM closed; CLOSED_CLOSURE];
    ASM SET_TAC[];
    MATCH_MP_TAC(SET_RULE
     `i SUBSET t /\ t SUBSET c ==> (s INTER i) INTER (s DIFF c) = {}`) THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SUBSET; CLOSURE_SUBSET];
    MP_TAC(ISPEC `t:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
    MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    ASM SET_TAC[]]);;

let CLOSED_RELATIVE_FRONTIER = prove
 (`!s:real^N->bool. closed(relative_frontier s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[relative_frontier] THEN
  MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
  EXISTS_TAC `affine hull s:real^N->bool` THEN
  REWRITE_TAC[CLOSED_AFFINE_HULL] THEN MATCH_MP_TAC CLOSED_IN_DIFF THEN
  REWRITE_TAC[OPEN_IN_RELATIVE_INTERIOR] THEN
  MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
  MATCH_MP_TAC(SET_RULE
   `s SUBSET closure t /\ closure t = t ==> s SUBSET t`) THEN
  SIMP_TAC[SUBSET_CLOSURE; HULL_SUBSET; CLOSURE_EQ; CLOSED_AFFINE_HULL]);;

let CLOSED_RELATIVE_BOUNDARY = prove
 (`!s. closed s ==> closed(s DIFF relative_interior s)`,
  MESON_TAC[CLOSED_RELATIVE_FRONTIER; relative_frontier; CLOSURE_CLOSED]);;

let COMPACT_RELATIVE_BOUNDARY = prove
 (`!s. compact s ==> compact(s DIFF relative_interior s)`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_RELATIVE_BOUNDARY;
           BOUNDED_DIFF]);;

let BOUNDED_RELATIVE_FRONTIER = prove
 (`!s:real^N->bool. bounded s ==> bounded(relative_frontier s)`,
  REWRITE_TAC[relative_frontier] THEN
  MESON_TAC[BOUNDED_CLOSURE; BOUNDED_SUBSET; SUBSET_DIFF]);;

let COMPACT_RELATIVE_FRONTIER_BOUNDED = prove
 (`!s:real^N->bool. bounded s ==> compact(relative_frontier s)`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_RELATIVE_FRONTIER;
           BOUNDED_RELATIVE_FRONTIER]);;

let COMPACT_RELATIVE_FRONTIER = prove
 (`!s:real^N->bool. compact s ==> compact(relative_frontier s)`,
  SIMP_TAC[COMPACT_RELATIVE_FRONTIER_BOUNDED; COMPACT_IMP_BOUNDED]);;

let CONVEX_SAME_RELATIVE_INTERIOR_CLOSURE = prove
 (`!s t. convex s /\ convex t
         ==> (relative_interior s = relative_interior t <=>
              closure s = closure t)`,
  MESON_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR;
            CONVEX_RELATIVE_INTERIOR_CLOSURE]);;

let CONVEX_SAME_RELATIVE_INTERIOR_CLOSURE_STRADDLE = prove
 (`!s t. convex s /\ convex t
         ==> (relative_interior s = relative_interior t <=>
              relative_interior s SUBSET t /\ t SUBSET closure s)`,
  MESON_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR;
            CONVEX_RELATIVE_INTERIOR_CLOSURE; SUBSET_CLOSURE;
                SUBSET_ANTISYM; RELATIVE_INTERIOR_SUBSET;
                CLOSURE_SUBSET; CLOSURE_CLOSURE]);;

let RELATIVE_INTERIOR_LINEAR_IMAGE_CONVEX = prove
 (`!f:real^M->real^N s.
        linear f /\ convex s
        ==> relative_interior(IMAGE f s) = IMAGE f (relative_interior s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `relative_interior (IMAGE f (relative_interior s)) =
      relative_interior (IMAGE (f:real^M->real^N) s)`
     (fun th -> REWRITE_TAC[SYM th; RELATIVE_INTERIOR_SUBSET]) THEN
    ASM_SIMP_TAC[CONVEX_SAME_RELATIVE_INTERIOR_CLOSURE_STRADDLE;
                 CONVEX_RELATIVE_INTERIOR; CONVEX_LINEAR_IMAGE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (f:real^M->real^N) (relative_interior s)` THEN
      SIMP_TAC[RELATIVE_INTERIOR_SUBSET; IMAGE_SUBSET];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
        `IMAGE (f:real^M->real^N) (closure(relative_interior s))` THEN
      ASM_SIMP_TAC[CLOSURE_LINEAR_IMAGE_SUBSET] THEN
      ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[CLOSURE_SUBSET]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^M` THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_PROLONG; CONVEX_LINEAR_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `z:real^M`; `x:real^M`]
        RELATIVE_INTERIOR_PROLONG) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o ISPEC `f:real^M->real^N` o MATCH_MP FUN_IN_IMAGE) THEN
    ASM_MESON_TAC[LINEAR_ADD; LINEAR_SUB; LINEAR_CMUL]]);;

let CLOSURE_INTERS_CONVEX = prove
 (`!f:(real^N->bool)->bool.
        (!s. s IN f ==> convex s) /\
        ~(INTERS(IMAGE relative_interior f) = {})
        ==> closure(INTERS f) = INTERS(IMAGE closure f)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[CLOSURE_INTERS_SUBSET] THEN
  REWRITE_TAC[SUBSET; IN_INTERS; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `b:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[INTERS_IMAGE; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `b:real^N = a` THENL
   [EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[DIST_REFL; IN_INTERS] THEN
    ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
    ALL_TAC] THEN
  EXISTS_TAC `b - min (&1 / &2) (e / &2 / norm(b - a)) % (b - a):real^N` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[NORM_ARITH `dist(b - a:real^N,b) = norm a`; NORM_MUL] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 < a /\ &0 < x /\ x < y ==> abs(min a x) < y`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_HALF; REAL_LT_DIV; NORM_POS_LT;
                 VECTOR_SUB_EQ] THEN
    ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[IN_INTERS] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC
   (MESON[RELATIVE_INTERIOR_SUBSET; SUBSET]
         `!x. x IN relative_interior s ==> x IN s`) THEN
  MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_HALF; REAL_LT_DIV; NORM_POS_LT;
               VECTOR_SUB_EQ] THEN
  REAL_ARITH_TAC);;

let CLOSURE_INTERS_CONVEX_OPEN = prove
 (`!f:(real^N->bool)->bool.
        (!s. s IN f ==> convex s /\ open s)
        ==> closure(INTERS f) =
                if INTERS f = {} then {}
                else INTERS(IMAGE closure f)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[CLOSURE_EMPTY] THEN
  MATCH_MP_TAC CLOSURE_INTERS_CONVEX THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `~(s = {}) ==> s = t ==> ~(t = {})`)) THEN
  AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = x) ==> s = IMAGE f s`) THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_OPEN; INTERIOR_EQ]);;

let CLOSURE_INTER_CONVEX = prove
 (`!s t:real^N->bool.
        convex s /\ convex t /\
        ~(relative_interior s INTER relative_interior t = {})
        ==> closure(s INTER t) = closure(s) INTER closure(t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{s:real^N->bool,t}` CLOSURE_INTERS_CONVEX) THEN
  ASM_SIMP_TAC[IMAGE_CLAUSES; INTERS_2] THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY]);;

let CLOSURE_INTER_CONVEX_OPEN = prove
 (`!s t. convex s /\ open s /\ convex t /\ open t
         ==> closure(s INTER t) =
                if s INTER t = {} then {} else closure(s) INTER closure(t)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[CLOSURE_EMPTY] THEN
  MATCH_MP_TAC CLOSURE_INTER_CONVEX THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_OPEN]);;

let CLOSURE_CONVEX_INTER_SUPERSET = prove
 (`!s t:real^N->bool.
        convex s /\ ~(interior s = {}) /\ interior s SUBSET closure t
        ==> closure(s INTER t) = closure s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[SUBSET_CLOSURE; INTER_SUBSET; SUBSET_INTER] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `closure(interior s):real^N->bool` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_INTERIOR; SUBSET_REFL];
    ASM_SIMP_TAC[GSYM CLOSURE_OPEN_INTER_SUPERSET; OPEN_INTERIOR] THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN
    MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN SET_TAC[]]);;

let CLOSURE_DYADIC_RATIONALS_IN_CONVEX_SET = prove
 (`!s:real^N->bool.
        convex s /\ ~(interior s = {})
        ==> closure(s INTER
                    { inv(&2 pow n) % x | n,x |
                      !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i) }) =
            closure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_CONVEX_INTER_SUPERSET THEN
  ASM_REWRITE_TAC[CLOSURE_DYADIC_RATIONALS; SUBSET_UNIV]);;

let CLOSURE_RATIONALS_IN_CONVEX_SET = prove
 (`!s:real^N->bool.
      convex s /\ ~(interior s = {})
      ==> closure(s INTER
                  { x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i) }) =
          closure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_CONVEX_INTER_SUPERSET THEN
  ASM_REWRITE_TAC[CLOSURE_RATIONAL_COORDINATES; SUBSET_UNIV]);;

let RELATIVE_INTERIOR_CONVEX_INTER_AFFINE = prove
 (`!s t:real^N->bool.
        convex s /\ affine t /\ ~(interior s INTER t = {})
        ==> relative_interior(s INTER t) = interior s INTER t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; RIGHT_AND_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` MP_TAC) THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN REWRITE_TAC[IN_INTER] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(vec 0:real^N) IN t` THEN
  ASM_SIMP_TAC[AFFINE_EQ_SUBSPACE] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `s:real^N->bool`]
        (ONCE_REWRITE_RULE[INTER_COMM]
           AFFINE_HULL_AFFINE_INTER_NONEMPTY_INTERIOR)) THEN
  ASM_SIMP_TAC[SUBSPACE_IMP_AFFINE; IN_RELATIVE_INTERIOR_CBALL] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_INTER; IN_INTERIOR_CBALL]] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN t` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[SUBSET; IN_INTER] THEN
  ASM_CASES_TAC `(x:real^N) IN s` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE]] THEN
  EQ_TAC THENL [REWRITE_TAC[IN_CBALL]; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `x:real^N = vec 0` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR_CBALL]) THEN
    ASM_REWRITE_TAC[SUBSET; IN_CBALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`s:real^N->bool`; `vec 0:real^N`; `(&1 + e / norm x) % x:real^N`]
   IN_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[SUBSPACE_MUL] THEN
    REWRITE_TAC[VECTOR_ADD_RDISTRIB; VECTOR_MUL_LID;
                NORM_ARITH `dist(a:real^N,a + x) = norm x`] THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM;
                 REAL_DIV_RMUL; NORM_EQ_0] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_INTERIOR_CBALL; IN_CBALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    EXISTS_TAC `inv(&1 + e / norm(x:real^N))` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_LT_DIV; NORM_POS_LT; VECTOR_MUL_LID;
                 REAL_LT_INV_EQ; REAL_MUL_LINV; REAL_INV_LT_1; REAL_ARITH
                 `&0 < x ==> &1 < &1 + x /\ &0 < &1 + x /\ ~(&1 + x = &0)`]]);;

(* ------------------------------------------------------------------------- *)
(* Lower-dimensional affine subsets are nowhere dense.                       *)
(* ------------------------------------------------------------------------- *)

let DENSE_COMPLEMENT_SUBSPACE = prove
 (`!s t:real^N->bool.
        dim t < dim s /\ subspace s ==> closure(s DIFF t) = s`,
  SUBGOAL_THEN
   `!s t:real^N->bool.
        dim t < dim s /\ subspace s /\ t SUBSET s
        ==> closure(s DIFF t) = s`
  MP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `s:real^N->bool` THEN
    DISCH_TAC THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s INTER t:real^N->bool`) THEN
    ASM_REWRITE_TAC[SET_RULE `s DIFF (s INTER t) = s DIFF t`] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[INTER_SUBSET] THEN
    TRANS_TAC LET_TRANS `dim(t:real^N->bool)` THEN
    ASM_SIMP_TAC[DIM_SUBSET; INTER_SUBSET]] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `s:real^N->bool`]
        ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN) THEN
  ASM_SIMP_TAC[PSUBSET; SPAN_MONO] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[LT_REFL; DIM_SPAN]; ASM_SIMP_TAC[SPAN_OF_SUBSPACE]] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[CLOSED_SUBSPACE] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; CLOSURE_APPROACHABLE] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN t` THENL
   [ALL_TAC; EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[DIST_REFL]] THEN
  EXISTS_TAC `x + e / &2 / norm(a) % a:real^N` THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBSPACE_ADD; SUBSPACE_MUL];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC
     `(x + e / &2 / norm(a) % a) + -- &1 % x:real^N`) THEN
    ASM_SIMP_TAC[NOT_IMP; SPAN_ADD; SPAN_MUL; SPAN_SUPERSET] THEN
    REWRITE_TAC[VECTOR_ARITH `(x + a) + -- &1 % x:real^N = a`] THEN
    ASM_REWRITE_TAC[ORTHOGONAL_MUL; ORTHOGONAL_REFL;
                    REAL_DIV_EQ_0; NORM_EQ_0] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[NORM_ARITH `dist(x + a:real^N,x) = norm a`] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0] THEN ASM_REAL_ARITH_TAC]);;

let DENSE_COMPLEMENT_AFFINE = prove
 (`!s t:real^N->bool.
        aff_dim t < aff_dim s /\ affine s ==> closure(s DIFF t) = s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s INTER t:real^N->bool = {}` THENL
   [REPEAT STRIP_TAC THEN
    TRANS_TAC EQ_TRANS `closure s:real^N->bool` THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN ASM SET_TAC[];
      ASM_SIMP_TAC[CLOSURE_CLOSED; CLOSED_AFFINE]];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_INTER] THEN X_GEN_TAC `z:real^N` THEN
    GEOM_ORIGIN_TAC `z:real^N` THEN
    SIMP_TAC[AFFINE_EQ_SUBSPACE; AFF_DIM_DIM_0; HULL_INC; INT_OF_NUM_LT] THEN
    MESON_TAC[DENSE_COMPLEMENT_SUBSPACE]]);;

let DENSE_COMPLEMENT_OPEN_IN_AFFINE_HULL = prove
 (`!s t:real^N->bool.
        aff_dim t < aff_dim s /\
        open_in (subtopology euclidean (affine hull s)) s
        ==> closure(s DIFF t) = closure s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `affine hull s DIFF t:real^N->bool`;
           `affine hull s:real^N->bool`] CLOSURE_OPEN_IN_INTER_CLOSURE) THEN
  ASM_REWRITE_TAC[OPEN_IN_RELATIVE_INTERIOR; SUBSET_DIFF] THEN
  ASM_SIMP_TAC[DENSE_COMPLEMENT_AFFINE; AFFINE_AFFINE_HULL;
               AFF_DIM_AFFINE_HULL] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN MATCH_MP_TAC EQ_IMP THEN
  BINOP_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `s:real^N->bool`]
        HULL_SUBSET) THEN SET_TAC[]);;

let DENSE_COMPLEMENT_CONVEX = prove
 (`!s t:real^N->bool.
        aff_dim t < aff_dim s /\ convex s ==> closure(s DIFF t) = closure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[SUBSET_CLOSURE; SUBSET_DIFF] THEN
  MP_TAC(ISPECL [`relative_interior s:real^N->bool`; `t:real^N->bool`]
        DENSE_COMPLEMENT_OPEN_IN_AFFINE_HULL) THEN
  ASM_SIMP_TAC[OPEN_IN_RELATIVE_INTERIOR; AFF_DIM_RELATIVE_INTERIOR;
    AFFINE_HULL_RELATIVE_INTERIOR; CONVEX_CLOSURE_RELATIVE_INTERIOR] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUBSET_CLOSURE THEN
  MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]);;

let DENSE_COMPLEMENT_CONVEX_CLOSED = prove
 (`!s t:real^N->bool.
        aff_dim t < aff_dim s /\ convex s /\ closed s
        ==> closure(s DIFF t) = s`,
  ASM_SIMP_TAC[DENSE_COMPLEMENT_CONVEX; CLOSURE_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* Homeomorphism of all convex compact sets with same affine dimension, and  *)
(* in particular all those with nonempty interior.                           *)
(* ------------------------------------------------------------------------- *)

let COMPACT_FRONTIER_LINE_LEMMA = prove
 (`!s x. compact s /\ (vec 0 IN s) /\ ~(x = vec 0 :real^N)
         ==> ?u. &0 <= u /\ (u % x) IN frontier s /\
                 !v. u < v ==> ~((v % x) IN s)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
    [`{y:real^N | ?u. &0 <= u /\ u <= b / norm(x) /\ (y = u % x)} INTER s`;
     `vec 0:real^N`]
   DISTANCE_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^N` THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      EXISTS_TAC `&0` THEN
      ASM_SIMP_TAC[VECTOR_MUL_LZERO; REAL_LE_REFL; REAL_LT_IMP_LE;
                   REAL_LT_DIV; NORM_POS_LT]] THEN
    MATCH_MP_TAC COMPACT_INTER THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `{y:real^N | ?u. &0 <= u /\ u <= b / norm(x) /\ (y = u % x)} =
      IMAGE (\u. drop u % x) (interval [vec 0,lambda i. b / norm(x:real^N)])`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_INTERVAL] THEN
      SIMP_TAC[LAMBDA_BETA] THEN
      SIMP_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> (i = 1)`] THEN
      REWRITE_TAC[GSYM drop; LEFT_FORALL_IMP_THM; EXISTS_REFL; DROP_VEC] THEN
      REWRITE_TAC[EXISTS_LIFT; LIFT_DROP] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_VMUL THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[TAUT `(a /\ b /\ c) /\ d <=> c /\ a /\ b /\ d`] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  GEN_REWRITE_TAC (BINDER_CONV o ONCE_DEPTH_CONV) [SWAP_FORALL_THM] THEN
  SIMP_TAC[IMP_CONJ] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LEFT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real` THEN
  REWRITE_TAC[dist; VECTOR_SUB_LZERO; NORM_NEG; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ; NORM_POS_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[real_abs] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[FRONTIER_STRADDLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [EXISTS_TAC `u % x :real^N` THEN ASM_REWRITE_TAC[DIST_REFL];
      ALL_TAC] THEN
    EXISTS_TAC `(u + (e / &2) / norm(x)) % x :real^N` THEN
    REWRITE_TAC[dist; VECTOR_ARITH `u % x - (u + a) % x = --(a % x)`] THEN
    ASM_SIMP_TAC[NORM_NEG; NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; NORM_EQ_0;
                 REAL_DIV_RMUL; REAL_ABS_NUM; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT;
                 ARITH; REAL_ARITH `abs e < e * &2 <=> &0 < e`] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u + (e / &2) / norm(x:real^N)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `&0 < e /\ &0 <= u /\ u + e <= b
      ==> ~(&0 <= u + e /\ u + e <= b ==> u + e <= u)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; NORM_POS_LT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(u + (e / &2) / norm(x:real^N)) % x`) THEN
    ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LE_RDIV_EQ; NORM_POS_LT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real`) THEN
  ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN ASM_REWRITE_TAC[REAL_NOT_LT] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[REAL_LET_TRANS; REAL_LT_IMP_LE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v % x:real^N`) THEN
  ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LE_RDIV_EQ; NORM_POS_LT] THEN
  REAL_ARITH_TAC);;

let STARLIKE_COMPACT_PROJECTIVE = prove
 (`!s:real^N->bool a.
        compact s /\ a IN relative_interior s /\
        (!x. x IN s ==> segment(a,x) SUBSET relative_interior s)
        ==> s DIFF relative_interior s homeomorphic
            sphere(a,&1) INTER affine hull s /\
            s homeomorphic cball(a,&1) INTER affine hull s`,
  REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC `a:real^N` THEN
  REWRITE_TAC[SUBSET; IMP_IMP; RIGHT_IMP_FORALL_THM] THEN
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^N u. x IN s /\ &0 <= u /\ u < &1
                 ==> (u % x) IN relative_interior s`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&0 <= u <=> u = &0 \/ &0 < u`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    ASM_CASES_TAC `x:real^N = vec 0` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SEGMENT] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(K ALL_TAC o SPECL [`x:real^N`; `x:real^N`])] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
    RELATIVE_INTERIOR_SUBSET)) THEN
  ABBREV_TAC `proj = \x:real^N. inv(norm(x)) % x` THEN
  SUBGOAL_THEN
   `!x:real^N y. (proj(x) = proj(y):real^N) /\ (norm x = norm y) <=> (x = y)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    ASM_CASES_TAC `y:real^N = vec 0` THEN
    ASM_SIMP_TAC[NORM_EQ_0; NORM_0] THEN
    ASM_CASES_TAC `x:real^N = vec 0` THENL
     [ASM_MESON_TAC[NORM_EQ_0]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    EXPAND_TAC "proj" THEN REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH
     `a % x = a % y <=> a % (x - y):real^N = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; NORM_EQ_0; VECTOR_SUB_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN affine hull s ==> proj x IN affine hull s) /\
    (!x. ~(x = vec 0) ==> norm(proj x) = &1) /\
    (!x:real^N. proj x = vec 0 <=> x = vec 0)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "proj" THEN REWRITE_TAC[NORM_MUL; VECTOR_MUL_EQ_0] THEN
    REWRITE_TAC[REAL_INV_EQ_0; NORM_EQ_0; REAL_ABS_INV; REAL_ABS_NORM] THEN
    SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_ADD_LID] THEN
    MATCH_MP_TAC IN_AFFINE_ADD_MUL THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; VECTOR_ADD_LID; HULL_INC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(proj:real^N->real^N) continuous_on (UNIV DELETE vec 0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[IN_DELETE; IN_UNIV] THEN EXPAND_TAC "proj" THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
    ASM_SIMP_TAC[CONTINUOUS_AT_ID] THEN
    REWRITE_TAC[GSYM(ISPEC `lift` o_DEF);
                GSYM(ISPEC `inv:real->real` o_DEF)] THEN
    MATCH_MP_TAC CONTINUOUS_AT_INV THEN
    ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ; CONTINUOUS_AT_LIFT_NORM];
    ALL_TAC] THEN
  ABBREV_TAC `usph = {x:real^N | x IN affine hull s /\ norm x = &1}` THEN
  SUBGOAL_THEN ` sphere(vec 0:real^N,&1) INTER affine hull s = usph`
  SUBST1_TAC THENL
   [EXPAND_TAC "usph" THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_SPHERE_0] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN affine hull s /\ ~(x = vec 0)
        ==> (proj:real^N->real^N) x IN usph`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?surf. homeomorphism (s DIFF relative_interior s,usph)
                                     (proj:real^N->real^N,surf)`
  MP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
    ASM_SIMP_TAC[COMPACT_RELATIVE_BOUNDARY] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN
        EXPAND_TAC "usph" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_MESON_TAC[HULL_INC];
        MAP_EVERY EXPAND_TAC ["proj"; "usph"] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
        ASM_CASES_TAC `x:real^N = vec 0` THEN
        ASM_REWRITE_TAC[NORM_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`s:real^N->bool`; `vec 0:real^N`; `x:real^N`]
            RAY_TO_RELATIVE_FRONTIER) THEN
        REWRITE_TAC[relative_frontier] THEN
        ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; CLOSURE_CLOSED; COMPACT_IMP_CLOSED;
                     VECTOR_ADD_LID] THEN
        DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
        EXPAND_TAC "proj" THEN REWRITE_TAC[IN_IMAGE] THEN
        EXISTS_TAC `d % x:real^N` THEN ASM_REWRITE_TAC[NORM_MUL] THEN
        ASM_SIMP_TAC[REAL_MUL_RID; real_abs; REAL_LT_IMP_LE] THEN
        ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
                     VECTOR_MUL_LID]];
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
      REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      ASM_CASES_TAC `x:real^N = vec 0` THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `y:real^N = vec 0` THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(proj:real^N->real^N) x = proj y` THEN
      EXPAND_TAC "proj" THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH
       `norm(x:real^N) = norm(y:real^N) \/
        norm x < norm y \/ norm y < norm x`)
      THENL
       [ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL; REAL_INV_EQ_0; NORM_EQ_0];
        DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
         [`y:real^N`; `norm(x:real^N) / norm(y:real^N)`]);
        DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
         [`x:real^N`; `norm(y:real^N) / norm(x:real^N)`])] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_LT_LDIV_EQ; NORM_POS_LT;
                   REAL_MUL_LID] THEN
      ASM_REWRITE_TAC[real_div; GSYM VECTOR_MUL_ASSOC] THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM); ALL_TAC] THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; NORM_EQ_0] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LID]];
    DISCH_THEN(fun th ->
      CONJ_TAC THENL
       [MESON_TAC[homeomorphic; th];
        ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
        MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN
        SIMP_TAC[COMPACT_INTER_CLOSED; CLOSED_AFFINE_HULL; COMPACT_CBALL] THEN
        MP_TAC th]) THEN
    REWRITE_TAC[HOMEOMORPHISM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `surf:real^N->real^N` THEN STRIP_TAC THEN
    EXISTS_TAC `\x:real^N. norm(x) % (surf:real^N->real^N)(proj(x))` THEN
    REWRITE_TAC[]] THEN
  UNDISCH_THEN
   `(proj:real^N->real^N) continuous_on s DIFF relative_interior s`
   (K ALL_TAC) THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_INTER] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    ASM_CASES_TAC `x = vec 0:real^N` THENL
     [ASM_REWRITE_TAC[CONTINUOUS_WITHIN; VECTOR_MUL_LZERO; NORM_0] THEN
      MATCH_MP_TAC LIM_NULL_VMUL_BOUNDED THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
      REWRITE_TAC[BOUNDED_POS] THEN MATCH_MP_TAC MONO_EXISTS THEN
      REPEAT STRIP_TAC THENL
       [REWRITE_TAC[LIM_WITHIN; o_THM; DIST_0; NORM_LIFT; REAL_ABS_NORM] THEN
        MESON_TAC[];
        REWRITE_TAC[EVENTUALLY_WITHIN] THEN EXISTS_TAC `&1` THEN
        REWRITE_TAC[REAL_LT_01; IN_INTER; DIST_0; NORM_POS_LT] THEN
        ASM SET_TAC[]];
      MATCH_MP_TAC CONTINUOUS_WITHIN_SUBSET THEN
      EXISTS_TAC `affine hull s:real^N->bool` THEN
      REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
      SIMP_TAC[CONTINUOUS_LIFT_NORM_COMPOSE; CONTINUOUS_WITHIN_ID; o_DEF] THEN
      SUBGOAL_THEN
       `((surf:real^N->real^N) o (proj:real^N->real^N)) continuous_on
        (affine hull s DELETE vec 0)`
      MP_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
        SIMP_TAC[SUBSET; IN_DELETE; IN_UNIV; FORALL_IN_IMAGE] THEN
        EXPAND_TAC "usph" THEN ASM_SIMP_TAC[IN_ELIM_THM];
        SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_SIMP_TAC[IN_DELETE] THEN
        REWRITE_TAC[CONTINUOUS_WITHIN; o_DEF] THEN MATCH_MP_TAC EQ_IMP THEN
        MATCH_MP_TAC LIM_TRANSFORM_WITHIN_SET THEN
        REWRITE_TAC[EVENTUALLY_AT] THEN EXISTS_TAC `norm(x:real^N)` THEN
        ASM_REWRITE_TAC[IN_DELETE; IN_INTER; IN_CBALL; NORM_POS_LT] THEN
        X_GEN_TAC `y:real^N` THEN
        ASM_CASES_TAC `(y:real^N) IN affine hull s` THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC NORM_ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a x. &0 < a ==> (proj:real^N->real^N)(a % x) = proj x`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "proj" THEN
    REWRITE_TAC[NORM_MUL; REAL_INV_MUL; VECTOR_MUL_ASSOC] THEN
    SIMP_TAC[REAL_FIELD `&0 < a ==> (inv(a) * x) * a = x`; real_abs;
             REAL_LT_IMP_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
    ASM_CASES_TAC `y:real^N = vec 0` THENL
     [ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_EQ_0; NORM_0; NORM_EQ_0] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `x:real^N = vec 0` THENL
     [CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
      ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_EQ_0; NORM_0; NORM_EQ_0] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INTER; IN_CBALL_0] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th -> MP_TAC th THEN
             MP_TAC(AP_TERM `proj:real^N->real^N` th)) THEN
    ASM_SIMP_TAC[NORM_POS_LT; VECTOR_MUL_RCANCEL] THEN ASM SET_TAC[]] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_CBALL_0] THEN
    X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
    ASM_REWRITE_TAC[NORM_0; VECTOR_MUL_LZERO; IN_INTER] THEN
    REWRITE_TAC[IN_CBALL_0; REAL_LE_LT] THEN STRIP_TAC  THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
      ASM SET_TAC[];
      ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_CBALL_0; IN_INTER] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x:real^N = vec 0` THENL
   [EXISTS_TAC `vec 0:real^N` THEN
    ASM_SIMP_TAC[NORM_0; VECTOR_MUL_LZERO; HULL_INC; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN usph ==> ~((surf:real^N->real^N) x = vec 0)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `inv(norm(surf(proj x:real^N):real^N)) % x:real^N` THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [NORM_POS_LT; REAL_LT_INV_EQ; HULL_INC; REAL_LT_MUL; NORM_MUL;
    REAL_ABS_INV; REAL_ABS_NORM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `~(y = &0) ==> x = (inv y * x) * y`) THEN
    ASM_SIMP_TAC[NORM_EQ_0; HULL_INC];
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
     [GSYM real_div; REAL_LE_LDIV_EQ; NORM_POS_LT; HULL_INC; REAL_MUL_LID] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`x:real^N`; `norm(surf(proj x:real^N):real^N) / norm(x:real^N)`]) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_LT_LDIV_EQ; NORM_POS_LT] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[REAL_NOT_LT; REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN
     `norm(surf(proj x)) / norm x % x:real^N = surf(proj x:real^N)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
      ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
       [NORM_POS_LT; REAL_LT_INV_EQ; HULL_INC; REAL_LT_MUL; NORM_MUL;
        REAL_ABS_INV; REAL_ABS_NORM; REAL_ABS_DIV; REAL_LT_DIV;
        REAL_DIV_RMUL; NORM_EQ_0];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE f s SUBSET t DIFF u ==> x IN s ==> ~(f x IN u)`)) THEN
      ASM_SIMP_TAC[HULL_INC]];
    GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_ADD_LID] THEN
    MATCH_MP_TAC IN_AFFINE_ADD_MUL THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; VECTOR_ADD_LID; HULL_INC]]);;

let HOMEOMORPHIC_CONVEX_COMPACT_SETS,
    HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS = (CONJ_PAIR o prove)
 (`(!s:real^M->bool t:real^N->bool.
        convex s /\ compact s /\ convex t /\ compact t /\ aff_dim s = aff_dim t
        ==> s homeomorphic t) /\
   (!s:real^M->bool t:real^N->bool.
        convex s /\ bounded s /\ convex t /\ bounded t /\ aff_dim s = aff_dim t
        ==> relative_frontier s homeomorphic relative_frontier t)`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool.
          convex s /\ compact s /\ convex t /\ compact t /\
          aff_dim s = aff_dim t
          ==> (s DIFF relative_interior s) homeomorphic
              (t DIFF relative_interior t) /\
              s homeomorphic t`,
    REPEAT GEN_TAC THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_CASES_TAC `relative_interior t:real^N->bool = {}` THENL
     [UNDISCH_TAC `relative_interior t:real^N->bool = {}` THEN
      ASM_SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_EQ_MINUS1;
                   EMPTY_DIFF; HOMEOMORPHIC_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY];
       FIRST_X_ASSUM(X_CHOOSE_THEN `b:real^N` MP_TAC o
          GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY])] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    ASM_CASES_TAC `relative_interior s:real^M->bool = {}` THENL
     [UNDISCH_TAC `relative_interior s:real^M->bool = {}` THEN
      ASM_SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_EQ_MINUS1;
                   EMPTY_DIFF; HOMEOMORPHIC_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY];
      FIRST_X_ASSUM(X_CHOOSE_THEN `a:real^M` MP_TAC o
          GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY])] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    GEOM_ORIGIN_TAC `b:real^N` THEN REPEAT GEN_TAC THEN
    GEOM_ORIGIN_TAC `a:real^M` THEN REPEAT GEN_TAC THEN
    REPEAT DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `vec 0:real^M`]
          STARLIKE_COMPACT_PROJECTIVE) THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `vec 0:real^N`]
          STARLIKE_COMPACT_PROJECTIVE) THEN
    ASM_SIMP_TAC[IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT;
                 REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN
    DISCH_THEN(fun th -> MATCH_MP_TAC MONO_AND THEN MP_TAC th) THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMEOMORPHIC_TRANS) THEN
     MP_TAC(ONCE_REWRITE_RULE[HOMEOMORPHIC_SYM] th)) THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] HOMEOMORPHIC_TRANS) THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
          RELATIVE_INTERIOR_SUBSET))) THEN
    FIRST_X_ASSUM(MP_TAC o SYM) THEN
    ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; AFF_DIM_DIM_0] THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`span s:real^M->bool`; `span t:real^N->bool`]
            ISOMETRIES_SUBSPACES) THEN
    ASM_REWRITE_TAC[SUBSPACE_SPAN; DIM_SPAN; homeomorphic; HOMEOMORPHISM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^M->real^N` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^M` THEN
    SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_CBALL_0; IN_SPHERE_0] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN ASM SET_TAC[]) in
  SIMP_TAC[lemma; relative_frontier] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`closure s:real^M->bool`; `closure t:real^N->bool`] lemma) THEN
  ASM_SIMP_TAC[CONVEX_CLOSURE; COMPACT_CLOSURE; AFF_DIM_CLOSURE] THEN
  ASM_SIMP_TAC[CONVEX_RELATIVE_INTERIOR_CLOSURE]);;

let HOMEOMORPHIC_CONVEX_COMPACT = prove
 (`!s:real^N->bool t:real^N->bool.
        convex s /\ compact s /\ ~(interior s = {}) /\
        convex t /\ compact t /\ ~(interior t = {})
        ==> s homeomorphic t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_CONVEX_COMPACT_SETS THEN
  ASM_SIMP_TAC[AFF_DIM_NONEMPTY_INTERIOR]);;

let HOMEOMORPHIC_CONVEX_COMPACT_CBALL = prove
 (`!s:real^N->bool b:real^N e.
        convex s /\ compact s /\ ~(interior s = {}) /\ &0 < e
        ==> s homeomorphic cball(b,e)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_CONVEX_COMPACT THEN
  ASM_REWRITE_TAC[COMPACT_CBALL; INTERIOR_CBALL; CONVEX_CBALL] THEN
  ASM_REWRITE_TAC[BALL_EQ_EMPTY; REAL_NOT_LE]);;

let HOMEOMORPHIC_CLOSED_INTERVALS = prove
 (`!a b:real^N c d:real^N.
        ~(interval(a,b) = {}) /\ ~(interval(c,d) = {})
        ==> interval[a,b] homeomorphic interval[c,d]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_CONVEX_COMPACT THEN
  REWRITE_TAC[CONVEX_INTERVAL; COMPACT_INTERVAL] THEN
  ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* More about affine dimension of special sets.                              *)
(* ------------------------------------------------------------------------- *)

let AFF_DIM_NONEMPTY_INTERIOR_EQ = prove
 (`!s:real^N->bool.
        convex s ==> (aff_dim s = &(dimindex (:N)) <=> ~(interior s = {}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[AFF_DIM_NONEMPTY_INTERIOR] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` EMPTY_INTERIOR_SUBSET_HYPERPLANE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SUBSET) THEN
  ASM_SIMP_TAC[AFF_DIM_HYPERPLANE] THEN INT_ARITH_TAC);;

let AFF_DIM_BALL = prove
 (`!a:real^N r.
        aff_dim(ball(a,r)) = if &0 < r then &(dimindex(:N)) else --(&1)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC AFF_DIM_OPEN THEN
    ASM_REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT; GSYM BALL_EQ_EMPTY]) THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY]]);;

let AFF_DIM_CBALL = prove
 (`!a:real^N r.
        aff_dim(cball(a,r)) =
            if &0 < r then &(dimindex(:N))
            else if r = &0 then &0 else --(&1)`,
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THENL
   [MATCH_MP_TAC AFF_DIM_NONEMPTY_INTERIOR THEN
    ASM_REWRITE_TAC[INTERIOR_CBALL; BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[CBALL_SING; AFF_DIM_SING];
    MATCH_MP_TAC(MESON[AFF_DIM_EMPTY] `s = {} ==> aff_dim s = --(&1)`) THEN
    REWRITE_TAC[CBALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC]);;

let AFF_DIM_INTERVAL = prove
 (`(!a b:real^N.
        aff_dim(interval[a,b]) =
                if interval[a,b] = {} then --(&1)
                else &(CARD {i | 1 <= i /\ i <= dimindex(:N) /\ a$i < b$i})) /\
   (!a b:real^N.
         aff_dim(interval(a,b)) =
                if interval(a,b) = {} then --(&1)
                else &(dimindex(:N)))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_OPEN; OPEN_INTERVAL] THEN
  POP_ASSUM MP_TAC THEN GEOM_ORIGIN_TAC `a:real^N` THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VEC_COMPONENT; REAL_LT_LADD] THEN
  ASM_SIMP_TAC[AFF_DIM_DIM_0; HULL_INC; ENDS_IN_INTERVAL] THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN MATCH_MP_TAC DIM_UNIQUE THEN EXISTS_TAC
   `{basis i:real^N | 1 <= i /\ i <= dimindex(:N) /\ &0 < (b:real^N)$i}` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY; VEC_COMPONENT]) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `basis i:real^N = inv(b$i) % (b:real^N)$i % basis i`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[VECTOR_MUL_LID];
      MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN
      SIMP_TAC[IN_INTERVAL; VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
      X_GEN_TAC `j:num` THEN REWRITE_TAC[VEC_COMPONENT] THEN
      COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_LE_REFL]];
    MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
    REWRITE_TAC[SUBSPACE_SPAN; SUBSET; IN_INTERVAL; VEC_COMPONENT] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
    MATCH_MP_TAC SPAN_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_CASES_TAC `&0 < (b:real^N)$i` THENL
     [MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN ASM SET_TAC[];
      SUBGOAL_THEN `(x:real^N)$i = &0`
        (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO; SPAN_0]) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
    REWRITE_TAC[SET_RULE `~(a IN {f x | P x}) <=> !x. P x ==> ~(f x = a)`] THEN
    SIMP_TAC[BASIS_NONZERO; pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    SIMP_TAC[FORALL_IN_GSPEC; BASIS_INJ_EQ; ORTHOGONAL_BASIS_BASIS];
    GEN_REWRITE_TAC LAND_CONV [SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC; BASIS_INJ_EQ;
             HAS_SIZE] THEN
    SIMP_TAC[CONJ_ASSOC; GSYM IN_NUMSEG; FINITE_RESTRICT; FINITE_NUMSEG]]);;

(* ------------------------------------------------------------------------- *)
(* Deducing convexity from midpoint convexity in common cases.               *)
(* ------------------------------------------------------------------------- *)

let MIDPOINT_CONVEX_DYADIC_RATIONALS = prove
 (`!f:real^N->real s.
        (!x y. x IN s /\ y IN s
               ==> midpoint(x,y) IN s /\
                   f(midpoint(x,y)) <= (f(x) + f(y)) / &2)
        ==> !n m p x y.
                x IN s /\ y IN s /\ m + p = 2 EXP n
                ==> (&m / &2 pow n % x + &p / &2 pow n % y) IN s /\
                    f(&m / &2 pow n % x + &p / &2 pow n % y)
                    <= &m / &2 pow n * f x + &p / &2 pow n * f y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE
     `m + p = 2 EXP 0 <=> m = 0 /\ p = 1 \/ m = 1 /\ p = 0`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO;
                  VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_SYM; REAL_ADD_SYM; ADD_SYM] THEN MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `p:num`] THEN DISCH_TAC THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[EXP; real_pow] THEN STRIP_TAC THEN
    REWRITE_TAC[real_div; REAL_INV_MUL] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x * inv(&2) * y = inv(&2) * x * y`] THEN
    ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; GSYM VECTOR_ADD_LDISTRIB] THEN
    SUBGOAL_THEN `2 EXP n <= p` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&p * inv(&2 pow n) = &(p - 2 EXP n) * inv(&2 pow n) + &1`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_POW] THEN
      ASM_SIMP_TAC[REAL_SUB_RDISTRIB; REAL_MUL_RINV; REAL_LT_IMP_NZ;
                   REAL_LT_POW2] THEN REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_ADD_RDISTRIB; REAL_ADD_RDISTRIB] THEN
      REWRITE_TAC[VECTOR_MUL_LID; REAL_MUL_LID] THEN
      REWRITE_TAC[VECTOR_ADD_ASSOC; REAL_ADD_ASSOC] THEN
      REWRITE_TAC[GSYM midpoint; GSYM real_div] THEN FIRST_X_ASSUM(fun th ->
        W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
      FIRST_X_ASSUM(fun th ->
        W(MP_TAC o PART_MATCH (lhand o rand) th o funpow 3 lhand o  snd)) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_ARITH_TAC; SIMP_TAC[] THEN REAL_ARITH_TAC]]]);;

let CONTINUOUS_MIDPOINT_CONVEX = prove
 (`!f:real^N->real s.
        (lift o f) continuous_on s /\ convex s /\
        (!x y. x IN s /\ y IN s ==> f(midpoint(x,y)) <= (f(x) + f(y)) / &2)
         ==> f convex_on s`,
  REWRITE_TAC[midpoint] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[convex_on] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ARITH `u + v = &1 <=> v = &1 - u`; IMP_CONJ] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; REAL_SUB_LE] THEN
  REWRITE_TAC[FORALL_DROP; GSYM DROP_VEC; IMP_IMP; GSYM IN_INTERVAL_1] THEN
  MP_TAC(ISPEC `interval[vec 0:real^1,vec 1]`
        CLOSURE_DYADIC_RATIONALS_IN_CONVEX_SET) THEN
  SIMP_TAC[CONVEX_INTERVAL; INTERIOR_CLOSED_INTERVAL;
           CLOSURE_CLOSED; CLOSED_INTERVAL; UNIT_INTERVAL_NONEMPTY] THEN
  REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop] THEN
  DISCH_THEN(fun th -> SUBST1_TAC(SYM th) THEN ASSUME_TAC th) THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a <= b <=> a - b <= &0`] THEN
  MATCH_MP_TAC CONTINUOUS_LE_ON_CLOSURE THEN
  REWRITE_TAC[IN_INTER; IMP_CONJ_ALT; FORALL_IN_GSPEC] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; GSYM FORALL_DROP; DROP_VEC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_ADD; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
     [REPLICATE_TAC 2 (ONCE_REWRITE_TAC[GSYM o_DEF]) THEN
      REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      CONJ_TAC THENL
       [ALL_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; GSYM FORALL_DROP;
                    DROP_VEC] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    SIMP_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST;
             LIFT_SUB; CONTINUOUS_ON_SUB];
    MAP_EVERY X_GEN_TAC [`n:num`; `i:real`] THEN
    ASM_SIMP_TAC[REAL_LE_MUL_EQ; REAL_LT_INV_EQ; REAL_LT_POW2] THEN
    ASM_CASES_TAC `&0 <= i` THEN ASM_SIMP_TAC[INTEGER_POS] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_POW2; REAL_MUL_LID] THEN
    GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV)
     [REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:real^N->real`; `s:real^N->bool`]
        MIDPOINT_CONVEX_DYADIC_RATIONALS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[midpoint] THEN REWRITE_TAC[VECTOR_ADD_LDISTRIB] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o SPECL
       [`n:num`; `m:num`; `2 EXP n - m`; `x:real^N`; `y:real^N`]) THEN
      ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_POW] THEN
      ASM_SIMP_TAC[REAL_LT_POW2; REAL_FIELD
       `&0 < y ==> (y - x) / y = &1 - x / y`] THEN
      REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Slightly shaper separating/supporting hyperplane results.                 *)
(* ------------------------------------------------------------------------- *)

let SEPARATING_HYPERPLANE_RELATIVE_INTERIORS = prove
 (`!s t. convex s /\ convex t /\
         ~(s = {} /\ t = (:real^N) \/ s = (:real^N) /\ t = {}) /\
         DISJOINT (relative_interior s) (relative_interior t)
         ==> ?a b. ~(a = vec 0) /\
                   (!x. x IN s ==> a dot x <= b) /\
                   (!x. x IN t ==> a dot x >= b)`,
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`s:real^N->bool = {}`; `t:real^N->bool = {}`] THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; UNIV_NOT_EMPTY; CONVEX_EMPTY;
                  RELATIVE_INTERIOR_EMPTY] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `basis 1:real^N` THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL];
    FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^N` o MATCH_MP (SET_RULE
     `~(s = UNIV) ==> ?a. ~(a IN s)`)) THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `x:real^N`]
        SEPARATING_HYPERPLANE_SET_POINT_INAFF) THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^N` o MATCH_MP (SET_RULE
     `~(s = UNIV) ==> ?a. ~(a IN s)`)) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`]
        SEPARATING_HYPERPLANE_SET_POINT_INAFF) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; real_ge] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`--a:real^N`; `--b:real`] THEN
    ASM_REWRITE_TAC[VECTOR_NEG_EQ_0; DOT_LNEG; REAL_LE_NEG2];
    MP_TAC(ISPECL [`relative_interior s:real^N->bool`;
                   `relative_interior t:real^N->bool`]
          SEPARATING_HYPERPLANE_SETS) THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY; CONVEX_RELATIVE_INTERIOR] THEN
    SIMP_TAC[real_ge] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `a:real^N` THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `b:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC
    (MESON[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_SUBSET; SUBSET]
      `convex s /\ (!x. x IN closure(relative_interior s) ==> P x)
       ==> !x. x IN s ==> P x`) THEN
    ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC CONTINUOUS_LE_ON_CLOSURE;
      MATCH_MP_TAC CONTINUOUS_GE_ON_CLOSURE] THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_LIFT_DOT]]);;

let SUPPORTING_HYPERPLANE_RELATIVE_BOUNDARY = prove
 (`!s x:real^N.
        convex s /\ x IN s /\ ~(x IN relative_interior s)
        ==> ?a. ~(a = vec 0) /\
                (!y. y IN s ==> a dot x <= a dot y) /\
                (!y. y IN relative_interior s ==> a dot x < a dot y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`relative_interior s:real^N->bool`; `x:real^N`]
        SEPARATING_HYPERPLANE_SET_POINT_INAFF) THEN
  ASM_SIMP_TAC[CONVEX_SING; CONVEX_RELATIVE_INTERIOR;
               RELATIVE_INTERIOR_EQ_EMPTY; real_ge] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`lift o (\x:real^N. a dot x)`;
                   `relative_interior s:real^N->bool`;
                   `y:real^N`; `(a:real^N) dot x`; `1`]
      CONTINUOUS_ON_CLOSURE_COMPONENT_GE) THEN
    REWRITE_TAC[CONTINUOUS_ON_LIFT_DOT; GSYM drop; o_THM; LIFT_DROP] THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR] THEN
    ASM_MESON_TAC[CLOSURE_SUBSET; REAL_LE_TRANS; SUBSET];
    DISCH_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `(y:real^N) IN relative_interior s` THEN
  REWRITE_TAC[IN_RELATIVE_INTERIOR_CBALL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; SUBSET; IN_INTER; IN_CBALL] THEN
  X_GEN_TAC `e:real` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `y + --(e / norm(a)) % ((x + a) - x):real^N`) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[NORM_ARITH `dist(y:real^N,y + e) = norm e`; VECTOR_ADD_SUB] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_NEG; REAL_ABS_DIV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `x IN s ==> s SUBSET t ==> x IN t`)) THEN
    MATCH_MP_TAC HULL_MONO THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; RELATIVE_INTERIOR_SUBSET];
    REWRITE_TAC[VECTOR_ADD_SUB] THEN DISCH_TAC THEN
    UNDISCH_TAC `!y:real^N. y IN s ==> a dot x <= a dot y` THEN
    DISCH_THEN(MP_TAC o SPEC `y + --(e / norm(a)) % a:real^N`) THEN
    ASM_REWRITE_TAC[DOT_RMUL; DOT_RNEG; DOT_RADD] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x * y ==> ~(a <= a + --x * y)`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; NORM_POS_LT; DOT_POS_LT]]);;

let SUPPORTING_HYPERPLANE_RELATIVE_FRONTIER = prove
 (`!s x:real^N.
        convex s /\ x IN closure s /\ ~(x IN relative_interior s)
        ==> ?a. ~(a = vec 0) /\
                (!y. y IN closure s ==> a dot x <= a dot y) /\
                (!y. y IN relative_interior s ==> a dot x < a dot y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`closure s:real^N->bool`; `x:real^N`]
    SUPPORTING_HYPERPLANE_RELATIVE_BOUNDARY) THEN
  ASM_SIMP_TAC[CONVEX_CLOSURE; CONVEX_RELATIVE_INTERIOR_CLOSURE]);;

(* ------------------------------------------------------------------------- *)
(* Containment of rays in unbounded convex sets.                             *)
(* ------------------------------------------------------------------------- *)

let UNBOUNDED_CONVEX_CLOSED_CONTAINS_RAY = prove
 (`!s a:real^N.
        convex s /\ ~bounded s /\ closed s /\ a IN s
        ==> ?l. ~(l = vec 0) /\ !t. &0 <= t ==> (a + t % l) IN s`,
  GEN_GEOM_ORIGIN_TAC `a:real^N` ["l"] THEN
  REWRITE_TAC[VECTOR_ADD_LID] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [BOUNDED_POS]) THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&n + &1:real`) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_ARITH `&0 < &n + &1`] THEN
  REWRITE_TAC[REAL_NOT_LE; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `x:num->real^N` THEN REWRITE_TAC[FORALL_AND_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!n. ~((x:num->real^N) n = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_ARITH `~(&n + &1 < norm(vec 0:real^N))`]; ALL_TAC] THEN
  MP_TAC(ISPEC `sphere(vec 0:real^N,&1)` compact) THEN
  REWRITE_TAC[COMPACT_SPHERE] THEN
  DISCH_THEN(MP_TAC o SPEC `\n. inv(norm(x n)) % (x:num->real^N) n`) THEN
  ASM_SIMP_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM;
               REAL_MUL_LINV; NORM_EQ_0; o_DEF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[NORM_ARITH `~(norm(vec 0:real^N) = &1)`]; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC CLOSED_CONTAINS_SEQUENTIAL_LIMIT THEN
  SUBGOAL_THEN
   `?N:num. !n. N <= n ==> t / norm(x n:real^N) <= &1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; NORM_POS_LT] THEN
    MP_TAC(SPEC `t:real` REAL_ARCH_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; REAL_MUL_LID] THEN
    ASM_MESON_TAC[REAL_ARITH `t <= m /\ m <= n /\ n + &1 < x ==> t <= x`];
    EXISTS_TAC `\n:num. t / norm((x:num->real^N)(r(N + n))) % x(r(N + n))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
      DISCH_THEN(MP_TAC o SPEC `vec 0:real^N`) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `N + n:num` o MATCH_MP MONOTONE_BIGGER) THEN
      ARITH_TAC;
      REWRITE_TAC[real_div; GSYM VECTOR_MUL_ASSOC] THEN
      MATCH_MP_TAC LIM_CMUL THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      FIRST_ASSUM(MP_TAC o SPEC `N:num` o MATCH_MP SEQ_OFFSET) THEN
      ASM_REWRITE_TAC[]]]);;

let CONVEX_CLOSED_CONTAINS_SAME_RAY = prove
 (`!s a b l:real^N.
        convex s /\ closed s /\ b IN s /\ (!t. &0 <= t ==> (a + t % l) IN s)
        ==> !t. &0 <= t ==> (b + t % l) IN s`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `&0`) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_IN_CLOSED_SET) THEN
  EXISTS_TAC `\n. (&1 - t / (&n + &1)) % b +
                  t / (&n + &1) % (a + (&n + &1) % l):real^N` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(SPEC `t:real` REAL_ARCH_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_ARITH `&0 <= &n + &1`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % b + u % c:real^N = b + u % (c - b)`] THEN
    MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC[LIM_CONST] THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_SUB_LDISTRIB] THEN
    SIMP_TAC[VECTOR_MUL_ASSOC; REAL_FIELD `t / (&n + &1) * (&n + &1) = t`] THEN
    SIMP_TAC[VECTOR_ARITH `(v % a + b) - v % c:real^N = b + v % (a - c)`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_ADD_RID] THEN
    MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC[LIM_CONST] THEN
    REWRITE_TAC[real_div; VECTOR_ARITH `(x * y) % a:real^N = y % x % a`] THEN
    MATCH_MP_TAC LIM_NULL_VMUL_BOUNDED THEN
    EXISTS_TAC `norm(t % (a - b):real^N)` THEN
    REWRITE_TAC[REAL_LE_REFL; EVENTUALLY_TRUE; o_DEF] THEN
    MP_TAC(MATCH_MP SEQ_OFFSET SEQ_HARMONIC) THEN
    SIMP_TAC[REAL_OF_NUM_ADD]]);;

let UNBOUNDED_CONVEX_CLOSED_CONTAINS_RAYS = prove
 (`!s:real^N->bool.
        convex s /\ ~bounded s /\ closed s
        ==> ?l. ~(l = vec 0) /\ !a t. a IN s /\ &0 <= t ==> (a + t % l) IN s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[BOUNDED_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_MESON_TAC[UNBOUNDED_CONVEX_CLOSED_CONTAINS_RAY;
                CONVEX_CLOSED_CONTAINS_SAME_RAY]);;

let RELATIVE_INTERIOR_UNBOUNDED_CONVEX_CONTAINS_RAY = prove
 (`!s a:real^N.
        convex s /\ ~bounded s /\ a IN relative_interior s
        ==> ?l. ~(l = vec 0) /\
                !t. &0 <= t ==> (a + t % l) IN relative_interior s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`closure s:real^N->bool`; `a:real^N`]
        UNBOUNDED_CONVEX_CLOSED_CONTAINS_RAY) THEN
  ASM_SIMP_TAC[CONVEX_CLOSURE; CLOSED_CLOSURE] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[BOUNDED_SUBSET; SUBSET; CLOSURE_SUBSET;
                  RELATIVE_INTERIOR_SUBSET];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
      `a + t % l:real^N =
       (a + (&2 * t) % l) - inv(&2) % ((a + (&2 * t) % l) - a)`] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let RELATIVE_INTERIOR_CONVEX_CONTAINS_SAME_RAY = prove
 (`!s a b l:real^N.
        convex s /\ b IN relative_interior s /\
        (!t. &0 <= t ==> (a + t % l) IN relative_interior s)
        ==> !t. &0 <= t ==> (b + t % l) IN relative_interior s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`closure s:real^N->bool`; `a:real^N`; `b:real^N`; `l:real^N`]
        CONVEX_CLOSED_CONTAINS_SAME_RAY) THEN
  ASM_SIMP_TAC[CONVEX_CLOSURE; CLOSED_CLOSURE] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[BOUNDED_SUBSET; SUBSET; CLOSURE_SUBSET;
                  RELATIVE_INTERIOR_SUBSET];
    DISCH_TAC THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
      `a + t % l:real^N =
       (a + (&2 * t) % l) - inv(&2) % ((a + (&2 * t) % l) - a)`] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let RELATIVE_INTERIOR_UNBOUNDED_CONVEX_CONTAINS_RAYS = prove
 (`!s:real^N->bool.
        convex s /\ ~bounded s
        ==> ?l. ~(l = vec 0) /\
                !a t. a IN relative_interior s /\ &0 <= t
                      ==> (a + t % l) IN relative_interior s`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `relative_interior s:real^N->bool = {}` THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; BOUNDED_EMPTY]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_MESON_TAC[RELATIVE_INTERIOR_UNBOUNDED_CONVEX_CONTAINS_RAY;
                RELATIVE_INTERIOR_CONVEX_CONTAINS_SAME_RAY]);;

(* ------------------------------------------------------------------------- *)
(* Explicit formulas for interior and relative interior of convex hull.      *)
(* ------------------------------------------------------------------------- *)

let EXPLICIT_SUBSET_RELATIVE_INTERIOR_CONVEX_HULL = prove
 (`!s. FINITE s
       ==> {y:real^N | ?u. (!x. x IN s ==> &0 < u x /\ u x < &1) /\
                           sum s u = &1 /\
                           vsum s (\x. u x % x) = y}
       SUBSET relative_interior(convex hull s)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SUM_CLAUSES; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[EMPTY_GSPEC; EMPTY_SUBSET] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RELATIVE_INTERIOR_MAXIMAL THEN
  REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN CONJ_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_FINITE; SUBSET; IN_ELIM_THM] THEN
    GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[open_in; IN_ELIM_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[AFFINE_HULL_FINITE; SUBSET; IN_ELIM_THM] THEN
    GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e = inf (IMAGE (\x:real^N. min (&1 - u x) (u x)) s)` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN
    ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    ASM_SIMP_TAC[REAL_LT_MIN; REAL_SUB_LT; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\z:real^N. z - y) (affine hull s)` BASIS_EXISTS) THEN
  REWRITE_TAC[SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool`
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `c:real^N->bool` (STRIP_ASSUME_TAC o GSYM))
                    MP_TAC)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; HAS_SIZE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[SPAN_FINITE; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `compo:real^N->real^N->real`) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o
    MATCH_MP BASIS_COORDINATES_LIPSCHITZ) THEN
  SUBGOAL_THEN
   `!i. i IN b ==> ?u. sum s u = &0 /\ vsum s (\x:real^N. u x % x) = i`
  MP_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN affine hull s` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[AFFINE_HULL_FINITE; IN_ELIM_THM]] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(\x. v x - u x):real^N->real` THEN
    ASM_SIMP_TAC[SUM_SUB; VSUM_SUB; VECTOR_SUB_RDISTRIB] THEN
    REWRITE_TAC[REAL_SUB_REFL; VECTOR_SUB_RZERO];
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [RIGHT_IMP_EXISTS_THM; SKOLEM_THM; FORALL_AND_THM;
                TAUT `(a ==> b /\ c) <=> (a ==> b) /\ (a ==> c)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->real^N->real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `e / B /
              (&1 + sum (b:real^N->bool)
                   (\i. abs(sup(IMAGE (abs o w i) (s:real^N->bool)))))` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 <= x ==> &0 < &1 + x`;
               SUM_POS_LE; REAL_ABS_POS] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  EXISTS_TAC
   `\x:real^N. u x + sum (b:real^N->bool)
                         (\i. compo (z:real^N) i * w i x)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[SUM_ADD; REAL_ARITH `&1 + x = &1 <=> x = &0`] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SUM_SWAP o lhand o snd) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_0 THEN
    ASM_SIMP_TAC[SUM_LMUL; ETA_AX; REAL_MUL_RZERO; SUM_0];
    ASM_SIMP_TAC[VSUM_ADD; VECTOR_ADD_RDISTRIB] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `y + w:real^N = z <=> w = z - y`] THEN
    ASM_SIMP_TAC[GSYM VSUM_LMUL; GSYM VSUM_RMUL; GSYM VECTOR_MUL_ASSOC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_SWAP o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[VSUM_LMUL] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `vsum b (\v:real^N. compo (z:real^N) v % v)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[]] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(x) < min u (&1 - u) ==> &0 < u + x /\ u + x < &1`) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
    `B * norm(z - y:real^N) * sum (b:real^N->bool)
                   (\i. abs(sup(IMAGE (abs o w i) (s:real^N->bool))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_ABS_LE THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_MUL_ASSOC] THEN
    X_GEN_TAC `i:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`(compo:real^N->real^N->real) z`;
                                  `i:real^N`]) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= abs a`) THEN
      ASM_SIMP_TAC[REAL_LE_SUP_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; o_THM] THEN ASM_MESON_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= x /\ x * (&1 + e) < d ==> x * e < d`) THEN
  REWRITE_TAC[NORM_POS_LE] THEN
  ASM_SIMP_TAC[NORM_POS_LE; GSYM REAL_LT_RDIV_EQ;
               REAL_ARITH `&0 <= x ==> &0 < &1 + x`;
               SUM_POS_LE; REAL_ABS_POS] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
   `dist(z:real^N,y) < k ==> k <= d ==> norm(z - y) < d`)) THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 <= x ==> &0 < &1 + x`;
               SUM_POS_LE; REAL_ABS_POS] THEN
  EXPAND_TAC "e" THEN
  ASM_SIMP_TAC[REAL_INF_LE_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN EXISTS_TAC `x:real^N` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let EXPLICIT_SUBSET_RELATIVE_INTERIOR_CONVEX_HULL_MINIMAL = prove
 (`!s. FINITE s
       ==> {y:real^N | ?u. (!x. x IN s ==> &0 < u x) /\
                           sum s u = &1 /\
                           vsum s (\x. u x % x) = y}
       SUBSET relative_interior(convex hull s)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SUM_CLAUSES; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[EMPTY_GSPEC; EMPTY_SUBSET] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `s = {a:real^N}` THENL
   [ASM_REWRITE_TAC[SUM_SING; VSUM_SING; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SING; CONVEX_HULL_SING] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN
    MESON_TAC[VECTOR_MUL_LID];
    FIRST_ASSUM(MP_TAC o MATCH_MP
      EXPLICIT_SUBSET_RELATIVE_INTERIOR_CONVEX_HULL) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `w:real^N` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->real` THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?y:real^N. y IN s /\ ~(y = x)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `sum {x,y} u <= sum s (u:real^N->real)` MP_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE; REAL_LT_IMP_LE; IN_DIFF] THEN
      ASM SET_TAC[];
      ASM_SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < y ==> x + y + &0 <= &1 ==> x < &1`) THEN
      ASM_SIMP_TAC[]]]);;

let RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT = prove
 (`!s. ~(affine_dependent s)
       ==> relative_interior(convex hull s) =
             {y:real^N | ?u. (!x. x IN s ==> &0 < u x) /\
                             sum s u = &1 /\
                             vsum s (\x. u x % x) = y}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[EXPLICIT_SUBSET_RELATIVE_INTERIOR_CONVEX_HULL_MINIMAL] THEN
  ASM_CASES_TAC `?a:real^N. s = {a}` THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN
    ASM_REWRITE_TAC[SUM_SING; VSUM_SING; CONVEX_HULL_SING;
                    RELATIVE_INTERIOR_SING] THEN
    REWRITE_TAC[IN_ELIM_THM; SUBSET; IN_SING] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `\x:real^N. &1` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; REAL_LT_01];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `relative_interior s SUBSET s /\
    (!x. x IN s /\ ~(x IN t) ==> ~(x IN relative_interior s))
    ==> relative_interior s SUBSET t`) THEN
  REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_RELATIVE_INTERIOR] THEN
  REWRITE_TAC[AFFINE_HULL_CONVEX_HULL; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC)
   (MP_TAC o SPEC `u:real^N->real`)) THEN
  ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; IN_RELATIVE_INTERIOR; DE_MORGAN_THM;
                  SUBSET; IN_ELIM_THM; IN_BALL; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN DISJ2_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))) THEN
  SUBGOAL_THEN `(u:real^N->real) a = &0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`]; ALL_TAC] THEN
  SUBGOAL_THEN `?b:real^N. b IN s /\ ~(b = a)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[];ALL_TAC] THEN
  SUBGOAL_THEN `?d. &0 < d /\ norm(d % (a - b):real^N) < e`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `e / &2 / norm(a - b:real^N)` THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; NORM_POS_LT;
                 REAL_ABS_DIV; REAL_ABS_NORM; REAL_ABS_NUM;
                 REAL_DIV_RMUL; REAL_LT_IMP_NZ; VECTOR_SUB_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `y - d % (a - b):real^N`) THEN
  ASM_REWRITE_TAC[NORM_ARITH `dist(a:real^N,a - b) = norm b`] THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [MATCH_MP_TAC IN_AFFINE_SUB_MUL_DIFF THEN
    ASM_SIMP_TAC[HULL_INC; AFFINE_AFFINE_HULL] THEN
    REWRITE_TAC[AFFINE_HULL_FINITE; IN_ELIM_THM] THEN
    EXISTS_TAC `u:real^N->real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~(affine_dependent(s:real^N->bool))` THEN
  ASM_SIMP_TAC[AFFINE_DEPENDENT_EXPLICIT_FINITE] THEN
  EXISTS_TAC `\x:real^N. (v x - u x) -
                   (if x = a then --d else if x = b then d else &0)` THEN
  REWRITE_TAC[VECTOR_SUB_RDISTRIB; MESON[]
   `(if p then a else b) % x = (if p then a % x else b % x)`] THEN
  ASM_SIMP_TAC[SUM_SUB; VSUM_SUB] THEN
  ASM_SIMP_TAC[VSUM_CASES; SUM_CASES; FINITE_RESTRICT; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[SET_RULE `a IN s ==> {x | x IN s /\ x = a} = {a}`;
   SET_RULE `b IN s /\ ~(b = a)
             ==> {x | (x IN s /\ ~(x = a)) /\ x = b} = {b}`] THEN
  ASM_SIMP_TAC[VECTOR_MUL_LZERO; SUM_0; VSUM_0; SUM_SING; VSUM_SING] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
  EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let EXPLICIT_SUBSET_INTERIOR_CONVEX_HULL = prove
 (`!s. FINITE s /\ affine hull s = (:real^N)
       ==> {y | ?u. (!x. x IN s ==> &0 < u x /\ u x < &1) /\
                    sum s u = &1 /\
                    vsum s (\x. u x % x) = y}
           SUBSET interior(convex hull s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o
    MATCH_MP EXPLICIT_SUBSET_RELATIVE_INTERIOR_CONVEX_HULL) THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_INTERIOR; AFFINE_HULL_CONVEX_HULL]);;

let EXPLICIT_SUBSET_INTERIOR_CONVEX_HULL_MINIMAL = prove
 (`!s. FINITE s /\ affine hull s = (:real^N)
       ==> {y | ?u. (!x. x IN s ==> &0 < u x) /\
                    sum s u = &1 /\
                    vsum s (\x. u x % x) = y}
           SUBSET interior(convex hull s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o
    MATCH_MP EXPLICIT_SUBSET_RELATIVE_INTERIOR_CONVEX_HULL_MINIMAL) THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_INTERIOR; AFFINE_HULL_CONVEX_HULL]);;

let INTERIOR_CONVEX_HULL_EXPLICIT_MINIMAL = prove
 (`!s:real^N->bool.
        ~(affine_dependent s)
        ==> interior(convex hull s) =
             if CARD(s) <= dimindex(:N) then {}
              else {y | ?u. (!x. x IN s ==> &0 < u x) /\
                            sum s u = &1 /\
                            vsum s (\x. u x % x) = y}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[EMPTY_INTERIOR_CONVEX_HULL] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `relative_interior(convex hull s):real^N->bool` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
    REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN
    MATCH_MP_TAC AFFINE_INDEPENDENT_SPAN_GT THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT]]);;

let INTERIOR_CONVEX_HULL_EXPLICIT = prove
 (`!s:real^N->bool.
        ~(affine_dependent s)
        ==> interior(convex hull s) =
             if CARD(s) <= dimindex(:N) then {}
              else {y | ?u. (!x. x IN s ==> &0 < u x /\ u x < &1) /\
                            sum s u = &1 /\
                            vsum s (\x. u x % x) = y}`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_EXPLICIT_MINIMAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
 REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `v:real^N` THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `u:real^N->real` THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` CHOOSE_SUBSET) THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
  DISCH_THEN(MP_TAC o SPEC `2`) THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `~(c <= n) ==> 1 <= n ==> 2 <= c`)) THEN
    REWRITE_TAC[DIMINDEX_GE_1];
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
        STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?y:real^N. y IN s /\ ~(y = x)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sum {x,y} u <= sum s (u:real^N->real)` MP_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE; REAL_LT_IMP_LE; IN_DIFF] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < y ==> x + y + &0 <= &1 ==> x < &1`) THEN
  ASM_SIMP_TAC[]);;

let DISJOINT_RELATIVE_INTERIOR_CONVEX_HULL = prove
 (`!s:real^N->bool.
        ~affine_dependent s /\ ~(?a. s = {a})
        ==> relative_interior(convex hull s) INTER s = {}`,
  REWRITE_TAC[SET_RULE `s INTER t = {} <=> !x. x IN t ==> ~(x IN s)`] THEN
  GEN_TAC THEN REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  X_GEN_TAC `z:real^N` THEN GEOM_ORIGIN_TAC `z:real^N` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN
  FIRST_X_ASSUM(fun th ->
   STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [AFFINE_INDEPENDENT_IFF_CARD] th) THEN
   MP_TAC th) THEN
  ASM_SIMP_TAC[AFFINE_DEPENDENT_EXPLICIT_FINITE; CONTRAPOS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x. (if x = vec 0 then -- &1 else &0) + (u:real^N->real) x` THEN
  ASM_SIMP_TAC[VECTOR_ADD_RDISTRIB; VSUM_ADD; SUM_ADD] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; VECTOR_MUL_LZERO] THEN
  ASM_SIMP_TAC[SUM_DELTA; VSUM_DELTA; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_LID] THEN MATCH_MP_TAC(MESON[]
   `(?x. ~(x = a) /\ q x) ==> ?x. if x = a then p x else q x`) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `~(?a. s = {a}) ==> vec 0 IN s ==> ?b. ~(b = vec 0) /\ b IN s`)) THEN
  ASM_MESON_TAC[REAL_LT_IMP_NZ]);;

let INTERIOR_CONVEX_HULL_3_MINIMAL = prove
 (`!a b c:real^2.
        ~collinear{a,b,c}
        ==> interior(convex hull {a,b,c}) =
                {v | ?x y z. &0 < x /\
                             &0 < y /\
                             &0 < z /\
                             x + y + z = &1 /\
                             x % a + y % b + z % c = v}`,
  REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_EXPLICIT_MINIMAL] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  CONV_TAC(LAND_CONV(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV(REWRITE_CONV
   [IN_INSERT; NOT_IN_EMPTY]))))) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; ARITH] THEN
  SIMP_TAC[FINITE_INSERT; FINITE_UNION; FINITE_EMPTY; RIGHT_EXISTS_AND_THM;
           AFFINE_HULL_FINITE_STEP_GEN; REAL_LT_ADD; REAL_HALF] THEN
  REWRITE_TAC[REAL_ARITH `&1 - a - b - c = &0 <=> a + b + c = &1`;
         VECTOR_ARITH `y - a - b - c:real^N = vec 0 <=> a + b + c = y`]);;

let INTERIOR_CONVEX_HULL_3 = prove
 (`!a b c:real^2.
        ~collinear{a,b,c}
        ==> interior(convex hull {a,b,c}) =
                {v | ?x y z. &0 < x /\ x < &1 /\
                             &0 < y /\ y < &1 /\
                             &0 < z /\ z < &1 /\
                             x + y + z = &1 /\
                             x % a + y % b + z % c = v}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3_MINIMAL] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Similar results for closure and (relative or absolute) frontier.          *)
(* ------------------------------------------------------------------------- *)

let CLOSURE_CONVEX_HULL = prove
 (`!s. compact s ==> closure(convex hull s) = convex hull s`,
  SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED; COMPACT_CONVEX_HULL]);;

let RELATIVE_FRONTIER_CONVEX_HULL_EXPLICIT = prove
 (`!s:real^N->bool.
        ~(affine_dependent s)
        ==> relative_frontier(convex hull s) =
                {y | ?u. (!x. x IN s ==> &0 <= u x) /\
                         (?x. x IN s /\ u x = &0) /\
                         sum s u = &1 /\
                         vsum s (\x. u x % x) = y}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[relative_frontier; UNIONS_GSPEC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  ASM_SIMP_TAC[CLOSURE_CONVEX_HULL; FINITE_IMP_COMPACT] THEN
  ASM_SIMP_TAC[CONVEX_HULL_FINITE; RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^N->real`) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> (~(&0 < x) <=> x = &0)`] THEN
    DISCH_TAC THEN EXISTS_TAC `u:real^N->real` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->real`
     (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    CONJ_TAC THENL
     [EXISTS_TAC `u:real^N->real` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [AFFINE_DEPENDENT_EXPLICIT]) THEN
    REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC
     [`s:real^N->bool`; `(\x. u x - v x):real^N->real`] THEN
    ASM_SIMP_TAC[SUBSET_REFL; VECTOR_SUB_RDISTRIB; SUM_SUB; VSUM_SUB] THEN
    REWRITE_TAC[REAL_SUB_0; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[REAL_LT_REFL]]);;

let FRONTIER_CONVEX_HULL_EXPLICIT = prove
 (`!s:real^N->bool.
        ~(affine_dependent s)
        ==> frontier(convex hull s) =
                {y | ?u. (!x. x IN s ==> &0 <= u x) /\
                         (dimindex(:N) < CARD s ==> ?x. x IN s /\ u x = &0) /\
                         sum s u = &1 /\
                         vsum s (\x. u x % x) = y}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  DISJ_CASES_TAC
   (ARITH_RULE `CARD(s:real^N->bool) <= dimindex(:N) \/
                dimindex(:N) < CARD(s:real^N->bool)`)
  THENL
   [ASM_SIMP_TAC[GSYM NOT_LE; INTERIOR_CONVEX_HULL_EXPLICIT] THEN
    ASM_SIMP_TAC[CLOSURE_CONVEX_HULL; FINITE_IMP_COMPACT; DIFF_EMPTY] THEN
    REWRITE_TAC[CONVEX_HULL_FINITE];
    ASM_SIMP_TAC[GSYM RELATIVE_FRONTIER_CONVEX_HULL_EXPLICIT] THEN
    REWRITE_TAC[relative_frontier] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
    MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ s = UNIV ==> t = UNIV`) THEN
    EXISTS_TAC `affine hull s:real^N->bool` THEN
    ASM_SIMP_TAC[AFFINE_INDEPENDENT_SPAN_GT; HULL_MONO; HULL_SUBSET]]);;

let RELATIVE_FRONTIER_CONVEX_HULL_CASES = prove
 (`!s:real^N->bool.
        ~(affine_dependent s)
        ==> relative_frontier(convex hull s) =
                UNIONS { convex hull (s DELETE a) |a| a IN s }`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNIONS_GSPEC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_CONVEX_HULL_EXPLICIT] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; CONVEX_HULL_FINITE] THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:real^N->real` THEN
    ASM_SIMP_TAC[IN_DELETE; SUM_DELETE; VSUM_DELETE; REAL_SUB_RZERO] THEN
    VECTOR_ARITH_TAC;
    REWRITE_TAC[IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `(\x. if x = a then &0 else u x):real^N->real` THEN
    ASM_SIMP_TAC[COND_RAND; COND_RATOR; REAL_LE_REFL; COND_ID] THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CASES; VSUM_CASES; VECTOR_MUL_LZERO] THEN
    ASM_SIMP_TAC[GSYM DELETE; SUM_0; VSUM_0; REAL_ADD_LID; VECTOR_ADD_LID]]);;

let FRONTIER_CONVEX_HULL_CASES = prove
 (`!s:real^N->bool.
        ~(affine_dependent s)
        ==> frontier(convex hull s) =
                if CARD(s) <= dimindex(:N) then convex hull s
                else UNIONS { convex hull (s DELETE a) |a| a IN s }`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  ASM_SIMP_TAC[frontier; CLOSURE_CONVEX_HULL; FINITE_IMP_COMPACT] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_EXPLICIT; DIFF_EMPTY]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM RELATIVE_FRONTIER_CONVEX_HULL_CASES] THEN
  ASM_SIMP_TAC[relative_frontier; frontier;
               CLOSURE_CONVEX_HULL; FINITE_IMP_COMPACT] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
  MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
  MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ s = UNIV ==> t = UNIV`) THEN
  EXISTS_TAC `affine hull s:real^N->bool` THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_SPAN_GT; HULL_MONO; HULL_SUBSET]);;

let IN_FRONTIER_CONVEX_HULL = prove
 (`!s x:real^N.
        FINITE s /\ CARD s <= dimindex(:N) + 1 /\ x IN s
        ==> x IN frontier(convex hull s)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `affine_dependent(s:real^N->bool)` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [affine_dependent]) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CONVEX_HULL; FINITE_IMP_COMPACT] THEN
    ASM_SIMP_TAC[HULL_INC; IN_DIFF] THEN MATCH_MP_TAC(SET_RULE
     `!t. s SUBSET t /\ t = {} ==> ~(x IN s)`) THEN
    EXISTS_TAC `interior(affine hull s):real^N->bool` THEN
    SIMP_TAC[SUBSET_INTERIOR; CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
    SUBGOAL_THEN `s = (a:real^N) INSERT (s DELETE a)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[HULL_REDUNDANT] THEN
    MATCH_MP_TAC EMPTY_INTERIOR_AFFINE_HULL THEN
    ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[FRONTIER_CONVEX_HULL_CASES] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[HULL_INC] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    SUBGOAL_THEN `?y:real^N. y IN s /\ ~(y = x)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `x IN s ==> ~(s = {x}) ==> ?y. y IN s /\ ~(y = x)`)) THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LE]) THEN
      ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      REWRITE_TAC[NOT_LT; NOT_IN_EMPTY; ARITH_SUC; DIMINDEX_GE_1];
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]]]);;

let NOT_IN_INTERIOR_CONVEX_HULL = prove
 (`!s x:real^N.
        FINITE s /\ CARD s <= dimindex(:N) + 1 /\ x IN s
        ==> ~(x IN interior(convex hull s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP IN_FRONTIER_CONVEX_HULL) THEN
  SIMP_TAC[frontier; IN_DIFF]);;

let INTERIOR_CONVEX_HULL_EQ_EMPTY = prove
 (`!s:real^N->bool.
        s HAS_SIZE (dimindex(:N) + 1)
        ==> (interior(convex hull s) = {} <=> affine_dependent s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
  ASM_CASES_TAC `affine_dependent(s:real^N->bool)` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [affine_dependent]) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CONVEX_HULL; FINITE_IMP_COMPACT] THEN
    ASM_SIMP_TAC[HULL_INC; IN_DIFF] THEN MATCH_MP_TAC(SET_RULE
     `!t. s SUBSET t /\ t = {} ==> s = {}`) THEN
    EXISTS_TAC `interior(affine hull s):real^N->bool` THEN
    SIMP_TAC[SUBSET_INTERIOR; CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
    SUBGOAL_THEN `s = (a:real^N) INSERT (s DELETE a)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[HULL_REDUNDANT] THEN
    MATCH_MP_TAC EMPTY_INTERIOR_AFFINE_HULL THEN
    ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_EXPLICIT_MINIMAL] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; ARITH_RULE `~(n + 1 <= n)`] THEN
    EXISTS_TAC `vsum s (\x:real^N. inv(&(dimindex(:N)) + &1) % x)` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `\x:real^N. inv(&(dimindex(:N)) + &1)` THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    ASM_SIMP_TAC[SUM_CONST; GSYM REAL_OF_NUM_ADD] THEN
    CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Similar things in special case (could use above as lemmas here instead).  *)
(* ------------------------------------------------------------------------- *)

let SIMPLEX_EXPLICIT = prove
 (`!s:real^N->bool.
        FINITE s /\ ~(vec 0 IN s)
        ==> convex hull (vec 0 INSERT s) =
            { y | ?u. (!x. x IN s ==> &0 <= u x) /\
                      sum s u <= &1 /\
                      vsum s (\x. u x % x) = y}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CONVEX_HULL_FINITE; FINITE_INSERT] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN
  ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; IN_INSERT] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `u:real^N->real` THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^N`) THEN REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    EXISTS_TAC `\x:real^N. if x = vec 0 then &1 - sum (s:real^N->bool) u
                           else u(x)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
      ASM_REWRITE_TAC[REAL_SUB_LE];
      MATCH_MP_TAC(REAL_ARITH `s = t ==> &1 - s + t = &1`) THEN
      MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC VSUM_EQ THEN ASM_MESON_TAC[]]]);;

let STD_SIMPLEX = prove
 (`convex hull (vec 0 INSERT { basis i | 1 <= i /\ i <= dimindex(:N)}) =
        {x:real^N | (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i) /\
                    sum (1..dimindex(:N)) (\i. x$i) <= &1 }`,
  W(MP_TAC o PART_MATCH (lhs o rand) SIMPLEX_EXPLICIT o lhs o snd) THEN ANTS_TAC THENL
   [REWRITE_TAC[SIMPLE_IMAGE; GSYM IN_NUMSEG] THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IN_IMAGE] THEN
    REWRITE_TAC[IN_NUMSEG] THEN MESON_TAC[BASIS_NONZERO];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXTENSION] THEN
  ONCE_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[SIMPLE_IMAGE; GSYM IN_NUMSEG] THEN
  SUBGOAL_THEN `!u. sum (IMAGE (basis:num->real^N) (1..dimindex(:N))) u =
                        sum (1..dimindex(:N)) (u o basis)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC SUM_IMAGE THEN REWRITE_TAC[IN_NUMSEG] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; BASIS_INJ];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. vsum (IMAGE (basis:num->real^N) (1..dimindex(:N))) u =
                        vsum (1..dimindex(:N)) ((u:real^N->real^N) o basis)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC VSUM_IMAGE THEN REWRITE_TAC[IN_NUMSEG] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; BASIS_INJ; FINITE_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; BASIS_EXPANSION_UNIQUE; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_NUMSEG] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x <= &1 ==> x = y ==> y <= &1`)) THEN
    MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[IN_NUMSEG];
    STRIP_TAC THEN EXISTS_TAC `\y:real^N. y dot x` THEN
    ASM_SIMP_TAC[DOT_BASIS]]);;

let INTERIOR_STD_SIMPLEX = prove
 (`interior
    (convex hull (vec 0 INSERT { basis i | 1 <= i /\ i <= dimindex(:N)})) =
        {x:real^N | (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 < x$i) /\
                    sum (1..dimindex(:N)) (\i. x$i) < &1 }`,
  REWRITE_TAC[EXTENSION; IN_INTERIOR; IN_ELIM_THM; STD_SIMPLEX] THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:real^N`) THEN REWRITE_TAC[DIST_REFL] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_LE] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x - (e / &2) % basis k:real^N`) THEN
      REWRITE_TAC[NORM_ARITH `dist(x,x - e) = norm(e)`; NORM_MUL] THEN
      ASM_SIMP_TAC[NORM_BASIS; REAL_ARITH `&0 < e ==> abs(e / &2) * &1 < e`;
                   VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[BASIS_COMPONENT] THEN UNDISCH_TAC `&0 < e` THEN
      REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `x + (e / &2) % basis 1:real^N`) THEN
      REWRITE_TAC[NORM_ARITH `dist(x,x + e) = norm(e)`; NORM_MUL] THEN
      ASM_SIMP_TAC[NORM_BASIS; LE_REFL; DIMINDEX_GE_1] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs(e / &2) * &1 < e`] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      MATCH_MP_TAC(REAL_ARITH `x < y ==> y <= &1 ==> ~(x = &1)`) THEN
      MATCH_MP_TAC SUM_LT THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> ~(a /\ b ==> ~c)`] THEN
      SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
               BASIS_COMPONENT] THEN
      CONJ_TAC THENL
       [GEN_TAC THEN COND_CASES_TAC;
        EXISTS_TAC `1` THEN REWRITE_TAC[LE_REFL; DIMINDEX_GE_1]] THEN
      ASM_REAL_ARITH_TAC];
    STRIP_TAC THEN
    EXISTS_TAC
     `min (inf(IMAGE (\i. (x:real^N)$i) (1..dimindex(:N))))
          ((&1 - sum (1..dimindex(:N)) (\i. x$i)) / &(dimindex(:N)))` THEN
    ASM_SIMP_TAC[REAL_LT_MIN] THEN
    SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; FINITE_NUMSEG;
             IMAGE_EQ_EMPTY; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < x <=> 1 <= x`; DIMINDEX_GE_1] THEN
    ASM_REWRITE_TAC[IN_NUMSEG; REAL_MUL_LZERO; REAL_SUB_LT] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN X_GEN_TAC `y:real^N` THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
      DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `abs(xk - yk) <= d ==> d < xk ==> &0 <= yk`);
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV)
       [GSYM CARD_NUMSEG_1] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      SIMP_TAC[GSYM SUM_CONST; FINITE_NUMSEG] THEN
      MATCH_MP_TAC(REAL_ARITH
       `s2 <= s0 + s1 ==> s0 < &1 - s1 ==> s2 <= &1`) THEN
      REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
      MATCH_MP_TAC SUM_LE_NUMSEG THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `abs(y - x) <= z ==> x <= z + y`)] THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; dist; COMPONENT_LE_NORM]]);;

(* ------------------------------------------------------------------------- *)
(* Barycentres.                                                              *)
(* ------------------------------------------------------------------------- *)

let barycentre = new_definition
  `barycentre s =
     if FINITE s then vsum s (\x. inv(&(CARD s)) % x) else vec 0`;;

let BARYCENTRE_0 = prove
 (`barycentre {} = vec 0`,
  REWRITE_TAC[barycentre; FINITE_EMPTY; VSUM_CLAUSES]);;

let BARYCENTRE_1 = prove
 (`!a:real^N. barycentre {a} = a`,
  REWRITE_TAC[barycentre; VSUM_SING; FINITE_SING; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[CARD_SING; REAL_INV_1; VECTOR_MUL_LID]);;

let BARYCENTRE_2 = prove
 (`!a b:real^N. barycentre {a,b} = midpoint(a,b)`,
  SIMP_TAC[barycentre; FINITE_INSERT; FINITE_EMPTY; NOT_INSERT_EMPTY;
           VSUM_CLAUSES; NOT_IN_EMPTY; IN_SING; midpoint] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RULES; IN_SING; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC VECTOR_ARITH);;

let BARYCENTRE_IN_RELATIVE_INTERIOR = prove
 (`!s:real^N->bool.
        FINITE s /\ ~(s = {})
        ==> (barycentre s) IN relative_interior(convex hull s)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o  REWRITE_RULE[SUBSET] o
    MATCH_MP EXPLICIT_SUBSET_RELATIVE_INTERIOR_CONVEX_HULL_MINIMAL) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  EXISTS_TAC `\x:real^N. inv(&(CARD(s:real^N->bool)))` THEN
  ASM_SIMP_TAC[SUM_CONST; barycentre; REAL_LT_INV_EQ] THEN
  REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  ASM_SIMP_TAC[CARD_EQ_0; REAL_OF_NUM_EQ; REAL_MUL_RINV]);;

let BARYCENTRE_IN_CONVEX_HULL = prove
 (`!s:real^N->bool.
        FINITE s /\ ~(s = {}) ==> (barycentre s) IN (convex hull s)`,
  MESON_TAC[BARYCENTRE_IN_RELATIVE_INTERIOR; SUBSET;
            RELATIVE_INTERIOR_SUBSET]);;

let BARYCENTRE_IN_AFFINE_HULL = prove
 (`!s:real^N->bool.
        FINITE s /\ ~(s = {}) ==> (barycentre s) IN (affine hull s)`,
  MESON_TAC[BARYCENTRE_IN_CONVEX_HULL; SUBSET;
            CONVEX_HULL_SUBSET_AFFINE_HULL]);;

let BARYCENTRE_TRANSLATION = prove
 (`!a:real^N s.
        barycentre (IMAGE (\x. a + x) s) =
        (if FINITE s /\ ~(s = {}) then a else vec 0) + barycentre s`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[BARYCENTRE_0; IMAGE_CLAUSES; VECTOR_ADD_RID] THEN
  REWRITE_TAC[barycentre] THEN
  SIMP_TAC[FINITE_IMAGE_INJ_EQ; CARD_IMAGE_INJ; VSUM_IMAGE; VECTOR_ARITH
   `a + x:real^N = a + y <=> x = y`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_ADD_RID] THEN
  ASM_SIMP_TAC[o_DEF; VECTOR_ADD_LDISTRIB; VSUM_ADD; VSUM_CONST] THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; CARD_EQ_0; REAL_OF_NUM_EQ;
               VECTOR_MUL_LID]);;

add_translation_invariants [BARYCENTRE_TRANSLATION];;

let BARYCENTRE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> barycentre (IMAGE f s) = f(barycentre s)`,
  REWRITE_TAC[INJECTIVE_ALT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[barycentre; IMAGE_EQ_EMPTY; FINITE_IMAGE_INJ_EQ;
               CARD_IMAGE_INJ; VSUM_IMAGE] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[LINEAR_0]] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; o_DEF] THEN MATCH_MP_TAC VSUM_EQ THEN
  ASM_MESON_TAC[LINEAR_CMUL]);;

add_linear_invariants [BARYCENTRE_LINEAR_IMAGE];;

let BARYCENTRE_NOT_IN_SET = prove
 (`!s:real^N->bool.
        ~affine_dependent s /\ ~(?a. s = {a}) ==> ~(barycentre s IN s)`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DISJOINT_RELATIVE_INTERIOR_CONVEX_HULL) THEN
  MATCH_MP_TAC(SET_RULE `b IN i ==> i INTER s = {} ==> ~(b IN s)`) THEN
  MATCH_MP_TAC BARYCENTRE_IN_RELATIVE_INTERIOR THEN
  ASM_MESON_TAC[AFFINE_INDEPENDENT_IFF_CARD]);;

(* ------------------------------------------------------------------------- *)
(* Construction of regular polyhedra with given parameters.                  *)
(* ------------------------------------------------------------------------- *)

let REGULAR_POLYTOPE_DIST_BARYCENTRE = prove
 (`!s:real^N->bool n r.
        s HAS_SIZE n /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> dist(x,y) = r)
        ==> !x. x IN s
                ==> dist(barycentre s,x) = sqrt((&n - &1) / (&2 * &n)) * r`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 <= r` THENL
   [POP_ASSUM MP_TAC;
    ASM_SIMP_TAC[NORM_ARITH `~(&0 <= r) ==> ~(dist(x,y) = r)`] THEN
    ASM_CASES_TAC `(?a:real^N. s = {a})` THENL [ALL_TAC; ASM SET_TAC[]] THEN
    FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC[HAS_SIZE; CARD_SING] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[BARYCENTRE_1; IN_SING; SQRT_0; DIST_REFL;
                 REAL_MUL_LZERO]] THEN
  ABBREV_TAC `z:real^N = barycentre s` THEN
  POP_ASSUM MP_TAC THEN GEOM_ORIGIN_TAC `z:real^N` THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `FINITE(s:real^N->bool)` THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  REWRITE_TAC[VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
  ASM_SIMP_TAC[barycentre] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN STRIP_TAC THEN MP_TAC th) THEN
  ASM_CASES_TAC `n = 0` THENL [ASM_MESON_TAC[CARD_EQ_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[VSUM_LMUL; VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_OF_NUM_EQ] THEN
  STRIP_TAC THEN SUBGOAL_THEN
   `!x. x IN s
        ==> sum s (\y:real^N. dist(x,y) pow 2) = (&n - &1) * r pow 2`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    TRANS_TAC EQ_TRANS `sum s (\y:real^N. if y = x then &0 else r pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[DIST_REFL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ASM_SIMP_TAC[SUM_CASES; GSYM DELETE; SUM_0; SUM_CONST; FINITE_DELETE;
                   REAL_ADD_LID; CARD_DELETE; GSYM REAL_OF_NUM_SUB; LE_1]];
      REWRITE_TAC[DIST_0] THEN REWRITE_TAC[dist; NORM_POW_2] THEN
      REWRITE_TAC[VECTOR_ARITH
       `(x - y:real^N) dot (x - y) = x dot x - &2 * x dot y + y dot y`] THEN
      ASM_SIMP_TAC[SUM_SUB; SUM_ADD; SUM_CONST; SUM_LMUL] THEN
      ASM_SIMP_TAC[GSYM DOT_RSUM; DOT_RZERO; REAL_ARITH
       `x - &2 * &0 + y = x + y`] THEN
      DISCH_THEN(LABEL_TAC "*")] THEN
  ASM_REWRITE_TAC[NORM_EQ_SQUARE] THEN
  SUBGOAL_THEN `sum s (\x. &n * (x dot x) + sum s (\y. y dot y)) =
                sum s (\x:real^N. (&n - &1) * r pow 2)`
  MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; SUM_CONST; REAL_OF_NUM_EQ; REAL_RING
   `n * s + n * s = (n - &1) * n * r <=> n = &0 \/ s = (n - &1) * r / &2`] THEN
  DISCH_TAC THEN REMOVE_THEN "*" MP_TAC THEN
  ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
  `~(n = &0) ==> (n * x + a * r / &2 = a * r <=> x = (a / (&2 * n)) * r)`] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[REAL_POW_MUL] THEN
  REWRITE_TAC[REAL_RING `x * r:real = y * r <=> y = x \/ r = &0`] THEN
  REWRITE_TAC[SQRT_POW2] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[SQRT_LE_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_POS; REAL_SUB_LE; REAL_OF_NUM_LE;
               LE_1]);;

let REGULAR_POLYTOPE_EXISTS = prove
 (`!r s:real^N->bool n.
       &n <= aff_dim s + &1 /\ &0 < r
       ==> ?k. k HAS_SIZE n /\ ~affine_dependent k /\ k SUBSET affine hull s /\
               (!x y. x IN k /\ y IN k /\ ~(x = y) ==> dist(x,y) = r)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[HAS_SIZE_0; UNWIND_THM2; AFFINE_INDEPENDENT_EMPTY] THEN
  REWRITE_TAC[EMPTY_SUBSET; NOT_IN_EMPTY; GSYM INT_OF_NUM_SUC] THEN
  DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN STRIP_ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `n = 0` THENL
   [UNDISCH_TAC `&n + &1 <= aff_dim(s:real^N->bool) + &1` THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THENL [INT_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN EXISTS_TAC `{a:real^N}` THEN
    ASM_SIMP_TAC[ARITH; AFFINE_INDEPENDENT_1; SING_SUBSET; HULL_INC] THEN
    REWRITE_TAC[HAS_SIZE_CONV `s HAS_SIZE 1`] THEN SET_TAC[];
    ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  ABBREV_TAC `z:real^N = barycentre k` THEN
  POP_ASSUM MP_TAC THEN GEOM_ORIGIN_TAC `z:real^N` THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `FINITE(k:real^N->bool)` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[HAS_SIZE]] THEN
  ASM_CASES_TAC `k:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[HAS_SIZE; CARD_CLAUSES] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `a + x:real^N = a + v <=> x = v`] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `n:num`; `r:real`]
        REGULAR_POLYTOPE_DIST_BARYCENTRE) THEN
  ASM_REWRITE_TAC[DIST_0] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `s:real^N->bool`]
        ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN) THEN
  MP_TAC(ISPEC `k:real^N->bool` BARYCENTRE_IN_AFFINE_HULL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(vec 0:real^N) IN affine hull s` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; HULL_HULL; HULL_MONO]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM AFFINE_HULL_EQ_SPAN] THEN ANTS_TAC THENL
   [REWRITE_TAC[PSUBSET] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[HULL_HULL; HULL_MONO]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
     MATCH_MP (INT_ARITH `n + &1:int <= s + &1 ==> k <= n - &1
                ==> ~(k = s)`)) THEN
    ASM_MESON_TAC[AFF_DIM_LE_CARD; HAS_SIZE];
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC
   `b = (sqrt((&n + &1) / (&2 * &n)) * r) % inv(norm a) % a:real^N` THEN
  EXISTS_TAC `(b:real^N) INSERT k` THEN
  SUBGOAL_THEN `norm(b:real^N) = sqrt((&n + &1) / (&2 * &n)) * r`
  ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_LE_0] THEN
    SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_LE_ADD; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(b:real^N = vec 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM NORM_EQ_0; REAL_ENTIRE; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[SQRT_EQ_0; REAL_DIV_EQ_0] THEN
    REWRITE_TAC[REAL_ENTIRE; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN affine hull k ==> orthogonal b y`
  ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[ORTHOGONAL_MUL] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^N) IN affine hull s` ASSUME_TAC THENL
   [SUBST1_TAC(VECTOR_ARITH `b:real^N = vec 0 + b`) THEN
    EXPAND_TAC "b" THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    MATCH_MP_TAC IN_AFFINE_ADD_MUL THEN
    ASM_REWRITE_TAC[AFFINE_AFFINE_HULL; VECTOR_ADD_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((b:real^N) IN affine hull k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_REFL]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
    ASM_SIMP_TAC[HAS_SIZE; FINITE_INSERT; CARD_CLAUSES] THEN
    ASM_MESON_TAC[HULL_INC];
    MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[INSERT_SUBSET];
    REWRITE_TAC[GSYM pairwise; PAIRWISE_INSERT] THEN
    ASM_REWRITE_TAC[pairwise; NORM_ARITH
     `dist(b:real^N,y) = r /\ dist(y,b) = r <=> dist(b,y) = r`] THEN
    X_GEN_TAC `c:real^N` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[NORM_EQ_SQUARE; dist; REAL_LT_IMP_LE; GSYM NORM_POW_2] THEN
    MP_TAC(ISPECL [`b:real^N`; `--c:real^N`] NORM_ADD_PYTHAGOREAN) THEN
    ASM_SIMP_TAC[ORTHOGONAL_CLAUSES; HULL_INC] THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB; NORM_NEG] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_DIV; REAL_LE_MUL; REAL_POS; REAL_LE_ADD;
       REAL_LT_IMP_LE; REAL_POW_MUL; REAL_SUB_LE; REAL_OF_NUM_LE; LE_1] THEN
    UNDISCH_TAC `~(n = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    CONV_TAC REAL_FIELD]);;

let REGULAR_POLYTOPE_WITH_BARYCENTRE_EXISTS_ALT = prove
 (`!r s:real^N->bool a n.
      &n <= aff_dim s + &1 /\ &0 < r /\ a IN affine hull s /\ ~(n = 0)
      ==> ?k. k HAS_SIZE n /\ ~affine_dependent k /\ k SUBSET affine hull s /\
              barycentre k = a /\
              (!x y. x IN k /\ y IN k /\ ~(x = y) ==> dist(x,y) = r) /\
              (!x. x IN k ==> dist(a,x) = sqrt((&n - &1) / (&2 * &n)) * r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:real`; `s:real^N->bool`; `n:num`]
        REGULAR_POLYTOPE_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\x:real^N. (a - barycentre k) + x) k` THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[REGULAR_POLYTOPE_DIST_BARYCENTRE]] THEN
  ASM_REWRITE_TAC[AFFINE_DEPENDENT_TRANSLATION_EQ] THEN
  ASM_SIMP_TAC[HAS_SIZE_IMAGE_INJ_EQ;
               VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_CASES_TAC `k:real^N->bool = {}` THENL
   [ASM_MESON_TAC[CARD_EQ_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[BARYCENTRE_TRANSLATION; VECTOR_ARITH
   `(a - b) + b:real^N = a`] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
  ASM_SIMP_TAC[NORM_ARITH `dist(a + x:real^N,a + y) = dist(x,y)`] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `x - y:real^N = &1 % (x - y)`] THEN
  MATCH_MP_TAC IN_AFFINE_MUL_DIFF_ADD THEN
  ASM_REWRITE_TAC[AFFINE_AFFINE_HULL] THEN
  ASM_MESON_TAC[BARYCENTRE_IN_AFFINE_HULL; SUBSET; HULL_MONO; HULL_HULL]);;

let REGULAR_POLYTOPE_WITH_BARYCENTRE_EXISTS = prove
 (`!r s:real^N->bool a n.
      &n <= aff_dim s + &1 /\ &0 < r /\ a IN affine hull s /\ 1 < n
      ==> ?k. k HAS_SIZE n /\ ~affine_dependent k /\ k SUBSET affine hull s /\
              barycentre k = a /\
              (!x. x IN k ==> dist(a,x) = r) /\
              (!x y. x IN k /\ y IN k /\ ~(x = y)
                     ==> dist(x,y) = sqrt((&2 * &n) / (&n - &1)) * r)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`sqrt((&2 * &n) / (&n - &1)) * r`; `s:real^N->bool`; `a:real^N`; `n:num`]
   REGULAR_POLYTOPE_WITH_BARYCENTRE_EXISTS_ALT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[SQRT_LT_0] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LT]) THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_RING `a * b = &1 ==> a * b * y = y`) THEN
    REWRITE_TAC[GSYM SQRT_MUL] THEN
    MATCH_MP_TAC(MESON[SQRT_1] `x = &1 ==> sqrt x = &1`) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LT]) THEN
    CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of convex functions and related results.                       *)
(* ------------------------------------------------------------------------- *)

let CONVEX_IMP_LOCALLY_BOUNDED = prove
 (`!f s a:real^N.
        f convex_on s /\ a IN relative_interior s
        ==> ?e B. &0 < e /\ &0 < B /\
                  cball(a,e) INTER affine hull s SUBSET s /\
                  !x. x IN cball(a,e) INTER affine hull s ==> abs(f x) <= B`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR_CBALL]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real`
    STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `aff_dim(s:real^N->bool) = &0` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [AFF_DIM_EQ_0]) THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^N` SUBST_ALL_TAC) THEN
    ASM_CASES_TAC `b:real^N = a` THEN ASM_REWRITE_TAC[IN_SING] THEN
    REWRITE_TAC[AFFINE_HULL_SING; INTER_SUBSET; IN_INTER; IN_SING] THEN
    MESON_TAC[REAL_ARITH `abs x <= abs x + &1 /\ &0 < abs x + &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= aff_dim(s:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(INT_ARITH
     `-- &1:int <= x /\ ~(x = &0) /\ ~(x = -- &1) ==> &1 <= x`) THEN
    ASM_REWRITE_TAC[AFF_DIM_GE; AFF_DIM_EQ_MINUS1];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. aff_dim(s:real^N->bool) = &n - &1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_EQ_SUB_LADD; INT_OF_NUM_EXISTS] THEN
    REWRITE_TAC[GSYM INT_LE_SUB_RADD; AFF_DIM_GE; INT_SUB_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 < n /\ ~(n = 0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LT] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real`; `s:real^N->bool`; `a:real^N`; `n:num`]
        REGULAR_POLYTOPE_WITH_BARYCENTRE_EXISTS) THEN
  ASM_SIMP_TAC[HULL_INC; INT_SUB_ADD; INT_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^N->real`; `k:real^N->bool`]
        UPPER_BOUND_FINITE_SET_REAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    CONVEX_ON_CONVEX_HULL_BOUND)) THEN
  SUBGOAL_THEN `(f:real^N->real) convex_on convex hull k` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONVEX_ON_SUBSET)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        SUBSET_TRANS)) THEN
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN
      ASM_SIMP_TAC[CONVEX_CBALL; SUBSET; IN_CBALL; REAL_LE_REFL];
      ASM_MESON_TAC[HULL_MONO; HULL_HULL; SUBSET;
                    CONVEX_HULL_SUBSET_AFFINE_HULL]];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(SPEC `k:real^N->bool` BARYCENTRE_IN_RELATIVE_INTERIOR) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[HAS_SIZE; CARD_CLAUSES]; ASM_SIMP_TAC[]] THEN
  REWRITE_TAC[IN_RELATIVE_INTERIOR_CBALL; AFFINE_HULL_CONVEX_HULL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `affine hull k:real^N->bool = affine hull s` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM HULL_HULL] THEN
    MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN
    ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
    MP_TAC(ISPECL [`k:real^N->bool`; `k:real^N->bool`] AFF_DIM_UNIQUE) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN ASM_SIMP_TAC[INT_LE_REFL];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `&1 + abs(b + &2 * abs(f(a:real^N)))` THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    SUBGOAL_THEN `convex hull k SUBSET cball(a:real^N,e)` MP_TAC THENL
     [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_SIMP_TAC[CONVEX_CBALL; SUBSET; IN_CBALL; REAL_LE_REFL];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN `f convex_on cball(a:real^N,d) INTER affine hull s`
    MP_TAC THENL [ASM_MESON_TAC[CONVEX_ON_SUBSET]; SIMP_TAC[convex_on]] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`x:real^N`; `&2 % a - x:real^N`; `&1 / &2`; `&1 / &2`]) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[IN_INTER] THEN
    REWRITE_TAC[VECTOR_ARITH
     `&1 / &2 % x + &1 / &2 % (&2 % a - x):real^N = a`] THEN
    UNDISCH_TAC `!x:real^N. x IN convex hull k ==> f x <= b` THEN
    DISCH_THEN(fun th ->
     MP_TAC(SPEC `&2 % a - x:real^N` th) THEN
     MP_TAC(SPEC `x:real^N` th) THEN
     MP_TAC(SPEC `a:real^N` th)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `&2 % a - x IN cball(a:real^N,d) /\
                  &2 % a - x IN affine hull s`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_CBALL; NORM_ARITH
       `dist(a:real^N,&2 % a - x) = dist(a,x)`] THEN
      ASM_REWRITE_TAC[GSYM IN_CBALL] THEN
      REWRITE_TAC[VECTOR_ARITH `&2 % a - x:real^N = &1 % (a - x) + a`] THEN
      MATCH_MP_TAC IN_AFFINE_MUL_DIFF_ADD THEN
      ASM_REWRITE_TAC[AFFINE_AFFINE_HULL] THEN
      ASM_MESON_TAC[SUBSET; CONVEX_HULL_SUBSET_AFFINE_HULL];
      ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

let CONVEX_IMP_LOCALLY_LIPSCHITZ = prove
 (`!f s a:real^N.
        f convex_on s /\ a IN relative_interior s
        ==> ?e B. &0 < e /\ &0 < B /\
                  cball(a,e) INTER affine hull s SUBSET s /\
                  !x y. x IN cball(a,e) INTER affine hull s /\
                        y IN cball(a,e) INTER affine hull s
                        ==> abs(f x - f y) <= B * norm(x - y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real`; `s:real^N->bool`; `a:real^N`]
    CONVEX_IMP_LOCALLY_BOUNDED) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`e:real`; `B:real`] THEN STRIP_TAC THEN
  EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  EXISTS_TAC `&4 * B / e` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_ARITH `&0 < &4`] THEN
  MP_TAC(ISPECL [`a:real^N`; `e / &2`; `e:real`] SUBSET_CBALL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `!i. (!x y. i x y \/ i y x) /\ (!x y. P x y ==> P y x) /\
        (!x y. i x y ==> P x y)
        ==> !x y. P x y`) THEN
  EXISTS_TAC `\x y. (f:real^N->real) x <= f y` THEN
  REWRITE_TAC[REAL_LE_TOTAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[NORM_SUB; REAL_ABS_SUB] THEN MESON_TAC[]; ALL_TAC] THEN
  SIMP_TAC[REAL_ARITH `x <= y ==> abs(x - y) = y - x`] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `y:real^N = x` THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; VECTOR_SUB_REFL; NORM_0;
                  REAL_MUL_RZERO; REAL_LE_REFL] THEN
  SUBGOAL_THEN
   `?z:real^N. dist(a,z) = e /\ z IN affine hull s /\ y IN segment[x,z]`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cball(a:real^N,e)`; `x:real^N`; `y - x:real^N`]
        RAY_TO_FRONTIER) THEN
    REWRITE_TAC[INTERIOR_CBALL; FRONTIER_CBALL] THEN
    ASM_REWRITE_TAC[IN_BALL; VECTOR_SUB_EQ; BOUNDED_CBALL] THEN ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_CBALL]) THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC `x + d % (y - x):real^N` THEN
    ASM_REWRITE_TAC[GSYM IN_SPHERE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[IN_INTER; AFFINE_AFFINE_HULL; IN_AFFINE_ADD_MUL_DIFF];
      REWRITE_TAC[IN_SEGMENT]] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; VECTOR_ARITH
     `y:real^N = (&1 - u) % x + u % (x + d % (y - x)) <=>
      (u * d - &1) % (y - x) = vec 0`] THEN
    EXISTS_TAC `inv(d):real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_IMP_NZ; REAL_MUL_LINV;
                 REAL_SUB_REFL; REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SPHERE]) THEN
    REWRITE_TAC[dist; VECTOR_ARITH
     `a - (x + d % (y - x)) = --((&1 - d) % (x - a) + d % (y - a))`] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(x:real^N) + norm(y) < e ==> ~(norm(--(x + y)) = e)`) THEN
    REWRITE_TAC[NORM_MUL] THEN TRANS_TAC REAL_LET_TRANS
     `abs(&1 - d) * e / &2 + abs d * e / &2` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] (GSYM dist)] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_CBALL]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONVEX_ON_LEFT_SECANT_MUL]) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `z:real^N`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_MESON_TAC[SUBSET; IN_CBALL; REAL_LE_REFL; IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `e / &2 <= norm(z - x:real^N)` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
     `dist(a:real^N,z) = e
      ==> dist(a,x) <= e / &2 ==> e / &2 <= norm(z - x)`)) THEN
    ASM_MESON_TAC[IN_INTER; IN_CBALL];
    ALL_TAC] THEN
  ASM_CASES_TAC `z:real^N = x` THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  REWRITE_TAC[REAL_ARITH `(a * b) / c:real = a / c * b`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [NORM_SUB] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
  TRANS_TAC REAL_LE_TRANS `(&4 * B / e) * e / &2` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_FIELD `&0 < e ==>  (&4 * B / e) * e / &2 = &2 * B`] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(x) <= B /\ abs(y) <= B ==> x - y <= &2 * B`) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[SUBSET; IN_CBALL; REAL_LE_REFL; IN_INTER];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE]]);;

let CONVEX_ON_CONTINUOUS_ON_RELATIVE_INTERIOR = prove
 (`!f s:real^N->bool.
        f convex_on s ==> lift o f continuous_on relative_interior s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[continuous_on] THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real`; `s:real^N->bool`; `a:real^N`]
        CONVEX_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:real`; `B:real`] THEN STRIP_TAC THEN
  EXISTS_TAC `min d (e / B)` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; o_DEF; DIST_LIFT] THEN
  X_GEN_TAC `b:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_RELATIVE_INTERIOR]) THEN
  ASM_SIMP_TAC[IN_INTER; HULL_INC; IN_CBALL; DIST_REFL] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `d < e ==> abs(a - b) <= d ==> abs(b - a) < e`) THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN
  ASM_REWRITE_TAC[NORM_ARITH `norm(a - b:real^N) = dist(b,a)`]);;

let CONVEX_ON_CONTINUOUS = prove
 (`!f s:real^N->bool. open s /\ f convex_on s ==> lift o f continuous_on s`,
  MESON_TAC[RELATIVE_INTERIOR_OPEN;
            CONVEX_ON_CONTINUOUS_ON_RELATIVE_INTERIOR]);;

let CONVEX_IMP_LIPSCHITZ = prove
 (`!f:real^N->real s t.
        f convex_on t /\ compact s /\ s SUBSET relative_interior t
        ==> ?B. &0 < B /\
                !x y. x IN s /\ y IN s ==> abs(f x - f y) <= B * norm(x - y)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `?x y a b:real^N.
        (!n. x n IN s) /\ (!n. y n IN s) /\ a IN s /\ b IN s /\
        (x --> a) sequentially /\ (y --> b) sequentially /\
        (!n. abs(f(x n) - f(y n)) > &n * norm(x n - y n))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN `n:num` o SPEC `&n + &1:real`) THEN
    REWRITE_TAC[REAL_ARITH `&0 < &n + &1`; NOT_FORALL_THM; NOT_IMP] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; GSYM CONJ_ASSOC] THEN
    MAP_EVERY X_GEN_TAC [`x:num->real^N`; `y:num->real^N`] THEN
    REWRITE_TAC[FORALL_AND_THM; REAL_NOT_LE] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:num->real^N` o
        GEN_REWRITE_RULE I [compact]) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `r:num->num`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `(y:num->real^N) o (r:num->num)` o
        GEN_REWRITE_RULE I [compact]) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; o_THM] THEN
    MAP_EVERY X_GEN_TAC [`b:real^N`; `q:num->num`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`(x:num->real^N) o (r:num->num) o (q:num->num)`;
      `(y:num->real^N) o (r:num->num) o (q:num->num)`;
      `a:real^N`; `b:real^N`] THEN
    ASM_SIMP_TAC[o_ASSOC; o_THM; LIM_SUBSEQUENCE] THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_NOT_LE] o
      SPEC `(r:num->num) ((q:num->num) n)`) THEN
    MATCH_MP_TAC(REAL_ARITH `b <= a ==> ~(x <= a) ==> x > b`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= b + &1`) THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN SPEC_TAC(`n:num`,`n:num`) THEN
    MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `b:real^N = a` SUBST_ALL_TAC THENL
   [ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. (y:num->real^N) n - x n` THEN
    ASM_SIMP_TAC[LIM_SUB; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC LIM_NULL_COMPARISON THEN
    EXISTS_TAC `\n. abs(f(y n) - f(x n:real^N)) / &n` THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
     [EXISTS_TAC `1` THEN SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ONCE_REWRITE_TAC[NORM_SUB; REAL_ABS_SUB] THEN
      ASM_SIMP_TAC[REAL_ARITH `b:real > a ==> a <= b`];
      REWRITE_TAC[real_div; LIFT_CMUL] THEN SUBST1_TAC(VECTOR_ARITH
       `vec 0:real^1 = abs(f(b:real^N) - f a) % vec 0`) THEN
      MATCH_MP_TAC LIM_MUL THEN REWRITE_TAC[SEQ_HARMONIC; o_DEF] THEN
      REWRITE_TAC[GSYM NORM_LIFT; LIFT_SUB] THEN
      MATCH_MP_TAC LIM_NORM THEN MATCH_MP_TAC LIM_SUB THEN
      CONJ_TAC THEN MP_TAC(ISPECL
       [`lift o (f:real^N->real)`; `relative_interior t:real^N->bool`]
       CONTINUOUS_WITHIN_SEQUENTIALLY) THEN
      REWRITE_TAC[o_DEF] THENL
       [DISCH_THEN(MP_TAC o SPEC `b:real^N`);
        DISCH_THEN(MP_TAC o SPEC `a:real^N`)] THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
      (ANTS_TAC THENL
        [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET]]) THEN
      FIRST_ASSUM(MP_TAC o
        MATCH_MP CONVEX_ON_CONTINUOUS_ON_RELATIVE_INTERIOR) THEN
      REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; o_DEF] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`f:real^N->real`; `t:real^N->bool`; `a:real^N`]
      CONVEX_IMP_LOCALLY_LIPSCHITZ) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`d:real`; `B:real`] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY])) THEN
  REWRITE_TAC[TAUT `a ==> ~b <=> ~(a /\ b)`; AND_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC `N1:num`) (X_CHOOSE_TAC `N2:num`)) THEN
  MP_TAC(SPEC `max B (max (&N1) (&N2))` REAL_ARCH_SIMPLE) THEN
  REWRITE_TAC[REAL_MAX_LE; REAL_OF_NUM_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`)) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`(x:num->real^N) n`; `(y:num->real^N) n`]) THEN
  ASM_REWRITE_TAC[IN_CBALL; IN_INTER] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; NOT_IMP] THEN
  CONJ_TAC THENL
    [ASM_MESON_TAC[SUBSET; HULL_INC; RELATIVE_INTERIOR_SUBSET];
     FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `x > a ==> b <= a ==> ~(x <= b)`)) THEN
     ASM_SIMP_TAC[REAL_LE_RMUL; NORM_POS_LE]]);;

let CONVEX_BOUNDS_LEMMA = prove
 (`!f x:real^N e.
        f convex_on cball(x,e) /\
        (!y. y IN cball(x,e) ==> f(y) <= b)
        ==> !y. y IN cball(x,e) ==> abs(f(y)) <= b + &2 * abs(f(x))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 <= e` THENL
   [ALL_TAC;
    REWRITE_TAC[IN_CBALL] THEN ASM_MESON_TAC[DIST_POS_LE; REAL_LE_TRANS]] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [convex_on]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`y:real^N`; `&2 % x - y:real^N`; `&1 / &2`; `&1 / &2`]) THEN
  REWRITE_TAC[GSYM VECTOR_ADD_LDISTRIB; GSYM REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[VECTOR_ARITH `y + x - y = x:real^N`] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ABBREV_TAC `z = &2 % x - y:real^N` THEN
  SUBGOAL_THEN `z:real^N IN cball(x,e)` ASSUME_TAC THENL
   [UNDISCH_TAC `y:real^N IN cball(x,e)`  THEN
    EXPAND_TAC "z" THEN REWRITE_TAC[dist; IN_CBALL] THEN
    REWRITE_TAC[VECTOR_ARITH `x - (&2 % x - y) = y - x`] THEN
    REWRITE_TAC[NORM_SUB];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  FIRST_X_ASSUM(fun th ->
    MAP_EVERY (MP_TAC o C SPEC th) [`y:real^N`; `z:real^N`]) THEN
  ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN REAL_ARITH_TAC);;

let CONVEX_IMP_BOUNDED_ON_INTERVAL = prove
 (`!f:real^1->real a b.
        f convex_on interval[a,b]
        ==> ?B. &0 < B /\ !x. x IN interval[a,b] ==> abs(f x) <= B`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `interval[a:real^1,b] = {}` THENL
   [ASM_MESON_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY_1]) THEN
  SUBGOAL_THEN `?B. !x:real^1. x IN interval[a,b] ==> f(x) <= B`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `max (f(a:real^1)) (f b)` THEN
    MP_TAC(ISPECL [`f:real^1->real`; `{a:real^1,b}`;
                   `max (f(a:real^1)) (f b)`] CONVEX_ON_CONVEX_HULL_BOUND) THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; SEGMENT_1] THEN
    DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC;
    EXISTS_TAC `(&1 + abs B) + &2 * abs(f(midpoint(a,b):real^1))` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REWRITE_TAC[INTERVAL_1]] THEN
    MATCH_MP_TAC CONVEX_BOUNDS_LEMMA THEN MAP_EVERY UNDISCH_TAC
     [`f convex_on interval[a:real^1,b]`;
      `!x:real^1. x IN interval[a,b] ==> f x <= B`] THEN
    ASM_SIMP_TAC[INTERVAL_1; REAL_ARITH `x <= b ==> x <= &1 + abs b`]]);;

(* ------------------------------------------------------------------------- *)
(* A convex function on R^1 is "piecewise monotone" in this precise sense.   *)
(* ------------------------------------------------------------------------- *)

let CONVEX_IMP_PIECEWISE_MONOTONE = prove
 (`!f s. f convex_on s /\ is_interval s
         ==> (!x y. x IN interior s /\ y IN interior s /\ drop x <= drop y
                    ==> f x <= f y) \/
             (!x y. x IN interior s /\ y IN interior s /\ drop x <= drop y
                    ==> f y <= f x) \/
             ?a. a IN interior s /\
                 (!x y. x IN s /\ y IN s /\
                        drop x <= drop y /\ drop y <= drop a
                        ==> f y <= f x) /\
                 (!x y. x IN s /\ y IN s /\
                        drop a <= drop x /\ drop x <= drop y
                        ==> f x <= f y)`,
  let lemma = time prove
   (`!P f:real->real.
          (!x y. P x /\ P y /\ x <= y ==> f x <= f y) \/
          (!x y. P x /\ P y /\ x <= y ==> f y <= f x) \/
          (?x y z. P x /\ P y /\ P z /\ x < y /\ y < z /\
                   (f x < f y /\ f z < f y \/ f y < f x /\ f y < f z))`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[TAUT `p \/ q <=> ~p ==> q`] THEN
    REWRITE_TAC[NOT_FORALL_THM; LEFT_IMP_EXISTS_THM; NOT_IMP] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; REAL_NOT_LE; MESON[REAL_LT_LE]
     `(x <= y /\ (f:real->real) y < f x <=> x < y /\ f y < f x) /\
      (x <= y /\ f x < f y <=> x < y /\ f x < f y)`] THEN
    MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`w:real`; `z:real`] THEN STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH
     `u:real = w \/ u < w \/ w < u`)
    THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MATCH_MP_TAC(MESON[] `P w v z \/ P w z v ==> ?x y z. P x y z`);
      MATCH_MP_TAC(MESON[] `P u v \/ P u w \/ P u z ==> ?x y. P x y`) THEN
      ASM_REWRITE_TAC[OR_EXISTS_THM; REAL_LT_REFL] THEN
      MATCH_MP_TAC(MESON[] `P(v:real) \/ P z ==> ?x. P x`);
      MATCH_MP_TAC(MESON[] `P w u \/ P w v \/ P w z ==> ?x y. P x y`) THEN
      ASM_REWRITE_TAC[OR_EXISTS_THM; REAL_LT_REFL] THEN
      MATCH_MP_TAC(MESON[] `P(v:real) \/ P z ==> ?x. P x`)] THEN
    ASM_SIMP_TAC[REAL_LT_REFL; REAL_ARITH `a < b ==> ~(b < a)`] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
    CONV_TAC NNFC_CONV THEN CONV_TAC CNF_CONV THEN
    REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
    ASM_CASES_TAC `u:real = w` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
    ASM_CASES_TAC `u:real = z` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
    ASM_CASES_TAC `v:real = w` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
    ASM_CASES_TAC `v:real = z` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
    REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN ASM_REAL_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. lift x IN interior s`;  `(f:real^1->real) o lift`]
        lemma) THEN
  REWRITE_TAC[o_THM; FORALL_DROP; LIFT_DROP; EXISTS_DROP] THEN
  REPEAT(MATCH_MP_TAC MONO_OR THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM]) THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `b:real^1`; `v:real^1`] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MP_TAC(ISPECL [`f:real^1->real`; `s:real^1->bool`;
                   `u:real^1`; `v:real^1`; `b:real^1`]
        CONVEX_LOWER_SEGMENT) THEN
    ASM_SIMP_TAC[NOT_IMP; REWRITE_RULE[SUBSET] INTERIOR_SUBSET] THEN
    REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `interval[u:real^1,v] SUBSET interior s` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERVAL_SUBSET_IS_INTERVAL; IS_INTERVAL_CONVEX_1;
                   CONVEX_INTERIOR];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`f:real^1->real`; `interval[u:real^1,v]`] CONTINUOUS_ATTAINS_INF) THEN
  REWRITE_TAC[COMPACT_INTERVAL] THEN ANTS_TAC THENL
   [REWRITE_TAC[INTERVAL_NE_EMPTY_1] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interior s:real^1->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONVEX_ON_CONTINUOUS THEN
    ASM_MESON_TAC[CONVEX_ON_SUBSET; INTERIOR_SUBSET; OPEN_INTERIOR];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^1`] THEN
  STRIP_TAC THEN MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `!x. x IN s ==> (f:real^1->real) a <= f x` ASSUME_TAC THENL
   [MATCH_MP_TAC CONVEX_LOCAL_GLOBAL_MINIMUM THEN
    EXISTS_TAC `interval(u:real^1,v)` THEN ASM_REWRITE_TAC[OPEN_INTERVAL] THEN
    CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
      ASM_SIMP_TAC[IN_INTERVAL_1; REAL_LT_LE; DROP_EQ] THEN
      ASM_MESON_TAC[REAL_LE_LT; REAL_NOT_LE];
      ASM_MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET; INTERIOR_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN s /\ y IN s /\ x IN segment[a,y] ==> (f:real^1->real) x <= f y`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^1->real`; `s:real^1->bool`;
            `a:real^1`; `y:real^1`; `x:real^1`] CONVEX_LOWER_SEGMENT) THEN
    ASM_SIMP_TAC[real_max] THEN ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC]);;
