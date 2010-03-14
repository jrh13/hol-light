(* ========================================================================= *)
(* Convex sets, functions and related things.                                *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*                 (c) Copyright, Lars Schewe 2007                           *)
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

(* ------------------------------------------------------------------------- *)
(* Some convenient lemmas about common affine combinations.                  *)
(* ------------------------------------------------------------------------- *)

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
 (`!s a b u v.
        convex s /\ a IN s /\ b IN s /\ &0 <= u /\ u <= &1
        ==> ((&1 - u) % a + u % b) IN s`,
  MESON_TAC[CONVEX_ALT]);;

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

let CONVEX_HULLS_EQ = prove
 (`!s t. s SUBSET convex hull t /\ t SUBSET convex hull s
         ==> convex hull s = convex hull t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULLS_EQ THEN
  ASM_SIMP_TAC[CONVEX_INTERS]);;

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
(* Some rather trivial consequences we could have derived earlier instead.   *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_UNIV = prove
 (`connected (UNIV:real^N->bool)`,
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_UNIV]);;

let CONNECTED_COMPONENT_UNIV = prove
 (`!x. connected_component(:real^N) x = (:real^N)`,
  MESON_TAC[CONNECTED_CONNECTED_COMPONENT_SET; CONNECTED_UNIV; IN_UNIV]);;

let CLOPEN = prove
 (`!s. closed s /\ open s <=> s = {} \/ s = (:real^N)`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[CLOSED_EMPTY; OPEN_EMPTY; CLOSED_UNIV; OPEN_UNIV] THEN
  MATCH_MP_TAC(REWRITE_RULE[CONNECTED_CLOPEN] CONNECTED_UNIV) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; GSYM CLOSED_IN]);;

let FINITE_IMP_NOT_OPEN = prove
 (`!s:real^N->bool. FINITE s /\ ~(s = {}) ==> ~(open s)`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FINITE_IMP_CLOSED) THEN
  ASM_REWRITE_TAC[TAUT `(p ==> ~q) <=> ~(p /\ q)`; CLOPEN] THEN
  ASM_MESON_TAC[INFINITE; EUCLIDEAN_SPACE_INFINITE]);;

let OPEN_IMP_INFINITE = prove
 (`!s. open s ==> s = {} \/ INFINITE s`,
  MESON_TAC[FINITE_IMP_NOT_OPEN; INFINITE]);;

let EMPTY_INTERIOR_FINITE = prove
 (`!s:real^N->bool. FINITE s ==> interior s = {}`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `s:real^N->bool` OPEN_INTERIOR) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] FINITE_IMP_NOT_OPEN) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[INTERIOR_SUBSET]);;

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

let CONVEX_LOWER = prove
 (`!f s x y. f convex_on s /\
             x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
             ==> f(u % x + v % y) <= max (f(x)) (f(y))`,
  REWRITE_TAC[convex_on] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  ASM_MESON_TAC[REAL_LE_ADD2; REAL_LE_LMUL; REAL_MAX_MAX]);;

let CONVEX_LOCAL_GLOBAL_MINIMUM = prove
 (`!f s t x:real^N.
       f convex_on s /\ x IN t /\ open t /\ t SUBSET s /\
       (!y. y IN t ==> f(x) <= f(y))
       ==> !y. y IN s ==> f(x) <= f(y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < dist(x:real^N,y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[DIST_POS_LT; REAL_LT_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`&1`; `e / dist(x:real^N,y)`] REAL_DOWN2) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [convex_on]) THEN
  DISCH_THEN(MP_TAC o
    SPECL [`x:real^N`; `y:real^N`; `&1 - u`; `u:real`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_SUB_ADD; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
    ASM_MESON_TAC[CENTRE_IN_BALL; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `(&1 - u) * f(x) + u * f(x:real^N):real` THEN
  ASM_SIMP_TAC[REAL_LT_LADD; REAL_LT_LMUL] THEN
  REWRITE_TAC[REAL_ARITH `(&1 - x) * a + x * a = a`] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  REWRITE_TAC[IN_BALL; dist] THEN
  REWRITE_TAC[VECTOR_ARITH `x - ((&1 - u) % x + u % y):real^N =
                            u % (x - y)`] THEN
  REWRITE_TAC[NORM_MUL; GSYM dist] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ;
               REAL_ARITH `&0 < x /\ x < b ==> abs x < b`]);;

let CONVEX_DISTANCE = prove
 (`!s a. (\x. dist(a,x)) convex_on s`,
  REWRITE_TAC[convex_on; dist] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
   [GSYM VECTOR_MUL_LID] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[VECTOR_ARITH
   `(u + v) % z - (u % x + v % y) = u % (z - x) + v % (z - y)`] THEN
  ASM_MESON_TAC[NORM_TRIANGLE; NORM_MUL; REAL_ABS_REFL]);;

let CONVEX_BALL = prove
 (`!x:real^N e. convex(ball(x,e))`,
  let lemma = REWRITE_RULE[convex_on; IN_UNIV]
   (ISPEC `(:real^N)` CONVEX_DISTANCE) in
  REWRITE_TAC[convex; IN_BALL] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) lemma o lhand o snd) THEN
  ASM_MESON_TAC[REAL_LET_TRANS; REAL_CONVEX_BOUND_LT]);;

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

let CONVEX_TRANSLATION_EQ = prove
 (`!a:real^N s. convex (IMAGE (\x. a + x) s) <=> convex s`,
  REWRITE_TAC[CONVEX_ALT; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE; UNWIND_THM1; VECTOR_ARITH
   `(&1 - u) % (a + x) + u % (a + y) = a + z <=> (&1 - u) % x + u % y = z`]);;

add_translation_invariants [CONVEX_TRANSLATION_EQ];;

let CONVEX_TRANSLATION = prove
 (`!s a:real^N. convex s ==> convex (IMAGE (\x. a + x) s)`,
  REWRITE_TAC[CONVEX_TRANSLATION_EQ]);;

let CONVEX_AFFINITY = prove
 (`!s a:real^N c.
        convex s ==> convex (IMAGE (\x. a + c % x) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. a + c % x) = (\x. a + x) o (\x. c % x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  ASM_SIMP_TAC[IMAGE_o; CONVEX_TRANSLATION; CONVEX_SCALING]);;

let CONVEX_LINEAR_IMAGE = prove
 (`!f s. convex s /\ linear f ==> convex(IMAGE f s)`,
  REWRITE_TAC[convex; FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IN_IMAGE; linear] THEN MESON_TAC[]);;

let CONVEX_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (convex (IMAGE f s) <=> convex s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE CONVEX_LINEAR_IMAGE));;

add_linear_invariants [CONVEX_LINEAR_IMAGE_EQ];;

let CONVEX_LINEAR_PREIMAGE = prove
 (`!f:real^M->real^N.
     linear f /\ convex s ==> convex {x | f(x) IN s}`,
  REWRITE_TAC[CONVEX_ALT; IN_ELIM_THM] THEN
  SIMP_TAC[LINEAR_ADD; LINEAR_CMUL]);;

(* ------------------------------------------------------------------------- *)
(* Balls, being convex, are connected.                                       *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* Convex hull.                                                              *)
(* ------------------------------------------------------------------------- *)

let CONVEX_CONVEX_HULL = prove
 (`!s. convex(convex hull s)`,
  SIMP_TAC[P_HULL; CONVEX_INTERS]);;

let CONVEX_HULL_EQ = prove
 (`!s. (convex hull s = s) <=> convex s`,
  SIMP_TAC[HULL_EQ; CONVEX_INTERS]);;

let IS_CONVEX_HULL = prove
 (`!s. convex s <=> ?t. s = convex hull t`,
  GEN_TAC THEN MATCH_MP_TAC IS_HULL THEN SIMP_TAC[CONVEX_INTERS]);;

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
 (`!s x. ~(s = {})
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

let AFFINE_INDEPENDENT_SING = prove
 (`!a. ~(affine_dependent {a})`,
  GEN_TAC THEN MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN
  ASM_REWRITE_TAC[AFFINE_HULL_EMPTY; AFFINE_INDEPENDENT_EMPTY; NOT_IN_EMPTY]);;

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
    REWRITE_TAC[AFFINE_INDEPENDENT_SING];
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

let AFF_DIM_CONVEX_HULL = prove
 (`!s:real^N->bool. aff_dim(convex hull s) = aff_dim s`,
  GEN_TAC THEN MATCH_MP_TAC(INT_ARITH
   `!c:int. c = a /\ a <= b /\ b <= c ==> b = a`) THEN
  EXISTS_TAC `aff_dim(affine hull s:real^N->bool)` THEN
  SIMP_TAC[AFF_DIM_AFFINE_HULL; AFF_DIM_SUBSET; HULL_SUBSET;
           CONVEX_HULL_SUBSET_AFFINE_HULL]);;

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

let AFFINE_HULL_CONVEX_INTER_OPEN = prove
 (`!s t:real^N->bool.
        convex s /\ open t /\ ~(s INTER t = {})
        ==> affine hull (s INTER t) = affine hull s`,
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; RIGHT_AND_EXISTS_THM;
              LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`; `a:real^N`] THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN REWRITE_TAC[IN_INTER] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
  SIMP_TAC[SUBSET_HULL; AFFINE_AFFINE_HULL] THEN
  ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; IN_INTER] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^N`) THEN
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

let AFFINE_HULL_OPEN = prove
 (`!s. open s /\ ~(s = {}) ==> affine hull s = (:real^N)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBST1_TAC(SET_RULE `s = (:real^N) INTER s`) THEN
  ASM_SIMP_TAC[AFFINE_HULL_CONVEX_INTER_OPEN; CONVEX_UNIV] THEN
  REWRITE_TAC[AFFINE_HULL_UNIV]);;

let AFF_DIM_OPEN = prove
 (`!s:real^N->bool. open s /\ ~(s = {}) ==> aff_dim s = &(dimindex(:N))`,
  SIMP_TAC[AFF_DIM_EQ_FULL; AFFINE_HULL_OPEN]);;

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

(* ------------------------------------------------------------------------- *)
(* Caratheodory's theorem.                                                   *)
(* ------------------------------------------------------------------------- *)

let CONVEX_HULL_CARATHEODORY = prove
 (`!p. convex hull p =
        {y:real^N | ?s u. FINITE s /\ s SUBSET p /\
                          CARD(s) <= dimindex(:N) + 1 /\
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
  GEN_REWRITE_TAC I [GSYM NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN REWRITE_TAC[NOT_IMP] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `d + 1 < n ==> n - 1 < n`]; ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^N->bool` AFFINE_DEPENDENT_BIGGERSET) THEN
  ASM_REWRITE_TAC[ARITH_RULE `x >= n + 2 <=> n + 1 < x`] THEN
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
   [`s DELETE (a:real^N)`; `\v:real^N. u(v) + t * w(v)`] THEN
  ASM_SIMP_TAC[SUM_DELETE; VSUM_DELETE; CARD_DELETE; FINITE_DELETE] THEN
  ASM_SIMP_TAC[SUM_ADD; VECTOR_ADD_RDISTRIB; VSUM_ADD] THEN
  ASM_SIMP_TAC[GSYM VECTOR_MUL_ASSOC; SUM_LMUL; VSUM_LMUL] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[]; ASM SET_TAC[real_ge]; REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

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
  ASM_SIMP_TAC[COMPACT_PASTECART; COMPACT_INTERVAL] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `z:real^(1,(N,N)finite_sum)finite_sum` THEN
  DISCH_THEN(K ALL_TAC) THEN
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

let DIAMETER_SIMPLEX = prove
 (`!s:real^N->bool.
        FINITE s /\ ~(s = {})
        ==> diameter(convex hull s) = sup { dist(x,y) | x IN s /\ y IN s}`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SIMPLEX_EXTREMAL_LE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sup {dist(x:real^N,y) | x IN s /\ y IN s} = dist(u:real^N,v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_SUP_LE THEN
      ASM_SIMP_TAC[FORALL_IN_GSPEC; dist; HULL_INC] THEN ASM SET_TAC[];
      SUBGOAL_THEN
       `{dist(x:real^N,y) | x IN s /\ y IN s} =
        IMAGE (\(x,y). dist(x,y)) (s CROSS s)`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; EXISTS_PAIR_THM;
                    IN_CROSS] THEN MESON_TAC[];
        ASM_SIMP_TAC[REAL_LE_SUP_FINITE; IMAGE_EQ_EMPTY; CROSS_EQ_EMPTY;
         FINITE_CROSS; FINITE_IMAGE; EXISTS_IN_IMAGE; EXISTS_PAIR_THM] THEN
        REWRITE_TAC[IN_CROSS] THEN ASM_MESON_TAC[REAL_LE_REFL]]];
    REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `convex hull s:real^N->bool` DIAMETER_COMPACT_ATTAINED) THEN
      ASM_SIMP_TAC[CONVEX_HULL_EQ_EMPTY; COMPACT_CONVEX_HULL;
                   FINITE_IMP_COMPACT; dist] THEN ASM_MESON_TAC[];
      REWRITE_TAC[dist] THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
      ASM_SIMP_TAC[BOUNDED_CONVEX_HULL; FINITE_IMP_BOUNDED] THEN
      ASM_MESON_TAC[HULL_INC]]]);;

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
    EXPAND_TAC "k" THEN REWRITE_TAC[IN_ELIM_THM; dist; VECTOR_SUB_LZERO] THEN
    REWRITE_TAC[NORM_NEG] THEN
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
    ASM_SIMP_TAC[IN_INTER; FRONTIER_CBALL; SPAN_CLAUSES; IN_ELIM_THM] THEN
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
  REWRITE_TAC[dist; VECTOR_SUB_LZERO; NORM_NEG; NORM_MUL] THEN
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

let CONVEX_INTERVAL = prove
 (`!a b:real^N. convex(interval [a,b]) /\ convex(interval (a,b))`,
  SIMP_TAC[IS_INTERVAL_CONVEX; IS_INTERVAL_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* On real^1, is_interval, convex and connected are all equivalent.          *)
(* ------------------------------------------------------------------------- *)

let IS_INTERVAL_1 = prove
 (`!s:real^1->bool.
        is_interval s <=>
          !a b x. a IN s /\ b IN s /\ drop a <= drop x /\ drop x <= drop b
                  ==> x IN s`,
  REWRITE_TAC[is_interval; DIMINDEX_1; FORALL_1; GSYM drop] THEN
  REWRITE_TAC[FORALL_LIFT; LIFT_DROP] THEN MESON_TAC[]);;

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

let IS_INTERVAL_CONVEX_1 = prove
 (`!s:real^1->bool. is_interval s <=> convex s`,
  MESON_TAC[IS_INTERVAL_CONVEX; CONVEX_CONNECTED; IS_INTERVAL_CONNECTED_1]);;

let CONVEX_CONNECTED_1 = prove
 (`!s:real^1->bool. convex s <=> connected s`,
  REWRITE_TAC[GSYM IS_INTERVAL_CONVEX_1; GSYM IS_INTERVAL_CONNECTED_1]);;

let CONNECTED_CONVEX_1 = prove
 (`!s:real^1->bool. connected s <=> convex s`,
  REWRITE_TAC[GSYM IS_INTERVAL_CONVEX_1; GSYM IS_INTERVAL_CONNECTED_1]);;

(* ------------------------------------------------------------------------- *)
(* Homeomorphism of all convex compact sets with nonempty interior.          *)
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
 (`!s:real^N->bool.
        compact s /\ cball(vec 0,&1) SUBSET s /\
        (!x u. x IN s /\ &0 <= u /\ u < &1 ==> (u % x) IN (s DIFF frontier(s)))
        ==> s homeomorphic cball(vec 0:real^N,&1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `frontier(s:real^N->bool) SUBSET s` ASSUME_TAC THENL
   [ASM_MESON_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  ABBREV_TAC `proj = \x:real^N. inv(norm(x)) % x` THEN
  SUBGOAL_THEN `~(vec(0):real^N IN frontier(s))` ASSUME_TAC THENL
   [REWRITE_TAC[FRONTIER_STRADDLE] THEN DISCH_THEN(MP_TAC o SPEC `&1`) THEN
    ASM_MESON_TAC[REAL_LT_01; IN_CBALL; SUBSET; DIST_REFL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
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
     `(a % x = a % y) <=> (a % (x - y) = vec 0)`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; NORM_EQ_0; VECTOR_SUB_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(proj:real^N->real^N) continuous_on (UNIV DELETE vec 0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[IN_DELETE; IN_UNIV] THEN EXPAND_TAC "proj" THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
    ASM_SIMP_TAC[CONTINUOUS_AT_ID] THEN
    REWRITE_TAC[GSYM(ISPEC `lift` o_DEF); GSYM(ISPEC `inv` o_DEF)] THEN
    MATCH_MP_TAC CONTINUOUS_AT_INV THEN
    ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ; CONTINUOUS_AT_LIFT_NORM];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN REWRITE_TAC[COMPACT_CBALL] THEN
  ABBREV_TAC `sphere = {x:real^N | norm(x) = &1}` THEN
  SUBGOAL_THEN
   `!x. ~(x = vec 0) ==> (proj:real^N->real^N)(x) IN sphere`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["proj"; "sphere"] THEN
    REWRITE_TAC[IN_ELIM_THM; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u x. &0 < u ==> ((proj:real^N->real^N)(u % x) = proj(x))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN ASM_CASES_TAC `x = vec 0 :real^N` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN EXPAND_TAC "proj" THEN
    REWRITE_TAC[IN_ELIM_THM; NORM_MUL; REAL_ABS_INV; REAL_INV_MUL;
                REAL_ABS_NORM] THEN SIMP_TAC[real_abs; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC `(a * b) * c = (c * a) * b`] THEN
    SIMP_TAC[REAL_LT_IMP_NZ; REAL_MUL_RINV; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `vec 0 IN (s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; CENTRE_IN_CBALL; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N u. x IN frontier(s) /\ &0 <= u ==> ((u % x) IN s <=> u <= &1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_LE_LT] THEN
      ASM_MESON_TAC[VECTOR_MUL_LID; SUBSET; IN_DIFF]] THEN
    MP_TAC
     (ISPECL [`s:real^N->bool`; `x:real^N`] COMPACT_FRONTIER_LINE_LEMMA) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real` MP_TAC) THEN
    REWRITE_TAC[GSYM REAL_NOT_LE; CONTRAPOS_THM] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    DISCH_THEN(MP_TAC o SPEC `u:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `(&0 < v ==> v <= &1) ==> u <= v ==> u <= &1`) THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`v % x:real^N`; `inv(v)`]) THEN
    ASM_SIMP_TAC[IN_DIFF; VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    ASM_SIMP_TAC[VECTOR_MUL_LID; REAL_LE_INV; REAL_NOT_LT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_INV_LE_1) THEN
    ASM_SIMP_TAC[REAL_INV_INV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `?surf. homeomorphism (frontier(s),sphere)
                                     (proj:real^N->real^N,surf)`
  MP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[COMPACT_FRONTIER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `UNIV DELETE (vec 0:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET; IN_UNIV; IN_DELETE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
       [SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
        ASM_MESON_TAC[];
        MAP_EVERY EXPAND_TAC ["sphere"; "proj"]] THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u. &0 <= u /\ (u % x :real^N) IN frontier s` MP_TAC THENL
       [ASM_MESON_TAC[COMPACT_FRONTIER_LINE_LEMMA;
                      NORM_0; SUBSET; REAL_ARITH `~(&1 = &0)`]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `u % x :real^N` THEN ASM_REWRITE_TAC[NORM_MUL] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RID; real_abs] THEN
      SUBGOAL_THEN `~(u = &0)` MP_TAC THEN
      ASM_MESON_TAC[REAL_MUL_LINV; VECTOR_MUL_LID; VECTOR_MUL_LZERO];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x y:real^N.
        x IN frontier s /\ y IN frontier s /\ (proj x = proj y :real^N)
        ==> norm y <= norm x`
    ASSUME_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LE_ANTISYM]] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(x:real^N = vec 0) /\ ~(y:real^N = vec 0)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[NORM_EQ_0; REAL_ARITH `~(&1 = &0)`]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`;
        `norm(y:real^N) / norm(x:real^N)`]) THEN
    SUBGOAL_THEN `norm(y) / norm(x) % x = y:real^N` SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `norm(y) / norm(y) % y:real^N` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[real_div; GSYM VECTOR_MUL_ASSOC] THEN ASM_MESON_TAC[];
        ASM_SIMP_TAC[REAL_DIV_REFL; NORM_EQ_0; VECTOR_MUL_LID]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; NORM_POS_LT;
                 REAL_MUL_LZERO; NORM_POS_LE; REAL_MUL_LID] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^N. ~(x = vec 0) ==> ~((surf:real^N->real^N)(proj(x)) = vec 0)`
  ASSUME_TAC THENL [ASM_MESON_TAC[IN_IMAGE; EXTENSION]; ALL_TAC] THEN
  EXISTS_TAC `\x:real^N. norm(x) % (surf:real^N->real^N)(proj(x))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x = vec 0:real^N` THENL
     [ALL_TAC;
      MATCH_MP_TAC CONTINUOUS_MUL THEN
      REWRITE_TAC[CONTINUOUS_AT_LIFT_NORM] THEN
      SUBGOAL_THEN
       `((surf:real^N->real^N) o (proj:real^N->real^N)) continuous_on
        (UNIV DELETE vec 0)`
      MP_TAC THENL
       [ALL_TAC;
        SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_DELETE; OPEN_UNIV] THEN
        ASM_SIMP_TAC[o_DEF; IN_DELETE; IN_UNIV]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `sphere:real^N->bool` THEN
      ASM_REWRITE_TAC[SUBSET; IN_IMAGE; IN_UNIV; IN_DELETE] THEN
      ASM_MESON_TAC[]] THEN
    ASM_REWRITE_TAC[CONTINUOUS_AT; LIM_AT; NORM_0; VECTOR_MUL_LZERO] THEN
    REWRITE_TAC[dist; VECTOR_SUB_RZERO] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `e / B` THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_LT_RDIV_EQ; REAL_ABS_NORM] THEN
    X_GEN_TAC `y:real^N` THEN MATCH_MP_TAC(REAL_ARITH
     `(&0 < x ==> x * c <= x * b) ==> &0 < x /\ x * b < e ==> x * c < e`) THEN
    SIMP_TAC[REAL_LE_LMUL_EQ] THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[IN_IMAGE; EXTENSION; SUBSET; NORM_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:real^N.
        (norm x % (surf:real^N->real^N)(proj x) = norm y % surf (proj y))
        ==> (x = y)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
    ASM_CASES_TAC `x = vec 0:real^N` THENL
     [ASM_REWRITE_TAC[NORM_0; VECTOR_MUL_LZERO] THEN
      ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0; NORM_EQ_0] THEN
      ASM_MESON_TAC[EXTENSION; IN_IMAGE];
      ALL_TAC] THEN
    ASM_CASES_TAC `y = vec 0:real^N` THENL
     [ASM_REWRITE_TAC[NORM_0; VECTOR_MUL_LZERO; VECTOR_MUL_EQ_0; NORM_EQ_0] THEN
       ASM_MESON_TAC[EXTENSION; IN_IMAGE];
      ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
    MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[VECTOR_MUL_RCANCEL; EXTENSION; IN_IMAGE];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `proj:real^N->real^N`) THEN
    ASM_SIMP_TAC[NORM_POS_LT];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `x = vec 0:real^N` THENL
   [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; NORM_EQ_0] THEN
    ASM_MESON_TAC[CENTRE_IN_CBALL; SUBSET; REAL_POS];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^N` MP_TAC) THEN
    ASM_CASES_TAC `y = vec 0:real^N` THEN
    ASM_REWRITE_TAC[NORM_0; VECTOR_MUL_LZERO] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`(surf:real^N->real^N)(proj(y:real^N))`; `norm(y:real^N)`]) THEN
    REWRITE_TAC[NORM_POS_LE] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[IN_IMAGE; FUN_EQ_THM]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [IN_CBALL; dist; VECTOR_SUB_LZERO; NORM_NEG]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  EXISTS_TAC `inv(norm(surf(proj x :real^N):real^N)) % x :real^N` THEN
  ASM_SIMP_TAC[NORM_POS_LT; REAL_LT_INV] THEN CONJ_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_ABS_MUL] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC `(inv x * y) * x = y * x * inv x`] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; REAL_MUL_RID] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `proj(surf(proj x):real^N):real^N` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM
       (fun th -> MATCH_MP_TAC th THEN
       ASM_SIMP_TAC[REAL_LT_INV; NORM_POS_LT; REAL_LT_MUL] THEN NO_TAC)];
    ALL_TAC] THEN
  REWRITE_TAC[IN_CBALL; dist; VECTOR_SUB_LZERO; NORM_NEG] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; NORM_POS_LT; REAL_MUL_LID] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(surf:real^N->real^N)(proj(x:real^N))`;
   `norm(x:real^N) / norm((surf:real^N->real^N)(proj(x:real^N)))`]) THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; NORM_POS_LT; REAL_LT_IMP_LE; REAL_LT_DIV] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[EXTENSION; IN_IMAGE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN
  SUBGOAL_THEN `norm x / norm(surf((proj:real^N->real^N) x)) % surf(proj x) = x`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_POS_LT; REAL_LT_IMP_NZ]);;

let HOMEOMORPHIC_CONVEX_COMPACT_LEMMA = prove
 (`!s:real^N->bool. convex s /\ compact s /\ &0 < e /\ cball(vec 0,&1) SUBSET s
                    ==> s homeomorphic cball(vec 0:real^N,&1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC STARLIKE_COMPACT_PROJECTIVE THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:real^N`; `u:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(u % x:real^N) IN interior(s)`
   (fun th -> MESON_TAC[th; frontier; SUBSET; IN_DIFF; INTERIOR_SUBSET]) THEN
  REWRITE_TAC[interior; IN_ELIM_THM] THEN
  EXISTS_TAC `ball(u % x:real^N,&1 - u)` THEN
  ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_SUB_LT] THEN
  REWRITE_TAC[SUBSET; IN_BALL; dist] THEN X_GEN_TAC `y:real^N` THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`inv(&1 - u) % (y - u % x:real^N)`; `x:real^N`; `&1 - u`; `u:real`]) THEN
  ASM_REWRITE_TAC[REAL_SUB_ADD] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; VECTOR_MUL_ASSOC; REAL_MUL_RINV;
               REAL_SUB_LT; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[VECTOR_ARITH `&1 % (y - ux) + ux = y`] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  REWRITE_TAC[IN_CBALL; NORM_MUL; dist; VECTOR_SUB_LZERO; NORM_NEG] THEN
  REWRITE_TAC[REAL_ABS_INV] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `u < &1 ==> &0 < abs(&1 - u)`] THEN
  ASM_SIMP_TAC[REAL_ARITH `x < &1 - u /\ u < &1 ==> x <= &1 * abs(&1 - u)`]);;

let HOMEOMORPHIC_CONVEX_COMPACT_CBALL = prove
 (`!s:real^N->bool b:real^N e.
        convex s /\ compact s /\ ~(interior s = {}) /\ &0 < e
        ==> s homeomorphic cball(b,e)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` MP_TAC) THEN
  REWRITE_TAC[IN_INTERIOR_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `IMAGE (\x:real^N. inv(d) % --a + inv(d) % x) s`
               HOMEOMORPHIC_CONVEX_COMPACT_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONVEX_AFFINITY; COMPACT_AFFINITY] THEN
    REWRITE_TAC[GSYM VECTOR_ADD_LDISTRIB] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (\x:real^N. inv(d) % (--a + x)) (cball(a,d))` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET] THEN
    REWRITE_TAC[SUBSET; IN_CBALL; IN_IMAGE; dist; VECTOR_SUB_LZERO] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[NORM_NEG] THEN DISCH_TAC THEN
    EXISTS_TAC `a + d % x:real^N` THEN
    REWRITE_TAC[VECTOR_ARITH `a - (a + b) = --b:real^N`;
                VECTOR_ARITH `--a + a + b = b:real^N`] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[VECTOR_MUL_LID; NORM_NEG; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> (abs d * x <= d <=> d * x <= d * &1)`;
                 REAL_LE_LMUL_EQ];
    DISCH_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN
    EXISTS_TAC `IMAGE (\x:real^N. inv d % --a + inv d % x) s` THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_AFFINITY; REAL_LT_IMP_NZ; REAL_LT_INV] THEN
    MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN
    EXISTS_TAC `cball(vec 0:real^N,&1)` THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_CBALLS; REAL_LT_01]]);;

let HOMEOMORPHIC_CONVEX_COMPACT = prove
 (`!s:real^N->bool t:real^N->bool.
        convex s /\ compact s /\ ~(interior s = {}) /\
        convex t /\ compact t /\ ~(interior t = {})
        ==> s homeomorphic t`,
  MESON_TAC[HOMEOMORPHIC_CONVEX_COMPACT_CBALL; REAL_LT_01;
            HOMEOMORPHIC_SYM; HOMEOMORPHIC_TRANS]);;

let HOMEOMORPHIC_CLOSED_INTERVALS = prove
 (`!a b:real^N c d:real^N.
        ~(interval(a,b) = {}) /\ ~(interval(c,d) = {})
        ==> interval[a,b] homeomorphic interval[c,d]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_CONVEX_COMPACT THEN
  REWRITE_TAC[CONVEX_INTERVAL; COMPACT_INTERVAL] THEN
  ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL]);;

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
(* Bounded convex function on open set is continuous.                        *)
(* ------------------------------------------------------------------------- *)

let CONVEX_ON_BOUNDED_CONTINUOUS = prove
 (`!f:real^N->real s b.
        open s /\ f convex_on s /\ (!x. x IN s ==> abs(f x) <= b)
        ==> (lift o f) continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[CONTINUOUS_AT_LIFT_RANGE] THEN
  ABBREV_TAC `B = abs(b) + &1` THEN
  SUBGOAL_THEN `&0 < B /\ !x:real^N. x IN s ==> abs(f x) <= B`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[REAL_ARITH `x <= b ==> x <= abs b + &1`];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ARITH `abs(x - y) < e <=> x - y < e /\ y - x < e`] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN REWRITE_TAC[SUBSET; IN_CBALL] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (k / &2) (e / (&2 * B) * k)` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; REAL_LT_MUL;
               REAL_OF_NUM_LT; ARITH] THEN
  X_GEN_TAC `y:real^N` THEN
  ASM_CASES_TAC `y:real^N = x` THEN ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
  STRIP_TAC THEN
  ABBREV_TAC `t = k / norm(y - x:real^N)` THEN
  SUBGOAL_THEN `&2 < t` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (REAL_ARITH
   `&2 < t ==> &0 < t /\ ~(t = &0) /\ &0 < t - &1 /\
               &0 < &1 + t /\ ~(&1 + t = &0)`)) THEN
  SUBGOAL_THEN `y:real^N IN s` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[dist] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < k / &2 ==> k / &2 <= k ==> x <= k`)) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    UNDISCH_TAC `&0 < k` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ABBREV_TAC `w:real^N = x + t % (y - x)` THEN
    SUBGOAL_THEN `w:real^N IN s` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "w" THEN
      REWRITE_TAC[dist; VECTOR_ARITH `x - (x + t) = --t:real^N`] THEN
      EXPAND_TAC "t" THEN REWRITE_TAC[NORM_NEG; NORM_MUL; REAL_ABS_DIV] THEN
      REWRITE_TAC[REAL_ABS_NORM; real_div; GSYM REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; NORM_POS_LT; VECTOR_SUB_EQ;
        REAL_MUL_RID; REAL_ARITH `&0 < x ==> abs(x) <= x`];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 / t) % w + (t - &1) / t % x = y:real^N` ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN
      REWRITE_TAC[VECTOR_ARITH
       `b % (x + c % (y - x)) + a % x =
        (a + b - b * c) % x + (b * c) % y`] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; VECTOR_MUL_LID] THEN
      ASM_SIMP_TAC[real_div; REAL_MUL_RINV; REAL_SUB_REFL;
                   VECTOR_MUL_LZERO; VECTOR_ADD_LID;
                   REAL_ARITH `(a - &1) * b + &1 * b - &1 = a * b - &1`];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [convex_on]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`w:real^N`; `x:real^N`; `&1 / t`; `(t - &1) / t`]) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_DIV; REAL_LT_01] THEN
    REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB] THEN
    ASM_SIMP_TAC[REAL_SUB_ADD2; REAL_MUL_RINV] THEN
    MATCH_MP_TAC(REAL_ARITH
     `a * fw + (b - &1) * fx < e
      ==> fy <= a * fw + b * fx ==> fy - fx < e`) THEN
    ASM_SIMP_TAC[real_div; REAL_SUB_RDISTRIB; REAL_MUL_RINV; REAL_MUL_LID;
                 REAL_ARITH `a * x + y - a * y - y = a * (x - y)`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!b. abs(x) <= b /\ abs(y) <= b /\ &2 * b < z ==> x - y < z`) THEN
    EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[real_div; REAL_ARITH `(a * b) * inv c = (b * inv c) * a`] THEN
    ASM_REWRITE_TAC[GSYM real_div];

    ABBREV_TAC `w:real^N = x - t % (y - x)` THEN
    SUBGOAL_THEN `w:real^N IN s` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "w" THEN
      REWRITE_TAC[dist; VECTOR_ARITH `x - (x - t) = t:real^N`] THEN
      EXPAND_TAC "t" THEN REWRITE_TAC[NORM_MUL; REAL_ABS_DIV] THEN
      REWRITE_TAC[REAL_ABS_NORM; real_div; GSYM REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; NORM_POS_LT; VECTOR_SUB_EQ;
        REAL_MUL_RID; REAL_ARITH `&0 < x ==> abs(x) <= x`];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 / (&1 + t)) % w + t / (&1 + t) % y = x:real^N`
    ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN
      REWRITE_TAC[VECTOR_ARITH
       `b % (x - c % (y - x)) + a % y =
        (b * (&1 + c)) % x + (a - b * c) % y`] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; VECTOR_MUL_LID] THEN
      REWRITE_TAC[real_div; REAL_MUL_AC; REAL_MUL_LID; REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [convex_on]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`w:real^N`; `y:real^N`; `&1 / (&1 + t)`; `t / (&1 + t)`]) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_DIV; REAL_LT_01] THEN
    REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB] THEN
    ASM_SIMP_TAC[REAL_SUB_ADD2; REAL_MUL_RINV] THEN
    MATCH_MP_TAC(REAL_ARITH
     `a * fw + (b - &1) * fx < e
      ==> fy <= a * fw + b * fx ==> fy - fx < e`) THEN
    SUBGOAL_THEN `t * inv(&1 + t) - &1 = --(inv(&1 + t))` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ARITH `(a * b - &1 = --b) <=> ((&1 + a) * b = &1)`] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(&1 * a) * x + --a * y = a * (x - y)`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!b. abs(x) <= b /\ abs(y) <= b /\ &2 * b < z ==> x - y < z`) THEN
    EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x < e * k ==> x < e * (&1 + k)`) THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[real_div; REAL_ARITH `(a * b) * inv c = (b * inv c) * a`] THEN
    ASM_REWRITE_TAC[GSYM real_div]]);;

(* ------------------------------------------------------------------------- *)
(* Upper bound on a ball implies upper and lower bounds.                     *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* Hence a convex function on an open set is continuous.                     *)
(* ------------------------------------------------------------------------- *)

let CONVEX_ON_CONTINUOUS = prove
 (`!f s:real^N->bool. open s /\ f convex_on s ==> lift o f continuous_on s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d = e / &(dimindex(:N))` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; DIMINDEX_GE_1;
                    ARITH_RULE `0 < d <=> 1 <= d`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?b. !y:real^N. y IN interval[(x - lambda i. d),(x + lambda i. d)]
                   ==> f(y) <= b`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x - (lambda i. d):real^N`; `x + (lambda i. d):real^N`]
        CLOSED_INTERVAL_AS_CONVEX_HULL) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `c = {}:real^N->bool` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY] THEN
    MP_TAC(ISPEC `IMAGE (f:real^N->real) c` SUP_FINITE) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
    ABBREV_TAC `k = sup(IMAGE (f:real^N->real) c)` THEN
    STRIP_TAC THEN EXISTS_TAC `k:real` THEN
    MATCH_MP_TAC CONVEX_ON_CONVEX_HULL_BOUND THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONVEX_ON_SUBSET THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball (x:real^N,e)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL; IN_CBALL] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; LAMBDA_BETA] THEN
    X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[REAL_ARITH `x - d <= z /\ z <= x + d <=> abs(x - z) <= d`] THEN
    DISCH_TAC THEN REWRITE_TAC[dist] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `sum(1..dimindex(:N)) (\i. abs((x - z:real^N)$i))` THEN
    REWRITE_TAC[NORM_LE_L1] THEN
    MATCH_MP_TAC SUM_BOUND_GEN THEN
    REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; CARD_NUMSEG] THEN
    ASM_SIMP_TAC[IN_NUMSEG; NOT_LT; DIMINDEX_GE_1; ADD_SUB;
                 VECTOR_SUB_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(x:real^N,d) SUBSET cball(x,e)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL] THEN GEN_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `d <= e ==> x <= d ==> x <= e`) THEN
    EXPAND_TAC "d" THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; DIMINDEX_GE_1;
                 ARITH_RULE `0 < x <=> 1 <= x`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_OF_NUM_LE; DIMINDEX_GE_1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^N. y IN cball(x,d) ==> abs(f(y)) <= b + &2 * abs(f(x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONVEX_BOUNDS_LEMMA THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONVEX_ON_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `y:real^N IN cball(x,d)` THEN REWRITE_TAC[IN_CBALL] THEN
    REWRITE_TAC[IN_INTERVAL; IN_CBALL; dist] THEN DISCH_TAC THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; LAMBDA_BETA] THEN
    REWRITE_TAC[REAL_ARITH `x - d <= z /\ z <= x + d <=> abs(x - z) <= d`] THEN
    SIMP_TAC[GSYM VECTOR_SUB_COMPONENT] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x - y:real^N)` THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(lift o f) continuous_on (ball(x:real^N,d))` MP_TAC THENL
   [MATCH_MP_TAC CONVEX_ON_BOUNDED_CONTINUOUS THEN REWRITE_TAC[OPEN_BALL] THEN
    EXISTS_TAC `b + &2 * abs(f(x:real^N))` THEN
    ASM_MESON_TAC[SUBSET; CONVEX_ON_SUBSET; SUBSET_TRANS; BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL; CENTRE_IN_BALL]);;

(* ------------------------------------------------------------------------- *)
(* Characterizations of convex functions in terms of sequents.               *)
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

let CONVEX_CONTAINS_SEGMENT = prove
 (`!s. convex s <=> !a b. a IN s /\ b IN s ==> segment[a,b] SUBSET s`,
  REWRITE_TAC[CONVEX_ALT; segment; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

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

(* ------------------------------------------------------------------------- *)
(* Relative interior of a set.                                               *)
(* ------------------------------------------------------------------------- *)

let relative_interior = new_definition
 `relative_interior s =
   {x | ?t. open_in (subtopology euclidean (affine hull s)) t /\
            x IN t /\ t SUBSET s}`;;

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

let RELATIVE_INTERIOR_SING = prove
 (`!a. relative_interior {a} = {a}`,
  GEN_TAC THEN MATCH_MP_TAC(SET_RULE
   `s SUBSET {a} /\ ~(s = {}) ==> s = {a}`) THEN
  SIMP_TAC[RELATIVE_INTERIOR_SUBSET; RELATIVE_INTERIOR_EQ_EMPTY;
           CONVEX_SING] THEN
  SET_TAC[]);;

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

let CONNECTED_INTER_RELATIVE_FRONTIER = prove
 (`!s t:real^N->bool.
        connected s /\ s SUBSET affine hull t /\
        ~(s INTER t = {}) /\ ~(s DIFF t = {})
        ==> ~(s INTER (closure t DIFF relative_interior t) = {})`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_LOCAL]) THEN
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
    REWRITE_TAC[GSYM CLOSED_OPEN; CLOSED_CLOSURE];
    ASM SET_TAC[];
    MATCH_MP_TAC(SET_RULE
     `i SUBSET t /\ t SUBSET c ==> (s INTER i) INTER (s DIFF c) = {}`) THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SUBSET; CLOSURE_SUBSET];
    MP_TAC(ISPEC `t:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
    MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    ASM SET_TAC[]]);;

let CLOSED_RELATIVE_FRONTIER = prove
 (`!s:real^N->bool. closed(closure s DIFF relative_interior s)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
  EXISTS_TAC `affine hull s:real^N->bool` THEN
  REWRITE_TAC[CLOSED_AFFINE_HULL] THEN MATCH_MP_TAC CLOSED_IN_DIFF THEN
  REWRITE_TAC[OPEN_IN_RELATIVE_INTERIOR] THEN
  MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
  MATCH_MP_TAC(SET_RULE
   `s SUBSET closure t /\ closure t = t ==> s SUBSET t`) THEN
  SIMP_TAC[SUBSET_CLOSURE; HULL_SUBSET; CLOSURE_EQ; CLOSED_AFFINE_HULL]);;

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

(* ------------------------------------------------------------------------- *)
(* Slightly shaper supporting hyperplane results.                            *)
(* ------------------------------------------------------------------------- *)

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
        ==> closure(convex hull s) DIFF relative_interior(convex hull s) =
                {y | ?u. (!x. x IN s ==> &0 <= u x) /\
                         (?x. x IN s /\ u x = &0) /\
                         sum s u = &1 /\
                         vsum s (\x. u x % x) = y}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNIONS_GSPEC] THEN
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
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
    MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ s = UNIV ==> t = UNIV`) THEN
    EXISTS_TAC `affine hull s:real^N->bool` THEN
    ASM_SIMP_TAC[AFFINE_INDEPENDENT_SPAN_GT; HULL_MONO; HULL_SUBSET]]);;

let RELATIVE_FRONTIER_CONVEX_HULL_CASES = prove
 (`!s:real^N->bool.
        ~(affine_dependent s)
        ==> closure(convex hull s) DIFF relative_interior(convex hull s) =
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
  ASM_SIMP_TAC[frontier; CLOSURE_CONVEX_HULL; FINITE_IMP_COMPACT] THEN
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
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; dist] THEN
    MATCH_MP_TAC COMPONENT_LE_NORM THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Paths.                                                                    *)
(* ------------------------------------------------------------------------- *)

let path = new_definition
 `!g:real^1->real^N. path g <=> g continuous_on interval[vec 0,vec 1]`;;

let pathstart = new_definition
 `pathstart (g:real^1->real^N) = g(vec 0)`;;

let pathfinish = new_definition
 `pathfinish (g:real^1->real^N) = g(vec 1)`;;

let path_image = new_definition
 `path_image (g:real^1->real^N) = IMAGE g (interval[vec 0,vec 1])`;;

let reversepath = new_definition
 `reversepath (g:real^1->real^N) = \x. g(vec 1 - x)`;;

let joinpaths = new_definition
 `(g1 ++ g2) = \x. if drop x <= &1 / &2 then g1(&2 % x)
                   else g2(&2 % x - vec 1)`;;

let simple_path = new_definition
 `simple_path (g:real^1->real^N) <=>
        path g /\
        !x y. x IN interval[vec 0,vec 1] /\
              y IN interval[vec 0,vec 1] /\
              g x = g y
              ==> x = y \/ x = vec 0 /\ y = vec 1 \/ x = vec 1 /\ y = vec 0`;;

let arc = new_definition
 `arc (g:real^1->real^N) <=>
        path g /\
        !x y. x IN interval [vec 0,vec 1] /\
              y IN interval [vec 0,vec 1] /\
              g x = g y
              ==> x = y`;;

(* ------------------------------------------------------------------------- *)
(* Invariance theorems.                                                      *)
(* ------------------------------------------------------------------------- *)

let PATH_CONTINUOUS_IMAGE = prove
 (`!f:real^M->real^N g.
     path g /\ f continuous_on path_image g ==> path(f o g)`,
  REWRITE_TAC[path; path_image; CONTINUOUS_ON_COMPOSE]);;

let PATH_TRANSLATION_EQ = prove
 (`!a g:real^1->real^N. path((\x. a + x) o g) <=> path g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path] THEN EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `(g:real^1->real^N) = (\x. --a + x) o (\x. a + x) o g`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN VECTOR_ARITH_TAC; ALL_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST]);;

add_translation_invariants [PATH_TRANSLATION_EQ];;

let PATH_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N g.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (path(f o g) <=> path g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `h:real^N->real^M` STRIP_ASSUME_TAC o
        MATCH_MP LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  REWRITE_TAC[path] THEN EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `g:real^1->real^M = h o (f:real^M->real^N) o g`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[o_ASSOC; I_O_ID]; ALL_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON]);;

add_linear_invariants [PATH_LINEAR_IMAGE_EQ];;

let PATHSTART_TRANSLATION = prove
 (`!a g. pathstart((\x. a + x) o g) = a + pathstart g`,
  REWRITE_TAC[pathstart; o_THM]);;

add_translation_invariants [PATHSTART_TRANSLATION];;

let PATHSTART_LINEAR_IMAGE_EQ = prove
 (`!f g. linear f ==> pathstart(f o g) = f(pathstart g)`,
  REWRITE_TAC[pathstart; o_THM]);;

add_linear_invariants [PATHSTART_LINEAR_IMAGE_EQ];;

let PATHFINISH_TRANSLATION = prove
 (`!a g. pathfinish((\x. a + x) o g) = a + pathfinish g`,
  REWRITE_TAC[pathfinish; o_THM]);;

add_translation_invariants [PATHFINISH_TRANSLATION];;

let PATHFINISH_LINEAR_IMAGE = prove
 (`!f g. linear f ==> pathfinish(f o g) = f(pathfinish g)`,
  REWRITE_TAC[pathfinish; o_THM]);;

add_linear_invariants [PATHFINISH_LINEAR_IMAGE];;

let PATH_IMAGE_TRANSLATION = prove
 (`!a g. path_image((\x. a + x) o g) = IMAGE (\x. a + x) (path_image g)`,
  REWRITE_TAC[path_image; IMAGE_o]);;

add_translation_invariants [PATH_IMAGE_TRANSLATION];;

let PATH_IMAGE_LINEAR_IMAGE = prove
 (`!f g. linear f ==> path_image(f o g) = IMAGE f (path_image g)`,
  REWRITE_TAC[path_image; IMAGE_o]);;

add_linear_invariants [PATH_IMAGE_LINEAR_IMAGE];;

let REVERSEPATH_TRANSLATION = prove
 (`!a g. reversepath((\x. a + x) o g) = (\x. a + x) o reversepath g`,
  REWRITE_TAC[FUN_EQ_THM; reversepath; o_THM]);;

add_translation_invariants [REVERSEPATH_TRANSLATION];;

let REVERSEPATH_LINEAR_IMAGE = prove
 (`!f g. linear f ==> reversepath(f o g) = f o reversepath g`,
  REWRITE_TAC[FUN_EQ_THM; reversepath; o_THM]);;

add_linear_invariants [REVERSEPATH_LINEAR_IMAGE];;

let JOINPATHS_TRANSLATION = prove
 (`!a:real^N g1 g2. ((\x. a + x) o g1) ++ ((\x. a + x) o g2) =
                    (\x. a + x) o (g1 ++ g2)`,
  REWRITE_TAC[joinpaths; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[o_THM]);;

add_translation_invariants [JOINPATHS_TRANSLATION];;

let JOINPATHS_LINEAR_IMAGE = prove
 (`!f g1 g2. linear f ==> (f o g1) ++ (f o g2) = f o (g1 ++ g2)`,
  REWRITE_TAC[joinpaths; FUN_EQ_THM] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[o_THM]);;

add_linear_invariants [JOINPATHS_LINEAR_IMAGE];;

let SIMPLE_PATH_TRANSLATION_EQ = prove
 (`!a g:real^1->real^N. simple_path((\x. a + x) o g) <=> simple_path g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simple_path; PATH_TRANSLATION_EQ] THEN
  REWRITE_TAC[o_THM; VECTOR_ARITH `a + x:real^N = a + y <=> x = y`]);;

add_translation_invariants [SIMPLE_PATH_TRANSLATION_EQ];;

let SIMPLE_PATH_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N g.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (simple_path(f o g) <=> simple_path g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simple_path; PATH_TRANSLATION_EQ] THEN
  BINOP_TAC THENL [ASM_MESON_TAC[PATH_LINEAR_IMAGE_EQ]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]);;

add_linear_invariants [SIMPLE_PATH_LINEAR_IMAGE_EQ];;

let ARC_TRANSLATION_EQ = prove
 (`!a g:real^1->real^N. arc((\x. a + x) o g) <=> arc g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[arc; PATH_TRANSLATION_EQ] THEN
  REWRITE_TAC[o_THM; VECTOR_ARITH `a + x:real^N = a + y <=> x = y`]);;

add_translation_invariants [ARC_TRANSLATION_EQ];;

let ARC_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N g.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (arc(f o g) <=> arc g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[arc; PATH_TRANSLATION_EQ] THEN
  BINOP_TAC THENL [ASM_MESON_TAC[PATH_LINEAR_IMAGE_EQ]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]);;

add_linear_invariants [ARC_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Basic lemmas about paths.                                                 *)
(* ------------------------------------------------------------------------- *)

let ARC_IMP_SIMPLE_PATH = prove
 (`!g. arc g ==> simple_path g`,
  REWRITE_TAC[arc; simple_path] THEN MESON_TAC[]);;

let ARC_IMP_PATH = prove
 (`!g. arc g ==> path g`,
  REWRITE_TAC[arc] THEN MESON_TAC[]);;

let SIMPLE_PATH_IMP_PATH = prove
 (`!g. simple_path g ==> path g`,
  REWRITE_TAC[simple_path] THEN MESON_TAC[]);;

let SIMPLE_PATH_CASES = prove
 (`!g:real^1->real^N. simple_path g ==> arc g \/ pathfinish g = pathstart g`,
  REWRITE_TAC[simple_path; arc; pathfinish; pathstart] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(g:real^1->real^N) (vec 0) = g(vec 1)` THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^1`; `v:real^1`]) THEN
  ASM_MESON_TAC[]);;

let SIMPLE_PATH_IMP_ARC = prove
 (`!g:real^1->real^N.
        simple_path g /\ ~(pathfinish g = pathstart g) ==> arc g`,
  MESON_TAC[SIMPLE_PATH_CASES]);;

let ARC_DISTINCT_ENDS = prove
 (`!g:real^1->real^N. arc g ==> ~(pathfinish g = pathstart g)`,
  GEN_TAC THEN REWRITE_TAC[arc; pathfinish; pathstart] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> a /\ b /\ ~d ==> ~c`] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[GSYM DROP_EQ; IN_INTERVAL_1; DROP_VEC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let ARC_SIMPLE_PATH = prove
 (`!g:real^1->real^N.
        arc g <=> simple_path g /\ ~(pathfinish g = pathstart g)`,
  MESON_TAC[SIMPLE_PATH_CASES; ARC_IMP_SIMPLE_PATH; ARC_DISTINCT_ENDS]);;

let PATH_IMAGE_NONEMPTY = prove
 (`!g. ~(path_image g = {})`,
  REWRITE_TAC[path_image; IMAGE_EQ_EMPTY; INTERVAL_EQ_EMPTY] THEN
  SIMP_TAC[DIMINDEX_1; CONJ_ASSOC; LE_ANTISYM; UNWIND_THM1; VEC_COMPONENT;
           ARITH; REAL_OF_NUM_LT]);;

let PATHSTART_IN_PATH_IMAGE = prove
 (`!g. (pathstart g) IN path_image g`,
  GEN_TAC THEN REWRITE_TAC[pathstart; path_image] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS]);;

let PATHFINISH_IN_PATH_IMAGE = prove
 (`!g. (pathfinish g) IN path_image g`,
  GEN_TAC THEN REWRITE_TAC[pathfinish; path_image] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC);;

let CONNECTED_PATH_IMAGE = prove
 (`!g. path g ==> connected(path_image g)`,
  REWRITE_TAC[path; path_image] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERVAL]);;

let COMPACT_PATH_IMAGE = prove
 (`!g. path g ==> compact(path_image g)`,
  REWRITE_TAC[path; path_image] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL]);;

let BOUNDED_PATH_IMAGE = prove
 (`!g. path g ==> bounded(path_image g)`,
  MESON_TAC[COMPACT_PATH_IMAGE; COMPACT_IMP_BOUNDED]);;

let CLOSED_PATH_IMAGE = prove
 (`!g. path g ==> closed(path_image g)`,
  MESON_TAC[COMPACT_PATH_IMAGE; COMPACT_IMP_CLOSED]);;

let CONNECTED_SIMPLE_PATH_IMAGE = prove
 (`!g. simple_path g ==> connected(path_image g)`,
  MESON_TAC[CONNECTED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH]);;

let COMPACT_SIMPLE_PATH_IMAGE = prove
 (`!g. simple_path g ==> compact(path_image g)`,
  MESON_TAC[COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH]);;

let BOUNDED_SIMPLE_PATH_IMAGE = prove
 (`!g. simple_path g ==> bounded(path_image g)`,
  MESON_TAC[BOUNDED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH]);;

let CLOSED_SIMPLE_PATH_IMAGE = prove
 (`!g. simple_path g ==> closed(path_image g)`,
  MESON_TAC[CLOSED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH]);;

let CONNECTED_ARC_IMAGE = prove
 (`!g. arc g ==> connected(path_image g)`,
  MESON_TAC[CONNECTED_PATH_IMAGE; ARC_IMP_PATH]);;

let COMPACT_ARC_IMAGE = prove
 (`!g. arc g ==> compact(path_image g)`,
  MESON_TAC[COMPACT_PATH_IMAGE; ARC_IMP_PATH]);;

let BOUNDED_ARC_IMAGE = prove
 (`!g. arc g ==> bounded(path_image g)`,
  MESON_TAC[BOUNDED_PATH_IMAGE; ARC_IMP_PATH]);;

let CLOSED_ARC_IMAGE = prove
 (`!g. arc g ==> closed(path_image g)`,
  MESON_TAC[CLOSED_PATH_IMAGE; ARC_IMP_PATH]);;

(* ------------------------------------------------------------------------- *)
(* Simple paths with the endpoints removed.                                  *)
(* ------------------------------------------------------------------------- *)

let SIMPLE_PATH_ENDLESS = prove
 (`!c:real^1->real^N.
        simple_path c
        ==> path_image c DIFF {pathstart c,pathfinish c} =
            IMAGE c (interval(vec 0,vec 1))`,
  REWRITE_TAC[simple_path; path_image; pathstart; pathfinish] THEN
  REWRITE_TAC[OPEN_CLOSED_INTERVAL_1; path] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
   `(!x y. x IN s /\ y IN s /\ c x = c y
           ==> x = y \/ x = a /\ y = b \/ x = b /\ y = a) /\
    a IN s /\ b IN s
    ==>  IMAGE c s DIFF {c a,c b} = IMAGE c (s DIFF {a,b})`) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL]);;

let CONNECTED_SIMPLE_PATH_ENDLESS = prove
 (`!c:real^1->real^N.
        simple_path c
        ==> connected(path_image c DIFF {pathstart c,pathfinish c})`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SIMPLE_PATH_ENDLESS] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
  SIMP_TAC[CONVEX_INTERVAL; CONVEX_CONNECTED] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[simple_path; path]) THEN
  ASM_REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED]);;

let NONEMPTY_SIMPLE_PATH_ENDLESS = prove
 (`!c:real^1->real^N.
      simple_path c ==> ~(path_image c DIFF {pathstart c,pathfinish c} = {})`,
  SIMP_TAC[SIMPLE_PATH_ENDLESS; IMAGE_EQ_EMPTY; INTERVAL_EQ_EMPTY_1] THEN
  REWRITE_TAC[DROP_VEC] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The operations on paths.                                                  *)
(* ------------------------------------------------------------------------- *)

let JOINPATHS = prove
 (`!g1 g2. pathfinish g1 = pathstart g2
           ==> g1 ++ g2 = \x. if drop x < &1 / &2 then g1(&2 % x)
                              else g2 (&2 % x - vec 1)`,
  REWRITE_TAC[pathstart; pathfinish] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[joinpaths; FUN_EQ_THM] THEN
  X_GEN_TAC `x:real^1` THEN ASM_CASES_TAC `drop x = &1 / &2` THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `lift`) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LIFT_DROP; REAL_LE_REFL; GSYM LIFT_CMUL; REAL_LT_REFL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[LIFT_NUM; VECTOR_SUB_REFL];
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC]);;

let REVERSEPATH_REVERSEPATH = prove
 (`!g:real^1->real^N. reversepath(reversepath g) = g`,
  REWRITE_TAC[reversepath; ETA_AX;
              VECTOR_ARITH `vec 1 - (vec 1 - x):real^1 = x`]);;

let PATHSTART_REVERSEPATH = prove
 (`pathstart(reversepath g) = pathfinish g`,
  REWRITE_TAC[pathstart; reversepath; pathfinish; VECTOR_SUB_RZERO]);;

let PATHFINISH_REVERSEPATH = prove
 (`pathfinish(reversepath g) = pathstart g`,
  REWRITE_TAC[pathstart; reversepath; pathfinish; VECTOR_SUB_REFL]);;

let PATHSTART_JOIN = prove
 (`!g1 g2. pathstart(g1 ++ g2) = pathstart g1`,
  REWRITE_TAC[joinpaths; pathstart; pathstart; DROP_VEC; VECTOR_MUL_RZERO] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let PATHFINISH_JOIN = prove
 (`!g1 g2. pathfinish(g1 ++ g2) = pathfinish g2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[joinpaths; pathfinish; DROP_VEC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC);;

let PATH_IMAGE_REVERSEPATH = prove
 (`!g:real^1->real^N. path_image(reversepath g) = path_image g`,
  SUBGOAL_THEN `!g:real^1->real^N.
      path_image(reversepath g) SUBSET path_image g`
   (fun th -> MESON_TAC[th; REVERSEPATH_REVERSEPATH; SUBSET_ANTISYM]) THEN
  REWRITE_TAC[SUBSET; path_image; FORALL_IN_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`g:real^1->real^N`; `x:real^1`] THEN
  DISCH_TAC THEN REWRITE_TAC[reversepath; IN_IMAGE] THEN
  EXISTS_TAC `vec 1 - x:real^1` THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN REAL_ARITH_TAC);;

let PATH_REVERSEPATH = prove
 (`!g:real^1->real^N. path(reversepath g) <=> path g`,
  SUBGOAL_THEN `!g:real^1->real^N. path g ==> path(reversepath g)`
   (fun th -> MESON_TAC[th; REVERSEPATH_REVERSEPATH]) THEN
  GEN_TAC THEN REWRITE_TAC[path; reversepath] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1] THEN
  REWRITE_TAC[DROP_VEC; DROP_SUB] THEN REAL_ARITH_TAC);;

let PATH_JOIN = prove
 (`!g1 g2:real^1->real^N.
        pathfinish g1 = pathstart g2
        ==> (path(g1 ++ g2) <=> path g1 /\ path g2)`,
  REWRITE_TAC[path; pathfinish; pathstart] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(g1:real^1->real^N) = (\x. g1 (&2 % x)) o (\x. &1 / &2 % x)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
        VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID] THEN
      MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `(g1 ++ g2):real^1->real^N` THEN CONJ_TAC THENL
       [REWRITE_TAC[FORALL_IN_IMAGE; joinpaths; IN_INTERVAL_1; DROP_CMUL] THEN
        SIMP_TAC[DROP_VEC; REAL_ARITH `&1 / &2 * x <= &1 / &2 <=> x <= &1`];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_CMUL] THEN
      REWRITE_TAC[DROP_VEC] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN
       `(g2:real^1->real^N) =
        (\x. g2 (&2 % x - vec 1)) o (\x. &1 / &2 % (x + vec 1))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
        VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST;
               CONTINUOUS_ON_ADD] THEN
      MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `(g1 ++ g2):real^1->real^N` THEN CONJ_TAC THENL
       [REWRITE_TAC[FORALL_IN_IMAGE; joinpaths; IN_INTERVAL_1; DROP_CMUL] THEN
        REWRITE_TAC[DROP_VEC; DROP_ADD; REAL_ARITH
         `&1 / &2 * (x + &1) <= &1 / &2 <=> x <= &0`] THEN
        SIMP_TAC[REAL_ARITH `&0 <= x ==> (x <= &0 <=> x = &0)`; LIFT_NUM;
          VECTOR_MUL_ASSOC; GSYM LIFT_EQ; LIFT_DROP; GSYM LIFT_CMUL] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_REWRITE_TAC[VECTOR_ADD_LID; VECTOR_MUL_LID] THEN
        REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[VECTOR_ARITH `(x + vec 1) - vec 1 = x`];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_CMUL] THEN
      REWRITE_TAC[DROP_VEC; DROP_ADD] THEN REAL_ARITH_TAC];
    STRIP_TAC THEN
    SUBGOAL_THEN `interval[vec 0,vec 1] =
                  interval[vec 0,lift(&1 / &2)] UNION
                  interval[lift(&1 / &2),vec 1]`
    SUBST1_TAC THENL
     [SIMP_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_UNION THEN REWRITE_TAC[CLOSED_INTERVAL] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THENL
     [EXISTS_TAC `\x. (g1:real^1->real^N) (&2 % x)`;
      EXISTS_TAC `\x. (g2:real^1->real^N) (&2 % x - vec 1)`] THEN
    REWRITE_TAC[joinpaths] THEN SIMP_TAC[IN_INTERVAL_1; LIFT_DROP] THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID] THEN
      ONCE_REWRITE_TAC[VECTOR_ARITH `&2 % (x:real^1) = &2 % x + vec 0`] THEN
      REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
      REWRITE_TAC[REAL_POS; INTERVAL_EQ_EMPTY_1; LIFT_DROP; DROP_VEC] THEN
      REWRITE_TAC[GSYM LIFT_CMUL; VECTOR_ADD_RID; VECTOR_MUL_RZERO] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[LIFT_NUM];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SIMP_TAC[REAL_ARITH `&1 / &2 <= x ==> (x <= &1 / &2 <=> x = &1 / &2)`;
               GSYM LIFT_EQ; LIFT_DROP; GSYM LIFT_CMUL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
      ASM_REWRITE_TAC[LIFT_NUM] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM LIFT_CMUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[LIFT_NUM; VECTOR_SUB_REFL];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST;
             CONTINUOUS_ON_ID] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `&2 % x - vec 1 = &2 % x + --vec 1`] THEN
    REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
    REWRITE_TAC[REAL_POS; INTERVAL_EQ_EMPTY_1; LIFT_DROP; DROP_VEC] THEN
    REWRITE_TAC[GSYM LIFT_CMUL; VECTOR_ADD_RID; VECTOR_MUL_RZERO] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[LIFT_NUM] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `&2 % x + --x = x /\ x + --x = vec 0`]]);;

let PATH_JOIN_IMP = prove
 (`!g1 g2:real^1->real^N.
        path g1 /\ path g2 /\ pathfinish g1 = pathstart g2
        ==> path(g1 ++ g2)`,
  MESON_TAC[PATH_JOIN]);;

let PATH_IMAGE_JOIN_SUBSET = prove
 (`!g1 g2:real^1->real^N.
        path_image(g1 ++ g2) SUBSET (path_image g1 UNION path_image g2)`,
  REWRITE_TAC[path_image; FORALL_IN_IMAGE; SUBSET] THEN
  GEN_TAC THEN GEN_TAC THEN X_GEN_TAC `x:real^1` THEN
  REWRITE_TAC[IN_INTERVAL_1; IN_UNION; IN_IMAGE; DROP_VEC; joinpaths] THEN
  STRIP_TAC THEN ASM_CASES_TAC `drop x <= &1 / &2` THEN ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC THEN EXISTS_TAC `&2 % x:real^1` THEN REWRITE_TAC[DROP_CMUL];
    DISJ2_TAC THEN EXISTS_TAC `&2 % x - vec 1:real^1` THEN
    REWRITE_TAC[DROP_CMUL; DROP_SUB; DROP_VEC]] THEN
  ASM_REAL_ARITH_TAC);;

let SUBSET_PATH_IMAGE_JOIN = prove
 (`!g1 g2:real^1->real^N s.
        path_image g1 SUBSET s /\ path_image g2 SUBSET s
        ==> path_image(g1 ++ g2) SUBSET s`,
  MP_TAC PATH_IMAGE_JOIN_SUBSET THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  SET_TAC[]);;

let PATH_IMAGE_JOIN = prove
 (`!g1 g2. path g1 /\ path g2 /\ pathfinish g1 = pathstart g2
           ==> path_image(g1 ++ g2) = path_image g1 UNION path_image g2`,
  REWRITE_TAC[pathfinish; pathstart] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[PATH_IMAGE_JOIN_SUBSET] THEN
  REWRITE_TAC[path_image; SUBSET; FORALL_AND_THM; IN_UNION; TAUT
                `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; joinpaths] THEN
  REWRITE_TAC[IN_INTERVAL_1; IN_IMAGE; DROP_VEC] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^1` THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC `(&1 / &2) % x:real^1` THEN
    ASM_REWRITE_TAC[DROP_CMUL; REAL_ARITH
     `&1 / &2 * x <= &1 / &2 <=> x <= &1`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID];
    EXISTS_TAC `(&1 / &2) % (x + vec 1):real^1` THEN
    ASM_REWRITE_TAC[DROP_CMUL; DROP_ADD; DROP_VEC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID; VECTOR_ARITH `(x + vec 1) - vec 1 = x`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> (&1 / &2 * (x + &1) <= &1 / &2 <=>
                                          x = &0)`] THEN
    REWRITE_TAC[GSYM LIFT_EQ; LIFT_DROP; LIFT_NUM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_ADD_LID; DROP_VEC]] THEN
  ASM_REAL_ARITH_TAC);;

let NOT_IN_PATH_IMAGE_JOIN = prove
 (`!g1 g2 x. ~(x IN path_image g1) /\ ~(x IN path_image g2)
             ==> ~(x IN path_image(g1 ++ g2))`,
  MESON_TAC[PATH_IMAGE_JOIN_SUBSET; SUBSET; IN_UNION]);;

let ARC_REVERSEPATH = prove
 (`!g. arc g ==> arc(reversepath g)`,
  GEN_TAC THEN SIMP_TAC[arc; PATH_REVERSEPATH] THEN
  REWRITE_TAC[arc; reversepath] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`vec 1 - x:real^1`; `vec 1 - y:real^1`]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ; DROP_SUB; DROP_VEC] THEN
  REAL_ARITH_TAC);;

let SIMPLE_PATH_REVERSEPATH = prove
 (`!g. simple_path g ==> simple_path (reversepath g)`,
  GEN_TAC THEN SIMP_TAC[simple_path; PATH_REVERSEPATH] THEN
  REWRITE_TAC[simple_path; reversepath] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`vec 1 - x:real^1`; `vec 1 - y:real^1`]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ; DROP_SUB; DROP_VEC] THEN
  REAL_ARITH_TAC);;

let SIMPLE_PATH_JOIN_LOOP = prove
 (`!g1 g2:real^1->real^N.
        arc g1 /\ arc g2 /\
        pathfinish g1 = pathstart g2 /\
        pathfinish g2 = pathstart g1 /\
        (path_image g1 INTER path_image g2) SUBSET
            {pathstart g1,pathstart g2}
        ==> simple_path(g1 ++ g2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[arc; simple_path] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ b /\ c /\ d ==> f) /\
    (a' /\ b' /\ c /\ d /\ e ==> g)
    ==> (a /\ a') /\ (b /\ b') /\ c /\ d /\ e ==> f /\ g`) THEN
  CONJ_TAC THENL [MESON_TAC[PATH_JOIN]; ALL_TAC] THEN
  REWRITE_TAC[arc; simple_path; SUBSET; IN_INTER; pathstart;
    pathfinish; IN_INTERVAL_1; DROP_VEC; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G1") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G2") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G0")) THEN
  MATCH_MP_TAC DROP_WLOG_LE THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[joinpaths] THEN
  MAP_EVERY ASM_CASES_TAC [`drop x <= &1 / &2`; `drop y <= &1 / &2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [REMOVE_THEN "G1" (MP_TAC o SPECL [`&2 % x:real^1`; `&2 % y:real^1`]) THEN
    ASM_REWRITE_TAC[DROP_CMUL; DROP_VEC; DROP_SUB] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> DISJ1_TAC THEN MP_TAC th) THEN VECTOR_ARITH_TAC;
    ALL_TAC;
    ASM_REAL_ARITH_TAC;
    REMOVE_THEN "G2" (MP_TAC o SPECL
     [`&2 % x:real^1 - vec 1`; `&2 % y:real^1 - vec 1`]) THEN
    ASM_REWRITE_TAC[DROP_CMUL; DROP_VEC; DROP_SUB] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> DISJ1_TAC THEN MP_TAC th) THEN VECTOR_ARITH_TAC] THEN
  REMOVE_THEN "G0" (MP_TAC o SPEC `(g1:real^1->real^N) (&2 % x)`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[path_image; IN_IMAGE] THEN EXISTS_TAC `&2 % x:real^1` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[path_image; IN_IMAGE] THEN
      EXISTS_TAC `&2 % y:real^1 - vec 1` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; DROP_SUB] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ2_TAC THEN DISJ1_TAC;
    DISJ1_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `&1 / &2 % vec 1:real^1`] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&2 % x:real^1 = vec 0` MP_TAC THENL
     [ALL_TAC; VECTOR_ARITH_TAC] THEN
    REMOVE_THEN "G1" MATCH_MP_TAC;
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_MUL_RZERO]) THEN
    UNDISCH_TAC `T` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 % y:real^1 - vec 1 = vec 1` MP_TAC THENL
     [ALL_TAC; VECTOR_ARITH_TAC] THEN
    REMOVE_THEN "G2" MATCH_MP_TAC;
    SUBGOAL_THEN `&2 % x:real^1 = vec 1` MP_TAC THENL
     [ALL_TAC; VECTOR_ARITH_TAC] THEN
    REMOVE_THEN "G1" MATCH_MP_TAC;
    DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `&2 % y:real^1 - vec 1 = vec 0` MP_TAC THENL
     [ALL_TAC; VECTOR_ARITH_TAC] THEN
    REMOVE_THEN "G2" MATCH_MP_TAC] THEN
  (REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
    [ALL_TAC; ASM_MESON_TAC[]] THEN
   ASM_REWRITE_TAC[DROP_CMUL; DROP_SUB; DROP_VEC] THEN
   ASM_REAL_ARITH_TAC));;

let ARC_JOIN = prove
 (`!g1 g2:real^1->real^N.
        arc g1 /\ arc g2 /\
        pathfinish g1 = pathstart g2 /\
        (path_image g1 INTER path_image g2) SUBSET {pathstart g2}
        ==> arc(g1 ++ g2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[arc; simple_path] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ b /\ c /\ d ==> f) /\
    (a' /\ b' /\ c /\ d ==> g)
    ==> (a /\ a') /\ (b /\ b') /\ c /\ d ==> f /\ g`) THEN
  CONJ_TAC THENL [MESON_TAC[PATH_JOIN]; ALL_TAC] THEN
  REWRITE_TAC[arc; simple_path; SUBSET; IN_INTER; pathstart;
    pathfinish; IN_INTERVAL_1; DROP_VEC; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G1") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G2") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G0")) THEN
  MATCH_MP_TAC DROP_WLOG_LE THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[joinpaths] THEN
  MAP_EVERY ASM_CASES_TAC [`drop x <= &1 / &2`; `drop y <= &1 / &2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [REMOVE_THEN "G1" (MP_TAC o SPECL [`&2 % x:real^1`; `&2 % y:real^1`]) THEN
    ASM_REWRITE_TAC[DROP_CMUL; DROP_VEC; DROP_SUB] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC;
    ASM_REAL_ARITH_TAC;
    REMOVE_THEN "G2" (MP_TAC o SPECL
     [`&2 % x:real^1 - vec 1`; `&2 % y:real^1 - vec 1`]) THEN
    ASM_REWRITE_TAC[DROP_CMUL; DROP_VEC; DROP_SUB] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    VECTOR_ARITH_TAC] THEN
  REMOVE_THEN "G0" (MP_TAC o SPEC `(g1:real^1->real^N) (&2 % x)`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[path_image; IN_IMAGE] THEN EXISTS_TAC `&2 % x:real^1` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[path_image; IN_IMAGE] THEN
      EXISTS_TAC `&2 % y:real^1 - vec 1` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; DROP_SUB] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `x:real^1 = &1 / &2 % vec 1` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `&2 % x:real^1 = vec 1` MP_TAC THENL
     [ALL_TAC; VECTOR_ARITH_TAC] THEN
    REMOVE_THEN "G1" MATCH_MP_TAC;
    SUBGOAL_THEN `&2 % y:real^1 - vec 1 = vec 0` MP_TAC THENL
     [ALL_TAC; VECTOR_ARITH_TAC] THEN
    REMOVE_THEN "G2" MATCH_MP_TAC] THEN
  (REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
    [ALL_TAC; ASM_MESON_TAC[]] THEN
   ASM_REWRITE_TAC[DROP_CMUL; DROP_SUB; DROP_VEC] THEN
   ASM_REAL_ARITH_TAC));;

let REVERSEPATH_JOINPATHS = prove
 (`!g1 g2. pathfinish g1 = pathstart g2
           ==> reversepath(g1 ++ g2) = reversepath g2 ++ reversepath g1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[reversepath; joinpaths; pathfinish; pathstart; FUN_EQ_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `t:real^1` THEN
  REWRITE_TAC[DROP_VEC; DROP_SUB; REAL_ARITH
   `&1 - x <= &1 / &2 <=> &1 / &2 <= x`] THEN
  ASM_CASES_TAC `t = lift(&1 / &2)` THENL
   [ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_REFL; GSYM LIFT_NUM; GSYM LIFT_SUB;
                    GSYM LIFT_CMUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[LIFT_NUM];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM DROP_EQ]) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH
     `~(x = &1 / &2) ==> (&1 / &2 <= x <=> ~(x <= &1 / &2))`] THEN
    ASM_CASES_TAC `drop t <= &1 / &2` THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN REWRITE_TAC[VECTOR_SUB_LDISTRIB] THEN VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Some reversed and "if and only if" versions of joining theorems.          *)
(* ------------------------------------------------------------------------- *)

let PATH_JOIN_PATH_ENDS = prove
 (`!g1 g2:real^1->real^N.
        path g2 /\ path(g1 ++ g2) ==> pathfinish g1 = pathstart g2`,
  REPEAT GEN_TAC THEN DISJ_CASES_TAC(NORM_ARITH
   `pathfinish g1:real^N = pathstart g2 \/
    &0 < dist(pathfinish g1,pathstart g2)`) THEN
  ASM_REWRITE_TAC[path; continuous_on; joinpaths] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
  REWRITE_TAC[pathstart; pathfinish] THEN
  ABBREV_TAC `e = dist((g1:real^1->real^N)(vec 1),g2(vec 0:real^1))` THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (MP_TAC o SPEC `vec 0:real^1`) (MP_TAC o SPEC `lift(&1 / &2)`)) THEN
  REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; LIFT_DROP; REAL_LE_REFL] THEN
  REWRITE_TAC[GSYM LIFT_CMUL; IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LIFT_NUM] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "1"))) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "2"))) THEN
  REMOVE_THEN "2" (MP_TAC o SPEC `lift(min (&1 / &2) (min d1 d2) / &2)`) THEN
  REWRITE_TAC[LIFT_DROP; DIST_LIFT; DIST_0; NORM_REAL; GSYM drop] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "1" (MP_TAC o SPEC
   `lift(&1 / &2 + min (&1 / &2) (min d1 d2) / &4)`) THEN
  REWRITE_TAC[LIFT_DROP; DIST_LIFT] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_CMUL; LIFT_ADD; REAL_ADD_LDISTRIB] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LIFT_NUM] THEN
  REWRITE_TAC[VECTOR_ADD_SUB; REAL_ARITH `&2 * x / &4 = x / &2`] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN NORM_ARITH_TAC);;

let PATH_JOIN_EQ = prove
 (`!g1 g2:real^1->real^N.
        path g1 /\ path g2
        ==> (path(g1 ++ g2) <=> pathfinish g1 = pathstart g2)`,
  MESON_TAC[PATH_JOIN_PATH_ENDS; PATH_JOIN_IMP]);;

let SIMPLE_PATH_JOIN_IMP = prove
 (`!g1 g2:real^1->real^N.
        simple_path(g1 ++ g2) /\ pathfinish g1 = pathstart g2
        ==> arc g1 /\ arc g2 /\
            path_image g1 INTER path_image g2 SUBSET
            {pathstart g1, pathstart g2}`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `path(g1:real^1->real^N) /\ path(g2:real^1->real^N)` THENL
   [ALL_TAC; ASM_MESON_TAC[PATH_JOIN; SIMPLE_PATH_IMP_PATH]] THEN
  REWRITE_TAC[simple_path; pathstart; pathfinish; arc] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THENL
   [MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`&1 / &2 % x:real^1`; `&1 / &2 % y:real^1`]) THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; joinpaths; DROP_CMUL] THEN
    REPEAT(COND_CASES_TAC THEN TRY ASM_REAL_ARITH_TAC) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; VECTOR_MUL_LID; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`&1 / &2 % (x + vec 1):real^1`; `&1 / &2 % (y + vec 1):real^1`]) THEN
    ASM_SIMP_TAC[JOINPATHS; pathstart; pathfinish] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_ADD; DROP_CMUL] THEN
    REPEAT(COND_CASES_TAC THEN TRY ASM_REAL_ARITH_TAC) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_ARITH `(a + b) - b:real^N = a`] THEN
    ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; VECTOR_MUL_LID; DROP_VEC;
                    DROP_ADD] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SET_RULE
     `s INTER t SUBSET u <=> !x. x IN s ==> x IN t ==> x IN u`] THEN
    REWRITE_TAC[path_image; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `y:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    SUBST1_TAC(SYM(ASSUME
     `(g1:real^1->real^N)(vec 1) = g2(vec 0:real^1)`)) THEN
    MATCH_MP_TAC(SET_RULE `x = a \/ x = b ==> f x IN {f a,f b}`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`&1 / &2 % x:real^1`; `&1 / &2 % (y + vec 1):real^1`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; DROP_ADD] THEN
      REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [joinpaths] THEN
      ASM_SIMP_TAC[JOINPATHS; pathstart; pathfinish] THEN
      REWRITE_TAC[DROP_ADD; DROP_CMUL; DROP_VEC] THEN
      REPEAT(COND_CASES_TAC THEN TRY ASM_REAL_ARITH_TAC) THEN
      REWRITE_TAC[VECTOR_ARITH `&2 % &1 / &2 % x:real^N = x`] THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(a + b) - b:real^N = a`];
      REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_ADD; DROP_VEC] THEN
      ASM_REAL_ARITH_TAC]]);;

let SIMPLE_PATH_JOIN_LOOP_EQ = prove
 (`!g1 g2:real^1->real^N.
        pathfinish g2 = pathstart g1 /\
        pathfinish g1 = pathstart g2
        ==> (simple_path(g1 ++ g2) <=>
             arc g1 /\ arc g2 /\
             path_image g1 INTER path_image g2 SUBSET
             {pathstart g1, pathstart g2})`,
  MESON_TAC[SIMPLE_PATH_JOIN_IMP; SIMPLE_PATH_JOIN_LOOP]);;

(* ------------------------------------------------------------------------- *)
(* Reparametrizing a closed curve to start at some chosen point.             *)
(* ------------------------------------------------------------------------- *)

let shiftpath = new_definition
  `shiftpath a (f:real^1->real^N) =
        \x. if drop(a + x) <= &1 then f(a + x)
            else f(a + x - vec 1)`;;

let SHIFTPATH_TRANSLATION = prove
 (`!a t g. shiftpath t ((\x. a + x) o g) = (\x. a + x) o shiftpath t g`,
  REWRITE_TAC[FUN_EQ_THM; shiftpath; o_THM] THEN MESON_TAC[]);;

add_translation_invariants [SHIFTPATH_TRANSLATION];;

let SHIFTPATH_LINEAR_IMAGE = prove
 (`!f t g1 g2. linear f ==> shiftpath t (f o g) = f o shiftpath t g`,
  REWRITE_TAC[FUN_EQ_THM; shiftpath; o_THM] THEN MESON_TAC[]);;

add_linear_invariants [SHIFTPATH_LINEAR_IMAGE];;

let PATHSTART_SHIFTPATH = prove
 (`!a g. drop a <= &1 ==> pathstart(shiftpath a g) = g(a)`,
  SIMP_TAC[pathstart; shiftpath; VECTOR_ADD_RID]);;

let PATHFINISH_SHIFTPATH = prove
 (`!a g. &0 <= drop a /\ pathfinish g = pathstart g
         ==> pathfinish(shiftpath a g) = g(a)`,
  SIMP_TAC[pathfinish; shiftpath; pathstart; DROP_ADD; DROP_VEC] THEN
  REWRITE_TAC[VECTOR_ARITH `a + vec 1 - vec 1 = a`] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> (x + &1 <= &1 <=> x = &0)`] THEN
  SIMP_TAC[DROP_EQ_0; VECTOR_ADD_LID] THEN MESON_TAC[]);;

let ENDPOINTS_SHIFTPATH = prove
 (`!a g. pathfinish g = pathstart g /\ a IN interval[vec 0,vec 1]
         ==> pathfinish(shiftpath a g) = g a /\
             pathstart(shiftpath a g) = g a`,
  SIMP_TAC[IN_INTERVAL_1; DROP_VEC;
           PATHSTART_SHIFTPATH; PATHFINISH_SHIFTPATH]);;

let CLOSED_SHIFTPATH = prove
 (`!a g. pathfinish g = pathstart g /\ a IN interval[vec 0,vec 1]
         ==> pathfinish(shiftpath a g) = pathstart(shiftpath a g)`,
  SIMP_TAC[IN_INTERVAL_1; PATHSTART_SHIFTPATH; PATHFINISH_SHIFTPATH;
           DROP_VEC]);;

let PATH_SHIFTPATH = prove
 (`!g a. path g /\ pathfinish g:real^N = pathstart g /\
         a IN interval[vec 0,vec 1]
         ==> path(shiftpath a g)`,
  REWRITE_TAC[shiftpath; path] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `interval[vec 0,vec 1] = interval[vec 0,vec 1 - a:real^1] UNION
                            interval[vec 1 - a,vec 1]`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
    REWRITE_TAC[DROP_SUB; DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_UNION THEN REWRITE_TAC[CLOSED_INTERVAL] THEN
  CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THENL
   [EXISTS_TAC `(\x. g(a + x)):real^1->real^N` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_VEC; DROP_SUB] THEN
    SIMP_TAC[REAL_ARITH `a + x <= &1 <=> x <= &1 - a`];
    EXISTS_TAC `(\x. g(a + x - vec 1)):real^1->real^N` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_VEC; DROP_SUB] THEN
    SIMP_TAC[REAL_ARITH `&1 - a <= x ==> (a + x <= &1 <=> a + x = &1)`] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    REWRITE_TAC[VECTOR_ARITH `a + x - vec 1 = (a + x) - vec 1`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_SIMP_TAC[GSYM LIFT_EQ; LIFT_ADD; LIFT_NUM; LIFT_DROP] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; COND_ID]] THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
  SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID;
           CONTINUOUS_ON_SUB] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC; DROP_ADD] THEN
  REAL_ARITH_TAC);;

let SHIFTPATH_SHIFTPATH = prove
 (`!g a x. a IN interval[vec 0,vec 1] /\ pathfinish g = pathstart g /\
           x IN interval[vec 0,vec 1]
           ==> shiftpath (vec 1 - a) (shiftpath a g) x = g x`,
  REWRITE_TAC[shiftpath; pathfinish; pathstart] THEN
  REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_VEC] THEN
  REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
  REWRITE_TAC[DROP_VEC] THEN REPEAT STRIP_TAC THENL
   [ALL_TAC;
    AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `x:real^1 = vec 0` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[VECTOR_ARITH `a + vec 1 - a + vec 0:real^1 = vec 1`]]);;

let PATH_IMAGE_SHIFTPATH = prove
 (`!a g:real^1->real^N.
        a IN interval[vec 0,vec 1] /\ pathfinish g = pathstart g
        ==> path_image(shiftpath a g) = path_image g`,
  REWRITE_TAC[IN_INTERVAL_1; pathfinish; pathstart] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  REWRITE_TAC[path_image; shiftpath; FORALL_IN_IMAGE; SUBSET] THEN
  REWRITE_TAC[IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_IMAGE] THENL
   [EXISTS_TAC `a + x:real^1`;
    EXISTS_TAC `a + x - vec 1:real^1`;
    ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_SUB; DROP_ADD] THEN
  TRY REAL_ARITH_TAC THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `drop a <= drop x` THENL
   [EXISTS_TAC `x - a:real^1` THEN
    REWRITE_TAC[VECTOR_ARITH `a + x - a:real^1 = x`; DROP_SUB] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    EXISTS_TAC `vec 1 + x - a:real^1` THEN
    REWRITE_TAC[VECTOR_ARITH `a + (v + x - a) - v:real^1 = x`] THEN
    REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_VEC] THEN
    ASM_CASES_TAC `x:real^1 = vec 0` THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `a + v + x - a:real^1 = v + x`] THEN
    ASM_REWRITE_TAC[VECTOR_ADD_RID; DROP_VEC; COND_ID] THEN
    ASM_REWRITE_TAC[REAL_ARITH `a + &1 + x - a <= &1 <=> x <= &0`] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN
    TRY(COND_CASES_TAC THEN POP_ASSUM MP_TAC) THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

let SIMPLE_PATH_SHIFTPATH = prove
 (`!g a. simple_path g /\ pathfinish g = pathstart g /\
         a IN interval[vec 0,vec 1]
         ==> simple_path(shiftpath a g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simple_path] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ c /\ d ==> e) /\ (b /\ c /\ d ==> f)
    ==>  (a /\ b) /\ c /\ d ==> e /\ f`) THEN
  CONJ_TAC THENL [MESON_TAC[PATH_SHIFTPATH]; ALL_TAC] THEN
  REWRITE_TAC[simple_path; shiftpath; IN_INTERVAL_1; DROP_VEC;
              DROP_ADD; DROP_SUB] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> c ==> a /\ b ==> d`] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_VEC; GSYM DROP_EQ] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Choosing a sub-path of an existing path.                                  *)
(* ------------------------------------------------------------------------- *)

let subpath = new_definition
 `subpath u v g = \x. g(u + drop(v - u) % x)`;;

let SUBPATH_SCALING_LEMMA = prove
 (`!u v x.
    IMAGE (\x. u + drop(v - u) % x) (interval[vec 0,vec 1]) = segment[u,v]`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
  REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; SEGMENT_1] THEN
  REWRITE_TAC[DROP_SUB; REAL_SUB_LE; INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  BINOP_TAC THEN REWRITE_TAC[GSYM LIFT_EQ_CMUL; VECTOR_MUL_RZERO] THEN
  REWRITE_TAC[LIFT_DROP; LIFT_SUB] THEN VECTOR_ARITH_TAC);;

let PATH_IMAGE_SUBPATH_GEN = prove
 (`!u v g:real^1->real^N. path_image(subpath u v g) = IMAGE g (segment[u,v])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_image; subpath] THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  REWRITE_TAC[IMAGE_o; SUBPATH_SCALING_LEMMA]);;

let PATH_IMAGE_SUBPATH = prove
 (`!u v g:real^1->real^N.
        drop u <= drop v
        ==> path_image(subpath u v g) = IMAGE g (interval[u,v])`,
  SIMP_TAC[PATH_IMAGE_SUBPATH_GEN; SEGMENT_1]);;

let PATH_SUBPATH = prove
 (`!u v g:real^1->real^N.
        path g /\ u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1]
        ==> path(subpath u v g)`,
  REWRITE_TAC[path; subpath] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
  SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID;
           CONTINUOUS_ON_CONST] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBPATH_SCALING_LEMMA; SEGMENT_1] THEN
  COND_CASES_TAC THEN REWRITE_TAC[SUBSET_INTERVAL_1] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
  REAL_ARITH_TAC);;

let PATHSTART_SUBPATH = prove
 (`!u v g:real^1->real^N. pathstart(subpath u v g) = g(u)`,
  REWRITE_TAC[pathstart; subpath; VECTOR_MUL_RZERO; VECTOR_ADD_RID]);;

let PATHFINISH_SUBPATH = prove
 (`!u v g:real^1->real^N. pathfinish(subpath u v g) = g(v)`,
  REWRITE_TAC[pathfinish; subpath; GSYM LIFT_EQ_CMUL] THEN
  REWRITE_TAC[LIFT_DROP; VECTOR_ARITH `u + v - u:real^N = v`]);;

let SUBPATH_TRIVIAL = prove
 (`!g. subpath (vec 0) (vec 1) g = g`,
  REWRITE_TAC[subpath; VECTOR_SUB_RZERO; DROP_VEC; VECTOR_MUL_LID;
              VECTOR_ADD_LID; ETA_AX]);;

let SUBPATH_REVERSEPATH = prove
 (`!g. subpath (vec 1) (vec 0) g = reversepath g`,
  REWRITE_TAC[subpath; reversepath; VECTOR_SUB_LZERO; DROP_NEG; DROP_VEC] THEN
  REWRITE_TAC[VECTOR_ARITH `a + -- &1 % b:real^N = a - b`]);;

let SUBPATH_TRANSLATION = prove
 (`!a g u v. subpath u v ((\x. a + x) o g) = (\x. a + x) o subpath u v g`,
  REWRITE_TAC[FUN_EQ_THM; subpath; o_THM]);;

add_translation_invariants [SUBPATH_TRANSLATION];;

let SUBPATH_LINEAR_IMAGE = prove
 (`!f g u v. linear f ==> subpath u v (f o g) = f o subpath u v g`,
  REWRITE_TAC[FUN_EQ_THM; subpath; o_THM]);;

add_linear_invariants [SUBPATH_LINEAR_IMAGE];;

let SIMPLE_PATH_SUBPATH_EQ = prove
 (`!g u v. simple_path(subpath u v g) <=>
           path(subpath u v g) /\ ~(u = v) /\
           (!x y. x IN segment[u,v] /\ y IN segment[u,v] /\ g x = g y
                  ==> x = y \/ x = u /\ y = v \/ x = v /\ y = u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simple_path; subpath] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM SUBPATH_SCALING_LEMMA] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[VECTOR_ARITH `u + a % x = u <=> a % x = vec 0`;
              VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
  REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_MUL_LCANCEL] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_ADD; DROP_SUB;
              REAL_RING `u + (v - u) * y = v <=> v = u \/ y = &1`] THEN
  REWRITE_TAC[REAL_SUB_0; DROP_EQ; GSYM DROP_VEC] THEN
  ASM_CASES_TAC `v:real^1 = u` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_SUB_REFL; DROP_VEC; VECTOR_MUL_LZERO] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`lift(&1 / &2)`; `lift(&3 / &4)`]) THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; GSYM DROP_EQ; LIFT_DROP] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let ARC_SUBPATH_EQ = prove
 (`!g u v. arc(subpath u v g) <=>
           path(subpath u v g) /\ ~(u = v) /\
           (!x y. x IN segment[u,v] /\ y IN segment[u,v] /\ g x = g y
                  ==> x = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[arc; subpath] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM SUBPATH_SCALING_LEMMA] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[VECTOR_ARITH `u + a % x = u + a % y <=> a % (x - y) = vec 0`;
              VECTOR_MUL_EQ_0; DROP_EQ_0; VECTOR_SUB_EQ] THEN
  ASM_CASES_TAC `v:real^1 = u` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_SUB_REFL; DROP_VEC; VECTOR_MUL_LZERO] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`lift(&1 / &2)`; `lift(&3 / &4)`]) THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; GSYM DROP_EQ; LIFT_DROP] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let SIMPLE_PATH_SUBPATH = prove
 (`!g u v. simple_path g /\
           u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
           ~(u = v)
           ==> simple_path(subpath u v g)`,
  SIMP_TAC[SIMPLE_PATH_SUBPATH_EQ; PATH_SUBPATH; SIMPLE_PATH_IMP_PATH] THEN
  REWRITE_TAC[simple_path] THEN GEN_TAC THEN
  REWRITE_TAC[FORALL_LIFT] THEN MATCH_MP_TAC REAL_WLOG_LT THEN
  REWRITE_TAC[FORALL_DROP; LIFT_DROP] THEN
  CONJ_TAC THENL [MESON_TAC[SEGMENT_SYM]; ALL_TAC] THEN
  SIMP_TAC[SEGMENT_1; REAL_LT_IMP_LE] THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN DISCH_TAC THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^1`; `y:real^1`]) THEN
  SUBGOAL_THEN
   `!x:real^1. x IN interval[u,v] ==> x IN interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUBSET; SUBSET_INTERVAL_1] THEN
    ASM_MESON_TAC[IN_INTERVAL_1; DROP_VEC; REAL_LE_TRANS];
    ASM_SIMP_TAC[]] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
  REWRITE_TAC[DROP_VEC; GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC);;

let ARC_SIMPLE_PATH_SUBPATH = prove
 (`!g u v. simple_path g /\
           u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
           ~(g u = g v)
           ==> arc(subpath u v g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIMPLE_PATH_IMP_ARC THEN
  ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
  ASM_MESON_TAC[SIMPLE_PATH_SUBPATH]);;

let ARC_SIMPLE_PATH_SUBPATH_INTERIOR = prove
 (`!g u v. simple_path g /\
           u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
           ~(u = v) /\ abs(drop u - drop v) < &1
           ==> arc(subpath u v g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_path]) THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^1`; `v:real^1`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[DROP_VEC] THEN REAL_ARITH_TAC);;

let PATH_IMAGE_SUBPATH_SUBSET = prove
 (`!u v g:real^1->real^N.
        path g /\ u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1]
        ==> path_image(subpath u v g) SUBSET path_image g`,
  SIMP_TAC[PATH_IMAGE_SUBPATH_GEN] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[path_image] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  SIMP_TAC[SEGMENT_CONVEX_HULL; SUBSET_HULL; CONVEX_INTERVAL] THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Some additional lemmas about choosing sub-paths.                          *)
(* ------------------------------------------------------------------------- *)

let EXISTS_SUBPATH_OF_PATH = prove
 (`!g a b:real^N.
        path g /\ a IN path_image g /\ b IN path_image g
        ==> ?h. path h /\ pathstart h = a /\ pathfinish h = b /\
                path_image h SUBSET path_image g`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; path_image; FORALL_IN_IMAGE] THEN
  GEN_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
  X_GEN_TAC `v:real^1` THEN DISCH_TAC THEN
  EXISTS_TAC `subpath u v (g:real^1->real^N)` THEN
  ASM_REWRITE_TAC[GSYM path_image; PATH_IMAGE_SUBPATH_GEN] THEN
  ASM_SIMP_TAC[PATH_SUBPATH; PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
  REWRITE_TAC[path_image] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  SIMP_TAC[SEGMENT_CONVEX_HULL; SUBSET_HULL; CONVEX_INTERVAL] THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET]);;

let EXISTS_SUBPATH_OF_ARC_NOENDS = prove
 (`!g a b:real^N.
        arc g /\ a IN path_image g /\ b IN path_image g /\
        {a,b} INTER {pathstart g,pathfinish g} = {}
        ==> ?h. path h /\ pathstart h = a /\ pathfinish h = b /\
                path_image h SUBSET
                (path_image g) DIFF {pathstart g,pathfinish g}`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; path_image; FORALL_IN_IMAGE] THEN
  GEN_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
  X_GEN_TAC `v:real^1` THEN DISCH_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `subpath u v (g:real^1->real^N)` THEN
  ASM_SIMP_TAC[PATH_SUBPATH; PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
               ARC_IMP_PATH; GSYM path_image; PATH_IMAGE_SUBPATH_GEN] THEN
  REWRITE_TAC[path_image; pathstart; pathfinish] THEN
  REWRITE_TAC[SET_RULE
   `s SUBSET t DIFF {a,b} <=> s SUBSET t /\ ~(a IN s) /\ ~(b IN s)`] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  SUBGOAL_THEN `~(vec 0 IN segment[u:real^1,v]) /\ ~(vec 1 IN segment[u,v])`
  STRIP_ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
    REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    SIMP_TAC[REAL_ARITH `a <= b ==> (b <= a <=> a = b)`] THEN
    REWRITE_TAC[GSYM DROP_VEC; DROP_EQ] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[arc; pathstart; pathfinish]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^1,v] SUBSET interval[vec 0,vec 1]` MP_TAC THENL
   [SIMP_TAC[SEGMENT_CONVEX_HULL; SUBSET_HULL; CONVEX_INTERVAL] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[arc; pathstart; pathfinish]) THEN
  SUBGOAL_THEN `(vec 0:real^1) IN interval[vec 0,vec 1] /\
                (vec 1:real^1) IN interval[vec 0,vec 1]`
  MP_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL];
    ASM SET_TAC[]]);;

let EXISTS_SUBARC_OF_ARC_NOENDS = prove
 (`!g a b:real^N.
        arc g /\ a IN path_image g /\ b IN path_image g /\ ~(a = b) /\
        {a,b} INTER {pathstart g,pathfinish g} = {}
        ==> ?h. arc h /\ pathstart h = a /\ pathfinish h = b /\
                path_image h SUBSET
                (path_image g) DIFF {pathstart g,pathfinish g}`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; path_image; FORALL_IN_IMAGE] THEN
  GEN_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
  X_GEN_TAC `v:real^1` THEN REPEAT DISCH_TAC THEN
  EXISTS_TAC `subpath u v (g:real^1->real^N)` THEN
  ASM_SIMP_TAC[PATH_SUBPATH; PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
               ARC_IMP_PATH; GSYM path_image; PATH_IMAGE_SUBPATH_GEN] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
    ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH];
    ALL_TAC] THEN
  REWRITE_TAC[path_image; pathstart; pathfinish] THEN
  REWRITE_TAC[SET_RULE
   `s SUBSET t DIFF {a,b} <=> s SUBSET t /\ ~(a IN s) /\ ~(b IN s)`] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  SUBGOAL_THEN `~(vec 0 IN segment[u:real^1,v]) /\ ~(vec 1 IN segment[u,v])`
  STRIP_ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
    REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    SIMP_TAC[REAL_ARITH `a <= b ==> (b <= a <=> a = b)`] THEN
    REWRITE_TAC[GSYM DROP_VEC; DROP_EQ] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[arc; pathstart; pathfinish]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^1,v] SUBSET interval[vec 0,vec 1]` MP_TAC THENL
   [SIMP_TAC[SEGMENT_CONVEX_HULL; SUBSET_HULL; CONVEX_INTERVAL] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[arc; pathstart; pathfinish]) THEN
  SUBGOAL_THEN `(vec 0:real^1) IN interval[vec 0,vec 1] /\
                (vec 1:real^1) IN interval[vec 0,vec 1]`
  MP_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL];
    ASM SET_TAC[]]);;

let EXISTS_ARC_PSUBSET_SIMPLE_PATH = prove
 (`!g:real^1->real^N.
        simple_path g /\ closed s /\ s PSUBSET path_image g
        ==> ?h. arc h /\
                s SUBSET path_image h /\
                path_image h SUBSET path_image g`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP SIMPLE_PATH_CASES) THENL
   [EXISTS_TAC `g:real^1->real^N` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PSUBSET_ALT]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [path_image] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `(h:real^1->real^N) = shiftpath u g` THEN
  SUBGOAL_THEN
   `simple_path(h:real^1->real^N) /\
    pathstart h = (g:real^1->real^N) u /\
    pathfinish h = (g:real^1->real^N) u /\
    path_image h = path_image g`
  MP_TAC THENL
   [EXPAND_TAC "h" THEN
    ASM_MESON_TAC[SIMPLE_PATH_SHIFTPATH; PATH_IMAGE_SHIFTPATH;
                  PATHSTART_SHIFTPATH; PATHFINISH_SHIFTPATH;
                  IN_INTERVAL_1; DROP_VEC];
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_THEN `pathstart(h:real^1->real^N) = (g:real^1->real^N) u`
        (SUBST_ALL_TAC o SYM)] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (interval[vec 0,vec 1]))
            {x:real^1 | x IN interval[vec 0,vec 1] /\
                        (h x) IN ((:real^N) DIFF s)}`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
    ASM_SIMP_TAC[GSYM path; GSYM CLOSED_OPEN; SIMPLE_PATH_IMP_PATH];
    REWRITE_TAC[open_in] THEN DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `vec 0:real^1` th) THEN MP_TAC(SPEC `vec 1:real^1` th)) THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL] THEN
  REWRITE_TAC[DIST_REAL; VEC_COMPONENT; REAL_SUB_RZERO] THEN
  SIMP_TAC[GSYM drop] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[pathfinish]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[pathstart]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `subpath (lift(min d1 (&1 / &4))) (lift(&1 - min d2 (&1 / &4)))
            (h:real^1->real^N)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH_INTERIOR THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP; LIFT_EQ] THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> t INTER s SUBSET u ==> s SUBSET u`)) THEN
    REWRITE_TAC[SUBSET; IN_INTER; IMP_CONJ] THEN
    SIMP_TAC[PATH_IMAGE_SUBPATH; LIFT_DROP;
             REAL_ARITH `min d1 (&1 / &4) <= &1 - min d2 (&1 / &4)`] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; path_image; IN_INTERVAL_1; DROP_VEC] THEN
    X_GEN_TAC `x:real^1` THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^1` THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC PATH_IMAGE_SUBPATH_SUBSET THEN
    ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC]);;

let EXISTS_DOUBLE_ARC = prove
 (`!g:real^1->real^N a b.
        simple_path g /\ pathfinish g = pathstart g /\
        a IN path_image g /\ b IN path_image g /\ ~(a = b)
        ==> ?u d. arc u /\ arc d /\
                  pathstart u = a /\ pathfinish u = b /\
                  pathstart d = b /\ pathfinish d = a /\
                  (path_image u) INTER (path_image d) = {a,b} /\
                  (path_image u) UNION (path_image d) = path_image g`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; path_image] THEN
  ONCE_REWRITE_TAC[FORALL_IN_IMAGE] THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN REWRITE_TAC[GSYM path_image] THEN
  X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `h = shiftpath u (g:real^1->real^N)` THEN
  SUBGOAL_THEN
   `simple_path(h:real^1->real^N) /\
    pathstart h = g u /\
    pathfinish h = g u /\
    path_image h = path_image g`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN
    ASM_SIMP_TAC[SIMPLE_PATH_SHIFTPATH; PATH_IMAGE_SHIFTPATH] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    EXPAND_TAC "h" THEN
    ASM_SIMP_TAC[PATHSTART_SHIFTPATH; PATHFINISH_SHIFTPATH];
    UNDISCH_THEN `path_image h :real^N->bool = path_image g`
     (SUBST_ALL_TAC o SYM)] THEN
  UNDISCH_TAC `(b:real^N) IN path_image h` THEN
  REWRITE_TAC[IN_IMAGE; path_image; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN REWRITE_TAC[GSYM path_image] THEN
  MAP_EVERY EXISTS_TAC
   [`subpath (vec 0) v (h:real^1->real^N)`;
    `subpath v (vec 1) (h:real^1->real^N)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
  ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
  UNDISCH_THEN `b = (h:real^1->real^N) v` SUBST_ALL_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]
   (ASSUME `(v:real^1) IN interval[vec 0,vec 1]`)) THEN
  ASM_SIMP_TAC[ARC_SIMPLE_PATH_SUBPATH; IN_INTERVAL_1; DROP_VEC;
               REAL_LE_REFL; REAL_POS; PATH_IMAGE_SUBPATH] THEN
  REWRITE_TAC[GSYM IMAGE_UNION; path_image] THEN
  UNDISCH_THEN `(h:real^1->real^N)(vec 0) = (g:real^1->real^N) u`
   (SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN
   `interval[vec 0,v] UNION interval[v,vec 1] = interval[vec 0:real^1,vec 1]`
  ASSUME_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[IMAGE_SUBSET] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x y. x IN (s UNION t) /\ y IN (s UNION t) /\ f x = f y
             ==> x = y \/ x = vec 0 /\ y = vec 1 \/ x = vec 1 /\ y = vec 0) /\
      (f(vec 0) = f(vec 1)) /\ (vec 0) IN s /\ (vec 1) IN t /\
      s INTER t = {c}
      ==> IMAGE f s INTER IMAGE f t = {f (vec 0), f c}`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[simple_path]) THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY; IN_INTER; IN_UNION] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
  REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ; DROP_VEC] THEN ASM_REAL_ARITH_TAC);;

let SUBPATH_TO_FRONTIER_EXPLICIT = prove
 (`!g:real^1->real^N s.
        path g /\ pathstart g IN s /\ ~(pathfinish g IN s)
        ==> ?u. u IN interval[vec 0,vec 1] /\
                (!x. &0 <= drop x /\ drop x < drop u ==> g x IN interior s) /\
                ~(g u IN interior s) /\
                (u = vec 0 \/ g u IN closure s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{u | lift u IN interval[vec 0,vec 1] /\
                     g(lift u) IN closure((:real^N) DIFF s)}`
         COMPACT_ATTAINS_INF) THEN
  SIMP_TAC[LIFT_DROP; SET_RULE
   `(!x. lift(drop x) = x) ==> IMAGE lift {x | P(lift x)} = {x | P x}`] THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[path; pathstart; pathfinish; SUBSET;
                                path_image; FORALL_IN_IMAGE]) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [MATCH_MP_TAC BOUNDED_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        REWRITE_TAC[BOUNDED_INTERVAL] THEN SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
        ASM_REWRITE_TAC[CLOSED_CLOSURE; CLOSED_INTERVAL]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[LIFT_NUM] THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL] THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_DROP; FORALL_DROP; IN_ELIM_THM; LIFT_DROP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^1` THEN
  REWRITE_TAC[CLOSURE_COMPLEMENT; IN_DIFF; IN_UNIV] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[subpath; VECTOR_SUB_RZERO; VECTOR_ADD_LID] THEN
  ASM_REWRITE_TAC[GSYM LIFT_EQ_CMUL; LIFT_DROP] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; GSYM DROP_EQ] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE BINDER_CONV
     [TAUT `a /\ ~b ==> c <=> a /\ ~c ==> b`]) THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o SPEC `x:real^1`) THEN DISCH_TAC] THEN
  ASM_CASES_TAC `drop u = &0` THEN
  ASM_REWRITE_TAC[frontier; IN_DIFF; CLOSURE_APPROACHABLE] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[path; pathstart; pathfinish]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_on]) THEN
  DISCH_THEN(MP_TAC o SPEC `u:real^1`) THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `lift(max (&0) (drop u - d / &2))`) THEN
  REWRITE_TAC[LIFT_DROP; DIST_REAL; GSYM drop] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC
   (MESON[] `P a ==> dist(a,y) < e ==> ?x. P x /\ dist(x,y) < e`) THEN
  MATCH_MP_TAC(REWRITE_RULE[SUBSET] INTERIOR_SUBSET) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN ASM_ARITH_TAC);;

let SUBPATH_TO_FRONTIER_STRONG = prove
 (`!g:real^1->real^N s.
        path g /\ pathstart g IN s /\ ~(pathfinish g IN s)
        ==> ?u. u IN interval[vec 0,vec 1] /\
                 ~(pathfinish(subpath (vec 0) u g) IN interior s) /\
                (u = vec 0 \/
                 (!x. x IN interval[vec 0,vec 1] /\ ~(x = vec 1)
                      ==> (subpath (vec 0) u g x) IN interior s) /\
                 pathfinish(subpath (vec 0) u g) IN closure s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUBPATH_TO_FRONTIER_EXPLICIT) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^1` THEN
  REWRITE_TAC[subpath; pathfinish; VECTOR_SUB_RZERO; VECTOR_ADD_LID] THEN
  ASM_CASES_TAC `u:real^1 = vec 0` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO] THEN
  ASM_REWRITE_TAC[GSYM LIFT_EQ_CMUL; LIFT_DROP] THEN
  X_GEN_TAC `x:real^1` THEN
  REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ; DROP_VEC] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
  ASM_SIMP_TAC[DROP_CMUL; REAL_LE_MUL] THEN
  REWRITE_TAC[REAL_ARITH `u * x < u <=> &0 < u * (&1 - x)`] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_SUB_LT] THEN
  ASM_REWRITE_TAC[REAL_LT_LE] THEN
  ASM_REWRITE_TAC[GSYM LIFT_EQ; LIFT_DROP; LIFT_NUM]);;

let SUBPATH_TO_FRONTIER = prove
 (`!g:real^1->real^N s.
        path g /\ pathstart g IN s /\ ~(pathfinish g IN s)
        ==> ?u. u IN interval[vec 0,vec 1] /\
                pathfinish(subpath (vec 0) u g) IN frontier s /\
                (path_image(subpath (vec 0) u g) DELETE
                 pathfinish(subpath (vec 0) u g))
                SUBSET interior s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[frontier; IN_DIFF] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUBPATH_TO_FRONTIER_STRONG) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^1` THEN
  ASM_CASES_TAC `u:real^1 = vec 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart]) THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN
    REWRITE_TAC[subpath; path_image; VECTOR_SUB_REFL; DROP_VEC;
                VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
    SET_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; path_image; FORALL_IN_IMAGE; IN_DELETE; IMP_CONJ] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; pathfinish] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_MESON_TAC[]]);;

let EXISTS_PATH_SUBPATH_TO_FRONTIER = prove
 (`!g:real^1->real^N s.
        path g /\ pathstart g IN s /\ ~(pathfinish g IN s)
        ==> ?h. path h /\ pathstart h = pathstart g /\
                (path_image h) SUBSET (path_image g) /\
                (path_image h DELETE (pathfinish h)) SUBSET interior s /\
                pathfinish h IN frontier s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SUBPATH_TO_FRONTIER) THEN
  EXISTS_TAC `subpath (vec 0) u (g:real^1->real^N)` THEN
  ASM_SIMP_TAC[PATH_SUBPATH; IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL;
               PATHSTART_SUBPATH; PATH_IMAGE_SUBPATH_SUBSET] THEN
  REWRITE_TAC[pathstart]);;

let EXISTS_PATH_SUBPATH_TO_FRONTIER_CLOSED = prove
 (`!g:real^1->real^N s.
        closed s /\ path g /\ pathstart g IN s /\ ~(pathfinish g IN s)
        ==> ?h. path h /\ pathstart h = pathstart g /\
                (path_image h) SUBSET (path_image g) INTER s /\
                pathfinish h IN frontier s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EXISTS_PATH_SUBPATH_TO_FRONTIER) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  REWRITE_TAC[SUBSET_INTER] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
   `(pathfinish h:real^N) INSERT (path_image h DELETE pathfinish h)` THEN
  CONJ_TAC THENL [SET_TAC[]; REWRITE_TAC[INSERT_SUBSET]] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[frontier; CLOSURE_EQ; IN_DIFF];
    ASM_MESON_TAC[SUBSET_TRANS; INTERIOR_SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* Special case of straight-line paths.                                      *)
(* ------------------------------------------------------------------------- *)

let linepath = new_definition
 `linepath(a,b) = \x. (&1 - drop x) % a + drop x % b`;;

let LINEPATH_TRANSLATION = prove
 (`!a b c. linepath(a + b,a + c) = (\x. a + x) o linepath(b,c)`,
  REWRITE_TAC[linepath; o_THM; FUN_EQ_THM] THEN VECTOR_ARITH_TAC);;

add_translation_invariants [LINEPATH_TRANSLATION];;

let LINEPATH_LINEAR_IMAGE = prove
 (`!f. linear f ==> !b c. linepath(f b,f c) = f o linepath(b,c)`,
  REWRITE_TAC[linepath; o_THM; FUN_EQ_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_ADD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_CMUL) THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

add_linear_invariants [LINEPATH_LINEAR_IMAGE];;

let PATHSTART_LINEPATH = prove
 (`!a b. pathstart(linepath(a,b)) = a`,
  REWRITE_TAC[linepath; pathstart; DROP_VEC] THEN VECTOR_ARITH_TAC);;

let PATHFINISH_LINEPATH = prove
 (`!a b. pathfinish(linepath(a,b)) = b`,
  REWRITE_TAC[linepath; pathfinish; DROP_VEC] THEN VECTOR_ARITH_TAC);;

let CONTINUOUS_LINEPATH_AT = prove
 (`!a b x. linepath(a,b) continuous (at x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linepath] THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - u) % x + y = x + u % --x + y`] THEN
  MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_VMUL THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_AT_ID]);;

let CONTINUOUS_ON_LINEPATH = prove
 (`!a b s. linepath(a,b) continuous_on s`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_LINEPATH_AT]);;

let PATH_LINEPATH = prove
 (`!a b. path(linepath(a,b))`,
  REWRITE_TAC[path; CONTINUOUS_ON_LINEPATH]);;

let PATH_IMAGE_LINEPATH = prove
 (`!a b. path_image(linepath (a,b)) = segment[a,b]`,
  REWRITE_TAC[segment; path_image; linepath] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTERVAL] THEN
  SIMP_TAC[DIMINDEX_1; FORALL_1; VEC_COMPONENT; ARITH] THEN
  REWRITE_TAC[EXISTS_LIFT; GSYM drop; LIFT_DROP] THEN MESON_TAC[]);;

let REVERSEPATH_LINEPATH = prove
 (`!a b. reversepath(linepath(a,b)) = linepath(b,a)`,
  REWRITE_TAC[reversepath; linepath; DROP_SUB; DROP_VEC; FUN_EQ_THM] THEN
  VECTOR_ARITH_TAC);;

let ARC_LINEPATH = prove
 (`!a b. ~(a = b) ==> arc(linepath(a,b))`,
  REWRITE_TAC[arc; PATH_LINEPATH] THEN REWRITE_TAC[linepath] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(&1 - x) % a + x % b:real^N = (&1 - y) % a + y % b <=>
    (x - y) % (a - b) = vec 0`] THEN
  SIMP_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; DROP_EQ; REAL_SUB_0]);;

let SIMPLE_PATH_LINEPATH = prove
 (`!a b. ~(a = b) ==> simple_path(linepath(a,b))`,
  MESON_TAC[ARC_IMP_SIMPLE_PATH; ARC_LINEPATH]);;

let ARC_LINEPATH_EQ = prove
 (`!a b. arc(linepath(a,b)) <=> ~(a = b)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[ARC_LINEPATH] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ARC_DISTINCT_ENDS) THEN
  REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  MESON_TAC[]);;

let LINEPATH_REFL = prove
 (`!a. linepath(a,a) = \x. a`,
  REWRITE_TAC[linepath; VECTOR_ARITH `(&1 - u) % x + u % x:real^N = x`]);;

(* ------------------------------------------------------------------------- *)
(* Bounding a point away from a path.                                        *)
(* ------------------------------------------------------------------------- *)

let NOT_ON_PATH_BALL = prove
 (`!g z:real^N.
        path g /\ ~(z IN path_image g)
        ==> ?e. &0 < e /\ ball(z,e) INTER (path_image g) = {}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`path_image g:real^N->bool`; `z:real^N`]
     DISTANCE_ATTAINS_INF) THEN
  REWRITE_TAC[PATH_IMAGE_NONEMPTY] THEN
  ASM_SIMP_TAC[COMPACT_PATH_IMAGE; COMPACT_IMP_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `dist(z:real^N,a)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[DIST_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_BALL; IN_INTER] THEN
  ASM_MESON_TAC[REAL_NOT_LE]);;

let NOT_ON_PATH_CBALL = prove
 (`!g z:real^N.
        path g /\ ~(z IN path_image g)
        ==> ?e. &0 < e /\ cball(z,e) INTER (path_image g) = {}`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP NOT_ON_PATH_BALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `s INTER u = {} ==> t SUBSET s ==> t INTER u = {}`)) THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Path component, considered as a "joinability" relation (from Tom Hales).  *)
(* ------------------------------------------------------------------------- *)

let path_component = new_definition
 `path_component s x y <=>
        ?g. path g /\ path_image g SUBSET s /\
            pathstart g = x /\ pathfinish g = y`;;

let PATH_COMPONENT_IN = prove
 (`!s x y. path_component s x y ==> x IN s /\ y IN s`,
  REWRITE_TAC[path_component; path_image; pathstart; pathfinish] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_LE_REFL; REAL_POS]);;

let PATH_COMPONENT_REFL = prove
 (`!s x:real^N. x IN s ==> path_component s x x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[path_component] THEN
  EXISTS_TAC `(\u. x):real^1->real^N` THEN
  REWRITE_TAC[pathstart; pathfinish; path_image; path;
              CONTINUOUS_ON_CONST; IMAGE; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let PATH_COMPONENT_REFL_EQ = prove
 (`!s x:real^N. path_component s x x <=> x IN s`,
  MESON_TAC[PATH_COMPONENT_IN; PATH_COMPONENT_REFL]);;

let PATH_COMPONENT_SYM = prove
 (`!s x y:real^N. path_component s x y ==> path_component s y x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_component] THEN
  MESON_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
            PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH]);;

let PATH_COMPONENT_TRANS = prove
 (`!s x y:real^N.
    path_component s x y /\ path_component s y z ==> path_component s x z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_component] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `g1:real^1->real^N`) (X_CHOOSE_TAC `g2:real^1->real^N`)) THEN
  EXISTS_TAC `g1 ++ g2 :real^1->real^N` THEN
  ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; UNION_SUBSET;
               PATHSTART_JOIN; PATHFINISH_JOIN]);;

let PATH_COMPONENT_OF_SUBSET = prove
 (`!s t x. s SUBSET t /\ path_component s x y ==> path_component t x y`,
  REWRITE_TAC[path_component] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Can also consider it as a set, as the name suggests.                      *)
(* ------------------------------------------------------------------------- *)

let PATH_COMPONENT_SET = prove
 (`!s x. path_component s x =
            { y | ?g. path g /\ path_image g SUBSET s /\
                      pathstart g = x /\ pathfinish g = y }`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REWRITE_TAC[IN; path_component]);;

let PATH_COMPONENT_SUBSET = prove
 (`!s x. (path_component s x) SUBSET s`,
  REWRITE_TAC[SUBSET; IN] THEN MESON_TAC[PATH_COMPONENT_IN; IN]);;

let PATH_COMPONENT_EQ_EMPTY = prove
 (`!s x. path_component s x = {} <=> ~(x IN s)`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
  MESON_TAC[IN; PATH_COMPONENT_REFL; PATH_COMPONENT_IN]);;

let PATH_COMPONENT_EMPTY = prove
 (`!x. path_component {} x = {}`,
  REWRITE_TAC[PATH_COMPONENT_EQ_EMPTY; NOT_IN_EMPTY]);;

let PATH_COMPONENT_TRANSLATION = prove
 (`!a s x. path_component (IMAGE (\x. a + x) s) (a + x) =
                IMAGE (\x. a + x) (path_component s x)`,
  REWRITE_TAC[PATH_COMPONENT_SET] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [PATH_COMPONENT_TRANSLATION];;

let PATH_COMPONENT_LINEAR_IMAGE = prove
 (`!f s x. linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
           ==> path_component (IMAGE f s) (f x) =
               IMAGE f (path_component s x)`,
  REWRITE_TAC[PATH_COMPONENT_SET] THEN
  GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [PATH_COMPONENT_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Path connectedness of a space.                                            *)
(* ------------------------------------------------------------------------- *)

let path_connected = new_definition
 `path_connected s <=>
        !x y. x IN s /\ y IN s
              ==> ?g. path g /\ (path_image g) SUBSET s /\
                      pathstart g = x /\ pathfinish g = y`;;

let PATH_CONNECTED_IFF_PATH_COMPONENT = prove
 (`!s. path_connected s <=> !x y. x IN s /\ y IN s ==> path_component s x y`,
  REWRITE_TAC[path_connected; path_component]);;

let PATH_CONNECTED_COMPONENT_SET = prove
 (`!s. path_connected s <=> !x. x IN s ==> path_component s x = s`,
  REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT; GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[PATH_COMPONENT_SUBSET] THEN SET_TAC[]);;

let PATH_COMPONENT_MONO = prove
 (`!s t x. s SUBSET t ==> (path_component s x) SUBSET (path_component t x)`,
  REWRITE_TAC[PATH_COMPONENT_SET] THEN SET_TAC[]);;

let PATH_COMPONENT_OF_SUBSET = prove
 (`!s t x y. s SUBSET t /\ path_component s x y ==> path_component t x y`,
  REPEAT GEN_TAC THEN DISCH_THEN
   (CONJUNCTS_THEN2 (MP_TAC o MATCH_MP PATH_COMPONENT_MONO) MP_TAC) THEN
  REWRITE_TAC[SUBSET; IN] THEN MESON_TAC[]);;

let PATH_COMPONENT_MAXIMAL = prove
 (`!s t x. x IN t /\ path_connected t /\ t SUBSET s
           ==> t SUBSET (path_component s x)`,
  REWRITE_TAC[path_connected; PATH_COMPONENT_SET; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let PATH_COMPONENT_EQ = prove
 (`!s x y. y IN path_component s x
           ==> path_component s y = path_component s x`,
  REWRITE_TAC[EXTENSION; IN] THEN
  MESON_TAC[PATH_COMPONENT_SYM; PATH_COMPONENT_TRANS]);;

let PATH_COMPONENT_PATH_IMAGE_PATHSTART = prove
 (`!p x:real^N.
        path p /\ x IN path_image p
        ==> path_component (path_image p) (pathstart p) x`,
  REWRITE_TAC[path_image; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real^1 = vec 0` THENL
   [ASM_REWRITE_TAC[pathstart] THEN MATCH_MP_TAC PATH_COMPONENT_REFL THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTERVAL_1] THEN
    REWRITE_TAC[DROP_VEC; REAL_POS];
    ALL_TAC] THEN
  REWRITE_TAC[path_component] THEN
  EXISTS_TAC `\y. (p:real^1->real^N)(drop x % y)` THEN
  ASM_REWRITE_TAC[path; path_image; pathstart; pathfinish] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [path]) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CONTINUOUS_ON_SUBSET);
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN REWRITE_TAC[IMAGE_o] THEN
    MATCH_MP_TAC IMAGE_SUBSET;
    AP_TERM_TAC THEN REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_VEC] THEN
    REWRITE_TAC[REAL_MUL_RID]] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
  SIMP_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC; REAL_LE_MUL] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]);;

let PATH_CONNECTED_PATH_IMAGE = prove
 (`!p:real^1->real^N. path p ==> path_connected(path_image p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC PATH_COMPONENT_TRANS THEN
  EXISTS_TAC `pathstart p :real^N` THEN
  ASM_MESON_TAC[PATH_COMPONENT_PATH_IMAGE_PATHSTART; PATH_COMPONENT_SYM]);;

let PATH_CONNECTED_PATH_COMPONENT = prove
 (`!s x:real^N. path_connected(path_component s x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_connected; IN] THEN
  MAP_EVERY X_GEN_TAC [`y:real^N`; `z:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `path_component s y (z:real^N)` MP_TAC THENL
   [ASM_MESON_TAC[PATH_COMPONENT_SYM; PATH_COMPONENT_TRANS]; ALL_TAC] THEN
  REWRITE_TAC[path_component] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real^1->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `path_component s (x:real^N) = path_component s y`
  SUBST1_TAC THENL [ASM_MESON_TAC[PATH_COMPONENT_EQ; IN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^1->real^N`; `w:real^N`]
     PATH_COMPONENT_PATH_IMAGE_PATHSTART) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PATH_COMPONENT_MONO) THEN
  REWRITE_TAC[SUBSET; IN] THEN MESON_TAC[]);;

let PATH_COMPONENT_PATH_COMPONENT = prove
 (`!s x:real^N.
        path_component (path_component s x) x = path_component s x`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN s` THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    SIMP_TAC[PATH_COMPONENT_MONO; PATH_COMPONENT_SUBSET] THEN
    MATCH_MP_TAC PATH_COMPONENT_MAXIMAL THEN
    REWRITE_TAC[SUBSET_REFL; PATH_CONNECTED_PATH_COMPONENT] THEN
    ASM_REWRITE_TAC[IN; PATH_COMPONENT_REFL_EQ];
    MATCH_MP_TAC(SET_RULE `s = {} /\ t = {} ==> s = t`) THEN
    ASM_REWRITE_TAC[PATH_COMPONENT_EQ_EMPTY] THEN
    ASM_MESON_TAC[SUBSET; PATH_COMPONENT_SUBSET]]);;

let PATH_CONNECTED_LINEPATH = prove
 (`!s a b:real^N. segment[a,b] SUBSET s ==> path_component s a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[path_component] THEN
  EXISTS_TAC `linepath(a:real^N,b)` THEN
  ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_LINEPATH] THEN
  ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH]);;

let PATH_COMPONENT_DISJOINT = prove
 (`!s a b. DISJOINT (path_component s a) (path_component s b) <=>
             ~(a IN path_component s b)`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN] THEN MESON_TAC[PATH_COMPONENT_SYM; PATH_COMPONENT_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* General "locally connected implies connected" type results.               *)
(* ------------------------------------------------------------------------- *)

let OPEN_GENERAL_COMPONENT = prove
 (`!c. (!s x y. c s x y ==> x IN s /\ y IN s) /\
       (!s x y. c s x y ==> c s y x) /\
       (!s x y z. c s x y /\ c s y z ==> c s x z) /\
       (!s t x y. s SUBSET t /\ c s x y ==> c t x y) /\
       (!s x y e. y IN ball(x,e) /\ ball(x,e) SUBSET s
                  ==> c (ball(x,e)) x y)
       ==> !s x:real^N. open s ==> open(c s x)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IN") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SYM") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "TRANS") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SUBSET") (LABEL_TAC "BALL")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_CONTAINS_BALL; SUBSET; IN_BALL] THEN
  DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[SUBSET; IN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN s /\ y IN s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN s`)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  REMOVE_THEN "TRANS" MATCH_MP_TAC THEN EXISTS_TAC `y:real^N` THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "SUBSET" MATCH_MP_TAC THEN
  EXISTS_TAC `ball(y:real^N,e)` THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  REMOVE_THEN "BALL" MATCH_MP_TAC THEN
  REWRITE_TAC[SUBSET; IN_BALL] THEN ASM_MESON_TAC[]);;

let OPEN_NON_GENERAL_COMPONENT = prove
 (`!c. (!s x y. c s x y ==> x IN s /\ y IN s) /\
       (!s x y. c s x y ==> c s y x) /\
       (!s x y z. c s x y /\ c s y z ==> c s x z) /\
       (!s t x y. s SUBSET t /\ c s x y ==> c t x y) /\
       (!s x y e. y IN ball(x,e) /\ ball(x,e) SUBSET s
                  ==> c (ball(x,e)) x y)
       ==> !s x:real^N. open s ==> open(s DIFF c s x)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IN") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SYM") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "TRANS") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SUBSET") (LABEL_TAC "BALL")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_CONTAINS_BALL; SUBSET; IN_BALL] THEN
  DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_DIFF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o REWRITE_RULE[IN])) THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN s`)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[IN] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
  REMOVE_THEN "TRANS" MATCH_MP_TAC THEN EXISTS_TAC `z:real^N` THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "SUBSET" MATCH_MP_TAC THEN
  EXISTS_TAC `ball(y:real^N,e)` THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  REMOVE_THEN "SYM" MATCH_MP_TAC THEN
  REMOVE_THEN "BALL" MATCH_MP_TAC THEN
  REWRITE_TAC[SUBSET; IN_BALL] THEN ASM_MESON_TAC[]);;

let GENERAL_CONNECTED_OPEN = prove
 (`!c. (!s x y. c s x y ==> x IN s /\ y IN s) /\
       (!s x y. c s x y ==> c s y x) /\
       (!s x y z. c s x y /\ c s y z ==> c s x z) /\
       (!s t x y. s SUBSET t /\ c s x y ==> c t x y) /\
       (!s x y e. y IN ball(x,e) /\ ball(x,e) SUBSET s
                  ==> c (ball(x,e)) x y)
       ==> !s x y:real^N. open s /\ connected s /\ x IN s /\ y IN s
                          ==> c s x y`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connected]) THEN
  REWRITE_TAC[IN] THEN REWRITE_TAC[NOT_EXISTS_THM; LEFT_IMP_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC
   [`c (s:real^N->bool) (x:real^N):real^N->bool`;
    `s DIFF (c (s:real^N->bool) (x:real^N))`] THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ c /\ d /\ e /\ (f ==> g)
                     ==> ~(a /\ b /\ c /\ d /\ e /\ ~f) ==> g`) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPEC `c:(real^N->bool)->real^N->real^N->bool`
        OPEN_GENERAL_COMPONENT) THEN ASM_MESON_TAC[];
    MP_TAC(SPEC `c:(real^N->bool)->real^N->real^N->bool`
        OPEN_NON_GENERAL_COMPONENT) THEN ASM_MESON_TAC[];
    SET_TAC[];
    SET_TAC[];
    ALL_TAC;
    ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:real^N` THEN
  ASM_REWRITE_TAC[IN_INTER] THEN REWRITE_TAC[IN] THEN
  FIRST_ASSUM(MATCH_MP_TAC o
    SPECL [`ball(x:real^N,e)`; `s:real^N->bool`]) THEN
  ASM_MESON_TAC[CENTRE_IN_BALL]);;

(* ------------------------------------------------------------------------- *)
(* Some useful lemmas about path-connectedness.                              *)
(* ------------------------------------------------------------------------- *)

let CONVEX_IMP_PATH_CONNECTED = prove
 (`!s:real^N->bool. convex s ==> path_connected s`,
  REWRITE_TAC[CONVEX_ALT; path_connected] THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `\u. (&1 - drop u) % x + drop u % y:real^N` THEN
  ASM_SIMP_TAC[pathstart; pathfinish; DROP_VEC; path; path_image;
               SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; GSYM FORALL_DROP] THEN
  CONJ_TAC THENL [ALL_TAC; CONJ_TAC THEN VECTOR_ARITH_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
  REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP; LIFT_NUM] THEN
  SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]);;

let PATH_CONNECTED_UNIV = prove
 (`path_connected(:real^N)`,
  SIMP_TAC[CONVEX_IMP_PATH_CONNECTED; CONVEX_UNIV]);;

let PATH_COMPONENT_UNIV = prove
 (`!x. path_component(:real^N) x = (:real^N)`,
  MESON_TAC[PATH_CONNECTED_COMPONENT_SET; PATH_CONNECTED_UNIV; IN_UNIV]);;

let PATH_CONNECTED_IMP_CONNECTED = prove
 (`!s:real^N->bool. path_connected s ==> connected s`,
  GEN_TAC THEN
  REWRITE_TAC[path_connected; CONNECTED_IFF_CONNECTED_COMPONENT] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^N` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[connected_component] THEN
  EXISTS_TAC `path_image(g:real^1->real^N)` THEN
  ASM_MESON_TAC[CONNECTED_PATH_IMAGE; PATHSTART_IN_PATH_IMAGE;
                PATHFINISH_IN_PATH_IMAGE]);;

let OPEN_PATH_COMPONENT = prove
 (`!s x:real^N. open s ==> open(path_component s x)`,
  MATCH_MP_TAC OPEN_GENERAL_COMPONENT THEN
  REWRITE_TAC[PATH_COMPONENT_IN; PATH_COMPONENT_SYM; PATH_COMPONENT_TRANS;
              PATH_COMPONENT_OF_SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[PATH_CONNECTED_IFF_PATH_COMPONENT]
   (MATCH_MP CONVEX_IMP_PATH_CONNECTED (SPEC_ALL CONVEX_BALL))) THEN
  ASM_MESON_TAC[CENTRE_IN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE; NOT_IN_EMPTY]);;

let OPEN_NON_PATH_COMPONENT = prove
 (`!s x:real^N. open s ==> open(s DIFF path_component s x)`,
  MATCH_MP_TAC OPEN_NON_GENERAL_COMPONENT THEN
  REWRITE_TAC[PATH_COMPONENT_IN; PATH_COMPONENT_SYM; PATH_COMPONENT_TRANS;
              PATH_COMPONENT_OF_SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[PATH_CONNECTED_IFF_PATH_COMPONENT]
   (MATCH_MP CONVEX_IMP_PATH_CONNECTED (SPEC_ALL CONVEX_BALL))) THEN
  ASM_MESON_TAC[CENTRE_IN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE; NOT_IN_EMPTY]);;

let CONNECTED_OPEN_PATH_CONNECTED = prove
 (`!s:real^N->bool. open s /\ connected s ==> path_connected s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PATH_CONNECTED_COMPONENT_SET] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SIMP_TAC[GSYM SUBSET_ANTISYM_EQ; PATH_COMPONENT_SUBSET] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connected]) THEN
  REWRITE_TAC[IN] THEN REWRITE_TAC[NOT_EXISTS_THM; LEFT_IMP_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC
   [`path_component s (x:real^N)`; `s DIFF (path_component s (x:real^N))`] THEN
  ASM_SIMP_TAC[OPEN_PATH_COMPONENT; OPEN_NON_PATH_COMPONENT] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  SIMP_TAC[PATH_COMPONENT_SUBSET; SET_RULE
   `s SUBSET t ==> (s INTER t = {} <=> s = {})`] THEN
  REWRITE_TAC[PATH_COMPONENT_EQ_EMPTY] THEN ASM SET_TAC[]);;

let PATH_CONNECTED_EQ_CONNECTED = prove
 (`!s. open s ==> (path_connected s <=> connected s)`,
  MESON_TAC[PATH_CONNECTED_IMP_CONNECTED; CONNECTED_OPEN_PATH_CONNECTED]);;

let PATH_CONNECTED_CONTINUOUS_IMAGE = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\ path_connected s ==> path_connected (IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_connected] THEN STRIP_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `y:real^M`]) THEN
  ASM_REWRITE_TAC[path; path_image; pathstart; pathfinish] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f:real^M->real^N) o (g:real^1->real^M)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ASM_REWRITE_TAC[o_DEF] THEN ASM SET_TAC[]]);;

let HOMEOMORPHIC_PATH_CONNECTEDNESS = prove
 (`!s t. s homeomorphic t ==> (path_connected s <=> path_connected t)`,
  REWRITE_TAC[homeomorphic; homeomorphism] THEN
  MESON_TAC[PATH_CONNECTED_CONTINUOUS_IMAGE]);;

let PATH_CONNECTED_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
     path_connected s /\ linear f ==> path_connected(IMAGE f s)`,
  SIMP_TAC[LINEAR_CONTINUOUS_ON; PATH_CONNECTED_CONTINUOUS_IMAGE]);;

let PATH_CONNECTED_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (path_connected (IMAGE f s) <=> path_connected s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE PATH_CONNECTED_LINEAR_IMAGE));;

add_linear_invariants [PATH_CONNECTED_LINEAR_IMAGE_EQ];;

let PATH_CONNECTED_EMPTY = prove
 (`path_connected {}`,
  REWRITE_TAC[path_connected; NOT_IN_EMPTY]);;

let PATH_CONNECTED_SING = prove
 (`!a:real^N. path_connected {a}`,
  GEN_TAC THEN REWRITE_TAC[path_connected; IN_SING] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `linepath(a:real^N,a)` THEN
  ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  REWRITE_TAC[SEGMENT_REFL; PATH_IMAGE_LINEPATH; SUBSET_REFL]);;

let PATH_CONNECTED_UNION = prove
 (`!s t. path_connected s /\ path_connected t /\ ~(s INTER t = {})
         ==> path_connected (s UNION t)`,
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
  REWRITE_TAC[IN_INTER; IN_UNION] THEN
  MESON_TAC[PATH_COMPONENT_OF_SUBSET; SUBSET_UNION; PATH_COMPONENT_TRANS]);;

let PATH_CONNECTED_TRANSLATION = prove
 (`!a s. path_connected s ==> path_connected (IMAGE (\x:real^N. a + x) s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST]);;

let PATH_CONNECTED_TRANSLATION_EQ = prove
 (`!a s. path_connected (IMAGE (\x:real^N. a + x) s) <=> path_connected s`,
  REWRITE_TAC[path_connected] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [PATH_CONNECTED_TRANSLATION_EQ];;

(* ------------------------------------------------------------------------- *)
(* A sharper result with arcwise connectedness (we could just prove this     *)
(* is equivalent to path-connectedness but it's quite a bit more work).      *)
(* We could easily get polygonal connections (with any other special         *)
(* features like all segments being horizontal or vertical) in the same way. *)
(* ------------------------------------------------------------------------- *)

let ARC_CONNECTED_TRANS = prove
 (`!g h:real^1->real^N.
        arc g /\ arc h /\
        pathfinish g = pathstart h /\ ~(pathstart g = pathfinish h)
        ==> ?i. arc i /\
                path_image i SUBSET (path_image g UNION path_image h) /\
                pathstart i = pathstart g /\
                pathfinish i = pathfinish h`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(pathfinish(h):real^N) IN path_image g` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [path_image]) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `subpath (vec 0) u (g:real^1->real^N)` THEN
    ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
    REWRITE_TAC[pathstart] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
      ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH];
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s SUBSET t UNION u`) THEN
      MATCH_MP_TAC PATH_IMAGE_SUBPATH_SUBSET THEN
      ASM_SIMP_TAC[ARC_IMP_PATH]] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL] THEN
    ASM_MESON_TAC[pathstart];
    ALL_TAC] THEN
  ASM_CASES_TAC `(pathstart(g):real^N) IN path_image h` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [path_image]) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `subpath u (vec 1) (h:real^1->real^N)` THEN
    ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
    REWRITE_TAC[pathfinish] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
      ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH];
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s SUBSET u UNION t`) THEN
      MATCH_MP_TAC PATH_IMAGE_SUBPATH_SUBSET THEN
      ASM_SIMP_TAC[ARC_IMP_PATH]] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL] THEN
    ASM_MESON_TAC[pathfinish];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^1->real^N`; `(:real^N) DIFF path_image h`]
   SUBPATH_TO_FRONTIER) THEN
  ASM_SIMP_TAC[ARC_IMP_PATH; IN_DIFF; IN_UNIV; PATHSTART_IN_PATH_IMAGE] THEN
  REWRITE_TAC[FRONTIER_COMPLEMENT; INTERIOR_COMPLEMENT] THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED; CLOSED_PATH_IMAGE; ARC_IMP_PATH; frontier] THEN
  REWRITE_TAC[IN_DIFF; PATHFINISH_SUBPATH] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [path_image]) THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^1` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `subpath (vec 0) u g ++ subpath v (vec 1) h:real^1->real^N` THEN
  ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_SUBPATH;
                  PATHFINISH_SUBPATH] THEN
  REWRITE_TAC[pathstart; pathfinish] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `path_image(subpath (vec 0) u g) UNION
                path_image(subpath v (vec 1) h):real^N->bool` THEN
    REWRITE_TAC[PATH_IMAGE_JOIN_SUBSET] THEN
    MATCH_MP_TAC(SET_RULE
     `s SUBSET t /\ s' SUBSET t' ==> (s UNION s') SUBSET (t UNION t')`) THEN
    CONJ_TAC THEN MATCH_MP_TAC PATH_IMAGE_SUBPATH_SUBSET THEN
    ASM_SIMP_TAC[ARC_IMP_PATH] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL]] THEN
  MATCH_MP_TAC ARC_JOIN THEN
  ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
    ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL] THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN
    MP_TAC(GEN_REWRITE_RULE I [arc] (ASSUME `arc(g:real^1->real^N)`)) THEN
    DISCH_THEN(MP_TAC o SPECL [`u:real^1`; `vec 0:real^1`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~((pathstart(g):real^N) IN path_image h)` THEN
    REWRITE_TAC[pathstart; path_image; IN_IMAGE] THEN
    EXISTS_TAC `v:real^1` THEN ASM_MESON_TAC[];
    MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
    ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL] THEN
    DISCH_TAC THEN
    MP_TAC(GEN_REWRITE_RULE I [arc] (ASSUME `arc(h:real^1->real^N)`)) THEN
    DISCH_THEN(MP_TAC o SPECL [`v:real^1`; `vec 1:real^1`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~((pathfinish(h):real^N) IN path_image g)` THEN
    REWRITE_TAC[pathfinish; path_image; IN_IMAGE] THEN
    EXISTS_TAC `u:real^1` THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
      `p DELETE gu SUBSET UNIV DIFF h
       ==> h' SUBSET h /\ gu = hv ==> p INTER h' SUBSET {hv}`)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PATH_IMAGE_SUBPATH_SUBSET THEN
    ASM_SIMP_TAC[ARC_IMP_PATH] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL]]);;

let CONNECTED_OPEN_ARC_CONNECTED = prove
 (`!s:real^N->bool.
      open s /\ connected s
      ==> !x y. x IN s /\ y IN s
                ==> x = y \/
                    ?g. arc g /\
                        path_image g SUBSET s /\
                        pathstart g = x /\
                        pathfinish g = y`,
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d ==> e \/ f <=>
                         a /\ b /\ c /\ d ==> c /\ d /\ e \/ f`] THEN
  MATCH_MP_TAC GENERAL_CONNECTED_OPEN THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
    REPEAT GEN_TAC THEN MATCH_MP_TAC MONO_OR THEN SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `reversepath(g:real^1->real^N)` THEN
    ASM_SIMP_TAC[ARC_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH];
    ALL_TAC;
    MESON_TAC[SUBSET_TRANS; SUBSET];
    MAP_EVERY X_GEN_TAC
     [`s:real^N->bool`; `x:real^N`; `y:real^N`; `e:real`] THEN
    ASM_CASES_TAC `y:real^N = x` THEN ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `&0 < e` THENL
     [STRIP_TAC; ASM_MESON_TAC[BALL_EQ_EMPTY; NOT_IN_EMPTY; REAL_NOT_LE]] THEN
    EXISTS_TAC `linepath(x:real^N,y)` THEN
    ASM_SIMP_TAC[ARC_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    MATCH_MP_TAC(GEN_REWRITE_RULE I [ CONVEX_CONTAINS_SEGMENT]
     (SPEC_ALL CONVEX_BALL)) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL]] THEN
  MAP_EVERY X_GEN_TAC
   [`s:real^N->bool`; `x:real^N`; `y:real^N`; `z:real^N`] THEN
  ASM_CASES_TAC `y:real^N = z` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `x:real^N = z` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET; ARC_IMP_PATH];
    ALL_TAC] THEN
  ASM_CASES_TAC `x:real^N = y` THEN ASM_REWRITE_TAC[] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `h:real^1->real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`g:real^1->real^N`; `h:real^1->real^N`]
        ARC_CONNECTED_TRANS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* More stuff about segments.                                                *)
(* ------------------------------------------------------------------------- *)

let SEGMENT_OPEN_SUBSET_CLOSED = prove
 (`!a b. segment(a,b) SUBSET segment[a,b]`,
  REWRITE_TAC[CONJUNCT2(SPEC_ALL segment)] THEN SET_TAC[]);;

let CLOSED_SEGMENT = prove
 (`!a b. closed(segment[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
  MATCH_MP_TAC FINITE_IMP_COMPACT THEN SIMP_TAC[FINITE_RULES]);;

let SEGMENT_IMAGE_INTERVAL = prove
 (`(!a b. segment[a,b] =
          IMAGE (\u. (&1 - drop u) % a + drop u % b)
                (interval[vec 0,vec 1])) /\
   (!a b. ~(a = b)
          ==> segment(a,b) =
                IMAGE (\u. (&1 - drop u) % a + drop u % b)
                (interval(vec 0,vec 1)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTERVAL_1; IN_SEGMENT] THEN
  ASM_REWRITE_TAC[GSYM EXISTS_DROP; DROP_VEC] THEN MESON_TAC[]);;

let CLOSURE_SEGMENT = prove
 (`(!a b:real^N. closure(segment[a,b]) = segment[a,b]) /\
   (!a b:real^N. closure(segment(a,b)) = if a = b then {} else segment[a,b])`,
  REWRITE_TAC[CLOSURE_EQ; CLOSED_SEGMENT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; CLOSURE_EMPTY] THEN
  ASM_SIMP_TAC[SEGMENT_IMAGE_INTERVAL] THEN
  ASM_SIMP_TAC[CONV_RULE(RAND_CONV SYM_CONV) (SPEC_ALL CLOSURE_OPEN_INTERVAL);
               INTERVAL_EQ_EMPTY_1; DROP_VEC; REAL_ARITH `~(&1 <= &0)`] THEN
  SUBGOAL_THEN
   `(\u. (&1 - drop u) % a + drop u % (b:real^N)) =
    (\x. a + x) o (\u. drop u % (b - a))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o; CLOSURE_TRANSLATION] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CLOSURE_INJECTIVE_LINEAR_IMAGE THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RCANCEL; VECTOR_SUB_EQ; DROP_EQ] THEN
  REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC);;

let AFFINE_HULL_SEGMENT = prove
 (`(!a b:real^N. affine hull (segment [a,b]) = affine hull {a,b}) /\
   (!a b:real^N. affine hull (segment(a,b)) =
                 if a = b then {} else affine hull {a,b})`,
  REWRITE_TAC[SEGMENT_CONVEX_HULL; AFFINE_HULL_CONVEX_HULL] THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM AFFINE_HULL_CLOSURE] THEN
  REWRITE_TAC[CLOSURE_SEGMENT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[AFFINE_HULL_EMPTY] THEN
  REWRITE_TAC[SEGMENT_CONVEX_HULL; AFFINE_HULL_CONVEX_HULL]);;

let SEGMENT_AS_BALL = prove
 (`(!a b. segment[a:real^N,b] =
         affine hull {a,b} INTER cball(inv(&2) % (a + b),norm(b - a) / &2)) /\
   (!a b. segment(a:real^N,b) =
         affine hull {a,b} INTER ball(inv(&2) % (a + b),norm(b - a) / &2))`,
  REPEAT STRIP_TAC THEN
  (ASM_CASES_TAC `b:real^N = a` THEN
   ASM_REWRITE_TAC[SEGMENT_REFL; VECTOR_SUB_REFL; NORM_0] THEN
   CONV_TAC REAL_RAT_REDUCE_CONV THEN
   REWRITE_TAC[BALL_TRIVIAL; CBALL_TRIVIAL] THENL
    [REWRITE_TAC[INTER_EMPTY; INSERT_AC] THEN
     REWRITE_TAC[VECTOR_ARITH `&1 / &2 % (a + a) = a`] THEN
     REWRITE_TAC[SET_RULE `a = b INTER a <=> a SUBSET b`; HULL_SUBSET];
     ASM_REWRITE_TAC[EXTENSION; IN_SEGMENT; IN_INTER; AFFINE_HULL_2] THEN
     X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
     REWRITE_TAC[REAL_ARITH `u + v:real = &1 <=> u = &1 - v`] THEN
     REWRITE_TAC[UNWIND_THM2] THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
     AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
     X_GEN_TAC `u:real` THEN REWRITE_TAC[] THEN
     ASM_CASES_TAC `y:real^N = (&1 - u) % a + u % b` THEN
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_BALL; IN_CBALL; dist; VECTOR_ARITH
      `&1 / &2 % (a + b) - ((&1 - u) % a + u % b):real^N =
       (&1 / &2 - u) % (b - a)`] THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_LT_MUL_EQ; REAL_LE_MUL_EQ; NORM_POS_LT;
     VECTOR_SUB_EQ; REAL_ARITH `a * n < n / &2 <=> &0 < n * (inv(&2) - a)`;
              REAL_ARITH `a * n <= n / &2 <=> &0 <= n * (inv(&2) - a)`] THEN
    REAL_ARITH_TAC]));;

let CONVEX_SEGMENT = prove
 (`(!a b. convex(segment[a,b])) /\ (!a b. convex(segment(a,b)))`,
  REWRITE_TAC[SEGMENT_AS_BALL] THEN
  SIMP_TAC[CONVEX_INTER; CONVEX_BALL; CONVEX_CBALL;
           AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL]);;

let RELATIVE_INTERIOR_SEGMENT = prove
 (`(!a b:real^N.
      relative_interior(segment[a,b]) = if a = b then {a} else segment(a,b)) /\
   (!a b:real^N. relative_interior(segment(a,b)) = segment(a,b))`,
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = b` THEN
    ASM_REWRITE_TAC[SEGMENT_REFL; RELATIVE_INTERIOR_EMPTY] THEN
    REWRITE_TAC[RELATIVE_INTERIOR_EQ; OPEN_IN_OPEN] THEN
    ASM_REWRITE_TAC[AFFINE_HULL_SEGMENT] THEN
    EXISTS_TAC `ball(inv(&2) % (a + b):real^N,norm(b - a) / &2)` THEN
    REWRITE_TAC[OPEN_BALL; SEGMENT_AS_BALL];
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[SEGMENT_REFL; RELATIVE_INTERIOR_SING] THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`] (CONJUNCT2 CLOSURE_SEGMENT)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
    MATCH_MP_TAC CONVEX_RELATIVE_INTERIOR_CLOSURE THEN
    REWRITE_TAC[CONVEX_SEGMENT]]);;

let PATH_CONNECTED_SEGMENT = prove
 (`(!a b. path_connected(segment[a,b])) /\
   (!a b. path_connected(segment(a,b)))`,
  SIMP_TAC[CONVEX_IMP_PATH_CONNECTED; CONVEX_SEGMENT]);;

let CONNECTED_SEGMENT = prove
 (`(!a b. connected(segment[a,b])) /\ (!a b. connected(segment(a,b)))`,
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_SEGMENT]);;

let CONVEX_SEMIOPEN_SEGMENT = prove
 (`(!a b:real^N. convex(segment[a,b] DELETE a)) /\
   (!a b:real^N. convex(segment[a,b] DELETE b))`,
  MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN
  CONJ_TAC THENL [MESON_TAC[SEGMENT_SYM]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:real^N = a` THEN
  ASM_SIMP_TAC[SEGMENT_REFL; SET_RULE `{a} DELETE a = {}`; CONVEX_EMPTY] THEN
  REWRITE_TAC[CONVEX_ALT; IN_DELETE] THEN
  SIMP_TAC[REWRITE_RULE[CONVEX_ALT] CONVEX_SEGMENT] THEN
  REWRITE_TAC[IN_SEGMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC;
                  GSYM VECTOR_ADD_ASSOC] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
   `x % a + y % b + z % a + w % b:real^N = a <=>
    (&1 - x - z) % a = (w + y) % b`] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL; REAL_ARITH
   `&1 - (&1 - u) * (&1 - v) - u * (&1 - w) =
    u * w + (&1 - u) * v`] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE; REAL_ARITH
   `&0 <= x /\ &0 <= y ==> (x + y = &0 <=> x = &0 /\ y = &0)`] THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_ARITH `&1 - x = &0 <=> x = &1`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `(u = &0 \/ w = &0) /\ (u = &1 \/ v = &0)
    ==> u = &0 /\ v = &0 \/ u = &1 /\ w = &0 \/ v = &0 /\ w = &0`)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
  ASM_MESON_TAC[VECTOR_ARITH `(&1 - &0) % a + &0 % b:real^N = a`]);;

let PATH_CONNECTED_SEMIOPEN_SEGMENT = prove
 (`(!a b:real^N. path_connected(segment[a,b] DELETE a)) /\
   (!a b:real^N. path_connected(segment[a,b] DELETE b))`,
  SIMP_TAC[CONVEX_IMP_PATH_CONNECTED; CONVEX_SEMIOPEN_SEGMENT]);;

let CONNECTED_SEMIOPEN_SEGMENT = prove
 (`(!a b:real^N. connected(segment[a,b] DELETE a)) /\
   (!a b:real^N. connected(segment[a,b] DELETE b))`,
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_SEMIOPEN_SEGMENT]);;

let SEGMENT_EQ_EMPTY = prove
 (`(!a b:real^N. ~(segment[a,b] = {})) /\
   (!a b:real^N. segment(a,b) = {} <=> a = b)`,
  REWRITE_TAC[SEGMENT_CONVEX_HULL; CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL] THEN
  ASM_MESON_TAC[NOT_IN_EMPTY; MIDPOINT_IN_SEGMENT]);;

let FINITE_SEGMENT = prove
 (`(!a b:real^N. FINITE(segment[a,b]) <=> a = b) /\
   (!a b:real^N. FINITE(segment(a,b)) <=> a = b)`,
  REWRITE_TAC[open_segment; SET_RULE `s DIFF {a,b} = s DELETE a DELETE b`] THEN
  REWRITE_TAC[FINITE_DELETE] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; FINITE_SING] THEN
  REWRITE_TAC[SEGMENT_IMAGE_INTERVAL] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) FINITE_IMAGE_INJ_EQ o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % a + u % b:real^N = (&1 - v) % a + v % b <=>
      (u - v) % (b - a) = vec 0`] THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; REAL_SUB_0; DROP_EQ];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FINITE_INTERVAL_1] THEN
    REWRITE_TAC[DROP_VEC] THEN REAL_ARITH_TAC]);;

let SEGMENT_EQ_SING = prove
 (`(!a b c:real^N. segment[a,b] = {c} <=> a = c /\ b = c) /\
   (!a b c:real^N. ~(segment(a,b) = {c}))`,
  REWRITE_TAC[SEGMENT_CONVEX_HULL; CONVEX_HULL_EQ_SING] THEN
  CONJ_TAC THENL [SET_TAC[]; REPEAT GEN_TAC] THEN
  ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; NOT_INSERT_EMPTY] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] (CONJUNCT2 FINITE_SEGMENT)) THEN
  ASM_REWRITE_TAC[FINITE_SING]);;

let SUBSET_SEGMENT_OPEN_CLOSED = prove
 (`!a b c d:real^N.
        segment(a,b) SUBSET segment(c,d) <=>
        a = b \/ segment[a,b] SUBSET segment[c,d]`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ASM_CASES_TAC `a:real^N = b` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUBSET_CLOSURE) THEN
    ASM_REWRITE_TAC[CLOSURE_SEGMENT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[SUBSET_EMPTY; SEGMENT_EQ_EMPTY];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THEN
  REWRITE_TAC[SEGMENT_REFL; EMPTY_SUBSET] THEN
  ABBREV_TAC `m:real^N = d - c` THEN POP_ASSUM MP_TAC THEN
  GEOM_NORMALIZE_TAC `m:real^N` THEN
  SIMP_TAC[VECTOR_SUB_EQ; SEGMENT_REFL; SEGMENT_EQ_SING; SEGMENT_EQ_EMPTY;
           SET_RULE `s SUBSET {a} <=> s = {a} \/ s = {}`; SUBSET_REFL] THEN
  X_GEN_TAC `m:real^N` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN POP_ASSUM MP_TAC THEN
  GEOM_ORIGIN_TAC `c:real^N` THEN GEOM_BASIS_MULTIPLE_TAC 1 `d:real^N` THEN
  X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  SIMP_TAC[VECTOR_SUB_RZERO; NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
  ASM_REWRITE_TAC[real_abs; REAL_MUL_RID] THEN DISCH_THEN SUBST_ALL_TAC THEN
  POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
  SUBGOAL_THEN `collinear{vec 0:real^N,&1 % basis 1,x} /\
                collinear{vec 0:real^N,&1 % basis 1,y}`
  MP_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {a,c,b}`] THEN
    CONJ_TAC THEN MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN
    REWRITE_TAC[BETWEEN_IN_SEGMENT] THEN
    ASM_MESON_TAC[SUBSET; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SIMP_TAC[COLLINEAR_LEMMA_ALT; BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL;
           VECTOR_ARITH `&1 % x:real^N = vec 0 <=> x = vec 0`] THEN
  REWRITE_TAC[IMP_CONJ; VECTOR_MUL_ASSOC; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:real` THEN REWRITE_TAC[REAL_MUL_RID] THEN
  DISCH_THEN SUBST_ALL_TAC THEN X_GEN_TAC `b:real` THEN
  DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
  SUBST1_TAC(VECTOR_ARITH `vec 0:real^N = &0 % basis 1`) THEN
  ASM_SIMP_TAC[SEGMENT_SCALAR_MULTIPLE; VECTOR_MUL_RCANCEL; BASIS_NONZERO;
               DIMINDEX_GE_1; LE_REFL; SET_RULE
                `(!x y. x % v = y % v <=> x = y)
                 ==> ({x % v | P x} SUBSET {x % v | Q x} <=>
                      {x | P x} SUBSET {x | Q x})`] THEN
  REWRITE_TAC[REAL_ARITH `a <= x /\ x <= b \/ b <= x /\ x <= a <=>
                          min a b <= x /\ x <= max a b`;
              REAL_ARITH `a < x /\ x < b \/ b < x /\ x < a <=>
                          min a b < x /\ x < max a b`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_TAC THEN
  X_GEN_TAC `x:real` THEN
  FIRST_X_ASSUM(fun th -> MAP_EVERY (MP_TAC o C SPEC th)
        [`min (a:real) b`; `max (a:real) b`]) THEN
  REAL_ARITH_TAC);;

let SUBSET_SEGMENT = prove
 (`(!a b c d:real^N.
        segment[a,b] SUBSET segment[c,d] <=>
        a IN segment[c,d] /\ b IN segment[c,d]) /\
   (!a b c d:real^N.
        segment[a,b] SUBSET segment(c,d) <=>
        a IN segment(c,d) /\ b IN segment(c,d)) /\
   (!a b c d:real^N.
        segment(a,b) SUBSET segment[c,d] <=>
        a = b \/ a IN segment[c,d] /\ b IN segment[c,d]) /\
   (!a b c d:real^N.
        segment(a,b) SUBSET segment(c,d) <=>
        a = b \/ a IN segment[c,d] /\ b IN segment[c,d])`,
  MATCH_MP_TAC(TAUT `(a /\ b) /\ (a /\ b ==> c) ==> a /\ b /\ c`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SEGMENT_CONVEX_HULL] THEN
    SIMP_TAC[SUBSET_HULL; CONVEX_SEGMENT] THEN SET_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_SEGMENT_OPEN_CLOSED] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `closure(segment(a:real^N,b)) SUBSET segment[c,d]` THEN
    CONJ_TAC THENL [SIMP_TAC[CLOSURE_MINIMAL_EQ; CLOSED_SEGMENT]; ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_SEGMENT] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[EMPTY_SUBSET]]);;

let INTERIOR_SEGMENT = prove
 (`(!a b:real^N. interior(segment[a,b]) =
                 if 2 <= dimindex(:N) then {} else segment(a,b)) /\
   (!a b:real^N. interior(segment(a,b)) =
                 if 2 <= dimindex(:N) then {} else segment(a,b))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `2 <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(SET_RULE `t SUBSET s /\ s = {} ==> s = {} /\ t = {}`) THEN
    SIMP_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET_INTERIOR] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC EMPTY_INTERIOR_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN FIRST_ASSUM
     (MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS)) THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN ARITH_TAC;
    ASM_CASES_TAC `a:real^N = b` THEN
    ASM_SIMP_TAC[SEGMENT_REFL; INTERIOR_EMPTY; EMPTY_INTERIOR_FINITE;
                 FINITE_SING] THEN
    SUBGOAL_THEN
     `affine hull (segment[a,b]) = (:real^N) /\
      affine hull (segment(a,b)) = (:real^N)`
     (fun th -> ASM_SIMP_TAC[th; GSYM RELATIVE_INTERIOR_INTERIOR;
                             RELATIVE_INTERIOR_SEGMENT]) THEN
    ASM_REWRITE_TAC[AFFINE_HULL_SEGMENT] THEN
    MATCH_MP_TAC AFFINE_INDEPENDENT_SPAN_GT THEN
    REWRITE_TAC[AFFINE_INDEPENDENT_2] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RULES; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_ARITH_TAC]);;

let SEGMENT_EQ = prove
 (`(!a b c d:real^N.
        segment[a,b] = segment[c,d] <=> {a,b} = {c,d}) /\
   (!a b c d:real^N.
        ~(segment[a,b] = segment(c,d))) /\
   (!a b c d:real^N.
        ~(segment(a,b) = segment[c,d])) /\
   (!a b c d:real^N.
        segment(a,b) = segment(c,d) <=> a = b /\ c = d \/ {a,b} = {c,d})`,
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN(fun th -> MP_TAC th THEN
       MP_TAC(AP_TERM `\s:real^N->bool. s DIFF relative_interior s` th)) THEN
      REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[SEGMENT_REFL]) THEN
      SIMP_TAC[ENDS_IN_SEGMENT; open_segment; SET_RULE
        `a IN s /\ b IN s ==> s DIFF (s DIFF {a,b}) = {a,b}`] THEN
      ASM SET_TAC[SEGMENT_EQ_SING];
      SIMP_TAC[SEGMENT_CONVEX_HULL]];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `closed:(real^N->bool)->bool`) THEN
    REWRITE_TAC[CLOSED_SEGMENT] THEN
    REWRITE_TAC[GSYM CLOSURE_EQ; CLOSURE_SEGMENT] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM SET_TAC[SEGMENT_EQ_EMPTY];
      REWRITE_TAC[open_segment; ENDS_IN_SEGMENT; SET_RULE
       `s = s DIFF {a,b} <=> ~(a IN s) /\ ~(b IN s)`]];
    DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REPEAT GEN_TAC THEN ASM_CASES_TAC `c:real^N = d` THEN
    ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY; SEGMENT_REFL] THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONV_TAC(BINOP_CONV SYM_CONV)THEN
    ASM_CASES_TAC `a:real^N = b` THEN
    ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY; SEGMENT_REFL] THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_SEGMENT_OPEN_CLOSED] THEN
    ASM_REWRITE_TAC[SUBSET_ANTISYM_EQ]]);;

let COMPACT_SEGMENT = prove
 (`!a b. compact(segment[a,b])`,
  SIMP_TAC[SEGMENT_CONVEX_HULL; COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT;
           FINITE_INSERT; FINITE_EMPTY]);;

let BOUNDED_SEGMENT = prove
 (`(!a b:real^N. bounded(segment[a,b])) /\
   (!a b:real^N. bounded(segment(a,b)))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(MESON[BOUNDED_SUBSET]
   `bounded s /\ t SUBSET s ==> bounded s /\ bounded t`) THEN
  REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED] THEN
  MESON_TAC[COMPACT_IMP_BOUNDED; COMPACT_SEGMENT]);;

(* ------------------------------------------------------------------------- *)
(* Relations between components and path components.                         *)
(* ------------------------------------------------------------------------- *)

let OPEN_CONNECTED_COMPONENT = prove
 (`!s x:real^N. open s ==> open(connected_component s x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[SUBSET; CONNECTED_COMPONENT_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `connected_component s (x:real^N) = connected_component s y`
  SUBST1_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENT_EQ];
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL; CONNECTED_BALL]]);;

let IN_CLOSURE_CONNECTED_COMPONENT = prove
 (`!x y:real^N.
        x IN s /\ open s
        ==> (x IN closure(connected_component s y) <=>
             x IN connected_component s y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN
  DISCH_TAC THEN SUBGOAL_THEN
   `~((connected_component s (x:real^N)) INTER
      closure(connected_component s y) = {})`
  MP_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    ASM_REWRITE_TAC[IN; CONNECTED_COMPONENT_REFL_EQ];
    ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY; OPEN_CONNECTED_COMPONENT] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_OVERLAP] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[IN; CONNECTED_COMPONENT_REFL_EQ]]);;

let PATH_COMPONENT_SUBSET_CONNECTED_COMPONENT = prove
 (`!s x:real^N. (path_component s x) SUBSET (connected_component s x)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN s` THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    ASM_REWRITE_TAC[PATH_COMPONENT_SUBSET; IN; PATH_COMPONENT_REFL_EQ] THEN
    SIMP_TAC[PATH_CONNECTED_IMP_CONNECTED; PATH_CONNECTED_PATH_COMPONENT];
    ASM_MESON_TAC[PATH_COMPONENT_EQ_EMPTY; SUBSET_REFL;
                  CONNECTED_COMPONENT_EQ_EMPTY]]);;

let OPEN_PATH_CONNECTED_COMPONENT = prove
 (`!s x:real^N. open s ==> path_component s x = connected_component s x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x:real^N) IN s` THENL
   [ALL_TAC;
    ASM_MESON_TAC[PATH_COMPONENT_EQ_EMPTY; CONNECTED_COMPONENT_EQ_EMPTY]] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[PATH_COMPONENT_SUBSET_CONNECTED_COMPONENT] THEN
  MATCH_MP_TAC PATH_COMPONENT_MAXIMAL THEN
  ASM_REWRITE_TAC[CONNECTED_COMPONENT_SUBSET; IN;
                  CONNECTED_COMPONENT_REFL_EQ] THEN
  MATCH_MP_TAC CONNECTED_OPEN_PATH_CONNECTED THEN
  ASM_SIMP_TAC[OPEN_CONNECTED_COMPONENT; CONNECTED_CONNECTED_COMPONENT]);;

(* ------------------------------------------------------------------------- *)
(* Lower bound on norms within segment between vectors.                      *)
(* Could have used these for connectedness results below, in fact.           *)
(* ------------------------------------------------------------------------- *)

let NORM_SEGMENT_LOWERBOUND = prove
 (`!a b x:real^N r d.
        &0 < r /\
        norm(a) = r /\ norm(b) = r /\ x IN segment[a,b] /\
        a dot b = d * r pow 2
        ==> sqrt((&1 - abs d) / &2) * r <= norm(x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM real_ge] THEN
  REWRITE_TAC[NORM_GE_SQUARE] THEN DISJ2_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[real_ge; DOT_LMUL; DOT_RMUL; REAL_MUL_RZERO; VECTOR_ARITH
   `(a + b) dot (a + b) = a dot a + b dot b + &2 * a dot b`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 - u) * (&1 - u) * r pow 2 + u * u * r pow 2 -
              &2 * (&1 - u) * u * abs d * r pow 2` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
    REWRITE_TAC[GSYM REAL_POW_2; REAL_ARITH
     `(&1 - u) pow 2 + u pow 2 - ((&2 * (&1 - u)) * u) * d =
      (&1 + d) * (&1 - &2 * u + &2 * u pow 2) - d`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + abs d) * &1 / &2 - abs d` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `(&1 + d) * &1 / &2 - d = (&1 - d) / &2`] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SQRT_POW_2 THEN
      MP_TAC(ISPECL [`a:real^N`; `b:real^N`] NORM_CAUCHY_SCHWARZ_ABS) THEN
      ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_POW2_ABS] THEN
      ASM_REWRITE_TAC[REAL_ARITH `r * r = &1 * r pow 2`] THEN
      ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_POW_LT] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x - a <= y - a`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= (u - &1 / &2) * (u - &1 / &2)
          ==> &1 / &2 <= &1 - &2 * u + &2 * u pow 2`) THEN
        REWRITE_TAC[REAL_LE_SQUARE]]];
    ASM_REWRITE_TAC[GSYM NORM_POW_2; REAL_LE_LADD; real_sub] THEN
    MATCH_MP_TAC(REAL_ARITH `abs(a) <= --x ==> x <= a`) THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_MUL_LNEG; REAL_NEG_NEG] THEN
    REWRITE_TAC[REAL_ABS_POW; REAL_POW2_ABS; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
    ASM_REWRITE_TAC[real_abs; GSYM real_sub; REAL_SUB_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Special case of orthogonality (could replace 2 by sqrt(2)).               *)
(* ------------------------------------------------------------------------- *)

let NORM_SEGMENT_ORTHOGONAL_LOWERBOUND = prove
 (`!a b:real^N x r.
        r <= norm(a) /\ r <= norm(b) /\ orthogonal a b /\ x IN segment[a,b]
        ==> r / &2 <= norm(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM real_ge] THEN
  REWRITE_TAC[NORM_GE_SQUARE] THEN REWRITE_TAC[real_ge] THEN
  ASM_CASES_TAC `r <= &0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[orthogonal] THEN STRIP_TAC THEN DISJ2_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[DOT_LMUL; DOT_RMUL; REAL_MUL_RZERO; VECTOR_ARITH
   `(a + b) dot (a + b) = a dot a + b dot b + &2 * a dot b`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 - u) * (&1 - u) * r pow 2 + u * u * r pow 2` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(r / &2) pow 2 = &1 / &4 * r pow 2`] THEN
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= (u - &1 / &2) * (u - &1 / &2)
      ==> &1 / &4 <= (&1 - u) * (&1 - u) + u * u`) THEN
    REWRITE_TAC[REAL_LE_SQUARE];
    REWRITE_TAC[REAL_ADD_RID] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
    CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Sphere is path-connected.                                                 *)
(* ------------------------------------------------------------------------- *)

let PATH_CONNECTED_PUNCTURED_UNIVERSE = prove
 (`!a. 2 <= dimindex(:N) ==> path_connected((:real^N) DIFF {a})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(:real^N) DIFF {a} = IMAGE (\x. x + a) {x | ~(x = vec 0)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_DIFF; IN_SING; IN_ELIM_THM;
      UNWIND_THM2; VECTOR_ARITH `x:real^N = y + a <=> y = x - a`] THEN
    REWRITE_TAC[VECTOR_SUB_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; NOT_FORALL_THM; NOT_IMP] THEN
  MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
  SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
  SUBGOAL_THEN
   `!k. 2 <= k /\ k <= dimindex(:N)
       ==> path_connected
              {x:real^N | ?i. (1 <= i /\ i <= k) /\ ~((basis i) dot x = &0)}`
  (MP_TAC o SPEC `dimindex(:N)`) THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[LE_REFL; TAUT `a /\ ~b <=> ~(a ==> b)`] THEN
    SIMP_TAC[VEC_COMPONENT; DOT_BASIS]] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{x:real^N | ?i. 1 <= i /\ i <= SUC k /\ ~(basis i dot x = &0)} =
    {x | basis(SUC k) dot x < &0} UNION
    {x | basis(SUC k) dot x > &0} UNION
    {x | ?i. 1 <= i /\ i <= k /\ ~(basis i dot x = &0)}`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[LE; ARITH_RULE `1 <= SUC k`;
                 REAL_ARITH `~(x = &0) <=> x < &0 \/ x > &0`] THEN
    SET_TAC[ARITH_RULE `1 <= SUC k`];
    ALL_TAC] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `2 <= SUC k ==> k = 1 \/ 2 <= k`))
  THENL
   [ASM_REWRITE_TAC[CONJ_ASSOC; LE_ANTISYM; UNWIND_THM1] THEN
    REWRITE_TAC[ARITH; REAL_ARITH `~(x = &0) <=> x < &0 \/ x > &0`] THEN
    REWRITE_TAC[SET_RULE
     `s UNION t UNION {x | P x \/ Q x} =
      (s UNION {x | P x}) UNION (t UNION {x | Q x})`] THEN
    REPEAT(MATCH_MP_TAC PATH_CONNECTED_UNION THEN REPEAT CONJ_TAC) THEN
    ASM_SIMP_TAC[CONVEX_IMP_PATH_CONNECTED; CONVEX_HALFSPACE_LT;
                 CONVEX_HALFSPACE_GT] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNION; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[DOT_BASIS; NOT_FORALL_THM; ARITH; DIMINDEX_GE_1] THENL
     [EXISTS_TAC `(lambda i. -- &1):real^N`;
      EXISTS_TAC `(lambda i. &1):real^N`;
      EXISTS_TAC `(lambda i. if i = 1 then &1 else -- &1):real^N`] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; ARITH; DIMINDEX_GE_1] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC PATH_CONNECTED_UNION THEN
    ASM_SIMP_TAC[CONVEX_IMP_PATH_CONNECTED; CONVEX_HALFSPACE_LT] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONNECTED_UNION THEN
      ASM_SIMP_TAC[CONVEX_IMP_PATH_CONNECTED; CONVEX_HALFSPACE_LT;
                   CONVEX_HALFSPACE_GT; ARITH_RULE `SUC k <= n ==> k <= n`];
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNION; IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ ~c <=> ~(a /\ b ==> c)`] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `SUC k <= n ==> !i. i <= k ==> i <= n`)) THEN
    ASM_SIMP_TAC[DOT_BASIS; NOT_FORALL_THM; ARITH; DIMINDEX_GE_1;
                 ARITH_RULE `1 <= SUC k`] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; NOT_IMP; RIGHT_OR_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN EXISTS_TAC `k:num` THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= k ==> 1 <= k`; LE_REFL] THENL
     [EXISTS_TAC `(lambda i. &1):real^N`;
      EXISTS_TAC `(lambda i. -- &1):real^N`] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; ARITH_RULE `2 <= j ==> 1 <= j`;
                 ARITH_RULE `SUC j <= n ==> j <= n`] THEN
    REAL_ARITH_TAC]);;

let PATH_CONNECTED_SPHERE = prove
 (`!a r. 2 <= dimindex(:N) ==> path_connected {x:real^N | norm(x - a) = r}`,
  REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `r < &0 \/ r = &0 \/ &0 < r`)
  THENL
   [ASM_SIMP_TAC[NORM_ARITH `r < &0 ==> ~(norm x = r)`; EMPTY_GSPEC;
                 PATH_CONNECTED_EMPTY];
    ASM_SIMP_TAC[NORM_EQ_0; VECTOR_SUB_EQ; SING_GSPEC; PATH_CONNECTED_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x:real^N | norm(x - a) = r} = IMAGE (\x. a + r % x) {x | norm x = &1}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN REWRITE_TAC[SUBSET] THENL
     [REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN
      DISCH_TAC THEN EXISTS_TAC `inv(r) % (x - a:real^N)` THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; NORM_MUL;
                  real_abs; REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_MUL_LINV] THEN
      VECTOR_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; VECTOR_ADD_SUB] THEN
      SIMP_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
  SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID;
           CONTINUOUS_ON_CONST] THEN
  SUBGOAL_THEN
   `{x:real^N | norm x = &1} =
    IMAGE (\x. inv(norm x) % x) ((:real^N) DIFF {vec 0})`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_DIFF; IN_SING; IN_UNIV] THEN
    SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM;
             REAL_MUL_LINV; NORM_EQ_0] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; REAL_INV_1] THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:real^N->real`) THEN
    ASM_REWRITE_TAC[NORM_0; REAL_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[PATH_CONNECTED_PUNCTURED_UNIVERSE] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  REWRITE_TAC[o_DEF; CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_AT_WITHIN_INV) THEN
  ASM_REWRITE_TAC[NORM_EQ_0] THEN MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
  REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_AT_LIFT_NORM]);;

let CONNECTED_SPHERE = prove
 (`!a r. 2 <= dimindex(:N) ==> connected {x:real^N | norm(x - a) = r}`,
  SIMP_TAC[PATH_CONNECTED_SPHERE; PATH_CONNECTED_IMP_CONNECTED]);;

(* ------------------------------------------------------------------------- *)
(* Complement of any bounded convex set is connected.                        *)
(* ------------------------------------------------------------------------- *)

let PATH_CONNECTED_COMPLEMENT_BOUNDED_CONVEX = prove
 (`!s. 2 <= dimindex(:N) /\ bounded s /\ convex s
       ==> path_connected((:real^N) DIFF s)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[DIFF_EMPTY; CONVEX_IMP_PATH_CONNECTED; CONVEX_UNIV] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(x:real^N = a) /\ ~(y = a)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `bounded((x:real^N) INSERT y INSERT s)` MP_TAC THENL
   [ASM_REWRITE_TAC[BOUNDED_INSERT]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N` o MATCH_MP BOUNDED_SUBSET_BALL) THEN
  REWRITE_TAC[INSERT_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC PATH_COMPONENT_TRANS THEN
  ABBREV_TAC `C = (B / norm(x - a:real^N))` THEN
  EXISTS_TAC `a + C % (x - a):real^N` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONNECTED_LINEPATH THEN
    REWRITE_TAC[SUBSET; segment; FORALL_IN_GSPEC; IN_DIFF; IN_UNIV] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % x + u % (a + B % (x - a)):real^N =
      a + (&1 + (B - &1) * u) % (x - a)`] THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`a:real^N`; `a + (&1 + (C - &1) * u) % (x - a):real^N`;
      `&1 / (&1 + (C - &1) * u)`]) THEN
    SUBGOAL_THEN `&1 <= &1 + (C - &1) * u` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[REAL_SUB_LE] THEN
      EXPAND_TAC "C" THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_BALL; dist]) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_ARITH `&1 * norm(x - a) = norm(a - x)`];
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP
       (REAL_ARITH `&1 <= a ==> &0 < a`))] THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ;
                 REAL_MUL_LID] THEN
    ASM_SIMP_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; REAL_DIV_RMUL;
                 REAL_LT_IMP_NZ] THEN
    UNDISCH_TAC `~((x:real^N) IN s)` THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PATH_COMPONENT_SYM THEN
  MATCH_MP_TAC PATH_COMPONENT_TRANS THEN
  ABBREV_TAC `D = (B / norm(y - a:real^N))` THEN
  EXISTS_TAC `a + D % (y - a):real^N` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONNECTED_LINEPATH THEN
    REWRITE_TAC[SUBSET; segment; FORALL_IN_GSPEC; IN_DIFF; IN_UNIV] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % y + u % (a + B % (y - a)):real^N =
      a + (&1 + (B - &1) * u) % (y - a)`] THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`a:real^N`; `a + (&1 + (D - &1) * u) % (y - a):real^N`;
      `&1 / (&1 + (D - &1) * u)`]) THEN
    SUBGOAL_THEN `&1 <= &1 + (D - &1) * u` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[REAL_SUB_LE] THEN
      EXPAND_TAC "D" THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_BALL; dist]) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_ARITH `&1 * norm(y - a) = norm(a - y)`];
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP
       (REAL_ARITH `&1 <= a ==> &0 < a`))] THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ;
                 REAL_MUL_LID] THEN
    ASM_SIMP_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; REAL_DIV_RMUL;
                 REAL_LT_IMP_NZ] THEN
    UNDISCH_TAC `~((y:real^N) IN s)` THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PATH_COMPONENT_OF_SUBSET THEN
  EXISTS_TAC `{x:real^N | norm(x - a) = B}` THEN CONJ_TAC THENL
   [UNDISCH_TAC `s SUBSET ball(a:real^N,B)` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_BALL; dist] THEN
    MESON_TAC[NORM_SUB; REAL_LT_REFL];
    MP_TAC(ISPECL [`a:real^N`; `B:real`] PATH_CONNECTED_SPHERE) THEN
    ASM_REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; VECTOR_ADD_SUB; NORM_MUL] THEN
    MAP_EVERY EXPAND_TAC ["C"; "D"] THEN
    REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
    ASM_REAL_ARITH_TAC]);;

let CONNECTED_COMPLEMENT_BOUNDED_CONVEX = prove
 (`!s. 2 <= dimindex(:N) /\ bounded s /\ convex s
       ==> connected((:real^N) DIFF s)`,
  SIMP_TAC[PATH_CONNECTED_IMP_CONNECTED;
           PATH_CONNECTED_COMPLEMENT_BOUNDED_CONVEX]);;

(* ------------------------------------------------------------------------- *)
(* Existence of unbounded components.                                        *)
(* ------------------------------------------------------------------------- *)

let COBOUNDED_UNBOUNDED_COMPONENT = prove
 (`!s. bounded((:real^N) DIFF s)
       ==> ?x. x IN s /\ ~bounded(connected_component s x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^N` o MATCH_MP BOUNDED_SUBSET_BALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B % basis 1:real^N` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `B % basis 1:real^N` o
     GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_UNIV; IN_DIFF; IN_BALL_0] THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < B ==> ~(abs B * &1 < B)`];
    MP_TAC(ISPECL [`basis 1:real^N`; `B:real`] BOUNDED_HALFSPACE_GE) THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL; CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] BOUNDED_SUBSET) THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    SIMP_TAC[CONVEX_HALFSPACE_GE; CONVEX_CONNECTED] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; DOT_RMUL; DOT_BASIS_BASIS; DIMINDEX_GE_1;
                 LE_REFL; real_ge; REAL_MUL_RID; REAL_LE_REFL] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
    `UNIV DIFF s SUBSET b ==> (!x. x IN h ==> ~(x IN b)) ==> h SUBSET s`)) THEN
    SIMP_TAC[IN_ELIM_THM; DOT_BASIS; IN_BALL_0; DIMINDEX_GE_1; LE_REFL] THEN
    GEN_TAC THEN REWRITE_TAC[REAL_NOT_LT] THEN
    MATCH_MP_TAC(REAL_ARITH `abs x <= n ==> b <= x ==> b <= n`) THEN
    SIMP_TAC[COMPONENT_LE_NORM; DIMINDEX_GE_1; LE_REFL]]);;

let COBOUNDED_UNIQUE_UNBOUNDED_COMPONENT = prove
 (`!s x y:real^N.
        2 <= dimindex(:N) /\ bounded((:real^N) DIFF s) /\
        ~bounded(connected_component s x) /\
        ~bounded(connected_component s y)
        ==> connected_component s x = connected_component s y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^N` o MATCH_MP BOUNDED_SUBSET_BALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `ball(vec 0:real^N,B)` CONNECTED_COMPLEMENT_BOUNDED_CONVEX) THEN
  ASM_REWRITE_TAC[BOUNDED_BALL; CONVEX_BALL] THEN DISCH_TAC THEN
  MAP_EVERY
   (MP_TAC o SPEC `B:real` o REWRITE_RULE[bounded; NOT_EXISTS_THM] o ASSUME)
   [`~bounded(connected_component s (y:real^N))`;
    `~bounded(connected_component s (x:real^N))`] THEN
  REWRITE_TAC[NOT_FORALL_THM; IN; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `y':real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN REWRITE_TAC[IN] THEN
  SUBGOAL_THEN `connected_component s (x':real^N) (y':real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `(:real^N) DIFF ball (vec 0,B)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_DIFF; IN_UNIV]] THEN
    REWRITE_TAC[IN_BALL_0] THEN ASM_MESON_TAC[REAL_LT_IMP_LE];
    ASM_MESON_TAC[CONNECTED_COMPONENT_SYM; CONNECTED_COMPONENT_TRANS]]);;
