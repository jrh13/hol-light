(* ========================================================================= *)
(* Faces, extreme points, polytopes, polyhedra etc.                          *)
(* ========================================================================= *)

needs "Multivariate/convex.ml";;

(* ------------------------------------------------------------------------- *)
(* Faces of a (usually convex) set.                                          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("face_of",(12,"right"));;

let face_of = new_definition
 `t face_of s <=>
        t SUBSET s /\ convex t /\
        !a b x. a IN s /\ b IN s /\ x IN t /\ x IN segment(a,b)
                ==> a IN t /\ b IN t`;;

let FACE_OF_TRANSLATION_EQ = prove
 (`!a f s.
        (IMAGE (\x. a + x) f) face_of (IMAGE (\x. a + x) s) <=> f face_of s`,
  REWRITE_TAC[face_of] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [FACE_OF_TRANSLATION_EQ];;

let FACE_OF_LINEAR_IMAGE = prove
 (`!f:real^M->real^N c s.
      linear f /\ (!x y. f x = f y ==> x = y)
      ==> ((IMAGE f c) face_of (IMAGE f s) <=> c face_of s)`,
  REWRITE_TAC[face_of; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN MP_TAC(end_itlist CONJ
   (mapfilter (ISPEC `f:real^M->real^N`) (!invariant_under_linear))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

add_linear_invariants [FACE_OF_LINEAR_IMAGE];;

let FACE_OF_REFL = prove
 (`!s. convex s ==> s face_of s`,
  SIMP_TAC[face_of] THEN SET_TAC[]);;

let FACE_OF_REFL_EQ = prove
 (`!s. s face_of s <=> convex s`,
  SIMP_TAC[face_of] THEN SET_TAC[]);;

let EMPTY_FACE_OF = prove
 (`!s. {} face_of s`,
  REWRITE_TAC[face_of; CONVEX_EMPTY] THEN SET_TAC[]);;

let FACE_OF_EMPTY = prove
 (`!s. s face_of {} <=> s = {}`,
  REWRITE_TAC[face_of; SUBSET_EMPTY; NOT_IN_EMPTY] THEN
  MESON_TAC[CONVEX_EMPTY]);;

let FACE_OF_TRANS = prove
 (`!s t u. s face_of t /\ t face_of u
           ==> s face_of u`,
  REWRITE_TAC[face_of] THEN SET_TAC[]);;

let FACE_OF_FACE = prove
 (`!f s t.
        t face_of s
        ==> (f face_of t <=> f face_of s /\ f SUBSET t)`,
  REWRITE_TAC[face_of] THEN SET_TAC[]);;

let FACE_OF_INTER = prove
 (`!s t1 t2. t1 face_of s /\ t2 face_of s
             ==> (t1 INTER t2) face_of s`,
  SIMP_TAC[face_of; CONVEX_INTER] THEN SET_TAC[]);;

let FACE_OF_INTERS = prove
 (`!P s. ~(P = {}) /\ (!t. t IN P ==> t face_of s)
         ==> (INTERS P) face_of s`,
  REWRITE_TAC[face_of] THEN REPEAT STRIP_TAC THENL
   [ASM SET_TAC[]; ASM_SIMP_TAC[CONVEX_INTERS]; ASM SET_TAC[]; ASM SET_TAC[]]);;

let FACE_OF_INTER_INTER = prove
 (`!f t f' t'.
     f face_of t /\ f' face_of t' ==> (f INTER f') face_of (t INTER t')`,
  REWRITE_TAC[face_of; SUBSET; IN_INTER] THEN MESON_TAC[CONVEX_INTER]);;

let FACE_OF_STILLCONVEX = prove
 (`!s t:real^N->bool.
        convex s
        ==> (t face_of s <=>
             t SUBSET s /\
             convex(s DIFF t) /\
             t = (affine hull t) INTER s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[face_of] THEN
  ASM_CASES_TAC `(t:real^N->bool) SUBSET s` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [CONJ_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN
      REWRITE_TAC[CONVEX_CONTAINS_SEGMENT; open_segment; IN_DIFF] THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; SUBSET_DIFF] THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
     [ASM MESON_TAC[HULL_INC; SUBSET; IN_INTER]; ALL_TAC] THEN
    ASM_CASES_TAC `t:real^N -> bool = {}` THEN
    ASM_REWRITE_TAC[IN_INTER; AFFINE_HULL_EMPTY; NOT_IN_EMPTY] THEN
    MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_RELATIVE_INTERIOR_CBALL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    STRIP_TAC THEN ASM_CASES_TAC `x:real^N = y` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
    ASM_SIMP_TAC[LEFT_FORALL_IMP_THM; OPEN_SEGMENT_ALT] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN ASM_SIMP_TAC[] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[EXISTS_IN_GSPEC] THEN
    EXISTS_TAC `min (&1 / &2) (e / norm(x - y:real^N))` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTER; IN_CBALL; dist] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NORM_MUL; VECTOR_ARITH
       `y - ((&1 - u) % y + u % x):real^N = u % (y - x)`] THEN
      ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
      REWRITE_TAC[NORM_SUB] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e ==> abs(min (&1 / &2) e) <= e`) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ];
      MATCH_MP_TAC(REWRITE_RULE[AFFINE_ALT] AFFINE_AFFINE_HULL) THEN
      ASM_SIMP_TAC[HULL_INC]];
    CONJ_TAC THENL
     [ONCE_ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONVEX_INTER THEN
      ASM_SIMP_TAC[AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `x:real^N`] THEN
    SUBGOAL_THEN
     `!a b x:real^N. a IN s /\ b IN s /\ x IN t /\ x IN segment(a,b) /\
                     (a IN affine hull t ==> b IN affine hull t)
                     ==> a IN t /\ b IN t`
     (fun th -> MESON_TAC[th; SEGMENT_SYM]) THEN
    REPEAT GEN_TAC THEN ASM_CASES_TAC `(a:real^N) IN affine hull t` THEN
    ASM_REWRITE_TAC[] THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    ASM_CASES_TAC `a:real^N = b` THENL
     [ASM_MESON_TAC[SEGMENT_REFL; NOT_IN_EMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^N) IN (s DIFF t) /\ b IN  (s DIFF t)`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF] THEN ONCE_ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      UNDISCH_TAC `~((a:real^N) IN affine hull t)` THEN
      UNDISCH_TAC `(x:real^N) IN segment(a,b)` THEN
      ASM_SIMP_TAC[OPEN_SEGMENT_ALT; CONTRAPOS_THM; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `(%) (inv(&1 - u)) :real^N->real^N`) THEN
      REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_ARITH `x < &1 ==> ~(&1 - x = &0)`] THEN
      REWRITE_TAC[VECTOR_ARITH
       `x:real^N = &1 % a + u % b <=> a = x + --u %  b`] THEN
      DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
      ASM_SIMP_TAC[HULL_INC] THEN
      UNDISCH_TAC `u < &1` THEN CONV_TAC REAL_FIELD;
      MP_TAC(ISPEC `s DIFF t:real^N->bool` CONVEX_CONTAINS_SEGMENT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
      ASM_REWRITE_TAC[SUBSET; IN_DIFF] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
      ASM_MESON_TAC[segment; IN_DIFF]]]);;

let FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE_STRONG = prove
 (`!s a:real^N b.
        convex(s INTER {x | a dot x = b}) /\ (!x. x IN s ==> a dot x <= b)
        ==> (s INTER {x | a dot x = b}) face_of s`,
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `c:real^N`; `d:real`] THEN
  SIMP_TAC[face_of; INTER_SUBSET] THEN
  STRIP_TAC THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `x:real^N`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= x /\ b <= x /\ ~(a < x) /\ ~(b < x) ==> a = x /\ b = x`) THEN
  ASM_SIMP_TAC[] THEN UNDISCH_TAC `(x:real^N) IN segment(a,b)` THEN
  ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; NOT_IN_EMPTY] THEN
  ASM_SIMP_TAC[OPEN_SEGMENT_ALT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `(c:real^N) dot x = d` THEN
  MATCH_MP_TAC(REAL_ARITH `x < a ==> x = a ==> F`) THEN
  SUBST1_TAC(REAL_ARITH `d = (&1 - u) * d + u * d`) THEN
  ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THENL
   [MATCH_MP_TAC REAL_LTE_ADD2; MATCH_MP_TAC REAL_LET_ADD2] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_LMUL_EQ; REAL_SUB_LT]);;

let FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE_STRONG = prove
 (`!s a:real^N b.
        convex(s INTER {x | a dot x = b}) /\ (!x. x IN s ==> a dot x >= b)
        ==> (s INTER {x | a dot x = b}) face_of s`,
  REWRITE_TAC[real_ge] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `--a:real^N`; `--b:real`]
    FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE_STRONG) THEN
  ASM_REWRITE_TAC[DOT_LNEG; REAL_EQ_NEG2; REAL_LE_NEG2]);;

let FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE = prove
 (`!s a:real^N b.
        convex s /\ (!x. x IN s ==> a dot x <= b)
        ==> (s INTER {x | a dot x = b}) face_of s`,
  SIMP_TAC[FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE_STRONG;
           CONVEX_INTER; CONVEX_HYPERPLANE]);;

let FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE = prove
 (`!s a:real^N b.
        convex s /\ (!x. x IN s ==> a dot x >= b)
        ==> (s INTER {x | a dot x = b}) face_of s`,
  SIMP_TAC[FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE_STRONG;
           CONVEX_INTER; CONVEX_HYPERPLANE]);;

let FACE_OF_IMP_SUBSET = prove
 (`!s t. t face_of s ==> t SUBSET s`,
  SIMP_TAC[face_of]);;

let FACE_OF_IMP_CONVEX = prove
 (`!s t. t face_of s ==> convex t`,
  SIMP_TAC[face_of]);;

let FACE_OF_IMP_CLOSED = prove
 (`!s t. convex s /\ closed s /\ t face_of s ==> closed t`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[FACE_OF_STILLCONVEX] THEN
  STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CLOSED_AFFINE; AFFINE_AFFINE_HULL; CLOSED_INTER]);;

let FACE_OF_IMP_COMPACT = prove
 (`!s t. convex s /\ compact s /\ t face_of s ==> compact t`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
  ASM_MESON_TAC[BOUNDED_SUBSET; FACE_OF_IMP_SUBSET; FACE_OF_IMP_CLOSED]);;

let SUBSET_OF_FACE_OF = prove
 (`!s t u:real^N->bool.
      t face_of s /\ u SUBSET s /\
      ~(DISJOINT t (relative_interior u))
      ==> u SUBSET t`,
  REWRITE_TAC[DISJOINT] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `c:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_INTER; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `b:real^N` THEN
  REWRITE_TAC[IN_RELATIVE_INTERIOR_CBALL] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[SUBSET; IN_CBALL; IN_INTER] THEN
  ASM_CASES_TAC `c:real^N = b` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `d:real^N = b + e / norm(b - c) % (b - c)` THEN
  DISCH_THEN(MP_TAC o SPEC `d:real^N`) THEN ANTS_TAC THENL
   [EXPAND_TAC "d" THEN CONJ_TAC THENL
     [REWRITE_TAC[NORM_ARITH `dist(b,b + e) = norm e`] THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_ARITH
       `b + u % (b - c):real^N = (&1 - --u) % b + --u % c`] THEN
      MATCH_MP_TAC(REWRITE_RULE[AFFINE_ALT] AFFINE_AFFINE_HULL) THEN
      ASM_SIMP_TAC[HULL_INC]];
    STRIP_TAC THEN
    SUBGOAL_THEN `(d:real^N) IN t /\ c IN t` (fun th -> MESON_TAC[th]) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [face_of]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `b:real^N` THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    SUBGOAL_THEN `~(b:real^N = d)` ASSUME_TAC THENL
     [EXPAND_TAC "d" THEN
      REWRITE_TAC[VECTOR_ARITH `b:real^N = b + e <=> e = vec 0`] THEN
      ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ;
                   VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ];
      ASM_REWRITE_TAC[segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      EXISTS_TAC `(e / norm(b - c:real^N)) / (&1 + e / norm(b - c))` THEN
      ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ;
                   REAL_ARITH `&0 < x ==> &0 < &1 + x`;
                   REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
      ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> (&1 + e / n) * n = n + e`;
                   NORM_POS_LT; VECTOR_SUB_EQ; REAL_LE_ADDL] THEN
      ASM_SIMP_TAC[NORM_POS_LT; REAL_LT_IMP_LE; VECTOR_SUB_EQ] THEN
      EXPAND_TAC "d" THEN REWRITE_TAC[VECTOR_ARITH
       `b = (&1 - u) % (b + e % (b - c)) + u % c <=>
        (u - e * (&1 - u)) % (b - c) = vec 0`] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
      MATCH_MP_TAC(REAL_FIELD
       `&0 < e ==> e / (&1 + e) - e * (&1 - e / (&1 + e)) = &0`) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ]]]);;

let FACE_OF_EQ = prove
 (`!s t u:real^N->bool.
        t face_of s /\ u face_of s /\
        ~(DISJOINT (relative_interior t) (relative_interior u))
        ==> t = u`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THEN MATCH_MP_TAC SUBSET_OF_FACE_OF THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[FACE_OF_IMP_SUBSET] THENL
   [MP_TAC(ISPEC `u:real^N->bool` RELATIVE_INTERIOR_SUBSET);
    MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET)] THEN
  ASM SET_TAC[]);;

let FACE_OF_DISJOINT_RELATIVE_INTERIOR = prove
 (`!f s:real^N->bool.
        f face_of s /\ ~(f = s) ==> f INTER relative_interior s = {}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->bool`; `s:real^N->bool`]
        SUBSET_OF_FACE_OF) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
  ASM SET_TAC[]);;

let FACE_OF_DISJOINT_INTERIOR = prove
 (`!f s:real^N->bool.
        f face_of s /\ ~(f = s) ==> f INTER interior s = {}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET_RELATIVE_INTERIOR) THEN
  SET_TAC[]);;

let FACE_OF_AFF_DIM_LT = prove
 (`!f s:real^N->bool.
        convex s /\ f face_of s /\ ~(f = s) ==> aff_dim f < aff_dim s`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[INT_LT_LE; FACE_OF_IMP_SUBSET; AFF_DIM_SUBSET] THEN
  REWRITE_TAC[IMP_CONJ; CONTRAPOS_THM] THEN
  ASM_CASES_TAC `f:real^N->bool = {}` THENL
   [CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    ASM_REWRITE_TAC[AFF_DIM_EQ_MINUS1; AFF_DIM_EMPTY];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_EQ THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[FACE_OF_REFL] THEN
    MATCH_MP_TAC(SET_RULE `~(f = {}) /\ f SUBSET s ==> ~DISJOINT f s`) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FACE_OF_IMP_CONVEX) THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN
    MATCH_MP_TAC SUBSET_RELATIVE_INTERIOR THEN
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; AFF_DIM_EQ_AFFINE_HULL; INT_LE_REFL]]);;

let FACE_OF_CONVEX_HULLS = prove
 (`!f s:real^N->bool.
        FINITE s /\ f SUBSET s /\
        DISJOINT (affine hull f) (convex hull (s DIFF f))
        ==> (convex hull f) face_of (convex hull s)`,
  let lemma = prove
   (`!s x y:real^N.
          affine s /\ ~(k = &0) /\ ~(k = &1) /\ x IN s /\ inv(&1 - k) % y IN s
          ==> inv(k) % (x - y) IN s`,
    REWRITE_TAC[AFFINE_ALT] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `inv(k) % (x - y):real^N = (&1 - inv k) % inv(&1 - k) % y + inv(k) % x`
     (fun th -> ASM_SIMP_TAC[th]) THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_ARITH
     `k % (x - y):real^N = a % b % y + k % x <=> (a * b + k) % y = vec 0`] THEN
    DISJ1_TAC THEN MAP_EVERY UNDISCH_TAC [`~(k = &0)`; `~(k = &1)`] THEN
    CONV_TAC REAL_FIELD) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[face_of] THEN
  SUBGOAL_THEN `FINITE(f:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  ASM_SIMP_TAC[HULL_MONO; CONVEX_CONVEX_HULL] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `w:real^N`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(w:real^N) IN affine hull f` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(y:real^N) IN convex hull s`; `(x:real^N) IN convex hull s`] THEN
  REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N->real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `(c:real^N->real) = \x. (&1 - u) * a x + u * b x` THEN
  SUBGOAL_THEN `!x:real^N. x IN s ==> &0 <= c x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "c" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `sum (s DIFF f:real^N->bool) c = &0` THENL
   [SUBGOAL_THEN `!x:real^N. x IN (s DIFF f) ==> c x = &0` MP_TAC THENL
     [MATCH_MP_TAC SUM_POS_EQ_0 THEN ASM_MESON_TAC[FINITE_DIFF; IN_DIFF];
      ALL_TAC] THEN
    EXPAND_TAC "c" THEN
    ASM_SIMP_TAC[IN_DIFF; REAL_LE_MUL; REAL_LT_IMP_LE; REAL_SUB_LT;
     REAL_ARITH `&0 <= x /\ &0 <= y ==> (x + y = &0 <=> x = &0 /\ y = &0)`;
     REAL_ENTIRE; REAL_SUB_0; REAL_LT_IMP_NE] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC `a:real^N->real`; EXISTS_TAC `b:real^N->real`] THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THEN FIRST_X_ASSUM(fun th g ->
      (GEN_REWRITE_TAC RAND_CONV [GSYM th] THEN CONV_TAC SYM_CONV THEN
       (MATCH_MP_TAC SUM_SUPERSET ORELSE MATCH_MP_TAC VSUM_SUPERSET)) g) THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  ABBREV_TAC `k = sum (s DIFF f:real^N->bool) c` THEN
  SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_LE] THEN EXPAND_TAC "k" THEN
    MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[FINITE_DIFF; IN_DIFF];
    ALL_TAC] THEN
  ASM_CASES_TAC `k = &1` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_DISJOINT]) THEN
    MATCH_MP_TAC(TAUT `b ==> ~b ==> c`) THEN
    EXISTS_TAC `w:real^N` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
    EXISTS_TAC `c:real^N->real` THEN
    ASM_SIMP_TAC[IN_DIFF; SUM_DIFF; VSUM_DIFF] THEN
    SUBGOAL_THEN `vsum f (\x:real^N. c x % x) = vec 0` SUBST1_TAC THENL
     [ALL_TAC;
      EXPAND_TAC "c" THEN REWRITE_TAC[VECTOR_ADD_RDISTRIB] THEN
      ASM_SIMP_TAC[VSUM_ADD; GSYM VECTOR_MUL_ASSOC; VSUM_LMUL] THEN
      REWRITE_TAC[VECTOR_SUB_RZERO]] THEN
    SUBGOAL_THEN `sum(s DIFF f) c = sum s c - sum f (c:real^N->real)`
    MP_TAC THENL [ASM_MESON_TAC[SUM_DIFF]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sum s (c:real^N->real) = &1` SUBST1_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[VECTOR_ADD_RDISTRIB] THEN
      ASM_SIMP_TAC[SUM_ADD; GSYM REAL_MUL_ASSOC; SUM_LMUL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&1 = &1 - x <=> x = &0`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:real^N->real`;`f:real^N->bool`] SUM_POS_EQ_0) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ALL_TAC] THEN
    SIMP_TAC[VECTOR_MUL_LZERO; VSUM_0];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_DISJOINT]) THEN
  MATCH_MP_TAC(TAUT `b ==> ~b ==> c`) THEN
  EXISTS_TAC `inv(k) % (w - vsum f (\x:real^N. c x % x))` THEN CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `w = vsum f (\x:real^N. c x % x) +
                      vsum (s DIFF f) (\x:real^N. c x % x)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[VSUM_DIFF; VECTOR_ARITH `a + b - a:real^N = b`] THEN
      EXPAND_TAC "c" THEN REWRITE_TAC[VECTOR_ADD_RDISTRIB] THEN
      ASM_SIMP_TAC[VSUM_ADD; GSYM VECTOR_MUL_ASSOC; VSUM_LMUL];
      REWRITE_TAC[VECTOR_ADD_SUB]] THEN
    ASM_SIMP_TAC[GSYM VSUM_LMUL; FINITE_DIFF] THEN
    REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
    EXISTS_TAC `\x. inv k * (c:real^N->real) x` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[IN_DIFF; REAL_LE_MUL; REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[SUM_LMUL; ETA_AX; REAL_MUL_LINV]] THEN
  MATCH_MP_TAC lemma THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[AFFINE_AFFINE_HULL];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VSUM_LMUL; AFFINE_HULL_FINITE; IN_ELIM_THM] THEN
  EXISTS_TAC `(\x. inv(&1 - k) * c x):real^N->real` THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; SUM_LMUL] THEN
  MATCH_MP_TAC(REAL_FIELD
   `~(k = &1) /\ f = &1 - k ==> inv(&1 - k) * f = &1`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sum(s DIFF f) c = sum s c - sum f (c:real^N->real)`
  MP_TAC THENL [ASM_MESON_TAC[SUM_DIFF]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sum s (c:real^N->real) = &1` SUBST1_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[VECTOR_ADD_RDISTRIB] THEN
    ASM_SIMP_TAC[SUM_ADD; GSYM REAL_MUL_ASSOC; SUM_LMUL];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let FACE_OF_AFFINE_TRIVIAL = prove
 (`!s f:real^N->bool.
        affine s /\ f face_of s ==> f = {} \/ f = s`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `f:real^N->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(b:real^N) IN f` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [face_of]) THEN
  DISCH_THEN(MP_TAC o SPECL [`&2 % a - b:real^N`; `b:real^N`; `a:real^N`] o
             CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `~(a:real^N = b)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[IN_SEGMENT; VECTOR_ARITH `&2 % a - b:real^N = b <=> a = b`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `&2 % a - b:real^N = a + &1 % (a - b)`] THEN
    MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN ASM SET_TAC[];
    EXISTS_TAC `&1 / &2` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    VECTOR_ARITH_TAC]);;

let INTERS_FACES_FINITE_BOUND = prove
 (`!s f:(real^N->bool)->bool.
        convex s /\ (!c. c IN f ==> c face_of s)
        ==> ?f'. FINITE f' /\ f' SUBSET f /\ CARD f' <= dimindex(:N) + 1 /\
                 INTERS f' = INTERS f`,
  SUBGOAL_THEN
   `!s f:(real^N->bool)->bool.
        convex s /\ (!c. c IN f ==> c face_of s /\ ~(c = s))
        ==> ?f'. FINITE f' /\ f' SUBSET f /\ CARD f' <= dimindex(:N) + 1 /\
                 INTERS f' = INTERS f`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `(s:real^N->bool) IN f` THENL
     [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]] THEN
    FIRST_ASSUM(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC o MATCH_MP (SET_RULE
     `s IN f ==> f = {s} \/ ?t. ~(t = s) /\ t IN f`)) THENL
     [EXISTS_TAC `{s:real^N->bool}` THEN
      SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; SUBSET_REFL; CARD_CLAUSES] THEN
      ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^N->bool`; `f DELETE
      (s:real^N->bool)`]) THEN
    ASM_SIMP_TAC[IN_DELETE; SUBSET_DELETE] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f':(real^N->bool)->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `f = (s:real^N->bool) INSERT (f DELETE s)` MP_TAC THENL
     [ASM SET_TAC[];
      DISCH_THEN(fun th -> GEN_REWRITE_TAC (funpow 2 RAND_CONV) [th])] THEN
    REWRITE_TAC[INTERS_INSERT] THEN
    MATCH_MP_TAC(SET_RULE `t SUBSET s ==> t = s INTER t`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_INTERS; IN_DELETE] THEN
    ASM SET_TAC[]] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC
   `!f':(real^N->bool)->bool.
        FINITE f' /\ f' SUBSET f /\ CARD f' <= dimindex(:N) + 1
        ==> ?c. c IN f /\ c INTER (INTERS f') PSUBSET (INTERS f')`
  THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    SIMP_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC[PSUBSET; INTER_SUBSET] THEN ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV
   [RIGHT_IMP_EXISTS_THM]) THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `c:((real^N->bool)->bool)->real^N->bool` THEN DISCH_TAC THEN
  CHOOSE_TAC(prove_recursive_functions_exist num_RECURSION
   `d 0 = {c {} :real^N->bool} /\ !n. d(SUC n) = c(d n) INSERT d n`) THEN
  SUBGOAL_THEN `!n:num. ~(d n:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. n <= dimindex(:N) + 1
        ==> (d n) SUBSET (f:(real^N->bool)->bool) /\
            FINITE(d n) /\ CARD(d n) <= n + 1`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[INSERT_SUBSET; CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
      EMPTY_SUBSET; ARITH_RULE `SUC n <= m + 1 ==> n <= m + 1`] THEN
    REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(d:num->(real^N->bool)->bool) n`) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. n <= dimindex(:N)
        ==> (INTERS(d(SUC n)):real^N->bool) PSUBSET INTERS(d n)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[INTERS_INSERT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(d:num->(real^N->bool)->bool) n`) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`)) THEN
    ASM_SIMP_TAC[ARITH_RULE `n <= N ==> n <= N + 1`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN(K ALL_TAC)) THEN
  SUBGOAL_THEN
   `!n. n <= dimindex(:N) + 1
        ==> aff_dim(INTERS(d n):real^N->bool) < &(dimindex(:N)) - &n`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [DISCH_TAC THEN REWRITE_TAC[INT_SUB_RZERO] THEN
      MATCH_MP_TAC INT_LTE_TRANS THEN
      EXISTS_TAC `aff_dim(s:real^N->bool)` THEN
      REWRITE_TAC[AFF_DIM_LE_UNIV] THEN
      MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FACE_OF_INTERS THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
          SPEC `0`) THEN
        DISCH_THEN(X_CHOOSE_TAC `e:real^N->bool`) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool`) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
        MATCH_MP_TAC(SET_RULE
         `!t. t PSUBSET s /\ u SUBSET t ==> ~(u = s)`) THEN
        EXISTS_TAC `e:real^N->bool` THEN
        FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
        ASM SET_TAC[]];
      DISCH_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN
      MATCH_MP_TAC(INT_ARITH
       `!d':int. d < d' /\ d' < m - n ==> d < m - (n + &1)`) THEN
      EXISTS_TAC `aff_dim(INTERS(d(n:num)):real^N->bool)` THEN
      ASM_SIMP_TAC[ARITH_RULE `SUC n <= k + 1 ==> n <= k + 1`] THEN
      MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
      ASM_SIMP_TAC[ARITH_RULE `SUC n <= m + 1 ==> n <= m`;
                   SET_RULE `s PSUBSET t ==> ~(s = t)`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_INTERS THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_IMP_CONVEX THEN
        EXISTS_TAC `s:real^N->bool` THEN
        ASM_MESON_TAC[SUBSET; ARITH_RULE `SUC n <= m + 1 ==> n <= m + 1`];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`INTERS(d(SUC n)):real^N->bool`;`s:real^N->bool`;
                     `INTERS(d(n:num)):real^N->bool`] FACE_OF_FACE) THEN
      ASM_SIMP_TAC[SET_RULE `s PSUBSET t ==> s SUBSET t`;
                   ARITH_RULE `SUC n <= m + 1 ==> n <= m`] THEN
      MATCH_MP_TAC(TAUT `a /\ b ==> (a ==> (c <=> b)) ==> c`) THEN
      CONJ_TAC THEN MATCH_MP_TAC FACE_OF_INTERS THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SUBSET; ARITH_RULE `SUC n <= m + 1 ==> n <= m + 1`]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `dimindex(:N) + 1`) THEN REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[INT_NOT_LT] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; INT_ARITH `d - (d + &1):int = -- &1`] THEN
  REWRITE_TAC[AFF_DIM_GE]);;

let INTERS_FACES_FINITE_ALTBOUND = prove
 (`!s f:(real^N->bool)->bool.
        (!c. c IN f ==> c face_of s)
        ==> ?f'. FINITE f' /\ f' SUBSET f /\ CARD f' <= dimindex(:N) + 2 /\
                 INTERS f' = INTERS f`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC
   `!f':(real^N->bool)->bool.
        FINITE f' /\ f' SUBSET f /\ CARD f' <= dimindex(:N) + 2
        ==> ?c. c IN f /\ c INTER (INTERS f') PSUBSET (INTERS f')`
  THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    SIMP_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC[PSUBSET; INTER_SUBSET] THEN ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV
   [RIGHT_IMP_EXISTS_THM]) THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `c:((real^N->bool)->bool)->real^N->bool` THEN DISCH_TAC THEN
  CHOOSE_TAC(prove_recursive_functions_exist num_RECURSION
   `d 0 = {c {} :real^N->bool} /\ !n. d(SUC n) = c(d n) INSERT d n`) THEN
  SUBGOAL_THEN `!n:num. ~(d n:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. n <= dimindex(:N) + 2
        ==> (d n) SUBSET (f:(real^N->bool)->bool) /\
            FINITE(d n) /\ CARD(d n) <= n + 1`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[INSERT_SUBSET; CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
      EMPTY_SUBSET; ARITH_RULE `SUC n <= m + 2 ==> n <= m + 2`] THEN
    REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(d:num->(real^N->bool)->bool) n`) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. n <= dimindex(:N) + 1
        ==> (INTERS(d(SUC n)):real^N->bool) PSUBSET INTERS(d n)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[INTERS_INSERT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(d:num->(real^N->bool)->bool) n`) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`)) THEN
    ASM_SIMP_TAC[ARITH_RULE `n <= N + 1 ==> n <= N + 2`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN(K ALL_TAC)) THEN
  SUBGOAL_THEN
   `!n. n <= dimindex(:N) + 2
        ==> aff_dim(INTERS(d n):real^N->bool) <= &(dimindex(:N)) - &n`
  MP_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[INT_SUB_RZERO; AFF_DIM_LE_UNIV] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN
    MATCH_MP_TAC(INT_ARITH
     `!d':int. d < d' /\ d' <= m - n ==> d <= m - (n + &1)`) THEN
    EXISTS_TAC `aff_dim(INTERS(d(n:num)):real^N->bool)` THEN
    ASM_SIMP_TAC[ARITH_RULE `SUC n <= k + 2 ==> n <= k + 2`] THEN
    MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
    ASM_SIMP_TAC[ARITH_RULE `SUC n <= m + 2 ==> n <= m + 1`;
                 SET_RULE `s PSUBSET t ==> ~(s = t)`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_INTERS THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_IMP_CONVEX THEN
      EXISTS_TAC `s:real^N->bool` THEN
      ASM_MESON_TAC[SUBSET; ARITH_RULE `SUC n <= m + 2 ==> n <= m + 2`];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`INTERS(d(SUC n)):real^N->bool`;`s:real^N->bool`;
                   `INTERS(d(n:num)):real^N->bool`] FACE_OF_FACE) THEN
    ASM_SIMP_TAC[SET_RULE `s PSUBSET t ==> s SUBSET t`;
                 ARITH_RULE `SUC n <= m + 2 ==> n <= m + 1`] THEN
    MATCH_MP_TAC(TAUT `a /\ b ==> (a ==> (c <=> b)) ==> c`) THEN
    CONJ_TAC THEN MATCH_MP_TAC FACE_OF_INTERS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET; ARITH_RULE `SUC n <= m + 2 ==> n <= m + 2`];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `dimindex(:N) + 2`) THEN REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[INT_NOT_LE] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; INT_ARITH
    `d - (d + &2):int < i <=> -- &1 <= i`] THEN
  REWRITE_TAC[AFF_DIM_GE]);;

let FACES_OF_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> {t | t face_of (IMAGE f s)} = IMAGE (IMAGE f) {t | t face_of s}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[face_of; SUBSET_IMAGE; SET_RULE
   `{y | (?x. P x /\ y = f x) /\ Q y} = {f x |x| P x /\ Q(f x)}`] THEN
  REWRITE_TAC[SET_RULE `IMAGE f {x | P x} = {f x | P x}`] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  FIRST_ASSUM(fun th ->
   REWRITE_TAC[MATCH_MP CONVEX_LINEAR_IMAGE_EQ th;
               MATCH_MP OPEN_SEGMENT_LINEAR_IMAGE th;
               MATCH_MP (SET_RULE
   `(!x y. f x = f y ==> x = y)  ==> (!s x. f x IN IMAGE f s <=> x IN s)`)
   (CONJUNCT2 th)]));;

(* ------------------------------------------------------------------------- *)
(* Exposed faces (faces that are intersection with supporting hyperplane).   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("exposed_face_of",(12,"right"));;

let exposed_face_of = new_definition
 `t exposed_face_of s <=>
    t face_of s /\
    ?a b. s SUBSET {x | a dot x <= b} /\ t = s INTER {x | a dot x = b}`;;

let EMPTY_EXPOSED_FACE_OF = prove
 (`!s:real^N->bool. {} exposed_face_of s`,
  GEN_TAC THEN REWRITE_TAC[exposed_face_of; EMPTY_FACE_OF] THEN
  MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `&1:real`] THEN
  REWRITE_TAC[DOT_LZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SET_TAC[]);;

let EXPOSED_FACE_OF_REFL_EQ = prove
 (`!s:real^N->bool. s exposed_face_of s <=> convex s`,
  GEN_TAC THEN REWRITE_TAC[exposed_face_of; FACE_OF_REFL_EQ] THEN
  ASM_CASES_TAC `convex(s:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `&0:real`] THEN
  REWRITE_TAC[DOT_LZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SET_TAC[]);;

let EXPOSED_FACE_OF_REFL = prove
 (`!s:real^N->bool. convex s ==> s exposed_face_of s`,
  REWRITE_TAC[EXPOSED_FACE_OF_REFL_EQ]);;

let EXPOSED_FACE_OF = prove
 (`!s t. t exposed_face_of s <=>
             t face_of s /\
             (t = {} \/ t = s \/
              ?a b. ~(a = vec 0) /\
                    s SUBSET {x:real^N | a dot x <= b} /\
                    t = s INTER {x | a dot x = b})`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[EMPTY_EXPOSED_FACE_OF; EMPTY_FACE_OF] THEN
  ASM_CASES_TAC `t:real^N->bool = s` THEN
  ASM_REWRITE_TAC[EXPOSED_FACE_OF_REFL_EQ; FACE_OF_REFL_EQ] THEN
  REWRITE_TAC[exposed_face_of] THEN AP_TERM_TAC THEN
  EQ_TAC THENL [REWRITE_TAC[LEFT_IMP_EXISTS_THM]; MESON_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real`] THEN
  ASM_CASES_TAC `a:real^N = vec 0` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[DOT_LZERO] THEN SET_TAC[]);;

let EXPOSED_FACE_OF_TRANSLATION_EQ = prove
 (`!a f s:real^N->bool.
        (IMAGE (\x. a + x) f) exposed_face_of (IMAGE (\x. a + x) s) <=>
        f exposed_face_of s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[exposed_face_of; FACE_OF_TRANSLATION_EQ] THEN
  MP_TAC(ISPEC `\x:real^N. a + x` QUANTIFY_SURJECTION_THM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MESON_TAC[VECTOR_ARITH `y + (x - y):real^N = x`]; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
    [last(CONJUNCTS th)]) THEN
  REWRITE_TAC[end_itlist CONJ (!invariant_under_translation)] THEN
  REWRITE_TAC[DOT_RADD] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[GSYM REAL_LE_SUB_LADD; GSYM REAL_EQ_SUB_LADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `c:real^N` THEN REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `b - (c:real^N) dot a`;
    EXISTS_TAC `b + (c:real^N) dot a`] THEN
  ASM_REWRITE_TAC[REAL_ARITH `(x + y) - y:real = x`]);;

add_translation_invariants [EXPOSED_FACE_OF_TRANSLATION_EQ];;

let EXPOSED_FACE_OF_LINEAR_IMAGE = prove
 (`!f:real^M->real^N c s.
      linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
      ==> ((IMAGE f c) exposed_face_of (IMAGE f s) <=> c exposed_face_of s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[exposed_face_of] THEN
  BINOP_TAC THENL [ASM_MESON_TAC[FACE_OF_LINEAR_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPEC `f:real^M->real^N` QUANTIFY_SURJECTION_THM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
    [last(CONJUNCTS th)]) THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_SIMP_TAC[ADJOINT_WORKS] THEN
  MP_TAC(end_itlist CONJ
   (mapfilter (ISPEC `f:real^M->real^N`) (!invariant_under_linear))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `adjoint(f:real^M->real^N) a` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `a:real^M` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `adjoint(f:real^M->real^N)`
      LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
    ASM_SIMP_TAC[ADJOINT_SURJECTIVE; ADJOINT_LINEAR] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `g:real^M->real^N` THEN STRIP_TAC THEN
    EXISTS_TAC `(g:real^M->real^N) a` THEN ASM_REWRITE_TAC[]]);;

let EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE = prove
 (`!s a:real^N b.
        convex s /\ (!x. x IN s ==> a dot x <= b)
        ==> (s INTER {x | a dot x = b}) exposed_face_of s`,
  SIMP_TAC[FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE; exposed_face_of] THEN
  SET_TAC[]);;

let EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE = prove
 (`!s a:real^N b.
        convex s /\ (!x. x IN s ==> a dot x >= b)
        ==> (s INTER {x | a dot x = b}) exposed_face_of s`,
  REWRITE_TAC[real_ge] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `--a:real^N`; `--b:real`]
    EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE) THEN
  ASM_REWRITE_TAC[DOT_LNEG; REAL_EQ_NEG2; REAL_LE_NEG2]);;

let EXPOSED_FACE_OF_INTER = prove
 (`!s t u:real^N->bool.
        t exposed_face_of s /\ u exposed_face_of s
        ==> (t INTER u) exposed_face_of s`,
  REPEAT GEN_TAC THEN SIMP_TAC[exposed_face_of; FACE_OF_INTER] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`a':real^N`; `b':real`; `a:real^N`; `b:real`] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`a + a':real^N`; `b + b':real`] THEN
  REWRITE_TAC[SET_RULE
   `(s INTER t1) INTER (s INTER t2) = s INTER u <=>
    !x. x IN s ==> (x IN t1 /\ x IN t2 <=> x IN u)`] THEN
  ASM_SIMP_TAC[DOT_LADD; REAL_LE_ADD2; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`)) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let EXPOSED_FACE_OF_INTERS = prove
 (`!P s:real^N->bool.
        ~(P = {}) /\ (!t. t IN P ==> t exposed_face_of s)
        ==> INTERS P exposed_face_of s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `P:(real^N->bool)->bool`]
    INTERS_FACES_FINITE_ALTBOUND) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[exposed_face_of]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN
  ASM_CASES_TAC `Q:(real^N->bool)->bool = {}` THENL
   [ASM_SIMP_TAC[INTERS_0] THEN
    REWRITE_TAC[SET_RULE `INTERS s = UNIV <=> !t. t IN s ==> t = UNIV`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    SUBGOAL_THEN `!t:real^N->bool. t IN Q ==> t exposed_face_of s` MP_TAC THENL
     [ASM SET_TAC[]; UNDISCH_TAC `FINITE(Q:(real^N->bool)->bool)`] THEN
    SPEC_TAC(`Q:(real^N->bool)->bool`,`Q:(real^N->bool)->bool`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[FORALL_IN_INSERT] THEN
    MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `P:(real^N->bool)->bool`] THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INTERS_INSERT] THEN
    ASM_CASES_TAC `P:(real^N->bool)->bool = {}` THEN
    ASM_SIMP_TAC[INTERS_0; INTER_UNIV; EXPOSED_FACE_OF_INTER]]);;

let EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE = prove
 (`!s a:real^N b.
        convex s /\ (!x. x IN s ==> a dot x <= b)
        ==> (s INTER {x | a dot x = b}) exposed_face_of s`,
  SIMP_TAC[exposed_face_of; FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE] THEN
  SET_TAC[]);;

let EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE = prove
 (`!s a:real^N b.
        convex s /\ (!x. x IN s ==> a dot x >= b)
        ==> (s INTER {x | a dot x = b}) exposed_face_of s`,
  REWRITE_TAC[real_ge] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `--a:real^N`; `--b:real`]
    EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE) THEN
  ASM_REWRITE_TAC[DOT_LNEG; REAL_EQ_NEG2; REAL_LE_NEG2]);;

let EXPOSED_FACE_OF_SUMS = prove
 (`!s t f:real^N->bool.
        convex s /\ convex t /\
        f exposed_face_of {x + y | x IN s /\ y IN t}
        ==> ?k l. k exposed_face_of s /\ l exposed_face_of t /\
                  f = {x + y | x IN k /\ y IN l}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXPOSED_FACE_OF]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `f:real^N->bool = {}` THENL
   [DISCH_TAC THEN REPEAT (EXISTS_TAC `{}:real^N->bool`) THEN
    ASM_REWRITE_TAC[EMPTY_EXPOSED_FACE_OF] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `f = {x + y :real^N | x IN s /\ y IN t}` THENL
   [DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN
    ASM_SIMP_TAC[EXPOSED_FACE_OF_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `z:real`] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM SUBSET_INTER_ABSORPTION]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[EXISTS_IN_GSPEC; IN_INTER] THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a0:real^N`; `b0:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  EXISTS_TAC `s INTER {x:real^N | u dot x = u dot a0}` THEN
  EXISTS_TAC `t INTER {y:real^N | u dot y = u dot b0}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b0:real^N`]) THEN
    ASM_REWRITE_TAC[DOT_RADD] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a0:real^N`; `b:real^N`]) THEN
    ASM_REWRITE_TAC[DOT_RADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_INTER; IMP_CONJ] THENL
   [ALL_TAC; SIMP_TAC[IN_INTER; IN_ELIM_THM; DOT_RADD] THEN MESON_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM; DOT_RADD] THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPECL  [`a:real^N`; `b0:real^N`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL  [`a0:real^N`; `b:real^N`]) THEN
  ASM_REWRITE_TAC[DOT_RADD] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Extreme points of a set, which are its singleton faces.                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("extreme_point_of",(12,"right"));;

let extreme_point_of = new_definition
 `x extreme_point_of s <=>
    x IN s /\ !a b. a IN s /\ b IN s ==> ~(x IN segment(a,b))`;;

let EXTREME_POINT_OF_STILLCONVEX = prove
 (`!s x:real^N.
        convex s ==> (x extreme_point_of s <=> x IN s /\ convex(s DELETE x))`,
  REWRITE_TAC[CONVEX_CONTAINS_SEGMENT; extreme_point_of; open_segment] THEN
  REWRITE_TAC[IN_DIFF; IN_DELETE; IN_INSERT; NOT_IN_EMPTY; SUBSET_DELETE] THEN
  SET_TAC[]);;

let FACE_OF_SING = prove
 (`!x s. {x} face_of s <=> x extreme_point_of s`,
  SIMP_TAC[face_of; extreme_point_of; SING_SUBSET; CONVEX_SING; IN_SING] THEN
  MESON_TAC[SEGMENT_REFL; NOT_IN_EMPTY]);;

let EXTREME_POINT_NOT_IN_RELATIVE_INTERIOR = prove
 (`!s x:real^N.
        x extreme_point_of s /\ ~(s = {x})
        ==> ~(x IN relative_interior s)`,
  REPEAT GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  REWRITE_TAC[GSYM FACE_OF_SING] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  SET_TAC[]);;

let EXTREME_POINT_NOT_IN_INTERIOR = prove
 (`!s x:real^N. x extreme_point_of s ==> ~(x IN interior s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `s = {x:real^N}` THEN
  ASM_SIMP_TAC[EMPTY_INTERIOR_FINITE; FINITE_SING; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
    INTERIOR_SUBSET_RELATIVE_INTERIOR)) THEN
  ASM_SIMP_TAC[EXTREME_POINT_NOT_IN_RELATIVE_INTERIOR]);;

let EXTREME_POINT_OF_FACE = prove
 (`!f s v. f face_of s
           ==> (v extreme_point_of f <=> v extreme_point_of s /\ v IN f)`,
  REWRITE_TAC[GSYM FACE_OF_SING; GSYM SING_SUBSET; FACE_OF_FACE]);;

let EXTREME_POINT_OF_MIDPOINT = prove
 (`!s x:real^N.
        convex s
        ==> (x extreme_point_of s <=>
             x IN s /\
             !a b. a IN s /\ b IN s /\ x = midpoint(a,b) ==> x = a /\ x = b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[extreme_point_of] THEN
  AP_TERM_TAC THEN EQ_TAC THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
    ASM_SIMP_TAC[MIDPOINT_IN_SEGMENT; MIDPOINT_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[IN_SEGMENT] THEN DISCH_THEN(CONJUNCTS_THEN2
    ASSUME_TAC (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `d = min (&1 - u) u` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`x - d / &2 % (b - a):real^N`; `x + d / &2 % (b - a):real^N`]) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH
     `((&1 - u) % a + u % b) - d / &2 % (b - a) =
      (&1 - (u - d / &2)) % a + (u - d / &2) % b`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH
     `((&1 - u) % a + u % b) + d / &2 % (b - a) =
      (&1 - (u + d / &2)) % a + (u + d / &2) % b`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[VECTOR_ARITH `x:real^N = x - d <=> d = vec 0`;
                VECTOR_ARITH `x:real^N = x + d <=> d = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN ASM_REAL_ARITH_TAC]);;

let EXTREME_POINT_OF_CONVEX_HULL = prove
 (`!x:real^N s. x extreme_point_of (convex hull s) ==> x IN s`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[EXTREME_POINT_OF_STILLCONVEX; CONVEX_CONVEX_HULL] THEN
  MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `s:real^N->bool`;
                 `(convex hull s) DELETE (x:real^N)`] HULL_MINIMAL) THEN
  MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `s:real^N->bool`]
        HULL_SUBSET) THEN
  ASM SET_TAC[]);;

let EXTREME_POINTS_OF_CONVEX_HULL = prove
 (`!s. {x | x extreme_point_of (convex hull s)} SUBSET s`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM; EXTREME_POINT_OF_CONVEX_HULL]);;

let EXTREME_POINT_OF_EMPTY = prove
 (`!x. ~(x extreme_point_of {})`,
  REWRITE_TAC[extreme_point_of; NOT_IN_EMPTY]);;

let EXTREME_POINT_OF_SING = prove
 (`!a x. x extreme_point_of {a} <=> x = a`,
  REWRITE_TAC[extreme_point_of; IN_SING] THEN
  MESON_TAC[SEGMENT_REFL; NOT_IN_EMPTY]);;

let EXTREME_POINT_OF_TRANSLATION_EQ = prove
 (`!a x s. (a + x) extreme_point_of (IMAGE (\x. a + x) s) <=>
           x extreme_point_of s`,
  REWRITE_TAC[extreme_point_of] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [EXTREME_POINT_OF_TRANSLATION_EQ];;

let EXTREME_POINT_OF_LINEAR_IMAGE = prove
 (`!f:real^M->real^N.
      linear f /\ (!x y. f x = f y ==> x = y)
      ==> ((f x) extreme_point_of (IMAGE f s) <=> x extreme_point_of s)`,
  REWRITE_TAC[GSYM FACE_OF_SING] THEN GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [EXTREME_POINT_OF_LINEAR_IMAGE];;

let EXTREME_POINTS_OF_TRANSLATION = prove
 (`!a x s. {x | x extreme_point_of (IMAGE (\x. a + x) s)} =
           IMAGE (\x. a + x) {x | x extreme_point_of s}`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[VECTOR_ARITH `a + x:real^N = y <=> x = y - a`; EXISTS_REFL] THEN
  REWRITE_TAC[IN_ELIM_THM; EXTREME_POINT_OF_TRANSLATION_EQ]);;

let EXTREME_POINT_OF_INTER = prove
 (`!x s t. x extreme_point_of s /\ x extreme_point_of t
           ==> x extreme_point_of (s INTER t)`,
  REWRITE_TAC[extreme_point_of; IN_INTER] THEN MESON_TAC[]);;

let EXTREME_POINTS_OF_LINEAR_IMAGE = prove
 (`!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> {y | y extreme_point_of (IMAGE f s)} =
            IMAGE f {x | x extreme_point_of s}`,

  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_SEGMENT_LINEAR_IMAGE) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC; SUBSET;
              extreme_point_of; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE; IN_ELIM_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  ASM SET_TAC[]);;

let EXTREME_POINT_OF_INTER_SUPPORTING_HYPERPLANE_LE = prove
 (`!s a b c. (!x. x IN s ==> a dot x <= b) /\
             s INTER {x | a dot x = b} = {c}
             ==> c extreme_point_of s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE_STRONG THEN
  ASM_REWRITE_TAC[CONVEX_SING]);;

let EXTREME_POINT_OF_INTER_SUPPORTING_HYPERPLANE_GE = prove
 (`!s a b c. (!x. x IN s ==> a dot x >= b) /\
             s INTER {x | a dot x = b} = {c}
             ==> c extreme_point_of s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE_STRONG THEN
  ASM_REWRITE_TAC[CONVEX_SING]);;

let EXPOSED_POINT_OF_INTER_SUPPORTING_HYPERPLANE_LE = prove
 (`!s a b c:real^N.
        (!x. x IN s ==> a dot x <= b) /\
        s INTER {x | a dot x = b} = {c}
        ==> {c} exposed_face_of s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[exposed_face_of] THEN CONJ_TAC THENL
   [REWRITE_TAC[FACE_OF_SING] THEN
    MATCH_MP_TAC EXTREME_POINT_OF_INTER_SUPPORTING_HYPERPLANE_LE;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real`] THEN ASM SET_TAC[]);;

let EXPOSED_POINT_OF_INTER_SUPPORTING_HYPERPLANE_GE = prove
 (`!s a b c:real^N.
        (!x. x IN s ==> a dot x >= b) /\
        s INTER {x | a dot x = b} = {c}
        ==> {c} exposed_face_of s`,
  REWRITE_TAC[real_ge] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `--a:real^N`; `--b:real`; `c:real^N`]
    EXPOSED_POINT_OF_INTER_SUPPORTING_HYPERPLANE_LE) THEN
  ASM_REWRITE_TAC[DOT_LNEG; REAL_EQ_NEG2; REAL_LE_NEG2]);;

let EXPOSED_POINT_OF_FURTHEST_POINT = prove
 (`!s a b:real^N.
        b IN s /\ (!x. x IN s ==> dist(a,x) <= dist(a,b))
        ==> {b} exposed_face_of s`,
  REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC `a:real^N` THEN
  REWRITE_TAC[DIST_0; NORM_LE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EXPOSED_POINT_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
  MAP_EVERY EXISTS_TAC [`b:real^N`; `(b:real^N) dot b`] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    ASM_REWRITE_TAC[IN_INTER; SING_SUBSET; IN_ELIM_THM] THEN
    REWRITE_TAC[SUBSET; IN_SING; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[VECTOR_EQ] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_ANTISYM] THEN
    UNDISCH_TAC `(b:real^N) dot x = b dot b`] THEN
  MP_TAC(ISPEC `b - x:real^N` DOT_POS_LE) THEN
  REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_SYM] THEN REAL_ARITH_TAC);;

let COLLINEAR_EXTREME_POINTS = prove
 (`!s. collinear s
       ==> FINITE {x:real^N | x extreme_point_of s} /\
           CARD {x | x extreme_point_of s} <= 2`,
  REWRITE_TAC[GSYM NOT_LT; TAUT `a /\ ~b <=> ~(a ==> b)`] THEN
  REWRITE_TAC[ARITH_RULE `2 < n <=> 3 <= n`] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CHOOSE_SUBSET_STRONG) THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`t:real^N->bool`; `a:real^N`; `b:real^N`; `c:real^N`] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `(a:real^N) extreme_point_of s /\
    b extreme_point_of s /\ c extreme_point_of s`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN s /\ b IN s /\ c IN s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
  SUBGOAL_THEN `collinear {a:real^N,b,c}` MP_TAC THENL
   [MATCH_MP_TAC COLLINEAR_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM SET_TAC[];
    REWRITE_TAC[COLLINEAR_BETWEEN_CASES; BETWEEN_IN_SEGMENT] THEN
    ASM_SIMP_TAC[SEGMENT_CLOSED_OPEN; IN_INSERT; NOT_IN_EMPTY; IN_UNION] THEN
    ASM_MESON_TAC[extreme_point_of]]);;

(* ------------------------------------------------------------------------- *)
(* Facets.                                                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("facet_of",(12, "right"));;

let facet_of = new_definition
 `f facet_of s <=> f face_of s /\ ~(f = {}) /\ aff_dim f = aff_dim s - &1`;;

let FACET_OF_EMPTY = prove
 (`!s. ~(s facet_of {})`,
  REWRITE_TAC[facet_of; FACE_OF_EMPTY] THEN CONV_TAC TAUT);;

let FACET_OF_REFL = prove
 (`!s. ~(s facet_of s)`,
  REWRITE_TAC[facet_of; INT_ARITH `~(x:int = x - &1)`]);;

let FACET_OF_IMP_FACE_OF = prove
 (`!f s. f facet_of s ==> f face_of s`,
  SIMP_TAC[facet_of]);;

let FACET_OF_IMP_SUBSET = prove
 (`!f s. f facet_of s ==> f SUBSET s`,
  SIMP_TAC[FACET_OF_IMP_FACE_OF; FACE_OF_IMP_SUBSET]);;

let FACET_OF_TRANSLATION_EQ = prove
 (`!a f s.
        (IMAGE (\x. a + x) f) facet_of (IMAGE (\x. a + x) s) <=> f facet_of s`,
  REWRITE_TAC[facet_of] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [FACET_OF_TRANSLATION_EQ];;

let FACET_OF_LINEAR_IMAGE = prove
 (`!f:real^M->real^N c s.
      linear f /\ (!x y. f x = f y ==> x = y)
      ==> ((IMAGE f c) facet_of (IMAGE f s) <=> c facet_of s)`,
  REWRITE_TAC[facet_of] THEN GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [FACET_OF_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Edges, i.e. faces of affine dimension 1.                                  *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("edge_of",(12, "right"));;

let edge_of = new_definition
 `e edge_of s <=> e face_of s /\ aff_dim e = &1`;;

let EDGE_OF_TRANSLATION_EQ = prove
 (`!a f s.
        (IMAGE (\x. a + x) f) edge_of (IMAGE (\x. a + x) s) <=> f edge_of s`,
  REWRITE_TAC[edge_of] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [EDGE_OF_TRANSLATION_EQ];;

let EDGE_OF_LINEAR_IMAGE = prove
 (`!f:real^M->real^N c s.
      linear f /\ (!x y. f x = f y ==> x = y)
      ==> ((IMAGE f c) edge_of (IMAGE f s) <=> c edge_of s)`,
  REWRITE_TAC[edge_of] THEN GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [EDGE_OF_LINEAR_IMAGE];;

let EDGE_OF_IMP_SUBSET = prove
 (`!s t. s edge_of t ==> s SUBSET t`,
  SIMP_TAC[edge_of; face_of]);;

(* ------------------------------------------------------------------------- *)
(* Existence of extreme points.                                              *)
(* ------------------------------------------------------------------------- *)

let DIFFERENT_NORM_3_COLLINEAR_POINTS = prove
 (`!a b x:real^N.
     ~(x IN segment(a,b) /\ norm(a) = norm(b) /\ norm(x) = norm(b))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = b` THEN
  ASM_SIMP_TAC[SEGMENT_REFL; NOT_IN_EMPTY; OPEN_SEGMENT_ALT] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) MP_TAC) THEN
  ASM_REWRITE_TAC[NORM_EQ] THEN REWRITE_TAC[VECTOR_ARITH
   `(x + y) dot (x + y) = x dot x + &2 * x dot y + y dot y`] THEN
  REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC) THEN
  UNDISCH_TAC `~(a:real^N = b)` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM VECTOR_SUB_EQ] THEN
  REWRITE_TAC[GSYM DOT_EQ_0; VECTOR_ARITH
   `(a - b) dot (a - b) = a dot a + b dot b - &2 * a dot b`] THEN
  ASM_REWRITE_TAC[REAL_RING `a + a - &2 * ab = &0 <=> ab = a`] THEN
  SIMP_TAC[REAL_RING
   `(&1 - u) * (&1 - u) * a + &2 * (&1 - u) * u * x + u * u * a = a <=>
    x = a \/ u = &0 \/ u = &1`] THEN
  ASM_REAL_ARITH_TAC);;

let EXTREME_POINT_EXISTS_CONVEX = prove
 (`!s:real^N->bool.
        compact s /\ convex s /\ ~(s = {}) ==> ?x. x extreme_point_of s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `vec 0:real^N`] DISTANCE_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[DIST_0; extreme_point_of] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `x:real^N`]
     DIFFERENT_NORM_3_COLLINEAR_POINTS) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= x /\ b <= x /\ (a < x ==> x < x) /\ (b < x ==> x < x)
    ==> a = b /\ x = b`) THEN
  ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `(x:real^N) IN segment(a,b)` THEN
  ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; NOT_IN_EMPTY] THEN
  ASM_SIMP_TAC[OPEN_SEGMENT_ALT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  CONJ_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  MATCH_MP_TAC NORM_TRIANGLE_LT THEN REWRITE_TAC[NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH
   `&0 < u /\ u < &1 ==> abs u = u /\ abs(&1 - u) = &1 - u`] THEN
  SUBST1_TAC(REAL_RING `norm(x:real^N) = (&1 - u) * norm x + u * norm x`) THENL
   [MATCH_MP_TAC REAL_LTE_ADD2; MATCH_MP_TAC REAL_LET_ADD2] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_LMUL_EQ; REAL_SUB_LT]);;

(* ------------------------------------------------------------------------- *)
(* Krein-Milman, the weaker form as in more general spaces first.            *)
(* ------------------------------------------------------------------------- *)

let KREIN_MILMAN = prove
 (`!s:real^N->bool.
        convex s /\ compact s
        ==> s = closure(convex hull {x | x extreme_point_of s})`,
  GEN_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[extreme_point_of; NOT_IN_EMPTY; EMPTY_GSPEC] THEN
    REWRITE_TAC[CONVEX_HULL_EMPTY; CLOSURE_EMPTY];
    ALL_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_SIMP_TAC[SUBSET; IN_ELIM_THM; extreme_point_of]] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`closure(convex hull {x:real^N | x extreme_point_of s})`;
                 `u:real^N`] SEPARATING_HYPERPLANE_CLOSED_POINT) THEN
  ASM_SIMP_TAC[CONVEX_CLOSURE; CLOSED_CLOSURE; CONVEX_CONVEX_HULL] THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. a dot x`; `s:real^N->bool`]
    CONTINUOUS_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_LIFT_DOT] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `t = {x:real^N | x IN s /\ a dot x = a dot m}` THEN
  SUBGOAL_THEN `?x:real^N. x extreme_point_of t` (X_CHOOSE_TAC `v:real^N`)
  THENL
   [MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER {x | P x}`] THEN
    ASM_SIMP_TAC[CONVEX_INTER; CONVEX_HYPERPLANE; COMPACT_INTER_CLOSED;
                 CLOSED_HYPERPLANE] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) extreme_point_of s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FACE_OF_SING] THEN MATCH_MP_TAC FACE_OF_TRANS THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_SIMP_TAC[FACE_OF_SING] THEN
    EXPAND_TAC "t" THEN
    REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER {x | P x}`] THEN
    MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE THEN
    ASM_SIMP_TAC[real_ge];
    SUBGOAL_THEN `(a:real^N) dot v > b` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
      MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    REWRITE_TAC[real_gt; REAL_NOT_LT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(a:real^N) dot u` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(a:real^N) dot m` THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `(v:real^N) extreme_point_of t` THEN EXPAND_TAC "t" THEN
    SIMP_TAC[extreme_point_of; IN_ELIM_THM; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Now the sharper form.                                                     *)
(* ------------------------------------------------------------------------- *)

let KREIN_MILMAN_MINKOWSKI = prove
 (`!s:real^N->bool.
        convex s /\ compact s
        ==> s = convex hull {x | x extreme_point_of s}`,
  SUBGOAL_THEN
   `!s:real^N->bool.
        convex s /\ compact s /\ (vec 0) IN s
        ==> (vec 0) IN convex hull {x | x extreme_point_of s}`
  ASSUME_TAC THENL
   [GEN_TAC THEN WF_INDUCT_TAC `dim(s:real^N->bool)` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(vec 0:real^N) IN relative_interior s` THENL
     [MP_TAC(ISPEC `s:real^N->bool` KREIN_MILMAN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `(vec 0:real^N) IN relative_interior s` THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
       (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
      SIMP_TAC[CONVEX_RELATIVE_INTERIOR_CLOSURE; CONVEX_CONVEX_HULL] THEN
      MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(relative_interior(s:real^N->bool) = {})` ASSUME_TAC THENL
     [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `vec 0:real^N`]
          SUPPORTING_HYPERPLANE_RELATIVE_BOUNDARY) THEN
    ASM_REWRITE_TAC[DOT_RZERO] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`; `&0`]
      FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE) THEN
    ASM_REWRITE_TAC[real_ge] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(vec 0:real^N) IN convex hull
          {x | x extreme_point_of (s INTER {x | a dot x = &0})}`
    MP_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s ==> x IN t`) THEN
      MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[SUBSET] THEN
      GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM; GSYM FACE_OF_SING] THEN
      ASM_MESON_TAC[FACE_OF_TRANS]] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP]) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[CONVEX_INTER; CONVEX_HYPERPLANE; COMPACT_INTER_CLOSED;
                 CLOSED_HYPERPLANE; IN_INTER; IN_ELIM_THM; DOT_RZERO] THEN
    REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`s INTER {x:real^N | a dot x = &0}`; `s:real^N->bool`]
          DIM_EQ_SPAN) THEN
    ASM_REWRITE_TAC[INTER_SUBSET; EXTENSION; NOT_FORALL_THM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `b /\ ~a ==> ~(a <=> b)`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET; SPAN_INC; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!x:real^N. x IN span (s INTER {x | a dot x = &0}) ==> a dot x = &0`
     (fun th -> ASM_MESON_TAC[th; REAL_LT_REFL]) THEN
    MATCH_MP_TAC SPAN_INDUCT THEN SIMP_TAC[IN_INTER; IN_ELIM_THM] THEN
    REWRITE_TAC[subspace; DOT_RZERO; DOT_RADD; DOT_RMUL; IN_ELIM_THM] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (\x:real^N. --a + x) s`) THEN
    ASM_SIMP_TAC[CONVEX_TRANSLATION_EQ; COMPACT_TRANSLATION_EQ] THEN
    REWRITE_TAC[IN_IMAGE; VECTOR_ARITH `vec 0:real^N = --a + x <=> x = a`] THEN
    ASM_REWRITE_TAC[UNWIND_THM2] THEN
    REWRITE_TAC[EXTREME_POINTS_OF_TRANSLATION; CONVEX_HULL_TRANSLATION] THEN
    REWRITE_TAC[IN_IMAGE; VECTOR_ARITH `vec 0:real^N = --a + x <=> x = a`] THEN
    REWRITE_TAC[UNWIND_THM2];
    MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_SIMP_TAC[SUBSET; extreme_point_of; IN_ELIM_THM]]);;

(* ------------------------------------------------------------------------- *)
(* Applying it to convex hulls of explicitly indicated finite sets.          *)
(* ------------------------------------------------------------------------- *)

let KREIN_MILMAN_POLYTOPE = prove
 (`!s. FINITE s
       ==> convex hull s =
           convex hull {x | x extreme_point_of (convex hull s)}`,
  SIMP_TAC[KREIN_MILMAN_MINKOWSKI; CONVEX_CONVEX_HULL;
           COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT]);;

let EXTREME_POINTS_OF_CONVEX_HULL_EQ = prove
 (`!s:real^N->bool.
        compact s /\
        (!t. t PSUBSET s ==> ~(convex hull t = convex hull s))
        ==> {x | x extreme_point_of (convex hull s)} = s`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC
   `{x:real^N | x extreme_point_of (convex hull s)}`) THEN
  MATCH_MP_TAC(SET_RULE
   `P /\ t SUBSET s ==> (t PSUBSET s ==> ~P) ==> t = s`) THEN
  REWRITE_TAC[EXTREME_POINTS_OF_CONVEX_HULL] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
  ASM_SIMP_TAC[CONVEX_CONVEX_HULL; COMPACT_CONVEX_HULL]);;

let EXTREME_POINT_OF_CONVEX_HULL_EQ = prove
 (`!s x:real^N.
        compact s /\
        (!t. t PSUBSET s ==> ~(convex hull t = convex hull s))
        ==> (x extreme_point_of (convex hull s) <=> x IN s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP EXTREME_POINTS_OF_CONVEX_HULL_EQ) THEN
  SET_TAC[]);;

let EXTREME_POINT_OF_CONVEX_HULL_CONVEX_INDEPENDENT = prove
 (`!s x:real^N.
        compact s /\
        (!a. a IN s ==> ~(a IN convex hull (s DELETE a)))
        ==> (x extreme_point_of (convex hull s) <=> x IN s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL_EQ THEN
  ASM_REWRITE_TAC[PSUBSET_MEMBER] THEN X_GEN_TAC `t:real^N->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `a:real^N`)) THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s SUBSET convex hull (s DELETE (a:real^N))` MP_TAC THENL
   [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull t:real^N->bool` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[HULL_SUBSET];
    MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]]);;

let EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT = prove
 (`!s x. ~affine_dependent s
         ==> (x extreme_point_of (convex hull s) <=> x IN s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL_CONVEX_INDEPENDENT THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE; FINITE_IMP_COMPACT] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [affine_dependent]) THEN
  MESON_TAC[SUBSET; CONVEX_HULL_SUBSET_AFFINE_HULL]);;

let EXTREME_POINT_OF_CONVEX_HULL_2 = prove
 (`!a b x. x extreme_point_of (convex hull {a,b}) <=> x = a \/ x = b`,
  REWRITE_TAC[SET_RULE `x = a \/ x = b <=> x IN {a,b}`] THEN
  SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
           AFFINE_INDEPENDENT_2]);;

let EXTREME_POINT_OF_SEGMENT = prove
 (`!a b x:real^N. x extreme_point_of segment[a,b] <=> x = a \/ x = b`,
  REWRITE_TAC[SEGMENT_CONVEX_HULL; EXTREME_POINT_OF_CONVEX_HULL_2]);;

let FACE_OF_CONVEX_HULL_SUBSET = prove
 (`!s t:real^N->bool.
        compact s /\ t face_of (convex hull s)
        ==> ?s'. s' SUBSET s /\ t = convex hull s'`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `{x:real^N | x extreme_point_of t}` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL THEN
    ASM_MESON_TAC[FACE_OF_SING; FACE_OF_TRANS];
    MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
    ASM_MESON_TAC[FACE_OF_IMP_CONVEX; FACE_OF_IMP_COMPACT;
                  COMPACT_CONVEX_HULL; CONVEX_CONVEX_HULL]]);;

let FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT = prove
 (`!s t:real^N->bool.
        ~affine_dependent s
        ==> (t face_of (convex hull s) <=>
             ?c. c SUBSET s /\ t = convex hull c)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE; FINITE_IMP_COMPACT;
                  FACE_OF_CONVEX_HULL_SUBSET];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FACE_OF_CONVEX_HULLS THEN
    ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
    MATCH_MP_TAC(SET_RULE `
     !t. u SUBSET t /\ DISJOINT s t ==> DISJOINT s u`) THEN
    EXISTS_TAC `affine hull (s DIFF c:real^N->bool)` THEN
    REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
    MATCH_MP_TAC DISJOINT_AFFINE_HULL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM SET_TAC[]]);;

let FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT = prove
 (`!s t:real^N->bool.
        ~affine_dependent s
        ==> (t facet_of (convex hull s) <=>
             ~(t = {}) /\ ?u. u IN s /\ t = convex hull (s DELETE u))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[facet_of; FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
    UNDISCH_TAC
     `aff_dim(convex hull c:real^N->bool) = aff_dim(s:real^N->bool) - &1` THEN
    SUBGOAL_THEN `~affine_dependent(c:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET];
      ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT; AFF_DIM_CONVEX_HULL]] THEN
    REWRITE_TAC[INT_ARITH `x - &1:int = y - &1 - &1 <=> y = x + &1`] THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s DIFF c:real^N->bool) HAS_SIZE 1` MP_TAC THENL
     [ASM_SIMP_TAC[HAS_SIZE; FINITE_DIFF; CARD_DIFF;
                   AFFINE_INDEPENDENT_IMP_FINITE] THEN ARITH_TAC;
      CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N` THEN
      DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
       `s DIFF t = {a} ==> t SUBSET s ==> s = a INSERT t`)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `CARD((u:real^N) INSERT c) = CARD c + 1` THEN
      ASM_SIMP_TAC[CARD_CLAUSES; AFFINE_INDEPENDENT_IMP_FINITE] THEN
      COND_CASES_TAC THENL [ARITH_TAC; DISCH_THEN(K ALL_TAC)] THEN
      CONJ_TAC THENL [ALL_TAC; AP_TERM_TAC] THEN ASM SET_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    CONJ_TAC THENL [MESON_TAC[DELETE_SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL] THEN
    SUBGOAL_THEN `~affine_dependent(s DELETE (u:real^N))` ASSUME_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET; DELETE_SUBSET];
      ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT]] THEN
    REWRITE_TAC[INT_ARITH `x - &1:int = y - &1 - &1 <=> y = x + &1`] THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[CARD_DELETE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    MATCH_MP_TAC(ARITH_RULE `~(s = 0) ==> s = s - 1 + 1`) THEN
    ASM_SIMP_TAC[CARD_EQ_0; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    ASM SET_TAC[]]);;

let FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT_ALT = prove
 (`!s t:real^N->bool.
        ~affine_dependent s
        ==> (t facet_of (convex hull s) <=>
             2 <= CARD s /\ ?u. u IN s /\ t = convex hull (s DELETE u))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `u:real^N` THEN
  ASM_CASES_TAC `t = convex hull (s DELETE (u:real^N))` THEN
  ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN
  ASM_CASES_TAC `(u:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `CARD s = 1 + CARD(s DELETE (u:real^N))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[CARD_DELETE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    MATCH_MP_TAC(ARITH_RULE `~(s = 0) ==> s = 1 + s - 1`) THEN
    ASM_SIMP_TAC[CARD_EQ_0; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    ASM SET_TAC[];
    REWRITE_TAC[ARITH_RULE `2 <= 1 + x <=> ~(x = 0)`] THEN
    ASM_SIMP_TAC[CARD_EQ_0; AFFINE_INDEPENDENT_IMP_FINITE; FINITE_DELETE]]);;

let SEGMENT_FACE_OF = prove
 (`!s a b:real^N.
    segment[a,b] face_of s ==> a extreme_point_of s /\ b extreme_point_of s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
  MATCH_MP_TAC FACE_OF_TRANS THEN EXISTS_TAC `segment[a:real^N,b]` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]);;

let SEGMENT_EDGE_OF = prove
 (`!s a b:real^N.
        segment[a,b] edge_of s
        ==> ~(a = b) /\ a extreme_point_of s /\ b extreme_point_of s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[edge_of; SEGMENT_FACE_OF]] THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  SIMP_TAC[SEGMENT_REFL; edge_of; AFF_DIM_SING] THEN INT_ARITH_TAC);;

let COMPACT_CONVEX_COLLINEAR_SEGMENT = prove
 (`!s:real^N->bool.
        ~(s = {}) /\ compact s /\ convex s /\ collinear s
        ==> ?a b. s = segment[a,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` KREIN_MILMAN_MINKOWSKI) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COLLINEAR_EXTREME_POINTS) THEN
  REWRITE_TAC[ARITH_RULE `n <= 2 <=> n = 0 \/ n = 1 \/ n = 2`] THEN
  REWRITE_TAC[LEFT_OR_DISTRIB; GSYM HAS_SIZE] THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; SEGMENT_CONVEX_HULL] THEN
  DISCH_THEN SUBST1_TAC THEN MESON_TAC[SET_RULE `{a} = {a,a}`]);;

(* ------------------------------------------------------------------------- *)
(* Polytopes.                                                                *)
(* ------------------------------------------------------------------------- *)

let polytope = new_definition
 `polytope s <=> ?v. FINITE v /\ s = convex hull v`;;

let POLYTOPE_TRANSLATION_EQ = prove
 (`!a s. polytope (IMAGE (\x:real^N. a + x) s) <=> polytope s`,
  REWRITE_TAC[polytope] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [POLYTOPE_TRANSLATION_EQ];;

let POLYTOPE_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> (polytope (IMAGE f s) <=> polytope s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[polytope] THEN
  MP_TAC(ISPEC `f:real^M->real^N` QUANTIFY_SURJECTION_THM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)[th]) THEN
  MP_TAC(end_itlist CONJ
   (mapfilter (ISPEC `f:real^M->real^N`) (!invariant_under_linear))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let FACE_OF_POLYTOPE_POLYTOPE = prove
 (`!f s:real^N->bool. polytope s /\ f face_of s ==> polytope f`,
  REWRITE_TAC[polytope] THEN
  MESON_TAC[FINITE_SUBSET; FACE_OF_CONVEX_HULL_SUBSET; FINITE_IMP_COMPACT]);;

let FINITE_POLYTOPE_FACES = prove
 (`!s:real^N->bool. polytope s ==> FINITE {f | f face_of s}`,
  GEN_TAC THEN REWRITE_TAC[polytope; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `v:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE ((hull) convex) {t:real^N->bool | t SUBSET v}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET; FINITE_IMAGE] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_IMAGE; IN_ELIM_THM] THEN
  ASM_MESON_TAC[FACE_OF_CONVEX_HULL_SUBSET; FINITE_IMP_COMPACT]);;

let POLYTOPE_SCALING = prove
 (`!c s:real^N->bool. polytope s ==> polytope (IMAGE (\x. c % x) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polytope] THEN DISCH_THEN
   (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\x:real^N. c % x) u` THEN
  ASM_SIMP_TAC[CONVEX_HULL_SCALING; FINITE_IMAGE]);;

let POLYTOPE_SCALING_EQ = prove
 (`!c s:real^N->bool.
     ~(c = &0) ==> (polytope (IMAGE (\x. c % x) s) <=> polytope s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[POLYTOPE_SCALING] THEN
  DISCH_THEN(MP_TAC o SPEC `inv c` o MATCH_MP POLYTOPE_SCALING) THEN
  ASM_SIMP_TAC[GSYM IMAGE_o; o_DEF; VECTOR_MUL_ASSOC;
               REAL_MUL_LINV; VECTOR_MUL_LID; IMAGE_ID]);;

let POLYTOPE_SUMS = prove
 (`!s t:real^N->bool.
        polytope s /\ polytope t ==> polytope {x + y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polytope] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `{x + y:real^N | x IN u /\ y IN v}` THEN
  ASM_SIMP_TAC[FINITE_PRODUCT_DEPENDENT] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
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
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]];
    MATCH_MP_TAC HULL_MINIMAL THEN
    SIMP_TAC[CONVEX_SUMS; CONVEX_CONVEX_HULL] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[HULL_INC]]);;

let POLYTOPE_IMP_COMPACT = prove
 (`!s. polytope s ==> compact s`,
  SIMP_TAC[polytope; LEFT_IMP_EXISTS_THM; COMPACT_CONVEX_HULL;
           FINITE_IMP_COMPACT; FINITE_INSERT; FINITE_EMPTY]);;

let POLYTOPE_IMP_CONVEX = prove
 (`!s. polytope s ==> convex s`,
  SIMP_TAC[polytope; LEFT_IMP_EXISTS_THM; CONVEX_CONVEX_HULL]);;

let POLYTOPE_IMP_CLOSED = prove
 (`!s. polytope s ==> closed s`,
  SIMP_TAC[POLYTOPE_IMP_COMPACT; COMPACT_IMP_CLOSED]);;

let POLYTOPE_IMP_BOUNDED = prove
 (`!s. polytope s ==> bounded s`,
  SIMP_TAC[POLYTOPE_IMP_COMPACT; COMPACT_IMP_BOUNDED]);;

let POLYTOPE_INTERVAL = prove
 (`!a b. polytope(interval[a,b])`,
  REWRITE_TAC[polytope] THEN MESON_TAC[CLOSED_INTERVAL_AS_CONVEX_HULL]);;

let POLYTOPE_SING = prove
 (`!a. polytope {a}`,
  MESON_TAC[POLYTOPE_INTERVAL; INTERVAL_SING]);;

(* ------------------------------------------------------------------------- *)
(* Polyhedra.                                                                *)
(* ------------------------------------------------------------------------- *)

let polyhedron = new_definition
 `polyhedron s <=>
        ?f. FINITE f /\
            s = INTERS f /\
            (!h. h IN f ==> ?a b. ~(a = vec 0) /\ h = {x | a dot x <= b})`;;

let POLYHEDRON_INTER = prove
 (`!s t:real^N->bool.
        polyhedron s /\ polyhedron t ==> polyhedron (s INTER t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polyhedron] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `f:(real^N->bool)->bool`)
   (X_CHOOSE_TAC `g:(real^N->bool)->bool`)) THEN
  EXISTS_TAC `f UNION g:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[SET_RULE `INTERS(f UNION g) = INTERS f INTER INTERS g`] THEN
  REWRITE_TAC[FINITE_UNION; IN_UNION] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

let POLYHEDRON_UNIV = prove
 (`polyhedron(:real^N)`,
  REWRITE_TAC[polyhedron] THEN EXISTS_TAC `{}:(real^N->bool)->bool` THEN
  REWRITE_TAC[INTERS_0; NOT_IN_EMPTY; FINITE_RULES]);;

let POLYHEDRON_INTERS = prove
 (`!f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> polyhedron s) ==> polyhedron(INTERS f)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; INTERS_0; POLYHEDRON_UNIV] THEN
  ASM_SIMP_TAC[INTERS_INSERT; FORALL_IN_INSERT; POLYHEDRON_INTER]);;

let POLYHEDRON_EMPTY = prove
 (`polyhedron({}:real^N->bool)`,
  REWRITE_TAC[polyhedron] THEN
  EXISTS_TAC `{{x:real^N | basis 1 dot x <= -- &1},
               {x | --(basis 1) dot x <= -- &1}}` THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; INTERS_2; FORALL_IN_INSERT] THEN
  REWRITE_TAC[NOT_IN_EMPTY; INTER; IN_ELIM_THM; DOT_LNEG] THEN
  REWRITE_TAC[REAL_ARITH `~(a <= -- &1 /\ --a <= -- &1)`; EMPTY_GSPEC] THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`basis 1:real^N`; `-- &1`];
    MAP_EVERY EXISTS_TAC [`--(basis 1):real^N`; `-- &1`]] THEN
  SIMP_TAC[VECTOR_NEG_EQ_0; BASIS_NONZERO; DOT_LNEG;
           DIMINDEX_GE_1; LE_REFL]);;

let POLYHEDRON_HALFSPACE_LE = prove
 (`!a b. polyhedron {x:real^N | a dot x <= b}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_SIMP_TAC[DOT_LZERO; SET_RULE `{x | p} = if p then UNIV else {}`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[POLYHEDRON_EMPTY; POLYHEDRON_UNIV];
    REWRITE_TAC[polyhedron] THEN EXISTS_TAC `{{x:real^N | a dot x <= b}}` THEN
    REWRITE_TAC[FINITE_SING; INTERS_1; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real`] THEN ASM_REWRITE_TAC[]]);;

let POLYHEDRON_HALFSPACE_GE = prove
 (`!a b. polyhedron {x:real^N | a dot x >= b}`,
  REWRITE_TAC[REAL_ARITH `a:real >= b <=> --a <= --b`] THEN
  REWRITE_TAC[GSYM DOT_LNEG; POLYHEDRON_HALFSPACE_LE]);;

let POLYHEDRON_HYPERPLANE = prove
 (`!a b. polyhedron {x:real^N | a dot x = b}`,
  REWRITE_TAC[REAL_ARITH `x:real = b <=> x <= b /\ x >= b`] THEN
  REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
  SIMP_TAC[POLYHEDRON_INTER; POLYHEDRON_HALFSPACE_LE;
           POLYHEDRON_HALFSPACE_GE]);;

let AFFINE_IMP_POLYHEDRON = prove
 (`!s:real^N->bool. affine s ==> polyhedron s`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `s:real^N->bool`
    AFFINE_HULL_FINITE_INTERSECTION_HYPERPLANES) THEN
  ASM_SIMP_TAC[HULL_P; RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC POLYHEDRON_INTERS THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  REWRITE_TAC[POLYHEDRON_HYPERPLANE]);;

let POLYHEDRON_IMP_CLOSED = prove
 (`!s:real^N->bool. polyhedron s ==> closed s`,
  REWRITE_TAC[polyhedron; RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CLOSED_INTERS THEN
  X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  REWRITE_TAC[CLOSED_HALFSPACE_LE]);;

let POLYHEDRON_IMP_CONVEX = prove
 (`!s:real^N->bool. polyhedron s ==> convex s`,
  REWRITE_TAC[polyhedron; RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONVEX_INTERS THEN
  X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  REWRITE_TAC[CONVEX_HALFSPACE_LE]);;

let POLYHEDRON_AFFINE_HULL = prove
 (`!s. polyhedron(affine hull s)`,
  SIMP_TAC[AFFINE_IMP_POLYHEDRON; AFFINE_AFFINE_HULL]);;

(* ------------------------------------------------------------------------- *)
(* Canonical polyedron representation making facial structure explicit.      *)
(* ------------------------------------------------------------------------- *)

let POLYHEDRON_INTER_AFFINE = prove
 (`!s. polyhedron s <=>
        ?f. FINITE f /\
            s = (affine hull s) INTER (INTERS f) /\
            (!h. h IN f
                 ==> ?a b. ~(a = vec 0) /\ h = {x:real^N | a dot x <= b})`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[polyhedron] THEN MATCH_MP_TAC MONO_EXISTS THEN
    GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC(SET_RULE `s = t /\ s SUBSET u ==> s = u INTER t`) THEN
    REWRITE_TAC[HULL_SUBSET] THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC POLYHEDRON_INTER THEN REWRITE_TAC[POLYHEDRON_AFFINE_HULL] THEN
    MATCH_MP_TAC POLYHEDRON_INTERS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[POLYHEDRON_HALFSPACE_LE]]);;

let POLYHEDRON_INTER_AFFINE_MINIMAL = prove
 (`!s. polyhedron s <=>
        ?f. FINITE f /\
            s = (affine hull s) INTER (INTERS f) /\
            (!h. h IN f
                 ==> ?a b. ~(a = vec 0) /\ h = {x:real^N | a dot x <= b}) /\
            !f'. f' PSUBSET f ==> s PSUBSET (affine hull s) INTER (INTERS f')`,
  GEN_TAC THEN REWRITE_TAC[POLYHEDRON_INTER_AFFINE] THEN
  EQ_TAC THENL [ALL_TAC; MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]] THEN
  GEN_REWRITE_TAC LAND_CONV
   [MESON[HAS_SIZE]
     `(?f. FINITE f /\ P f) <=> (?n f. f HAS_SIZE n /\ P f)`] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[HAS_SIZE] THEN
  X_GEN_TAC `f:(real^N->bool)->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  X_GEN_TAC `f':(real^N->bool)->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CARD(f':(real^N->bool)->bool)`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CARD_PSUBSET]; ALL_TAC] THEN
  REWRITE_TAC[NOT_EXISTS_THM; HAS_SIZE] THEN
  DISCH_THEN(MP_TAC o SPEC `f':(real^N->bool)->bool`) THEN
  MATCH_MP_TAC(TAUT `a /\ c /\ (~b ==> d) ==> ~(a /\ b /\ c) ==> d`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[PSUBSET; FINITE_SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> ~(s = t) ==> s PSUBSET t`) THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  ASM SET_TAC[]);;

let RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT = prove
 (`!s:real^N->bool f a b.
        FINITE f /\
        s = affine hull s INTER INTERS f /\
        (!h. h IN f ==> ~(a h = vec 0) /\ h = {x | a h dot x <= b h}) /\
        (!f'. f' PSUBSET f ==> s PSUBSET affine hull s INTER INTERS f')
        ==> relative_interior s =
                {x | x IN s /\ !h. h IN f ==> a h dot x < b h}`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[RELATIVE_INTERIOR; IN_ELIM_THM] THEN
    EXISTS_TAC `INTERS {interior h | (h:real^N->bool) IN f}` THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; OPEN_INTERS; FINITE_IMAGE; OPEN_INTERIOR;
                 FORALL_IN_IMAGE; IN_INTERS] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`)) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
      FIRST_ASSUM(SUBST1_TAC o CONJUNCT2) THEN
      ASM_SIMP_TAC[INTERIOR_HALFSPACE_LE; IN_ELIM_THM];
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      MATCH_MP_TAC(SET_RULE
       `(!s. s IN f ==> i s SUBSET s)
        ==> INTERS (IMAGE i f) INTER t SUBSET t INTER INTERS f`) THEN
      REWRITE_TAC[INTERIOR_SUBSET]]] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR]) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:real^N->bool` THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `f DELETE (i:real^N->bool)`) THEN ANTS_TAC THENL
   [ASM SET_TAC[];
    REWRITE_TAC[PSUBSET_ALT; IN_INTER; IN_INTERS; IN_DELETE]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(a:(real^N->bool)->real^N) i dot z > b i` ASSUME_TAC THENL
   [UNDISCH_TAC `~((z:real^N) IN s)` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER; IN_INTERS] THEN
    ASM_REWRITE_TAC[REAL_ARITH `a:real > b <=> ~(a <= b)`] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z:real^N = x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?l. &0 < l /\ l < &1 /\ (l % z + (&1 - l) % x:real^N) IN s`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `e:real` MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; dist] THEN STRIP_TAC THEN
    EXISTS_TAC `min (&1 / &2) (e / &2 / norm(z - x:real^N))` THEN
    REWRITE_TAC[REAL_MIN_LT; REAL_LT_MIN] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH
       `x - (l % z + (&1 - l) % x):real^N = --l % (z - x)`] THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_NEG] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 < a /\ &0 < b /\ b < c ==> abs(min a b) < c`) THEN
      ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ] THEN
      REWRITE_TAC[REAL_LT_01; real_div; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN
      ASM_REWRITE_TAC[REAL_LT_INV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
      UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
      MATCH_MP_TAC(REWRITE_RULE[AFFINE_ALT] AFFINE_AFFINE_HULL) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC `&1 - l` THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  REWRITE_TAC[REAL_ARITH `a < b * (&1 - l) <=> l * b + a < b`] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC
   `l * (a:(real^N->bool)->real^N) i dot z + (a i dot x) * (&1 - l)` THEN
  ASM_SIMP_TAC[REAL_LT_RADD; REAL_LT_LMUL_EQ; GSYM real_gt] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * (&1 - b) = (&1 - b) * a`] THEN
  REWRITE_TAC[GSYM DOT_RMUL; GSYM DOT_RADD] THEN ASM SET_TAC[]);;

let FACET_OF_POLYHEDRON_EXPLICIT = prove
 (`!s:real^N->bool f a b.
        FINITE f /\
        s = affine hull s INTER INTERS f /\
        (!h. h IN f ==> ~(a h = vec 0) /\ h = {x | a h dot x <= b h}) /\
        (!f'. f' PSUBSET f ==> s PSUBSET affine hull s INTER INTERS f')
        ==> !c. c facet_of s <=>
                ?h. h IN f /\ c = s INTER {x | a h dot x = b h}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[INTER_EMPTY; AFFINE_HULL_EMPTY; SET_RULE `~(s PSUBSET s)`;
                    FACET_OF_EMPTY] THEN
    ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `h:real^N->bool`) THEN DISCH_THEN
     (MP_TAC o SPEC `f DELETE (h:real^N->bool)` o last o CONJUNCTS) THEN
    ASM SET_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `polyhedron(s:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[POLYHEDRON_INTER_AFFINE] THEN
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP POLYHEDRON_IMP_CONVEX) THEN
  SUBGOAL_THEN
   `!h:real^N->bool.
       h IN f ==> (s INTER {x:real^N | a h dot x = b h}) facet_of s`
  (LABEL_TAC "face") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[facet_of] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC POLYHEDRON_IMP_CONVEX THEN
        REWRITE_TAC[POLYHEDRON_INTER_AFFINE] THEN
        REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN ASM_MESON_TAC[];
        X_GEN_TAC `x:real^N` THEN FIRST_X_ASSUM SUBST1_TAC THEN
        REWRITE_TAC[IN_INTER; IN_INTERS] THEN
        DISCH_THEN(MP_TAC o SPEC `h:real^N->bool` o CONJUNCT2) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_EQ_EMPTY) THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR]) THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `f DELETE (h:real^N->bool)`) THEN
    ANTS_TAC THENL
     [ASM SET_TAC[];
      REWRITE_TAC[PSUBSET_ALT; IN_INTER; IN_INTERS; IN_DELETE]] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(a:(real^N->bool)->real^N) h dot z > b h` ASSUME_TAC THENL
     [UNDISCH_TAC `~((z:real^N) IN s)` THEN
      FIRST_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[IN_INTER; IN_INTERS] THEN
      ASM_REWRITE_TAC[REAL_ARITH `a:real > b <=> ~(a <= b)`] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(z:real^N = x)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `f:(real^N->bool)->bool`;
                   `a:(real^N->bool)->real^N`; `b:(real^N->bool)->real`]
           RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPEC `h:real^N->bool` th) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN ASSUME_TAC th) THEN
    SUBGOAL_THEN `(a:(real^N->bool)->real^N) h dot x < a h dot z`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `l = (b h - (a:(real^N->bool)->real^N) h dot x) /
                    (a h dot z - a h dot x)` THEN
    SUBGOAL_THEN `&0 < l /\ l < &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "l" THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_SUB_LT] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `w:real^N = (&1 - l) % x + l % z:real^N` THEN
    SUBGOAL_THEN
     `!i. i IN f /\ ~(i = h) ==> (a:(real^N->bool)->real^N) i dot w < b i`
    ASSUME_TAC THENL
     [X_GEN_TAC `i:real^N->bool` THEN STRIP_TAC THEN EXPAND_TAC "w" THEN
      REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
      MATCH_MP_TAC(REAL_ARITH
       `(&1 - l) * x < (&1 - l) * z /\ l * y <= l * z
        ==> (&1 - l) * x + l * y < z`) THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_IMP_LE;
                   REAL_LT_LMUL_EQ; REAL_SUB_LT] THEN
      UNDISCH_TAC `!t:real^N->bool. t IN f /\ ~(t = h) ==> z IN t` THEN
      DISCH_THEN(MP_TAC o SPEC `i:real^N->bool`) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:(real^N->bool)->real^N) h dot w = b h` ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN REWRITE_TAC[VECTOR_ARITH
         `(&1 - l) % x + l % z:real^N = x + l % (z - x)`] THEN
      EXPAND_TAC "l" THEN REWRITE_TAC[DOT_RADD; DOT_RSUB; DOT_RMUL] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NE; REAL_SUB_0] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^N) IN s` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
      REWRITE_TAC[IN_INTER; IN_INTERS] THEN CONJ_TAC THENL
       [EXPAND_TAC "w" THEN
        MATCH_MP_TAC(REWRITE_RULE[AFFINE_ALT] AFFINE_AFFINE_HULL) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN
        ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
        ALL_TAC] THEN
      X_GEN_TAC `i:real^N->bool` THEN DISCH_TAC THEN
      ASM_CASES_TAC `i:real^N->bool = h` THENL
       [ASM SET_TAC[REAL_LE_REFL]; ALL_TAC] THEN
      SUBGOAL_THEN `convex(i:real^N->bool)` MP_TAC THENL
       [REPEAT(FIRST_X_ASSUM(MP_TAC o C MATCH_MP
         (ASSUME `(i:real^N->bool) IN f`))) THEN
        REPEAT(DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th])) THEN
        REWRITE_TAC[CONVEX_HALFSPACE_LE];
        ALL_TAC] THEN
      REWRITE_TAC[CONVEX_ALT] THEN EXPAND_TAC "w" THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[] THEN FIRST_X_ASSUM(MP_TAC o CONJUNCT1) THEN
      FIRST_ASSUM(fun t -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [t]) THEN
      REWRITE_TAC[IN_INTER; IN_INTERS] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
    SUBGOAL_THEN
     `affine hull (s INTER {x | (a:(real^N->bool)->real^N) h dot x = b h}) =
      (affine hull s) INTER {x | a h dot x = b h}`
    SUBST1_TAC THENL
     [ALL_TAC;
      SIMP_TAC[AFF_DIM_AFFINE_INTER_HYPERPLANE; AFFINE_AFFINE_HULL] THEN
      COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      COND_CASES_TAC THENL [ASM SET_TAC[REAL_LT_REFL]; REFL_TAC]] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET_INTER] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      MATCH_MP_TAC(SET_RULE
       `s SUBSET affine hull t /\ affine hull t = t ==> s SUBSET t`) THEN
      REWRITE_TAC[AFFINE_HULL_EQ; AFFINE_HYPERPLANE] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?t. &0 < t /\
          !j. j IN f /\ ~(j:real^N->bool = h)
              ==> t * (a j dot y - a j dot w) <= b j - a j dot (w:real^N)`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `f DELETE (h:real^N->bool) = {}` THENL
       [ASM_REWRITE_TAC[GSYM IN_DELETE; NOT_IN_EMPTY] THEN
        EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01];
        ALL_TAC] THEN
      EXISTS_TAC `inf (IMAGE
       (\j. if &0 < a j dot y - a j dot (w:real^N)
            then (b j - a j dot w) / (a j dot y - a j dot w)
            else &1) (f DELETE (h:real^N->bool)))` THEN
      MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; FINITE_DELETE;
                     IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_DELETE] THEN
        ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
        ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT; REAL_LT_01; COND_ID];
        REWRITE_TAC[REAL_SUB_LT] THEN DISCH_TAC] THEN
      X_GEN_TAC `j:real^N->bool` THEN STRIP_TAC THEN
      ASM_CASES_TAC `a j dot (w:real^N) < a(j:real^N->bool) dot y` THENL
       [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_INF_LE_FINITE; REAL_SUB_LT;
                     FINITE_IMAGE; FINITE_DELETE; IMAGE_EQ_EMPTY] THEN
        REWRITE_TAC[EXISTS_IN_IMAGE] THEN EXISTS_TAC `j:real^N->bool` THEN
        ASM_REWRITE_TAC[IN_DELETE; REAL_LE_REFL];
        MATCH_MP_TAC(REAL_ARITH `&0 <= --x /\ &0 < y ==> x <= y`) THEN
        ASM_SIMP_TAC[REAL_SUB_LT; GSYM REAL_MUL_RNEG; REAL_LE_MUL_EQ] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `c:real^N = (&1 - t) % w + t % y` THEN
    SUBGOAL_THEN `y:real^N = (&1 - inv t) % w + inv(t) % c` SUBST1_TAC THENL
     [EXPAND_TAC "c" THEN
      REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ;
                REAL_FIELD `&0 < x ==> inv x * (&1 - x) = inv x - &1`] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[AFFINE_ALT] AFFINE_AFFINE_HULL) THEN
    CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
      DISCH_TAC] THEN
    FIRST_ASSUM(fun t -> GEN_REWRITE_TAC RAND_CONV [t]) THEN
    REWRITE_TAC[IN_INTER; IN_INTERS] THEN CONJ_TAC THENL
     [EXPAND_TAC "c" THEN
      MATCH_MP_TAC(REWRITE_RULE[AFFINE_ALT] AFFINE_AFFINE_HULL) THEN
      ASM_SIMP_TAC[HULL_INC];
      ALL_TAC] THEN
    X_GEN_TAC `j:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o C MATCH_MP
      (ASSUME `(j:real^N->bool) IN f`)) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_CASES_TAC `j:real^N->bool = h` THEN ASM_SIMP_TAC[REAL_EQ_IMP_LE] THEN
    EXPAND_TAC "c" THEN REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
    REWRITE_TAC[REAL_ARITH
     `(&1 - t) * x + t * y <= z <=> t * (y - x) <= z - x`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `c:real^N->bool` THEN EQ_TAC THENL
   [ALL_TAC; STRIP_TAC THEN ASM_SIMP_TAC[]] THEN
  REWRITE_TAC[facet_of] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FACE_OF_IMP_CONVEX) THEN
  SUBGOAL_THEN `~(relative_interior(c:real^N->bool) = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:(real^N->bool)->bool`;
                 `a:(real^N->bool)->real^N`; `b:(real^N->bool)->real`]
         RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `~(c:real^N->bool = s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[INT_ARITH`~(i:int = i - &1)`]; ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^N) IN relative_interior s)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(c:real^N->bool = s)` THEN REWRITE_TAC[CONTRAPOS_THM] THEN
    DISCH_TAC THEN MATCH_MP_TAC FACE_OF_EQ THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[FACE_OF_REFL] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN s` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o MATCH_MP
       FACE_OF_IMP_SUBSET) THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  FIRST_ASSUM(fun t -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [t]) THEN
  REWRITE_TAC[IN_INTER; IN_INTERS] THEN STRIP_TAC THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `i:real^N->bool` THEN REWRITE_TAC[NOT_IMP] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(a:(real^N->bool)->real^N) i dot x = b i` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= y /\ ~(x < y) ==> x = y`) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_THEN
     `!t:real^N->bool. t IN f ==> x IN t` (MP_TAC o SPEC `i:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o C MATCH_MP
     (ASSUME `(i:real^N->bool) IN f`)) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c SUBSET (s INTER {x:real^N | a(i:real^N->bool) dot x = b i})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[FACE_OF_IMP_SUBSET] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[facet_of]) THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `c face_of (s INTER {x:real^N | a(i:real^N->bool) dot x = b i})`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:real^N->bool`; `s:real^N->bool`;
                   `s INTER {x:real^N | a(i:real^N->bool) dot x = b i}`]
                FACE_OF_FACE) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[facet_of]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `aff_dim(c:real^N->bool) <
    aff_dim(s INTER {x:real^N | a(i:real^N->bool) dot x = b i})`
  MP_TAC THENL
   [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
    ASM_SIMP_TAC[CONVEX_INTER; CONVEX_HYPERPLANE];
    RULE_ASSUM_TAC(REWRITE_RULE[facet_of]) THEN ASM_SIMP_TAC[INT_LT_REFL]]);;

let FACE_OF_POLYHEDRON_SUBSET_EXPLICIT = prove
 (`!s:real^N->bool f a b.
        FINITE f /\
        s = affine hull s INTER INTERS f /\
        (!h. h IN f ==> ~(a h = vec 0) /\ h = {x | a h dot x <= b h}) /\
        (!f'. f' PSUBSET f ==> s PSUBSET affine hull s INTER INTERS f')
        ==> !c. c face_of s /\ ~(c = {}) /\ ~(c = s)
                ==> ?h. h IN f /\ c SUBSET (s INTER {x | a h dot x = b h})`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THENL
   [DISCH_THEN(MP_TAC o SYM o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[INTERS_0; INTER_UNIV; AFFINE_HULL_EQ] THEN
    MESON_TAC[FACE_OF_AFFINE_TRIVIAL];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP FACET_OF_POLYHEDRON_EXPLICIT) THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FACE_OF_IMP_CONVEX) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
  SUBGOAL_THEN `polyhedron(s:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[POLYHEDRON_INTER_AFFINE] THEN
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP POLYHEDRON_IMP_CONVEX) THEN
  SUBGOAL_THEN
   `!h:real^N->bool.
        h IN f ==> (s INTER {x:real^N | a h dot x = b h}) face_of s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYHEDRON_IMP_CONVEX THEN
      REWRITE_TAC[POLYHEDRON_INTER_AFFINE] THEN
      REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN ASM_MESON_TAC[];
      X_GEN_TAC `x:real^N` THEN FIRST_X_ASSUM SUBST1_TAC THEN
      REWRITE_TAC[IN_INTER; IN_INTERS] THEN
      DISCH_THEN(MP_TAC o SPEC `h:real^N->bool` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior(c:real^N->bool) = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:(real^N->bool)->bool`;
                 `a:(real^N->bool)->real^N`; `b:(real^N->bool)->real`]
         RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `~((x:real^N) IN relative_interior s)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(c:real^N->bool = s)` THEN REWRITE_TAC[CONTRAPOS_THM] THEN
    DISCH_TAC THEN MATCH_MP_TAC FACE_OF_EQ THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[FACE_OF_REFL] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN s` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o MATCH_MP
       FACE_OF_IMP_SUBSET) THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  FIRST_ASSUM(fun t -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [t]) THEN
  REWRITE_TAC[IN_INTER; IN_INTERS] THEN STRIP_TAC THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `i:real^N->bool` THEN REWRITE_TAC[NOT_IMP] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(a:(real^N->bool)->real^N) i dot x = b i` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= y /\ ~(x < y) ==> x = y`) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_THEN
     `!t:real^N->bool. t IN f ==> x IN t` (MP_TAC o SPEC `i:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o C MATCH_MP
     (ASSUME `(i:real^N->bool) IN f`)) THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_SIMP_TAC[FACE_OF_IMP_SUBSET] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[facet_of]) THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
  EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]);;

let FACE_OF_POLYHEDRON_EXPLICIT = prove
 (`!s:real^N->bool f a b.
        FINITE f /\
        s = affine hull s INTER INTERS f /\
        (!h. h IN f ==> ~(a h = vec 0) /\ h = {x | a h dot x <= b h}) /\
        (!f'. f' PSUBSET f ==> s PSUBSET affine hull s INTER INTERS f')
        ==> !c. c face_of s /\ ~(c = {}) /\ ~(c = s)
                ==> c = INTERS {s INTER {x | a h dot x = b h} |h|
                                h IN f /\
                                c SUBSET (s INTER {x | a h dot x = b h})}`,
  let lemma = prove
   (`!t s. (!a. P a ==> t SUBSET s INTER INTERS {f x | P x})
           ==> t SUBSET INTERS {s INTER f x | P x}`,
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[INTERS_IMAGE] THEN SET_TAC[]) in
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP FACET_OF_POLYHEDRON_EXPLICIT) THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FACE_OF_IMP_CONVEX) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
  SUBGOAL_THEN `polyhedron(s:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[POLYHEDRON_INTER_AFFINE] THEN
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP POLYHEDRON_IMP_CONVEX) THEN
  SUBGOAL_THEN
   `!h:real^N->bool.
        h IN f ==> (s INTER {x:real^N | a h dot x = b h}) face_of s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYHEDRON_IMP_CONVEX THEN
      REWRITE_TAC[POLYHEDRON_INTER_AFFINE] THEN
      REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN ASM_MESON_TAC[];
      X_GEN_TAC `x:real^N` THEN FIRST_X_ASSUM SUBST1_TAC THEN
      REWRITE_TAC[IN_INTER; IN_INTERS] THEN
      DISCH_THEN(MP_TAC o SPEC `h:real^N->bool` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior(c:real^N->bool) = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN s` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC FACE_OF_EQ THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FACE_OF_INTERS THEN ASM_SIMP_TAC[FORALL_IN_GSPEC] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `f:(real^N->bool)->bool`;
                   `a:(real^N->bool)->real^N`; `b:(real^N->bool)->real`]
         FACE_OF_POLYHEDRON_SUBSET_EXPLICIT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL[FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{s INTER {x | a(h:real^N->bool) dot x = b h} |h|
     h IN f /\ c SUBSET (s INTER {x:real^N | a h dot x = b h})} =
    {s INTER {x | a(h:real^N->bool) dot x = b h} |h|
     h IN f /\ z IN s INTER {x:real^N | a h dot x = b h}}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x. P x <=> Q x) ==> {f x | P x} = {f x | Q x}`) THEN
    X_GEN_TAC `h:real^N->bool` THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `?e. &0 < e /\ !h. h IN f /\ a(h:real^N->bool) dot z < b h
                      ==> ball(z,e) SUBSET {w:real^N | a h dot w < b h}`
  (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))) THENL
   [REWRITE_TAC[SET_RULE
     `(!h. P h ==> s SUBSET t h) <=> s SUBSET INTERS (IMAGE t {h | P h})`] THEN
    MATCH_MP_TAC(MESON[OPEN_CONTAINS_BALL]
     `open s /\ x IN s ==> ?e. &0 < e /\ ball(x,e) SUBSET s`) THEN
    SIMP_TAC[IN_INTERS; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    MATCH_MP_TAC OPEN_INTERS THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE; FINITE_IMAGE; FINITE_RESTRICT] THEN
    REWRITE_TAC[OPEN_HALFSPACE_LT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_RELATIVE_INTERIOR] THEN
  ASM_SIMP_TAC[IN_INTERS; FORALL_IN_GSPEC; IN_ELIM_THM; IN_INTER] THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC lemma THEN X_GEN_TAC `i:real^N->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [th]) THEN
  MATCH_MP_TAC(SET_RULE
   `ae SUBSET as /\ ae SUBSET hs /\
    b INTER hs SUBSET fs
    ==> (b INTER ae) SUBSET (as INTER fs) INTER hs`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN
    REWRITE_TAC[SUBSET; IN_INTERS; FORALL_IN_GSPEC] THEN ASM SET_TAC[];
    SIMP_TAC[SET_RULE `s SUBSET INTERS f <=> !t. t IN f ==> s SUBSET t`] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `j:real^N->bool` THEN
    STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[AFFINE_HYPERPLANE] THEN
    REWRITE_TAC[SUBSET; IN_INTERS; FORALL_IN_GSPEC] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `s SUBSET INTERS f <=> !t. t IN f ==> s SUBSET t`] THEN
  X_GEN_TAC `j:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(a:(real^N->bool)->real^N) j dot z <= b j` MP_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[REAL_LE_LT]] THEN
  STRIP_TAC THENL [ASM SET_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
  `(?s. s IN f /\ s SUBSET t) ==> u INTER INTERS f SUBSET t`) THEN
  REWRITE_TAC[EXISTS_IN_GSPEC] THEN EXISTS_TAC `j:real^N->bool` THEN
  ASM SET_TAC[REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* More general corollaries from the explicit representation.                *)
(* ------------------------------------------------------------------------- *)

let FACET_OF_POLYHEDRON = prove
 (`!s:real^N->bool c.
        polyhedron s /\ c facet_of s
        ==> ?a b. ~(a = vec 0) /\
                  s SUBSET {x | a dot x <= b} /\
                  c = s INTER {x | a dot x = b}`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [POLYHEDRON_INTER_AFFINE_MINIMAL]) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`f:(real^N->bool)->bool`; `a:(real^N->bool)->real^N`;
    `b:(real^N->bool)->real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:(real^N->bool)->bool`;
                 `a:(real^N->bool)->real^N`; `b:(real^N->bool)->real`]
        FACET_OF_POLYHEDRON_EXPLICIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(a:(real^N->bool)->real^N) i` THEN
  EXISTS_TAC `(b:(real^N->bool)->real) i` THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  MATCH_MP_TAC(SET_RULE `t SUBSET u ==> (s INTER t) SUBSET u`) THEN
  MATCH_MP_TAC(SET_RULE `t IN f ==> INTERS f SUBSET t`) THEN ASM_MESON_TAC[]);;

let FACE_OF_POLYHEDRON = prove
 (`!s:real^N->bool c.
        polyhedron s /\ c face_of s /\ ~(c = {}) /\ ~(c = s)
        ==> c = INTERS {f | f facet_of s /\ c SUBSET f}`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [POLYHEDRON_INTER_AFFINE_MINIMAL]) THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`f:(real^N->bool)->bool`; `a:(real^N->bool)->real^N`;
    `b:(real^N->bool)->real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:(real^N->bool)->bool`;
                 `a:(real^N->bool)->real^N`; `b:(real^N->bool)->real`]
         FACET_OF_POLYHEDRON_EXPLICIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:(real^N->bool)->bool`;
                 `a:(real^N->bool)->real^N`; `b:(real^N->bool)->real`]
         FACE_OF_POLYHEDRON_EXPLICIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `h:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

let FACE_OF_POLYHEDRON_SUBSET_FACET = prove
 (`!s:real^N->bool c.
        polyhedron s /\ c face_of s /\ ~(c = {}) /\ ~(c = s)
        ==> ?f. f facet_of s /\ c SUBSET f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c:real^N->bool`] FACE_OF_POLYHEDRON) THEN
  ASM_CASES_TAC `{f:real^N->bool | f facet_of s /\ c SUBSET f} = {}` THEN
  ASM SET_TAC[]);;

let EXPOSED_FACE_OF_POLYHEDRON = prove
 (`!s f:real^N->bool. polyhedron s ==> (f exposed_face_of s <=> f face_of s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [SIMP_TAC[exposed_face_of]; ALL_TAC] THEN
  DISCH_TAC THEN ASM_CASES_TAC `f:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[EMPTY_EXPOSED_FACE_OF] THEN
  ASM_CASES_TAC `f:real^N->bool = s` THEN
  ASM_SIMP_TAC[EXPOSED_FACE_OF_REFL; POLYHEDRON_IMP_CONVEX] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->bool`] FACE_OF_POLYHEDRON) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC EXPOSED_FACE_OF_INTERS THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[FACE_OF_POLYHEDRON_SUBSET_FACET; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[exposed_face_of; FACET_OF_IMP_FACE_OF] THEN
  ASM_MESON_TAC[FACET_OF_POLYHEDRON]);;

let FACE_OF_POLYHEDRON_POLYHEDRON = prove
 (`!s:real^N->bool c. polyhedron s /\ c face_of s ==> polyhedron c`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [POLYHEDRON_INTER_AFFINE_MINIMAL]) THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`f:(real^N->bool)->bool`; `a:(real^N->bool)->real^N`;
    `b:(real^N->bool)->real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:(real^N->bool)->bool`;
                 `a:(real^N->bool)->real^N`; `b:(real^N->bool)->real`]
         FACE_OF_POLYHEDRON_EXPLICIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `c:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[POLYHEDRON_EMPTY] THEN
  ASM_CASES_TAC `c:real^N->bool = s` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC POLYHEDRON_INTERS THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_RESTRICT] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[IMAGE_ID] THEN
  MATCH_MP_TAC POLYHEDRON_INTER THEN
  ASM_REWRITE_TAC[POLYHEDRON_HYPERPLANE]);;

let FINITE_POLYHEDRON_FACES = prove
 (`!s:real^N->bool. polyhedron s ==> FINITE {f | f face_of s}`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [POLYHEDRON_INTER_AFFINE_MINIMAL]) THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`f:(real^N->bool)->bool`; `a:(real^N->bool)->real^N`;
    `b:(real^N->bool)->real`] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(MESON[FINITE_DELETE]
   `!a b. FINITE (s DELETE a DELETE b) ==> FINITE s`) THEN
  MAP_EVERY EXISTS_TAC [`{}:real^N->bool`; `s:real^N->bool`] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{INTERS {s INTER {x:real^N | a(h:real^N->bool) dot x = b h} | h | h IN f'}
    |f'| f' SUBSET f}` THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SIMPLE_IMAGE_GEN] THEN
  ASM_SIMP_TAC[FINITE_POWERSET; FINITE_IMAGE] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:(real^N->bool)->bool`;
                 `a:(real^N->bool)->real^N`; `b:(real^N->bool)->real`]
         FACE_OF_POLYHEDRON_EXPLICIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `c:real^N->bool` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN EXISTS_TAC
   `{h:real^N->bool |
     h IN f /\ c SUBSET s INTER {x:real^N | a h dot x = b h}}` THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN FIRST_ASSUM ACCEPT_TAC);;

let FINITE_POLYHEDRON_EXPOSED_FACES = prove
 (`!s:real^N->bool. polyhedron s ==> FINITE {f | f exposed_face_of s}`,
  SIMP_TAC[EXPOSED_FACE_OF_POLYHEDRON; FINITE_POLYHEDRON_FACES]);;

let FINITE_POLYHEDRON_EXTREME_POINTS = prove
 (`!s:real^N->bool. polyhedron s ==> FINITE {v | v extreme_point_of s}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
  ONCE_REWRITE_TAC[SET_RULE `{v} face_of s <=> {v} IN {f | f face_of s}`] THEN
  MATCH_MP_TAC FINITE_FINITE_PREIMAGE THEN
  ASM_SIMP_TAC[FINITE_POLYHEDRON_FACES] THEN X_GEN_TAC `f:real^N->bool` THEN
  DISCH_TAC THEN ASM_CASES_TAC `!a:real^N. ~({a} = f)` THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SET_RULE `{v | {v} = {a}} = {a}`; FINITE_SING]);;

let RELATIVE_INTERIOR_OF_POLYHEDRON = prove
 (`!s:real^N->bool.
        polyhedron s
        ==> relative_interior s = s DIFF UNIONS {f | f facet_of s}`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [POLYHEDRON_INTER_AFFINE_MINIMAL]) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`f:(real^N->bool)->bool`; `a:(real^N->bool)->real^N`;
    `b:(real^N->bool)->real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:(real^N->bool)->bool`;
                 `a:(real^N->bool)->real^N`; `b:(real^N->bool)->real`]
        FACET_OF_POLYHEDRON_EXPLICIT) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:(real^N->bool)->bool`;
                 `a:(real^N->bool)->real^N`; `b:(real^N->bool)->real`]
        RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> P x \/ x IN t) /\ (!x. x IN t ==> ~P x)
    ==> {x | x IN s /\ P x} = s DIFF t`) THEN
  REWRITE_TAC[FORALL_IN_UNIONS] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_GSPEC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM; TAUT `(a /\ b) /\ c <=> b /\ a /\ c`] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    ASM_REWRITE_TAC[UNWIND_THM2; IN_ELIM_THM; IN_INTER] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. P x ==> Q x \/ R x) ==> (!x. P x ==> Q x) \/ (?x. P x /\ R x)`) THEN
    X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM REAL_LE_LT] THEN
    SUBGOAL_THEN `(x:real^N) IN INTERS f` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTERS] THEN
    DISCH_THEN(MP_TAC o SPEC `h:real^N->bool`) THEN
    SUBGOAL_THEN `h = {x:real^N | a h dot x <= b h}` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN SET_TAC[]];
    X_GEN_TAC `h:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `x:real^N` THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    ASM_MESON_TAC[REAL_LT_REFL]]);;

let RELATIVE_FRONTIER_OF_POLYHEDRON = prove
 (`!s:real^N->bool.
        polyhedron s
        ==> s DIFF relative_interior s = UNIONS {f | f facet_of s}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RELATIVE_INTERIOR_OF_POLYHEDRON] THEN
  MATCH_MP_TAC(SET_RULE `f SUBSET s ==> s DIFF (s DIFF f) = f`) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[FACET_OF_IMP_SUBSET; SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* A characterization of polyhedra as having finitely many faces.            *)
(* ------------------------------------------------------------------------- *)

let POLYHEDRON_EQ_FINITE_EXPOSED_FACES = prove
 (`!s:real^N->bool.
    polyhedron s <=> closed s /\ convex s /\ FINITE {f | f exposed_face_of s}`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[POLYHEDRON_IMP_CLOSED; POLYHEDRON_IMP_CONVEX;
               FINITE_POLYHEDRON_EXPOSED_FACES] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[POLYHEDRON_EMPTY] THEN
  ABBREV_TAC
   `f = {h:real^N->bool | h exposed_face_of s /\ ~(h = {}) /\ ~(h = s)}` THEN
  SUBGOAL_THEN `FINITE(f:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN
    ONCE_REWRITE_TAC[SET_RULE
     `{x | P x /\ Q x} = {x | x IN {x | P x} /\ Q x}`] THEN
    ASM_SIMP_TAC[FINITE_RESTRICT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^N->bool.
        h IN f
        ==> h face_of s /\
            ?a b. ~(a = vec 0) /\
                  s SUBSET {x | a dot x <= b} /\
                  h = s INTER {x | a dot x = b}`
  MP_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[EXPOSED_FACE_OF; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; FORALL_AND_THM;
              TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:(real^N->bool)->real^N` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:(real^N->bool)->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `s = affine hull s INTER
        INTERS {{x:real^N | a(h:real^N->bool) dot x <= b h} | h IN f}`
  SUBST1_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC POLYHEDRON_INTER THEN REWRITE_TAC[POLYHEDRON_AFFINE_HULL] THEN
    MATCH_MP_TAC POLYHEDRON_INTERS THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; POLYHEDRON_HALFSPACE_LE]] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET_INTER; HULL_SUBSET;
              SET_RULE `s SUBSET INTERS f <=> !h. h IN f ==> s SUBSET h`] THEN
  ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_INTERS; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `p:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(relative_interior(s:real^N->bool) = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY];
    GEN_REWRITE_TAC LAND_CONV [GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `c:real^N`)] THEN
  SUBGOAL_THEN
   `?x:real^N. x IN segment[c,p] /\ x IN (s DIFF relative_interior s)`
  MP_TAC THENL
   [MP_TAC(ISPEC `segment[c:real^N,p]` CONNECTED_LOCAL) THEN
    REWRITE_TAC[CONNECTED_SEGMENT; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`segment[c:real^N,p] INTER relative_interior s`;
      `segment[c:real^N,p] INTER (UNIV DIFF s)`]) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[IN_DIFF; NOT_EXISTS_THM] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
      EXISTS_TAC `affine hull s:real^N->bool` THEN
      SIMP_TAC[OPEN_IN_RELATIVE_INTERIOR; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
        OPEN_IN_SUBTOPOLOGY_REFL; SUBSET_UNIV; OPEN_IN_INTER;
        TOPSPACE_EUCLIDEAN] THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      SIMP_TAC[AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL] THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; HULL_INC; SUBSET];
      REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `(:real^N) DIFF s` THEN
      ASM_REWRITE_TAC[GSYM CLOSED_OPEN];
     MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
     MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      ASM_MESON_TAC[ENDS_IN_SEGMENT];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_INTER; IN_UNIV] THEN
      ASM_MESON_TAC[ENDS_IN_SEGMENT]];
    REWRITE_TAC[IN_SEGMENT; LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM2] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real` MP_TAC) THEN
    ASM_CASES_TAC `l = &0` THEN
    ASM_REWRITE_TAC[VECTOR_ADD_RID; VECTOR_MUL_LZERO; REAL_SUB_RZERO;
                    VECTOR_MUL_LID; IN_DIFF] THEN
    ASM_CASES_TAC `l = &1` THEN
    ASM_REWRITE_TAC[VECTOR_ADD_LID; VECTOR_MUL_LZERO; REAL_SUB_REFL;
                    VECTOR_MUL_LID; IN_DIFF] THEN
    ASM_REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC] THEN
  ABBREV_TAC `x:real^N = (&1 - l) % c + l % p` THEN
  SUBGOAL_THEN `?h:real^N->bool. h IN f /\ x IN h` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `(&1 - l) % c + l % p:real^N`]
      SUPPORTING_HYPERPLANE_RELATIVE_FRONTIER) THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real^N` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "f" THEN
    EXISTS_TAC `s INTER {y:real^N | d dot y = d dot x}` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE THEN
      ASM_SIMP_TAC[real_ge; REWRITE_RULE[SUBSET] CLOSURE_SUBSET];
      ASM SET_TAC[];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `c:real^N`) THEN
      ASM_MESON_TAC[SUBSET; REAL_LT_REFL; RELATIVE_INTERIOR_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{y:real^N | a(h:real^N->bool) dot y = b h} face_of
                {y | a h dot y <= b h}`
  MP_TAC THENL
   [MATCH_MP_TAC(MESON[]
     `(t INTER s) face_of t /\ t INTER s = s ==> s face_of t`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
      REWRITE_TAC[IN_ELIM_THM; CONVEX_HALFSPACE_LE];
      SET_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[face_of] THEN
  DISCH_THEN(MP_TAC o SPECL [`c:real^N`; `p:real^N`; `x:real^N`] o
        CONJUNCT2 o CONJUNCT2) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; NOT_IMP; GSYM CONJ_ASSOC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
      RELATIVE_INTERIOR_SUBSET)) THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM SET_TAC[];
    REWRITE_TAC[IN_SEGMENT] THEN ASM SET_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `h:real^N->bool`; `s:real^N->bool`]
        SUBSET_OF_FACE_OF) THEN
  ASM SET_TAC[]);;

let POLYHEDRON_EQ_FINITE_FACES = prove
 (`!s:real^N->bool.
        polyhedron s <=>
        closed s /\ convex s /\ FINITE {f | f face_of s}`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[POLYHEDRON_IMP_CLOSED; POLYHEDRON_IMP_CONVEX;
               FINITE_POLYHEDRON_FACES] THEN
  REWRITE_TAC[POLYHEDRON_EQ_FINITE_EXPOSED_FACES] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{f:real^N->bool | f face_of s}` THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; exposed_face_of]);;

let POLYHEDRON_TRANSLATION_EQ = prove
 (`!a s. polyhedron (IMAGE (\x:real^N. a + x) s) <=> polyhedron s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[POLYHEDRON_EQ_FINITE_FACES] THEN
  REWRITE_TAC[CLOSED_TRANSLATION_EQ] THEN AP_TERM_TAC THEN
  REWRITE_TAC[CONVEX_TRANSLATION_EQ] THEN AP_TERM_TAC THEN
  MP_TAC(ISPEC `IMAGE (\x:real^N. a + x)` QUANTIFY_SURJECTION_THM) THEN
  REWRITE_TAC[SURJECTIVE_IMAGE; EXISTS_REFL;
    VECTOR_ARITH `a + x:real^N = y <=> x = y - a`] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[FACE_OF_TRANSLATION_EQ] THEN
  MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
  MATCH_MP_TAC(MESON[]
   `(!x y. Q x y ==> R x y) ==> (!x y. P x /\ P y /\ Q x y ==> R x y)`) THEN
  REWRITE_TAC[INJECTIVE_IMAGE] THEN VECTOR_ARITH_TAC);;

add_translation_invariants [POLYHEDRON_TRANSLATION_EQ];;

let POLYHEDRON_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> (polyhedron (IMAGE f s) <=> polyhedron s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[POLYHEDRON_EQ_FINITE_FACES] THEN
  BINOP_TAC THENL
   [ASM_MESON_TAC[CLOSED_INJECTIVE_LINEAR_IMAGE_EQ]; ALL_TAC] THEN
  BINOP_TAC THENL [ASM_MESON_TAC[CONVEX_LINEAR_IMAGE_EQ]; ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (f:real^M->real^N)` QUANTIFY_SURJECTION_THM) THEN
  ASM_REWRITE_TAC[SURJECTIVE_IMAGE] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  MP_TAC(ISPEC `f:real^M->real^N` FACE_OF_LINEAR_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [GSYM INJECTIVE_IMAGE]) THEN
  ASM_REWRITE_TAC[IMP_CONJ]);;

add_linear_invariants [POLYHEDRON_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Relation between polytopes and polyhedra.                                 *)
(* ------------------------------------------------------------------------- *)

let POLYTOPE_EQ_BOUNDED_POLYHEDRON = prove
 (`!s:real^N->bool. polytope s <=> polyhedron s /\ bounded s`,
  GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[FINITE_POLYTOPE_FACES; POLYHEDRON_EQ_FINITE_FACES;
             POLYTOPE_IMP_CLOSED; POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_BOUNDED];
    STRIP_TAC THEN REWRITE_TAC[polytope] THEN
    EXISTS_TAC `{v:real^N | v extreme_point_of s}` THEN
    ASM_SIMP_TAC[FINITE_POLYHEDRON_EXTREME_POINTS] THEN
    MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
    ASM_SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; POLYHEDRON_IMP_CLOSED;
                 POLYHEDRON_IMP_CONVEX]]);;

let POLYTOPE_INTER = prove
 (`!s t. polytope s /\ polytope t ==> polytope(s INTER t)`,
  SIMP_TAC[POLYTOPE_EQ_BOUNDED_POLYHEDRON; POLYHEDRON_INTER; BOUNDED_INTER]);;

let POLYTOPE_IMP_POLYHEDRON = prove
 (`!p. polytope p ==> polyhedron p`,
  SIMP_TAC[POLYTOPE_EQ_BOUNDED_POLYHEDRON]);;

let POLYTOPE_FACET_EXISTS = prove
 (`!p:real^N->bool. polytope p /\ &0 < aff_dim p ==> ?f. f facet_of p`,
  GEN_TAC THEN ASM_CASES_TAC `p:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN CONV_TAC INT_REDUCE_CONV THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `p:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT; POLYTOPE_IMP_CONVEX] THEN
  DISCH_THEN(X_CHOOSE_TAC `v:real^N`) THEN
  MP_TAC(ISPECL [`p:real^N->bool`; `{v:real^N}`]
    FACE_OF_POLYHEDRON_SUBSET_FACET) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_POLYHEDRON; FACE_OF_SING; NOT_INSERT_EMPTY] THEN
  ASM_MESON_TAC[AFF_DIM_SING; INT_LT_REFL]);;

let POLYHEDRON_INTERVAL = prove
 (`!a b. polyhedron(interval[a,b])`,
  MESON_TAC[POLYTOPE_IMP_POLYHEDRON; POLYTOPE_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* Polytope is union of convex hulls of facets plus any point inside.        *)
(* ------------------------------------------------------------------------- *)

let POLYTOPE_UNION_CONVEX_HULL_FACETS = prove
 (`!s p:real^N->bool.
        polytope p /\ &0 < aff_dim p /\ ~(s = {}) /\ s SUBSET p
        ==> p = UNIONS { convex hull (s UNION f) | f facet_of p}`,
  let lemma = SET_RULE `{f x | p x} = {y | ?x. p x /\ y = f x}` in
  MATCH_MP_TAC SET_PROVE_CASES THEN REWRITE_TAC[] THEN
  X_GEN_TAC `a:real^N` THEN ONCE_REWRITE_TAC[lemma] THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN ONCE_REWRITE_TAC[GSYM lemma] THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(SET_RULE `(vec 0:real^N) IN (vec 0 INSERT s)`) THEN
  SPEC_TAC(`(vec 0:real^N) INSERT s`,`s:real^N->bool`) THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  X_GEN_TAC `p:real^N->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
   GEN_REWRITE_RULE I [POLYTOPE_EQ_BOUNDED_POLYHEDRON]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; RIGHT_FORALL_IMP_THM] THEN
    X_GEN_TAC `f:real^N->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM SUBSET] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `convex hull p:real^N->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP FACET_OF_IMP_SUBSET) THEN ASM SET_TAC[];
      ASM_MESON_TAC[CONVEX_HULL_EQ; POLYHEDRON_IMP_CONVEX; SUBSET_REFL]]] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `v:real^N = vec 0` THENL
   [MP_TAC(ISPEC `p:real^N->bool` POLYTOPE_FACET_EXISTS) THEN
    ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[HULL_INC; IN_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN `?t. &1 < t /\ ~((t % v:real^N) IN p)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `max (&2) ((B + &1) / norm (v:real^N))` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o
     GEN_REWRITE_RULE BINDER_CONV [GSYM CONTRAPOS_THM]) THEN
    ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LE_RDIV_EQ; NORM_POS_LT] THEN
    MATCH_MP_TAC(REAL_ARITH `a < b ==> ~(abs(max (&2) b) <= a)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ; NORM_POS_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^N) IN p` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`segment[vec 0,t % v:real^N] INTER p`; `vec 0:real^N`]
        DISTANCE_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_INTER_CLOSED; POLYHEDRON_IMP_CLOSED; COMPACT_SEGMENT;
                 GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    ASM_MESON_TAC[ENDS_IN_SEGMENT];
    REWRITE_TAC[IN_INTER; GSYM CONJ_ASSOC; IMP_CONJ] THEN
    REWRITE_TAC[segment; FORALL_IN_GSPEC; EXISTS_IN_GSPEC] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; DIST_0] THEN
    REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; NORM_MUL; REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ; NORM_POS_LT; LEFT_IMP_EXISTS_THM;
                 REAL_ARITH `&1 < t ==> &0 < abs t`] THEN
    X_GEN_TAC `u:real` THEN
    ASM_CASES_TAC `u = &1` THEN ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[real_abs] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `inv(t) <= u` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_INV_LE_1; REAL_LT_IMP_LE; REAL_LE_INV_EQ;
                 REAL_ARITH `&1 < t ==> &0 <= t`] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID;
                 REAL_ARITH `&1 < t ==> ~(t = &0)`];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REAL_ARITH `&1 < t ==> &0 < t`)) THEN
  SUBGOAL_THEN `&0 < u /\ u < &1` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_LE] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `inv t <= &0` THEN REWRITE_TAC[REAL_NOT_LE] THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!t. t SUBSET s /\ x IN t ==> x IN s`) THEN
  EXISTS_TAC `convex hull {vec 0:real^N,u % t % v}` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[CONVEX_HULL_2; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`&1 - inv(u * t)`; `inv(u * t)`] THEN
    REWRITE_TAC[REAL_ARITH `&1 - x + x = &1`; REAL_SUB_LE; REAL_LE_INV_EQ] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_ENTIRE; REAL_MUL_LINV;
                 REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LID]] THEN
  SUBGOAL_THEN
   `(u % t % v:real^N) IN (p DIFF relative_interior p)`
  MP_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[RELATIVE_INTERIOR_OF_POLYHEDRON] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `x IN s DIFF (s DIFF t) ==> x IN t`)) THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(SET_RULE
     `(?s. s IN f /\ t SUBSET s) ==> t SUBSET UNIONS f`) THEN
    REWRITE_TAC[EXISTS_IN_GSPEC] THEN EXISTS_TAC `f:real^N->bool` THEN
    ASM_SIMP_TAC[SUBSET_HULL; CONVEX_CONVEX_HULL] THEN
    ASM_SIMP_TAC[HULL_INC; IN_UNION; INSERT_SUBSET; EMPTY_SUBSET]] THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_RELATIVE_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_INTER; dist] THEN
  ABBREV_TAC `k = min (e / &2 / norm(t % v:real^N)) (&1 - u)` THEN
  SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[REAL_LT_MIN] THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_HALF; NORM_POS_LT; VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(u + k) % t % v:real^N`) THEN
  REWRITE_TAC[VECTOR_ARITH `u % x - (u + k) % x:real^N = --k % x`] THEN
  ONCE_REWRITE_TAC[NORM_MUL] THEN REWRITE_TAC[REAL_ABS_NEG; NOT_IMP] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; NORM_POS_LT; VECTOR_MUL_EQ_0;
                 REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE] THEN
    EXPAND_TAC "k" THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC] THEN
    REPEAT(MATCH_MP_TAC SPAN_MUL) THEN ASM_SIMP_TAC[SPAN_SUPERSET];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u + k:real`) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= u /\ &0 < x /\ x <= &1 - u
      ==> (&0 <= u + x /\ u + x <= &1) /\ ~(u + x <= u)`) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "k" THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Finitely generated cone is polyhedral, and hence closed.                  *)
(* ------------------------------------------------------------------------- *)

let POLYHEDRON_CONVEX_CONE_HULL = prove
 (`!s:real^N->bool. FINITE s ==> polyhedron(convex_cone hull s)`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN DISCH_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_CONE_HULL_EMPTY] THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_POLYHEDRON; POLYTOPE_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `polyhedron(convex hull ((vec 0:real^N) INSERT s))`
  MP_TAC THENL
   [MATCH_MP_TAC POLYTOPE_IMP_POLYHEDRON THEN
    REWRITE_TAC[polytope] THEN ASM_MESON_TAC[FINITE_INSERT];
    REWRITE_TAC[polyhedron] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SKOLEM_THM; RIGHT_IMP_EXISTS_THM]) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `a:(real^N->bool)->real^N` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_TAC `b:(real^N->bool)->real`)] THEN
  SUBGOAL_THEN `~(f:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM(MP_TAC o
     GEN_REWRITE_RULE RAND_CONV [INTERS_0]) THEN
    DISCH_THEN(MP_TAC o AP_TERM `bounded:(real^N->bool)->bool`) THEN
    ASM_SIMP_TAC[NOT_BOUNDED_UNIV; BOUNDED_CONVEX_HULL; FINITE_IMP_BOUNDED;
                 FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  EXISTS_TAC `{h:real^N->bool | h IN f /\ b h = &0}` THEN
  ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `h:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC
     [`(a:(real^N->bool)->real^N) h`; `(b:(real^N->bool)->real) h`] THEN
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `convex hull ((vec 0:real^N) INSERT s)` THEN CONJ_TAC THENL
       [SIMP_TAC[SUBSET; HULL_INC; IN_INSERT]; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> INTERS t SUBSET INTERS s`) THEN
      SET_TAC[];
      MATCH_MP_TAC CONVEX_CONE_INTERS THEN
      X_GEN_TAC `h:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
      REWRITE_TAC[CONVEX_CONE_HALFSPACE_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTERS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!h:real^N->bool. h IN f ==> ?t. &0 < t /\ (t % x) IN h`
  MP_TAC THENL
   [X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(b:(real^N->bool)->real) h = &0` THENL
     [EXISTS_TAC `&1` THEN ASM_SIMP_TAC[REAL_LT_01; VECTOR_MUL_LID];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (b:(real^N->bool)->real) h` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_LE] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
      DISCH_THEN(MP_TAC o SPEC `vec 0:real^N`) THEN
      SIMP_TAC[HULL_INC; IN_INSERT; IN_INTERS] THEN
      DISCH_THEN(MP_TAC o SPEC `h:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `h = {x:real^N | a h dot x <= b h}`
       (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th])
      THENL [ASM_MESON_TAC[]; REWRITE_TAC[IN_ELIM_THM; DOT_RZERO]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(vec 0:real^N) IN interior h` MP_TAC THENL
     [SUBGOAL_THEN `h = {x:real^N | a h dot x <= b h}` SUBST1_TAC THENL
       [ASM_MESON_TAC[];
        ASM_SIMP_TAC[INTERIOR_HALFSPACE_LE; IN_ELIM_THM; DOT_RZERO]];
      REWRITE_TAC[IN_INTERIOR; SUBSET; IN_BALL_0; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `e:real` THEN STRIP_TAC THEN
      ASM_CASES_TAC `x:real^N = vec 0` THENL
       [EXISTS_TAC `&1` THEN
        ASM_SIMP_TAC[VECTOR_MUL_RZERO; REAL_LT_01; NORM_0];
        EXISTS_TAC `e / &2 / norm(x:real^N)` THEN
        ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; NORM_POS_LT] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_NORM] THEN
        ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `t:(real^N->bool)->real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `x:real^N = inv(inf(IMAGE t (f:(real^N->bool)->bool))) %
                           inf(IMAGE t f) % x`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_MUL_LID] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_LINV THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE];
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[conic] CONIC_CONVEX_CONE_HULL) THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_INF_FINITE; FINITE_IMAGE;
               IMAGE_EQ_EMPTY; REAL_LT_IMP_LE; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC(SET_RULE `!s t. s SUBSET t /\ x IN s ==> x IN t`) THEN
  EXISTS_TAC `convex hull ((vec 0:real^N) INSERT s)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[CONVEX_CONVEX_CONE_HULL] THEN
    ASM_SIMP_TAC[INSERT_SUBSET; HULL_SUBSET; CONVEX_CONE_HULL_CONTAINS_0];
    ASM_REWRITE_TAC[IN_INTERS] THEN X_GEN_TAC `h:real^N->bool` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `inf(IMAGE (t:(real^N->bool)->real) f) % x:real^N =
                  (&1 - inf(IMAGE t f) / t h) % vec 0 +
                  (inf(IMAGE t f) / t h) % t h % x`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_RZERO; VECTOR_ADD_LID;
                   REAL_DIV_RMUL; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    MATCH_MP_TAC IN_CONVEX_SET THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_INF_LE_FINITE; REAL_LE_INF_FINITE;
                 FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `h = {x:real^N | a h dot x <= b h}` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ASM_SIMP_TAC[CONVEX_HALFSPACE_LE]];
      SUBGOAL_THEN `(vec 0:real^N) IN convex hull (vec 0 INSERT s)` MP_TAC
      THENL [SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_INTERS] THEN ASM_MESON_TAC[];
      ASM SET_TAC[REAL_LE_REFL]]]);;

let CLOSED_CONVEX_CONE_HULL = prove
 (`!s:real^N->bool. FINITE s ==> closed(convex_cone hull s)`,
  MESON_TAC[POLYHEDRON_IMP_CLOSED; POLYHEDRON_CONVEX_CONE_HULL]);;

(* ------------------------------------------------------------------------- *)
(* And conversely, a polyhedral cone is finitely generated.                  *)
(* ------------------------------------------------------------------------- *)

let FINITELY_GENERATED_CONIC_POLYHEDRON = prove
 (`!s:real^N->bool.
        polyhedron s /\ conic s /\ ~(s = {})
        ==> ?c. FINITE c /\ s = convex_cone hull c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?p:real^N->bool. polytope p /\ vec 0 IN interior p`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `interval[--vec 1:real^N,vec 1:real^N]` THEN
    REWRITE_TAC[POLYTOPE_INTERVAL; INTERIOR_CLOSED_INTERVAL] THEN
    SIMP_TAC[IN_INTERVAL; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `polytope(s INTER p:real^N->bool)` MP_TAC THENL
   [REWRITE_TAC[POLYTOPE_EQ_BOUNDED_POLYHEDRON] THEN
    ASM_SIMP_TAC[BOUNDED_INTER; POLYTOPE_IMP_BOUNDED]THEN
    ASM_SIMP_TAC[POLYHEDRON_INTER; POLYTOPE_IMP_POLYHEDRON];
    REWRITE_TAC[polytope] THEN MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[SUBSET_HULL; POLYHEDRON_IMP_CONVEX; convex_cone] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s INTER p:real^N->bool` THEN
    REWRITE_TAC[INTER_SUBSET] THEN ASM_REWRITE_TAC[HULL_SUBSET]] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?t. &0 < t /\ (t % x:real^N) IN p` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
    REWRITE_TAC[SUBSET; IN_BALL_0; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `x:real^N = vec 0` THENL
     [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO; REAL_LT_01] THEN
      ASM_SIMP_TAC[NORM_0];
      EXISTS_TAC `e / &2 / norm(x:real^N)` THEN
      ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; NORM_POS_LT] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; REAL_ABS_NUM] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `x:real^N = inv t % t % x` SUBST1_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID;
                 REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[conic] CONIC_CONVEX_CONE_HULL) THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC(SET_RULE `!s. x IN s /\ s SUBSET t ==> x IN t`) THEN
  EXISTS_TAC `convex hull c:real^N->bool` THEN
  REWRITE_TAC[CONVEX_HULL_SUBSET_CONVEX_CONE_HULL] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [conic]) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* The notion of n-simplex where n is an integer >= -1.                      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("simplex",(12,"right"));;

let simplex = new_definition
 `n simplex s <=> ?c. ~(affine_dependent c) /\
                      &(CARD c):int = n + &1 /\
                      s = convex hull c`;;

let SIMPLEX = prove
 (`n simplex s <=> ?c. FINITE c /\
                       ~(affine_dependent c) /\
                       &(CARD c):int = n + &1 /\
                       s = convex hull c`,
  REWRITE_TAC[simplex] THEN MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]);;

let CONVEX_SIMPLEX = prove
 (`!n s. n simplex s ==> convex s`,
  REWRITE_TAC[simplex] THEN MESON_TAC[CONVEX_CONVEX_HULL]);;

let COMPACT_SIMPLEX = prove
 (`!n s. n simplex s ==> compact s`,
  REWRITE_TAC[SIMPLEX] THEN
  MESON_TAC[FINITE_IMP_COMPACT; COMPACT_CONVEX_HULL]);;

let AFF_DIM_SIMPLEX = prove
 (`!n s. n simplex s ==> aff_dim s = n`,
  REWRITE_TAC[simplex] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (INT_ARITH
   `c:int = n + &1 ==> n = c - &1`)) THEN
  MATCH_MP_TAC AFF_DIM_UNIQUE THEN ASM_REWRITE_TAC[]);;

let SIMPLEX_IMP_POLYTOPE = prove
 (`!n s. n simplex s ==> polytope s`,
  REWRITE_TAC[simplex; polytope] THEN
  MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]);;

let SIMPLEX_DIM_GE = prove
 (`!n s. n simplex s ==> -- &1 <= n`,
  REWRITE_TAC[simplex] THEN INT_ARITH_TAC);;

let SIMPLEX_EMPTY = prove
 (`!n. n simplex {} <=> n = -- &1`,
  GEN_TAC THEN REWRITE_TAC[SIMPLEX] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES; AFFINE_INDEPENDENT_EMPTY] THEN
  INT_ARITH_TAC);;

let SIMPLEX_MINUS_1 = prove
 (`!s. (-- &1) simplex s <=> s = {}`,
  GEN_TAC THEN REWRITE_TAC[SIMPLEX; INT_ADD_LINV; INT_OF_NUM_EQ] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b <=> ~(a ==> ~b)`] THEN
  SIMP_TAC[CARD_EQ_0] THEN REWRITE_TAC[NOT_IMP] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> c /\ a /\ b /\ d`] THEN
  REWRITE_TAC[UNWIND_THM2; FINITE_EMPTY; AFFINE_INDEPENDENT_EMPTY] THEN
  REWRITE_TAC[CONVEX_HULL_EMPTY]);;

let AFF_DIM_SIMPLEX = prove
 (`!s n. n simplex s ==> aff_dim s = n`,
  REWRITE_TAC[simplex; INT_ARITH `x:int = n + &1 <=> n = x - &1`] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT]);;

let SIMPLEX_EXTREME_POINTS = prove
 (`!n s:real^N->bool.
       n simplex s
       ==> FINITE {v | v extreme_point_of s} /\
           ~(affine_dependent {v | v extreme_point_of s}) /\
           &(CARD {v | v extreme_point_of s}) = n + &1 /\
           s = convex hull {v | v extreme_point_of s}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SIMPLEX; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `c:real^N->bool` THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  SUBGOAL_THEN `{v:real^N | v extreme_point_of s} = c`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t /\ ~(s PSUBSET t) ==> s = t`) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; EXTREME_POINT_OF_CONVEX_HULL] THEN
  ABBREV_TAC `c' = {v:real^N | v extreme_point_of (convex hull c)}` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `convex hull c:real^N->bool = convex hull c'` ASSUME_TAC THENL
   [EXPAND_TAC "c'" THEN MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL] THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
    ASM_MESON_TAC[HAS_SIZE; FINITE_IMP_COMPACT];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PSUBSET_MEMBER]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [affine_dependent]) THEN
    REWRITE_TAC[] THEN EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a:real^N) IN convex hull c'` MP_TAC THENL
     [ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
      CONVEX_HULL_SUBSET_AFFINE_HULL)) THEN
    SUBGOAL_THEN `c' SUBSET (c DELETE (a:real^N))` MP_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[HULL_MONO; SUBSET]]]);;

let SIMPLEX_FACE_OF_SIMPLEX = prove
 (`!n s f:real^N->bool.
        n simplex s /\ f face_of s ==> ?m. m <= n /\ m simplex f`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SIMPLEX]) THEN
  REWRITE_TAC[HAS_SIZE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `?c':real^N->bool. c' SUBSET c /\ f = convex hull c'`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_SUBSET; FINITE_IMP_COMPACT]; ALL_TAC] THEN
  EXISTS_TAC `&(CARD(c':real^N->bool)) - &1:int` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CARD_SUBSET)) THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC;
    REWRITE_TAC[simplex] THEN EXISTS_TAC `c':real^N->bool` THEN
    ASM_REWRITE_TAC[INT_ARITH `a - &1 + &1:int = a`] THEN
    ASM_MESON_TAC[AFFINE_DEPENDENT_MONO]]);;

let FACE_OF_SIMPLEX_SUBSET = prove
 (`!n s f:real^N->bool.
        n simplex s /\ f face_of s
        ==> ?c. c SUBSET {x | x extreme_point_of s} /\ f = convex hull c`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SIMPLEX_EXTREME_POINTS) THEN
  ABBREV_TAC `c = {x:real^N | x extreme_point_of s}` THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_MESON_TAC[FACE_OF_CONVEX_HULL_SUBSET; FINITE_IMP_COMPACT]);;

let SUBSET_FACE_OF_SIMPLEX = prove
 (`!s n c:real^N->bool.
      n simplex s /\ c SUBSET {x | x extreme_point_of s}
      ==> (convex hull c) face_of s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SIMPLEX_EXTREME_POINTS) THEN
  REWRITE_TAC[HAS_SIZE] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC FACE_OF_CONVEX_HULLS THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `!t. u SUBSET t /\ DISJOINT s t ==> DISJOINT s u`) THEN
  EXISTS_TAC `affine hull ({v:real^N | v extreme_point_of s} DIFF c)` THEN
  REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
  MATCH_MP_TAC DISJOINT_AFFINE_HULL THEN
  EXISTS_TAC `{v:real^N | v extreme_point_of s}` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let FACES_OF_SIMPLEX = prove
 (`!n s. n simplex s
         ==> {f | f face_of s} =
             {convex hull c | c SUBSET {v | v extreme_point_of s}}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[FACE_OF_SIMPLEX_SUBSET; SUBSET_FACE_OF_SIMPLEX]);;

let HAS_SIZE_FACES_OF_SIMPLEX = prove
 (`!n s:real^N->bool.
        n simplex s
        ==> {f | f face_of s} HAS_SIZE 2 EXP (num_of_int(n + &1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP FACES_OF_SIMPLEX) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GSYM o MATCH_MP SIMPLEX_EXTREME_POINTS) THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ];
    MATCH_MP_TAC HAS_SIZE_POWERSET THEN
    ASM_REWRITE_TAC[HAS_SIZE; NUM_OF_INT_OF_NUM]] THEN
  SUBGOAL_THEN
   `!a b. a SUBSET {v:real^N | v extreme_point_of s} /\
          b SUBSET {v | v extreme_point_of s} /\
          convex hull a SUBSET convex hull b
          ==> a SUBSET b`
   (fun th -> MESON_TAC[th]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [affine_dependent]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `!s t u. x IN s /\ s SUBSET t /\ t SUBSET u /\ u SUBSET v ==> x IN v`) THEN
  MAP_EVERY EXISTS_TAC
   [`convex hull a:real^N->bool`; `convex hull b:real^N->bool`;
    `affine hull b:real^N->bool`] THEN
  ASM_SIMP_TAC[HULL_INC; CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
  MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]);;

let FINITE_FACES_OF_SIMPLEX = prove
 (`!n s. n simplex s ==> FINITE {f | f face_of s}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_SIZE_FACES_OF_SIMPLEX) THEN
  SIMP_TAC[HAS_SIZE]);;

let CARD_FACES_OF_SIMPLEX = prove
 (`!n s. n simplex s ==> CARD {f | f face_of s} = 2 EXP (num_of_int(n + &1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_SIZE_FACES_OF_SIMPLEX) THEN
  SIMP_TAC[HAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Simplicial complexes and triangulations.                                  *)
(* ------------------------------------------------------------------------- *)

let simplicial_complex = new_definition
 `simplicial_complex c <=>
        FINITE c /\
        (!s. s IN c ==> ?n. n simplex s) /\
        (!f s. s IN c /\ f face_of s ==> f IN c) /\
        (!s s'. s IN c /\ s' IN c
                ==> (s INTER s') face_of s /\ (s INTER s') face_of s')`;;

let triangulation = new_definition
 `triangulation(tr:(real^N->bool)->bool) <=>
        FINITE tr /\
        (!t. t IN tr ==> ?n. n simplex t) /\
        (!t t'. t IN tr /\ t' IN tr
                ==> (t INTER t') face_of t /\ (t INTER t') face_of t')`;;

let TRIANGULATION_INTER_SIMPLEX = prove
 (`!tr t t':real^N->bool.
        triangulation tr /\ t IN tr /\ t' IN tr
        ==> t INTER t' = convex hull ({x | x extreme_point_of t} INTER
                                      {x | x extreme_point_of t'})`,
  REWRITE_TAC[triangulation] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real^N->bool`; `t':real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MAP_EVERY (MP_TAC o C SPEC th)
   [`t:real^N->bool`; `t':real^N->bool`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m:int` THEN DISCH_TAC THEN X_GEN_TAC `n:int` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`m:int`; `t':real^N->bool`;
                 `t INTER t':real^N->bool`] FACE_OF_SIMPLEX_SUBSET) THEN
  MP_TAC(ISPECL [`n:int`; `t:real^N->bool`;
                 `t INTER t':real^N->bool`] FACE_OF_SIMPLEX_SUBSET) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool` (STRIP_ASSUME_TAC o GSYM)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d':real^N->bool` (STRIP_ASSUME_TAC o GSYM)) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HULL_MINIMAL THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[CONVEX_INTER; CONVEX_SIMPLEX]] THEN
    SIMP_TAC[SUBSET; IN_INTER; IN_ELIM_THM; extreme_point_of]] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `convex hull {x:real^N | x extreme_point_of (t INTER t')}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE `s = t ==> s SUBSET t`) THEN
    MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
    ASM_MESON_TAC[COMPACT_INTER; CONVEX_INTER; COMPACT_SIMPLEX; CONVEX_SIMPLEX];
    MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `convex hull d:real^N->bool = t INTER t'`));
      SUBST1_TAC(SYM(ASSUME `convex hull d':real^N->bool = t INTER t'`))] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP EXTREME_POINT_OF_CONVEX_HULL) THEN
    ASM SET_TAC[]]);;

let TRIANGULATION_SIMPLICIAL_COMPLEX = prove
 (`!tr. triangulation tr
        ==> simplicial_complex {f:real^N->bool | ?t. t IN tr /\ f face_of t}`,
  let lemma = prove
   (`!s t t'. t face_of s /\ t SUBSET s' /\ s' SUBSET s ==> t face_of s'`,
    REWRITE_TAC[face_of; SUBSET] THEN MESON_TAC[])
  and lemma' = prove
   (`{f | ?t. t IN tr /\ P f t} = UNIONS (IMAGE (\t. {f | P f t}) tr)`,
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIONS; IN_IMAGE; LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2; IN_ELIM_THM]) in
  REWRITE_TAC[triangulation; simplicial_complex] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[lemma'] THEN ASM_SIMP_TAC[FINITE_UNIONS; FINITE_IMAGE] THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[FINITE_FACES_OF_SIMPLEX];
    ASM_MESON_TAC[SIMPLEX_FACE_OF_SIMPLEX];
    ASM_MESON_TAC[FACE_OF_TRANS];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(GEN_ALL lemma) THENL
   [EXISTS_TAC `t:real^N->bool`; EXISTS_TAC `t':real^N->bool`] THEN
  ASM_SIMP_TAC[INTER_SUBSET; FACE_OF_IMP_SUBSET] THEN
  (SUBGOAL_THEN
    `?c. c SUBSET {x:real^N | x extreme_point_of t} INTER
                  {x | x extreme_point_of t'} /\
         f INTER f' = convex hull c`
   STRIP_ASSUME_TAC THENL
    [ALL_TAC;
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_FACE_OF_SIMPLEX THEN
     ASM SET_TAC[]] THEN
   MATCH_MP_TAC FACE_OF_CONVEX_HULL_SUBSET THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC FINITE_IMP_COMPACT THEN MATCH_MP_TAC FINITE_INTER THEN
     DISJ1_TAC THEN
     FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(t:real^N->bool) IN tr`)) THEN
     DISCH_THEN(CHOOSE_THEN(MP_TAC o MATCH_MP SIMPLEX_EXTREME_POINTS)) THEN
     SIMP_TAC[];
     ALL_TAC] THEN
   MP_TAC(ISPECL
    [`tr:(real^N->bool)->bool`; `t:real^N->bool`; `t':real^N->bool`]
         TRIANGULATION_INTER_SIMPLEX) THEN
   ASM_REWRITE_TAC[triangulation] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
   ASM_SIMP_TAC[FACE_OF_INTER_INTER]));;
