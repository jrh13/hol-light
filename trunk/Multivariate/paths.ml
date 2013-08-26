(* ========================================================================= *)
(* Paths, connectedness, homotopy, simple connectedness & contractibility.   *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

needs "Multivariate/convex.ml";;

(* ------------------------------------------------------------------------- *)
(* Paths and arcs.                                                           *)
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

let PATH_EQ = prove
 (`!p q. (!t. t IN interval[vec 0,vec 1] ==> p t = q t) /\ path p
         ==> path q`,
  REWRITE_TAC[path; CONTINUOUS_ON_EQ]);;

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

let SIMPLE_PATH_EQ_ARC = prove
 (`!g. ~(pathstart g = pathfinish g) ==> (simple_path g <=> arc g)`,
  SIMP_TAC[ARC_SIMPLE_PATH]);;

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

let PATHSTART_COMPOSE = prove
 (`!f p. pathstart(f o p) = f(pathstart p)`,
  REWRITE_TAC[pathstart; o_THM]);;

let PATHFINISH_COMPOSE = prove
 (`!f p. pathfinish(f o p) = f(pathfinish p)`,
  REWRITE_TAC[pathfinish; o_THM]);;

let PATH_IMAGE_COMPOSE = prove
 (`!f p. path_image (f o p) = IMAGE f (path_image p)`,
  REWRITE_TAC[path_image; IMAGE_o]);;

let PATH_COMPOSE_JOIN = prove
 (`!f p q. f o (p ++ q) = (f o p) ++ (f o q)`,
  REWRITE_TAC[joinpaths; o_DEF; FUN_EQ_THM] THEN MESON_TAC[]);;

let PATH_COMPOSE_REVERSEPATH = prove
 (`!f p. f o reversepath p = reversepath(f o p)`,
  REWRITE_TAC[reversepath; o_DEF; FUN_EQ_THM] THEN MESON_TAC[]);;

let JOIN_PATHS_EQ = prove
 (`!p q:real^1->real^N.
   (!t. t IN interval[vec 0,vec 1] ==> p t = p' t) /\
   (!t. t IN interval[vec 0,vec 1] ==> q t = q' t)
   ==> !t. t IN interval[vec 0,vec 1] ==> (p ++ q) t = (p' ++ q') t`,
  REWRITE_TAC[joinpaths; IN_INTERVAL_1; DROP_VEC] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_SUB; DROP_VEC] THEN
  ASM_REAL_ARITH_TAC);;

let CARD_EQ_SIMPLE_PATH_IMAGE = prove
 (`!g. simple_path g ==> path_image g =_c (:real)`,
  SIMP_TAC[CONNECTED_CARD_EQ_IFF_NONTRIVIAL; CONNECTED_SIMPLE_PATH_IMAGE] THEN
  GEN_TAC THEN REWRITE_TAC[simple_path; path_image] THEN MATCH_MP_TAC(SET_RULE
   `(?u v. u IN s /\ v IN s /\ ~(u = a) /\ ~(v = a) /\ ~(u = v))
    ==> P /\ (!x y. x IN s /\ y IN s /\ f x = f y
                    ==> x = y \/ x = a /\ y = b \/ x = b /\ y = a)
        ==> ~(?c. IMAGE f s SUBSET {c})`) THEN
  MAP_EVERY EXISTS_TAC [`lift(&1 / &3)`; `lift(&1 / &2)`] THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; GSYM LIFT_NUM; LIFT_EQ] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let INFINITE_SIMPLE_PATH_IMAGE = prove
 (`!g. simple_path g ==> INFINITE(path_image g)`,
  MESON_TAC[CARD_EQ_SIMPLE_PATH_IMAGE; INFINITE; FINITE_IMP_COUNTABLE;
            UNCOUNTABLE_REAL; CARD_COUNTABLE_CONG]);;

let CARD_EQ_ARC_IMAGE = prove
 (`!g. arc g ==> path_image g =_c (:real)`,
  MESON_TAC[ARC_IMP_SIMPLE_PATH; CARD_EQ_SIMPLE_PATH_IMAGE]);;

let INFINITE_ARC_IMAGE = prove
 (`!g. arc g ==> INFINITE(path_image g)`,
  MESON_TAC[ARC_IMP_SIMPLE_PATH; INFINITE_SIMPLE_PATH_IMAGE]);;

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
 (`!g1 g2. pathfinish g1 = pathstart g2
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

let ARC_JOIN_EQ = prove
 (`!g1 g2:real^1->real^N.
        pathfinish g1 = pathstart g2
        ==> (arc(g1 ++ g2) <=>
             arc g1 /\ arc g2 /\
             path_image g1 INTER path_image g2 SUBSET {pathstart g2})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[ARC_JOIN] THEN
  GEN_REWRITE_TAC LAND_CONV [ARC_SIMPLE_PATH] THEN
  REWRITE_TAC[PATHFINISH_JOIN; PATHSTART_JOIN] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g1:real^1->real^N`; `g2:real^1->real^N`]
        SIMPLE_PATH_JOIN_IMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((pathstart g1:real^N) IN path_image g2)`
   (fun th -> MP_TAC th THEN ASM SET_TAC[]) THEN
  REWRITE_TAC[path_image; IN_IMAGE; IN_INTERVAL_1; DROP_VEC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_path]) THEN
  DISCH_THEN(MP_TAC o SPECL [`vec 0:real^1`; `lift(&1 / &2) + inv(&2) % u`] o
    CONJUNCT2) THEN
  REWRITE_TAC[GSYM DROP_EQ; IN_INTERVAL_1; DROP_ADD; DROP_VEC;
              DROP_CMUL; LIFT_DROP; joinpaths] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_IMP_NZ;
               REAL_ARITH `&0 <= x ==> &0 < &1 / &2 + &1 / &2 * x`] THEN
  REWRITE_TAC[REAL_ARITH `&1 / &2 + &1 / &2 * u = &1 <=> u = &1`] THEN
  ASM_SIMP_TAC[REAL_ARITH
   `&0 <= u ==> (&1 / &2 + &1 / &2 * u <= &1 / &2 <=> u = &0)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
  ASM_SIMP_TAC[REAL_ARITH `u <= &1 ==> &1 / &2 + &1 / &2 * u <= &1`] THEN
  REWRITE_TAC[GSYM LIFT_EQ; LIFT_NUM; LIFT_DROP] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID; GSYM LIFT_CMUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LIFT_NUM] THEN
    ASM_REWRITE_TAC[VEC_EQ] THEN ARITH_TAC;
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; GSYM LIFT_CMUL] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[LIFT_NUM; VECTOR_MUL_LID; VECTOR_ADD_SUB] THEN
    ASM_MESON_TAC[]]);;

let ARC_JOIN_EQ_ALT = prove
 (`!g1 g2:real^1->real^N.
        pathfinish g1 = pathstart g2
        ==> (arc(g1 ++ g2) <=>
             arc g1 /\ arc g2 /\
             path_image g1 INTER path_image g2 = {pathstart g2})`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ARC_JOIN_EQ] THEN
  MP_TAC(ISPEC `g1:real^1->real^N` PATHFINISH_IN_PATH_IMAGE) THEN
  MP_TAC(ISPEC `g2:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Reassociating a joined path doesn't matter for various properties.        *)
(* ------------------------------------------------------------------------- *)

let PATH_ASSOC = prove
 (`!p q r:real^1->real^N.
        pathfinish p = pathstart q /\ pathfinish q = pathstart r
        ==> (path(p ++ (q ++ r)) <=> path((p ++ q) ++ r))`,
  SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN] THEN CONV_TAC TAUT);;

let SIMPLE_PATH_ASSOC = prove
 (`!p q r:real^1->real^N.
        pathfinish p = pathstart q /\ pathfinish q = pathstart r
        ==> (simple_path(p ++ (q ++ r)) <=> simple_path((p ++ q) ++ r))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `pathstart(p:real^1->real^N) = pathfinish r` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[SIMPLE_PATH_EQ_ARC; PATHSTART_JOIN; PATHFINISH_JOIN]] THEN
  ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_JOIN; PATHFINISH_JOIN;
               ARC_JOIN_EQ; PATH_IMAGE_JOIN] THEN
  MAP_EVERY ASM_CASES_TAC
   [`arc(p:real^1->real^N)`; `arc(q:real^1->real^N)`;
    `arc(r:real^1->real^N)`] THEN
  ASM_REWRITE_TAC[UNION_OVER_INTER; UNION_SUBSET;
                  ONCE_REWRITE_RULE[INTER_COMM] UNION_OVER_INTER] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP ARC_DISTINCT_ENDS)) THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t PATHSTART_IN_PATH_IMAGE) THEN
                      MP_TAC(ISPEC t PATHFINISH_IN_PATH_IMAGE))
   [`p:real^1->real^N`; `q:real^1->real^N`; `r:real^1->real^N`] THEN
  ASM SET_TAC[]);;

let ARC_ASSOC = prove
 (`!p q r:real^1->real^N.
        pathfinish p = pathstart q /\ pathfinish q = pathstart r
        ==> (arc(p ++ (q ++ r)) <=> arc((p ++ q) ++ r))`,
  SIMP_TAC[ARC_SIMPLE_PATH; SIMPLE_PATH_ASSOC] THEN
  SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN]);;

(* ------------------------------------------------------------------------- *)
(* In the case of a loop, neither does symmetry.                             *)
(* ------------------------------------------------------------------------- *)

let PATH_SYM = prove
 (`!p q. pathfinish p = pathstart q /\ pathfinish q = pathstart p
         ==> (path(p ++ q) <=> path(q ++ p))`,
  SIMP_TAC[PATH_JOIN; CONJ_ACI]);;

let SIMPLE_PATH_SYM = prove
 (`!p q. pathfinish p = pathstart q /\ pathfinish q = pathstart p
         ==> (simple_path(p ++ q) <=> simple_path(q ++ p))`,
  SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; INTER_ACI; CONJ_ACI; INSERT_AC]);;

let PATH_IMAGE_SYM = prove
 (`!p q. pathfinish p = pathstart q /\ pathfinish q = pathstart p
         ==> path_image(p ++ q) = path_image(q ++ p)`,
  SIMP_TAC[PATH_IMAGE_JOIN; UNION_ACI]);;

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
 (`!f t g. linear f ==> shiftpath t (f o g) = f o shiftpath t g`,
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
 (`!u v.
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

let REVERSEPATH_SUBPATH = prove
 (`!g u v. reversepath(subpath u v g) = subpath v u g`,
  REWRITE_TAC[reversepath; subpath; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[DROP_SUB; VECTOR_SUB_LDISTRIB] THEN
  REWRITE_TAC[GSYM LIFT_EQ_CMUL; LIFT_SUB; LIFT_DROP] THEN
  VECTOR_ARITH_TAC);;

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

let ARC_SUBPATH_ARC = prove
 (`!u v g. arc g /\
           u IN interval [vec 0,vec 1] /\ v IN interval [vec 0,vec 1] /\
           ~(u = v)
           ==> arc(subpath u v g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
  ASM_MESON_TAC[ARC_IMP_SIMPLE_PATH; arc]);;

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

let JOIN_SUBPATHS_MIDDLE = prove
 (`!p:real^1->real^N.
   subpath (vec 0) (lift(&1 / &2)) p ++ subpath (lift(&1 / &2)) (vec 1) p = p`,
  REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[joinpaths; subpath] THEN COND_CASES_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_SUB; DROP_CMUL; LIFT_DROP;
              DROP_VEC] THEN
  REAL_ARITH_TAC);;

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
    ASM_SIMP_TAC[GSYM path; GSYM closed; SIMPLE_PATH_IMP_PATH];
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

let SIMPLE_PATH_LINEPATH_EQ = prove
 (`!a b:real^N. simple_path(linepath(a,b)) <=> ~(a = b)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[SIMPLE_PATH_LINEPATH] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[simple_path] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[linepath; GSYM VECTOR_ADD_RDISTRIB] THEN
  DISCH_THEN(MP_TAC o SPECL [`lift(&0)`; `lift(&1 / &2)`]) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; GSYM DROP_EQ; DROP_VEC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let ARC_LINEPATH_EQ = prove
 (`!a b. arc(linepath(a,b)) <=> ~(a = b)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[ARC_LINEPATH] THEN
  MESON_TAC[SIMPLE_PATH_LINEPATH_EQ; ARC_IMP_SIMPLE_PATH]);;

let LINEPATH_REFL = prove
 (`!a. linepath(a,a) = \x. a`,
  REWRITE_TAC[linepath; VECTOR_ARITH `(&1 - u) % x + u % x:real^N = x`]);;

let SHIFTPATH_TRIVIAL = prove
 (`!t a. shiftpath t (linepath(a,a)) = linepath(a,a)`,
  REWRITE_TAC[shiftpath; LINEPATH_REFL; COND_ID]);;

let SUBPATH_REFL = prove
 (`!g a. subpath a a g = linepath(g a,g a)`,
  REWRITE_TAC[subpath; linepath; VECTOR_SUB_REFL; DROP_VEC; VECTOR_MUL_LZERO;
              FUN_EQ_THM; VECTOR_ADD_RID] THEN
  VECTOR_ARITH_TAC);;

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
(* Homeomorphisms of arc images.                                             *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHISM_ARC = prove
 (`!g:real^1->real^N.
     arc g ==> ?h. homeomorphism (interval[vec 0,vec 1],path_image g) (g,h)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
  ASM_REWRITE_TAC[path_image; COMPACT_INTERVAL; GSYM path; GSYM arc]);;

let HOMEOMORPHIC_ARC_IMAGE_INTERVAL = prove
 (`!g:real^1->real^N a b:real^1.
      arc g /\ drop a < drop b ==> (path_image g) homeomorphic interval[a,b]`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC HOMEOMORPHIC_TRANS `interval[vec 0:real^1,vec 1]` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    EXISTS_TAC `g:real^1->real^N` THEN ASM_SIMP_TAC[HOMEOMORPHISM_ARC];
    MATCH_MP_TAC HOMEOMORPHIC_CLOSED_INTERVALS THEN
    ASM_REWRITE_TAC[INTERVAL_NE_EMPTY_1; DROP_VEC; REAL_LT_01]]);;

let HOMEOMORPHIC_ARC_IMAGES = prove
 (`!g:real^1->real^M h:real^1->real^N.
        arc g /\ arc h ==> (path_image g) homeomorphic (path_image h)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC HOMEOMORPHIC_TRANS `interval[vec 0:real^1,vec 1]` THEN
  CONJ_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM]] THEN
  MATCH_MP_TAC HOMEOMORPHIC_ARC_IMAGE_INTERVAL THEN
  ASM_REWRITE_TAC[DROP_VEC; REAL_LT_01]);;

let HOMEOMORPHIC_ARC_IMAGE_SEGMENT = prove
 (`!g:real^1->real^N a b:real^M.
        arc g /\ ~(a = b) ==> (path_image g) homeomorphic segment[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM PATH_IMAGE_LINEPATH] THEN
  MATCH_MP_TAC HOMEOMORPHIC_ARC_IMAGES THEN
  ASM_REWRITE_TAC[ARC_LINEPATH_EQ]);;

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

let PATH_COMPONENT_SYM_EQ = prove
 (`!s x y. path_component s x y <=> path_component s y x`,
  MESON_TAC[PATH_COMPONENT_SYM]);;

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

let UNIONS_PATH_COMPONENT = prove
 (`!s:real^N->bool. UNIONS {path_component s x |x| x IN s} = s`,
  GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; PATH_COMPONENT_SUBSET] THEN
  REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `x:real^N` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN
  ASM_REWRITE_TAC[PATH_COMPONENT_REFL_EQ]);;

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

let PATH_COMPONENT = prove
 (`!s x y:real^N.
        path_component s x y <=>
        ?t. path_connected t /\ t SUBSET s /\ x IN t /\ y IN t`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `path_component s (x:real^N)` THEN
    REWRITE_TAC[PATH_CONNECTED_PATH_COMPONENT; PATH_COMPONENT_SUBSET] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PATH_COMPONENT_IN) THEN
    ASM_SIMP_TAC[IN; PATH_COMPONENT_REFL_EQ];
    REWRITE_TAC[path_component] THEN ASM_MESON_TAC[path_connected; SUBSET]]);;

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

let PATH_COMPONENT_EQ_EQ = prove
 (`!s x y:real^N.
        path_component s x = path_component s y <=>
        ~(x IN s) /\ ~(y IN s) \/
        x IN s /\ y IN s /\ path_component s x y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(y:real^N) IN s` THENL
   [ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN
      ASM_MESON_TAC[PATH_COMPONENT_TRANS; PATH_COMPONENT_REFL;
                    PATH_COMPONENT_SYM];
      ASM_MESON_TAC[PATH_COMPONENT_EQ_EMPTY]];
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM PATH_COMPONENT_EQ_EMPTY]) THEN
    ASM_REWRITE_TAC[PATH_COMPONENT_EQ_EMPTY] THEN
    ONCE_REWRITE_TAC[PATH_COMPONENT_SYM_EQ] THEN
    ASM_REWRITE_TAC[EMPTY] THEN ASM_MESON_TAC[PATH_COMPONENT_EQ_EMPTY]]);;

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

let IS_INTERVAL_PATH_CONNECTED = prove
 (`!s. is_interval s ==> path_connected s`,
  SIMP_TAC[CONVEX_IMP_PATH_CONNECTED; IS_INTERVAL_CONVEX]);;

let PATH_CONNECTED_INTERVAL = prove
 (`(!a b:real^N. path_connected(interval[a,b])) /\
   (!a b:real^N. path_connected(interval(a,b)))`,
  SIMP_TAC[IS_INTERVAL_PATH_CONNECTED; IS_INTERVAL_INTERVAL]);;

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

let PATH_CONNECTED_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        path_connected s /\ path_connected t
        ==> path_connected (s PCROSS t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PCROSS; path_connected] THEN DISCH_TAC THEN
  REWRITE_TAC[FORALL_PASTECART; IN_ELIM_PASTECART_THM] THEN
  MAP_EVERY X_GEN_TAC [`x1:real^M`; `y1:real^N`; `x2:real^M`; `y2:real^N`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(CONJUNCTS_THEN2
   (MP_TAC o SPECL [`x1:real^M`; `x2:real^M`])
   (MP_TAC o SPECL [`y1:real^N`; `y2:real^N`])) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h:real^1->real^N` THEN STRIP_TAC THEN
  X_GEN_TAC `g:real^1->real^M` THEN STRIP_TAC THEN
  EXISTS_TAC `(\t. pastecart (x1:real^M) ((h:real^1->real^N) t)) ++
              (\t. pastecart ((g:real^1->real^M) t) (y2:real^N))` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish; path]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[path_image; FORALL_IN_IMAGE; SUBSET]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_JOIN_IMP THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[path] THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
      REWRITE_TAC[path] THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
      ASM_REWRITE_TAC[pathstart; pathfinish]];
    MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN
    ASM_SIMP_TAC[path_image; FORALL_IN_IMAGE; SUBSET; IN_ELIM_PASTECART_THM];
    REWRITE_TAC[PATHSTART_JOIN] THEN ASM_REWRITE_TAC[pathstart];
    REWRITE_TAC[PATHFINISH_JOIN] THEN ASM_REWRITE_TAC[pathfinish]]);;

let PATH_CONNECTED_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        path_connected(s PCROSS t) <=>
        s = {} \/ t = {} \/ path_connected s /\ path_connected t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; PATH_CONNECTED_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; PATH_CONNECTED_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[PATH_CONNECTED_PCROSS] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
                    `(s:real^M->bool) PCROSS (t:real^N->bool)`]
       PATH_CONNECTED_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART];
    MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
                   `(s:real^M->bool) PCROSS (t:real^N->bool)`]
       PATH_CONNECTED_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART]] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

let PATH_CONNECTED_SCALING = prove
 (`!s:real^N->bool c.
        path_connected s ==> path_connected (IMAGE (\x. c % x) s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let PATH_CONNECTED_NEGATIONS = prove
 (`!s:real^N->bool.
        path_connected s ==> path_connected (IMAGE (--) s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let PATH_CONNECTED_SUMS = prove
 (`!s t:real^N->bool.
        path_connected s /\ path_connected t
        ==> path_connected {x + y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP PATH_CONNECTED_PCROSS) THEN
  DISCH_THEN(MP_TAC o ISPEC
   `\z. (fstcart z + sndcart z:real^N)` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      PATH_CONNECTED_CONTINUOUS_IMAGE)) THEN
  SIMP_TAC[CONTINUOUS_ON_ADD; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART;
           LINEAR_SNDCART; PCROSS] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; EXISTS_PASTECART] THEN
  REWRITE_TAC[PASTECART_INJ; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MESON_TAC[]);;

let IS_INTERVAL_PATH_CONNECTED_1 = prove
 (`!s:real^1->bool. is_interval s <=> path_connected s`,
  MESON_TAC[CONVEX_IMP_PATH_CONNECTED; PATH_CONNECTED_IMP_CONNECTED;
            IS_INTERVAL_CONNECTED_1; IS_INTERVAL_CONVEX_1]);;

(* ------------------------------------------------------------------------- *)
(* Bounds on components of a continuous image.                               *)
(* ------------------------------------------------------------------------- *)

let CARD_LE_PATH_COMPONENTS = prove
 (`!f:real^M->real^N s.
        f continuous_on s
        ==> {path_component (IMAGE f s) y | y | y IN IMAGE f s}
            <=_c {path_component s x | x | x IN s}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LE_C] THEN
  SIMP_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC; FORALL_IN_IMAGE] THEN EXISTS_TAC
   `\c. path_component (IMAGE (f:real^M->real^N) s) (f(@x. x IN c))` THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN EXISTS_TAC `x:real^M` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PATH_COMPONENT_EQ THEN
  REWRITE_TAC[IN] THEN ONCE_REWRITE_TAC[PATH_COMPONENT] THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) (path_component s x)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; PATH_COMPONENT_SUBSET;
                  PATH_CONNECTED_PATH_COMPONENT];
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[PATH_COMPONENT_SUBSET];
    ALL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN] THEN
  ASM_MESON_TAC[PATH_COMPONENT_REFL_EQ]);;

let CARD_LE_CONNECTED_COMPONENTS = prove
 (`!f:real^M->real^N s.
        f continuous_on s
        ==> {connected_component (IMAGE f s) y | y | y IN IMAGE f s}
            <=_c {connected_component s x | x | x IN s}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LE_C] THEN
  SIMP_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC; FORALL_IN_IMAGE] THEN EXISTS_TAC
   `\c. connected_component (IMAGE (f:real^M->real^N) s) (f(@x. x IN c))` THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN EXISTS_TAC `x:real^M` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN
  REWRITE_TAC[IN] THEN ONCE_REWRITE_TAC[connected_component] THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) (connected_component s x)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; CONNECTED_COMPONENT_SUBSET;
                  CONNECTED_CONNECTED_COMPONENT];
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[CONNECTED_COMPONENT_SUBSET];
    ALL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN] THEN
  ASM_MESON_TAC[CONNECTED_COMPONENT_REFL_EQ]);;

let CARD_LE_COMPONENTS = prove
 (`!f:real^M->real^N s.
        f continuous_on s ==> components(IMAGE f s) <=_c components s`,
  REWRITE_TAC[components; CARD_LE_CONNECTED_COMPONENTS]);;

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

let COLLINEAR_SEGMENT = prove
 (`(!a b:real^N. collinear(segment[a,b])) /\
   (!a b:real^N. collinear(segment(a,b)))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL; CONVEX_HULL_SUBSET_AFFINE_HULL];
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COLLINEAR_SUBSET) THEN
    REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED]]);;

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

let INTER_SEGMENT = prove
 (`!a b c:real^N.
        b IN segment[a,c] \/ ~collinear{a,b,c}
        ==> segment[a,b] INTER segment[b,c] = {b}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c:real^N = a` THENL
   [ASM_SIMP_TAC[SEGMENT_REFL; IN_SING; INTER_IDEMPOT; INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`{a:real^N,c}`; `b:real^N`; `{a:real^N}`; `{c:real^N}`]
        CONVEX_HULL_EXCHANGE_INTER) THEN
    ASM_REWRITE_TAC[AFFINE_INDEPENDENT_2] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[INSERT_AC]] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[SET_RULE `~(a = c) ==> {a} INTER {c} = {}`] THEN
    REWRITE_TAC[CONVEX_HULL_SING];
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `~(s INTER t = {b})
      ==> b IN s /\ b IN t
          ==> ?a. ~(a = b) /\ a IN s /\ b IN s /\ a IN t /\ b IN t`)) THEN
    ANTS_TAC THENL [REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
    REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:real^N` THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR)) THEN
    MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `d:real^N` THEN
    REPEAT(POP_ASSUM MP_TAC) THEN SIMP_TAC[INSERT_AC]]);;

let SUBSET_CONTINUOUS_IMAGE_SEGMENT_1 = prove
 (`!f:real^N->real^1 a b.
        f continuous_on segment[a,b]
        ==> segment[f a,f b] SUBSET IMAGE f (segment[a,b])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONNECTED_CONTINUOUS_IMAGE)) THEN
  REWRITE_TAC[CONNECTED_SEGMENT] THEN
  REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1; IS_INTERVAL_CONVEX_1] THEN
  REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
  MESON_TAC[IN_IMAGE; ENDS_IN_SEGMENT]);;

let CONTINUOUS_INJECTIVE_IMAGE_SEGMENT_1 = prove
 (`!f:real^N->real^1 a b.
        f continuous_on segment[a,b] /\
        (!x y. x IN segment[a,b] /\ y IN segment[a,b] /\ f x = f y ==> x = y)
        ==> IMAGE f (segment[a,b]) = segment[f a,f b]`,
  let lemma = prove
   (`!a b c:real^1.
      ~(a = b) /\ ~(a IN segment(c,b)) /\ ~(b IN segment(a,c))
      ==> c IN segment[a,b]`,
    REWRITE_TAC[FORALL_LIFT; SEGMENT_1; LIFT_DROP] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[SEGMENT_1; LIFT_EQ] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP]) THEN
    ASM_REAL_ARITH_TAC) in
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:real^1->real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^1`; `g:real^1->real^N`;
                 `segment[a:real^N,b]`]
        CONTINUOUS_ON_INVERSE) THEN
  ASM_REWRITE_TAC[COMPACT_SEGMENT] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBSET_CONTINUOUS_IMAGE_SEGMENT_1]; DISCH_TAC] THEN
  ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL] THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `c:real^N` THEN
  DISCH_TAC THEN MATCH_MP_TAC lemma THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ENDS_IN_SEGMENT]; DISCH_TAC] THEN
  ONCE_REWRITE_TAC[segment] THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->real^1`; `c:real^N`; `b:real^N`]
        SUBSET_CONTINUOUS_IMAGE_SEGMENT_1) THEN
    SUBGOAL_THEN `segment[c:real^N,b] SUBSET segment[a,b]` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT]; ALL_TAC] THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; REWRITE_TAC[SUBSET]] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^N->real^1) a`) THEN
    ASM_REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN
    X_GEN_TAC `d:real^N` THEN ASM_CASES_TAC `d:real^N = a` THENL
     [ASM_MESON_TAC[BETWEEN_ANTISYM; BETWEEN_IN_SEGMENT];
      ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]];
    MP_TAC(ISPECL [`f:real^N->real^1`; `a:real^N`; `c:real^N`]
        SUBSET_CONTINUOUS_IMAGE_SEGMENT_1) THEN
    SUBGOAL_THEN `segment[a:real^N,c] SUBSET segment[a,b]` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT]; ALL_TAC] THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; REWRITE_TAC[SUBSET]] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^N->real^1) b`) THEN
    ASM_REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN
    X_GEN_TAC `d:real^N` THEN ASM_CASES_TAC `d:real^N = b` THENL
     [ASM_MESON_TAC[BETWEEN_ANTISYM; BETWEEN_IN_SEGMENT; BETWEEN_SYM];
      ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]]]);;

let CONTINUOUS_INJECTIVE_IMAGE_OPEN_SEGMENT_1 = prove
 (`!f:real^N->real^1 a b.
        f continuous_on segment[a,b] /\
        (!x y. x IN segment[a,b] /\ y IN segment[a,b] /\ f x = f y ==> x = y)
        ==> IMAGE f (segment(a,b)) = segment(f a,f b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[segment] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_INJECTIVE_IMAGE_SEGMENT_1) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`(f:real^N->real^1) a`; `(f:real^1->real^1) b`]
    ENDS_IN_SEGMENT) THEN
  ASM SET_TAC[]);;

let CONTINUOUS_IVT_LOCAL_EXTREMUM = prove
 (`!f:real^N->real^1 a b.
        f continuous_on segment[a,b] /\ ~(a = b) /\ f(a) = f(b)
         ==> ?z. z IN segment(a,b) /\
                 ((!w. w IN segment[a,b] ==> drop(f w) <= drop(f z)) \/
                  (!w. w IN segment[a,b] ==> drop(f z) <= drop(f w)))`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (MP_TAC o ISPECL
            [`drop o (f:real^N->real^1)`; `segment[a:real^N,b]`])
            [CONTINUOUS_ATTAINS_SUP; CONTINUOUS_ATTAINS_INF] THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
  REWRITE_TAC[COMPACT_SEGMENT; SEGMENT_EQ_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(d:real^N) IN segment(a,b)` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(c:real^N) IN segment(a,b)` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `midpoint(a:real^N,b)` THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT]; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CONJUNCT2 segment]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [segment])) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[REAL_LE_ANTISYM; DROP_EQ]);;

let FRONTIER_UNIONS_SUBSET_CLOSURE = prove
 (`!f:(real^N->bool)->bool.
        frontier(UNIONS f) SUBSET closure(UNIONS {frontier t | t IN f})`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [frontier] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; CLOSURE_APPROACHABLE] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[EXISTS_IN_UNIONS; EXISTS_IN_GSPEC; RIGHT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN
  ASM_CASES_TAC `(t:real^N->bool) IN f` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(x:real^N) IN t` THENL
   [DISCH_THEN(K ALL_TAC) THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[frontier; DIST_REFL; IN_DIFF] THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    SPEC_TAC(`x:real^N`,`z:real^N`) THEN
    REWRITE_TAC[CONTRAPOS_THM; GSYM SUBSET] THEN
    MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`segment[x:real^N,y]`; `t:real^N->bool`]
        CONNECTED_INTER_FRONTIER) THEN
    SIMP_TAC[CONNECTED_SEGMENT; GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_DIFF] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^N` THEN
    ASM_MESON_TAC[DIST_IN_CLOSED_SEGMENT; DIST_SYM; REAL_LET_TRANS]]);;

let CLOSURE_CONVEX_INTER_AFFINE = prove
 (`!s t:real^N->bool.
      convex s /\ affine t /\ ~(relative_interior s INTER t = {})
      ==> closure(s INTER t) = closure(s) INTER t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET_INTER] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[];
    TRANS_TAC SUBSET_TRANS `closure t:real^N->bool` THEN
    SIMP_TAC[SUBSET_CLOSURE; INTER_SUBSET] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; CLOSED_AFFINE; SUBSET_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:real^N` MP_TAC o
        GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[AFFINE_EQ_SUBSPACE] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP(REWRITE_RULE[SUBSET]
    RELATIVE_INTERIOR_SUBSET)) THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
  STRIP_TAC THEN ASM_CASES_TAC `x:real^N = vec 0` THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `x IN closure(segment(vec 0:real^N,x))` MP_TAC THENL
   [ASM_REWRITE_TAC[CLOSURE_SEGMENT; ENDS_IN_SEGMENT]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s ==> x IN t`) THEN
  MATCH_MP_TAC SUBSET_CLOSURE THEN REWRITE_TAC[SUBSET_INTER] THEN
  CONJ_TAC THENL
   [TRANS_TAC SUBSET_TRANS `relative_interior s:real^N->bool` THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN
    MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SUBSET; IN_SEGMENT; VECTOR_MUL_RZERO; VECTOR_ADD_LID;
                 SUBSPACE_MUL; LEFT_IMP_EXISTS_THM]]);;

let RELATIVE_FRONTIER_CONVEX_INTER_AFFINE = prove
 (`!s t:real^N->bool.
        convex s /\ affine t /\ ~(interior s INTER t = {})
        ==> relative_frontier(s INTER t) = frontier s INTER t`,
  SIMP_TAC[relative_frontier; RELATIVE_INTERIOR_CONVEX_INTER_AFFINE;
           frontier] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(relative_interior s INTER t:real^N->bool = {})`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET_RELATIVE_INTERIOR) THEN
    ASM SET_TAC[];
    ASM_SIMP_TAC[CLOSURE_CONVEX_INTER_AFFINE] THEN SET_TAC[]]);;

let CONNECTED_COMPONENT_1_GEN = prove
 (`!s a b:real^N.
        dimindex(:N) = 1
        ==> (connected_component s a b <=> segment[a,b] SUBSET s)`,
  SIMP_TAC[connected_component; GSYM CONNECTED_CONVEX_1_GEN] THEN
 MESON_TAC[CONVEX_CONTAINS_SEGMENT; SUBSET; CONVEX_SEGMENT;
            ENDS_IN_SEGMENT]);;

let CONNECTED_COMPONENT_1 = prove
 (`!s a b:real^1. connected_component s a b <=> segment[a,b] SUBSET s`,
  SIMP_TAC[CONNECTED_COMPONENT_1_GEN; DIMINDEX_1]);;

(* ------------------------------------------------------------------------- *)
(* An injective function into R is a homeomorphism and so an open map.       *)
(* ------------------------------------------------------------------------- *)

let INJECTIVE_INTO_1D_EQ_HOMEOMORPHISM = prove
 (`!f:real^N->real^1 s.
        f continuous_on s /\ path_connected s
        ==>  ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
              ?g. homeomorphism (s,IMAGE f s) (f,g))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE];
    REWRITE_TAC[homeomorphism] THEN MESON_TAC[]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^1->real^N` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[homeomorphism; FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `is_interval (IMAGE (f:real^N->real^1) s)` ASSUME_TAC THENL
   [REWRITE_TAC[IS_INTERVAL_PATH_CONNECTED_1] THEN
    ASM_MESON_TAC[PATH_CONNECTED_CONTINUOUS_IMAGE];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_on; IMP_CONJ; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ABBREV_TAC `y = (f:real^N->real^1) x` THEN
  ABBREV_TAC `t = IMAGE (f:real^N->real^1) s` THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?a b d. a IN s /\ b IN s /\ &0 < d /\
            ball(y,d) INTER t SUBSET segment[(f:real^N->real^1) a,f b]`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^1->bool`; `y:real^1`]
        INTERVAL_CONTAINS_COMPACT_NEIGHBOURHOOD) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[INTERVAL_SUBSET_IS_INTERVAL] THEN
    REWRITE_TAC[SET_RULE
     `P /\ y IN s /\ (s = {} \/ a IN t /\ b IN t) /\ R <=>
      a IN t /\ b IN t /\ P /\ y IN s /\ R`] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[EXISTS_IN_IMAGE] THEN
    REWRITE_TAC[SEGMENT_1; IN_INTERVAL_1] THEN
    MESON_TAC[REAL_LE_TRANS];
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [path_connected]) THEN
   DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `p:real^1->real^N` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN
    `(g:real^1->real^N) continuous_on segment[(f:real^N->real^1) a,f b]`
   MP_TAC THENL
    [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
     EXISTS_TAC `IMAGE (f:real^N->real^1) (path_image p)` THEN CONJ_TAC THENL
      [MATCH_MP_TAC CONTINUOUS_ON_INVERSE THEN
       ASM_SIMP_TAC[COMPACT_PATH_IMAGE] THEN CONJ_TAC THENL
        [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]];
       SUBGOAL_THEN `convex(IMAGE (f:real^N->real^1) (path_image p))`
       MP_TAC THENL
        [REWRITE_TAC[GSYM IS_INTERVAL_CONVEX_1; IS_INTERVAL_CONNECTED_1] THEN
         MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
         ASM_SIMP_TAC[CONNECTED_PATH_IMAGE] THEN
         ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
         REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
         CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
         ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]]];
     REWRITE_TAC[continuous_on] THEN
     DISCH_THEN(MP_TAC o SPEC `y:real^1`) THEN ANTS_TAC THENL
      [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
       ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN ASM SET_TAC[];
       ALL_TAC] THEN
     DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `min d k` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
     X_GEN_TAC `x':real^N` THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
     ASM_REWRITE_TAC[IN_INTER; IN_BALL] THEN
     ONCE_REWRITE_TAC[DIST_SYM] THEN ASM SET_TAC[]]]);;

let INJECTIVE_INTO_1D_IMP_OPEN_MAP = prove
 (`!f:real^N->real^1 s t.
        f continuous_on s /\ path_connected s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        open_in (subtopology euclidean s) t
        ==> open_in (subtopology euclidean (IMAGE f s)) (IMAGE f t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
  ASM_MESON_TAC[INJECTIVE_INTO_1D_EQ_HOMEOMORPHISM]);;

(* ------------------------------------------------------------------------- *)
(* Injective function on an interval is strictly increasing or decreasing.   *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_INJECTIVE_IFF_MONOTONIC = prove
 (`!f:real^1->real^1 s.
        f continuous_on s /\ is_interval s
        ==> ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
             (!x y. x IN s /\ y IN s /\ drop x < drop y
                    ==> drop(f x) < drop(f y)) \/
             (!x y. x IN s /\ y IN s /\ drop x < drop y
                    ==> drop(f y) < drop(f x)))`,
  let lemma = prove
   (`!s f:real^1->real^1.
        f continuous_on s /\ is_interval s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> !u v w. u IN s /\ v IN s /\ w IN s /\
                    drop u < drop v /\ drop v < drop w /\
                    drop(f u) <= drop(f v) /\ drop(f w) <= drop(f v) ==> F`,
    REWRITE_TAC[IS_INTERVAL_CONVEX_1; CONVEX_CONTAINS_SEGMENT] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `u:real^1`; `w:real^1`]
        CONTINUOUS_INJECTIVE_IMAGE_SEGMENT_1) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[EXTENSION] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^1->real^1) v`) THEN
    MATCH_MP_TAC(TAUT `p /\ ~q ==> (p <=> q) ==> F`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[SEGMENT_1] THEN
      COND_CASES_TAC THENL
       [ASM_SIMP_TAC[IN_INTERVAL_1; REAL_LT_IMP_LE]; ASM_REAL_ARITH_TAC];
      REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1] THEN DISCH_TAC THENL
       [SUBGOAL_THEN `drop(f(w:real^1)) = drop(f v)` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[DROP_EQ; REAL_LT_REFL]];
        SUBGOAL_THEN `drop(f(u:real^1)) = drop(f v)` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[DROP_EQ; REAL_LT_REFL]]]])
  and tac s1 s2 =
   let [l1;l2] = map (map (fun x -> mk_var(x,`:real^1`)) o explode) [s1;s2] in
   REPEAT(FIRST_X_ASSUM(fun th ->
     MP_TAC(ISPECL l1 th) THEN MP_TAC(ISPECL l2 th))) THEN
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC in
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM DROP_EQ] THEN
    MESON_TAC[REAL_LT_TOTAL; REAL_LT_REFL]] THEN
  DISCH_TAC THEN MATCH_MP_TAC(MESON[]
   `(!a b c d. ~(~P a b /\ ~Q c d)) ==> (!x y. P x y) \/ (!x y. Q x y)`) THEN
  MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`; `c:real^1`; `d:real^1`] THEN
  REWRITE_TAC[NOT_IMP; REAL_NOT_LT] THEN STRIP_TAC THEN
  REPEAT
   (FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_LE_LT]) THEN
    REWRITE_TAC[DROP_EQ] THEN STRIP_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[REAL_LT_REFL]]) THEN
  MP_TAC(ISPEC `s:real^1->bool` lemma) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
   MP_TAC(SPEC `(--) o (f:real^1->real^1)` th) THEN
   MP_TAC(SPEC `f:real^1->real^1` th)) THEN
  ASM_REWRITE_TAC[o_THM; VECTOR_ARITH `--x:real^N = --y <=> x = y`] THEN
  DISCH_TAC THEN REWRITE_TAC[NOT_IMP; DROP_NEG; REAL_LE_NEG2] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_COMPOSE;LINEAR_CONTINUOUS_ON; LINEAR_NEGATION];
    DISCH_TAC] THEN
  ASM_CASES_TAC `drop d <= drop a` THENL [tac "cab" "cdb"; ALL_TAC] THEN
  ASM_CASES_TAC `drop b <= drop c` THENL [tac "abd" "acd"; ALL_TAC] THEN
  ASM_CASES_TAC `c:real^1 = a /\ d:real^1 = b` THENL
   [ASM_MESON_TAC[REAL_LT_ANTISYM]; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
   `~(c = a /\ d = b)
    ==> (c = a ==> d = b) /\ (d = b ==> c = a) /\
        (~(c = a) /\ ~(d = b) ==> F) ==> F`)) THEN
  REPEAT CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN SIMP_TAC[GSYM DROP_EQ] THEN tac "adb" "abd";
    DISCH_THEN SUBST_ALL_TAC THEN SIMP_TAC[GSYM DROP_EQ] THEN tac "acb" "cab";
    REWRITE_TAC[GSYM DROP_EQ] THEN STRIP_TAC] THEN
  ASM_CASES_TAC `drop a <= drop c` THENL [tac "acb" "acd"; tac "cab" "cad"]);;

(* ------------------------------------------------------------------------- *)
(* Some uncountability results for relevant sets.                            *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_SEGMENT = prove
 (`(!a b:real^N. ~(a = b) ==> segment[a,b] =_c (:real)) /\
   (!a b:real^N. ~(a = b) ==> segment(a,b) =_c (:real))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SEGMENT_IMAGE_INTERVAL] THENL
   [TRANS_TAC CARD_EQ_TRANS `interval[vec 0:real^1,vec 1]`;
    TRANS_TAC CARD_EQ_TRANS `interval(vec 0:real^1,vec 1)`] THEN
  SIMP_TAC[CARD_EQ_INTERVAL; UNIT_INTERVAL_NONEMPTY] THEN
  MATCH_MP_TAC CARD_EQ_IMAGE THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; VECTOR_ARITH
   `(&1 - x) % a + x % b:real^N = (&1 - y) % a + y % b <=>
    (x - y) % (a - b) = vec 0`] THEN
  SIMP_TAC[REAL_SUB_0; DROP_EQ]);;

let UNCOUNTABLE_SEGMENT = prove
 (`(!a b:real^N. ~(a = b) ==> ~COUNTABLE(segment[a,b])) /\
   (!a b:real^N. ~(a = b) ==> ~COUNTABLE(segment(a,b)))`,
  SIMP_TAC[CARD_EQ_REAL_IMP_UNCOUNTABLE; CARD_EQ_SEGMENT]);;

let CARD_EQ_PATH_CONNECTED = prove
 (`!s a b:real^N.
        path_connected s /\ a IN s /\ b IN s /\ ~(a = b) ==> s =_c (:real)`,
  MESON_TAC[CARD_EQ_CONNECTED; PATH_CONNECTED_IMP_CONNECTED]);;

let UNCOUNTABLE_PATH_CONNECTED = prove
 (`!s a b:real^N.
        path_connected s /\ a IN s /\ b IN s /\ ~(a = b) ==> ~COUNTABLE s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CARD_EQ_REAL_IMP_UNCOUNTABLE THEN
  MATCH_MP_TAC CARD_EQ_PATH_CONNECTED THEN
  ASM_MESON_TAC[]);;

let CARD_EQ_CONVEX = prove
 (`!s a b:real^N.
        convex s /\ a IN s /\ b IN s /\ ~(a = b) ==> s =_c (:real)`,
  MESON_TAC[CARD_EQ_PATH_CONNECTED; CONVEX_IMP_PATH_CONNECTED]);;

let UNCOUNTABLE_CONVEX = prove
 (`!s a b:real^N.
        convex s /\ a IN s /\ b IN s /\ ~(a = b) ==> ~COUNTABLE s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CARD_EQ_REAL_IMP_UNCOUNTABLE THEN
  MATCH_MP_TAC CARD_EQ_CONVEX THEN
  ASM_MESON_TAC[]);;

let CARD_EQ_NONEMPTY_INTERIOR = prove
 (`!s:real^N->bool. ~(interior s = {}) ==> s =_c (:real)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN
    SIMP_TAC[CARD_LE_UNIV; CARD_EQ_IMP_LE; CARD_EQ_EUCLIDEAN];
    TRANS_TAC CARD_LE_TRANS `interior(s:real^N->bool)` THEN
    SIMP_TAC[CARD_LE_SUBSET; INTERIOR_SUBSET] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[CARD_EQ_SYM] CARD_EQ_IMP_LE) THEN
    MATCH_MP_TAC CARD_EQ_OPEN THEN ASM_REWRITE_TAC[OPEN_INTERIOR]]);;

let UNCOUNTABLE_NONEMPTY_INTERIOR = prove
 (`!s:real^N->bool. ~(interior s = {}) ==> ~(COUNTABLE s)`,
  SIMP_TAC[CARD_EQ_NONEMPTY_INTERIOR; CARD_EQ_REAL_IMP_UNCOUNTABLE]);;

let COUNTABLE_EMPTY_INTERIOR = prove
 (`!s:real^N->bool. COUNTABLE s ==> interior s = {}`,
  MESON_TAC[UNCOUNTABLE_NONEMPTY_INTERIOR]);;

let FINITE_EMPTY_INTERIOR = prove
 (`!s:real^N->bool. FINITE s ==> interior s = {}`,
  SIMP_TAC[COUNTABLE_EMPTY_INTERIOR; FINITE_IMP_COUNTABLE]);;

let [CONNECTED_FINITE_IFF_SING;
     CONNECTED_FINITE_IFF_COUNTABLE;
     CONNECTED_INFINITE_IFF_CARD_EQ] = (CONJUNCTS o prove)
 (`(!s:real^N->bool. connected s ==> (FINITE s <=> s = {} \/ ?a. s = {a})) /\
   (!s:real^N->bool. connected s ==> (FINITE s <=> COUNTABLE s)) /\
   (!s:real^N->bool. connected s ==> (INFINITE s <=> s =_c (:real)))`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  ASM_CASES_TAC `connected(s:real^N->bool)` THEN
  ASM_REWRITE_TAC[INFINITE] THEN MATCH_MP_TAC(TAUT
   `(f ==> c) /\ (r ==> ~c) /\ (s ==> f) /\ (~s ==> r)
    ==> (f <=> s) /\ (f <=> c) /\ (~f <=> r)`) THEN
  REWRITE_TAC[FINITE_IMP_COUNTABLE] THEN
  REPEAT CONJ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_EQ_REAL_IMP_UNCOUNTABLE; FINITE_INSERT; FINITE_EMPTY] THEN
  MATCH_MP_TAC CARD_EQ_CONNECTED THEN ASM SET_TAC[]);;

let CLOSED_AS_FRONTIER_OF_SUBSET = prove
 (`!s:real^N->bool. closed s <=> ?t. t SUBSET s /\ s = frontier t`,
  GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[FRONTIER_CLOSED]] THEN
  DISCH_TAC THEN MP_TAC(ISPEC `s:real^N->bool` SEPARABLE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN
  SIMP_TAC[frontier] THEN STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
   `s SUBSET c /\ c SUBSET s /\ i = {} ==> s = c DIFF i`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET_CLOSURE; CLOSURE_CLOSED];
    ASM_MESON_TAC[UNCOUNTABLE_NONEMPTY_INTERIOR]]);;

let CLOSED_AS_FRONTIER = prove
 (`!s:real^N->bool. closed s <=> ?t. s = frontier t`,
  GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[CLOSED_AS_FRONTIER_OF_SUBSET]; MESON_TAC[FRONTIER_CLOSED]]);;

let CARD_EQ_CLOSED = prove
 (`!s:real^N->bool. closed s ==> s <=_c (:num) \/ s =_c (:real)`,
  let slemma = prove
   (`!s:real^N->bool.
          ~COUNTABLE s
          ==> ?x y. ~(x = y) /\ x IN s /\ y IN s /\
                    x condensation_point_of s /\
                    y condensation_point_of s`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CARD_EQ_CONDENSATION_POINTS_IN_SET) THEN
    DISCH_THEN(MP_TAC o MATCH_MP CARD_INFINITE_CONG) THEN
    REWRITE_TAC[INFINITE] THEN
    MATCH_MP_TAC(TAUT `q /\ (p ==> s) ==> (p <=> q) ==> s`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_IMP_COUNTABLE]; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`2`; `{x:real^N | x IN s /\ x condensation_point_of s}`]
          CHOOSE_SUBSET_STRONG) THEN
    ASM_REWRITE_TAC[HAS_SIZE_CONV `s HAS_SIZE 2`; RIGHT_AND_EXISTS_THM] THEN
    DISCH_THEN(CHOOSE_THEN MP_TAC) THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FORALL_IN_INSERT; NOT_IN_EMPTY]) THEN
    ASM_REWRITE_TAC[]) in
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM COUNTABLE_ALT] THEN
  ASM_CASES_TAC `COUNTABLE(s:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!n t:real^N->bool.
        closed t /\ ~COUNTABLE t
        ==> ?l r. (compact l /\ ~COUNTABLE l) /\ (compact r /\ ~COUNTABLE r) /\
                  l INTER r = {} /\ l SUBSET t /\ r SUBSET t /\
                  diameter l <= inv(&2 pow n) /\
                  diameter r <= inv(&2 pow n)`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o MATCH_MP slemma)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`t INTER cball(a:real^N,min (inv(&2 pow (SUC n))) (dist(a,b) / &3))`;
     `t INTER cball(b:real^N,min (inv(&2 pow (SUC n))) (dist(a,b) / &3))`] THEN
    ASM_SIMP_TAC[CLOSED_INTER_COMPACT; COMPACT_CBALL] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I
       [CONDENSATION_POINT_INFINITE_CBALL]) THEN
      REWRITE_TAC[REAL_LT_MIN; REAL_LT_INV_EQ; REAL_LT_POW2] THEN
      UNDISCH_TAC `~(a:real^N = b)` THEN CONV_TAC NORM_ARITH;
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I
       [CONDENSATION_POINT_INFINITE_CBALL]) THEN
      REWRITE_TAC[REAL_LT_MIN; REAL_LT_INV_EQ; REAL_LT_POW2] THEN
      UNDISCH_TAC `~(a:real^N = b)` THEN CONV_TAC NORM_ARITH;
      MATCH_MP_TAC(SET_RULE
       `(!x. ~(x IN t /\ x IN u)) ==> (s INTER t) INTER (s INTER u) = {}`) THEN
      REWRITE_TAC[IN_CBALL; REAL_LE_MIN] THEN
      UNDISCH_TAC `~(a:real^N = b)` THEN CONV_TAC NORM_ARITH;
      SET_TAC[];
      SET_TAC[];
      MATCH_MP_TAC DIAMETER_LE THEN
      SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_LT_POW2] THEN
      REWRITE_TAC[IN_INTER; IN_CBALL; REAL_LE_MIN; real_pow; REAL_INV_MUL] THEN
      CONV_TAC NORM_ARITH;
      MATCH_MP_TAC DIAMETER_LE THEN
      SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_LT_POW2] THEN
      REWRITE_TAC[IN_INTER; IN_CBALL; REAL_LE_MIN; real_pow; REAL_INV_MUL] THEN
      CONV_TAC NORM_ARITH];
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`l:num->(real^N->bool)->(real^N->bool)`;
      `r:num->(real^N->bool)->(real^N->bool)`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `!b. ?x:num->real^N->bool.
          (x 0 = s) /\ (!n. x(SUC n) = if b(n) then r n (x n) else l n (x n))`
    MP_TAC THENL
     [GEN_TAC THEN
      W(ACCEPT_TAC o prove_recursive_functions_exist num_RECURSION o
        snd o dest_exists o snd);
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM]] THEN
    X_GEN_TAC `x:(num->bool)->num->real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
     [TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN
      SIMP_TAC[CARD_LE_UNIV; CARD_EQ_EUCLIDEAN; CARD_EQ_IMP_LE];
      TRANS_TAC CARD_LE_TRANS `(:num->bool)` THEN
      SIMP_TAC[CARD_EQ_REAL; CARD_EQ_IMP_LE]] THEN
    REWRITE_TAC[le_c; IN_UNIV] THEN
    SUBGOAL_THEN
     `!b n. closed((x:(num->bool)->num->real^N->bool) b n) /\
            ~COUNTABLE(x b n)`
    MP_TAC THENL
     [GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
    MP_TAC(GEN `b:num->bool` (ISPEC `(x:(num->bool)->num->real^N->bool) b`
          DECREASING_CLOSED_NEST_SING)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP MONO_FORALL) THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[FORALL_AND_THM] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[COUNTABLE_EMPTY];
        GEN_TAC THEN MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
        REWRITE_TAC[SUBSET_REFL] THEN ASM SET_TAC[];
        MAP_EVERY X_GEN_TAC [`b:num->bool`; `e:real`] THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`inv(&2)`; `e:real`] REAL_ARCH_POW_INV) THEN
        ASM_REWRITE_TAC[REAL_POW_INV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
        EXISTS_TAC `SUC m` THEN ASM_SIMP_TAC[] THEN
        REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o MATCH_MP
         (REWRITE_RULE[TAUT `p /\ q /\ r ==> s <=> q /\ r ==> p ==> s`]
          DIAMETER_BOUNDED_BOUND)) THEN
        ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
        UNDISCH_TAC `inv(&2 pow m) < e` THEN MATCH_MP_TAC(NORM_ARITH
         `d <= i ==> i < e ==> norm(x - y) <= d ==> dist(x:real^N,y) < e`) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `f:(num->bool)->real^N` THEN STRIP_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `b:num->bool` THEN
      REWRITE_TAC[SET_RULE `x IN s <=> {x} SUBSET s`] THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
      REWRITE_TAC[SUBSET; INTERS_GSPEC; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
      ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      SIMP_TAC[FORALL_UNWIND_THM2] THEN GEN_TAC THEN ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`b:num->bool`; `c:num->bool`] THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [FUN_EQ_THM] THEN
      REWRITE_TAC[NOT_FORALL_THM] THEN ONCE_REWRITE_TAC[num_WOP] THEN
      SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC(SET_RULE
       `!f g. INTERS f = {a} /\ INTERS g = {b} /\
              (?s t. s IN f /\ t IN g /\ s INTER t = {})
              ==> ~(a = b)`) THEN
      EXISTS_TAC `{t | ?n. t = (x:(num->bool)->num->real^N->bool) b n}` THEN
      EXISTS_TAC `{t | ?n. t = (x:(num->bool)->num->real^N->bool) c n}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      EXISTS_TAC `(x:(num->bool)->num->real^N->bool) b (SUC k)` THEN
      EXISTS_TAC `(x:(num->bool)->num->real^N->bool) c (SUC k)` THEN
      REPEAT(CONJ_TAC THENL [MESON_TAC[]; ALL_TAC]) THEN ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN
       `!i. i <= k ==> (x:(num->bool)->num->real^N->bool) b i = x c i`
      MP_TAC THENL
       [INDUCT_TAC THEN ASM_SIMP_TAC[LE_SUC_LT; LT_IMP_LE];
        DISCH_THEN(MP_TAC o SPEC `k:num`)] THEN
      REWRITE_TAC[LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [TAUT `~(p <=> q) <=> (q <=> ~p)`]) THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      ASM_MESON_TAC[INTER_COMM]]]);;

let CONDENSATION_POINTS_EQ_EMPTY,CARD_EQ_CONDENSATION_POINTS =
 (CONJ_PAIR o prove)
 (`(!s:real^N->bool.
        {x | x condensation_point_of s} = {} <=> COUNTABLE s) /\
   (!s:real^N->bool.
        {x | x condensation_point_of s} =_c (:real) <=> ~(COUNTABLE s))`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(r ==> p) /\ (~r ==> q) /\ (p ==> ~q)
    ==> (p <=> r) /\ (q <=> ~r)`) THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    REWRITE_TAC[condensation_point_of] THEN
    ASM_MESON_TAC[COUNTABLE_SUBSET; INTER_SUBSET; IN_UNIV; OPEN_UNIV];
    DISCH_TAC THEN MATCH_MP_TAC(REWRITE_RULE
     [TAUT `p ==> q \/ r <=> p /\ ~q ==> r`] CARD_EQ_CLOSED) THEN
    REWRITE_TAC[CLOSED_CONDENSATION_POINTS; GSYM COUNTABLE_ALT] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CARD_EQ_CONDENSATION_POINTS_IN_SET) THEN
    DISCH_THEN(MP_TAC o MATCH_MP CARD_COUNTABLE_CONG) THEN
    ASM_REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP CARD_FINITE_CONG) THEN
    REWRITE_TAC[FINITE_EMPTY; GSYM INFINITE; real_INFINITE]]);;

let UNCOUNTABLE_HAS_CONDENSATION_POINT = prove
 (`!s:real^N->bool. ~COUNTABLE s ==> ?x. x condensation_point_of s`,
  REWRITE_TAC[GSYM CONDENSATION_POINTS_EQ_EMPTY] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Density of sets with small complement, including irrationals.             *)
(* ------------------------------------------------------------------------- *)

let COSMALL_APPROXIMATION = prove
 (`!s. ((:real) DIFF s) <_c (:real)
       ==> !x e. &0 < e ==> ?y. y IN s /\ abs(y - x) < e`,
  let lemma = prove
   (`!s. ((:real^1) DIFF s) <_c (:real)
         ==> !x e. &0 < e ==> ?y. y IN s /\ norm(y - x) < e`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
      `~({x | P x} SUBSET UNIV DIFF s) ==> ?x. x IN s /\ P x`) THEN
    MP_TAC(ISPEC `ball(x:real^1,e)` CARD_EQ_OPEN) THEN
    ASM_REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP CARD_LE_SUBSET) THEN
    REWRITE_TAC[CARD_NOT_LE] THEN
    REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[DIST_SYM] dist); GSYM ball] THEN
    TRANS_TAC CARD_LTE_TRANS `(:real)` THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[CARD_EQ_SYM] CARD_EQ_IMP_LE]) in
  REWRITE_TAC[FORALL_DROP_IMAGE; FORALL_DROP; EXISTS_DROP] THEN
  REWRITE_TAC[GSYM IMAGE_DROP_UNIV; GSYM DROP_SUB; GSYM ABS_DROP] THEN
  REWRITE_TAC[DROP_IN_IMAGE_DROP] THEN REWRITE_TAC[GSYM FORALL_DROP] THEN
  SIMP_TAC[GSYM IMAGE_DIFF_INJ; DROP_EQ] THEN GEN_TAC THEN
  DISCH_TAC THEN MATCH_MP_TAC lemma THEN POP_ASSUM MP_TAC THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC CARD_LT_CONG THEN
  REWRITE_TAC[IMAGE_DROP_UNIV; CARD_EQ_REFL] THEN
  MATCH_MP_TAC CARD_EQ_IMAGE THEN SIMP_TAC[DROP_EQ]);;

let COCOUNTABLE_APPROXIMATION = prove
 (`!s. COUNTABLE((:real) DIFF s)
       ==> !x e. &0 < e ==> ?y. y IN s /\ abs(y - x) < e`,
  GEN_TAC THEN REWRITE_TAC[COUNTABLE; ge_c] THEN DISCH_TAC THEN
  MATCH_MP_TAC COSMALL_APPROXIMATION THEN
  TRANS_TAC CARD_LET_TRANS `(:num)` THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC CARD_LTE_TRANS `(:num->bool)` THEN SIMP_TAC[CANTOR_THM_UNIV] THEN
  MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
  REWRITE_TAC[CARD_EQ_REAL]);;

let IRRATIONAL_APPROXIMATION = prove
 (`!x e. &0 < e ==> ?y. ~(rational y) /\ abs(y - x) < e`,
  REWRITE_TAC[SET_RULE `~rational y <=> y IN UNIV DIFF rational`] THEN
  MATCH_MP_TAC COCOUNTABLE_APPROXIMATION THEN
  REWRITE_TAC[SET_RULE `UNIV DIFF (UNIV DIFF s) = s`; COUNTABLE_RATIONAL]);;

let OPEN_SET_COSMALL_COORDINATES = prove
 (`!P. (!i. 1 <= i /\ i <= dimindex(:N)
            ==> (:real) DIFF {x | P i x} <_c (:real))
       ==> !s:real^N->bool.
              open s /\ ~(s = {})
              ==> ?x. x IN s /\ !i. 1 <= i /\ i <= dimindex(:N) ==> P i (x$i)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> ?y:real. P i y /\ abs(y - (a:real^N)$i) < d / &(dimindex(:N))`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COSMALL_APPROXIMATION) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1];
    REWRITE_TAC[LAMBDA_SKOLEM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_CBALL; dist] THEN
    W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    MATCH_MP_TAC SUM_BOUND_GEN THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; NUMSEG_EMPTY; NOT_LT; DIMINDEX_GE_1] THEN
    ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; CARD_NUMSEG_1]]);;

let OPEN_SET_COCOUNTABLE_COORDINATES = prove
 (`!P. (!i. 1 <= i /\ i <= dimindex(:N)
            ==> COUNTABLE((:real) DIFF {x | P i x}))
       ==> !s:real^N->bool.
              open s /\ ~(s = {})
              ==> ?x. x IN s /\ !i. 1 <= i /\ i <= dimindex(:N) ==> P i (x$i)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC OPEN_SET_COSMALL_COORDINATES THEN
  REPEAT STRIP_TAC THEN
  TRANS_TAC CARD_LET_TRANS `(:num)` THEN ASM_SIMP_TAC[GSYM COUNTABLE_ALT] THEN
  TRANS_TAC CARD_LTE_TRANS `(:num->bool)` THEN SIMP_TAC[CANTOR_THM_UNIV] THEN
  MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
  REWRITE_TAC[CARD_EQ_REAL]);;

let OPEN_SET_IRRATIONAL_COORDINATES = prove
 (`!s:real^N->bool.
        open s /\ ~(s = {})
        ==> ?x. x IN s /\ !i. 1 <= i /\ i <= dimindex(:N) ==> ~rational(x$i)`,
  MATCH_MP_TAC OPEN_SET_COCOUNTABLE_COORDINATES THEN
  REWRITE_TAC[SET_RULE `UNIV DIFF {x | ~P x} = P`; COUNTABLE_RATIONAL]);;

let CLOSURE_COSMALL_COORDINATES = prove
 (`!P. (!i. 1 <= i /\ i <= dimindex(:N)
            ==> (:real) DIFF {x | P i x} <_c (:real))
       ==> closure {x | !i. 1 <= i /\ i <= dimindex (:N) ==> P i (x$i)} =
           (:real^N)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE; IN_UNIV; EXTENSION; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `e:real`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_SET_COSMALL_COORDINATES) THEN
  DISCH_THEN(MP_TAC o SPEC `ball(x:real^N,e)`) THEN
  ASM_REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE; IN_BALL] THEN
  MESON_TAC[DIST_SYM]);;

let CLOSURE_COCOUNTABLE_COORDINATES = prove
 (`!P. (!i. 1 <= i /\ i <= dimindex(:N)
            ==> COUNTABLE((:real) DIFF {x | P i x}))
       ==> closure {x | !i. 1 <= i /\ i <= dimindex (:N) ==> P i (x$i)} =
           (:real^N)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_COSMALL_COORDINATES THEN
  REPEAT STRIP_TAC THEN
  TRANS_TAC CARD_LET_TRANS `(:num)` THEN ASM_SIMP_TAC[GSYM COUNTABLE_ALT] THEN
  TRANS_TAC CARD_LTE_TRANS `(:num->bool)` THEN SIMP_TAC[CANTOR_THM_UNIV] THEN
  MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
  REWRITE_TAC[CARD_EQ_REAL]);;

let CLOSURE_IRRATIONAL_COORDINATES = prove
 (`closure {x | !i. 1 <= i /\ i <= dimindex (:N) ==> ~rational(x$i)} =
   (:real^N)`,
  MATCH_MP_TAC CLOSURE_COCOUNTABLE_COORDINATES THEN
  REWRITE_TAC[SET_RULE `UNIV DIFF {x | ~P x} = P`; COUNTABLE_RATIONAL]);;

(* ------------------------------------------------------------------------- *)
(* Every path between distinct points contains an arc, and hence             *)
(* that path connection is equivalent to arcwise connection, for distinct    *)
(* points. The proof is based on Whyburn's "Topological Analysis".           *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_MONOTONE_IMAGE_INTERVAL = prove
 (`!f:real^1->real^N.
       f continuous_on interval[vec 0,vec 1] /\
       (!y. connected {x | x IN interval[vec 0,vec 1] /\ f x = y}) /\
       ~(f(vec 1) = f(vec 0))
       ==> (IMAGE f (interval[vec 0,vec 1])) homeomorphic
           (interval[vec 0:real^1,vec 1])`,
  let closure_dyadic_rationals_in_convex_set_pos_1 = prove
   (`!s. convex s /\ ~(interior s = {}) /\ (!x. x IN s ==> &0 <= drop x)
         ==> closure(s INTER { lift(&m / &2 pow n) |
                               m IN (:num) /\ n IN (:num)}) =
             closure s`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `s:real^1->bool` CLOSURE_DYADIC_RATIONALS_IN_CONVEX_SET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. x IN t ==> x IN u) /\ (!x. x IN u ==> x IN s ==> x IN t)
      ==> s INTER t = s INTER u`) THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; DIMINDEX_1; FORALL_1] THEN
    REWRITE_TAC[IN_ELIM_THM; EXISTS_LIFT; GSYM drop; LIFT_DROP] THEN
    REWRITE_TAC[REAL_ARITH `x / y:real = inv y * x`; LIFT_CMUL] THEN
    CONJ_TAC THENL [MESON_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real^1`] THEN REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `inv(&2 pow n) % x:real^1`) THEN
    ASM_SIMP_TAC[DROP_CMUL; REAL_LE_MUL_EQ; REAL_LT_POW2; REAL_LT_INV_EQ] THEN
    ASM_MESON_TAC[INTEGER_POS; LIFT_DROP]) in
  let function_on_dyadic_rationals = prove
   (`!f:num->num->A.
          (!m n. f (2 * m) (n + 1) = f m n)
          ==> ?g. !m n. g(&m / &2 pow n) = f m n`,
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN MP_TAC(ISPECL
     [`\(m,n). (f:num->num->A) m n`; `\(m,n). &m / &2 pow n`]
     FUNCTION_FACTORS_LEFT) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FUN_EQ_THM; o_THM] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    ONCE_REWRITE_TAC[MESON[]
      `(!a b c d. P a b c d) <=> (!b d a c. P a b c d)`] THEN
    MATCH_MP_TAC WLOG_LE THEN REPEAT CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    SIMP_TAC[REAL_FIELD `~(y = &0) /\ ~(y' = &0)
                         ==> (x / y = x' / y' <=> y' / y * x = x')`;
       REAL_POW_EQ_0; REAL_OF_NUM_EQ; REAL_DIV_POW2; ARITH_EQ] THEN
    SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    SIMP_TAC[ADD_SUB2; REAL_OF_NUM_MUL; REAL_OF_NUM_EQ; REAL_OF_NUM_POW] THEN
    REWRITE_TAC[MESON[]
     `(!n n' d. n' = f d n ==> !m m'. g d m = m' ==> P m m' n d) <=>
      (!d m n. P m (g d m) n d)`] THEN
    INDUCT_TAC THEN SIMP_TAC[EXP; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; ADD1] THEN ASM_MESON_TAC[]) in
  let recursion_on_dyadic_rationals = prove
   (`!b:num->A l r.
          ?f. (!m. f(&m) = b m) /\
              (!m n. f(&(4 * m + 1) / &2 pow (n + 1)) =
                     l(f(&(2 * m + 1) / &2 pow n))) /\
              (!m n. f(&(4 * m + 3) / &2 pow (n + 1)) =
                     r(f(&(2 * m + 1) / &2 pow n)))`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `?f:num->num->A.
          (!m n. f (2 * m) (n + 1) = f m n) /\
          (!m. f m 0 = b m) /\
          (!m n. f (4 * m + 1) (n + 1) = l(f (2 * m + 1) n)) /\
          (!m n. f (4 * m + 3) (n + 1) = r(f (2 * m + 1) n))`
    MP_TAC THENL
     [MP_TAC(prove_recursive_functions_exist num_RECURSION
       `(!m. f m 0 = (b:num->A) m) /\
        (!m n. f m (SUC n) =
                  if EVEN m then f (m DIV 2) n
                  else if EVEN(m DIV 2)
                       then l(f ((m + 1) DIV 2) n)
                       else r(f (m DIV 2) n))`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `f:num->num->A` THEN STRIP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD1]) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[EVEN_MULT; ARITH_EVEN; ARITH_RULE `(2 * m) DIV 2 = m`] THEN
      REWRITE_TAC[ARITH_RULE `(4 * m + 1) DIV 2 = 2 * m`;
                  ARITH_RULE `(4 * m + 3) DIV 2 = 2 * m + 1`;
                  ARITH_RULE `((4 * m + 1) + 1) DIV 2 = 2 * m + 1`;
                  ARITH_RULE `((4 * m + 3) + 1) DIV 2 = 2 * m + 2`] THEN
      REWRITE_TAC[EVEN_ADD; EVEN_MULT; EVEN; ARITH_EVEN; SND];
      DISCH_THEN(X_CHOOSE_THEN `f:num->num->A`
       (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP function_on_dyadic_rationals) THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th])) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_ARITH `x / &2 pow 0 = x`]) THEN
      ASM_REWRITE_TAC[]]) in
  let recursion_on_dyadic_rationals_1 = prove
   (`!b:A l r.
          ?f. (!m. f(&m / &2) = b) /\
              (!m n. 0 < n ==> f(&(4 * m + 1) / &2 pow (n + 1)) =
                               l(f(&(2 * m + 1) / &2 pow n))) /\
              (!m n. 0 < n ==> f(&(4 * m + 3) / &2 pow (n + 1)) =
                               r(f(&(2 * m + 1) / &2 pow n)))`,
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`(\n. b):num->A`; `l:A->A`; `r:A->A`]
          recursion_on_dyadic_rationals) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\x. (f:real->A)(&2 * x)` THEN
    ASM_REWRITE_TAC[REAL_ARITH `&2 * x / &2 = x`] THEN
    CONJ_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LT_REFL] THEN
    ASM_SIMP_TAC[ADD_CLAUSES; real_pow; REAL_POW_EQ_0; REAL_OF_NUM_EQ;
      ARITH_EQ; REAL_FIELD `~(y = &0) ==> &2 * x / (&2 * y) = x / y`]) in
  let exists_function_unpair = prove
   (`(?f:A->B#C. P f) <=> (?f1 f2. P(\x. (f1 x,f2 x)))`,
    EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN STRIP_TAC THEN
    EXISTS_TAC `\x. FST((f:A->B#C) x)` THEN
    EXISTS_TAC `\x. SND((f:A->B#C) x)` THEN
    ASM_REWRITE_TAC[PAIR; ETA_AX]) in
  let dyadics_in_open_unit_interval = prove
   (`interval(vec 0,vec 1) INTER
      {lift(&m / &2 pow n) | m IN (:num) /\ n IN (:num)} =
      {lift(&m / &2 pow n) | 0 < m /\ m < 2 EXP n}`,
    MATCH_MP_TAC(SET_RULE
     `(!m n. (f m n) IN s <=> P m n)
      ==> s INTER {f m n | m IN UNIV /\ n IN UNIV} =
          {f m n | P m n}`) THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_LT_POW2] THEN
    SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_POW; REAL_OF_NUM_LT]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b m. m IN interval[a,b] /\ interval[a,b] SUBSET interval[vec 0,vec 1]
            ==> ?c d. drop a <= drop c /\ drop c <= drop m /\
                      drop m <= drop d /\ drop d <= drop b /\
                      (!x. x IN interval[c,d] ==> f x = f m) /\
                      (!x. x IN interval[a,c] DELETE c ==> ~(f x = f m)) /\
                      (!x. x IN interval[d,b] DELETE d ==> ~(f x = f m)) /\
                      (!x y. x IN interval[a,c] DELETE c /\
                             y IN interval[d,b] DELETE d
                             ==> ~((f:real^1->real^N) x = f y))`
  MP_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; SUBSET_INTERVAL_1] THEN
    REPEAT STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `?c d. {x | x IN interval[a,b] /\ (f:real^1->real^N) x = f m} =
            interval[c,d]`
    MP_TAC THENL
     [SUBGOAL_THEN
       `{x | x IN interval[a,b] /\ (f:real^1->real^N) x = f m} =
        interval[a,b] INTER
        {x | x IN interval[vec 0,vec 1] /\ (f:real^1->real^N) x = f m}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_INTERVAL_1; IN_ELIM_THM;
                    DROP_VEC] THEN
        GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `?c d. {x | x IN interval[vec 0,vec 1] /\ (f:real^1->real^N) x = f m} =
              interval[c,d]`
      MP_TAC THENL
       [ASM_REWRITE_TAC[GSYM CONNECTED_COMPACT_INTERVAL_1] THEN
        ONCE_REWRITE_TAC[SET_RULE
         `{x | x IN s /\ P x} = s INTER {x | x IN s /\ P x}`] THEN
        MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
        REWRITE_TAC[COMPACT_INTERVAL] THEN
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_CONSTANT THEN
        ASM_REWRITE_TAC[CLOSED_INTERVAL];
        STRIP_TAC THEN ASM_REWRITE_TAC[INTER_INTERVAL_1] THEN MESON_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^1` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `m IN interval[c:real^1,d]` MP_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
                  ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_INTERVAL_1; IN_DELETE] THEN STRIP_TAC] THEN
    SUBGOAL_THEN `{c:real^1,d} SUBSET interval[c,d]` MP_TAC THENL
     [ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTERVAL_1] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
       [GSYM th]) THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM; IN_INTERVAL_1] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[GSYM IN_INTERVAL_1] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC  (LAND_CONV o RAND_CONV)
       [GSYM th]) THEN SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
      `{x | x IN s /\ f x = a} = t
       ==> (!x. P x ==> x IN s) /\ (!x. P x /\ Q x ==> ~(x IN t))
           ==> !x. P x /\ Q x ==> ~(f x = a)`)) THEN
      REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
    REWRITE_TAC[GSYM DROP_EQ] THEN STRIP_TAC THEN
    SUBGOAL_THEN `{x:real^1,y} INTER interval[c,d] = {}` MP_TAC THENL
     [REWRITE_TAC[SET_RULE `{a,b} INTER s = {} <=> ~(a IN s) /\ ~(b IN s)`;
                  IN_INTERVAL_1] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
       (LAND_CONV o LAND_CONV o RAND_CONV) [GSYM th])] THEN
    REWRITE_TAC[SET_RULE `{a,b} INTER s = {} <=> ~(a IN s) /\ ~(b IN s)`] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1] THEN
    ASM_CASES_TAC `(f:real^1->real^N) x = f m` THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `(f:real^1->real^N) y = f m` THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM IS_INTERVAL_CONNECTED_1] o
                  SPEC `(f:real^1->real^N) y`) THEN
    ASM_REWRITE_TAC[IS_INTERVAL_1] THEN DISCH_THEN(MP_TAC o SPECL
     [`x:real^1`; `y:real^1`; `m:real^1`]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`leftcut:real^1->real^1->real^1->real^1`;
      `rightcut:real^1->real^1->real^1->real^1`] THEN
    STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL
   [`vec 0:real^1`; `vec 1:real^1`; `vec 0:real^1`]) THEN
  REWRITE_TAC[SUBSET_REFL; ENDS_IN_UNIT_INTERVAL] THEN ABBREV_TAC
   `u = (rightcut:real^1->real^1->real^1->real^1) (vec 0) (vec 1) (vec 0)` THEN
  REWRITE_TAC[CONJ_ASSOC; REAL_LE_ANTISYM; DROP_EQ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[INTERVAL_SING; SET_RULE `~(x IN ({a} DELETE a))`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL
   [`u:real^1`; `vec 1:real^1`; `vec 1:real^1`]) THEN
  REWRITE_TAC[ENDS_IN_INTERVAL; SUBSET_INTERVAL_1; INTERVAL_NE_EMPTY_1] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ABBREV_TAC
   `v = (leftcut:real^1->real^1->real^1->real^1) u (vec 1) (vec 1)` THEN
  ONCE_REWRITE_TAC[TAUT
    `a /\ b /\ c /\ d /\ e <=> (c /\ d) /\ a /\ b /\ e`] THEN
  REWRITE_TAC[REAL_LE_ANTISYM; DROP_EQ] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[INTERVAL_SING; SET_RULE `~(x IN ({a} DELETE a))`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN interval[vec 0,v] DELETE v
        ==> ~((f:real^1->real^N) x = f(vec 1))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN
    REWRITE_TAC[IN_DELETE; IN_INTERVAL_1; GSYM DROP_EQ] THEN STRIP_TAC THEN
    ASM_CASES_TAC `drop t < drop u` THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
       `~(f1 = f0) ==> ft = f0 ==> ~(ft = f1)`));
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; IN_DELETE; GSYM DROP_EQ] THEN
    ASM_REAL_ARITH_TAC;
    UNDISCH_THEN
      `!x. x IN interval[u,v] DELETE v ==> ~((f:real^1->real^N) x = f (vec 1))`
      (K ALL_TAC)] THEN
  MP_TAC(ISPECL
   [`(u:real^1,v:real^1)`;
    `\(a,b). (a:real^1,leftcut a b (midpoint(a,b)):real^1)`;
    `\(a,b). (rightcut a b (midpoint(a,b)):real^1,b:real^1)`]
        recursion_on_dyadic_rationals_1) THEN
  REWRITE_TAC[exists_function_unpair; PAIR_EQ] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real->real^1`; `b:real->real^1`] THEN
  ABBREV_TAC `(c:real->real^1) x = midpoint(a x,b x)` THEN
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!m n. drop u <= drop(a(&m / &2 pow n)) /\
          drop(a(&m / &2 pow n)) <= drop(b(&m / &2 pow n)) /\
          drop(b(&m / &2 pow n)) <= drop v`
  MP_TAC THENL
   [GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN MATCH_MP_TAC num_INDUCTION THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x / &2 pow 0 = (&2 * x) / &2`] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_LE_REFL];
      X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "*")] THEN
    X_GEN_TAC `p:num` THEN DISJ_CASES_TAC(SPEC `p:num` EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; real_pow] THEN
      ASM_SIMP_TAC[REAL_LT_POW2; REAL_FIELD
       `&0 < y ==> (&2 * x) / (&2 * y) = x / y`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
    DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 0 < n`) THENL
     [ASM_REWRITE_TAC[real_pow; REAL_MUL_RID; REAL_LE_REFL];
      REWRITE_TAC[ADD1]] THEN
    DISJ_CASES_TAC(SPEC `m:num` EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC) THEN
      ASM_SIMP_TAC[ARITH_RULE `2 * 2 * r = 4 * r`];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC) THEN
      ASM_SIMP_TAC[ARITH_RULE `2 * SUC(2 * r) + 1 = 4 * r + 3`]] THEN
    (FIRST_X_ASSUM(MP_TAC o SPECL
      [`a(&(2 * r + 1) / &2 pow n):real^1`;
       `b(&(2 * r + 1) / &2 pow n):real^1`;
       `c(&(2 * r + 1) / &2 pow n):real^1`]) THEN
     ANTS_TAC THENL
      [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
        [GSYM th]) THEN
       REWRITE_TAC[midpoint; IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
       REWRITE_TAC[DROP_CMUL; DROP_ADD] THEN
       UNDISCH_TAC `drop(vec 0) <= drop u` THEN
       UNDISCH_TAC `drop v <= drop (vec 1)`;
       ALL_TAC] THEN
     REMOVE_THEN "*" (MP_TAC o SPEC `2 * r + 1`) THEN REAL_ARITH_TAC);
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `!m n. drop(vec 0) <= drop(a(&m / &2 pow n))` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. drop(b(&m / &2 pow n)) <= drop(vec 1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!m n. drop(a(&m / &2 pow n)) <= drop(c(&m / &2 pow n)) /\
          drop(c(&m / &2 pow n)) <= drop(b(&m / &2 pow n))`
  MP_TAC THENL
   [UNDISCH_THEN `!x:real. midpoint(a x:real^1,b x) = c x`
      (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[midpoint; IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
    ASM_REWRITE_TAC[DROP_CMUL; DROP_ADD; REAL_ARITH
     `a <= inv(&2) * (a + b) /\ inv(&2) * (a + b) <= b <=> a <= b`];
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `!i m n j. ODD j /\
              abs(&i / &2 pow m - &j / &2 pow n) < inv(&2 pow n)
              ==> drop(a(&j / &2 pow n)) <= drop(c(&i / &2 pow m)) /\
                  drop(c(&i / &2 pow m)) <= drop(b(&j / &2 pow n))`
  ASSUME_TAC THENL
   [REPLICATE_TAC 3 GEN_TAC THEN WF_INDUCT_TAC `m - n:num` THEN
    DISJ_CASES_TAC(ARITH_RULE `m <= n \/ n:num < m`) THENL
     [GEN_TAC THEN STRIP_TAC THEN
      MP_TAC(SPEC `abs(&2 pow n) * abs(&i / &2 pow m - &j / &2 pow n)`
                REAL_ABS_INTEGER_LEMMA) THEN
      MATCH_MP_TAC(TAUT
       `i /\ ~b /\ (n ==> p) ==> (i /\ ~n ==> b) ==> p`) THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_ABS_MUL; INTEGER_ABS] THEN
        REWRITE_TAC[REAL_ARITH
         `n * (x / m - y / n):real = x * (n / m) - y * (n / n)`] THEN
        ASM_SIMP_TAC[GSYM REAL_POW_SUB; LE_REFL; REAL_OF_NUM_EQ; ARITH_EQ] THEN
        MESON_TAC[INTEGER_CLOSED];
        SIMP_TAC[REAL_ABS_MUL; REAL_ABS_ABS; REAL_ABS_POW; REAL_ABS_NUM] THEN
        REWRITE_TAC[REAL_ARITH `~(&1 <= x * y) <=> y * x < &1`] THEN
        SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
        ASM_REWRITE_TAC[REAL_ARITH `&1 / x = inv x`];
        ASM_SIMP_TAC[REAL_ABS_POW; REAL_ABS_NUM; REAL_ENTIRE; REAL_LT_IMP_NZ;
          REAL_LT_POW2; REAL_ARITH `abs(x - y) = &0 <=> x = y`]];
      ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[IMP_CONJ; ODD_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
    DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 0 < n`) THENL
     [ASM_REWRITE_TAC[REAL_ARITH `x / &2 pow 0 = (&2 * x) / &2`] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_MUL] THEN ASM_MESON_TAC[REAL_LE_TRANS];
      ALL_TAC] THEN
    UNDISCH_THEN `n:num < m`
      (fun th -> let th' = MATCH_MP
                   (ARITH_RULE `n < m ==> m - SUC n < m - n`) th in
                 FIRST_X_ASSUM(MP_TAC o C MATCH_MP th')) THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH
     `&i / &2 pow m = &(2 * j + 1) / &2 pow n \/
      &i / &2 pow m < &(2 * j + 1) / &2 pow n \/
      &(2 * j + 1) / &2 pow n < &i / &2 pow m`)
    THENL
     [ASM_REWRITE_TAC[ADD1];
      DISCH_THEN(MP_TAC o SPEC `4 * j + 1`) THEN
      REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN ASM_SIMP_TAC[ADD1] THEN
      MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH
         `x < i /\ &2 * n1 = n /\ j + n1 = i
          ==> abs(x - i) < n ==> abs(x - j) < n1`) THEN
        ASM_REWRITE_TAC[REAL_ARITH `a / b + inv b = (a + &1) / b`] THEN
        REWRITE_TAC[real_div; REAL_POW_ADD; REAL_INV_MUL] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH
         `b' <= b ==> a <= c /\ c <= b' ==> a <= c /\ c <= b`) THEN
        FIRST_X_ASSUM(MP_TAC o SPECL
         [`a(&(2 * j + 1) / &2 pow n):real^1`;
          `b(&(2 * j + 1) / &2 pow n):real^1`;
          `c(&(2 * j + 1) / &2 pow n):real^1`]) THEN
        ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
          [GSYM th]) THEN
        REWRITE_TAC[midpoint; IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
        REWRITE_TAC[DROP_CMUL; DROP_ADD] THEN
        ASM_REWRITE_TAC[DROP_CMUL; DROP_ADD; REAL_ARITH
         `a <= inv(&2) * (a + b) /\ inv(&2) * (a + b) <= b <=> a <= b`]];
      DISCH_THEN(MP_TAC o SPEC `4 * j + 3`) THEN
      REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN ASM_SIMP_TAC[ADD1] THEN
      MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH
         `i < x /\ &2 * n1 = n /\ j - n1 = i
          ==> abs(x - i) < n ==> abs(x - j) < n1`) THEN
        ASM_REWRITE_TAC[REAL_ARITH `a / b - inv b = (a - &1) / b`] THEN
        REWRITE_TAC[real_div; REAL_POW_ADD; REAL_INV_MUL] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH
         `a <= a' ==> a' <= c /\ c <= b ==> a <= c /\ c <= b`) THEN
        FIRST_X_ASSUM(MP_TAC o SPECL
         [`a(&(2 * j + 1) / &2 pow n):real^1`;
          `b(&(2 * j + 1) / &2 pow n):real^1`;
          `c(&(2 * j + 1) / &2 pow n):real^1`]) THEN
        ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
          [GSYM th]) THEN
        REWRITE_TAC[midpoint; IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
        REWRITE_TAC[DROP_CMUL; DROP_ADD] THEN
        ASM_REWRITE_TAC[DROP_CMUL; DROP_ADD; REAL_ARITH
         `a <= inv(&2) * (a + b) /\ inv(&2) * (a + b) <= b <=> a <= b`]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m n. ODD m ==> abs(drop(a(&m / &2 pow n)) - drop(b(&m / &2 pow n)))
                    <= &2 / &2 pow n`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THENL
     [ASM_REWRITE_TAC[REAL_ARITH `x / &2 pow 0 = (&2 * x) / &2`] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_MUL] THEN CONV_TAC NUM_REDUCE_CONV THEN
      RULE_ASSUM_TAC(REWRITE_RULE[DROP_VEC]) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `m:num` THEN REWRITE_TAC[ODD_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
    DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 0 < n`) THENL
     [ASM_REWRITE_TAC[ARITH; REAL_POW_1] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[DROP_VEC]) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISJ_CASES_TAC(SPEC `k:num` EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
      REWRITE_TAC[ARITH_RULE `SUC(2 * 2 * j) = 4 * j + 1`] THEN
      ASM_SIMP_TAC[ADD1] THEN
      MATCH_MP_TAC(REAL_ARITH
       `drop c = (drop a + drop b) / &2 /\
        abs(drop a - drop b) <= &2 * k /\
        drop a <= drop(leftcut a b c) /\
        drop(leftcut a b c) <= drop c
        ==> abs(drop a - drop(leftcut a b c)) <= k`);
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
      REWRITE_TAC[ARITH_RULE `SUC(2 * SUC(2 * j)) = 4 * j + 3`] THEN
      ASM_SIMP_TAC[ADD1] THEN
      MATCH_MP_TAC(REAL_ARITH
       `drop c = (drop a + drop b) / &2 /\
        abs(drop a - drop b) <= &2 * k /\
        drop c <= drop(rightcut a b c) /\
        drop(rightcut a b c) <= drop b
        ==> abs(drop(rightcut a b c) - drop b) <= k`)] THEN
    (CONJ_TAC THENL
      [UNDISCH_THEN `!x:real. midpoint(a x:real^1,b x) = c x`
        (fun th -> REWRITE_TAC[GSYM th]) THEN
       REWRITE_TAC[midpoint; DROP_CMUL; DROP_ADD] THEN REAL_ARITH_TAC;
       ALL_TAC] THEN
     CONJ_TAC THENL
      [REWRITE_TAC[real_div; REAL_POW_ADD; REAL_INV_MUL] THEN
       REWRITE_TAC[REAL_ARITH `&2 * x * inv y * inv(&2 pow 1) = x / y`] THEN
       ASM_SIMP_TAC[GSYM real_div; ODD_ADD; ODD_MULT; ARITH];
       ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPECL
      [`a(&(2 * j + 1) / &2 pow n):real^1`;
       `b(&(2 * j + 1) / &2 pow n):real^1`;
       `c(&(2 * j + 1) / &2 pow n):real^1`]) THEN
     ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
     FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
       [GSYM th]) THEN
     REWRITE_TAC[midpoint; IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
     REWRITE_TAC[DROP_CMUL; DROP_ADD] THEN
     ASM_REWRITE_TAC[DROP_CMUL; DROP_ADD; REAL_ARITH
      `a <= inv(&2) * (a + b) /\ inv(&2) * (a + b) <= b <=> a <= b`]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n j. 0 < 2 * j /\ 2 * j < 2 EXP n
          ==> (f:real^1->real^N)(b(&(2 * j - 1) / &2 pow n)) =
              f(a(&(2 * j + 1) / &2 pow n))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `0 < 2 * j <=> 0 < j`;
                  ARITH_RULE `2 * j < 2 <=> j < 1`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "+") THEN
    DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 0 < n`) THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ARITH_RULE `0 < 2 * j <=> 0 < j`;
                   ARITH_RULE `2 * j < 2  <=> j < 1`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISJ_CASES_TAC(SPEC `k:num` EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
      REWRITE_TAC[EXP; ARITH_RULE `0 < 2 * j <=> 0 < j`; LT_MULT_LCANCEL] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[ARITH_RULE `0 < j ==> 2 * 2 * j - 1 = 4 * (j - 1) + 3`;
        ADD1; ARITH_RULE `2 * 2 * j + 1 = 4 * j + 1`] THEN
      SIMP_TAC[ARITH_RULE `0 < j ==> 2 * (j - 1) + 1 = 2 * j - 1`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
      STRIP_TAC THEN
      ASM_SIMP_TAC[ADD1; ARITH_RULE `2 * SUC(2 * j) - 1 = 4 * j + 1`;
                   ARITH_RULE `2 * SUC(2 * j) + 1 = 4 * j + 3`] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`a(&(2 * j + 1) / &2 pow n):real^1`;
        `b(&(2 * j + 1) / &2 pow n):real^1`;
        `c(&(2 * j + 1) / &2 pow n):real^1`]) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
         [GSYM th]) THEN
        REWRITE_TAC[midpoint; IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
        REWRITE_TAC[DROP_CMUL; DROP_ADD] THEN
        ASM_REWRITE_TAC[DROP_CMUL; DROP_ADD; REAL_ARITH
         `a <= inv(&2) * (a + b) /\ inv(&2) * (a + b) <= b <=> a <= b`];
        REPLICATE_TAC 4 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
        MATCH_MP_TAC(MESON[]
         `a IN s /\ b IN s ==> (!x. x IN s ==> f x = c) ==> f a = f b`) THEN
        REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1] THEN
        ASM_MESON_TAC[REAL_LE_TRANS]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n j. 0 < j /\ j < 2 EXP n
          ==> (f:real^1->real^N)(b(&(2 * j - 1) / &2 pow (n + 1))) =
              f(c(&j / &2 pow n)) /\
              f(a(&(2 * j + 1) / &2 pow (n + 1))) = f(c(&j / &2 pow n))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN
    REWRITE_TAC[ARITH_RULE `~(0 < j /\ j < 2 EXP 0)`] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "*") THEN
    X_GEN_TAC `j:num` THEN
    DISJ_CASES_TAC(SPEC `j:num` EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
      REWRITE_TAC[ADD_CLAUSES; EXP; ARITH_RULE `0 < 2 * k <=> 0 < k`;
                  ARITH_RULE `2 * x < 2 * y <=> x < y`] THEN STRIP_TAC THEN
      REMOVE_THEN "*" (MP_TAC o SPEC `k:num`) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(MESON[]
       `c' = c /\ a' = a /\ b' = b
        ==> b = c /\ a = c ==> b' = c' /\ a' = c'`) THEN
      REPEAT CONJ_TAC THEN AP_TERM_TAC THENL
       [AP_TERM_TAC THEN
        REWRITE_TAC[real_pow; real_div; REAL_INV_MUL;
                    GSYM REAL_OF_NUM_MUL] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[ADD1; ARITH_RULE `2 * 2 * n = 4 * n`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
        SUBGOAL_THEN `k = PRE k + 1` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[ARITH_RULE `2 * (k + 1) - 1 = 2 * k + 1`;
                    ARITH_RULE `2 * 2 * (k + 1) - 1 = 4 * k + 3`] THEN
        REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
      REWRITE_TAC[EXP; ARITH_RULE `SUC(2 * k) < 2 * n <=> k < n`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
       [`a(&(2 * k + 1) / &2 pow (SUC n)):real^1`;
        `b(&(2 * k + 1) / &2 pow (SUC n)):real^1`;
        `c(&(2 * k + 1) / &2 pow (SUC n)):real^1`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[midpoint; IN_INTERVAL_1; SUBSET_INTERVAL_1];
        REPLICATE_TAC 4 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)] THEN
      REWRITE_TAC[ARITH_RULE `SUC(2 * k) = 2 * k + 1`] THEN
      DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th) THEN
      ASM_SIMP_TAC[ARITH_RULE `2 * (2 * k + 1) - 1 = 4 * k + 1`; ADD1;
                   ARITH_RULE `2 * (2 * k + 1) + 1 = 4 * k + 3`;
                   ARITH_RULE `0 < n + 1`] THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; GSYM ADD1] THEN
      ASM_SIMP_TAC[ARITH_RULE `SUC(2 * k) = 2 * k + 1`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN
  REWRITE_TAC[COMPACT_INTERVAL] THEN
  MP_TAC(ISPECL [`\x. (f:real^1->real^N)(c(drop x))`;
                 `interval(vec 0,vec 1) INTER
                  {lift(&m / &2 pow n) | m IN (:num) /\ n IN (:num)}`]
        UNIFORMLY_CONTINUOUS_EXTENDS_TO_CLOSURE) THEN
  SIMP_TAC[closure_dyadic_rationals_in_convex_set_pos_1;
           CONVEX_INTERVAL; INTERIOR_OPEN; OPEN_INTERVAL;
           UNIT_INTERVAL_NONEMPTY; IN_INTERVAL_1; REAL_LT_IMP_LE; DROP_VEC;
           CLOSURE_OPEN_INTERVAL] THEN
  REWRITE_TAC[dyadics_in_open_unit_interval] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[uniformly_continuous_on; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN SUBGOAL_THEN
     `(f:real^1->real^N) uniformly_continuous_on interval[vec 0,vec 1]`
    MP_TAC THENL
     [ASM_SIMP_TAC[COMPACT_UNIFORMLY_CONTINUOUS; COMPACT_INTERVAL];
      REWRITE_TAC[uniformly_continuous_on]] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`inv(&2)`; `min (d:real) (&1 / &4)`] REAL_ARCH_POW_INV) THEN
    ASM_REWRITE_TAC[REAL_HALF; REAL_POW_INV; REAL_LT_MIN] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
    EXISTS_TAC `inv(&2 pow n)` THEN
    REWRITE_TAC[REAL_LT_POW2; REAL_LT_INV_EQ] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    SUBGOAL_THEN
     `!i j m. 0 < i /\ i < 2 EXP m /\ 0 < j /\ j < 2 EXP n /\
              abs(&i / &2 pow m - &j / &2 pow n) < inv(&2 pow n)
              ==> norm((f:real^1->real^N)(c(&i / &2 pow m)) -
                       f(c(&j / &2 pow n))) < e / &2`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC o MATCH_MP (REAL_ARITH
       `abs(x - a) < e
        ==> x = a \/
            abs(x - (a - e / &2)) < e / &2 \/
            abs(x - (a + e / &2)) < e / &2`))
      THENL
       [DISCH_THEN SUBST1_TAC THEN
        ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_HALF];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `&j / &2 pow n = &(2 * j) / &2 pow (n + 1)`
       (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
      THENL
       [REWRITE_TAC[REAL_POW_ADD; real_div; REAL_INV_MUL;
                    GSYM REAL_OF_NUM_MUL] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[real_div; GSYM REAL_INV_MUL] THEN
      REWRITE_TAC[GSYM real_div;
           GSYM(ONCE_REWRITE_RULE[REAL_MUL_SYM] (CONJUNCT2 real_pow))] THEN
      REWRITE_TAC[ADD1; REAL_ARITH `x / n + inv n = (x + &1) / n`;
                  REAL_ARITH `x / n - inv n = (x - &1) / n`] THEN
      ASM_SIMP_TAC[REAL_OF_NUM_SUB; ARITH_RULE `0 < j ==> 1 <= 2 * j`] THEN
      REWRITE_TAC[REAL_OF_NUM_ADD] THEN STRIP_TAC THENL
       [SUBGOAL_THEN `(f:real^1->real^N)(c(&j / &2 pow n)) =
                      f(b (&(2 * j - 1) / &2 pow (n + 1)))`
        SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC];
        SUBGOAL_THEN `(f:real^1->real^N)(c(&j / &2 pow n)) =
                      f(a (&(2 * j + 1) / &2 pow (n + 1)))`
        SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC]] THEN
      REWRITE_TAC[GSYM dist] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_INTERVAL_1] THEN
      REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC]) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `m:num`; `n + 1`]) THENL
       [DISCH_THEN(MP_TAC o SPEC `2 * j - 1`) THEN REWRITE_TAC[ODD_SUB];
        DISCH_THEN(MP_TAC o SPEC `2 * j + 1`) THEN REWRITE_TAC[ODD_ADD]] THEN
      ASM_REWRITE_TAC[ODD_MULT; ARITH; ARITH_RULE `1 < 2 * j <=> 0 < j`] THEN
      REWRITE_TAC[DIST_REAL; GSYM drop] THENL
       [MATCH_MP_TAC(NORM_ARITH
         `!t. abs(a - b) <= t /\ t < d
              ==> a <= c /\ c <= b ==> abs(c - b) < d`);
        MATCH_MP_TAC(NORM_ARITH
         `!t. abs(a - b) <= t /\ t < d
              ==> a <= c /\ c <= b ==> abs(c - a) < d`)] THEN
      EXISTS_TAC `&2 / &2 pow (n + 1)` THEN
      (CONJ_TAC THENL
        [FIRST_X_ASSUM MATCH_MP_TAC THEN
         REWRITE_TAC[ODD_SUB; ODD_ADD; ODD_MULT; ARITH_ODD] THEN
         ASM_REWRITE_TAC[ARITH_RULE `1 < 2 * j <=> 0 < j`];
         REWRITE_TAC[REAL_POW_ADD; real_div; REAL_INV_MUL] THEN
         ASM_REAL_ARITH_TAC]);
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `m:num`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `p:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[DIST_LIFT; LIFT_DROP] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?j. 0 < j /\ j < 2 EXP n /\
          abs(&i / &2 pow m - &j / &2 pow n) < inv(&2 pow n) /\
          abs(&k / &2 pow p - &j / &2 pow n) < inv(&2 pow n)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `max (&2 pow n * &i / &2 pow m)
                       (&2 pow n * &k / &2 pow p)`
        FLOOR_POS) THEN
      SIMP_TAC[REAL_LE_MUL; REAL_LE_MAX; REAL_LE_DIV;
               REAL_POS; REAL_POW_LE] THEN
      DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN
      MP_TAC(SPEC `max (&2 pow n * &i / &2 pow m)
                       (&2 pow n * &k / &2 pow p)` FLOOR) THEN
      ASM_REWRITE_TAC[REAL_LE_MAX; REAL_MAX_LT] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      SIMP_TAC[GSYM REAL_LE_LDIV_EQ; GSYM REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
      REWRITE_TAC[REAL_ARITH `(j + &1) / n = j / n + inv n`] THEN
      ASM_CASES_TAC `j = 0` THENL
       [ASM_REWRITE_TAC[REAL_ARITH `&0 / x = &0`; REAL_ADD_LID] THEN
        DISCH_TAC THEN EXISTS_TAC `1` THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[ARITH_RULE `1 < n <=> 2 EXP 1 <= n`] THEN
        ASM_SIMP_TAC[LE_EXP; LE_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 < x /\ x < inv n /\ &0 < y /\ y < inv n
          ==> abs(x - &1 / n) < inv n /\ abs(y - &1 / n) < inv n`) THEN
        ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; REAL_LT_POW2];
        DISCH_TAC THEN EXISTS_TAC `j:num` THEN ASM_SIMP_TAC[LE_1] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_POW] THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
        SIMP_TAC[GSYM REAL_NOT_LE; REAL_LE_FLOOR; INTEGER_CLOSED] THEN
        REWRITE_TAC[REAL_NOT_LE; REAL_MAX_LT] THEN
        REWRITE_TAC[REAL_ARITH `n * x < n <=> n * x < n * &1`] THEN
        SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_POW2; REAL_LT_LDIV_EQ] THEN
        ASM_REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_POW; REAL_OF_NUM_LT]];
      MATCH_MP_TAC(NORM_ARITH
       `!u. dist(w:real^N,u) < e / &2 /\ dist(z,u) < e / &2
            ==> dist(w,z) < e`) THEN
      EXISTS_TAC `(f:real^1->real^N)(c(&j / &2 pow n))` THEN
      REWRITE_TAC[dist] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^1->real^N` THEN
  REWRITE_TAC[FORALL_IN_GSPEC; LIFT_DROP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT1)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS) THEN
  ONCE_REWRITE_TAC[MESON[] `h x = f(c(drop x)) <=> f(c(drop x)) = h x`] THEN
  REWRITE_TAC[IN_INTER; IMP_CONJ_ALT; FORALL_IN_GSPEC] THEN
  ASM_REWRITE_TAC[IN_UNIV; LIFT_DROP; IMP_IMP; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
  SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_LT_POW2] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `interval(vec 0:real^1,vec 1)`
        closure_dyadic_rationals_in_convex_set_pos_1) THEN
      SIMP_TAC[CONVEX_INTERVAL; IN_INTERVAL_1; REAL_LT_IMP_LE; DROP_VEC;
        INTERIOR_OPEN; OPEN_INTERVAL; INTERVAL_NE_EMPTY_1; REAL_LT_01;
        CLOSURE_OPEN_INTERVAL] THEN
      DISCH_THEN(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
      MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_INTERVAL] THEN
        MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s INTER t SUBSET u`) THEN
        REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED];
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        ASM_REWRITE_TAC[COMPACT_INTERVAL];
        SIMP_TAC[dyadics_in_open_unit_interval; SUBSET; FORALL_IN_IMAGE] THEN
        ASM_SIMP_TAC[FORALL_IN_GSPEC] THEN
        MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTERVAL_1] THEN
        ASM_MESON_TAC[REAL_LE_TRANS]];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `closure(IMAGE (h:real^1->real^N)
                                 (interval (vec 0,vec 1) INTER
        {lift (&m / &2 pow n) | m IN (:num) /\ n IN (:num)}))` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC CLOSURE_MINIMAL THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_INTERVAL;
                     COMPACT_CONTINUOUS_IMAGE] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN
        MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s INTER t SUBSET u`) THEN
        REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED]] THEN
      REWRITE_TAC[SUBSET; CLOSURE_APPROACHABLE; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[dyadics_in_open_unit_interval;
                  EXISTS_IN_IMAGE; EXISTS_IN_GSPEC] THEN
      X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN UNDISCH_TAC
       `(f:real^1->real^N) continuous_on interval [vec 0,vec 1]` THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        COMPACT_UNIFORMLY_CONTINUOUS)) THEN
      REWRITE_TAC[COMPACT_INTERVAL; uniformly_continuous_on] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `!n. ~(n = 0)
            ==> ?m y. ODD m /\ 0 < m /\ m < 2 EXP n /\
                      y IN interval[a(&m / &2 pow n),b(&m / &2 pow n)] /\
                     (f:real^1->real^N) y = f x`
      MP_TAC THENL
       [ALL_TAC;
        MP_TAC(SPECL [`inv(&2)`; `min (d / &2) (&1 / &4)`]
         REAL_ARCH_POW_INV) THEN
        ASM_REWRITE_TAC[REAL_HALF; REAL_POW_INV; REAL_LT_MIN] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
        ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
        DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^1` MP_TAC) THEN
        REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN EXISTS_TAC `n:num` THEN
        ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
        REWRITE_TAC[DIST_REAL; GSYM drop; IN_INTERVAL_1] THEN
        REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC]) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `a <= y /\ y <= b
          ==> a <= c /\ c <= b /\ abs(a - b) < d
              ==> abs(c - y) < d`)) THEN
        REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC]) THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 / &2 pow n` THEN
        ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[NOT_SUC] THEN
      X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
       [EXISTS_TAC `1` THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_REWRITE_TAC[REAL_POW_1] THEN
        SUBGOAL_THEN
         `x IN interval[vec 0:real^1,u] \/
          x IN interval[u,v] \/
          x IN interval[v,vec 1]`
        STRIP_ASSUME_TAC THENL
         [REWRITE_TAC[IN_INTERVAL_1] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
          ASM_REAL_ARITH_TAC;
          EXISTS_TAC `u:real^1` THEN
          ASM_MESON_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1];
          EXISTS_TAC `x:real^1` THEN ASM_MESON_TAC[];
          EXISTS_TAC `v:real^1` THEN
          ASM_MESON_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1]];
        DISCH_THEN(X_CHOOSE_THEN `m:num`
         (X_CHOOSE_THEN `y:real^1` MP_TAC)) THEN
        REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
        DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THEN
        REWRITE_TAC[ADD1] THEN DISCH_TAC THEN
        SUBGOAL_THEN
        `y IN interval[a(&(2 * j + 1) / &2 pow n):real^1,
                       b(&(4 * j + 1) / &2 pow (n + 1))] \/
         y IN interval[b(&(4 * j + 1) / &2 pow (n + 1)),
                       a(&(4 * j + 3) / &2 pow (n + 1))] \/
         y IN interval[a(&(4 * j + 3) / &2 pow (n + 1)),
                       b(&(2 * j + 1) / &2 pow n)]`
        STRIP_ASSUME_TAC THENL
         [REWRITE_TAC[IN_INTERVAL_1] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
          ASM_REAL_ARITH_TAC;
          EXISTS_TAC `4 * j + 1` THEN
          EXISTS_TAC `y:real^1` THEN
          REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH; EXP_ADD] THEN
          REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
           `y IN interval[a,b]
            ==> a = a' /\ b = b' ==> y IN interval[a',b']`)) THEN
          ASM_MESON_TAC[LE_1];
          EXISTS_TAC `4 * j + 1` THEN
          EXISTS_TAC `b(&(4 * j + 1) / &2 pow (n + 1)):real^1` THEN
          REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH; EXP_ADD] THEN
          REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
          REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1] THEN
          CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
          FIRST_X_ASSUM(MP_TAC o SPECL
           [`a(&(2 * j + 1) / &2 pow n):real^1`;
            `b(&(2 * j + 1) / &2 pow n):real^1`;
            `c(&(2 * j + 1) / &2 pow n):real^1`]) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[midpoint; IN_INTERVAL_1; SUBSET_INTERVAL_1];
            REPLICATE_TAC 4
             (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
            DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)] THEN
          MATCH_MP_TAC(MESON[]
           `a IN s /\ b IN s ==> (!x. x IN s ==> f x = k) ==> f a = f b`) THEN
          SUBGOAL_THEN
           `leftcut (a (&(2 * j + 1) / &2 pow n))
                    (b (&(2 * j + 1) / &2 pow n))
                    (c (&(2 * j + 1) / &2 pow n):real^1):real^1 =
            b(&(4 * j + 1) / &2 pow (n + 1)) /\
            rightcut (a (&(2 * j + 1) / &2 pow n))
                     (b (&(2 * j + 1) / &2 pow n))
                     (c (&(2 * j + 1) / &2 pow n)):real^1 =
            a(&(4 * j + 3) / &2 pow (n + 1))`
          (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
            [ASM_MESON_TAC[LE_1]; ALL_TAC] THEN
          REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1] THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
           `y IN interval[a,b]
            ==> a = a' /\ b = b' ==> y IN interval[a',b']`)) THEN
          ASM_MESON_TAC[LE_1];
          EXISTS_TAC `4 * j + 3` THEN
          EXISTS_TAC `y:real^1` THEN
          REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH; EXP_ADD] THEN
          REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
           `y IN interval[a,b]
            ==> a = a' /\ b = b' ==> y IN interval[a',b']`)) THEN
          ASM_MESON_TAC[LE_1]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n m. drop(a(&m / &2 pow n)) < drop(b(&m / &2 pow n)) /\
          (!x. drop(a(&m / &2 pow n)) < drop x /\
               drop x <= drop(b(&m / &2 pow n))
               ==> ~(f x = f(a(&m / &2 pow n)))) /\
          (!x. drop(a(&m / &2 pow n)) <= drop x /\
               drop x < drop(b(&m / &2 pow n))
               ==> ~(f x :real^N = f(b(&m / &2 pow n))))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `drop u < drop v` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_LE; DROP_EQ] THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [IN_DELETE; IN_INTERVAL_1; GSYM DROP_EQ; DROP_VEC]) THEN
      ASM_MESON_TAC[DROP_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(!x. drop u < drop x /\ drop x <= drop v
          ==> ~((f:real^1->real^N) x = f u)) /\
      (!x. drop u <= drop x /\ drop x < drop v
           ==> ~(f x = f v))`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN
       `(f:real^1->real^N) u = f(vec 0) /\
        (f:real^1->real^N) v = f(vec 1)`
       (CONJUNCTS_THEN SUBST1_TAC)
      THENL
       [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL];
        ALL_TAC] THEN
      CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_DELETE; IN_INTERVAL_1; GSYM DROP_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC num_INDUCTION THEN
    ASM_REWRITE_TAC[REAL_ARITH `&m / &2 pow 0 = (&2 * &m) / &2`] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_MUL] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "*") THEN
    DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 0 < n`) THEN
    ASM_REWRITE_TAC[ARITH; REAL_POW_1] THEN
    X_GEN_TAC `j:num` THEN
    DISJ_CASES_TAC(ISPEC `j:num` EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
      SIMP_TAC[GSYM REAL_OF_NUM_MUL; real_div; REAL_INV_MUL; real_pow] THEN
      ASM_REWRITE_TAC[REAL_ARITH `(&2 * p) * inv(&2) * inv q = p / q`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
    DISJ_CASES_TAC(ISPEC `k:num` EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
      ASM_SIMP_TAC[ARITH_RULE `2 * 2 * m = 4 * m`; ADD1] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`a(&(2 * m + 1) / &2 pow n):real^1`;
        `b(&(2 * m + 1) / &2 pow n):real^1`;
        `c(&(2 * m + 1) / &2 pow n):real^1`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
        ASM_MESON_TAC[REAL_LE_TRANS];
        REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(K ALL_TAC)] THEN
      SUBGOAL_THEN
       `(f:real^1->real^N)
        (leftcut (a (&(2 * m + 1) / &2 pow n):real^1)
                 (b (&(2 * m + 1) / &2 pow n):real^1)
                 (c (&(2 * m + 1) / &2 pow n):real^1)) =
        (f:real^1->real^N) (c(&(2 * m + 1) / &2 pow n))`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_LT_LE] THEN ASM_REWRITE_TAC[DROP_EQ] THEN
      REPEAT CONJ_TAC THENL
       [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        UNDISCH_THEN
         `(f:real^1->real^N) (a (&(2 * m + 1) / &2 pow n)) =
          f(c (&(2 * m + 1) / &2 pow n))` (MP_TAC o SYM) THEN
        REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o SPEC_ALL) THEN
        REWRITE_TAC[GSYM(ASSUME `!x. midpoint ((a:real->real^1) x,b x) = c x`);
                    midpoint; DROP_CMUL; DROP_ADD] THEN
        ASM_REWRITE_TAC[REAL_ARITH
         `a < inv(&2) * (a + b) /\ inv(&2) * (a + b) <= b <=> a < b`];
        GEN_TAC THEN STRIP_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o SPEC_ALL) THEN
        ASM_MESON_TAC[REAL_LE_TRANS];
        GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM
         (fun th -> MATCH_MP_TAC th THEN
                    REWRITE_TAC[IN_INTERVAL_1; IN_DELETE; GSYM DROP_EQ] THEN
             GEN_REWRITE_TAC I [REAL_ARITH
              `(a <= x /\ x <= b) /\ ~(x = b) <=> a <= x /\ x < b`]) THEN
        ASM_REWRITE_TAC[]];
       FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
       DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
       ASM_SIMP_TAC[ARITH_RULE `2 * (2 * m + 1) + 1  = 4 * m + 3`; ADD1] THEN
       FIRST_X_ASSUM(MP_TAC o SPECL
        [`a(&(2 * m + 1) / &2 pow n):real^1`;
         `b(&(2 * m + 1) / &2 pow n):real^1`;
         `c(&(2 * m + 1) / &2 pow n):real^1`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
        ASM_MESON_TAC[REAL_LE_TRANS];
        REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(K ALL_TAC)] THEN
      SUBGOAL_THEN
       `(f:real^1->real^N)
        (rightcut (a (&(2 * m + 1) / &2 pow n):real^1)
                  (b (&(2 * m + 1) / &2 pow n):real^1)
                  (c (&(2 * m + 1) / &2 pow n):real^1)) =
        (f:real^1->real^N) (c(&(2 * m + 1) / &2 pow n))`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_LT_LE] THEN ASM_REWRITE_TAC[DROP_EQ] THEN
      REPEAT CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_THEN
         `(f:real^1->real^N) (b (&(2 * m + 1) / &2 pow n)) =
          f(c (&(2 * m + 1) / &2 pow n))` (MP_TAC o SYM) THEN
        REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC_ALL) THEN
        REWRITE_TAC[GSYM(ASSUME `!x. midpoint ((a:real->real^1) x,b x) = c x`);
                    midpoint; DROP_CMUL; DROP_ADD] THEN
        ASM_REWRITE_TAC[REAL_ARITH
         `a <= inv(&2) * (a + b) /\ inv(&2) * (a + b) < b <=> a < b`];
        GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM
         (fun th -> MATCH_MP_TAC th THEN
                    REWRITE_TAC[IN_INTERVAL_1; IN_DELETE; GSYM DROP_EQ] THEN
             GEN_REWRITE_TAC I [REAL_ARITH
              `(a <= x /\ x <= b) /\ ~(x = a) <=> a < x /\ x <= b`]) THEN
        ASM_REWRITE_TAC[];
        GEN_TAC THEN STRIP_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC_ALL) THEN
        ASM_MESON_TAC[REAL_LE_TRANS]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m i n j. 0 < i /\ i < 2 EXP m /\ 0 < j /\ j < 2 EXP n /\
              &i / &2 pow m < &j / &2 pow n
              ==> drop(c(&i / &2 pow m)) <= drop(c(&j / &2 pow n))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!N m p i k.
         0 < i /\ i < 2 EXP m /\ 0 < k /\ k < 2 EXP p /\
         &i / &2 pow m < &k / &2 pow p /\ m + p = N
         ==> ?j n. ODD(j) /\ ~(n = 0) /\
                   &i / &2 pow m <= &j / &2 pow n /\
                   &j / &2 pow n <= &k / &2 pow p /\
                   abs(&i / &2 pow m - &j / &2 pow n) < inv(&2 pow n) /\
                   abs(&k / &2 pow p - &j / &2 pow n) < inv(&2 pow n)`
    MP_TAC THENL
     [MATCH_MP_TAC num_WF THEN X_GEN_TAC `N:num` THEN
      DISCH_THEN(LABEL_TAC "I") THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `p:num`; `i:num`; `k:num`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN
       `&i / &2 pow m <= &1 / &2 pow 1 /\
        &1 / &2 pow 1 <= &k / &2 pow p \/
        &k / &2 pow p < &1 / &2 \/
        &1 / &2 < &i / &2 pow m`
       (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC)
      THENL
       [ASM_REAL_ARITH_TAC;
        MAP_EVERY EXISTS_TAC [`1`; `1`] THEN ASM_REWRITE_TAC[ARITH] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 < i /\ i <= &1 / &2 pow 1 /\ &1 / &2 pow 1 <= k /\ k < &1
          ==> abs(i -  &1 / &2 pow 1) < inv(&2 pow 1) /\
              abs(k -  &1 / &2 pow 1) < inv(&2 pow 1)`) THEN
        ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_LT_POW2] THEN
        REWRITE_TAC[MULT_CLAUSES; REAL_OF_NUM_POW; REAL_OF_NUM_MUL] THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LT];
        REMOVE_THEN "I" MP_TAC THEN
        POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
        SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THEN
        REWRITE_TAC[ARITH_RULE `i < 2 EXP 0 <=> ~(0 < i)`] THEN
        REWRITE_TAC[TAUT `p /\ ~p /\ q <=> F`] THEN POP_ASSUM(K ALL_TAC) THEN
        SPEC_TAC(`p:num`,`p:num`) THEN INDUCT_TAC THEN
        REWRITE_TAC[ARITH_RULE `i < 2 EXP 0 <=> ~(0 < i)`] THEN
        REWRITE_TAC[TAUT `p /\ ~p /\ q <=> F`] THEN POP_ASSUM(K ALL_TAC) THEN
        STRIP_TAC THEN DISCH_THEN(MP_TAC o SPEC `m + p:num`) THEN
        ANTS_TAC THENL [EXPAND_TAC "N" THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`m:num`; `p:num`; `i:num`; `k:num`]) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [`&k / &2 pow SUC p < &1 / &2`;
            `&i / &2 pow SUC m < &k / &2 pow SUC p`] THEN
          REWRITE_TAC[real_div; real_pow; REAL_INV_MUL;
                      REAL_ARITH `x * inv(&2) * y = (x * y) * inv(&2)`] THEN
          SIMP_TAC[GSYM real_div; REAL_LT_DIV2_EQ; REAL_OF_NUM_LT; ARITH] THEN
          REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
           `x < y /\ y < &1 ==> x < &1 /\ y < &1`)) THEN
          SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_POW2; REAL_MUL_LID] THEN
          REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT];
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:num` THEN
          DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
          EXISTS_TAC `SUC n` THEN ASM_REWRITE_TAC[NOT_SUC] THEN
          REWRITE_TAC[real_div; real_pow; REAL_INV_MUL;
                      REAL_ARITH `inv(&2) * y = y * inv(&2)`] THEN
          REWRITE_TAC[GSYM REAL_SUB_RDISTRIB; REAL_MUL_ASSOC;
                      REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
          REWRITE_TAC[GSYM real_div; REAL_ABS_NUM] THEN
          ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_DIV2_EQ;
                       REAL_OF_NUM_LT; ARITH]];
        REMOVE_THEN "I" MP_TAC THEN
        POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
        SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THEN
        REWRITE_TAC[ARITH_RULE `i < 2 EXP 0 <=> ~(0 < i)`] THEN
        REWRITE_TAC[TAUT `p /\ ~p /\ q <=> F`] THEN POP_ASSUM(K ALL_TAC) THEN
        SPEC_TAC(`p:num`,`p:num`) THEN INDUCT_TAC THEN
        REWRITE_TAC[ARITH_RULE `i < 2 EXP 0 <=> ~(0 < i)`] THEN
        REWRITE_TAC[TAUT `p /\ ~p /\ q <=> F`] THEN POP_ASSUM(K ALL_TAC) THEN
        STRIP_TAC THEN DISCH_THEN(MP_TAC o SPEC `m + p:num`) THEN
        ANTS_TAC THENL [EXPAND_TAC "N" THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL
         [`m:num`; `p:num`; `i - 2 EXP m`; `k - 2 EXP p`]) THEN
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC
         [`&1 / &2 < &i / &2 pow SUC m`;
          `&i / &2 pow SUC m < &k / &2 pow SUC p`] THEN
        REWRITE_TAC[real_div; real_pow; REAL_INV_MUL;
                    REAL_ARITH `x * inv(&2) * y = (x * y) * inv(&2)`] THEN
        SIMP_TAC[GSYM real_div; REAL_LT_DIV2_EQ; REAL_OF_NUM_LT; ARITH] THEN
        GEN_REWRITE_TAC I [IMP_IMP] THEN DISCH_THEN(fun th ->
          STRIP_ASSUME_TAC th THEN MP_TAC(MATCH_MP
           (REAL_ARITH `i < k /\ &1 < i ==> &1 < i /\ &1 < k`) th)) THEN
        SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_POW2; REAL_MUL_LID] THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_OF_NUM_POW] THEN
        SIMP_TAC[REAL_OF_NUM_LT; GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
        STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN ANTS_TAC THENL
         [ASM_SIMP_TAC[ARITH_RULE `a < b ==> 0 < b - a`] THEN
          ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
          REWRITE_TAC[real_div; REAL_SUB_RDISTRIB] THEN
          ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LT_POW2] THEN
          ASM_REWRITE_TAC[REAL_ARITH `u * inv v - &1 < w * inv z - &1 <=>
                                      u / v < w / z`] THEN
          CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
           `i < 2 * m ==> i - m < m`) THEN
          ASM_REWRITE_TAC[GSYM(CONJUNCT2 EXP)];
          REWRITE_TAC[real_div; REAL_SUB_RDISTRIB] THEN
          ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LT_POW2] THEN
          REWRITE_TAC[GSYM real_div] THEN
          DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `n:num`
           STRIP_ASSUME_TAC)) THEN
          EXISTS_TAC `2 EXP n + j` THEN EXISTS_TAC `SUC n` THEN
          ASM_REWRITE_TAC[NOT_SUC; ODD_ADD; ODD_EXP; ARITH] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
          REWRITE_TAC[real_div; real_pow; REAL_INV_MUL;
                      REAL_ARITH `inv(&2) * y = y * inv(&2)`] THEN
          REWRITE_TAC[GSYM REAL_SUB_RDISTRIB; REAL_MUL_ASSOC;
                      REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
          REWRITE_TAC[GSYM real_div; REAL_ABS_NUM] THEN
          ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_DIV2_EQ;
                       REAL_OF_NUM_LT; ARITH] THEN
          REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN
          ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LT_POW2] THEN
          REWRITE_TAC[GSYM real_div] THEN ASM_REAL_ARITH_TAC]];
      DISCH_THEN(fun th ->
       MAP_EVERY X_GEN_TAC [`m:num`; `i:num`; `p:num`; `k:num`] THEN
       STRIP_TAC THEN MP_TAC(ISPECL
        [`m + p:num`; `m:num`; `p:num`; `i:num`; `k:num`] th)) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
      REWRITE_TAC[ADD1; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `q:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `drop(c(&(2 * q + 1) / &2 pow n))` THEN CONJ_TAC THENL
       [ASM_CASES_TAC `&i / &2 pow m = &(2 * q + 1) / &2 pow n` THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        SUBGOAL_THEN
         `drop(a(&(4 * q + 1) / &2 pow (n + 1))) <= drop(c(&i / &2 pow m)) /\
          drop(c(&i / &2 pow m)) <= drop(b(&(4 * q + 1) / &2 pow (n + 1)))`
        MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN
          SIMP_TAC[real_div; REAL_POW_ADD; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
          REWRITE_TAC[GSYM real_div; REAL_POW_1] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `abs(i - q) < n
            ==> i <= q /\ ~(i = q) /\ q = q' + n / &2
                ==> abs(i - q') < n / &2`)) THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
          REAL_ARITH_TAC;
          ASM_SIMP_TAC[LE_1] THEN MATCH_MP_TAC(REAL_ARITH
           `l <= d ==> u <= v /\ c <= l ==> c <= d`) THEN
          FIRST_X_ASSUM(MP_TAC o SPECL
           [`a(&(2 * q + 1) / &2 pow n):real^1`;
            `b(&(2 * q + 1) / &2 pow n):real^1`;
            `c(&(2 * q + 1) / &2 pow n):real^1`]) THEN
          ANTS_TAC THENL
           [REWRITE_TAC[IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
            ASM_MESON_TAC[REAL_LE_TRANS];
            DISCH_THEN(fun th -> REWRITE_TAC[th])]];
        ASM_CASES_TAC `&k / &2 pow p = &(2 * q + 1) / &2 pow n` THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        SUBGOAL_THEN
         `drop(a(&(4 * q + 3) / &2 pow (n + 1))) <= drop(c(&k / &2 pow p)) /\
          drop(c(&k / &2 pow p)) <= drop(b(&(4 * q + 3) / &2 pow (n + 1)))`
        MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN
          SIMP_TAC[real_div; REAL_POW_ADD; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
          REWRITE_TAC[GSYM real_div; REAL_POW_1] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `abs(i - q) < n
            ==> q <= i /\ ~(i = q) /\ q' = q +  n / &2
                ==> abs(i - q') < n / &2`)) THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
          REAL_ARITH_TAC;
          ASM_SIMP_TAC[LE_1] THEN MATCH_MP_TAC(REAL_ARITH
           `d <= l ==> l <= c /\ u <= v ==> d <= c`) THEN
          FIRST_X_ASSUM(MP_TAC o SPECL
           [`a(&(2 * q + 1) / &2 pow n):real^1`;
            `b(&(2 * q + 1) / &2 pow n):real^1`;
            `c(&(2 * q + 1) / &2 pow n):real^1`]) THEN
          ANTS_TAC THENL
           [REWRITE_TAC[IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
            ASM_MESON_TAC[REAL_LE_TRANS];
            DISCH_THEN(fun th -> REWRITE_TAC[th])]]]];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_LIFT] THEN MATCH_MP_TAC REAL_WLOG_LT THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_DROP; LIFT_DROP; IN_INTERVAL_1; DROP_VEC] THEN
  MAP_EVERY X_GEN_TAC [`x1:real^1`; `x2:real^1`] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?m n. 0 < m /\ m < 2 EXP n /\
          drop x1 < &m / &2 pow n /\ &m / &2 pow n < drop x2 /\
          ~(h(x1):real^N = h(lift(&m / &2 pow n)))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `interval(vec 0:real^1,vec 1)`
        closure_dyadic_rationals_in_convex_set_pos_1) THEN
    SIMP_TAC[CONVEX_INTERVAL; IN_INTERVAL_1; REAL_LT_IMP_LE; DROP_VEC;
            INTERIOR_OPEN; OPEN_INTERVAL; INTERVAL_NE_EMPTY_1; REAL_LT_01;
            CLOSURE_OPEN_INTERVAL] THEN
    REWRITE_TAC[EXTENSION] THEN
    DISCH_THEN(MP_TAC o SPEC `inv(&2) % (x1 + x2):real^1`) THEN
    REWRITE_TAC[dyadics_in_open_unit_interval; IN_INTERVAL_1; DROP_VEC] THEN
    REWRITE_TAC[DROP_CMUL; DROP_ADD] THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (q <=> p) ==> r`) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[CLOSURE_APPROACHABLE]] THEN
    DISCH_THEN(MP_TAC o SPEC `(drop x2 - drop x1) / &64`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[EXISTS_IN_GSPEC]] THEN
    REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP; DROP_CMUL; DROP_ADD] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `?m n. (0 < m /\ m < 2 EXP n) /\
            abs(&m / &2 pow n - inv (&2) * (drop x1 + drop x2)) <
            (drop x2 - drop x1) / &64 /\
            inv(&2 pow n) < (drop x2 - drop x1) / &128`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`inv(&2)`; `min (&1 / &4) ((drop x2 - drop x1) / &128)`]
      REAL_ARCH_POW_INV) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN
      ASM_CASES_TAC `N = 0` THENL
       [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_INV_POW; REAL_LT_MIN; EXISTS_IN_GSPEC] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `n:num`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `2 EXP N * m` THEN EXISTS_TAC `N + n:num` THEN
      ASM_SIMP_TAC[EXP_ADD; LT_MULT; EXP_LT_0; LT_MULT_LCANCEL; LE_1;
                   ARITH_EQ] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_POW_ADD; real_div; REAL_INV_MUL] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; REAL_ARITH
         `(N * n) * inv N * inv m:real = (N / N) * (n / m)`] THEN
        ASM_SIMP_TAC[REAL_DIV_REFL; REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ;
                     REAL_MUL_LID; GSYM real_div];
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&2) pow N` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LE_ADD]];
      REWRITE_TAC[CONJ_ASSOC] THEN MATCH_MP_TAC(MESON[]
       `!m n m' n'. (P m n /\ P m' n') /\
                    (P m n /\ P m' n' ==> ~(g m n = g m' n'))
        ==> (?m n. P m n /\ ~(a = g m n))`) THEN
      MAP_EVERY EXISTS_TAC
       [`2 * m + 1`; `n + 1`; `4 * m + 3`; `n + 2`] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THEN
        (REWRITE_TAC[GSYM CONJ_ASSOC] THEN
         REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC])) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `abs(x - inv(&2) * (x1 + x2)) < (x2 - x1) / &64
          ==> abs(x - y) < (x2 - x1) / &4
              ==> x1 < y /\ y < x2`)) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `n < x / &128 ==> &0 < x /\ y < &4 * n ==> y < x / &4`)) THEN
        ASM_REWRITE_TAC[REAL_SUB_LT] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
        MATCH_MP_TAC(REAL_ARITH
         `a / y = x /\ abs(b / y) < z
          ==> abs(x - (a + b) / y) < z`) THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[REAL_POW_ADD] THEN
        SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_MUL; REAL_ABS_POW] THEN
        REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
        SIMP_TAC[REAL_LT_RMUL_EQ; REAL_EQ_MUL_RCANCEL; REAL_LT_INV_EQ;
           REAL_LT_POW2; REAL_INV_EQ_0; REAL_POW_EQ_0; ARITH_EQ;
           REAL_OF_NUM_EQ] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
        FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o SPECL [`n + 2`; `4 * m + 3`]) THEN
        UNDISCH_THEN `!x. midpoint ((a:real->real^1) x,b x) = c x`
         (fun th -> REWRITE_TAC[GSYM th] THEN
              ASM_SIMP_TAC[ARITH_RULE `n + 2 = (n + 1) + 1 /\ 0 < n + 1`] THEN
              REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
        DISCH_TAC THEN
        CONV_TAC(RAND_CONV SYM_CONV) THEN
        FIRST_X_ASSUM(MP_TAC o SPECL
         [`a(&(2 * m + 1) / &2 pow (n + 1)):real^1`;
          `b(&(2 * m + 1) / &2 pow (n + 1)):real^1`;
          `c(&(2 * m + 1) / &2 pow (n + 1)):real^1`]) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[IN_INTERVAL_1; SUBSET_INTERVAL_1] THEN
          ASM_MESON_TAC[REAL_LE_TRANS];
          REPLICATE_TAC 6 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
          DISCH_THEN(MATCH_MP_TAC o CONJUNCT1)] THEN
        REWRITE_TAC[IN_INTERVAL_1; IN_DELETE; GSYM DROP_EQ] THEN
        REWRITE_TAC[REAL_ARITH
         `(a <= b /\ b <= c) /\ ~(b = a) <=> a < b /\ b <= c`] THEN
        REWRITE_TAC[midpoint; DROP_CMUL; DROP_ADD] THEN
        ASM_REWRITE_TAC[REAL_ARITH
           `a < inv(&2) * (a + b) /\ inv(&2) * (a + b) <= b <=> a < b`] THEN
        ASM_REWRITE_TAC[REAL_LT_LE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE h (interval[vec 0,lift(&m / &2 pow n)]) SUBSET
    IMAGE (f:real^1->real^N) (interval[vec 0,c(&m / &2 pow n)]) /\
    IMAGE h (interval[lift(&m / &2 pow n),vec 1]) SUBSET
    IMAGE (f:real^1->real^N) (interval[c(&m / &2 pow n),vec 1])`
  MP_TAC THENL
   [MP_TAC(ISPEC `interval(lift(&m / &2 pow n),vec 1)`
      closure_dyadic_rationals_in_convex_set_pos_1) THEN
    MP_TAC(ISPEC `interval(vec 0,lift(&m / &2 pow n))`
      closure_dyadic_rationals_in_convex_set_pos_1) THEN
    SUBGOAL_THEN `&0 < &m / &2 pow n /\ &m / &2 pow n < &1`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_POW2; REAL_OF_NUM_LT; REAL_LT_LDIV_EQ;
        REAL_OF_NUM_MUL; REAL_OF_NUM_LT; REAL_OF_NUM_POW; MULT_CLAUSES];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT
     `(p1 /\ p2) /\ (q1 ==> r1) /\ (q2 ==> r2)
      ==> (p1 ==> q1) ==> (p2 ==> q2) ==> r1 /\ r2`) THEN
    ASM_SIMP_TAC[CONVEX_INTERVAL; IN_INTERVAL_1; REAL_LT_IMP_LE; DROP_VEC;
     INTERIOR_OPEN; OPEN_INTERVAL; INTERVAL_NE_EMPTY_1; REAL_LT_01;
     CLOSURE_OPEN_INTERVAL; LIFT_DROP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    (MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REPEAT CONJ_TAC THENL
      [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         CONTINUOUS_ON_SUBSET)) THEN
       MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_INTERVAL] THEN
       MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s INTER t SUBSET u`) THEN
       ASM_SIMP_TAC[SUBSET_INTERVAL_1; LIFT_DROP; REAL_LT_IMP_LE; DROP_VEC;
                    REAL_LE_REFL];
       MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
       MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
       ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN
       FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         CONTINUOUS_ON_SUBSET)) THEN
       REWRITE_TAC[SUBSET_INTERVAL_1; REAL_LE_REFL] THEN
       ASM_MESON_TAC[REAL_LE_TRANS];
       REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
       MATCH_MP_TAC(SET_RULE
        `i SUBSET interval(vec 0,vec 1) /\
         (!x. x IN interval(vec 0,vec 1) INTER l ==> x IN i ==> P x)
         ==> !x. x IN i INTER l ==> P x`) THEN
       ASM_SIMP_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC;
                    REAL_LT_IMP_LE; REAL_LE_REFL] THEN
       REWRITE_TAC[dyadics_in_open_unit_interval; FORALL_IN_GSPEC] THEN
       MAP_EVERY X_GEN_TAC [`k:num`; `p:num`] THEN STRIP_TAC THEN
       REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
       STRIP_TAC THEN ASM_SIMP_TAC[] THEN
       MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTERVAL_1] THEN
       ASM_SIMP_TAC[] THEN ASM_MESON_TAC[REAL_LE_TRANS]]);
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `IMAGE h s SUBSET t /\ IMAGE h s' SUBSET t'
      ==> !x y. x IN s /\ y IN s' ==> h(x) IN t /\ h(y) IN t'`)) THEN
    DISCH_THEN(MP_TAC o SPECL [`x1:real^1`; `x2:real^1`]) THEN
    ASM_SIMP_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC; REAL_LT_IMP_LE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `a IN IMAGE f s /\ a IN IMAGE f t
      ==> ?x y. x IN s /\ y IN t /\ f x = a /\ f y = a`)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t1:real^1`; `t2:real^1`] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(h:real^1->real^N) x2` o
     GEN_REWRITE_RULE BINDER_CONV [GSYM IS_INTERVAL_CONNECTED_1]) THEN
    REWRITE_TAC[IS_INTERVAL_1; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`t1:real^1`; `t2:real^1`; `c(&m / &2 pow n):real^1`]) THEN
    UNDISCH_TAC `~(h x1:real^N = h(lift (&m / &2 pow n)))` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC(TAUT `q ==> p ==> ~q ==> r`) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    ASM_MESON_TAC[REAL_LE_TRANS]]);;

let PATH_CONTAINS_ARC = prove
 (`!p:real^1->real^N a b.
        path p /\ pathstart p = a /\ pathfinish p = b /\ ~(a = b)
        ==> ?q. arc q /\ path_image q SUBSET path_image p /\
                pathstart q = a /\ pathfinish q = b`,
  REWRITE_TAC[pathstart; pathfinish; path] THEN
  MAP_EVERY X_GEN_TAC [`f:real^1->real^N`; `a:real^N`; `b:real^N`] THEN
  STRIP_TAC THEN MP_TAC(ISPECL
   [`\s. s SUBSET interval[vec 0,vec 1] /\
         vec 0 IN s /\ vec 1 IN s /\
         (!x y. x IN s /\ y IN s /\ segment(x,y) INTER s = {}
                ==> (f:real^1->real^N)(x) = f(y))`;
    `interval[vec 0:real^1,vec 1]`]
  BROUWER_REDUCTION_THEOREM_GEN) THEN
  ASM_REWRITE_TAC[GSYM path_image; CLOSED_INTERVAL; SUBSET_REFL] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
       `s INTER i = {} ==> s SUBSET i ==> s = {}`)) THEN
      REWRITE_TAC[SEGMENT_EQ_EMPTY] THEN
      ANTS_TAC THENL [ONCE_REWRITE_TAC[segment]; MESON_TAC[]] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s DIFF i SUBSET t`) THEN
      ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT; CONVEX_INTERVAL]] THEN
    X_GEN_TAC `s:num->real^1->bool` THEN
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[INTERS_GSPEC; SUBSET; IN_ELIM_THM; IN_UNIV] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[FORALL_LIFT] THEN MATCH_MP_TAC REAL_WLOG_LT THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SEGMENT_SYM] THEN MESON_TAC[];
      REWRITE_TAC[FORALL_DROP; LIFT_DROP]] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
    REWRITE_TAC[INTERS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
    SIMP_TAC[SEGMENT_1; REAL_LT_IMP_LE] THEN DISCH_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        COMPACT_UNIFORMLY_CONTINUOUS)) THEN
    REWRITE_TAC[COMPACT_INTERVAL; uniformly_continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `norm((f:real^1->real^N) x - f y) / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?u v. u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1] /\
            norm(u - x) < e /\ norm(v - y) < e /\ (f:real^1->real^N) u = f v`
    STRIP_ASSUME_TAC THENL
     [ALL_TAC;
      FIRST_X_ASSUM(fun th ->
        MP_TAC(ISPECL [`x:real^1`; `u:real^1`] th) THEN
        MP_TAC(ISPECL [`y:real^1`; `v:real^1`] th)) THEN
      ASM_REWRITE_TAC[dist] THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `q /\ (p ==> ~r) ==> p ==> ~(q ==> r)`) THEN
      CONJ_TAC THENL [ASM SET_TAC[]; CONV_TAC NORM_ARITH]] THEN
    SUBGOAL_THEN
     `?w z. w IN interval(x,y) /\ z IN interval(x,y) /\ drop w < drop z /\
            norm(w - x) < e /\ norm(z - y) < e`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `x + lift(min e (drop y - drop x) / &3)` THEN
      EXISTS_TAC `y - lift(min e (drop y - drop x) / &3)` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_SUB; LIFT_DROP;
                  NORM_REAL; GSYM drop] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`interval[w:real^1,z]`;
                   `{s n :real^1->bool | n IN (:num)}`] COMPACT_IMP_FIP) THEN
    ASM_REWRITE_TAC[COMPACT_INTERVAL; FORALL_IN_GSPEC] THEN
    MATCH_MP_TAC(TAUT `q /\ (~p ==> r) ==> (p ==> ~q) ==> r`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INTERS_GSPEC; IN_UNIV] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
       MATCH_MP (SET_RULE
        `s INTER u = {} ==> t SUBSET s ==> t INTER u = {}`)) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[MESON[] `~(!x. P x /\ Q x ==> R x) <=>
                         (?x. P x /\ Q x /\ ~R x)`] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\n:num. n` o MATCH_MP
      UPPER_BOUND_FINITE_SET) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `interval[w,z] INTER (s:num->real^1->bool) n = {}`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `a INTER t = {} ==> s SUBSET t ==> a INTER s = {}`)) THEN
      REWRITE_TAC[SUBSET; INTERS_IMAGE; IN_ELIM_THM] THEN
      REWRITE_TAC[SET_RULE
       `(!x. x IN s n ==> !i. i IN k ==> x IN s i) <=>
        (!i. i IN k ==> s n SUBSET s i)`] THEN
      SUBGOAL_THEN
       `!i n. i <= n ==> (s:num->real^1->bool) n SUBSET s i`
       (fun th -> ASM_MESON_TAC[th]) THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?u. u IN (s:num->real^1->bool) n /\ u IN interval[x,w] /\
          (interval[u,w] DELETE u) INTER (s n) = {}`
    MP_TAC THENL
     [ASM_CASES_TAC `w IN (s:num->real^1->bool) n` THENL
       [EXISTS_TAC `w:real^1` THEN ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
        REWRITE_TAC[INTERVAL_SING; SET_RULE `{a} DELETE a = {}`] THEN
        REWRITE_TAC[INTER_EMPTY; INTERVAL_NE_EMPTY_1] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`(s:num->real^1->bool) n INTER interval[x,w]`;
                   `w:real^1`] SEGMENT_TO_POINT_EXISTS) THEN
      ASM_SIMP_TAC[CLOSED_INTER; CLOSED_INTERVAL] THEN ANTS_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:real^1` THEN
        ASM_REWRITE_TAC[IN_INTER; IN_INTERVAL_1] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^1` THEN
        REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
         `s INTER t INTER u = {} ==> s SUBSET u ==> s INTER t = {}`)) THEN
        REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
          ASM_MESON_TAC[DROP_EQ; REAL_LE_ANTISYM];
          ANTS_TAC THENL
           [REWRITE_TAC[SUBSET_INTERVAL_1] THEN
            RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
            ASM_REAL_ARITH_TAC;
            REWRITE_TAC[OPEN_CLOSED_INTERVAL_1] THEN ASM SET_TAC[]]]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?v. v IN (s:num->real^1->bool) n /\ v IN interval[z,y] /\
          (interval[z,v] DELETE v) INTER (s n) = {}`
    MP_TAC THENL
     [ASM_CASES_TAC `z IN (s:num->real^1->bool) n` THENL
       [EXISTS_TAC `z:real^1` THEN ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
        REWRITE_TAC[INTERVAL_SING; SET_RULE `{a} DELETE a = {}`] THEN
        REWRITE_TAC[INTER_EMPTY; INTERVAL_NE_EMPTY_1] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`(s:num->real^1->bool) n INTER interval[z,y]`;
                   `z:real^1`] SEGMENT_TO_POINT_EXISTS) THEN
      ASM_SIMP_TAC[CLOSED_INTER; CLOSED_INTERVAL] THEN ANTS_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^1` THEN
        ASM_REWRITE_TAC[IN_INTER; IN_INTERVAL_1] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^1` THEN
        REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
         `s INTER t INTER u = {} ==> s SUBSET u ==> s INTER t = {}`)) THEN
        REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC THENL
         [ANTS_TAC THENL
           [REWRITE_TAC[SUBSET_INTERVAL_1] THEN
            RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
            ASM_REAL_ARITH_TAC;
            REWRITE_TAC[OPEN_CLOSED_INTERVAL_1] THEN ASM SET_TAC[]];
          RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
          ASM_MESON_TAC[DROP_EQ; REAL_LE_ANTISYM]]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM SET_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[NORM_REAL; GSYM drop; DROP_SUB]) THEN
      REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[NORM_REAL; GSYM drop; DROP_SUB]) THEN
      REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`interval[w,z] INTER (s:num->real^1->bool) n = {}`;
          `interval[u,w] DELETE u INTER (s:num->real^1->bool) n = {}`;
          `interval[z,v] DELETE v INTER (s:num->real^1->bool) n = {}`] THEN
        REWRITE_TAC[IMP_IMP; SET_RULE
          `s1 INTER t = {} /\ s2 INTER t = {} <=>
           (s1 UNION s2) INTER t = {}`] THEN
        MATCH_MP_TAC(SET_RULE
         `t SUBSET s ==> s INTER u = {} ==> t INTER u = {}`) THEN
        REWRITE_TAC[SUBSET; IN_UNION; IN_DELETE;
                    GSYM DROP_EQ; IN_INTERVAL_1] THEN
        ASM_REAL_ARITH_TAC;
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^1->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `t:real^1->bool = {}` THENL
   [ASM_MESON_TAC[IN_IMAGE; NOT_IN_EMPTY]; ALL_TAC] THEN
  ABBREV_TAC
   `h = \x. (f:real^1->real^N)(@y. y IN t /\ segment(x,y) INTER t = {})` THEN
  SUBGOAL_THEN
   `!x y. y IN t /\ segment(x,y) INTER t = {} ==> h(x) = (f:real^1->real^N)(y)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!x y z. y IN t /\ segment(x,y) INTER t = {} /\
              z IN t /\ segment(x,z) INTER t = {}
              ==> (f:real^1->real^N)(y) = f(z)`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN ASM_CASES_TAC `(x:real^1) IN t` THENL
       [ASM_MESON_TAC[]; UNDISCH_TAC `~((x:real^1) IN t)`] THEN
      ONCE_REWRITE_TAC[TAUT `p ==> a /\ b /\ c /\ d ==> q <=>
                             (a /\ c) ==> p /\ b /\ d ==> q`] THEN
      STRIP_TAC THEN
      REWRITE_TAC[SET_RULE `~(x IN t) /\ s INTER t = {} /\ s' INTER t = {} <=>
                            (x INSERT (s UNION s')) INTER t = {}`] THEN
      DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE
       `s SUBSET s' ==> s' INTER t = {} ==> s INTER t = {}`) THEN
      REWRITE_TAC[SEGMENT_1; SUBSET; IN_UNION; IN_INSERT; IN_INTERVAL_1] THEN
      GEN_TAC THEN REWRITE_TAC[GSYM DROP_EQ] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1]) THEN
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN t ==> h(x) = (f:real^1->real^N)(x)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SEGMENT_REFL; INTER_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^1. ?y. y IN t /\ segment(x,y) INTER t = {}`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^1` THEN
    EXISTS_TAC `closest_point t (x:real^1)` THEN
    ASM_SIMP_TAC[SEGMENT_TO_CLOSEST_POINT; CLOSEST_POINT_EXISTS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. segment(x,y) INTER t = {} ==> (h:real^1->real^N) x = h y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^1`; `x':real^1`] THEN
    ASM_CASES_TAC `(x:real^1) IN t` THENL
     [ASM_MESON_TAC[SEGMENT_SYM]; ALL_TAC] THEN
    ASM_CASES_TAC `(x':real^1) IN t` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?y y'. y IN t /\ segment(x,y) INTER t = {} /\ h x = f y /\
             y' IN t /\ segment(x',y') INTER t = {} /\
             (h:real^1->real^N) x' = f y'`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC
     [`~((x:real^1) IN t)`; `~((x':real^1) IN t)`;
      `segment(x:real^1,y) INTER t = {}`;
      `segment(x':real^1,y') INTER t = {}`;
      `segment(x:real^1,x') INTER t = {}`] THEN
    MATCH_MP_TAC(SET_RULE
     `s SUBSET (x1 INSERT x2 INSERT (s0 UNION s1 UNION s2))
      ==> s0 INTER t = {} ==> s1 INTER t = {} ==> s2 INTER t = {}
          ==> ~(x1 IN t) ==> ~(x2 IN t) ==> s INTER t = {}`) THEN
    REWRITE_TAC[SEGMENT_1; SUBSET; IN_UNION; IN_INSERT; IN_INTERVAL_1] THEN
      GEN_TAC THEN REWRITE_TAC[GSYM DROP_EQ] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `h:real^1->real^N` HOMEOMORPHIC_MONOTONE_IMAGE_INTERVAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[continuous_on] THEN X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_on]) THEN
      DISCH_THEN(MP_TAC o SPEC `u:real^1`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
      ASM_CASES_TAC `segment(u:real^1,v) INTER t = {}` THENL
       [ASM_MESON_TAC[DIST_REFL]; ALL_TAC] THEN
      SUBGOAL_THEN
       `(?w:real^1. w IN t /\ w IN segment[u,v] /\ segment(u,w) INTER t = {}) /\
        (?z:real^1. z IN t /\ z IN segment[u,v] /\ segment(v,z) INTER t = {})`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MP_TAC(ISPECL [`segment[u:real^1,v] INTER t`; `u:real^1`]
            SEGMENT_TO_POINT_EXISTS);
          MP_TAC(ISPECL [`segment[u:real^1,v] INTER t`; `v:real^1`]
          SEGMENT_TO_POINT_EXISTS)] THEN
       (ASM_SIMP_TAC[CLOSED_INTER; CLOSED_SEGMENT] THEN ANTS_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
            `~(segment(u,v) INTER t = {})
             ==> segment(u,v) SUBSET segment[u,v]
                 ==> ~(segment[u,v] INTER t = {})`)) THEN
          REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED];
          ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^1` THEN
        SIMP_TAC[IN_INTER] THEN
        MATCH_MP_TAC(SET_RULE
         `(w IN uv ==> uw SUBSET uv)
          ==> (w IN uv /\ w IN t) /\ (uw INTER uv INTER t = {})
          ==> uw INTER t = {}`) THEN
        DISCH_TAC THEN REWRITE_TAC[open_segment] THEN
        MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s DIFF u SUBSET t`) THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
        REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; CONVEX_SEGMENT] THEN
        ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; ENDS_IN_SEGMENT]);
        SUBGOAL_THEN `(h:real^1->real^N) u = (f:real^1->real^N) w /\
                      (h:real^1->real^N) v = (f:real^1->real^N) z`
          (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(NORM_ARITH
         `!u. dist(w:real^N,u) < e / &2 /\ dist(z,u) < e / &2
              ==> dist(w,z) < e`) THEN
        EXISTS_TAC `(f:real^1->real^N) u` THEN CONJ_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        (CONJ_TAC THENL
          [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
            `x IN s ==> s SUBSET t ==> x IN t`)) THEN
           REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
           ASM_REWRITE_TAC[CONVEX_INTERVAL; INSERT_SUBSET; EMPTY_SUBSET];
           ASM_MESON_TAC[DIST_IN_CLOSED_SEGMENT; REAL_LET_TRANS; DIST_SYM]])];
      X_GEN_TAC `z:real^N` THEN
      REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT] THEN
      MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      REWRITE_TAC[connected_component] THEN
      EXISTS_TAC `segment[u:real^1,v]` THEN
      REWRITE_TAC[CONNECTED_SEGMENT; ENDS_IN_SEGMENT] THEN
      ASM_CASES_TAC `segment(u:real^1,v) INTER t = {}` THENL
       [REWRITE_TAC[SET_RULE `s SUBSET {x | x IN t /\ P x} <=>
                              s SUBSET t /\ !x. x IN s ==> P x`] THEN
        CONJ_TAC THENL
         [ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT; CONVEX_INTERVAL];
          X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
          SUBGOAL_THEN `segment(u:real^1,x) INTER t = {}`
            (fun th -> ASM_MESON_TAC[th]) THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `uv INTER t = {} ==> ux SUBSET uv ==> ux INTER t = {}`)) THEN
          UNDISCH_TAC `(x:real^1) IN segment[u,v]` THEN
          REWRITE_TAC[SEGMENT_1] THEN
          REPEAT(COND_CASES_TAC THEN
                 ASM_REWRITE_TAC[IN_INTERVAL_1; SUBSET_INTERVAL_1]) THEN
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t DIFF segment(u:real^1,v)`) THEN
      ASM_REWRITE_TAC[SET_RULE `t DIFF s PSUBSET t <=> ~(s INTER t = {})`] THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        MATCH_MP_TAC CLOSED_DIFF THEN ASM_REWRITE_TAC[OPEN_SEGMENT_1];
        ASM SET_TAC[];
        ASM_REWRITE_TAC[IN_DIFF] THEN MAP_EVERY UNDISCH_TAC
         [`(u:real^1) IN interval[vec 0,vec 1]`;
          `(v:real^1) IN interval[vec 0,vec 1]`] THEN
        REWRITE_TAC[SEGMENT_1] THEN
        REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1]) THEN
        ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[IN_DIFF] THEN MAP_EVERY UNDISCH_TAC
         [`(u:real^1) IN interval[vec 0,vec 1]`;
          `(v:real^1) IN interval[vec 0,vec 1]`] THEN
        REWRITE_TAC[SEGMENT_1] THEN
        REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1]) THEN
        ASM_REAL_ARITH_TAC;
        MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
        REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
        ASM_CASES_TAC `segment(x:real^1,y) INTER segment(u,v) = {}` THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN
         `(segment(x:real^1,u) SUBSET segment(x,y) DIFF segment(u,v) /\
           segment(y:real^1,v) SUBSET segment(x,y) DIFF segment(u,v)) \/
          (segment(y:real^1,u) SUBSET segment(x,y) DIFF segment(u,v) /\
           segment(x:real^1,v) SUBSET segment(x,y) DIFF segment(u,v))`
        MP_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [`~(x IN segment(u:real^1,v))`; `~(y IN segment(u:real^1,v))`;
            `~(segment(x:real^1,y) INTER segment (u,v) = {})`] THEN
          POP_ASSUM_LIST(K ALL_TAC) THEN
          MAP_EVERY (fun t -> SPEC_TAC(t,t))
           [`v:real^1`; `u:real^1`; `y:real^1`; `x:real^1`] THEN
          REWRITE_TAC[FORALL_LIFT] THEN
          MATCH_MP_TAC REAL_WLOG_LE THEN CONJ_TAC THENL
           [REWRITE_TAC[SEGMENT_SYM] THEN MESON_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[FORALL_DROP; LIFT_DROP] THEN
          MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN DISCH_TAC THEN
          REWRITE_TAC[FORALL_LIFT] THEN
          MATCH_MP_TAC REAL_WLOG_LE THEN CONJ_TAC THENL
           [REWRITE_TAC[SEGMENT_SYM] THEN MESON_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[FORALL_DROP; LIFT_DROP] THEN
          MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN DISCH_TAC THEN
          ASM_REWRITE_TAC[SEGMENT_1] THEN
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
          REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
          REWRITE_TAC[IN_INTERVAL_1; SUBSET; IN_DIFF; AND_FORALL_THM] THEN
          ASM_REAL_ARITH_TAC;
          DISCH_THEN(DISJ_CASES_THEN(CONJUNCTS_THEN
           (let sl = SET_RULE
             `i SUBSET xy DIFF uv
              ==> xy INTER (t DIFF uv) = {} ==> i INTER t = {}` in
            fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP (MATCH_MP sl th))))) THEN
          ASM_MESON_TAC[]]];
      ASM_MESON_TAC[]];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `?q:real^1->real^N.
        arc q /\ path_image q SUBSET path_image f /\
        a IN path_image q /\ b IN path_image q`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
    REWRITE_TAC[homeomorphism] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^1->real^N` THEN
    REWRITE_TAC[arc; path; path_image] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM MESON_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; path_image] THEN ASM SET_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^1` THEN
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 1:real^1` THEN
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN ASM_MESON_TAC[]];
    SUBGOAL_THEN
     `?u v. u IN interval[vec 0,vec 1] /\ a = (q:real^1->real^N) u /\
            v IN interval[vec 0,vec 1] /\ b = (q:real^1->real^N) v`
    STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[path_image]) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `subpath u v (q:real^1->real^N)` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
      ASM_MESON_TAC[ARC_IMP_SIMPLE_PATH];
      ASM_MESON_TAC[SUBSET_TRANS; PATH_IMAGE_SUBPATH_SUBSET; ARC_IMP_PATH];
      ASM_MESON_TAC[pathstart; PATHSTART_SUBPATH];
      ASM_MESON_TAC[pathfinish; PATHFINISH_SUBPATH]]]);;

let PATH_CONNECTED_ARCWISE = prove
 (`!s:real^N->bool.
        path_connected s <=>
        !x y. x IN s /\ y IN s /\ ~(x = y)
              ==> ?g. arc g /\
                      path_image g SUBSET s /\
                      pathstart g = x /\
                      pathfinish g = y`,
  GEN_TAC THEN REWRITE_TAC[path_connected] THEN EQ_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`g:real^1->real^N`; `x:real^N`; `y:real^N`]
        PATH_CONTAINS_ARC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    ASM_CASES_TAC `y:real^N = x` THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `linepath(y:real^N,y)` THEN
      ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                      PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET];
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[ARC_IMP_PATH]]]);;

let ARC_CONNECTED_TRANS = prove
 (`!g h:real^1->real^N.
        arc g /\ arc h /\
        pathfinish g = pathstart h /\ ~(pathstart g = pathfinish h)
        ==> ?i. arc i /\
                path_image i SUBSET (path_image g UNION path_image h) /\
                pathstart i = pathstart g /\
                pathfinish i = pathfinish h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g ++ h:real^1->real^N`; `pathstart(g):real^N`;
                 `pathfinish(h):real^N`] PATH_CONTAINS_ARC) THEN
  ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATH_JOIN_EQ; ARC_IMP_PATH;
               PATH_IMAGE_JOIN]);;

(* ------------------------------------------------------------------------- *)
(* Local versions of topological properties in general.                      *)
(* ------------------------------------------------------------------------- *)

let locally = new_definition
 `locally P (s:real^N->bool) <=>
        !w x. open_in (subtopology euclidean s) w /\ x IN w
              ==> ?u v. open_in (subtopology euclidean s) u /\ P v /\
                        x IN u /\ u SUBSET v /\ v SUBSET w`;;

let LOCALLY_MONO = prove
 (`!P Q s. (!t. P t ==> Q t) /\ locally P s ==> locally Q s`,
  REWRITE_TAC[locally] THEN MESON_TAC[]);;

let LOCALLY_OPEN_SUBSET = prove
 (`!P s t:real^N->bool.
        locally P s /\ open_in (subtopology euclidean s) t
        ==> locally P t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[locally] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`w:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^N->bool`; `x:real^N`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_TRANS]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_MESON_TAC[open_in; SUBSET]);;

let LOCALLY_DIFF_CLOSED = prove
 (`!P s t:real^N->bool.
        locally P s /\ closed_in (subtopology euclidean s) t
        ==> locally P (s DIFF t)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_DIFF THEN
  ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; SUBSET_UNIV; TOPSPACE_EUCLIDEAN]);;

let LOCALLY_EMPTY = prove
 (`!P. locally P {}`,
  REWRITE_TAC[locally] THEN MESON_TAC[open_in; SUBSET; NOT_IN_EMPTY]);;

let LOCALLY_SING = prove
 (`!P a. locally P {a} <=> P {a}`,
  REWRITE_TAC[locally; open_in] THEN
  REWRITE_TAC[SET_RULE
   `(w SUBSET {a} /\ P) /\ x IN w <=> w = {a} /\ x = a /\ P`] THEN
  SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2; IN_SING] THEN
  REWRITE_TAC[SET_RULE
   `(u SUBSET {a} /\ P) /\ Q /\ a IN u /\ u SUBSET v /\ v SUBSET {a} <=>
    u = {a} /\ v = {a} /\ P /\ Q`] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2; IN_SING] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; MESON[REAL_LT_01] `?x. &0 < x`]);;

let LOCALLY_INTER = prove
 (`!P:(real^N->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> !s t. locally P s /\ locally P t ==> locally P (s INTER t)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[locally; OPEN_IN_OPEN] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; GSYM CONJ_ASSOC; MESON[]
   `(!w x. (?t. P t /\ w = f t) /\ Q w x ==> R w x) <=>
    (!t x. P t /\ Q (f t) x ==> R (f t) x)`] THEN
  ONCE_REWRITE_TAC[MESON[]
   `(?a b c. P a b c /\ Q a b c /\ R a b c) <=>
    (?b c a. Q a b c /\ P a b c /\ R a b c)`] THEN
  REWRITE_TAC[AND_FORALL_THM; UNWIND_THM2; IN_INTER] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `w:real^N->bool` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `u1:real^N->bool` (X_CHOOSE_THEN `v1:real^N->bool`
        STRIP_ASSUME_TAC))
   (X_CHOOSE_THEN `u2:real^N->bool` (X_CHOOSE_THEN `v2:real^N->bool`
        STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `u1 INTER u2:real^N->bool` THEN
  EXISTS_TAC `v1 INTER v2:real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_INTER] THEN ASM SET_TAC[]);;

let HOMEOMORPHISM_LOCALLY = prove
 (`!P Q f:real^N->real^M g.
        (!s t. homeomorphism (s,t) (f,g) ==> (P s <=> Q t))
        ==> (!s t. homeomorphism (s,t) (f,g)
                   ==> (locally P s <=> locally Q t))`,

  let lemma = prove
   (`!P Q f g.
        (!s t. P s /\ homeomorphism (s,t) (f,g) ==> Q t)
        ==> (!s:real^N->bool t:real^M->bool.
                locally P s /\ homeomorphism (s,t) (f,g) ==> locally Q t)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[locally] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    MAP_EVERY X_GEN_TAC [`w:real^M->bool`; `y:real^M`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`IMAGE (g:real^M->real^N) w`; `(g:real^M->real^N) y`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      SUBGOAL_THEN `IMAGE (g:real^M->real^N) w =
                     {x | x IN s /\ f(x) IN w}`
      SUBST1_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[open_in]) THEN ASM SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_IMP_OPEN_IN THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`IMAGE (f:real^N->real^M) u`; `IMAGE (f:real^N->real^M) v`] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `IMAGE (f:real^N->real^M) u =
                     {x | x IN t /\ g(x) IN u}`
      SUBST1_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[open_in]) THEN ASM SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_IMP_OPEN_IN THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `v:real^N->bool` THEN
      ASM_REWRITE_TAC[homeomorphism] THEN
      REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THEN
      TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)));
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[open_in]) THEN ASM SET_TAC[]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM;
        TAUT `p ==> q /\ r ==> s <=> p /\ r ==> q ==> s`] lemma) THEN
  ASM_MESON_TAC[HOMEOMORPHISM_SYM]);;

let HOMEOMORPHIC_LOCALLY = prove
 (`!P Q. (!s:real^N->bool t:real^M->bool. s homeomorphic t ==> (P s <=> Q t))
         ==> (!s t. s homeomorphic t ==> (locally P s <=> locally Q t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[homeomorphic; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[MESON[]
   `(!a b c d. P a b c d) <=> (!c d a b. P a b c d)`] THEN
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_LOCALLY THEN
  ASM_MESON_TAC[homeomorphic]);;

let LOCALLY_TRANSLATION = prove
 (`!P:(real^N->bool)->bool.
        (!a s. P (IMAGE (\x. a + x) s) <=> P s)
        ==> (!a s. locally P (IMAGE (\x. a + x) s) <=> locally P s)`,
  GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MP_TAC(ISPECL
   [`P:(real^N->bool)->bool`; `P:(real^N->bool)->bool`;
    `\x:real^N. a + x`; `\x:real^N. --a + x`]
     HOMEOMORPHISM_LOCALLY) THEN
  REWRITE_TAC[homeomorphism] THEN
  SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
  REWRITE_TAC[FORALL_UNWIND_THM1; IMP_CONJ; GSYM IMAGE_o; o_DEF; IMAGE_ID;
              VECTOR_ARITH `--a + a + x:real^N = x /\ a + --a + x = x`] THEN
  MESON_TAC[]);;

let LOCALLY_INJECTIVE_LINEAR_IMAGE = prove
 (`!P:(real^N->bool)->bool Q:(real^M->bool)->bool.
        (!f s. linear f /\ (!x y. f x = f y ==> x = y)
               ==> (P (IMAGE f s) <=> Q s))
        ==>  (!f s. linear f /\ (!x y. f x = f y ==> x = y)
                    ==> (locally P (IMAGE f s) <=> locally Q s))`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  ASM_CASES_TAC `linear(f:real^M->real^N) /\ (!x y. f x = f y ==> x = y)` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`Q:(real^M->bool)->bool`; `P:(real^N->bool)->bool`;
    `f:real^M->real^N`; `g:real^N->real^M`]
     HOMEOMORPHISM_LOCALLY) THEN
  ASM_SIMP_TAC[homeomorphism; LINEAR_CONTINUOUS_ON] THEN
  ASM_REWRITE_TAC[FORALL_UNWIND_THM1; IMP_CONJ; FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID] THEN MESON_TAC[]);;

let LOCALLY_OPEN_MAP_IMAGE = prove
 (`!P Q f:real^M->real^N s.
        f continuous_on s /\
        (!t. open_in (subtopology euclidean s) t
              ==> open_in (subtopology euclidean (IMAGE f s)) (IMAGE f t)) /\
        (!t. t SUBSET s /\ P t ==> Q(IMAGE f t)) /\
        locally P s
        ==> locally Q (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[locally] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`w:real^N->bool`; `y:real^N`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [open_in]) THEN
  FIRST_ASSUM(MP_TAC o  SPEC `w:real^N->bool` o
    GEN_REWRITE_RULE I [CONTINUOUS_ON_OPEN]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?x. x IN s /\ (f:real^M->real^N) x = y` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`{x | x IN s /\ (f:real^M->real^N) x IN w}`; `x:real^M`]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^M->bool`; `v:real^M->bool`] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`IMAGE (f:real^M->real^N) u`; `IMAGE (f:real^M->real^N) v`] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Important special cases of local connectedness & path connectedness.      *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_CONNECTED,LOCALLY_CONNECTED_OPEN_CONNECTED_COMPONENT =
 (CONJ_PAIR o prove)
 (`(!s:real^N->bool.
        locally connected s <=>
        !v x. open_in (subtopology euclidean s) v /\ x IN v
              ==> ?u. open_in (subtopology euclidean s) u /\
                      connected u /\
                      x IN u /\ u SUBSET v) /\
   (!s:real^N->bool.
        locally connected s <=>
        !t x. open_in (subtopology euclidean s) t /\ x IN t
              ==> open_in (subtopology euclidean s)
                          (connected_component t x))`,
  REWRITE_TAC[AND_FORALL_THM; locally] THEN X_GEN_TAC `s:real^N->bool` THEN
  MATCH_MP_TAC(TAUT
   `(q ==> p) /\ (p ==> r) /\ (r ==> q) ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[SUBSET_REFL];
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `y:real^N`] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP CONNECTED_COMPONENT_EQ) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `x:real^N`]) THEN ANTS_TAC
    THENL [ASM_MESON_TAC[CONNECTED_COMPONENT_SUBSET; SUBSET]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` (X_CHOOSE_THEN `a:real^N->bool`
          STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `v:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `a:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
    EXISTS_TAC `connected_component u (x:real^N)` THEN
    REWRITE_TAC[CONNECTED_COMPONENT_SUBSET; CONNECTED_CONNECTED_COMPONENT] THEN
    ASM_SIMP_TAC[IN; CONNECTED_COMPONENT_REFL]]);;

let LOCALLY_PATH_CONNECTED,LOCALLY_PATH_CONNECTED_OPEN_PATH_COMPONENT =
 (CONJ_PAIR o prove)
 (`(!s:real^N->bool.
        locally path_connected s <=>
        !v x. open_in (subtopology euclidean s) v /\ x IN v
              ==> ?u. open_in (subtopology euclidean s) u /\
                      path_connected u /\
                      x IN u /\ u SUBSET v) /\
   (!s:real^N->bool.
        locally path_connected s <=>
        !t x. open_in (subtopology euclidean s) t /\ x IN t
              ==> open_in (subtopology euclidean s)
                          (path_component t x))`,
  REWRITE_TAC[AND_FORALL_THM; locally] THEN X_GEN_TAC `s:real^N->bool` THEN
  MATCH_MP_TAC(TAUT
   `(q ==> p) /\ (p ==> r) /\ (r ==> q) ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[SUBSET_REFL];
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `y:real^N`] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP PATH_COMPONENT_EQ) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `x:real^N`]) THEN ANTS_TAC
    THENL [ASM_MESON_TAC[PATH_COMPONENT_SUBSET; SUBSET]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` (X_CHOOSE_THEN `a:real^N->bool`
          STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `v:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `a:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PATH_COMPONENT_MAXIMAL THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
    EXISTS_TAC `path_component u (x:real^N)` THEN
    REWRITE_TAC[PATH_COMPONENT_SUBSET; PATH_CONNECTED_PATH_COMPONENT] THEN
    ASM_SIMP_TAC[IN; PATH_COMPONENT_REFL]]);;

let LOCALLY_CONNECTED_OPEN_COMPONENT = prove
 (`!s:real^N->bool.
        locally connected s <=>
        !t c. open_in (subtopology euclidean s) t /\ c IN components t
              ==> open_in (subtopology euclidean s) c`,
  REWRITE_TAC[LOCALLY_CONNECTED_OPEN_CONNECTED_COMPONENT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; components; FORALL_IN_GSPEC]);;

let LOCALLY_CONNECTED_IM_KLEINEN = prove
 (`!s:real^N->bool.
      locally connected s <=>
      !v x. open_in (subtopology euclidean s) v /\ x IN v
            ==> ?u. open_in (subtopology euclidean s) u /\
                    x IN u /\ u SUBSET v /\
                    !y. y IN u
                        ==> ?c. connected c /\ c SUBSET v /\ x IN c /\ y IN c`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[LOCALLY_CONNECTED] THEN MESON_TAC[SUBSET_REFL]; DISCH_TAC] THEN
  REWRITE_TAC[LOCALLY_CONNECTED_OPEN_COMPONENT] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `c:real^N->bool`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `x:real^N`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(k:real^N->bool) SUBSET c` MP_TAC THENL
   [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM SET_TAC[]);;

let LOCALLY_PATH_CONNECTED_IM_KLEINEN = prove
 (`!s:real^N->bool.
      locally path_connected s <=>
      !v x. open_in (subtopology euclidean s) v /\ x IN v
            ==> ?u. open_in (subtopology euclidean s) u /\
                    x IN u /\ u SUBSET v /\
                    !y. y IN u
                        ==> ?p. path p /\ path_image p SUBSET v /\
                                pathstart p = x /\ pathfinish p = y`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[LOCALLY_PATH_CONNECTED] THEN
    REWRITE_TAC[path_connected] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[LOCALLY_PATH_CONNECTED_OPEN_PATH_COMPONENT] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `z:real^N`] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `x:real^N`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[PATH_COMPONENT_SUBSET; SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^N->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^1->real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(path_image p) SUBSET path_component u (z:real^N)` MP_TAC
    THENL [ALL_TAC; ASM_MESON_TAC[PATHFINISH_IN_PATH_IMAGE; SUBSET]] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP PATH_COMPONENT_EQ) THEN
    MATCH_MP_TAC PATH_COMPONENT_MAXIMAL THEN
    ASM_SIMP_TAC[PATH_CONNECTED_PATH_IMAGE] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE]]);;

let LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED = prove
 (`!s:real^N->bool. locally path_connected s ==> locally connected s`,
  MESON_TAC[LOCALLY_MONO; PATH_CONNECTED_IMP_CONNECTED]);;

let LOCALLY_CONNECTED_COMPONENTS = prove
 (`!s c:real^N->bool.
        locally connected s /\ c IN components s ==> locally connected c`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] LOCALLY_OPEN_SUBSET)) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o
   GEN_REWRITE_RULE I [LOCALLY_CONNECTED_OPEN_COMPONENT]) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[OPEN_IN_REFL]);;

let LOCALLY_CONNECTED_CONNECTED_COMPONENT = prove
 (`!s x:real^N.
        locally connected s
        ==> locally connected (connected_component s x)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `connected_component s (x:real^N) = {}` THEN
  ASM_REWRITE_TAC[LOCALLY_EMPTY] THEN
  MATCH_MP_TAC LOCALLY_CONNECTED_COMPONENTS THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[IN_COMPONENTS] THEN
  ASM_MESON_TAC[CONNECTED_COMPONENT_EQ_EMPTY]);;

let LOCALLY_PATH_CONNECTED_COMPONENTS = prove
 (`!s c:real^N->bool.
        locally path_connected s /\ c IN components s
        ==> locally path_connected c`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] LOCALLY_OPEN_SUBSET)) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o
   GEN_REWRITE_RULE I [LOCALLY_CONNECTED_OPEN_COMPONENT] o
   MATCH_MP LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[OPEN_IN_REFL]);;

let LOCALLY_PATH_CONNECTED_CONNECTED_COMPONENT = prove
 (`!s x:real^N.
        locally path_connected s
        ==> locally path_connected (connected_component s x)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `connected_component s (x:real^N) = {}` THEN
  ASM_REWRITE_TAC[LOCALLY_EMPTY] THEN
  MATCH_MP_TAC LOCALLY_PATH_CONNECTED_COMPONENTS THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[IN_COMPONENTS] THEN
  ASM_MESON_TAC[CONNECTED_COMPONENT_EQ_EMPTY]);;

let OPEN_IMP_LOCALLY_PATH_CONNECTED = prove
 (`!s:real^N->bool. open s ==> locally path_connected s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOCALLY_MONO THEN
  EXISTS_TAC `convex:(real^N->bool)->bool` THEN
  REWRITE_TAC[CONVEX_IMP_PATH_CONNECTED] THEN
  ASM_SIMP_TAC[locally; OPEN_IN_OPEN_EQ] THEN
  ASM_MESON_TAC[OPEN_CONTAINS_BALL; CENTRE_IN_BALL; OPEN_BALL; CONVEX_BALL;
                SUBSET]);;

let OPEN_IMP_LOCALLY_CONNECTED = prove
 (`!s:real^N->bool. open s ==> locally connected s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOCALLY_MONO THEN
  EXISTS_TAC `path_connected:(real^N->bool)->bool` THEN
  ASM_SIMP_TAC[OPEN_IMP_LOCALLY_PATH_CONNECTED;
               PATH_CONNECTED_IMP_CONNECTED]);;

let LOCALLY_PATH_CONNECTED_UNIV = prove
 (`locally path_connected (:real^N)`,
  SIMP_TAC[OPEN_IMP_LOCALLY_PATH_CONNECTED; OPEN_UNIV]);;

let LOCALLY_CONNECTED_UNIV = prove
 (`locally connected (:real^N)`,
  SIMP_TAC[OPEN_IMP_LOCALLY_CONNECTED; OPEN_UNIV]);;

let OPEN_IN_CONNECTED_COMPONENT_LOCALLY_CONNECTED = prove
 (`!s x:real^N.
        locally connected s
        ==> open_in (subtopology euclidean s) (connected_component s x)`,
  REWRITE_TAC[LOCALLY_CONNECTED_OPEN_CONNECTED_COMPONENT] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x:real^N) IN s` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; SUBSET_UNIV; TOPSPACE_EUCLIDEAN];
    ASM_MESON_TAC[OPEN_IN_EMPTY; CONNECTED_COMPONENT_EQ_EMPTY]]);;

let OPEN_IN_COMPONENTS_LOCALLY_CONNECTED = prove
 (`!s c:real^N->bool.
        locally connected s /\ c IN components s
        ==> open_in (subtopology euclidean s) c`,
  MESON_TAC[LOCALLY_CONNECTED_OPEN_COMPONENT; OPEN_IN_REFL]);;

let OPEN_IN_PATH_COMPONENT_LOCALLY_PATH_CONNECTED = prove
 (`!s x:real^N.
        locally path_connected s
        ==> open_in (subtopology euclidean s) (path_component s x)`,
  REWRITE_TAC[LOCALLY_PATH_CONNECTED_OPEN_PATH_COMPONENT] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x:real^N) IN s` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; SUBSET_UNIV; TOPSPACE_EUCLIDEAN];
    ASM_MESON_TAC[OPEN_IN_EMPTY; PATH_COMPONENT_EQ_EMPTY]]);;

let CLOSED_IN_PATH_COMPONENT_LOCALLY_PATH_CONNECTED = prove
 (`!s x:real^N.
        locally path_connected s
        ==> closed_in (subtopology euclidean s) (path_component s x)`,
  REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
              PATH_COMPONENT_SUBSET] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `s DIFF path_component s (x:real^N) =
    UNIONS({path_component s y | y | y IN s} DELETE (path_component s x))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM UNIONS_PATH_COMPONENT] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. x IN s DELETE a ==> DISJOINT a x)
       ==> UNIONS s DIFF a = UNIONS (s DELETE a)`) THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC; IN_DELETE] THEN
    SIMP_TAC[PATH_COMPONENT_DISJOINT; PATH_COMPONENT_EQ_EQ] THEN
    MESON_TAC[IN; SUBSET; PATH_COMPONENT_SUBSET];
    MATCH_MP_TAC OPEN_IN_UNIONS THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC; IN_DELETE] THEN
    ASM_SIMP_TAC[OPEN_IN_PATH_COMPONENT_LOCALLY_PATH_CONNECTED]]);;

let CONVEX_IMP_LOCALLY_PATH_CONNECTED = prove
 (`!s:real^N->bool. convex s ==> locally path_connected s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LOCALLY_PATH_CONNECTED] THEN
  MAP_EVERY X_GEN_TAC [`v:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s INTER ball(x:real^N,e)` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_OPEN] THEN MESON_TAC[OPEN_BALL];
    MATCH_MP_TAC CONVEX_IMP_PATH_CONNECTED THEN
    ASM_SIMP_TAC[CONVEX_INTER; CONVEX_BALL];
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
    ASM SET_TAC[]]);;

let OPEN_IN_CONNECTED_COMPONENTS = prove
 (`!s c:real^N->bool.
        FINITE(components s) /\ c IN components s
        ==> open_in (subtopology euclidean s) c`,
  REWRITE_TAC[components; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  SIMP_TAC[OPEN_IN_CONNECTED_COMPONENT]);;

let FINITE_COMPONENTS = prove
 (`!s:real^N->bool. compact s /\ locally connected s ==> FINITE(components s)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL_SUBTOPOLOGY]) THEN
  DISCH_THEN(MP_TAC o SPEC `components(s:real^N->bool)`) THEN
  REWRITE_TAC[GSYM UNIONS_COMPONENTS; SUBSET_REFL] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_COMPONENTS_LOCALLY_CONNECTED]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `components(s:real^N->bool) = f`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_CASES_TAC `?c:real^N->bool. c IN components s /\ ~(c IN f)` THENL
   [FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC); ASM SET_TAC[]] THEN
  SUBGOAL_THEN
   `~(c:real^N->bool = {}) /\ c SUBSET UNIONS f /\ DISJOINT c (UNIONS f)`
  MP_TAC THENL [ALL_TAC; SET_TAC[]] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
    ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET_TRANS];
    REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DISJOINT] THEN
    MATCH_MP_TAC(REWRITE_RULE[pairwise] PAIRWISE_DISJOINT_COMPONENTS) THEN
    ASM_MESON_TAC[SUBSET]]);;

let CONVEX_IMP_LOCALLY_CONNECTED = prove
 (`!s:real^N->bool. convex s ==> locally connected s`,
  MESON_TAC[CONVEX_IMP_LOCALLY_PATH_CONNECTED;
            LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED]);;

let HOMEOMORPHIC_LOCAL_CONNECTEDNESS = prove
 (`!s t. s homeomorphic t ==> (locally connected s <=> locally connected t)`,
  MATCH_MP_TAC HOMEOMORPHIC_LOCALLY THEN
  REWRITE_TAC[HOMEOMORPHIC_CONNECTEDNESS]);;

let HOMEOMORPHIC_LOCAL_PATH_CONNECTEDNESS = prove
 (`!s t. s homeomorphic t
         ==> (locally path_connected s <=> locally path_connected t)`,
  MATCH_MP_TAC HOMEOMORPHIC_LOCALLY THEN
  REWRITE_TAC[HOMEOMORPHIC_PATH_CONNECTEDNESS]);;

let LOCALLY_PATH_CONNECTED_TRANSLATION_EQ = prove
 (`!a:real^N s. locally path_connected (IMAGE (\x. a + x) s) <=>
                locally path_connected s`,
  MATCH_MP_TAC LOCALLY_TRANSLATION THEN
  REWRITE_TAC[PATH_CONNECTED_TRANSLATION_EQ]);;

add_translation_invariants [LOCALLY_PATH_CONNECTED_TRANSLATION_EQ];;

let LOCALLY_CONNECTED_TRANSLATION_EQ = prove
 (`!a:real^N s. locally connected (IMAGE (\x. a + x) s) <=>
                locally connected s`,
  MATCH_MP_TAC LOCALLY_TRANSLATION THEN
  REWRITE_TAC[CONNECTED_TRANSLATION_EQ]);;

add_translation_invariants [LOCALLY_CONNECTED_TRANSLATION_EQ];;

let LOCALLY_PATH_CONNECTED_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (locally path_connected (IMAGE f s) <=> locally path_connected s)`,
  MATCH_MP_TAC LOCALLY_INJECTIVE_LINEAR_IMAGE THEN
  REWRITE_TAC[PATH_CONNECTED_LINEAR_IMAGE_EQ]);;

add_linear_invariants [LOCALLY_PATH_CONNECTED_LINEAR_IMAGE_EQ];;

let LOCALLY_CONNECTED_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (locally connected (IMAGE f s) <=> locally connected s)`,
  MATCH_MP_TAC LOCALLY_INJECTIVE_LINEAR_IMAGE THEN
  REWRITE_TAC[CONNECTED_LINEAR_IMAGE_EQ]);;

add_linear_invariants [LOCALLY_CONNECTED_LINEAR_IMAGE_EQ];;

let LOCALLY_CONNECTED_QUOTIENT_IMAGE = prove
 (`!f:real^M->real^N s.
      (!t. t SUBSET IMAGE f s
           ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN t} <=>
                open_in (subtopology euclidean (IMAGE f s)) t)) /\
      locally connected s
      ==> locally connected (IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LOCALLY_CONNECTED_OPEN_COMPONENT] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `c:real^N->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [open_in]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `c:real^N->bool`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN EXISTS_TAC
   `connected_component {w | w IN s /\ (f:real^M->real^N)(w) IN u} x` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [LOCALLY_CONNECTED_OPEN_COMPONENT]) THEN
    REWRITE_TAC[IMP_CONJ_ALT] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_COMPONENTS; IN_ELIM_THM] THEN ASM SET_TAC[];
    ALL_TAC;
    ASSUME_TAC(ISPECL [`{w | w IN s /\ (f:real^M->real^N) w IN u}`; `x:real^M`]
        CONNECTED_COMPONENT_SUBSET) THEN
    SUBGOAL_THEN
     `IMAGE (f:real^M->real^N) (connected_component {w | w IN s /\ f w IN u} x)
      SUBSET c`
    MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[CONTINUOUS_ON_OPEN] THEN ASM_MESON_TAC[open_in];
        ASM SET_TAC[]];
      ASM SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(f:real^M->real^N) x` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE]] THEN
  GEN_REWRITE_TAC I [IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN
  ASM SET_TAC[]);;

let LOCALLY_PATH_CONNECTED_QUOTIENT_IMAGE = prove
 (`!f:real^M->real^N s.
      (!t. t SUBSET IMAGE f s
           ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN t} <=>
                open_in (subtopology euclidean (IMAGE f s)) t)) /\
      locally path_connected s
      ==> locally path_connected (IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LOCALLY_PATH_CONNECTED_OPEN_PATH_COMPONENT] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `y:real^N`] THEN
  STRIP_TAC THEN
  ASSUME_TAC(ISPECL [`u:real^N->bool`; `y:real^N`] PATH_COMPONENT_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [open_in]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `path_component u (y:real^N)`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN EXISTS_TAC
   `path_component {w | w IN s /\ (f:real^M->real^N)(w) IN u} x` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [LOCALLY_PATH_CONNECTED_OPEN_PATH_COMPONENT]) THEN
    REWRITE_TAC[IMP_CONJ_ALT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC;
    ASSUME_TAC(ISPECL [`{w | w IN s /\ (f:real^M->real^N) w IN u}`; `x:real^M`]
        PATH_COMPONENT_SUBSET) THEN
    SUBGOAL_THEN
     `IMAGE (f:real^M->real^N) (path_component {w | w IN s /\ f w IN u} x)
      SUBSET path_component u y`
    MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP PATH_COMPONENT_EQ) THEN
    MATCH_MP_TAC PATH_COMPONENT_MAXIMAL THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE;
      MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[PATH_CONNECTED_PATH_COMPONENT] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[CONTINUOUS_ON_OPEN] THEN ASM_MESON_TAC[open_in];
        ASM SET_TAC[]];
      ASM SET_TAC[]]] THEN
  GEN_REWRITE_TAC I [IN] THEN REWRITE_TAC[PATH_COMPONENT_REFL_EQ] THEN
  ASM SET_TAC[]);;

let LOCALLY_CONNECTED_CONTINUOUS_IMAGE_COMPACT = prove
 (`!f:real^M->real^N s.
        locally connected s /\ compact s /\ f continuous_on s
        ==> locally connected (IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOCALLY_CONNECTED_QUOTIENT_IMAGE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_MAP_IMP_QUOTIENT_MAP THEN
  ASM_SIMP_TAC[CLOSED_IN_CLOSED_EQ; COMPACT_IMP_CLOSED;
               COMPACT_CONTINUOUS_IMAGE; IMAGE_SUBSET] THEN
  ASM_MESON_TAC[COMPACT_IMP_CLOSED; COMPACT_CONTINUOUS_IMAGE;
    CONTINUOUS_ON_SUBSET; BOUNDED_SUBSET; COMPACT_EQ_BOUNDED_CLOSED]);;

let LOCALLY_PATH_CONNECTED_CONTINUOUS_IMAGE_COMPACT = prove
 (`!f:real^M->real^N s.
        locally path_connected s /\ compact s /\ f continuous_on s
        ==> locally path_connected (IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOCALLY_PATH_CONNECTED_QUOTIENT_IMAGE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_MAP_IMP_QUOTIENT_MAP THEN
  ASM_SIMP_TAC[CLOSED_IN_CLOSED_EQ; COMPACT_IMP_CLOSED;
               COMPACT_CONTINUOUS_IMAGE; IMAGE_SUBSET] THEN
  ASM_MESON_TAC[COMPACT_IMP_CLOSED; COMPACT_CONTINUOUS_IMAGE;
    CONTINUOUS_ON_SUBSET; BOUNDED_SUBSET; COMPACT_EQ_BOUNDED_CLOSED]);;

let LOCALLY_PATH_CONNECTED_PATH_IMAGE = prove
 (`!p:real^1->real^N. path p ==> locally path_connected (path_image p)`,
  REWRITE_TAC[path; path_image] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LOCALLY_PATH_CONNECTED_CONTINUOUS_IMAGE_COMPACT THEN
  ASM_SIMP_TAC[COMPACT_INTERVAL; CONVEX_INTERVAL;
               CONVEX_IMP_LOCALLY_PATH_CONNECTED]);;

let LOCALLY_CONNECTED_PATH_IMAGE = prove
 (`!p:real^1->real^N. path p ==> locally connected (path_image p)`,
  SIMP_TAC[LOCALLY_PATH_CONNECTED_PATH_IMAGE;
           LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED]);;

let LOCALLY_CONNECTED_LEFT_INVERTIBLE_IMAGE = prove
 (`!f:real^M->real^N g s.
        f continuous_on s /\ g continuous_on (IMAGE f s) /\
        (!x. x IN s ==> g(f x) = x) /\
        locally connected s
        ==> locally connected (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LOCALLY_CONNECTED_QUOTIENT_IMAGE) THEN
  MATCH_MP_TAC CONTINUOUS_LEFT_INVERSE_IMP_QUOTIENT_MAP THEN ASM_MESON_TAC[]);;

let LOCALLY_CONNECTED_RIGHT_INVERTIBLE_IMAGE = prove
 (`!f:real^M->real^N g s.
        f continuous_on s /\ g continuous_on (IMAGE f s) /\
        IMAGE g (IMAGE f s) SUBSET s /\ (!x. x IN IMAGE f s ==> f(g x) = x) /\
        locally connected s
        ==> locally connected (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LOCALLY_CONNECTED_QUOTIENT_IMAGE) THEN
  MATCH_MP_TAC CONTINUOUS_RIGHT_INVERSE_IMP_QUOTIENT_MAP THEN
  EXISTS_TAC `g:real^N->real^M` THEN ASM SET_TAC[]);;

let LOCALLY_PATH_CONNECTED_LEFT_INVERTIBLE_IMAGE = prove
 (`!f:real^M->real^N g s.
        f continuous_on s /\ g continuous_on (IMAGE f s) /\
        (!x. x IN s ==> g(f x) = x) /\
        locally path_connected s
        ==> locally path_connected (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
    LOCALLY_PATH_CONNECTED_QUOTIENT_IMAGE) THEN
  MATCH_MP_TAC CONTINUOUS_LEFT_INVERSE_IMP_QUOTIENT_MAP THEN ASM_MESON_TAC[]);;

let LOCALLY_PATH_CONNECTED_RIGHT_INVERTIBLE_IMAGE = prove
 (`!f:real^M->real^N g s.
        f continuous_on s /\ g continuous_on (IMAGE f s) /\
        IMAGE g (IMAGE f s) SUBSET s /\ (!x. x IN IMAGE f s ==> f(g x) = x) /\
        locally path_connected s
        ==> locally path_connected (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
    LOCALLY_PATH_CONNECTED_QUOTIENT_IMAGE) THEN
  MATCH_MP_TAC CONTINUOUS_RIGHT_INVERSE_IMP_QUOTIENT_MAP THEN
  EXISTS_TAC `g:real^N->real^M` THEN ASM SET_TAC[]);;

let LOCALLY_PCROSS = prove
 (`!P Q R.
        (!s:real^M->bool t:real^N->bool. P s /\ Q t ==> R(s PCROSS t))
        ==> (!s t. locally P s /\ locally Q t ==> locally R (s PCROSS t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[locally; FORALL_PASTECART] THEN
  MAP_EVERY X_GEN_TAC
   [`w:real^(M,N)finite_sum->bool`; `x:real^M`; `y:real^N`] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
   MP_TAC(MATCH_MP PASTECART_IN_INTERIOR_SUBTOPOLOGY
        (ONCE_REWRITE_RULE[CONJ_SYM] th))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^M->bool`; `v:real^N->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^M->bool`; `x:real^M`] o
    GEN_REWRITE_RULE I [locally]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`v:real^N->bool`; `y:real^N`] o
    GEN_REWRITE_RULE I [locally]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v':real^N->bool`; `v'':real^N->bool`] THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`u':real^M->bool`; `u'':real^M->bool`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `(u':real^M->bool) PCROSS (v':real^N->bool)` THEN
  EXISTS_TAC `(u'':real^M->bool) PCROSS (v'':real^N->bool)` THEN
  ASM_SIMP_TAC[PASTECART_IN_PCROSS; PCROSS_MONO; OPEN_IN_PCROSS] THEN
  ASM_MESON_TAC[PCROSS_MONO; SUBSET_TRANS]);;

let LOCALLY_CONNECTED_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        locally connected s /\ locally connected t
        ==> locally connected (s PCROSS t)`,
  MATCH_MP_TAC LOCALLY_PCROSS THEN REWRITE_TAC[CONNECTED_PCROSS]);;

let LOCALLY_PATH_CONNECTED_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        locally path_connected s /\ locally path_connected t
        ==> locally path_connected (s PCROSS t)`,
  MATCH_MP_TAC LOCALLY_PCROSS THEN REWRITE_TAC[PATH_CONNECTED_PCROSS]);;

let LOCALLY_CONNECTED_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        locally connected (s PCROSS t) <=>
        s = {} \/ t = {} \/ locally connected s /\ locally connected t`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; LOCALLY_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; LOCALLY_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[LOCALLY_CONNECTED_PCROSS] THEN
  GEN_REWRITE_TAC LAND_CONV [LOCALLY_CONNECTED] THEN DISCH_TAC THEN
  REWRITE_TAC[LOCALLY_CONNECTED_IM_KLEINEN] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real^M->bool`; `x:real^M`] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(t:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`(u:real^M->bool) PCROSS (t:real^N->bool)`;
      `pastecart (x:real^M) (y:real^N)`]);
    MAP_EVERY X_GEN_TAC [`v:real^N->bool`; `y:real^N`] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(s:real^M->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^M`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`(s:real^M->bool) PCROSS (v:real^N->bool)`;
      `pastecart (x:real^M) (y:real^N)`])] THEN
  ASM_SIMP_TAC[OPEN_IN_PCROSS_EQ; PASTECART_IN_PCROSS; SUBSET_UNIV;
    OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `w:real^(M,N)finite_sum->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`s:real^M->bool`; `t:real^N->bool`; `w:real^(M,N)finite_sum->bool`;
    `x:real^M`; `y:real^N`] PASTECART_IN_INTERIOR_SUBTOPOLOGY) THEN
  ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u':real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
      EXISTS_TAC `IMAGE fstcart (w:real^(M,N)finite_sum->bool)` THEN
      ASM_SIMP_TAC[CONNECTED_LINEAR_IMAGE; LINEAR_FSTCART] THEN
      REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PASTECART; FSTCART_PASTECART]];
    DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` MP_TAC) THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `v':real^N->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `IMAGE sndcart (w:real^(M,N)finite_sum->bool)` THEN
      ASM_SIMP_TAC[CONNECTED_LINEAR_IMAGE; LINEAR_SNDCART] THEN
      REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PASTECART; SNDCART_PASTECART]]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SUBSET; FORALL_IN_PCROSS; PASTECART_IN_PCROSS; FORALL_PASTECART]) THEN
  ASM SET_TAC[]);;

let LOCALLY_PATH_CONNECTED_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        locally path_connected (s PCROSS t) <=>
        s = {} \/ t = {} \/
        locally path_connected s /\ locally path_connected t`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; LOCALLY_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; LOCALLY_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[LOCALLY_PATH_CONNECTED_PCROSS] THEN
  GEN_REWRITE_TAC LAND_CONV [LOCALLY_PATH_CONNECTED] THEN DISCH_TAC THEN
  REWRITE_TAC[LOCALLY_PATH_CONNECTED_IM_KLEINEN] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real^M->bool`; `x:real^M`] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(t:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`(u:real^M->bool) PCROSS (t:real^N->bool)`;
      `pastecart (x:real^M) (y:real^N)`]);
    MAP_EVERY X_GEN_TAC [`v:real^N->bool`; `y:real^N`] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(s:real^M->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^M`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`(s:real^M->bool) PCROSS (v:real^N->bool)`;
      `pastecart (x:real^M) (y:real^N)`])] THEN
  ASM_SIMP_TAC[OPEN_IN_PCROSS_EQ; PASTECART_IN_PCROSS; SUBSET_UNIV;
    OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `w:real^(M,N)finite_sum->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`s:real^M->bool`; `t:real^N->bool`; `w:real^(M,N)finite_sum->bool`;
    `x:real^M`; `y:real^N`] PASTECART_IN_INTERIOR_SUBTOPOLOGY) THEN
  ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u':real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
                     `w:real^(M,N)finite_sum->bool`]
        PATH_CONNECTED_LINEAR_IMAGE) THEN ASM_REWRITE_TAC[LINEAR_FSTCART] THEN
      REWRITE_TAC[path_connected] THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `z:real^M`]) THEN ANTS_TAC THENL
       [REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; FSTCART_PASTECART];
        MATCH_MP_TAC MONO_EXISTS THEN
        REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PASTECART; FSTCART_PASTECART] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]];
    DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` MP_TAC) THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `v':real^N->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
                     `w:real^(M,N)finite_sum->bool`]
        PATH_CONNECTED_LINEAR_IMAGE) THEN ASM_REWRITE_TAC[LINEAR_SNDCART] THEN
      REWRITE_TAC[path_connected] THEN
      DISCH_THEN(MP_TAC o SPECL [`y:real^N`; `z:real^N`]) THEN ANTS_TAC THENL
       [REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; SNDCART_PASTECART];
        MATCH_MP_TAC MONO_EXISTS THEN
        REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PASTECART; SNDCART_PASTECART] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SUBSET; FORALL_IN_PCROSS; PASTECART_IN_PCROSS; FORALL_PASTECART]) THEN
  ASM SET_TAC[]);;

let CARD_EQ_OPEN_IN = prove
 (`!u s:real^N->bool.
      locally connected u /\
      open_in (subtopology euclidean u) s /\
      (?x. x IN s /\ x limit_point_of u)
      ==> s =_c (:real)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN
    SIMP_TAC[CARD_EQ_IMP_LE; CARD_EQ_EUCLIDEAN] THEN
    MATCH_MP_TAC CARD_LE_SUBSET THEN REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[IN_INTER] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LOCALLY_CONNECTED]) THEN
  DISCH_THEN(MP_TAC o SPECL [`u INTER t:real^N->bool`; `x:real^N`]) THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; IN_INTER] THEN
  REWRITE_TAC[OPEN_IN_OPEN; GSYM CONJ_ASSOC; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
  REWRITE_TAC[UNWIND_THM2; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [limit_point_of]) THEN
  DISCH_THEN(MP_TAC o SPEC `t INTER v:real^N->bool`) THEN
  ASM_SIMP_TAC[IN_INTER; OPEN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  TRANS_TAC CARD_LE_TRANS `u INTER v:real^N->bool` THEN
  ASM_SIMP_TAC[CARD_LE_SUBSET] THEN MATCH_MP_TAC CARD_EQ_IMP_LE THEN
  ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN MATCH_MP_TAC CARD_EQ_CONNECTED THEN
  ASM SET_TAC[]);;

let CARD_EQ_OPEN_IN_AFFINE = prove
 (`!u s:real^N->bool.
        affine u /\ ~(aff_dim u = &0) /\
        open_in (subtopology euclidean u) s /\ ~(s = {})
        ==> s =_c (:real)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_EQ_OPEN_IN THEN
  EXISTS_TAC `u:real^N->bool` THEN
  ASM_SIMP_TAC[CONVEX_IMP_LOCALLY_CONNECTED; AFFINE_IMP_CONVEX] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_IMP_PERFECT_AFF_DIM THEN
  ASM_SIMP_TAC[AFFINE_IMP_CONVEX; CONVEX_CONNECTED] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Basic properties of local compactness.                                    *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_COMPACT = prove
 (`!s:real^N->bool.
        locally compact s <=>
        !x. x IN s ==> ?u v. x IN u /\ u SUBSET v /\ v SUBSET s /\
                             open_in (subtopology euclidean s) u /\
                             compact v`,
  GEN_TAC THEN REWRITE_TAC[locally] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM
     (MP_TAC o SPECL [`s INTER ball(x:real^N,&1)`; `x:real^N`]) THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL] THEN
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; REAL_LT_01] THEN
    MESON_TAC[SUBSET_INTER];
    MAP_EVERY X_GEN_TAC [`w:real^N->bool`; `x:real^N`] THEN
    REWRITE_TAC[IMP_CONJ] THEN GEN_REWRITE_TAC LAND_CONV [OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(s INTER ball(x:real^N,e)) INTER u` THEN
    EXISTS_TAC `cball(x:real^N,e) INTER v` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; OPEN_IN_OPEN_INTER; OPEN_BALL; CENTRE_IN_BALL;
                 COMPACT_INTER; COMPACT_CBALL; IN_INTER] THEN
    MP_TAC(ISPECL [`x:real^N`; `e:real`] BALL_SUBSET_CBALL) THEN
    ASM SET_TAC[]]);;

let OPEN_IMP_LOCALLY_COMPACT = prove
 (`!s:real^N->bool. open s ==> locally compact s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LOCALLY_COMPACT] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN FIRST_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`ball(x:real^N,e)`; `cball(x:real^N,e)`] THEN
  ASM_REWRITE_TAC[BALL_SUBSET_CBALL; CENTRE_IN_BALL; COMPACT_CBALL] THEN
  MATCH_MP_TAC OPEN_OPEN_IN_TRANS THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
  ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS]);;

let CLOSED_IMP_LOCALLY_COMPACT = prove
 (`!s:real^N->bool. closed s ==> locally compact s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LOCALLY_COMPACT] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MAP_EVERY EXISTS_TAC
   [`s INTER ball(x:real^N,&1)`; `s INTER cball(x:real^N,&1)`] THEN
  ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; INTER_SUBSET; REAL_LT_01] THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL] THEN
  ASM_SIMP_TAC[CLOSED_INTER_COMPACT; COMPACT_CBALL] THEN
  MP_TAC(ISPECL [`x:real^N`; `&1`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[]);;

let IS_INTERVAL_IMP_LOCALLY_COMPACT = prove
 (`!s:real^N->bool. is_interval s ==> locally compact s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LOCALLY_COMPACT] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`]
   INTERVAL_CONTAINS_COMPACT_NEIGHBOURHOOD) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `d:real`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`s INTER ball(x:real^N,d)`; `interval[a:real^N,b]`] THEN
  ASM_SIMP_TAC[COMPACT_INTERVAL; OPEN_IN_OPEN_INTER; OPEN_BALL] THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL; IN_INTER] THEN ASM SET_TAC[]);;

let LOCALLY_COMPACT_UNIV = prove
 (`locally compact (:real^N)`,
  SIMP_TAC[OPEN_IMP_LOCALLY_COMPACT; OPEN_UNIV]);;

let LOCALLY_COMPACT_INTER = prove
 (`!s t:real^N->bool.
        locally compact s /\ locally compact t
        ==> locally compact (s INTER t)`,
  MATCH_MP_TAC LOCALLY_INTER THEN REWRITE_TAC[COMPACT_INTER]);;

let LOCALLY_COMPACT_OPEN_IN = prove
 (`!s t:real^N->bool.
        open_in (subtopology euclidean s) t /\ locally compact s
        ==> locally compact t`,
  REWRITE_TAC[OPEN_IN_OPEN] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LOCALLY_COMPACT_INTER; OPEN_IMP_LOCALLY_COMPACT]);;

let LOCALLY_COMPACT_CLOSED_IN = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean s) t /\ locally compact s
        ==> locally compact t`,
  REWRITE_TAC[CLOSED_IN_CLOSED] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LOCALLY_COMPACT_INTER; CLOSED_IMP_LOCALLY_COMPACT]);;

let SIGMA_COMPACT = prove
 (`!s:real^N->bool.
        locally compact s
        ==> ?f. COUNTABLE f /\ (!t. t IN f ==> compact t) /\ UNIONS f = s`,
  GEN_TAC THEN REWRITE_TAC[LOCALLY_COMPACT] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->real^N->bool`; `c:real^N->real^N->bool`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (u:real^N->real^N->bool) s`; `s:real^N->bool`]
   LINDELOF_OPEN_IN) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
  REWRITE_TAC[EXISTS_COUNTABLE_SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (c:real^N->real^N->bool) t` THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; FORALL_IN_IMAGE; FORALL_IN_UNIONS] THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE] THEN ASM SET_TAC[]);;

let HOMEOMORPHIC_LOCAL_COMPACTNESS = prove
 (`!s t:real^N->bool.
        s homeomorphic t ==> (locally compact s <=> locally compact t)`,
  MATCH_MP_TAC HOMEOMORPHIC_LOCALLY THEN
  REWRITE_TAC[HOMEOMORPHIC_COMPACTNESS]);;

let LOCALLY_COMPACT_TRANSLATION_EQ = prove
 (`!a:real^N s. locally compact (IMAGE (\x. a + x) s) <=>
                locally compact s`,
  MATCH_MP_TAC LOCALLY_TRANSLATION THEN
  REWRITE_TAC[COMPACT_TRANSLATION_EQ]);;

add_translation_invariants [LOCALLY_COMPACT_TRANSLATION_EQ];;

let LOCALLY_COMPACT_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (locally compact (IMAGE f s) <=> locally compact s)`,
  MATCH_MP_TAC LOCALLY_INJECTIVE_LINEAR_IMAGE THEN
  REWRITE_TAC[COMPACT_LINEAR_IMAGE_EQ]);;

add_linear_invariants [LOCALLY_COMPACT_LINEAR_IMAGE_EQ];;

let LOCALLY_CLOSED = prove
 (`!s:real^N->bool. locally closed s <=> locally compact s`,
  GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[LOCALLY_MONO; COMPACT_IMP_CLOSED]] THEN
  REWRITE_TAC[locally] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`w:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^N->bool`; `x:real^N`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `u INTER ball(x:real^N,&1)` THEN
  EXISTS_TAC `v INTER cball(x:real^N,&1)` THEN
  ASM_SIMP_TAC[OPEN_IN_INTER_OPEN; OPEN_BALL] THEN
  ASM_SIMP_TAC[CLOSED_INTER_COMPACT; COMPACT_CBALL] THEN
  ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; REAL_LT_01] THEN
  MP_TAC(ISPEC `x:real^N` BALL_SUBSET_CBALL) THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Locally compact sets are closed in an open set and are homeomorphic       *)
(* to an absolutely closed set if we have one more dimension to play with.   *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_COMPACT_OPEN_INTER_CLOSURE = prove
 (`!s:real^N->bool. locally compact s ==> ?t. open t /\ s = t INTER closure s`,
  GEN_TAC THEN SIMP_TAC[LOCALLY_COMPACT; OPEN_IN_OPEN; CLOSED_IN_CLOSED] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; TAUT `p /\ x = y /\ q <=> x = y /\ p /\ q`] THEN
  ONCE_REWRITE_TAC[MESON[] `(?a b c. P a b c) <=> (?c b a. P a b c)`] THEN
  REWRITE_TAC[UNWIND_THM2] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->real^N->bool`; `v:real^N->real^N->bool`] THEN
  DISCH_TAC THEN EXISTS_TAC `UNIONS (IMAGE (u:real^N->real^N->bool) s)` THEN
  ASM_SIMP_TAC[CLOSED_CLOSURE; OPEN_UNIONS; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[INTER_UNIONS] THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `UNIONS {v INTER s | v | v IN IMAGE (u:real^N->real^N->bool) s}` THEN
  CONJ_TAC THENL
   [SIMP_TAC[UNIONS_GSPEC; EXISTS_IN_IMAGE] THEN ASM SET_TAC[]; ALL_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f(g x) = f'(g x))
    ==> {f x | x IN IMAGE g s} = {f' x | x IN IMAGE g s}`) THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
  REWRITE_TAC[SUBSET_INTER; INTER_SUBSET] THEN MATCH_MP_TAC  SUBSET_TRANS THEN
  EXISTS_TAC `closure((u:real^N->real^N->bool) x INTER s)` THEN
  ASM_SIMP_TAC[OPEN_INTER_CLOSURE_SUBSET] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `(v:real^N->real^N->bool) x` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[]]);;

let LOCALLY_COMPACT_CLOSED_IN_OPEN = prove
 (`!s:real^N->bool.
    locally compact s ==> ?t. open t /\ closed_in (subtopology euclidean t) s`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP LOCALLY_COMPACT_OPEN_INTER_CLOSURE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  SIMP_TAC[CLOSED_IN_CLOSED_INTER; CLOSED_CLOSURE]);;

let LOCALLY_COMPACT_HOMEOMORPHISM_PROJECTION_CLOSED = prove
 (`!s:real^M->bool.
        locally compact s
        ==> ?t:real^(M,N)finite_sum->bool f.
                closed t /\ homeomorphism (s,t) (f,fstcart)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `closed(s:real^M->bool)` THENL
   [EXISTS_TAC `(s:real^M->bool) PCROSS {vec 0:real^N}` THEN
    EXISTS_TAC `\x. (pastecart x (vec 0):real^(M,N)finite_sum)` THEN
    ASM_SIMP_TAC[CLOSED_PCROSS; CLOSED_SING; HOMEOMORPHISM] THEN
    SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID;
      LINEAR_FSTCART; LINEAR_CONTINUOUS_ON; SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; PASTECART_IN_PCROSS; IN_SING] THEN
    SIMP_TAC[FSTCART_PASTECART];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LOCALLY_COMPACT_OPEN_INTER_CLOSURE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` (STRIP_ASSUME_TAC o GSYM)) THEN
  DISJ_CASES_TAC(SET_RULE `t = (:real^M) \/ ~((:real^M) DIFF t = {})`) THENL
   [ASM_MESON_TAC[CLOSURE_EQ; INTER_UNIV]; ALL_TAC] THEN
  ABBREV_TAC
   `f:real^M->real^(M,N)finite_sum =
      \x. pastecart x (inv(setdist({x},(:real^M) DIFF t)) % vec 1)` THEN
  SUBGOAL_THEN
   `homeomorphism (t,IMAGE (f:real^M->real^(M,N)finite_sum) t) (f,fstcart)`
  ASSUME_TAC THENL
   [SIMP_TAC[HOMEOMORPHISM; SUBSET_REFL; LINEAR_CONTINUOUS_ON;
             LINEAR_FSTCART; FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC(TAUT `(r ==> q /\ s) /\ r /\ p ==> p /\ q /\ r /\ s`) THEN
    CONJ_TAC THENL [SET_TAC[]; EXPAND_TAC "f"] THEN
    SIMP_TAC[FSTCART_PASTECART] THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_ID] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[o_DEF; CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
    REWRITE_TAC[SETDIST_EQ_0_SING; CONTINUOUS_ON_LIFT_SETDIST] THEN
    ASM_SIMP_TAC[CLOSURE_COMPLEMENT; IN_DIFF; IN_UNIV; INTERIOR_OPEN];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (f:real^M->real^(M,N)finite_sum) s` THEN
  EXISTS_TAC `f:real^M->real^(M,N)finite_sum` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
    EXISTS_TAC `IMAGE (f:real^M->real^(M,N)finite_sum) t` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_IMP_CLOSED_MAP THEN MAP_EVERY EXISTS_TAC
       [`fstcart:real^(M,N)finite_sum->real^M`; `t:real^M->bool`] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN
      SIMP_TAC[CLOSED_IN_CLOSED_INTER; CLOSED_CLOSURE];
      SUBGOAL_THEN
       `IMAGE (f:real^M->real^(M,N)finite_sum) t =
        {z | (setdist({fstcart z},(:real^M) DIFF t) % sndcart z) IN {vec 1}}`
      SUBST1_TAC THENL
       [EXPAND_TAC "f" THEN
        REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_ELIM_THM; PASTECART_INJ;
                    FSTCART_PASTECART; SNDCART_PASTECART; IN_IMAGE; IN_INTER;
                    GSYM CONJ_ASSOC; UNWIND_THM1; IN_SING] THEN
        REWRITE_TAC[CART_EQ; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
        MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^N`] THEN
        MP_TAC(ISPECL [`(:real^M) DIFF t`; `x:real^M`]
          (CONJUNCT1 SETDIST_EQ_0_SING)) THEN
        ASM_SIMP_TAC[CLOSURE_COMPLEMENT; IN_DIFF; IN_UNIV; INTERIOR_OPEN] THEN
        ASM_CASES_TAC `(x:real^M) IN t` THEN ASM_SIMP_TAC[REAL_FIELD
         `~(x = &0) ==> (y = inv x * &1 <=> x * y = &1)`] THEN
        DISCH_TAC THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
        REWRITE_TAC[LE_REFL; DIMINDEX_GE_1] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
        REWRITE_TAC[CLOSED_SING] THEN X_GEN_TAC `z:real^(M,N)finite_sum` THEN
        MATCH_MP_TAC CONTINUOUS_MUL THEN
        SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_SNDCART; o_DEF] THEN
        SUBGOAL_THEN
         `(\z:real^(M,N)finite_sum.
             lift(setdist({fstcart z},(:real^M) DIFF t))) =
          (\x. lift (setdist ({x},(:real^M) DIFF t))) o fstcart`
        SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
        SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART] THEN
        REWRITE_TAC[CONTINUOUS_AT_LIFT_SETDIST]]];
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN MAP_EVERY EXISTS_TAC
     [`t:real^M->bool`; `IMAGE (f:real^M->real^(M,N)finite_sum) t`] THEN
    ASM SET_TAC[]]);;

let LOCALLY_COMPACT_HOMEOMORPHIC_CLOSED = prove
 (`!s:real^M->bool.
        locally compact s /\ dimindex(:M) < dimindex(:N)
        ==> ?t:real^N->bool. closed t /\ s homeomorphic t`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `?t:real^(M,1)finite_sum->bool h.
            closed t /\ homeomorphism (s,t) (h,fstcart)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOCALLY_COMPACT_HOMEOMORPHISM_PROJECTION_CLOSED];
    ALL_TAC] THEN
  ABBREV_TAC
   `f:real^(M,1)finite_sum->real^N =
        \x. lambda i. if i <= dimindex(:M) then x$i
                      else x$(dimindex(:M)+1)` THEN
  ABBREV_TAC
   `g:real^N->real^(M,1)finite_sum = (\x. lambda i. x$i)` THEN
  EXISTS_TAC `IMAGE (f:real^(M,1)finite_sum->real^N) t` THEN
  SUBGOAL_THEN `linear(f:real^(M,1)finite_sum->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[linear; CART_EQ] THEN
    SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(g:real^N->real^(M,1)finite_sum)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[linear; CART_EQ] THEN
    SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (g:real^N->real^(M,1)finite_sum)((f:real^(M,1)finite_sum->real^N) x) =
        x`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["f"; "g"] THEN FIRST_ASSUM(MP_TAC o MATCH_MP
     (ARITH_RULE `m < n ==> !i. i <= m + 1 ==> i <= n`)) THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
    REWRITE_TAC[ARITH_RULE `i <= n + 1 <=> i <= n \/ i = n + 1`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CLOSED_INJECTIVE_LINEAR_IMAGE]; ALL_TAC] THEN
  TRANS_TAC HOMEOMORPHIC_TRANS `t:real^(M,1)finite_sum->bool` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[homeomorphic]; ALL_TAC] THEN
  REWRITE_TAC[homeomorphic; HOMEOMORPHISM] THEN MAP_EVERY EXISTS_TAC
   [`f:real^(M,1)finite_sum->real^N`; `g:real^N->real^(M,1)finite_sum`] THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN ASM SET_TAC[]);;

let LOCALLY_COMPACT_CLOSED_INTER_OPEN = prove
 (`!s:real^N->bool.
        locally compact s <=> ?t u. closed t /\ open u /\ s = t INTER u`,
  MESON_TAC[CLOSED_IMP_LOCALLY_COMPACT; OPEN_IMP_LOCALLY_COMPACT;
            LOCALLY_COMPACT_INTER; INTER_COMM; CLOSED_CLOSURE;
            LOCALLY_COMPACT_OPEN_INTER_CLOSURE]);;

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

let PATH_COMPONENT_EQ_CONNECTED_COMPONENT = prove
 (`!s x:real^N.
        locally path_connected s
        ==> (path_component s x = connected_component s x)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN s` THENL
   [ALL_TAC;
    ASM_MESON_TAC[PATH_COMPONENT_EQ_EMPTY; CONNECTED_COMPONENT_EQ_EMPTY]] THEN
  MP_TAC(ISPECL[`s:real^N->bool`; `x:real^N`]
    CONNECTED_CONNECTED_COMPONENT) THEN REWRITE_TAC[CONNECTED_CLOPEN] THEN
  REWRITE_TAC[TAUT `p ==> q \/ r <=> p /\ ~q ==> r`] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[PATH_COMPONENT_EQ_EMPTY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS;
    MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS] THEN
  EXISTS_TAC `s:real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_IN_PATH_COMPONENT_LOCALLY_PATH_CONNECTED;
               CLOSED_IN_PATH_COMPONENT_LOCALLY_PATH_CONNECTED;
               PATH_COMPONENT_SUBSET_CONNECTED_COMPONENT;
               CONNECTED_COMPONENT_SUBSET]);;

let LOCALLY_PATH_CONNECTED_PATH_COMPONENT = prove
 (`!s x:real^N.
        locally path_connected s
        ==> locally path_connected (path_component s x)`,
  MESON_TAC[LOCALLY_PATH_CONNECTED_CONNECTED_COMPONENT;
            PATH_COMPONENT_EQ_CONNECTED_COMPONENT]);;

let OPEN_PATH_CONNECTED_COMPONENT = prove
 (`!s x:real^N. open s ==> path_component s x = connected_component s x`,
  SIMP_TAC[PATH_COMPONENT_EQ_CONNECTED_COMPONENT;
  OPEN_IMP_LOCALLY_PATH_CONNECTED]);;

let PATH_CONNECTED_EQ_CONNECTED_LPC = prove
 (`!s. locally path_connected s ==> (path_connected s <=> connected s)`,
  REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT;
              CONNECTED_IFF_CONNECTED_COMPONENT] THEN
  SIMP_TAC[PATH_COMPONENT_EQ_CONNECTED_COMPONENT]);;

let PATH_CONNECTED_EQ_CONNECTED = prove
 (`!s. open s ==> (path_connected s <=> connected s)`,
  SIMP_TAC[PATH_CONNECTED_EQ_CONNECTED_LPC; OPEN_IMP_LOCALLY_PATH_CONNECTED]);;

let CONNECTED_OPEN_PATH_CONNECTED = prove
 (`!s:real^N->bool. open s /\ connected s ==> path_connected s`,
  SIMP_TAC[PATH_CONNECTED_EQ_CONNECTED]);;

let CONNECTED_OPEN_ARC_CONNECTED = prove
 (`!s:real^N->bool.
      open s /\ connected s
      ==> !x y. x IN s /\ y IN s
                ==> x = y \/
                    ?g. arc g /\
                        path_image g SUBSET s /\
                        pathstart g = x /\
                        pathfinish g = y`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CONNECTED_OPEN_PATH_CONNECTED) THEN
  REWRITE_TAC[PATH_CONNECTED_ARCWISE] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN MESON_TAC[]);;

let OPEN_COMPONENTS = prove
 (`!u:real^N->bool s. open u /\ s IN components u ==> open s`,
  REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC (MESON[IN_COMPONENTS;
  ASSUME `s:real^N->bool IN components u`] `?x. s:real^N->bool =
  connected_component u x`) THEN ASM_SIMP_TAC [OPEN_CONNECTED_COMPONENT]);;

let COMPONENTS_OPEN_UNIQUE = prove
 (`!f:(real^N->bool)->bool s.
        (!c. c IN f ==> open c /\ connected c /\ ~(c = {})) /\
        pairwise DISJOINT f /\ UNIONS f = s
        ==> components s = f`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_DISJOINT_UNIONS_OPEN_UNIQUE THEN
  ASM_REWRITE_TAC[GSYM UNIONS_COMPONENTS; PAIRWISE_DISJOINT_COMPONENTS] THEN
  ASM_MESON_TAC[OPEN_COMPONENTS; IN_COMPONENTS_NONEMPTY;
                IN_COMPONENTS_CONNECTED; OPEN_UNIONS]);;

let CONTINUOUS_ON_COMPONENTS = prove
 (`!f:real^M->real^N s.
        open s /\ (!c. c IN components s ==> f continuous_on c)
        ==> f continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPONENTS_GEN THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_SUBSET THEN
  ASM_MESON_TAC[OPEN_COMPONENTS; IN_COMPONENTS_SUBSET]);;

let CONTINUOUS_ON_COMPONENTS_EQ = prove
 (`!f s. open s
         ==> (f continuous_on s <=>
              !c. c IN components s ==> f continuous_on c)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MESON_TAC[CONTINUOUS_ON_SUBSET; IN_COMPONENTS_SUBSET];
    ASM_MESON_TAC[CONTINUOUS_ON_COMPONENTS]]);;

let CLOSED_IN_UNION_COMPLEMENT_COMPONENT = prove
 (`!u s c:real^N->bool.
        locally connected u /\
        closed_in (subtopology euclidean u) s /\
        c IN components(u DIFF s)
        ==> closed_in (subtopology euclidean u) (s UNION c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `s UNION c:real^N->bool = u DIFF (UNIONS(components(u DIFF s) DELETE c))`
  SUBST1_TAC THENL
   [MP_TAC(ISPEC `(u:real^N->bool) DIFF s` UNIONS_COMPONENTS) THEN
    ONCE_REWRITE_TAC [EXTENSION] THEN
    REWRITE_TAC[IN_UNION; IN_UNIV; IN_UNIONS; IN_DELETE; IN_DIFF] THEN
    MP_TAC(ISPEC `(u:real^N->bool) DIFF s` PAIRWISE_DISJOINT_COMPONENTS) THEN
    REWRITE_TAC[pairwise; SET_RULE
     `DISJOINT s t <=> !x. ~(x IN s /\ x IN t)`] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
    REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
    REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBSET_DIFF] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL] THEN
    MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[IN_DELETE] THEN
    X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC OPEN_IN_TRANS THEN
    EXISTS_TAC `u DIFF s:real^N->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_COMPONENTS_LOCALLY_CONNECTED THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
      EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_SIMP_TAC[OPEN_IN_REFL]]);;

let CLOSED_UNION_COMPLEMENT_COMPONENT = prove
 (`!s c. closed s /\ c IN components((:real^N) DIFF s) ==> closed(s UNION c)`,
  ONCE_REWRITE_TAC[CLOSED_IN] THEN ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CLOSED_IN_UNION_COMPLEMENT_COMPONENT THEN
  ASM_REWRITE_TAC[LOCALLY_CONNECTED_UNIV]);;

let COUNTABLE_COMPONENTS = prove
 (`!s:real^N->bool. open s ==> COUNTABLE(components s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COUNTABLE_DISJOINT_OPEN_SUBSETS THEN
  REWRITE_TAC[PAIRWISE_DISJOINT_COMPONENTS] THEN
  ASM_MESON_TAC[OPEN_COMPONENTS]);;

let FRONTIER_MINIMAL_SEPARATING_CLOSED = prove
 (`!s c. closed s /\ ~connected((:real^N) DIFF s) /\
         (!t. closed t /\ t PSUBSET s ==> connected((:real^N) DIFF t)) /\
         c IN components ((:real^N) DIFF s)
         ==> frontier c = s`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o
    GEN_REWRITE_RULE RAND_CONV [CONNECTED_EQ_CONNECTED_COMPONENTS_EQ]) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
   `~(!x x'. x IN s /\ x' IN s ==> x = x')
    ==> !x. x IN s ==> ?y. y IN s /\ ~(y = x)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `frontier c:real^N->bool`) THEN
  REWRITE_TAC[SET_RULE `s PSUBSET t <=> s SUBSET t /\ ~(t SUBSET s)`;
              GSYM SUBSET_ANTISYM_EQ] THEN
  ASM_SIMP_TAC[FRONTIER_OF_COMPONENTS_CLOSED_COMPLEMENT; FRONTIER_CLOSED] THEN
  MATCH_MP_TAC(TAUT `~r ==> (~p ==> r) ==> p`) THEN
  REWRITE_TAC[connected] THEN
  MAP_EVERY EXISTS_TAC [`c:real^N->bool`; `(:real^N) DIFF closure c`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[OPEN_COMPONENTS; closed];
    REWRITE_TAC[GSYM closed; CLOSED_CLOSURE];
    MP_TAC(ISPEC `c:real^N->bool` INTERIOR_SUBSET) THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    MATCH_MP_TAC(SET_RULE
     `c SUBSET c' ==> c INTER (UNIV DIFF c') INTER s = {}`) THEN
    REWRITE_TAC[GSYM INTERIOR_COMPLEMENT; CLOSURE_SUBSET];
    REWRITE_TAC[frontier] THEN MATCH_MP_TAC(SET_RULE
     `ci = c /\ ~(c = {})
      ==> ~(c INTER (UNIV DIFF (cc DIFF ci)) = {})`) THEN
    ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; INTERIOR_OPEN; closed;
                  OPEN_COMPONENTS];
    REWRITE_TAC[frontier] THEN MATCH_MP_TAC(SET_RULE
     `~(UNIV DIFF c = {})
      ==> ~((UNIV DIFF c) INTER (UNIV DIFF (c DIFF i)) = {})`) THEN
    REWRITE_TAC[GSYM INTERIOR_COMPLEMENT] THEN
    MATCH_MP_TAC(SET_RULE `!t. t SUBSET s /\ ~(t = {}) ==> ~(s = {})`) THEN
    EXISTS_TAC `d:real^N->bool` THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]] THEN
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN
    REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> s INTER t = {}`] THEN
    ASM_MESON_TAC[COMPONENTS_NONOVERLAP; OPEN_COMPONENTS; GSYM closed]]);;

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
(* Accessibility of frontier points.                                         *)
(* ------------------------------------------------------------------------- *)

let DENSE_ACCESSIBLE_FRONTIER_POINTS = prove
 (`!s:real^N->bool v.
        open s /\ open_in (subtopology euclidean (frontier s)) v /\ ~(v = {})
        ==> ?g. arc g /\
                IMAGE g (interval [vec 0,vec 1] DELETE vec 1) SUBSET s /\
                pathstart g IN s /\ pathfinish g IN v`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_CONTAINS_BALL]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `z:real^N`)) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN frontier s` MP_TAC THENL
   [ASM SET_TAC[];
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[IN_DIFF; INTERIOR_OPEN]] THEN
  REWRITE_TAC[closure; IN_UNION; TAUT `(p \/ q) /\ ~p <=> ~p /\ q`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIMPT_INFINITE_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `s INTER ball(z:real^N,r) = {}` THENL
   [ASM_MESON_TAC[INFINITE; FINITE_EMPTY]; DISCH_THEN(K ALL_TAC)] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~((y:real^N) IN frontier s)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[IN_DIFF; INTERIOR_OPEN; frontier]; ALL_TAC] THEN
  SUBGOAL_THEN `path_connected(ball(z:real^N,r))` MP_TAC THENL
   [ASM_SIMP_TAC[CONVEX_BALL; CONVEX_IMP_PATH_CONNECTED]; ALL_TAC] THEN
  REWRITE_TAC[PATH_CONNECTED_ARCWISE] THEN
  DISCH_THEN(MP_TAC o SPECL [`y:real^N`; `z:real^N`]) THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC
    `IMAGE drop {t | t IN interval[vec 0,vec 1] /\
                     (g:real^1->real^N) t IN frontier s}`
   COMPACT_ATTAINS_INF) THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IMP_CONJ] THEN
  REWRITE_TAC[IMP_IMP; FORALL_IN_GSPEC; EXISTS_IN_GSPEC; GSYM IMAGE_o] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; IMAGE_ID] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [MATCH_MP_TAC BOUNDED_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        REWRITE_TAC[BOUNDED_INTERVAL; SUBSET_RESTRICT];
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
        REWRITE_TAC[FRONTIER_CLOSED; CLOSED_INTERVAL; GSYM path] THEN
        ASM_MESON_TAC[arc]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 1:real^1` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; ENDS_IN_UNIT_INTERVAL] THEN
      ASM_MESON_TAC[pathfinish; SUBSET]];
    DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `subpath (vec 0) t (g:real^1->real^N)` THEN
    ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC ARC_SUBPATH_ARC THEN
      ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
      ASM_MESON_TAC[pathstart];
      REWRITE_TAC[arc] THEN STRIP_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [GSYM pathstart] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC; RULE_ASSUM_TAC(SIMP_RULE[path_image]) THEN ASM SET_TAC[]] THEN
    MATCH_MP_TAC(SET_RULE
     `a IN s /\ IMAGE f s DELETE (f a) SUBSET t /\
      (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
      ==> IMAGE f (s DELETE a) SUBSET t`) THEN
    ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; GSYM path_image] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) PATH_IMAGE_SUBPATH o lhand o lhand o
      snd) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[IN_INTERVAL_1]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[REWRITE_RULE[pathfinish] PATHFINISH_SUBPATH] THEN
    MATCH_MP_TAC(SET_RULE
     `IMAGE f (s DELETE a) DIFF t = {}
      ==> IMAGE f s DELETE f a SUBSET t`) THEN
    MATCH_MP_TAC(REWRITE_RULE[TAUT
     `p /\ q /\ ~r ==> ~s <=> p /\ q /\ s ==> r`]
     CONNECTED_INTER_FRONTIER) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [arc]) THEN
        REWRITE_TAC[path] THEN MATCH_MP_TAC
         (REWRITE_RULE[IMP_CONJ_ALT] CONTINUOUS_ON_SUBSET) THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
        REWRITE_TAC[SUBSET; IN_DELETE; GSYM DROP_EQ; IN_INTERVAL_1] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
        EXISTS_TAC `interval(vec 0:real^1,t)` THEN
        REWRITE_TAC[CONNECTED_INTERVAL; CLOSURE_INTERVAL] THEN
        REWRITE_TAC[INTERVAL_EQ_EMPTY_1] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
        COND_CASES_TAC THEN
        ASM_REWRITE_TAC[SUBSET; IN_DELETE; GSYM DROP_EQ; IN_INTERVAL_1] THEN
        REWRITE_TAC[NOT_IN_EMPTY] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[SET_RULE
        `~(IMAGE f s INTER t = {}) <=> ?x. x IN s /\ f x IN t`] THEN
      EXISTS_TAC `vec 0:real^1` THEN
      REWRITE_TAC[IN_INTERVAL_1; IN_DELETE; REAL_LE_REFL] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
      ASM SET_TAC[pathstart];
      REWRITE_TAC[SET_RULE
       `IMAGE g i INTER s = {} <=> !x. x IN i ==> ~(g x IN s)`] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_UNIV; IN_DIFF] THEN
      X_GEN_TAC `z:real^1` THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[GSYM DROP_EQ; IN_INTERVAL_1] THEN DISCH_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
      ASM_REAL_ARITH_TAC]]);;

let DENSE_ACCESSIBLE_FRONTIER_POINTS_CONNECTED = prove
 (`!s:real^N->bool v x.
        open s /\ connected s /\ x IN s /\
        open_in (subtopology euclidean (frontier s)) v /\ ~(v = {})
        ==> ?g. arc g /\
                IMAGE g (interval [vec 0,vec 1] DELETE vec 1) SUBSET s /\
                pathstart g = x /\ pathfinish g IN v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `v:real^N->bool`]
        DENSE_ACCESSIBLE_FRONTIER_POINTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `path_connected(s:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[CONNECTED_OPEN_PATH_CONNECTED]; ALL_TAC] THEN
  REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `pathstart g:real^N`]) THEN
  ASM_REWRITE_TAC[path_component; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:real^1->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f ++ g:real^1->real^N`; `x:real^N`; `pathfinish g:real^N`]
        PATH_CONTAINS_ARC) THEN
  ASM_SIMP_TAC[PATH_JOIN_EQ; ARC_IMP_PATH; PATH_IMAGE_JOIN;
               PATHSTART_JOIN; PATHFINISH_JOIN] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  GEN_REWRITE_TAC LAND_CONV [SUBSET] THEN
  ASM_SIMP_TAC[frontier; INTERIOR_OPEN; IN_DIFF] THEN
  DISCH_TAC THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^1->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE
   `a IN s /\ IMAGE f s DELETE (f a) SUBSET t /\
    (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
    ==> IMAGE f (s DELETE a) SUBSET t`) THEN
  REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM path_image]; ASM_MESON_TAC[arc]] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `h SUBSET f UNION g
    ==> f SUBSET s /\ g DELETE a SUBSET s ==> h DELETE a SUBSET s`)) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[path_image; pathstart; pathfinish]) THEN
  REWRITE_TAC[path_image] THEN ASM SET_TAC[]);;

let DENSE_ACCESSIBLE_FRONTIER_POINT_PAIRS = prove
 (`!s u v:real^N->bool.
         open s /\ connected s /\
         open_in (subtopology euclidean (frontier s)) u /\
         open_in (subtopology euclidean (frontier s)) v /\
         ~(u = {}) /\ ~(v = {}) /\ ~(u = v)
         ==> ?g. arc g /\
                 pathstart g IN u /\ pathfinish g IN v /\
                 IMAGE g (interval(vec 0,vec 1)) SUBSET s`,
  GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN
  GEN_REWRITE_TAC (funpow 2 BINDER_CONV o LAND_CONV o RAND_CONV)
    [GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[DE_MORGAN_THM; GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(MESON[]
   `(!u v. R u v ==> R v u) /\ (!u v. P u v ==> R u v)
    ==> !u v. P u v \/ P v u ==> R u v`) THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `g:real^1->real^N` THEN
    STRIP_TAC THEN EXISTS_TAC `reversepath g:real^1->real^N` THEN
    ASM_SIMP_TAC[ARC_REVERSEPATH; PATHSTART_REVERSEPATH;
                 PATHFINISH_REVERSEPATH] THEN
    REWRITE_TAC[reversepath] THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (SET_RULE `IMAGE f i SUBSET t
                ==> IMAGE r i SUBSET i ==> IMAGE f (IMAGE r i) SUBSET t`)) THEN
    SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[FRONTIER_EMPTY; OPEN_IN_SUBTOPOLOGY_EMPTY] THENL
   [CONV_TAC TAUT; STRIP_TAC THEN UNDISCH_TAC `~(s:real^N->bool = {})`] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`s:real^N->bool`; `v:real^N->bool`; `x:real^N`]
   DENSE_ACCESSIBLE_FRONTIER_POINTS_CONNECTED) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:real^1->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`s:real^N->bool`; `(u DELETE pathfinish g):real^N->bool`; `x:real^N`]
   DENSE_ACCESSIBLE_FRONTIER_POINTS_CONNECTED) THEN
  ASM_SIMP_TAC[OPEN_IN_DELETE; IN_DELETE; LEFT_IMP_EXISTS_THM] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `h:real^1->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(reversepath h ++ g):real^1->real^N`;
                 `pathfinish h:real^N`; `pathfinish g:real^N`]
        PATH_CONTAINS_ARC) THEN
  ASM_SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
               PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
               PATH_REVERSEPATH; ARC_IMP_PATH; PATH_IMAGE_JOIN;
               PATH_IMAGE_REVERSEPATH] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^1->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[OPEN_CLOSED_INTERVAL_1] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
    t SUBSET s /\ IMAGE f s SUBSET u UNION IMAGE f t
    ==> IMAGE f (s DIFF t) SUBSET u`) THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; ENDS_IN_UNIT_INTERVAL] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[arc]; REWRITE_TAC[GSYM path_image]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        SUBSET_TRANS)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish; path_image]) THEN
  REWRITE_TAC[path_image] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some simple positive connection theorems.                                 *)
(* ------------------------------------------------------------------------- *)

let PATH_CONNECTED_CONVEX_DIFF_CARD_LT = prove
 (`!u s:real^N->bool.
    convex u /\ ~(collinear u) /\ s <_c (:real) ==> path_connected(u DIFF s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[path_connected; IN_DIFF; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `a:real^N = b` THENL
   [EXISTS_TAC `linepath(a:real^N,b)` THEN
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_LINEPATH] THEN
    ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `m:real^N = midpoint(a,b)` THEN
  SUBGOAL_THEN `~(m:real^N = a) /\ ~(m = b)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MIDPOINT_EQ_ENDPOINT]; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  GEOM_ORIGIN_TAC `m:real^N` THEN REPEAT GEN_TAC THEN
  GEOM_NORMALIZE_TAC `b:real^N` THEN REWRITE_TAC[] THEN GEN_TAC THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `b:real^N` THEN X_GEN_TAC `bbb:real` THEN
  DISCH_TAC THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
  ASM_REWRITE_TAC[real_abs; REAL_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN POP_ASSUM(K ALL_TAC) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[midpoint; VECTOR_MUL_LID] THEN
  REWRITE_TAC[VECTOR_ARITH `inv(&2) % (a + b):real^N = vec 0 <=> a = --b`] THEN
  ASM_CASES_TAC `a:real^N = --(basis 1)` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(K ALL_TAC) THEN
  REPLICATE_TAC 7 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `segment[--basis 1:real^N,basis 1] SUBSET u` ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^N) IN u` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `&1 / &2` THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?c:real^N k. 1 <= k /\ ~(k = 1) /\ k <= dimindex(:N) /\
                             c IN u /\ ~(c$k = &0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_FORALL_THM; TAUT
     `a /\ ~b /\ c /\ d /\ ~e <=> ~(d ==> a /\ c ==> ~b ==> e)`] THEN
    DISCH_TAC THEN UNDISCH_TAC `~collinear(u:real^N->bool)` THEN
    REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `basis 1:real^N`] THEN
    SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; IN_INSERT; SPAN_INSERT_0] THEN
    REWRITE_TAC[SPAN_SING; SUBSET; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `c:real^N` THEN DISCH_TAC THEN EXISTS_TAC `(c:real^N)$1` THEN
    SIMP_TAC[CART_EQ; VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c:real^N = vec 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CART_EQ; VEC_COMPONENT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[vec 0:real^N,c] SUBSET u` ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?z:real^N. z IN segment[vec 0,c] /\
               (segment[--basis 1,z] UNION segment[z,basis 1]) INTER s = {}`
  STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `linepath(--basis 1:real^N,z) ++ linepath(z,basis 1)` THEN
    ASM_SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATH_LINEPATH;
                 PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_JOIN] THEN
    REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `(t UNION v) INTER s = {}
      ==> t SUBSET u /\ v SUBSET u
          ==> (t UNION v) SUBSET u DIFF s`)) THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    CONJ_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN ASM SET_TAC[]] THEN
  MATCH_MP_TAC(SET_RULE
   `~(s SUBSET {z | z IN s /\ ~P z}) ==> ?z. z IN s /\ P z`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP CARD_LE_SUBSET) THEN
  REWRITE_TAC[CARD_NOT_LE; SET_RULE
   `~((b UNION c) INTER s = {}) <=>
    ~(b INTER s = {}) \/ ~(c INTER s = {})`] THEN
  REWRITE_TAC[SET_RULE
   `{x | P x /\ (Q x \/ R x)} = {x | P x /\ Q x} UNION {x | P x /\ R x}`] THEN
  W(MP_TAC o PART_MATCH lhand UNION_LE_ADD_C o lhand o snd) THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] CARD_LET_TRANS) THEN
  TRANS_TAC CARD_LTE_TRANS `(:real)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_ADD2_ABSORB_LT THEN REWRITE_TAC[real_INFINITE];
    MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
    ASM_SIMP_TAC[CARD_EQ_SEGMENT]] THEN
  REWRITE_TAC[MESON[SEGMENT_SYM] `segment[--a:real^N,b] = segment[b,--a]`] THEN
  SUBGOAL_THEN
   `!b:real^N.
       b IN u /\ ~(b IN s) /\ ~(b = vec 0) /\ b$k = &0
       ==> {z | z IN segment[vec 0,c] /\ ~(segment[z,b] INTER s = {})} <_c
           (:real)`
   (fun th -> CONJ_TAC THEN MATCH_MP_TAC th THEN
              REWRITE_TAC[VECTOR_NEG_EQ_0; VECTOR_NEG_COMPONENT] THEN
              ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL;
                           BASIS_COMPONENT] THEN
              REWRITE_TAC[REAL_NEG_0]) THEN
  REPEAT STRIP_TAC THEN TRANS_TAC CARD_LET_TRANS `s:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; RIGHT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> r /\ p /\ q`] THEN
  MATCH_MP_TAC CARD_LE_RELATIONAL THEN
  MAP_EVERY X_GEN_TAC [`w:real^N`; `x1:real^N`; `x2:real^N`] THEN
  REWRITE_TAC[SEGMENT_SYM] THEN STRIP_TAC THEN
  ASM_CASES_TAC `x2:real^N = x1` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`x1:real^N`; `b:real^N`; `x2:real^N`] INTER_SEGMENT) THEN
  REWRITE_TAC[NOT_IMP; SEGMENT_SYM] THEN
  CONJ_TAC THENL [DISJ2_TAC; REWRITE_TAC[SEGMENT_SYM] THEN ASM SET_TAC[]] THEN
  ONCE_REWRITE_TAC[SET_RULE `{x1,b,x2} = {x1,x2,b}`] THEN
  ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(b:real^N) IN affine hull {vec 0,c}` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `b IN s ==> s SUBSET t ==> b IN t`)) THEN
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_AFFINE_HULL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `segment[c:real^N,vec 0]` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ONCE_REWRITE_TAC[SEGMENT_SYM]] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL; CONVEX_HULL_SUBSET_AFFINE_HULL];
    REWRITE_TAC[AFFINE_HULL_2_ALT; IN_ELIM_THM; IN_UNIV] THEN
    REWRITE_TAC[VECTOR_ADD_LID; VECTOR_SUB_RZERO; NOT_EXISTS_THM] THEN
    X_GEN_TAC `r:real` THEN
    ASM_CASES_TAC `r = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^N. x$k`) THEN
    ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_ENTIRE]]);;

let PATH_CONNECTED_COMPLEMENT_CARD_LT = prove
 (`!s. 2 <= dimindex(:N) /\ s <_c (:real)
       ==> path_connected((:real^N) DIFF s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_CONNECTED_CONVEX_DIFF_CARD_LT THEN
  ASM_REWRITE_TAC[CONVEX_UNIV; COLLINEAR_AFF_DIM; AFF_DIM_UNIV] THEN
  REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC);;

let PATH_CONNECTED_OPEN_IN_DIFF_CARD_LT = prove
 (`!s t:real^N->bool.
        connected s /\ open_in (subtopology euclidean (affine hull s)) s /\
        ~collinear s /\ t <_c (:real)
        ==> path_connected(s DIFF t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT; IN_DIFF] THEN
  REWRITE_TAC[TAUT `(p /\ q) /\ (r /\ s) <=> p /\ r /\ q /\ s`] THEN
  MATCH_MP_TAC CONNECTED_EQUIVALENCE_RELATION_GEN THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN
  REWRITE_TAC[PATH_COMPONENT_SYM; PATH_COMPONENT_TRANS] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
      `open_in (subtopology euclidean (affine hull s)) (u:real^N->bool)`
    MP_TAC THENL [ASM_MESON_TAC[OPEN_IN_TRANS]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:real^N`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(SET_RULE `~(s SUBSET t) ==> ?x. x IN s /\ ~(x IN t)`) THEN
    DISCH_THEN(MP_TAC o MATCH_MP CARD_LE_SUBSET) THEN
    REWRITE_TAC[CARD_NOT_LE] THEN TRANS_TAC CARD_LTE_TRANS `(:real)` THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC CARD_LE_TRANS `ball(x:real^N,r) INTER affine hull s` THEN
    ASM_SIMP_TAC[CARD_LE_SUBSET] THEN MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN MATCH_MP_TAC CARD_EQ_CONVEX THEN
    EXISTS_TAC `x:real^N` THEN
    ASM_SIMP_TAC[CONVEX_INTER; AFFINE_IMP_CONVEX; CONVEX_BALL;
                 AFFINE_AFFINE_HULL; IN_INTER; CENTRE_IN_BALL; HULL_INC] THEN
    SUBGOAL_THEN `~(s SUBSET {x:real^N})` MP_TAC THENL
     [ASM_MESON_TAC[COLLINEAR_SUBSET; COLLINEAR_SING]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_SING; NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x + r / &2 / norm(y - x) % (y - x):real^N` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    ASM_SIMP_TAC[HULL_INC; IN_AFFINE_ADD_MUL_DIFF; AFFINE_AFFINE_HULL] THEN
    REWRITE_TAC[IN_BALL; VECTOR_ARITH `x:real^N = x + y <=> y = vec 0`] THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_DIV_EQ_0; NORM_EQ_0; VECTOR_SUB_EQ;
            REAL_LT_IMP_NZ; NORM_ARITH `dist(x:real^N,x + y) = norm y`] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_CONTAINS_BALL]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:real^N`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ball(x:real^N,r) INTER affine hull s` THEN
    ASM_SIMP_TAC[IN_INTER; HULL_INC; CENTRE_IN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
      EXISTS_TAC `affine hull s:real^N->bool` THEN
      ASM_SIMP_TAC[ONCE_REWRITE_RULE[INTER_COMM]OPEN_IN_OPEN_INTER; OPEN_BALL];
      MAP_EVERY X_GEN_TAC [`y:real^N`; `z:real^N`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`ball(x:real^N,r) INTER affine hull s`; `t:real^N->bool`]
        PATH_CONNECTED_CONVEX_DIFF_CARD_LT) THEN
      ASM_SIMP_TAC[CONVEX_INTER; AFFINE_IMP_CONVEX; CONVEX_BALL;
                   AFFINE_AFFINE_HULL] THEN
      ANTS_TAC THENL
       [REWRITE_TAC[COLLINEAR_AFF_DIM] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
        W(MP_TAC o PART_MATCH (lhs o rand) AFF_DIM_CONVEX_INTER_OPEN o
          lhand o rand o snd) THEN
        SIMP_TAC[AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL; OPEN_BALL] THEN
        ANTS_TAC THENL [ASM SET_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
        ASM_REWRITE_TAC[GSYM COLLINEAR_AFF_DIM];
        REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
        DISCH_THEN(MP_TAC o SPECL [`y:real^N`; `z:real^N`]) THEN
        ASM_REWRITE_TAC[IN_INTER; IN_DIFF] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] PATH_COMPONENT_OF_SUBSET) THEN
        ASM SET_TAC[]]]]);;

let CONNECTED_OPEN_IN_DIFF_CARD_LT = prove
 (`!s t:real^N->bool.
        connected s /\ open_in (subtopology euclidean (affine hull s)) s /\
        ~collinear s /\ t <_c (:real)
        ==> connected(s DIFF t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED THEN
  MATCH_MP_TAC PATH_CONNECTED_OPEN_IN_DIFF_CARD_LT THEN
  ASM_REWRITE_TAC[]);;

let PATH_CONNECTED_OPEN_DIFF_CARD_LT = prove
 (`!s t:real^N->bool.
        2 <= dimindex(:N) /\ open s /\ connected s /\ t <_c (:real)
        ==> path_connected(s DIFF t)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[EMPTY_DIFF; PATH_CONNECTED_EMPTY] THEN
  MATCH_MP_TAC PATH_CONNECTED_OPEN_IN_DIFF_CARD_LT THEN
  ASM_REWRITE_TAC[COLLINEAR_AFF_DIM] THEN
  ASM_SIMP_TAC[AFFINE_HULL_OPEN; AFF_DIM_OPEN] THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LE; SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
  ASM_ARITH_TAC);;

let CONNECTED_OPEN_DIFF_CARD_LT = prove
 (`!s t:real^N->bool.
        2 <= dimindex(:N) /\ open s /\ connected s /\ t <_c (:real)
        ==> connected(s DIFF t)`,
  SIMP_TAC[PATH_CONNECTED_OPEN_DIFF_CARD_LT; PATH_CONNECTED_IMP_CONNECTED]);;

let PATH_CONNECTED_OPEN_DIFF_COUNTABLE = prove
 (`!s t:real^N->bool.
        2 <= dimindex(:N) /\ open s /\ connected s /\ COUNTABLE t
        ==> path_connected(s DIFF t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_CONNECTED_OPEN_DIFF_CARD_LT THEN
  ASM_REWRITE_TAC[GSYM CARD_NOT_LE] THEN
  ASM_MESON_TAC[UNCOUNTABLE_REAL; CARD_LE_COUNTABLE]);;

let CONNECTED_OPEN_DIFF_COUNTABLE = prove
 (`!s t:real^N->bool.
        2 <= dimindex(:N) /\ open s /\ connected s /\ COUNTABLE t
        ==> connected(s DIFF t)`,
  SIMP_TAC[PATH_CONNECTED_OPEN_DIFF_COUNTABLE; PATH_CONNECTED_IMP_CONNECTED]);;

let PATH_CONNECTED_OPEN_DELETE = prove
 (`!s a:real^N. 2 <= dimindex(:N) /\ open s /\ connected s
                ==> path_connected(s DELETE a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SET_RULE `s DELETE a = s DIFF {a}`] THEN
  MATCH_MP_TAC PATH_CONNECTED_OPEN_DIFF_COUNTABLE THEN
  ASM_REWRITE_TAC[COUNTABLE_SING]);;

let CONNECTED_OPEN_DELETE = prove
 (`!s a:real^N. 2 <= dimindex(:N) /\ open s /\ connected s
                ==> connected(s DELETE a)`,
  SIMP_TAC[PATH_CONNECTED_OPEN_DELETE; PATH_CONNECTED_IMP_CONNECTED]);;

let PATH_CONNECTED_PUNCTURED_UNIVERSE = prove
 (`!a. 2 <= dimindex(:N) ==> path_connected((:real^N) DIFF {a})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_CONNECTED_OPEN_DIFF_COUNTABLE THEN
  ASM_REWRITE_TAC[OPEN_UNIV; CONNECTED_UNIV; COUNTABLE_SING]);;

let CONNECTED_PUNCTURED_UNIVERSE = prove
 (`!a. 2 <= dimindex(:N) ==> connected((:real^N) DIFF {a})`,
  SIMP_TAC[PATH_CONNECTED_PUNCTURED_UNIVERSE; PATH_CONNECTED_IMP_CONNECTED]);;

let PATH_CONNECTED_PUNCTURED_BALL = prove
 (`!a:real^N r. 2 <= dimindex(:N) ==> path_connected(ball(a,r) DELETE a)`,
  SIMP_TAC[PATH_CONNECTED_OPEN_DELETE; OPEN_BALL; CONNECTED_BALL]);;

let CONNECTED_PUNCTURED_BALL = prove
 (`!a:real^N r. 2 <= dimindex(:N) ==> connected(ball(a,r) DELETE a)`,
  SIMP_TAC[CONNECTED_OPEN_DELETE; OPEN_BALL; CONNECTED_BALL]);;

let PATH_CONNECTED_SPHERE = prove
 (`!a:real^N r. 2 <= dimindex(:N) ==> path_connected(sphere(a,r))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sphere; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN GEN_TAC THEN
  REWRITE_TAC[VECTOR_SUB_RZERO] THEN DISCH_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `r < &0 \/ r = &0 \/ &0 < r`)
  THENL
   [ASM_SIMP_TAC[NORM_ARITH `r < &0 ==> ~(norm(x:real^N) = r)`] THEN
    REWRITE_TAC[EMPTY_GSPEC; PATH_CONNECTED_EMPTY];
    ASM_REWRITE_TAC[NORM_EQ_0; SING_GSPEC; PATH_CONNECTED_SING];
    SUBGOAL_THEN
     `{x:real^N | norm x = r} =
      IMAGE (\x. r / norm x % x) ((:real^N) DIFF {vec 0})`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_DIFF; IN_SING; IN_UNIV] THEN
      ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; REAL_DIV_RMUL;
                   NORM_EQ_0; REAL_ARITH `&0 < r ==> abs r = r`] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `x:real^N` THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
      ASM_MESON_TAC[NORM_0; REAL_LT_IMP_NZ];
      MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[PATH_CONNECTED_PUNCTURED_UNIVERSE] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    REWRITE_TAC[o_DEF; CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING] THEN
    DISCH_TAC THEN REWRITE_TAC[real_div; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_CMUL THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_AT_WITHIN_INV) THEN
    ASM_REWRITE_TAC[NORM_EQ_0] THEN MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
    REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_AT_LIFT_NORM]]]);;

let CONNECTED_SPHERE = prove
 (`!a:real^N r. 2 <= dimindex(:N) ==> connected(sphere(a,r))`,
  SIMP_TAC[PATH_CONNECTED_SPHERE; PATH_CONNECTED_IMP_CONNECTED]);;

let CONNECTED_SPHERE_EQ = prove
 (`!a:real^N r. connected(sphere(a,r)) <=> 2 <= dimindex(:N) \/ r <= &0`,
  let lemma = prove
   (`!a:real^1 r. &0 < r
         ==> ?x y. ~(x = y) /\ dist(a,x) = r /\ dist(a,y) = r`,
    MP_TAC SPHERE_1 THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_SPHERE; IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
    `~(a = b) ==> ?x y. ~(x = y) /\ (x = a \/ x = b) /\ (y = a \/ y = b)`) THEN
    REWRITE_TAC[VECTOR_ARITH `a - r:real^1 = a + r <=> r = vec 0`] THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN ASM_REAL_ARITH_TAC) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[SPHERE_EMPTY; CONNECTED_EMPTY; REAL_LT_IMP_LE] THEN
  ASM_CASES_TAC `r = &0` THEN
  ASM_SIMP_TAC[SPHERE_SING; REAL_LE_REFL; CONNECTED_SING] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[GSYM REAL_NOT_LT]] THEN
  EQ_TAC THEN SIMP_TAC[CONNECTED_SPHERE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONNECTED_FINITE_IFF_SING) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> (2 <= n <=> ~(n = 1))`] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM DIMINDEX_1] THEN
  DISCH_TAC THEN FIRST_ASSUM (fun th ->
    REWRITE_TAC[GEOM_EQUAL_DIMENSION_RULE th FINITE_SPHERE_1]) THEN
  REWRITE_TAC[SET_RULE
   `~(s = {} \/ ?a. s = {a}) <=> ?x y. ~(x = y) /\ x IN s /\ y IN s`] THEN
  REWRITE_TAC[IN_SPHERE] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o C GEOM_EQUAL_DIMENSION_RULE lemma) THEN
  ASM_REWRITE_TAC[]);;

let PATH_CONNECTED_SPHERE_EQ = prove
 (`!a:real^N r. path_connected(sphere(a,r)) <=> 2 <= dimindex(:N) \/ r <= &0`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[GSYM CONNECTED_SPHERE_EQ; PATH_CONNECTED_IMP_CONNECTED];
    STRIP_TAC THEN ASM_SIMP_TAC[PATH_CONNECTED_SPHERE]] THEN
  ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[SPHERE_EMPTY; PATH_CONNECTED_EMPTY] THEN
  ASM_CASES_TAC `r = &0` THEN
  ASM_SIMP_TAC[SPHERE_SING; PATH_CONNECTED_SING] THEN
  ASM_REAL_ARITH_TAC);;

let FINITE_SPHERE = prove
 (`!a:real^N r. FINITE(sphere(a,r)) <=> r <= &0 \/ dimindex(:N) = 1`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `dimindex(:N) = 1` THEN
  ASM_REWRITE_TAC[] THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[GSYM DIMINDEX_1]) THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o C PROVE_HYP
      (GEOM_EQUAL_DIMENSION_RULE(ASSUME `dimindex(:N) = dimindex(:1)`)
      FINITE_SPHERE_1));
    ASM_SIMP_TAC[CONNECTED_SPHERE; ARITH_RULE `2 <= n <=> 1 <= n /\ ~(n = 1)`;
                 DIMINDEX_GE_1; CONNECTED_FINITE_IFF_SING] THEN
    REWRITE_TAC[SET_RULE `(s = {} \/ ?a. s = {a}) <=>
                          (!a b. a IN s /\ b IN s ==> a = b)`] THEN
    SIMP_TAC[IN_SPHERE] THEN EQ_TAC THENL [ALL_TAC; CONV_TAC NORM_ARITH] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `r:real`] VECTOR_CHOOSE_DIST) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `a - (x - a):real^N`]) THEN
    FIRST_X_ASSUM(K ALL_TAC o check (is_neg o concl)) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC NORM_ARITH]);;

let LIMIT_POINT_OF_SPHERE = prove
 (`!a r x:real^N. x limit_point_of sphere(a,r) <=>
                  &0 < r /\ 2 <= dimindex(:N) /\ x IN sphere(a,r)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `FINITE(sphere(a:real^N,r))` THENL
   [ASM_SIMP_TAC[LIMIT_POINT_FINITE]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[FINITE_SPHERE]) THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_NOT_LE; ARITH; REAL_NOT_LT] THEN
  ASM_SIMP_TAC[GSYM REAL_NOT_LE; DIMINDEX_GE_1;
               ARITH_RULE `1 <= n ==> (2 <= n <=> ~(n = 1))`] THEN
  EQ_TAC THEN REWRITE_TAC[REWRITE_RULE[CLOSED_LIMPT] CLOSED_SPHERE] THEN
  DISCH_TAC THEN MATCH_MP_TAC CONNECTED_IMP_PERFECT THEN
  ASM_SIMP_TAC[CONNECTED_SPHERE_EQ; DIMINDEX_GE_1;
               ARITH_RULE `1 <= n ==> (2 <= n <=> ~(n = 1))`] THEN
  ASM_MESON_TAC[FINITE_SING]);;

let CARD_EQ_SPHERE = prove
 (`!a:real^N r. 2 <= dimindex(:N) /\ &0 < r ==> sphere(a,r) =_c (:real)`,
  SIMP_TAC[CONNECTED_CARD_EQ_IFF_NONTRIVIAL; CONNECTED_SPHERE] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET)) THEN
  ASM_REWRITE_TAC[FINITE_SING; FINITE_SPHERE; REAL_NOT_LE; DE_MORGAN_THM] THEN
  ASM_ARITH_TAC);;

let PATH_CONNECTED_ANNULUS = prove
 (`(!a:real^N r1 r2.
        2 <= dimindex(:N)
        ==> path_connected {x | r1 < norm(x - a) /\ norm(x - a) < r2}) /\
   (!a:real^N r1 r2.
        2 <= dimindex(:N)
        ==> path_connected {x | r1 < norm(x - a) /\ norm(x - a) <= r2}) /\
   (!a:real^N r1 r2.
        2 <= dimindex(:N)
        ==> path_connected {x | r1 <= norm(x - a) /\ norm(x - a) < r2}) /\
   (!a:real^N r1 r2.
        2 <= dimindex(:N)
        ==> path_connected {x | r1 <= norm(x - a) /\ norm(x - a) < r2})`,
  let lemma = prove
   (`!a:real^N P.
      2 <= dimindex(:N) /\ path_connected {lift r | &0 <= r /\ P r}
      ==> path_connected {x | P(norm(x - a))}`,
    REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC `a:real^N` THEN
    REWRITE_TAC[VECTOR_SUB_RZERO] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `{x:real^N | P(norm(x))} =
      IMAGE (\z. drop(fstcart z) % sndcart z)
            {pastecart x y | x IN {lift x | &0 <= x /\ P x} /\
                             y IN {y | norm y = &1}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
      REWRITE_TAC[EXISTS_IN_GSPEC; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      X_GEN_TAC `z:real^N` THEN REWRITE_TAC[EXISTS_LIFT; LIFT_DROP] THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      REWRITE_TAC[LIFT_IN_IMAGE_LIFT; IMAGE_ID] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN
      ASM_REWRITE_TAC[real_abs] THEN ASM_CASES_TAC `z:real^N = vec 0` THENL
       [MAP_EVERY EXISTS_TAC [`&0`; `basis 1:real^N`] THEN
        ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL; VECTOR_MUL_LZERO] THEN
        ASM_MESON_TAC[NORM_0; REAL_ABS_NUM; REAL_LE_REFL];
        MAP_EVERY EXISTS_TAC [`norm(z:real^N)`; `inv(norm z) % z:real^N`] THEN
        ASM_SIMP_TAC[REAL_ABS_NORM; NORM_MUL; VECTOR_MUL_ASSOC; VECTOR_MUL_LID;
          NORM_POS_LE; REAL_ABS_INV; REAL_MUL_RINV; REAL_MUL_LINV; NORM_EQ_0]];
      MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
        REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART];
        REWRITE_TAC[GSYM PCROSS] THEN
        MATCH_MP_TAC PATH_CONNECTED_PCROSS THEN ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[NORM_ARITH `norm y = norm(y - vec 0:real^N)`] THEN
        ONCE_REWRITE_TAC[NORM_SUB] THEN
        REWRITE_TAC[REWRITE_RULE[dist] (GSYM sphere)] THEN
        ASM_SIMP_TAC[PATH_CONNECTED_SPHERE]]]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `a:real^N` lemma) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONVEX_IMP_PATH_CONNECTED THEN
  MATCH_MP_TAC IS_INTERVAL_CONVEX THEN
  REWRITE_TAC[is_interval] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[IN_IMAGE_LIFT_DROP; FORALL_1; DIMINDEX_1] THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM drop] THEN REAL_ARITH_TAC);;

let CONNECTED_ANNULUS = prove
 (`(!a:real^N r1 r2.
        2 <= dimindex(:N)
        ==> connected {x | r1 < norm(x - a) /\ norm(x - a) < r2}) /\
   (!a:real^N r1 r2.
        2 <= dimindex(:N)
        ==> connected {x | r1 < norm(x - a) /\ norm(x - a) <= r2}) /\
   (!a:real^N r1 r2.
        2 <= dimindex(:N)
        ==> connected {x | r1 <= norm(x - a) /\ norm(x - a) < r2}) /\
   (!a:real^N r1 r2.
        2 <= dimindex(:N)
        ==> connected {x | r1 <= norm(x - a) /\ norm(x - a) < r2})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED THEN
  ASM_SIMP_TAC[PATH_CONNECTED_ANNULUS]);;

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
    REWRITE_TAC[REWRITE_RULE[ONCE_REWRITE_RULE[DIST_SYM] dist] sphere] THEN
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

let CONNECTED_DIFF_BALL = prove
 (`!s a:real^N r.
        2 <= dimindex(:N) /\ connected s /\ cball(a,r) SUBSET s
        ==> connected(s DIFF ball(a,r))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_DIFF_OPEN_FROM_CLOSED THEN
  EXISTS_TAC `cball(a:real^N,r)` THEN
  ASM_REWRITE_TAC[OPEN_BALL; CLOSED_CBALL; BALL_SUBSET_CBALL] THEN
  REWRITE_TAC[CBALL_DIFF_BALL] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] dist] THEN
  ASM_SIMP_TAC[CONNECTED_SPHERE]);;

let PATH_CONNECTED_DIFF_BALL = prove
 (`!s a:real^N r.
        2 <= dimindex(:N) /\ path_connected s /\ cball(a,r) SUBSET s
        ==> path_connected(s DIFF ball(a,r))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `ball(a:real^N,r) = {}` THEN
  ASM_SIMP_TAC[DIFF_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BALL_EQ_EMPTY; REAL_NOT_LE]) THEN
  REWRITE_TAC[path_connected] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:real^N` o GEN_REWRITE_RULE I [SUBSET]) THEN
  ASM_SIMP_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [path_connected]) THEN
  DISCH_THEN(fun th ->
   MP_TAC(SPECL [`x:real^N`; `a:real^N`] th) THEN
   MP_TAC(SPECL [`y:real^N`; `a:real^N`] th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:real^1->real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g2:real^1->real^N`; `(:real^N) DIFF ball(a,r)`]
        EXISTS_PATH_SUBPATH_TO_FRONTIER) THEN
  MP_TAC(ISPECL [`g1:real^1->real^N`; `(:real^N) DIFF ball(a,r)`]
        EXISTS_PATH_SUBPATH_TO_FRONTIER) THEN
  ASM_SIMP_TAC[CENTRE_IN_BALL; IN_DIFF; IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
  ASM_SIMP_TAC[FRONTIER_COMPLEMENT; INTERIOR_COMPLEMENT; CLOSURE_BALL] THEN
  ASM_SIMP_TAC[FRONTIER_BALL; IN_SPHERE] THEN
  X_GEN_TAC `h1:real^1->real^N` THEN STRIP_TAC THEN
  X_GEN_TAC `h2:real^1->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `r:real`] PATH_CONNECTED_SPHERE) THEN
  ASM_REWRITE_TAC[path_connected] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`pathfinish h1:real^N`; `pathfinish h2:real^N`]) THEN
  ASM_SIMP_TAC[IN_SPHERE] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `h1 ++ h ++ reversepath h2:real^1->real^N` THEN
  ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_REVERSEPATH;
               PATHFINISH_REVERSEPATH; PATH_JOIN; PATH_REVERSEPATH;
               PATH_IMAGE_JOIN; PATH_IMAGE_REVERSEPATH] THEN
  REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          SUBSET_TRANS)) THEN
    UNDISCH_TAC `cball(a:real^N,r) SUBSET s` THEN
    SIMP_TAC[SUBSET; IN_CBALL; IN_SPHERE; IN_BALL; IN_DIFF] THEN
    MESON_TAC[REAL_LE_REFL; REAL_LT_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `s SUBSET t /\ s INTER u = {} ==> s SUBSET t DIFF u`) THEN
  (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `s DELETE a SUBSET (UNIV DIFF t) ==> ~(a IN u) /\ u SUBSET t
      ==> s INTER u = {}`)) THEN
  ASM_REWRITE_TAC[BALL_SUBSET_CBALL; IN_BALL; REAL_LT_REFL]);;

let CONNECTED_OPEN_DIFF_CBALL = prove
 (`!s a:real^N r.
        2 <= dimindex (:N) /\ open s /\ connected s /\ cball(a,r) SUBSET s
        ==> connected(s DIFF cball(a,r))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `cball(a:real^N,r) = {}` THEN ASM_REWRITE_TAC[DIFF_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CBALL_EQ_EMPTY; REAL_NOT_LT]) THEN
  SUBGOAL_THEN `?r'. r < r' /\ cball(a:real^N,r') SUBSET s`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `s = (:real^N)` THENL
     [EXISTS_TAC `r + &1` THEN ASM_SIMP_TAC[SUBSET_UNIV] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`cball(a:real^N,r)`; `(:real^N) DIFF s`]
      SETDIST_POS_LE) THEN
    REWRITE_TAC[REAL_ARITH `&0 <= x <=> &0 < x \/ x = &0`] THEN
    ASM_SIMP_TAC[SETDIST_EQ_0_COMPACT_CLOSED; GSYM OPEN_CLOSED;
                 COMPACT_CBALL; CBALL_EQ_EMPTY] THEN
    ASM_REWRITE_TAC[SET_RULE `UNIV DIFF s = {} <=> s = UNIV`] THEN
    ASM_SIMP_TAC[SET_RULE `b INTER (UNIV DIFF s) = {} <=> b SUBSET s`;
                 REAL_ARITH `&0 <= r ==> ~(r < &0)`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `r + setdist(cball(a,r),(:real^N) DIFF s) / &2` THEN
    ASM_REWRITE_TAC[REAL_LT_ADDR; REAL_HALF; SUBSET; IN_CBALL] THEN
    X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `x:real^N = a` THENL
     [ASM_MESON_TAC[SUBSET; DIST_REFL; IN_CBALL]; ALL_TAC] THEN
    ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[REAL_NOT_LE] THEN
    MP_TAC(ISPECL [`cball(a:real^N,r)`; `(:real^N) DIFF s`;
                   `a + r / dist(a,x) % (x - a):real^N`; `x:real^N`]
      SETDIST_LE_DIST) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_CBALL] THEN
    REWRITE_TAC[NORM_ARITH `dist(a:real^N,a + x) = norm x`] THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; ONCE_REWRITE_RULE[DIST_SYM] dist;
                 REAL_ABS_NORM; REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
    ASM_REWRITE_TAC[REAL_ARITH `abs r <= r <=> &0 <= r`] THEN
    REWRITE_TAC[NORM_MUL; VECTOR_ARITH
     `x - (a + d % (x - a)):real^N = (&1 - d) % (x - a)`] THEN
    ONCE_REWRITE_TAC[GSYM REAL_ABS_NORM] THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL] THEN
    REWRITE_TAC[REAL_ABS_NORM; REAL_SUB_RDISTRIB] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[IN_CBALL; ONCE_REWRITE_RULE[DIST_SYM] dist] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `s DIFF cball(a:real^N,r) =
                  s DIFF ball(a,r') UNION
                  {x | r < norm(x - a) /\ norm(x - a) <= r'}`
    SUBST1_TAC THENL
     [REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] (GSYM dist)] THEN
      REWRITE_TAC[GSYM REAL_NOT_LE; GSYM IN_CBALL] THEN MATCH_MP_TAC(SET_RULE
       `b' SUBSET c' /\ c' SUBSET s /\ c SUBSET b'
        ==> s DIFF c = (s DIFF b') UNION {x | ~(x IN c) /\ x IN c'}`) THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL] THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONNECTED_UNION THEN
      ASM_SIMP_TAC[CONNECTED_ANNULUS; PATH_CONNECTED_DIFF_BALL;
        PATH_CONNECTED_IMP_CONNECTED; CONNECTED_OPEN_PATH_CONNECTED] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] (GSYM dist)] THEN
      REWRITE_TAC[GSYM REAL_NOT_LE; GSYM IN_CBALL] THEN MATCH_MP_TAC(SET_RULE
       `c' SUBSET s /\ (?x. x IN c' /\ ~(x IN b') /\ ~(x IN c))
        ==> ~((s DIFF b') INTER {x | ~(x IN c) /\ x IN c'} = {})`) THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `a + r' % basis 1:real^N` THEN
      REWRITE_TAC[IN_BALL; IN_CBALL] THEN
      REWRITE_TAC[NORM_ARITH `dist(a:real^N,a + x) = norm x`] THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
      ASM_REAL_ARITH_TAC]]);;

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

let COBOUNDED_UNBOUNDED_COMPONENTS = prove
 (`!s. bounded ((:real^N) DIFF s) ==> ?c. c IN components s /\ ~bounded c`,
  REWRITE_TAC[components; EXISTS_IN_GSPEC; COBOUNDED_UNBOUNDED_COMPONENT]);;

let COBOUNDED_UNIQUE_UNBOUNDED_COMPONENTS = prove
 (`!s c c'.
        2 <= dimindex(:N) /\
        bounded ((:real^N) DIFF s) /\
        c IN components s /\ ~bounded c /\
        c' IN components s /\ ~bounded c'
        ==> c' = c`,
  REWRITE_TAC[components; IN_ELIM_THM] THEN
  MESON_TAC[COBOUNDED_UNIQUE_UNBOUNDED_COMPONENT]);;

let COBOUNDED_HAS_BOUNDED_COMPONENT = prove
 (`!s. 2 <= dimindex(:N) /\ bounded((:real^N) DIFF s) /\ ~connected s
       ==> ?c. c IN components s /\ bounded c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?c c':real^N->bool. c IN components s /\ c' IN components s /\ ~(c = c')`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `~(s = {}) /\ ~(?a. s = {a}) ==> ?x y. x IN s /\ y IN s /\ ~(x = y)`) THEN
    ASM_REWRITE_TAC[COMPONENTS_EQ_SING_EXISTS; COMPONENTS_EQ_EMPTY] THEN
    ASM_MESON_TAC[DIFF_EMPTY; NOT_BOUNDED_UNIV];
    ASM_MESON_TAC[COBOUNDED_UNIQUE_UNBOUNDED_COMPONENTS]]);;

(* ------------------------------------------------------------------------- *)
(* Self-homeomorphisms shuffling points about in various ways.               *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHISM_MOVING_POINT_EXISTS = prove
 (`!s t a b:real^N.
        open_in (subtopology euclidean (affine hull s)) s /\
        s SUBSET t /\ t SUBSET affine hull s /\
        connected s /\ a IN s /\ b IN s
        ==> ?f g. homeomorphism (t,t) (f,g) /\ f a = b /\
                  {x | ~(f x = x /\ g x = x)} SUBSET s /\
                  bounded {x | ~(f x = x /\ g x = x)}`,
  let lemma1 = prove
   (`!a t r u:real^N.
          affine t /\ a IN t /\ u IN ball(a,r) INTER t
          ==> ?f g. homeomorphism (cball(a,r) INTER t,cball(a,r) INTER t)
                                  (f,g) /\
                    f(a) = u /\ (!x. x IN sphere(a,r) ==> f(x) = x)`,
    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH `r <= &0 \/ &0 < r`) THENL
     [ASM_MESON_TAC[BALL_EMPTY; INTER_EMPTY; NOT_IN_EMPTY]; ALL_TAC] THEN
    EXISTS_TAC `\x:real^N. (&1 - norm(x - a) / r) % (u - a) + x` THEN
    REWRITE_TAC[LEFT_EXISTS_AND_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
      ASM_SIMP_TAC[COMPACT_INTER_CLOSED; COMPACT_CBALL; CLOSED_AFFINE];
      ASM_SIMP_TAC[IN_SPHERE; ONCE_REWRITE_RULE[NORM_SUB] dist;
                   REAL_DIV_REFL; REAL_LT_IMP_NZ; IN_INTER] THEN
      REWRITE_TAC[real_div; VECTOR_SUB_REFL; NORM_0; REAL_MUL_LZERO] THEN
      REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF; LIFT_SUB] THEN
      SIMP_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST; CONTINUOUS_ON_SUB] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div; LIFT_CMUL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST; CONTINUOUS_ON_SUB];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> f x IN s) /\ (!y. y IN s ==> ?x. x IN s /\ f x = y)
        ==> IMAGE f s = s`) THEN REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[VECTOR_ARITH
       `(&1 - n) % (u - a) + x:real^N = a + (&1 - n) % (u - a) + (x - a)`];
      ALL_TAC] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN GEOM_ORIGIN_TAC `a:real^N` THEN
    REWRITE_TAC[IN_BALL_0; VECTOR_SUB_RZERO; IN_CBALL_0; IN_INTER] THEN
    REWRITE_TAC[VECTOR_ADD_LID; VECTOR_ADD_RID;
                VECTOR_ARITH `a + x:real^N = a + y <=> x = y`;
                VECTOR_ARITH `(&1 - n) % u + a + x = (&1 - m) % u + a + y <=>
                              (n - m) % u:real^N = x - y`] THEN
    REWRITE_TAC[REAL_ARITH `x / r - y / r:real = (x - y) / r`] THENL
     [ALL_TAC;
      REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REPEAT GEN_TAC THEN
      ASM_CASES_TAC `x:real^N = y` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `norm(x:real^N) = norm(y:real^N)` THEN
      ASM_REWRITE_TAC[real_div; REAL_SUB_REFL; REAL_MUL_LZERO; VECTOR_MUL_LZERO;
                      VECTOR_ARITH `vec 0:real^N = x - y <=> x = y`] THEN
      STRIP_TAC THEN FIRST_ASSUM(MP_TAC o AP_TERM `norm:real^N->real`) THEN
      ASM_SIMP_TAC[NORM_MUL; REAL_ABS_MUL; REAL_ABS_INV] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (NORM_ARITH
       `r = norm(x - y:real^N) ==> r < abs(norm x - norm y) * &1 ==> F`)) THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ONCE_REWRITE_TAC[REAL_MUL_SYM]] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ;
                   REAL_ARITH `&0 < r ==> &0 < abs r`] THEN
      ASM_REAL_ARITH_TAC] THEN
    REPEAT GEN_TAC THEN
    ASM_CASES_TAC `subspace(t:real^N->bool)` THENL
     [ALL_TAC; ASM_MESON_TAC[AFFINE_IMP_SUBSPACE]] THEN
    ASM_SIMP_TAC[SUBSPACE_ADD; SUBSPACE_MUL] THEN
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
       `norm(x) + norm(y) <= &1 * r ==> norm(x + y:real^N) <= r`) THEN
      ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LE_LDIV_EQ; REAL_ARITH
       `(a * u + x) / r:real = a * u / r + x / r`] THEN
      MATCH_MP_TAC(REAL_ARITH
       `x <= &1 /\ a <= abs(&1 - x) * &1 ==> a + x <= &1`) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\a. lift((&1 - drop a) * r - norm(y - drop a % u:real^N))`;
      `vec 0:real^1`; `vec 1:real^1`; `&0`; `1`]
          IVT_DECREASING_COMPONENT_1) THEN
    REWRITE_TAC[DIMINDEX_1; GSYM drop; LIFT_DROP; DROP_VEC] THEN
    REWRITE_TAC[REAL_POS; LE_REFL; REAL_SUB_REFL; VECTOR_MUL_LZERO] THEN
    REWRITE_TAC[REAL_SUB_RZERO; VECTOR_SUB_RZERO; REAL_MUL_LID] THEN
    REWRITE_TAC[NORM_ARITH `&0 * r - norm(x:real^N) <= &0`] THEN
    ASM_REWRITE_TAC[REAL_SUB_LE; GSYM EXISTS_DROP; IN_INTERVAL_1] THEN
    ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_ARITH `(&1 - x) * r - b:real = r - r * x - b`] THEN
      REWRITE_TAC[LIFT_SUB; LIFT_CMUL; LIFT_DROP] THEN
      REPEAT(MATCH_MP_TAC CONTINUOUS_SUB THEN CONJ_TAC THEN
             REWRITE_TAC[CONTINUOUS_CONST]) THEN
      SIMP_TAC[CONTINUOUS_CMUL; CONTINUOUS_AT_ID] THEN
      MATCH_MP_TAC CONTINUOUS_LIFT_NORM_COMPOSE THEN
      MATCH_MP_TAC CONTINUOUS_SUB THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_MUL THEN
      REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_AT_ID; CONTINUOUS_CONST];

      ASM_SIMP_TAC[DROP_VEC; REAL_FIELD
       `&0 < r ==> ((&1 - x) * r - n = &0 <=> &1 - n / r = x)`] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `y - a % u:real^N` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
      ASM_SIMP_TAC[SUBSPACE_SUB; SUBSPACE_MUL] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]) in
  let lemma2 = prove
   (`!a t u v:real^N r.
          affine t /\ a IN t /\
          u IN ball(a,r) INTER t /\ v IN ball(a,r) INTER t
          ==> ?f g. homeomorphism (cball(a,r) INTER t,cball(a,r) INTER t)
                                  (f,g) /\ f(u) = v /\
                    !x. x IN sphere(a,r) /\ x IN t ==> f(x) = x`,
    REPEAT GEN_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH `r <= &0 \/ &0 < r`) THENL
     [ASM_MESON_TAC[BALL_EMPTY; INTER_EMPTY; NOT_IN_EMPTY];
      REPLICATE_TAC 2 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`a:real^N`; `t:real^N->bool`; `r:real`] lemma1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
        FIRST_ASSUM(CONJUNCTS_THEN(MP_TAC o MATCH_MP th))) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f1:real^N->real^N`; `g1:real^N->real^N`] THEN
    STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`f2:real^N->real^N`; `g2:real^N->real^N`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `(f1:real^N->real^N) o (g2:real^N->real^N)` THEN
    EXISTS_TAC `(f2:real^N->real^N) o (g1:real^N->real^N)` THEN
    REWRITE_TAC[o_THM; SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN ASM_MESON_TAC[HOMEOMORPHISM_SYM];
      RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism; IN_INTER]) THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`a:real^N`; `r:real`] CENTRE_IN_CBALL) THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM SET_TAC[];
        MP_TAC(ISPECL [`a:real^N`; `r:real`] SPHERE_SUBSET_CBALL) THEN
        ASM SET_TAC[]]]) in
  let lemma3 = prove
   (`!a t u v:real^N r s.
        affine t /\ a IN t /\ ball(a,r) INTER t SUBSET s /\ s SUBSET t /\
        u IN ball(a,r) INTER t /\ v IN ball(a,r) INTER t
        ==> ?f g. homeomorphism (s,s) (f,g) /\ f(u) = v /\
                  {x | ~(f x = x /\ g x = x)} SUBSET ball(a,r) INTER t`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `t:real^N->bool`; `u:real^N`; `v:real^N`;
                   `r:real`] lemma2) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `\x:real^N. if x IN ball(a,r) INTER t then f x else x` THEN
    EXISTS_TAC `\x:real^N. if x IN ball(a,r) INTER t then g x else x` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHISM]) THEN
    REWRITE_TAC[HOMEOMORPHISM; SUBSET; FORALL_IN_IMAGE] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(!x:real^N. x IN ball(a,r) INTER t ==> f x IN ball(a,r)) /\
                  (!x:real^N. x IN ball(a,r) INTER t ==> g x IN ball(a,r))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM CBALL_DIFF_SPHERE] THEN ASM SET_TAC[]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THEN
    TRY(X_GEN_TAC `x:real^N` THEN
        ASM_CASES_TAC `x IN ball(a:real^N,r)` THEN ASM_SIMP_TAC[] THEN
        MP_TAC(ISPECL [`a:real^N`; `r:real`] BALL_SUBSET_CBALL) THEN
        REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[]) THEN
        ASM SET_TAC[]) THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(cball(a,r) INTER t) UNION
                ((t:real^N->bool) DIFF ball(a,r))` THEN
    (CONJ_TAC THENL
      [ALL_TAC;
       MP_TAC(ISPECL [`a:real^N`; `r:real`] BALL_SUBSET_CBALL) THEN
       ASM SET_TAC[]]) THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    ASM_SIMP_TAC[CLOSED_CBALL; CLOSED_DIFF; OPEN_BALL; CONTINUOUS_ON_ID;
             GSYM IN_DIFF; CBALL_DIFF_BALL; CLOSED_AFFINE; CLOSED_INTER] THEN
    MP_TAC(ISPECL [`a:real^N`; `r:real`] SPHERE_SUBSET_CBALL) THEN
    MP_TAC(ISPECL [`a:real^N`; `r:real`] CBALL_DIFF_BALL) THEN
    ASM SET_TAC[]) in
  REWRITE_TAC[TAUT `p /\ q /\ r /\ s /\ t ==> u <=>
                    p /\ q /\ r /\ s ==> t ==> u`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  ONCE_REWRITE_TAC[TAUT `p ==> q <=> p ==> p /\ q`] THEN
  MATCH_MP_TAC CONNECTED_EQUIVALENCE_RELATION THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `a:real^N` THENL
   [X_GEN_TAC `b:real^N` THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^N->real^N` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^N` THEN
    REWRITE_TAC[HOMEOMORPHISM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[TAUT `~(p /\ q) <=> ~(q /\ p)`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`b:real^N`; `c:real^N`] THEN
    MAP_EVERY (fun t -> ASM_CASES_TAC t THEN ASM_REWRITE_TAC[])
     [`(a:real^N) IN s`; `(b:real^N) IN s`; `(c:real^N) IN s`] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f1:real^N->real^N`; `g1:real^N->real^N`] THEN
    STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`f2:real^N->real^N`; `g2:real^N->real^N`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `(f2:real^N->real^N) o (f1:real^N->real^N)` THEN
    EXISTS_TAC `(g1:real^N->real^N) o (g2:real^N->real^N)` THEN
    ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[HOMEOMORPHISM_COMPOSE]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `{x | ~(f1 x = x /\ g1 x = x)} UNION
                {x:real^N | ~(f2 x = x /\ g2 x = x)}` THEN
    ASM_REWRITE_TAC[BOUNDED_UNION] THEN ASM SET_TAC[];
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_CONTAINS_BALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^N` o CONJUNCT2) THEN ASM_SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s INTER ball(a:real^N,r)` THEN
    ASM_SIMP_TAC[IN_INTER; CENTRE_IN_BALL; OPEN_IN_OPEN_INTER; OPEN_BALL] THEN
    X_GEN_TAC `b:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`a:real^N`; `affine hull s:real^N->bool`;
      `a:real^N`; `b:real^N`; `r:real`; `t:real^N->bool`]
        lemma3) THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL; AFFINE_AFFINE_HULL; HULL_INC; IN_INTER] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    ASM_MESON_TAC[BOUNDED_SUBSET; BOUNDED_BALL; INTER_SUBSET; SUBSET_TRANS]]);;

let HOMEOMORPHISM_MOVING_POINTS_EXISTS_GEN = prove
 (`!s t x (y:A->real^N) k.
        &2 <= aff_dim s /\ open_in (subtopology euclidean (affine hull s)) s /\
        s SUBSET t /\ t SUBSET affine hull s /\ connected s /\
        FINITE k /\ (!i. i IN k ==> x i IN s /\ y i IN s) /\
        pairwise (\i j. ~(x i = x j) /\ ~(y i = y j)) k
        ==> ?f g. homeomorphism (t,t) (f,g) /\
                  (!i. i IN k ==> f(x i) = y i) /\
                  {x | ~(f x = x /\ g x = x)} SUBSET s /\
                  bounded {x | ~(f x = x /\ g x = x)}`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `FINITE(k:A->bool)` THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`s:real^N->bool`,`s:real^N->bool`) THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`k:A->bool`,`k:A->bool`) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN REPEAT(EXISTS_TAC `I:real^N->real^N`) THEN
    REWRITE_TAC[HOMEOMORPHISM_I; NOT_IN_EMPTY; I_THM; EMPTY_GSPEC] THEN
    REWRITE_TAC[EMPTY_SUBSET; BOUNDED_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:A`; `k:A->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `s:real^N->bool` THEN
  REWRITE_TAC[PAIRWISE_INSERT; FORALL_IN_INSERT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
  STRIP_TAC THEN MP_TAC(ISPECL
   [`s DIFF IMAGE (y:A->real^N) k`; `t:real^N->bool`;
    `(f:real^N->real^N) ((x:A->real^N) i)`; `(y:A->real^N) i`]
   HOMEOMORPHISM_MOVING_POINT_EXISTS) THEN
  SUBGOAL_THEN
   `affine hull (s DIFF (IMAGE (y:A->real^N) k)) = affine hull s`
  SUBST1_TAC THENL
   [MATCH_MP_TAC AFFINE_HULL_OPEN_IN THEN CONJ_TAC THENL
     [TRANS_TAC OPEN_IN_TRANS `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
      MATCH_MP_TAC FINITE_IMP_CLOSED_IN THEN
      ASM_SIMP_TAC[FINITE_IMAGE] THEN ASM SET_TAC[];

      REWRITE_TAC[SET_RULE `s DIFF t = {} <=> s SUBSET t`] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        FINITE_SUBSET)) THEN
      ASM_SIMP_TAC[FINITE_IMAGE; CONNECTED_FINITE_IFF_SING] THEN
      UNDISCH_TAC `&2 <= aff_dim(s:real^N->bool)` THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_SING] THEN
      CONV_TAC INT_REDUCE_CONV];
    ASM_REWRITE_TAC[]] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FINITE_IMP_CLOSED_IN THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[];
      ASM SET_TAC[];
      MATCH_MP_TAC CONNECTED_OPEN_IN_DIFF_CARD_LT THEN
      ASM_REWRITE_TAC[COLLINEAR_AFF_DIM;
                      INT_ARITH `~(s:int <= &1) <=> &2 <= s`] THEN
      MATCH_MP_TAC CARD_LT_FINITE_INFINITE THEN
      ASM_SIMP_TAC[FINITE_IMAGE; real_INFINITE];
      ALL_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN REWRITE_TAC[IN_DIFF] THEN
    (CONJ_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[IN_DIFF]]) THEN
    SIMP_TAC[SET_RULE `~(y IN IMAGE f s) <=> !x. x IN s ==> ~(f x = y)`] THEN
    ASM SET_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`h:real^N->real^N`; `k:real^N->real^N`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`(h:real^N->real^N) o (f:real^N->real^N)`;
      `(g:real^N->real^N) o (k:real^N->real^N)`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[HOMEOMORPHISM_COMPOSE]; ALL_TAC] THEN
    ASM_SIMP_TAC[o_THM] THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `{x | ~(f x = x /\ g x = x)} UNION
                {x:real^N | ~(h x = x /\ k x = x)}` THEN
    ASM_REWRITE_TAC[BOUNDED_UNION] THEN ASM SET_TAC[]]);;

let HOMEOMORPHISM_MOVING_POINTS_EXISTS = prove
 (`!s t x (y:A->real^N) k.
        2 <= dimindex(:N) /\ open s /\ connected s /\ s SUBSET t /\
        FINITE k /\ (!i. i IN k ==> x i IN s /\ y i IN s) /\
        pairwise (\i j. ~(x i = x j) /\ ~(y i = y j)) k
        ==> ?f g. homeomorphism (t,t) (f,g) /\
                  (!i. i IN k ==> f(x i) = y i) /\
                  {x | ~(f x = x /\ g x = x)} SUBSET s /\
                  bounded {x | ~(f x = x /\ g x = x)}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [STRIP_TAC THEN REPEAT(EXISTS_TAC `I:real^N->real^N`) THEN
    REWRITE_TAC[HOMEOMORPHISM_I; NOT_IN_EMPTY; I_THM; EMPTY_GSPEC] THEN
    REWRITE_TAC[EMPTY_SUBSET; BOUNDED_EMPTY] THEN ASM SET_TAC[];
    STRIP_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHISM_MOVING_POINTS_EXISTS_GEN THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  SUBGOAL_THEN `affine hull s = (:real^N)` SUBST1_TAC THENL
   [MATCH_MP_TAC AFFINE_HULL_OPEN THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; AFF_DIM_UNIV] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_LE; SUBSET_UNIV]]);;

let HOMEOMORPHISM_GROUPING_POINTS_EXISTS = prove
 (`!u s t k:real^N->bool.
        open u /\ open s /\ connected s /\ ~(u = {}) /\
        FINITE k /\ k SUBSET s /\ u SUBSET s /\ s SUBSET t
        ==> ?f g. homeomorphism (t,t) (f,g) /\
                  {x | ~(f x = x /\ g x = x)} SUBSET s /\
                  bounded {x | ~(f x = x /\ g x = x)} /\
                  !x. x IN k ==> (f x) IN u`,
  let lemma1 = prove
   (`!a b:real^1 c d:real^1.
          drop a < drop b /\ drop c < drop d
          ==> ?f g. homeomorphism (interval[a,b],interval[c,d]) (f,g) /\
                    f(a) = c /\ f(b) = d`,
    REPEAT STRIP_TAC THEN EXISTS_TAC
     `\x. c + (drop x - drop a) / (drop b - drop a) % (d - c:real^1)` THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_SUB_LT; REAL_LT_IMP_NZ;
                 REAL_ARITH `(a - a) / x = &0`; LEFT_EXISTS_AND_THM] THEN
    CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
    REWRITE_TAC[COMPACT_INTERVAL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
      REWRITE_TAC[LIFT_CMUL; real_div; o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
      REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      REWRITE_TAC[EXTENSION; IN_INTERVAL_1; IN_IMAGE] THEN
      ASM_SIMP_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; DROP_SUB; REAL_FIELD
       `a < b /\ c < d
        ==> (x = c + (y - a) / (b - a) * (d - c) <=>
             a + (x - c) / (d - c) * (b - a) = y)`] THEN
      REWRITE_TAC[GSYM EXISTS_DROP; UNWIND_THM1] THEN
      REWRITE_TAC[REAL_ARITH
       `c <= c + x /\ c + x <= d <=> &0 <= x /\ x <= &1 * (d - c)`] THEN
      ASM_SIMP_TAC[REAL_LE_MUL_EQ; REAL_LE_RMUL_EQ; REAL_SUB_LT] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[VECTOR_ARITH `a + x:real^N = a + y <=> x = y`;
                  REAL_FIELD `a < b ==> (x / (b - a) = y / (b - a) <=> x = y)`;
                  REAL_ARITH `x - a:real = y - a <=> x = y`;
                  VECTOR_MUL_RCANCEL; DROP_EQ; VECTOR_SUB_EQ] THEN
      ASM_MESON_TAC[REAL_LT_REFL]]) in
  let lemma2 = prove
   (`!a b c:real^1 u v w:real^1 f1 g1 f2 g2.
          homeomorphism (interval[a,b],interval[u,v]) (f1,g1) /\
          homeomorphism (interval[b,c],interval[v,w]) (f2,g2)
          ==> b IN interval[a,c] /\ v IN interval[u,w] /\
              f1 a = u /\ f1 b = v /\ f2 b = v /\ f2 c = w
              ==> ?f g. homeomorphism(interval[a,c],interval[u,w]) (f,g) /\
                        f a = u /\ f c = w /\
                        (!x. x IN interval[a,b] ==> f x = f1 x) /\
                        (!x. x IN interval[b,c] ==> f x = f2 x)`,
    REWRITE_TAC[IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM
     (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism])) THEN
    EXISTS_TAC `\x. if drop x <= drop b then (f1:real^1->real^1) x
                    else f2 x` THEN
    ASM_REWRITE_TAC[LEFT_EXISTS_AND_THM; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[DROP_EQ; REAL_ARITH `b <= c ==> (c <= b <=> c = b)`] THEN
    CONJ_TAC THENL [REWRITE_TAC[GSYM CONJ_ASSOC]; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
    REWRITE_TAC[COMPACT_INTERVAL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CASES_LE THEN
      ASM_SIMP_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID; DROP_EQ] THEN
      CONJ_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      SIMP_TAC[SUBSET; FORALL_DROP; IN_ELIM_THM; IN_INTERVAL_1];
      SUBGOAL_THEN
       `interval[a:real^1,c] = interval[a,b] UNION interval[b,c] /\
        interval[u:real^1,w] = interval[u,v] UNION interval[v,w]`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IMAGE_UNION] THEN BINOP_TAC THEN FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
        MATCH_MP_TAC(SET_RULE
         `(!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
        SIMP_TAC[IN_INTERVAL_1; REAL_ARITH
           `b <= c ==> (c <= b <=> c = b)`] THEN
        ASM_MESON_TAC[DROP_EQ]];
      REWRITE_TAC[FORALL_LIFT] THEN MATCH_MP_TAC REAL_WLOG_LT THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[FORALL_DROP; LIFT_DROP; IN_INTERVAL_1] THEN
      MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN DISCH_TAC THEN
      ASM_CASES_TAC `drop y <= drop b` THEN ASM_REWRITE_TAC[] THENL
       [COND_CASES_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; REAL_NOT_LE]) THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; REAL_NOT_LE]) THENL
       [ALL_TAC; ASM_MESON_TAC[REAL_LT_IMP_LE]] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(f1:real^1->real^1) x IN interval[u,v] INTER interval[v,w]`
      MP_TAC THENL
       [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
         [ALL_TAC; ASM_REWRITE_TAC[]] THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTERVAL_1] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[IN_INTER; IN_INTERVAL_1] THEN DISCH_THEN(MP_TAC o MATCH_MP
       (REAL_ARITH `(a <= x /\ x <= b) /\ (b <= x /\ x <= c) ==> x = b`)) THEN
      REWRITE_TAC[DROP_EQ] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `(f1:real^1->real^1) x = f1 b /\ (f2:real^1->real^1) y = f2 b`
      MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(MESON[]
       `!g1:real^1->real^1 g2:real^1->real^1.
          g1(f1 x) = x /\ g1(f1 b) = b /\ g2(f2 y) = y /\ g2(f2 b) = b
          ==> f1 x = f1 b /\ f2 y = f2 b ==> x = y`) THEN
      MAP_EVERY EXISTS_TAC [`g1:real^1->real^1`; `g2:real^1->real^1`] THEN
      REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC]) in
  let lemma3 = prove
   (`!a b c d u v:real^1.
          interval[c,d] SUBSET interval(a,b) /\
          interval[u,v] SUBSET interval(a,b) /\
          ~(interval(c,d) = {}) /\ ~(interval(u,v) = {})
          ==> ?f g. homeomorphism (interval[a,b],interval[a,b]) (f,g) /\
                    f a = a /\ f b = b /\
                    !x. x IN interval[c,d] ==> f(x) IN interval[u,v]`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; INTERVAL_NE_EMPTY_1] THEN
    ASM_CASES_TAC `drop u < drop v` THEN
    ASM_SIMP_TAC[REAL_ARITH `u < v ==> ~(v < u)`] THEN
    ASM_CASES_TAC `interval[c:real^1,d] = {}` THENL
     [DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT(EXISTS_TAC `I:real^1->real^1`) THEN
      REWRITE_TAC[HOMEOMORPHISM_I; NOT_IN_EMPTY; I_THM];
      RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY_1]) THEN
      ASM_SIMP_TAC[REAL_ARITH `c <= d ==> ~(d < c)`] THEN STRIP_TAC] THEN
    MP_TAC(ISPECL [`d:real^1`; `b:real^1`; `v:real^1`; `b:real^1`] lemma1) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f3:real^1->real^1`; `g3:real^1->real^1`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:real^1`; `d:real^1`; `u:real^1`; `v:real^1`] lemma1) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f2:real^1->real^1`; `g2:real^1->real^1`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`a:real^1`; `c:real^1`; `a:real^1`; `u:real^1`] lemma1) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f1:real^1->real^1`; `g1:real^1->real^1`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    GEN_REWRITE_TAC I [IMP_IMP] THEN DISCH_THEN(fun th ->
      ASSUME_TAC(CONJUNCT2 th) THEN MP_TAC(MATCH_MP lemma2 th)) THEN
    ASM_SIMP_TAC[IN_INTERVAL_1; REAL_LT_IMP_LE; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f4:real^1->real^1`; `g4:real^1->real^1`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    GEN_REWRITE_TAC I [IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP lemma2) THEN
    ASM_SIMP_TAC[IN_INTERVAL_1; REAL_LT_IMP_LE; LEFT_IMP_EXISTS_THM] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN SIMP_TAC[] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
    X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [HOMEOMORPHISM]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1]) THEN
    SUBGOAL_THEN `drop a <= drop x` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]]) in
  let lemma4 = prove
   (`!s k u t:real^1->bool.
          open u /\ open s /\ connected s /\ ~(u = {}) /\
          FINITE k /\ k SUBSET s /\ u SUBSET s /\ s SUBSET t
          ==> ?f g. homeomorphism (t,t) (f,g) /\
                    (!x. x IN k ==> f(x) IN u) /\
                    {x | ~(f x = x /\ g x = x)} SUBSET s /\
                    bounded {x | ~(f x = x /\ g x = x)}`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `?c d:real^1. ~(interval(c,d) = {}) /\ interval[c,d] SUBSET u`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `open(u:real^1->bool)` THEN
      REWRITE_TAC[OPEN_CONTAINS_INTERVAL] THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      DISCH_THEN(X_CHOOSE_TAC `y:real^1`) THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^1`) THEN
      ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?a b:real^1. ~(interval(a,b) = {}) /\
                   k SUBSET interval[a,b] /\
                   interval[a,b] SUBSET s`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `k:real^1->bool = {}` THENL
       [ASM_MESON_TAC[SUBSET_TRANS; EMPTY_SUBSET]; ALL_TAC] THEN
      MP_TAC(SPEC `IMAGE drop k` COMPACT_ATTAINS_SUP) THEN
      MP_TAC(SPEC `IMAGE drop k` COMPACT_ATTAINS_INF) THEN
      ASM_SIMP_TAC[GSYM IMAGE_o; o_DEF; LIFT_DROP; IMAGE_EQ_EMPTY;
        IMAGE_ID; FINITE_IMP_COMPACT; EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^1` STRIP_ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `b:real^1` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `open(s:real^1->bool)` THEN
      REWRITE_TAC[OPEN_CONTAINS_INTERVAL] THEN
      DISCH_THEN(MP_TAC o SPEC `b:real^1`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
      MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL_1] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`a:real^1`; `v:real^1`] THEN
      REWRITE_TAC[INTERVAL_NE_EMPTY_1] THEN FIRST_X_ASSUM(MP_TAC o
        GEN_REWRITE_RULE I [GSYM IS_INTERVAL_CONNECTED_1]) THEN
      REWRITE_TAC[IS_INTERVAL_1] THEN
      ASM_MESON_TAC[GSYM MEMBER_NOT_EMPTY; REAL_LET_TRANS; REAL_LE_TRANS;
                    REAL_LT_IMP_LE; SUBSET; REAL_LE_TOTAL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?w z:real^1. interval[w,z] SUBSET s /\
                   interval[a,b] UNION interval[c,d] SUBSET interval(w,z)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN
        `?w z:real^1. interval[w,z] SUBSET s /\
                      interval[a,b] UNION interval[c,d] SUBSET interval[w,z]`
      STRIP_ASSUME_TAC THENL
       [EXISTS_TAC `lift(min (drop a) (drop c))` THEN
        EXISTS_TAC `lift(max (drop b) (drop d))` THEN
        REWRITE_TAC[UNION_SUBSET; SUBSET_INTERVAL_1; LIFT_DROP] THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o
           GEN_REWRITE_RULE I [GSYM IS_INTERVAL_CONNECTED_1]) THEN
          REWRITE_TAC[IS_INTERVAL_1; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
          REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          EXISTS_TAC `lift(min (drop a) (drop c))` THEN
          EXISTS_TAC `lift(max (drop b) (drop d))` THEN
          ASM_REWRITE_TAC[LIFT_DROP] THEN
          REWRITE_TAC[real_min; real_max] THEN CONJ_TAC THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
          ASM_MESON_TAC[ENDS_IN_INTERVAL; SUBSET; INTERVAL_EQ_EMPTY_1;
                        REAL_LT_IMP_LE];
          ASM_REAL_ARITH_TAC];
        UNDISCH_TAC `open(s:real^1->bool)` THEN
        REWRITE_TAC[OPEN_CONTAINS_INTERVAL] THEN DISCH_THEN(fun th ->
          MP_TAC(SPEC `z:real^1` th) THEN MP_TAC(SPEC `w:real^1` th)) THEN
        SUBGOAL_THEN `(w:real^1) IN interval[w,z] /\ z IN interval[w,z]`
        STRIP_ASSUME_TAC THENL
         [REWRITE_TAC[ENDS_IN_INTERVAL] THEN MP_TAC
           (ISPECL [`a:real^1`; `b:real^1`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
          ASM SET_TAC[];
          REWRITE_TAC[UNION_SUBSET]] THEN
        ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
        MAP_EVERY X_GEN_TAC [`w0:real^1`; `w1:real^1`] THEN
        REWRITE_TAC[IN_INTERVAL_1; SUBSET] THEN STRIP_TAC THEN
        ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
        MAP_EVERY X_GEN_TAC [`z0:real^1`; `z1:real^1`] THEN
        STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`w0:real^1`; `z1:real^1`] THEN
        RULE_ASSUM_TAC
         (REWRITE_RULE[ENDS_IN_UNIT_INTERVAL; INTERVAL_NE_EMPTY_1;
                       UNION_SUBSET; SUBSET_INTERVAL_1]) THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_INTERVAL_1]) THEN
        X_GEN_TAC `x:real^1` THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`)) THEN
        ASM_CASES_TAC `(x:real^1) IN s` THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [UNION_SUBSET]) THEN
    MP_TAC(ISPECL
     [`w:real^1`; `z:real^1`; `a:real^1`; `b:real^1`; `c:real^1`; `d:real^1`]
     lemma3) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:real^1->real^1`; `g:real^1->real^1`] THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    EXISTS_TAC `\x:real^1. if x IN interval[w,z] then f x else x` THEN
    EXISTS_TAC `\x:real^1. if x IN interval[w,z] then g x else x` THEN
    ASSUME_TAC(ISPECL [`w:real^1`; `z:real^1`]INTERVAL_OPEN_SUBSET_CLOSED) THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM SET_TAC[];
      ALL_TAC;
      ASM SET_TAC[];
      ASM SET_TAC[];
      ALL_TAC;
      ASM SET_TAC[];
      ASM SET_TAC[];
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `interval[w:real^1,z]` THEN
      REWRITE_TAC[BOUNDED_INTERVAL] THEN ASM SET_TAC[]] THEN
    (SUBGOAL_THEN
      `t = interval[w:real^1,z] UNION (t DIFF interval(w,z))`
      (fun th -> SUBST1_TAC th THEN
                 MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
                 ASSUME_TAC(SYM th))
     THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
     ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[CLOSED_INTERVAL] THEN
       ASM SET_TAC[];
       MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL] THEN
       MATCH_MP_TAC OPEN_SUBSET THEN REWRITE_TAC[OPEN_INTERVAL] THEN
       ASM SET_TAC[];
       REWRITE_TAC[CLOSED_DIFF_OPEN_INTERVAL_1; SET_RULE
        `p /\ ~p \/ x IN t DIFF s /\ x IN u <=> x IN t /\ x IN u DIFF s`] THEN
       MAP_EVERY (MP_TAC o ISPECL [`w:real^1`; `z:real^1`])
                 (CONJUNCTS ENDS_IN_INTERVAL) THEN
       ASM SET_TAC[]])) in
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `2 <= dimindex(:N)` THENL
   [MP_TAC(ISPECL
     [`CARD(k:real^N->bool)`; `u:real^N->bool`] CHOOSE_SUBSET_STRONG) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[FINITE_IMP_NOT_OPEN]; ALL_TAC] THEN
    REWRITE_TAC[HAS_SIZE; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `p:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:real^N->bool`; `p:real^N->bool`] CARD_EQ_BIJECTION) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `y:real^N->real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`s:real^N->bool`; `t:real^N->bool`; `\x:real^N. x`;
      `y:real^N->real^N`; `k:real^N->bool`]
     HOMEOMORPHISM_MOVING_POINTS_EXISTS) THEN
    ASM_REWRITE_TAC[pairwise] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LE]) THEN
    SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> (n < 2 <=> n = 1)`] THEN
    REWRITE_TAC[GSYM DIMINDEX_1] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ISOMORPHISMS_UNIV_UNIV) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`h:real^N->real^1`; `j:real^1->real^N`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`IMAGE (h:real^N->real^1) s`;
      `IMAGE (h:real^N->real^1) k`;
      `IMAGE (h:real^N->real^1) u`;
      `IMAGE (h:real^N->real^1) t`]
        lemma4) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_SUBSET; IMAGE_EQ_EMPTY;
                 CONNECTED_CONTINUOUS_IMAGE; LINEAR_CONTINUOUS_ON] THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[OPEN_BIJECTIVE_LINEAR_IMAGE_EQ];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM; homeomorphism]] THEN
    MAP_EVERY X_GEN_TAC [`f:real^1->real^1`; `g:real^1->real^1`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`(j:real^1->real^N) o (f:real^1->real^1) o (h:real^N->real^1)`;
      `(j:real^1->real^N) o (g:real^1->real^1) o (h:real^N->real^1)`] THEN
    ASM_REWRITE_TAC[o_THM; IMAGE_o] THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_COMPOSE; LINEAR_CONTINUOUS_ON] THEN
    ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `{x | ~(j ((f:real^1->real^1) (h x)) = x /\ j (g (h x)) = x)} =
      IMAGE (j:real^1->real^N) {x | ~(f x = x /\ g x = x)}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_SIMP_TAC[BOUNDED_LINEAR_IMAGE]]);;

let HOMEOMORPHISM_GROUPING_POINTS_EXISTS_GEN = prove
 (`!u s t k:real^N->bool.
        open_in (subtopology euclidean (affine hull s)) s /\
        s SUBSET t /\ t SUBSET affine hull s /\ connected s /\
        FINITE k /\ k SUBSET s /\
        open_in (subtopology euclidean s) u /\ ~(u = {})
        ==> ?f g. homeomorphism (t,t) (f,g) /\
                  (!x. x IN k ==> f(x) IN u) /\
                  {x | ~(f x = x /\ g x = x)} SUBSET s /\
                  bounded {x | ~(f x = x /\ g x = x)}`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&2 <= aff_dim(s:real^N->bool)` THENL
   [MP_TAC(ISPECL
     [`CARD(k:real^N->bool)`; `u:real^N->bool`] CHOOSE_SUBSET_STRONG) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[GSYM INFINITE] THEN
      MATCH_MP_TAC INFINITE_OPEN_IN THEN
      EXISTS_TAC `affine hull s:real^N->bool` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_TRANS]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONNECTED_IMP_PERFECT_AFF_DIM THEN
      ASM_SIMP_TAC[CONVEX_CONNECTED; AFFINE_AFFINE_HULL; AFFINE_IMP_CONVEX;
                   AFF_DIM_AFFINE_HULL] THEN
      CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; SUBSET];
      REWRITE_TAC[HAS_SIZE; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `p:real^N->bool` THEN STRIP_TAC THEN MP_TAC
       (ISPECL [`k:real^N->bool`; `p:real^N->bool`] CARD_EQ_BIJECTION) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `y:real^N->real^N` THEN STRIP_TAC THEN
      MP_TAC(ISPECL
       [`s:real^N->bool`; `t:real^N->bool`; `\x:real^N. x`;
        `y:real^N->real^N`; `k:real^N->bool`]
       HOMEOMORPHISM_MOVING_POINTS_EXISTS_GEN) THEN
      ASM_REWRITE_TAC[pairwise] THEN
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[]];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INT_NOT_LE])] THEN
  SIMP_TAC[AFF_DIM_GE; INT_ARITH
   `--(&1):int <= x ==> (x < &2 <=> x = --(&1) \/ x = &0 \/ x = &1)`] THEN
  REWRITE_TAC[AFF_DIM_EQ_MINUS1; AFF_DIM_EQ_0] THEN
  SUBGOAL_THEN
   `(u:real^N->bool) SUBSET s /\ s SUBSET affine hull s`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[open_in]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [REPEAT(EXISTS_TAC `I:real^N->real^N`) THEN
    REWRITE_TAC[HOMEOMORPHISM_I; I_THM; EMPTY_GSPEC; BOUNDED_EMPTY] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`affine hull s:real^N->bool`; `(:real^1)`]
   HOMEOMORPHIC_AFFINE_SETS) THEN
  ASM_REWRITE_TAC[AFF_DIM_UNIV; AFFINE_AFFINE_HULL; AFFINE_UNIV] THEN
  ASM_REWRITE_TAC[DIMINDEX_1; AFF_DIM_AFFINE_HULL] THEN
  REWRITE_TAC[homeomorphic; homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:real^N->real^1`; `j:real^1->real^N`] THEN
  STRIP_TAC THEN MP_TAC(ISPECL
   [`IMAGE (h:real^N->real^1) u`; `IMAGE (h:real^N->real^1) s`;
    `IMAGE (h:real^N->real^1) t`; `IMAGE (h:real^N->real^1) k`]
    HOMEOMORPHISM_GROUPING_POINTS_EXISTS) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_SUBSET; IMAGE_EQ_EMPTY] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL
     [`h:real^N->real^1`; `j:real^1->real^N`;
      `affine hull s:real^N->bool`; `(:real^1)`]
     HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_SIMP_TAC[homeomorphism; SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
    REPEAT STRIP_TAC THENL [ASM_MESON_TAC[OPEN_IN_TRANS]; ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; homeomorphism]] THEN
  MAP_EVERY X_GEN_TAC [`f:real^1->real^1`; `g:real^1->real^1`] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`\x. if x IN affine hull s
         then ((j:real^1->real^N) o (f:real^1->real^1) o (h:real^N->real^1)) x
         else x`;
    `\x. if x IN affine hull s
         then ((j:real^1->real^N) o (g:real^1->real^1) o (h:real^N->real^1)) x
         else x`] THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM_SIMP_TAC[SET_RULE
     `t SUBSET s ==> IMAGE (\x. if x IN s then f x else x) t = IMAGE f t`] THEN
    REPLICATE_TAC 3 (ONCE_REWRITE_TAC[GSYM o_DEF]) THEN
    ASM_REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC
     `(j:real^1->real^N) o (f:real^1->real^1) o (h:real^N->real^1)` THEN
    REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM_SIMP_TAC[SET_RULE
     `t SUBSET s ==> IMAGE (\x. if x IN s then f x else x) t = IMAGE f t`] THEN
    REPLICATE_TAC 3 (ONCE_REWRITE_TAC[GSYM o_DEF]) THEN
    ASM_REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC
     `(j:real^1->real^N) o (g:real^1->real^1) o (h:real^N->real^1)` THEN
    REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    ASM SET_TAC[];
    ALL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MESON[] `(if P then f x else x) = x <=> ~P \/ f x = x`] THEN
  REWRITE_TAC[DE_MORGAN_THM; GSYM LEFT_OR_DISTRIB] THEN
  (SUBGOAL_THEN
   `{x | x IN affine hull s /\ (~(j (f (h x)) = x) \/ ~(j (g (h x)) = x))} =
    IMAGE (j:real^1->real^N) {x | ~(f x = x /\ g x = x)}`
   SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC])
  THENL
   [TRANS_TAC SUBSET_TRANS
     `IMAGE (j:real^1->real^N) (IMAGE (h:real^N->real^1) s)` THEN
    ASM SET_TAC[];
    MATCH_MP_TAC(MESON[CLOSURE_SUBSET; BOUNDED_SUBSET; IMAGE_SUBSET]
     `bounded (IMAGE f (closure s)) ==> bounded (IMAGE f s)`) THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[COMPACT_CLOSURE] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]]);;

(* ------------------------------------------------------------------------- *)
(* The "inside" and "outside" of a set, i.e. the points respectively in a    *)
(* bounded or unbounded connected component of the set's complement.         *)
(* ------------------------------------------------------------------------- *)

let inside = new_definition
 `inside s = {x | ~(x IN s) /\
                  bounded(connected_component ((:real^N) DIFF s) x)}`;;

let outside = new_definition
 `outside s = {x | ~(x IN s) /\
                   ~bounded(connected_component ((:real^N) DIFF s) x)}`;;

let INSIDE_TRANSLATION = prove
 (`!a s. inside(IMAGE (\x. a + x) s) = IMAGE (\x. a + x) (inside s)`,
  REWRITE_TAC[inside] THEN GEOM_TRANSLATE_TAC[]);;

let OUTSIDE_TRANSLATION = prove
 (`!a s. outside(IMAGE (\x. a + x) s) = IMAGE (\x. a + x) (outside s)`,
  REWRITE_TAC[outside] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [INSIDE_TRANSLATION; OUTSIDE_TRANSLATION];;

let INSIDE_LINEAR_IMAGE = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
         ==> inside(IMAGE f s) = IMAGE f (inside s)`,
  REWRITE_TAC[inside] THEN GEOM_TRANSFORM_TAC[]);;

let OUTSIDE_LINEAR_IMAGE = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
         ==> outside(IMAGE f s) = IMAGE f (outside s)`,
  REWRITE_TAC[outside] THEN GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [INSIDE_LINEAR_IMAGE; OUTSIDE_LINEAR_IMAGE];;

let OUTSIDE = prove
 (`!s. outside s = {x | ~bounded(connected_component((:real^N) DIFF s) x)}`,
  GEN_TAC THEN REWRITE_TAC[outside; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `(x:real^N) IN s` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[BOUNDED_EMPTY; CONNECTED_COMPONENT_EQ_EMPTY; IN_DIFF]);;

let INSIDE_NO_OVERLAP = prove
 (`!s. inside s INTER s = {}`,
  REWRITE_TAC[inside] THEN SET_TAC[]);;

let OUTSIDE_NO_OVERLAP = prove
 (`!s. outside s INTER s = {}`,
  REWRITE_TAC[outside] THEN SET_TAC[]);;

let INSIDE_INTER_OUTSIDE = prove
 (`!s. inside s INTER outside s = {}`,
  REWRITE_TAC[inside; outside] THEN SET_TAC[]);;

let INSIDE_UNION_OUTSIDE = prove
 (`!s. inside s UNION outside s = (:real^N) DIFF s`,
  REWRITE_TAC[inside; outside] THEN SET_TAC[]);;

let INSIDE_EQ_OUTSIDE = prove
 (`!s. inside s = outside s <=> s = (:real^N)`,
  REWRITE_TAC[inside; outside] THEN SET_TAC[]);;

let INSIDE_OUTSIDE = prove
 (`!s. inside s = (:real^N) DIFF (s UNION outside s)`,
  GEN_TAC THEN MAP_EVERY (MP_TAC o ISPEC `s:real^N->bool`)
   [INSIDE_INTER_OUTSIDE; INSIDE_UNION_OUTSIDE] THEN
  SET_TAC[]);;

let OUTSIDE_INSIDE = prove
 (`!s. outside s = (:real^N) DIFF (s UNION inside s)`,
  GEN_TAC THEN MAP_EVERY (MP_TAC o ISPEC `s:real^N->bool`)
   [INSIDE_INTER_OUTSIDE; INSIDE_UNION_OUTSIDE] THEN
  SET_TAC[]);;

let UNION_WITH_INSIDE = prove
 (`!s. s UNION inside s = (:real^N) DIFF outside s`,
  REWRITE_TAC[OUTSIDE_INSIDE] THEN SET_TAC[]);;

let UNION_WITH_OUTSIDE = prove
 (`!s. s UNION outside s = (:real^N) DIFF inside s`,
  REWRITE_TAC[INSIDE_OUTSIDE] THEN SET_TAC[]);;

let OUTSIDE_MONO = prove
 (`!s t. s SUBSET t ==> outside t SUBSET outside s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OUTSIDE; SUBSET; IN_ELIM_THM] THEN
  DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[CONTRAPOS_THM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] BOUNDED_SUBSET) THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_MONO THEN ASM SET_TAC[]);;

let INSIDE_MONO = prove
 (`!s t. s SUBSET t ==> inside s DIFF t SUBSET inside t`,
  REPEAT STRIP_TAC THEN SIMP_TAC[SUBSET; IN_DIFF; inside; IN_ELIM_THM] THEN
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
    ASSUME_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] BOUNDED_SUBSET) THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_MONO THEN ASM SET_TAC[]);;

let COBOUNDED_OUTSIDE = prove
 (`!s:real^N->bool. bounded s ==> bounded((:real^N) DIFF outside s)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[outside] THEN
  REWRITE_TAC[SET_RULE `UNIV DIFF {x | ~(x IN s) /\ ~P x} =
                        s UNION {x | P x}`] THEN
  ASM_REWRITE_TAC[BOUNDED_UNION] THEN
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^N` o MATCH_MP BOUNDED_SUBSET_BALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `ball(vec 0:real^N,B)` THEN
  REWRITE_TAC[BOUNDED_BALL; SUBSET; IN_ELIM_THM; IN_BALL_0] THEN
  X_GEN_TAC `x:real^N` THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[REAL_NOT_LT] THEN
  ASM_CASES_TAC `x:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(B + C) / norm(x) % x:real^N`) THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; NOT_IMP] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[IN] THEN REWRITE_TAC[connected_component] THEN
  EXISTS_TAC `segment[x:real^N,(B + C) / norm(x) % x]` THEN
  REWRITE_TAC[ENDS_IN_SEGMENT; CONNECTED_SEGMENT] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `(:real^N) DIFF ball(vec 0,B)` THEN
  ASM_REWRITE_TAC[SET_RULE
   `UNIV DIFF s SUBSET UNIV DIFF t <=> t SUBSET s`] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_BALL_0] THEN
  REWRITE_TAC[segment; FORALL_IN_GSPEC] THEN X_GEN_TAC `u:real` THEN
  STRIP_TAC THEN REWRITE_TAC[REAL_NOT_LT] THEN
  REWRITE_TAC[GSYM VECTOR_ADD_RDISTRIB; NORM_MUL; VECTOR_MUL_ASSOC] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_ABS_NORM] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL] THEN MATCH_MP_TAC(REAL_ARITH
   `&0 < B /\ B <= x ==> B <= abs x`) THEN
  ASM_SIMP_TAC[REAL_ADD_RDISTRIB; REAL_DIV_RMUL; NORM_EQ_0; GSYM
               REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 - u) * B + u * (B + C)` THEN
  ASM_SIMP_TAC[REAL_LE_RADD; REAL_LE_LMUL; REAL_SUB_LE] THEN
  SIMP_TAC[REAL_ARITH `B <= (&1 - u) * B + u * (B + C) <=> &0 <= u * C`] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

let UNBOUNDED_OUTSIDE = prove
 (`!s:real^N->bool. bounded s ==> ~bounded(outside s)`,
  MESON_TAC[COBOUNDED_IMP_UNBOUNDED; COBOUNDED_OUTSIDE]);;

let BOUNDED_INSIDE = prove
 (`!s:real^N->bool. bounded s ==> bounded(inside s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `(:real^N) DIFF outside s` THEN
  ASM_SIMP_TAC[COBOUNDED_OUTSIDE] THEN
  MP_TAC(ISPEC `s:real^N->bool` INSIDE_INTER_OUTSIDE) THEN SET_TAC[]);;

let CONNECTED_OUTSIDE = prove
 (`!s:real^N->bool. 2 <= dimindex(:N) /\ bounded s ==> connected(outside s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  REWRITE_TAC[outside; IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_OF_SUBSET THEN
  EXISTS_TAC `connected_component ((:real^N) DIFF s) x` THEN
  REWRITE_TAC[SUBSET; IN_UNIV; IN_DIFF; IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
      CONNECTED_COMPONENT_SUBSET)) THEN
    REWRITE_TAC[IN_DIFF] THEN ASM_MESON_TAC[CONNECTED_COMPONENT_EQ];
    REWRITE_TAC[CONNECTED_COMPONENT_IDEMP] THEN
    SUBGOAL_THEN `connected_component ((:real^N) DIFF s) x =
                  connected_component ((:real^N) DIFF s) y`
    SUBST1_TAC THENL
     [MATCH_MP_TAC COBOUNDED_UNIQUE_UNBOUNDED_COMPONENT THEN
      ASM_REWRITE_TAC[SET_RULE `UNIV DIFF (UNIV DIFF s) = s`];
      ASM_REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ; IN_DIFF; IN_UNIV]]]);;

let OUTSIDE_CONNECTED_COMPONENT_LT = prove
 (`!s. outside s =
            {x | !B. ?y. B < norm(y) /\
                         connected_component((:real^N) DIFF s) x y}`,
  REWRITE_TAC[OUTSIDE; bounded; EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[IN] THEN ASM_MESON_TAC[REAL_NOT_LE]);;

let OUTSIDE_CONNECTED_COMPONENT_LE = prove
 (`!s. outside s =
            {x | !B. ?y. B <= norm(y) /\
                         connected_component((:real^N) DIFF s) x y}`,
  GEN_TAC THEN REWRITE_TAC[OUTSIDE_CONNECTED_COMPONENT_LT] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MESON_TAC[REAL_LT_IMP_LE; REAL_ARITH `B + &1 <= x ==> B < x`]);;

let NOT_OUTSIDE_CONNECTED_COMPONENT_LT = prove
 (`!s. 2 <= dimindex(:N) /\ bounded s
       ==> (:real^N) DIFF (outside s) =
           {x | !B. ?y. B < norm(y) /\
                        ~(connected_component((:real^N) DIFF s) x y)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OUTSIDE] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[bounded] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN X_GEN_TAC `B:real` THEN
    EXISTS_TAC `(abs B + abs C + &1) % basis 1:real^N` THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC] THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    REAL_ARITH_TAC;
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN STRIP_TAC THEN
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `B:real`) THEN DISCH_THEN
     (X_CHOOSE_THEN `z:real^N` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_OF_SUBSET THEN
    EXISTS_TAC `(:real^N) DIFF cball(vec 0,B)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_UNIV; CONTRAPOS_THM] THEN
    REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `(:real^N) DIFF cball(vec 0,B)` THEN
    ASM_SIMP_TAC[SUBSET_REFL; IN_DIFF; IN_UNIV; IN_CBALL_0; REAL_NOT_LE] THEN
    MATCH_MP_TAC CONNECTED_COMPLEMENT_BOUNDED_CONVEX THEN
    ASM_SIMP_TAC[BOUNDED_CBALL; CONVEX_CBALL]]);;

let NOT_OUTSIDE_CONNECTED_COMPONENT_LE = prove
 (`!s. 2 <= dimindex(:N) /\ bounded s
       ==> (:real^N) DIFF (outside s) =
           {x | !B. ?y. B <= norm(y) /\
                        ~(connected_component((:real^N) DIFF s) x y)}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NOT_OUTSIDE_CONNECTED_COMPONENT_LT] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MESON_TAC[REAL_LT_IMP_LE; REAL_ARITH `B + &1 <= x ==> B < x`]);;

let INSIDE_CONNECTED_COMPONENT_LT = prove
 (`!s. 2 <= dimindex(:N) /\ bounded s
       ==> inside s =
            {x:real^N | ~(x IN s) /\
                        !B. ?y. B < norm(y) /\
                                ~(connected_component((:real^N) DIFF s) x y)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INSIDE_OUTSIDE] THEN
  REWRITE_TAC[SET_RULE `UNIV DIFF (s UNION t) = (UNIV DIFF t) DIFF s`] THEN
  ASM_SIMP_TAC[NOT_OUTSIDE_CONNECTED_COMPONENT_LT] THEN SET_TAC[]);;

let INSIDE_CONNECTED_COMPONENT_LE = prove
 (`!s. 2 <= dimindex(:N) /\ bounded s
       ==> inside s =
            {x:real^N | ~(x IN s) /\
                        !B. ?y. B <= norm(y) /\
                                ~(connected_component((:real^N) DIFF s) x y)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INSIDE_OUTSIDE] THEN
  REWRITE_TAC[SET_RULE `UNIV DIFF (s UNION t) = (UNIV DIFF t) DIFF s`] THEN
  ASM_SIMP_TAC[NOT_OUTSIDE_CONNECTED_COMPONENT_LE] THEN SET_TAC[]);;

let OUTSIDE_UNION_OUTSIDE_UNION = prove
 (`!c c1 c2:real^N->bool.
        c INTER outside(c1 UNION c2) = {}
        ==> outside(c1 UNION c2) SUBSET outside(c1 UNION c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[OUTSIDE_CONNECTED_COMPONENT_LT; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `B:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[connected_component] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `t SUBSET outside(c1 UNION c2:real^N->bool)`
  MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `connected_component((:real^N) DIFF (c1 UNION c2)) x` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONNECTED_COMPONENT_MAXIMAL]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN outside(c1 UNION c2)` THEN
  REWRITE_TAC[OUTSIDE; IN_ELIM_THM; SUBSET] THEN
  MESON_TAC[CONNECTED_COMPONENT_EQ]);;

let INSIDE_SUBSET = prove
 (`!s t u. connected u /\ ~bounded u /\ t UNION u = (:real^N) DIFF s
           ==> inside s SUBSET t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; inside; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `~bounded(u:real^N->bool)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `connected_component((:real^N) DIFF s) x` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let INSIDE_UNIQUE = prove
 (`!s t u. connected t /\ bounded t /\
           connected u /\ ~(bounded u) /\
           ~connected((:real^N) DIFF s) /\
           t UNION u = (:real^N) DIFF s
           ==> inside s = t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ASM_MESON_TAC[INSIDE_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; inside; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `t:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE
   `!s u. c INTER s = {} /\ c INTER u = {} /\ t UNION u = UNIV DIFF s
          ==> c SUBSET t`) THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `u:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SET_RULE `c INTER s = {} <=> c SUBSET (UNIV DIFF s)`] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `(!x. x IN s /\ x IN t ==> F) ==> s INTER t = {}`) THEN
  X_GEN_TAC `y:real^N` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [IN] THEN STRIP_TAC THEN
  UNDISCH_TAC `~connected((:real^N) DIFF s)` THEN
  REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
  SUBGOAL_THEN
   `(!w. w IN t ==> connected_component ((:real^N) DIFF s) x w) /\
    (!w. w IN u ==> connected_component ((:real^N) DIFF s) y w)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[connected_component] THENL
     [EXISTS_TAC `t:real^N->bool`; EXISTS_TAC `u:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNION] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONNECTED_COMPONENT_TRANS; CONNECTED_COMPONENT_SYM]]);;

let INSIDE_OUTSIDE_UNIQUE = prove
 (`!s t u. connected t /\ bounded t /\
           connected u /\ ~(bounded u) /\
           ~connected((:real^N) DIFF s) /\
           t UNION u = (:real^N) DIFF s
           ==> inside s = t /\ outside s = u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[OUTSIDE_INSIDE] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[INSIDE_UNIQUE];
    MP_TAC(ISPEC `(:real^N) DIFF s` INSIDE_NO_OVERLAP) THEN
    SUBGOAL_THEN `t INTER u:real^N->bool = {}` MP_TAC THENL
     [ALL_TAC; ASM SET_TAC[]] THEN
    UNDISCH_TAC `~connected ((:real^N) DIFF s)` THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_UNION THEN
    ASM_REWRITE_TAC[]]);;

let INTERIOR_INSIDE_FRONTIER = prove
 (`!s:real^N->bool. bounded s ==> interior s SUBSET inside(frontier s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inside; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[frontier; IN_DIFF]; DISCH_TAC] THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(connected_component((:real^N) DIFF frontier s) x INTER
                  frontier s = {})`
  MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_INTER_FRONTIER THEN
    REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT; GSYM MEMBER_NOT_EMPTY] THEN
    CONJ_TAC THENL [REWRITE_TAC[IN_INTER]; ASM SET_TAC[]] THEN
    EXISTS_TAC `x:real^N` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN; CONNECTED_COMPONENT_REFL_EQ] THEN
      GEN_REWRITE_TAC I [GSYM IN] THEN ASM SET_TAC[];
      ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]];
    REWRITE_TAC[SET_RULE `s INTER t = {} <=> s SUBSET (UNIV DIFF t)`] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]]);;

let INSIDE_EMPTY = prove
 (`inside {} = {}`,
  REWRITE_TAC[inside; NOT_IN_EMPTY; DIFF_EMPTY; CONNECTED_COMPONENT_UNIV] THEN
  REWRITE_TAC[NOT_BOUNDED_UNIV; EMPTY_GSPEC]);;

let OUTSIDE_EMPTY = prove
 (`outside {} = (:real^N)`,
  REWRITE_TAC[OUTSIDE_INSIDE; INSIDE_EMPTY] THEN SET_TAC[]);;

let INSIDE_SAME_COMPONENT = prove
 (`!s x y. connected_component((:real^N) DIFF s) x y /\ x IN inside s
           ==> y IN inside s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o GEN_REWRITE_RULE I [GSYM IN])
        MP_TAC) THEN
  REWRITE_TAC[inside; IN_ELIM_THM] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP CONNECTED_COMPONENT_EQ) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENT_IN) THEN
  SIMP_TAC[IN_DIFF]);;

let OUTSIDE_SAME_COMPONENT = prove
 (`!s x y. connected_component((:real^N) DIFF s) x y /\ x IN outside s
           ==> y IN outside s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o GEN_REWRITE_RULE I [GSYM IN])
        MP_TAC) THEN
  REWRITE_TAC[outside; IN_ELIM_THM] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP CONNECTED_COMPONENT_EQ) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENT_IN) THEN
  SIMP_TAC[IN_DIFF]);;

let OUTSIDE_CONVEX = prove
 (`!s. convex s ==> outside s = (:real^N) DIFF s`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ;
              REWRITE_RULE[SET_RULE `t INTER s = {} <=> t SUBSET UNIV DIFF s`]
                          OUTSIDE_NO_OVERLAP] THEN
  REWRITE_TAC[SUBSET; IN_UNIV; IN_DIFF] THEN
  MATCH_MP_TAC SET_PROVE_CASES THEN REWRITE_TAC[OUTSIDE_EMPTY; IN_UNIV] THEN
  X_GEN_TAC `a:real^N` THEN GEOM_ORIGIN_TAC `a:real^N` THEN
  X_GEN_TAC `t:real^N->bool` THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(SET_RULE `(vec 0:real^N) IN (vec 0 INSERT t)`) THEN
  SPEC_TAC(`(vec 0:real^N) INSERT t`,`s:real^N->bool`) THEN
  GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[outside; IN_ELIM_THM] THEN
  SUBGOAL_THEN `~(x:real^N = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; NOT_EXISTS_THM] THEN X_GEN_TAC `B:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `(max (&2) ((B + &1) / norm(x))) % x:real^N`) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN] THEN REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `segment[x:real^N,(max (&2) ((B + &1) / norm(x))) % x]` THEN
    REWRITE_TAC[ENDS_IN_SEGMENT; CONNECTED_SEGMENT] THEN
    REWRITE_TAC[segment; SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `u:real` THEN
    ASM_CASES_TAC `u = &0` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; REAL_SUB_RZERO;
                    VECTOR_ADD_RID; IN_DIFF; IN_UNIV] THEN
    DISCH_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `a % x + b % c % x:real^N = (a + b * c) % x`] THEN
    ABBREV_TAC `c = &1 - u + u * max (&2) ((B + &1) / norm(x:real^N))` THEN
    DISCH_TAC THEN SUBGOAL_THEN `&1 < c` ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN
      REWRITE_TAC[REAL_ARITH `&1 < &1 - u + u * x <=> &0 < u * (x - &1)`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `~((x:real^N) IN s)` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `x:real^N = (&1 - inv c) % vec 0 + inv c % c % x`
      SUBST1_TAC THENL
       [REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_ARITH `&1 < x ==> ~(x = &0)`] THEN
        REWRITE_TAC[VECTOR_MUL_LID];
        MATCH_MP_TAC IN_CONVEX_SET THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_INV_LE_1; REAL_LT_IMP_LE] THEN
        ASM_REAL_ARITH_TAC]];
    ASM_SIMP_TAC[NORM_MUL; REAL_NOT_LE; GSYM REAL_LT_LDIV_EQ; NORM_POS_LT] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < b /\ b < c ==> b < abs(max (&2) c)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; REAL_LT_DIV2_EQ] THEN
    REAL_ARITH_TAC]);;

let INSIDE_CONVEX = prove
 (`!s. convex s ==> inside s = {}`,
  SIMP_TAC[INSIDE_OUTSIDE; OUTSIDE_CONVEX] THEN SET_TAC[]);;

let OUTSIDE_SUBSET_CONVEX = prove
 (`!s t. convex t /\ s SUBSET t ==> (:real^N) DIFF t SUBSET outside s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `outside(t:real^N->bool)` THEN
  ASM_SIMP_TAC[OUTSIDE_MONO] THEN
  ASM_SIMP_TAC[OUTSIDE_CONVEX; SUBSET_REFL]);;

let OUTSIDE_FRONTIER_MISSES_CLOSURE = prove
 (`!s. bounded s ==> outside(frontier s) SUBSET (:real^N) DIFF closure s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OUTSIDE_INSIDE] THEN
  SIMP_TAC[SET_RULE `(UNIV DIFF s) SUBSET (UNIV DIFF t) <=> t SUBSET s`] THEN
  REWRITE_TAC[frontier] THEN
  MATCH_MP_TAC(SET_RULE
   `i SUBSET ins ==> c SUBSET (c DIFF i) UNION ins`) THEN
  ASM_SIMP_TAC[GSYM frontier; INTERIOR_INSIDE_FRONTIER]);;

let OUTSIDE_FRONTIER_EQ_COMPLEMENT_CLOSURE = prove
 (`!s. bounded s /\ convex s
       ==> outside(frontier s) = (:real^N) DIFF closure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[OUTSIDE_FRONTIER_MISSES_CLOSURE] THEN
  MATCH_MP_TAC OUTSIDE_SUBSET_CONVEX THEN
  ASM_SIMP_TAC[CONVEX_CLOSURE; frontier] THEN SET_TAC[]);;

let INSIDE_FRONTIER_EQ_INTERIOR = prove
 (`!s:real^N->bool.
        bounded s /\ convex s ==> inside(frontier s) = interior s`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[INSIDE_OUTSIDE; OUTSIDE_FRONTIER_EQ_COMPLEMENT_CLOSURE] THEN
  REWRITE_TAC[frontier] THEN
  MAP_EVERY (MP_TAC o ISPEC `s:real^N->bool`)
   [CLOSURE_SUBSET; INTERIOR_SUBSET] THEN
  ASM SET_TAC[]);;

let OPEN_INSIDE = prove
 (`!s:real^N->bool. closed s ==> open(inside s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(connected_component ((:real^N) DIFF s) x)` MP_TAC THENL
   [MATCH_MP_TAC OPEN_CONNECTED_COMPONENT THEN ASM_REWRITE_TAC[GSYM closed];
    REWRITE_TAC[open_def] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN; CONNECTED_COMPONENT_REFL_EQ] THEN
      GEN_REWRITE_TAC I [GSYM IN] THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
      MP_TAC(ISPEC `s:real^N->bool` INSIDE_NO_OVERLAP) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC INSIDE_SAME_COMPONENT THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM]]]);;

let OPEN_OUTSIDE = prove
 (`!s:real^N->bool. closed s ==> open(outside s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(connected_component ((:real^N) DIFF s) x)` MP_TAC THENL
   [MATCH_MP_TAC OPEN_CONNECTED_COMPONENT THEN ASM_REWRITE_TAC[GSYM closed];
    REWRITE_TAC[open_def] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN; CONNECTED_COMPONENT_REFL_EQ] THEN
      GEN_REWRITE_TAC I [GSYM IN] THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
      MP_TAC(ISPEC `s:real^N->bool` OUTSIDE_NO_OVERLAP) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC OUTSIDE_SAME_COMPONENT THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM]]]);;

let CLOSURE_INSIDE_SUBSET = prove
 (`!s:real^N->bool. closed s ==> closure(inside s) SUBSET s UNION inside s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
  ASM_SIMP_TAC[closed; GSYM OUTSIDE_INSIDE; OPEN_OUTSIDE] THEN SET_TAC[]);;

let FRONTIER_INSIDE_SUBSET = prove
 (`!s:real^N->bool. closed s ==> frontier(inside s) SUBSET s`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[frontier; OPEN_INSIDE; INTERIOR_OPEN] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CLOSURE_INSIDE_SUBSET) THEN SET_TAC[]);;

let CLOSURE_OUTSIDE_SUBSET = prove
 (`!s:real^N->bool. closed s ==> closure(outside s) SUBSET s UNION outside s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
  ASM_SIMP_TAC[closed; GSYM INSIDE_OUTSIDE; OPEN_INSIDE] THEN SET_TAC[]);;

let FRONTIER_OUTSIDE_SUBSET = prove
 (`!s:real^N->bool. closed s ==> frontier(outside s) SUBSET s`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[frontier; OPEN_OUTSIDE; INTERIOR_OPEN] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CLOSURE_OUTSIDE_SUBSET) THEN SET_TAC[]);;

let INSIDE_COMPLEMENT_UNBOUNDED_CONNECTED_EMPTY = prove
 (`!s. connected((:real^N) DIFF s) /\ ~bounded((:real^N) DIFF s)
       ==> inside s = {}`,
  REWRITE_TAC[inside; CONNECTED_CONNECTED_COMPONENT_SET] THEN
  REWRITE_TAC[SET_RULE `s = {} <=> !x. x IN s ==> F`] THEN
  SIMP_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; TAUT `~(a /\ b) <=> a ==> ~b`]);;

let INSIDE_BOUNDED_COMPLEMENT_CONNECTED_EMPTY = prove
 (`!s. connected((:real^N) DIFF s) /\ bounded s
       ==> inside s = {}`,
  MESON_TAC[INSIDE_COMPLEMENT_UNBOUNDED_CONNECTED_EMPTY;
            COBOUNDED_IMP_UNBOUNDED]);;

let INSIDE_INSIDE = prove
 (`!s t:real^N->bool.
        s SUBSET inside t ==> inside s DIFF t SUBSET inside t`,
  REPEAT STRIP_TAC THEN SIMP_TAC[SUBSET; inside; IN_DIFF; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s INTER connected_component ((:real^N) DIFF t) x = {}` THENL
   [MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `connected_component ((:real^N) DIFF s) x` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT; IN] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN ASM SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `~(s INTER t = {}) ==> ?x. x IN s /\ x IN t`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N`
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM o MATCH_MP CONNECTED_COMPONENT_EQ) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_SIMP_TAC[inside; IN_ELIM_THM]]);;

let INSIDE_INSIDE_SUBSET = prove
 (`!s:real^N->bool. inside(inside s) SUBSET s`,
  GEN_TAC THEN MP_TAC
   (ISPECL [`inside s:real^N->bool`; `s:real^N->bool`] INSIDE_INSIDE) THEN
  REWRITE_TAC[SUBSET_REFL] THEN
  MP_TAC(ISPEC `inside s:real^N->bool` INSIDE_NO_OVERLAP) THEN SET_TAC[]);;

let INSIDE_OUTSIDE_INTERSECT_CONNECTED = prove
 (`!s t:real^N->bool.
        connected t /\ ~(inside s INTER t = {}) /\ ~(outside s INTER t = {})
        ==> ~(s INTER t = {})`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  REWRITE_TAC[inside; outside; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `connected_component ((:real^N) DIFF s) y =
    connected_component ((:real^N) DIFF s) x`
   (fun th -> ASM_MESON_TAC[th]) THEN
  ASM_REWRITE_TAC[CONNECTED_COMPONENT_EQ_EQ; IN_DIFF; IN_UNIV] THEN
  REWRITE_TAC[connected_component] THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM SET_TAC[]);;

let OUTSIDE_BOUNDED_NONEMPTY = prove
 (`!s:real^N->bool. bounded s ==> ~(outside s = {})`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^N` o MATCH_MP BOUNDED_SUBSET_BALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] OUTSIDE_SUBSET_CONVEX)) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  SIMP_TAC[CONVEX_BALL; SUBSET_EMPTY] THEN
  REWRITE_TAC[SET_RULE `s DIFF t = {} <=> s SUBSET t`] THEN
  MESON_TAC[BOUNDED_BALL; BOUNDED_SUBSET; NOT_BOUNDED_UNIV]);;

let OUTSIDE_COMPACT_IN_OPEN = prove
 (`!s t:real^N->bool.
        compact s /\ open t /\ s SUBSET t /\ ~(t = {})
        ==> ~(outside s INTER t = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OUTSIDE_BOUNDED_NONEMPTY o
        MATCH_MP COMPACT_IMP_BOUNDED) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM; IN_INTER] THEN
  X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(a:real^N) IN t` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`linepath(a:real^N,b)`; `(:real^N) DIFF t`]
        EXISTS_PATH_SUBPATH_TO_FRONTIER) THEN
  REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:real^1->real^N` THEN REWRITE_TAC[FRONTIER_COMPLEMENT] THEN
  REWRITE_TAC[PATH_IMAGE_LINEPATH; INTERIOR_DIFF; INTERIOR_UNIV] THEN
  ABBREV_TAC `c:real^N = pathfinish g` THEN STRIP_TAC THEN
  SUBGOAL_THEN `frontier t SUBSET (:real^N) DIFF s` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM FRONTIER_COMPLEMENT] THEN
    REWRITE_TAC[frontier] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; GSYM OPEN_CLOSED] THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV]] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MP_TAC(ISPEC `(:real^N) DIFF s` OPEN_CONTAINS_CBALL) THEN
  ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:real^N`; `t:real^N->bool`]
        CLOSURE_APPROACHABLE) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[frontier; IN_DIFF]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OUTSIDE_SAME_COMPONENT THEN
  EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[connected_component] THEN
  EXISTS_TAC `path_image(g) UNION segment[c:real^N,d]` THEN
  REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN
    ASM_SIMP_TAC[CONNECTED_SEGMENT; GSYM MEMBER_NOT_EMPTY;
                 CONNECTED_PATH_IMAGE] THEN
    EXISTS_TAC `c:real^N` THEN REWRITE_TAC[ENDS_IN_SEGMENT; IN_INTER] THEN
    ASM_MESON_TAC[PATHFINISH_IN_PATH_IMAGE; SUBSET];
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE]] THEN
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `~(c IN s)
        ==> (t DELETE c) SUBSET (UNIV DIFF s)
            ==> t SUBSET (UNIV DIFF s)`)) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        SUBSET_TRANS)) THEN
      SIMP_TAC[SET_RULE `UNIV DIFF s SUBSET UNIV DIFF t <=> t SUBSET s`] THEN
      ASM_MESON_TAC[SUBSET_TRANS; CLOSURE_SUBSET];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        SUBSET_TRANS)) THEN
     REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      ASM_SIMP_TAC[CONVEX_CBALL; INSERT_SUBSET; REAL_LT_IMP_LE;
                   EMPTY_SUBSET; CENTRE_IN_CBALL] THEN
      REWRITE_TAC[IN_CBALL] THEN
      ASM_MESON_TAC[DIST_SYM; REAL_LT_IMP_LE]]]);;

let INSIDE_INSIDE_COMPACT_CONNECTED = prove
 (`!s t:real^N->bool.
        closed s /\ compact t /\ s SUBSET inside t /\ connected t
        ==> inside s SUBSET inside t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `inside t:real^N->bool = {}` THEN
  ASM_SIMP_TAC[INSIDE_EMPTY; SUBSET_EMPTY; EMPTY_SUBSET] THEN
  SUBGOAL_THEN `1 <= dimindex(:N)` MP_TAC THENL
   [REWRITE_TAC[DIMINDEX_GE_1];
    REWRITE_TAC[ARITH_RULE `1 <= n <=> n = 1 \/ 2 <= n`]] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[GSYM CONNECTED_CONVEX_1_GEN] THENL
   [ASM_MESON_TAC[INSIDE_CONVEX]; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP INSIDE_INSIDE) THEN
  MATCH_MP_TAC(SET_RULE
   `s INTER t = {} ==> s DIFF t SUBSET u ==> s SUBSET u`) THEN
  SUBGOAL_THEN `compact(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_SUBSET; BOUNDED_INSIDE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`]
        INSIDE_OUTSIDE_INTERSECT_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
   `r /\ q ==> (~p /\ q ==> ~r) ==> p`) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `t:real^N->bool` INSIDE_NO_OVERLAP) THEN ASM SET_TAC[];
    ONCE_REWRITE_TAC[INTER_COMM]] THEN
  MATCH_MP_TAC INSIDE_OUTSIDE_INTERSECT_CONNECTED THEN
  ASM_SIMP_TAC[CONNECTED_OUTSIDE; COMPACT_IMP_BOUNDED] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC OUTSIDE_COMPACT_IN_OPEN THEN
    ASM_SIMP_TAC[OPEN_INSIDE; COMPACT_IMP_CLOSED];
    MP_TAC(ISPECL [`s UNION t:real^N->bool`; `vec 0:real^N`]
        BOUNDED_SUBSET_BALL) THEN
    ASM_SIMP_TAC[BOUNDED_UNION; COMPACT_IMP_BOUNDED] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(SET_RULE
     `!u. ~(u = UNIV) /\ UNIV DIFF u SUBSET s /\ UNIV DIFF u SUBSET t
          ==> ~(s INTER t = {})`) THEN
    EXISTS_TAC `ball(vec 0:real^N,r)` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[NOT_BOUNDED_UNIV; BOUNDED_BALL]; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC OUTSIDE_SUBSET_CONVEX THEN
    REWRITE_TAC[CONVEX_BALL] THEN ASM SET_TAC[]]);;

let CONNECTED_WITH_INSIDE = prove
 (`!s:real^N->bool. closed s /\ connected s ==> connected(s UNION inside s)`,
  GEN_TAC THEN ASM_CASES_TAC `s UNION inside s = (:real^N)` THEN
  ASM_REWRITE_TAC[CONNECTED_UNIV] THEN
  REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT] THEN
  REWRITE_TAC[CONNECTED_COMPONENT_SET; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN (s UNION inside s)
        ==> ?y:real^N t. y IN s /\ connected t /\ x IN t /\ y IN t /\
                         t SUBSET (s UNION inside s)`
  MP_TAC THENL
   [X_GEN_TAC `a:real^N` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`a:real^N`; `{a:real^N}`] THEN
      ASM_REWRITE_TAC[IN_SING; CONNECTED_SING] THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
       `~(s UNION t = UNIV) ==> ?b. ~(b IN s) /\ ~(b IN t)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`linepath(a:real^N,b)`; `inside s:real^N->bool`]
        EXISTS_PATH_SUBPATH_TO_FRONTIER) THEN
      ASM_SIMP_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                   IN_UNION; OPEN_INSIDE; INTERIOR_OPEN] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `pathfinish g :real^N` THEN
      EXISTS_TAC `path_image g :real^N->bool` THEN
      ASM_SIMP_TAC[PATHFINISH_IN_PATH_IMAGE; CONNECTED_PATH_IMAGE] THEN
      MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
      REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[FRONTIER_INSIDE_SUBSET; SUBSET];
        ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE];
        ASM SET_TAC[]]];
    DISCH_THEN(fun th ->
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
      MP_TAC(SPEC `y:real^N` th) THEN MP_TAC(SPEC `x:real^N` th)) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `t:real^N->bool`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`b:real^N`; `u:real^N->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t UNION v UNION u:real^N->bool` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REPEAT(MATCH_MP_TAC CONNECTED_UNION THEN
           ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC) THEN
    ASM SET_TAC[]]);;

let CONNECTED_WITH_OUTSIDE = prove
 (`!s:real^N->bool. closed s /\ connected s ==> connected(s UNION outside s)`,
  GEN_TAC THEN ASM_CASES_TAC `s UNION outside s = (:real^N)` THEN
  ASM_REWRITE_TAC[CONNECTED_UNIV] THEN
  REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT] THEN
  REWRITE_TAC[CONNECTED_COMPONENT_SET; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN (s UNION outside s)
        ==> ?y:real^N t. y IN s /\ connected t /\ x IN t /\ y IN t /\
                         t SUBSET (s UNION outside s)`
  MP_TAC THENL
   [X_GEN_TAC `a:real^N` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`a:real^N`; `{a:real^N}`] THEN
      ASM_REWRITE_TAC[IN_SING; CONNECTED_SING] THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
       `~(s UNION t = UNIV) ==> ?b. ~(b IN s) /\ ~(b IN t)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`linepath(a:real^N,b)`; `outside s:real^N->bool`]
        EXISTS_PATH_SUBPATH_TO_FRONTIER) THEN
      ASM_SIMP_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                   IN_UNION; OPEN_OUTSIDE; INTERIOR_OPEN] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `pathfinish g :real^N` THEN
      EXISTS_TAC `path_image g :real^N->bool` THEN
      ASM_SIMP_TAC[PATHFINISH_IN_PATH_IMAGE; CONNECTED_PATH_IMAGE] THEN
      MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
      REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[FRONTIER_OUTSIDE_SUBSET; SUBSET];
        ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE];
        ASM SET_TAC[]]];
    DISCH_THEN(fun th ->
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
      MP_TAC(SPEC `y:real^N` th) THEN MP_TAC(SPEC `x:real^N` th)) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `t:real^N->bool`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`b:real^N`; `u:real^N->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t UNION v UNION u:real^N->bool` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REPEAT(MATCH_MP_TAC CONNECTED_UNION THEN
           ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC) THEN
    ASM SET_TAC[]]);;

let INSIDE_INSIDE_EQ_EMPTY = prove
 (`!s:real^N->bool.
        closed s /\ connected s ==> inside(inside s) = {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^N` THEN ONCE_REWRITE_TAC[inside] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC[INSIDE_OUTSIDE] THEN
  REWRITE_TAC[SET_RULE `UNIV DIFF (UNIV DIFF s) = s`] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[CONNECTED_COMPONENT_EQ_SELF; CONNECTED_WITH_OUTSIDE] THEN
  REWRITE_TAC[BOUNDED_UNION] THEN MESON_TAC[UNBOUNDED_OUTSIDE]);;

let INSIDE_IN_COMPONENTS = prove
 (`!s. (inside s) IN components((:real^N) DIFF s) <=>
       connected(inside s) /\ ~(inside s = {})`,
  X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_COMPONENTS_MAXIMAL] THEN
  ASM_CASES_TAC `inside s:real^N->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `connected(inside s:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> s INTER t = {}`] THEN
  REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
  X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC INSIDE_SAME_COMPONENT THEN
  UNDISCH_TAC `~(inside s:real^N->bool = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[connected_component] THEN
  EXISTS_TAC `d:real^N->bool` THEN ASM SET_TAC[]);;

let OUTSIDE_IN_COMPONENTS = prove
 (`!s. (outside s) IN components((:real^N) DIFF s) <=>
       connected(outside s) /\ ~(outside s = {})`,
  X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_COMPONENTS_MAXIMAL] THEN
  ASM_CASES_TAC `outside s:real^N->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `connected(outside s:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> s INTER t = {}`] THEN
  REWRITE_TAC[OUTSIDE_NO_OVERLAP] THEN
  X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC OUTSIDE_SAME_COMPONENT THEN
  UNDISCH_TAC `~(outside s:real^N->bool = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[connected_component] THEN
  EXISTS_TAC `d:real^N->bool` THEN ASM SET_TAC[]);;

let BOUNDED_UNIQUE_OUTSIDE = prove
 (`!c s. 2 <= dimindex(:N) /\ bounded s
         ==> (c IN components ((:real^N) DIFF s) /\ ~bounded c <=>
              c = outside s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC COBOUNDED_UNIQUE_UNBOUNDED_COMPONENTS THEN
    EXISTS_TAC `(:real^N) DIFF s` THEN
    ASM_REWRITE_TAC[SET_RULE `UNIV DIFF (UNIV DIFF s) = s`] THEN
    ASM_REWRITE_TAC[OUTSIDE_IN_COMPONENTS];
    ASM_REWRITE_TAC[OUTSIDE_IN_COMPONENTS]] THEN
  ASM_SIMP_TAC[UNBOUNDED_OUTSIDE; OUTSIDE_BOUNDED_NONEMPTY;
               CONNECTED_OUTSIDE]);;

(* ------------------------------------------------------------------------- *)
(* Homotopy of maps p,q : X->Y with property P of all intermediate maps.     *)
(* We often just want to require that it fixes some subset, but to take in   *)
(* the case of loop homotopy it's convenient to have a general property P.   *)
(* ------------------------------------------------------------------------- *)

let homotopic_with = new_definition
 `homotopic_with P (X,Y) p q <=>
   ?h:real^(1,M)finite_sum->real^N.
     h continuous_on (interval[vec 0,vec 1] PCROSS X) /\
     IMAGE h (interval[vec 0,vec 1] PCROSS X) SUBSET Y /\
     (!x. h(pastecart (vec 0) x) = p x) /\
     (!x. h(pastecart (vec 1) x) = q x) /\
     (!t. t IN interval[vec 0,vec 1] ==> P(\x. h(pastecart t x)))`;;

(* ------------------------------------------------------------------------- *)
(* We often want to just localize the ending function equality or whatever.  *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_WITH = prove
 (`(!h k. (!x. x IN X ==> h x = k x) ==> (P h <=> P k))
   ==> (homotopic_with P (X,Y) p q <=>
        ?h:real^(1,M)finite_sum->real^N.
          h continuous_on (interval[vec 0,vec 1] PCROSS X) /\
          IMAGE h (interval[vec 0,vec 1] PCROSS X) SUBSET Y /\
          (!x. x IN X ==> h(pastecart (vec 0) x) = p x) /\
          (!x. x IN X ==> h(pastecart (vec 1) x) = q x) /\
          (!t. t IN interval[vec 0,vec 1] ==> P(\x. h(pastecart t x))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[homotopic_with; PCROSS] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    REWRITE_TAC[homotopic_with; PCROSS] THEN
     DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N`
      (fun th -> EXISTS_TAC
        `\y. if sndcart(y) IN X then (h:real^(1,M)finite_sum->real^N) y
             else if fstcart(y) = vec 0 then p(sndcart y)
             else q(sndcart y)` THEN
      MP_TAC th)) THEN
     REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; VEC_EQ; ARITH_EQ] THEN
     REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THENL
      [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_EQ) THEN
       SIMP_TAC[FORALL_IN_GSPEC; SNDCART_PASTECART];
       SIMP_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC; SUBSET] THEN
       SIMP_TAC[FORALL_IN_GSPEC; SNDCART_PASTECART];
       ASM_MESON_TAC[];
       ASM_MESON_TAC[];
       MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real^1` THEN
       MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
       MATCH_MP_TAC EQ_IMP THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       SIMP_TAC[]]]);;

let HOMOTOPIC_WITH_EQ = prove
 (`!P X Y f g f' g':real^M->real^N.
        homotopic_with P (X,Y) f g /\
        (!x. x IN X ==> f' x = f x /\ g' x = g x) /\
        (!h k. (!x. x IN X ==> h x = k x) ==> (P h <=> P k))
        ==>  homotopic_with P (X,Y) f' g'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_with] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N`
   (fun th -> EXISTS_TAC
     `\y. if sndcart(y) IN X then (h:real^(1,M)finite_sum->real^N) y
          else if fstcart(y) = vec 0 then f'(sndcart y)
          else g'(sndcart y)` THEN
   MP_TAC th)) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; VEC_EQ; ARITH_EQ] THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_EQ) THEN
    SIMP_TAC[FORALL_IN_PCROSS; SNDCART_PASTECART];
    SIMP_TAC[FORALL_IN_IMAGE; FORALL_IN_PCROSS; SUBSET] THEN
    SIMP_TAC[FORALL_IN_PCROSS; SNDCART_PASTECART];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real^1` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[]]);;

let HOMOTOPIC_WITH_EQUAL = prove
 (`!P f:real^M->real^N g s t.
        P f /\ P g /\
        f continuous_on s /\ IMAGE f s SUBSET t /\
        (!x. x IN s ==> g x = f x)
        ==> homotopic_with P (s,t) f g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homotopic_with] THEN
  EXISTS_TAC `\z:real^(1,M)finite_sum.
    if fstcart z = vec 1 then g(sndcart z):real^N else f(sndcart z)` THEN
  REWRITE_TAC[VEC_EQ; ARITH_EQ; SNDCART_PASTECART; FSTCART_PASTECART] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\z:real^(1,M)finite_sum. (f:real^M->real^N)(sndcart z)` THEN
    ASM_SIMP_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[COND_ID] THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; IMAGE_SNDCART_PCROSS] THEN
    ASM_REWRITE_TAC[UNIT_INTERVAL_NONEMPTY];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    REWRITE_TAC[ FSTCART_PASTECART; SNDCART_PASTECART] THEN
    CONJ_TAC THEN X_GEN_TAC `t:real^1` THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `t:real^1 = vec 1` THEN ASM_REWRITE_TAC[ETA_AX] THEN
    ASM SET_TAC[]]);;

let HOMOTOPIC_CONSTANT_MAPS = prove
 (`!s:real^M->bool t:real^N->bool a b.
        homotopic_with (\x. T) (s,t) (\x. a) (\x. b) <=>
        s = {} \/ path_component t a b`,
  REPEAT GEN_TAC THEN SIMP_TAC[HOMOTOPIC_WITH; path_component] THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; PCROSS_EMPTY; IMAGE_CLAUSES] THEN
  REWRITE_TAC[EMPTY_SUBSET; CONTINUOUS_ON_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PATH_IMAGE_NONEMPTY; SUBSET_EMPTY; PCROSS_EQ_EMPTY;
                  IMAGE_EQ_EMPTY; UNIT_INTERVAL_NONEMPTY] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N`
        STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?c:real^M. c IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `(h:real^(1,M)finite_sum->real^N) o (\t. pastecart t c)` THEN
    ASM_SIMP_TAC[pathstart; pathfinish; o_THM; PATH_IMAGE_COMPOSE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[path] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET));
      REWRITE_TAC[path_image]] THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE; FORALL_IN_PCROSS];
    REWRITE_TAC[path; pathstart; path_image; pathfinish] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC
     `(g:real^1->real^N) o (fstcart:real^(1,M)finite_sum->real^1)` THEN
    ASM_SIMP_TAC[FSTCART_PASTECART; o_THM; IMAGE_o; IMAGE_FSTCART_PCROSS] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[LINEAR_FSTCART; LINEAR_CONTINUOUS_ON;
                 IMAGE_FSTCART_PCROSS]]);;

(* ------------------------------------------------------------------------- *)
(* Trivial properties.                                                       *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_WITH_IMP_PROPERTY = prove
 (`!P X Y (f:real^M->real^N) g. homotopic_with P (X,Y) f g ==> P f /\ P g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN DISCH_THEN
   (fun th -> MP_TAC(SPEC `vec 0:real^1` th) THEN
              MP_TAC(SPEC `vec 1:real^1` th)) THEN
  ASM_SIMP_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL; ETA_AX]);;

let HOMOTOPIC_WITH_IMP_CONTINUOUS = prove
 (`!P X Y (f:real^M->real^N) g.
      homotopic_with P (X,Y) f g ==> f continuous_on X /\ g continuous_on X`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N` MP_TAC) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `((h:real^(1,M)finite_sum->real^N) o (\x. pastecart (vec 0) x))
    continuous_on X /\
    ((h:real^(1,M)finite_sum->real^N) o (\x. pastecart (vec 1) x))
    continuous_on X`
  MP_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[o_DEF; ETA_AX]] THEN
  CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SIMP_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1; IN_INTERVAL_1] THEN
  REWRITE_TAC[DROP_VEC; REAL_POS; REAL_LE_REFL]);;

let HOMOTOPIC_WITH_IMP_SUBSET = prove
 (`!P X Y (f:real^M->real^N) g.
      homotopic_with P (X,Y) f g ==> IMAGE f X SUBSET Y /\ IMAGE g X SUBSET Y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N` MP_TAC) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_PCROSS; SUBSET] THEN DISCH_THEN
   (fun th -> MP_TAC(SPEC `vec 0:real^1` th) THEN
              MP_TAC(SPEC `vec 1:real^1` th)) THEN
  ASM_SIMP_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL]);;

let HOMOTOPIC_WITH_MONO = prove
 (`!P Q X Y f g:real^M->real^N.
        homotopic_with P (X,Y) f g /\
        (!h. h continuous_on X /\ IMAGE h X SUBSET Y /\ P h ==> Q h)
        ==> homotopic_with Q (X,Y) f g`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_with; PCROSS] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
             CONTINUOUS_ON_CONST] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let HOMOTOPIC_WITH_SUBSET_LEFT = prove
 (`!P X Y Z f g.
        homotopic_with P (X,Y) f g /\ Z SUBSET X
        ==> homotopic_with P (Z,Y) f g`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_with; PCROSS] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let HOMOTOPIC_WITH_SUBSET_RIGHT = prove
 (`!P X Y Z (f:real^M->real^N) g h.
        homotopic_with P (X,Y) f g /\ Y SUBSET Z
        ==> homotopic_with P (X,Z) f g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_with] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN
  ASM_MESON_TAC[SUBSET_TRANS]);;

let HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT = prove
 (`!p f:real^N->real^P g h:real^M->real^N W X Y.
        homotopic_with (\f. p(f o h)) (X,Y) f g /\
        h continuous_on W /\ IMAGE h W SUBSET X
        ==> homotopic_with p (W,Y) (f o h) (g o h)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_with; o_DEF; PCROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^(1,N)finite_sum->real^P`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\y:real^(1,M)finite_sum.
                (k:real^(1,N)finite_sum->real^P)
                (pastecart (fstcart y) (h(sndcart y)))` THEN
  ASM_REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE [IMP_CONJ]
      CONTINUOUS_ON_SUBSET));
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  SIMP_TAC[IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

let HOMOTOPIC_COMPOSE_CONTINUOUS_RIGHT = prove
 (`!f:real^N->real^P g h:real^M->real^N W X Y.
        homotopic_with (\f. T) (X,Y) f g /\
        h continuous_on W /\ IMAGE h W SUBSET X
        ==> homotopic_with (\f. T) (W,Y) (f o h) (g o h)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
  EXISTS_TAC `X:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT = prove
 (`!p f:real^M->real^N g h:real^N->real^P X Y Z.
        homotopic_with (\f. p(h o f)) (X,Y) f g /\
        h continuous_on Y /\ IMAGE h Y SUBSET Z
        ==> homotopic_with p (X,Z) (h o f) (h o g)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_with; o_DEF] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^(1,M)finite_sum->real^N`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(h:real^N->real^P) o (k:real^(1,M)finite_sum->real^N)` THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE [IMP_CONJ]
      CONTINUOUS_ON_SUBSET));
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[]);;

let HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT = prove
 (`!f:real^M->real^N g h:real^N->real^P X Y Z.
        homotopic_with (\f. T) (X,Y) f g /\
        h continuous_on Y /\ IMAGE h Y SUBSET Z
        ==> homotopic_with (\f. T) (X,Z) (h o f) (h o g)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
  EXISTS_TAC `Y:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let HOMOTOPIC_WITH_PCROSS = prove
 (`!f:real^M->real^N f':real^P->real^Q g g' p p' q s s' t t'.
     homotopic_with p (s,t) f g /\
     homotopic_with p' (s',t') f' g' /\
     (!f g. p f /\ p' g ==> q(\x. pastecart (f(fstcart x)) (g(sndcart x))))
     ==> homotopic_with q (s PCROSS s',t PCROSS t')
          (\z. pastecart (f(fstcart z)) (f'(sndcart z)))
          (\z. pastecart (g(fstcart z)) (g'(sndcart z)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k:real^(1,M)finite_sum->real^N` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `k':real^(1,P)finite_sum->real^Q` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC
   `\z:real^(1,(M,P)finite_sum)finite_sum.
        pastecart (k(pastecart (fstcart z) (fstcart(sndcart z))):real^N)
                  (k'(pastecart (fstcart z) (sndcart(sndcart z))):real^Q)` THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS]) THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS;
               FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS;
               IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
     SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
     GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
     MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
     SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART];
     FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN
     REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS;
                 IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
     ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART;
                  PASTECART_IN_PCROSS]]));;

(* ------------------------------------------------------------------------- *)
(* Homotopy with P is an equivalence relation (on continuous functions       *)
(* mapping X into Y that satisfy P, though this only affects reflexivity).   *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_WITH_REFL = prove
 (`!P X Y (f:real^M->real^N).
      homotopic_with P (X,Y) f f <=>
      f continuous_on X /\ IMAGE f X SUBSET Y /\ P f`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[HOMOTOPIC_WITH_IMP_PROPERTY; HOMOTOPIC_WITH_IMP_CONTINUOUS;
              HOMOTOPIC_WITH_IMP_SUBSET];
    STRIP_TAC THEN REWRITE_TAC[homotopic_with; PCROSS]] THEN
  EXISTS_TAC `\y:real^(1,M)finite_sum. (f:real^M->real^N) (sndcart y)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
  ASM_SIMP_TAC[SNDCART_PASTECART; ETA_AX; SUBSET; FORALL_IN_IMAGE;
               FORALL_IN_GSPEC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; SNDCART_PASTECART]);;

let HOMOTOPIC_WITH_SYM = prove
 (`!P X Y (f:real^M->real^N) g.
      homotopic_with P (X,Y) f g <=> homotopic_with P (X,Y) g f`,
  REPLICATE_TAC 3 GEN_TAC THEN MATCH_MP_TAC(MESON[]
   `(!x y. P x y ==> P y x) ==> (!x y. P x y <=> P y x)`) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with; PCROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,M)finite_sum->real^N`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\y:real^(1,M)finite_sum.
        (h:real^(1,M)finite_sum->real^N)
        (pastecart (vec 1 - fstcart y) (sndcart y))` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_SUB_RZERO] THEN REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST;
             LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET));
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
    REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `IMAGE h s SUBSET t ==> IMAGE g s SUBSET s
      ==> IMAGE h (IMAGE g s) SUBSET t`)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC];
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[PASTECART_EQ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SIMP_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1; IN_INTERVAL_1] THEN
  REWRITE_TAC[DROP_VEC; REAL_POS; REAL_LE_REFL; DROP_SUB] THEN
  ASM_REAL_ARITH_TAC);;

let HOMOTOPIC_WITH_TRANS = prove
 (`!P X Y (f:real^M->real^N) g h.
      homotopic_with P (X,Y) f g /\ homotopic_with P (X,Y) g h
      ==> homotopic_with P (X,Y) f h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with; PCROSS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k1:real^(1,M)finite_sum->real^N` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `k2:real^(1,M)finite_sum->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\y:real^(1,M)finite_sum.
        if drop(fstcart y) <= &1 / &2
        then (k1:real^(1,M)finite_sum->real^N)
             (pastecart (&2 % fstcart y) (sndcart y))
        else (k2:real^(1,M)finite_sum->real^N)
             (pastecart (&2 % fstcart y - vec 1) (sndcart y))` THEN
  REWRITE_TAC[FSTCART_PASTECART; DROP_VEC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `&2 % x - x:real^N = x`; SNDCART_PASTECART] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `interval[vec 0:real^1,vec 1] =
      interval[vec 0,lift(&1 / &2)] UNION interval[lift(&1 / &2),vec 1]`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SET_RULE `{f x y | x IN s UNION t /\ y IN u} =
                          {f x y | x IN s /\ y IN u} UNION
                          {f x y | x IN t /\ y IN u}`] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
    ONCE_REWRITE_TAC[TAUT
     `a /\ b /\ c /\ d /\ e <=> (a /\ b) /\ (c /\ d) /\ e`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CLOSED_IN_CLOSED] THEN CONJ_TAC THENL
       [EXISTS_TAC `{ pastecart (t:real^1) (x:real^M) |
                      t IN interval[vec 0,lift(&1 / &2)] /\ x IN UNIV }`;
        EXISTS_TAC `{ pastecart (t:real^1) (x:real^M) |
                      t IN interval[lift(&1 / &2),vec 1] /\ x IN UNIV}`] THEN
      SIMP_TAC[REWRITE_RULE[PCROSS] CLOSED_PCROSS;
               CLOSED_INTERVAL; CLOSED_UNIV] THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_INTER; TAUT
       `(x IN (s UNION t) /\ x IN u ==> x IN v) <=>
        (x IN u ==> x IN (s UNION t) ==> x IN v)`] THEN
      REWRITE_TAC[PASTECART_EQ; IN_ELIM_THM; IN_UNION] THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_UNIV] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
       [CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CMUL; CONTINUOUS_ON_SUB;
        CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART;
        LINEAR_SNDCART] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[IN_ELIM_THM; PASTECART_EQ; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      REWRITE_TAC[MESON[] `(?t x. P t x /\ a = t /\ b = x) <=> P a b`] THEN
      SIMP_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC; DROP_CMUL; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
      REWRITE_TAC[FORALL_AND_THM; IMP_CONJ; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1] THEN
      SIMP_TAC[LIFT_DROP; DROP_VEC; REAL_ARITH
       `&1 / &2 <= t ==> (t <= &1 / &2 <=> t = &1 / &2)`] THEN
      SIMP_TAC[GSYM LIFT_EQ; LIFT_DROP; GSYM LIFT_CMUL; GSYM LIFT_NUM] THEN
      REWRITE_TAC[GSYM LIFT_SUB] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REWRITE_TAC[LIFT_NUM]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `IMAGE k s SUBSET t ==> x IN s ==> k x IN t`)) THEN
    ASM_REWRITE_TAC[IN_ELIM_PASTECART_THM; IN_INTERVAL_1; DROP_VEC;
                    DROP_CMUL; DROP_SUB] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    STRIP_TAC THEN ASM_CASES_TAC `drop t <= &1 / &2` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; DROP_SUB] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Two characterizations of homotopic triviality, one of which               *)
(* implicitly incorporates path-connectedness.                               *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_TRIVIALITY = prove
 (`!s:real^M->bool t:real^N->bool.
        (!f g. f continuous_on s /\ IMAGE f s SUBSET t /\
               g continuous_on s /\ IMAGE g s SUBSET t
               ==> homotopic_with (\x. T) (s,t) f g) <=>
        (s = {} \/ path_connected t) /\
        (!f. f continuous_on s /\ IMAGE f s SUBSET t
             ==> ?c. homotopic_with (\x. T) (s,t) f (\x. c))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THENL
   [ASM_SIMP_TAC[CONTINUOUS_ON_EMPTY; HOMOTOPIC_WITH; NOT_IN_EMPTY;
                 PCROSS_EMPTY; IMAGE_CLAUSES; EMPTY_SUBSET];
    ASM_CASES_TAC `t:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[SUBSET_EMPTY; IMAGE_EQ_EMPTY; PATH_CONNECTED_EMPTY]] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (rand o rand) HOMOTOPIC_CONSTANT_MAPS o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; CONTINUOUS_ON_CONST] THEN
    ASM SET_TAC[];
    SUBGOAL_THEN `?c:real^N. c IN t` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; CONTINUOUS_ON_CONST];
    FIRST_X_ASSUM(fun th ->
      MP_TAC(ISPEC `g:real^M->real^N` th) THEN
      MP_TAC(ISPEC `f:real^M->real^N` th)) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `c:real^N` THEN DISCH_TAC THEN
    X_GEN_TAC `d:real^N` THEN DISCH_TAC THEN
    TRANS_TAC HOMOTOPIC_WITH_TRANS `(\x. c):real^M->real^N` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
    TRANS_TAC HOMOTOPIC_WITH_TRANS `(\x. d):real^M->real^N` THEN
    ASM_REWRITE_TAC[HOMOTOPIC_CONSTANT_MAPS] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o
      REWRITE_RULE[PATH_CONNECTED_IFF_PATH_COMPONENT]) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET)) THEN
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Homotopy of paths, maintaining the same endpoints.                        *)
(* ------------------------------------------------------------------------- *)

let homotopic_paths = new_definition
 `homotopic_paths s p q =
     homotopic_with
       (\r. pathstart r = pathstart p /\ pathfinish r = pathfinish p)
       (interval[vec 0:real^1,vec 1],s)
       p q`;;

let HOMOTOPIC_PATHS = prove
 (`!s p q:real^1->real^N.
      homotopic_paths s p q <=>
      ?h. h continuous_on
          interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1] /\
          IMAGE h (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1])
          SUBSET s /\
          (!x. x IN interval[vec 0,vec 1] ==> h(pastecart (vec 0) x) = p x) /\
          (!x. x IN interval[vec 0,vec 1] ==> h(pastecart (vec 1) x) = q x) /\
          (!t. t IN interval[vec 0:real^1,vec 1]
               ==> pathstart(h o pastecart t) = pathstart p /\
                   pathfinish(h o pastecart t) = pathfinish p)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[homotopic_paths] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) HOMOTOPIC_WITH o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[pathstart; pathfinish; ENDS_IN_UNIT_INTERVAL];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let HOMOTOPIC_PATHS_IMP_PATHSTART = prove
 (`!s p q. homotopic_paths s p q ==> pathstart p = pathstart q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_paths] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN
  SIMP_TAC[]);;

let HOMOTOPIC_PATHS_IMP_PATHFINISH = prove
 (`!s p q. homotopic_paths s p q ==> pathfinish p = pathfinish q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_paths] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN
  SIMP_TAC[]);;

let HOMOTOPIC_PATHS_IMP_PATH = prove
 (`!s p q. homotopic_paths s p q ==> path p /\ path q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_paths] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
  SIMP_TAC[path]);;

let HOMOTOPIC_PATHS_IMP_SUBSET = prove
 (`!s p q.
     homotopic_paths s p q ==> path_image p SUBSET s /\ path_image q SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_paths] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  SIMP_TAC[path_image]);;

let HOMOTOPIC_PATHS_REFL = prove
 (`!s p. homotopic_paths s p p <=>
           path p /\ path_image p SUBSET s`,
  REWRITE_TAC[homotopic_paths; HOMOTOPIC_WITH_REFL; path; path_image]);;

let HOMOTOPIC_PATHS_SYM = prove
 (`!s p q. homotopic_paths s p q <=> homotopic_paths s q p`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHSTART) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHFINISH) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_paths]) THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN ASM_SIMP_TAC[homotopic_paths]);;

let HOMOTOPIC_PATHS_TRANS = prove
 (`!s p q r.
        homotopic_paths s p q /\ homotopic_paths s q r
        ==> homotopic_paths s p r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(CONJUNCTS_THEN
   (fun th -> ASSUME_TAC(MATCH_MP HOMOTOPIC_PATHS_IMP_PATHSTART th) THEN
              ASSUME_TAC(MATCH_MP HOMOTOPIC_PATHS_IMP_PATHFINISH th))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE BINOP_CONV [homotopic_paths]) THEN
  ASM_REWRITE_TAC[HOMOTOPIC_WITH_TRANS; homotopic_paths]);;

let HOMOTOPIC_PATHS_EQ = prove
 (`!p:real^1->real^N q s.
        path p /\ path_image p SUBSET s /\
        (!t. t IN interval[vec 0,vec 1] ==> p(t) = q(t))
        ==> homotopic_paths s p q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homotopic_paths] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  REPEAT(EXISTS_TAC `p:real^1->real^N`) THEN
  ASM_SIMP_TAC[HOMOTOPIC_WITH_REFL] THEN
  ASM_REWRITE_TAC[GSYM path; GSYM path_image] THEN
  REWRITE_TAC[pathstart; pathfinish] THEN
  MESON_TAC[ENDS_IN_UNIT_INTERVAL]);;

let HOMOTOPIC_PATHS_REPARAMETRIZE = prove
 (`!p:real^1->real^N q f:real^1->real^1.
        path p /\ path_image p SUBSET s /\
        (?f. f continuous_on interval[vec 0,vec 1] /\
             IMAGE f (interval[vec 0,vec 1]) SUBSET interval[vec 0,vec 1] /\
             f(vec 0) = vec 0 /\ f(vec 1) = vec 1 /\
             !t. t IN interval[vec 0,vec 1] ==> q(t) = p(f t))
        ==> homotopic_paths s p q`,
  REWRITE_TAC[path; path_image] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `(p:real^1->real^N) o (f:real^1->real^1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_EQ THEN
    ASM_SIMP_TAC[o_THM; pathstart; pathfinish; o_THM;
                 IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL] THEN
    REWRITE_TAC[path; path_image] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `(p:real^1->real^N) o (f:real^1->real^1)` THEN
      ASM_SIMP_TAC[o_THM] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ASM SET_TAC[]];
    REWRITE_TAC[homotopic_paths; homotopic_with; PCROSS] THEN
    EXISTS_TAC `(p:real^1->real^N) o
                (\y. (&1 - drop(fstcart y)) % f(sndcart y) +
                     drop(fstcart y) % sndcart y)` THEN
    ASM_REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC;
                    pathstart; pathfinish] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_RZERO; VECTOR_ADD_LID;
                VECTOR_MUL_LID; VECTOR_ADD_RID] THEN
    REWRITE_TAC[VECTOR_ARITH `(&1 - u) % x + u % x:real^N = x`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
        MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
        REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX; LIFT_SUB] THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST; LINEAR_FSTCART;
                 LINEAR_SNDCART; CONTINUOUS_ON_SUB] THEN
        MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; SNDCART_PASTECART];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET))];
      ONCE_REWRITE_TAC[IMAGE_o] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE p i SUBSET s
        ==> IMAGE f x SUBSET i
            ==> IMAGE p (IMAGE f x) SUBSET s`))] THEN
    SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; SNDCART_PASTECART;
             FSTCART_PASTECART] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] (CONJUNCT1(SPEC_ALL
      CONVEX_INTERVAL))) THEN
    ASM_MESON_TAC[IN_INTERVAL_1; DROP_VEC; SUBSET; IN_IMAGE]]);;

let HOMOTOPIC_PATHS_SUBSET = prove
 (`!s p q.
        homotopic_paths s p q /\ s SUBSET t
        ==> homotopic_paths t p q`,
  REWRITE_TAC[homotopic_paths; HOMOTOPIC_WITH_SUBSET_RIGHT]);;

(* ------------------------------------------------------------------------- *)
(* A slightly ad-hoc but useful lemma in constructing homotopies.            *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_JOIN_LEMMA = prove
 (`!p q:real^1->real^1->real^N.
  (\y. p (fstcart y) (sndcart y)) continuous_on
  (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]) /\
  (\y. q (fstcart y) (sndcart y)) continuous_on
  (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]) /\
  (!t. t IN interval[vec 0,vec 1] ==> pathfinish(p t) = pathstart(q t))
  ==> (\y. (p(fstcart y) ++ q(fstcart y)) (sndcart y)) continuous_on
      (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1])`,
  REWRITE_TAC[joinpaths; PCROSS] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_CASES_LE THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
    `(\y. p (fstcart y) (&2 % sndcart y)):real^(1,1)finite_sum->real^N =
     (\y. p (fstcart y) (sndcart y)) o
     (\y. pastecart (fstcart y) (&2 % sndcart y))`
    SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC];
    SUBGOAL_THEN
    `(\y. q (fstcart y) (&2 % sndcart y - vec 1)):real^(1,1)finite_sum->real^N =
     (\y. q (fstcart y) (sndcart y)) o
     (\y. pastecart (fstcart y) (&2 % sndcart y - vec 1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC];
    SIMP_TAC[o_DEF; LIFT_DROP; LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; ETA_AX];
    SIMP_TAC[IMP_CONJ; FORALL_IN_GSPEC; FSTCART_PASTECART; SNDCART_PASTECART;
             GSYM LIFT_EQ; LIFT_DROP; GSYM LIFT_CMUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_SIMP_TAC[LIFT_NUM; VECTOR_SUB_REFL]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  (CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_ON_PASTECART; ALL_TAC]) THEN
  SIMP_TAC[CONTINUOUS_ON_CMUL; LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_SUB;
           CONTINUOUS_ON_CONST; LINEAR_FSTCART; LINEAR_SNDCART] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; IMP_CONJ] THEN
  SIMP_TAC[IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_SUB; DROP_VEC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Congruence properties of homotopy w.r.t. path-combining operations.       *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_PATHS_REVERSEPATH = prove
 (`!s p q:real^1->real^N.
     homotopic_paths s (reversepath p) (reversepath q) <=>
     homotopic_paths s p q`,
  GEN_TAC THEN MATCH_MP_TAC(MESON[]
   `(!p. f(f p) = p) /\
    (!a b. homotopic_paths s a b ==> homotopic_paths s (f a) (f b))
    ==> !a b. homotopic_paths s (f a) (f b) <=>
              homotopic_paths s a b`) THEN
  REWRITE_TAC[REVERSEPATH_REVERSEPATH] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[homotopic_paths; homotopic_with; PCROSS; o_DEF] THEN DISCH_THEN
   (X_CHOOSE_THEN `h:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\y:real^(1,1)finite_sum.
                 (h:real^(1,1)finite_sum->real^N)
                 (pastecart(fstcart y) (vec 1 - sndcart y))` THEN
  ASM_REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
  ASM_SIMP_TAC[reversepath; pathstart; pathfinish; VECTOR_SUB_REFL;
               VECTOR_SUB_RZERO] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART;
               CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC;
        IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN REAL_ARITH_TAC];
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
     REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `IMAGE h s SUBSET t ==> IMAGE g s SUBSET s
      ==> IMAGE h (IMAGE g s) SUBSET t`)) THEN
     SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC;
        IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
     REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN REAL_ARITH_TAC]);;

let HOMOTOPIC_PATHS_JOIN = prove
 (`!s p q p' q':real^1->real^N.
     homotopic_paths s p p' /\ homotopic_paths s q q' /\
     pathfinish p = pathstart q
     ==> homotopic_paths s (p ++ q) (p' ++ q')`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_paths; homotopic_with; PCROSS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k1:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `k2:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(\y. ((k1 o pastecart (fstcart y)) ++
                    (k2 o pastecart (fstcart y))) (sndcart y))
              :real^(1,1)finite_sum->real^N` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[PCROSS] HOMOTOPIC_JOIN_LEMMA) THEN
    ASM_REWRITE_TAC[o_DEF; PASTECART_FST_SND; ETA_AX] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_REWRITE_TAC[pathstart; pathfinish] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[ETA_AX; GSYM path_image; SET_RULE
      `(!x. x IN i ==> f x IN s) <=> IMAGE f i SUBSET s`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN
    REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE; o_DEF] THEN ASM SET_TAC[];
    ALL_TAC; ALL_TAC; ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM_REWRITE_TAC[joinpaths; o_DEF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
  REWRITE_TAC[pathstart; pathfinish; DROP_VEC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[VECTOR_ARITH `&2 % x - x:real^N = x`; VECTOR_MUL_RZERO]);;

let HOMOTOPIC_PATHS_CONTINUOUS_IMAGE = prove
 (`!f:real^1->real^M g h:real^M->real^N s t.
        homotopic_paths s f g /\
        h continuous_on s /\ IMAGE h s SUBSET t
        ==> homotopic_paths t (h o f) (h o g)`,
  REWRITE_TAC[homotopic_paths] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_WITH_MONO)) THEN
  SIMP_TAC[pathstart; pathfinish; o_THM]);;

(* ------------------------------------------------------------------------- *)
(* Group properties for homotopy of paths (so taking equivalence classes     *)
(* under homotopy would give the fundamental group).                         *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_PATHS_RID = prove
 (`!s p. path p /\ path_image p SUBSET s
         ==> homotopic_paths s (p ++ linepath(pathfinish p,pathfinish p)) p`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_REPARAMETRIZE THEN
  ASM_REWRITE_TAC[joinpaths] THEN
  EXISTS_TAC `\t. if drop t <= &1 / &2 then &2 % t else vec 1` THEN
  ASM_REWRITE_TAC[DROP_VEC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; linepath; pathfinish;
              VECTOR_ARITH `(&1 - t) % x + t % x:real^N = x`] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `interval[vec 0:real^1,vec 1] =
      interval[vec 0,lift(&1 / &2)] UNION interval[lift(&1 / &2),vec 1]`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
      SIMP_TAC[CLOSED_INTERVAL; CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST; IN_INTERVAL_1; DROP_VEC; LIFT_DROP;
               GSYM DROP_EQ; DROP_CMUL] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_VEC] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[DROP_CMUL; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC]);;

let HOMOTOPIC_PATHS_LID = prove
 (`!s p:real^1->real^N.
        path p /\ path_image p SUBSET s
        ==> homotopic_paths s (linepath(pathstart p,pathstart p) ++ p) p`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM HOMOTOPIC_PATHS_REVERSEPATH] THEN
  REWRITE_TAC[o_DEF; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
  SIMP_TAC[REVERSEPATH_JOINPATHS; REVERSEPATH_LINEPATH;
           PATHFINISH_LINEPATH] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `reversepath p :real^1->real^N`]
    HOMOTOPIC_PATHS_RID) THEN
  ASM_SIMP_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
               PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH]);;

let HOMOTOPIC_PATHS_ASSOC = prove
 (`!s p q r:real^1->real^N.
        path p /\ path_image p SUBSET s /\
        path q /\ path_image q SUBSET s /\
        path r /\ path_image r SUBSET s /\
        pathfinish p = pathstart q /\ pathfinish q = pathstart r
        ==> homotopic_paths s (p ++ (q ++ r)) ((p ++ q) ++ r)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_REPARAMETRIZE THEN
  ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; UNION_SUBSET;
               PATHSTART_JOIN; PATHFINISH_JOIN] THEN
  REWRITE_TAC[joinpaths] THEN
  EXISTS_TAC `\t. if drop t <= &1 / &2 then inv(&2) % t
                  else if drop t <= &3 / &4 then t - lift(&1 / &4)
                  else &2 % t - vec 1` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_CASES_1 THEN
    SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID; LIFT_DROP] THEN
    REWRITE_TAC[GSYM LIFT_SUB; GSYM LIFT_CMUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_1 THEN
    SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID;
             CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[GSYM LIFT_SUB; GSYM LIFT_CMUL; GSYM LIFT_NUM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; DROP_VEC] THEN
    REPEAT STRIP_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    REWRITE_TAC[DROP_CMUL; DROP_VEC; LIFT_DROP; DROP_SUB] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[DROP_VEC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_RZERO];
    REWRITE_TAC[DROP_VEC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    VECTOR_ARITH_TAC;
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    STRIP_TAC THEN
    ASM_CASES_TAC `drop t <= &1 / &2` THEN ASM_REWRITE_TAC[DROP_CMUL] THEN
    ASM_REWRITE_TAC[REAL_ARITH `inv(&2) * t <= &1 / &2 <=> t <= &1`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[REAL_MUL_LID] THEN
    ASM_CASES_TAC `drop t <= &3 / &4` THEN
    ASM_REWRITE_TAC[DROP_SUB; DROP_VEC; DROP_CMUL; LIFT_DROP;
                    REAL_ARITH `&2 * (t - &1 / &4) <= &1 / &2 <=> t <= &1 / &2`;
                    REAL_ARITH `&2 * t - &1 <= &1 / &2 <=> t <= &3 / &4`;
                    REAL_ARITH `t - &1 / &4 <= &1 / &2 <=> t <= &3 / &4`] THEN
    REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC; GSYM LIFT_CMUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LIFT_NUM] THEN
    REWRITE_TAC[VECTOR_ARITH `a - b - b:real^N = a - &2 % b`]]);;

let HOMOTOPIC_PATHS_RINV = prove
 (`!s p:real^1->real^N.
        path p /\ path_image p SUBSET s
        ==> homotopic_paths s
              (p ++ reversepath p) (linepath(pathstart p,pathstart p))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
  REWRITE_TAC[homotopic_paths; homotopic_with; PCROSS] THEN
  EXISTS_TAC `(\y. (subpath (vec 0) (fstcart y) p ++
                    reversepath(subpath (vec 0) (fstcart y) p)) (sndcart y))
              : real^(1,1)finite_sum->real^N` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; SUBPATH_TRIVIAL] THEN
  REWRITE_TAC[ETA_AX; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
  REWRITE_TAC[REVERSEPATH_SUBPATH; PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[joinpaths] THEN MATCH_MP_TAC CONTINUOUS_ON_CASES_LE THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path; path_image]) THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[subpath; VECTOR_ADD_LID; VECTOR_SUB_RZERO] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
        REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART;
                 CONTINUOUS_ON_CMUL];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; FORALL_IN_GSPEC; IMP_CONJ] THEN
        REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC] THEN
        REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `drop x * &2 * &1 / &2` THEN CONJ_TAC THEN
        REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[subpath; VECTOR_ADD_LID; VECTOR_SUB_RZERO] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
        MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
        REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART;
                 CONTINUOUS_ON_CMUL; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; FORALL_IN_GSPEC; IMP_CONJ] THEN
        REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_CMUL; DROP_VEC; DROP_ADD;
         REAL_ARITH `t + (&0 - t) * (&2 * x - &1) =
                     t * &2 * (&1 - x)`] THEN
        REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_SUB_LE] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `drop x * &2 * &1 / &2` THEN CONJ_TAC THEN
        REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN
        ASM_REAL_ARITH_TAC];
      SIMP_TAC[o_DEF; LIFT_DROP; ETA_AX; LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
      REWRITE_TAC[GSYM LIFT_EQ; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[subpath] THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_SUB; DROP_VEC; DROP_ADD; DROP_CMUL;
                  LIFT_DROP] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; ETA_AX;
      SET_RULE `(!x. x IN s ==> f x IN t) <=> IMAGE f s SUBSET t`] THEN
    REWRITE_TAC[GSYM path_image] THEN MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN
    REWRITE_TAC[PATH_IMAGE_SUBPATH_GEN] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [path_image]) THEN
    MATCH_MP_TAC(SET_RULE
      `t SUBSET s /\ u SUBSET s
       ==> IMAGE p s SUBSET v
           ==> IMAGE p t SUBSET v /\ IMAGE p u SUBSET v`) THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN CONJ_TAC THEN
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_INTERVAL] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL];
    REWRITE_TAC[subpath; linepath; pathstart; joinpaths] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; DROP_VEC; VECTOR_MUL_LZERO] THEN
    REWRITE_TAC[VECTOR_ADD_RID; COND_ID] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[pathstart; PATHFINISH_LINEPATH; PATHSTART_LINEPATH]]);;

let HOMOTOPIC_PATHS_LINV = prove
 (`!s p:real^1->real^N.
        path p /\ path_image p SUBSET s
        ==> homotopic_paths s
              (reversepath p ++ p) (linepath(pathfinish p,pathfinish p))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `reversepath p:real^1->real^N`]
        HOMOTOPIC_PATHS_RINV) THEN
  ASM_SIMP_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH] THEN
  REWRITE_TAC[PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
              REVERSEPATH_REVERSEPATH]);;

(* ------------------------------------------------------------------------- *)
(* Homotopy of loops without requiring preservation of endpoints.            *)
(* ------------------------------------------------------------------------- *)

let homotopic_loops = new_definition
 `homotopic_loops s p q =
     homotopic_with
       (\r. pathfinish r = pathstart r)
       (interval[vec 0:real^1,vec 1],s)
       p q`;;

let HOMOTOPIC_LOOPS = prove
 (`!s p q:real^1->real^N.
      homotopic_loops s p q <=>
      ?h. h continuous_on
          interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1] /\
          IMAGE h (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1])
          SUBSET s /\
          (!x. x IN interval[vec 0,vec 1] ==> h(pastecart (vec 0) x) = p x) /\
          (!x. x IN interval[vec 0,vec 1] ==> h(pastecart (vec 1) x) = q x) /\
          (!t. t IN interval[vec 0:real^1,vec 1]
               ==> pathfinish(h o pastecart t) = pathstart(h o pastecart t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[homotopic_loops] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) HOMOTOPIC_WITH o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[pathstart; pathfinish; ENDS_IN_UNIT_INTERVAL];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let HOMOTOPIC_LOOPS_IMP_LOOP = prove
 (`!s p q. homotopic_loops s p q
           ==> pathfinish p = pathstart p /\
               pathfinish q = pathstart q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_loops] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN
  SIMP_TAC[]);;

let HOMOTOPIC_LOOPS_IMP_PATH = prove
 (`!s p q. homotopic_loops s p q ==> path p /\ path q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_loops] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
  SIMP_TAC[path]);;

let HOMOTOPIC_LOOPS_IMP_SUBSET = prove
 (`!s p q.
     homotopic_loops s p q ==> path_image p SUBSET s /\ path_image q SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_loops] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  SIMP_TAC[path_image]);;

let HOMOTOPIC_LOOPS_REFL = prove
 (`!s p. homotopic_loops s p p <=>
           path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p`,
  REWRITE_TAC[homotopic_loops; HOMOTOPIC_WITH_REFL; path; path_image]);;

let HOMOTOPIC_LOOPS_SYM = prove
 (`!s p q. homotopic_loops s p q <=> homotopic_loops s q p`,
  REWRITE_TAC[homotopic_loops; HOMOTOPIC_WITH_SYM]);;

let HOMOTOPIC_LOOPS_TRANS = prove
 (`!s p q r.
        homotopic_loops s p q /\ homotopic_loops s q r
        ==> homotopic_loops s p r`,
  REWRITE_TAC[homotopic_loops; HOMOTOPIC_WITH_TRANS]);;

let HOMOTOPIC_LOOPS_SUBSET = prove
 (`!s p q.
        homotopic_loops s p q /\ s SUBSET t
        ==> homotopic_loops t p q`,
  REWRITE_TAC[homotopic_loops; HOMOTOPIC_WITH_SUBSET_RIGHT]);;

let HOMOTOPIC_LOOPS_EQ = prove
 (`!p:real^1->real^N q s.
        path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
        (!t. t IN interval[vec 0,vec 1] ==> p(t) = q(t))
        ==> homotopic_loops s p q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homotopic_loops] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  REPEAT(EXISTS_TAC `p:real^1->real^N`) THEN
  ASM_SIMP_TAC[HOMOTOPIC_WITH_REFL] THEN
  ASM_REWRITE_TAC[GSYM path; GSYM path_image] THEN
  REWRITE_TAC[pathstart; pathfinish] THEN
  MESON_TAC[ENDS_IN_UNIT_INTERVAL]);;

let HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE = prove
 (`!f:real^1->real^M g h:real^M->real^N s t.
        homotopic_loops s f g /\
        h continuous_on s /\ IMAGE h s SUBSET t
        ==> homotopic_loops t (h o f) (h o g)`,
  REWRITE_TAC[homotopic_loops] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_WITH_MONO)) THEN
  SIMP_TAC[pathstart; pathfinish; o_THM]);;

let HOMOTOPIC_LOOPS_SHIFTPATH_SELF = prove
 (`!p:real^1->real^N t s.
        path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
        t IN interval[vec 0,vec 1]
        ==> homotopic_loops s p (shiftpath t p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMOTOPIC_LOOPS] THEN EXISTS_TAC
   `\z. shiftpath (drop t % fstcart z) (p:real^1->real^N) (sndcart z)` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; o_DEF] THEN
  REWRITE_TAC[GSYM LIFT_EQ_CMUL; VECTOR_MUL_RZERO; ETA_AX] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MATCH_MP_TAC(SET_RULE
     `IMAGE p t SUBSET u /\
      (!x. x IN s ==> IMAGE(shiftpath (f x) p) t = IMAGE p t)
      ==> (!x y. x IN s /\ y IN t ==> shiftpath (f x) p y  IN u)`) THEN
    ASM_REWRITE_TAC[GSYM path_image] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC PATH_IMAGE_SHIFTPATH THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_SIMP_TAC[REAL_LE_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[];
    SIMP_TAC[shiftpath; VECTOR_ADD_LID; IN_INTERVAL_1; DROP_VEC];
    REWRITE_TAC[LIFT_DROP];
    X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN MATCH_MP_TAC CLOSED_SHIFTPATH THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_SIMP_TAC[REAL_LE_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[]] THEN
  REWRITE_TAC[shiftpath; DROP_ADD; DROP_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CASES_LE THEN REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_MUL; o_DEF; LIFT_DROP;
             LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART;
             CONTINUOUS_ON_CONST] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART] THEN
    REWRITE_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1;
                 DROP_ADD; DROP_CMUL; DROP_VEC; REAL_LE_ADD; REAL_LE_MUL];
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_MUL; o_DEF; LIFT_DROP;
             LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART;
             CONTINUOUS_ON_CONST; CONTINUOUS_ON_SUB] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART] THEN
    REWRITE_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; DROP_SUB;
                 DROP_ADD; DROP_CMUL; DROP_VEC; REAL_LE_ADD; REAL_LE_MUL] THEN
    SIMP_TAC[REAL_ARITH `&0 <= x + y - &1 <=> &1 <= x + y`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `t * x <= &1 * &1 /\ y <= &1 ==> t * x + y - &1 <= &1`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL2; REAL_POS];
    REWRITE_TAC[o_DEF; LIFT_ADD; LIFT_CMUL; LIFT_DROP] THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CMUL; LINEAR_CONTINUOUS_ON;
             LINEAR_FSTCART; LINEAR_SNDCART];
    SIMP_TAC[GSYM LIFT_EQ; LIFT_ADD; LIFT_CMUL; LIFT_DROP; LIFT_NUM;
             VECTOR_ARITH `a + b - c:real^1 = (a + b) - c`] THEN
    ASM_MESON_TAC[VECTOR_SUB_REFL; pathstart; pathfinish]]);;

(* ------------------------------------------------------------------------- *)
(* Relations between the two variants of homotopy.                           *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS = prove
 (`!s p q. homotopic_paths s p q /\
           pathfinish p = pathstart p /\
           pathfinish q = pathstart p
           ==> homotopic_loops s p q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_paths; homotopic_loops] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_MONO) THEN
  ASM_SIMP_TAC[]);;

let HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL = prove
 (`!s p a:real^N.
        homotopic_loops s p (linepath(a,a))
        ==> homotopic_paths s p (linepath(pathstart p,pathstart p))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_PATH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_loops]) THEN
  REWRITE_TAC[homotopic_with; PCROSS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h:real^(1,1)finite_sum->real^N` THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN EXISTS_TAC
   `(p:real^1->real^N) ++ linepath(pathfinish p,pathfinish p)` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[HOMOTOPIC_PATHS_RID; HOMOTOPIC_PATHS_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN EXISTS_TAC
   `linepath(pathstart p,pathstart p) ++ (p:real^1->real^N) ++
    linepath(pathfinish p,pathfinish p)` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    MP_TAC(ISPECL [`s:real^N->bool`;
       `(p:real^1->real^N) ++ linepath(pathfinish p,pathfinish p)`]
     HOMOTOPIC_PATHS_LID) THEN
    REWRITE_TAC[PATHSTART_JOIN] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_LINEPATH; PATHSTART_LINEPATH] THEN
    MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN
    ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN EXISTS_TAC
   `((\u. (h:real^(1,1)finite_sum->real^N) (pastecart u (vec 0))) ++
     linepath(a,a) ++
     reversepath(\u. h (pastecart u (vec 0))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(MESON[HOMOTOPIC_PATHS_LID; HOMOTOPIC_PATHS_JOIN;
                       HOMOTOPIC_PATHS_TRANS; HOMOTOPIC_PATHS_SYM;
                       HOMOTOPIC_PATHS_RINV]
       `(path p /\ path(reversepath p)) /\
        (path_image p SUBSET s /\ path_image(reversepath p) SUBSET s) /\
        (pathfinish p = pathstart(linepath(b,b) ++ reversepath p) /\
         pathstart(reversepath p) = b) /\
        pathstart p = a
        ==> homotopic_paths s (p ++ linepath(b,b) ++ reversepath p)
                              (linepath(a,a))`) THEN
    REWRITE_TAC[PATHSTART_REVERSEPATH; PATHSTART_JOIN; PATH_REVERSEPATH;
                PATH_IMAGE_REVERSEPATH; PATHSTART_LINEPATH] THEN
    ASM_REWRITE_TAC[path; path_image; pathstart; pathfinish;
                    LINEPATH_REFL] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_PASTECART_THM;
               ENDS_IN_UNIT_INTERVAL];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          SUBSET_TRANS)) THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
      REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_PASTECART_THM;
               ENDS_IN_UNIT_INTERVAL]]] THEN
  REWRITE_TAC[homotopic_paths; homotopic_with; PCROSS] THEN
  EXISTS_TAC
   `\y:real^(1,1)finite_sum.
        (subpath (vec 0) (fstcart y) (\u. h(pastecart u (vec 0))) ++
         (\u. (h:real^(1,1)finite_sum->real^N) (pastecart (fstcart y) u)) ++
         subpath (fstcart y) (vec 0) (\u. h(pastecart u (vec 0))))
        (sndcart y)` THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; SUBPATH_TRIVIAL;
                  SUBPATH_REFL; SUBPATH_REVERSEPATH; ETA_AX;
                  PATHSTART_JOIN; PATHFINISH_JOIN;
                  PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
                  PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[pathstart]] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[PCROSS] HOMOTOPIC_JOIN_LEMMA) THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REWRITE_RULE[PCROSS] HOMOTOPIC_JOIN_LEMMA) THEN
      ASM_REWRITE_TAC[PASTECART_FST_SND; ETA_AX] THEN CONJ_TAC THENL
       [ALL_TAC;
        RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
        REWRITE_TAC[PATHSTART_SUBPATH] THEN
        ASM_SIMP_TAC[pathstart; pathfinish]];
      RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
      REWRITE_TAC[PATHFINISH_SUBPATH; PATHSTART_JOIN] THEN
      ASM_SIMP_TAC[pathstart]] THEN
    REWRITE_TAC[subpath] THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; VECTOR_SUB_LZERO; VECTOR_ADD_LID] THEN
    (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
       [CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ADD; CONTINUOUS_ON_MUL;
        LIFT_DROP; CONTINUOUS_ON_NEG; DROP_NEG; CONTINUOUS_ON_CONST;
        CONTINUOUS_ON_ID; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART;
        LIFT_NEG; o_DEF; ETA_AX] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1] THEN
    REWRITE_TAC[DROP_ADD; DROP_NEG; DROP_VEC; DROP_CMUL; REAL_POS] THEN
    SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE; REAL_ARITH
     `t + --t * x = t * (&1 - x)`] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `t * x <= t * &1 /\ &1 * t <= &1 * &1 ==> t * x <= &1`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;

    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; IMP_CONJ;
      RIGHT_FORALL_IMP_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
    REWRITE_TAC[SET_RULE
     `(!x. x IN s ==> f x IN t) <=> IMAGE f s SUBSET t`] THEN
    REWRITE_TAC[GSYM path_image; ETA_AX] THEN
    REPEAT(MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN CONJ_TAC) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      SUBSET_TRANS)) THEN
    REWRITE_TAC[path_image; subpath] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_PASTECART_THM] THEN
    SIMP_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC; DROP_CMUL; DROP_ADD] THEN
    REWRITE_TAC[REAL_ADD_LID; REAL_SUB_RZERO; REAL_POS] THEN
    REWRITE_TAC[REAL_ARITH `t + (&0 - t) * x = t * (&1 - x)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE] THEN
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC]);;

let HOMOTOPIC_LOOPS_CONJUGATE = prove
 (`!p q s:real^N->bool.
        path p /\ path_image p SUBSET s /\
        path q /\ path_image q SUBSET s /\
        pathfinish p = pathstart q /\ pathfinish q = pathstart q
        ==> homotopic_loops s (p ++ q ++ reversepath p) q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN EXISTS_TAC
   `linepath(pathstart q,pathstart q) ++ (q:real^1->real^N) ++
    linepath(pathstart q,pathstart q)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
    MP_TAC(ISPECL [`s:real^N->bool`;
       `(q:real^1->real^N) ++ linepath(pathfinish q,pathfinish q)`]
     HOMOTOPIC_PATHS_LID) THEN
    ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; UNION_SUBSET; SING_SUBSET;
                 PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH;
                 PATH_JOIN; PATH_IMAGE_JOIN; PATH_LINEPATH; SEGMENT_REFL] THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_PATHS_TRANS) THEN
    ASM_MESON_TAC[HOMOTOPIC_PATHS_RID]] THEN
  REWRITE_TAC[homotopic_loops; homotopic_with; PCROSS] THEN
  EXISTS_TAC
   `(\y. (subpath (fstcart y) (vec 1) p ++ q ++ subpath (vec 1) (fstcart y) p)
         (sndcart y)):real^(1,1)finite_sum->real^N` THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; SUBPATH_TRIVIAL;
                  SUBPATH_REFL; SUBPATH_REVERSEPATH; ETA_AX;
                 PATHSTART_JOIN; PATHFINISH_JOIN;
                  PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
                  PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
  ASM_REWRITE_TAC[pathstart; pathfinish] THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[path; path_image]) THEN
    MATCH_MP_TAC(REWRITE_RULE[PCROSS] HOMOTOPIC_JOIN_LEMMA) THEN
    REPEAT CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(REWRITE_RULE[PCROSS] HOMOTOPIC_JOIN_LEMMA) THEN
      REPEAT CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
        SIMP_TAC[SNDCART_PASTECART];
        ALL_TAC;
        REWRITE_TAC[PATHSTART_SUBPATH] THEN ASM_REWRITE_TAC[pathfinish]];
      REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_SUBPATH] THEN
      ASM_REWRITE_TAC[pathstart]] THEN
    REWRITE_TAC[subpath] THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    (CONJ_TAC THENL
      [REWRITE_TAC[DROP_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
       SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST; LINEAR_FSTCART] THEN
       MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
       SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
       REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
       SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON;
                LINEAR_FSTCART];
       FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
       REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
       REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1] THEN
       REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_VEC; DROP_CMUL]])
    THENL
     [REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
        TRY(MATCH_MP_TAC REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ARITH `t + (&1 - t) * x <= &1 <=>
                                (&1 - t) * x <= (&1 - t) * &1`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH
         `x * (&1 - t) <= x * &1 /\ x <= &1
          ==> &0 <= &1 + (t - &1) * x`) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ARITH
         `a + (t - &1) * x <= a <=> &0 <= (&1 - t) * x`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[ETA_AX; GSYM path_image; SET_RULE
      `(!x. x IN i ==> f x IN s) <=> IMAGE f i SUBSET s`] THEN
    REPEAT STRIP_TAC THEN
    REPEAT(MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `path_image p:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PATH_IMAGE_SUBPATH_SUBSET THEN
    ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]]);;

(* ------------------------------------------------------------------------- *)
(* Relating homotopy of trivial loops to path-connectedness.                 *)
(* ------------------------------------------------------------------------- *)

let PATH_COMPONENT_IMP_HOMOTOPIC_POINTS = prove
 (`!s a b:real^N.
        path_component s a b
        ==> homotopic_loops s (linepath(a,a)) (linepath(b,b))`,
  REWRITE_TAC[path_component; homotopic_loops; homotopic_with; PCROSS] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[pathstart; pathfinish; path_image; path] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\y:real^(1,1)finite_sum. (g(fstcart y):real^N)` THEN
  ASM_SIMP_TAC[FSTCART_PASTECART; linepath] THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - x) % a + x % a:real^N = a`] THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; FSTCART_PASTECART]);;

let HOMOTOPIC_LOOPS_IMP_PATH_COMPONENT_VALUE = prove
 (`!s p q:real^1->real^N t.
        homotopic_loops s p q /\ t IN interval[vec 0,vec 1]
        ==> path_component s (p t) (q t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[path_component; homotopic_loops; homotopic_with; PCROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,1)finite_sum->real^N` MP_TAC) THEN
  STRIP_TAC THEN
  EXISTS_TAC `\u. (h:real^(1,1)finite_sum->real^N) (pastecart u t)` THEN
  ASM_REWRITE_TAC[pathstart; pathfinish] THEN CONJ_TAC THENL
   [REWRITE_TAC[path] THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      ASM SET_TAC[]];
    REWRITE_TAC[path_image] THEN ASM SET_TAC[]]);;

let HOMOTOPIC_POINTS_EQ_PATH_COMPONENT = prove
 (`!s a b:real^N.
        homotopic_loops s (linepath(a,a)) (linepath(b,b)) <=>
        path_component s a b`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  REWRITE_TAC[PATH_COMPONENT_IMP_HOMOTOPIC_POINTS] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^1` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    HOMOTOPIC_LOOPS_IMP_PATH_COMPONENT_VALUE)) THEN
  REWRITE_TAC[linepath; IN_INTERVAL_1; DROP_VEC; REAL_POS] THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - &0) % a + &0 % b:real^N = a`]);;

let PATH_CONNECTED_EQ_HOMOTOPIC_POINTS = prove
 (`!s:real^N->bool.
        path_connected s <=>
        !a b. a IN s /\ b IN s
              ==> homotopic_loops s (linepath(a,a)) (linepath(b,b))`,
  GEN_TAC THEN REWRITE_TAC[HOMOTOPIC_POINTS_EQ_PATH_COMPONENT] THEN
  REWRITE_TAC[path_connected; path_component]);;

(* ------------------------------------------------------------------------- *)
(* Homotopy of "nearby" function, paths and loops.                           *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_WITH_LINEAR = prove
 (`!f g:real^M->real^N s t.
        f continuous_on s /\ g continuous_on s /\
        (!x. x IN s ==> segment[f x,g x] SUBSET t)
        ==> homotopic_with (\z. T) (s,t) f g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homotopic_with] THEN
  EXISTS_TAC
    `\y. ((&1 - drop(fstcart y)) % (f:real^M->real^N)(sndcart y) +
         drop(fstcart y) % g(sndcart y):real^N)` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC] THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_SUB_RZERO] THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - t) % a + t % a:real^N = a`] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN
  REWRITE_TAC[VECTOR_ADD_LID; VECTOR_ADD_RID] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; LIFT_SUB] THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON;
             LINEAR_FSTCART; ETA_AX] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    SIMP_TAC[SNDCART_PASTECART; FORALL_IN_PCROSS];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `u:real^M`] THEN STRIP_TAC THEN
    SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; RIGHT_IMP_FORALL_THM; IMP_IMP]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `u:real^M` THEN
    ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `drop t` THEN
    ASM_MESON_TAC[IN_INTERVAL_1; DROP_VEC]]);;

let HOMOTOPIC_PATHS_LINEAR,HOMOTOPIC_LOOPS_LINEAR = (CONJ_PAIR o prove)
 (`(!g s:real^N->bool h.
        path g /\ path h /\
        pathstart h = pathstart g /\ pathfinish h = pathfinish g /\
        (!t x. t IN interval[vec 0,vec 1] ==> segment[g t,h t] SUBSET s)
        ==> homotopic_paths s g h) /\
   (!g s:real^N->bool h.
        path g /\ path h /\
        pathfinish g = pathstart g /\ pathfinish h = pathstart h /\
        (!t x. t IN interval[vec 0,vec 1] ==> segment[g t,h t] SUBSET s)
        ==> homotopic_loops s g h)`,
  CONJ_TAC THEN
 (REWRITE_TAC[pathstart; pathfinish] THEN
  REWRITE_TAC[SUBSET; RIGHT_IMP_FORALL_THM; IMP_IMP] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[homotopic_paths; homotopic_loops; homotopic_with; PCROSS] THEN
  EXISTS_TAC
   `\y:real^(1,1)finite_sum.
      ((&1 - drop(fstcart y)) % g(sndcart y) +
       drop(fstcart y) % h(sndcart y):real^N)` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC] THEN
  ASM_REWRITE_TAC[pathstart; pathfinish; REAL_SUB_REFL; REAL_SUB_RZERO] THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - t) % a + t % a:real^N = a`] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN
  REWRITE_TAC[VECTOR_ADD_LID; VECTOR_ADD_RID] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; LIFT_SUB] THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON;
             LINEAR_FSTCART; ETA_AX] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    SIMP_TAC[SNDCART_PASTECART];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `u:real^1`] THEN STRIP_TAC THEN
    SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `u:real^1` THEN
    ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `drop t` THEN
    ASM_MESON_TAC[IN_INTERVAL_1; DROP_VEC]]));;

let HOMOTOPIC_PATHS_NEARBY_EXPLICIT,
    HOMOTOPIC_LOOPS_NEARBY_EXPLICIT = (CONJ_PAIR o prove)
 (`(!g s:real^N->bool h.
        path g /\ path h /\
        pathstart h = pathstart g /\ pathfinish h = pathfinish g /\
        (!t x. t IN interval[vec 0,vec 1] /\ ~(x IN s)
               ==> norm(h t - g t) < norm(g t - x))
        ==> homotopic_paths s g h) /\
   (!g s:real^N->bool h.
        path g /\ path h /\
        pathfinish g = pathstart g /\ pathfinish h = pathstart h /\
        (!t x. t IN interval[vec 0,vec 1] /\ ~(x IN s)
               ==> norm(h t - g t) < norm(g t - x))
        ==> homotopic_loops s g h)`,
  ONCE_REWRITE_TAC[TAUT `p /\ ~q ==> r <=> p /\ ~r ==> q`] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_LINEAR;
    MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; segment; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `t:real^1` THEN
  ASM_REWRITE_TAC[REAL_NOT_LT] THEN
  MP_TAC(ISPECL [`(g:real^1->real^N) t`; `(h:real^1->real^N) t`]
      DIST_IN_CLOSED_SEGMENT) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
  REWRITE_TAC[segment; FORALL_IN_GSPEC;
              ONCE_REWRITE_RULE[DIST_SYM] dist] THEN
  ASM_MESON_TAC[]);;

let HOMOTOPIC_NEARBY_PATHS,HOMOTOPIC_NEARBY_LOOPS = (CONJ_PAIR o prove)
 (`(!g s:real^N->bool.
        path g /\ open s /\ path_image g SUBSET s
        ==> ?e. &0 < e /\
                !h. path h /\
                    pathstart h = pathstart g /\
                    pathfinish h = pathfinish g /\
                    (!t. t IN interval[vec 0,vec 1] ==> norm(h t - g t) < e)
                    ==> homotopic_paths s g h) /\
   (!g s:real^N->bool.
        path g /\ pathfinish g = pathstart g /\ open s /\ path_image g SUBSET s
        ==> ?e. &0 < e /\
                !h. path h /\
                    pathfinish h = pathstart h /\
                    (!t. t IN interval[vec 0,vec 1] ==> norm(h t - g t) < e)
                    ==> homotopic_loops s g h)`,
  CONJ_TAC THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`path_image g:real^N->bool`; `(:real^N) DIFF s`]
        SEPARATE_COMPACT_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_PATH_IMAGE; GSYM OPEN_CLOSED] THEN
  (ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_DIFF; IN_UNIV; dist]]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  REWRITE_TAC[REAL_NOT_LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `h:real^1->real^N` THEN STRIP_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_NEARBY_EXPLICIT;
    MATCH_MP_TAC HOMOTOPIC_LOOPS_NEARBY_EXPLICIT] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real^1`; `x:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e:real` THEN
  ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[path_image] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Homotopy of non-antipodal sphere maps.                                    *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_NON_MIDPOINT_SPHEREMAPS = prove
 (`!f g:real^M->real^N s a r.
        f continuous_on s /\ IMAGE f s SUBSET sphere(a,r) /\
        g continuous_on s /\ IMAGE g s SUBSET sphere(a,r) /\
        (!x. x IN s ==> ~(midpoint(f x,g x) = a))
    ==> homotopic_with (\x. T) (s,sphere(a,r)) f g`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r <= &0` THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
    REPEAT(EXISTS_TAC `g:real^M->real^N`) THEN
    ASM_REWRITE_TAC[HOMOTOPIC_WITH_REFL] THEN
    SUBGOAL_THEN `?c:real^N. sphere(a,r) SUBSET {c}` MP_TAC THENL
     [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_CASES_TAC `r = &0` THEN
    ASM_SIMP_TAC[SPHERE_SING; SPHERE_EMPTY; REAL_LT_LE] THEN
    MESON_TAC[SUBSET_REFL; EMPTY_SUBSET];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `homotopic_with (\z. T) (s:real^M->bool,(:real^N) DELETE a) f g`
  MP_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN
    ASM_REWRITE_TAC[SET_RULE `s SUBSET UNIV DELETE a <=> ~(a IN s)`] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET])) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_SPHERE; IMP_IMP] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
    FIRST_X_ASSUM(MP_TAC o GSYM o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; MIDPOINT_BETWEEN] THEN
    MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o
    ISPECL [`\y:real^N. a + r / norm(y - a) % (y - a)`;
            `sphere(a:real^N,r)`] o
    MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT)) THEN
  REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
      REWRITE_TAC[real_div; o_DEF; LIFT_CMUL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
      SIMP_TAC[IN_DELETE; NORM_EQ_0; VECTOR_SUB_EQ] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_DELETE; IN_SPHERE] THEN
      REWRITE_TAC[NORM_ARITH `dist(a:real^N,a + b) = norm b`] THEN
      SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[real_abs; REAL_LE_RMUL; REAL_DIV_RMUL;
                   NORM_EQ_0; VECTOR_SUB_EQ; REAL_LT_IMP_LE]];
      MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; IN_SPHERE]) THEN
      ASM_SIMP_TAC[NORM_ARITH `norm(a - b:real^N) = dist(b,a)`] THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ] THEN REPEAT STRIP_TAC THEN
      VECTOR_ARITH_TAC]);;

let HOMOTOPIC_NON_ANTIPODAL_SPHEREMAPS = prove
 (`!f g:real^M->real^N s r.
        f continuous_on s /\ IMAGE f s SUBSET sphere(vec 0,r) /\
        g continuous_on s /\ IMAGE g s SUBSET sphere(vec 0,r) /\
        (!x. x IN s ==> ~(f x = --g x))
    ==> homotopic_with (\x. T) (s,sphere(vec 0,r)) f g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_NON_MIDPOINT_SPHEREMAPS THEN
  ASM_REWRITE_TAC[midpoint; VECTOR_ARITH
   `inv(&2) % (a + b):real^N = vec 0 <=> a = --b`]);;

(* ------------------------------------------------------------------------- *)
(* Retracts, in a general sense, preserve (co)homotopic triviality.          *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPICALLY_TRIVIAL_RETRACTION_GEN = prove
 (`!P Q s:real^M->bool t:real^N->bool u:real^P->bool h k.
        (h continuous_on s /\ IMAGE h s = t /\
         k continuous_on t /\ IMAGE k t SUBSET s /\
         (!y. y IN t ==> h(k y) = y) /\
         (!f. f continuous_on u /\ IMAGE f u SUBSET t /\ Q f ==> P(k o f)) /\
         (!f. f continuous_on u /\ IMAGE f u SUBSET s /\ P f ==> Q(h o f)) /\
         (!h k. (!x. x IN u ==> h x = k x) ==> (Q h <=> Q k))) /\
        (!f g. f continuous_on u /\ IMAGE f u SUBSET s /\ P f /\
               g continuous_on u /\ IMAGE g u SUBSET s /\ P g
               ==> homotopic_with P (u,s)  f g)
        ==> (!f g. f continuous_on u /\ IMAGE f u SUBSET t /\ Q f /\
                   g continuous_on u /\ IMAGE g u SUBSET t /\ Q g
                   ==> homotopic_with Q (u,t) f g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`p:real^P->real^N`; `q:real^P->real^N`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`(k:real^N->real^M) o (p:real^P->real^N)`;
    `(k:real^N->real^M) o (q:real^P->real^N)`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[IMAGE_o] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE) THEN ASM_REWRITE_TAC[] THEN
    TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET))) THEN
    ASM SET_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN MAP_EVERY EXISTS_TAC
   [`(h:real^M->real^N) o (k:real^N->real^M) o (p:real^P->real^N)`;
    `(h:real^M->real^N) o (k:real^N->real^M) o (q:real^P->real^N)`] THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_WITH_MONO)) THEN
  ASM_SIMP_TAC[]);;

let HOMOTOPICALLY_TRIVIAL_RETRACTION_NULL_GEN = prove
 (`!P Q s:real^M->bool t:real^N->bool u:real^P->bool h k.
        (h continuous_on s /\ IMAGE h s = t /\
         k continuous_on t /\ IMAGE k t SUBSET s /\
         (!y. y IN t ==> h(k y) = y) /\
         (!f. f continuous_on u /\ IMAGE f u SUBSET t /\ Q f ==> P(k o f)) /\
         (!f. f continuous_on u /\ IMAGE f u SUBSET s /\ P f ==> Q(h o f)) /\
         (!h k. (!x. x IN u ==> h x = k x) ==> (Q h <=> Q k))) /\
        (!f. f continuous_on u /\ IMAGE f u SUBSET s /\ P f
             ==> ?c. homotopic_with P (u,s) f (\x. c))
        ==> (!f. f continuous_on u /\ IMAGE f u SUBSET t /\ Q f
                 ==> ?c. homotopic_with Q (u,t) f (\x. c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `p:real^P->real^N` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC
    `(k:real^N->real^M) o (p:real^P->real^N)`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[IMAGE_o] THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE) THEN ASM_REWRITE_TAC[] THEN
    TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET))) THEN
    ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `c:real^M`)] THEN
  EXISTS_TAC `(h:real^M->real^N) c` THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN MAP_EVERY EXISTS_TAC
   [`(h:real^M->real^N) o (k:real^N->real^M) o (p:real^P->real^N)`;
    `(h:real^M->real^N) o ((\x. c):real^P->real^M)`] THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_WITH_MONO)) THEN
  ASM_SIMP_TAC[]);;

let COHOMOTOPICALLY_TRIVIAL_RETRACTION_GEN = prove
 (`!P Q s:real^M->bool t:real^N->bool u:real^P->bool h k.
        (h continuous_on s /\ IMAGE h s = t /\
         k continuous_on t /\ IMAGE k t SUBSET s /\
         (!y. y IN t ==> h(k y) = y) /\
         (!f. f continuous_on t /\ IMAGE f t SUBSET u /\ Q f ==> P(f o h)) /\
         (!f. f continuous_on s /\ IMAGE f s SUBSET u /\ P f ==> Q(f o k)) /\
         (!h k. (!x. x IN t ==> h x = k x) ==> (Q h <=> Q k))) /\
        (!f g. f continuous_on s /\ IMAGE f s SUBSET u /\ P f /\
               g continuous_on s /\ IMAGE g s SUBSET u /\ P g
               ==> homotopic_with P (s,u) f g)
        ==> (!f g. f continuous_on t /\ IMAGE f t SUBSET u /\ Q f /\
                   g continuous_on t /\ IMAGE g t SUBSET u /\ Q g
                   ==> homotopic_with Q (t,u) f g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`p:real^N->real^P`; `q:real^N->real^P`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`(p:real^N->real^P) o (h:real^M->real^N)`;
    `(q:real^N->real^P) o (h:real^M->real^N)`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[IMAGE_o] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE) THEN ASM_REWRITE_TAC[] THEN
    TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET))) THEN
    ASM SET_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN MAP_EVERY EXISTS_TAC
   [`((p:real^N->real^P) o (h:real^M->real^N)) o (k:real^N->real^M)`;
    `((q:real^N->real^P) o (h:real^M->real^N)) o (k:real^N->real^M)`] THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_WITH_MONO)) THEN
  ASM_SIMP_TAC[]);;

let COHOMOTOPICALLY_TRIVIAL_RETRACTION_NULL_GEN = prove
 (`!P Q s:real^M->bool t:real^N->bool u:real^P->bool h k.
        (h continuous_on s /\ IMAGE h s = t /\
         k continuous_on t /\ IMAGE k t SUBSET s /\
         (!y. y IN t ==> h(k y) = y) /\
         (!f. f continuous_on t /\ IMAGE f t SUBSET u /\ Q f ==> P(f o h)) /\
         (!f. f continuous_on s /\ IMAGE f s SUBSET u /\ P f ==> Q(f o k)) /\
         (!h k. (!x. x IN t ==> h x = k x) ==> (Q h <=> Q k))) /\
        (!f. f continuous_on s /\ IMAGE f s SUBSET u /\ P f
             ==> ?c. homotopic_with P (s,u) f (\x. c))
        ==> (!f. f continuous_on t /\ IMAGE f t SUBSET u /\ Q f
                 ==> ?c. homotopic_with Q (t,u) f (\x. c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `p:real^N->real^P` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC
    `(p:real^N->real^P) o (h:real^M->real^N)`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[IMAGE_o] THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE) THEN ASM_REWRITE_TAC[] THEN
    TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET))) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^P` THEN DISCH_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN MAP_EVERY EXISTS_TAC
   [`((p:real^N->real^P) o (h:real^M->real^N)) o (k:real^N->real^M)`;
    `((\x. c):real^M->real^P) o (k:real^N->real^M)`] THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_WITH_MONO)) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Another useful lemma.                                                     *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_JOIN_SUBPATHS = prove
 (`!g:real^1->real^N s.
       path g /\ path_image g SUBSET s /\
       u IN interval[vec 0,vec 1] /\
       v IN interval[vec 0,vec 1] /\
       w IN interval[vec 0,vec 1]
       ==> homotopic_paths s (subpath u v g ++ subpath v w g) (subpath u w g)`,
  let lemma1 = prove
   (`!g:real^1->real^N s.
         drop u <= drop v /\ drop v <= drop w
         ==> path g /\ path_image g SUBSET s /\
             u IN interval[vec 0,vec 1] /\
             v IN interval[vec 0,vec 1] /\
             w IN interval[vec 0,vec 1] /\
             drop u <= drop v /\ drop v <= drop w
             ==> homotopic_paths s
                 (subpath u v g ++ subpath v w g) (subpath u w g)`,
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_SUBSET THEN
    EXISTS_TAC `path_image g:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `w:real^1 = u` THENL
     [MP_TAC(ISPECL
      [`path_image g:real^N->bool`;
       `subpath u v (g:real^1->real^N)`] HOMOTOPIC_PATHS_RINV) THEN
      ASM_REWRITE_TAC[REVERSEPATH_SUBPATH; SUBPATH_REFL] THEN
      REWRITE_TAC[LINEPATH_REFL; PATHSTART_SUBPATH] THEN
      ASM_SIMP_TAC[PATH_SUBPATH; PATH_IMAGE_SUBPATH_SUBSET];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_REPARAMETRIZE THEN
    ASM_SIMP_TAC[PATH_SUBPATH; PATH_IMAGE_SUBPATH_SUBSET] THEN
    EXISTS_TAC
    `\t. if drop t <= &1 / &2
         then inv(drop(w - u)) % (&2 * drop(v - u)) % t
         else inv(drop(w - u)) %
              ((v - u) + drop(w - v) % (&2 % t - vec 1))` THEN
    REWRITE_TAC[DROP_VEC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_RZERO] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CASES_1 THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; LIFT_DROP; GSYM LIFT_NUM;
                  DROP_ADD; DROP_SUB] THEN
      (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
        [CONTINUOUS_ON_MUL; o_DEF; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID;
         CONTINUOUS_ON_SUB; CONTINUOUS_ON_ADD] THEN
      REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `drop u < drop w` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_LE; DROP_EQ] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC; DROP_ADD; DROP_SUB] THEN
      ONCE_REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
      (CONJ_TAC THENL
        [REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
         REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
         ASM_REAL_ARITH_TAC;
         ALL_TAC]) THEN
      REWRITE_TAC[REAL_ARITH `v - u + x * t <= w - u <=> x * t <= w - v`;
                  REAL_ARITH `(&2 * x) * t = x * &2 * t`] THEN
      MATCH_MP_TAC(REAL_ARITH `a * t <= a * &1 /\ a <= b ==> a * t <= b`) THEN
      (CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL; ALL_TAC]) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; DROP_ADD; DROP_CMUL; DROP_SUB] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_ARITH `(v - u) + (w - v) * &1 = w - u`] THEN
      ASM_SIMP_TAC[REAL_SUB_0; DROP_EQ; REAL_MUL_LINV];
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
      REWRITE_TAC[subpath; joinpaths] THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; DROP_EQ_0; VECTOR_SUB_EQ] THEN
      AP_TERM_TAC THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; DROP_ADD; DROP_CMUL; DROP_SUB] THEN
      REAL_ARITH_TAC]) in
  let lemma2 = prove
   (`path g /\ path_image g SUBSET s /\
     u IN interval[vec 0,vec 1] /\
     v IN interval[vec 0,vec 1] /\
     w IN interval[vec 0,vec 1] /\
     homotopic_paths s (subpath u v g ++ subpath v w g) (subpath u w g)
     ==> homotopic_paths s (subpath w v g ++ subpath v u g) (subpath w u g)`,
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM HOMOTOPIC_PATHS_REVERSEPATH] THEN
    SIMP_TAC[REVERSEPATH_JOINPATHS; PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
    ASM_REWRITE_TAC[REVERSEPATH_SUBPATH]) in
  let lemma3 = prove
   (`path (g:real^1->real^N) /\ path_image g SUBSET s /\
     u IN interval[vec 0,vec 1] /\
     v IN interval[vec 0,vec 1] /\
     w IN interval[vec 0,vec 1] /\
     homotopic_paths s (subpath u v g ++ subpath v w g) (subpath u w g)
     ==> homotopic_paths s (subpath v w g ++ subpath w u g) (subpath v u g)`,
    let tac =
      ASM_MESON_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH; PATH_SUBPATH;
                 HOMOTOPIC_PATHS_REFL; PATH_IMAGE_SUBPATH_SUBSET; SUBSET_TRANS;
                 PATHSTART_JOIN; PATHFINISH_JOIN] in
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM HOMOTOPIC_PATHS_REVERSEPATH] THEN
    SIMP_TAC[REVERSEPATH_JOINPATHS; PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
    ASM_REWRITE_TAC[REVERSEPATH_SUBPATH] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC
     `(subpath u v g ++ subpath v w g) ++ subpath w v g:real^1->real^N` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
      ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
      ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL] THEN tac;
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC
     `subpath u v g ++ (subpath v w g ++ subpath w v g):real^1->real^N` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
      MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN tac;
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC
     `(subpath u v g :real^1->real^N) ++
      linepath(pathfinish(subpath u v g),pathfinish(subpath u v g))` THEN
    CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC HOMOTOPIC_PATHS_RID THEN tac] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    REPEAT CONJ_TAC THENL [tac; ALL_TAC; tac] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC
     `linepath(pathstart(subpath v w g):real^N,pathstart(subpath v w g))` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REVERSEPATH_SUBPATH] THEN
      MATCH_MP_TAC HOMOTOPIC_PATHS_RINV THEN tac;
      ALL_TAC] THEN
    REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH; HOMOTOPIC_PATHS_REFL;
                PATH_LINEPATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL;
                INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_MESON_TAC[path_image; IN_IMAGE; SUBSET]) in
  REPEAT STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (REAL_ARITH `(drop u <= drop v /\ drop v <= drop w \/
                   drop w <= drop v /\ drop v <= drop u) \/
                  (drop u <= drop w /\ drop w <= drop v \/
                   drop v <= drop w /\ drop w <= drop u) \/
                  (drop v <= drop u /\ drop u <= drop w \/
                   drop w <= drop u /\ drop u <= drop v)`) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`g:real^1->real^N`; `s:real^N->bool`] o
    MATCH_MP lemma1) THEN
  ASM_MESON_TAC[lemma2; lemma3]);;

let HOMOTOPIC_LOOPS_SHIFTPATH = prove
 (`!s:real^N->bool p q u.
        homotopic_loops s p q /\ u IN interval[vec 0,vec 1]
        ==> homotopic_loops s (shiftpath u p) (shiftpath u q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_loops; homotopic_with; PCROSS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN DISCH_THEN(
   (X_CHOOSE_THEN `h:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC
   `\z. shiftpath u (\t. (h:real^(1,1)finite_sum->real^N)
                         (pastecart (fstcart z) t)) (sndcart z)` THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; ETA_AX] THEN
  ASM_SIMP_TAC[CLOSED_SHIFTPATH] THEN CONJ_TAC THENL
   [REWRITE_TAC[shiftpath; DROP_ADD; REAL_ARITH
     `u + z <= &1 <=> z <= &1 - u`] THEN
    SUBGOAL_THEN
     `{ pastecart (t:real^1) (x:real^1) |
        t IN interval[vec 0,vec 1] /\ x IN interval[vec 0,vec 1]} =
      { pastecart (t:real^1) (x:real^1) |
        t IN interval[vec 0,vec 1] /\ x IN interval[vec 0,vec 1 - u]} UNION
      { pastecart (t:real^1) (x:real^1) |
        t IN interval[vec 0,vec 1] /\ x IN interval[vec 1 - u,vec 1]}`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE `s UNION s' = u
        ==> {f t x | t IN i /\ x IN u} =
            {f t x | t IN i /\ x IN s} UNION
            {f t x | t IN i /\ x IN s'}`) THEN
      UNDISCH_TAC `(u:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[EXTENSION; IN_INTERVAL_1; IN_UNION; DROP_SUB; DROP_VEC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    SIMP_TAC[REWRITE_RULE[PCROSS] CLOSED_PCROSS; CLOSED_INTERVAL] THEN
    REWRITE_TAC[FORALL_AND_THM; FORALL_IN_GSPEC; TAUT
     `p /\ q \/ r /\ s ==> t <=> (p ==> q ==> t) /\ (r ==> s ==> t)`] THEN
    SIMP_TAC[SNDCART_PASTECART; IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN
    SIMP_TAC[REAL_ARITH `&1 - u <= x ==> (x <= &1 - u <=> x = &1 - u)`] THEN
    SIMP_TAC[GSYM LIFT_EQ; LIFT_SUB; LIFT_DROP; LIFT_NUM] THEN
    REWRITE_TAC[FSTCART_PASTECART; VECTOR_ARITH `u + v - u:real^N = v`;
                VECTOR_ARITH `u + v - u - v:real^N = vec 0`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_SIMP_TAC[GSYM IN_INTERVAL_1; GSYM DROP_VEC] THEN CONJ_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST;
             LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART;
             VECTOR_ARITH `u + z - v:real^N = (u - v) + z`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN
    UNDISCH_TAC `(u:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1;
                IN_ELIM_PASTECART_THM; DROP_ADD; DROP_SUB; DROP_VEC] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; SET_RULE
     `(!t x. t IN i /\ x IN i ==> f t x IN s) <=>
      (!t. t IN i ==> IMAGE (f t) i SUBSET s)`] THEN
    X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN REWRITE_TAC[GSYM path_image] THEN
    ASM_SIMP_TAC[PATH_IMAGE_SHIFTPATH; ETA_AX] THEN
    REWRITE_TAC[path_image] THEN ASM SET_TAC[]]);;

let HOMOTOPIC_PATHS_LOOP_PARTS = prove
 (`!s p q a:real^N.
        homotopic_loops s (p ++ reversepath q) (linepath(a,a)) /\ path q
        ==> homotopic_paths s p q`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
    MATCH_MP HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL) THEN
  REWRITE_TAC[PATHSTART_JOIN] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP HOMOTOPIC_PATHS_IMP_PATH) THEN
  ASM_CASES_TAC `pathfinish p:real^N = pathstart(reversepath q)` THENL
   [ASM_SIMP_TAC[PATH_JOIN; PATH_REVERSEPATH] THEN STRIP_TAC;
    ASM_MESON_TAC[PATH_JOIN_PATH_ENDS; PATH_REVERSEPATH]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PATHSTART_REVERSEPATH]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_SUBSET) THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
    PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH; UNION_SUBSET; SING_SUBSET;
    PATH_IMAGE_REVERSEPATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `p ++ (linepath(pathfinish p:real^N,pathfinish p))` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_RID THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `p ++ (reversepath q ++ q):real^1->real^N` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_SIMP_TAC[HOMOTOPIC_PATHS_LINV; PATHSTART_JOIN; PATHSTART_REVERSEPATH;
                 HOMOTOPIC_PATHS_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `(p ++ reversepath q) ++ q:real^1->real^N` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
    ASM_REWRITE_TAC[PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                    PATH_IMAGE_REVERSEPATH; PATH_REVERSEPATH];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `linepath(pathstart p:real^N,pathstart p) ++ q` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL] THEN
    REWRITE_TAC[PATHFINISH_JOIN; PATHFINISH_REVERSEPATH];
    FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHFINISH) THEN
    REWRITE_TAC[PATHFINISH_JOIN; PATHFINISH_LINEPATH;
                PATHFINISH_REVERSEPATH] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_LID THEN ASM_REWRITE_TAC[]]);;

let HOMOTOPIC_LOOPS_ADD_SYM = prove
 (`!p q:real^1->real^N.
        path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p /\
        path q /\ path_image q SUBSET s /\ pathfinish q = pathstart q /\
        pathstart q = pathstart p
        ==> homotopic_loops s (p ++ q) (q ++ p)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  SUBGOAL_THEN `lift(&1 / &2) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  EXISTS_TAC `shiftpath (lift(&1 / &2)) (p ++ q:real^1->real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_SHIFTPATH_SELF;
    MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ] THEN
  ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
               UNION_SUBSET; IN_INTERVAL_1; DROP_VEC; LIFT_DROP;
               PATH_SHIFTPATH; PATH_IMAGE_SHIFTPATH; CLOSED_SHIFTPATH] THEN
  SIMP_TAC[shiftpath; joinpaths; LIFT_DROP; DROP_ADD; DROP_SUB; DROP_VEC;
           REAL_ARITH `&0 <= t ==> (a + t <= a <=> t = &0)`;
           REAL_ARITH `t <= &1 ==> &1 / &2 + t - &1 <= &1 / &2`;
           REAL_ARITH `&1 / &2 + t <= &1 <=> t <= &1 / &2`] THEN
  X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
  ASM_CASES_TAC `drop t <= &1 / &2` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[GSYM LIFT_EQ; LIFT_NUM; LIFT_DROP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_ADD_RID] THENL
     [REWRITE_TAC[GSYM LIFT_CMUL; VECTOR_MUL_RZERO] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_MESON_TAC[LIFT_NUM; pathstart; pathfinish];
      ALL_TAC];
    ALL_TAC] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_SUB; DROP_ADD; DROP_VEC; DROP_CMUL;
              LIFT_DROP] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Simply connected sets defined as "all loops are homotopic (as loops)".    *)
(* ------------------------------------------------------------------------- *)

let simply_connected = new_definition
 `simply_connected(s:real^N->bool) <=>
        !p q. path p /\ pathfinish p = pathstart p /\ path_image p SUBSET s /\
              path q /\ pathfinish q = pathstart q /\ path_image q SUBSET s
              ==> homotopic_loops s p q`;;

let SIMPLY_CONNECTED_EMPTY = prove
 (`simply_connected {}`,
  REWRITE_TAC[simply_connected; SUBSET_EMPTY] THEN
  MESON_TAC[PATH_IMAGE_NONEMPTY]);;

let SIMPLY_CONNECTED_IMP_PATH_CONNECTED = prove
 (`!s:real^N->bool. simply_connected s ==> path_connected s`,
  REWRITE_TAC[simply_connected; PATH_CONNECTED_EQ_HOMOTOPIC_POINTS] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                  PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN
  ASM SET_TAC[]);;

let SIMPLY_CONNECTED_IMP_CONNECTED = prove
 (`!s:real^N->bool. simply_connected s ==> connected s`,
  SIMP_TAC[SIMPLY_CONNECTED_IMP_PATH_CONNECTED;
           PATH_CONNECTED_IMP_CONNECTED]);;

let SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY = prove
 (`!s:real^N->bool.
        simply_connected s <=>
        !p a. path p /\ path_image p SUBSET s /\
              pathfinish p = pathstart p /\ a IN s
              ==> homotopic_loops s p (linepath(a,a))`,
  GEN_TAC THEN REWRITE_TAC[simply_connected] THEN EQ_TAC THEN DISCH_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET];
    MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `q:real^1->real^N`] THEN
    STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `linepath(pathstart p:real^N,pathstart p)` THEN
    CONJ_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]]);;

let SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_SOME = prove
 (`!s:real^N->bool.
        simply_connected s <=>
        path_connected s /\
        !p. path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
            ==> ?a. a IN s /\ homotopic_loops s p (linepath(a,a))`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SIMPLY_CONNECTED_IMP_PATH_CONNECTED] THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY]) THEN
    MESON_TAC[SUBSET; PATHSTART_IN_PATH_IMAGE];
    REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY] THEN
    MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `a:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:real^1->real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `b:real^N` THEN
    STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `linepath(b:real^N,b)` THEN
    ASM_REWRITE_TAC[HOMOTOPIC_POINTS_EQ_PATH_COMPONENT] THEN
    ASM_MESON_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT]]);;

let SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ALL = prove
 (`!s:real^N->bool.
        simply_connected s <=>
        s = {} \/
        ?a. a IN s /\
            !p. path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
                ==> homotopic_loops s p (linepath(a,a))`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SIMPLY_CONNECTED_EMPTY] THEN
  REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_SOME] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:real^1->real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:real^1->real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `b:real^N` THEN
    STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `linepath(b:real^N,b)` THEN
    ASM_REWRITE_TAC[HOMOTOPIC_POINTS_EQ_PATH_COMPONENT] THEN
    ASM_MESON_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT];
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[PATH_CONNECTED_EQ_HOMOTOPIC_POINTS] THEN
    MAP_EVERY X_GEN_TAC [`b:real^N`; `c:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `linepath(a:real^N,a)` THEN
    GEN_REWRITE_TAC RAND_CONV [HOMOTOPIC_LOOPS_SYM] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL;
                PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ASM SET_TAC[]]);;

let SIMPLY_CONNECTED_EQ_CONTRACTIBLE_PATH = prove
 (`!s:real^N->bool.
        simply_connected s <=>
        path_connected s /\
        !p. path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
            ==> homotopic_paths s p (linepath(pathstart p,pathstart p))`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [ASM_SIMP_TAC[SIMPLY_CONNECTED_IMP_PATH_CONNECTED] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL THEN
    EXISTS_TAC `pathstart p :real^N` THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o
      REWRITE_RULE[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY]) THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET];
    REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY] THEN
    MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `a:real^N`] THEN
    STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `linepath(pathstart p:real^N,pathfinish p)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
      ASM_SIMP_TAC[PATHFINISH_LINEPATH];
      ASM_REWRITE_TAC[HOMOTOPIC_POINTS_EQ_PATH_COMPONENT] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[PATH_CONNECTED_IFF_PATH_COMPONENT]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]]]);;

let SIMPLY_CONNECTED_EQ_HOMOTOPIC_PATHS = prove
 (`!s:real^N->bool.
        simply_connected s <=>
        path_connected s /\
        !p q. path p /\ path_image p SUBSET s /\
              path q /\ path_image q SUBSET s /\
              pathstart q = pathstart p /\ pathfinish q = pathfinish p
              ==> homotopic_paths s p q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_PATH] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:real^1->real^N` THENL
   [X_GEN_TAC `q:real^1->real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p ++ reversepath q :real^1->real^N`) THEN
    ASM_SIMP_TAC[PATH_JOIN; PATHSTART_REVERSEPATH; PATH_REVERSEPATH;
                 PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_REVERSEPATH;
                 PATH_IMAGE_JOIN; UNION_SUBSET; PATH_IMAGE_REVERSEPATH] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `p ++ linepath(pathfinish p,pathfinish p):real^1->real^N` THEN
    GEN_REWRITE_TAC LAND_CONV [HOMOTOPIC_PATHS_SYM] THEN
    ASM_SIMP_TAC[HOMOTOPIC_PATHS_RID] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `p ++ (reversepath q ++ q):real^1->real^N` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
      ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATHSTART_LINEPATH] THEN
      ASM_MESON_TAC[HOMOTOPIC_PATHS_LINV; HOMOTOPIC_PATHS_SYM];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `(p ++ reversepath q) ++ q:real^1->real^N` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
      ASM_SIMP_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH] THEN
      ASM_REWRITE_TAC[PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `linepath(pathstart q,pathstart q) ++ q:real^1->real^N` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
      ASM_SIMP_TAC[HOMOTOPIC_PATHS_RINV; HOMOTOPIC_PATHS_REFL] THEN
      ASM_REWRITE_TAC[PATHFINISH_JOIN; PATHFINISH_REVERSEPATH];
      ASM_MESON_TAC[HOMOTOPIC_PATHS_LID]];
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_LINEPATH] THEN
    REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]]);;

let SIMPLY_CONNECTED_RETRACTION_GEN = prove
 (`!s:real^M->bool t:real^N->bool h k.
        h continuous_on s /\ IMAGE h s = t /\
        k continuous_on t /\ IMAGE k t SUBSET s /\
        (!y. y IN t ==> h(k y) = y) /\
        simply_connected s
        ==> simply_connected t`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[simply_connected; path; path_image; homotopic_loops] THEN
  ONCE_REWRITE_TAC[TAUT
   `a /\ b /\ c /\ a' /\ b' /\ c' <=> a /\ c /\ b /\ a' /\ c' /\ b'`] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
    HOMOTOPICALLY_TRIVIAL_RETRACTION_GEN) THEN
  MAP_EVERY EXISTS_TAC [`h:real^M->real^N`; `k:real^N->real^M`] THEN
  ASM_SIMP_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
  REWRITE_TAC[pathfinish; pathstart] THEN MESON_TAC[ENDS_IN_UNIT_INTERVAL]);;

let HOMEOMORPHIC_SIMPLY_CONNECTED = prove
 (`!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\ simply_connected s
        ==> simply_connected t`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
   (REWRITE_RULE[CONJ_ASSOC] SIMPLY_CONNECTED_RETRACTION_GEN)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  SIMP_TAC[homeomorphism; SUBSET_REFL]);;

let HOMEOMORPHIC_SIMPLY_CONNECTED_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        s homeomorphic t
        ==> (simply_connected s <=> simply_connected t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOMEOMORPHIC_SIMPLY_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  ASM_REWRITE_TAC[]);;

let SIMPLY_CONNECTED_TRANSLATION = prove
 (`!a:real^N s. simply_connected (IMAGE (\x. a + x) s) <=> simply_connected s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_SIMPLY_CONNECTED_EQ THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION]);;

add_translation_invariants [SIMPLY_CONNECTED_TRANSLATION];;

let SIMPLY_CONNECTED_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (simply_connected (IMAGE f s) <=> simply_connected s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_SIMPLY_CONNECTED_EQ THEN
  ASM_MESON_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_LEFT_EQ;
                HOMEOMORPHIC_REFL]);;

add_linear_invariants [SIMPLY_CONNECTED_INJECTIVE_LINEAR_IMAGE];;

let SIMPLY_CONNECTED_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        simply_connected s /\ simply_connected t
        ==> simply_connected(s PCROSS t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY] THEN
  REWRITE_TAC[path; path_image; pathstart; pathfinish; FORALL_PASTECART] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`p:real^1->real^(M,N)finite_sum`; `a:real^M`; `b:real^N`] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; FORALL_IN_IMAGE; SUBSET] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2
   (MP_TAC o SPECL [`fstcart o (p:real^1->real^(M,N)finite_sum)`; `a:real^M`])
   (MP_TAC o SPECL [`sndcart o (p:real^1->real^(M,N)finite_sum)`;
                    `b:real^N`])) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_COMPOSE; LINEAR_FSTCART; LINEAR_SNDCART;
               LINEAR_CONTINUOUS_ON; homotopic_loops; homotopic_with;
               pathfinish; pathstart; IMAGE_o; o_THM] THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[PCROSS; IN_ELIM_THM]) THEN
    ASM_MESON_TAC[SNDCART_PASTECART];
    DISCH_THEN(X_CHOOSE_THEN
      `k:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC)] THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[PCROSS; IN_ELIM_THM]) THEN
    ASM_MESON_TAC[FSTCART_PASTECART];
    DISCH_THEN(X_CHOOSE_THEN
      `h:real^(1,1)finite_sum->real^M` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC
   `(\z. pastecart (h z) (k z))
    :real^(1,1)finite_sum->real^(M,N)finite_sum` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_PASTECART; ETA_AX] THEN
  REWRITE_TAC[LINEPATH_REFL; PASTECART_FST_SND] THEN
  ASM_SIMP_TAC[PASTECART_IN_PCROSS]);;

let SIMPLY_CONNECTED_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        simply_connected(s PCROSS t) <=>
        s = {} \/ t = {} \/ simply_connected s /\ simply_connected t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; SIMPLY_CONNECTED_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; SIMPLY_CONNECTED_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[SIMPLY_CONNECTED_PCROSS] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY] THEN
    MAP_EVERY X_GEN_TAC [`p:real^1->real^M`; `a:real^M`] THEN
    REWRITE_TAC[path; path_image; pathstart; pathfinish; SUBSET;
                FORALL_IN_IMAGE] THEN
    STRIP_TAC THEN UNDISCH_TAC `~(t:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`(\t. pastecart (p t) (b)):real^1->real^(M,N)finite_sum`;
      `pastecart (a:real^M) (b:real^N)`]) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    ASM_SIMP_TAC[path; path_image; pathstart; pathfinish; SUBSET;
                 FORALL_IN_IMAGE; PASTECART_IN_PCROSS; PASTECART_INJ;
                 CONTINUOUS_ON_PASTECART; ETA_AX; CONTINUOUS_ON_CONST] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL
     [`(\t. pastecart (p t) b):real^1->real^(M,N)finite_sum`;
      `linepath (pastecart (a:real^M) (b:real^N),pastecart a b)`;
      `fstcart:real^(M,N)finite_sum->real^M`;
      `(s:real^M->bool) PCROSS (t:real^N->bool)`; `s:real^M->bool`]
        HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE) THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
    SIMP_TAC[o_DEF; LINEPATH_REFL; FSTCART_PASTECART; ETA_AX;
             SUBSET; FORALL_IN_PCROSS; FORALL_IN_IMAGE];
    REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY] THEN
    MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `b:real^N`] THEN
    REWRITE_TAC[path; path_image; pathstart; pathfinish; SUBSET;
                FORALL_IN_IMAGE] THEN
    STRIP_TAC THEN UNDISCH_TAC `~(s:real^M->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^M` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`(\t. pastecart a (p t)):real^1->real^(M,N)finite_sum`;
      `pastecart (a:real^M) (b:real^N)`]) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    ASM_SIMP_TAC[path; path_image; pathstart; pathfinish; SUBSET;
                 FORALL_IN_IMAGE; PASTECART_IN_PCROSS; PASTECART_INJ;
                 CONTINUOUS_ON_PASTECART; ETA_AX; CONTINUOUS_ON_CONST] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL
     [`(\t. pastecart a (p t)):real^1->real^(M,N)finite_sum`;
      `linepath (pastecart (a:real^M) (b:real^N),pastecart a b)`;
      `sndcart:real^(M,N)finite_sum->real^N`;
      `(s:real^M->bool) PCROSS (t:real^N->bool)`; `t:real^N->bool`]
        HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE) THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    SIMP_TAC[o_DEF; LINEPATH_REFL; SNDCART_PASTECART; ETA_AX;
             SUBSET; FORALL_IN_PCROSS; FORALL_IN_IMAGE]]);;

(* ------------------------------------------------------------------------- *)
(* A mapping out of a sphere is nullhomotopic iff it extends to the ball.    *)
(* This even works out in the degenerate cases when the radius is <= 0, and  *)
(* we also don't need to explicitly assume continuity since it's already     *)
(* implicit in both sides of the equivalence.                                *)
(* ------------------------------------------------------------------------- *)

let NULLHOMOTOPIC_FROM_SPHERE_EXTENSION = prove
 (`!f:real^M->real^N s a r.
        (?c. homotopic_with (\x. T) (sphere(a,r),s) f (\x. c)) <=>
        (?g. g continuous_on cball(a,r) /\ IMAGE g (cball(a,r)) SUBSET s /\
             !x. x IN sphere(a,r) ==> g x = f x)`,
  let lemma = prove
   (`!f:real^M->real^N g a r.
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !x. ~(x = a) /\ norm(x - a) < d ==> norm(g x - f a) < e) /\
        g continuous_on (cball(a,r) DELETE a) /\
        (!x. x IN cball(a,r) /\ ~(x = a) ==> f x = g x)
        ==> f continuous_on cball(a,r)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_CBALL; dist] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x:real^M = a` THENL
     [ASM_REWRITE_TAC[continuous_within; IN_CBALL; dist] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_CBALL; dist]) THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `y:real^M` THEN ASM_CASES_TAC `y:real^M = a` THEN
      ASM_MESON_TAC[VECTOR_SUB_REFL; NORM_0];
      MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
      EXISTS_TAC `g:real^M->real^N` THEN EXISTS_TAC `norm(x - a:real^M)` THEN
      ASM_SIMP_TAC[NORM_POS_LT; VECTOR_SUB_EQ; IN_CBALL; dist] THEN
      CONJ_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[IN_CBALL; dist]);
        UNDISCH_TAC
         `(g:real^M->real^N) continuous_on (cball(a,r) DELETE a)` THEN
        REWRITE_TAC[continuous_on; continuous_within] THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
        ASM_REWRITE_TAC[IN_DELETE; IN_CBALL; dist] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
        ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `min d (norm(x - a:real^M))` THEN
        ASM_REWRITE_TAC[REAL_LT_MIN; NORM_POS_LT; VECTOR_SUB_EQ]] THEN
       ASM_MESON_TAC[NORM_SUB; NORM_ARITH
        `norm(y - x:real^N) < norm(x - a) ==> ~(y = a)`]]) in
  REWRITE_TAC[sphere; ONCE_REWRITE_RULE[DIST_SYM] dist] THEN
  REPEAT GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `r < &0 \/ r = &0 \/ &0 < r`)
  THENL
   [ASM_SIMP_TAC[NORM_ARITH `r < &0 ==> ~(norm x = r)`] THEN
    FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [GSYM CBALL_EQ_EMPTY]) THEN
    ASM_SIMP_TAC[HOMOTOPIC_WITH; IMAGE_CLAUSES; EMPTY_GSPEC; NOT_IN_EMPTY;
       PCROSS; SET_RULE `{f t x |x,t| F} = {}`; EMPTY_SUBSET] THEN
    REWRITE_TAC[CONTINUOUS_ON_EMPTY];
    ASM_SIMP_TAC[NORM_EQ_0; VECTOR_SUB_EQ; CBALL_SING] THEN
    SIMP_TAC[HOMOTOPIC_WITH; PCROSS; FORALL_IN_GSPEC; FORALL_UNWIND_THM2] THEN
    ASM_CASES_TAC `(f:real^M->real^N) a IN s` THENL
     [MATCH_MP_TAC(TAUT `p /\ q ==> (p <=> q)`) THEN CONJ_TAC THENL
       [EXISTS_TAC `(f:real^M->real^N) a` THEN
        EXISTS_TAC `\y:real^(1,M)finite_sum. (f:real^M->real^N) a` THEN
        ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; SUBSET; FORALL_IN_IMAGE];
        EXISTS_TAC `f:real^M->real^N` THEN REWRITE_TAC[CONTINUOUS_ON_SING] THEN
        ASM SET_TAC[]];
      MATCH_MP_TAC(TAUT `~q /\ ~p ==> (p <=> q)`) THEN CONJ_TAC THENL
       [ASM SET_TAC[]; STRIP_TAC] THEN
      UNDISCH_TAC `~((f:real^M->real^N) a IN s)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE h t SUBSET s ==> (?y. y IN t /\ z = h y) ==> z IN s`)) THEN
      REWRITE_TAC[EXISTS_IN_GSPEC] THEN
      EXISTS_TAC `vec 0:real^1` THEN ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL] THEN
      ASM_REWRITE_TAC[EXISTS_IN_GSPEC; UNWIND_THM2]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT
   `!p. (q ==> p) /\ (r ==> p) /\ (p ==> (q <=> r)) ==> (q <=> r)`) THEN
  EXISTS_TAC
   `(f:real^M->real^N) continuous_on {x | norm(x - a) = r} /\
    IMAGE f {x | norm(x - a) = r} SUBSET s` THEN
  REPEAT CONJ_TAC THENL
   [STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `g:real^M->real^N` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `cball(a:real^M,r)`;
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `IMAGE g t SUBSET s
         ==> u SUBSET t /\ (!x. x IN u ==> f x = g x)
             ==> IMAGE f u SUBSET s`)) THEN
      ASM_SIMP_TAC[]] THEN
    ASM_SIMP_TAC[SUBSET; IN_CBALL; dist; IN_ELIM_THM] THEN
    MESON_TAC[REAL_LE_REFL; NORM_SUB];
    STRIP_TAC] THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN EQ_TAC THENL
   [REWRITE_TAC[homotopic_with; PCROSS; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`c:real^N`; `h:real^(1,M)finite_sum->real^N`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `\x. (h:real^(1,M)finite_sum->real^N)
                    (pastecart (lift(inv(r) * norm(x - a)))
                               (a + (if x = a then r % basis 1
                                     else r / norm(x - a) % (x - a))))` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REAL_MUL_LINV; REAL_DIV_REFL; REAL_LT_IMP_NZ;
                 LIFT_NUM; VECTOR_ARITH `a + &1 % (x - a):real^N = x`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC lemma THEN
      EXISTS_TAC `\x. (h:real^(1,M)finite_sum->real^N)
                    (pastecart (lift(inv(r) * norm(x - a)))
                               (a + r / norm(x - a) % (x - a)))` THEN
      SIMP_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_MUL_RZERO; LIFT_NUM] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          COMPACT_UNIFORMLY_CONTINUOUS)) THEN
        SIMP_TAC[REWRITE_RULE[PCROSS] COMPACT_PCROSS;
            REWRITE_RULE[REWRITE_RULE[ONCE_REWRITE_RULE[DIST_SYM] dist] sphere]
                 COMPACT_SPHERE; COMPACT_INTERVAL] THEN
        REWRITE_TAC[uniformly_continuous_on] THEN
        DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
        REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
        DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `min r (d * r):real` THEN
        ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_MIN] THEN
        X_GEN_TAC `x:real^M` THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^1`) THEN
        REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; RIGHT_IMP_FORALL_THM] THEN
        ASM_REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
         `(!x t y. P x t y) ==> (!t x. P x t x)`)) THEN
        REWRITE_TAC[dist] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
        ASM_SIMP_TAC[REAL_MUL_LID; REAL_MUL_LZERO; NORM_POS_LE] THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; CONJ_ASSOC] THEN
        REWRITE_TAC[VECTOR_ADD_SUB; NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
        ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
        REWRITE_TAC[PASTECART_SUB; VECTOR_SUB_REFL; NORM_PASTECART] THEN
        REWRITE_TAC[NORM_0; VECTOR_SUB_RZERO] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_ADD_RID] THEN
        REWRITE_TAC[POW_2_SQRT_ABS; REAL_ABS_NORM; NORM_LIFT] THEN
        ASM_SIMP_TAC[REAL_ABS_DIV; REAL_LT_LDIV_EQ; REAL_ABS_NORM;
                     REAL_ARITH `&0 < r ==> abs r = r`];
        GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
          SIMP_TAC[CONTINUOUS_ON_CMUL; LIFT_CMUL; CONTINUOUS_ON_SUB;
                   CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST;
                   CONTINUOUS_ON_LIFT_NORM_COMPOSE] THEN
          MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
          REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
          MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
          SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST;
                   o_DEF; real_div; LIFT_CMUL] THEN
          MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
          REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
          GEN_TAC THEN REWRITE_TAC[IN_DELETE] THEN DISCH_TAC THEN
          MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
          MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_INV) THEN
          ASM_SIMP_TAC[NETLIMIT_AT; NORM_EQ_0; VECTOR_SUB_EQ] THEN
          MATCH_MP_TAC CONTINUOUS_LIFT_NORM_COMPOSE THEN
          SIMP_TAC[CONTINUOUS_SUB; CONTINUOUS_AT_ID; CONTINUOUS_CONST];
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC; SUBSET] THEN
          REWRITE_TAC[IN_ELIM_PASTECART_THM; IN_DELETE; IN_ELIM_THM] THEN
          SIMP_TAC[IN_CBALL; NORM_ARITH `dist(a:real^M,a + x) = norm x`] THEN
          REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] dist] THEN
          REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
          REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
          ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
          ASM_SIMP_TAC[REAL_MUL_LID; REAL_MUL_LZERO; NORM_POS_LE] THEN
          SIMP_TAC[VECTOR_ADD_SUB; NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM;
                   REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
          ASM_REAL_ARITH_TAC]];
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
      REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE g s SUBSET u ==> t SUBSET s ==> IMAGE g t SUBSET u`)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[IN_ELIM_PASTECART_THM; IN_CBALL; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^M` THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] dist] THEN REPEAT STRIP_TAC THENL
       [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
        ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO; NORM_POS_LE];
        REWRITE_TAC[VECTOR_ADD_SUB] THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL;
                     REAL_ABS_DIV; REAL_ABS_NORM;
                     REAL_MUL_RID; REAL_ARITH `&0 < r ==> abs r = r`] THEN
        ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ]];
      GEN_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[VECTOR_SUB_REFL; NORM_0; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[VECTOR_ARITH `a + &1 % (x - a):real^N = x`]];
    DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(g:real^M->real^N) a` THEN
    ASM_SIMP_TAC[HOMOTOPIC_WITH; PCROSS] THEN
    EXISTS_TAC `\y:real^(1,M)finite_sum.
                   (g:real^M->real^N)
                   (a + drop(fstcart y) % (sndcart y - a))` THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID] THEN
    ASM_SIMP_TAC[VECTOR_SUB_ADD2] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN SIMP_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
        SIMP_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST;
                 LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; LINEAR_FSTCART; ETA_AX];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET))];
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
      REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE g s SUBSET u ==> t SUBSET s ==> IMAGE g t SUBSET u`))] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_ELIM_THM] THEN
    REWRITE_TAC[IN_CBALL; NORM_ARITH `dist(a:real^M,a + x) = norm x`] THEN
    ASM_SIMP_TAC[NORM_MUL; IN_INTERVAL_1; DROP_VEC; REAL_LE_RMUL_EQ;
                 REAL_ARITH `x * r <= r <=> x * r <= &1 * r`] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Homotopy equivalence.                                                     *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("homotopy_equivalent",(12,"right"));;

let homotopy_equivalent = new_definition
 `(s:real^M->bool) homotopy_equivalent (t:real^N->bool) <=>
        ?f g. f continuous_on s /\ IMAGE f s SUBSET t /\
              g continuous_on t /\ IMAGE g t SUBSET s /\
              homotopic_with (\x. T) (s,s) (g o f) I /\
              homotopic_with (\x. T) (t,t) (f o g) I`;;

let HOMOTOPY_EQUIVALENT = prove
 (`!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t <=>
        ?f g h. f continuous_on s /\ IMAGE f s SUBSET t /\
                g continuous_on t /\ IMAGE g t SUBSET s /\
                h continuous_on t /\ IMAGE h t SUBSET s /\
                homotopic_with (\x. T) (s,s) (g o f) I /\
                homotopic_with (\x. T) (t,t) (f o h) I`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopy_equivalent] THEN
  MATCH_MP_TAC(MESON[] `(!x. P x <=> Q x) ==> ((?x. P x) <=> (?x. Q x))`) THEN
  X_GEN_TAC `f:real^M->real^N` THEN
  EQ_TAC THENL [MESON_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC `(g:real^N->real^M) o f o (h:real^N->real^M)` THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
    REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
    ASM SET_TAC[];
    TRANS_TAC HOMOTOPIC_WITH_TRANS
      `((g:real^N->real^M) o I) o (f:real^M->real^N)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[I_O_ID]] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
    TRANS_TAC HOMOTOPIC_WITH_TRANS
      `(f:real^M->real^N) o I o (h:real^N->real^M)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[I_O_ID]] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[o_ASSOC] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[]]);;

let HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT = prove
 (`!s:real^M->bool t:real^N->bool.
        s homeomorphic t ==> s homotopy_equivalent t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[homeomorphic; homotopy_equivalent; homeomorphism] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  CONJ_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQUAL THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_COMPOSE; IMAGE_o; o_THM; I_THM; SUBSET_REFL]);;

let HOMOTOPY_EQUIVALENT_REFL = prove
 (`!s:real^N->bool. s homotopy_equivalent s`,
  SIMP_TAC[HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT; HOMEOMORPHIC_REFL]);;

let HOMOTOPY_EQUIVALENT_SYM = prove
 (`!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t <=> t homotopy_equivalent s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopy_equivalent] THEN
  GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN CONV_TAC TAUT);;

let HOMOTOPY_EQUIVALENT_TRANS = prove
 (`!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homotopy_equivalent t /\ t homotopy_equivalent u
        ==> s homotopy_equivalent u`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[homotopy_equivalent; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  SIMP_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`f1:real^M->real^N`; `g1:real^N->real^M`;
    `f2:real^N->real^P`; `g2:real^P->real^N`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(f2:real^N->real^P) o (f1:real^M->real^N)`;
    `(g1:real^N->real^M) o (g2:real^P->real^N)`] THEN
  REWRITE_TAC[IMAGE_o] THEN
  REPLICATE_TAC 2
   (CONJ_TAC THENL
    [ASM_MESON_TAC[CONTINUOUS_ON_COMPOSE; CONTINUOUS_ON_SUBSET];ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  CONJ_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THENL
   [EXISTS_TAC `(g1:real^N->real^M) o I o (f1:real^M->real^N)`;
    EXISTS_TAC `(f2:real^N->real^P) o I o (g2:real^P->real^N)`] THEN
  (CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[I_O_ID]]) THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[o_ASSOC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_SELF = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (IMAGE f s) homotopy_equivalent s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT THEN
  MATCH_MP_TAC HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF THEN
  ASM_REWRITE_TAC[]);;

let HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_LEFT_EQ = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ((IMAGE f s) homotopy_equivalent t <=> s homotopy_equivalent t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o SPEC `s:real^M->bool` o
    MATCH_MP HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_SELF) THEN
  EQ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMOTOPY_EQUIVALENT_SYM]);
    POP_ASSUM MP_TAC] THEN
  REWRITE_TAC[IMP_IMP; HOMOTOPY_EQUIVALENT_TRANS]);;

let HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_RIGHT_EQ = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (s homotopy_equivalent (IMAGE f t) <=> s homotopy_equivalent t)`,
  ONCE_REWRITE_TAC[HOMOTOPY_EQUIVALENT_SYM] THEN
  REWRITE_TAC[HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_LEFT_EQ]);;

add_linear_invariants
  [HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_LEFT_EQ;
   HOMOTOPY_EQUIVALENT_INJECTIVE_LINEAR_IMAGE_RIGHT_EQ];;

let HOMOTOPY_EQUIVALENT_TRANSLATION_SELF = prove
 (`!a:real^N s. (IMAGE (\x. a + x) s) homotopy_equivalent s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION_SELF]);;

let HOMOTOPY_EQUIVALENT_TRANSLATION_LEFT_EQ = prove
 (`!a:real^N s t.
      (IMAGE (\x. a + x) s) homotopy_equivalent t <=> s homotopy_equivalent t`,
  MESON_TAC[HOMOTOPY_EQUIVALENT_TRANSLATION_SELF;
            HOMOTOPY_EQUIVALENT_SYM; HOMOTOPY_EQUIVALENT_TRANS]);;

let HOMOTOPY_EQUIVALENT_TRANSLATION_RIGHT_EQ = prove
 (`!a:real^N s t.
      s homotopy_equivalent (IMAGE (\x. a + x) t) <=> s homotopy_equivalent t`,
  ONCE_REWRITE_TAC[HOMOTOPY_EQUIVALENT_SYM] THEN
  REWRITE_TAC[HOMOTOPY_EQUIVALENT_TRANSLATION_LEFT_EQ]);;

add_translation_invariants
  [HOMOTOPY_EQUIVALENT_TRANSLATION_LEFT_EQ;
   HOMOTOPY_EQUIVALENT_TRANSLATION_RIGHT_EQ];;

let HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY = prove
  (`!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homotopy_equivalent t
        ==> ((!f g. f continuous_on u /\ IMAGE f u SUBSET s /\
                    g continuous_on u /\ IMAGE g u SUBSET s
                    ==> homotopic_with (\x. T) (u,s) f g) <=>
             (!f g. f continuous_on u /\ IMAGE f u SUBSET t /\
                    g continuous_on u /\ IMAGE g u SUBSET t
                    ==> homotopic_with (\x. T) (u,t) f g))`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool u:real^P->bool.
          s homotopy_equivalent t /\
          (!f g. f continuous_on u /\ IMAGE f u SUBSET s /\
                 g continuous_on u /\ IMAGE g u SUBSET s
                 ==> homotopic_with (\x. T) (u,s) f g)
          ==> (!f g. f continuous_on u /\ IMAGE f u SUBSET t /\
                     g continuous_on u /\ IMAGE g u SUBSET t
                     ==> homotopic_with (\x. T) (u,t) f g)`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopy_equivalent]) THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N`
     (X_CHOOSE_THEN `k:real^N->real^M` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `homotopic_with (\x. T) (u,t)
          ((h:real^M->real^N) o (k:real^N->real^M) o (f:real^P->real^N))
          (h o k o g)`
    MP_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IMAGE_o] THEN
      REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE) THEN
      ASM_REWRITE_TAC[] THEN
      TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET))) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC(MESON[HOMOTOPIC_WITH_TRANS; HOMOTOPIC_WITH_SYM]
       `homotopic_with P (u,t) f f' /\ homotopic_with P (u,t) g g'
        ==> homotopic_with P (u,t) f g ==> homotopic_with P (u,t) f' g'`) THEN
      CONJ_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM(CONJUNCT1(SPEC_ALL I_O_ID))] THEN
      REWRITE_TAC[o_ASSOC] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] lemma) THEN
  ASM_MESON_TAC[HOMOTOPY_EQUIVALENT_SYM]);;

let HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY = prove
 (`!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homotopy_equivalent t
        ==> ((!f g. f continuous_on s /\ IMAGE f s SUBSET u /\
                    g continuous_on s /\ IMAGE g s SUBSET u
                    ==> homotopic_with (\x. T) (s,u) f g) <=>
             (!f g. f continuous_on t /\ IMAGE f t SUBSET u /\
                    g continuous_on t /\ IMAGE g t SUBSET u
                    ==> homotopic_with (\x. T) (t,u) f g))`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool u:real^P->bool.
          s homotopy_equivalent t /\
          (!f g. f continuous_on s /\ IMAGE f s SUBSET u /\
                 g continuous_on s /\ IMAGE g s SUBSET u
                 ==> homotopic_with (\x. T) (s,u) f g)
           ==> (!f g. f continuous_on t /\ IMAGE f t SUBSET u /\
                      g continuous_on t /\ IMAGE g t SUBSET u
                      ==> homotopic_with (\x. T) (t,u) f g)`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopy_equivalent]) THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N`
     (X_CHOOSE_THEN `k:real^N->real^M` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `homotopic_with (\x. T) (t,u)
          (((f:real^N->real^P) o h) o (k:real^N->real^M)) ((g o h) o k)`
    MP_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IMAGE_o] THEN
      REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE) THEN
      ASM_REWRITE_TAC[] THEN
      TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET))) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC(MESON[HOMOTOPIC_WITH_TRANS; HOMOTOPIC_WITH_SYM]
       `homotopic_with P (u,t) f f' /\ homotopic_with P (u,t) g g'
        ==> homotopic_with P (u,t) f g ==> homotopic_with P (u,t) f' g'`) THEN
      CONJ_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM(CONJUNCT2(SPEC_ALL I_O_ID))] THEN
      REWRITE_TAC[GSYM o_ASSOC] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] lemma) THEN
  ASM_MESON_TAC[HOMOTOPY_EQUIVALENT_SYM]);;

let HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY_NULL = prove
  (`!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homotopy_equivalent t
        ==> ((!f. f continuous_on u /\ IMAGE f u SUBSET s
                  ==> ?c. homotopic_with (\x. T) (u,s) f (\x. c)) <=>
             (!f. f continuous_on u /\ IMAGE f u SUBSET t
                  ==> ?c. homotopic_with (\x. T) (u,t) f (\x. c)))`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool u:real^P->bool.
          s homotopy_equivalent t /\
          (!f. f continuous_on u /\ IMAGE f u SUBSET s
               ==> ?c. homotopic_with (\x. T) (u,s) f (\x. c))
          ==> (!f. f continuous_on u /\ IMAGE f u SUBSET t
                   ==> ?c. homotopic_with (\x. T) (u,t) f (\x. c))`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopy_equivalent]) THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N`
     (X_CHOOSE_THEN `k:real^N->real^M` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(k:real^N->real^M) o (f:real^P->real^N)`) THEN
    REWRITE_TAC[IMAGE_o] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE; ASM SET_TAC[]] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      DISCH_THEN(X_CHOOSE_TAC `c:real^M`) THEN
      EXISTS_TAC `(h:real^M->real^N) c`] THEN
    SUBGOAL_THEN
     `homotopic_with (\x. T) (u,t)
          ((h:real^M->real^N) o (k:real^N->real^M) o (f:real^P->real^N))
          (h o (\x. c))`
    MP_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [o_DEF] THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOMOTOPIC_WITH_TRANS) THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM(CONJUNCT1(SPEC_ALL I_O_ID))] THEN
      REWRITE_TAC[o_ASSOC] THEN ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
      EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[]]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] lemma) THEN
  ASM_MESON_TAC[HOMOTOPY_EQUIVALENT_SYM]);;

let HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY_NULL = prove
 (`!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homotopy_equivalent t
        ==> ((!f. f continuous_on s /\ IMAGE f s SUBSET u
                  ==> ?c. homotopic_with (\x. T) (s,u) f (\x. c)) <=>
             (!f. f continuous_on t /\ IMAGE f t SUBSET u
                  ==> ?c. homotopic_with (\x. T) (t,u) f (\x. c)))`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool u:real^P->bool.
          s homotopy_equivalent t /\
          (!f. f continuous_on s /\ IMAGE f s SUBSET u
               ==> ?c. homotopic_with (\x. T) (s,u) f (\x. c))
          ==> (!f. f continuous_on t /\ IMAGE f t SUBSET u
                   ==> ?c. homotopic_with (\x. T) (t,u) f (\x. c))`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopy_equivalent]) THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N`
     (X_CHOOSE_THEN `k:real^N->real^M` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(f:real^N->real^P) o (h:real^M->real^N)`) THEN
    REWRITE_TAC[IMAGE_o] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE; ASM SET_TAC[]] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^P` THEN DISCH_TAC] THEN
    SUBGOAL_THEN
     `homotopic_with (\x. T) (t,u)
          (((f:real^N->real^P) o h) o (k:real^N->real^M)) ((\x. c) o k)`
    MP_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [o_DEF] THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOMOTOPIC_WITH_TRANS) THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM(CONJUNCT2(SPEC_ALL I_O_ID))] THEN
      REWRITE_TAC[GSYM o_ASSOC] THEN ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
      EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[]]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] lemma) THEN
  ASM_MESON_TAC[HOMOTOPY_EQUIVALENT_SYM]);;

let HOMOTOPY_INVARIANT_CONNECTEDNESS = prove
 (`!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET s /\
        homotopic_with (\x. T) (t,t) (f o g) I /\
        connected s
        ==> connected t`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_with]) THEN
  REWRITE_TAC[o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,N)finite_sum->real^N`
        STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
  `t = IMAGE (h:real^(1,N)finite_sum->real^N) (interval[vec 0,vec 1] PCROSS t)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[EXISTS_IN_PCROSS] THEN
    ASM_MESON_TAC[ENDS_IN_UNIT_INTERVAL];
    ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT; IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`t1:real^1`; `x1:real^N`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t2:real^1`; `x2:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[CONNECTED_COMPONENT_TRANS; CONNECTED_COMPONENT_SYM]
    `!a b. (connected_component t a a' /\ connected_component t b b') /\
           connected_component t a b
           ==> connected_component t a' b'`) THEN
  MAP_EVERY EXISTS_TAC
   [`(h:real^(1,N)finite_sum->real^N) (pastecart (vec 0) x1)`;
    `(h:real^(1,N)finite_sum->real^N) (pastecart (vec 0) x2)`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[connected_component] THEN CONJ_TAC THENL
     [EXISTS_TAC
       `IMAGE ((h:real^(1,N)finite_sum->real^N) o (\s. pastecart s x1))
              (interval[vec 0,vec 1])`;
      EXISTS_TAC
       `IMAGE ((h:real^(1,N)finite_sum->real^N) o (\s. pastecart s x2))
              (interval[vec 0,vec 1])`] THEN
    (CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[CONNECTED_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS];
      REWRITE_TAC[IMAGE_o] THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS];
        CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE] THEN
      REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[ENDS_IN_UNIT_INTERVAL]]);
    ASM_REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `IMAGE (f:real^M->real^N) s` THEN
    ASM_SIMP_TAC[CONNECTED_CONTINUOUS_IMAGE] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN
    REWRITE_TAC[EXISTS_PASTECART; PASTECART_IN_PCROSS] THEN
    X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`vec 1:real^1`; `(f:real^M->real^N) y`] THEN
    ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN ASM SET_TAC[]]);;

let HOMOTOPY_INVARIANT_PATH_CONNECTEDNESS = prove
 (`!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET s /\
        homotopic_with (\x. T) (t,t) (f o g) I /\
        path_connected s
        ==> path_connected t`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_with]) THEN
  REWRITE_TAC[o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,N)finite_sum->real^N`
        STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
  `t = IMAGE (h:real^(1,N)finite_sum->real^N) (interval[vec 0,vec 1] PCROSS t)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[EXISTS_IN_PCROSS] THEN
    ASM_MESON_TAC[ENDS_IN_UNIT_INTERVAL];
    ALL_TAC] THEN
  REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT; IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`t1:real^1`; `x1:real^N`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t2:real^1`; `x2:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[PATH_COMPONENT_TRANS; PATH_COMPONENT_SYM]
    `!a b. (path_component t a a' /\ path_component t b b') /\
           path_component t a b
           ==> path_component t a' b'`) THEN
  MAP_EVERY EXISTS_TAC
   [`(h:real^(1,N)finite_sum->real^N) (pastecart (vec 0) x1)`;
    `(h:real^(1,N)finite_sum->real^N) (pastecart (vec 0) x2)`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PATH_COMPONENT] THEN CONJ_TAC THENL
     [EXISTS_TAC
       `IMAGE ((h:real^(1,N)finite_sum->real^N) o (\s. pastecart s x1))
              (interval[vec 0,vec 1])`;
      EXISTS_TAC
       `IMAGE ((h:real^(1,N)finite_sum->real^N) o (\s. pastecart s x2))
              (interval[vec 0,vec 1])`] THEN
    (CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[PATH_CONNECTED_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS];
      REWRITE_TAC[IMAGE_o] THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS];
        CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE] THEN
      REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[ENDS_IN_UNIT_INTERVAL]]);
    ASM_REWRITE_TAC[PATH_COMPONENT] THEN
    EXISTS_TAC `IMAGE (f:real^M->real^N) s` THEN
    ASM_SIMP_TAC[PATH_CONNECTED_CONTINUOUS_IMAGE] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN
    REWRITE_TAC[EXISTS_PASTECART; PASTECART_IN_PCROSS] THEN
    X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`vec 1:real^1`; `(f:real^M->real^N) y`] THEN
    ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN ASM SET_TAC[]]);;

let HOMOTOPY_EQUIVALENT_CONNECTEDNESS = prove
 (`!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t ==> (connected s <=> connected t)`,
  REWRITE_TAC[homotopy_equivalent] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
   (REWRITE_RULE[CONJ_ASSOC] HOMOTOPY_INVARIANT_CONNECTEDNESS)) THEN
  ASM_MESON_TAC[]);;

let HOMOTOPY_EQUIVALENT_PATH_CONNECTEDNESS = prove
 (`!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t ==> (path_connected s <=> path_connected t)`,
  REWRITE_TAC[homotopy_equivalent] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
   (REWRITE_RULE[CONJ_ASSOC] HOMOTOPY_INVARIANT_PATH_CONNECTEDNESS)) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Contractible sets.                                                        *)
(* ------------------------------------------------------------------------- *)

let contractible = new_definition
 `contractible s <=> ?a. homotopic_with (\x. T) (s,s) (\x. x) (\x. a)`;;

let CONTRACTIBLE_IMP_SIMPLY_CONNECTED = prove
 (`!s:real^N->bool. contractible s ==> simply_connected s`,
  GEN_TAC THEN REWRITE_TAC[contractible] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[SIMPLY_CONNECTED_EMPTY] THEN
  ASM_REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ALL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  DISCH_TAC THEN REWRITE_TAC[homotopic_loops; PCROSS] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  X_GEN_TAC `p:real^1->real^N` THEN
  REWRITE_TAC[path; path_image; pathfinish; pathstart] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_with]) THEN
  REWRITE_TAC[homotopic_with; SUBSET; FORALL_IN_IMAGE; PCROSS] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,N)finite_sum->real^N`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(h o (\y. pastecart (fstcart y) (p(sndcart y):real^N)))
              :real^(1,1)finite_sum->real^N` THEN
  ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; linepath; o_THM] THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC VECTOR_ARITH] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE [IMP_CONJ]
     CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART]);;

let CONTRACTIBLE_IMP_CONNECTED = prove
 (`!s:real^N->bool. contractible s ==> connected s`,
  SIMP_TAC[CONTRACTIBLE_IMP_SIMPLY_CONNECTED;
           SIMPLY_CONNECTED_IMP_CONNECTED]);;

let CONTRACTIBLE_IMP_PATH_CONNECTED = prove
 (`!s:real^N->bool. contractible s ==> path_connected s`,
  SIMP_TAC[CONTRACTIBLE_IMP_SIMPLY_CONNECTED;
           SIMPLY_CONNECTED_IMP_PATH_CONNECTED]);;

let NULLHOMOTOPIC_THROUGH_CONTRACTIBLE = prove
 (`!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET u /\
        contractible t
        ==> ?c. homotopic_with (\h. T) (s,u) (g o f) (\x. c)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [contractible]) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N` MP_TAC) THEN
  DISCH_THEN(MP_TAC o ISPECL [`g:real^N->real^P`; `u:real^P->bool`] o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o ISPECL [`f:real^M->real^N`; `s:real^M->bool`] o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] HOMOTOPIC_COMPOSE_CONTINUOUS_RIGHT)) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_TAC THEN
  EXISTS_TAC `(g:real^N->real^P) b` THEN ASM_REWRITE_TAC[]);;

let NULLHOMOTOPIC_INTO_CONTRACTIBLE = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ contractible t
        ==> ?c. homotopic_with (\h. T) (s,t) f (\x. c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) = (\x. x) o f` SUBST1_TAC THENL
   [REWRITE_TAC[o_THM; FUN_EQ_THM];
    MATCH_MP_TAC NULLHOMOTOPIC_THROUGH_CONTRACTIBLE THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    SET_TAC[]]);;

let NULLHOMOTOPIC_FROM_CONTRACTIBLE = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ contractible s
        ==> ?c. homotopic_with (\h. T) (s,t) f (\x. c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) = f o (\x. x)` SUBST1_TAC THENL
   [REWRITE_TAC[o_THM; FUN_EQ_THM];
    MATCH_MP_TAC NULLHOMOTOPIC_THROUGH_CONTRACTIBLE THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    SET_TAC[]]);;

let HOMOTOPIC_THROUGH_CONTRACTIBLE = prove
 (`!f1:real^M->real^N g1:real^N->real^P f2 g2 s t u.
        f1 continuous_on s /\ IMAGE f1 s SUBSET t /\
        g1 continuous_on t /\ IMAGE g1 t SUBSET u /\
        f2 continuous_on s /\ IMAGE f2 s SUBSET t /\
        g2 continuous_on t /\ IMAGE g2 t SUBSET u /\
        contractible t /\ path_connected u
        ==> homotopic_with (\h. T) (s,u) (g1 o f1) (g2 o f2)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`f1:real^M->real^N`; `g1:real^N->real^P`; `s:real^M->bool`;
    `t:real^N->bool`; `u:real^P->bool`]
    NULLHOMOTOPIC_THROUGH_CONTRACTIBLE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `c1:real^P` THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET th) THEN
                       MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_TRANS) THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN MP_TAC(ISPECL
   [`f2:real^M->real^N`; `g2:real^N->real^P`; `s:real^M->bool`;
    `t:real^N->bool`; `u:real^P->bool`]
   NULLHOMOTOPIC_THROUGH_CONTRACTIBLE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `c2:real^P` THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET th) THEN
                       MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_TRANS) THEN
  REWRITE_TAC[HOMOTOPIC_CONSTANT_MAPS] THEN FIRST_X_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [PATH_CONNECTED_IFF_PATH_COMPONENT]) THEN
  ASM SET_TAC[]);;

let HOMOTOPIC_INTO_CONTRACTIBLE = prove
 (`!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on s /\ IMAGE g s SUBSET t /\
        contractible t
        ==> homotopic_with (\h. T) (s,t) f g`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `(f:real^M->real^N) = (\x. x) o f /\ (g:real^M->real^N) = (\x. x) o g`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL [REWRITE_TAC[o_THM; FUN_EQ_THM]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_THROUGH_CONTRACTIBLE THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  ASM_SIMP_TAC[IMAGE_ID; SUBSET_REFL; CONTRACTIBLE_IMP_PATH_CONNECTED]);;

let HOMOTOPIC_FROM_CONTRACTIBLE = prove
 (`!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on s /\ IMAGE g s SUBSET t /\
        contractible s /\ path_connected t
        ==> homotopic_with (\h. T) (s,t) f g`,
  REPEAT STRIP_TAC THEN
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `(f:real^M->real^N) = f o (\x. x) /\ (g:real^M->real^N) = g o (\x. x)`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL [REWRITE_TAC[o_THM; FUN_EQ_THM]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_THROUGH_CONTRACTIBLE THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  ASM_REWRITE_TAC[IMAGE_ID; SUBSET_REFL]);;

let HOMOTOPY_EQUIVALENT_CONTRACTIBLE_SETS = prove
 (`!s:real^M->bool t:real^N->bool.
        contractible s /\ contractible t /\ (s = {} <=> t = {})
        ==> s homotopy_equivalent t`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT; HOMEOMORPHIC_EMPTY] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `b:real^N` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  STRIP_TAC THEN REWRITE_TAC[homotopy_equivalent] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:real^M` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  EXISTS_TAC `(\x. b):real^M->real^N` THEN
  EXISTS_TAC `(\y. a):real^N->real^M` THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  CONJ_TAC THEN MATCH_MP_TAC HOMOTOPIC_INTO_CONTRACTIBLE THEN
  ASM_REWRITE_TAC[o_DEF; IMAGE_ID; I_DEF; SUBSET_REFL; CONTINUOUS_ON_ID;
                  CONTINUOUS_ON_CONST] THEN
  ASM SET_TAC[]);;

let STARLIKE_IMP_CONTRACTIBLE_GEN = prove
 (`!P s.
        (!a t. a IN s /\ &0 <= t /\ t <= &1 ==> P(\x. (&1 - t) % x + t % a)) /\
        starlike s
        ==> ?a:real^N. homotopic_with P (s,s) (\x. x) (\x. a)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[starlike] THEN ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
  REWRITE_TAC[segment; SUBSET; FORALL_IN_GSPEC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
  REWRITE_TAC[homotopic_with; PCROSS] THEN
  EXISTS_TAC `\y:real^(1,N)finite_sum.
             (&1 - drop(fstcart y)) % sndcart y +
             drop(fstcart y) % a` THEN
  ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC; IN_INTERVAL_1;
    SUBSET; FORALL_IN_IMAGE; REAL_SUB_RZERO; REAL_SUB_REFL; FORALL_IN_GSPEC;
    VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  SIMP_TAC[o_DEF; LIFT_DROP; ETA_AX; LIFT_SUB; CONTINUOUS_ON_SUB;
           CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON; ETA_AX;
           LINEAR_FSTCART; LINEAR_SNDCART]);;

let STARLIKE_IMP_CONTRACTIBLE = prove
 (`!s:real^N->bool. starlike s ==> contractible s`,
  SIMP_TAC[contractible; STARLIKE_IMP_CONTRACTIBLE_GEN]);;

let CONTRACTIBLE_UNIV = prove
 (`contractible(:real^N)`,
  SIMP_TAC[STARLIKE_IMP_CONTRACTIBLE; STARLIKE_UNIV]);;

let STARLIKE_IMP_SIMPLY_CONNECTED = prove
 (`!s:real^N->bool. starlike s ==> simply_connected s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTRACTIBLE_IMP_SIMPLY_CONNECTED THEN
  MATCH_MP_TAC STARLIKE_IMP_CONTRACTIBLE THEN ASM_REWRITE_TAC[]);;

let CONVEX_IMP_SIMPLY_CONNECTED = prove
 (`!s:real^N->bool. convex s ==> simply_connected s`,
  MESON_TAC[CONVEX_IMP_STARLIKE; STARLIKE_IMP_SIMPLY_CONNECTED;
            SIMPLY_CONNECTED_EMPTY]);;

let STARLIKE_IMP_PATH_CONNECTED = prove
 (`!s:real^N->bool. starlike s ==> path_connected s`,
  MESON_TAC[STARLIKE_IMP_SIMPLY_CONNECTED;
            SIMPLY_CONNECTED_IMP_PATH_CONNECTED]);;

let STARLIKE_IMP_CONNECTED = prove
 (`!s:real^N->bool. starlike s ==> connected s`,
  MESON_TAC[STARLIKE_IMP_PATH_CONNECTED; PATH_CONNECTED_IMP_CONNECTED]);;

let IS_INTERVAL_SIMPLY_CONNECTED_1 = prove
 (`!s:real^1->bool. is_interval s <=> simply_connected s`,
  MESON_TAC[SIMPLY_CONNECTED_IMP_PATH_CONNECTED; IS_INTERVAL_PATH_CONNECTED_1;
            CONVEX_IMP_SIMPLY_CONNECTED; IS_INTERVAL_CONVEX_1]);;

let CONTRACTIBLE_EMPTY = prove
 (`contractible {}`,
  SIMP_TAC[contractible; HOMOTOPIC_WITH; PCROSS_EMPTY; NOT_IN_EMPTY] THEN
  REWRITE_TAC[CONTINUOUS_ON_EMPTY] THEN SET_TAC[]);;

let CONTRACTIBLE_CONVEX_TWEAK_BOUNDARY_POINTS = prove
 (`!s t:real^N->bool.
        convex s /\ relative_interior s SUBSET t /\ t SUBSET closure s
        ==> contractible t`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[SUBSET_EMPTY; CLOSURE_EMPTY; CONTRACTIBLE_EMPTY] THEN
  STRIP_TAC THEN MATCH_MP_TAC STARLIKE_IMP_CONTRACTIBLE THEN
  MATCH_MP_TAC STARLIKE_CONVEX_TWEAK_BOUNDARY_POINTS THEN ASM_MESON_TAC[]);;

let CONVEX_IMP_CONTRACTIBLE = prove
 (`!s:real^N->bool. convex s ==> contractible s`,
  MESON_TAC[CONVEX_IMP_STARLIKE; CONTRACTIBLE_EMPTY;
            STARLIKE_IMP_CONTRACTIBLE]);;

let CONTRACTIBLE_SING = prove
 (`!a:real^N. contractible {a}`,
  SIMP_TAC[CONVEX_IMP_CONTRACTIBLE; CONVEX_SING]);;

let IS_INTERVAL_CONTRACTIBLE_1 = prove
 (`!s:real^1->bool. is_interval s <=> contractible s`,
  MESON_TAC[CONTRACTIBLE_IMP_PATH_CONNECTED; IS_INTERVAL_PATH_CONNECTED_1;
            CONVEX_IMP_CONTRACTIBLE; IS_INTERVAL_CONVEX_1]);;

let CONTRACTIBLE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        contractible s /\ contractible t ==> contractible(s PCROSS t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contractible; homotopic_with] THEN
  REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `h:real^(1,M)finite_sum->real^M`] THEN
  REPEAT DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`b:real^N`; `k:real^(1,N)finite_sum->real^N`] THEN
  REPEAT DISCH_TAC THEN
  EXISTS_TAC `pastecart (a:real^M) (b:real^N)` THEN
  EXISTS_TAC `\z. pastecart
                   ((h:real^(1,M)finite_sum->real^M)
                    (pastecart (fstcart z) (fstcart(sndcart z))))
                   ((k:real^(1,N)finite_sum->real^N)
                    (pastecart (fstcart z) (sndcart(sndcart z))))` THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
               FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[CONTINUOUS_ON_PASTECART; LINEAR_CONTINUOUS_ON;
           LINEAR_FSTCART; LINEAR_SNDCART; CONTINUOUS_ON_ID;
           GSYM o_DEF; CONTINUOUS_ON_COMPOSE] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART] THEN
  SIMP_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART]);;

let CONTRACTIBLE_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        contractible(s PCROSS t) <=>
        s = {} \/ t = {} \/ contractible s /\ contractible t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; CONTRACTIBLE_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; CONTRACTIBLE_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[CONTRACTIBLE_PCROSS] THEN
  REWRITE_TAC[contractible; homotopic_with; LEFT_IMP_EXISTS_THM] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC
   [`a:real^M`; `b:real^N`;
    `h:real^(1,(M,N)finite_sum)finite_sum->real^(M,N)finite_sum`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^M) IN s /\ (b:real^N) IN t` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM PASTECART_IN_PCROSS] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
    ASM_MESON_TAC[ENDS_IN_UNIT_INTERVAL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `a:real^M` THEN
    EXISTS_TAC
     `fstcart o
      (h:real^(1,(M,N)finite_sum)finite_sum->real^(M,N)finite_sum) o
      (\z. pastecart (fstcart z) (pastecart (sndcart z) b))`;
    EXISTS_TAC `b:real^N` THEN
    EXISTS_TAC
     `sndcart o
      (h:real^(1,(M,N)finite_sum)finite_sum->real^(M,N)finite_sum) o
      (\z. pastecart (fstcart z) (pastecart a (sndcart z)))`] THEN
  ASM_REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                  SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; o_THM] THEN
  (CONJ_TAC THENL
    [ALL_TAC;  ASM_MESON_TAC[PASTECART_FST_SND; PASTECART_IN_PCROSS]]) THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST;
           LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
  ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS]);;

let HOMOTOPY_EQUIVALENT_EMPTY = prove
 (`(!s. (s:real^M->bool) homotopy_equivalent ({}:real^N->bool) <=> s = {}) /\
   (!t. ({}:real^M->bool) homotopy_equivalent (t:real^N->bool) <=> t = {})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  SIMP_TAC[HOMOTOPY_EQUIVALENT_CONTRACTIBLE_SETS; CONTRACTIBLE_EMPTY] THEN
  REWRITE_TAC[homotopy_equivalent] THEN SET_TAC[]);;

let HOMOTOPY_EQUIVALENT_CONTRACTIBILITY = prove
 (`!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t ==> (contractible s <=> contractible t)`,
  let lemma = prove
   (`!s:real^M->bool t:real^N->bool.
          s homotopy_equivalent t /\ contractible s ==> contractible t`,
    REPEAT GEN_TAC THEN SIMP_TAC[homotopy_equivalent; contractible; I_DEF] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `f:real^M->real^N` (X_CHOOSE_THEN `g:real^N->real^M`
          STRIP_ASSUME_TAC))
     (X_CHOOSE_TAC `a:real^M`)) THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`; `t:real^N->bool`]
          NULLHOMOTOPIC_FROM_CONTRACTIBLE) THEN
    ASM_REWRITE_TAC[contractible; I_DEF] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^N` THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN DISCH_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
    EXISTS_TAC `(f:real^M->real^N) o (g:real^N->real^M)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\x. (b:real^N)) = (\x. b) o (g:real^N->real^M)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] lemma) THEN
  ASM_MESON_TAC[HOMOTOPY_EQUIVALENT_SYM]);;

let HOMOTOPY_EQUIVALENT_SING = prove
 (`!s:real^M->bool a:real^N.
        s homotopy_equivalent {a} <=> ~(s = {}) /\ contractible s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[HOMOTOPY_EQUIVALENT_EMPTY; NOT_INSERT_EMPTY] THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPY_EQUIVALENT_CONTRACTIBILITY) THEN
    REWRITE_TAC[CONTRACTIBLE_SING];
    DISCH_TAC THEN MATCH_MP_TAC HOMOTOPY_EQUIVALENT_CONTRACTIBLE_SETS THEN
    ASM_REWRITE_TAC[CONTRACTIBLE_SING; NOT_INSERT_EMPTY]]);;

let HOMEOMORPHIC_CONTRACTIBLE_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        s homeomorphic t ==> (contractible s <=> contractible t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPY_EQUIVALENT_CONTRACTIBILITY THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT]);;

let HOMEOMORPHIC_CONTRACTIBLE = prove
 (`!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\ contractible s ==> contractible t`,
  MESON_TAC[HOMEOMORPHIC_CONTRACTIBLE_EQ]);;

let CONTRACTIBLE_TRANSLATION = prove
 (`!a:real^N s. contractible (IMAGE (\x. a + x) s) <=> contractible s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_CONTRACTIBLE_EQ THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION]);;

add_translation_invariants [CONTRACTIBLE_TRANSLATION];;

let CONTRACTIBLE_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (contractible (IMAGE f s) <=> contractible s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_CONTRACTIBLE_EQ THEN
  ASM_MESON_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_LEFT_EQ;
                HOMEOMORPHIC_REFL]);;

add_linear_invariants [CONTRACTIBLE_INJECTIVE_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Homeomorphisms between punctured spheres and affine sets.                 *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_PUNCTURED_AFFINE_SPHERE_AFFINE = prove
 (`!a r b t:real^N->bool p:real^M->bool.
        &0 < r /\ b IN sphere(a,r) /\ affine t /\ a IN t /\ b IN t /\
        affine p /\ aff_dim t = aff_dim p + &1
        ==> ((sphere(a:real^N,r) INTER t) DELETE b) homeomorphic p`,
  GEOM_ORIGIN_TAC `a:real^N` THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
  REWRITE_TAC[sphere; DIST_0; IN_ELIM_THM] THEN
  SIMP_TAC[CONJ_ASSOC; NORM_ARITH
   `&0 < r /\ norm(b:real^N) = r <=> norm(b) = r /\ ~(b = vec 0)`] THEN
  GEOM_NORMALIZE_TAC `b:real^N` THEN REWRITE_TAC[] THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `b:real^N` THEN
  SIMP_TAC[NORM_MUL; real_abs; NORM_BASIS; LE_REFL; DIMINDEX_GE_1] THEN
  X_GEN_TAC `b:real` THEN REWRITE_TAC[REAL_MUL_RID; VECTOR_MUL_EQ_0] THEN
  DISCH_THEN(K ALL_TAC) THEN DISCH_THEN SUBST1_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[VECTOR_MUL_LID] THEN
  ASM_CASES_TAC `r = &1` THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(K ALL_TAC) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `subspace(t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_EQ_SUBSPACE]; ALL_TAC] THEN
  TRANS_TAC HOMEOMORPHIC_TRANS `{x:real^N | x$1 = &0} INTER t` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HOMEOMORPHIC_AFFINE_SETS THEN
    ASM_SIMP_TAC[AFFINE_INTER; AFFINE_STANDARD_HYPERPLANE] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    MP_TAC(ISPECL [`basis 1:real^N`; `&0`; `t:real^N->bool`]
        AFF_DIM_AFFINE_INTER_HYPERPLANE) THEN
    ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~(t INTER {x:real^N | x$1 = &0} = {})` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
      EXISTS_TAC `vec 0:real^N` THEN ASM_REWRITE_TAC[VEC_COMPONENT];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(t SUBSET {v:real^N | v$1 = &0})` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `basis 1:real^N`) THEN
      ASM_SIMP_TAC[IN_ELIM_THM; BASIS_COMPONENT; DIMINDEX_GE_1; LE_REFL] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]] THEN
  SUBGOAL_THEN
   `({x:real^N | norm x = &1} INTER t) DELETE (basis 1) =
    {x | norm x = &1 /\ ~(x$1 = &1)} INTER t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `s DELETE a = s' ==> (s INTER t) DELETE a = s' INTER t`) THEN
    MATCH_MP_TAC(SET_RULE
     `Q a /\ (!x. P x /\ Q x ==> x = a)
      ==> {x | P x} DELETE a = {x | P x /\ ~Q x}`) THEN
    SIMP_TAC[BASIS_COMPONENT; CART_EQ; DIMINDEX_GE_1; LE_REFL] THEN
    REWRITE_TAC[NORM_EQ_SQUARE; REAL_POS; REAL_POW_ONE] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    ASM_SIMP_TAC[dot; SUM_CLAUSES_LEFT; DIMINDEX_GE_1] THEN
    REWRITE_TAC[REAL_ARITH `&1 * &1 + s = &1 <=> s = &0`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
      SUM_POS_EQ_0_NUMSEG)) THEN
    REWRITE_TAC[REAL_LE_SQUARE; REAL_ENTIRE] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[homeomorphic; HOMEOMORPHISM] THEN MAP_EVERY ABBREV_TAC
   [`f = \x:real^N. &2 % basis 1 + &2 / (&1 - x$1) % (x - basis 1)`;
    `g = \y:real^N.
           basis 1 + &4 / (norm y pow 2 + &4) % (y - &2 % basis 1)`] THEN
  MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(MESON[CONTINUOUS_ON_SUBSET; INTER_SUBSET]
     `f continuous_on s ==> f continuous_on (s INTER t)`) THEN
    EXPAND_TAC "f" THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
    REWRITE_TAC[o_DEF; real_div; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
    SIMP_TAC[REAL_SUB_0; IN_ELIM_THM] THEN
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN
    REWRITE_TAC[LE_REFL; DIMINDEX_GE_1];
    MATCH_MP_TAC(SET_RULE
     `IMAGE f s SUBSET s' /\ IMAGE f t SUBSET t
      ==> IMAGE f (s INTER t) SUBSET (s' INTER t)`) THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[SUBSPACE_ADD; SUBSPACE_MUL; SUBSPACE_SUB] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
             LE_REFL; DIMINDEX_GE_1; VECTOR_SUB_COMPONENT] THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC(MESON[CONTINUOUS_ON_SUBSET; INTER_SUBSET]
     `f continuous_on s ==> f continuous_on (s INTER t)`) THEN
    EXPAND_TAC "g" THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
    REWRITE_TAC[o_DEF; real_div; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
    SIMP_TAC[LIFT_ADD; REAL_POW_LE; NORM_POS_LE; REAL_ARITH
     `&0 <= x ==> ~(x + &4 = &0)`] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[REAL_POW_2; LIFT_CMUL; CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM; GSYM o_DEF];
    MATCH_MP_TAC(SET_RULE
     `IMAGE f s SUBSET s' /\ IMAGE f t SUBSET t
      ==> IMAGE f (s INTER t) SUBSET (s' INTER t)`) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[NORM_EQ_SQUARE; REAL_POS] THEN EXPAND_TAC "g" THEN
    CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[SUBSPACE_ADD; SUBSPACE_MUL; SUBSPACE_SUB]] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_ARITH
     `b + a % (y - &2 % b):real^N = (&1 - &2 * a) % b + a % y`] THEN
    REWRITE_TAC[NORM_POW_2; VECTOR_ARITH
     `(a + b:real^N) dot (a + b) = (a dot a + b dot b) + &2 * a dot b`] THEN
    ASM_SIMP_TAC[DOT_LMUL; DOT_RMUL; DOT_BASIS; BASIS_COMPONENT; LE_REFL;
                VECTOR_ADD_COMPONENT; DIMINDEX_GE_1; VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; GSYM REAL_POW_2] THEN
    SUBGOAL_THEN `~((y:real^N) dot y + &4 = &0)` MP_TAC THENL
     [MESON_TAC[DOT_POS_LE; REAL_ARITH `&0 <= x ==> ~(x + &4 = &0)`];
      CONV_TAC REAL_FIELD];
    SUBGOAL_THEN
     `!x. norm x = &1 /\ ~(x$1 = &1)
          ==> norm((f:real^N->real^N) x) pow 2 = &4 * (&1 + x$1) / (&1 - x$1)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "f" THEN
      REWRITE_TAC[VECTOR_ARITH
       `a % b + m % (x - b):real^N = (a - m) % b + m % x`] THEN
      REWRITE_TAC[NORM_POW_2; VECTOR_ARITH
       `(a + b:real^N) dot (a + b) = (a dot a + b dot b) + &2 * a dot b`] THEN
      SIMP_TAC[DOT_LMUL; DOT_RMUL; DOT_BASIS; BASIS_COMPONENT;
               DIMINDEX_GE_1; LE_REFL; VECTOR_MUL_COMPONENT] THEN
      ASM_REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_2; REAL_MUL_RID;
                      REAL_POW_ONE] THEN
      UNDISCH_TAC `~((x:real^N)$1 = &1)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_FIELD
     `~(x = &1)
      ==> &4 * (&1 + x) / (&1 - x) + &4 = &8 / (&1 - x)`] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN
    REWRITE_TAC[REAL_ARITH `&4 * inv(&8) * x = x / &2`] THEN
    EXPAND_TAC "f" THEN
    REWRITE_TAC[VECTOR_ARITH `(a + x) - a:real^N = x`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ARITH
     `b + a % (x - b):real^N = x <=> (&1 - a) % (x - b) = vec 0`] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN
    UNDISCH_TAC `~((x:real^N)$1 = &1)` THEN CONV_TAC REAL_FIELD;
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `~((y:real^N) dot y + &4 = &0)` ASSUME_TAC THENL
     [MESON_TAC[DOT_POS_LE; REAL_ARITH `&0 <= x ==> ~(x + &4 = &0)`];
      ALL_TAC] THEN
    SUBGOAL_THEN `((g:real^N->real^N) y)$1 =
                  (y dot y - &4) / (y dot y + &4)` ASSUME_TAC THENL
     [EXPAND_TAC "g" THEN REWRITE_TAC[VECTOR_ADD_COMPONENT] THEN
      REWRITE_TAC[VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT] THEN
      ASM_SIMP_TAC[BASIS_COMPONENT; LE_REFL; NORM_POW_2; DIMINDEX_GE_1] THEN
      UNDISCH_TAC `~((y:real^N) dot y + &4 = &0)` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "g" THEN SIMP_TAC[VECTOR_ARITH `(a + x) - a:real^N = x`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ARITH
     `b + a % (x - b):real^N = x <=> (&1 - a) % (x - b) = vec 0`] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; NORM_POW_2] THEN DISJ1_TAC THEN
    UNDISCH_TAC `~((y:real^N) dot y + &4 = &0)` THEN CONV_TAC REAL_FIELD]);;

let HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN = prove
 (`!s:real^N->bool t:real^M->bool a.
        convex s /\ bounded s /\ a IN relative_frontier s /\
        affine t /\ aff_dim s = aff_dim t + &1
        ==> (relative_frontier s DELETE a) homeomorphic t`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_GE; INT_ARITH
   `--(&1):int <= s ==> ~(--(&1) = s + &1)`] THEN
  MP_TAC(ISPECL [`(:real^N)`; `aff_dim(s:real^N->bool)`]
    CHOOSE_AFFINE_SUBSET) THEN REWRITE_TAC[SUBSET_UNIV] THEN
  REWRITE_TAC[AFF_DIM_GE; AFF_DIM_LE_UNIV; AFF_DIM_UNIV; AFFINE_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` MP_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_EQ_MINUS1]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`s:real^N->bool`; `ball(z:real^N,&1) INTER t`]
        HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS) THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `ball(z:real^N,&1)`]
        (ONCE_REWRITE_RULE[INTER_COMM] AFF_DIM_CONVEX_INTER_OPEN)) THEN
  MP_TAC(ISPECL [`ball(z:real^N,&1)`; `t:real^N->bool`]
        RELATIVE_FRONTIER_CONVEX_INTER_AFFINE) THEN
  ASM_SIMP_TAC[CONVEX_INTER; BOUNDED_INTER; BOUNDED_BALL; CONVEX_BALL;
               AFFINE_IMP_CONVEX; INTERIOR_OPEN; OPEN_BALL;
               FRONTIER_BALL; REAL_LT_01] THEN
  SUBGOAL_THEN `~(ball(z:real^N,&1) INTER t = {})` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_01];
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN SIMP_TAC[]] THEN
  REWRITE_TAC[homeomorphic; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:real^N->real^N`; `k:real^N->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM homeomorphic] THEN
  TRANS_TAC HOMEOMORPHIC_TRANS
    `(sphere(z,&1) INTER t) DELETE (h:real^N->real^N) a` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^N`; `k:real^N->real^N`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHISM]) THEN
    REWRITE_TAC[HOMEOMORPHISM] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; DELETE_SUBSET];
      ASM SET_TAC[];
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; DELETE_SUBSET];
      ASM SET_TAC[];
      ASM SET_TAC[];
      ASM SET_TAC[]];
    MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_AFFINE_SPHERE_AFFINE THEN
    ASM_REWRITE_TAC[REAL_LT_01; GSYM IN_INTER] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHISM]) THEN
    ASM SET_TAC[]]);;

let HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE = prove
 (`!a r b:real^N t:real^M->bool.
    &0 < r /\ b IN sphere(a,r) /\ affine t /\ aff_dim(t) + &1 = &(dimindex(:N))
    ==> (sphere(a:real^N,r) DELETE b) homeomorphic t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cball(a:real^N,r)`; `t:real^M->bool`; `b:real^N`]
        HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_CBALL; REAL_LT_IMP_NZ; AFF_DIM_CBALL;
               CONVEX_CBALL; BOUNDED_CBALL]);;

let HOMEOMORPHIC_PUNCTURED_SPHERE_HYPERPLANE = prove
 (`!a r b c d.
        &0 < r /\ b IN sphere(a,r) /\ ~(c = vec 0)
        ==> (sphere(a:real^N,r) DELETE b) homeomorphic
             {x:real^N | c dot x = d}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE THEN
  ASM_SIMP_TAC[AFFINE_HYPERPLANE; AFF_DIM_HYPERPLANE] THEN INT_ARITH_TAC);;

let HOMEOMORPHIC_PUNCTURED_SPHERE_UNIV = prove
 (`!a r b.
        &0 < r /\ b IN sphere(a,r) /\ dimindex(:N) = dimindex(:M) + 1
        ==> (sphere(a:real^N,r) DELETE b) homeomorphic (:real^M)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC HOMEOMORPHIC_TRANS `{x:real^N | basis 1 dot x = &0}` THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_HYPERPLANE_UNIV; BASIS_NONZERO; LE_REFL;
               DIMINDEX_GE_1; HOMEOMORPHIC_PUNCTURED_SPHERE_HYPERPLANE]);;

let CONTRACTIBLE_PUNCTURED_SPHERE = prove
 (`!a r b:real^N.
        &0 < r /\ b IN sphere(a,r) ==> contractible(sphere(a,r) DELETE b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `contractible {x:real^N | basis 1 dot x = &0}` MP_TAC THENL
   [SIMP_TAC[CONVEX_IMP_CONTRACTIBLE; CONVEX_HYPERPLANE];
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOMEOMORPHIC_CONTRACTIBLE) THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
    MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_SPHERE_HYPERPLANE THEN
    ASM_SIMP_TAC[BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1]]);;

(* ------------------------------------------------------------------------- *)
(* Simple connectedness of a union. This is essentially a stripped-down      *)
(* version of the Seifert - Van Kampen theorem.                              *)
(* ------------------------------------------------------------------------- *)

let SIMPLY_CONNECTED_UNION = prove
 (`!s t:real^N->bool.
    open_in (subtopology euclidean (s UNION t)) s /\
    open_in (subtopology euclidean (s UNION t)) t /\
    simply_connected s /\ simply_connected t /\
    path_connected (s INTER t) /\ ~(s INTER t = {})
    ==> simply_connected (s UNION t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool`
   (STRIP_ASSUME_TAC o GSYM)) MP_TAC) THEN
   DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^N->bool`
   (STRIP_ASSUME_TAC o GSYM)) MP_TAC) THEN
  SIMP_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_PATH; PATH_CONNECTED_UNION] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(pathstart p:real^N) IN s UNION t` MP_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]; REWRITE_TAC[IN_UNION]] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`] THEN
  MAP_EVERY (fun s -> let x = mk_var(s,`:real^N->bool`) in SPEC_TAC(x,x))
   ["v"; "u"; "t"; "s"] THEN
  MATCH_MP_TAC(MESON[]
   `(!s t u v. x IN s ==> P x s t u v) /\
    (!x s t u v. P x s t u v ==> P x t s v u)
    ==> (!s t u v. x IN s \/ x IN t ==>  P x s t u v)`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[UNION_COMM; INTER_COMM] THEN
    MATCH_MP_TAC MONO_IMP THEN SIMP_TAC[]] THEN
  SUBGOAL_THEN
   `?e. &0 < e /\
        !x y. x IN interval[vec 0,vec 1] /\ y IN interval[vec 0,vec 1] /\
              norm(x - y) < e
              ==> path_image(subpath x y p) SUBSET (s:real^N->bool) \/
                  path_image(subpath x y p) SUBSET t`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `path_image(p:real^1->real^N)` HEINE_BOREL_LEMMA) THEN
    ASM_SIMP_TAC[COMPACT_PATH_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `{u:real^N->bool,v}`) THEN
    SIMP_TAC[UNIONS_2; EXISTS_IN_INSERT; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`p:real^1->real^N`; `interval[vec 0:real^1,vec 1]`]
        COMPACT_UNIFORMLY_CONTINUOUS) THEN
    ASM_REWRITE_TAC[GSYM path; COMPACT_INTERVAL; uniformly_continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[dist] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(p:real^1->real^N) x`) THEN
    ANTS_TAC THENL [REWRITE_TAC[path_image] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!p'. p SUBSET b /\
           (s UNION t) INTER u = s /\ (s UNION t) INTER v = t /\
           p SUBSET p' /\ p' SUBSET s UNION t
           ==>  (b SUBSET u \/ b SUBSET v) ==> p SUBSET s \/ p SUBSET t`) THEN
    EXISTS_TAC `path_image(p:real^1->real^N)` THEN
    ASM_SIMP_TAC[PATH_IMAGE_SUBPATH_SUBSET] THEN
    REWRITE_TAC[PATH_IMAGE_SUBPATH_GEN; SUBSET; FORALL_IN_IMAGE] THEN
    SUBGOAL_THEN `segment[x,y] SUBSET ball(x:real^1,d)` MP_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; CENTRE_IN_BALL] THEN
      ASM_REWRITE_TAC[IN_BALL; EMPTY_SUBSET; CONVEX_BALL; dist];
      REWRITE_TAC[IN_BALL; dist; SUBSET] THEN STRIP_TAC THEN
      X_GEN_TAC `z:real^1` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [SEGMENT_1]) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
      ASM_REAL_ARITH_TAC];
    MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `N:num` THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `!n. n <= N /\ p(lift(&n / &N)) IN s
        ==> ?q. path(q:real^1->real^N) /\ path_image q SUBSET s /\
                homotopic_paths (s UNION t)
                                (subpath (vec 0) (lift(&n / &N)) p) q`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `N:num`) THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_OF_NUM_EQ; LE_REFL; LIFT_NUM] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[pathfinish]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^N` MP_TAC) THEN
    REWRITE_TAC[SUBPATH_TRIVIAL] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_PATHS_TRANS) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHSTART) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHFINISH) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_PATHS_SUBSET THEN
    EXISTS_TAC `s:real^N->bool` THEN
    ASM_MESON_TAC[SUBSET_UNION]] THEN
  SUBGOAL_THEN
   `!n. n < N
        ==> path_image(subpath (lift(&n / &N)) (lift(&(SUC n) / &N)) p)
              SUBSET (s:real^N->bool) \/
            path_image(subpath (lift(&n / &N)) (lift(&(SUC n) / &N)) p)
              SUBSET t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; GSYM LIFT_SUB; DROP_VEC;
                NORM_REAL; GSYM drop;
                REAL_ARITH `abs(a / c - b / c) = abs((b - a) / c)`] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUC; REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ;
                 REAL_OF_NUM_LT; LE_1; REAL_ARITH `(x + &1) - x = &1`] THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LID; REAL_MUL_LZERO; REAL_ABS_INV;
      REAL_ABS_NUM; REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[REAL_ARITH `&0 / x = &0`; LIFT_NUM] THEN
    EXISTS_TAC `linepath((p:real^1->real^N)(vec 0),p(vec 0))` THEN
    REWRITE_TAC[SUBPATH_REFL; HOMOTOPIC_PATHS_REFL] THEN
    REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN
    UNDISCH_TAC `(pathstart p:real^N) IN s` THEN REWRITE_TAC[pathstart] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\m. m < n /\ (p(lift(&m / &N)):real^N) IN s` num_MAX) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL
   [CONJ_TAC THENL [EXISTS_TAC `0`; MESON_TAC[LT_IMP_LE]] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 / x = &0`; LIFT_NUM; LE_1] THEN
    ASM_MESON_TAC[pathstart];
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `?q. path q /\
        path_image(q:real^1->real^N) SUBSET s /\
        homotopic_paths (s UNION t) (subpath (vec 0) (lift (&m / &N)) p) q`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. m < i /\ i <= n
        ==> path_image(subpath (lift(&m / &N)) (lift(&i / &N)) p) SUBSET s \/
            path_image(subpath (lift(&m / &N)) (lift(&i / &N)) p) SUBSET
                 (t:real^N->bool)`
  MP_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[CONJUNCT1 LT] THEN
    X_GEN_TAC `i:num` THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_CASES_TAC `i:num = m` THENL
     [DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]] THEN
    SUBGOAL_THEN
     `p(lift(&i / &N)) IN t /\ ~((p(lift(&i / &N)):real^N) IN s)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `x IN s UNION t /\ ~(x IN s) ==> x IN t /\ ~(x IN s)`) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `s SUBSET t ==> x IN s ==> x IN t`)) THEN
        REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                     LE_1; REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
        ASM_ARITH_TAC;
        SUBGOAL_THEN `i < n /\ ~(i:num <= m)` MP_TAC THENL
         [ASM_ARITH_TAC; ASM_MESON_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `path_image(subpath (lift(&i / &N)) (lift (&(SUC i) / &N)) p) SUBSET s \/
      path_image(subpath (lift(&i / &N)) (lift (&(SUC i) / &N)) p) SUBSET
        (t:real^N->bool)`
    MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `~(x IN s)
      ==> (x IN p /\ x IN q) /\ (q UNION p = r)
          ==> p SUBSET s \/ p SUBSET t
              ==> q SUBSET s \/ q SUBSET t
                  ==> r SUBSET s \/ r SUBSET t`)) THEN
    SIMP_TAC[PATH_IMAGE_SUBPATH_GEN; FUN_IN_IMAGE; ENDS_IN_SEGMENT] THEN
    REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC UNION_SEGMENT THEN
    ASM_SIMP_TAC[SEGMENT_1; LIFT_DROP; REAL_LE_DIV2_EQ; REAL_OF_NUM_LT;
                 LE_1; REAL_OF_NUM_LE; LT_IMP_LE; IN_INTERVAL_1] THEN
    ASM_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[LE_REFL]] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `(q:real^1->real^N) ++
                subpath (lift(&m / &N)) (lift (&n / &N)) p` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PATH_JOIN_IMP THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHFINISH) THEN
      ASM_SIMP_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
      DISCH_TAC THEN MATCH_MP_TAC PATH_SUBPATH THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                   LE_1; REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
      EXISTS_TAC `subpath (vec 0) (lift(&m / &N)) (p:real^1->real^N) ++
                  subpath (lift(&m / &N)) (lift(&n / &N)) p` THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
        MATCH_MP_TAC HOMOTOPIC_JOIN_SUBPATHS THEN
        ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL];
        MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
        ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
        MATCH_MP_TAC HOMOTOPIC_PATHS_SUBSET THEN
        EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_UNION] THEN
        ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL] THEN
        MATCH_MP_TAC PATH_SUBPATH] THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                   LE_1; REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC];
    SUBGOAL_THEN
     `(p(lift(&m / &N)):real^N) IN t /\ (p(lift(&n / &N)):real^N) IN t`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE;
                    PATHSTART_SUBPATH; PATHFINISH_SUBPATH; SUBSET];
      ALL_TAC] THEN
    UNDISCH_TAC `path_connected(s INTER t:real^N->bool)` THEN
    REWRITE_TAC[path_connected] THEN DISCH_THEN(MP_TAC o SPECL
     [`p(lift(&m / &N)):real^N`; `p(lift(&n / &N)):real^N`]) THEN
    ASM_REWRITE_TAC[IN_INTER; SUBSET_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^1->real^N` STRIP_ASSUME_TAC) THEN
    UNDISCH_THEN
     `!p. path p /\ path_image p SUBSET t /\ pathfinish p:real^N = pathstart p
          ==> homotopic_paths t p (linepath (pathstart p,pathstart p))`
     (MP_TAC o SPEC `subpath (lift(&m / &N)) (lift(&n / &N)) p ++
                     reversepath(r:real^1->real^N)`) THEN
    ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
                PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_REVERSEPATH] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[SUBSET_PATH_IMAGE_JOIN; PATH_IMAGE_REVERSEPATH] THEN
      MATCH_MP_TAC PATH_JOIN_IMP THEN
      ASM_SIMP_TAC[PATH_REVERSEPATH; PATHFINISH_SUBPATH;
                   PATHSTART_REVERSEPATH] THEN
      MATCH_MP_TAC PATH_SUBPATH THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                   LE_1; REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
     DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS)) THEN
     ASM_REWRITE_TAC[PATHFINISH_LINEPATH; PATHSTART_SUBPATH;
       PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_REVERSEPATH] THEN
     DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_PATHS_LOOP_PARTS)) THEN
     FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHSTART) THEN
     FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHFINISH) THEN
     REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
     REPLICATE_TAC 2 (DISCH_THEN(ASSUME_TAC o SYM)) THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
     EXISTS_TAC `(q:real^1->real^N) ++ r` THEN
     ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; UNION_SUBSET] THEN
     MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
     EXISTS_TAC `subpath (vec 0) (lift(&m / &N)) (p:real^1->real^N) ++
                 subpath (lift(&m / &N)) (lift(&n / &N)) p` THEN
     CONJ_TAC THENL
      [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
       MATCH_MP_TAC HOMOTOPIC_JOIN_SUBPATHS THEN
       ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
       ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
       ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                    LE_1; REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
       ASM_ARITH_TAC;
       MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
       ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
       MATCH_MP_TAC HOMOTOPIC_PATHS_SUBSET THEN
       EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_UNION]]]);;

let SIMPLY_CONNECTED_SPHERE = prove
 (`!a:real^N r. 3 <= dimindex(:N) ==> simply_connected(sphere(a,r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sphere] THEN GEOM_ORIGIN_TAC `a:real^N` THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIST_0] THEN
  ASM_CASES_TAC `r < &0` THENL
   [ASM_SIMP_TAC[NORM_ARITH `r < &0 ==> ~(norm(x:real^N) = r)`] THEN
    REWRITE_TAC[EMPTY_GSPEC; SIMPLY_CONNECTED_EMPTY];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT])] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `b:real^N` (SUBST1_TAC o SYM) o
        MATCH_MP VECTOR_CHOOSE_SIZE) THEN
  UNDISCH_THEN `&0 <= r` (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
  GEOM_NORMALIZE_TAC `b:real^N` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[NORM_EQ_0; SING_GSPEC; NORM_0] THEN
  SIMP_TAC[CONVEX_SING; CONVEX_IMP_SIMPLY_CONNECTED] THEN
  X_GEN_TAC `bbb:real^N` THEN DISCH_THEN(K ALL_TAC) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{x:real^N | norm x = &1} =
    {x | norm x = &1} DELETE (basis 1) UNION
    {x | norm x = &1} DELETE (--(basis 1))`
   (fun th -> SUBST1_TAC th THEN ASSUME_TAC(SYM th))
  THENL
   [MATCH_MP_TAC(SET_RULE
     `~(x = y) ==> s = s DELETE x UNION s DELETE y`) THEN
    REWRITE_TAC[VECTOR_ARITH `x:real^N = --x <=> x = vec 0`] THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ; BASIS_NONZERO;
                 DIMINDEX_GE_1; LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC SIMPLY_CONNECTED_UNION THEN
  ASM_SIMP_TAC[TAUT `p /\ q /\ r /\ s /\ t <=> (p /\ q) /\ (r /\ s) /\ t`] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE `s DELETE x = s INTER (UNIV DELETE x)`] THEN
    CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_INTER_OPEN THEN
    SIMP_TAC[OPEN_DELETE; OPEN_UNIV; OPEN_IN_SUBTOPOLOGY_REFL] THEN
    REWRITE_TAC[SUBSET_UNIV; TOPSPACE_EUCLIDEAN];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTRACTIBLE_IMP_SIMPLY_CONNECTED THEN
    ONCE_REWRITE_TAC[NORM_ARITH `norm(x:real^N) = dist(vec 0,x)`] THEN
    REWRITE_TAC[GSYM sphere] THEN
    MATCH_MP_TAC CONTRACTIBLE_PUNCTURED_SPHERE THEN
    SIMP_TAC[IN_SPHERE; DIST_0; NORM_BASIS; DIMINDEX_GE_1;
             LE_REFL; REAL_LT_01; NORM_NEG];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_DELETE] THEN
    EXISTS_TAC `basis 2:real^N` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; NORM_MUL; NORM_BASIS; ARITH;
                 ARITH_RULE `3 <= n ==> 2 <= n`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r * &1 = r`] THEN
    CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `\x:real^N. x$1`) THEN
    ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; VECTOR_NEG_COMPONENT; BASIS_COMPONENT;
                 ARITH; DIMINDEX_GE_1] THEN
    ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN
   `({x:real^N | norm x = &1} DELETE basis 1) INTER
    ({x | norm x = &1} DELETE --basis 1) =
    ({x:real^N | norm x = &1} DELETE basis 1) INTER {x | &0 <= x$1} UNION
    ({x:real^N | norm x = &1} DELETE --basis 1) INTER {x | x$1 <= &0}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `t UNION u = UNIV /\ ~(b IN u) /\ ~(c IN t)
      ==> (s DELETE b) INTER (s DELETE c) =
          (s DELETE b) INTER t UNION (s DELETE c) INTER u`) THEN
    SIMP_TAC[IN_ELIM_THM; EXTENSION; IN_UNION; IN_UNIV; BASIS_COMPONENT;
             DIMINDEX_GE_1; LE_REFL; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PATH_CONNECTED_UNION THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `basis 2:real^N` THEN
    ASM_SIMP_TAC[IN_INTER; IN_DELETE; IN_ELIM_THM; NORM_BASIS; BASIS_NE; ARITH;
      BASIS_COMPONENT; ARITH_RULE `3 <= n ==> 1 <= n /\ 2 <= n`] THEN
    REWRITE_TAC[REAL_LE_REFL] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^N. x$1`) THEN
    ASM_SIMP_TAC[VECTOR_NEG_COMPONENT; BASIS_COMPONENT;
                 ARITH; ARITH_RULE `3 <= n ==> 1 <= n /\ 2 <= n`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  SUBGOAL_THEN
   `path_connected((cball(vec 0,&1) INTER {x:real^N | x$1 = &0}) DELETE
                   (vec 0))`
  MP_TAC THENL
   [REWRITE_TAC[SET_RULE `s DELETE a = s DIFF {a}`] THEN
    MATCH_MP_TAC PATH_CONNECTED_CONVEX_DIFF_CARD_LT THEN
    SIMP_TAC[CARD_LT_FINITE_INFINITE; FINITE_SING; real_INFINITE] THEN
    SIMP_TAC[CONVEX_INTER; CONVEX_CBALL; CONVEX_STANDARD_HYPERPLANE] THEN
    DISCH_THEN(MP_TAC o
      SPEC `{vec 0:real^N,basis 2,basis 3}` o
      MATCH_MP (REWRITE_RULE [IMP_CONJ] COLLINEAR_SUBSET)) THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTER; IN_CBALL_0;
                IN_ELIM_THM; NORM_0; VEC_COMPONENT; REAL_POS] THEN
    ASM_SIMP_TAC[NORM_BASIS; BASIS_COMPONENT; ARITH; REAL_LE_REFL;
                 ARITH_RULE `3 <= n ==> 1 <= n /\ 2 <= n`;
                 COLLINEAR_3_AFFINE_HULL; BASIS_NONZERO] THEN
    REWRITE_TAC[AFFINE_HULL_2_ALT; VECTOR_ADD_LID; VECTOR_SUB_RZERO] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^N. x$3`) THEN
    ASM_SIMP_TAC[BASIS_COMPONENT; VECTOR_MUL_COMPONENT;
                 ARITH; ARITH_RULE `3 <= n ==> 1 <= n /\ 2 <= n`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[PATH_CONNECTED_CONTINUOUS_IMAGE]
   `(?f g. f continuous_on s /\ g continuous_on s /\
           IMAGE f s = t /\ IMAGE g s = u)
    ==> path_connected s ==> path_connected t /\ path_connected u`) THEN
  EXISTS_TAC `\x:real^N. x + sqrt(&1 - norm(x) pow 2) % basis 1` THEN
  EXISTS_TAC `\x:real^N. x - sqrt(&1 - norm(x) pow 2) % basis 1` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC(REWRITE_RULE[o_DEF]
      CONTINUOUS_ON_LIFT_SQRT_COMPOSE) THEN
    SIMP_TAC[IN_INTER; IN_DELETE; IN_CBALL_0; REAL_SUB_LE;
             REAL_POW_1_LE; NORM_POS_LE; LIFT_SUB] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
    REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM];
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC(REWRITE_RULE[o_DEF]
      CONTINUOUS_ON_LIFT_SQRT_COMPOSE) THEN
    SIMP_TAC[IN_INTER; IN_DELETE; IN_CBALL_0; REAL_SUB_LE;
             REAL_POW_1_LE; NORM_POS_LE; LIFT_SUB] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
    REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_DELETE; IN_CBALL_0;
                IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_GE_1; LE_REFL] THEN
      REWRITE_TAC[NORM_EQ_SQUARE; REAL_ADD_LID; REAL_MUL_RID; REAL_POS] THEN
      REWRITE_TAC[VECTOR_ARITH
       `(x + y:real^N) dot (x + y) = (x dot x + y dot y) + &2 * x dot y`] THEN
      ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_GE_1; LE_REFL; DOT_RMUL;
                   VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID] THEN
      REWRITE_TAC[GSYM REAL_POW_2] THEN
      ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LE; REAL_SUB_LE; REAL_POW_1_LE;
                   NORM_POS_LE] THEN
      CONJ_TAC THENL [REWRITE_TAC[NORM_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\x:real^N. x$1`) THEN
      ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                   BASIS_COMPONENT; DIMINDEX_GE_1; LE_REFL] THEN
      REWRITE_TAC[REAL_ADD_LID; REAL_MUL_RID] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\x:real. x pow 2`) THEN
      ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LE; REAL_SUB_LE; REAL_POW_1_LE;
                   NORM_POS_LE] THEN
      REWRITE_TAC[REAL_RING `&1 - x pow 2 = &1 pow 2 <=> x = &0`] THEN
      ASM_REWRITE_TAC[NORM_EQ_0];
      STRIP_TAC THEN EXISTS_TAC `y - y$1 % basis 1:real^N` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_SUB_0; VECTOR_ARITH
         `y:real^N = y - r % b + s % b <=> (s - r) % b = vec 0`] THEN
        DISJ1_TAC THEN MATCH_MP_TAC SQRT_UNIQUE THEN
        ASM_REWRITE_TAC[NORM_POW_2; VECTOR_ARITH
        `(x - y:real^N) dot (x - y) = (x dot x + y dot y) - &2 * x dot y`] THEN
        SIMP_TAC[DOT_RMUL] THEN
        SIMP_TAC[DOT_LMUL; DOT_BASIS; DIMINDEX_GE_1; LE_REFL;
                 BASIS_COMPONENT] THEN
        ASM_REWRITE_TAC[GSYM NORM_POW_2] THEN REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
        SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
                 BASIS_COMPONENT; DIMINDEX_GE_1; LE_REFL] THEN
        REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC;
        SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
                 BASIS_COMPONENT; DIMINDEX_GE_1; LE_REFL] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[VECTOR_SUB_EQ] THEN DISCH_THEN SUBST_ALL_TAC THEN
        MAP_EVERY UNDISCH_TAC
         [`~((y:real^N)$1 % basis 1:real^N = basis 1)`;
          `norm((y:real^N)$1 % basis 1:real^N) = &1`;
          `&0 <= ((y:real^N)$1 % basis 1:real^N)$1`] THEN
        SIMP_TAC[NORM_MUL; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; NORM_BASIS;
          DIMINDEX_GE_1; LE_REFL; REAL_MUL_RID; real_abs; VECTOR_MUL_LID]]];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_DELETE; IN_CBALL_0;
                IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_GE_1; LE_REFL] THEN
      REWRITE_TAC[NORM_EQ_SQUARE; REAL_ADD_LID; REAL_MUL_RID; REAL_POS] THEN
      REWRITE_TAC[VECTOR_ARITH
       `(x - y:real^N) dot (x - y) = (x dot x + y dot y) - &2 * x dot y`] THEN
      ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_GE_1; LE_REFL; DOT_RMUL;
                   VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_SUB_RZERO] THEN
      REWRITE_TAC[GSYM REAL_POW_2] THEN
      REWRITE_TAC[REAL_ARITH `&0 - x <= &0 <=> &0 <= x`] THEN
      ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LE; REAL_SUB_LE; REAL_POW_1_LE;
                   NORM_POS_LE] THEN
      CONJ_TAC THENL [REWRITE_TAC[NORM_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\x:real^N. x$1`) THEN
      ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
        VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_GE_1; LE_REFL] THEN
      REWRITE_TAC[REAL_ARITH `&0 - x * &1 = -- &1 <=> x = &1`] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\x:real. x pow 2`) THEN
      ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LE; REAL_SUB_LE; REAL_POW_1_LE;
                   NORM_POS_LE] THEN
      REWRITE_TAC[REAL_RING `&1 - x pow 2 = &1 pow 2 <=> x = &0`] THEN
      ASM_REWRITE_TAC[NORM_EQ_0];
      STRIP_TAC THEN EXISTS_TAC `y - y$1 % basis 1:real^N` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_SUB_0; VECTOR_ARITH
         `y:real^N = y - r % b - s % b <=> (s + r) % b = vec 0`] THEN
        DISJ1_TAC THEN REWRITE_TAC[REAL_ARITH `x + y = &0 <=> x = --y`] THEN
        MATCH_MP_TAC SQRT_UNIQUE THEN
        ASM_REWRITE_TAC[REAL_NEG_GE0; NORM_POW_2; VECTOR_ARITH
        `(x - y:real^N) dot (x - y) = (x dot x + y dot y) - &2 * x dot y`] THEN
        SIMP_TAC[DOT_RMUL] THEN
        SIMP_TAC[DOT_LMUL; DOT_BASIS; DIMINDEX_GE_1; LE_REFL;
                 BASIS_COMPONENT] THEN
        ASM_REWRITE_TAC[GSYM NORM_POW_2] THEN REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
        SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
                 BASIS_COMPONENT; DIMINDEX_GE_1; LE_REFL] THEN
        REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC;
        SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
                 BASIS_COMPONENT; DIMINDEX_GE_1; LE_REFL] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[VECTOR_SUB_EQ] THEN DISCH_THEN SUBST_ALL_TAC THEN
        MAP_EVERY UNDISCH_TAC
         [`~((y:real^N)$1 % basis 1:real^N = --basis 1)`;
          `norm((y:real^N)$1 % basis 1:real^N) = &1`;
          `((y:real^N)$1 % basis 1:real^N)$1 <= &0`] THEN
        SIMP_TAC[NORM_MUL; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; NORM_BASIS;
          DIMINDEX_GE_1; LE_REFL; REAL_MUL_RID; VECTOR_MUL_LID;
          REAL_ARITH `y <= &0 ==> abs y = --y`;
          REAL_ARITH `--x = &1 <=> x = -- &1`] THEN
        REPEAT DISCH_TAC THEN VECTOR_ARITH_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* Covering spaces and lifting results for them.                             *)
(* ------------------------------------------------------------------------- *)

let covering_space = new_definition
 `covering_space(c,(p:real^M->real^N)) s <=>
        p continuous_on c /\ IMAGE p c = s /\
        !x. x IN s
            ==> ?t. x IN t /\ open_in (subtopology euclidean s) t /\
                    ?v. UNIONS v = {x | x IN c /\ p(x) IN t} /\
                        (!u. u IN v ==> open_in (subtopology euclidean c) u) /\
                        pairwise DISJOINT v /\
                        (!u. u IN v ==> ?q. homeomorphism (u,t) (p,q))`;;

let COVERING_SPACE_IMP_CONTINUOUS = prove
 (`!p:real^M->real^N c s. covering_space (c,p) s ==> p continuous_on c`,
  SIMP_TAC[covering_space]);;

let COVERING_SPACE_IMP_SURJECTIVE = prove
 (`!p:real^M->real^N c s. covering_space (c,p) s ==> IMAGE p c = s`,
  SIMP_TAC[covering_space]);;

let HOMEOMORPHISM_IMP_COVERING_SPACE = prove
 (`!f:real^M->real^N g s t.
        homeomorphism (s,t) (f,g) ==> covering_space (s,f) t`,
  REWRITE_TAC[homeomorphism] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[covering_space] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  EXISTS_TAC `t:real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV] THEN
  EXISTS_TAC `{s:real^M->bool}` THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; UNIONS_1; PAIRWISE_SING] THEN
  ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `g:real^N->real^M`] THEN
  ASM_REWRITE_TAC[homeomorphism]);;

let COVERING_SPACE_LOCAL_HOMEOMORPHISM = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> !x. x IN c
                ==> ?t u. x IN t /\ open_in (subtopology euclidean c) t /\
                          p(x) IN u /\ open_in (subtopology euclidean s) u /\
                          ?q. homeomorphism (t,u) (p,q)`,
  REWRITE_TAC[covering_space] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(p:real^M->real^N) x`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^M) IN UNIONS v` MP_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[IN_UNIONS]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^M->bool` THEN
  STRIP_TAC THEN EXISTS_TAC `t:real^N->bool` THEN ASM_SIMP_TAC[]);;

let COVERING_SPACE_LOCAL_HOMEOMORPHISM_ALT = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> !y. y IN s
                ==> ?x t u. p(x) = y /\
                            x IN t /\ open_in (subtopology euclidean c) t /\
                            y IN u /\ open_in (subtopology euclidean s) u /\
                            ?q. homeomorphism (t,u) (p,q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?x. x IN c /\ (p:real^M->real^N) x = y` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:real^M` o MATCH_MP
     COVERING_SPACE_LOCAL_HOMEOMORPHISM) THEN
    ASM_MESON_TAC[]]);;

let COVERING_SPACE_OPEN_MAP = prove
 (`!p:real^M->real^N c s t.
        covering_space (c,p) s /\
        open_in (subtopology euclidean c) t
        ==> open_in (subtopology euclidean s) (IMAGE p t)`,
  REWRITE_TAC[covering_space] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [open_in]) THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `y:real^N` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `vs:(real^M->bool)->bool`
   (STRIP_ASSUME_TAC o GSYM)) THEN
  SUBGOAL_THEN
   `?x. x IN {x | x IN c /\ (p:real^M->real^N) x IN u} /\ x IN t /\ p x = y`
  MP_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `v:real^M->bool`)) THEN
  ASM_REWRITE_TAC[homeomorphism] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:real^N->real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (p:real^M->real^N) (t INTER v)` THEN CONJ_TAC THENL
   [ALL_TAC; ASM SET_TAC[]] THEN
  SUBGOAL_THEN
   `IMAGE (p:real^M->real^N) (t INTER v) =
    {z | z IN u /\ q z IN (t INTER v)}`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_ON_OPEN]) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
  MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
  EXISTS_TAC `c:real^M->bool` THEN
  CONJ_TAC THENL [MATCH_MP_TAC OPEN_IN_INTER; ASM_MESON_TAC[open_in]] THEN
  ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV]);;

let COVERING_SPACE_QUOTIENT_MAP = prove
 (`!p:real^M->real^N c s.
    covering_space (c,p) s
    ==> !u. u SUBSET s
            ==> (open_in (subtopology euclidean c) {x | x IN c /\ p x IN u} <=>
                 open_in (subtopology euclidean s) u)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  MATCH_MP_TAC OPEN_MAP_IMP_QUOTIENT_MAP THEN
  CONJ_TAC THENL [ASM_MESON_TAC[COVERING_SPACE_IMP_CONTINUOUS]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  ASM_MESON_TAC[COVERING_SPACE_OPEN_MAP]);;

let COVERING_SPACE_LOCALLY = prove
 (`!P Q p:real^M->real^N c s.
        covering_space (c,p) s /\ (!t. t SUBSET c /\ P t ==> Q(IMAGE p t)) /\
        locally P c
        ==> locally Q s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  MATCH_MP_TAC LOCALLY_OPEN_MAP_IMAGE THEN
  EXISTS_TAC `P:(real^M->bool)->bool` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[COVERING_SPACE_IMP_CONTINUOUS]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  ASM_MESON_TAC[COVERING_SPACE_OPEN_MAP]);;

let COVERING_SPACE_LOCALLY_CONNECTED = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s /\ locally connected c ==> locally connected s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COVERING_SPACE_LOCALLY THEN
  MAP_EVERY EXISTS_TAC
   [`connected:(real^M->bool)->bool`;
    `p:real^M->real^N`; `c:real^M->bool`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[COVERING_SPACE_IMP_CONTINUOUS; CONTINUOUS_ON_SUBSET]);;

let COVERING_SPACE_LOCALLY_PATH_CONNECTED = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s /\ locally path_connected c
        ==> locally path_connected s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COVERING_SPACE_LOCALLY THEN
  MAP_EVERY EXISTS_TAC
   [`path_connected:(real^M->bool)->bool`;
    `p:real^M->real^N`; `c:real^M->bool`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[COVERING_SPACE_IMP_CONTINUOUS; CONTINUOUS_ON_SUBSET]);;

let COVERING_SPACE_LIFT_UNIQUE_GEN = prove
 (`!p:real^M->real^N f:real^P->real^N g1 g2 c s t u a x.
        covering_space (c,p) s /\
        f continuous_on t /\ IMAGE f t SUBSET s /\
        g1 continuous_on t /\ IMAGE g1 t SUBSET c /\
        (!x. x IN t ==> f(x) = p(g1 x)) /\
        g2 continuous_on t /\ IMAGE g2 t SUBSET c /\
        (!x. x IN t ==> f(x) = p(g2 x)) /\
        u IN components t /\ a IN u /\ g1(a) = g2(a) /\ x IN u
        ==> g1(x) = g2(x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  UNDISCH_TAC `(x:real^P) IN u` THEN SPEC_TAC(`x:real^P`,`x:real^P`) THEN
  MATCH_MP_TAC(SET_RULE
   `(?a. a IN u /\ g a = z) /\
    ({x | x IN u /\ g x = z} = {} \/ {x | x IN u /\ g x = z} = u)
    ==> !x. x IN u ==> g x = z`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[VECTOR_SUB_EQ]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_CONNECTED) THEN
  REWRITE_TAC[CONNECTED_CLOPEN] THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^P` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `(g1:real^P->real^M) x` o
        MATCH_MP COVERING_SPACE_LOCAL_HOMEOMORPHISM) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [`v:real^M->bool`; `w:real^N->bool`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_SUB_EQ]) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->real^M` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{x | x IN u /\ (g1:real^P->real^M) x IN v} INTER
                {x | x IN u /\ (g2:real^P->real^M) x IN v}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ONCE_REWRITE_TAC[SET_RULE
       `{x | x IN u /\ g x IN v} =
        {x | x IN u /\ g x IN (v INTER IMAGE g u)}`] THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_IMP_OPEN_IN THEN
      (CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC]) THEN
      UNDISCH_TAC `open_in (subtopology euclidean c) (v:real^M->bool)` THEN
      REWRITE_TAC[OPEN_IN_OPEN] THEN
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER; VECTOR_SUB_EQ] THEN
      ASM SET_TAC[]];
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]]);;

let COVERING_SPACE_LIFT_UNIQUE = prove
 (`!p:real^M->real^N f:real^P->real^N g1 g2 c s t a x.
        covering_space (c,p) s /\
        f continuous_on t /\ IMAGE f t SUBSET s /\
        g1 continuous_on t /\ IMAGE g1 t SUBSET c /\
        (!x. x IN t ==> f(x) = p(g1 x)) /\
        g2 continuous_on t /\ IMAGE g2 t SUBSET c /\
        (!x. x IN t ==> f(x) = p(g2 x)) /\
        connected t /\ a IN t /\ g1(a) = g2(a) /\ x IN t
        ==> g1(x) = g2(x)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`p:real^M->real^N`; `f:real^P->real^N`;
    `g1:real^P->real^M`; `g2:real^P->real^M`;
    `c:real^M->bool`; `s:real^N->bool`; `t:real^P->bool`; `t:real^P->bool`;
    `a:real^P`; `x:real^P`] COVERING_SPACE_LIFT_UNIQUE_GEN) THEN
  ASM_REWRITE_TAC[IN_COMPONENTS_SELF] THEN ASM SET_TAC[]);;

let COVERING_SPACE_LIFT_UNIQUE_IDENTITY = prove
 (`!p:real^M->real^N c f s a.
     covering_space (c,p) s /\
     path_connected c /\
     f continuous_on c /\ IMAGE f c SUBSET c /\
     (!x. x IN c ==> p(f x) = p x) /\
     a IN c /\ f(a) = a
     ==> !x. x IN c ==> f x = x`,
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [path_connected]) THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^M`; `x:real^M`]) THEN
  ASM_REWRITE_TAC[path; path_image; pathstart; pathfinish] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^M` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`p:real^M->real^N`; `(p:real^M->real^N) o (g:real^1->real^M)`;
    `(f:real^M->real^M) o (g:real^1->real^M)`; `g:real^1->real^M`;
    `c:real^M->bool`; `s:real^N->bool`;
    `interval[vec 0:real^1,vec 1]`;
    `vec 0:real^1`; `vec 1:real^1`]
   COVERING_SPACE_LIFT_UNIQUE) THEN
  ASM_REWRITE_TAC[o_THM; IMAGE_o] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; CONNECTED_INTERVAL] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [covering_space]) THEN
  STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP (SET_RULE
   `IMAGE p c = s ==> !x. x IN c ==> p(x) IN s`)) THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE]);;

let COVERING_SPACE_LIFT_HOMOTOPY = prove
 (`!p:real^M->real^N c s (h:real^(1,P)finite_sum->real^N) f u.
        covering_space (c,p) s /\
        h continuous_on (interval[vec 0,vec 1] PCROSS u) /\
        IMAGE h (interval[vec 0,vec 1] PCROSS u) SUBSET s /\
        (!y. y IN u ==> h (pastecart (vec 0) y) = p(f y)) /\
        f continuous_on u /\ IMAGE f u SUBSET c
        ==> ?k. k continuous_on (interval[vec 0,vec 1] PCROSS u) /\
                IMAGE k (interval[vec 0,vec 1] PCROSS u) SUBSET c /\
                (!y. y IN u ==> k(pastecart (vec 0) y) = f y) /\
                (!z. z IN interval[vec 0,vec 1] PCROSS u ==> h z = p(k z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN u
        ==> ?v. open_in (subtopology euclidean u) v /\ y IN v /\
                ?k:real^(1,P)finite_sum->real^M.
                    k continuous_on (interval[vec 0,vec 1] PCROSS v) /\
                    IMAGE k (interval[vec 0,vec 1] PCROSS v) SUBSET c /\
                    (!y. y IN v ==> k(pastecart (vec 0) y) = f y) /\
                    (!z. z IN interval[vec 0,vec 1] PCROSS v
                         ==> h z :real^N = p(k z))`
  MP_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [RIGHT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`v:real^P->real^P->bool`; `fs:real^P->real^(1,P)finite_sum->real^M`] THEN
    DISCH_THEN(LABEL_TAC "*") THEN
    MP_TAC(ISPECL
     [`fs:real^P->real^(1,P)finite_sum->real^M`;
      `(\x. interval[vec 0,vec 1] PCROSS (v x))
        :real^P->real^(1,P)finite_sum->bool`;
      `(interval[vec 0,vec 1] PCROSS u):real^(1,P)finite_sum->bool`;
      `u:real^P->bool`]
      PASTING_LEMMA_EXISTS) THEN
    ASM_SIMP_TAC[] THEN ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `k:real^(1,P)finite_sum->real^M` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_PCROSS; SUBSET] THEN
      REPEAT CONJ_TAC THEN TRY(X_GEN_TAC `t:real^1`) THEN
      X_GEN_TAC `y:real^P` THEN STRIP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL
         [`pastecart (t:real^1) (y:real^P)`; `y:real^P`]);
        FIRST_X_ASSUM(MP_TAC o SPECL
         [`pastecart (vec 0:real^1) (y:real^P)`; `y:real^P`]);
        FIRST_X_ASSUM(MP_TAC o SPECL
         [`pastecart (t:real^1) (y:real^P)`; `y:real^P`])] THEN
      ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_INTER; ENDS_IN_UNIT_INTERVAL] THEN
      DISCH_THEN SUBST1_TAC THEN
      REMOVE_THEN "*" (MP_TAC o SPEC `y:real^P`) THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS]] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; UNIONS_GSPEC; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^P`] THEN STRIP_TAC THEN
      EXISTS_TAC `y:real^P` THEN ASM_SIMP_TAC[PASTECART_IN_PCROSS];
      X_GEN_TAC `y:real^P` THEN DISCH_TAC THEN
      REMOVE_THEN "*" (MP_TAC o SPEC `y:real^P`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      REWRITE_TAC[OPEN_IN_OPEN] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^P->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(:real^1) PCROSS (t:real^P->bool)` THEN
      ASM_SIMP_TAC[REWRITE_RULE[GSYM PCROSS] OPEN_PCROSS; OPEN_UNIV] THEN
      REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS;
                    IN_INTER; IN_UNIV] THEN
      REPEAT GEN_TAC THEN CONV_TAC TAUT;
      REWRITE_TAC[FORALL_PASTECART; IN_INTER; PASTECART_IN_PCROSS] THEN
      MAP_EVERY X_GEN_TAC
       [`x:real^P`; `z:real^P`; `t:real^1`; `y:real^P`] THEN
      REWRITE_TAC[CONJ_ACI] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o
        ISPECL [`h:real^(1,P)finite_sum->real^N`;
                `(fs:real^P->real^(1,P)finite_sum->real^M) x`;
                `(fs:real^P->real^(1,P)finite_sum->real^M) z`;
                `interval[vec 0:real^1,vec 1] PCROSS {y:real^P}`;
                `pastecart (vec 0:real^1) (y:real^P)`;
                `pastecart (t:real^1) (y:real^P)`] o
        MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_UNIQUE)) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_SING; ENDS_IN_UNIT_INTERVAL] THEN
      SIMP_TAC[REWRITE_RULE[GSYM PCROSS] CONNECTED_PCROSS;
               CONNECTED_INTERVAL; CONNECTED_SING] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[FORALL_PASTECART; SUBSET; PASTECART_IN_PCROSS] THEN
        ASM_SIMP_TAC[IN_SING];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS)) THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[FORALL_PASTECART; SUBSET; PASTECART_IN_PCROSS] THEN
        ASM_SIMP_TAC[IN_SING];
        ALL_TAC] THEN
      ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> (p /\ q /\ r) /\ s`] THEN
      CONJ_TAC THENL
       [REMOVE_THEN "*" (MP_TAC o SPEC `x:real^P`);
        REMOVE_THEN "*" (MP_TAC o SPEC `z:real^P`)] THEN
      ASM_REWRITE_TAC[FORALL_IN_GSPEC; SUBSET; FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SING] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[FORALL_PASTECART; SUBSET; PASTECART_IN_PCROSS] THEN
      ASM_SIMP_TAC[IN_SING]]] THEN
  X_GEN_TAC `y:real^P` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o last o CONJUNCTS o
    GEN_REWRITE_RULE I [covering_space]) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `uu:real^N->real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!t. t IN interval[vec 0,vec 1]
        ==> ?k n i:real^N.
                open_in (subtopology euclidean (interval[vec 0,vec 1])) k /\
                open_in (subtopology euclidean u) n /\
                t IN k /\ y IN n /\ i IN s /\
                IMAGE (h:real^(1,P)finite_sum->real^N) (k PCROSS n) SUBSET uu i`
  MP_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:real^(1,P)finite_sum->real^N) (pastecart t y) IN s`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o ONCE_REWRITE_RULE[FORALL_IN_IMAGE] o
        GEN_REWRITE_RULE I [SUBSET]) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `open_in (subtopology euclidean (interval[vec 0,vec 1] PCROSS u))
              {z | z IN (interval[vec 0,vec 1] PCROSS u) /\
                   (h:real^(1,P)finite_sum->real^N) z IN
                   uu(h(pastecart t y))}`
    MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        PASTECART_IN_INTERIOR_SUBTOPOLOGY)) THEN
    DISCH_THEN(MP_TAC o SPECL [`t:real^1`; `y:real^P`]) THEN
    ASM_SIMP_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^1->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:real^P->bool` THEN
    STRIP_TAC THEN
    EXISTS_TAC `(h:real^(1,P)finite_sum->real^N) (pastecart t y)` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [OPEN_IN_OPEN] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[MESON[]
   `(?x y. (P y /\ x = f y) /\ Q x) <=> ?y. P y /\ Q(f y)`] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`kk:real^1->real^1->bool`; `nn:real^1->real^P->bool`;
    `xx:real^1->real^N`] THEN
  DISCH_THEN(LABEL_TAC "+") THEN
  MP_TAC(ISPEC `interval[vec 0:real^1,vec 1] PCROSS {y:real^P}`
    COMPACT_IMP_HEINE_BOREL) THEN
  SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; COMPACT_SING] THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE ((\i. kk i PCROSS nn i):real^1->real^(1,P)finite_sum->bool)
          (interval[vec 0,vec 1])`) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; OPEN_PCROSS] THEN ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; IN_SING] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `z:real^P`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; PASTECART_IN_PCROSS] THEN
    ASM_MESON_TAC[IN_INTER];
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
    REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `tk:real^1->bool` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `n = INTERS (IMAGE (nn:real^1->real^P->bool) tk)` THEN
  SUBGOAL_THEN `(y:real^P) IN n /\ open n` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN CONJ_TAC THENL
     [REWRITE_TAC[INTERS_IMAGE; IN_ELIM_THM];
      MATCH_MP_TAC OPEN_INTERS THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[FINITE_IMAGE]] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REMOVE_THEN "+" (MP_TAC o SPEC `t:real^1`) THEN
    (ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[IN_INTER]]);
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`interval[vec 0:real^1,vec 1]`; `IMAGE (kk:real^1->real^1->bool) tk`]
   LEBESGUE_COVERING_LEMMA) THEN
  REWRITE_TAC[COMPACT_INTERVAL; FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
  MATCH_MP_TAC(TAUT
   `q /\ (p ==> ~q) /\ (q ==> (r ==> s) ==> t)
    ==> (~p /\ q /\ r ==> s) ==> t`) THEN
  SIMP_TAC[UNIONS_0; IMAGE_CLAUSES; SUBSET_EMPTY; UNIT_INTERVAL_NONEMPTY] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [UNIONS_IMAGE]) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; IMP_CONJ; IN_SING] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
    REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; PASTECART_IN_PCROSS] THEN
    MESON_TAC[];
    DISCH_TAC] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `d:real` REAL_ARCH_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n. n <= N
        ==> ?v k:real^(1,P)finite_sum->real^M.
                open_in (subtopology euclidean u) v /\
                y IN v /\
                k continuous_on interval[vec 0,lift(&n / &N)] PCROSS v /\
                IMAGE k (interval[vec 0,lift(&n / &N)] PCROSS v) SUBSET c /\
                (!y. y IN v ==> k (pastecart (vec 0) y) = f y) /\
                (!z. z IN interval[vec 0,lift(&n / &N)] PCROSS v
                     ==> h z:real^N = p (k z))`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[LE_REFL] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_OF_NUM_EQ; LIFT_NUM]] THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[real_div; REAL_MUL_LZERO; LIFT_NUM] THEN
    EXISTS_TAC `u:real^P->bool` THEN
    EXISTS_TAC `(f o sndcart):real^(1,P)finite_sum->real^M` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; INTERVAL_SING] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; IN_SING; o_THM] THEN
    ASM_REWRITE_TAC[FORALL_UNWIND_THM2; SNDCART_PASTECART] THEN
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    SIMP_TAC[SNDCART_PASTECART];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN ASM_CASES_TAC `SUC m <= N` THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC m <= N ==> m <= N`; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`v:real^P->bool`; `k:real^(1,P)finite_sum->real^M`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM
   (MP_TAC o SPEC `interval[lift(&m / &N),lift(&(SUC m) / &N)]`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIAMETER_INTERVAL; SUBSET_INTERVAL_1] THEN
    REWRITE_TAC[LIFT_DROP; DROP_VEC; INTERVAL_EQ_EMPTY_1;
                GSYM LIFT_SUB; NORM_LIFT] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_DIV2_EQ; REAL_OF_NUM_LT; LE_1;
                 REAL_FIELD `&0 < x ==> a / x - b / x = (a - b) / x`] THEN
    SIMP_TAC[GSYM NOT_LE; ARITH_RULE `m <= SUC m`; REAL_OF_NUM_SUB] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_LE_DIV; REAL_POS;
                 REAL_ABS_NUM; ARITH_RULE `SUC m - m = 1`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 / n = inv(n)`; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
    ASM_REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "+" (MP_TAC o SPEC `t:real^1`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(xx:real^1->real^N) t`) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:(real^M->bool)->bool` MP_TAC) THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC
   `(k:real^(1,P)finite_sum->real^M) (pastecart (lift(&m / &N)) y)`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC(TAUT
   `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [IN_INTER])) THEN
  SUBGOAL_THEN
   `lift(&m / &N) IN interval[vec 0,lift (&m / &N)] /\
    lift(&m / &N) IN interval[lift(&m / &N),lift(&(SUC m) / &N)]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; LE_1; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
    FIRST_X_ASSUM(MP_TAC o SPEC `pastecart(lift(&m / &N)) (y:real^P)`) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (SET_RULE `IMAGE h s SUBSET t ==> x IN s ==> h x IN t`)) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTER] THEN
    ASM_SIMP_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_DIV; REAL_LE_LDIV_EQ;
                 REAL_POS; REAL_OF_NUM_LT; LE_1; DROP_VEC] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC LAND_CONV [IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^M->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `w:real^M->bool`) MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^M->bool` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `p':real^N->real^M`) THEN
    DISCH_TAC THEN UNDISCH_THEN `(w:real^M->bool) IN vv` (K ALL_TAC)] THEN
  ABBREV_TAC `w' = (uu:real^N->real^N->bool)(xx(t:real^1))` THEN
  SUBGOAL_THEN
   `?n'. open_in (subtopology euclidean u) n' /\ y IN n' /\
         IMAGE (k:real^(1,P)finite_sum->real^M) ({lift(&m / &N)} PCROSS n')
         SUBSET w`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC
     `{z | z IN v /\ ((k:real^(1,P)finite_sum->real^M) o
                     pastecart (lift(&m / &N))) z IN w}` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; IN_SING; o_THM] THEN
    MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `v:real^P->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `c:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST;
               CONTINUOUS_ON_ID] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET));
      REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE k s SUBSET c ==> t SUBSET s ==> IMAGE k t SUBSET c`))] THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?q q':real^P->bool.
        open_in (subtopology euclidean u) q /\
        closed_in (subtopology euclidean u) q' /\
        y IN q /\ y IN q' /\ q SUBSET q' /\
        q SUBSET (u INTER nn(t:real^1)) INTER n' INTER v /\
        q' SUBSET (u INTER nn(t:real^1)) INTER n' INTER v`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE
     `y IN q /\ y IN q' /\ q SUBSET q' /\ q SUBSET s /\ q' SUBSET s <=>
      y IN q /\ q SUBSET q' /\ q' SUBSET s`] THEN
    UNDISCH_TAC `open_in (subtopology euclidean u) (v:real^P->bool)` THEN
    UNDISCH_TAC `open_in (subtopology euclidean u) (n':real^P->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `vo:real^P->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `vx:real^P->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `nn(t:real^1) INTER vo INTER vx:real^P->bool`
      OPEN_CONTAINS_CBALL) THEN
    ASM_SIMP_TAC[OPEN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `y:real^P`) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u INTER ball(y:real^P,e)` THEN
    EXISTS_TAC `u INTER cball(y:real^P,e)` THEN
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN
    CONJ_TAC THENL [MESON_TAC[OPEN_BALL]; ALL_TAC] THEN
    CONJ_TAC THENL [MESON_TAC[CLOSED_CBALL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN
    MP_TAC(ISPECL [`y:real^P`; `e:real`] BALL_SUBSET_CBALL) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  EXISTS_TAC `q:real^P->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`\x:real^(1,P)finite_sum.
       x IN interval[vec 0,lift(&m / &N)] PCROSS (q':real^P->bool)`;
    `k:real^(1,P)finite_sum->real^M`;
    `(p':real^N->real^M) o (h:real^(1,P)finite_sum->real^N)`;
    `interval[vec 0,lift(&m / &N)] PCROSS (q':real^P->bool)`;
    `interval[lift(&m / &N),lift(&(SUC m) / &N)] PCROSS (q':real^P->bool)`]
   CONTINUOUS_ON_CASES_LOCAL) THEN
  REWRITE_TAC[TAUT `~(p /\ ~p)`] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CLOSED_IN_CLOSED] THEN
      EXISTS_TAC `interval[vec 0,lift(&m / &N)] PCROSS (:real^P)` THEN
      SIMP_TAC[CLOSED_PCROSS; CLOSED_INTERVAL; CLOSED_UNIV] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; FORALL_PASTECART] THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN CONV_TAC TAUT;
      REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC
       `interval[lift(&m / &N),lift(&(SUC m) / &N)] PCROSS (:real^P)` THEN
      SIMP_TAC[CLOSED_PCROSS; CLOSED_INTERVAL; CLOSED_UNIV] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; FORALL_PASTECART] THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN CONV_TAC TAUT;
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET))
      THENL
       [ALL_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `IMAGE k s SUBSET c ==> t SUBSET s ==> IMAGE k t SUBSET c`))] THEN
      MATCH_MP_TAC PCROSS_MONO THEN
      (CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]]) THEN
      ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC;
                      SUBSET_INTER] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_DIV2_EQ; REAL_OF_NUM_LT;
                   LE_1] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LE_1;
                   REAL_MUL_LZERO; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
      DISJ2_TAC THEN ARITH_TAC;
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
      MAP_EVERY X_GEN_TAC [`r:real^1`; `z:real^P`] THEN
      ASM_CASES_TAC `(z:real^P) IN q'` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN DISCH_THEN(MP_TAC o MATCH_MP
       (REAL_ARITH `(b <= x /\ x <= c) /\ (a <= x /\ x <= b) ==> x = b`)) THEN
      REWRITE_TAC[DROP_EQ; o_THM] THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
       `(!x. x IN w ==> p' (p x) = x)
        ==> h z = p(k z) /\ k z IN w
            ==> k z = p' (h z)`)) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM SET_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING] THEN ASM SET_TAC[]]];
    SUBGOAL_THEN
     `interval[vec 0,lift(&m / &N)] UNION
      interval [lift(&m / &N),lift(&(SUC m) / &N)] =
      interval[vec 0,lift(&(SUC m) / &N)]`
    ASSUME_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1] THEN GEN_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b /\ b <= c ==>
       (a <= x /\ x <= b \/ b <= x /\ x <= c <=> a <= x /\ x <= c)`) THEN
      SIMP_TAC[LIFT_DROP; DROP_VEC; REAL_LE_DIV; REAL_POS] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LT; REAL_OF_NUM_LE; LE_1] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `interval[vec 0,lift(&m / &N)] PCROSS (q':real^P->bool) UNION
      interval [lift(&m / &N),lift(&(SUC m) / &N)] PCROSS q' =
      interval[vec 0,lift(&(SUC m) / &N)] PCROSS q'`
    SUBST1_TAC THENL
     [SIMP_TAC[EXTENSION; IN_UNION; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[CONTINUOUS_ON_SUBSET]
     `t SUBSET s /\ (f continuous_on s ==> P f)
      ==> f continuous_on s ==> ?g. g continuous_on t /\ P g`) THEN
    ASM_SIMP_TAC[PCROSS_MONO; SUBSET_REFL] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
      MAP_EVERY X_GEN_TAC [`r:real^1`; `z:real^P`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^P) IN q'` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[PASTECART_IN_PCROSS]] THEN
      COND_CASES_TAC THEN REWRITE_TAC[o_THM] THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING] THEN ASM SET_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
          CONJUNCT1 o GEN_REWRITE_RULE I [open_in]) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `IMAGE p w' = w ==> x IN w' ==> p x IN w`))];
      X_GEN_TAC `z:real^P` THEN REWRITE_TAC[PASTECART_IN_PCROSS] THEN
      DISCH_TAC THEN REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL] THEN
      SUBGOAL_THEN `(z:real^P) IN q'` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[LIFT_DROP; DROP_VEC]] THEN
      SIMP_TAC[REAL_LE_DIV; REAL_POS] THEN ASM SET_TAC[];
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
      MAP_EVERY X_GEN_TAC [`r:real^1`; `z:real^P`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^P) IN q'` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM SET_TAC[];
        REWRITE_TAC[o_THM] THEN CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM MATCH_MP_TAC]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      (SET_RULE `IMAGE h s SUBSET t ==> x IN s ==> h x IN t`)) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTER] THEN
    REPEAT(CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REAL_ARITH `a <= x /\ x <= b ==> b <= c ==> a <= x /\ x <= c`)) THEN
    ASM_SIMP_TAC[LIFT_DROP; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
    ASM_REWRITE_TAC[DROP_VEC; REAL_MUL_LID; REAL_OF_NUM_LE]]);;

let COVERING_SPACE_LIFT_HOMOTOPIC_FUNCTION = prove
 (`!p:real^M->real^N c s f f' g u:real^P->bool.
        covering_space (c,p) s /\
        g continuous_on u /\ IMAGE g u SUBSET c /\
        (!y. y IN u ==> p(g y) = f y) /\
        homotopic_with (\x. T) (u,s) f f'
        ==> ?g'. g' continuous_on u /\ IMAGE g' u SUBSET c /\
                 (!y. y IN u ==> p(g' y) = f' y)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `h:real^(1,P)finite_sum->real^N`
    STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homotopic_with]) THEN
  FIRST_ASSUM(MP_TAC o
    ISPECL [`h:real^(1,P)finite_sum->real^N`;
            `g:real^P->real^M`; `u:real^P->bool`] o
    MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_HOMOTOPY)) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^(1,P)finite_sum->real^M`
        STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(k:real^(1,P)finite_sum->real^M) o
              (\x. pastecart (vec 1) x)` THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST;
             CONTINUOUS_ON_ID] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS;
                ENDS_IN_UNIT_INTERVAL];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `IMAGE k s SUBSET c ==> t SUBSET s ==> IMAGE k t SUBSET c`)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS;
                ENDS_IN_UNIT_INTERVAL];
    ASM_MESON_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL]]);;

let COVERING_SPACE_LIFT_INESSENTIAL_FUNCTION = prove
 (`!p:real^M->real^N c s f a u:real^P->bool.
        covering_space (c,p) s /\ homotopic_with (\x. T) (u,s) f (\x. a)
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\
                (!y. y IN u ==> p(g y) = f y)`,
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `u:real^P->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; IMAGE_CLAUSES; EMPTY_SUBSET;
                  CONTINUOUS_ON_EMPTY] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE
     [TAUT `a /\ b /\ c /\ d /\ e ==> f <=> a /\ e ==> b /\ c /\ d ==> f`]
     COVERING_SPACE_LIFT_HOMOTOPIC_FUNCTION)) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  SUBGOAL_THEN `?b. b IN c /\ (p:real^M->real^N) b = a` CHOOSE_TAC THENL
   [ASM SET_TAC[];
    EXISTS_TAC `(\x. b):real^P->real^M`] THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN ASM SET_TAC[]);;

let COVERING_SPACE_LIFT_HOMOTOPY_ALT = prove
 (`!p:real^M->real^N c s (h:real^(P,1)finite_sum->real^N) f u.
        covering_space (c,p) s /\
        h continuous_on (u PCROSS interval[vec 0,vec 1]) /\
        IMAGE h (u PCROSS interval[vec 0,vec 1]) SUBSET s /\
        (!y. y IN u ==> h (pastecart y (vec 0)) = p(f y)) /\
        f continuous_on u /\ IMAGE f u SUBSET c
        ==> ?k. k continuous_on (u PCROSS interval[vec 0,vec 1]) /\
                IMAGE k (u PCROSS interval[vec 0,vec 1]) SUBSET c /\
                (!y. y IN u ==> k(pastecart y (vec 0)) = f y) /\
                (!z. z IN u PCROSS interval[vec 0,vec 1] ==> h z = p(k z))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPECL
   [`(h:real^(P,1)finite_sum->real^N) o
     (\z. pastecart (sndcart z) (fstcart z))`;
    `f:real^P->real^M`; `u:real^P->bool`] o
      MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_HOMOTOPY)) THEN
  ASM_SIMP_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; LINEAR_CONTINUOUS_ON;
               LINEAR_FSTCART; LINEAR_SNDCART] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET));
      REWRITE_TAC[IMAGE_o] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE k s SUBSET c ==> t SUBSET s ==> IMAGE k t SUBSET c`))] THEN
    SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; FORALL_IN_PCROSS;
             FSTCART_PASTECART; SNDCART_PASTECART];
    DISCH_THEN(X_CHOOSE_THEN `k:real^(1,P)finite_sum->real^M`
        STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(k:real^(1,P)finite_sum->real^M) o
                (\z. pastecart (sndcart z) (fstcart z))` THEN
    ASM_SIMP_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                 FORALL_IN_PCROSS; PASTECART_IN_PCROSS] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; LINEAR_CONTINUOUS_ON;
               LINEAR_FSTCART; LINEAR_SNDCART] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET));
      REWRITE_TAC[IMAGE_o] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE k s SUBSET c ==> t SUBSET s ==> IMAGE k t SUBSET c`));
      MAP_EVERY X_GEN_TAC [`x:real^P`; `t:real^1`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (t:real^1) (x:real^P)`)] THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS;
                 FSTCART_PASTECART; SNDCART_PASTECART; FORALL_IN_PCROSS]]);;

let COVERING_SPACE_LIFT_PATH_STRONG = prove
 (`!p:real^M->real^N c s g a.
     covering_space (c,p) s /\
     path g /\ path_image g SUBSET s /\ pathstart g = p(a) /\ a IN c
     ==> ?h. path h /\ path_image h SUBSET c /\ pathstart h = a /\
             !t. t IN interval[vec 0,vec 1] ==> p(h t) = g t`,
  REWRITE_TAC[path_image; path; pathstart] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o
    ISPECL [`(g:real^1->real^N) o (fstcart:real^(1,P)finite_sum->real^1)`;
            `(\y. a):real^P->real^M`; `{arb:real^P}`] o
    MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_HOMOTOPY)) THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; o_THM; FSTCART_PASTECART] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_o; CONTINUOUS_ON_CONST] THEN
    ASM_REWRITE_TAC[SET_RULE `IMAGE (\y. a) {b} SUBSET s <=> a IN s`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_FSTCART; LINEAR_CONTINUOUS_ON] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET));
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    SIMP_TAC[FSTCART_PASTECART] THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `k:real^(1,P)finite_sum->real^M`
        STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(k:real^(1,P)finite_sum->real^M) o (\t. pastecart t arb)` THEN
    ASM_REWRITE_TAC[o_THM; IMAGE_o] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART;
               CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_SING];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE k s SUBSET c ==> t SUBSET s ==> IMAGE k t SUBSET c`)) THEN
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_SING];
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (t:real^1) (arb:real^P)`) THEN
      ASM_SIMP_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; IN_SING]]]);;

let COVERING_SPACE_LIFT_PATH = prove
 (`!p:real^M->real^N c s g.
     covering_space (c,p) s /\ path g /\ path_image g SUBSET s
     ==> ?h. path h /\ path_image h SUBSET c /\
             !t. t IN interval[vec 0,vec 1] ==> p(h t) = g t`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `IMAGE g i SUBSET s ==> vec 0 IN i ==> g(vec 0) IN s`) o
   GEN_REWRITE_RULE LAND_CONV [path_image]) THEN
  REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  REWRITE_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:real^M` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^M->real^N`; `c:real^M->bool`; `s:real^N->bool`;
                `g:real^1->real^N`; `a:real^M`]
    COVERING_SPACE_LIFT_PATH_STRONG) THEN
  ASM_REWRITE_TAC[pathstart] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

let COVERING_SPACE_LIFT_HOMOTOPIC_PATHS = prove
 (`!p:real^M->real^N c s g1 g2 h1 h2.
     covering_space (c,p) s /\
     path g1 /\ path_image g1 SUBSET s /\
     path g2 /\ path_image g2 SUBSET s /\
     homotopic_paths s g1 g2 /\
     path h1 /\ path_image h1 SUBSET c /\
     (!t. t IN interval[vec 0,vec 1] ==> p(h1 t) = g1 t) /\
     path h2 /\ path_image h2 SUBSET c /\
     (!t. t IN interval[vec 0,vec 1] ==> p(h2 t) = g2 t) /\
     pathstart h1 = pathstart h2
     ==> homotopic_paths c h1 h2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMOTOPIC_PATHS] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_paths]) THEN
  REWRITE_TAC[homotopic_with; pathstart; pathfinish] THEN
  DISCH_THEN(X_CHOOSE_THEN
   `h:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o ISPECL
   [`h:real^(1,1)finite_sum->real^N`; `(\x. pathstart h2):real^1->real^M`;
    `interval[vec 0:real^1,vec 1]`] o
   MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_HOMOTOPY_ALT)) THEN
  ASM_SIMP_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_CONST; SUBSET; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[pathstart; ENDS_IN_UNIT_INTERVAL; PATHSTART_IN_PATH_IMAGE;
                  SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^(1,1)finite_sum->real^M` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[o_DEF] THEN
  MATCH_MP_TAC(TAUT `(p /\ q) /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
  CONJ_TAC THENL
   [CONJ_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o
      REWRITE_RULE[RIGHT_FORALL_IMP_THM] o
      ONCE_REWRITE_RULE[IMP_CONJ] o
      REWRITE_RULE[CONJ_ASSOC] o MATCH_MP
       (ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_UNIQUE)) THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THENL
     [MAP_EVERY EXISTS_TAC [`g1:real^1->real^N`; `vec 0:real^1`];
      MAP_EVERY EXISTS_TAC [`g2:real^1->real^N`; `vec 0:real^1`]] THEN
    ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL; UNIT_INTERVAL_NONEMPTY] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path_image; pathstart; pathfinish; path]) THEN
    ASM_REWRITE_TAC[CONNECTED_INTERVAL; pathstart; pathfinish] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN
    (REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST;
               CONTINUOUS_ON_ID] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET));
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
      REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE k s SUBSET c ==> t SUBSET s ==> IMAGE k t SUBSET c`));
      ASM_MESON_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL]] THEN
     SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; FORALL_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART; ENDS_IN_UNIT_INTERVAL]);
     STRIP_TAC THEN
     REWRITE_TAC[TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
     REWRITE_TAC[FORALL_AND_THM] THEN CONJ_TAC THENL
      [ASM_MESON_TAC[pathstart; ENDS_IN_UNIT_INTERVAL]; ALL_TAC] THEN
     FIRST_ASSUM(MATCH_MP_TAC o
      REWRITE_RULE[RIGHT_FORALL_IMP_THM] o
      ONCE_REWRITE_RULE[IMP_CONJ] o
      REWRITE_RULE[CONJ_ASSOC] o MATCH_MP
       (ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_UNIQUE)) THEN
     MAP_EVERY EXISTS_TAC
      [`(\x. pathfinish g1):real^1->real^N`; `vec 0:real^1`] THEN
     ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL; CONNECTED_INTERVAL] THEN
     REWRITE_TAC[CONTINUOUS_ON_CONST; pathfinish] THEN
     REPEAT CONJ_TAC THENL
      [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
       ASM_MESON_TAC[SUBSET; pathfinish; PATHFINISH_IN_PATH_IMAGE];
       GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
       MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
       SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST;
                CONTINUOUS_ON_ID] THEN
       FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
           CONTINUOUS_ON_SUBSET)) THEN
       SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; FORALL_IN_PCROSS;
                FSTCART_PASTECART; SNDCART_PASTECART; ENDS_IN_UNIT_INTERVAL];
       REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
       X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (t:real^1) (vec 1:real^1)` o
         REWRITE_RULE[FORALL_IN_IMAGE] o GEN_REWRITE_RULE I [SUBSET]) THEN
       ASM_REWRITE_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL];
       ASM_MESON_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL];
       REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
       ASM_MESON_TAC[SUBSET; pathfinish; PATHFINISH_IN_PATH_IMAGE]]]);;

let COVERING_SPACE_MONODROMY = prove
 (`!p:real^M->real^N c s g1 g2 h1 h2.
     covering_space (c,p) s /\
     path g1 /\ path_image g1 SUBSET s /\
     path g2 /\ path_image g2 SUBSET s /\
     homotopic_paths s g1 g2 /\
     path h1 /\ path_image h1 SUBSET c /\
     (!t. t IN interval[vec 0,vec 1] ==> p(h1 t) = g1 t) /\
     path h2 /\ path_image h2 SUBSET c /\
     (!t. t IN interval[vec 0,vec 1] ==> p(h2 t) = g2 t) /\
     pathstart h1 = pathstart h2
     ==> pathfinish h1 = pathfinish h2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP COVERING_SPACE_LIFT_HOMOTOPIC_PATHS) THEN
  REWRITE_TAC[HOMOTOPIC_PATHS_IMP_PATHFINISH]);;

let COVERING_SPACE_LIFT_HOMOTOPIC_PATH = prove
 (`!p:real^M->real^N c s f f' g a b.
        covering_space (c,p) s /\
        homotopic_paths s f f' /\
        path g /\ path_image g SUBSET c /\
        pathstart g = a /\ pathfinish g = b /\
        (!t. t IN interval[vec 0,vec 1] ==> p(g t) = f t)
        ==> ?g'. path g' /\ path_image g' SUBSET c /\
                 pathstart g' = a /\ pathfinish g' = b /\
                 (!t. t IN interval[vec 0,vec 1] ==> p(g' t) = f' t)`,
  ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_SUBSET) THEN
  FIRST_ASSUM(MP_TAC o ISPECL [`f':real^1->real^N`; `a:real^M`] o
   MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_PATH_STRONG)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[pathstart; ENDS_IN_UNIT_INTERVAL;
                    HOMOTOPIC_PATHS_IMP_PATHSTART];
      ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g':real^1->real^M` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `pathfinish g:real^M = b`)) THEN
    FIRST_ASSUM(MATCH_MP_TAC o
     MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_MONODROMY)) THEN
    MAP_EVERY EXISTS_TAC [`f':real^1->real^N`; `f:real^1->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let COVERING_SPACE_INESSENTIAL_LOOP_LIFT_IS_LOOP = prove
 (`!p:real^M->real^N c s g h a.
        covering_space (c,p) s /\
        path g /\ path_image g SUBSET s /\ pathfinish g = pathstart g /\
        homotopic_paths s g (linepath(a,a)) /\
        path h /\ path_image h SUBSET c /\
        (!t. t IN interval[vec 0,vec 1] ==> p(h t) = g t)
        ==> pathfinish h = pathstart h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_SUBSET) THEN
  REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHSTART) THEN
  REWRITE_TAC[PATHSTART_LINEPATH] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
    ISPECL [`g:real^1->real^N`; `linepath(a:real^N,a)`;
            `h:real^1->real^M`; `linepath(pathstart h:real^M,pathstart h)`] o
    MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_MONODROMY)) THEN
  ASM_REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN
  ASM_REWRITE_TAC[SING_SUBSET; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[LINEPATH_REFL] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[pathstart] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]]);;

let COVERING_SPACE_SIMPLY_CONNECTED_LOOP_LIFT_IS_LOOP = prove
 (`!p:real^M->real^N c s g h.
        covering_space (c,p) s /\ simply_connected s /\
        path g /\ path_image g SUBSET s /\ pathfinish g = pathstart g /\
        path h /\ path_image h SUBSET c /\
        (!t. t IN interval[vec 0,vec 1] ==> p(h t) = g t)
        ==> pathfinish h = pathstart h`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o
    MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_INESSENTIAL_LOOP_LIFT_IS_LOOP)) THEN
  EXISTS_TAC `g:real^1->real^N` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_PATH]);;

(* ------------------------------------------------------------------------- *)
(* Lifting of general functions to covering space                            *)
(* ------------------------------------------------------------------------- *)

let COVERING_SPACE_LIFT_GENERAL = prove
 (`!p:real^M->real^N c s f:real^P->real^N u a z.
        covering_space (c,p) s /\ a IN c /\ z IN u /\
        path_connected u /\ locally path_connected u /\
        f continuous_on u /\ IMAGE f u SUBSET s /\ f z = p a /\
        (!r. path r /\ path_image r SUBSET u /\
             pathstart r = z /\ pathfinish r = z
             ==> ?q. path q /\ path_image q SUBSET c /\
                     pathstart q = a /\ pathfinish q = a /\
                     homotopic_paths s (f o r) (p o q))
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\ g z = a /\
                (!y. y IN u ==> p(g y) = f y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN u
        ==> ?g h. path g /\ path_image g SUBSET u /\
                  pathstart g = z /\ pathfinish g = y /\
                  path h /\ path_image h SUBSET c /\ pathstart h = a /\
                  (!t. t IN interval[vec 0,vec 1]
                       ==> (p:real^M->real^N)(h t) = (f:real^P->real^N)(g t))`
   (LABEL_TAC "*")
  THENL
   [X_GEN_TAC `y:real^P` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [path_connected]) THEN
    DISCH_THEN(MP_TAC o SPECL [`z:real^P`; `y:real^P`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `g:real^1->real^P` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC  COVERING_SPACE_LIFT_PATH_STRONG THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[GSYM o_DEF] THEN
    ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE; PATHSTART_COMPOSE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?l. !y g h. path g /\ path_image g SUBSET u /\
                pathstart g = z /\ pathfinish g = y /\
                path h /\ path_image h SUBSET c /\ pathstart h = a /\
                (!t. t IN interval[vec 0,vec 1]
                     ==> (p:real^M->real^N)(h t) = (f:real^P->real^N)(g t))
                ==> pathfinish h = l y`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `y:real^P` THEN
    MATCH_MP_TAC(MESON[]
      `(!g h g' h'. P g h /\ P g' h' ==> f h = f h')
       ==> ?z. !g h. P g h ==> f h = z`) THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g ++ reversepath g'):real^1->real^P`) THEN
    ASM_SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
      PATH_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
      SUBSET_PATH_IMAGE_JOIN; PATH_IMAGE_REVERSEPATH] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^M` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o
     ISPECL [`(p:real^M->real^N) o (q:real^1->real^M)`;
             `(f:real^P->real^N) o (g ++ reversepath g')`;
             `q:real^1->real^M`; `pathstart q:real^M`; `pathfinish q:real^M`] o
      MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ]
       (ONCE_REWRITE_RULE[HOMOTOPIC_PATHS_SYM]
         COVERING_SPACE_LIFT_HOMOTOPIC_PATH))) THEN
    ASM_REWRITE_TAC[o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `q':real^1->real^M` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `path(h ++ reversepath h':real^1->real^M)` MP_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[PATH_JOIN_EQ; PATH_REVERSEPATH; PATHSTART_REVERSEPATH]] THEN
    MATCH_MP_TAC PATH_EQ THEN EXISTS_TAC `q':real^1->real^M` THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    STRIP_TAC THEN REWRITE_TAC[joinpaths] THEN COND_CASES_TAC THENL
     [FIRST_ASSUM(MP_TAC o
        ISPECL [`(f:real^P->real^N) o (g:real^1->real^P) o (\t. &2 % t)`;
                `q':real^1->real^M`;
                `(h:real^1->real^M) o (\t. &2 % t)`;
                `interval[vec 0,lift(&1 / &2)]`;
                `vec 0:real^1`; `t:real^1`] o
        MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_UNIQUE)) THEN
      REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
        EXISTS_TAC `(f:real^P->real^N) o (g ++ reversepath g')` THEN
        CONJ_TAC THENL
         [SIMP_TAC[IN_INTERVAL_1; LIFT_DROP; joinpaths; o_THM];
          ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN CONJ_TAC THENL
         [ASM_MESON_TAC[HOMOTOPIC_PATHS_IMP_PATH; path];
          REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
          REAL_ARITH_TAC];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
         `path_image ((f:real^P->real^N) o (g ++ reversepath g'))` THEN
        CONJ_TAC THENL[ALL_TAC; ASM_MESON_TAC[HOMOTOPIC_PATHS_IMP_SUBSET]] THEN
        REWRITE_TAC[path_image] THEN MATCH_MP_TAC(SET_RULE
         `(!x. x IN s ==> f x = g x) /\ s SUBSET t
          ==> IMAGE f s SUBSET IMAGE g t`) THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC; IN_INTERVAL_1] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[joinpaths; o_THM];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        ASM_REWRITE_TAC[GSYM path] THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
         `path_image(q':real^1->real^M)` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[path_image] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `t':real^1` THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(fun th ->
         W(MP_TAC o PART_MATCH (lhand o rand) th o rand o snd)) THEN
        ASM_SIMP_TAC[IN_INTERVAL_1; joinpaths; DROP_VEC] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        ASM_SIMP_TAC[GSYM path] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; LIFT_DROP] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `path_image(h:real^1->real^M)` THEN
        CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
        REWRITE_TAC[path_image; IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1] THEN
        REWRITE_TAC[DROP_VEC; DROP_CMUL; LIFT_DROP] THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `t':real^1` THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN STRIP_TAC THEN
        CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[CONNECTED_INTERVAL];
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM pathstart] THEN
        ASM_REWRITE_TAC[] THEN
        SUBST1_TAC(SYM(ASSUME `pathstart h:real^M = a`)) THEN
        REWRITE_TAC[pathstart] THEN AP_TERM_TAC THEN
        REWRITE_TAC[VECTOR_MUL_RZERO];
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
        ASM_REAL_ARITH_TAC];
      FIRST_ASSUM(MP_TAC o
        ISPECL [`(f:real^P->real^N) o reversepath(g':real^1->real^P) o
                 (\t. &2 % t - vec 1)`;
                `q':real^1->real^M`;
                `reversepath(h':real^1->real^M) o (\t. &2 % t - vec 1)`;
                `{t | &1 / &2 < drop t /\ drop t <= &1}`;
                `vec 1:real^1`; `t:real^1`] o
        MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT_UNIQUE)) THEN
      REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
        EXISTS_TAC `(f:real^P->real^N) o (g ++ reversepath g')` THEN
        CONJ_TAC THENL
         [SIMP_TAC[IN_ELIM_THM; GSYM REAL_NOT_LE; joinpaths; o_THM];
          ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN CONJ_TAC THENL
         [ASM_MESON_TAC[HOMOTOPIC_PATHS_IMP_PATH; path];
          REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
          REAL_ARITH_TAC];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
         `path_image ((f:real^P->real^N) o (g ++ reversepath g'))` THEN
        CONJ_TAC THENL[ALL_TAC; ASM_MESON_TAC[HOMOTOPIC_PATHS_IMP_SUBSET]] THEN
        REWRITE_TAC[path_image] THEN MATCH_MP_TAC(SET_RULE
         `(!x. x IN s ==> f x = g x) /\ s SUBSET t
          ==> IMAGE f s SUBSET IMAGE g t`) THEN
        SIMP_TAC[IN_ELIM_THM; GSYM REAL_NOT_LE; joinpaths; o_THM] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        ASM_REWRITE_TAC[GSYM path] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
         `path_image(q':real^1->real^M)` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[path_image] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `t':real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(fun th ->
         W(MP_TAC o PART_MATCH (lhand o rand) th o rand o snd)) THEN
        ASM_SIMP_TAC[IN_INTERVAL_1; joinpaths; DROP_VEC; GSYM REAL_NOT_LT] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID;
                 CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        ASM_SIMP_TAC[GSYM path; PATH_REVERSEPATH] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; DROP_SUB] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `path_image(reversepath h':real^1->real^M)` THEN
        CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[PATH_IMAGE_REVERSEPATH]] THEN
        REWRITE_TAC[path_image; IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; DROP_SUB] THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `t':real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        REWRITE_TAC[reversepath] THEN CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC; DROP_CMUL] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1; IS_INTERVAL_1] THEN
        REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
        REWRITE_TAC[IN_ELIM_THM; DROP_VEC] THEN REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM pathfinish] THEN
        ASM_REWRITE_TAC[reversepath] THEN
        SUBST1_TAC(SYM(ASSUME `pathstart h':real^M = a`)) THEN
        REWRITE_TAC[pathstart] THEN AP_TERM_TAC THEN
        REWRITE_TAC[GSYM DROP_EQ; DROP_SUB; DROP_CMUL; DROP_VEC] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^P->real^M` THEN
  DISCH_THEN(LABEL_TAC "+") THEN
  MATCH_MP_TAC(TAUT `(q ==> p) /\ q ==> p /\ q`) THEN REPEAT CONJ_TAC THENL
   [STRIP_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^P` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `y:real^P`) THEN
    ASM_MESON_TAC[PATHFINISH_IN_PATH_IMAGE; SUBSET];
    FIRST_ASSUM(MP_TAC o SPECL
     [`z:real^P`; `linepath(z:real^P,z)`; `linepath(a:real^M,a)`]) THEN
    REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ASM_SIMP_TAC[LINEPATH_REFL; SING_SUBSET];
    X_GEN_TAC `y:real^P` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `y:real^P`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`g:real^1->real^P`; `h:real^1->real^M`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`y:real^P`; `g:real^1->real^P`; `h:real^1->real^M`]) THEN
    ASM_MESON_TAC[pathfinish; ENDS_IN_UNIT_INTERVAL]] THEN
  FIRST_ASSUM(fun th ->
   GEN_REWRITE_TAC I [MATCH_MP CONTINUOUS_ON_OPEN_GEN th]) THEN
  X_GEN_TAC `n:real^M->bool` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `y:real^P` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [open_in]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `(f:real^P->real^N) y` o last o CONJUNCTS o
        GEN_REWRITE_RULE I [covering_space]) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:(real^M->bool)->bool` MP_TAC) THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `(l:real^P->real^M) y`) THEN
  MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_UNIONS]] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':real^M->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `w':real^M->bool`) MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `w':real^M->bool` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `p':real^N->real^M`) THEN
  DISCH_TAC THEN UNDISCH_THEN `(w':real^M->bool) IN vv` (K ALL_TAC) THEN
  SUBGOAL_THEN
   `?v. y IN v /\ y IN u /\ IMAGE (f:real^P->real^N) v SUBSET w /\
        v SUBSET u /\ path_connected v /\ open_in (subtopology euclidean u) v`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LOCALLY_PATH_CONNECTED]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`{x | x IN u /\ (f:real^P->real^N) x IN w}`; `y:real^P`]) THEN
    ANTS_TAC THENL [ALL_TAC; MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(w':real^M->bool) SUBSET c /\ (w:real^N->bool) SUBSET s`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[open_in]; ALL_TAC] THEN
  EXISTS_TAC
   `v INTER
    {x | x IN u /\ (f:real^P->real^N) x IN
                   {x | x IN w /\ (p':real^N->real^M) x IN w' INTER n}}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `w:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `w':real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
    UNDISCH_TAC `open_in (subtopology euclidean c) (n:real^M->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `y':real^P` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [path_connected]) THEN
  DISCH_THEN(MP_TAC o SPECL [`y:real^P`; `y':real^P`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^1->real^P` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `y:real^P`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`pp:real^1->real^P`; `qq:real^1->real^M`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL
   [`y':real^P`; `(pp:real^1->real^P) ++ r`;
    `(qq:real^1->real^M) ++ ((p':real^N->real^M) o (f:real^P->real^N) o
                            (r:real^1->real^P))`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`y:real^P`; `pp:real^1->real^P`; `qq:real^1->real^M`]) THEN
  ASM_SIMP_TAC[o_THM; PATHSTART_JOIN; PATHFINISH_JOIN] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `path_image ((pp:real^1->real^P) ++ r) SUBSET u`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN ASM SET_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[PATHFINISH_COMPOSE] THEN ASM_MESON_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[PATH_JOIN];
    ASM_SIMP_TAC[SUBSET_PATH_IMAGE_JOIN];
    MATCH_MP_TAC PATH_JOIN_IMP THEN ASM_SIMP_TAC[PATHSTART_COMPOSE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      CONJ_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
             CONTINUOUS_ON_SUBSET)) THEN
      ASM SET_TAC[];
      REWRITE_TAC[pathfinish] THEN ASM SET_TAC[]];
    MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN ASM SET_TAC[];
    X_GEN_TAC `tt:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    STRIP_TAC THEN REWRITE_TAC[joinpaths; o_THM] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [ABBREV_TAC `t:real^1 = &2 % tt`;
      ABBREV_TAC `t:real^1 = &2 % tt - vec 1`] THEN
    (SUBGOAL_THEN `t IN interval[vec 0:real^1,vec 1]` ASSUME_TAC THENL
      [EXPAND_TAC "t" THEN
       REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; DROP_CMUL; DROP_SUB] THEN
       ASM_REAL_ARITH_TAC;
       ALL_TAC]) THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path_image]) THEN ASM SET_TAC[]]);;

let COVERING_SPACE_LIFT_STRONGER = prove
 (`!p:real^M->real^N c s f:real^P->real^N u a z.
        covering_space (c,p) s /\ a IN c /\ z IN u /\
        path_connected u /\ locally path_connected u /\
        f continuous_on u /\ IMAGE f u SUBSET s /\ f z = p a /\
        (!r. path r /\ path_image r SUBSET u /\
             pathstart r = z /\ pathfinish r = z
             ==> ?b. homotopic_paths s (f o r) (linepath(b,b)))
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\ g z = a /\
                (!y. y IN u ==> p(g y) = f y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_LIFT_GENERAL)) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real^1->real^P` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC  `r:real^1->real^P`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:real^N`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHSTART) THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHSTART_LINEPATH] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  EXISTS_TAC `linepath(a:real^M,a)` THEN
  REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_DEF; LINEPATH_REFL]) THEN
  ASM_REWRITE_TAC[o_DEF; LINEPATH_REFL]);;

let COVERING_SPACE_LIFT_STRONG = prove
 (`!p:real^M->real^N c s f:real^P->real^N u a z.
        covering_space (c,p) s /\ a IN c /\ z IN u /\
        simply_connected u /\ locally path_connected u /\
        f continuous_on u /\ IMAGE f u SUBSET s /\ f z = p a
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\ g z = a /\
                (!y. y IN u ==> p(g y) = f y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_LIFT_STRONGER)) THEN
  ASM_SIMP_TAC[SIMPLY_CONNECTED_IMP_PATH_CONNECTED] THEN
  X_GEN_TAC `r:real^1->real^P` THEN STRIP_TAC THEN
  EXISTS_TAC `(f:real^P->real^N) z` THEN
  SUBGOAL_THEN
   `linepath(f z,f z) = (f:real^P->real^N) o linepath(z,z)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF; LINEPATH_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_CONTINUOUS_IMAGE THEN
  EXISTS_TAC `u:real^P->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I
   [SIMPLY_CONNECTED_EQ_HOMOTOPIC_PATHS]) THEN
  ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET]);;

let COVERING_SPACE_LIFT = prove
 (`!p:real^M->real^N c s f:real^P->real^N u.
        covering_space (c,p) s /\
        simply_connected u /\ locally path_connected u /\
        f continuous_on u /\ IMAGE f u SUBSET s
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET c /\
                (!y. y IN u ==> p(g y) = f y)`,
  MP_TAC COVERING_SPACE_LIFT_STRONG THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th THEN ASM_REWRITE_TAC[]) THEN
  ASM_CASES_TAC `u:real^P->bool = {}` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_EMPTY; IMAGE_CLAUSES; EMPTY_SUBSET;
                  NOT_IN_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^P`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real^P->real^N) a`) THEN
  MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_IMAGE]] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some additional lemmas about covering spaces.                             *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_COVERING_MAP_FIBRES = prove
 (`!p:real^M->real^N c s a b.
        covering_space (c,p) s /\ path_connected s /\ a IN s /\ b IN s
        ==> {x | x IN c /\ p(x) = a} =_c {x | x IN c /\ p(x) = b}`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; FORALL_AND_THM;
              TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2 BINDER_CONV o LAND_CONV)
   [CONJ_SYM] THEN
  MATCH_MP_TAC(MESON[]
   `(!a b. P a b) ==> (!a b. P a b) /\ (!a b. P b a)`) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`] o
    GEN_REWRITE_RULE I [path_connected]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:real^1->real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. ?h. z IN c /\ p z = a
            ==> path h /\ path_image h SUBSET c /\ pathstart h = z /\
                !t. t IN interval[vec 0,vec 1]
                    ==> (p:real^M->real^N)(h t) = g t`
  MP_TAC THENL
   [REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC COVERING_SPACE_LIFT_PATH_STRONG THEN
    REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `h:real^M->real^1->real^M` THEN DISCH_TAC] THEN
  REWRITE_TAC[le_c; IN_ELIM_THM] THEN
  EXISTS_TAC `\z. pathfinish((h:real^M->real^1->real^M) z)` THEN
  ASM_REWRITE_TAC[pathfinish] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[SUBSET; path_image; pathstart; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[pathfinish; ENDS_IN_UNIT_INTERVAL];
    MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`p:real^M->real^N`; `c:real^M->bool`; `s:real^N->bool`;
      `reversepath(g:real^1->real^N)`; `reversepath(g:real^1->real^N)`;
      `reversepath((h:real^M->real^1->real^M) x)`;
      `reversepath((h:real^M->real^1->real^M) y)`]
    COVERING_SPACE_MONODROMY) THEN
    ASM_SIMP_TAC[PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
                 HOMOTOPIC_PATHS_REFL] THEN
    ASM_REWRITE_TAC[pathfinish; reversepath; IN_INTERVAL_1; DROP_VEC] THEN
    REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`);
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^M`)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_VEC] THEN ASM_REAL_ARITH_TAC]);;

let COVERING_SPACE_INJECTIVE = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s /\ path_connected c /\ simply_connected s
        ==> (!x y. x IN c /\ y IN c /\ p x = p y ==> x = y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP COVERING_SPACE_IMP_CONTINUOUS) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [path_connected]) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `y:real^M`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^M` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_LIFT_PATH_STRONG)) THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `(p:real^M->real^N) o (g:real^1->real^M)` th) THEN
    MP_TAC(SPEC `(p:real^M->real^N) o linepath(x:real^M,x)` th)) THEN
  SUBGOAL_THEN
   `(path ((p:real^M->real^N) o linepath(x,x)) /\
     path (p o g)) /\
    (path_image (p o linepath(x:real^M,x)) SUBSET s /\
     path_image (p o g) SUBSET s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_SING; SEGMENT_REFL] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REWRITE_TAC[PATH_IMAGE_COMPOSE; PATH_IMAGE_LINEPATH] THEN
      REWRITE_TAC[SEGMENT_REFL] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHSTART_LINEPATH] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real^1->real^M` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:real^1->real^M` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o
    SPECL [`(p:real^M->real^N) o linepath(x:real^M,x)`;
           `(p:real^M->real^N) o (g:real^1->real^M)`;
           `h1:real^1->real^M`; `h2:real^1->real^M`] o
  MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_MONODROMY)) THEN
  ASM_SIMP_TAC[] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
        GEN_REWRITE_RULE I [SIMPLY_CONNECTED_EQ_HOMOTOPIC_PATHS]) THEN
    ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
    ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `pathfinish(linepath(x:real^M,x))` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[PATHFINISH_LINEPATH]];
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th])] THEN
  REWRITE_TAC[pathfinish] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_LIFT_UNIQUE))
  THENL
   [EXISTS_TAC `(p:real^M->real^N) o (h1:real^1->real^M)`;
    EXISTS_TAC `(p:real^M->real^N) o (h2:real^1->real^M)`] THEN
  MAP_EVERY EXISTS_TAC [`interval[vec 0:real^1,vec 1]`; `vec 0:real^1`] THEN
  REWRITE_TAC[CONNECTED_INTERVAL; ENDS_IN_UNIT_INTERVAL] THEN
  ASM_REWRITE_TAC[GSYM path; PATH_LINEPATH; GSYM path_image] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_THM]) THEN ASM_REWRITE_TAC[o_THM] THEN
  ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pathstart]) THEN
  ASM_REWRITE_TAC[LINEPATH_REFL; PATH_IMAGE_COMPOSE] THEN
  (CONJ_TAC THENL
    [ASM_MESON_TAC[PATH_CONTINUOUS_IMAGE; CONTINUOUS_ON_SUBSET];
     ASM SET_TAC[]]));;

let COVERING_SPACE_HOMEOMORPHISM = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s /\ path_connected c /\ simply_connected s
        ==> ?q. homeomorphism (c,s) (p,q)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_INJECTIVE_OPEN_MAP THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[COVERING_SPACE_IMP_CONTINUOUS];
    ASM_MESON_TAC[COVERING_SPACE_IMP_SURJECTIVE];
    ASM_MESON_TAC[COVERING_SPACE_INJECTIVE];
    ASM_MESON_TAC[COVERING_SPACE_OPEN_MAP]]);;

(* ------------------------------------------------------------------------- *)
(* Results on finiteness of the number of sheets in a covering space.        *)
(* ------------------------------------------------------------------------- *)

let COVERING_SPACE_FIBRE_NO_LIMPT = prove
 (`!p:real^M->real^N c s a b.
        covering_space (c,p) s /\ a IN c
        ==> ~(a limit_point_of {x | x IN c /\ p x = b})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [covering_space]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(p:real^M->real^N) a`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:(real^M->bool)->bool` MP_TAC) THEN
  GEN_REWRITE_TAC I [IMP_CONJ] THEN
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `t:real^M->bool`)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:real^N->real^M` MP_TAC) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  UNDISCH_TAC `open_in (subtopology euclidean c) (t:real^M->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^M->bool` o
        GEN_REWRITE_RULE I [LIMPT_INFINITE_OPEN]) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[INFINITE]] THEN
  MATCH_MP_TAC(MESON[FINITE_SING; FINITE_SUBSET]
   `(?a. s SUBSET {a}) ==> FINITE s`) THEN
  ASM SET_TAC[]);;

let COVERING_SPACE_COUNTABLE_SHEETS = prove
 (`!p:real^M->real^N c s b.
        covering_space (c,p) s ==> COUNTABLE {x | x IN c /\ p x = b}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM]
        UNCOUNTABLE_CONTAINS_LIMIT_POINT)) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[COVERING_SPACE_FIBRE_NO_LIMPT]);;

let COVERING_SPACE_FINITE_EQ_COMPACT_FIBRE = prove
 (`!p:real^M->real^N c s b.
        covering_space (c,p) s
        ==> (FINITE {x | x IN c /\ p x = b} <=>
             compact {x | x IN c /\ p x = b})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[FINITE_IMP_COMPACT] THEN
  DISCH_TAC THEN ASM_CASES_TAC `(b:real^N) IN s` THENL
   [ONCE_REWRITE_TAC[TAUT `p <=> (~p ==> F)`] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o
     SPEC `{x | x IN c /\ (p:real^M->real^N) x = b}` o
     GEN_REWRITE_RULE I [COMPACT_EQ_BOLZANO_WEIERSTRASS]) THEN
    ASM_REWRITE_TAC[INFINITE; SUBSET_REFL; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^M` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^M`; `b:real^N`] o
       MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        COVERING_SPACE_FIBRE_NO_LIMPT)) THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `{x  | x IN c /\ (p:real^M->real^N) x = b} = {}`
     (fun th -> REWRITE_TAC[th; FINITE_EMPTY]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
    ASM SET_TAC[]]);;

let COVERING_SPACE_CLOSED_MAP = prove
 (`!p:real^M->real^N c s t.
        covering_space (c,p) s /\
        (!b. b IN s ==> FINITE {x | x IN c /\ p x = b}) /\
        closed_in (subtopology euclidean c) t
        ==> closed_in (subtopology euclidean s) (IMAGE p t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [ASM SET_TAC[]; ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN]] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o last o CONJUNCTS o
    GEN_REWRITE_RULE I [covering_space]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `v:real^N->bool` THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `uu:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `uu:(real^M->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[UNIONS_0; NOT_IN_EMPTY] THEN ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `INTERS {IMAGE (p:real^M->real^N) (u DIFF t) | u IN uu}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTERS THEN
    ASM_REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN
      SUBGOAL_THEN
       `!u. u IN uu ==> ?x. x IN u /\ (p:real^M->real^N) x = y`
      ASSUME_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `FINITE (IMAGE (\u. @x. x IN u /\ (p:real^M->real^N) x = y) uu)`
      MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          FINITE_SUBSET)) THEN ASM SET_TAC[];
        MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
        REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN ASM SET_TAC[]];
      X_GEN_TAC `u:real^M->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `v:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN EXISTS_TAC `u:real^M->bool` THEN
      ASM_SIMP_TAC[LEFT_EXISTS_AND_THM] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSED_IN_CLOSED]) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
      EXISTS_TAC `(:real^M) DIFF k` THEN
      ASM_REWRITE_TAC[GSYM closed] THEN ASM SET_TAC[]];
    REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `u:real^M->bool` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `u:real^M->bool`)) THEN
    ASM_REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET; INTERS_GSPEC; IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_IMAGE]] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^M` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^M`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `q /\ r /\ ~s ==> ~(s <=> q /\ r)`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[IN_UNIONS] THEN ASM SET_TAC[]]);;

let COVERING_SPACE_FINITE_SHEETS_EQ_CLOSED_MAP_STRONG = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s /\ (!b. b IN s ==> b limit_point_of s)
        ==> ((!b. b IN s ==> FINITE {x | x IN c /\ p x = b}) <=>
             (!t. closed_in (subtopology euclidean c) t
                  ==> closed_in (subtopology euclidean s) (IMAGE p t)))`,
  let lemma = prove
   (`!f:num->real^N.
          (!n. ~(s = v n) ==> DISJOINT s (v n))
          ==> (!n. f n IN v n) /\
              (!m n. v m = v n <=> m = n)
              ==> ?n. IMAGE f (:num) INTER s SUBSET {f n}`,
    ASM_CASES_TAC `?n. s = (v:num->real^N->bool) n` THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
        MP_TAC th THEN MATCH_MP_TAC MONO_EXISTS);
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[]] THEN
    ASM SET_TAC[]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC COVERING_SPACE_CLOSED_MAP THEN
    EXISTS_TAC `c:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MESON[INFINITE] `FINITE s <=> ~INFINITE s`] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `b:real^N` o last o CONJUNCTS o
    GEN_REWRITE_RULE I [covering_space]) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `t:real^N->bool` THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(b:real^N) limit_point_of t` MP_TAC THENL
   [MATCH_MP_TAC LIMPT_OF_OPEN_IN THEN ASM_MESON_TAC[];
    PURE_REWRITE_TAC[LIMPT_SEQUENTIAL_INJ]] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `INFINITE(vv:(real^M->bool)->bool)` MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CARD_LE_INFINITE)) THEN REWRITE_TAC[le_c] THEN
    SUBGOAL_THEN
      `!x. ?v. x IN c /\ (p:real^M->real^N) x = b ==> v IN vv /\ x IN v`
    MP_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[SKOLEM_THM]] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^M->real^M->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `x:real^M` th) THEN MP_TAC(SPEC `y:real^M` th)) THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INFINITE_CARD_LE; le_c; INJECTIVE_ON_ALT] THEN
  REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:num->real^M->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_THEN
    `!u. u IN vv ==> ?q:real^N->real^M. homeomorphism (u,t) (p,q)`
    (MP_TAC o GEN `n:num` o SPEC `(v:num->real^M->bool) n`) THEN
  ASM_REWRITE_TAC[SKOLEM_THM; homeomorphism; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->real^N->real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `closed_in (subtopology euclidean s)
              (IMAGE (p:real^M->real^N) (IMAGE (\n. q n (y n:real^N)) (:num)))`
  MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[CLOSED_IN_LIMPT; SUBSET; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; X_GEN_TAC `a:real^M`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LIMPT_OF_SEQUENCE_SUBSEQUENCE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(p:real^M->real^N) a = b` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
      EXISTS_TAC
       `(p:real^M->real^N) o (\n:num. q n (y n :real^N)) o (r:num->num)` THEN
      REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(GEN_ALL(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
        (fst(EQ_IMP_RULE(SPEC_ALL CONTINUOUS_ON_SEQUENTIALLY))))) THEN
        EXISTS_TAC `c:real^M->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[COVERING_SPACE_IMP_CONTINUOUS];
          REWRITE_TAC[o_DEF] THEN ASM SET_TAC[]];
        REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC LIM_SUBSEQUENCE THEN
        ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (REWRITE_RULE[IMP_CONJ_ALT] LIM_TRANSFORM_EVENTUALLY)) THEN
        MATCH_MP_TAC ALWAYS_EVENTUALLY THEN REWRITE_TAC[o_DEF] THEN
        ASM SET_TAC[]];
      SUBGOAL_THEN `?u. u IN vv /\ (a:real^M) IN u` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `?w:real^M->bool. open w /\ u = c INTER w`
       (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))
      THENL [ASM_MESON_TAC[OPEN_IN_OPEN]; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIMPT_INFINITE_OPEN]) THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^M->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
       `INFINITE s ==> !k. s INTER k = s ==> INFINITE(s INTER k)`)) THEN
      DISCH_THEN(MP_TAC o SPEC `c:real^M->bool`) THEN ANTS_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[INTER_ASSOC]] THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[INFINITE] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
      DISCH_THEN(MP_TAC o SPEC `c INTER w:real^M->bool`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `(v:num->real^M->bool) n`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `\n. (q:num->real^N->real^M) n (y n)` o
        MATCH_MP lemma) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MESON_TAC[FINITE_SUBSET; FINITE_SING; INTER_COMM]];
    SUBGOAL_THEN
     `IMAGE (p:real^M->real^N) (IMAGE (\n. q n (y n:real^N)) (:num)) =
      IMAGE y (:num)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CLOSED_IN_LIMPT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `b:real^N`)) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[LIMPT_SEQUENTIAL_INJ] THEN
    EXISTS_TAC `y:num->real^N` THEN ASM SET_TAC[]]);;

let COVERING_SPACE_FINITE_SHEETS_EQ_CLOSED_MAP = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s /\ connected s /\ ~(?a. s = {a})
        ==> ((!b. b IN s ==> FINITE {x | x IN c /\ p x = b}) <=>
             (!t. closed_in (subtopology euclidean c) t
                  ==> closed_in (subtopology euclidean s) (IMAGE p t)))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [SUBGOAL_THEN `c:real^M->bool = {}` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
      ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
      ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_EMPTY; CLOSED_IN_SUBTOPOLOGY_EMPTY;
                      IMAGE_EQ_EMPTY; NOT_IN_EMPTY]];
    MATCH_MP_TAC COVERING_SPACE_FINITE_SHEETS_EQ_CLOSED_MAP_STRONG THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONNECTED_IMP_PERFECT THEN ASM SET_TAC[]]);;

let COVERING_SPACE_FINITE_SHEETS_EQ_PROPER_MAP = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> ((!b. b IN s ==> FINITE {x | x IN c /\ p x = b}) <=>
             (!k. k SUBSET s /\ compact k
                  ==> compact {x | x IN c /\ p(x) IN k}))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE `s = t ==> s SUBSET t`)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP PROPER_MAP th]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC
   [GSYM(MATCH_MP COVERING_SPACE_FINITE_EQ_COMPACT_FIBRE th)]) THEN
  REWRITE_TAC[TAUT `(p <=> q /\ p) <=> (p ==> q)`] THEN
  ASM_MESON_TAC[COVERING_SPACE_CLOSED_MAP]);;

(* ------------------------------------------------------------------------- *)
(* Special cases where one or both of the sets is compact.                   *)
(* ------------------------------------------------------------------------- *)

let COVERING_SPACE_FINITE_SHEETS = prove
 (`!p:real^M->real^N c s b.
      covering_space (c,p) s /\ compact c ==> FINITE {x | x IN c /\ p x = b}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BOLZANO_WEIERSTRASS_CONTRAPOS THEN
  EXISTS_TAC `c:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_RESTRICT] THEN
  ASM_MESON_TAC[COVERING_SPACE_FIBRE_NO_LIMPT]);;

let COVERING_SPACE_COMPACT = prove
 (`!p:real^M->real^N c s.
        covering_space (c,p) s
        ==> (compact c <=>
             compact s /\ (!b. b IN s ==> FINITE {x | x IN c /\ p x = b}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[covering_space; COMPACT_CONTINUOUS_IMAGE];
    MATCH_MP_TAC COVERING_SPACE_FINITE_SHEETS THEN ASM_MESON_TAC[];
    FIRST_ASSUM(MP_TAC o
      MATCH_MP COVERING_SPACE_FINITE_SHEETS_EQ_PROPER_MAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COVERING_SPACE_IMP_SURJECTIVE) THEN
    SET_TAC[]]);;
