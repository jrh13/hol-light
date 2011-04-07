(* ========================================================================= *)
(* Elementary topology in Euclidean space.                                   *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

needs "Multivariate/determinants.ml";;

(* ------------------------------------------------------------------------- *)
(* General notion of a topology.                                             *)
(* ------------------------------------------------------------------------- *)

let istopology = new_definition
 `istopology L <=>
        {} IN L /\
        (!s t. s IN L /\ t IN L ==> (s INTER t) IN L) /\
        (!k. k SUBSET L ==> (UNIONS k) IN L)`;;

let topology_tybij_th = prove
 (`?t:(A->bool)->bool. istopology t`,
  EXISTS_TAC `UNIV:(A->bool)->bool` THEN REWRITE_TAC[istopology; IN_UNIV]);;

let topology_tybij =
  new_type_definition "topology" ("topology","open_in") topology_tybij_th;;

let ISTOPOLOGY_OPEN_IN = prove
 (`istopology(open_in top)`,
  MESON_TAC[topology_tybij]);;

let TOPOLOGY_EQ = prove
 (`!top1 top2. top1 = top2 <=> !s. open_in top1 s <=> open_in top2 s`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[ETA_AX] THEN MESON_TAC[topology_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Infer the "universe" from union of all sets in the topology.              *)
(* ------------------------------------------------------------------------- *)

let topspace = new_definition
 `topspace top = UNIONS {s | open_in top s}`;;

(* ------------------------------------------------------------------------- *)
(* Main properties of open sets.                                             *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_CLAUSES = prove
 (`!top:(A)topology.
        open_in top {} /\
        (!s t. open_in top s /\ open_in top t ==> open_in top (s INTER t)) /\
        (!k. (!s. s IN k ==> open_in top s) ==> open_in top (UNIONS k))`,
  SIMP_TAC[IN; SUBSET; SIMP_RULE[istopology; IN; SUBSET] ISTOPOLOGY_OPEN_IN]);;

let OPEN_IN_SUBSET = prove
 (`!top s. open_in top s ==> s SUBSET (topspace top)`,
  REWRITE_TAC[topspace] THEN SET_TAC[]);;

let OPEN_IN_EMPTY = prove
 (`!top. open_in top {}`,
  REWRITE_TAC[OPEN_IN_CLAUSES]);;

let OPEN_IN_INTER = prove
 (`!top s t. open_in top s /\ open_in top t ==> open_in top (s INTER t)`,
  REWRITE_TAC[OPEN_IN_CLAUSES]);;

let OPEN_IN_UNIONS = prove
 (`!top k. (!s. s IN k ==> open_in top s) ==> open_in top (UNIONS k)`,
  REWRITE_TAC[OPEN_IN_CLAUSES]);;

let OPEN_IN_UNION = prove
 (`!top s t. open_in top s /\ open_in top t ==> open_in top (s UNION t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM UNIONS_2] THEN
  MATCH_MP_TAC OPEN_IN_UNIONS THEN ASM SET_TAC[]);;

let OPEN_IN_TOPSPACE = prove
 (`!top. open_in top (topspace top)`,
  SIMP_TAC[topspace; OPEN_IN_UNIONS; IN_ELIM_THM]);;

let OPEN_IN_SUBOPEN = prove
 (`!top s:A->bool.
        open_in top s <=>
        !x. x IN s ==> ?t. open_in top t /\ x IN t /\ t SUBSET s`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[GSYM FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_UNIONS) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Closed sets.                                                              *)
(* ------------------------------------------------------------------------- *)

let closed_in = new_definition
 `closed_in top s <=>
        s SUBSET (topspace top) /\ open_in top (topspace top DIFF s)`;;

let CLOSED_IN_SUBSET = prove
 (`!top s. closed_in top s ==> s SUBSET (topspace top)`,
  MESON_TAC[closed_in]);;

let CLOSED_IN_EMPTY = prove
 (`!top. closed_in top {}`,
  REWRITE_TAC[closed_in; EMPTY_SUBSET; DIFF_EMPTY; OPEN_IN_TOPSPACE]);;

let CLOSED_IN_TOPSPACE = prove
 (`!top. closed_in top (topspace top)`,
  REWRITE_TAC[closed_in; SUBSET_REFL; DIFF_EQ_EMPTY; OPEN_IN_EMPTY]);;

let CLOSED_IN_UNION = prove
 (`!top s t. closed_in top s /\ closed_in top t ==> closed_in top (s UNION t)`,
  SIMP_TAC[closed_in; UNION_SUBSET; OPEN_IN_INTER;
           SET_RULE `u DIFF (s UNION t) = (u DIFF s) INTER (u DIFF t)`]);;

let CLOSED_IN_INTERS = prove
 (`!top k:(A->bool)->bool.
        ~(k = {}) /\ (!s. s IN k ==> closed_in top s)
        ==> closed_in top (INTERS k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[closed_in] THEN REPEAT STRIP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace top DIFF INTERS k :A->bool =
                UNIONS {topspace top DIFF s | s IN k}` SUBST1_TAC
  THENL [ALL_TAC; MATCH_MP_TAC OPEN_IN_UNIONS THEN ASM SET_TAC[]] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  REWRITE_TAC[IN_UNIONS; IN_INTERS; IN_DIFF; EXISTS_IN_IMAGE] THEN
  MESON_TAC[]);;

let CLOSED_IN_INTER = prove
 (`!top s t. closed_in top s /\ closed_in top t ==> closed_in top (s INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_2] THEN
  MATCH_MP_TAC CLOSED_IN_INTERS THEN ASM SET_TAC[]);;

let OPEN_IN_CLOSED_IN_EQ = prove
 (`!top s. open_in top s <=>
           s SUBSET topspace top /\ closed_in top (topspace top DIFF s)`,
  REWRITE_TAC[closed_in; SET_RULE `(u DIFF s) SUBSET u`] THEN
  REWRITE_TAC[SET_RULE `u DIFF (u DIFF s) = u INTER s`] THEN
  MESON_TAC[OPEN_IN_SUBSET; SET_RULE `s SUBSET t ==> t INTER s = s`]);;

let OPEN_IN_CLOSED_IN = prove
 (`!s u. s SUBSET topspace top
         ==> (open_in top s <=> closed_in top (topspace top DIFF s))`,
  SIMP_TAC[OPEN_IN_CLOSED_IN_EQ]);;

let OPEN_IN_DIFF = prove
 (`!top s t:A->bool.
      open_in top s /\ closed_in top t ==> open_in top (s DIFF t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s DIFF t :A->bool = s INTER (topspace top DIFF t)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_MESON_TAC[closed_in]]);;

let CLOSED_IN_DIFF = prove
 (`!top s t:A->bool.
        closed_in top s /\ open_in top t ==> closed_in top (s DIFF t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s DIFF t :A->bool = s INTER (topspace top DIFF t)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN SET_TAC[];
    MATCH_MP_TAC CLOSED_IN_INTER THEN ASM_MESON_TAC[OPEN_IN_CLOSED_IN_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Subspace topology.                                                        *)
(* ------------------------------------------------------------------------- *)

let subtopology = new_definition
 `subtopology top u = topology {s INTER u | open_in top s}`;;

let ISTOPLOGY_SUBTOPOLOGY = prove
 (`!top u:A->bool. istopology {s INTER u | open_in top s}`,
  REWRITE_TAC[istopology; SET_RULE
   `{s INTER u | open_in top s} =
    IMAGE (\s. s INTER u) {s | open_in top s}`] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[SUBSET_IMAGE; IN_IMAGE; IN_ELIM_THM; SUBSET] THEN
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `{}:A->bool` THEN REWRITE_TAC[OPEN_IN_EMPTY; INTER_EMPTY];
    SIMP_TAC[SET_RULE `(s INTER u) INTER t INTER u = (s INTER t) INTER u`] THEN
    ASM_MESON_TAC[OPEN_IN_INTER];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:(A->bool)->bool`; `g:(A->bool)->bool`] THEN
    STRIP_TAC THEN EXISTS_TAC `UNIONS g :A->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_UNIONS; INTER_UNIONS] THEN SET_TAC[]]);;

let OPEN_IN_SUBTOPOLOGY = prove
 (`!top u s. open_in (subtopology top u) s <=>
                ?t. open_in top t /\ s = t INTER u`,
  REWRITE_TAC[subtopology] THEN
  SIMP_TAC[REWRITE_RULE[CONJUNCT2 topology_tybij] ISTOPLOGY_SUBTOPOLOGY] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM]);;

let TOPSPACE_SUBTOPOLOGY = prove
 (`!top u. topspace(subtopology top u) = topspace top INTER u`,
  REWRITE_TAC[topspace; OPEN_IN_SUBTOPOLOGY; INTER_UNIONS] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM]);;

let CLOSED_IN_SUBTOPOLOGY = prove
 (`!top u s. closed_in (subtopology top u) s <=>
                ?t:A->bool. closed_in top t /\ s = t INTER u`,
  REWRITE_TAC[closed_in; TOPSPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[SUBSET_INTER; OPEN_IN_SUBTOPOLOGY; RIGHT_AND_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `topspace top DIFF t :A->bool` THEN
  ASM_SIMP_TAC[CLOSED_IN_TOPSPACE; OPEN_IN_DIFF; CLOSED_IN_DIFF;
               OPEN_IN_TOPSPACE] THEN
  ASM SET_TAC[]);;

let OPEN_IN_SUBTOPOLOGY_REFL = prove
 (`!top u:A->bool. open_in (subtopology top u) u <=> u SUBSET topspace top`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s INTER t SUBSET u`) THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET];
    DISCH_TAC THEN EXISTS_TAC `topspace top:A->bool` THEN
    REWRITE_TAC[OPEN_IN_TOPSPACE] THEN ASM SET_TAC[]]);;

let CLOSED_IN_SUBTOPOLOGY_REFL = prove
 (`!top u:A->bool. closed_in (subtopology top u) u <=> u SUBSET topspace top`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s INTER t SUBSET u`) THEN
    ASM_SIMP_TAC[CLOSED_IN_SUBSET];
    DISCH_TAC THEN EXISTS_TAC `topspace top:A->bool` THEN
    REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN ASM SET_TAC[]]);;

let SUBTOPOLOGY_SUPERSET = prove
 (`!top s:A->bool. topspace top SUBSET s ==> subtopology top s = top`,
  REPEAT GEN_TAC THEN SIMP_TAC[TOPOLOGY_EQ; OPEN_IN_SUBTOPOLOGY] THEN
  DISCH_TAC THEN X_GEN_TAC `u:A->bool` THEN EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
    DISCH_THEN(fun th -> MP_TAC th THEN
      ASSUME_TAC(MATCH_MP OPEN_IN_SUBSET th)) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[];
    DISCH_TAC THEN EXISTS_TAC `u:A->bool` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[]]);;

let SUBTOPOLOGY_TOPSPACE = prove
 (`!top. subtopology top (topspace top) = top`,
  SIMP_TAC[SUBTOPOLOGY_SUPERSET; SUBSET_REFL]);;

let SUBTOPOLOGY_UNIV = prove
 (`!top. subtopology top UNIV = top`,
  SIMP_TAC[SUBTOPOLOGY_SUPERSET; SUBSET_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* The universal Euclidean versions are what we use most of the time.        *)
(* ------------------------------------------------------------------------- *)

let open_def = new_definition
  `open s <=> !x. x IN s ==> ?e. &0 < e /\ !x'. dist(x',x) < e ==> x' IN s`;;

let closed = new_definition
  `closed(s:real^N->bool) <=> open(UNIV DIFF s)`;;

let euclidean = new_definition
 `euclidean = topology open`;;

let OPEN_EMPTY = prove
 (`open {}`,
  REWRITE_TAC[open_def; NOT_IN_EMPTY]);;

let OPEN_UNIV = prove
 (`open(:real^N)`,
  REWRITE_TAC[open_def; IN_UNIV] THEN MESON_TAC[REAL_LT_01]);;

let OPEN_INTER = prove
 (`!s t. open s /\ open t ==> open (s INTER t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[open_def; AND_FORALL_THM; IN_INTER] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `d1:real`) (X_CHOOSE_TAC `d2:real`)) THEN
  MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN
  ASM_MESON_TAC[REAL_LT_TRANS]);;

let OPEN_UNIONS = prove
 (`(!s. s IN f ==> open s) ==> open(UNIONS f)`,
  REWRITE_TAC[open_def; IN_UNIONS] THEN MESON_TAC[]);;

let OPEN_IN = prove
 (`!s:real^N->bool. open s <=> open_in euclidean s`,
  GEN_TAC THEN REWRITE_TAC[euclidean] THEN CONV_TAC SYM_CONV THEN
  AP_THM_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 topology_tybij)] THEN
  REWRITE_TAC[REWRITE_RULE[IN] istopology] THEN
  REWRITE_TAC[OPEN_EMPTY; OPEN_INTER; SUBSET] THEN
  MESON_TAC[IN; OPEN_UNIONS]);;

let TOPSPACE_EUCLIDEAN = prove
 (`topspace euclidean = (:real^N)`,
  REWRITE_TAC[topspace; EXTENSION; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[OPEN_UNIV; IN_UNIV; OPEN_IN]);;

let TOPSPACE_EUCLIDEAN_SUBTOPOLOGY = prove
 (`!s. topspace (subtopology euclidean s) = s`,
  REWRITE_TAC[TOPSPACE_EUCLIDEAN; TOPSPACE_SUBTOPOLOGY; INTER_UNIV]);;

let CLOSED_IN = prove
 (`!s:real^N->bool. closed s <=> closed_in euclidean s`,
  REWRITE_TAC[closed; closed_in; TOPSPACE_EUCLIDEAN; OPEN_IN; SUBSET_UNIV]);;

let OPEN_UNION = prove
 (`!s t. open s /\ open t ==> open(s UNION t)`,
  REWRITE_TAC[OPEN_IN; OPEN_IN_UNION]);;

let OPEN_SUBOPEN = prove
 (`!s. open s <=> !x. x IN s ==> ?t. open t /\ x IN t /\ t SUBSET s`,
  REWRITE_TAC[OPEN_IN; GSYM OPEN_IN_SUBOPEN]);;

let CLOSED_EMPTY = prove
 (`closed {}`,
  REWRITE_TAC[CLOSED_IN; CLOSED_IN_EMPTY]);;

let CLOSED_UNIV = prove
 (`closed(UNIV:real^N->bool)`,
  REWRITE_TAC[CLOSED_IN; GSYM TOPSPACE_EUCLIDEAN; CLOSED_IN_TOPSPACE]);;

let CLOSED_UNION = prove
 (`!s t. closed s /\ closed t ==> closed(s UNION t)`,
  REWRITE_TAC[CLOSED_IN; CLOSED_IN_UNION]);;

let CLOSED_INTER = prove
 (`!s t. closed s /\ closed t ==> closed(s INTER t)`,
  REWRITE_TAC[CLOSED_IN; CLOSED_IN_INTER]);;

let CLOSED_INTERS = prove
 (`!f. (!s:real^N->bool. s IN f ==> closed s) ==> closed(INTERS f)`,
  REWRITE_TAC[CLOSED_IN] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THEN
  ASM_SIMP_TAC[CLOSED_IN_INTERS; INTERS_0] THEN
  REWRITE_TAC[GSYM TOPSPACE_EUCLIDEAN; CLOSED_IN_TOPSPACE]);;

let OPEN_CLOSED = prove
 (`!s:real^N->bool. open s <=> closed(UNIV DIFF s)`,
  SIMP_TAC[OPEN_IN; CLOSED_IN; TOPSPACE_EUCLIDEAN; SUBSET_UNIV;
           OPEN_IN_CLOSED_IN_EQ]);;

let CLOSED_OPEN = prove
 (`!s:real^N->bool. closed s <=> open(UNIV DIFF s)`,
  SIMP_TAC[OPEN_IN; CLOSED_IN; TOPSPACE_EUCLIDEAN; SUBSET_UNIV; closed_in]);;

let OPEN_DIFF = prove
 (`!s t. open s /\ closed t ==> open(s DIFF t)`,
  REWRITE_TAC[OPEN_IN; CLOSED_IN; OPEN_IN_DIFF]);;

let CLOSED_DIFF = prove
 (`!s t. closed s /\ open t ==> closed(s DIFF t)`,
  REWRITE_TAC[OPEN_IN; CLOSED_IN; CLOSED_IN_DIFF]);;

let OPEN_INTERS = prove
 (`!s. FINITE s /\ (!t. t IN s ==> open t) ==> open(INTERS s)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[INTERS_INSERT; INTERS_0; OPEN_UNIV; IN_INSERT] THEN
  MESON_TAC[OPEN_INTER]);;

let CLOSED_UNIONS = prove
 (`!s. FINITE s /\ (!t. t IN s ==> closed t) ==> closed(UNIONS s)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_INSERT; UNIONS_0; CLOSED_EMPTY; IN_INSERT] THEN
  MESON_TAC[CLOSED_UNION]);;

(* ------------------------------------------------------------------------- *)
(* Open and closed balls.                                                    *)
(* ------------------------------------------------------------------------- *)

let ball = new_definition
  `ball(x,e) = { y | dist(x,y) < e}`;;

let cball = new_definition
  `cball(x,e) = { y | dist(x,y) <= e}`;;

let IN_BALL = prove
 (`!x y e. y IN ball(x,e) <=> dist(x,y) < e`,
  REWRITE_TAC[ball; IN_ELIM_THM]);;

let IN_CBALL = prove
 (`!x y e. y IN cball(x,e) <=> dist(x,y) <= e`,
  REWRITE_TAC[cball; IN_ELIM_THM]);;

let IN_BALL_0 = prove
 (`!x e. x IN ball(vec 0,e) <=> norm(x) < e`,
  REWRITE_TAC[IN_BALL; dist; VECTOR_SUB_LZERO; NORM_NEG]);;

let IN_CBALL_0 = prove
 (`!x e. x IN cball(vec 0,e) <=> norm(x) <= e`,
  REWRITE_TAC[IN_CBALL; dist; VECTOR_SUB_LZERO; NORM_NEG]);;

let BALL_TRIVIAL = prove
 (`!x. ball(x,&0) = {}`,
  REWRITE_TAC[EXTENSION; IN_BALL; IN_SING; NOT_IN_EMPTY] THEN NORM_ARITH_TAC);;

let CBALL_TRIVIAL = prove
 (`!x. cball(x,&0) = {x}`,
  REWRITE_TAC[EXTENSION; IN_CBALL; IN_SING; NOT_IN_EMPTY] THEN NORM_ARITH_TAC);;

let CENTRE_IN_CBALL = prove
 (`!x e. x IN cball(x,e) <=> &0 <= e`,
  MESON_TAC[IN_CBALL; DIST_REFL]);;

let BALL_SUBSET_CBALL = prove
 (`!x e. ball(x,e) SUBSET cball(x,e)`,
  REWRITE_TAC[IN_BALL; IN_CBALL; SUBSET] THEN REAL_ARITH_TAC);;

let SUBSET_BALL = prove
 (`!x d e. d <= e ==> ball(x,d) SUBSET ball(x,e)`,
  REWRITE_TAC[SUBSET; IN_BALL] THEN MESON_TAC[REAL_LTE_TRANS]);;

let SUBSET_CBALL = prove
 (`!x d e. d <= e ==> cball(x,d) SUBSET cball(x,e)`,
  REWRITE_TAC[SUBSET; IN_CBALL] THEN MESON_TAC[REAL_LE_TRANS]);;

let BALL_MAX_UNION = prove
 (`!a r s. ball(a,max r s) = ball(a,r) UNION ball(a,s)`,
  REWRITE_TAC[IN_BALL; IN_UNION; EXTENSION] THEN REAL_ARITH_TAC);;

let BALL_MIN_INTER = prove
 (`!a r s. ball(a,min r s) = ball(a,r) INTER ball(a,s)`,
  REWRITE_TAC[IN_BALL; IN_INTER; EXTENSION] THEN REAL_ARITH_TAC);;

let BALL_TRANSLATION = prove
 (`!a x r. ball(a + x,r) = IMAGE (\y. a + y) (ball(x,r))`,
  REWRITE_TAC[ball] THEN GEOM_TRANSLATE_TAC[]);;

let CBALL_TRANSLATION = prove
 (`!a x r. cball(a + x,r) = IMAGE (\y. a + y) (cball(x,r))`,
  REWRITE_TAC[cball] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [BALL_TRANSLATION; CBALL_TRANSLATION];;

let BALL_LINEAR_IMAGE = prove
 (`!f:real^M->real^N x r.
        linear f /\ (!y. ?x. f x = y) /\ (!x. norm(f x) = norm x)
        ==> ball(f x,r) = IMAGE f (ball(x,r))`,
  REWRITE_TAC[ball] THEN GEOM_TRANSFORM_TAC[]);;

let CBALL_LINEAR_IMAGE = prove
 (`!f:real^M->real^N x r.
        linear f /\ (!y. ?x. f x = y) /\ (!x. norm(f x) = norm x)
        ==> cball(f x,r) = IMAGE f (cball(x,r))`,
  REWRITE_TAC[cball] THEN GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [BALL_LINEAR_IMAGE; CBALL_LINEAR_IMAGE];;

let BALL_SCALING = prove
 (`!c. &0 < c ==> !x r. ball(c % x,c * r) = IMAGE (\x. c % x) (ball(x,r))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SURJECTIVE_SCALING; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  REWRITE_TAC[IN_BALL; DIST_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_LT_LMUL_EQ]);;

let CBALL_SCALING = prove
 (`!c. &0 < c ==> !x r. cball(c % x,c * r) = IMAGE (\x. c % x) (cball(x,r))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SURJECTIVE_SCALING; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  REWRITE_TAC[IN_CBALL; DIST_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_LE_LMUL_EQ]);;

add_scaling_theorems [BALL_SCALING; CBALL_SCALING];;

(* ------------------------------------------------------------------------- *)
(* Topological properties of open balls.                                     *)
(* ------------------------------------------------------------------------- *)

let OPEN_BALL = prove
 (`!x e. open(ball(x,e))`,
  REWRITE_TAC[open_def; ball; IN_ELIM_THM] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  MESON_TAC[REAL_SUB_LT; REAL_LT_SUB_LADD; REAL_ADD_SYM; REAL_LET_TRANS;
            DIST_TRIANGLE_ALT]);;

let CENTRE_IN_BALL = prove
 (`!x e. x IN ball(x,e) <=> &0 < e`,
  MESON_TAC[IN_BALL; DIST_REFL]);;

let OPEN_CONTAINS_BALL = prove
 (`!s. open s <=> !x. x IN s ==> ?e. &0 < e /\ ball(x,e) SUBSET s`,
  REWRITE_TAC[open_def; SUBSET; IN_BALL] THEN REWRITE_TAC[DIST_SYM]);;

let OPEN_CONTAINS_BALL_EQ = prove
 (`!s. open s ==> (!x. x IN s <=> ?e. &0 < e /\ ball(x,e) SUBSET s)`,
  MESON_TAC[OPEN_CONTAINS_BALL; SUBSET; CENTRE_IN_BALL]);;

let BALL_EQ_EMPTY = prove
 (`!x e. (ball(x,e) = {}) <=> e <= &0`,
  REWRITE_TAC[EXTENSION; IN_BALL; NOT_IN_EMPTY; REAL_NOT_LT] THEN
  MESON_TAC[DIST_POS_LE; REAL_LE_TRANS; DIST_REFL]);;

let BALL_EMPTY = prove
 (`!x e. e <= &0 ==> ball(x,e) = {}`,
  REWRITE_TAC[BALL_EQ_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Basic "localization" results are handy for connectedness.                 *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_OPEN = prove
 (`!s:real^N->bool u.
        open_in (subtopology euclidean u) s <=> ?t. open t /\ (s = u INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; GSYM OPEN_IN] THEN
  REWRITE_TAC[INTER_ACI]);;

let OPEN_IN_OPEN_INTER = prove
 (`!u s. open s ==> open_in (subtopology euclidean u) (u INTER s)`,
  REWRITE_TAC[OPEN_IN_OPEN] THEN MESON_TAC[]);;

let OPEN_OPEN_IN_TRANS = prove
 (`!s t. open s /\ open t /\ t SUBSET s
         ==> open_in (subtopology euclidean s) t`,
  MESON_TAC[OPEN_IN_OPEN_INTER; SET_RULE `t SUBSET s ==> t = s INTER t`]);;

let OPEN_SUBSET = prove
 (`!s t:real^N->bool.
        s SUBSET t /\ open s ==> open_in (subtopology euclidean t) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM SET_TAC[]);;

let CLOSED_IN_CLOSED = prove
 (`!s:real^N->bool u.
    closed_in (subtopology euclidean u) s <=> ?t. closed t /\ (s = u INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY; GSYM CLOSED_IN] THEN
  REWRITE_TAC[INTER_ACI]);;

let CLOSED_IN_CLOSED_INTER = prove
 (`!u s. closed s ==> closed_in (subtopology euclidean u) (u INTER s)`,
  REWRITE_TAC[CLOSED_IN_CLOSED] THEN MESON_TAC[]);;

let CLOSED_CLOSED_IN_TRANS = prove
 (`!s t. closed s /\ closed t /\ t SUBSET s
         ==> closed_in (subtopology euclidean s) t`,
  MESON_TAC[CLOSED_IN_CLOSED_INTER; SET_RULE `t SUBSET s ==> t = s INTER t`]);;

let CLOSED_SUBSET = prove
 (`!s t:real^N->bool.
        s SUBSET t /\ closed s ==> closed_in (subtopology euclidean t) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSED_IN_CLOSED] THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM SET_TAC[]);;

let open_in = prove
 (`!u s:real^N->bool.
        open_in (subtopology euclidean u) s <=>
          s SUBSET u /\
          !x. x IN s ==> ?e. &0 < e /\
                             !x'. x' IN u /\ dist(x',x) < e ==> x' IN s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; GSYM OPEN_IN] THEN EQ_TAC THENL
   [REWRITE_TAC[open_def] THEN ASM SET_TAC[INTER_SUBSET; IN_INTER];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `d:real^N->real`) THEN
  EXISTS_TAC `UNIONS {b | ?x:real^N. (b = ball(x,d x)) /\ x IN s}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_UNIONS THEN
    ASM_SIMP_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; OPEN_BALL];
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    ASM_MESON_TAC[SUBSET; DIST_REFL; DIST_SYM; IN_BALL]]);;

(* ------------------------------------------------------------------------- *)
(* These "transitivity" results are handy too.                               *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_TRANS = prove
 (`!s t u. open_in (subtopology euclidean t) s /\
           open_in (subtopology euclidean u) t
           ==> open_in (subtopology euclidean u) s`,
  ASM_MESON_TAC[OPEN_IN_OPEN; OPEN_IN; OPEN_INTER; INTER_ASSOC]);;

let OPEN_IN_OPEN_TRANS = prove
 (`!s t. open_in (subtopology euclidean t) s /\ open t ==> open s`,
  REWRITE_TAC[ONCE_REWRITE_RULE[GSYM SUBTOPOLOGY_UNIV] OPEN_IN] THEN
  REWRITE_TAC[OPEN_IN_TRANS]);;

let CLOSED_IN_TRANS = prove
 (`!s t u. closed_in (subtopology euclidean t) s /\
           closed_in (subtopology euclidean u) t
           ==> closed_in (subtopology euclidean u) s`,
  ASM_MESON_TAC[CLOSED_IN_CLOSED; CLOSED_IN; CLOSED_INTER; INTER_ASSOC]);;

let CLOSED_IN_CLOSED_TRANS = prove
 (`!s t. closed_in (subtopology euclidean t) s /\ closed t ==> closed s`,
  REWRITE_TAC[ONCE_REWRITE_RULE[GSYM SUBTOPOLOGY_UNIV] CLOSED_IN] THEN
  REWRITE_TAC[CLOSED_IN_TRANS]);;

let OPEN_IN_SUBTOPOLOGY_INTER_SUBSET = prove
 (`!s u v. open_in (subtopology euclidean u) (u INTER s) /\ v SUBSET u
           ==> open_in (subtopology euclidean v) (v INTER s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN; LEFT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Also some invariance theorems for relative topology.                      *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_TRANSLATION_EQ = prove
 (`!a s t. open_in (subtopology euclidean (IMAGE (\x. a + x) t))
                   (IMAGE (\x. a + x) s) <=>
           open_in (subtopology euclidean t) s`,
  REWRITE_TAC[open_in] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [OPEN_IN_TRANSLATION_EQ];;

let CLOSED_IN_TRANSLATION_EQ = prove
 (`!a s t. closed_in (subtopology euclidean (IMAGE (\x. a + x) t))
                   (IMAGE (\x. a + x) s) <=>
           closed_in (subtopology euclidean t) s`,
  REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [CLOSED_IN_TRANSLATION_EQ];;

let OPEN_IN_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s t.
          linear f /\ (!x y. f x = f y ==> x = y)
          ==> (open_in (subtopology euclidean (IMAGE f t)) (IMAGE f s) <=>
               open_in (subtopology euclidean t) s)`,
  REWRITE_TAC[open_in; FORALL_IN_IMAGE; IMP_CONJ; SUBSET] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (SET_RULE
   `(!x y. f x = f y ==> x = y) ==> (!x s. f x IN IMAGE f s <=> x IN s)`)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_BOUNDED_POS) THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_BOUNDED_BELOW_POS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `B2:real` THEN STRIP_TAC THEN
  X_GEN_TAC `B1:real` THEN STRIP_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GSYM o MATCH_MP LINEAR_SUB) THEN
  ASM_REWRITE_TAC[dist; IMP_IMP] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `e / B1:real`; EXISTS_TAC `e * B2:real`] THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(REAL_ARITH
     `norm(f x) <= B1 * norm(x) /\ norm(x) * B1 < e ==> norm(f x) < e`) THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ];
    MATCH_MP_TAC(REAL_ARITH
     `norm x <= norm (f x :real^N) / B2 /\ norm(f x) / B2 < e
      ==> norm x < e`) THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ]]);;

add_linear_invariants [OPEN_IN_INJECTIVE_LINEAR_IMAGE];;

let CLOSED_IN_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s t.
          linear f /\ (!x y. f x = f y ==> x = y)
          ==> (closed_in (subtopology euclidean (IMAGE f t)) (IMAGE f s) <=>
               closed_in (subtopology euclidean t) s)`,
  REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [CLOSED_IN_INJECTIVE_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Connectedness.                                                            *)
(* ------------------------------------------------------------------------- *)

let connected = new_definition
  `connected s <=>
      ~(?e1 e2. open e1 /\ open e2 /\ s SUBSET (e1 UNION e2) /\
                (e1 INTER e2 INTER s = {}) /\
                ~(e1 INTER s = {}) /\ ~(e2 INTER s = {}))`;;

let CONNECTED_LOCAL = prove
 (`!s. connected s <=>
           ~(?e1 e2.
                 open_in (subtopology euclidean s) e1 /\
                 open_in (subtopology euclidean s) e2 /\
                 s SUBSET e1 UNION e2 /\
                 e1 INTER e2 = {} /\
                 ~(e1 = {}) /\
                 ~(e2 = {}))`,
  GEN_TAC THEN REWRITE_TAC[connected; OPEN_IN_OPEN] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV UNWIND_CONV) THEN
  AP_TERM_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  SET_TAC[]);;

let CONNECTED_CLOPEN = prove
 (`!s. connected s <=>
        !t. open_in (subtopology euclidean s) t /\
            closed_in (subtopology euclidean s) t ==> t = {} \/ t = s`,
  GEN_TAC THEN REWRITE_TAC[connected; OPEN_IN_OPEN; CLOSED_IN_CLOSED] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINDER_CONV) [GSYM EXISTS_DIFF] THEN
  ONCE_REWRITE_TAC[TAUT `(~a <=> b) <=> (a <=> ~b)`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; GSYM CONJ_ASSOC; DE_MORGAN_THM] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> b /\ a /\ c /\ d`] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN REWRITE_TAC[GSYM closed] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[TAUT `(a /\ b) /\ (c /\ d) /\ e <=> a /\ c /\ b /\ d /\ e`] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let CONNECTED_EMPTY = prove
 (`connected {}`,
  REWRITE_TAC[connected; INTER_EMPTY]);;

let CONNECTED_SING = prove
 (`!a. connected{a}`,
  REWRITE_TAC[connected] THEN SET_TAC[]);;

let CONNECTED_UNIONS = prove
 (`!P:(real^N->bool)->bool.
        (!s. s IN P ==> connected s) /\ ~(INTERS P = {})
        ==> connected(UNIONS P)`,
  GEN_TAC THEN REWRITE_TAC[connected; NOT_EXISTS_THM] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`e1:real^N->bool`; `e2:real^N->bool`] THEN
  STRIP_TAC THEN UNDISCH_TAC `~(INTERS P :real^N->bool = {})` THEN
  PURE_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTERS] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(a:real^N) IN e1 \/ a IN e2` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[];
    UNDISCH_TAC `~(e2 INTER UNIONS P:real^N->bool = {})`;
    UNDISCH_TAC `~(e1 INTER UNIONS P:real^N->bool = {})`] THEN
  PURE_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N`
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `!t:real^N->bool. t IN P ==> a IN t` THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`e1:real^N->bool`; `e2:real^N->bool`]) THEN
  ASM SET_TAC[]);;

let CONNECTED_UNION = prove
 (`!s t:real^N->bool.
        connected s /\ connected t /\ ~(s INTER t = {})
        ==> connected (s UNION t)`,
  REWRITE_TAC[GSYM UNIONS_2; GSYM INTERS_2] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_UNIONS THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Limit points.                                                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("limit_point_of",(12,"right"));;

let limit_point_of = new_definition
 `x limit_point_of s <=>
        !t. x IN t /\ open t ==> ?y. ~(y = x) /\ y IN s /\ y IN t`;;

let LIMPT_SUBSET = prove
 (`!x s t. x limit_point_of s /\ s SUBSET t ==> x limit_point_of t`,
  REWRITE_TAC[limit_point_of; SUBSET] THEN MESON_TAC[]);;

let LIMPT_APPROACHABLE = prove
 (`!x s. x limit_point_of s <=>
                !e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ dist(x',x) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[limit_point_of] THEN
  MESON_TAC[open_def; DIST_SYM; OPEN_BALL; CENTRE_IN_BALL; IN_BALL]);;

let LIMPT_APPROACHABLE_LE = prove
 (`!x s. x limit_point_of s <=>
                !e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ dist(x',x) <= e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIMPT_APPROACHABLE] THEN
  MATCH_MP_TAC(TAUT `(~a <=> ~b) ==> (a <=> b)`) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> c ==> ~(a /\ b)`; APPROACHABLE_LT_LE]);;

let LIMPT_UNIV = prove
 (`!x:real^N. x limit_point_of UNIV`,
  GEN_TAC THEN REWRITE_TAC[LIMPT_APPROACHABLE; IN_UNIV] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?c:real^N. norm(c) = e / &2` CHOOSE_TAC THENL
   [ASM_SIMP_TAC[VECTOR_CHOOSE_SIZE; REAL_HALF; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  EXISTS_TAC `x + c:real^N` THEN
  REWRITE_TAC[dist; VECTOR_EQ_ADDR] THEN ASM_REWRITE_TAC[VECTOR_ADD_SUB] THEN
  SUBGOAL_THEN `&0 < e / &2 /\ e / &2 < e`
   (fun th -> ASM_MESON_TAC[th; NORM_0; REAL_LT_REFL]) THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;

let CLOSED_LIMPT = prove
 (`!s. closed s <=> !x. x limit_point_of s ==> x IN s`,
  REWRITE_TAC[closed] THEN ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN
  REWRITE_TAC[limit_point_of; IN_DIFF; IN_UNIV; SUBSET] THEN MESON_TAC[]);;

let LIMPT_EMPTY = prove
 (`!x. ~(x limit_point_of {})`,
  REWRITE_TAC[LIMPT_APPROACHABLE; NOT_IN_EMPTY] THEN MESON_TAC[REAL_LT_01]);;


let CLOSED_POSITIVE_ORTHANT = prove
 (`closed {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                          ==> &0 <= x$i}`,
  REWRITE_TAC[CLOSED_LIMPT; LIMPT_APPROACHABLE] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `--(x:real^N $ i)`) THEN
  ASM_REWRITE_TAC[REAL_LT_RNEG; REAL_ADD_LID; NOT_EXISTS_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  MATCH_MP_TAC(TAUT `(a ==> ~c) ==> ~(a /\ b /\ c)`) THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `!b. abs x <= b /\ b <= a ==> ~(a + x < &0)`) THEN
  EXISTS_TAC `abs((y - x :real^N)$i)` THEN
  ASM_SIMP_TAC[dist; COMPONENT_LE_NORM] THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; REAL_ARITH
   `x < &0 /\ &0 <= y ==> abs(x) <= abs(y - x)`]);;

let FINITE_SET_AVOID = prove
 (`!a:real^N s. FINITE s
                ==> ?d. &0 < d /\ !x. x IN s /\ ~(x = a) ==> d <= dist(a,x)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY] THEN
  CONJ_TAC THENL [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `s:real^N->bool`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `x:real^N = a` THEN REWRITE_TAC[IN_INSERT] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `min d (dist(a:real^N,x))` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; GSYM DIST_NZ; REAL_MIN_LE] THEN
  ASM_MESON_TAC[REAL_LE_REFL]);;

let LIMIT_POINT_FINITE = prove
 (`!s a. FINITE s ==> ~(a limit_point_of s)`,
  REWRITE_TAC[LIMPT_APPROACHABLE; GSYM REAL_NOT_LE] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM; REAL_NOT_LE;
    REAL_NOT_LT; TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN
  MESON_TAC[FINITE_SET_AVOID; DIST_SYM]);;

let LIMPT_SING = prove
 (`!x y:real^N. ~(x limit_point_of {y})`,
  SIMP_TAC[LIMIT_POINT_FINITE; FINITE_SING]);;

let LIMIT_POINT_UNION = prove
 (`!s t x:real^N. x limit_point_of (s UNION t) <=>
                        x limit_point_of s \/ x limit_point_of t`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[LIMPT_SUBSET; SUBSET_UNION]] THEN
  REWRITE_TAC[LIMPT_APPROACHABLE; IN_UNION] THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~a ==> b) ==> a \/ b`) THEN
  REWRITE_TAC[NOT_FORALL_THM; LEFT_IMP_EXISTS_THM; NOT_IMP] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min d e`) THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  ASM_MESON_TAC[]);;

let DISCRETE_IMP_CLOSED = prove
 (`!s:real^N->bool e.
        &0 < e /\
        (!x y. x IN s /\ y IN s /\ norm(y - x) < e ==> y = x)
        ==> closed s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^N. ~(x limit_point_of s)`
    (fun th -> MESON_TAC[th; CLOSED_LIMPT]) THEN
  GEN_TAC THEN REWRITE_TAC[LIMPT_APPROACHABLE] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  REWRITE_TAC[REAL_HALF; ASSUME `&0 < e`] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min (e / &2) (dist(x:real^N,y))`) THEN
  ASM_SIMP_TAC[REAL_LT_MIN; DIST_POS_LT; REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `z:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_NORM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Interior of a set.                                                        *)
(* ------------------------------------------------------------------------- *)

let interior = new_definition
  `interior s = {x | ?t. open t /\ x IN t /\ t SUBSET s}`;;

let INTERIOR_EQ = prove
 (`!s. (interior s = s) <=> open s`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; interior; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [OPEN_SUBOPEN] THEN MESON_TAC[SUBSET]);;

let INTERIOR_OPEN = prove
 (`!s. open s ==> (interior s = s)`,
  MESON_TAC[INTERIOR_EQ]);;

let INTERIOR_EMPTY = prove
 (`interior {} = {}`,
  SIMP_TAC[INTERIOR_OPEN; OPEN_EMPTY]);;

let INTERIOR_UNIV = prove
 (`interior(:real^N) = (:real^N)`,
  SIMP_TAC[INTERIOR_OPEN; OPEN_UNIV]);;

let OPEN_INTERIOR = prove
 (`!s. open(interior s)`,
  GEN_TAC THEN REWRITE_TAC[interior] THEN GEN_REWRITE_TAC I [OPEN_SUBOPEN] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let INTERIOR_INTERIOR = prove
 (`!s. interior(interior s) = interior s`,
  MESON_TAC[INTERIOR_EQ; OPEN_INTERIOR]);;

let INTERIOR_SUBSET = prove
 (`!s. (interior s) SUBSET s`,
  REWRITE_TAC[SUBSET; interior; IN_ELIM_THM] THEN MESON_TAC[]);;

let SUBSET_INTERIOR = prove
 (`!s t. s SUBSET t ==> (interior s) SUBSET (interior t)`,
  REWRITE_TAC[interior; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let INTERIOR_MAXIMAL = prove
 (`!s t. t SUBSET s /\ open t ==> t SUBSET (interior s)`,
  REWRITE_TAC[interior; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let INTERIOR_MAXIMAL_EQ = prove
 (`!s t. open s ==> (s SUBSET interior t <=> s SUBSET t)`,
  MESON_TAC[SUBSET_TRANS; INTERIOR_SUBSET; INTERIOR_MAXIMAL]);;

let INTERIOR_UNIQUE = prove
 (`!s t. t SUBSET s /\ open t /\ (!t'. t' SUBSET s /\ open t' ==> t' SUBSET t)
         ==> (interior s = t)`,
  MESON_TAC[SUBSET_ANTISYM; INTERIOR_MAXIMAL; INTERIOR_SUBSET;
            OPEN_INTERIOR]);;

let IN_INTERIOR = prove
 (`!x s. x IN interior s <=> ?e. &0 < e /\ ball(x,e) SUBSET s`,
  REWRITE_TAC[interior; IN_ELIM_THM] THEN
  MESON_TAC[OPEN_CONTAINS_BALL; SUBSET_TRANS; CENTRE_IN_BALL; OPEN_BALL]);;

let OPEN_SUBSET_INTERIOR = prove
 (`!s t. open s ==> (s SUBSET interior t <=> s SUBSET t)`,
  MESON_TAC[INTERIOR_MAXIMAL; INTERIOR_SUBSET; SUBSET_TRANS]);;

let INTERIOR_INTER = prove
 (`!s t:real^N->bool. interior(s INTER t) = interior s INTER interior t`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN
    MATCH_MP_TAC SUBSET_INTERIOR THEN REWRITE_TAC[INTER_SUBSET];
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN SIMP_TAC[OPEN_INTER; OPEN_INTERIOR] THEN
    MATCH_MP_TAC(SET_RULE
      `s SUBSET s' /\ t SUBSET t' ==> s INTER t SUBSET s' INTER t'`) THEN
    REWRITE_TAC[INTERIOR_SUBSET]]);;

let INTERIOR_FINITE_INTERS = prove
 (`!s:(real^N->bool)->bool.
        FINITE s ==> interior(INTERS s) = INTERS(IMAGE interior s)`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[INTERS_0; INTERS_INSERT; INTERIOR_UNIV; IMAGE_CLAUSES] THEN
  SIMP_TAC[INTERIOR_INTER]);;

let INTERIOR_INTERS_SUBSET = prove
 (`!f. interior(INTERS f) SUBSET INTERS (IMAGE interior f)`,
  REWRITE_TAC[SUBSET; IN_INTERIOR; IN_INTERS; FORALL_IN_IMAGE] THEN
  MESON_TAC[]);;

let INTERIOR_LIMIT_POINT = prove
 (`!s x:real^N. x IN interior s ==> x limit_point_of s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_INTERIOR; IN_ELIM_THM; SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[LIMPT_APPROACHABLE] THEN X_GEN_TAC `d:real` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `min d e / &2`] VECTOR_CHOOSE_DIST) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC;
    CONV_TAC (RAND_CONV SYM_CONV) THEN REWRITE_TAC[GSYM DIST_EQ_0];
    ONCE_REWRITE_TAC[DIST_SYM]] THEN
  ASM_REAL_ARITH_TAC);;

let INTERIOR_CLOSED_UNION_EMPTY_INTERIOR = prove
 (`!s t:real^N->bool.
        closed(s) /\ interior(t) = {}
        ==> interior(s UNION t) = interior(s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[SUBSET_INTERIOR; SUBSET_UNION] THEN
  REWRITE_TAC[SUBSET; IN_INTERIOR; IN_INTER; IN_UNION] THEN
  X_GEN_TAC `x:real^N` THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) limit_point_of s`
   (fun th -> ASM_MESON_TAC[CLOSED_LIMPT; th]) THEN
  REWRITE_TAC[IN_INTERIOR; NOT_IN_EMPTY; LIMPT_APPROACHABLE] THEN
  X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?z:real^N. ~(z IN t) /\ ~(z = y) /\ dist(z,y) < d /\ dist(x,z) < e`
   (fun th -> ASM_MESON_TAC[th; IN_BALL]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_BALL]) THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
  REWRITE_TAC[IN_INTERIOR; NOT_IN_EMPTY; NOT_EXISTS_THM] THEN
  ABBREV_TAC `k = min d (e - dist(x:real^N,y))` THEN
  SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^N. dist(y,w) = k / &2` CHOOSE_TAC THENL
   [ASM_SIMP_TAC[VECTOR_CHOOSE_DIST; REAL_HALF; REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`w:real^N`; `k / &4`]) THEN
  ASM_SIMP_TAC[SUBSET; NOT_FORALL_THM; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH;
               NOT_IMP; IN_BALL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  ASM_NORM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Closure of a set.                                                         *)
(* ------------------------------------------------------------------------- *)

let closure = new_definition
  `closure s = s UNION {x | x limit_point_of s}`;;

let CLOSURE_INTERIOR = prove
 (`!s:real^N->bool. closure s = UNIV DIFF (interior (UNIV DIFF s))`,
  REWRITE_TAC[EXTENSION; closure; IN_UNION; IN_DIFF; IN_UNIV; interior;
              IN_ELIM_THM; limit_point_of; SUBSET] THEN
  MESON_TAC[]);;

let INTERIOR_CLOSURE = prove
 (`!s:real^N->bool. interior s = UNIV DIFF (closure (UNIV DIFF s))`,
  let lemma = prove(`!s t. UNIV DIFF (UNIV DIFF t) = t`,SET_TAC[]) in
  REWRITE_TAC[CLOSURE_INTERIOR; lemma]);;

let CLOSED_CLOSURE = prove
 (`!s. closed(closure s)`,
  let lemma = prove(`UNIV DIFF (UNIV DIFF s) = s`,SET_TAC[]) in
  REWRITE_TAC[closed; CLOSURE_INTERIOR; lemma; OPEN_INTERIOR]);;

let CLOSURE_HULL = prove
 (`!s. closure s = closed hull s`,
  GEN_TAC THEN MATCH_MP_TAC(GSYM HULL_UNIQUE) THEN
  REWRITE_TAC[CLOSED_CLOSURE; SUBSET] THEN
  REWRITE_TAC[closure; IN_UNION; IN_ELIM_THM; CLOSED_LIMPT] THEN
  MESON_TAC[limit_point_of]);;

let CLOSURE_EQ = prove
 (`!s. (closure s = s) <=> closed s`,
  SIMP_TAC[CLOSURE_HULL; HULL_EQ; CLOSED_INTERS]);;

let CLOSURE_CLOSED = prove
 (`!s. closed s ==> (closure s = s)`,
  MESON_TAC[CLOSURE_EQ]);;

let CLOSURE_CLOSURE = prove
 (`!s. closure(closure s) = closure s`,
  REWRITE_TAC[CLOSURE_HULL; HULL_HULL]);;

let CLOSURE_SUBSET = prove
 (`!s. s SUBSET (closure s)`,
  REWRITE_TAC[CLOSURE_HULL; HULL_SUBSET]);;

let SUBSET_CLOSURE = prove
 (`!s t. s SUBSET t ==> (closure s) SUBSET (closure t)`,
  REWRITE_TAC[CLOSURE_HULL; HULL_MONO]);;

let CLOSURE_INTER_SUBSET = prove
 (`!s t. closure(s INTER t) SUBSET closure(s) INTER closure(t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET_INTER] THEN
  CONJ_TAC THEN MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[]);;

let CLOSURE_INTERS_SUBSET = prove
 (`!f. closure(INTERS f) SUBSET INTERS(IMAGE closure f)`,
  REWRITE_TAC[SET_RULE `s SUBSET INTERS f <=> !t. t IN f ==> s SUBSET t`] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_CLOSURE THEN ASM SET_TAC[]);;

let CLOSURE_MINIMAL = prove
 (`!s t. s SUBSET t /\ closed t ==> (closure s) SUBSET t`,
  REWRITE_TAC[HULL_MINIMAL; CLOSURE_HULL]);;

let CLOSURE_MINIMAL_EQ = prove
 (`!s t:real^N->bool. closed t ==> (closure s SUBSET t <=> s SUBSET t)`,
  MESON_TAC[SUBSET_TRANS; CLOSURE_SUBSET; CLOSURE_MINIMAL]);;

let CLOSURE_UNIQUE = prove
 (`!s t. s SUBSET t /\ closed t /\
         (!t'. s SUBSET t' /\ closed t' ==> t SUBSET t')
         ==> (closure s = t)`,
  REWRITE_TAC[CLOSURE_HULL; HULL_UNIQUE]);;

let CLOSURE_EMPTY = prove
 (`closure {} = {}`,
  SIMP_TAC[CLOSURE_CLOSED; CLOSED_EMPTY]);;

let CLOSURE_UNIV = prove
 (`closure(:real^N) = (:real^N)`,
  SIMP_TAC[CLOSURE_CLOSED; CLOSED_UNIV]);;

let CLOSURE_EQ_EMPTY = prove
 (`!s. closure s = {} <=> s = {}`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[CLOSURE_EMPTY] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> t = {} ==> s = {}`) THEN
  REWRITE_TAC[CLOSURE_SUBSET]);;

let CLOSURE_SUBSET_EQ = prove
 (`!s:real^N->bool. closure s SUBSET s <=> closed s`,
  GEN_TAC THEN REWRITE_TAC[GSYM CLOSURE_EQ] THEN
  MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN SET_TAC[]);;

let OPEN_INTER_CLOSURE_EQ_EMPTY = prove
 (`!s t:real^N->bool.
        open s ==> (s INTER (closure t) = {} <=> s INTER t = {})`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MP_TAC(ISPEC `t:real^N->bool` CLOSURE_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[CLOSURE_INTERIOR] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s INTER (UNIV DIFF t) = {}`) THEN
  ASM_SIMP_TAC[OPEN_SUBSET_INTERIOR] THEN ASM SET_TAC[]);;

let OPEN_INTER_CLOSURE_SUBSET = prove
 (`!s t:real^N->bool.
        open s ==> (s INTER (closure t)) SUBSET closure(s INTER t)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[SUBSET; IN_INTER; closure; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN REWRITE_TAC[LIMPT_APPROACHABLE] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [open_def]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIMPT_APPROACHABLE]) THEN
  DISCH_THEN(MP_TAC o SPEC `min d e`) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; IN_INTER] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[]);;

let CLOSURE_COMPLEMENT = prove
 (`!s. closure(UNIV DIFF s) = UNIV DIFF interior(s)`,
  REWRITE_TAC[SET_RULE `s = UNIV DIFF t <=> UNIV DIFF s = t`] THEN
  REWRITE_TAC[GSYM INTERIOR_CLOSURE]);;

let INTERIOR_COMPLEMENT = prove
 (`!s. interior(UNIV DIFF s) = UNIV DIFF closure(s)`,
  REWRITE_TAC[SET_RULE `s = UNIV DIFF t <=> UNIV DIFF s = t`] THEN
  REWRITE_TAC[GSYM CLOSURE_INTERIOR]);;

let CONNECTED_CLOSURE = prove
 (`!s:real^N->bool. connected s ==> connected(closure s)`,
  GEN_TAC THEN REWRITE_TAC[connected; NOT_EXISTS_THM] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `v:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASSUME_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[GSYM DE_MORGAN_THM] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `(closure s) SUBSET ((:real^N) DIFF u)` MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[GSYM OPEN_CLOSED]; ALL_TAC];
    SUBGOAL_THEN `(closure s) SUBSET ((:real^N) DIFF v)` MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[GSYM OPEN_CLOSED]; ALL_TAC]] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Frontier (aka boundary).                                                  *)
(* ------------------------------------------------------------------------- *)

let frontier = new_definition
  `frontier s = (closure s) DIFF (interior s)`;;

let FRONTIER_CLOSED = prove
 (`!s. closed(frontier s)`,
  SIMP_TAC[frontier; CLOSED_DIFF; CLOSED_CLOSURE; OPEN_INTERIOR]);;

let FRONTIER_CLOSURES = prove
 (`!s:real^N->bool. frontier s = (closure s) INTER (closure(UNIV DIFF s))`,
  let lemma = prove(`s DIFF (UNIV DIFF t) = s INTER t`,SET_TAC[]) in
  REWRITE_TAC[frontier; INTERIOR_CLOSURE; lemma]);;

let FRONTIER_STRADDLE = prove
 (`!a:real^N s.
     a IN frontier s <=>
        !e. &0 < e ==> (?x. x IN s /\ dist(a,x) < e) /\
                       (?x. ~(x IN s) /\ dist(a,x) < e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRONTIER_CLOSURES; IN_INTER] THEN
  REWRITE_TAC[closure; IN_UNION; IN_ELIM_THM; limit_point_of;
              IN_UNIV; IN_DIFF] THEN
  ASM_MESON_TAC[IN_BALL; SUBSET; OPEN_CONTAINS_BALL;
                CENTRE_IN_BALL; OPEN_BALL; DIST_REFL]);;

let FRONTIER_SUBSET_CLOSED = prove
 (`!s. closed s ==> (frontier s) SUBSET s`,
  MESON_TAC[frontier; CLOSURE_CLOSED; SUBSET_DIFF]);;

let FRONTIER_EMPTY = prove
 (`frontier {} = {}`,
  REWRITE_TAC[frontier; CLOSURE_EMPTY; EMPTY_DIFF]);;

let FRONTIER_SUBSET_EQ = prove
 (`!s:real^N->bool. (frontier s) SUBSET s <=> closed s`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[FRONTIER_SUBSET_CLOSED] THEN
  REWRITE_TAC[frontier] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `s DIFF t SUBSET u ==> t SUBSET u ==> s SUBSET u`)) THEN
  REWRITE_TAC[INTERIOR_SUBSET; CLOSURE_SUBSET_EQ]);;

let FRONTIER_COMPLEMENT = prove
 (`!s. frontier(UNIV DIFF s) = frontier s`,
  REWRITE_TAC[frontier; CLOSURE_COMPLEMENT; INTERIOR_COMPLEMENT] THEN
  SET_TAC[]);;

let FRONTIER_DISJOINT_EQ = prove
 (`!s. (frontier s) INTER s = {} <=> open s`,
  ONCE_REWRITE_TAC[GSYM FRONTIER_COMPLEMENT; OPEN_CLOSED] THEN
  REWRITE_TAC[GSYM FRONTIER_SUBSET_EQ] THEN SET_TAC[]);;

let FRONTIER_INTER_SUBSET = prove
 (`!s t. frontier(s INTER t) SUBSET frontier(s) UNION frontier(t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[frontier; INTERIOR_INTER] THEN
  MATCH_MP_TAC(SET_RULE
   `cst SUBSET cs INTER ct
    ==> cst DIFF (s INTER t) SUBSET (cs DIFF s) UNION (ct DIFF t)`) THEN
  REWRITE_TAC[CLOSURE_INTER_SUBSET]);;

let FRONTIER_INTERIORS = prove
 (`!s. frontier s = (:real^N) DIFF interior(s) DIFF interior((:real^N) DIFF s)`,
  REWRITE_TAC[frontier; CLOSURE_INTERIOR] THEN SET_TAC[]);;

let CONNECTED_INTER_FRONTIER = prove
 (`!s t:real^N->bool.
        connected s /\ ~(s INTER t = {}) /\ ~(s DIFF t = {})
        ==> ~(s INTER frontier t = {})`,
  REWRITE_TAC[FRONTIER_INTERIORS] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_LOCAL]) THEN
  REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC
   [`s INTER interior t:real^N->bool`;
    `s INTER (interior((:real^N) DIFF t))`] THEN
  SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_INTERIOR] THEN
  MAP_EVERY (MP_TAC o C ISPEC INTERIOR_SUBSET)
   [`t:real^N->bool`; `(:real^N) DIFF t`] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A variant of nets (slightly non-standard but good for our purposes).      *)
(* ------------------------------------------------------------------------- *)

let net_tybij = new_type_definition "net" ("mk_net","netord")
 (prove
   (`?g:A->A->bool. !x y. (!z. g z x ==> g z y) \/ (!z. g z y ==> g z x)`,
    EXISTS_TAC `\x:A y:A. F` THEN REWRITE_TAC[]));;

let NET = prove
 (`!n x y. (!z. netord n z x ==> netord n z y) \/
           (!z. netord n z y ==> netord n z x)`,
   REWRITE_TAC[net_tybij; ETA_AX]);;

let OLDNET = prove
 (`!n x y. netord n x x /\ netord n y y
           ==> ?z. netord n z z /\
                   !w. netord n w z ==> netord n w x /\ netord n w y`,
  MESON_TAC[NET]);;

let NET_DILEMMA = prove
 (`!net. (?a. (?x. netord net x a) /\ (!x. netord net x a ==> P x)) /\
         (?b. (?x. netord net x b) /\ (!x. netord net x b ==> Q x))
         ==> ?c. (?x. netord net x c) /\ (!x. netord net x c ==> P x /\ Q x)`,
  MESON_TAC[NET]);;

(* ------------------------------------------------------------------------- *)
(* Common nets and the "within" modifier for nets.                           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("within",(14,"right"));;
parse_as_infix("in_direction",(14,"right"));;

let at = new_definition
  `at a = mk_net(\x y. &0 < dist(x,a) /\ dist(x,a) <= dist(y,a))`;;

let at_infinity = new_definition
  `at_infinity = mk_net(\x y. norm(x) >= norm(y))`;;

let sequentially = new_definition
  `sequentially = mk_net(\m:num n. m >= n)`;;

let within = new_definition
  `net within s = mk_net(\x y. netord net x y /\ x IN s)`;;

let in_direction = new_definition
  `a in_direction v = (at a) within {b | ?c. &0 <= c /\ (b - a = c % v)}`;;

(* ------------------------------------------------------------------------- *)
(* Prove that they are all nets.                                             *)
(* ------------------------------------------------------------------------- *)

let NET_PROVE_TAC[def] =
  REWRITE_TAC[GSYM FUN_EQ_THM; def] THEN
  REWRITE_TAC[ETA_AX] THEN
  ASM_SIMP_TAC[GSYM(CONJUNCT2 net_tybij)];;

let AT = prove
 (`!a:real^N x y.
        netord(at a) x y <=> &0 < dist(x,a) /\ dist(x,a) <= dist(y,a)`,
  GEN_TAC THEN NET_PROVE_TAC[at] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_REFL; REAL_LE_TRANS; REAL_LET_TRANS]);;

let AT_INFINITY = prove
 (`!a:real^N x y. netord at_infinity x y <=> norm(x) >= norm(y)`,
  GEN_TAC THEN NET_PROVE_TAC[at_infinity] THEN
  REWRITE_TAC[real_ge; REAL_LE_REFL] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_REFL; REAL_LE_TRANS]);;

let SEQUENTIALLY = prove
 (`!m n. netord sequentially m n <=> m >= n`,
  NET_PROVE_TAC[sequentially] THEN REWRITE_TAC[GE; LE_REFL] THEN
  MESON_TAC[LE_CASES; LE_REFL; LE_TRANS]);;

let WITHIN = prove
 (`!n s x y. netord(n within s) x y <=> netord n x y /\ x IN s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[within; GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 net_tybij); ETA_AX] THEN
  MESON_TAC[NET]);;

let IN_DIRECTION = prove
 (`!a v x y. netord(a in_direction v) x y <=>
                &0 < dist(x,a) /\ dist(x,a) <= dist(y,a) /\
                 ?c. &0 <= c /\ (x - a = c % v)`,
  REWRITE_TAC[WITHIN; AT; in_direction; IN_ELIM_THM; CONJ_ACI]);;

let WITHIN_UNIV = prove
 (`!x:real^N. at x within UNIV = at x`,
  REWRITE_TAC[within; at; IN_UNIV] THEN REWRITE_TAC[ETA_AX; net_tybij]);;

let WITHIN_WITHIN = prove
 (`!net s t. (net within s) within t = net within (s INTER t)`,
  ONCE_REWRITE_TAC[within] THEN
  REWRITE_TAC[WITHIN; IN_INTER; GSYM CONJ_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Identify trivial limits, where we can't approach arbitrarily closely.     *)
(* ------------------------------------------------------------------------- *)

let trivial_limit = new_definition
  `trivial_limit net <=>
     (!a:A b. a = b) \/
     ?a:A b. ~(a = b) /\ !x. ~(netord(net) x a) /\ ~(netord(net) x b)`;;

let TRIVIAL_LIMIT_WITHIN = prove
 (`!a:real^N. trivial_limit (at a within s) <=> ~(a limit_point_of s)`,
  REWRITE_TAC[trivial_limit; LIMPT_APPROACHABLE_LE; WITHIN; AT; DIST_NZ] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [MESON_TAC[REAL_LT_01; REAL_LT_REFL; VECTOR_CHOOSE_DIST;
                DIST_REFL; REAL_LT_IMP_LE];
      DISCH_THEN(X_CHOOSE_THEN `b:real^N` (X_CHOOSE_THEN `c:real^N`
        STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `&0 < dist(a,b:real^N) \/ &0 < dist(a,c:real^N)` MP_TAC THEN
      ASM_MESON_TAC[DIST_TRIANGLE; DIST_SYM; GSYM DIST_NZ; GSYM DIST_EQ_0;
                    REAL_ARITH `x <= &0 + &0 ==> ~(&0 < x)`]];
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN DISJ2_TAC THEN
    EXISTS_TAC `a:real^N` THEN
    SUBGOAL_THEN `?b:real^N. dist(a,b) = e` MP_TAC THENL
     [ASM_SIMP_TAC[VECTOR_CHOOSE_DIST; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^N` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_MESON_TAC[REAL_NOT_LE; DIST_REFL; DIST_NZ; DIST_SYM]]);;

let TRIVIAL_LIMIT_AT = prove
 (`!a. ~(trivial_limit (at a))`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[TRIVIAL_LIMIT_WITHIN; LIMPT_UNIV]);;

let TRIVIAL_LIMIT_AT_INFINITY = prove
 (`~(trivial_limit at_infinity)`,
  REWRITE_TAC[trivial_limit; AT_INFINITY; real_ge] THEN
  MESON_TAC[REAL_LE_REFL; VECTOR_CHOOSE_SIZE; REAL_LT_01; REAL_LT_LE]);;

let TRIVIAL_LIMIT_SEQUENTIALLY = prove
 (`~(trivial_limit sequentially)`,
  REWRITE_TAC[trivial_limit; SEQUENTIALLY] THEN
  MESON_TAC[GE_REFL; NOT_SUC]);;

let LIM_WITHIN_CLOSED_TRIVIAL = prove
 (`!a s. closed s /\ ~(a IN s) ==> trivial_limit (at a within s)`,
  REWRITE_TAC[TRIVIAL_LIMIT_WITHIN] THEN MESON_TAC[CLOSED_LIMPT]);;

(* ------------------------------------------------------------------------- *)
(* Some property holds "sufficiently close" to the limit point.              *)
(* ------------------------------------------------------------------------- *)

let eventually = new_definition
 `eventually p net <=>
        trivial_limit net \/
        ?y. (?x. netord net x y) /\ (!x. netord net x y ==> p x)`;;

let EVENTUALLY_HAPPENS = prove
 (`!net p. eventually p net ==> trivial_limit net \/ ?x. p x`,
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_WITHIN_LE = prove
 (`!s a:real^M p.
     eventually p (at a within s) <=>
        ?d. &0 < d /\ !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) <= d ==> p(x)`,
  REWRITE_TAC[eventually; AT; WITHIN; TRIVIAL_LIMIT_WITHIN] THEN
  REWRITE_TAC[LIMPT_APPROACHABLE_LE; DIST_NZ] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[REAL_LTE_TRANS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(TAUT `(a ==> b) ==> ~a \/ b`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `?b:real^M. dist(a,b) = d` MP_TAC THENL
   [ASM_SIMP_TAC[VECTOR_CHOOSE_DIST; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^M` THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_MESON_TAC[REAL_NOT_LE; DIST_REFL; DIST_NZ; DIST_SYM]);;

let EVENTUALLY_WITHIN = prove
 (`!s a:real^M p.
     eventually p (at a within s) <=>
        ?d. &0 < d /\ !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) < d ==> p(x)`,
  REWRITE_TAC[EVENTUALLY_WITHIN_LE] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> c ==> a /\ b ==> d`] THEN
  REWRITE_TAC[APPROACHABLE_LT_LE]);;

let EVENTUALLY_AT = prove
 (`!a p. eventually p (at a) <=>
         ?d. &0 < d /\ !x. &0 < dist(x,a) /\ dist(x,a) < d ==> p(x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[EVENTUALLY_WITHIN; IN_UNIV]);;

let EVENTUALLY_SEQUENTIALLY = prove
 (`!p. eventually p sequentially <=> ?N. !n. N <= n ==> p n`,
  REWRITE_TAC[eventually; SEQUENTIALLY; GE; LE_REFL;
    TRIVIAL_LIMIT_SEQUENTIALLY] THEN  MESON_TAC[LE_REFL]);;

let EVENTUALLY_AT_INFINITY = prove
 (`!f l. eventually p at_infinity <=> ?b. !x. norm(x) >= b ==> p x`,
  REWRITE_TAC[eventually; AT_INFINITY; TRIVIAL_LIMIT_AT_INFINITY] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MESON_TAC[real_ge; REAL_LE_REFL; VECTOR_CHOOSE_SIZE;
    REAL_ARITH `&0 <= b \/ (!x. x >= &0 ==> x >= b)`]);;

let ALWAYS_EVENTUALLY = prove
 (`(!x. p x) ==> eventually p net`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[eventually; trivial_limit] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Combining theorems for "eventually".                                      *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_AND = prove
 (`!net:(A net) p q.
        eventually (\x. p x /\ q x) net <=>
        eventually p net /\ eventually q net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eventually] THEN
  ASM_CASES_TAC `trivial_limit(net:(A net))` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN SIMP_TAC[NET_DILEMMA] THEN MESON_TAC[]);;

let EVENTUALLY_MONO = prove
 (`!net:(A net) p q.
        (!x. p x ==> q x) /\ eventually p net
        ==> eventually q net`,
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_MP = prove
 (`!net:(A net) p q.
        eventually (\x. p x ==> q x) net /\ eventually p net
        ==> eventually q net`,
  REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_FALSE = prove
 (`!net. eventually (\x. F) net <=> trivial_limit net`,
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_TRUE = prove
 (`!net. eventually (\x. T) net <=> T`,
  REWRITE_TAC[eventually; trivial_limit] THEN MESON_TAC[]);;

let NOT_EVENTUALLY = prove
 (`!net p. (!x. ~(p x)) /\ ~(trivial_limit net) ==> ~(eventually p net)`,
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_FORALL = prove
 (`!net:(A net) p s:B->bool.
        FINITE s /\ ~(s = {})
        ==> (eventually (\x. !a. a IN s ==> p a x) net <=>
             !a. a IN s ==> eventually (p a) net)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[FORALL_IN_INSERT; EVENTUALLY_AND; ETA_AX] THEN
  MAP_EVERY X_GEN_TAC [`b:B`; `t:B->bool`] THEN
  ASM_CASES_TAC `t:B->bool = {}` THEN
  ASM_SIMP_TAC[NOT_IN_EMPTY; EVENTUALLY_TRUE]);;

let FORALL_EVENTUALLY = prove
 (`!net:(A net) p s:B->bool.
        FINITE s /\ ~(s = {})
        ==> ((!a. a IN s ==> eventually (p a) net) <=>
             eventually (\x. !a. a IN s ==> p a x) net)`,
  SIMP_TAC[EVENTUALLY_FORALL]);;

(* ------------------------------------------------------------------------- *)
(* Limits, defined as vacuously true when the limit is trivial.              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("-->",(12,"right"));;

let tendsto = new_definition
  `(f --> l) net <=> !e. &0 < e ==> eventually (\x. dist(f(x),l) < e) net`;;

let lim = new_definition
 `lim net f = @l. (f --> l) net`;;

let LIM = prove
 (`(f --> l) net <=>
        trivial_limit net \/
        !e. &0 < e ==> ?y. (?x. netord(net) x y) /\
                           !x. netord(net) x y ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; eventually] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Show that they yield usual definitions in the various cases.              *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHIN_LE = prove
 (`!f:real^M->real^N l a s.
        (f --> l)(at a within s) <=>
           !e. &0 < e ==> ?d. &0 < d /\
                              !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) <= d
                                   ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_WITHIN_LE]);;

let LIM_WITHIN = prove
 (`!f:real^M->real^N l a s.
      (f --> l) (at a within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) < d
                    ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_WITHIN] THEN MESON_TAC[]);;

let LIM_AT = prove
 (`!f l:real^N a:real^M.
      (f --> l) (at a) <=>
              !e. &0 < e
                  ==> ?d. &0 < d /\ !x. &0 < dist(x,a) /\ dist(x,a) < d
                          ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_AT] THEN MESON_TAC[]);;

let LIM_AT_INFINITY = prove
 (`!f l. (f --> l) at_infinity <=>
               !e. &0 < e ==> ?b. !x. norm(x) >= b ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_AT_INFINITY] THEN MESON_TAC[]);;

let LIM_SEQUENTIALLY = prove
 (`!s l. (s --> l) sequentially <=>
          !e. &0 < e ==> ?N. !n. N <= n ==> dist(s(n),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_SEQUENTIALLY] THEN MESON_TAC[]);;

let LIM_EVENTUALLY = prove
 (`!net f l. eventually (\x. f x = l) net ==> (f --> l) net`,
  REWRITE_TAC[eventually; LIM] THEN MESON_TAC[DIST_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The expected monotonicity property.                                       *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHIN_EMPTY = prove
 (`!f l x. (f --> l) (at x within {})`,
  REWRITE_TAC[LIM_WITHIN; NOT_IN_EMPTY] THEN MESON_TAC[REAL_LT_01]);;

let LIM_WITHIN_SUBSET = prove
 (`!f l a s.
    (f --> l) (at a within s) /\ t SUBSET s ==> (f --> l) (at a within t)`,
  REWRITE_TAC[LIM_WITHIN; SUBSET] THEN MESON_TAC[]);;

let LIM_UNION = prove
 (`!f x l s t.
        (f --> l) (at x within s) /\ (f --> l) (at x within t)
        ==> (f --> l) (at x within (s UNION t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_WITHIN; IN_UNION] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `e:real` THEN ASM_CASES_TAC `&0 < e` THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `d1:real`) (X_CHOOSE_TAC `d2:real`)) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_MESON_TAC[REAL_LT_MIN]);;

let LIM_UNION_UNIV = prove
 (`!f x l s t.
        (f --> l) (at x within s) /\ (f --> l) (at x within t) /\
        s UNION t = (:real^N)
        ==> (f --> l) (at x)`,
  MESON_TAC[LIM_UNION; WITHIN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Interrelations between restricted and unrestricted limits.                *)
(* ------------------------------------------------------------------------- *)

let LIM_AT_WITHIN = prove
 (`!f l a s. (f --> l)(at a) ==> (f --> l)(at a within s)`,
  REWRITE_TAC[LIM_AT; LIM_WITHIN] THEN MESON_TAC[]);;

let LIM_WITHIN_OPEN = prove
 (`!f l a:real^M s.
     a IN s /\ open s ==> ((f --> l)(at a within s) <=> (f --> l)(at a))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[LIM_AT_WITHIN] THEN
  REWRITE_TAC[LIM_AT; LIM_WITHIN] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real^M` o GEN_REWRITE_RULE I [open_def]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[REAL_LT_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Another limit point characterization.                                     *)
(* ------------------------------------------------------------------------- *)

let LIMPT_SEQUENTIAL = prove
 (`!x:real^N s.
      x limit_point_of s <=>
             ?f. (!n. f(n) IN (s DELETE x)) /\ (f --> x) sequentially`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIMPT_APPROACHABLE; LIM_SEQUENTIALLY; IN_DELETE] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[GE; LE_REFL]] THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `inv(&n + &1)`) THEN
  SIMP_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 <= x ==> &0 < x + &1`; REAL_POS] THEN
  REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `f:num->real^N` THEN REWRITE_TAC[FORALL_AND_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FORALL_POS_MONO_1 THEN
  CONJ_TAC THENL [MESON_TAC[REAL_LT_TRANS]; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN EXISTS_TAC `n:num` THEN REWRITE_TAC[GSYM GE] THEN
  MATCH_MP_TAC SEQ_MONO_LEMMA THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[REAL_LE_INV2; GE; REAL_OF_NUM_LE; REAL_LE_RADD; GE_REFL;
           REAL_POS; REAL_ARITH `&0 <= x ==> &0 < x + &1`]);;

(* ------------------------------------------------------------------------- *)
(* Basic arithmetical combining theorems for limits.                         *)
(* ------------------------------------------------------------------------- *)

let LIM_LINEAR = prove
 (`!net:(A)net h f l.
        (f --> l) net /\ linear h ==> ((\x. h(f x)) --> h l) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN
  ASM_CASES_TAC `trivial_limit (net:(A)net)` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o
    MATCH_MP LINEAR_BOUNDED_POS) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / B`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; dist; GSYM LINEAR_SUB; REAL_LT_RDIV_EQ] THEN
  ASM_MESON_TAC[REAL_LET_TRANS; REAL_MUL_SYM]);;

let LIM_CONST = prove
 (`!net a:real^N. ((\x. a) --> a) net`,
  SIMP_TAC[LIM; DIST_REFL; trivial_limit] THEN MESON_TAC[]);;

let LIM_CMUL = prove
 (`!f l c. (f --> l) net ==> ((\x. c % f x) --> c % l) net`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_LINEAR THEN
  ASM_REWRITE_TAC[REWRITE_RULE[ETA_AX]
    (MATCH_MP LINEAR_COMPOSE_CMUL LINEAR_ID)]);;

let LIM_NEG = prove
 (`!net f l:real^N. (f --> l) net ==> ((\x. --(f x)) --> --l) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM; dist] THEN
  REWRITE_TAC[VECTOR_ARITH `--x - --y = --(x - y:real^N)`; NORM_NEG]);;

let LIM_NEG_EQ = prove
 (`!net f l:real^N. ((\x. --(f x)) --> --l) net <=> (f --> l) net`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_NEG) THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX]);;

let LIM_ADD = prove
 (`!net:(A)net f g l m.
    (f --> l) net /\ (g --> m) net ==> ((\x. f(x) + g(x)) --> l + m) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN
  ASM_CASES_TAC `trivial_limit (net:(A)net)` THEN
  ASM_REWRITE_TAC[AND_FORALL_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP NET_DILEMMA) THEN MATCH_MP_TAC MONO_EXISTS THEN
  MESON_TAC[REAL_HALF; DIST_TRIANGLE_ADD; REAL_LT_ADD2; REAL_LET_TRANS]);;

let LIM_ABS = prove
 (`!net:(A)net f:A->real^N l.
     (f --> l) net
     ==> ((\x. lambda i. (abs(f(x)$i))) --> (lambda i. abs(l$i)):real^N) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN
  ASM_CASES_TAC `trivial_limit (net:(A)net)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x - y) <= norm(a - b) ==> dist(a,b) < e ==> dist(x,y) < e`) THEN
  MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
  SIMP_TAC[LAMBDA_BETA; VECTOR_SUB_COMPONENT] THEN
  REAL_ARITH_TAC);;

let LIM_SUB = prove
 (`!net:(A)net f g l m.
    (f --> l) net /\ (g --> m) net ==> ((\x. f(x) - g(x)) --> l - m) net`,
  REWRITE_TAC[real_sub; VECTOR_SUB] THEN ASM_SIMP_TAC[LIM_ADD; LIM_NEG]);;

let LIM_MAX = prove
 (`!net:(A)net f g l:real^N m:real^N.
    (f --> l) net /\ (g --> m) net
    ==> ((\x. lambda i. max (f(x)$i) (g(x)$i))
         --> (lambda i. max (l$i) (m$i)):real^N) net`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LIM_ADD) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LIM_SUB) THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_ABS) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_ADD) THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&2)` o MATCH_MP LIM_CMUL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
  SIMP_TAC[FUN_EQ_THM; CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           VECTOR_SUB_COMPONENT; LAMBDA_BETA] THEN
  REAL_ARITH_TAC);;

let LIM_MIN = prove
 (`!net:(A)net f g l:real^N m:real^N.
    (f --> l) net /\ (g --> m) net
    ==> ((\x. lambda i. min (f(x)$i) (g(x)$i))
         --> (lambda i. min (l$i) (m$i)):real^N) net`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN(MP_TAC o MATCH_MP LIM_NEG)) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_NEG o MATCH_MP LIM_MAX) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
  SIMP_TAC[FUN_EQ_THM; CART_EQ; LAMBDA_BETA; VECTOR_NEG_COMPONENT] THEN
  REAL_ARITH_TAC);;

let LIM_NULL = prove
 (`!net f l. (f --> l) net <=> ((\x. f(x) - l) --> vec 0) net`,
  REWRITE_TAC[LIM; dist; VECTOR_SUB_RZERO]);;

let LIM_NULL_NORM = prove
 (`!net f. (f --> vec 0) net <=> ((\x. lift(norm(f x))) --> vec 0) net`,
  REWRITE_TAC[LIM; dist; VECTOR_SUB_RZERO; REAL_ABS_NORM; NORM_LIFT]);;

let LIM_NULL_COMPARISON = prove
 (`!net f g. eventually (\x. norm(f x) <= g x) net /\
             ((\x. lift(g x)) --> vec 0) net
             ==> (f --> vec 0) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tendsto; RIGHT_AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  REWRITE_TAC[dist; VECTOR_SUB_RZERO; NORM_LIFT] THEN REAL_ARITH_TAC);;

let LIM_COMPONENT = prove
 (`!net f i l:real^N. (f --> l) net /\ 1 <= i /\ i <= dimindex(:N)
                      ==> ((\a. lift(f(a)$i)) --> lift(l$i)) net`,
  REWRITE_TAC[LIM; dist; GSYM LIFT_SUB; NORM_LIFT] THEN
  SIMP_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
  MESON_TAC[COMPONENT_LE_NORM; REAL_LET_TRANS]);;

let LIM_TRANSFORM_BOUND = prove
 (`!f g. eventually (\n. norm(f n) <= norm(g n)) net /\ (g --> vec 0) net
         ==> (f --> vec 0) net`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[tendsto; RIGHT_AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  REWRITE_TAC[dist; VECTOR_SUB_RZERO] THEN REAL_ARITH_TAC);;

let LIM_NULL_CMUL_BOUNDED = prove
 (`!f g:A->real^N B.
        eventually (\a. abs(f a) <= B) net /\
        (g --> vec 0) net
        ==> ((\n. f n % g n) --> vec 0) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tendsto] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / (abs B + &1)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < abs x + &1`] THEN
  UNDISCH_TAC `eventually (\a. abs(f a) <= B) (net:(A net))` THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MP) THEN
  REWRITE_TAC[dist; VECTOR_SUB_RZERO; o_THM; NORM_LIFT; NORM_MUL] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `x:A` THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `B * e / (abs B + &1)` THEN
  ASM_SIMP_TAC[REAL_LE_MUL2; REAL_ABS_POS; NORM_POS_LE; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_ARITH `c * (a / b) = (c * a) / b`] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < abs x + &1`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `e * B <= e * abs B /\ &0 < e ==> B * e < e * (abs B + &1)`) THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC);;

let LIM_NULL_VMUL_BOUNDED = prove
 (`!f g:A->real^N B.
        ((lift o f) --> vec 0) net /\
        eventually (\a. norm(g a) <= B) net
        ==> ((\n. f n % g n) --> vec 0) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tendsto] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / (abs B + &1)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < abs x + &1`] THEN
  UNDISCH_TAC `eventually (\a. norm ((g:A->real^N) a) <= B) net` THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MP) THEN
  REWRITE_TAC[dist; VECTOR_SUB_RZERO; o_THM; NORM_LIFT; NORM_MUL] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `x:A` THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `e / (abs B + &1) * B` THEN
  ASM_SIMP_TAC[REAL_LE_MUL2; REAL_ABS_POS; NORM_POS_LE; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_ARITH `(a / b) * c = (a * c) / b`] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < abs x + &1`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `e * B <= e * abs B /\ &0 < e ==> e * B < e * (abs B + &1)`) THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC);;

let LIM_VSUM = prove
 (`!f:A->B->real^N s.
        FINITE s /\ (!i. i IN s ==> ((f i) --> (l i)) net)
        ==> ((\x. vsum s (\i. f i x)) --> vsum s l) net`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; LIM_CONST; LIM_ADD; IN_INSERT; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Deducing things about the limit from the elements.                        *)
(* ------------------------------------------------------------------------- *)

let LIM_IN_CLOSED_SET = prove
 (`!net f:A->real^N s l.
        closed s /\ eventually (\x. f(x) IN s) net /\
        ~(trivial_limit net) /\ (f --> l) net
        ==> l IN s`,
  REWRITE_TAC[closed] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `~(x IN (UNIV DIFF s)) ==> x IN s`) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `l:real^N` o GEN_REWRITE_RULE I
          [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNION] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o GEN_REWRITE_RULE I [tendsto]) THEN
  UNDISCH_TAC `eventually (\x. (f:A->real^N) x IN s) net` THEN
  ASM_REWRITE_TAC[GSYM EVENTUALLY_AND; TAUT `a ==> ~b <=> ~(a /\ b)`] THEN
  MATCH_MP_TAC NOT_EVENTUALLY THEN ASM_MESON_TAC[DIST_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Need to prove closed(cball(x,e)) before deducing this as a corollary.     *)
(* ------------------------------------------------------------------------- *)

let LIM_NORM_UBOUND = prove
 (`!net:(A)net f (l:real^N) b.
      ~(trivial_limit net) /\
      (f --> l) net /\
      eventually (\x. norm(f x) <= b) net
      ==> norm(l) <= b`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[LIM] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[eventually] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?x:A. dist(f(x):real^N,l) < norm(l:real^N) - b /\ norm(f x) <= b`
  (CHOOSE_THEN MP_TAC) THENL [ASM_MESON_TAC[NET]; ALL_TAC] THEN
  REWRITE_TAC[REAL_NOT_LT; REAL_LE_SUB_RADD; DE_MORGAN_THM; dist] THEN
  NORM_ARITH_TAC);;

let LIM_NORM_LBOUND = prove
 (`!net:(A)net f (l:real^N) b.
      ~(trivial_limit net) /\ (f --> l) net /\
      eventually (\x. b <= norm(f x)) net
      ==> b <= norm(l)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[LIM] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[eventually] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?x:A. dist(f(x):real^N,l) < b - norm(l:real^N) /\ b <= norm(f x)`
  (CHOOSE_THEN MP_TAC) THENL [ASM_MESON_TAC[NET]; ALL_TAC] THEN
  REWRITE_TAC[REAL_NOT_LT; REAL_LE_SUB_RADD; DE_MORGAN_THM; dist] THEN
  NORM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness of the limit, when nontrivial.                                 *)
(* ------------------------------------------------------------------------- *)

let LIM_UNIQUE = prove
 (`!net:(A)net f l:real^N l'.
      ~(trivial_limit net) /\ (f --> l) net /\ (f --> l') net ==> (l = l')`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[VECTOR_SUB_REFL] o MATCH_MP LIM_SUB) THEN
  SUBGOAL_THEN `!e. &0 < e ==> norm(l:real^N - l') <= e` MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC LIM_NORM_UBOUND THEN
    MAP_EVERY EXISTS_TAC [`net:(A)net`; `\x:A. vec 0 : real^N`] THEN
    ASM_SIMP_TAC[NORM_0; REAL_LT_IMP_LE; eventually] THEN
    ASM_MESON_TAC[trivial_limit];
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[DIST_NZ; dist] THEN
    DISCH_TAC THEN DISCH_THEN(MP_TAC o SPEC `norm(l - l':real^N) / &2`) THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    UNDISCH_TAC `&0 < norm(l - l':real^N)` THEN REAL_ARITH_TAC]);;

let TENDSTO_LIM = prove
 (`!net f l. ~(trivial_limit net) /\ (f --> l) net ==> lim net f = l`,
  REWRITE_TAC[lim] THEN MESON_TAC[LIM_UNIQUE]);;

let LIM_CONST_EQ = prove
 (`!net:(A net) c d:real^N.
        ((\x. c) --> d) net <=> trivial_limit net \/ c = d`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `trivial_limit (net:A net)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[LIM]; ALL_TAC] THEN
  EQ_TAC THEN SIMP_TAC[LIM_CONST] THEN DISCH_TAC THEN
  MATCH_MP_TAC(SPEC `net:A net` LIM_UNIQUE) THEN
  EXISTS_TAC `(\x. c):A->real^N` THEN ASM_REWRITE_TAC[LIM_CONST]);;

(* ------------------------------------------------------------------------- *)
(* Limit under bilinear function (surprisingly tedious, but important).      *)
(* ------------------------------------------------------------------------- *)

let NORM_BOUND_LEMMA = prove
 (`!x:real^M y:real^N e.
        &0 < e
        ==> ?d. &0 < d /\
                !x' y'. norm(x' - x) < d /\ norm(y' - y) < d
                        ==> norm(x') * norm(y' - y) + norm(x' - x) * norm(y)
                                < e`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `min (&1) (e / &2 / (norm(x:real^M) + norm(y:real^N) + &1))` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; REAL_OF_NUM_LT; NORM_POS_LE; ARITH;
    REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 < x + y + &1`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
   `(norm(x:real^M) + &1) * norm(y' - y) + norm(x' - x) * norm(y:real^N)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_RADD; GSYM REAL_ADD_RDISTRIB] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_MESON_TAC[NORM_TRIANGLE_SUB; REAL_ARITH
     `x' <= x + d /\ d < &1 ==> x' <= x + &1`];
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(norm(x:real^M) + norm(y:real^N) + &1) *
                (norm(x' - x) + norm(y' - y))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `y * xd <= p * xd /\ x * yd <= p * yd
      ==> x * yd + xd * y <= p * (xd + yd)`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THENL
     [MP_TAC(ISPEC `x:real^M` NORM_POS_LE);
      MP_TAC(ISPEC `y:real^N` NORM_POS_LE)] THEN
    REAL_ARITH_TAC]);;

let LIM_BILINEAR = prove
 (`!net:(A)net (h:real^M->real^N->real^P) f g l m.
        (f --> l) net /\ (g --> m) net /\ bilinear h
        ==> ((\x. h (f x) (g x)) --> (h l m)) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN
  ASM_CASES_TAC `trivial_limit (net:(A)net)` THEN
  ASM_REWRITE_TAC[AND_FORALL_THM; CONJ_ASSOC] THEN
  STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o  MATCH_MP
   BILINEAR_BOUNDED_POS) THEN
  MP_TAC(ISPECL [`l:real^M`; `m:real^N`; `e / B`] NORM_BOUND_LEMMA) THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP NET_DILEMMA) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:A` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `a:A` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[dist] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH
    `h a b - h c d :real^N = (h a b - h a d) + (h a d - h c d)`] THEN
  MATCH_MP_TAC NORM_TRIANGLE_LT THEN
  ASM_SIMP_TAC[GSYM BILINEAR_LSUB; GSYM BILINEAR_RSUB] THEN
  FIRST_X_ASSUM(fun th ->
   MP_TAC(SPECL [`(f:A->real^M) a`; `(g:A->real^N) a - m`] th) THEN
   MP_TAC(SPECL [`(f:A->real^M) a - l`; `m:real^N`] th)) THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* These are special for limits out of the same vector space.                *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHIN_ID = prove
 (`!a s. ((\x. x) --> a) (at a within s)`,
  REWRITE_TAC[LIM_WITHIN] THEN MESON_TAC[]);;

let LIM_AT_ID = prove
 (`!a. ((\x. x) --> a) (at a)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN REWRITE_TAC[LIM_WITHIN_ID]);;

let LIM_AT_ZERO = prove
 (`!f:real^M->real^N l a.
        (f --> l) (at a) <=> ((\x. f(a + x)) --> l) (at(vec 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_AT] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `&0 < d` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:real^M` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a + x:real^M`) THEN
    REWRITE_TAC[dist; VECTOR_ADD_SUB; VECTOR_SUB_RZERO];
    FIRST_X_ASSUM(MP_TAC o SPEC `x - a:real^M`) THEN
    REWRITE_TAC[dist; VECTOR_SUB_RZERO; VECTOR_SUB_ADD2]]);;

(* ------------------------------------------------------------------------- *)
(* It's also sometimes useful to extract the limit point from the net.       *)
(* ------------------------------------------------------------------------- *)

let netlimit = new_definition
  `netlimit net = @a. !x. ~(netord net x a)`;;

let NETLIMIT_WITHIN = prove
 (`!a:real^N s. ~(trivial_limit (at a within s))
                ==> (netlimit (at a within s) = a)`,
  REWRITE_TAC[trivial_limit; netlimit; AT; WITHIN; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x:real^N. ~(&0 < dist(x,a) /\ dist(x,a) <= dist(a,a) /\ x IN s)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[DIST_REFL; REAL_NOT_LT]; ASM_MESON_TAC[]]);;

let NETLIMIT_AT = prove
 (`!a. netlimit(at a) = a`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  MATCH_MP_TAC NETLIMIT_WITHIN THEN
  SIMP_TAC[TRIVIAL_LIMIT_AT; WITHIN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Transformation of limit.                                                  *)
(* ------------------------------------------------------------------------- *)

let LIM_TRANSFORM = prove
 (`!net f g l.
     ((\x. f x - g x) --> vec 0) net /\ (f --> l) net ==> (g --> l) net`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LIM_SUB) THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_NEG) THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN BINOP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  VECTOR_ARITH_TAC);;

let LIM_TRANSFORM_EVENTUALLY = prove
 (`!net f g l.
        eventually (\x. f x = g x) net /\ (f --> l) net ==> (g --> l) net`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP LIM_EVENTUALLY) MP_TAC) THEN
  MESON_TAC[LIM_TRANSFORM]);;

let LIM_TRANSFORM_WITHIN = prove
 (`!f g x s d.
        &0 < d /\
        (!x'. x' IN s /\ &0 < dist(x',x) /\ dist(x',x) < d ==> f(x') = g(x')) /\
        (f --> l) (at x within s)
        ==> (g --> l) (at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM) THEN
  REWRITE_TAC[LIM_WITHIN] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `d:real` THEN
  ASM_SIMP_TAC[VECTOR_SUB_REFL; DIST_REFL]);;

let LIM_TRANSFORM_AT = prove
 (`!f g x d.
        &0 < d /\
        (!x'. &0 < dist(x',x) /\ dist(x',x) < d ==> f(x') = g(x')) /\
        (f --> l) (at x)
        ==> (g --> l) (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN MESON_TAC[LIM_TRANSFORM_WITHIN]);;

(* ------------------------------------------------------------------------- *)
(* Common case assuming being away from some crucial point like 0.           *)
(* ------------------------------------------------------------------------- *)

let LIM_TRANSFORM_AWAY_WITHIN = prove
 (`!f:real^M->real^N g a b s.
        ~(a = b) /\
        (!x. x IN s /\ ~(x = a) /\ ~(x = b) ==> f(x) = g(x)) /\
        (f --> l) (at a within s)
        ==> (g --> l) (at a within s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `dist(a:real^M,b)`] THEN
  ASM_REWRITE_TAC[GSYM DIST_NZ] THEN X_GEN_TAC `y:real^M` THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[DIST_SYM; REAL_LT_REFL]);;

let LIM_TRANSFORM_AWAY_AT = prove
 (`!f:real^M->real^N g a b.
        ~(a = b) /\
        (!x. ~(x = a) /\ ~(x = b) ==> f(x) = g(x)) /\
        (f --> l) (at a)
        ==> (g --> l) (at a)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  MESON_TAC[LIM_TRANSFORM_AWAY_WITHIN]);;

(* ------------------------------------------------------------------------- *)
(* Alternatively, within an open set.                                        *)
(* ------------------------------------------------------------------------- *)

let LIM_TRANSFORM_WITHIN_OPEN = prove
 (`!f g:real^M->real^N s a.
        open s /\ a IN s /\
        (!x. x IN s /\ ~(x = a) ==> f x = g x) /\
        (f --> l) (at a)
        ==> (g --> l) (at a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_TRANSFORM_AT THEN
  EXISTS_TAC `f:real^M->real^N` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^M`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
  ASM_MESON_TAC[DIST_NZ; DIST_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Another quite common idiom of an explicit conditional in a sequence.      *)
(* ------------------------------------------------------------------------- *)

let LIM_CASES_FINITE_SEQUENTIALLY = prove
 (`!f g l. FINITE {n | P n}
           ==> (((\n. if P n then f n else g n) --> l) sequentially <=>
                (g --> l) sequentially)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  FIRST_ASSUM(MP_TAC o SPEC `\n:num. n` o MATCH_MP UPPER_BOUND_FINITE_SET) THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN SIMP_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `N + 1` THEN
  ASM_MESON_TAC[ARITH_RULE `~(x <= n /\ n + 1 <= x)`]);;

let LIM_CASES_COFINITE_SEQUENTIALLY = prove
 (`!f g l. FINITE {n | ~P n}
           ==> (((\n. if P n then f n else g n) --> l) sequentially <=>
                (f --> l) sequentially)`,
  ONCE_REWRITE_TAC[TAUT `(if p then x else y) = (if ~p then y else x)`] THEN
  REWRITE_TAC[LIM_CASES_FINITE_SEQUENTIALLY]);;

let LIM_CASES_SEQUENTIALLY = prove
 (`!f g l m. (((\n. if m <= n then f n else g n) --> l) sequentially <=>
              (f --> l) sequentially) /\
             (((\n. if m < n then f n else g n) --> l) sequentially <=>
              (f --> l) sequentially) /\
             (((\n. if n <= m then f n else g n) --> l) sequentially <=>
              (g --> l) sequentially) /\
             (((\n. if n < m then f n else g n) --> l) sequentially <=>
              (g --> l) sequentially)`,
  SIMP_TAC[LIM_CASES_FINITE_SEQUENTIALLY; LIM_CASES_COFINITE_SEQUENTIALLY;
           NOT_LE; NOT_LT; FINITE_NUMSEG_LT; FINITE_NUMSEG_LE]);;

(* ------------------------------------------------------------------------- *)
(* A congruence rule allowing us to transform limits assuming not at point.  *)
(* ------------------------------------------------------------------------- *)

let LIM_CONG_WITHIN = prove
 (`(!x. ~(x = a) ==> f x = g x)
   ==> (((\x. f x) --> l) (at a within s) <=> ((g --> l) (at a within s)))`,
  REWRITE_TAC[LIM_WITHIN; GSYM DIST_NZ] THEN SIMP_TAC[]);;

let LIM_CONG_AT = prove
 (`(!x. ~(x = a) ==> f x = g x)
   ==> (((\x. f x) --> l) (at a) <=> ((g --> l) (at a)))`,
  REWRITE_TAC[LIM_AT; GSYM DIST_NZ] THEN SIMP_TAC[]);;

extend_basic_congs [LIM_CONG_WITHIN; LIM_CONG_AT];;

(* ------------------------------------------------------------------------- *)
(* Useful lemmas on closure and set of possible sequential limits.           *)
(* ------------------------------------------------------------------------- *)

let CLOSURE_SEQUENTIAL = prove
 (`!s l:real^N.
     l IN closure(s) <=> ?x. (!n. x(n) IN s) /\ (x --> l) sequentially`,
  REWRITE_TAC[closure; IN_UNION; LIMPT_SEQUENTIAL; IN_ELIM_THM; IN_DELETE] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
    `((b ==> c) /\ (~a /\ c ==> b)) /\ (a ==> c) ==> (a \/ b <=> c)`) THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  EXISTS_TAC `\n:num. l:real^N` THEN
  ASM_REWRITE_TAC[LIM_CONST]);;

let CLOSED_SEQUENTIAL_LIMITS = prove
 (`!s. closed s <=>
       !x l. (!n. x(n) IN s) /\ (x --> l) sequentially ==> l IN s`,
  MESON_TAC[CLOSURE_SEQUENTIAL; CLOSURE_CLOSED;
            CLOSED_LIMPT; LIMPT_SEQUENTIAL; IN_DELETE]);;

let CLOSURE_APPROACHABLE = prove
 (`!x s. x IN closure(s) <=> !e. &0 < e ==> ?y. y IN s /\ dist(y,x) < e`,
  REWRITE_TAC[closure; LIMPT_APPROACHABLE; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[DIST_REFL]);;

let CLOSED_APPROACHABLE = prove
 (`!x s. closed s
         ==> ((!e. &0 < e ==> ?y. y IN s /\ dist(y,x) < e) <=> x IN s)`,
  MESON_TAC[CLOSURE_CLOSED; CLOSURE_APPROACHABLE]);;

(* ------------------------------------------------------------------------- *)
(* Some other lemmas about sequences.                                        *)
(* ------------------------------------------------------------------------- *)

let SEQ_OFFSET = prove
 (`!f l k. (f --> l) sequentially ==> ((\i. f(i + k)) --> l) sequentially`,
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  MESON_TAC[ARITH_RULE `N <= n ==> N <= n + k:num`]);;

let SEQ_OFFSET_NEG = prove
 (`!f l k. (f --> l) sequentially ==> ((\i. f(i - k)) --> l) sequentially`,
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  MESON_TAC[ARITH_RULE `N + k <= n ==> N <= n - k:num`]);;

let SEQ_OFFSET_REV = prove
 (`!f l k. ((\i. f(i + k)) --> l) sequentially ==> (f --> l) sequentially`,
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  MESON_TAC[ARITH_RULE `N + k <= n ==> N <= n - k /\ (n - k) + k = n:num`]);;

let SEQ_HARMONIC = prove
 (`((\n. lift(inv(&n))) --> vec 0) sequentially`,
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
  EXISTS_TAC `N:num` THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[dist; VECTOR_SUB_RZERO; NORM_LIFT] THEN
  ASM_REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; LT_NZ]);;

(* ------------------------------------------------------------------------- *)
(* More properties of closed balls.                                          *)
(* ------------------------------------------------------------------------- *)

let CLOSED_CBALL = prove
 (`!x:real^N e. closed(cball(x,e))`,
  REWRITE_TAC[CLOSED_SEQUENTIAL_LIMITS; IN_CBALL; dist] THEN
  GEN_TAC THEN GEN_TAC THEN X_GEN_TAC `s:num->real^N` THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\n. x - (s:num->real^N) n` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  ASM_SIMP_TAC[LIM_SUB; LIM_CONST; SEQUENTIALLY] THEN MESON_TAC[GE_REFL]);;

let OPEN_CONTAINS_CBALL = prove
 (`!s. open s <=> !x. x IN s ==> ?e. &0 < e /\ cball(x,e) SUBSET s`,
  GEN_TAC THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[SUBSET_TRANS; BALL_SUBSET_CBALL]] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  SUBGOAL_THEN `e / &2 < e` (fun th -> ASM_MESON_TAC[th; REAL_LET_TRANS]) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;

let OPEN_CONTAINS_CBALL_EQ = prove
 (`!s. open s ==> (!x. x IN s <=> ?e. &0 < e /\ cball(x,e) SUBSET s)`,
  MESON_TAC[OPEN_CONTAINS_CBALL; SUBSET; REAL_LT_IMP_LE; CENTRE_IN_CBALL]);;

let IN_INTERIOR_CBALL = prove
 (`!x s. x IN interior s <=> ?e. &0 < e /\ cball(x,e) SUBSET s`,
  REWRITE_TAC[interior; IN_ELIM_THM] THEN
  MESON_TAC[OPEN_CONTAINS_CBALL; SUBSET_TRANS;
            BALL_SUBSET_CBALL; CENTRE_IN_BALL; OPEN_BALL]);;

let LIMPT_BALL = prove
 (`!x:real^N y e. y limit_point_of ball(x,e) <=> &0 < e /\ y IN cball(x,e)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 < e` THENL
   [ALL_TAC; ASM_MESON_TAC[LIMPT_EMPTY; REAL_NOT_LT; BALL_EQ_EMPTY]] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [MESON_TAC[CLOSED_CBALL; CLOSED_LIMPT; LIMPT_SUBSET; BALL_SUBSET_CBALL];
    REWRITE_TAC[IN_CBALL; LIMPT_APPROACHABLE; IN_BALL]] THEN
  DISCH_TAC THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `y:real^N = x` THEN ASM_REWRITE_TAC[DIST_NZ] THENL
   [MP_TAC(SPECL [`d:real`; `e:real`] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_MESON_TAC 0 40 1 [VECTOR_CHOOSE_DIST; DIST_SYM; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`norm(y:real^N - x)`; `d:real`] REAL_DOWN2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIST_NZ; dist]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(y:real^N) - (k / dist(y,x)) % (y - x)` THEN
  REWRITE_TAC[dist; VECTOR_ARITH `(y - c % z) - y = --c % z`] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; REAL_ABS_NEG] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[VECTOR_ARITH `x - (y - k % (y - x)) = (&1 - k) % (x - y)`] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> &0 < abs k`; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < k /\ k < d ==> abs k < d`] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `norm(x:real^N - y)` THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LT_RMUL THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[NORM_SUB]] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < k /\ k < &1 ==> abs(&1 - k) < &1`) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_MUL_LZERO;
               REAL_MUL_LID]);;

let CLOSURE_BALL = prove
 (`!x:real^N e. &0 < e ==> (closure(ball(x,e)) = cball(x,e))`,
  SIMP_TAC[EXTENSION; closure; IN_ELIM_THM; IN_UNION; LIMPT_BALL] THEN
  REWRITE_TAC[IN_BALL; IN_CBALL] THEN REAL_ARITH_TAC);;

let INTERIOR_CBALL = prove
 (`!x:real^N e. interior(cball(x,e)) = ball(x,e)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 <= e` THENL
   [ALL_TAC;
    SUBGOAL_THEN `cball(x:real^N,e) = {} /\ ball(x:real^N,e) = {}`
     (fun th -> REWRITE_TAC[th; INTERIOR_EMPTY]) THEN
    REWRITE_TAC[IN_BALL; IN_CBALL; EXTENSION; NOT_IN_EMPTY] THEN
    CONJ_TAC THEN X_GEN_TAC `y:real^N` THEN
    MP_TAC(ISPECL [`x:real^N`; `y:real^N`] DIST_POS_LE) THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC INTERIOR_UNIQUE THEN
  REWRITE_TAC[BALL_SUBSET_CBALL; OPEN_BALL] THEN
  X_GEN_TAC `t:real^N->bool` THEN
  SIMP_TAC[SUBSET; IN_CBALL; IN_BALL; REAL_LT_LE] THEN STRIP_TAC THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o GEN_REWRITE_RULE I [open_def]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `z:real^N = x` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `k:real` o MATCH_MP REAL_DOWN) THEN
    SUBGOAL_THEN `?w:real^N. dist(w,x) = k` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[VECTOR_CHOOSE_DIST; DIST_SYM; REAL_LT_IMP_LE];
      ASM_MESON_TAC[REAL_NOT_LE; DIST_REFL; DIST_SYM]];
    RULE_ASSUM_TAC(REWRITE_RULE[DIST_NZ]) THEN
    DISCH_THEN(MP_TAC o SPEC `z + ((d / &2) / dist(z,x)) % (z - x:real^N)`) THEN
    REWRITE_TAC[dist; VECTOR_ADD_SUB; NORM_MUL; REAL_ABS_DIV;
                REAL_ABS_NORM; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; GSYM dist; REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    ASM_REWRITE_TAC[REAL_ARITH `abs d < d * &2 <=> &0 < d`] THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC[dist] THEN
    REWRITE_TAC[VECTOR_ARITH `x - (z + k % (z - x)) = (&1 + k) % (x - z)`] THEN
    REWRITE_TAC[REAL_NOT_LE; NORM_MUL] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ; GSYM dist] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &1 < abs(&1 + x)`) THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH]]);;

let FRONTIER_BALL = prove
 (`!a e. &0 < e
         ==> (frontier(ball(a,e)) = {x | dist(a,x) = e})`,
  SIMP_TAC[frontier; CLOSURE_BALL; INTERIOR_OPEN; OPEN_BALL;
           REAL_LT_IMP_LE] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; IN_BALL; IN_CBALL] THEN
  REAL_ARITH_TAC);;

let FRONTIER_CBALL = prove
 (`!a e. frontier(cball(a,e)) = {x | dist(a,x) = e}`,
  SIMP_TAC[frontier; INTERIOR_CBALL; CLOSED_CBALL; CLOSURE_CLOSED;
           REAL_LT_IMP_LE] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; IN_BALL; IN_CBALL] THEN
  REAL_ARITH_TAC);;

let CBALL_EQ_EMPTY = prove
 (`!x e. (cball(x,e) = {}) <=> e < &0`,
  REWRITE_TAC[EXTENSION; IN_CBALL; NOT_IN_EMPTY; REAL_NOT_LE] THEN
  MESON_TAC[DIST_POS_LE; DIST_REFL; REAL_LTE_TRANS]);;

let CBALL_EMPTY = prove
 (`!x e. e < &0 ==> cball(x,e) = {}`,
  REWRITE_TAC[CBALL_EQ_EMPTY]);;

let CBALL_EQ_SING = prove
 (`!x:real^N e. (cball(x,e) = {x}) <=> e = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_CBALL; IN_SING] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[DIST_LE_0]] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `x + (e / &2) % basis 1:real^N` th) THEN
                       MP_TAC(SPEC `x:real^N` th)) THEN
  REWRITE_TAC[dist; VECTOR_ARITH `x - (x + e):real^N = --e`;
              VECTOR_ARITH `x + e = x <=> e:real^N = vec 0`] THEN
  REWRITE_TAC[NORM_NEG; NORM_MUL; VECTOR_MUL_EQ_0; NORM_0; VECTOR_SUB_REFL] THEN
  SIMP_TAC[NORM_BASIS; BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1] THEN
  REAL_ARITH_TAC);;

let CBALL_SING = prove
 (`!x e. e = &0 ==> cball(x,e) = {x}`,
  REWRITE_TAC[CBALL_EQ_SING]);;

(* ------------------------------------------------------------------------- *)
(* For points in the interior, localization of limits makes no difference.   *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_WITHIN_INTERIOR = prove
 (`!p s x.
        x IN interior s
        ==> (eventually p (at x within s) <=> eventually p (at x))`,
  REWRITE_TAC[EVENTUALLY_WITHIN; EVENTUALLY_AT; IN_INTERIOR] THEN
  REPEAT GEN_TAC THEN SIMP_TAC[SUBSET; IN_BALL; LEFT_IMP_FORALL_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (d:real) e` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  ASM_MESON_TAC[DIST_SYM]);;

let LIM_WITHIN_INTERIOR = prove
 (`!f l s x.
        x IN interior s
        ==> ((f --> l) (at x within s) <=> (f --> l) (at x))`,
  SIMP_TAC[tendsto; EVENTUALLY_WITHIN_INTERIOR]);;

let NETLIMIT_WITHIN_INTERIOR = prove
 (`!s x:real^N. x IN interior s ==> netlimit(at x within s) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NETLIMIT_WITHIN THEN
  REWRITE_TAC[TRIVIAL_LIMIT_WITHIN] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP(REWRITE_RULE[OPEN_CONTAINS_BALL]
   (SPEC_ALL OPEN_INTERIOR))) THEN
  ASM_MESON_TAC[LIMPT_SUBSET; LIMPT_BALL; CENTRE_IN_CBALL; REAL_LT_IMP_LE;
                SUBSET_TRANS; INTERIOR_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Boundedness.                                                              *)
(* ------------------------------------------------------------------------- *)

let bounded = new_definition
  `bounded s <=> ?a. !x:real^N. x IN s ==> norm(x) <= a`;;

let BOUNDED_EMPTY = prove
 (`bounded {}`,
  REWRITE_TAC[bounded; NOT_IN_EMPTY]);;

let BOUNDED_SUBSET = prove
 (`!s t. bounded t /\ s SUBSET t ==> bounded s`,
  MESON_TAC[bounded; SUBSET]);;

let BOUNDED_INTERIOR = prove
 (`!s:real^N->bool. bounded s ==> bounded(interior s)`,
  MESON_TAC[BOUNDED_SUBSET; INTERIOR_SUBSET]);;

let BOUNDED_CLOSURE = prove
 (`!s:real^N->bool. bounded s ==> bounded(closure s)`,
  REWRITE_TAC[bounded; CLOSURE_SEQUENTIAL] THEN
  GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MESON_TAC[REWRITE_RULE[eventually] LIM_NORM_UBOUND;
            TRIVIAL_LIMIT_SEQUENTIALLY; trivial_limit]);;

let BOUNDED_CLOSURE_EQ = prove
 (`!s:real^N->bool. bounded(closure s) <=> bounded s`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[BOUNDED_CLOSURE] THEN
  MESON_TAC[BOUNDED_SUBSET; CLOSURE_SUBSET]);;

let BOUNDED_CBALL = prove
 (`!x:real^N e. bounded(cball(x,e))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bounded] THEN
  EXISTS_TAC `norm(x:real^N) + e` THEN REWRITE_TAC[IN_CBALL; dist] THEN
  NORM_ARITH_TAC);;

let BOUNDED_BALL = prove
 (`!x e. bounded(ball(x,e))`,
  MESON_TAC[BALL_SUBSET_CBALL; BOUNDED_CBALL; BOUNDED_SUBSET]);;

let FINITE_IMP_BOUNDED = prove
 (`!s:real^N->bool. FINITE s ==> bounded s`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[BOUNDED_EMPTY] THEN
  REWRITE_TAC[bounded; IN_INSERT] THEN X_GEN_TAC `x:real^N` THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `B:real`) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `norm(x:real^N) + abs B` THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[NORM_POS_LE; REAL_ARITH
   `(y <= b /\ &0 <= x ==> y <= x + abs b) /\ x <= x + abs b`]);;

let BOUNDED_UNION = prove
 (`!s t. bounded (s UNION t) <=> bounded s /\ bounded t`,
  REWRITE_TAC[bounded; IN_UNION] THEN MESON_TAC[REAL_LE_MAX]);;

let BOUNDED_UNIONS = prove
 (`!f. FINITE f /\ (!s. s IN f ==> bounded s) ==> bounded(UNIONS f)`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; BOUNDED_EMPTY; IN_INSERT; UNIONS_INSERT] THEN
  MESON_TAC[BOUNDED_UNION]);;

let BOUNDED_POS = prove
 (`!s. bounded s <=> ?b. &0 < b /\ !x. x IN s ==> norm(x) <= b`,
  REWRITE_TAC[bounded] THEN
  MESON_TAC[REAL_ARITH `&0 < &1 + abs(y) /\ (x <= y ==> x <= &1 + abs(y))`]);;

let BOUNDED_POS_LT = prove
 (`!s. bounded s <=> ?b. &0 < b /\ !x. x IN s ==> norm(x) < b`,
  REWRITE_TAC[bounded] THEN
  MESON_TAC[REAL_LT_IMP_LE;
            REAL_ARITH `&0 < &1 + abs(y) /\ (x <= y ==> x < &1 + abs(y))`]);;

let BOUNDED_INTER = prove
 (`!s t. bounded s \/ bounded t ==> bounded (s INTER t)`,
  MESON_TAC[BOUNDED_SUBSET; INTER_SUBSET]);;

let BOUNDED_DIFF = prove
 (`!s t. bounded s ==> bounded (s DIFF t)`,
  MESON_TAC[BOUNDED_SUBSET; SUBSET_DIFF]);;

let BOUNDED_INSERT = prove
 (`!x s. bounded(x INSERT s) <=> bounded s`,
  ONCE_REWRITE_TAC[SET_RULE `x INSERT s = {x} UNION s`] THEN
  SIMP_TAC[BOUNDED_UNION; FINITE_IMP_BOUNDED; FINITE_RULES]);;

let NOT_BOUNDED_UNIV = prove
 (`~(bounded (:real^N))`,
  REWRITE_TAC[BOUNDED_POS; NOT_FORALL_THM; NOT_EXISTS_THM; IN_UNIV;
              DE_MORGAN_THM; REAL_NOT_LE] THEN
  X_GEN_TAC `B:real` THEN ASM_CASES_TAC `&0 < B` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `B + &1` VECTOR_CHOOSE_SIZE) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < B ==> &0 <= B + &1`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REAL_ARITH_TAC);;

let COBOUNDED_IMP_UNBOUNDED = prove
 (`!s. bounded((:real^N) DIFF s) ==> ~bounded s`,
  GEN_TAC THEN REWRITE_TAC[TAUT `a ==> ~b <=> ~(a /\ b)`] THEN
  REWRITE_TAC[GSYM BOUNDED_UNION; SET_RULE `UNIV DIFF s UNION s = UNIV`] THEN
  REWRITE_TAC[NOT_BOUNDED_UNIV]);;

let BOUNDED_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s. bounded s /\ linear f ==> bounded(IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `B1:real`) MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `B2:real` o MATCH_MP LINEAR_BOUNDED_POS) THEN
  EXISTS_TAC `B2 * B1` THEN ASM_SIMP_TAC[REAL_LT_MUL; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B2 * norm(x:real^M)` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ]);;

let BOUNDED_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (bounded (IMAGE f s) <=> bounded s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE BOUNDED_LINEAR_IMAGE));;

add_linear_invariants [BOUNDED_LINEAR_IMAGE_EQ];;

let BOUNDED_SCALING = prove
 (`!c s. bounded s ==> bounded (IMAGE (\x. c % x) s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BOUNDED_LINEAR_IMAGE THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE_CMUL; LINEAR_ID]);;

let BOUNDED_NEGATIONS = prove
 (`!s. bounded s ==> bounded (IMAGE (--) s)`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `-- &1` o MATCH_MP BOUNDED_SCALING) THEN
  REWRITE_TAC[bounded; IN_IMAGE; VECTOR_MUL_LNEG; VECTOR_MUL_LID]);;

let BOUNDED_TRANSLATION = prove
 (`!a:real^N s. bounded s ==> bounded (IMAGE (\x. a + x) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC `B + norm(a:real^N)` THEN POP_ASSUM MP_TAC THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL [NORM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN NORM_ARITH_TAC);;

let BOUNDED_TRANSLATION_EQ = prove
 (`!a s. bounded (IMAGE (\x:real^N. a + x) s) <=> bounded s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[BOUNDED_TRANSLATION] THEN
  DISCH_THEN(MP_TAC o SPEC `--a:real^N` o MATCH_MP BOUNDED_TRANSLATION) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID;
              VECTOR_ARITH `--a + a + x:real^N = x`]);;

add_translation_invariants [BOUNDED_TRANSLATION_EQ];;

let BOUNDED_DIFFS = prove
 (`!s t:real^N->bool.
        bounded s /\ bounded t ==> bounded {x - y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `B:real`) (X_CHOOSE_TAC `C:real`)) THEN
  EXISTS_TAC `B + C:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REPEAT STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(NORM_ARITH
   `norm x <= a /\ norm y <= b ==> norm(x - y) <= a + b`) THEN
  ASM_SIMP_TAC[]);;

let BOUNDED_SUMS = prove
 (`!s t:real^N->bool.
        bounded s /\ bounded t ==> bounded {x + y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `B:real`) (X_CHOOSE_TAC `C:real`)) THEN
  EXISTS_TAC `B + C:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REPEAT STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(NORM_ARITH
   `norm x <= a /\ norm y <= b ==> norm(x + y) <= a + b`) THEN
  ASM_SIMP_TAC[]);;

let BOUNDED_SUMS_IMAGE = prove
 (`!f g t. bounded {f x | x IN t} /\ bounded {g x | x IN t}
           ==> bounded {f x + g x | x IN t}`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_SUMS) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] BOUNDED_SUBSET) THEN
  SET_TAC[]);;

let BOUNDED_SUMS_IMAGES = prove
 (`!f:A->B->real^N t s.
        FINITE s /\
        (!a. a IN s ==> bounded {f x a | x IN t})
        ==> bounded { vsum s (f x) | x IN t}`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES] THEN CONJ_TAC THENL
   [DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `{vec 0:real^N}` THEN
    SIMP_TAC[FINITE_IMP_BOUNDED; FINITE_RULES] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BOUNDED_SUMS_IMAGE THEN
  ASM_SIMP_TAC[IN_INSERT]);;

let BOUNDED_SUBSET_BALL = prove
 (`!s x:real^N. bounded(s) ==> ?r. &0 < r /\ s SUBSET ball(x,r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&2 * B + norm(x:real^N)` THEN
  ASM_SIMP_TAC[NORM_POS_LE; REAL_ARITH
    `&0 < B /\ &0 <= x ==> &0 < &2 * B + x`] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[IN_BALL] THEN
  UNDISCH_TAC `&0 < B` THEN NORM_ARITH_TAC);;

let BOUNDED_SUBSET_CBALL = prove
 (`!s x:real^N. bounded(s) ==> ?r. &0 < r /\ s SUBSET cball(x,r)`,
  MESON_TAC[BOUNDED_SUBSET_BALL; SUBSET_TRANS; BALL_SUBSET_CBALL]);;

let UNBOUNDED_INTER_COBOUNDED = prove
 (`!s t. ~bounded s /\ bounded((:real^N) DIFF t) ==> ~(s INTER t = {})`,
  REWRITE_TAC[SET_RULE `s INTER t = {} <=> s SUBSET (:real^N) DIFF t`] THEN
  MESON_TAC[BOUNDED_SUBSET]);;

let COBOUNDED_INTER_UNBOUNDED = prove
 (`!s t. bounded((:real^N) DIFF s) /\ ~bounded t ==> ~(s INTER t = {})`,
  REWRITE_TAC[SET_RULE `s INTER t = {} <=> t SUBSET (:real^N) DIFF s`] THEN
  MESON_TAC[BOUNDED_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Some theorems on sups and infs using the notion "bounded".                *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_LIFT = prove
 (`!s. bounded(IMAGE lift s) <=>  ?a. !x. x IN s ==> abs(x) <= a`,
  REWRITE_TAC[bounded; FORALL_LIFT; NORM_LIFT; LIFT_IN_IMAGE_LIFT]);;

let BOUNDED_HAS_SUP = prove
 (`!s. bounded(IMAGE lift s) /\ ~(s = {})
       ==> (!x. x IN s ==> x <= sup s) /\
           (!b. (!x. x IN s ==> x <= b) ==> sup s <= b)`,
  REWRITE_TAC[BOUNDED_LIFT; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[SUP; REAL_ARITH `abs(x) <= a ==> x <= a`]);;

let SUP_INSERT = prove
 (`!x s. bounded (IMAGE lift s)
         ==> sup(x INSERT s) = if s = {} then x else max x (sup s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUP_UNIQUE THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING] THENL
   [MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_MAX; REAL_LT_MAX; IN_INSERT] THEN
  MP_TAC(ISPEC `s:real->bool` BOUNDED_HAS_SUP) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[REAL_LE_REFL; REAL_NOT_LT]);;

let SUP_INSERT_FINITE = prove
 (`!x s. FINITE s ==> sup(x INSERT s) = if s = {} then x else max x (sup s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUP_INSERT THEN
  MATCH_MP_TAC FINITE_IMP_BOUNDED THEN ASM_SIMP_TAC[FINITE_IMAGE]);;

let BOUNDED_HAS_INF = prove
 (`!s. bounded(IMAGE lift s) /\ ~(s = {})
       ==> (!x. x IN s ==> inf s <= x) /\
           (!b. (!x. x IN s ==> b <= x) ==> b <= inf s)`,
  REWRITE_TAC[BOUNDED_LIFT; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[INF; REAL_ARITH `abs(x) <= a ==> --a <= x`]);;

let INF_INSERT = prove
 (`!x s. bounded (IMAGE lift s)
         ==> inf(x INSERT s) = if s = {} then x else min x (inf s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INF_UNIQUE THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING] THENL
   [MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MIN_LE; REAL_MIN_LT; IN_INSERT] THEN
  MP_TAC(ISPEC `s:real->bool` BOUNDED_HAS_INF) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[REAL_LE_REFL; REAL_NOT_LT]);;

let INF_INSERT_FINITE = prove
 (`!x s. FINITE s ==> inf(x INSERT s) = if s = {} then x else min x (inf s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INF_INSERT THEN
  MATCH_MP_TAC FINITE_IMP_BOUNDED THEN ASM_SIMP_TAC[FINITE_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Compactness (the definition is the one based on convegent subsequences).  *)
(* ------------------------------------------------------------------------- *)

let compact = new_definition
  `compact s <=>
        !f:num->real^N.
            (!n. f(n) IN s)
            ==> ?l r. l IN s /\ (!m n:num. m < n ==> r(m) < r(n)) /\
                      ((f o r) --> l) sequentially`;;

let MONOTONE_BIGGER = prove
 (`!r. (!m n. m < n ==> r(m) < r(n)) ==> !n:num. n <= r(n)`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  ASM_MESON_TAC[LE_0; ARITH_RULE `n <= m /\ m < p ==> SUC n <= p`; LT]);;

let LIM_SUBSEQUENCE = prove
 (`!s r. (!m n. m < n ==> r(m) < r(n)) /\ (s --> l) sequentially
         ==> (s o r --> l) sequentially`,
  REWRITE_TAC[LIM_SEQUENTIALLY; o_THM] THEN
  MESON_TAC[MONOTONE_BIGGER; LE_TRANS]);;

let MONOTONE_SUBSEQUENCE = prove
 (`!s:num->real. ?r:num->num.
           (!m n. m < n ==> r(m) < r(n)) /\
           ((!m n. m <= n ==> s(r(m)) <= s(r(n))) \/
            (!m n. m <= n ==> s(r(n)) <= s(r(m))))`,
  GEN_TAC THEN
  ASM_CASES_TAC `!n:num. ?p. n < p /\ !m. p <= m ==> s(m) <= s(p)` THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM; NOT_IMP; DE_MORGAN_THM] THEN
  REWRITE_TAC[RIGHT_OR_EXISTS_THM; SKOLEM_THM; REAL_NOT_LE; REAL_NOT_LT] THENL
   [ABBREV_TAC `N = 0`; DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC)] THEN
  DISCH_THEN(X_CHOOSE_THEN `next:num->num` STRIP_ASSUME_TAC) THEN
  (MP_TAC o prove_recursive_functions_exist num_RECURSION)
   `(r 0 = next(SUC N)) /\ (!n. r(SUC n) = next(r n))` THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `!m:num n:num. r n <= m ==> s(m) <= s(r n):real`
    ASSUME_TAC THEN TRY CONJ_TAC THEN TRY DISJ2_TAC THEN
    GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[LT; LE] THEN
    ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL; LT_IMP_LE; LT_TRANS];
    SUBGOAL_THEN `!n. N < (r:num->num) n` ASSUME_TAC THEN
    TRY(CONJ_TAC THENL [GEN_TAC; DISJ1_TAC THEN GEN_TAC]) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[LT; LE] THEN
    TRY STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[REAL_LT_REFL; LT_LE; LTE_TRANS; REAL_LE_REFL;
                  REAL_LT_LE; REAL_LE_TRANS; LT]]);;

let CONVERGENT_BOUNDED_INCREASING = prove
 (`!s:num->real b. (!m n. m <= n ==> s m <= s n) /\ (!n. abs(s n) <= b)
                   ==> ?l. !e. &0 < e ==> ?N. !n. N <= n ==> abs(s n - l) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\x. ?n. (s:num->real) n = x` REAL_COMPLETE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_ARITH `abs(x) <= b ==> x <= b`]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real` THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l - e`) THEN
  ASM_MESON_TAC[REAL_ARITH `&0 < e ==> ~(l <= l - e)`;
      REAL_ARITH `x <= y /\ y <= l /\ ~(x <= l - e) ==> abs(y - l) < e`]);;

let CONVERGENT_BOUNDED_MONOTONE = prove
 (`!s:num->real b. (!n. abs(s n) <= b) /\
                   ((!m n. m <= n ==> s m <= s n) \/
                    (!m n. m <= n ==> s n <= s m))
                   ==> ?l. !e. &0 < e ==> ?N. !n. N <= n ==> abs(s n - l) < e`,
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[CONVERGENT_BOUNDED_INCREASING]; ALL_TAC] THEN
  MP_TAC(SPEC `\n. --((s:num->real) n)` CONVERGENT_BOUNDED_INCREASING) THEN
  ASM_REWRITE_TAC[REAL_LE_NEG2; REAL_ABS_NEG] THEN
  ASM_MESON_TAC[REAL_ARITH `abs(x - --l) = abs(--x - l)`]);;

let COMPACT_REAL_LEMMA = prove
 (`!s b. (!n:num. abs(s n) <= b)
         ==> ?l r. (!m n:num. m < n ==> r(m) < r(n)) /\
                   !e. &0 < e ==> ?N. !n. N <= n ==> abs(s(r n) - l) < e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MP_TAC(SPEC `s:num->real` MONOTONE_SUBSEQUENCE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC CONVERGENT_BOUNDED_MONOTONE THEN ASM_MESON_TAC[]);;

let COMPACT_LEMMA = prove
 (`!s. bounded s /\ (!n. (x:num->real^N) n IN s)
       ==> !d. d <= dimindex(:N)
               ==> ?l:real^N r. (!m n. m < n ==> r m < (r:num->num) n) /\
                         !e. &0 < e
                             ==> ?N. !n i. 1 <= i /\ i <= d
                                           ==> N <= n
                                               ==> abs(x(r n)$i - l$i) < e`,
  GEN_TAC THEN REWRITE_TAC[bounded] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `b:real`) ASSUME_TAC) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 0 <=> F`; CONJ_ASSOC] THEN
    DISCH_TAC THEN EXISTS_TAC `\n:num. n` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC d <= n ==> d <= n`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`\n:num. (x:num->real^N) (r n) $ (SUC d)`; `b:real`]
         COMPACT_REAL_LEMMA) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS; COMPONENT_LE_NORM; ARITH_RULE `1 <= SUC n`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real` (X_CHOOSE_THEN `s:num->num`
        STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`(lambda k. if k = SUC d then y else (l:real^N)$k):real^N`;
    `(r:num->num) o (s:num->num)`] THEN
  ASM_SIMP_TAC[o_THM] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REPEAT(FIRST_ASSUM(C UNDISCH_THEN (MP_TAC o SPEC `e:real`) o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN EXISTS_TAC `N1 + N2:num` THEN
  FIRST_ASSUM(fun th -> SIMP_TAC[LAMBDA_BETA; MATCH_MP(ARITH_RULE
   `SUC d <= n ==> !i. 1 <= i /\ i <= SUC d ==> 1 <= i /\ i <= n`) th]) THEN
  REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN
  ASM_MESON_TAC[MONOTONE_BIGGER; LE_TRANS;
    ARITH_RULE `N1 + N2 <= n ==> N2 <= n:num /\ N1 <= n`;
    ARITH_RULE `1 <= i /\ i <= d /\ SUC d <= n
                ==> ~(i = SUC d) /\ 1 <= SUC d /\ d <= n /\ i <= n`]);;

let BOUNDED_CLOSED_IMP_COMPACT = prove
 (`!s:real^N->bool. bounded s /\ closed s ==> compact s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[compact] THEN
  X_GEN_TAC `x:num->real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` COMPACT_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `dimindex(:N)`) THEN
  REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:num->num` THEN ASM_SIMP_TAC[] THEN
  STRIP_TAC THEN MATCH_MP_TAC(TAUT `(b ==> a) /\ b ==> a /\ b`) THEN
  REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CLOSED_SEQUENTIAL_LIMITS]) THEN
    EXISTS_TAC `(x:num->real^N) o (r:num->num)` THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2 / &(dimindex(:N))`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; DIMINDEX_NONZERO;
               REAL_HALF; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  REWRITE_TAC[dist] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MATCH_MP (REAL_ARITH `a <= b ==> b < e ==> a < e`)
                        (SPEC_ALL NORM_LE_L1)) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sum (1..dimindex(:N))
                  (\k. e / &2 / &(dimindex(:N)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN
    SIMP_TAC[o_THM; LAMBDA_BETA; vector_sub] THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE; LE_TRANS];
    ASM_SIMP_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_DIV_LMUL; REAL_OF_NUM_EQ;
                 DIMINDEX_NONZERO; REAL_LE_REFL; REAL_LT_LDIV_EQ; ARITH;
                 REAL_OF_NUM_LT; REAL_ARITH `x < x * &2 <=> &0 < x`]]);;

(* ------------------------------------------------------------------------- *)
(* Completeness.                                                             *)
(* ------------------------------------------------------------------------- *)

let cauchy = new_definition
  `cauchy (s:num->real^N) <=>
     !e. &0 < e ==> ?N. !m n. m >= N /\ n >= N ==> dist(s m,s n) < e`;;

let complete = new_definition
  `complete s <=>
     !f:num->real^N. (!n. f n IN s) /\ cauchy f
                      ==> ?l. l IN s /\ (f --> l) sequentially`;;

let CAUCHY = prove
 (`!s:num->real^N.
      cauchy s <=> !e. &0 < e ==> ?N. !n. n >= N ==> dist(s n,s N) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cauchy; GE] THEN EQ_TAC THENL
   [MESON_TAC[LE_REFL]; DISCH_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MESON_TAC[DIST_TRIANGLE_HALF_L]);;

let CONVERGENT_IMP_CAUCHY = prove
 (`!s l. (s --> l) sequentially ==> cauchy s`,
  REWRITE_TAC[LIM_SEQUENTIALLY; cauchy] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  ASM_MESON_TAC[GE; LE_REFL; DIST_TRIANGLE_HALF_L]);;

let CAUCHY_IMP_BOUNDED = prove
 (`!s:num->real^N. cauchy s ==> bounded {y | ?n. y = s n}`,
  REWRITE_TAC[cauchy; bounded; IN_ELIM_THM] THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
  REWRITE_TAC[GE_REFL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n:num. N <= n ==> norm(s n :real^N) <= norm(s N) + &1`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[GE; dist; DIST_SYM; NORM_TRIANGLE_SUB;
                  REAL_ARITH `a <= b + c /\ c < &1 ==> a <= b + &1`];
    MP_TAC(ISPECL [`\n:num. norm(s n :real^N)`; `0..N`]
                  UPPER_BOUND_FINITE_SET_REAL) THEN
    SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0; LEFT_IMP_EXISTS_THM] THEN
    ASM_MESON_TAC[LE_CASES;
                  REAL_ARITH `x <= a \/ x <= b ==> x <= abs a + abs b`]]);;

let COMPACT_IMP_COMPLETE = prove
 (`!s:real^N->bool. compact s ==> complete s`,
  GEN_TAC THEN REWRITE_TAC[complete; compact] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `f:num->real^N` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] LIM_ADD)) THEN
  DISCH_THEN(MP_TAC o SPEC `\n. (f:num->real^N)(n) - f(r n)`) THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0: real^N`) THEN ASM_REWRITE_TAC[o_THM] THEN
  REWRITE_TAC[VECTOR_ADD_RID; VECTOR_SUB_ADD2; ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cauchy]) THEN
  REWRITE_TAC[GE; LIM; SEQUENTIALLY; dist; VECTOR_SUB_RZERO] THEN
  SUBGOAL_THEN `!n:num. n <= r(n)` MP_TAC THENL [INDUCT_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[ LE_TRANS; LE_REFL; LT; LET_TRANS; LE_0; LE_SUC_LT]);;

let COMPLETE_UNIV = prove
 (`complete(:real^N)`,
  REWRITE_TAC[complete; IN_UNIV] THEN X_GEN_TAC `x:num->real^N` THEN
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP CAUCHY_IMP_BOUNDED) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP BOUNDED_CLOSURE) THEN
  MP_TAC(ISPEC `closure {y:real^N | ?n:num. y = x n}`
               COMPACT_IMP_COMPLETE) THEN
  ASM_SIMP_TAC[BOUNDED_CLOSED_IMP_COMPACT; CLOSED_CLOSURE; complete] THEN
  DISCH_THEN(MP_TAC o SPEC `x:num->real^N`) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  ASM_REWRITE_TAC[closure; IN_ELIM_THM; IN_UNION] THEN MESON_TAC[]);;

let COMPLETE_EQ_CLOSED = prove
 (`!s:real^N->bool. complete s <=> closed s`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[complete; CLOSED_LIMPT; LIMPT_SEQUENTIAL] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN GEN_TAC THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
    MESON_TAC[CONVERGENT_IMP_CAUCHY; IN_DELETE; LIM_UNIQUE;
              TRIVIAL_LIMIT_SEQUENTIALLY];
    REWRITE_TAC[complete; CLOSED_SEQUENTIAL_LIMITS] THEN DISCH_TAC THEN
    X_GEN_TAC `f:num->real^N` THEN STRIP_TAC THEN
    MP_TAC(REWRITE_RULE[complete] COMPLETE_UNIV) THEN
    DISCH_THEN(MP_TAC o SPEC `f:num->real^N`) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN ASM_MESON_TAC[]]);;

let CONVERGENT_EQ_CAUCHY = prove
 (`!s. (?l. (s --> l) sequentially) <=> cauchy s`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM; CONVERGENT_IMP_CAUCHY];
    REWRITE_TAC[REWRITE_RULE[complete; IN_UNIV] COMPLETE_UNIV]]);;

let CONVERGENT_IMP_BOUNDED = prove
 (`!s l. (s --> l) sequentially ==> bounded (IMAGE s (:num))`,
  REWRITE_TAC[LEFT_FORALL_IMP_THM; CONVERGENT_EQ_CAUCHY] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CAUCHY_IMP_BOUNDED) THEN
  REWRITE_TAC[IMAGE; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Total boundedness.                                                        *)
(* ------------------------------------------------------------------------- *)

let COMPACT_IMP_TOTALLY_BOUNDED = prove
 (`!s:real^N->bool.
        compact s
        ==> !e. &0 < e ==> ?k. FINITE k /\ k SUBSET s /\
                               s SUBSET (UNIONS(IMAGE (\x. ball(x,e)) k))`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`; SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?x:num->real^N. !n. x(n) IN s /\ !m. m < n ==> ~(dist(x(m),x(n)) < e)`
  MP_TAC THENL
   [SUBGOAL_THEN
     `?x:num->real^N.
          !n. x(n) = @y. y IN s /\ !m. m < n ==> ~(dist(x(m),y) < e)`
    MP_TAC THENL
     [MATCH_MP_TAC(MATCH_MP WF_REC WF_num) THEN SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:num->real^N` THEN
    DISCH_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    CONV_TAC SELECT_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (x:num->real^N) {m | m < n}`) THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; NOT_FORALL_THM; NOT_IMP] THEN
    REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[IN_BALL];
    ALL_TAC] THEN
  REWRITE_TAC[compact; NOT_FORALL_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `x:num->real^N` THEN  REWRITE_TAC[NOT_IMP; FORALL_AND_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CONVERGENT_IMP_CAUCHY) THEN
  REWRITE_TAC[cauchy] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[o_THM; NOT_EXISTS_THM; NOT_IMP; NOT_FORALL_THM; NOT_IMP] THEN
  X_GEN_TAC `N:num` THEN MAP_EVERY EXISTS_TAC [`N:num`; `SUC N`] THEN
  CONJ_TAC THENL [ARITH_TAC; ASM_MESON_TAC[LT]]);;

(* ------------------------------------------------------------------------- *)
(* Heine-Borel theorem (following Burkill & Burkill vol. 2)                  *)
(* ------------------------------------------------------------------------- *)

let HEINE_BOREL_LEMMA = prove
 (`!s:real^N->bool.
      compact s
      ==> !t. s SUBSET (UNIONS t) /\ (!b. b IN t ==> open b)
              ==> ?e. &0 < e /\
                      !x. x IN s ==> ?b. b IN t /\ ball(x,e) SUBSET b`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&1 / (&n + &1)`) THEN
  SIMP_TAC[REAL_LT_DIV; REAL_LT_01; REAL_ARITH `x <= y ==> x < y + &1`;
   FORALL_AND_THM; REAL_POS; NOT_FORALL_THM; NOT_IMP; SKOLEM_THM; compact] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`l:real^N`; `r:num->num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?b:real^N->bool. l IN b /\ b IN t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; IN_UNIONS]; ALL_TAC] THEN
  SUBGOAL_THEN `?e. &0 < e /\ !z:real^N. dist(z,l) < e ==> z IN b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[open_def]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  SUBGOAL_THEN `&0 < e / &2` (fun th ->
    REWRITE_TAC[th; o_THM] THEN MP_TAC(GEN_REWRITE_RULE I [REAL_ARCH_INV] th))
  THENL [ASM_REWRITE_TAC[REAL_HALF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(r:num->num)(N1 + N2)`; `b:real^N->bool`]) THEN
  ASM_REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC DIST_TRIANGLE_HALF_R THEN
  EXISTS_TAC `(f:num->real^N)(r(N1 + N2:num))` THEN CONJ_TAC THENL
   [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_BALL]) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x < a ==> x < b`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&N1)` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
  ASM_MESON_TAC[ARITH_RULE `(~(n = 0) ==> 0 < n)`; LE_ADD; MONOTONE_BIGGER;
                LT_IMP_LE; LE_TRANS]);;

let COMPACT_IMP_HEINE_BOREL = prove
 (`!s. compact (s:real^N->bool)
       ==> !f. (!t. t IN f ==> open t) /\ s SUBSET (UNIONS f)
               ==> ?f'. f' SUBSET f /\ FINITE f' /\ s SUBSET (UNIONS f')`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `f:(real^N->bool)->bool` o
    MATCH_MP HEINE_BOREL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real^N->real^N->bool`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `e:real` o
    MATCH_MP COMPACT_IMP_TOTALLY_BOUNDED) THEN
  ASM_REWRITE_TAC[UNIONS_IMAGE; SUBSET; IN_ELIM_THM] THEN
  REWRITE_TAC[IN_UNIONS; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (B:real^N->real^N->bool) k` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; SUBSET; IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  ASM_MESON_TAC[IN_BALL]);;

(* ------------------------------------------------------------------------- *)
(* Bolzano-Weierstrass property.                                             *)
(* ------------------------------------------------------------------------- *)

let HEINE_BOREL_IMP_BOLZANO_WEIERSTRASS = prove
 (`!s:real^N->bool.
        (!f. (!t. t IN f ==> open t) /\ s SUBSET (UNIONS f)
             ==> ?f'. f' SUBSET f /\ FINITE f' /\ s SUBSET (UNIONS f'))
        ==> !t. INFINITE t /\ t SUBSET s ==> ?x. x IN s /\ x limit_point_of t`,
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; limit_point_of] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b /\ c ==> d <=> c ==> ~d ==> a ==> ~b`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM; RIGHT_AND_FORALL_THM] THEN
  DISCH_TAC THEN REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `f:real^N->real^N->bool`) THEN
  DISCH_THEN(MP_TAC o SPEC
   `{t:real^N->bool | ?x:real^N. x IN s /\ (t = f x)}`) THEN
  REWRITE_TAC[INFINITE; SUBSET; IN_ELIM_THM; IN_UNIONS; NOT_IMP] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x:real^N | x IN t /\ (f(x):real^N->bool) IN g}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ_GENERAL THEN ASM_MESON_TAC[SUBSET];
    SIMP_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `u:real^N` THEN
    DISCH_TAC THEN SUBGOAL_THEN `(u:real^N) IN s` ASSUME_TAC THEN
    ASM_MESON_TAC[SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* Complete the chain of compactness variants.                               *)
(* ------------------------------------------------------------------------- *)

let BOLZANO_WEIERSTRASS_IMP_BOUNDED = prove
 (`!s:real^N->bool.
        (!t. INFINITE t /\ t SUBSET s ==> ?x. x IN s /\ x limit_point_of t)
        ==> bounded s`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  SIMP_TAC[compact; bounded] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM; SKOLEM_THM; NOT_IMP] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_THEN(X_CHOOSE_TAC `beyond:real->real^N`) THEN
  (MP_TAC o prove_recursive_functions_exist num_RECURSION)
   `(f(0) = beyond(&0)) /\
    (!n. f(SUC n) = beyond(norm(f n) + &1):real^N)` THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (x:num->real^N) UNIV` THEN
  SUBGOAL_THEN
   `!m n. m < n ==> norm((x:num->real^N) m) + &1 < norm(x n)`
  ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[LT] THEN
    ASM_MESON_TAC[REAL_LT_TRANS; REAL_ARITH `b < b + &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. ~(m = n) ==> &1 < dist((x:num->real^N) m,x n)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [`m:num`; `n:num`] LT_CASES) THEN
    ASM_MESON_TAC[dist; LT_CASES; NORM_TRIANGLE_SUB; NORM_SUB;
                  REAL_ARITH `x + &1 < y /\ y <= x + d ==> &1 < d`];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[INFINITE_IMAGE_INJ; num_INFINITE; DIST_REFL;
                  REAL_ARITH `~(&1 < &0)`];
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN INDUCT_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `l:real^N` THEN REWRITE_TAC[LIMPT_APPROACHABLE] THEN
  REWRITE_TAC[IN_IMAGE; IN_UNIV; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `&1 / &2`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `dist((x:num->real^N) k,l)`) THEN
  ASM_SIMP_TAC[DIST_POS_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `m:num = k` THEN
  ASM_MESON_TAC[DIST_TRIANGLE_HALF_L; REAL_LT_TRANS; REAL_LT_REFL]);;

let SEQUENCE_INFINITE_LEMMA = prove
 (`!f l. (!n. ~(f(n) = l)) /\ (f --> l) sequentially
         ==> INFINITE {y:real^N | ?n. y = f n}`,
  REWRITE_TAC[INFINITE] THEN REPEAT STRIP_TAC THEN MP_TAC(ISPEC
   `IMAGE (\y:real^N. dist(y,l)) {y | ?n:num. y = f n}` INF_FINITE) THEN
  ASM_SIMP_TAC[GSYM MEMBER_NOT_EMPTY; IN_IMAGE; FINITE_IMAGE; IN_ELIM_THM] THEN
  ASM_MESON_TAC[LIM_SEQUENTIALLY; LE_REFL; REAL_NOT_LE; DIST_POS_LT]);;

let SEQUENCE_UNIQUE_LIMPT = prove
 (`!f l. (!n. ~(f(n) = l)) /\ (f --> l) sequentially
         ==> !l'. l' limit_point_of {y:real^N | ?n. y = f n}
                  ==> (l' = l)`,
  let tm =
   `(e / &2) INSERT
    (IMAGE (\n. if dist((f:num->real^N) n,l') = &0 then e / &2
                else dist((f:num->real^N) n,l'))
           {n | n < N})` in
  REWRITE_TAC[LIMPT_APPROACHABLE; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  REPEAT STRIP_TAC THEN ABBREV_TAC `e = dist(l':real^N,l)` THEN
  SUBGOAL_THEN `~(&0 < e)` (fun th -> ASM_MESON_TAC[th; DIST_POS_LT]) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN MP_TAC(ISPEC tm INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_RULES; FINITE_IMAGE; FINITE_NUMSEG_LT;
               NOT_EMPTY_INSERT] THEN
  ABBREV_TAC(mk_eq(`d:real`,mk_comb(`inf`,tm))) THEN
  REWRITE_TAC[IN_INSERT; IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    REPEAT COND_CASES_TAC THEN
    ASM_MESON_TAC[REAL_HALF; REAL_LT_LE; DIST_POS_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `e / &2` th) THEN
                   MP_TAC(SPEC `dist((f:num->real^N) k,l')` th)) THEN
  ASM_REWRITE_TAC[GSYM REAL_NOT_LT; DE_MORGAN_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
  ASM_REWRITE_TAC[DIST_EQ_0; NOT_LT; GSYM REAL_NOT_LE] THEN
  ASM_MESON_TAC[DIST_TRIANGLE_HALF_R; REAL_LT_REFL; REAL_LTE_TRANS]);;

let BOLZANO_WEIERSTRASS_IMP_CLOSED = prove
 (`!s:real^N->bool.
        (!t. INFINITE t /\ t SUBSET s ==> ?x. x IN s /\ x limit_point_of t)
        ==> closed s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSED_SEQUENTIAL_LIMITS] THEN
  MAP_EVERY X_GEN_TAC [`f:num->real^N`; `l:real^N`] THEN
  DISCH_TAC THEN
  MAP_EVERY (MP_TAC o ISPECL [`f:num->real^N`; `l:real^N`])
   [SEQUENCE_UNIQUE_LIMPT; SEQUENCE_INFINITE_LEMMA] THEN
  MATCH_MP_TAC(TAUT
   `(~d ==> a /\ ~(b /\ c)) ==> (a ==> b) ==> (a ==> c) ==> d`) THEN
  DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{y:real^N | ?n:num. y = f n}`) THEN
  ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM];
    ABBREV_TAC `t = {y:real^N | ?n:num. y = f n}`] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence express everything as an equivalence.                               *)
(* ------------------------------------------------------------------------- *)

let COMPACT_EQ_HEINE_BOREL = prove
 (`!s:real^N->bool.
        compact s <=>
           !f. (!t. t IN f ==> open t) /\ s SUBSET (UNIONS f)
               ==> ?f'. f' SUBSET f /\ FINITE f' /\ s SUBSET (UNIONS f')`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[COMPACT_IMP_HEINE_BOREL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HEINE_BOREL_IMP_BOLZANO_WEIERSTRASS) THEN
  DISCH_TAC THEN MATCH_MP_TAC BOUNDED_CLOSED_IMP_COMPACT THEN
  ASM_SIMP_TAC[BOLZANO_WEIERSTRASS_IMP_BOUNDED;
               BOLZANO_WEIERSTRASS_IMP_CLOSED]);;

let COMPACT_EQ_BOLZANO_WEIERSTRASS = prove
 (`!s:real^N->bool.
        compact s <=>
           !t. INFINITE t /\ t SUBSET s ==> ?x. x IN s /\ x limit_point_of t`,
  GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[COMPACT_EQ_HEINE_BOREL; HEINE_BOREL_IMP_BOLZANO_WEIERSTRASS];
    SIMP_TAC[BOLZANO_WEIERSTRASS_IMP_BOUNDED; BOLZANO_WEIERSTRASS_IMP_CLOSED;
             BOUNDED_CLOSED_IMP_COMPACT]]);;

let COMPACT_EQ_BOUNDED_CLOSED = prove
 (`!s:real^N->bool. compact s <=> bounded s /\ closed s`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[BOUNDED_CLOSED_IMP_COMPACT] THEN
  SIMP_TAC[COMPACT_EQ_BOLZANO_WEIERSTRASS; BOLZANO_WEIERSTRASS_IMP_BOUNDED;
           BOLZANO_WEIERSTRASS_IMP_CLOSED]);;

let COMPACT_IMP_BOUNDED = prove
 (`!s. compact s ==> bounded s`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED]);;

let COMPACT_IMP_CLOSED = prove
 (`!s. compact s ==> closed s`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* A version of Heine-Borel for subtopology.                                 *)
(* ------------------------------------------------------------------------- *)

let COMPACT_EQ_HEINE_BOREL_SUBTOPOLOGY = prove
 (`!s:real^N->bool.
        compact s <=>
        (!f. (!t. t IN f ==> open_in(subtopology euclidean s) t) /\
             s SUBSET UNIONS f
             ==> ?f'. f' SUBSET f /\ FINITE f' /\ s SUBSET UNIONS f')`,
  GEN_TAC THEN REWRITE_TAC[COMPACT_EQ_HEINE_BOREL] THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `f:(real^N->bool)->bool` THENL
   [REWRITE_TAC[OPEN_IN_OPEN] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `m:(real^N->bool)->(real^N->bool)`) ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
     `IMAGE (m:(real^N->bool)->(real^N->bool)) f`) THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (\t:real^N->bool. s INTER t) f'` THEN
    ASM_SIMP_TAC[FINITE_IMAGE; UNIONS_IMAGE; SUBSET; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_IMAGE]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{s INTER t:real^N->bool | t IN f}`) THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; OPEN_IN_OPEN; UNIONS_IMAGE] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
    REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE; UNIONS_IMAGE] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* More easy lemmas.                                                         *)
(* ------------------------------------------------------------------------- *)

let COMPACT_CLOSURE = prove
 (`!s. compact(closure s) <=> bounded s`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_CLOSURE; BOUNDED_CLOSURE_EQ]);;

let BOLZANO_WEIERSTRASS_CONTRAPOS = prove
 (`!s t:real^N->bool.
        compact s /\ t SUBSET s /\
        (!x. x IN s ==> ~(x limit_point_of t))
        ==> FINITE t`,
  REWRITE_TAC[COMPACT_EQ_BOLZANO_WEIERSTRASS; INFINITE] THEN MESON_TAC[]);;

let DISCRETE_BOUNDED_IMP_FINITE = prove
 (`!s:real^N->bool e.
        &0 < e /\
        (!x y. x IN s /\ y IN s /\ norm(y - x) < e ==> y = x) /\
        bounded s
        ==> FINITE s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact(s:real^N->bool)` MP_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
    ASM_MESON_TAC[DISCRETE_IMP_CLOSED];
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_HEINE_BOREL)] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\x:real^N. ball(x,e)) s`) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL; UNIONS_IMAGE; IN_ELIM_THM] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[CENTRE_IN_BALL];
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`]] THEN
  REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s:real^N->bool = t` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [UNIONS_IMAGE]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N` o GEN_REWRITE_RULE I [SUBSET]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; IN_BALL; dist] THEN ASM_MESON_TAC[SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* In particular, some common special cases.                                 *)
(* ------------------------------------------------------------------------- *)

let COMPACT_EMPTY = prove
 (`compact {}`,
  REWRITE_TAC[compact; NOT_IN_EMPTY]);;

let COMPACT_UNION = prove
 (`!s t. compact s /\ compact t ==> compact (s UNION t)`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_UNION; CLOSED_UNION]);;

let COMPACT_INTER = prove
 (`!s t. compact s /\ compact t ==> compact (s INTER t)`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_INTER; CLOSED_INTER]);;

let COMPACT_INTER_CLOSED = prove
 (`!s t. compact s /\ closed t ==> compact (s INTER t)`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_INTER] THEN
  MESON_TAC[BOUNDED_SUBSET; INTER_SUBSET]);;

let CLOSED_INTER_COMPACT = prove
 (`!s t. closed s /\ compact t ==> compact (s INTER t)`,
  MESON_TAC[COMPACT_INTER_CLOSED; INTER_COMM]);;

let FINITE_IMP_CLOSED = prove
 (`!s. FINITE s ==> closed s`,
  MESON_TAC[BOLZANO_WEIERSTRASS_IMP_CLOSED; INFINITE; FINITE_SUBSET]);;

let FINITE_IMP_COMPACT = prove
 (`!s. FINITE s ==> compact s`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; FINITE_IMP_CLOSED; FINITE_IMP_BOUNDED]);;

let COMPACT_SING = prove
 (`!a. compact {a}`,
  SIMP_TAC[FINITE_IMP_COMPACT; FINITE_RULES]);;

let CLOSED_SING = prove
 (`!a. closed {a}`,
  MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED; COMPACT_SING]);;

let COMPACT_CBALL = prove
 (`!x e. compact(cball(x,e))`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_CBALL; CLOSED_CBALL]);;

let COMPACT_FRONTIER_BOUNDED = prove
 (`!s. bounded s ==> compact(frontier s)`,
  SIMP_TAC[frontier; COMPACT_EQ_BOUNDED_CLOSED;
           CLOSED_DIFF; OPEN_INTERIOR; CLOSED_CLOSURE] THEN
  MESON_TAC[SUBSET_DIFF; BOUNDED_SUBSET; BOUNDED_CLOSURE]);;

let COMPACT_FRONTIER = prove
 (`!s. compact s ==> compact (frontier s)`,
  MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED; COMPACT_FRONTIER_BOUNDED]);;

let FRONTIER_SUBSET_COMPACT = prove
 (`!s. compact s ==> frontier s SUBSET s`,
  MESON_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_EQ_BOUNDED_CLOSED]);;

let OPEN_DELETE = prove
 (`!s x. open s ==> open(s DELETE x)`,
  let lemma = prove(`s DELETE x = s DIFF {x}`,SET_TAC[]) in
  SIMP_TAC[lemma; OPEN_DIFF; CLOSED_SING]);;

let CLOSED_INTERS_COMPACT = prove
 (`!s:real^N->bool.
        closed s <=> !e. compact(cball(vec 0,e) INTER s)`,
  GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_INTER; CLOSED_CBALL;
             BOUNDED_INTER; BOUNDED_CBALL];
    ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[CLOSED_LIMPT] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `norm(x:real^N) + &1`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_CLOSED) THEN
  REWRITE_TAC[CLOSED_LIMPT] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  REWRITE_TAC[IN_INTER] THEN ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[LIMPT_APPROACHABLE] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min e (&1 / &2)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `y:real^N` THEN SIMP_TAC[IN_INTER; IN_CBALL] THEN NORM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Finite intersection property. I could make it an equivalence in fact.     *)
(* ------------------------------------------------------------------------- *)

let COMPACT_IMP_FIP = prove
 (`!s:real^N->bool f.
        compact s /\
        (!t. t IN f ==> closed t) /\
        (!f'. FINITE f' /\ f' SUBSET f ==> ~(s INTER (INTERS f') = {}))
        ==> ~(s INTER (INTERS f) = {})`,
  let lemma = prove(`(s = UNIV DIFF t) <=> (UNIV DIFF s = t)`,SET_TAC[]) in
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\t:real^N->bool. UNIV DIFF t) f`) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN
  DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[OPEN_DIFF; CLOSED_DIFF; OPEN_UNIV; CLOSED_UNIV; NOT_IMP] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) INTER INTERS f = {}` THEN
    ONCE_REWRITE_TAC[SUBSET; EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` MP_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (\t:real^N->bool. UNIV DIFF t) g`) THEN
    ASM_CASES_TAC `FINITE(g:(real^N->bool)->bool)` THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN ONCE_REWRITE_TAC[SUBSET; EXTENSION] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; IN_INTERS; IN_IMAGE; IN_DIFF;
                IN_UNIV; NOT_IN_EMPTY; lemma; UNWIND_THM1; IN_UNIONS] THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Bounded closed nest property (proof does not use Heine-Borel).            *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_CLOSED_NEST = prove
 (`!s. (!n. closed(s n)) /\ (!n. ~(s n = {})) /\
       (!m n. m <= n ==> s(n) SUBSET s(m)) /\
       bounded(s 0)
       ==> ?a:real^N. !n:num. a IN s(n)`,
  GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; SKOLEM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `a:num->real^N`) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `compact(s 0:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[BOUNDED_CLOSED_IMP_COMPACT]; ALL_TAC] THEN
  REWRITE_TAC[compact] THEN
  DISCH_THEN(MP_TAC o SPEC `a:num->real^N`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET; LE_0]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^N` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~(~p)`] THEN
  GEN_REWRITE_TAC RAND_CONV [NOT_FORALL_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN
  MP_TAC(ISPECL [`l:real^N`; `(s:num->real^N->bool) N`]
                CLOSED_APPROACHABLE) THEN
  ASM_MESON_TAC[SUBSET; LE_REFL; LE_TRANS; LE_CASES; MONOTONE_BIGGER]);;

(* ------------------------------------------------------------------------- *)
(* Decreasing case does not even need compactness, just completeness.        *)
(* ------------------------------------------------------------------------- *)

let DECREASING_CLOSED_NEST = prove
 (`!s. (!n. closed(s n)) /\ (!n. ~(s n = {})) /\
       (!m n. m <= n ==> s(n) SUBSET s(m)) /\
       (!e. &0 < e ==> ?n. !x y. x IN s(n) /\ y IN s(n) ==> dist(x,y) < e)
       ==> ?a:real^N. !n:num. a IN s(n)`,
  GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; SKOLEM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `a:num->real^N`) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?l:real^N. (a --> l) sequentially` MP_TAC THENL
   [ASM_MESON_TAC[cauchy; GE; SUBSET; LE_TRANS; LE_REFL;
                  complete; COMPLETE_UNIV; IN_UNIV];
    ASM_MESON_TAC[LIM_SEQUENTIALLY; CLOSED_APPROACHABLE;
                  SUBSET; LE_REFL; LE_TRANS; LE_CASES]]);;

(* ------------------------------------------------------------------------- *)
(* Strengthen it to the intersection actually being a singleton.             *)
(* ------------------------------------------------------------------------- *)

let DECREASING_CLOSED_NEST_SING = prove
 (`!s. (!n. closed(s n)) /\ (!n. ~(s n = {})) /\
       (!m n. m <= n ==> s(n) SUBSET s(m)) /\
       (!e. &0 < e ==> ?n. !x y. x IN s(n) /\ y IN s(n) ==> dist(x,y) < e)
       ==> ?a:real^N. INTERS {t | ?n:num. t = s n} = {a}`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DECREASING_CLOSED_NEST) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  DISCH_TAC THEN REWRITE_TAC[EXTENSION; IN_INTERS; IN_SING; IN_ELIM_THM] THEN
  ASM_MESON_TAC[DIST_POS_LT; REAL_LT_REFL; SUBSET; LE_CASES]);;

(* ------------------------------------------------------------------------- *)
(* A version for a more general chain, not indexed by N.                     *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_CLOSED_CHAIN = prove
 (`!f b:real^N->bool.
        (!s. s IN f ==> closed s /\ ~(s = {})) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s) /\
         b IN f /\ bounded b
         ==> ~(INTERS f = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(b INTER (INTERS f):real^N->bool = {})` MP_TAC THENL
   [ALL_TAC; SET_TAC[]] THEN
  MATCH_MP_TAC COMPACT_IMP_FIP THEN
  ASM_SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
  X_GEN_TAC `u:(real^N->bool)->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN f /\ !t. t IN u ==> s SUBSET t`
  MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  UNDISCH_TAC `(u:(real^N->bool)->bool) SUBSET f` THEN
  UNDISCH_TAC `FINITE(u:(real^N->bool)->bool)` THEN
  SPEC_TAC(`u:(real^N->bool)->bool`,`u:(real^N->bool)->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:(real^N->bool)->bool`] THEN
  REWRITE_TAC[INSERT_SUBSET] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^N->bool`; `t:real^N->bool`]) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Separation properties: normal, Hausdorff and weaker ones.                 *)
(* ------------------------------------------------------------------------- *)

let SEPARATION_NORMAL = prove
 (`!s t:real^N->bool.
        closed s /\ closed t /\ s INTER t = {}
        ==> ?u v. open u /\ open v /\
                  s SUBSET u /\ t SUBSET v /\ u INTER v = {}`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC
    `UNIONS { ball(x:real^N,d) | x IN s /\ ball(x,&2 * d) INTER t = {}}` THEN
  EXISTS_TAC
    `UNIONS { ball(y:real^N,e) | y IN t /\ ball(y,&2 * e) INTER s = {}}` THEN
  SIMP_TAC[OPEN_UNIONS; FORALL_IN_GSPEC; OPEN_BALL] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `open((:real^N) DIFF t)` MP_TAC THENL
     [ASM_REWRITE_TAC[GSYM CLOSED_OPEN]; ALL_TAC];
    SUBGOAL_THEN `open((:real^N) DIFF s)` MP_TAC THENL
     [ASM_REWRITE_TAC[GSYM CLOSED_OPEN]; ALL_TAC];
    REWRITE_TAC[SET_RULE `s INTER t = {} <=> !x. x IN s ==> ~(x IN t)`] THEN
    REWRITE_TAC[FORALL_IN_UNIONS; FORALL_IN_GSPEC; IMP_CONJ;
                RIGHT_FORALL_IMP_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN X_GEN_TAC `d:real` THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[FORALL_IN_UNIONS; FORALL_IN_GSPEC; IMP_CONJ;
                RIGHT_FORALL_IMP_THM] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[IN_BALL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[IN_BALL] THEN NORM_ARITH_TAC] THEN
  REWRITE_TAC[SUBSET; OPEN_CONTAINS_BALL] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  (ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  ONCE_REWRITE_TAC[EXTENSION] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  EXISTS_TAC `ball(x:real^N,e / &2)` THEN
  ASM_SIMP_TAC[CENTRE_IN_BALL; REAL_HALF] THEN
  MAP_EVERY EXISTS_TAC [`x:real^N`; `e / &2`] THEN
  REWRITE_TAC[REAL_ARITH `&2 * x / &2 = x`] THEN ASM SET_TAC[]);;

let SEPARATION_HAUSDORFF = prove
 (`!x:real^N y.
      ~(x = y)
      ==> ?u v. open u /\ open v /\ x IN u /\ y IN v /\ (u INTER v = {})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`{x:real^N}`; `{y:real^N}`] SEPARATION_NORMAL) THEN
  REWRITE_TAC[SING_SUBSET; CLOSED_SING] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]);;

let SEPARATION_T2 = prove
 (`!x:real^N y.
        ~(x = y) <=> ?u v. open u /\ open v /\ x IN u /\ y IN v /\
                           (u INTER v = {})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[SEPARATION_HAUSDORFF] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let SEPARATION_T1 = prove
 (`!x:real^N y.
        ~(x = y) <=> ?u v. open u /\ open v /\ x IN u /\ ~(y IN u) /\
                           ~(x IN v) /\ y IN v`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_SIMP_TAC[SEPARATION_T2; EXTENSION; NOT_IN_EMPTY; IN_INTER];
    ALL_TAC] THEN MESON_TAC[]);;

let SEPARATION_T0 = prove
 (`!x:real^N y. ~(x = y) <=> ?u. open u /\ ~(x IN u <=> y IN u)`,
  MESON_TAC[SEPARATION_T1]);;

(* ------------------------------------------------------------------------- *)
(* Cauchy-type criteria for *uniform* convergence.                           *)
(* ------------------------------------------------------------------------- *)

let UNIFORMLY_CONVERGENT_EQ_CAUCHY = prove
 (`!P s:num->A->real^N.
         (?l. !e. &0 < e
                  ==> ?N. !n x. N <= n /\ P x ==> dist(s n x,l x) < e) <=>
         (!e. &0 < e
              ==> ?N. !m n x. N <= m /\ N <= n /\ P x
                              ==> dist(s m x,s n x) < e)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `l:A->real^N`) THEN X_GEN_TAC `e:real` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN MESON_TAC[DIST_TRIANGLE_HALF_L];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!x:A. P x ==> cauchy (\n. s n x :real^N)` MP_TAC THENL
   [REWRITE_TAC[cauchy; GE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM CONVERGENT_EQ_CAUCHY; LIM_SEQUENTIALLY] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `l:A->real^N` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `N + M:num`; `x:A`]) THEN
  ASM_REWRITE_TAC[LE_ADD] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `M + N:num`) THEN REWRITE_TAC[LE_ADD] THEN
  ASM_MESON_TAC[DIST_TRIANGLE_HALF_L; DIST_SYM]);;

let UNIFORMLY_CAUCHY_IMP_UNIFORMLY_CONVERGENT = prove
 (`!P (s:num->A->real^N) l.
    (!e. &0 < e
         ==> ?N. !m n x. N <= m /\ N <= n /\ P x ==> dist(s m x,s n x) < e) /\
    (!x. P x ==> !e. &0 < e ==> ?N. !n. N <= n ==> dist(s n x,l x) < e)
    ==> (!e. &0 < e ==> ?N. !n x. N <= n /\ P x ==> dist(s n x,l x) < e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM UNIFORMLY_CONVERGENT_EQ_CAUCHY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `l':A->real^N`) ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. P x ==> (l:A->real^N) x = l' x` MP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `\n. (s:num->A->real^N) n x` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Define continuity over a net to take in restrictions of the set.          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("continuous",(12,"right"));;

let continuous = new_definition
  `f continuous net <=> (f --> f(netlimit net)) net`;;

let CONTINUOUS_TRIVIAL_LIMIT = prove
 (`!f net. trivial_limit net ==> f continuous net`,
  SIMP_TAC[continuous; LIM]);;

let CONTINUOUS_WITHIN = prove
 (`!f x:real^M. f continuous (at x within s) <=> (f --> f(x)) (at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous] THEN
  ASM_CASES_TAC `trivial_limit(at (x:real^M) within s)` THENL
   [ASM_REWRITE_TAC[LIM]; ASM_SIMP_TAC[NETLIMIT_WITHIN]]);;

let CONTINUOUS_AT = prove
 (`!f (x:real^N). f continuous (at x) <=> (f --> f(x)) (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[CONTINUOUS_WITHIN; IN_UNIV]);;

let CONTINUOUS_AT_WITHIN = prove
 (`!f:real^M->real^N x s.
        f continuous (at x) ==> f continuous (at x within s)`,
  SIMP_TAC[LIM_AT_WITHIN; CONTINUOUS_AT; CONTINUOUS_WITHIN]);;

let CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL = prove
 (`!a s. closed s /\ ~(a IN s) ==> f continuous (at a within s)`,
  ASM_SIMP_TAC[continuous; LIM; LIM_WITHIN_CLOSED_TRIVIAL]);;

(* ------------------------------------------------------------------------- *)
(* Derive the epsilon-delta forms, which we often use as "definitions"       *)
(* ------------------------------------------------------------------------- *)

let continuous_within = prove
 (`f continuous (at x within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x'. x' IN s /\ dist(x',x) < d ==> dist(f(x'),f(x)) < e`,
  REWRITE_TAC[CONTINUOUS_WITHIN; LIM_WITHIN] THEN
  REWRITE_TAC[GSYM DIST_NZ] THEN MESON_TAC[DIST_REFL]);;

let continuous_at = prove
 (`f continuous (at x) <=>
        !e. &0 < e ==> ?d. &0 < d /\
                           !x'. dist(x',x) < d ==> dist(f(x'),f(x)) < e`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[continuous_within; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Versions in terms of open balls.                                          *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_BALL = prove
 (`!f s x. f continuous (at x within s) <=>
                !e. &0 < e
                    ==> ?d. &0 < d /\
                            IMAGE f (ball(x,d) INTER s) SUBSET ball(f x,e)`,
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL; continuous_within; IN_INTER] THEN
  MESON_TAC[DIST_SYM]);;

let CONTINUOUS_AT_BALL = prove
 (`!f x. f continuous (at x) <=>
                !e. &0 < e
                    ==> ?d. &0 < d /\
                            IMAGE f (ball(x,d)) SUBSET ball(f x,e)`,
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL; continuous_at] THEN
  MESON_TAC[DIST_SYM]);;

(* ------------------------------------------------------------------------- *)
(* For setwise continuity, just start from the epsilon-delta definitions.    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("continuous_on",(12,"right"));;
parse_as_infix ("uniformly_continuous_on",(12,"right"));;

let continuous_on = new_definition
  `f continuous_on s <=>
        !x. x IN s ==> !e. &0 < e
                           ==> ?d. &0 < d /\
                                   !x'. x' IN s /\ dist(x',x) < d
                                        ==> dist(f(x'),f(x)) < e`;;

let uniformly_continuous_on = new_definition
  `f uniformly_continuous_on s <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x x'. x IN s /\ x' IN s /\ dist(x',x) < d
                           ==> dist(f(x'),f(x)) < e`;;

(* ------------------------------------------------------------------------- *)
(* Some simple consequential lemmas.                                         *)
(* ------------------------------------------------------------------------- *)

let UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS = prove
 (`!f s. f uniformly_continuous_on s ==> f continuous_on s`,
  REWRITE_TAC[uniformly_continuous_on; continuous_on] THEN MESON_TAC[]);;

let CONTINUOUS_AT_IMP_CONTINUOUS_ON = prove
 (`!f s. (!x. x IN s ==> f continuous (at x)) ==> f continuous_on s`,
  REWRITE_TAC[continuous_at; continuous_on] THEN MESON_TAC[]);;

let CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN = prove
 (`!f s. f continuous_on s <=> !x. x IN s ==> f continuous (at x within s)`,
  REWRITE_TAC[continuous_on; continuous_within]);;

let CONTINUOUS_ON = prove
 (`!f (s:real^N->bool).
        f continuous_on s <=> !x. x IN s ==> (f --> f(x)) (at x within s)`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_WITHIN]);;

let CONTINUOUS_ON_EQ_CONTINUOUS_AT = prove
 (`!f:real^M->real^N s.
      open s ==> (f continuous_on s <=> (!x. x IN s ==> f continuous (at x)))`,
  SIMP_TAC[CONTINUOUS_ON; CONTINUOUS_AT; LIM_WITHIN_OPEN]);;

let CONTINUOUS_WITHIN_SUBSET = prove
 (`!f s t x. f continuous (at x within s) /\ t SUBSET s
             ==> f continuous (at x within t)`,
   REWRITE_TAC[CONTINUOUS_WITHIN] THEN MESON_TAC[LIM_WITHIN_SUBSET]);;

let CONTINUOUS_ON_SUBSET = prove
 (`!f s t. f continuous_on s /\ t SUBSET s ==> f continuous_on t`,
  REWRITE_TAC[CONTINUOUS_ON] THEN MESON_TAC[SUBSET; LIM_WITHIN_SUBSET]);;

let UNIFORMLY_CONTINUOUS_ON_SUBSET = prove
 (`!f s t. f uniformly_continuous_on s /\ t SUBSET s
           ==> f uniformly_continuous_on t`,
  REWRITE_TAC[uniformly_continuous_on] THEN
  MESON_TAC[SUBSET; LIM_WITHIN_SUBSET]);;

let CONTINUOUS_ON_INTERIOR = prove
 (`!f:real^M->real^N s x.
        f continuous_on s /\ x IN interior(s) ==> f continuous at x`,
  REWRITE_TAC[interior; IN_ELIM_THM] THEN
  MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; CONTINUOUS_ON_SUBSET]);;

let CONTINUOUS_ON_EQ = prove
 (`!f g s. (!x. x IN s ==> f(x) = g(x)) /\ f continuous_on s
           ==> g continuous_on s`,
  REWRITE_TAC[continuous_on] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Characterization of various kinds of continuity in terms of sequences.    *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_SEQUENTIALLY = prove
 (`!f a:real^N.
        f continuous (at a within s) <=>
                !x. (!n. x(n) IN s) /\ (x --> a) sequentially
                     ==> ((f o x) --> f(a)) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_within] THEN EQ_TAC THENL
   [REWRITE_TAC[LIM_SEQUENTIALLY; o_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&1 / (&n + &1)`) THEN
  SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; REAL_OF_NUM_LE; REAL_POS; ARITH;
       REAL_ARITH `&0 <= n ==> &0 < n + &1`; NOT_FORALL_THM; SKOLEM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[NOT_IMP; FORALL_AND_THM] THEN
  X_GEN_TAC `y:num->real^N` THEN REWRITE_TAC[LIM_SEQUENTIALLY; o_THM] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[LE_REFL]] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FORALL_POS_MONO_1 THEN
  CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_TRANS]; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `&1 / (&m + &1)` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_INV2; real_div; REAL_ARITH `&0 <= x ==> &0 < x + &1`;
               REAL_POS; REAL_MUL_LID; REAL_LE_RADD; REAL_OF_NUM_LE]);;

let CONTINUOUS_AT_SEQUENTIALLY = prove
 (`!f a:real^N.
        f continuous (at a) <=>
              !x. (x --> a) sequentially
                  ==> ((f o x) --> f(a)) sequentially`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[CONTINUOUS_WITHIN_SEQUENTIALLY; IN_UNIV]);;

let CONTINUOUS_ON_SEQUENTIALLY = prove
 (`!f s:real^N->bool.
        f continuous_on s <=>
              !x a. a IN s /\ (!n. x(n) IN s) /\ (x --> a) sequentially
                    ==> ((f o x) --> f(a)) sequentially`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              CONTINUOUS_WITHIN_SEQUENTIALLY] THEN MESON_TAC[]);;

let UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY = prove
 (`!f s:real^N->bool.
        f uniformly_continuous_on s <=>
              !x y. (!n. x(n) IN s) /\ (!n. y(n) IN s) /\
                    ((\n. x(n) - y(n)) --> vec 0) sequentially
                    ==> ((\n. f(x(n)) - f(y(n))) --> vec 0) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[uniformly_continuous_on] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; dist; VECTOR_SUB_RZERO] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&1 / (&n + &1)`) THEN
  SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; REAL_OF_NUM_LE; REAL_POS; ARITH;
       REAL_ARITH `&0 <= n ==> &0 < n + &1`; NOT_FORALL_THM; SKOLEM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:num->real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:num->real^N` THEN
  REWRITE_TAC[NOT_IMP; FORALL_AND_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FORALL_POS_MONO_1 THEN
    CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_TRANS]; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&1 / (&m + &1)` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_INV2; real_div; REAL_ARITH `&0 <= x ==> &0 < x + &1`;
                 REAL_POS; REAL_MUL_LID; REAL_LE_RADD; REAL_OF_NUM_LE];
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `\x:num. x` THEN ASM_REWRITE_TAC[LE_REFL]]);;

let LIM_CONTINUOUS_FUNCTION = prove
 (`!f net g l.
        f continuous (at l) /\ (g --> l) net ==> ((\x. f(g x)) --> f l) net`,
  REWRITE_TAC[tendsto; continuous_at; eventually] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The usual transformation theorems.                                        *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_TRANSFORM_WITHIN = prove
 (`!f:real^M->real^N g x s d.
        &0 < d /\ x IN s /\
        (!x'. x' IN s /\ dist(x',x) < d ==> f(x') = g(x')) /\
        f continuous (at x within s)
        ==> g continuous (at x within s)`,
  REWRITE_TAC[CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LIM_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `d:real`] THEN
  ASM_MESON_TAC[DIST_REFL]);;

let CONTINUOUS_TRANSFORM_AT = prove
 (`!f:real^M->real^N g x s d.
        &0 < d /\
        (!x'. dist(x',x) < d ==> f(x') = g(x')) /\
        f continuous at x
        ==> g continuous at x`,
  REWRITE_TAC[CONTINUOUS_AT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LIM_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `d:real`] THEN
  ASM_MESON_TAC[DIST_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Combination results for pointwise continuity.                             *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_CONST = prove
 (`!net c. (\x. c) continuous net`,
  REWRITE_TAC[continuous; LIM_CONST]);;

let CONTINUOUS_CMUL = prove
 (`!f c net. f continuous net ==> (\x. c % f(x)) continuous net`,
  REWRITE_TAC[continuous; LIM_CMUL]);;

let CONTINUOUS_NEG = prove
 (`!f net. f continuous net ==> (\x. --(f x)) continuous net`,
  REWRITE_TAC[continuous; LIM_NEG]);;

let CONTINUOUS_ADD = prove
 (`!f g net. f continuous net /\ g continuous net
           ==> (\x. f(x) + g(x)) continuous net`,
  REWRITE_TAC[continuous; LIM_ADD]);;

let CONTINUOUS_SUB = prove
 (`!f g net. f continuous net /\ g continuous net
           ==> (\x. f(x) - g(x)) continuous net`,
  REWRITE_TAC[continuous; LIM_SUB]);;

let CONTINUOUS_ABS = prove
 (`!(f:A->real^N) net.
        f continuous net
        ==> (\x. (lambda i. abs(f(x)$i)):real^N) continuous net`,
  REWRITE_TAC[continuous; LIM_ABS]);;

let CONTINUOUS_MAX = prove
 (`!(f:A->real^N) (g:A->real^N) net.
        f continuous net /\ g continuous net
        ==> (\x. (lambda i. max (f(x)$i) (g(x)$i)):real^N) continuous net`,
  REWRITE_TAC[continuous; LIM_MAX]);;

let CONTINUOUS_MIN = prove
 (`!(f:A->real^N) (g:A->real^N) net.
        f continuous net /\ g continuous net
        ==> (\x. (lambda i. min (f(x)$i) (g(x)$i)):real^N) continuous net`,
  REWRITE_TAC[continuous; LIM_MIN]);;

let CONTINUOUS_VSUM = prove
 (`!net f s. FINITE s /\ (!a. a IN s ==> (f a) continuous net)
             ==> (\x. vsum s (\a. f a x)) continuous net`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; VSUM_CLAUSES;
           CONTINUOUS_CONST; CONTINUOUS_ADD; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Same thing for setwise continuity.                                        *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_CONST = prove
 (`!s c. (\x. c) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_CONST]);;

let CONTINUOUS_ON_CMUL = prove
 (`!f c s. f continuous_on s ==> (\x. c % f(x)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_CMUL]);;

let CONTINUOUS_ON_NEG = prove
 (`!f s. f continuous_on s
         ==> (\x. --(f x)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_NEG]);;

let CONTINUOUS_ON_ADD = prove
 (`!f g s. f continuous_on s /\ g continuous_on s
           ==> (\x. f(x) + g(x)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_ADD]);;

let CONTINUOUS_ON_SUB = prove
 (`!f g s. f continuous_on s /\ g continuous_on s
           ==> (\x. f(x) - g(x)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_SUB]);;

let CONTINUOUS_ON_ABS = prove
 (`!f:real^M->real^N s.
        f continuous_on s
        ==> (\x. (lambda i. abs(f(x)$i)):real^N) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_ABS]);;

let CONTINUOUS_ON_MAX = prove
 (`!f:real^M->real^N g:real^M->real^N s.
        f continuous_on s /\ g continuous_on s
        ==> (\x. (lambda i. max (f(x)$i) (g(x)$i)):real^N)
            continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_MAX]);;

let CONTINUOUS_ON_MIN = prove
 (`!f:real^M->real^N g:real^M->real^N s.
        f continuous_on s /\ g continuous_on s
        ==> (\x. (lambda i. min (f(x)$i) (g(x)$i)):real^N)
            continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_MIN]);;

let CONTINUOUS_ON_VSUM = prove
 (`!t f s. FINITE s /\ (!a. a IN s ==> (f a) continuous_on t)
             ==> (\x. vsum s (\a. f a x)) continuous_on t`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_VSUM]);;

(* ------------------------------------------------------------------------- *)
(* Same thing for uniform continuity, using sequential formulations.         *)
(* ------------------------------------------------------------------------- *)

let UNIFORMLY_CONTINUOUS_ON_CONST = prove
 (`!s c. (\x. c) uniformly_continuous_on s`,
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY; o_DEF;
              VECTOR_SUB_REFL; LIM_CONST]);;

let UNIFORMLY_CONTINUOUS_ON_CMUL = prove
 (`!f c s. f uniformly_continuous_on s
           ==> (\x. c % f(x)) uniformly_continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_CMUL) THEN
  ASM_SIMP_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_RZERO]);;

let UNIFORMLY_CONTINUOUS_ON_NEG = prove
 (`!f s. f uniformly_continuous_on s
         ==> (\x. --(f x)) uniformly_continuous_on s`,
  ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_CMUL]);;

let UNIFORMLY_CONTINUOUS_ON_ADD = prove
 (`!f g s. f uniformly_continuous_on s /\ g uniformly_continuous_on s
           ==> (\x. f(x) + g(x)) uniformly_continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN(MP_TAC o MATCH_MP LIM_ADD) THEN
  MATCH_MP_TAC EQ_IMP THEN
  REWRITE_TAC[VECTOR_ADD_LID] THEN AP_THM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC);;

let UNIFORMLY_CONTINUOUS_ON_SUB = prove
 (`!f g s. f uniformly_continuous_on s /\ g uniformly_continuous_on s
           ==> (\x. f(x) - g(x)) uniformly_continuous_on s`,
  REWRITE_TAC[VECTOR_SUB] THEN
  SIMP_TAC[UNIFORMLY_CONTINUOUS_ON_NEG; UNIFORMLY_CONTINUOUS_ON_ADD]);;

let UNIFORMLY_CONTINUOUS_ON_VSUM = prove
 (`!t f s. FINITE s /\ (!a. a IN s ==> (f a) uniformly_continuous_on t)
             ==> (\x. vsum s (\a. f a x)) uniformly_continuous_on t`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; VSUM_CLAUSES;
       UNIFORMLY_CONTINUOUS_ON_CONST; UNIFORMLY_CONTINUOUS_ON_ADD; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Identity function is continuous in every sense.                           *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_ID = prove
 (`!net a s. (\x. x) continuous (at a within s)`,
  REWRITE_TAC[continuous_within] THEN MESON_TAC[]);;

let CONTINUOUS_AT_ID = prove
 (`!net s. (\x. x) continuous (at a)`,
  REWRITE_TAC[continuous_at] THEN MESON_TAC[]);;

let CONTINUOUS_ON_ID = prove
 (`!s. (\x. x) continuous_on s`,
  REWRITE_TAC[continuous_on] THEN MESON_TAC[]);;

let UNIFORMLY_CONTINUOUS_ON_ID = prove
 (`!s. (\x. x) uniformly_continuous_on s`,
  REWRITE_TAC[uniformly_continuous_on] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of all kinds is preserved under composition.                   *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_COMPOSE = prove
 (`!f g x s. f continuous (at x within s) /\
             g continuous (at (f x) within IMAGE f s)
             ==> (g o f) continuous (at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_within; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let CONTINUOUS_AT_COMPOSE = prove
 (`!f g x. f continuous (at x) /\ g continuous (at (f x))
           ==> (g o f) continuous (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  MESON_TAC[CONTINUOUS_WITHIN_COMPOSE; IN_IMAGE; CONTINUOUS_WITHIN_SUBSET;
            SUBSET_UNIV; IN_UNIV]);;

let CONTINUOUS_ON_COMPOSE = prove
 (`!f g s. f continuous_on s /\ g continuous_on (IMAGE f s)
           ==> (g o f) continuous_on s`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  MESON_TAC[IN_IMAGE; CONTINUOUS_WITHIN_COMPOSE]);;

let UNIFORMLY_CONTINUOUS_ON_COMPOSE = prove
 (`!f g s. f uniformly_continuous_on s /\
           g uniformly_continuous_on (IMAGE f s)
           ==> (g o f) uniformly_continuous_on s`,
  let lemma = prove
   (`(!y. ((?x. (y = f x) /\ P x) /\ Q y ==> R y)) <=>
     (!x. P x /\ Q (f x) ==> R (f x))`,
    MESON_TAC[]) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[uniformly_continuous_on; o_THM; IN_IMAGE] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN REWRITE_TAC[lemma] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN REWRITE_TAC[lemma] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `e:real` THEN ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Continuity in terms of open preimages.                                    *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_AT_OPEN = prove
 (`!f:real^M->real^N x.
     f continuous (at x) <=>
        !t. open t /\ f(x) IN t
            ==> ?s. open s /\ x IN s /\
                    !x'. x' IN s ==> f(x') IN t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_at] THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `t:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [open_def] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^M->real^N) x`) THEN
    ASM_MESON_TAC[IN_BALL; DIST_SYM; OPEN_BALL; CENTRE_IN_BALL];
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ball((f:real^M->real^N) x,e)`) THEN
    ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    MESON_TAC[open_def; IN_BALL; REAL_LT_TRANS; DIST_SYM]]);;

let CONTINUOUS_ON_OPEN = prove
 (`!f:real^M->real^N s.
      f continuous_on s <=>
        !t. open_in (subtopology euclidean (IMAGE f s)) t
            ==> open_in (subtopology euclidean s) {x | x IN s /\ f(x) IN t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_on] THEN EQ_TAC THENL
   [REWRITE_TAC[open_in; SUBSET; IN_ELIM_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[DIST_REFL]; ALL_TAC] THEN
    X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(f:real^M->real^N) x`) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    DISCH_TAC THEN X_GEN_TAC `x:real^M` THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o
      SPEC `ball((f:real^M->real^N) x,e) INTER (IMAGE f s)`) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_OPEN; INTER_COMM; OPEN_BALL]; ALL_TAC] THEN
    REWRITE_TAC[open_in; SUBSET; IN_INTER; IN_ELIM_THM; IN_BALL; IN_IMAGE] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
    ASM_MESON_TAC[DIST_REFL; DIST_SYM]]);;

(* ------------------------------------------------------------------------- *)
(* Similarly in terms of closed sets.                                        *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_CLOSED = prove
 (`!f:real^M->real^N s.
      f continuous_on s <=>
        !t. closed_in (subtopology euclidean (IMAGE f s)) t
            ==> closed_in (subtopology euclidean s) {x | x IN s /\ f(x) IN t}`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONTINUOUS_ON_OPEN] THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `t:real^N->bool` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (f:real^M->real^N) s DIFF t`) THENL
   [REWRITE_TAC[closed_in]; REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ]] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[SUBSET_RESTRICT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Half-global and completely global cases.                                  *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_OPEN_IN_PREIMAGE = prove
 (`!f s t.
         f continuous_on s /\ open t
         ==> open_in (subtopology euclidean s) {x | x IN s /\ f x IN t}`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SET_RULE
   `x IN s /\ f x IN t <=> x IN s /\ f x IN (t INTER IMAGE f s)`] THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CONTINUOUS_ON_OPEN]) THEN
  ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
  ASM_REWRITE_TAC[]);;

let CONTINUOUS_CLOSED_IN_PREIMAGE = prove
 (`!f s t.
         f continuous_on s /\ closed t
         ==> closed_in (subtopology euclidean s) {x | x IN s /\ f x IN t}`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SET_RULE
   `x IN s /\ f x IN t <=> x IN s /\ f x IN (t INTER IMAGE f s)`] THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CONTINUOUS_ON_CLOSED]) THEN
  ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN
  ASM_REWRITE_TAC[]);;

let CONTINUOUS_OPEN_PREIMAGE = prove
 (`!f:real^M->real^N s t.
     f continuous_on s /\ open s /\ open t
     ==> open {x | x IN s /\ f(x) IN t}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_ON_OPEN]) THEN
  REWRITE_TAC [OPEN_IN_OPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (f:real^M->real^N) s INTER t`) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    SUBGOAL_THEN `{x | x IN s /\ (f:real^M->real^N) x IN t} =
                 s INTER t'` SUBST1_TAC THENL
    [ASM SET_TAC []; ASM_MESON_TAC [OPEN_INTER]]]);;

let CONTINUOUS_CLOSED_PREIMAGE = prove
 (`!f:real^M->real^N s t.
     f continuous_on s /\ closed s /\ closed t
     ==> closed {x | x IN s /\ f(x) IN t}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_ON_CLOSED]) THEN
  REWRITE_TAC [CLOSED_IN_CLOSED] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (f:real^M->real^N) s INTER t`) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    SUBGOAL_THEN `{x | x IN s /\ (f:real^M->real^N) x IN t} =
                 s INTER t'` SUBST1_TAC THENL
    [ASM SET_TAC []; ASM_MESON_TAC [CLOSED_INTER]]]);;

let CONTINUOUS_OPEN_PREIMAGE_UNIV = prove
 (`!f:real^M->real^N s.
        (!x. f continuous (at x)) /\ open s ==> open {x | f(x) IN s}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:real^M->real^N`; `(:real^M)`; `s:real^N->bool`]
    CONTINUOUS_OPEN_PREIMAGE) THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; CONTINUOUS_AT_IMP_CONTINUOUS_ON]);;

let CONTINUOUS_CLOSED_PREIMAGE_UNIV = prove
 (`!f:real^M->real^N s.
        (!x. f continuous (at x)) /\ closed s ==> closed {x | f(x) IN s}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:real^M->real^N`; `(:real^M)`; `s:real^N->bool`]
    CONTINUOUS_CLOSED_PREIMAGE) THEN
  ASM_SIMP_TAC[CLOSED_UNIV; IN_UNIV; CONTINUOUS_AT_IMP_CONTINUOUS_ON]);;

(* ------------------------------------------------------------------------- *)
(* Equality of continuous functions on closure and related results.          *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT = prove
 (`!f:real^M->real^N s a.
        f continuous_on s
        ==> closed_in (subtopology euclidean s) {x | x IN s /\ f x = a}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{x | x IN s /\ f(x) = a} = {x | x IN s /\ f(x) IN {a}}`] THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
  ASM_REWRITE_TAC[CLOSED_SING]);;

let CONTINUOUS_CLOSED_PREIMAGE_CONSTANT = prove
 (`!f:real^M->real^N s.
      f continuous_on s /\ closed s ==> closed {x | x IN s /\ f(x) = a}`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `{x | x IN s /\ (f:real^M->real^N)(x) = a} = {}` THEN
  ASM_REWRITE_TAC[CLOSED_EMPTY] THEN ONCE_REWRITE_TAC[SET_RULE
   `{x | x IN s /\ f(x) = a} = {x | x IN s /\ f(x) IN {a}}`] THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
  ASM_REWRITE_TAC[CLOSED_SING] THEN ASM SET_TAC[]);;

let CONTINUOUS_CONSTANT_ON_CLOSURE = prove
 (`!f:real^M->real^N s a.
        f continuous_on closure(s) /\ (!x. x IN s ==> f(x) = a)
        ==> !x. x IN closure(s) ==> f(x) = a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `closure s SUBSET {x | x IN closure s /\ (f:real^M->real^N)(x) = a}`
  MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[CLOSURE_SUBSET; SUBSET];
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_CONSTANT THEN
    ASM_REWRITE_TAC[CLOSED_CLOSURE]]);;

(* ------------------------------------------------------------------------- *)
(* Topological properties of linear functions.                               *)
(* ------------------------------------------------------------------------- *)

let LINEAR_LIM_0 = prove
 (`!f. linear f ==> (f --> vec 0) (at (vec 0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIM_AT] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LINEAR_BOUNDED_POS) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `e / B` THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN REWRITE_TAC[dist; VECTOR_SUB_RZERO] THEN
  ASM_MESON_TAC[REAL_MUL_SYM; REAL_LET_TRANS; REAL_LT_RDIV_EQ]);;

let LINEAR_CONTINUOUS_AT = prove
 (`!f:real^M->real^N a. linear f ==> f continuous (at a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\x. (f:real^M->real^N) (a + x) - f(a)` LINEAR_LIM_0) THEN
  ANTS_TAC THENL
   [POP_ASSUM MP_TAC THEN SIMP_TAC[linear] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM LIM_NULL; CONTINUOUS_AT] THEN
  GEN_REWRITE_TAC RAND_CONV [LIM_AT_ZERO] THEN SIMP_TAC[]);;

let LINEAR_CONTINUOUS_WITHIN = prove
 (`!f:real^M->real^N s a. linear f ==> f continuous (at x within s)`,
  SIMP_TAC[CONTINUOUS_AT_WITHIN; LINEAR_CONTINUOUS_AT]);;

let LINEAR_CONTINUOUS_ON = prove
 (`!f:real^M->real^N s. linear f ==> f continuous_on s`,
  MESON_TAC[LINEAR_CONTINUOUS_AT; CONTINUOUS_AT_IMP_CONTINUOUS_ON]);;

(* ------------------------------------------------------------------------- *)
(* Also bilinear functions, in composition form.                             *)
(* ------------------------------------------------------------------------- *)

let BILINEAR_CONTINUOUS_AT_COMPOSE = prove
 (`!f g h x.
        f continuous (at x) /\ g continuous (at x) /\ bilinear h
        ==> (\x. h (f x) (g x)) continuous (at x)`,
  REWRITE_TAC[CONTINUOUS_AT; LIM_BILINEAR]);;

let BILINEAR_CONTINUOUS_WITHIN_COMPOSE = prove
 (`!f g h a s.
        f continuous (at x within s) /\
        g continuous (at x within s) /\
        bilinear h
        ==> (\x. h (f x) (g x)) continuous (at x within s)`,
  REWRITE_TAC[CONTINUOUS_WITHIN; LIM_BILINEAR]);;

let BILINEAR_CONTINUOUS_ON_COMPOSE = prove
 (`!f g h s. f continuous_on s /\ g continuous_on s /\ bilinear h
             ==> (\x. h (f x) (g x)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
           BILINEAR_CONTINUOUS_WITHIN_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Occasionally useful invariance properties.                                *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_AT_COMPOSE_EQ = prove
 (`!f:real^M->real^N g:real^M->real^M h:real^M->real^M.
        g continuous at x /\ h continuous at (g x) /\
        (!y. g(h y) = y) /\ h(g x) = x
        ==> (f continuous at (g x) <=> (\x. f(g x)) continuous at x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_AT_COMPOSE] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `((f:real^M->real^N) o (g:real^M->real^M) o (h:real^M->real^M))
     continuous at (g(x:real^M))`
  MP_TAC THENL
   [REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    ASM_REWRITE_TAC[o_DEF];

    ASM_REWRITE_TAC[o_DEF; ETA_AX]]);;

let CONTINUOUS_AT_TRANSLATION = prove
 (`!a z f:real^M->real^N.
      f continuous at (a + z) <=> (\x. f(a + x)) continuous at z`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE_EQ THEN
  EXISTS_TAC `\x:real^M. x - a` THEN
  SIMP_TAC[CONTINUOUS_ADD; CONTINUOUS_SUB;
           CONTINUOUS_AT_ID; CONTINUOUS_CONST] THEN
  VECTOR_ARITH_TAC);;

add_translation_invariants [CONTINUOUS_AT_TRANSLATION];;

let CONTINUOUS_AT_LINEAR_IMAGE = prove
 (`!h:real^M->real^M z f:real^M->real^N.
        linear h /\ (!x. norm(h x) = norm x)
        ==> (f continuous at (h z) <=> (\x. f(h x)) continuous at z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I
   [GSYM ORTHOGONAL_TRANSFORMATION]) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `g:real^M->real^M` o MATCH_MP
    ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE_EQ THEN
  EXISTS_TAC `g:real^M->real^M` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ORTHOGONAL_TRANSFORMATION]) THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT]);;

add_linear_invariants [CONTINUOUS_AT_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Interior of an injective image.                                           *)
(* ------------------------------------------------------------------------- *)

let INTERIOR_IMAGE_SUBSET = prove
 (`!f:real^M->real^N s.
       (!x. f continuous at x) /\ (!x y. f x = f y ==> x = y)
       ==> interior(IMAGE f s) SUBSET IMAGE f (interior s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN
  REWRITE_TAC[interior; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  SUBGOAL_THEN `y IN IMAGE (f:real^M->real^N) s` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  EXISTS_TAC `{x | (f:real^M->real^N)(x) IN t}` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_MESON_TAC[];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Making a continuous function avoid some value in a neighbourhood.         *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_AVOID = prove
 (`!f:real^M->real^N x s a.
        f continuous (at x within s) /\ x IN s /\  ~(f x = a)
        ==> ?e. &0 < e /\ !y. y IN s /\ dist(x,y) < e ==> ~(f y = a)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_within]) THEN
  DISCH_THEN(MP_TAC o SPEC `norm((f:real^M->real^N) x - a)`) THEN
  ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN
  GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN SIMP_TAC[] THEN NORM_ARITH_TAC);;

let CONTINUOUS_AT_AVOID = prove
 (`!f:real^M->real^N x a.
        f continuous (at x) /\ ~(f x = a)
        ==> ?e. &0 < e /\ !y. dist(x,y) < e ==> ~(f y = a)`,
  MP_TAC CONTINUOUS_WITHIN_AVOID THEN
  REPLICATE_TAC 2 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `(:real^M)`) THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  REWRITE_TAC[WITHIN_UNIV; IN_UNIV]);;

let CONTINUOUS_ON_AVOID = prove
 (`!f:real^M->real^N x s a.
        f continuous_on s /\ x IN s /\ ~(f x = a)
        ==> ?e. &0 < e /\ !y. y IN s /\ dist(x,y) < e ==> ~(f y = a)`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_WITHIN_AVOID THEN
  ASM_SIMP_TAC[]);;

let CONTINUOUS_ON_OPEN_AVOID = prove
 (`!f:real^M->real^N x s a.
        f continuous_on s /\ open s /\ x IN s /\ ~(f x = a)
        ==> ?e. &0 < e /\ !y. dist(x,y) < e ==> ~(f y = a)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `open(s:real^M->bool)` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_AVOID THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Proving a function is constant by proving open-ness of level set.         *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_LEVELSET_OPEN_IN_CASES = prove
 (`!f:real^M->real^N s a.
        connected s /\
        f continuous_on s /\
        open_in (subtopology euclidean s) {x | x IN s /\ f x = a}
        ==> (!x. x IN s ==> ~(f x = a)) \/ (!x. x IN s ==> f x = a)`,
  REWRITE_TAC[SET_RULE `(!x. x IN s ==> ~(f x = a)) <=>
                        {x | x IN s /\ f x = a} = {}`;
              SET_RULE `(!x. x IN s ==> f x = a) <=>
                        {x | x IN s /\ f x = a} = s`] THEN
  REWRITE_TAC[CONNECTED_CLOPEN] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT]);;

let CONTINUOUS_LEVELSET_OPEN_IN = prove
 (`!f:real^M->real^N s a.
        connected s /\
        f continuous_on s /\
        open_in (subtopology euclidean s) {x | x IN s /\ f x = a} /\
        (?x. x IN s /\ f x = a)
        ==> (!x. x IN s ==> f x = a)`,
  MESON_TAC[CONTINUOUS_LEVELSET_OPEN_IN_CASES]);;

let CONTINUOUS_LEVELSET_OPEN = prove
 (`!f:real^M->real^N s a.
        connected s /\
        f continuous_on s /\
        open {x | x IN s /\ f x = a} /\
        (?x. x IN s /\ f x = a)
        ==> (!x. x IN s ==> f x = a)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC CONTINUOUS_LEVELSET_OPEN_IN THEN
  ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
  EXISTS_TAC `{x | x IN s /\ (f:real^M->real^N) x = a}` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence a continuous function is constant if it maps into a discrete set.   *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_DISCRETE_RANGE_CONSTANT = prove
 (`!f:real^M->real^N s.
        connected s /\
        f continuous_on s /\
        (!x. x IN s
             ==> ?e. &0 < e /\
                     !y. y IN s /\ ~(f y = f x) ==> e <= norm(f y - f x))
        ==> ?a. !x. x IN s ==> f x = a`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^M`) THEN
  EXISTS_TAC `(f:real^M->real^N) a` THEN
  MATCH_MP_TAC CONTINUOUS_LEVELSET_OPEN_IN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  SIMP_TAC[open_in; IN_ELIM_THM; SUBSET] THEN X_GEN_TAC `x:real^M` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_on]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[dist; REAL_NOT_LE]);;

(* ------------------------------------------------------------------------- *)
(* Some arithmetical combinations (more to prove).                           *)
(* ------------------------------------------------------------------------- *)

let OPEN_SCALING = prove
 (`!s:real^N->bool c. ~(c = &0) /\ open s ==> open(IMAGE (\x. c % x) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[open_def; FORALL_IN_IMAGE] THEN
  STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e * abs(c)` THEN ASM_SIMP_TAC[REAL_LT_MUL; GSYM REAL_ABS_NZ] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  EXISTS_TAC `inv(c) % y:real^N` THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `x = inv(c) % c % x:real^N` SUBST1_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID];
    REWRITE_TAC[dist; GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_ABS_INV] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; GSYM REAL_ABS_NZ] THEN
    ASM_REWRITE_TAC[GSYM dist]]);;

let OPEN_NEGATIONS = prove
 (`!s:real^N->bool. open s ==> open (IMAGE (--) s)`,
  SUBGOAL_THEN `(--) = \x:real^N. --(&1) % x`
   (fun th -> SIMP_TAC[th; OPEN_SCALING; REAL_ARITH `~(--(&1) = &0)`]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC);;

let OPEN_TRANSLATION = prove
 (`!s a:real^N. open s ==> open(IMAGE (\x. a + x) s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. x - a`; `s:real^N->bool`]
         CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
  ASM_SIMP_TAC[CONTINUOUS_SUB; CONTINUOUS_AT_ID; CONTINUOUS_CONST] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN
  ASM_MESON_TAC[VECTOR_ARITH `(a + x) - a = x:real^N`;
                VECTOR_ARITH `a + (x - a) = x:real^N`]);;

let OPEN_TRANSLATION_EQ = prove
 (`!a s. open (IMAGE (\x:real^N. a + x) s) <=> open s`,
  REWRITE_TAC[open_def] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [OPEN_TRANSLATION_EQ];;

let OPEN_AFFINITY = prove
 (`!s a:real^N c.
        open s /\ ~(c = &0) ==> open (IMAGE (\x. a + c % x) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. a + c % x) = (\x. a + x) o (\x. c % x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  ASM_SIMP_TAC[IMAGE_o; OPEN_TRANSLATION; OPEN_SCALING]);;

let INTERIOR_TRANSLATION = prove
 (`!a:real^N s.
    interior (IMAGE (\x. a + x) s) = IMAGE (\x. a + x) (interior s)`,
  REWRITE_TAC[interior] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [INTERIOR_TRANSLATION];;

(* ------------------------------------------------------------------------- *)
(* Preservation of compactness and connectedness under continuous function.  *)
(* ------------------------------------------------------------------------- *)

let COMPACT_CONTINUOUS_IMAGE = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\ compact s ==> compact(IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_on; compact] THEN
  STRIP_TAC THEN X_GEN_TAC `y:num->real^N` THEN
  REWRITE_TAC[IN_IMAGE; SKOLEM_THM; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->real^M` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num->real^M`) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `r:num->num` THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f:real^M->real^N) l` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l:real^M`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[o_THM] THEN
  ASM_MESON_TAC[]);;

let COMPACT_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s. compact s /\ linear f ==> compact(IMAGE f s)`,
  SIMP_TAC[LINEAR_CONTINUOUS_ON; COMPACT_CONTINUOUS_IMAGE]);;

let COMPACT_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (compact (IMAGE f s) <=> compact s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE COMPACT_LINEAR_IMAGE));;

add_linear_invariants [COMPACT_LINEAR_IMAGE_EQ];;

let CONNECTED_CONTINUOUS_IMAGE = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\ connected s ==> connected(IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_ON_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[CONNECTED_CLOPEN; NOT_FORALL_THM; NOT_IMP; DE_MORGAN_THM] THEN
  REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `t:real^N->bool` th) THEN
    MP_TAC(SPEC `IMAGE (f:real^M->real^N) s DIFF t` th)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{x | x IN s /\ (f:real^M->real^N) x IN IMAGE f s DIFF t} =
                s DIFF {x | x IN s /\ f x IN t}`
  SUBST1_TAC THENL
   [UNDISCH_TAC `t SUBSET IMAGE (f:real^M->real^N) s` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF; IN_ELIM_THM; SUBSET] THEN
    MESON_TAC[];
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `{x | x IN s /\ (f:real^M->real^N) x IN t}` THEN
    ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[IN_IMAGE; SUBSET; IN_ELIM_THM; NOT_IN_EMPTY; EXTENSION] THEN
    MESON_TAC[]]);;

let CONNECTED_TRANSLATION = prove
 (`!a s. connected s ==> connected (IMAGE (\x:real^N. a + x) s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST]);;

let CONNECTED_TRANSLATION_EQ = prove
 (`!a s. connected (IMAGE (\x:real^N. a + x) s) <=> connected s`,
  REWRITE_TAC[connected] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [CONNECTED_TRANSLATION_EQ];;

let CONNECTED_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s. connected s /\ linear f ==> connected(IMAGE f s)`,
  SIMP_TAC[LINEAR_CONTINUOUS_ON; CONNECTED_CONTINUOUS_IMAGE]);;

let CONNECTED_LINEAR_IMAGE_EQ = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (connected (IMAGE f s) <=> connected s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE CONNECTED_LINEAR_IMAGE));;

add_linear_invariants [CONNECTED_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Connected components, considered as a "connectedness" relation or a set.  *)
(* ------------------------------------------------------------------------- *)

let connected_component = new_definition
 `connected_component s x y <=>
        ?t. connected t /\ t SUBSET s /\ x IN t /\ y IN t`;;

let CONNECTED_COMPONENT_IN = prove
 (`!s x y. connected_component s x y ==> x IN s /\ y IN s`,
  REWRITE_TAC[connected_component] THEN SET_TAC[]);;

let CONNECTED_COMPONENT_REFL = prove
 (`!s x:real^N. x IN s ==> connected_component s x x`,
  REWRITE_TAC[connected_component] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `{x:real^N}` THEN REWRITE_TAC[CONNECTED_SING] THEN
  ASM SET_TAC[]);;

let CONNECTED_COMPONENT_REFL_EQ = prove
 (`!s x:real^N. connected_component s x x <=> x IN s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[CONNECTED_COMPONENT_REFL] THEN
  REWRITE_TAC[connected_component] THEN SET_TAC[]);;

let CONNECTED_COMPONENT_SYM = prove
 (`!s x y:real^N. connected_component s x y ==> connected_component s y x`,
  REWRITE_TAC[connected_component] THEN MESON_TAC[]);;

let CONNECTED_COMPONENT_TRANS = prove
 (`!s x y:real^N.
    connected_component s x y /\ connected_component s y z
    ==> connected_component s x z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected_component] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `t:real^N->bool`)
                             (X_CHOOSE_TAC `u:real^N->bool`)) THEN
  EXISTS_TAC `t UNION u:real^N->bool` THEN
  ASM_REWRITE_TAC[IN_UNION; UNION_SUBSET] THEN
  MATCH_MP_TAC CONNECTED_UNION THEN ASM SET_TAC[]);;

let CONNECTED_COMPONENT_OF_SUBSET = prove
 (`!s t x. s SUBSET t /\ connected_component s x y
           ==> connected_component t x y`,
  REWRITE_TAC[connected_component] THEN SET_TAC[]);;

let CONNECTED_COMPONENT_SET = prove
 (`!s x. connected_component s x =
            { y | ?t. connected t /\ t SUBSET s /\ x IN t /\ y IN t}`,
  REWRITE_TAC[IN_ELIM_THM; EXTENSION] THEN
  REWRITE_TAC[IN; connected_component] THEN MESON_TAC[]);;

let CONNECTED_COMPONENT_UNIONS = prove
 (`!s x. connected_component s x =
                UNIONS {t | connected t /\ x IN t /\ t SUBSET s}`,
  REWRITE_TAC[CONNECTED_COMPONENT_SET] THEN SET_TAC[]);;

let CONNECTED_COMPONENT_SUBSET = prove
 (`!s x. (connected_component s x) SUBSET s`,
  REWRITE_TAC[CONNECTED_COMPONENT_SET] THEN SET_TAC[]);;

let CONNECTED_CONNECTED_COMPONENT_SET = prove
 (`!s. connected s <=> !x:real^N. x IN s ==> connected_component s x = s`,
  GEN_TAC THEN REWRITE_TAC[CONNECTED_COMPONENT_UNIONS] THEN EQ_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[CONNECTED_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CONNECTED_UNIONS THEN
  ASM SET_TAC[]);;

let CONNECTED_IFF_CONNECTED_COMPONENT = prove
 (`!s. connected s <=>
          !x y. x IN s /\ y IN s ==> connected_component s x y`,
  REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT_SET] THEN
  REWRITE_TAC[EXTENSION] THEN MESON_TAC[IN; CONNECTED_COMPONENT_IN]);;

let CONNECTED_COMPONENT_MAXIMAL = prove
 (`!s t x:real^N.
        x IN t /\ connected t /\ t SUBSET s
        ==> t SUBSET (connected_component s x)`,
  REWRITE_TAC[CONNECTED_COMPONENT_SET] THEN SET_TAC[]);;

let CONNECTED_COMPONENT_MONO = prove
 (`!s t x. s SUBSET t
           ==> (connected_component s x) SUBSET (connected_component t x)`,
  REWRITE_TAC[CONNECTED_COMPONENT_SET] THEN SET_TAC[]);;

let CONNECTED_CONNECTED_COMPONENT = prove
 (`!s x. connected(connected_component s x)`,
  REWRITE_TAC[CONNECTED_COMPONENT_UNIONS] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_UNIONS THEN SET_TAC[]);;

let CONNECTED_COMPONENT_EQ_EMPTY = prove
 (`!s x:real^N. connected_component s x = {} <=> ~(x IN s)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    REWRITE_TAC[IN; CONNECTED_COMPONENT_REFL_EQ];
    REWRITE_TAC[CONNECTED_COMPONENT_SET] THEN SET_TAC[]]);;

let CONNECTED_COMPONENT_EMPTY = prove
 (`!x. connected_component {} x = {}`,
  REWRITE_TAC[CONNECTED_COMPONENT_EQ_EMPTY; NOT_IN_EMPTY]);;

let CONNECTED_COMPONENT_EQ = prove
 (`!s x y. y IN connected_component s x
           ==> (connected_component s y = connected_component s x)`,
  REWRITE_TAC[EXTENSION; IN] THEN
  MESON_TAC[CONNECTED_COMPONENT_SYM; CONNECTED_COMPONENT_TRANS]);;

let CONNECTED_COMPONENT_CONNECTED_COMPONENT = prove
 (`!s x:real^N.
        connected_component (connected_component s x) x =
        connected_component s x`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN s` THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    SIMP_TAC[CONNECTED_COMPONENT_MONO; CONNECTED_COMPONENT_SUBSET] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    REWRITE_TAC[SUBSET_REFL; CONNECTED_CONNECTED_COMPONENT] THEN
    ASM_REWRITE_TAC[IN; CONNECTED_COMPONENT_REFL_EQ];
    MATCH_MP_TAC(SET_RULE `s = {} /\ t = {} ==> s = t`) THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_EQ_EMPTY] THEN
    ASM_MESON_TAC[SUBSET; CONNECTED_COMPONENT_SUBSET]]);;

let CLOSED_CONNECTED_COMPONENT = prove
 (`!s x:real^N. closed s ==> closed(connected_component s x)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN s` THENL
   [ALL_TAC; ASM_MESON_TAC[CONNECTED_COMPONENT_EQ_EMPTY; CLOSED_EMPTY]] THEN
  REWRITE_TAC[GSYM CLOSURE_EQ] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[CLOSURE_SUBSET] THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
  SIMP_TAC[CONNECTED_CLOSURE; CONNECTED_CONNECTED_COMPONENT] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[IN; CONNECTED_COMPONENT_REFL_EQ];
    MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]]);;

let CONNECTED_COMPONENT_DISJOINT = prove
 (`!s a b. DISJOINT (connected_component s a) (connected_component s b) <=>
             ~(a IN connected_component s b)`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN] THEN
  MESON_TAC[CONNECTED_COMPONENT_SYM; CONNECTED_COMPONENT_TRANS]);;

let CONNECTED_COMPONENT_NONOVERLAP = prove
 (`!s a b:real^N.
        (connected_component s a) INTER (connected_component s b) = {} <=>
        ~(a IN s) \/ ~(b IN s) \/
        ~(connected_component s a = connected_component s b)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(a:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONNECTED_COMPONENT_EQ_EMPTY]) THEN
  ASM_REWRITE_TAC[INTER_EMPTY] THEN
  ASM_CASES_TAC `(b:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONNECTED_COMPONENT_EQ_EMPTY]) THEN
  ASM_REWRITE_TAC[INTER_EMPTY] THEN ASM_CASES_TAC
   `connected_component s (a:real^N) = connected_component s b` THEN
  ASM_REWRITE_TAC[INTER_IDEMPOT; CONNECTED_COMPONENT_EQ_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o check(is_neg o concl)) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM DISJOINT]) THEN
  REWRITE_TAC[CONNECTED_COMPONENT_DISJOINT]);;

let CONNECTED_COMPONENT_OVERLAP = prove
 (`!s a b:real^N.
        ~((connected_component s a) INTER (connected_component s b) = {}) <=>
        a IN s /\ b IN s /\
        connected_component s a = connected_component s b`,
  REWRITE_TAC[CONNECTED_COMPONENT_NONOVERLAP; DE_MORGAN_THM]);;

let CONNECTED_COMPONENT_SYM_EQ = prove
 (`!s x y. connected_component s x y <=> connected_component s y x`,
  MESON_TAC[CONNECTED_COMPONENT_SYM]);;

let CONNECTED_COMPONENT_EQ_EQ = prove
 (`!s x y:real^N.
        connected_component s x = connected_component s y <=>
           ~(x IN s) /\ ~(y IN s) \/
           x IN s /\ y IN s /\ connected_component s x y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(y:real^N) IN s` THENL
   [ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN
      ASM_MESON_TAC[CONNECTED_COMPONENT_TRANS; CONNECTED_COMPONENT_REFL;
                    CONNECTED_COMPONENT_SYM];
      ASM_MESON_TAC[CONNECTED_COMPONENT_EQ_EMPTY]];
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONNECTED_COMPONENT_EQ_EMPTY]) THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_EQ_EMPTY] THEN
    ONCE_REWRITE_TAC[CONNECTED_COMPONENT_SYM_EQ] THEN
    ASM_REWRITE_TAC[EMPTY] THEN ASM_MESON_TAC[CONNECTED_COMPONENT_EQ_EMPTY]]);;

let CONNECTED_COMPONENT_IDEMP = prove
 (`!s x:real^N. connected_component (connected_component s x) x =
                connected_component s x`,
  REWRITE_TAC[FUN_EQ_THM; connected_component] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CONNECTED_COMPONENT_MAXIMAL; SUBSET_TRANS;
                CONNECTED_COMPONENT_SUBSET]);;

let CONNECTED_COMPONENT_TRANSLATION = prove
 (`!a s x. connected_component (IMAGE (\x. a + x) s) (a + x) =
                IMAGE (\x. a + x) (connected_component s x)`,
  REWRITE_TAC[CONNECTED_COMPONENT_SET] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [CONNECTED_COMPONENT_TRANSLATION];;

let CONNECTED_COMPONENT_LINEAR_IMAGE = prove
 (`!f s x. linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
           ==> connected_component (IMAGE f s) (f x) =
               IMAGE f (connected_component s x)`,
  REWRITE_TAC[CONNECTED_COMPONENT_SET] THEN
  GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [CONNECTED_COMPONENT_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* The set of connected components of a set.                                 *)
(* ------------------------------------------------------------------------- *)

let components = new_definition
  `components s = {connected_component s x | x | x:real^N IN s}`;;

let IN_COMPONENTS = prove
 (`!u:real^N->bool s. s IN components u
    <=> ?x. x IN u /\ s = connected_component u x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[components] THEN EQ_TAC
  THENL [SET_TAC[];STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `x:real^N IN u` THEN SET_TAC[]]);;

let UNIONS_COMPONENTS = prove
 (`!u:real^N->bool. u = UNIONS (components u)`,
  REWRITE_TAC[EXTENSION] THEN REPEAT GEN_TAC THEN EQ_TAC
  THENL[DISCH_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
  EXISTS_TAC `connected_component (u:real^N->bool) x` THEN CONJ_TAC THENL
  [REWRITE_TAC[components] THEN SET_TAC[ASSUME `x:real^N IN u`];
  REWRITE_TAC[CONNECTED_COMPONENT_SET] THEN SUBGOAL_THEN
  `?s:real^N->bool. connected s /\ s SUBSET u /\ x IN s` MP_TAC
  THENL[EXISTS_TAC `{x:real^N}` THEN ASM_REWRITE_TAC[CONNECTED_SING] THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]; SET_TAC[]]];
  REWRITE_TAC[IN_UNIONS] THEN STRIP_TAC THEN
  MATCH_MP_TAC (SET_RULE `!x:real^N s u. x IN s /\ s SUBSET u ==> x IN u`) THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN STRIP_ASSUME_TAC
  (MESON[IN_COMPONENTS;ASSUME `t:real^N->bool IN components u`]
  `?y. t:real^N->bool = connected_component u y`) THEN
   ASM_REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]]);;

let PAIRWISE_DISJOINT_COMPONENTS = prove
 (`!u:real^N->bool. pairwise DISJOINT (components u)`,
  GEN_TAC THEN REWRITE_TAC[pairwise;DISJOINT] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN STRIP_TAC THEN
  ASSERT_TAC `(?a. s:real^N->bool = connected_component u a) /\
  ?b. t:real^N->bool = connected_component u b`
  THENL [ASM_MESON_TAC[IN_COMPONENTS];
  ASM_MESON_TAC[CONNECTED_COMPONENT_NONOVERLAP]]);;

(* ------------------------------------------------------------------------- *)
(* Continuity implies uniform continuity on a compact domain.                *)
(* ------------------------------------------------------------------------- *)

let COMPACT_UNIFORMLY_CONTINUOUS = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\ compact s ==> f uniformly_continuous_on s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[continuous_on; RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `d:real^M->real->real`) THEN
  REWRITE_TAC[uniformly_continuous_on] THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP HEINE_BOREL_LEMMA) THEN
  DISCH_THEN(MP_TAC o SPEC
    `{b | ?x:real^M. x IN s /\ (b = ball(x,d x (e / &2)))}`) THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_BALL] THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[CENTRE_IN_BALL; REAL_HALF; OPEN_BALL]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `v:real^M` th) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CHOOSE_THEN MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `u:real^M` th) THEN MP_TAC(SPEC `v:real^M` th)) THEN
  ASM_REWRITE_TAC[DIST_REFL] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^M` (CONJUNCTS_THEN2 ASSUME_TAC
    SUBST_ALL_TAC)) THEN
  REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC DIST_TRIANGLE_HALF_L THEN
  ASM_MESON_TAC[REAL_HALF]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of inverse function on compact domain.                         *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_INVERSE = prove
 (`!f:real^M->real^N g s.
        f continuous_on s /\ compact s /\ (!x. x IN s ==> (g(f(x)) = x))
        ==> g continuous_on (IMAGE f s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_CLOSED] THEN
  SUBGOAL_THEN `IMAGE g (IMAGE (f:real^M->real^N) s) = s` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:real^M->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[CLOSED_IN_CLOSED] THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) t` THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN
    REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    ASM_MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_IN_CLOSED_TRANS;
                  BOUNDED_SUBSET; CONTINUOUS_ON_SUBSET];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_IMAGE] THEN
    ASM_MESON_TAC[CLOSED_IN_SUBSET; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* A uniformly convergent limit of continuous functions is continuous.       *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_UNIFORM_LIMIT = prove
 (`!net f:A->real^M->real^N g s.
        ~(trivial_limit net) /\
        eventually (\n. (f n) continuous_on s) net /\
        (!e. &0 < e
             ==> eventually (\n. !x. x IN s ==> norm(f n x - g x) < e) net)
        ==> g continuous_on s`,
  REWRITE_TAC[continuous_on] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC th THEN REWRITE_TAC[IMP_IMP] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM EVENTUALLY_AND]) THEN
  DISCH_THEN(MP_TAC o MATCH_MP EVENTUALLY_HAPPENS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `a:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `x:real^M`) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `y:real^M` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th ->
   MP_TAC(SPEC `x:real^M` th) THEN MP_TAC(SPEC `y:real^M` th)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
   `w <= x + y + z
    ==> x < e / &3 ==> y < e / &3 ==> z < e / &3 ==> w < e`) THEN
  REWRITE_TAC[dist] THEN
  SUBST1_TAC(VECTOR_ARITH
   `(g:real^M->real^N) y - g x =
    --(f (a:A) y - g y) + (f a x - g x) + (f a y - f a x)`) THEN
  MATCH_MP_TAC NORM_TRIANGLE_LE THEN REWRITE_TAC[NORM_NEG; REAL_LE_LADD] THEN
  MATCH_MP_TAC NORM_TRIANGLE_LE THEN REWRITE_TAC[NORM_NEG; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Topological stuff lifted from and dropped to R                            *)
(* ------------------------------------------------------------------------- *)

let OPEN_LIFT = prove
 (`!s. open(IMAGE lift s) <=>
        !x. x IN s ==> ?e. &0 < e /\ !x'. abs(x' - x) < e ==> x' IN s`,
  REWRITE_TAC[open_def; FORALL_LIFT; LIFT_IN_IMAGE_LIFT; DIST_LIFT]);;

let LIMPT_APPROACHABLE_LIFT = prove
 (`!x s. (lift x) limit_point_of (IMAGE lift s) <=>
         !e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ abs(x' - x) < e`,
  REWRITE_TAC[LIMPT_APPROACHABLE; EXISTS_LIFT; LIFT_IN_IMAGE_LIFT;
              LIFT_EQ; DIST_LIFT]);;

let CLOSED_LIFT = prove
 (`!s. closed (IMAGE lift s) <=>
        !x. (!e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ abs(x' - x) < e)
            ==> x IN s`,
  GEN_TAC THEN REWRITE_TAC[CLOSED_LIMPT; LIMPT_APPROACHABLE] THEN
  ONCE_REWRITE_TAC[FORALL_LIFT] THEN
  REWRITE_TAC[LIMPT_APPROACHABLE_LIFT; LIFT_EQ; DIST_LIFT;
              EXISTS_LIFT; LIFT_IN_IMAGE_LIFT]);;

let CONTINUOUS_AT_LIFT_RANGE = prove
 (`!f x. (lift o f) continuous (at x) <=>
                !e. &0 < e
                    ==> ?d. &0 < d /\
                            (!x'. norm(x' - x) < d
                                  ==> abs(f x' - f x) < e)`,
  REWRITE_TAC[continuous_at; o_THM; DIST_LIFT] THEN REWRITE_TAC[dist]);;

let CONTINUOUS_ON_LIFT_RANGE = prove
 (`!f s. (lift o f) continuous_on s <=>
         !x. x IN s
             ==> !e. &0 < e
                     ==> ?d. &0 < d /\
                             (!x'. x' IN s /\ norm(x' - x) < d
                                   ==> abs(f x' - f x) < e)`,
  REWRITE_TAC[continuous_on; o_THM; DIST_LIFT] THEN REWRITE_TAC[dist]);;

let CONTINUOUS_AT_LIFT_NORM = prove
 (`!x. (lift o norm) continuous (at x)`,
  REWRITE_TAC[CONTINUOUS_AT_LIFT_RANGE; NORM_LIFT] THEN
  MESON_TAC[REAL_ABS_SUB_NORM; REAL_LET_TRANS]);;

let CONTINUOUS_ON_LIFT_NORM = prove
 (`!s. (lift o norm) continuous_on s`,
  REWRITE_TAC[CONTINUOUS_ON_LIFT_RANGE; NORM_LIFT] THEN
  MESON_TAC[REAL_ABS_SUB_NORM; REAL_LET_TRANS]);;

let CONTINUOUS_AT_LIFT_COMPONENT = prove
 (`!i a. 1 <= i /\ i <= dimindex(:N)
         ==> (\x:real^N. lift(x$i)) continuous (at a)`,
  SIMP_TAC[continuous_at; DIST_LIFT; GSYM VECTOR_SUB_COMPONENT] THEN
  MESON_TAC[dist; REAL_LET_TRANS; COMPONENT_LE_NORM]);;

let CONTINUOUS_ON_LIFT_COMPONENT = prove
 (`!i s. 1 <= i /\ i <= dimindex(:N)
         ==> (\x:real^N. lift(x$i)) continuous_on s`,
  SIMP_TAC[continuous_on; DIST_LIFT; GSYM VECTOR_SUB_COMPONENT] THEN
  MESON_TAC[dist; REAL_LET_TRANS; COMPONENT_LE_NORM]);;

let CONTINUOUS_AT_LIFT_INFNORM = prove
 (`!x:real^N. (lift o infnorm) continuous (at x)`,
  REWRITE_TAC[CONTINUOUS_AT; LIM_AT; o_THM; DIST_LIFT] THEN
  MESON_TAC[REAL_LET_TRANS; dist; REAL_ABS_SUB_INFNORM; INFNORM_LE_NORM]);;

(* ------------------------------------------------------------------------- *)
(* Hence some handy theorems on distance, diameter etc. of/from a set.       *)
(* ------------------------------------------------------------------------- *)

let COMPACT_ATTAINS_SUP = prove
 (`!s. compact (IMAGE lift s) /\ ~(s = {})
       ==> ?x. x IN s /\ !y. y IN s ==> y <= x`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `s:real->bool` BOUNDED_HAS_SUP) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN EXISTS_TAC `sup s` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CLOSED_LIFT; REAL_ARITH `s <= s - e <=> ~(&0 < e)`;
                REAL_ARITH `x <= s /\ ~(x <= s - e) ==> abs(x - s) < e`]);;

let COMPACT_ATTAINS_INF = prove
 (`!s. compact (IMAGE lift s) /\ ~(s = {})
       ==> ?x. x IN s /\ !y. y IN s ==> x <= y`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `s:real->bool` BOUNDED_HAS_INF) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN EXISTS_TAC `inf s` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CLOSED_LIFT; REAL_ARITH `s + e <= s <=> ~(&0 < e)`;
                REAL_ARITH `s <= x /\ ~(s + e <= x) ==> abs(x - s) < e`]);;

let CONTINUOUS_ATTAINS_SUP = prove
 (`!f:real^N->real s.
        compact s /\ ~(s = {}) /\ (lift o f) continuous_on s
        ==> ?x. x IN s /\ !y. y IN s ==> f(y) <= f(x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `IMAGE (f:real^N->real) s` COMPACT_ATTAINS_SUP) THEN
  ASM_SIMP_TAC[GSYM IMAGE_o; COMPACT_CONTINUOUS_IMAGE; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[IN_IMAGE]);;

let CONTINUOUS_ATTAINS_INF = prove
 (`!f:real^N->real s.
        compact s /\ ~(s = {}) /\ (lift o f) continuous_on s
        ==> ?x. x IN s /\ !y. y IN s ==> f(x) <= f(y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `IMAGE (f:real^N->real) s` COMPACT_ATTAINS_INF) THEN
  ASM_SIMP_TAC[GSYM IMAGE_o; COMPACT_CONTINUOUS_IMAGE; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[IN_IMAGE]);;

let DISTANCE_ATTAINS_SUP = prove
 (`!s a. compact s /\ ~(s = {})
         ==> ?x. x IN s /\ !y. y IN s ==> dist(a,y) <= dist(a,x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ATTAINS_SUP THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_LIFT_RANGE] THEN REWRITE_TAC[dist] THEN
  ASM_MESON_TAC[REAL_LET_TRANS; REAL_ABS_SUB_NORM; NORM_NEG;
                VECTOR_ARITH `(a - x) - (a - y) = --(x - y):real^N`]);;

(* ------------------------------------------------------------------------- *)
(* For *minimal* distance, we only need closure, not compactness.            *)
(* ------------------------------------------------------------------------- *)

let DISTANCE_ATTAINS_INF = prove
 (`!s a:real^N.
        closed s /\ ~(s = {})
        ==> ?x. x IN s /\ !y. y IN s ==> dist(a,x) <= dist(a,y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:real^N`) THEN
  MP_TAC(ISPECL [`\x:real^N. dist(a,x)`; `cball(a:real^N,dist(b,a)) INTER s`]
                CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_INTER; BOUNDED_INTER;
                 BOUNDED_CBALL; CLOSED_CBALL; GSYM MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[dist; CONTINUOUS_ON_LIFT_RANGE; IN_INTER; IN_CBALL] THEN
    ASM_MESON_TAC[REAL_LET_TRANS; REAL_ABS_SUB_NORM; NORM_NEG; REAL_LE_REFL;
            NORM_SUB; VECTOR_ARITH `(a - x) - (a - y) = --(x - y):real^N`];
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[IN_INTER; IN_CBALL] THEN
    ASM_MESON_TAC[DIST_SYM; REAL_LE_TOTAL; REAL_LE_TRANS]]);;

(* ------------------------------------------------------------------------- *)
(* We can now extend limit compositions to consider the scalar multiplier.   *)
(* ------------------------------------------------------------------------- *)

let LIM_MUL = prove
 (`!net:(A)net f l:real^N c d.
        ((lift o c) --> lift d) net /\ (f --> l) net
        ==> ((\x. c(x) % f(x)) --> (d % l)) net`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`net:(A)net`; `\x (y:real^N). drop x % y`;
  `lift o (c:A->real)`; `f:A->real^N`; `lift d`; `l:real^N`] LIM_BILINEAR) THEN
  ASM_REWRITE_TAC[LIFT_DROP; o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[bilinear; linear; DROP_ADD; DROP_CMUL] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let LIM_VMUL = prove
 (`!net:(A)net c d v:real^N.
        ((lift o c) --> lift d) net ==> ((\x. c(x) % v) --> d % v) net`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_MUL THEN ASM_REWRITE_TAC[LIM_CONST]);;

let CONTINUOUS_VMUL = prove
 (`!net c v. (lift o c) continuous net ==> (\x. c(x) % v) continuous net`,
  REWRITE_TAC[continuous; LIM_VMUL; o_THM]);;

let CONTINUOUS_MUL = prove
 (`!net f c. (lift o c) continuous net /\ f continuous net
             ==> (\x. c(x) % f(x)) continuous net`,
  REWRITE_TAC[continuous; LIM_MUL; o_THM]);;

let CONTINUOUS_ON_VMUL = prove
 (`!s c v. (lift o c) continuous_on s ==> (\x. c(x) % v) continuous_on s`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  SIMP_TAC[CONTINUOUS_VMUL]);;

let CONTINUOUS_ON_MUL = prove
 (`!s c f v. (lift o c) continuous_on s /\ f continuous_on s
             ==> (\x. c(x) % f(x)) continuous_on s`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  SIMP_TAC[CONTINUOUS_MUL]);;

(* ------------------------------------------------------------------------- *)
(* And so we have continuity of inverse.                                     *)
(* ------------------------------------------------------------------------- *)

let LIM_INV = prove
 (`!net:(A)net f l.
        ((lift o f) --> lift l) net /\ ~(l = &0)
        ==> ((lift o inv o f) --> lift(inv l)) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN
  ASM_CASES_TAC `trivial_limit(net:(A)net)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[o_THM; DIST_LIFT] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min (abs(l) / &2) ((l pow 2 * e) / &2)`) THEN
  REWRITE_TAC[REAL_LT_MIN] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_ABS_NZ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; GSYM REAL_ABS_NZ; REAL_POW_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:A` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `b:A` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  SIMP_TAC[REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `abs(x - l) * &2 < abs l ==> ~(x = &0)`)) THEN
  ASM_SIMP_TAC[REAL_SUB_INV; REAL_ABS_DIV; REAL_LT_LDIV_EQ;
               GSYM REAL_ABS_NZ; REAL_ENTIRE] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `abs(x - y) * &2 < b * c ==> c * b <= d * &2 ==> abs(y - x) < d`)) THEN
  ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_LE_LMUL_EQ] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_POW_2; REAL_MUL_ASSOC; GSYM REAL_ABS_NZ;
               REAL_LE_RMUL_EQ] THEN
  ASM_SIMP_TAC[REAL_ARITH `abs(x - y) * &2 < abs y ==> abs y <= &2 * abs x`]);;

let CONTINUOUS_INV = prove
 (`!net f. (lift o f) continuous net /\ ~(f(netlimit net) = &0)
           ==> (lift o inv o f) continuous net`,
  REWRITE_TAC[continuous; LIM_INV; o_THM]);;

let CONTINUOUS_AT_WITHIN_INV = prove
 (`!f s a:real^N.
        (lift o f) continuous (at a within s) /\ ~(f a = &0)
        ==> (lift o inv o f) continuous (at a within s)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `trivial_limit (at (a:real^N) within s)` THENL
   [ASM_REWRITE_TAC[continuous; LIM];
    ASM_SIMP_TAC[NETLIMIT_WITHIN; CONTINUOUS_INV]]);;

let CONTINUOUS_AT_INV = prove
 (`!f a. (lift o f) continuous at a /\ ~(f a = &0)
         ==> (lift o inv o f) continuous at a`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[CONTINUOUS_AT_WITHIN_INV]);;

let CONTINUOUS_ON_INV = prove
 (`!f s. (lift o f) continuous_on s /\ (!x. x IN s ==> ~(f x = &0))
         ==> (lift o inv o f) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_AT_WITHIN_INV]);;

(* ------------------------------------------------------------------------- *)
(* Preservation properties for pasted sets.                                  *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_PASTECART = prove
 (`!s:real^M->bool t:real^N->bool.
     bounded s /\ bounded t ==> bounded {pastecart x y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bounded; IN_ELIM_THM] THEN
  ASM_MESON_TAC[NORM_PASTECART_LE; REAL_LE_ADD2; REAL_LE_TRANS]);;

let CLOSED_PASTECART = prove
 (`!s:real^M->bool t:real^N->bool.
     closed s /\ closed t ==> closed {pastecart x y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_SEQUENTIAL_LIMITS] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; IN_ELIM_THM; dist] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`z:num->real^(M,N)finite_sum`; `l:real^(M,N)finite_sum`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:num->real^M`; `y:num->real^N`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`fstcart(l:real^(M,N)finite_sum)`; `sndcart(l:real^(M,N)finite_sum)`] THEN
  REWRITE_TAC[PASTECART_FST_SND] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `x:num->real^M`; EXISTS_TAC `y:num->real^N`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < a ==> x < a`) THEN
  MESON_TAC[NORM_FSTCART; FSTCART_SUB; FSTCART_PASTECART;
            NORM_SNDCART; SNDCART_SUB; SNDCART_PASTECART]);;

let COMPACT_PASTECART = prove
 (`!s:real^M->bool t:real^N->bool.
     compact s /\ compact t ==> compact {pastecart x y | x IN s /\ y IN t}`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_PASTECART; CLOSED_PASTECART]);;

let LIM_PASTECART = prove
 (`!net f:A->real^M g:A->real^N.
        (f --> a) net /\ (g --> b) net
        ==> ((\x. pastecart (f x) (g x)) --> pastecart a b) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN
  ASM_CASES_TAC `trivial_limit(net:(A)net)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP NET_DILEMMA) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  REWRITE_TAC[dist; PASTECART_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH
    `z <= x + y ==> x < e / &2 /\ y < e / &2 ==> z < e`) THEN
  REWRITE_TAC[NORM_PASTECART_LE]);;

let CONTINUOUS_PASTECART = prove
 (`!net f:A->real^M g:A->real^N.
        f continuous net /\ g continuous net
        ==> (\x. pastecart (f x) (g x)) continuous net`,
  REWRITE_TAC[continuous; LIM_PASTECART]);;

let CONTINUOUS_ON_PASTECART = prove
 (`!f:real^M->real^N g:real^M->real^P s.
        f continuous_on s /\ g continuous_on s
        ==> (\x. pastecart (f x) (g x)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON; LIM_PASTECART]);;

(* ------------------------------------------------------------------------- *)
(* Hence some useful properties follow quite easily.                         *)
(* ------------------------------------------------------------------------- *)

let COMPACT_SCALING = prove
 (`!s:real^N->bool c. compact s ==> compact (IMAGE (\x. c % x) s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let COMPACT_NEGATIONS = prove
 (`!s:real^N->bool. compact s ==> compact (IMAGE (--) s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let COMPACT_SUMS = prove
 (`!s:real^N->bool t.
        compact s /\ compact t ==> compact {x + y | x IN s /\ y IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x + y | x IN s /\ y IN t} =
                IMAGE (\z. fstcart z + sndcart z :real^N)
                      {pastecart x y | x IN s /\ y IN t}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_FST_SND];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[COMPACT_PASTECART] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[linear; FSTCART_ADD; FSTCART_CMUL; SNDCART_ADD;
              SNDCART_CMUL] THEN
  CONJ_TAC THEN VECTOR_ARITH_TAC);;

let COMPACT_DIFFERENCES = prove
 (`!s:real^N->bool t.
        compact s /\ compact t ==> compact {x - y | x IN s /\ y IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x - y | x:real^N IN s /\ y IN t} =
                {x + y | x IN s /\ y IN (IMAGE (--) t)}`
    (fun th -> ASM_SIMP_TAC[th; COMPACT_SUMS; COMPACT_NEGATIONS]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `(x:real^N = --y) <=> (y = --x)`] THEN
  SIMP_TAC[VECTOR_SUB; GSYM CONJ_ASSOC; UNWIND_THM2] THEN
  MESON_TAC[VECTOR_NEG_NEG]);;

let COMPACT_TRANSLATION_EQ = prove
 (`!a s. compact (IMAGE (\x:real^N. a + x) s) <=> compact s`,
  REWRITE_TAC[COMPACT_EQ_HEINE_BOREL] THEN GEOM_TRANSLATE_TAC[]);;

let COMPACT_TRANSLATION = prove
 (`!s a:real^N. compact s ==> compact (IMAGE (\x. a + x) s)`,
  REWRITE_TAC[COMPACT_TRANSLATION_EQ]);;

add_translation_invariants [COMPACT_TRANSLATION_EQ];;

let COMPACT_AFFINITY = prove
 (`!s a:real^N c.
        compact s ==> compact (IMAGE (\x. a + c % x) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. a + c % x) = (\x. a + x) o (\x. c % x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  ASM_SIMP_TAC[IMAGE_o; COMPACT_TRANSLATION; COMPACT_SCALING]);;

(* ------------------------------------------------------------------------- *)
(* Hence we get the following.                                               *)
(* ------------------------------------------------------------------------- *)

let COMPACT_SUP_MAXDISTANCE = prove
 (`!s:real^N->bool.
        compact s /\ ~(s = {})
        ==> ?x y. x IN s /\ y IN s /\
                  !u v. u IN s /\ v IN s ==> norm(u - v) <= norm(x - y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{x - y:real^N | x IN s /\ y IN s}`; `vec 0:real^N`]
                DISTANCE_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_DIFFERENCES] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[MEMBER_NOT_EMPTY];
    REWRITE_TAC[IN_ELIM_THM; dist; VECTOR_SUB_RZERO; VECTOR_SUB_LZERO;
                NORM_NEG] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* We can state this in terms of diameter of a set.                          *)
(* ------------------------------------------------------------------------- *)

let diameter = new_definition
  `diameter s =
        if s = {} then &0
        else sup {norm(x - y) | x IN s /\ y IN s}`;;

let DIAMETER_BOUNDED = prove
 (`!s. bounded s
       ==> (!x:real^N y. x IN s /\ y IN s ==> norm(x - y) <= diameter s) /\
           (!d. &0 <= d /\ d < diameter s
                ==> ?x y. x IN s /\ y IN s /\ norm(x - y) > d)`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[diameter; NOT_IN_EMPTY; REAL_LET_ANTISYM] THEN
  MP_TAC(SPEC `{norm(x - y:real^N) | x IN s /\ y IN s}` SUP) THEN
  ABBREV_TAC `b = sup {norm(x - y:real^N) | x IN s /\ y IN s}` THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[NOT_IN_EMPTY; real_gt] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC];
    MESON_TAC[REAL_NOT_LE]] THEN
  SIMP_TAC[VECTOR_SUB; LEFT_IMP_EXISTS_THM] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
  MESON_TAC[REAL_ARITH `x <= y + z /\ y <= b /\ z<= b ==> x <= b + b`;
            NORM_TRIANGLE; NORM_NEG]);;

let DIAMETER_BOUNDED_BOUND = prove
 (`!s x y. bounded s /\ x IN s /\ y IN s ==> norm(x - y) <= diameter s`,
  MESON_TAC[DIAMETER_BOUNDED]);;

let DIAMETER_COMPACT_ATTAINED = prove
 (`!s:real^N->bool.
        compact s /\ ~(s = {})
        ==> ?x y. x IN s /\ y IN s /\ (norm(x - y) = diameter s)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_SUP_MAXDISTANCE) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `s:real^N->bool` DIAMETER_BOUNDED) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COMPACT_EQ_BOUNDED_CLOSED]) THEN
  ASM_REWRITE_TAC[real_gt] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  ASM_MESON_TAC[NORM_POS_LE; REAL_NOT_LT]);;

let DIAMETER_TRANSLATION = prove
 (`!a s. diameter (IMAGE (\x. a + x) s) = diameter s`,
  REWRITE_TAC[diameter] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [DIAMETER_TRANSLATION];;

let DIAMETER_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x. norm(f x) = norm x)
        ==> diameter(IMAGE f s) = diameter s`,
  REWRITE_TAC[diameter] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[diameter; IMAGE_EQ_EMPTY] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; EXISTS_IN_IMAGE] THEN
  ASM_MESON_TAC[LINEAR_SUB]);;

add_linear_invariants [DIAMETER_LINEAR_IMAGE];;

let DIAMETER_EMPTY = prove
 (`diameter {} = &0`,
  REWRITE_TAC[diameter]);;

let DIAMETER_POS_LE = prove
 (`!s:real^N->bool. bounded s ==> &0 <= diameter s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[diameter] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MP_TAC(SPEC `{norm(x - y:real^N) | x IN s /\ y IN s}` SUP) THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `B:real` o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
    EXISTS_TAC `&2 * B` THEN
    ASM_SIMP_TAC[NORM_ARITH
      `norm x <= B /\ norm y <= B ==> norm(x - y) <= &2 * B`];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `a:real^N`] o CONJUNCT1) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0]]);;

let DIAMETER_SUBSET = prove
 (`!s t:real^N->bool. s SUBSET t /\ bounded t ==> diameter s <= diameter t`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_SIMP_TAC[DIAMETER_EMPTY; DIAMETER_POS_LE] THEN
  ASM_REWRITE_TAC[diameter] THEN
  COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN
  REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `B:real` o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  EXISTS_TAC `&2 * B` THEN
  ASM_SIMP_TAC[NORM_ARITH
    `norm x <= B /\ norm y <= B ==> norm(x - y) <= &2 * B`]);;

let DIAMETER_CLOSURE = prove
 (`!s:real^N->bool. bounded s ==> diameter(closure s) = diameter s`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIAMETER_SUBSET; BOUNDED_CLOSURE; CLOSURE_SUBSET] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  DISCH_TAC THEN MP_TAC(ISPEC `closure s:real^N->bool` DIAMETER_BOUNDED) THEN
  ABBREV_TAC `d = diameter(closure s) - diameter(s:real^N->bool)` THEN
  ASM_SIMP_TAC[BOUNDED_CLOSURE] THEN DISCH_THEN(MP_TAC o
    SPEC `diameter(closure(s:real^N->bool)) - d / &2` o CONJUNCT2) THEN
  REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC; NOT_EXISTS_THM] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIAMETER_POS_LE) THEN
  REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE; CONJ_ASSOC; AND_FORALL_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `d / &4`) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < d / &4 <=> &0 < d`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `u:real^N` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))
   (X_CHOOSE_THEN `v:real^N` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIAMETER_BOUNDED) THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^N`; `v:real^N`] o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN NORM_ARITH_TAC);;

let DIAMETER_SUBSET_CBALL_NONEMPTY = prove
 (`!s:real^N->bool.
       bounded s /\ ~(s = {}) ==> ?z. z IN s /\ s SUBSET cball(z,diameter s)`,
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[SUBSET] THEN X_GEN_TAC `b:real^N` THEN
   DISCH_TAC THEN REWRITE_TAC[IN_CBALL; dist] THEN
   ASM_MESON_TAC[DIAMETER_BOUNDED]);;

let DIAMETER_SUBSET_CBALL = prove
 (`!s:real^N->bool. bounded s ==> ?z. s SUBSET cball(z,diameter s)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_MESON_TAC[DIAMETER_SUBSET_CBALL_NONEMPTY; EMPTY_SUBSET]);;

let LEBESGUE_COVERING_LEMMA = prove
 (`!s:real^N->bool c.
        compact s /\ ~(c = {}) /\ s SUBSET UNIONS c /\ (!b. b IN c ==> open b)
        ==> ?d. &0 < d /\
                !t. t SUBSET s /\ diameter t <= d
                    ==> ?b. b IN c /\ t SUBSET b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HEINE_BOREL_LEMMA) THEN
  DISCH_THEN(MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN ASM_SIMP_TAC[] THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `t:real^N->bool` DIAMETER_SUBSET_CBALL_NONEMPTY) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[BOUNDED_SUBSET; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `b:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `cball(x:real^N,diameter(t:real^N->bool))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `ball(x:real^N,e)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN
  MAP_EVERY UNDISCH_TAC [`&0 < e`; `diameter(t:real^N->bool) <= e / &2`] THEN
  NORM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Related results with closure as the conclusion.                           *)
(* ------------------------------------------------------------------------- *)

let CLOSED_SCALING = prove
 (`!s:real^N->bool c. closed s ==> closed (IMAGE (\x. c % x) s)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s :real^N->bool = {}` THEN
  ASM_REWRITE_TAC[CLOSED_EMPTY; IMAGE_CLAUSES] THEN
  ASM_CASES_TAC `c = &0` THENL
   [SUBGOAL_THEN `IMAGE (\x:real^N. c % x) s = {(vec 0)}`
     (fun th -> REWRITE_TAC[th; CLOSED_SING]) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SING; VECTOR_MUL_LZERO] THEN
    ASM_MESON_TAC[MEMBER_NOT_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSED_SEQUENTIAL_LIMITS; IN_IMAGE; SKOLEM_THM] THEN
  STRIP_TAC THEN X_GEN_TAC `x:num->real^N` THEN X_GEN_TAC `l:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num->real^N` MP_TAC) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  EXISTS_TAC `inv(c) % l :real^N` THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `\n:num. inv(c) % x n:real^N` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID];
    MATCH_MP_TAC LIM_CMUL THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[SYM(SPEC_ALL th)]) THEN
    ASM_REWRITE_TAC[ETA_AX]]);;

let CLOSED_NEGATIONS = prove
 (`!s:real^N->bool. closed s ==> closed (IMAGE (--) s)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `IMAGE (--) s = IMAGE (\x:real^N. --(&1) % x) s`
  SUBST1_TAC THEN SIMP_TAC[CLOSED_SCALING] THEN
  REWRITE_TAC[VECTOR_ARITH `--(&1) % x = --x`] THEN REWRITE_TAC[ETA_AX]);;

let COMPACT_CLOSED_SUMS = prove
 (`!s:real^N->bool t.
        compact s /\ closed t ==> closed {x + y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[compact; IN_ELIM_THM; CLOSED_SEQUENTIAL_LIMITS] THEN
  STRIP_TAC THEN X_GEN_TAC `f:num->real^N` THEN X_GEN_TAC `l:real^N` THEN
  REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num->real^N` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check(is_imp o concl) o SPEC `a:num->real^N`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `la:real^N` (X_CHOOSE_THEN `sub:num->num`
        STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`la:real^N`; `l - la:real^N`] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `a + (b - a) = b:real^N`] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `\n. (f o (sub:num->num)) n - (a o sub) n:real^N` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[VECTOR_ADD_SUB; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LIM_SUB THEN ASM_SIMP_TAC[LIM_SUBSEQUENCE; ETA_AX]);;

let CLOSED_COMPACT_SUMS = prove
 (`!s:real^N->bool t.
        closed s /\ compact t ==> closed {x + y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{x + y:real^N | x IN s /\ y IN t} = {y + x | y IN t /\ x IN s}`
  SUBST1_TAC THEN  SIMP_TAC[COMPACT_CLOSED_SUMS] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[VECTOR_ADD_SYM]);;

let COMPACT_CLOSED_DIFFERENCES = prove
 (`!s:real^N->bool t.
        compact s /\ closed t ==> closed {x - y | x IN s /\ y IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x - y | x:real^N IN s /\ y IN t} =
                {x + y | x IN s /\ y IN (IMAGE (--) t)}`
    (fun th -> ASM_SIMP_TAC[th; COMPACT_CLOSED_SUMS; CLOSED_NEGATIONS]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `(x:real^N = --y) <=> (y = --x)`] THEN
  SIMP_TAC[VECTOR_SUB; GSYM CONJ_ASSOC; UNWIND_THM2] THEN
  MESON_TAC[VECTOR_NEG_NEG]);;

let CLOSED_COMPACT_DIFFERENCES = prove
 (`!s:real^N->bool t.
        closed s /\ compact t ==> closed {x - y | x IN s /\ y IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x - y | x:real^N IN s /\ y IN t} =
                {x + y | x IN s /\ y IN (IMAGE (--) t)}`
    (fun th -> ASM_SIMP_TAC[th; CLOSED_COMPACT_SUMS; COMPACT_NEGATIONS]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `(x:real^N = --y) <=> (y = --x)`] THEN
  SIMP_TAC[VECTOR_SUB; GSYM CONJ_ASSOC; UNWIND_THM2] THEN
  MESON_TAC[VECTOR_NEG_NEG]);;

let CLOSED_TRANSLATION_EQ = prove
 (`!a s. closed (IMAGE (\x:real^N. a + x) s) <=> closed s`,
  REWRITE_TAC[closed] THEN GEOM_TRANSLATE_TAC[]);;

let CLOSED_TRANSLATION = prove
 (`!s a:real^N. closed s ==> closed (IMAGE (\x. a + x) s)`,
  REWRITE_TAC[CLOSED_TRANSLATION_EQ]);;

add_translation_invariants [CLOSED_TRANSLATION_EQ];;

let COMPLETE_TRANSLATION_EQ = prove
 (`!a s. complete(IMAGE (\x:real^N. a + x) s) <=> complete s`,
  REWRITE_TAC[COMPLETE_EQ_CLOSED; CLOSED_TRANSLATION_EQ]);;

add_translation_invariants [COMPLETE_TRANSLATION_EQ];;

let TRANSLATION_UNIV = prove
 (`!a. IMAGE (\x. a + x) (:real^N) = (:real^N)`,
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN GEOM_TRANSLATE_TAC[]);;

let TRANSLATION_DIFF = prove
 (`!s t:real^N->bool.
        IMAGE (\x. a + x) (s DIFF t) =
        (IMAGE (\x. a + x) s) DIFF (IMAGE (\x. a + x) t)`,
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_IMAGE] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `x:real^N = a + y <=> y = x - a`] THEN
  REWRITE_TAC[UNWIND_THM2]);;

let CLOSURE_TRANSLATION = prove
 (`!a s. closure(IMAGE (\x:real^N. a + x) s) = IMAGE (\x. a + x) (closure s)`,
  REWRITE_TAC[CLOSURE_INTERIOR] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [CLOSURE_TRANSLATION];;

let FRONTIER_TRANSLATION = prove
 (`!a s. frontier(IMAGE (\x:real^N. a + x) s) = IMAGE (\x. a + x) (frontier s)`,
  REWRITE_TAC[frontier] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [FRONTIER_TRANSLATION];;

(* ------------------------------------------------------------------------- *)
(* Separation between points and sets.                                       *)
(* ------------------------------------------------------------------------- *)

let SEPARATE_POINT_CLOSED = prove
 (`!s a:real^N.
        closed s /\ ~(a IN s)
        ==> ?d. &0 < d /\ !x. x IN s ==> d <= dist(a,x)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`] DISTANCE_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `b:real^N` THEN
  STRIP_TAC THEN EXISTS_TAC `dist(a:real^N,b)` THEN
  ASM_MESON_TAC[DIST_POS_LT]);;

let SEPARATE_COMPACT_CLOSED = prove
 (`!s t:real^N->bool.
        compact s /\ closed t /\ s INTER t = {}
        ==> ?d. &0 < d /\ !x y. x IN s /\ y IN t ==> d <= dist(x,y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{x - y:real^N | x IN s /\ y IN t}`; `vec 0:real^N`]
                SEPARATE_POINT_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_CLOSED_DIFFERENCES; IN_ELIM_THM] THEN
  REWRITE_TAC[VECTOR_ARITH `vec 0 = x - y <=> x = y`] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
  MESON_TAC[NORM_ARITH `dist(vec 0,x - y) = dist(x,y)`]);;

let SEPARATE_CLOSED_COMPACT = prove
 (`!s t:real^N->bool.
        closed s /\ compact t /\ s INTER t = {}
        ==> ?d. &0 < d /\ !x y. x IN s /\ y IN t ==> d <= dist(x,y)`,
  ONCE_REWRITE_TAC[DIST_SYM; INTER_COMM] THEN
  MESON_TAC[SEPARATE_COMPACT_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* A cute way of denoting open and closed intervals using overloading.       *)
(* ------------------------------------------------------------------------- *)

let open_interval = new_definition
  `open_interval(a:real^N,b:real^N) =
        {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                        ==> a$i < x$i /\ x$i < b$i}`;;

let closed_interval = new_definition
  `closed_interval(l:(real^N#real^N)list) =
         {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                         ==> FST(HD l)$i <= x$i /\ x$i <= SND(HD l)$i}`;;

make_overloadable "interval" `:A`;;

overload_interface("interval",`open_interval`);;
overload_interface("interval",`closed_interval`);;

let interval = prove
 (`(interval (a,b) = {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                                     ==> a$i < x$i /\ x$i < b$i}) /\
   (interval [a,b] = {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                                     ==> a$i <= x$i /\ x$i <= b$i})`,
  REWRITE_TAC[open_interval; closed_interval; HD; FST; SND]);;

let IN_INTERVAL = prove
 (`(!x:real^N.
        x IN interval (a,b) <=>
                !i. 1 <= i /\ i <= dimindex(:N)
                    ==> a$i < x$i /\ x$i < b$i) /\
   (!x:real^N.
        x IN interval [a,b] <=>
                !i. 1 <= i /\ i <= dimindex(:N)
                    ==> a$i <= x$i /\ x$i <= b$i)`,
  REWRITE_TAC[interval; IN_ELIM_THM]);;

let IN_INTERVAL_REFLECT = prove
 (`(!a b x. (--x) IN interval[--b,--a] <=> x IN interval[a,b]) /\
   (!a b x. (--x) IN interval(--b,--a) <=> x IN interval(a,b))`,
  SIMP_TAC[IN_INTERVAL; REAL_LT_NEG2; REAL_LE_NEG2; VECTOR_NEG_COMPONENT] THEN
  MESON_TAC[]);;

let INTERVAL_EQ_EMPTY = prove
 (`((interval [a:real^N,b] = {}) <=>
    ?i. 1 <= i /\ i <= dimindex(:N) /\ b$i < a$i) /\
   ((interval (a:real^N,b) = {}) <=>
    ?i. 1 <= i /\ i <= dimindex(:N) /\ b$i <= a$i)`,
  REWRITE_TAC[EXTENSION; IN_INTERVAL; NOT_IN_EMPTY] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; GSYM CONJ_ASSOC] THEN
  CONJ_TAC THEN EQ_TAC THENL
   [MESON_TAC[REAL_LE_REFL; REAL_NOT_LE];
    MESON_TAC[REAL_LE_TRANS; REAL_NOT_LE];
    ALL_TAC;
    MESON_TAC[REAL_LT_TRANS; REAL_NOT_LT]] THEN
  SUBGOAL_THEN `!a b. ?c. a < b ==> a < c /\ c < b`
  (MP_TAC o REWRITE_RULE[SKOLEM_THM]) THENL
   [MESON_TAC[REAL_LT_BETWEEN]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `mid:real->real->real`) THEN
  DISCH_THEN(MP_TAC o SPEC
   `(lambda i. mid ((a:real^N)$i) ((b:real^N)$i)):real^N`) THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(a /\ b ==> ~c)`] THEN
  SIMP_TAC[LAMBDA_BETA] THEN ASM_MESON_TAC[REAL_NOT_LT]);;

let INTERVAL_NE_EMPTY = prove
 (`(~(interval [a:real^N,b] = {}) <=>
    !i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= b$i) /\
   (~(interval (a:real^N,b) = {}) <=>
    !i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i)`,
  REWRITE_TAC[INTERVAL_EQ_EMPTY] THEN MESON_TAC[REAL_NOT_LE]);;

let SUBSET_INTERVAL_IMP = prove
 (`((!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)
    ==> interval[c,d] SUBSET interval[a:real^N,b]) /\
   ((!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < c$i /\ d$i < b$i)
    ==> interval[c,d] SUBSET interval(a:real^N,b)) /\
   ((!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)
    ==> interval(c,d) SUBSET interval[a:real^N,b]) /\
   ((!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)
    ==> interval(c,d) SUBSET interval(a:real^N,b))`,
  REWRITE_TAC[SUBSET; IN_INTERVAL] THEN REPEAT CONJ_TAC THEN
  DISCH_TAC THEN GEN_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
  GEN_TAC THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let INTERVAL_SING = prove
 (`interval[a,a] = {a} /\ interval(a,a) = {}`,
  REWRITE_TAC[EXTENSION; IN_SING; NOT_IN_EMPTY; IN_INTERVAL] THEN
  REWRITE_TAC[REAL_LE_ANTISYM; REAL_LT_ANTISYM; CART_EQ; EQ_SYM_EQ] THEN
  MESON_TAC[DIMINDEX_GE_1; LE_REFL]);;

let SUBSET_INTERVAL = prove
 (`(interval[c,d] SUBSET interval[a:real^N,b] <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> c$i <= d$i)
        ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)) /\
   (interval[c,d] SUBSET interval(a:real^N,b) <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> c$i <= d$i)
        ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < c$i /\ d$i < b$i)) /\
   (interval(c,d) SUBSET interval[a:real^N,b] <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> c$i < d$i)
        ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)) /\
   (interval(c,d) SUBSET interval(a:real^N,b) <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> c$i < d$i)
        ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i))`,
  let lemma = prove
   (`(!x:real^N. (!i. 1 <= i /\ i <= dimindex(:N) ==> Q i (x$i))
                 ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> R i (x$i)))
     ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> ?y. Q i y)
         ==> !i y. 1 <= i /\ i <= dimindex(:N) /\ Q i y ==> R i y`,
    DISCH_TAC THEN REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:num->real` STRIP_ASSUME_TAC) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
     SPEC `(lambda j. if j = i then y else f j):real^N`) THEN
    SIMP_TAC[LAMBDA_BETA] THEN ASM_MESON_TAC[]) in
  REPEAT STRIP_TAC THEN
  (MATCH_MP_TAC(TAUT
    `(~q ==> p) /\ (q ==> (p <=> r)) ==> (p <=> q ==> r)`) THEN
   CONJ_TAC THENL
    [DISCH_TAC THEN MATCH_MP_TAC(SET_RULE `s = {} ==> s SUBSET t`) THEN
     REWRITE_TAC[INTERVAL_EQ_EMPTY] THEN ASM_MESON_TAC[REAL_NOT_LT];
     ALL_TAC] THEN
   DISCH_TAC THEN EQ_TAC THEN REWRITE_TAC[SUBSET_INTERVAL_IMP] THEN
   REWRITE_TAC[SUBSET; IN_INTERVAL] THEN
   DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN ANTS_TAC THENL
    [ASM_MESON_TAC[REAL_LT_BETWEEN; REAL_LE_BETWEEN]; ALL_TAC] THEN
   MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
   DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
   ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC)
  THENL
   [ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL];
    ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL];
    ALL_TAC; ALL_TAC] THEN
  (REPEAT STRIP_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC
      `((c:real^N)$i + min ((a:real^N)$i) ((d:real^N)$i)) / &2`) THEN
     POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
     FIRST_X_ASSUM(MP_TAC o SPEC
      `(max ((b:real^N)$i) ((c:real^N)$i) + (d:real^N)$i) / &2`) THEN
     POP_ASSUM MP_TAC THEN REAL_ARITH_TAC]));;

let DISJOINT_INTERVAL = prove
 (`!a b c d:real^N.
        (interval[a,b] INTER interval[c,d] = {} <=>
          ?i. 1 <= i /\ i <= dimindex(:N) /\
              (b$i < a$i \/ d$i < c$i \/ b$i < c$i \/ d$i < a$i)) /\
        (interval[a,b] INTER interval(c,d) = {} <=>
          ?i. 1 <= i /\ i <= dimindex(:N) /\
              (b$i < a$i \/ d$i <= c$i \/ b$i <= c$i \/ d$i <= a$i)) /\
        (interval(a,b) INTER interval[c,d] = {} <=>
          ?i. 1 <= i /\ i <= dimindex(:N) /\
              (b$i <= a$i \/ d$i < c$i \/ b$i <= c$i \/ d$i <= a$i)) /\
        (interval(a,b) INTER interval(c,d) = {} <=>
          ?i. 1 <= i /\ i <= dimindex(:N) /\
              (b$i <= a$i \/ d$i <= c$i \/ b$i <= c$i \/ d$i <= a$i))`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_INTERVAL; NOT_IN_EMPTY] THEN
  REWRITE_TAC[AND_FORALL_THM; NOT_FORALL_THM] THEN
  REWRITE_TAC[TAUT `~((p ==> q) /\ (p ==> r)) <=> p /\ (~q \/ ~r)`] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
  (EQ_TAC THENL
    [DISCH_THEN(MP_TAC o SPEC
      `(lambda i. (max ((a:real^N)$i) ((c:real^N)$i) +
                   min ((b:real^N)$i) ((d:real^N)$i)) / &2):real^N`) THEN
     MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
     DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
     ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
     DISCH_THEN(fun th -> GEN_TAC THEN MP_TAC th) THEN
     MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN SIMP_TAC[] THEN
     REAL_ARITH_TAC]));;

let ENDS_IN_INTERVAL = prove
 (`(!a b. a IN interval[a,b] <=> ~(interval[a,b] = {})) /\
   (!a b. b IN interval[a,b] <=> ~(interval[a,b] = {})) /\
   (!a b. ~(a IN interval(a,b))) /\
   (!a b. ~(b IN interval(a,b)))`,
  REWRITE_TAC[IN_INTERVAL; INTERVAL_NE_EMPTY] THEN
  REWRITE_TAC[REAL_LE_REFL; REAL_LT_REFL] THEN
  MESON_TAC[DIMINDEX_GE_1; LE_REFL]);;

let ENDS_IN_UNIT_INTERVAL = prove
 (`vec 0 IN interval[vec 0,vec 1] /\
   vec 1 IN interval[vec 0,vec 1] /\
   ~(vec 0 IN interval(vec 0,vec 1)) /\
   ~(vec 1 IN interval(vec 0,vec 1))`,
  REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY; VEC_COMPONENT] THEN
  REWRITE_TAC[REAL_POS]);;

let INTER_INTERVAL = prove
 (`interval[a,b] INTER interval[c,d] =
        interval[(lambda i. max (a$i) (c$i)),(lambda i. min (b$i) (d$i))]`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_INTERVAL] THEN
  SIMP_TAC[LAMBDA_BETA; REAL_MAX_LE; REAL_LE_MIN] THEN MESON_TAC[]);;

let INTERVAL_OPEN_SUBSET_CLOSED = prove
 (`!a b. interval(a,b) SUBSET interval[a,b]`,
  REWRITE_TAC[SUBSET; IN_INTERVAL] THEN MESON_TAC[REAL_LT_IMP_LE]);;

let OPEN_INTERVAL_LEMMA = prove
 (`!a b x. a < x /\ x < b
           ==> ?d. &0 < d /\ !x'. abs(x' - x) < d ==> a < x' /\ x' < b`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `min (x - a) (b - x)` THEN REWRITE_TAC[REAL_LT_MIN] THEN
  ASM_REAL_ARITH_TAC);;

let OPEN_INTERVAL = prove
 (`!a:real^N b. open(interval (a,b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[open_def; interval; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= dimindex(:N)
                    ==> ?d. &0 < d /\
                            !x'. abs(x' - (x:real^N)$i) < d
                                 ==> (a:real^N)$i < x' /\ x' < (b:real^N)$i`
  MP_TAC THENL [ASM_SIMP_TAC[OPEN_INTERVAL_LEMMA]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `inf (IMAGE d (1..dimindex(:N)))` THEN
  SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; FINITE_NUMSEG;
           IMAGE_EQ_EMPTY; NOT_INSERT_EMPTY; NUMSEG_EMPTY;
           ARITH_RULE `n < 1 <=> (n = 0)`; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG; dist] THEN
  ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LET_TRANS; VECTOR_SUB_COMPONENT]);;

let CLOSED_INTERVAL = prove
 (`!a:real^N b. closed(interval [a,b])`,
  REWRITE_TAC[CLOSED_LIMPT; LIMPT_APPROACHABLE; IN_INTERVAL] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(a:real^N)$i - (x:real^N)$i`);
    FIRST_X_ASSUM(MP_TAC o SPEC `(x:real^N)$i - (b:real^N)$i`)] THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[dist; REAL_NOT_LT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((z - x :real^N)$i)` THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
  ASM_SIMP_TAC[REAL_ARITH `x < a /\ a <= z ==> a - x <= abs(z - x)`;
               REAL_ARITH `z <= b /\ b < x ==> x - b <= abs(z - x)`]);;

let INTERIOR_CLOSED_INTERVAL = prove
 (`!a:real^N b. interior(interval [a,b]) = interval (a,b)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN
    REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED; OPEN_INTERVAL]] THEN
  REWRITE_TAC[interior; SUBSET; IN_INTERVAL; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LT_LE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [open_def]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THENL
   [(let t = `x - (e / &2) % basis i :real^N` in
     DISCH_THEN(MP_TAC o SPEC t) THEN FIRST_X_ASSUM(MP_TAC o SPEC t));
    (let t = `x + (e / &2) % basis i :real^N` in
     DISCH_THEN(MP_TAC o SPEC t) THEN FIRST_X_ASSUM(MP_TAC o SPEC t))] THEN
  REWRITE_TAC[dist; VECTOR_ADD_SUB; VECTOR_ARITH `x - y - x = --y:real^N`] THEN
  ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; NORM_NEG; REAL_MUL_RID;
               REAL_ARITH `&0 < e ==> abs(e / &2) < e`] THEN
  MATCH_MP_TAC(TAUT `~b ==> (a ==> b) ==> ~a`) THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN EXISTS_TAC `i:num` THEN
  ASM_SIMP_TAC[DE_MORGAN_THM; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT] THENL
   [DISJ1_TAC THEN REWRITE_TAC[REAL_ARITH `a <= a - b <=> ~(&0 < b)`];
    DISJ2_TAC THEN REWRITE_TAC[REAL_ARITH `a + b <= a <=> ~(&0 < b)`]] THEN
  ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; basis; LAMBDA_BETA; REAL_MUL_RID] THEN
  ASM_REWRITE_TAC[REAL_HALF]);;

let BOUNDED_CLOSED_INTERVAL = prove
 (`!a b:real^N. bounded (interval [a,b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bounded; interval] THEN
  EXISTS_TAC `sum(1..dimindex(:N))
                 (\i. abs((a:real^N)$i) + abs((b:real^N)$i))` THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N)) (\i. abs((x:real^N)$i))` THEN
  REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_LE THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_ARITH
   `a <= x /\ x <= b ==> abs(x) <= abs(a) + abs(b)`]);;

let BOUNDED_INTERVAL = prove
 (`(!a b. bounded (interval [a,b])) /\ (!a b. bounded (interval (a,b)))`,
  MESON_TAC[BOUNDED_CLOSED_INTERVAL; BOUNDED_SUBSET;
            INTERVAL_OPEN_SUBSET_CLOSED]);;

let NOT_INTERVAL_UNIV = prove
 (`(!a b. ~(interval[a,b] = UNIV)) /\
   (!a b. ~(interval(a,b) = UNIV))`,
  MESON_TAC[BOUNDED_INTERVAL; NOT_BOUNDED_UNIV]);;

let COMPACT_INTERVAL = prove
 (`!a b. compact (interval [a,b])`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_INTERVAL; CLOSED_INTERVAL]);;

let OPEN_INTERVAL_MIDPOINT = prove
 (`!a b:real^N.
        ~(interval(a,b) = {}) ==> (inv(&2) % (a + b)) IN interval(a,b)`,
  REWRITE_TAC[INTERVAL_NE_EMPTY; IN_INTERVAL] THEN
  SIMP_TAC[VECTOR_MUL_COMPONENT; VECTOR_ADD_COMPONENT] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let OPEN_CLOSED_INTERVAL_CONVEX = prove
 (`!a b x y:real^N e.
        x IN interval(a,b) /\ y IN interval[a,b] /\ &0 < e /\ e <= &1
        ==> (e % x + (&1 - e) % y) IN interval(a,b)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(c /\ d ==> a /\ b ==> e) ==> a /\ b /\ c /\ d ==> e`) THEN
  STRIP_TAC THEN REWRITE_TAC[IN_INTERVAL; AND_FORALL_THM] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  MATCH_MP_TAC MONO_FORALL THEN
  GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBST1_TAC(REAL_ARITH `(a:real^N)$i = e * a$i + (&1 - e) * a$i`) THEN
  SUBST1_TAC(REAL_ARITH `(b:real^N)$i = e * b$i + (&1 - e) * b$i`) THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LTE_ADD2 THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LE_LMUL; REAL_SUB_LE]);;

let CLOSURE_OPEN_INTERVAL = prove
 (`!a b:real^N.
     ~(interval(a,b) = {}) ==> closure(interval(a,b)) = interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN
    REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED; CLOSED_INTERVAL];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; closure; IN_UNION] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~b ==> c) ==> b \/ c`) THEN DISCH_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; LIMPT_SEQUENTIAL] THEN
  ABBREV_TAC `(c:real^N) = inv(&2) % (a + b)` THEN
  EXISTS_TAC `\n. (x:real^N) + inv(&n + &1) % (c - x)` THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_DELETE] THEN
    REWRITE_TAC[VECTOR_ARITH `x + a = x <=> a = vec 0`] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0] THEN
    REWRITE_TAC[VECTOR_SUB_EQ; REAL_ARITH `~(&n + &1 = &0)`] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[OPEN_INTERVAL_MIDPOINT]] THEN
    REWRITE_TAC[VECTOR_ARITH `x + a % (y - x) = a % y + (&1 - a) % x`] THEN
    MATCH_MP_TAC OPEN_CLOSED_INTERVAL_CONVEX THEN
    CONJ_TAC THENL [ASM_MESON_TAC[OPEN_INTERVAL_MIDPOINT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [VECTOR_ARITH `x:real^N = x + &0 % (c - x)`] THEN
  MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC[LIM_CONST] THEN
  MATCH_MP_TAC LIM_VMUL THEN REWRITE_TAC[LIM_CONST] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; o_THM; DIST_LIFT; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `inv(&N)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN UNDISCH_TAC `N:num <= n` THEN
  UNDISCH_TAC `~(N = 0)` THEN
  REWRITE_TAC[GSYM LT_NZ; GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_LT] THEN
  REAL_ARITH_TAC);;

let BOUNDED_SUBSET_OPEN_INTERVAL_SYMMETRIC = prove
 (`!s:real^N->bool. bounded s ==> ?a. s SUBSET interval(--a,a)`,
  REWRITE_TAC[BOUNDED_POS; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `B:real`] THEN STRIP_TAC THEN
  EXISTS_TAC `(lambda i. B + &1):real^N` THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; REAL_BOUNDS_LT; VECTOR_NEG_COMPONENT] THEN
  ASM_MESON_TAC[COMPONENT_LE_NORM;
                REAL_ARITH `x <= y ==> a <= x ==> a < y + &1`]);;

let BOUNDED_SUBSET_OPEN_INTERVAL = prove
 (`!s:real^N->bool. bounded s ==> ?a b. s SUBSET interval(a,b)`,
  MESON_TAC[BOUNDED_SUBSET_OPEN_INTERVAL_SYMMETRIC]);;

let BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC = prove
 (`!s:real^N->bool. bounded s ==> ?a. s SUBSET interval[--a,a]`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_SUBSET_OPEN_INTERVAL_SYMMETRIC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  SIMP_TAC[IN_BALL; IN_INTERVAL; SUBSET; REAL_LT_IMP_LE]);;

let BOUNDED_SUBSET_CLOSED_INTERVAL = prove
 (`!s:real^N->bool. bounded s ==> ?a b. s SUBSET interval[a,b]`,
  MESON_TAC[BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC]);;

let FRONTIER_CLOSED_INTERVAL = prove
 (`!a b. frontier(interval[a,b]) = interval[a,b] DIFF interval(a,b)`,
  SIMP_TAC[frontier; INTERIOR_CLOSED_INTERVAL; CLOSURE_CLOSED;
           CLOSED_INTERVAL]);;

let FRONTIER_OPEN_INTERVAL = prove
 (`!a b. frontier(interval(a,b)) =
                if interval(a,b) = {} then {}
                else interval[a,b] DIFF interval(a,b)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FRONTIER_EMPTY] THEN
  ASM_SIMP_TAC[frontier; CLOSURE_OPEN_INTERVAL; INTERIOR_OPEN;
               OPEN_INTERVAL]);;

let INTER_INTERVAL_MIXED_EQ_EMPTY = prove
 (`!a b c d:real^N.
        ~(interval(c,d) = {})
        ==> (interval(a,b) INTER interval[c,d] = {} <=>
             interval(a,b) INTER interval(c,d) = {})`,
  SIMP_TAC[GSYM CLOSURE_OPEN_INTERVAL; OPEN_INTER_CLOSURE_EQ_EMPTY;
           OPEN_INTERVAL]);;

let INTERVAL_TRANSLATION = prove
 (`(!c a b. interval[c + a,c + b] = IMAGE (\x. c + x) (interval[a,b])) /\
   (!c a b. interval(c + a,c + b) = IMAGE (\x. c + x) (interval(a,b)))`,
  REWRITE_TAC[interval] THEN CONJ_TAC THEN GEOM_TRANSLATE_TAC[] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; REAL_LT_LADD; REAL_LE_LADD]);;

add_translation_invariants
 [CONJUNCT1 INTERVAL_TRANSLATION; CONJUNCT2 INTERVAL_TRANSLATION];;

let EMPTY_AS_INTERVAL = prove
 (`{} = interval[vec 1,vec 0]`,
  SIMP_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTERVAL; VEC_COMPONENT] THEN
  GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
  REWRITE_TAC[LE_REFL; DIMINDEX_GE_1] THEN REAL_ARITH_TAC);;

let UNIT_INTERVAL_NONEMPTY = prove
 (`~(interval[vec 0:real^N,vec 1] = {}) /\
   ~(interval(vec 0:real^N,vec 1) = {})`,
  SIMP_TAC[INTERVAL_NE_EMPTY; VEC_COMPONENT; REAL_LT_01; REAL_POS]);;

let IMAGE_STRETCH_INTERVAL = prove
 (`!a b:real^N m.
    IMAGE (\x. lambda k. m(k) * x$k) (interval[a,b]) =
        if interval[a,b] = {} then {}
        else interval[(lambda k. min (m(k) * a$k) (m(k) * b$k)):real^N,
                      (lambda k. max (m(k) * a$k) (m(k) * b$k))]`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[IMAGE_CLAUSES] THEN
  ASM_SIMP_TAC[EXTENSION; IN_IMAGE; CART_EQ; IN_INTERVAL; AND_FORALL_THM;
               TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`;
                LAMBDA_BETA; GSYM LAMBDA_SKOLEM] THEN
  X_GEN_TAC `x:real^N` THEN MATCH_MP_TAC(MESON[]
   `(!x. p x ==> (q x <=> r x))
    ==> ((!x. p x ==> q x) <=> (!x. p x ==> r x))`) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INTERVAL_NE_EMPTY]) THEN
  MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `k:num` THEN ASM_CASES_TAC `1 <= k /\ k <= dimindex(:N)` THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `(m:num->real) k = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MAX_ACI; REAL_MIN_ACI] THEN
    ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(m = &0) ==> (x = m * y <=> y = x / m)`] THEN
  REWRITE_TAC[UNWIND_THM2] THEN FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP
   (REAL_ARITH `~(z = &0) ==> &0 < z \/ &0 < --z`))
  THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM REAL_LE_NEG2] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_ARITH `--(max a b) = min (--a) (--b)`;
                REAL_ARITH `--(min a b) = max (--a) (--b)`; real_div;
                GSYM REAL_MUL_RNEG; GSYM REAL_INV_NEG] THEN
    REWRITE_TAC[GSYM real_div]] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
  ASM_SIMP_TAC[real_min; real_max; REAL_LE_LMUL_EQ; REAL_LE_RMUL_EQ] THEN
  REAL_ARITH_TAC);;

let INTERVAL_IMAGE_STRETCH_INTERVAL = prove
 (`!a b:real^N m. ?u v:real^N.
     IMAGE (\x. lambda k. m k * x$k) (interval[a,b]) = interval[u,v]`,
  REWRITE_TAC[IMAGE_STRETCH_INTERVAL] THEN MESON_TAC[EMPTY_AS_INTERVAL]);;

let CLOSED_INTERVAL_IMAGE_UNIT_INTERVAL = prove
 (`!a b:real^N.
        ~(interval[a,b] = {})
        ==> interval[a,b] = IMAGE (\x:real^N. a + x)
                                  (IMAGE (\x. (lambda i. (b$i - a$i) * x$i))
                                         (interval[vec 0:real^N,vec 1]))`,
  REWRITE_TAC[INTERVAL_NE_EMPTY] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[IMAGE_STRETCH_INTERVAL; UNIT_INTERVAL_NONEMPTY] THEN
  REWRITE_TAC[GSYM INTERVAL_TRANSLATION] THEN
  REWRITE_TAC[EXTENSION; IN_INTERVAL] THEN
  SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT; VEC_COMPONENT] THEN
  GEN_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID] THEN
  MATCH_MP_TAC(MESON[] `(!x. P x <=> Q x) ==> ((!x. P x) <=> (!x. Q x))`) THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `1 <= i /\ i <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some special cases for intervals in R^1.                                  *)
(* ------------------------------------------------------------------------- *)

let INTERVAL_CASES_1 = prove
 (`!x:real^1. x IN interval[a,b] ==> x IN interval(a,b) \/ (x = a) \/ (x = b)`,
  REWRITE_TAC[CART_EQ; IN_INTERVAL; FORALL_DIMINDEX_1] THEN REAL_ARITH_TAC);;

let IN_INTERVAL_1 = prove
 (`!a b x:real^1.
        (x IN interval[a,b] <=> drop a <= drop x /\ drop x <= drop b) /\
        (x IN interval(a,b) <=> drop a < drop x /\ drop x < drop b)`,
  REWRITE_TAC[IN_INTERVAL; drop; CONJ_ASSOC; DIMINDEX_1; LE_ANTISYM] THEN
  MESON_TAC[]);;

let INTERVAL_EQ_EMPTY_1 = prove
 (`!a b:real^1.
        (interval[a,b] = {} <=> drop b < drop a) /\
        (interval(a,b) = {} <=> drop b <= drop a)`,
  REWRITE_TAC[INTERVAL_EQ_EMPTY; drop; CONJ_ASSOC; DIMINDEX_1; LE_ANTISYM] THEN
  MESON_TAC[]);;

let SUBSET_INTERVAL_1 = prove
 (`!a b c d.
        (interval[a,b] SUBSET interval[c,d] <=>
                drop b < drop a \/
                drop c <= drop a /\ drop a <= drop b /\ drop b <= drop d) /\
        (interval[a,b] SUBSET interval(c,d) <=>
                drop b < drop a \/
                drop c < drop a /\ drop a <= drop b /\ drop b < drop d) /\
        (interval(a,b) SUBSET interval[c,d] <=>
                drop b <= drop a \/
                drop c <= drop a /\ drop a < drop b /\ drop b <= drop d) /\
        (interval(a,b) SUBSET interval(c,d) <=>
                drop b <= drop a \/
                drop c <= drop a /\ drop a < drop b /\ drop b <= drop d)`,
  REWRITE_TAC[SUBSET_INTERVAL; FORALL_1; DIMINDEX_1; drop] THEN
  REAL_ARITH_TAC);;

let EQ_INTERVAL_1 = prove
 (`!a b c d:real^1.
       (interval[a,b] = interval[c,d] <=>
          drop b < drop a /\ drop d < drop c \/
          drop a = drop c /\ drop b = drop d)`,
  REWRITE_TAC[SET_RULE `s = t <=> s SUBSET t /\ t SUBSET s`] THEN
  REWRITE_TAC[SUBSET_INTERVAL_1] THEN REAL_ARITH_TAC);;

let DISJOINT_INTERVAL_1 = prove
 (`!a b c d:real^1.
        (interval[a,b] INTER interval[c,d] = {} <=>
          drop b < drop a \/ drop d < drop c \/
          drop b < drop c \/ drop d < drop a) /\
        (interval[a,b] INTER interval(c,d) = {} <=>
          drop b < drop a \/ drop d <= drop c \/
          drop b <= drop c \/ drop d <= drop a) /\
        (interval(a,b) INTER interval[c,d] = {} <=>
          drop b <= drop a \/ drop d < drop c \/
          drop b <= drop c \/ drop d <= drop a) /\
        (interval(a,b) INTER interval(c,d) = {} <=>
          drop b <= drop a \/ drop d <= drop c \/
          drop b <= drop c \/ drop d <= drop a)`,
  REWRITE_TAC[DISJOINT_INTERVAL; CONJ_ASSOC; DIMINDEX_1; LE_ANTISYM;
              UNWIND_THM1; drop]);;

let OPEN_CLOSED_INTERVAL_1 = prove
 (`!a b:real^1. interval(a,b) = interval[a,b] DIFF {a,b}`,
  REWRITE_TAC[EXTENSION; IN_INTERVAL_1; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[GSYM DROP_EQ] THEN REAL_ARITH_TAC);;

let CLOSED_OPEN_INTERVAL_1 = prove
 (`!a b:real^1. drop a <= drop b ==> interval[a,b] = interval(a,b) UNION {a,b}`,
  REWRITE_TAC[EXTENSION; IN_INTERVAL_1; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[GSYM DROP_EQ] THEN REAL_ARITH_TAC);;

let BALL_1 = prove
 (`!x:real^1 r. cball(x,r) = interval[x - lift r,x + lift r] /\
                ball(x,r) = interval(x - lift r,x + lift r)`,
  REWRITE_TAC[EXTENSION; IN_BALL; IN_CBALL; IN_INTERVAL_1] THEN
  REWRITE_TAC[dist; NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP; DROP_ADD] THEN
  REAL_ARITH_TAC);;

let FINITE_INTERVAL_1 = prove
 (`(!a b. FINITE(interval[a,b]) <=> drop b <= drop a) /\
   (!a b. FINITE(interval(a,b)) <=> drop b <= drop a)`,
  REWRITE_TAC[OPEN_CLOSED_INTERVAL_1] THEN
  REWRITE_TAC[SET_RULE `s DIFF {a,b} = s DELETE a DELETE b`] THEN
  REWRITE_TAC[FINITE_DELETE] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `interval[a,b] = IMAGE lift {x | drop a <= x /\ x <= drop b}`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    CONJ_TAC THENL [MESON_TAC[LIFT_DROP]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP];
    SIMP_TAC[FINITE_IMAGE_INJ_EQ; LIFT_EQ; FINITE_REAL_INTERVAL]]);;

let BALL_INTERVAL = prove
 (`!x:real^1 e. ball(x,e) = interval(x - lift e,x + lift e)`,
  REWRITE_TAC[EXTENSION; IN_BALL; IN_INTERVAL_1; DIST_REAL] THEN
  REWRITE_TAC[GSYM drop; DROP_SUB; DROP_ADD; LIFT_DROP] THEN REAL_ARITH_TAC);;

let CBALL_INTERVAL = prove
 (`!x:real^1 e. cball(x,e) = interval[x - lift e,x + lift e]`,
  REWRITE_TAC[EXTENSION; IN_CBALL; IN_INTERVAL_1; DIST_REAL] THEN
  REWRITE_TAC[GSYM drop; DROP_SUB; DROP_ADD; LIFT_DROP] THEN REAL_ARITH_TAC);;

let BALL_INTERVAL_0 = prove
 (`!e. ball(vec 0:real^1,e) = interval(--lift e,lift e)`,
  GEN_TAC THEN REWRITE_TAC[BALL_INTERVAL] THEN AP_TERM_TAC THEN
  BINOP_TAC THEN VECTOR_ARITH_TAC);;

let CBALL_INTERVAL_0 = prove
 (`!e. cball(vec 0:real^1,e) = interval[--lift e,lift e]`,
  GEN_TAC THEN REWRITE_TAC[CBALL_INTERVAL] THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN BINOP_TAC THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some stuff for half-infinite intervals too; maybe I need a notation?      *)
(* ------------------------------------------------------------------------- *)

let CLOSED_INTERVAL_LEFT = prove
 (`!b:real^N.
     closed
        {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> x$i <= b$i}`,
  REWRITE_TAC[CLOSED_LIMPT; LIMPT_APPROACHABLE; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(x:real^N)$i - (b:real^N)$i`) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[dist; REAL_NOT_LT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((z - x :real^N)$i)` THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
  ASM_SIMP_TAC[REAL_ARITH `z <= b /\ b < x ==> x - b <= abs(z - x)`]);;

let CLOSED_INTERVAL_RIGHT = prove
 (`!a:real^N.
     closed
        {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= x$i}`,
  REWRITE_TAC[CLOSED_LIMPT; LIMPT_APPROACHABLE; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(a:real^N)$i - (x:real^N)$i`) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[dist; REAL_NOT_LT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((z - x :real^N)$i)` THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
  ASM_SIMP_TAC[REAL_ARITH `x < a /\ a <= z ==> a - x <= abs(z - x)`]);;

(* ------------------------------------------------------------------------- *)
(* Intervals in general, including infinite and mixtures of open and closed. *)
(* ------------------------------------------------------------------------- *)

let is_interval = new_definition
  `is_interval(s:real^N->bool) <=>
        !a b x. a IN s /\ b IN s /\
                (!i. 1 <= i /\ i <= dimindex(:N)
                     ==> (a$i <= x$i /\ x$i <= b$i) \/
                         (b$i <= x$i /\ x$i <= a$i))
                ==> x IN s`;;

let IS_INTERVAL_INTERVAL = prove
 (`!a:real^N b. is_interval(interval (a,b)) /\ is_interval(interval [a,b])`,
  REWRITE_TAC[is_interval; IN_INTERVAL] THEN
  MESON_TAC[REAL_LT_TRANS; REAL_LE_TRANS; REAL_LET_TRANS; REAL_LTE_TRANS]);;

let IS_INTERVAL_EMPTY = prove
 (`is_interval {}`,
  REWRITE_TAC[is_interval; NOT_IN_EMPTY]);;

let IS_INTERVAL_UNIV = prove
 (`is_interval(UNIV:real^N->bool)`,
  REWRITE_TAC[is_interval; IN_UNIV]);;

let IS_INTERVAL_TRANSLATION_EQ = prove
 (`!a:real^N s. is_interval(IMAGE (\x. a + x) s) <=> is_interval s`,
  REWRITE_TAC[is_interval] THEN GEOM_TRANSLATE_TAC[] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; REAL_LT_LADD; REAL_LE_LADD]);;

add_translation_invariants [IS_INTERVAL_TRANSLATION_EQ];;

let IS_INTERVAL_TRANSLATION = prove
 (`!s a:real^N. is_interval s ==> is_interval(IMAGE (\x. a + x) s)`,
  REWRITE_TAC[IS_INTERVAL_TRANSLATION_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Line segments, with same open/closed overloading as for intervals.        *)
(* ------------------------------------------------------------------------- *)

let closed_segment = define
 `closed_segment[a,b] = {(&1 - u) % a + u % b | &0 <= u /\ u <= &1}`;;

let open_segment = new_definition
 `open_segment(a,b) = closed_segment[a,b] DIFF {a,b}`;;

let OPEN_SEGMENT_ALT = prove
 (`!a b:real^N.
        ~(a = b)
        ==> open_segment(a,b) = {(&1 - u) % a + u % b | &0 < u /\ u < &1}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[open_segment; closed_segment] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `u:real` THEN ASM_CASES_TAC `x:real^N = (&1 - u) % a + u % b` THEN
  ASM_REWRITE_TAC[REAL_LE_LT;
    VECTOR_ARITH `(&1 - u) % a + u % b = a <=> u % (b - a) = vec 0`;
    VECTOR_ARITH `(&1 - u) % a + u % b = b <=> (&1 - u) % (b - a) = vec 0`;
    VECTOR_MUL_EQ_0; REAL_SUB_0; VECTOR_SUB_EQ] THEN
  REAL_ARITH_TAC);;

make_overloadable "segment" `:A`;;

overload_interface("segment",`open_segment`);;
overload_interface("segment",`closed_segment`);;

let segment = prove
 (`segment[a,b] = {(&1 - u) % a + u % b | &0 <= u /\ u <= &1} /\
   segment(a,b) = segment[a,b] DIFF {a,b}`,
  REWRITE_TAC[open_segment; closed_segment]);;

let SEGMENT_REFL = prove
 (`(!a. segment[a,a] = {a}) /\
   (!a. segment(a,a) = {})`,
  REWRITE_TAC[segment; VECTOR_ARITH `(&1 - u) % a + u % a = a`] THEN
  SET_TAC[REAL_POS]);;

let IN_SEGMENT = prove
 (`!a b x:real^N.
        (x IN segment[a,b] <=>
         ?u. &0 <= u /\ u <= &1 /\ x = (&1 - u) % a + u % b) /\
        (x IN segment(a,b) <=>
         ~(a = b) /\ ?u. &0 < u /\ u < &1 /\ x = (&1 - u) % a + u % b)`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[segment; IN_ELIM_THM; CONJ_ASSOC]; ALL_TAC] THEN
  ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; NOT_IN_EMPTY] THEN
  ASM_SIMP_TAC[OPEN_SEGMENT_ALT; IN_ELIM_THM; CONJ_ASSOC]);;

let SEGMENT_SYM = prove
 (`(!a b:real^N. segment[a,b] = segment[b,a]) /\
   (!a b:real^N. segment(a,b) = segment(b,a))`,
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
  SIMP_TAC[open_segment] THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[INSERT_AC]] THEN
  REWRITE_TAC[EXTENSION; IN_SEGMENT] THEN REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `u:real`) THEN EXISTS_TAC `&1 - u` THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN VECTOR_ARITH_TAC);;

let ENDS_IN_SEGMENT = prove
 (`!a b. a IN segment[a,b] /\ b IN segment[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[segment; IN_ELIM_THM] THENL
   [EXISTS_TAC `&0`; EXISTS_TAC `&1`] THEN
  (CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]));;

let ENDS_NOT_IN_SEGMENT = prove
 (`!a b. ~(a IN segment(a,b)) /\ ~(b IN segment(a,b))`,
  REWRITE_TAC[open_segment] THEN SET_TAC[]);;

let SEGMENT_CLOSED_OPEN = prove
 (`!a b. segment[a,b] = segment(a,b) UNION {a,b}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[open_segment] THEN MATCH_MP_TAC(SET_RULE
   `a IN s /\ b IN s ==> s = (s DIFF {a,b}) UNION {a,b}`) THEN
  REWRITE_TAC[ENDS_IN_SEGMENT]);;

let MIDPOINT_IN_SEGMENT = prove
 (`(!a b:real^N. midpoint(a,b) IN segment[a,b]) /\
   (!a b:real^N. midpoint(a,b) IN segment(a,b) <=> ~(a = b))`,
  REWRITE_TAC[IN_SEGMENT] THEN REPEAT STRIP_TAC THENL
   [ALL_TAC; ASM_CASES_TAC `a:real^N = b` THEN ASM_REWRITE_TAC[]] THEN
  EXISTS_TAC `&1 / &2` THEN REWRITE_TAC[midpoint] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC);;

let BETWEEN_IN_SEGMENT = prove
 (`!x a b:real^N. between x (a,b) <=> x IN segment[a,b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[between] THEN
  ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; IN_SING] THENL [NORM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[segment; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(ASSUME_TAC o SYM) THEN
    EXISTS_TAC `dist(a:real^N,x) / dist(a,b)` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; DIST_POS_LT] THEN CONJ_TAC
    THENL [FIRST_ASSUM(SUBST1_TAC o SYM) THEN NORM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN EXISTS_TAC `dist(a:real^N,b)` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; VECTOR_ADD_LDISTRIB; REAL_SUB_LDISTRIB;
                 REAL_DIV_LMUL; DIST_EQ_0] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DIST_TRIANGLE_EQ] o SYM) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[dist; REAL_ARITH `(a + b) * &1 - a = b`] THEN
    VECTOR_ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[dist] THEN
    REWRITE_TAC[VECTOR_ARITH `a - ((&1 - u) % a + u % b) = u % (a - b)`;
                VECTOR_ARITH `((&1 - u) % a + u % b) - b = (&1 - u) % (a - b)`;
                NORM_MUL; GSYM REAL_ADD_LDISTRIB] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD]);;

let SEGMENT_1 = prove
 (`(!a b. segment[a,b] =
          if drop a <= drop b then interval[a,b] else interval[b,a]) /\
   (!a b. segment(a,b) =
          if drop a <= drop b then interval(a,b) else interval(b,a))`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[open_segment] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY;
              EXTENSION; GSYM BETWEEN_IN_SEGMENT; between; IN_INTERVAL_1] THEN
  REWRITE_TAC[GSYM DROP_EQ; DIST_REAL; GSYM drop] THEN ASM_REAL_ARITH_TAC);;

let SEGMENT_TRANSLATION = prove
 (`(!c a b. segment[c + a,c + b] = IMAGE (\x. c + x) (segment[a,b])) /\
   (!c a b. segment(c + a,c + b) = IMAGE (\x. c + x) (segment(a,b)))`,
  REWRITE_TAC[EXTENSION; IN_SEGMENT; IN_IMAGE] THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - u) % (c + a) + u % (c + b) =
                            c + (&1 - u) % a + u % b`] THEN
  REWRITE_TAC[VECTOR_ARITH `c + a:real^N = c + b <=> a = b`] THEN
  MESON_TAC[]);;

add_translation_invariants
 [CONJUNCT1 SEGMENT_TRANSLATION; CONJUNCT2 SEGMENT_TRANSLATION];;

let CLOSED_SEGMENT_LINEAR_IMAGE = prove
 (`!f a b. linear f
           ==> segment[f a,f b] = IMAGE f (segment[a,b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SEGMENT] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_CMUL th)]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_ADD th)]) THEN
  MESON_TAC[]);;

add_linear_invariants [CLOSED_SEGMENT_LINEAR_IMAGE];;

let OPEN_SEGMENT_LINEAR_IMAGE = prove
 (`!f:real^M->real^N a b.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> segment(f a,f b) = IMAGE f (segment(a,b))`,
  REWRITE_TAC[open_segment] THEN GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [OPEN_SEGMENT_LINEAR_IMAGE];;

let IN_OPEN_SEGMENT = prove
 (`!a b x:real^N.
        x IN segment(a,b) <=> x IN segment[a,b] /\ ~(x = a) /\ ~(x = b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[open_segment; IN_DIFF] THEN SET_TAC[]);;

let IN_OPEN_SEGMENT_ALT = prove
 (`!a b x:real^N.
        x IN segment(a,b) <=>
        x IN segment[a,b] /\ ~(x = a) /\ ~(x = b) /\ ~(a = b)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; IN_SING; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[IN_OPEN_SEGMENT]);;

let COLLINEAR_DIST_IN_CLOSED_SEGMENT = prove
 (`!a b x. collinear {x,a,b} /\
           dist(x,a) <= dist(a,b) /\ dist(x,b) <= dist(a,b)
           ==> x IN segment[a,b]`,
  REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; COLLINEAR_DIST_BETWEEN]);;

let COLLINEAR_DIST_IN_OPEN_SEGMENT = prove
 (`!a b x. collinear {x,a,b} /\
           dist(x,a) < dist(a,b) /\ dist(x,b) < dist(a,b)
           ==> x IN segment(a,b)`,
  REWRITE_TAC[IN_OPEN_SEGMENT] THEN
  MESON_TAC[COLLINEAR_DIST_IN_CLOSED_SEGMENT; REAL_LT_LE; DIST_SYM]);;

let SEGMENT_SCALAR_MULTIPLE = prove
 (`(!a b v. segment[a % v,b % v] =
            {x % v:real^N | a <= x /\ x <= b \/ b <= x /\ x <= a}) /\
   (!a b v. ~(v = vec 0)
            ==> segment(a % v,b % v) =
                {x % v:real^N | a < x /\ x < b \/ b < x /\ x < a})`,
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN REPEAT STRIP_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(SPECL [`a % basis 1:real^1`; `b % basis 1:real^1`]
     (CONJUNCT1 SEGMENT_1)) THEN
    REWRITE_TAC[segment; VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB] THEN
    REWRITE_TAC[SET_RULE `{f x % b | p x} = IMAGE (\a. a % b) {f x | p x}`] THEN
    DISCH_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `IMAGE drop`) THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF; DROP_CMUL] THEN
    SIMP_TAC[drop; BASIS_COMPONENT; DIMINDEX_GE_1; LE_REFL] THEN
    REWRITE_TAC[REAL_MUL_RID; IMAGE_ID] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    CONJ_TAC THENL [MESON_TAC[LIFT_DROP]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_LIFT; LIFT_DROP] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    SIMP_TAC[drop; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_GE_1;
             LE_REFL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[open_segment] THEN
    ASM_SIMP_TAC[VECTOR_MUL_RCANCEL; SET_RULE
     `(!x y. x % v = y % v <=> x = y)
      ==> {x % v | P x} DIFF {a % v,b % v} =
          {x % v | P x /\ ~(x = a) /\ ~(x = b)}`] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

let FINITE_INTER_COLLINEAR_OPEN_SEGMENTS = prove
 (`!a b c d:real^N.
        collinear{a,b,c}
        ==> (FINITE(segment(a,b) INTER segment(c,d)) <=>
             segment(a,b) INTER segment(c,d) = {})`,
  REPEAT GEN_TAC THEN ABBREV_TAC `m:real^N = b - a` THEN POP_ASSUM MP_TAC THEN
  GEOM_NORMALIZE_TAC `m:real^N` THEN
  SIMP_TAC[VECTOR_SUB_EQ; SEGMENT_REFL; INTER_EMPTY; FINITE_EMPTY] THEN
  X_GEN_TAC `m:real^N` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN POP_ASSUM MP_TAC THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN GEOM_BASIS_MULTIPLE_TAC 1 `b:real^N` THEN
  X_GEN_TAC `b:real` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  SIMP_TAC[VECTOR_SUB_RZERO; NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
  ASM_REWRITE_TAC[real_abs; REAL_MUL_RID] THEN DISCH_THEN SUBST_ALL_TAC THEN
  POP_ASSUM(K ALL_TAC) THEN
  ASM_CASES_TAC `collinear{vec 0:real^N,&1 % basis 1,y}` THENL
   [POP_ASSUM MP_TAC THEN
    SIMP_TAC[COLLINEAR_LEMMA_ALT; BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL] THEN
    MATCH_MP_TAC(TAUT
     `~a /\ (b ==> c ==> d) ==> a \/ b ==> a \/ c ==> d`) THEN
    CONJ_TAC THENL
     [SIMP_TAC[VECTOR_MUL_LID; BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC `b:real` THEN DISCH_THEN SUBST_ALL_TAC THEN
    X_GEN_TAC `a:real` THEN DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RID] THEN
    SUBST1_TAC(VECTOR_ARITH `vec 0:real^N = &0 % basis 1`) THEN
    SIMP_TAC[SEGMENT_SCALAR_MULTIPLE; BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL;
     VECTOR_MUL_RCANCEL; IMAGE_EQ_EMPTY; FINITE_IMAGE_INJ_EQ; SET_RULE
     `(!x y. x % v = y % v <=> x = y)
      ==> {x % v | P x} INTER {x % v | Q x} =
          IMAGE (\x. x % v) {x | P x /\ Q x}`] THEN
    REWRITE_TAC[REAL_ARITH `(&0 < x /\ x < &1 \/ &1 < x /\ x < &0) /\
                            (b < x /\ x < a \/ a < x /\ x < b) <=>
                       max (&0) (min a b) < x /\ x < min (&1) (max a b)`] THEN
    SIMP_TAC[FINITE_REAL_INTERVAL; EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    SIMP_TAC[GSYM REAL_LT_BETWEEN; GSYM NOT_EXISTS_THM] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN ASM_CASES_TAC
     `segment(vec 0:real^N,&1 % basis 1) INTER segment (x,y) = {}` THEN
    ASM_REWRITE_TAC[FINITE_EMPTY] THEN DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[open_segment; IN_DIFF; NOT_IN_EMPTY;
                DE_MORGAN_THM; IN_INTER; IN_INSERT] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~collinear{vec 0:real^N,&1 % basis 1, y}` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_MUL_LID]) THEN
    REWRITE_TAC[VECTOR_MUL_LID] THEN
    MATCH_MP_TAC COLLINEAR_SUBSET THEN
    EXISTS_TAC `{p,x:real^N, y, vec 0, basis 1}` THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    MP_TAC(ISPECL [`{y:real^N,vec 0,basis 1}`; `p:real^N`; `x:real^N`]
        COLLINEAR_TRIPLES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `{p,x,y} = {x,p,y}`] THEN
      MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN
      ASM_REWRITE_TAC[BETWEEN_IN_SEGMENT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM COLLINEAR_4_3] THEN
    ONCE_REWRITE_TAC[SET_RULE `{p,x,z,w} = {w,z,p,x}`] THEN
    SIMP_TAC[COLLINEAR_4_3; BASIS_NONZERO; DIMINDEX_GE_1; ARITH] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR o
        GEN_REWRITE_RULE I [GSYM BETWEEN_IN_SEGMENT])) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN SIMP_TAC[INSERT_AC]]);;

(* ------------------------------------------------------------------------- *)
(* Closure of halfspaces and hyperplanes.                                    *)
(* ------------------------------------------------------------------------- *)

let LIM_LIFT_DOT = prove
 (`!f:real^M->real^N a.
        (f --> l) net ==> ((lift o (\y. a dot f(y))) --> lift(a dot l)) net`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = vec 0:real^N` THENL
   [ASM_REWRITE_TAC[DOT_LZERO; LIFT_NUM; o_DEF; LIM_CONST]; ALL_TAC] THEN
  REWRITE_TAC[LIM] THEN MATCH_MP_TAC MONO_OR THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / norm(a:real^N)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; REAL_LT_RDIV_EQ] THEN
  REWRITE_TAC[dist; o_THM; GSYM LIFT_SUB; GSYM DOT_RSUB; NORM_LIFT] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN
  MESON_TAC[NORM_CAUCHY_SCHWARZ_ABS; REAL_MUL_SYM; REAL_LET_TRANS]);;

let CONTINUOUS_AT_LIFT_DOT = prove
 (`!a:real^N x. (lift o (\y. a dot y)) continuous at x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_AT; o_THM] THEN
  MATCH_MP_TAC LIM_LIFT_DOT THEN REWRITE_TAC[LIM_AT] THEN MESON_TAC[]);;

let CONTINUOUS_ON_LIFT_DOT = prove
 (`!s x. (lift o (\y. a dot y)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON; CONTINUOUS_AT_LIFT_DOT]);;

let CLOSED_HALFSPACE_LE = prove
 (`!a:real^N b. closed {x | a dot x <= b}`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `a:real^N`] CONTINUOUS_ON_LIFT_DOT) THEN
  REWRITE_TAC[CONTINUOUS_ON_CLOSED; GSYM CLOSED_IN; SUBTOPOLOGY_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE lift {r | ?x:real^N. (a dot x = r) /\ r <= b}`) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN
    REWRITE_TAC[o_DEF] THEN MESON_TAC[LIFT_DROP]] THEN
  REWRITE_TAC[CLOSED_IN_CLOSED] THEN
  EXISTS_TAC `{x | !i. 1 <= i /\ i <= dimindex(:1)
                       ==> (x:real^1)$i <= (lift b)$i}` THEN
  REWRITE_TAC[CLOSED_INTERVAL_LEFT] THEN
  SIMP_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_ELIM_THM; IN_INTER; IN_INTERVAL;
    VEC_COMPONENT; DIMINDEX_1; LAMBDA_BETA; o_THM] THEN
  SIMP_TAC[ARITH_RULE `1 <= i /\ i <= 1 <=> (i = 1)`] THEN
  REWRITE_TAC[GSYM drop; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  MESON_TAC[LIFT_DROP]);;

let CLOSED_HALFSPACE_GE = prove
 (`!a:real^N b. closed {x | a dot x >= b}`,
  REWRITE_TAC[REAL_ARITH `a >= b <=> --a <= --b`] THEN
  REWRITE_TAC[GSYM DOT_LNEG; CLOSED_HALFSPACE_LE]);;

let CLOSED_HYPERPLANE = prove
 (`!a b. closed {x | a dot x = b}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  REWRITE_TAC[REAL_ARITH `b <= a dot x <=> a dot x >= b`] THEN
  REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
  SIMP_TAC[CLOSED_INTER; CLOSED_HALFSPACE_LE; CLOSED_HALFSPACE_GE]);;

let CLOSED_STANDARD_HYPERPLANE = prove
 (`!k a. closed {x:real^N | x$k = a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CLOSED_HYPERPLANE) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let CLOSED_HALFSPACE_COMPONENT_LE = prove
 (`!a k. closed {x:real^N | x$k <= a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CLOSED_HALFSPACE_LE) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let CLOSED_HALFSPACE_COMPONENT_GE = prove
 (`!a k. closed {x:real^N | x$k >= a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CLOSED_HALFSPACE_GE) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

(* ------------------------------------------------------------------------- *)
(* Openness of halfspaces.                                                   *)
(* ------------------------------------------------------------------------- *)

let OPEN_HALFSPACE_LT = prove
 (`!a b. open {x | a dot x < b}`,
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  REWRITE_TAC[SET_RULE `{x | ~p x} = UNIV DIFF {x | p x}`] THEN
  REWRITE_TAC[GSYM closed; GSYM real_ge; CLOSED_HALFSPACE_GE]);;

let OPEN_HALFSPACE_COMPONENT_LT = prove
 (`!a k. open {x:real^N | x$k < a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] OPEN_HALFSPACE_LT) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let OPEN_HALFSPACE_GT = prove
 (`!a b. open {x | a dot x > b}`,
  REWRITE_TAC[REAL_ARITH `x > y <=> ~(x <= y)`] THEN
  REWRITE_TAC[SET_RULE `{x | ~p x} = UNIV DIFF {x | p x}`] THEN
  REWRITE_TAC[GSYM closed; CLOSED_HALFSPACE_LE]);;

let OPEN_HALFSPACE_COMPONENT_GT = prove
 (`!a k. open {x:real^N | x$k > a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] OPEN_HALFSPACE_GT) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let OPEN_POSITIVE_MULTIPLES = prove
 (`!s:real^N->bool. open s ==> open {c % x | &0 < c /\ x IN s}`,
  REWRITE_TAC[open_def; FORALL_IN_GSPEC] THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c * e:real` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv(c) % y:real^N`) THEN ANTS_TAC THENL
   [SUBGOAL_THEN `x:real^N = inv c % c % x` SUBST1_TAC THENL
     [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID;
                   REAL_LT_IMP_NZ];
      ASM_SIMP_TAC[DIST_MUL; real_abs; REAL_LT_INV_EQ; REAL_LT_IMP_LE] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `inv c * x:real = x / c`] THEN
      ASM_MESON_TAC[REAL_LT_LDIV_EQ; REAL_MUL_SYM]];
    DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `c:real` THEN EXISTS_TAC `inv(c) % y:real^N` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
    VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Closures and interiors of halfspaces.                                     *)
(* ------------------------------------------------------------------------- *)

let INTERIOR_HALFSPACE_LE = prove
 (`!a:real^N b.
        ~(a = vec 0) ==> interior {x | a dot x <= b} = {x | a dot x < b}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERIOR_UNIQUE THEN
  SIMP_TAC[OPEN_HALFSPACE_LT; SUBSET; IN_ELIM_THM; REAL_LT_IMP_LE] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[REAL_LT_LE] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[SUBSET; IN_CBALL] THEN
  DISCH_THEN(MP_TAC o SPEC `x + e / norm(a) % a:real^N`) THEN
  REWRITE_TAC[NORM_ARITH `dist(x:real^N,x + y) = norm y`] THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; REAL_DIV_RMUL;
               NORM_EQ_0; REAL_ARITH `&0 < x ==> abs x <= x`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC  `x + e / norm(a) % a:real^N`) THEN
  ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < e ==> ~(b + e <= b)`) THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; NORM_POS_LT; DOT_POS_LT]);;

let INTERIOR_HALFSPACE_GE = prove
 (`!a:real^N b.
        ~(a = vec 0) ==> interior {x | a dot x >= b} = {x | a dot x > b}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a >= b <=> --a <= --b`;
                   REAL_ARITH `a > b <=> --a < --b`] THEN
  ASM_SIMP_TAC[GSYM DOT_LNEG; INTERIOR_HALFSPACE_LE; VECTOR_NEG_EQ_0]);;

let INTERIOR_HALFSPACE_COMPONENT_LE = prove
 (`!a k. interior {x:real^N | x$k <= a} = {x | x$k < a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] INTERIOR_HALFSPACE_LE) THEN
  ASM_SIMP_TAC[DOT_BASIS; BASIS_NONZERO]);;

let INTERIOR_HALFSPACE_COMPONENT_GE = prove
 (`!a k. interior {x:real^N | x$k >= a} = {x | x$k > a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] INTERIOR_HALFSPACE_GE) THEN
  ASM_SIMP_TAC[DOT_BASIS; BASIS_NONZERO]);;

let CLOSURE_HALFSPACE_LT = prove
 (`!a:real^N b.
        ~(a = vec 0) ==> closure {x | a dot x < b} = {x | a dot x <= b}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSURE_INTERIOR] THEN
  REWRITE_TAC[SET_RULE `UNIV DIFF {x | P x} = {x | ~P x}`] THEN
  ASM_SIMP_TAC[REAL_ARITH `~(x < b) <=> x >= b`; INTERIOR_HALFSPACE_GE] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let CLOSURE_HALFSPACE_GT = prove
 (`!a:real^N b.
        ~(a = vec 0) ==> closure {x | a dot x > b} = {x | a dot x >= b}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a >= b <=> --a <= --b`;
                   REAL_ARITH `a > b <=> --a < --b`] THEN
  ASM_SIMP_TAC[GSYM DOT_LNEG; CLOSURE_HALFSPACE_LT; VECTOR_NEG_EQ_0]);;

let CLOSURE_HALFSPACE_COMPONENT_LT = prove
 (`!a k. closure {x:real^N | x$k < a} = {x | x$k <= a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CLOSURE_HALFSPACE_LT) THEN
  ASM_SIMP_TAC[DOT_BASIS; BASIS_NONZERO]);;

let CLOSURE_HALFSPACE_COMPONENT_GT = prove
 (`!a k. closure {x:real^N | x$k > a} = {x | x$k >= a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] CLOSURE_HALFSPACE_GT) THEN
  ASM_SIMP_TAC[DOT_BASIS; BASIS_NONZERO]);;

let INTERIOR_HYPERPLANE = prove
 (`!a b. ~(a = vec 0) ==> interior {x | a dot x = b} = {}`,
  REWRITE_TAC[REAL_ARITH `x = y <=> x <= y /\ x >= y`] THEN
  REWRITE_TAC[SET_RULE `{x | p x /\ q x} = {x | p x} INTER {x | q x}`] THEN
  REWRITE_TAC[INTERIOR_INTER] THEN
  ASM_SIMP_TAC[INTERIOR_HALFSPACE_LE; INTERIOR_HALFSPACE_GE] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  REAL_ARITH_TAC);;

let INTERIOR_STANDARD_HYPERPLANE = prove
 (`!k a. interior {x:real^N | x$k = a} = {}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !x:real^N. x$k = x$i`
  CHOOSE_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis i:real^N`; `a:real`] INTERIOR_HYPERPLANE) THEN
  ASM_SIMP_TAC[DOT_BASIS; BASIS_NONZERO]);;

let EMPTY_INTERIOR_LOWDIM = prove
 (`!s:real^N->bool. dim(s) < dimindex(:N) ==> interior s = {}`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LOWDIM_SUBSET_HYPERPLANE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(SET_RULE
   `!t u. s SUBSET t /\ t SUBSET u /\ u = {} ==> s = {}`) THEN
  MAP_EVERY EXISTS_TAC
   [`interior(span(s):real^N->bool)`;
    `interior({x:real^N | a dot x = &0})`] THEN
  ASM_SIMP_TAC[SUBSET_INTERIOR; SPAN_INC; INTERIOR_HYPERPLANE]);;

(* ------------------------------------------------------------------------- *)
(* Unboundedness of halfspaces.                                              *)
(* ------------------------------------------------------------------------- *)

let UNBOUNDED_HALFSPACE_COMPONENT_LE = prove
 (`!a k. ~bounded {x:real^N | x$k <= a}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?i. 1 <= i /\ i <= dimindex(:N) /\ !z:real^N. z$k = z$i`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[bounded; FORALL_IN_GSPEC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` MP_TAC) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  EXISTS_TAC `--(&1 + max (abs B) (abs a)) % basis i:real^N` THEN
  ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; BASIS_COMPONENT;
               VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let UNBOUNDED_HALFSPACE_COMPONENT_GE = prove
 (`!a k. ~bounded {x:real^N | x$k >= a}`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_NEGATIONS) THEN
  MP_TAC(SPECL [`--a:real`; `k:num`] UNBOUNDED_HALFSPACE_COMPONENT_LE) THEN
  REWRITE_TAC[CONTRAPOS_THM] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN CONJ_TAC THENL
   [MESON_TAC[VECTOR_NEG_NEG];
    REWRITE_TAC[IN_ELIM_THM; VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC]);;

let UNBOUNDED_HALFSPACE_COMPONENT_LT = prove
 (`!a k. ~bounded {x:real^N | x$k < a}`,
  ONCE_REWRITE_TAC[GSYM BOUNDED_CLOSURE_EQ] THEN
  REWRITE_TAC[CLOSURE_HALFSPACE_COMPONENT_LT;
              UNBOUNDED_HALFSPACE_COMPONENT_LE]);;

let UNBOUNDED_HALFSPACE_COMPONENT_GT = prove
 (`!a k. ~bounded {x:real^N | x$k > a}`,
  ONCE_REWRITE_TAC[GSYM BOUNDED_CLOSURE_EQ] THEN
  REWRITE_TAC[CLOSURE_HALFSPACE_COMPONENT_GT;
              UNBOUNDED_HALFSPACE_COMPONENT_GE]);;

let BOUNDED_HALFSPACE_LE = prove
 (`!a:real^N b. bounded {x | a dot x <= b} <=> a = vec 0 /\ b < &0`,
  GEOM_BASIS_MULTIPLE_TAC 1 `a:real^N` THEN
  SIMP_TAC[DOT_LMUL; DOT_BASIS; VECTOR_MUL_EQ_0; DIMINDEX_GE_1; LE_REFL;
           BASIS_NONZERO] THEN
  X_GEN_TAC `a:real` THEN ASM_CASES_TAC `a = &0` THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN X_GEN_TAC `b:real` THENL
   [REWRITE_TAC[REAL_MUL_LZERO; DOT_LZERO; GSYM REAL_NOT_LE] THEN
    ASM_CASES_TAC `&0 <= b` THEN
    ASM_REWRITE_TAC[BOUNDED_EMPTY; NOT_BOUNDED_UNIV;
                    SET_RULE `{x | T} = UNIV`; EMPTY_GSPEC];
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_LE;
                 UNBOUNDED_HALFSPACE_COMPONENT_LE]]);;

let BOUNDED_HALFSPACE_GE = prove
 (`!a:real^N b. bounded {x | a dot x >= b} <=> a = vec 0 /\ &0 < b`,
  REWRITE_TAC[REAL_ARITH `a >= b <=> --a <= --b`] THEN
  REWRITE_TAC[GSYM DOT_LNEG; BOUNDED_HALFSPACE_LE] THEN
  REWRITE_TAC[VECTOR_NEG_EQ_0; REAL_ARITH `--b < &0 <=> &0 < b`]);;

let BOUNDED_HALFSPACE_LT = prove
 (`!a:real^N b. bounded {x | a dot x < b} <=> a = vec 0 /\ b <= &0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[DOT_LZERO; GSYM REAL_NOT_LE] THEN ASM_CASES_TAC `b <= &0` THEN
    ASM_REWRITE_TAC[BOUNDED_EMPTY; NOT_BOUNDED_UNIV;
                    SET_RULE `{x | T} = UNIV`; EMPTY_GSPEC];
    ONCE_REWRITE_TAC[GSYM BOUNDED_CLOSURE_EQ] THEN
    ASM_SIMP_TAC[CLOSURE_HALFSPACE_LT; BOUNDED_HALFSPACE_LE]]);;

let BOUNDED_HALFSPACE_GT = prove
 (`!a:real^N b. bounded {x | a dot x > b} <=> a = vec 0 /\ &0 <= b`,
  REWRITE_TAC[REAL_ARITH `a > b <=> --a < --b`] THEN
  REWRITE_TAC[GSYM DOT_LNEG; BOUNDED_HALFSPACE_LT] THEN
  REWRITE_TAC[VECTOR_NEG_EQ_0; REAL_ARITH `--b <= &0 <=> &0 <= b`]);;

(* ------------------------------------------------------------------------- *)
(* Limit component bounds.                                                   *)
(* ------------------------------------------------------------------------- *)

let LIM_COMPONENT_UBOUND = prove
 (`!net:(A)net f (l:real^N) b k.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. (f x)$k <= b) net /\
        1 <= k /\ k <= dimindex(:N)
        ==> l$k <= b`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`net:(A)net`; `f:A->real^N`; `{y:real^N | basis k dot y <= b}`; `l:real^N`]
   LIM_IN_CLOSED_SET) THEN
  ASM_SIMP_TAC[CLOSED_HALFSPACE_LE; IN_ELIM_THM; DOT_BASIS]);;

let LIM_COMPONENT_LBOUND = prove
 (`!net:(A)net f (l:real^N) b k.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. b <= (f x)$k) net /\
        1 <= k /\ k <= dimindex(:N)
        ==> b <= l$k`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`net:(A)net`; `f:A->real^N`; `{y:real^N | b <= basis k dot y}`; `l:real^N`]
   LIM_IN_CLOSED_SET) THEN
  ASM_SIMP_TAC[REWRITE_RULE[real_ge] CLOSED_HALFSPACE_GE;
               IN_ELIM_THM; DOT_BASIS]);;

let LIM_COMPONENT_EQ = prove
 (`!net f:A->real^N i l b.
        (f --> l) net /\ 1 <= i /\ i <= dimindex(:N) /\
        ~(trivial_limit net) /\ eventually (\x. f(x)$i = b) net
        ==> l$i = b`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; EVENTUALLY_AND] THEN
  MESON_TAC[LIM_COMPONENT_UBOUND; LIM_COMPONENT_LBOUND]);;

let LIM_COMPONENT_LE = prove
 (`!net:(A)net f:A->real^N g:A->real^N k l m.
         ~(trivial_limit net) /\ (f --> l) net /\ (g --> m) net /\
        eventually (\x. (f x)$k <= (g x)$k) net /\
        1 <= k /\ k <= dimindex(:N)
        ==> l$k <= m$k`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT; LIM_COMPONENT_LBOUND] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> b /\ a ==> c ==> d`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_SUB) THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; LIM_COMPONENT_LBOUND]);;

let LIM_DROP_LE = prove
 (`!net:(A)net f g k l m.
         ~(trivial_limit net) /\ (f --> l) net /\ (g --> m) net /\
        eventually (\x. drop(f x) <= drop(g x)) net
        ==> drop l <= drop m`,
  REWRITE_TAC[drop] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `net:(A)net` LIM_COMPONENT_LE) THEN
  MAP_EVERY EXISTS_TAC [`f:A->real^1`; `g:A->real^1`] THEN
  ASM_REWRITE_TAC[DIMINDEX_1; LE_REFL]);;

let LIM_DROP_UBOUND = prove
 (`!net f:A->real^1 l b.
        (f --> l) net /\
        ~(trivial_limit net) /\ eventually (\x. drop(f x) <= b) net
        ==> drop l <= b`,
  SIMP_TAC[drop] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LIM_COMPONENT_UBOUND THEN
  REWRITE_TAC[LE_REFL; DIMINDEX_1] THEN ASM_MESON_TAC[]);;

let LIM_DROP_LBOUND = prove
 (`!net f:A->real^1 l b.
        (f --> l) net /\
        ~(trivial_limit net) /\ eventually (\x. b <= drop(f x)) net
        ==> b <= drop l`,
  SIMP_TAC[drop] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LIM_COMPONENT_LBOUND THEN
  REWRITE_TAC[LE_REFL; DIMINDEX_1] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Also extending closed bounds to closures.                                 *)
(* ------------------------------------------------------------------------- *)

let IMAGE_CLOSURE_SUBSET = prove
 (`!f (s:real^N->bool) (t:real^M->bool).
      f continuous_on closure s /\ closed t /\ IMAGE f s SUBSET t
      ==> IMAGE f (closure s) SUBSET t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `closure s SUBSET {x | (f:real^N->real^M) x IN t}` MP_TAC
  THENL [MATCH_MP_TAC SUBSET_TRANS; SET_TAC []]  THEN
  EXISTS_TAC `{x | x IN closure s /\ (f:real^N->real^M) x IN t}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC CLOSURE_MINIMAL; SET_TAC[]] THEN
  ASM_SIMP_TAC[CONTINUOUS_CLOSED_PREIMAGE; CLOSED_CLOSURE] THEN
  MP_TAC (ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]);;

let CONTINUOUS_ON_CLOSURE_NORM_LE = prove
 (`!f:real^N->real^M s x b.
      f continuous_on (closure s) /\
      (!y. y IN s ==> norm(f y) <= b) /\
      x IN (closure s)
      ==> norm(f x) <= b`,
  REWRITE_TAC [GSYM IN_CBALL_0] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^M) (closure s) SUBSET cball(vec 0,b)`
    MP_TAC THENL
  [MATCH_MP_TAC IMAGE_CLOSURE_SUBSET; ASM SET_TAC []] THEN
  ASM_REWRITE_TAC [CLOSED_CBALL] THEN ASM SET_TAC []);;

let CONTINUOUS_ON_CLOSURE_COMPONENT_LE = prove
 (`!f:real^N->real^M s x b k.
      f continuous_on (closure s) /\
      (!y. y IN s ==> (f y)$k <= b) /\
      x IN (closure s)
      ==> (f x)$k <= b`,
  REWRITE_TAC [GSYM IN_CBALL_0] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^M) (closure s) SUBSET {x | x$k <= b}`
  MP_TAC THENL
   [MATCH_MP_TAC IMAGE_CLOSURE_SUBSET; ASM SET_TAC []] THEN
  ASM_REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE] THEN ASM SET_TAC[]);;

let CONTINUOUS_ON_CLOSURE_COMPONENT_GE = prove
 (`!f:real^N->real^M s x b k.
      f continuous_on (closure s) /\
      (!y. y IN s ==> b <= (f y)$k) /\
      x IN (closure s)
      ==> b <= (f x)$k`,
  REWRITE_TAC [GSYM IN_CBALL_0] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^M) (closure s) SUBSET {x | x$k >= b}`
  MP_TAC THENL
   [MATCH_MP_TAC IMAGE_CLOSURE_SUBSET; ASM SET_TAC [real_ge]] THEN
  ASM_REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE] THEN ASM SET_TAC[real_ge]);;

(* ------------------------------------------------------------------------- *)
(* Limits relative to a union.                                               *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHIN_UNION = prove
 (`(f --> l) (at x within (s UNION t)) <=>
   (f --> l) (at x within s) /\ (f --> l) (at x within t)`,
  REWRITE_TAC[LIM_WITHIN; IN_UNION; AND_FORALL_THM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_THEN
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `d:real`) (X_CHOOSE_TAC `k:real`)) THEN
  EXISTS_TAC `min d k` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  ASM_MESON_TAC[]);;

let CONTINUOUS_ON_UNION = prove
 (`!f s t. closed s /\ closed t /\ f continuous_on s /\ f continuous_on t
           ==> f continuous_on (s UNION t)`,
  REWRITE_TAC[CONTINUOUS_ON; CLOSED_LIMPT; IN_UNION; LIM_WITHIN_UNION] THEN
  MESON_TAC[LIM; TRIVIAL_LIMIT_WITHIN]);;

let CONTINUOUS_ON_CASES = prove
 (`!P f g:real^M->real^N s t.
        closed s /\ closed t /\ f continuous_on s /\ g continuous_on t /\
        (!x. x IN s /\ ~P x \/ x IN t /\ P x ==> f x = g x)
        ==> (\x. if P x then f x else g x) continuous_on (s UNION t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_UNION THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THENL
   [EXISTS_TAC `f:real^M->real^N`; EXISTS_TAC `g:real^M->real^N`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Componentwise limits and continuity.                                      *)
(* ------------------------------------------------------------------------- *)

let LIM_COMPONENTWISE_LIFT = prove
 (`!net f:A->real^N.
        (f --> l) net <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> ((\x. lift((f x)$i)) --> lift(l$i)) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tendsto] THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X_GEN_TAC `e:real` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    GEN_TAC THEN REWRITE_TAC[dist] THEN MATCH_MP_TAC(REAL_ARITH
     `y <= x ==> x < e ==> y < e`) THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM; GSYM LIFT_SUB; NORM_LIFT;
                 GSYM VECTOR_SUB_COMPONENT];
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_FORALL_THM] THEN
    ONCE_REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; RIGHT_FORALL_IMP_THM] THEN
    SIMP_TAC[FORALL_EVENTUALLY; FINITE_NUMSEG; NUMSEG_EMPTY;
             GSYM NOT_LE; DIMINDEX_GE_1] THEN
    REWRITE_TAC[DIST_LIFT; GSYM VECTOR_SUB_COMPONENT] THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &(dimindex(:N))`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `x:A` THEN SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; dist] THEN
    DISCH_TAC THEN W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC(REAL_ARITH `s < e ==> n <= s ==> n < e`) THEN
    MATCH_MP_TAC SUM_BOUND_LT_GEN THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1;
                 CARD_NUMSEG_1; GSYM IN_NUMSEG]]);;

let CONTINUOUS_COMPONENTWISE_LIFT = prove
 (`!net f:A->real^N.
        f continuous net <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift((f x)$i)) continuous net`,
  REWRITE_TAC[continuous; GSYM LIM_COMPONENTWISE_LIFT]);;

let CONTINUOUS_ON_COMPONENTWISE_LIFT = prove
 (`!f:real^M->real^N s.
        f continuous_on s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift((f x)$i)) continuous_on s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [CONTINUOUS_COMPONENTWISE_LIFT] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some more convenient intermediate-value theorem formulations.             *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_IVT_HYPERPLANE = prove
 (`!s x y:real^N a b.
        connected s /\
        x IN s /\ y IN s /\ a dot x <= b /\ b <= a dot y
        ==> ?z. z IN s /\ a dot z = b`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connected]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPECL
   [`{x:real^N | a dot x < b}`; `{x:real^N | a dot x > b}`]) THEN
  REWRITE_TAC[OPEN_HALFSPACE_LT; OPEN_HALFSPACE_GT] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; NOT_IN_EMPTY; SUBSET;
              IN_UNION; REAL_LT_LE; real_gt] THEN
  ASM_MESON_TAC[REAL_LE_TOTAL; REAL_LE_ANTISYM]);;

let CONNECTED_IVT_COMPONENT = prove
 (`!s x y:real^N a k.
        connected s /\ x IN s /\ y IN s /\
        1 <= k /\ k <= dimindex(:N) /\ x$k <= a /\ a <= y$k
        ==> ?z. z IN s /\ z$k = a`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`s:real^N->bool`; `x:real^N`; `y:real^N`; `(basis k):real^N`;
    `a:real`] CONNECTED_IVT_HYPERPLANE) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

(* ------------------------------------------------------------------------- *)
(* Also more convenient formulations of monotone convergence.                *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_INCREASING_CONVERGENT = prove
 (`!s:num->real^1.
        bounded {s n | n IN (:num)} /\ (!n. drop(s n) <= drop(s(SUC n)))
        ==> ?l. (s --> l) sequentially`,
  GEN_TAC THEN
  REWRITE_TAC[bounded; IN_ELIM_THM; ABS_DROP; LIM_SEQUENTIALLY; dist;
              DROP_SUB; IN_UNIV; GSYM EXISTS_DROP] THEN
  DISCH_TAC THEN MATCH_MP_TAC CONVERGENT_BOUNDED_MONOTONE THEN
  REWRITE_TAC[LEFT_EXISTS_AND_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISJ1_TAC THEN MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
  ASM_REWRITE_TAC[REAL_LE_TRANS; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Basic homeomorphism definitions.                                          *)
(* ------------------------------------------------------------------------- *)

let homeomorphism = new_definition
  `homeomorphism (s,t) (f,g) <=>
     (!x. x IN s ==> (g(f(x)) = x)) /\ (IMAGE f s = t) /\ f continuous_on s /\
     (!y. y IN t ==> (f(g(y)) = y)) /\ (IMAGE g t = s) /\ g continuous_on t`;;

parse_as_infix("homeomorphic",(12,"right"));;

let homeomorphic = new_definition
  `s homeomorphic t <=> ?f g. homeomorphism (s,t) (f,g)`;;

let HOMEOMORPHIC_REFL = prove
 (`!s:real^N->bool. s homeomorphic s`,
  GEN_TAC THEN REWRITE_TAC[homeomorphic; homeomorphism] THEN
  REPEAT(EXISTS_TAC `\x:real^N. x`) THEN
  REWRITE_TAC[CONTINUOUS_ON_ID; EXTENSION; IN_IMAGE; UNWIND_THM1]);;

let HOMEOMORPHIC_SYM = prove
 (`!s t. s homeomorphic t <=> t homeomorphic s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic; homeomorphism] THEN
  GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN CONV_TAC TAUT);;

let HOMEOMORPHIC_TRANS = prove
 (`!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homeomorphic t /\ t homeomorphic u ==> s homeomorphic u`,
  REWRITE_TAC[homeomorphic; homeomorphism; LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`s:real^M->bool`; `t:real^N->bool`; `u:real^P->bool`;
    `f1:real^M->real^N`; `g1:real^N->real^M`;
    `f2:real^N->real^P`; `g2:real^P->real^N`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `(f2:real^N->real^P) o (f1:real^M->real^N)` THEN
  EXISTS_TAC `(g1:real^N->real^M) o (g2:real^P->real^N)` THEN
  ASM_SIMP_TAC[o_THM; IMAGE_o; CONTINUOUS_ON_COMPOSE] THEN
  ASM_MESON_TAC[IN_IMAGE]);;

let HOMEOMORPHIC_EMPTY = prove
 (`(!s. (s:real^N->bool) homeomorphic ({}:real^M->bool) <=> s = {}) /\
   (!s. ({}:real^M->bool) homeomorphic (s:real^N->bool) <=> s = {})`,
  REWRITE_TAC[homeomorphic; homeomorphism; IMAGE_CLAUSES; IMAGE_EQ_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[continuous_on; NOT_IN_EMPTY]);;

let HOMEOMORPHIC_MINIMAL = prove
 (`!s t. s homeomorphic t <=>
            ?f g. (!x. x IN s ==> f(x) IN t /\ (g(f(x)) = x)) /\
                  (!y. y IN t ==> g(y) IN s /\ (f(g(y)) = y)) /\
                  f continuous_on s /\ g continuous_on t`,
  REWRITE_TAC[homeomorphic; homeomorphism; EXTENSION; IN_IMAGE] THEN
  REPEAT GEN_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN MESON_TAC[]);;

let HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (IMAGE f s) homeomorphic s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_LEFT_INVERSE]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `f:real^M->real^N` THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; FORALL_IN_IMAGE; FUN_IN_IMAGE] THEN
  ASM_SIMP_TAC[continuous_on; IMP_CONJ; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_BOUNDED_BELOW_POS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e * B:real` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  X_GEN_TAC `y:real^M` THEN ASM_SIMP_TAC[dist; GSYM LINEAR_SUB] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b < x ==> a < x`) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ]);;

let HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_LEFT_EQ = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ((IMAGE f s) homeomorphic t <=> s homeomorphic t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o SPEC `s:real^M->bool` o
    MATCH_MP HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF) THEN
  EQ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_SYM]);
    POP_ASSUM MP_TAC] THEN
  REWRITE_TAC[IMP_IMP; HOMEOMORPHIC_TRANS]);;

let HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_RIGHT_EQ = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (s homeomorphic (IMAGE f t) <=> s homeomorphic t)`,
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  REWRITE_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_LEFT_EQ]);;

add_linear_invariants
  [HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_LEFT_EQ;
   HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_RIGHT_EQ];;

let HOMEOMORPHIC_TRANSLATION_SELF = prove
 (`!a:real^N s. (IMAGE (\x. a + x) s) homeomorphic s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
  EXISTS_TAC `\x:real^N. x - a` THEN
  EXISTS_TAC `\x:real^N. a + x` THEN
  SIMP_TAC[FORALL_IN_IMAGE; CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID;
           CONTINUOUS_ON_CONST; CONTINUOUS_ON_ADD; VECTOR_ADD_SUB] THEN
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

let HOMEOMORPHIC_TRANSLATION_LEFT_EQ = prove
 (`!a:real^N s t.
      (IMAGE (\x. a + x) s) homeomorphic t <=> s homeomorphic t`,
  MESON_TAC[HOMEOMORPHIC_TRANSLATION_SELF;
            HOMEOMORPHIC_SYM; HOMEOMORPHIC_TRANS]);;

let HOMEOMORPHIC_TRANSLATION_RIGHT_EQ = prove
 (`!a:real^N s t.
      s homeomorphic (IMAGE (\x. a + x) t) <=> s homeomorphic t`,
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION_LEFT_EQ]);;

add_translation_invariants
  [HOMEOMORPHIC_TRANSLATION_LEFT_EQ;
   HOMEOMORPHIC_TRANSLATION_RIGHT_EQ];;

(* ------------------------------------------------------------------------- *)
(* Relatively weak hypotheses if a set is compact.                           *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHISM_COMPACT = prove
 (`!s f t. compact s /\ f continuous_on s /\ (IMAGE f s = t) /\
           (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> ?g. homeomorphism(s,t) (f,g)`,
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE] THEN REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM_SIMP_TAC[EXTENSION; homeomorphism] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_MESON_TAC[CONTINUOUS_ON_INVERSE; IN_IMAGE]);;

let HOMEOMORPHIC_COMPACT = prove
 (`!s f t. compact s /\ f continuous_on s /\ (IMAGE f s = t) /\
           (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> s homeomorphic t`,
  REWRITE_TAC[homeomorphic] THEN MESON_TAC[HOMEOMORPHISM_COMPACT]);;

(* ------------------------------------------------------------------------- *)
(* Preservation of topological properties.                                   *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_COMPACTNESS = prove
 (`!s t. s homeomorphic t ==> (compact s <=> compact t)`,
  REWRITE_TAC[homeomorphic; homeomorphism] THEN
  MESON_TAC[COMPACT_CONTINUOUS_IMAGE]);;

let HOMEOMORPHIC_CONNECTEDNESS = prove
 (`!s t. s homeomorphic t ==> (connected s <=> connected t)`,
  REWRITE_TAC[homeomorphic; homeomorphism] THEN
  MESON_TAC[CONNECTED_CONTINUOUS_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Results on translation, scaling etc.                                      *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_SCALING = prove
 (`!s:real^N->bool c. ~(c = &0) ==> s homeomorphic (IMAGE (\x. c % x) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
  MAP_EVERY EXISTS_TAC [`\x:real^N. c % x`; `\x:real^N. inv(c) % x`] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RINV] THEN
  SIMP_TAC[VECTOR_MUL_LID; IN_IMAGE; REAL_MUL_LID] THEN MESON_TAC[]);;

let HOMEOMORPHIC_TRANSLATION = prove
 (`!s a:real^N. s homeomorphic (IMAGE (\x. a + x) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
  MAP_EVERY EXISTS_TAC [`\x:real^N. a +  x`; `\x:real^N. --a + x`] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
  SIMP_TAC[VECTOR_ADD_ASSOC; VECTOR_ADD_LINV; VECTOR_ADD_RINV;
           FORALL_IN_IMAGE; VECTOR_ADD_LID] THEN
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

let HOMEOMORPHIC_AFFINITY = prove
 (`!s a:real^N c. ~(c = &0) ==> s homeomorphic (IMAGE (\x. a + c % x) s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN
  EXISTS_TAC `IMAGE (\x:real^N. c % x) s` THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_SCALING] THEN
  SUBGOAL_THEN `(\x:real^N. a + c % x) = (\x. a + x) o (\x. c % x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o; HOMEOMORPHIC_TRANSLATION]);;

let HOMEOMORPHIC_BALLS,HOMEOMORPHIC_CBALLS = (CONJ_PAIR o prove)
 (`(!a:real^N b:real^N d e.
      &0 < d /\ &0 < e ==> ball(a,d) homeomorphic ball(b,e)) /\
   (!a:real^N b:real^N d e.
      &0 < d /\ &0 < e ==> cball(a,d) homeomorphic cball(b,e))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
  EXISTS_TAC `\x:real^N. b + (e / d) % (x - a)` THEN
  EXISTS_TAC `\x:real^N. a + (d / e) % (x - b)` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CMUL;
               CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID; IN_BALL; IN_CBALL] THEN
  REWRITE_TAC[dist; VECTOR_ARITH `a - (a + b) = --b:real^N`; NORM_NEG] THEN
  REWRITE_TAC[real_div; VECTOR_ARITH
   `a + d % ((b + e % (x - a)) - b) = (&1 - d * e) % a + (d * e) % x`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
    `(e * d') * (d * e') = (d * d') * (e * e')`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID; REAL_SUB_REFL] THEN
  REWRITE_TAC[NORM_MUL; VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID] THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ARITH
   `&0 < x ==> (abs x = x)`] THEN
  GEN_REWRITE_TAC(BINOP_CONV o BINDER_CONV o funpow 2 RAND_CONV)
        [GSYM REAL_MUL_RID] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `(a * b) * c = (a * c) * b`] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ; GSYM real_div; REAL_LE_LDIV_EQ; REAL_MUL_LID;
    GSYM REAL_MUL_ASSOC; REAL_LT_LMUL_EQ; REAL_LT_LDIV_EQ; NORM_SUB]);;

(* ------------------------------------------------------------------------- *)
(* Homeomorphisms between open intervals in real^1 and then in real^N.       *)
(* Could prove similar things for closed intervals, but they drop out of     *)
(* later stuff in "convex.ml" even more easily.                              *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_OPEN_INTERVALS_1 = prove
 (`!a b c d.
        drop a < drop b /\ drop c < drop d
        ==> interval(a,b) homeomorphic interval(c,d)`,
  SUBGOAL_THEN
   `!a b. drop a < drop b
          ==> interval(vec 0:real^1,vec 1) homeomorphic interval(a,b)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
    EXISTS_TAC `(\x. a + drop x % (b - a)):real^1->real^1` THEN
    EXISTS_TAC `(\x. inv(drop b - drop a) % (x - a)):real^1->real^1` THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ] THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL; DROP_NEG; DROP_VEC; DROP_SUB] THEN
    REWRITE_TAC[REAL_ARITH `inv b * a:real = a / b`] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_SUB_LT;
       REAL_LT_ADDR; REAL_EQ_LDIV_EQ; REAL_DIV_RMUL; REAL_LT_IMP_NZ;
       REAL_LT_MUL; REAL_MUL_LZERO; REAL_ADD_SUB; REAL_LT_RMUL_EQ;
       REAL_ARITH `a + x < b <=> x < &1 * (b - a)`] THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
      REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID];
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]];
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`a:real^1`; `b:real^1`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^1`; `d:real^1`]) THEN
    ASM_REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [HOMEOMORPHIC_SYM] THEN
    REWRITE_TAC[HOMEOMORPHIC_TRANS]]);;

let HOMEOMORPHIC_OPEN_INTERVAL_UNIV_1 = prove
 (`!a b. drop a < drop b ==> interval(a,b) homeomorphic (:real^1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real^1`; `b:real^1`; `--vec 1:real^1`; `vec 1:real^1`]
        HOMEOMORPHIC_OPEN_INTERVALS_1) THEN
  ASM_REWRITE_TAC[DROP_VEC; DROP_NEG] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMEOMORPHIC_TRANS) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[HOMEOMORPHIC_MINIMAL; IN_UNIV] THEN
  EXISTS_TAC `\x:real^1. inv(&1 - norm x) % x` THEN
  EXISTS_TAC `\y. if &0 <= drop y then inv(&1 + drop y) % y
                  else inv(&1 - drop y) % y` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1] THEN
    REWRITE_TAC[DROP_NEG; DROP_VEC; DROP_CMUL; NORM_REAL; GSYM drop] THEN
    SIMP_TAC[REAL_LE_MUL_EQ; REAL_LT_INV_EQ; REAL_LE_MUL_EQ; REAL_ARITH
     `--a < x /\ x < a ==> &0 < a - abs x`] THEN
    SIMP_TAC[real_abs; VECTOR_MUL_ASSOC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    X_GEN_TAC `y:real^1` THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; DROP_VEC; REAL_BOUNDS_LT] THEN
    REWRITE_TAC[DROP_CMUL; REAL_ABS_MUL; REAL_ABS_INV] THEN
    REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div)] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= x ==> &0 < abs(&1 + x)`;
                 REAL_ARITH `~(&0 <= x) ==> &0 < abs(&1 - x)`] THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[NORM_REAL; VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM drop; DROP_CMUL; REAL_ABS_MUL] THEN
    ASM_REWRITE_TAC[real_abs; REAL_LE_INV_EQ] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> &0 <= &1 + x`;
                 REAL_ARITH `~(&0 <= x) ==> &0 <= &1 - x`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
    DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
    REWRITE_TAC[CONTINUOUS_AT_ID] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_INV THEN
    REWRITE_TAC[NETLIMIT_AT; o_DEF; LIFT_SUB; LIFT_DROP] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_SUB THEN
      SIMP_TAC[CONTINUOUS_CONST; REWRITE_RULE[o_DEF] CONTINUOUS_AT_LIFT_NORM];
      REWRITE_TAC[NORM_REAL; GSYM drop] THEN ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `(:real^1) = {x | x$1 >= &0} UNION {x | x$1 <= &0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_UNION; IN_ELIM_THM; IN_UNIV] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
      REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE; CLOSED_HALFSPACE_COMPONENT_GE;
                  IN_ELIM_THM] THEN
      REWRITE_TAC[GSYM drop; REAL_NOT_LE; real_ge; REAL_LET_ANTISYM] THEN
      SIMP_TAC[REAL_LE_ANTISYM; REAL_SUB_RZERO; REAL_ADD_RID] THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_ELIM_THM; real_ge] THEN
      DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
      REWRITE_TAC[CONTINUOUS_AT_ID] THEN
      ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_INV THEN
      REWRITE_TAC[NETLIMIT_AT; o_DEF; LIFT_ADD; LIFT_SUB; LIFT_DROP] THEN
      ASM_SIMP_TAC[CONTINUOUS_ADD; CONTINUOUS_AT_ID; CONTINUOUS_SUB;
                   CONTINUOUS_CONST] THEN
      ASM_REAL_ARITH_TAC]]);;

let HOMEOMORPHIC_OPEN_INTERVALS = prove
 (`!a b:real^N c d:real^N.
        (interval(a,b) = {} <=> interval(c,d) = {})
        ==> interval(a,b) homeomorphic interval(c,d)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `interval(c:real^N,d) = {}` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[HOMEOMORPHIC_REFL] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> interval(lift((a:real^N)$i),lift((b:real^N)$i)) homeomorphic
            interval(lift((c:real^N)$i),lift((d:real^N)$i))`
  MP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_OPEN_INTERVALS_1; LIFT_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[HOMEOMORPHIC_MINIMAL; IN_INTERVAL_1; LIFT_DROP] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:num->real^1->real^1`; `g:num->real^1->real^1`] THEN
  DISCH_TAC THEN
  EXISTS_TAC
   `(\x. lambda i.
       drop((f:num->real^1->real^1) i (lift(x$i)))):real^N->real^N` THEN
  EXISTS_TAC
   `(\x. lambda i.
       drop((g:num->real^1->real^1) i (lift(x$i)))):real^N->real^N` THEN
  ASM_SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; CART_EQ; LIFT_DROP] THEN
  ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
  SIMP_TAC[LAMBDA_BETA; LIFT_DROP] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THENL
   [EXISTS_TAC `interval(lift((a:real^N)$i),lift((b:real^N)$i))`;
    EXISTS_TAC `interval(lift((c:real^N)$i),lift((d:real^N)$i))`] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1] THEN
  ASM_SIMP_TAC[LIFT_DROP; IN_INTERVAL]);;

let HOMEOMORPHIC_OPEN_INTERVAL_UNIV = prove
 (`!a b:real^N.
        ~(interval(a,b) = {})
        ==> interval(a,b) homeomorphic (:real^N)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> interval(lift((a:real^N)$i),lift((b:real^N)$i)) homeomorphic
            (:real^1)`
  MP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_OPEN_INTERVAL_UNIV_1; LIFT_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[HOMEOMORPHIC_MINIMAL; IN_INTERVAL_1; LIFT_DROP] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`f:num->real^1->real^1`; `g:num->real^1->real^1`] THEN
  DISCH_TAC THEN
  EXISTS_TAC
   `(\x. lambda i.
       drop((f:num->real^1->real^1) i (lift(x$i)))):real^N->real^N` THEN
  EXISTS_TAC
   `(\x. lambda i.
       drop((g:num->real^1->real^1) i (lift(x$i)))):real^N->real^N` THEN
  ASM_SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; CART_EQ; LIFT_DROP; IN_UNIV] THEN
  ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
  SIMP_TAC[LAMBDA_BETA; LIFT_DROP] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THENL
   [EXISTS_TAC `interval(lift((a:real^N)$i),lift((b:real^N)$i))`;
    EXISTS_TAC `(:real^1)`] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; IN_UNIV] THEN
  ASM_SIMP_TAC[LIFT_DROP; IN_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* "Isometry" (up to constant bounds) of injective linear map etc.           *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_ISOMETRIC = prove
 (`!f s e x.
        &0 < e /\ subspace s /\
        linear f /\ (!x. x IN s ==> norm(f x) >= e * norm(x)) /\
        (!n. x(n) IN s) /\ cauchy(f o x)
        ==> cauchy x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_ge] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[CAUCHY; dist; o_THM] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_SUB th)]) THEN
  DISCH_THEN(fun th -> X_GEN_TAC `d:real` THEN DISCH_TAC THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o SPEC `d * e`) THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  ASM_MESON_TAC[REAL_LE_RDIV_EQ; REAL_MUL_SYM; REAL_LET_TRANS; SUBSPACE_SUB;
                REAL_LT_LDIV_EQ]);;

let COMPLETE_ISOMETRIC_IMAGE = prove
 (`!f:real^M->real^N s e.
        &0 < e /\ subspace s /\
        linear f /\ (!x. x IN s ==> norm(f x) >= e * norm(x)) /\
        complete s
        ==> complete(IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[complete; EXISTS_IN_IMAGE] THEN
  STRIP_TAC THEN X_GEN_TAC `g:num->real^N` THEN
  REWRITE_TAC[IN_IMAGE; SKOLEM_THM; FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->real^M` MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[GSYM o_DEF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num->real^M`) THEN
  ASM_MESON_TAC[CAUCHY_ISOMETRIC; LINEAR_CONTINUOUS_AT;
                CONTINUOUS_AT_SEQUENTIALLY]);;

let INJECTIVE_IMP_ISOMETRIC = prove
 (`!f:real^M->real^N s.
        closed s /\ subspace s /\
        linear f /\ (!x. x IN s /\ (f x = vec 0) ==> (x = vec 0))
        ==> ?e. &0 < e /\ !x. x IN s ==> norm(f x) >= e * norm(x)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s SUBSET {vec 0 :real^M}` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; REAL_MUL_LID; real_ge] THEN
    ASM_MESON_TAC[SUBSET; IN_SING; NORM_0; LINEAR_0; REAL_LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [SUBSET]) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^M` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`{(f:real^M->real^N) x | x IN s /\ norm(x) = norm(a:real^M)}`;
    `vec 0:real^N`] DISTANCE_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    SUBST1_TAC(SET_RULE
     `{f x | x IN s /\ norm(x) = norm(a:real^M)} =
      IMAGE (f:real^M->real^N) (s INTER {x | norm x = norm a})`) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
    MATCH_MP_TAC CLOSED_INTER_COMPACT THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `{x:real^M | norm x = norm(a:real^M)} = frontier(cball(vec 0,norm a))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[FRONTIER_CBALL; NORM_POS_LT; dist; VECTOR_SUB_LZERO;
                   NORM_NEG];
      ASM_SIMP_TAC[COMPACT_FRONTIER; COMPACT_CBALL]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SET_RULE `{f x | P x} = IMAGE f {x | P x}`] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M` MP_TAC) THEN
  REWRITE_TAC[IN_ELIM_THM; dist; VECTOR_SUB_LZERO; NORM_NEG] THEN
  STRIP_TAC THEN REWRITE_TAC[CLOSED_LIMPT; LIMPT_APPROACHABLE] THEN
  EXISTS_TAC `norm((f:real^M->real^N) b) / norm(b)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LT_DIV; NORM_POS_LT; NORM_EQ_0]; ALL_TAC] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x:real^M = vec 0` THENL
   [FIRST_ASSUM(fun th -> ASM_REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN
    REWRITE_TAC[NORM_0; REAL_MUL_RZERO; real_ge; REAL_LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(norm(a:real^M) / norm(x)) % x:real^M`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0] THEN ASM_MESON_TAC[subspace];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; real_ge] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; NORM_POS_LT] THEN
  REWRITE_TAC[real_div; REAL_MUL_AC]);;

let CLOSED_INJECTIVE_IMAGE_SUBSPACE = prove
 (`!f s. subspace s /\
         linear f /\
         (!x. x IN s /\ f(x) = vec 0 ==> x = vec 0) /\
         closed s
         ==> closed(IMAGE f s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM COMPLETE_EQ_CLOSED] THEN
  MATCH_MP_TAC COMPLETE_ISOMETRIC_IMAGE THEN
  ASM_REWRITE_TAC[COMPLETE_EQ_CLOSED] THEN
  MATCH_MP_TAC INJECTIVE_IMP_ISOMETRIC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Relating linear images to open/closed/interior/closure.                   *)
(* ------------------------------------------------------------------------- *)

let OPEN_SURJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N.
        linear f /\ (!y. ?x. f x = y)
        ==> !s. open s ==> open(IMAGE f s)`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[open_def; FORALL_IN_IMAGE] THEN
  FIRST_ASSUM(MP_TAC o GEN `k:num` o SPEC `basis k:real^N`) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `bounded(IMAGE (b:num->real^M) (1..dimindex(:N)))` MP_TAC THENL
   [SIMP_TAC[FINITE_IMP_BOUNDED; FINITE_IMAGE; FINITE_NUMSEG]; ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `s:real^M->bool` THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `x:real^M` THEN ASM_CASES_TAC `(x:real^M) IN s` THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / B / &(dimindex(:N))` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; DIMINDEX_GE_1; LE_1] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  ABBREV_TAC `u = y - (f:real^M->real^N) x` THEN
  EXISTS_TAC `x + vsum(1..dimindex(:N)) (\i. (u:real^N)$i % b i):real^M` THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_VSUM; FINITE_NUMSEG; o_DEF;
               LINEAR_CMUL; BASIS_EXPANSION] THEN
  CONJ_TAC THENL [EXPAND_TAC "u" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[NORM_ARITH `dist(x + y,x) = norm y`] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(dist(y,(f:real^M->real^N) x) * &(dimindex(:N))) * B` THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; DIMINDEX_GE_1; LE_1] THEN
  MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = b * a * c`] THEN
  GEN_REWRITE_TAC(RAND_CONV o LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_MUL; dist] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM]);;

let OPEN_BIJECTIVE_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> (open(IMAGE f s) <=> open s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC; ASM_MESON_TAC[OPEN_SURJECTIVE_LINEAR_IMAGE]] THEN
  SUBGOAL_THEN `s = {x | (f:real^M->real^N) x IN IMAGE f s}`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT]);;

add_linear_invariants [OPEN_BIJECTIVE_LINEAR_IMAGE_EQ];;

let CLOSED_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> !s. closed s ==> closed(IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) (:real^M)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`g:real^N->real^M`; `IMAGE (f:real^M->real^N) (:real^M)`;
                   `IMAGE (g:real^N->real^M) (IMAGE (f:real^M->real^N) s)`]
        CONTINUOUS_CLOSED_IN_PREIMAGE) THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM IMAGE_o; IMAGE_I]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    REWRITE_TAC[EXTENSION; o_THM; I_THM] THEN SET_TAC[];
    MATCH_MP_TAC CLOSED_INJECTIVE_IMAGE_SUBSPACE THEN
    ASM_REWRITE_TAC[IN_UNIV; SUBSPACE_UNIV; CLOSED_UNIV] THEN
    X_GEN_TAC `x:real^M` THEN
    DISCH_THEN(MP_TAC o AP_TERM `g:real^N->real^M`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FUN_EQ_THM; I_THM; o_THM]) THEN
    ASM_MESON_TAC[LINEAR_0]]);;

let CLOSED_INJECTIVE_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (closed(IMAGE f s) <=> closed s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC; ASM_MESON_TAC[CLOSED_INJECTIVE_LINEAR_IMAGE]] THEN
  SUBGOAL_THEN `s = {x | (f:real^M->real^N) x IN IMAGE f s}`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT]);;

add_linear_invariants [CLOSED_INJECTIVE_LINEAR_IMAGE_EQ];;

let CLOSURE_LINEAR_IMAGE_SUBSET = prove
 (`!f:real^M->real^N s.
        linear f ==> IMAGE f (closure s) SUBSET closure(IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN
  ASM_SIMP_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET; LINEAR_CONTINUOUS_ON]);;

let CLOSURE_INJECTIVE_LINEAR_IMAGE  = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> closure(IMAGE f s) = IMAGE f (closure s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[CLOSURE_LINEAR_IMAGE_SUBSET] THEN
  MATCH_MP_TAC CLOSURE_MINIMAL THEN
  SIMP_TAC[CLOSURE_SUBSET; IMAGE_SUBSET] THEN
  ASM_MESON_TAC[CLOSED_INJECTIVE_LINEAR_IMAGE; CLOSED_CLOSURE]);;

add_linear_invariants [CLOSURE_INJECTIVE_LINEAR_IMAGE];;

let CLOSURE_BOUNDED_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ bounded s
        ==> closure(IMAGE f s) = IMAGE f (closure s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[CLOSURE_LINEAR_IMAGE_SUBSET] THEN
  MATCH_MP_TAC CLOSURE_MINIMAL THEN
  SIMP_TAC[CLOSURE_SUBSET; IMAGE_SUBSET] THEN
  MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
  MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN
  ASM_REWRITE_TAC[COMPACT_CLOSURE]);;

let LINEAR_INTERIOR_IMAGE_SUBSET = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
       ==> interior(IMAGE f s) SUBSET IMAGE f (interior s)`,
  MESON_TAC[INTERIOR_IMAGE_SUBSET; LINEAR_CONTINUOUS_AT]);;

let LINEAR_IMAGE_SUBSET_INTERIOR = prove
 (`!f:real^M->real^N s.
        linear f /\ (!y. ?x. f x = y)
        ==> IMAGE f (interior s) SUBSET interior(IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN
  ASM_SIMP_TAC[OPEN_SURJECTIVE_LINEAR_IMAGE; OPEN_INTERIOR;
               IMAGE_SUBSET; INTERIOR_SUBSET]);;

let INTERIOR_BIJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> interior(IMAGE f s) = IMAGE f (interior s)`,
  REWRITE_TAC[interior] THEN GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [INTERIOR_BIJECTIVE_LINEAR_IMAGE];;

let FRONTIER_BIJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> frontier(IMAGE f s) = IMAGE f (frontier s)`,
  REWRITE_TAC[frontier] THEN GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [FRONTIER_BIJECTIVE_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Corollaries, reformulations and special cases for M = N.                  *)
(* ------------------------------------------------------------------------- *)

let IN_INTERIOR_LINEAR_IMAGE = prove
 (`!f:real^M->real^N g s x.
        linear f /\ linear g /\ (f o g = I) /\ x IN interior s
        ==> (f x) IN interior (IMAGE f s)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`]
    LINEAR_IMAGE_SUBSET_INTERIOR) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  ASM_MESON_TAC[]);;

let LINEAR_OPEN_MAPPING = prove
 (`!f:real^M->real^N g s.
        linear f /\ linear g /\ (f o g = I)
        ==> !s. open s ==> open(IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC OPEN_SURJECTIVE_LINEAR_IMAGE THEN
  ASM_MESON_TAC[]);;

let INTERIOR_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> interior(IMAGE f s) = IMAGE f (interior s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERIOR_BIJECTIVE_LINEAR_IMAGE THEN
  ASM_MESON_TAC[LINEAR_INJECTIVE_IMP_SURJECTIVE]);;

let INTERIOR_SURJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ (!y. ?x. f x = y)
        ==> interior(IMAGE f s) = IMAGE f (interior s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERIOR_BIJECTIVE_LINEAR_IMAGE THEN
  ASM_MESON_TAC[LINEAR_SURJECTIVE_IMP_INJECTIVE]);;

let CLOSURE_SURJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ (!y. ?x. f x = y)
        ==> closure(IMAGE f s) = IMAGE f (closure s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_INJECTIVE_LINEAR_IMAGE THEN
  ASM_MESON_TAC[LINEAR_SURJECTIVE_IMP_INJECTIVE]);;

let FRONTIER_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> frontier(IMAGE f s) = IMAGE f (frontier s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FRONTIER_BIJECTIVE_LINEAR_IMAGE THEN
  ASM_MESON_TAC[LINEAR_INJECTIVE_IMP_SURJECTIVE]);;

let FRONTIER_SURJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N.
        linear f /\ (!y. ?x. f x = y)
        ==> frontier(IMAGE f s) = IMAGE f (frontier s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FRONTIER_BIJECTIVE_LINEAR_IMAGE THEN
  ASM_MESON_TAC[LINEAR_SURJECTIVE_IMP_INJECTIVE]);;

let COMPLETE_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> !s. complete s ==> complete(IMAGE f s)`,
  REWRITE_TAC[COMPLETE_EQ_CLOSED; CLOSED_INJECTIVE_LINEAR_IMAGE]);;

let COMPLETE_INJECTIVE_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (complete(IMAGE f s) <=> complete s)`,
  REWRITE_TAC[COMPLETE_EQ_CLOSED; CLOSED_INJECTIVE_LINEAR_IMAGE_EQ]);;

add_linear_invariants [COMPLETE_INJECTIVE_LINEAR_IMAGE_EQ];;

let LIMPT_INJECTIVE_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ((f x) limit_point_of (IMAGE f s) <=> x limit_point_of s)`,
  REWRITE_TAC[LIMPT_APPROACHABLE; EXISTS_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THENL
   [MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_BOUNDED_BELOW_POS);
    MP_TAC(ISPEC `f:real^M->real^N` LINEAR_BOUNDED_POS)] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `e * B:real`);
    FIRST_X_ASSUM(MP_TAC o SPEC `e / B:real`)] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; dist; GSYM LINEAR_SUB] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN
         CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b < x ==> a < x`) THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ]);;

add_linear_invariants [LIMPT_INJECTIVE_LINEAR_IMAGE_EQ];;

let LIMPT_TRANSLATION_EQ = prove
 (`!a s x. (a + x) limit_point_of (IMAGE (\y. a + y) s) <=> x limit_point_of s`,
  REWRITE_TAC[limit_point_of] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [LIMPT_TRANSLATION_EQ];;

(* ------------------------------------------------------------------------- *)
(* Even more special cases.                                                  *)
(* ------------------------------------------------------------------------- *)

let INTERIOR_NEGATIONS = prove
 (`!s. interior(IMAGE (--) s) = IMAGE (--) (interior s)`,
  GEN_TAC THEN MATCH_MP_TAC INTERIOR_INJECTIVE_LINEAR_IMAGE THEN
  REWRITE_TAC[linear] THEN REPEAT CONJ_TAC THEN VECTOR_ARITH_TAC);;

let SYMMETRIC_INTERIOR = prove
 (`!s:real^N->bool.
        (!x. x IN s ==> --x IN s)
        ==> !x. x IN interior s ==> (--x) IN interior s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP(ISPEC `(--):real^N->real^N` FUN_IN_IMAGE)) THEN
  REWRITE_TAC[GSYM INTERIOR_NEGATIONS] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[VECTOR_NEG_NEG]);;

let CLOSURE_NEGATIONS = prove
 (`!s. closure(IMAGE (--) s) = IMAGE (--) (closure s)`,
  GEN_TAC THEN MATCH_MP_TAC CLOSURE_INJECTIVE_LINEAR_IMAGE THEN
  REWRITE_TAC[linear] THEN REPEAT CONJ_TAC THEN VECTOR_ARITH_TAC);;

let SYMMETRIC_CLOSURE = prove
 (`!s:real^N->bool.
        (!x. x IN s ==> --x IN s)
        ==> !x. x IN closure s ==> (--x) IN closure s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP(ISPEC `(--):real^N->real^N` FUN_IN_IMAGE)) THEN
  REWRITE_TAC[GSYM CLOSURE_NEGATIONS] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[VECTOR_NEG_NEG]);;

(* ------------------------------------------------------------------------- *)
(* Some properties of a canonical subspace.                                  *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_SUBSTANDARD = prove
 (`!d. subspace
         {x:real^N | !i. d < i /\ i <= dimindex(:N) ==> x$i = &0}`,
  GEN_TAC THEN ASM_CASES_TAC `d <= dimindex(:N)` THENL
   [MP_TAC(ARITH_RULE `!i. d < i ==> 1 <= i`) THEN
    SIMP_TAC[subspace; IN_ELIM_THM; REAL_MUL_RZERO; REAL_ADD_LID;
             VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT];
    ASM_SIMP_TAC[ARITH_RULE `~(d:num <= e) ==> (d < i /\ i <= e <=> F)`] THEN
    REWRITE_TAC[SET_RULE `{x | T} = UNIV`; SUBSPACE_UNIV]]);;

let CLOSED_SUBSTANDARD = prove
 (`!d. closed
        {x:real^N | !i. d < i /\ i <= dimindex(:N) ==> x$i = &0}`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `{x:real^N | !i. d < i /\ i <= dimindex(:N) ==> x$i = &0} =
    INTERS {{x | basis i dot x = &0} | d < i /\ i <= dimindex(:N)}`
  SUBST1_TAC THENL
   [ALL_TAC;
    SIMP_TAC[CLOSED_INTERS; CLOSED_HYPERPLANE; IN_ELIM_THM;
             LEFT_IMP_EXISTS_THM]] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN
  MP_TAC(ARITH_RULE `!i. d < i ==> 1 <= i`) THEN
  SIMP_TAC[DOT_BASIS] THEN MESON_TAC[]);;

let DIM_SUBSTANDARD = prove
 (`!d. d <= dimindex(:N)
       ==> (dim {x:real^N | !i. d < i /\ i <= dimindex(:N)
                                ==> x$i = &0} =
            d)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIM_UNIQUE THEN
  EXISTS_TAC `IMAGE (basis:num->real^N) (1..d)` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
    MESON_TAC[BASIS_COMPONENT; ARITH_RULE `d < i ==> 1 <= i`; NOT_LT];
    ALL_TAC;
    MATCH_MP_TAC INDEPENDENT_MONO THEN
    EXISTS_TAC `{basis i :real^N | 1 <= i /\ i <= dimindex(:N)}` THEN
    REWRITE_TAC[INDEPENDENT_STDBASIS]THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
    ASM_MESON_TAC[LE_TRANS];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN REWRITE_TAC[HAS_SIZE_NUMSEG_1] THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_MESON_TAC[LE_TRANS; BASIS_INJ]] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`d:num`,`d:num`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `0 < i <=> 1 <= i`; SPAN_STDBASIS] THEN
    SUBGOAL_THEN `IMAGE basis (1 .. 0) :real^N->bool = {}` SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_EQ_EMPTY; NUMSEG_EMPTY; ARITH]; ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[SPAN_EMPTY; SUBSET; IN_ELIM_THM; IN_SING] THEN
    SIMP_TAC[CART_EQ; VEC_COMPONENT];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC d <= n ==> d <= n`] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_TAC THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x - (x$(SUC d)) % basis(SUC d) :real^N`) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP(ARITH_RULE `d < i ==> 1 <= i`)) THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    ASM_SIMP_TAC[BASIS_COMPONENT] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_RID; REAL_SUB_REFL] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
    ASM_MESON_TAC[ARITH_RULE `d < i /\ ~(i = SUC d) ==> SUC d < i`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBST1_TAC(VECTOR_ARITH
   `x = (x - (x$(SUC d)) % basis(SUC d)) +
        x$(SUC d) % basis(SUC d) :real^N`) THEN
  MATCH_MP_TAC SPAN_ADD THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SPAN_MONO; SUBSET_IMAGE; SUBSET; SUBSET_NUMSEG; LE_REFL; LE];
    MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN
    REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN
    MESON_TAC[LE_REFL; ARITH_RULE `1 <= SUC d`]]);;

(* ------------------------------------------------------------------------- *)
(* Hence closure and completeness of all subspaces.                          *)
(* ------------------------------------------------------------------------- *)

let CLOSED_SUBSPACE = prove
 (`!s:real^N->bool. subspace s ==> closed s`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `d = dim(s:real^N->bool)` THEN
  MP_TAC(MATCH_MP DIM_SUBSTANDARD
    (ISPEC `s:real^N->bool` DIM_SUBSET_UNIV)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`{x:real^N | !i. d < i /\ i <= dimindex(:N)
                                ==> x$i = &0}`;
    `s:real^N->bool`] SUBSPACE_ISOMORPHISM) THEN
  ASM_REWRITE_TAC[SUBSPACE_SUBSTANDARD] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(ISPEC `f:real^N->real^N` CLOSED_INJECTIVE_IMAGE_SUBSPACE) THEN
  ASM_REWRITE_TAC[SUBSPACE_SUBSTANDARD; CLOSED_SUBSTANDARD] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[LINEAR_0]] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[VEC_COMPONENT; ARITH_RULE `d < i ==> 1 <= i`]);;

let COMPLETE_SUBSPACE = prove
 (`!s:real^N->bool. subspace s ==> complete s`,
  REWRITE_TAC[COMPLETE_EQ_CLOSED; CLOSED_SUBSPACE]);;

let CLOSED_SPAN = prove
 (`!s. closed(span s)`,
  SIMP_TAC[CLOSED_SUBSPACE; SUBSPACE_SPAN]);;

let DIM_CLOSURE = prove
 (`!s:real^N->bool. dim(closure s) = dim s`,
  GEN_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM DIM_SPAN]; ALL_TAC] THEN
  MATCH_MP_TAC DIM_SUBSET THEN REWRITE_TAC[CLOSURE_SUBSET] THEN
  MATCH_MP_TAC CLOSURE_MINIMAL THEN
  SIMP_TAC[CLOSED_SUBSPACE; SUBSPACE_SPAN; SPAN_INC]);;

let CLOSED_BOUNDEDPREIM_CONTINUOUS_IMAGE = prove
 (`!f:real^M->real^N s.
      closed s /\ f continuous_on s /\
      (!e. bounded {x | x IN s /\ norm(f x) <= e})
      ==> closed(IMAGE f s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSED_INTERS_COMPACT] THEN
  REWRITE_TAC[SET_RULE
   `cball(vec 0,e) INTER IMAGE (f:real^M->real^N) s =
    IMAGE f (s INTER {x | x IN s /\ f x IN cball(vec 0,e)})`] THEN
  X_GEN_TAC `e:real` THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC CLOSED_INTER_COMPACT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[IN_CBALL_0];
      ASM_SIMP_TAC[CONTINUOUS_CLOSED_PREIMAGE; CLOSED_CBALL]]]);;

let CLOSED_INJECTIVE_IMAGE_SUBSET_SUBSPACE = prove
 (`!f:real^M->real^N s t.
        closed s /\ s SUBSET t /\ subspace t /\
        linear f /\
        (!x y. x IN t /\ f(x) = vec 0 ==> x = vec 0)
        ==> closed(IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_BOUNDEDPREIM_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `t:real^M->bool`]
    INJECTIVE_IMP_ISOMETRIC) THEN
  ASM_SIMP_TAC[CLOSED_SUBSPACE; real_ge] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `e:real` THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `cball(vec 0:real^M,e / B)` THEN
  REWRITE_TAC[BOUNDED_CBALL] THEN
  ASM_SIMP_TAC[SUBSET; IN_ELIM_THM; IN_CBALL_0; REAL_LE_RDIV_EQ] THEN
  ASM_MESON_TAC[SUBSET; REAL_LE_TRANS]);;

let BASIS_COORDINATES_LIPSCHITZ = prove
 (`!b:real^N->bool.
        independent b
        ==> ?B. &0 < B /\
                !c v. v IN b
                      ==> abs(c v) <= B * norm(vsum b (\v. c(v) % v))`,
  X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INDEPENDENT_BOUND) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `b:num->real^N` STRIP_ASSUME_TAC o
        GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  ABBREV_TAC `n = CARD(k:real^N->bool)` THEN
  MP_TAC(ISPECL
   [`(\x. vsum(1..n) (\i. x$i % b i)):real^N->real^N`;
    `span(IMAGE basis (1..n)):real^N->bool`]
        INJECTIVE_IMP_ISOMETRIC) THEN
  REWRITE_TAC[SUBSPACE_SPAN] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [SIMP_TAC[CLOSED_SUBSPACE; SUBSPACE_SPAN]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC LINEAR_VMUL_COMPONENT THEN
      SIMP_TAC[LINEAR_ID] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SPAN_IMAGE_BASIS]) THEN
    REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
    DISCH_THEN(X_CHOOSE_TAC `c:real^N->num`) THEN
    SUBGOAL_THEN
     `vsum(1..n) (\i. (x:real^N)$i % b i:real^N) = vsum k (\v. x$(c v) % v)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC VSUM_EQ_GENERAL_INVERSES THEN
      MAP_EVERY EXISTS_TAC [`b:num->real^N`; `c:real^N->num`] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INDEPENDENT_EXPLICIT]) THEN
    DISCH_THEN(MP_TAC o SPEC `\v:real^N. (x:real^N)$(c v)` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; FORALL_IN_IMAGE; VEC_COMPONENT] THEN
    ASM_MESON_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `inv(B:real)` THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N->real`; `j:num`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `inv B * x = x / B`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o rand o rand o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `(lambda i. if 1 <= i /\ i <= n then c(b i:real^N) else &0):real^N`) THEN
  SIMP_TAC[IN_SPAN_IMAGE_BASIS; LAMBDA_BETA] THEN
  ANTS_TAC THENL [MESON_TAC[IN_NUMSEG]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = v /\ u <= y ==> x >= y ==> u <= v`) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    SUBGOAL_THEN `!i. i <= n ==> i <= dimindex(:N)` MP_TAC THENL
     [ASM_ARITH_TAC; SIMP_TAC[LAMBDA_BETA] THEN DISCH_THEN(K ALL_TAC)] THEN
    REWRITE_TAC[o_THM];
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN
    MP_TAC(ISPECL
     [`(lambda i. if 1 <= i /\ i <= n then c(b i:real^N) else &0):real^N`;
      `j:num`] COMPONENT_LE_NORM) THEN
    SIMP_TAC[LAMBDA_BETA] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let BASIS_COORDINATES_CONTINUOUS = prove
 (`!b:real^N->bool e.
        independent b /\ &0 < e
        ==> ?d. &0 < d /\
                !c. norm(vsum b (\v. c(v) % v)) < d
                    ==> !v. v IN b ==> abs(c v) < e`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BASIS_COORDINATES_LIPSCHITZ) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / B:real` THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
  X_GEN_TAC `c:real^N->real` THEN DISCH_TAC THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `B * norm(vsum b (\v:real^N. c v % v))` THEN
  ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Affine transformations of intervals.                                      *)
(* ------------------------------------------------------------------------- *)

let AFFINITY_INVERSES = prove
 (`!m c. ~(m = &0)
         ==> (\x. m % x + c) o (\x. inv(m) % x + (--(inv(m) % c))) = I /\
             (\x. inv(m) % x + (--(inv(m) % c))) o (\x. m % x + c) = I`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_RNEG] THEN
  SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RINV] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let REAL_AFFINITY_LE = prove
 (`!m c x y. &0 < m ==> (m * x + c <= y <=> x <= inv(m) * y + --(c / m))`,
  REWRITE_TAC[REAL_ARITH `m * x + c <= y <=> x * m <= y - c`] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC);;

let REAL_LE_AFFINITY = prove
 (`!m c x y. &0 < m ==> (y <= m * x + c <=> inv(m) * y + --(c / m) <= x)`,
  REWRITE_TAC[REAL_ARITH `y <= m * x + c <=> y - c <= x * m`] THEN
  SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

let REAL_AFFINITY_LT = prove
 (`!m c x y. &0 < m ==> (m * x + c < y <=> x < inv(m) * y + --(c / m))`,
  SIMP_TAC[REAL_LE_AFFINITY; GSYM REAL_NOT_LE]);;

let REAL_LT_AFFINITY = prove
 (`!m c x y. &0 < m ==> (y < m * x + c <=> inv(m) * y + --(c / m) < x)`,
  SIMP_TAC[REAL_AFFINITY_LE; GSYM REAL_NOT_LE]);;

let REAL_AFFINITY_EQ = prove
 (`!m c x y. ~(m = &0) ==> (m * x + c = y <=> x = inv(m) * y + --(c / m))`,
  CONV_TAC REAL_FIELD);;

let REAL_EQ_AFFINITY = prove
 (`!m c x y. ~(m = &0) ==> (y = m * x + c  <=> inv(m) * y + --(c / m) = x)`,
  CONV_TAC REAL_FIELD);;

let VECTOR_AFFINITY_EQ = prove
 (`!m c x y. ~(m = &0)
             ==> (m % x + c = y <=> x = inv(m) % y + --(inv(m) % c))`,
  SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           real_div; VECTOR_NEG_COMPONENT; REAL_AFFINITY_EQ] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let VECTOR_EQ_AFFINITY = prove
 (`!m c x y. ~(m = &0)
             ==> (y = m % x + c <=> inv(m) % y + --(inv(m) % c) = x)`,
  SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           real_div; VECTOR_NEG_COMPONENT; REAL_EQ_AFFINITY] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let IMAGE_AFFINITY_INTERVAL = prove
 (`!a b:real^N m c.
        IMAGE (\x. m % x + c) (interval[a,b]) =
            if interval[a,b] = {} then {}
            else if &0 <= m then interval[m % a + c,m % b + c]
            else interval[m % b + c,m % a + c]`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  ASM_CASES_TAC `m = &0` THEN ASM_REWRITE_TAC[REAL_LE_LT] THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; COND_ID] THEN
    REWRITE_TAC[INTERVAL_SING] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `~(x = &0) ==> &0 < x \/ &0 < --x`)) THEN
  ASM_SIMP_TAC[EXTENSION; IN_IMAGE; REAL_ARITH `&0 < --x ==> ~(&0 < x)`] THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[VECTOR_ARITH `x = m % y + c <=> c = (--m) % y + x`]] THEN
  ASM_SIMP_TAC[VECTOR_EQ_AFFINITY; REAL_LT_IMP_NZ; UNWIND_THM1] THEN
  SIMP_TAC[IN_INTERVAL; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           VECTOR_NEG_COMPONENT] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_LT_INV_EQ]) THEN
  SIMP_TAC[REAL_AFFINITY_LE; REAL_LE_AFFINITY; real_div] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[REAL_INV_INV] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_NEGNEG] THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < m ==> (inv m * x) * m = x`] THEN
  GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Infinite sums of vectors. Allow general starting point (and more).        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("sums",(12,"right"));;

let sums = new_definition
  `(f sums l) s = ((\n. vsum(s INTER (0..n)) f) --> l) sequentially`;;

let infsum = new_definition
 `infsum s f = @l. (f sums l) s`;;

let summable = new_definition
 `summable s f = ?l. (f sums l) s`;;

let SUMS_SUMMABLE = prove
 (`!f l s. (f sums l) s ==> summable s f`,
  REWRITE_TAC[summable] THEN MESON_TAC[]);;

let SUMS_INFSUM = prove
 (`!f s. (f sums (infsum s f)) s <=> summable s f`,
  REWRITE_TAC[infsum; summable] THEN MESON_TAC[]);;

let SUMS_LIM = prove
 (`!f:num->real^N s.
      (f sums lim sequentially (\n. vsum (s INTER (0..n)) f)) s
      <=> summable s f`,
  GEN_TAC THEN GEN_TAC THEN EQ_TAC THENL [MESON_TAC[summable];
  REWRITE_TAC[summable; sums] THEN STRIP_TAC THEN REWRITE_TAC[lim] THEN
  ASM_MESON_TAC[]]);;

let from = new_definition
  `from n = {m:num | n <= m}`;;

let FROM_0 = prove
 (`from 0 = (:num)`,
  REWRITE_TAC[from; LE_0] THEN SET_TAC[]);;

let FINITE_INTER_NUMSEG = prove
 (`!s m n. FINITE(s INTER (m..n))`,
  MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG; INTER_SUBSET]);;

let FROM_INTER_NUMSEG_GEN = prove
 (`!k m n. (from k) INTER (m..n) = (if m < k then k..n else m..n)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[from; IN_ELIM_THM; IN_INTER; IN_NUMSEG; EXTENSION] THEN
  ARITH_TAC);;

let FROM_INTER_NUMSEG = prove
 (`!k n. (from k) INTER (0..n) = k..n`,
  REWRITE_TAC[from; IN_ELIM_THM; IN_INTER; IN_NUMSEG; EXTENSION] THEN
  ARITH_TAC);;

let IN_FROM = prove
 (`!m n. m IN from n <=> n <= m`,
  REWRITE_TAC[from; IN_ELIM_THM]);;

let SERIES_FROM = prove
 (`!f l k. (f sums l) (from k) = ((\n. vsum(k..n) f) --> l) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sums] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; numseg; from; IN_ELIM_THM; IN_INTER] THEN ARITH_TAC);;

let SERIES_UNIQUE = prove
 (`!f:num->real^N l l' s. (f sums l) s /\ (f sums l') s ==> (l = l')`,
  REWRITE_TAC[sums] THEN MESON_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; LIM_UNIQUE]);;

let INFSUM_UNIQUE = prove
 (`!f:num->real^N l s. (f sums l) s ==> infsum s f = l`,
  MESON_TAC[SERIES_UNIQUE; SUMS_INFSUM; summable]);;

let SERIES_FINITE = prove
 (`!f s. FINITE s ==> (f sums (vsum s f)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[num_FINITE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[sums; LIM_SEQUENTIALLY] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `n:num` THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `s INTER (0..m) = s`
   (fun th -> ASM_REWRITE_TAC[th; DIST_REFL]) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_NUMSEG; LE_0] THEN
  ASM_MESON_TAC[LE_TRANS]);;

let SERIES_LINEAR = prove
 (`!f h l s. (f sums l) s /\ linear h ==> ((\n. h(f n)) sums h l) s`,
  SIMP_TAC[sums; LIM_LINEAR; FINITE_INTER; FINITE_NUMSEG;
           GSYM(REWRITE_RULE[o_DEF] LINEAR_VSUM)]);;

let SERIES_0 = prove
 (`!s. ((\n. vec 0) sums (vec 0)) s`,
  REWRITE_TAC[sums; VSUM_0; LIM_CONST]);;

let SERIES_ADD = prove
 (`!x x0 y y0 s.
     (x sums x0) s /\ (y sums y0) s ==> ((\n. x n + y n) sums (x0 + y0)) s`,
  SIMP_TAC[sums; FINITE_INTER_NUMSEG; VSUM_ADD; LIM_ADD]);;

let SERIES_SUB = prove
 (`!x x0 y y0 s.
     (x sums x0) s /\ (y sums y0) s ==> ((\n. x n - y n) sums (x0 - y0)) s`,
  SIMP_TAC[sums; FINITE_INTER_NUMSEG; VSUM_SUB; LIM_SUB]);;

let SERIES_CMUL = prove
 (`!x x0 c s. (x sums x0) s ==> ((\n. c % x n) sums (c % x0)) s`,
  SIMP_TAC[sums; FINITE_INTER_NUMSEG; VSUM_LMUL; LIM_CMUL]);;

let SERIES_NEG = prove
 (`!x x0 s. (x sums x0) s ==> ((\n. --(x n)) sums (--x0)) s`,
  SIMP_TAC[sums; FINITE_INTER_NUMSEG; VSUM_NEG; LIM_NEG]);;

let SUMS_IFF = prove
 (`!f g k. (!x. x IN k ==> f x = g x) ==> ((f sums l) k <=> (g sums l) k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sums] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[IN_INTER]);;

let SUMS_EQ = prove
 (`!f g k. (!x. x IN k ==> f x = g x) /\ (f sums l) k ==> (g sums l) k`,
  MESON_TAC[SUMS_IFF]);;

let SUMS_0 = prove
 (`!f:num->real^N s. (!n. n IN s ==> f n = vec 0) ==> (f sums vec 0) s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUMS_EQ THEN
  EXISTS_TAC `\n:num. vec 0:real^N` THEN ASM_SIMP_TAC[SERIES_0]);;

let SERIES_FINITE_SUPPORT = prove
 (`!f:num->real^N s k.
     FINITE (s INTER k) /\ (!x. ~(x IN s INTER k) ==> f x = vec 0)
     ==> (f sums vsum (s INTER k) f) k`,
  REWRITE_TAC[sums; LIM_SEQUENTIALLY] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPEC `\x:num. x` o MATCH_MP UPPER_BOUND_FINITE_SET) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `vsum (k INTER (0..n)) (f:num->real^N) = vsum(s INTER k) f`
   (fun th -> ASM_REWRITE_TAC[DIST_REFL; th]) THEN
  MATCH_MP_TAC VSUM_SUPERSET THEN
  ASM_SIMP_TAC[SUBSET; IN_INTER; IN_NUMSEG; LE_0] THEN
  ASM_MESON_TAC[IN_INTER; LE_TRANS]);;

let SERIES_COMPONENT = prove
 (`!f s l:real^N k. (f sums l) s /\ 1 <= k /\ k <= dimindex(:N)
                    ==> ((\i. lift(f(i)$k)) sums lift(l$k)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sums] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  ASM_SIMP_TAC[GSYM LIFT_SUM; GSYM VSUM_COMPONENT;
               FINITE_INTER; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[o_DEF; LIM_COMPONENT]);;

let SERIES_DIFFS = prove
 (`!f:num->real^N k.
        (f --> vec 0) sequentially
        ==> ((\n. f(n) - f(n + 1)) sums f(k)) (from k)`,
  REWRITE_TAC[sums; FROM_INTER_NUMSEG; VSUM_DIFFS] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. (f:num->real^N) k - f(n + 1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `k:num` THEN
    SIMP_TAC[];
    GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_SUB_RZERO] THEN
    MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC[LIM_CONST] THEN
    MATCH_MP_TAC SEQ_OFFSET THEN ASM_REWRITE_TAC[]]);;

let SERIES_TRIVIAL = prove
 (`!f. (f sums vec 0) {}`,
  REWRITE_TAC[sums; INTER_EMPTY; VSUM_CLAUSES; LIM_CONST]);;

let SERIES_RESTRICT = prove
 (`!f k l:real^N.
        ((\n. if n IN k then f(n) else vec 0) sums l) (:num) <=>
        (f sums l) k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sums] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; INTER_UNIV] THEN GEN_TAC THEN
  MATCH_MP_TAC(MESON[] `vsum s f = vsum t f /\ vsum t f = vsum t g
                        ==> vsum s f = vsum t g`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN SET_TAC[];
    MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[IN_INTER]]);;

let SERIES_VSUM = prove
 (`!f l k s. FINITE s /\ s SUBSET k /\ (!x. ~(x IN s) ==> f x = vec 0) /\
             vsum s f = l ==> (f sums l) k`,
  REPEAT STRIP_TAC THEN EXPAND_TAC "l" THEN
  SUBGOAL_THEN `s INTER k = s:num->bool` ASSUME_TAC THENL
   [ASM SET_TAC []; ASM_MESON_TAC [SERIES_FINITE_SUPPORT]]);;

let SUMS_REINDEX = prove
 (`!k a l n. ((\x. a(x + k)) sums l) (from n) <=> (a sums l) (from(n + k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sums; FROM_INTER_NUMSEG] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VSUM_OFFSET] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  ASM_MESON_TAC[ARITH_RULE `N + k:num <= n ==> n = (n - k) + k /\ N <= n - k`;
                ARITH_RULE `N + k:num <= n ==> N <= n + k`]);;

(* ------------------------------------------------------------------------- *)
(* Similar combining theorems just for summability.                          *)
(* ------------------------------------------------------------------------- *)

let SUMMABLE_LINEAR = prove
 (`!f h s. summable s f /\ linear h ==> summable s (\n. h(f n))`,
  REWRITE_TAC[summable] THEN MESON_TAC[SERIES_LINEAR]);;

let SUMMABLE_0 = prove
 (`!s. summable s (\n. vec 0)`,
  REWRITE_TAC[summable] THEN MESON_TAC[SERIES_0]);;

let SUMMABLE_ADD = prove
 (`!x y s. summable s x /\ summable s y ==> summable s (\n. x n + y n)`,
  REWRITE_TAC[summable] THEN MESON_TAC[SERIES_ADD]);;

let SUMMABLE_SUB = prove
 (`!x y s. summable s x /\ summable s y ==> summable s (\n. x n - y n)`,
  REWRITE_TAC[summable] THEN MESON_TAC[SERIES_SUB]);;

let SUMMABLE_CMUL = prove
 (`!s x c. summable s x ==> summable s (\n. c % x n)`,
  REWRITE_TAC[summable] THEN MESON_TAC[SERIES_CMUL]);;

let SUMMABLE_NEG = prove
 (`!x s. summable s x ==> summable s (\n. --(x n))`,
  REWRITE_TAC[summable] THEN MESON_TAC[SERIES_NEG]);;

let SUMMABLE_IFF = prove
 (`!f g k. (!x. x IN k ==> f x = g x) ==> (summable k f <=> summable k g)`,
  REWRITE_TAC[summable] THEN MESON_TAC[SUMS_IFF]);;

let SUMMABLE_EQ = prove
 (`!f g k. (!x. x IN k ==> f x = g x) /\ summable k f ==> summable k g`,
  REWRITE_TAC[summable] THEN MESON_TAC[SUMS_EQ]);;

let SUMMABLE_COMPONENT = prove
 (`!f:num->real^N s k.
        summable s f /\ 1 <= k /\ k <= dimindex(:N)
        ==> summable s (\i. lift(f(i)$k))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `l:real^N` o REWRITE_RULE[summable]) THEN
  REWRITE_TAC[summable] THEN EXISTS_TAC `lift((l:real^N)$k)` THEN
  ASM_SIMP_TAC[SERIES_COMPONENT]);;

let SERIES_SUBSET = prove
 (`!x s t l.
        s SUBSET t /\
        ((\i. if i IN s then x i else vec 0) sums l) t
        ==> (x sums l) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[sums] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  ASM_SIMP_TAC[GSYM VSUM_RESTRICT_SET; FINITE_INTER_NUMSEG] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN SET_TAC[]);;

let SUMMABLE_SUBSET = prove
 (`!x s t l.
        s SUBSET t /\
        summable t (\i. if i IN s then x i else vec 0)
        ==> summable s x`,
  REWRITE_TAC[summable] THEN MESON_TAC[SERIES_SUBSET]);;

let SUMMABLE_TRIVIAL = prove
 (`!f:num->real^N. summable {} f`,
  GEN_TAC THEN REWRITE_TAC[summable] THEN EXISTS_TAC `vec 0:real^N` THEN
  REWRITE_TAC[SERIES_TRIVIAL]);;

let SUMMABLE_RESTRICT = prove
 (`!f k l:real^N.
        summable (:num) (\n. if n IN k then f(n) else vec 0) <=>
        summable k f`,
  REWRITE_TAC[summable; SERIES_RESTRICT]);;

let SUMS_FINITE_DIFF = prove
 (`!f:num->real^N t s l.
        t SUBSET s /\ FINITE t /\ (f sums l) s
        ==> (f sums (l - vsum t f)) (s DIFF t)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(MP_TAC o ISPEC `f:num->real^N` o MATCH_MP SERIES_FINITE) THEN
  ONCE_REWRITE_TAC[GSYM SERIES_RESTRICT] THEN
  REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SERIES_SUB) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:num` THEN REWRITE_TAC[IN_DIFF] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:num` o GEN_REWRITE_RULE I [SUBSET]) THEN
  MAP_EVERY ASM_CASES_TAC [`(x:num) IN s`; `(x:num) IN t`] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let SUMS_FINITE_UNION = prove
 (`!f:num->real^N s t l.
        FINITE t /\ (f sums l) s
        ==> (f sums (l + vsum (t DIFF s) f)) (s UNION t)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:num->bool` o MATCH_MP FINITE_DIFF) THEN
  DISCH_THEN(MP_TAC o ISPEC `f:num->real^N` o MATCH_MP SERIES_FINITE) THEN
  ONCE_REWRITE_TAC[GSYM SERIES_RESTRICT] THEN
  REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SERIES_ADD) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:num` THEN
  REWRITE_TAC[IN_DIFF; IN_UNION] THEN
  MAP_EVERY ASM_CASES_TAC [`(x:num) IN s`; `(x:num) IN t`] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let SUMS_OFFSET = prove
 (`!f:num->real^N t s l m n.
        (f sums l) (from m) /\ m < n
        ==> (f sums (l - vsum(m..(n-1)) f)) (from n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `from n = from m DIFF (m..(n-1))` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_FROM; IN_DIFF; IN_NUMSEG] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC SUMS_FINITE_DIFF THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    SIMP_TAC[SUBSET; IN_FROM; IN_NUMSEG]]);;

let SUMS_OFFSET_REV = prove
 (`!f:num->real^N t s l m n.
        (f sums l) (from m) /\ n < m
        ==> (f sums (l + vsum(n..m-1) f)) (from n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real^N`; `from m`; `n..m-1`; `l:real^N`]
                SUMS_FINITE_UNION) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN MATCH_MP_TAC EQ_IMP THEN
  BINOP_TAC THENL [AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_FROM; IN_NUMSEG] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Cauchy criterion for series.                                              *)
(* ------------------------------------------------------------------------- *)

let SEQUENCE_CAUCHY_WLOG = prove
 (`!P s. (!m n:num. P m /\ P n ==> dist(s m,s n) < e) <=>
         (!m n. P m /\ P n /\ m <= n ==> dist(s m,s n) < e)`,
  MESON_TAC[DIST_SYM; LE_CASES]);;

let VSUM_DIFF_LEMMA = prove
 (`!f:num->real^N k m n.
        m <= n
        ==> vsum(k INTER (0..n)) f - vsum(k INTER (0..m)) f =
            vsum(k INTER (m+1..n)) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real^N`; `k INTER (0..n)`; `k INTER (0..m)`]
    VSUM_DIFF) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_INTER; FINITE_NUMSEG] THEN MATCH_MP_TAC
     (SET_RULE `s SUBSET t ==> (u INTER s SUBSET u INTER t)`) THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG] THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[SET_RULE
     `(k INTER s) DIFF (k INTER t) = k INTER (s DIFF t)`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_DIFF; IN_NUMSEG] THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC]);;

let NORM_VSUM_TRIVIAL_LEMMA = prove
 (`!e. &0 < e ==> (P ==> norm(vsum(s INTER (m..n)) f) < e <=>
                   P ==> n < m \/ norm(vsum(s INTER (m..n)) f) < e)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n:num < m` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I [GSYM NUMSEG_EMPTY]) THEN
  ASM_REWRITE_TAC[VSUM_CLAUSES; NORM_0; INTER_EMPTY]);;

let SERIES_CAUCHY = prove
 (`!f s. (?l. (f sums l) s) =
         !e. &0 < e
             ==> ?N. !m n. m >= N
                           ==> norm(vsum(s INTER (m..n)) f) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sums; CONVERGENT_EQ_CAUCHY; cauchy] THEN
  REWRITE_TAC[SEQUENCE_CAUCHY_WLOG] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  SIMP_TAC[dist; VSUM_DIFF_LEMMA; NORM_VSUM_TRIVIAL_LEMMA] THEN
  REWRITE_TAC[GE; TAUT `a ==> b \/ c <=> a /\ ~b ==> c`] THEN
  REWRITE_TAC[NOT_LT; ARITH_RULE
   `(N <= m /\ N <= n /\ m <= n) /\ m + 1 <= n <=>
    N + 1 <= m + 1 /\ m + 1 <= n`] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THENL
   [EXISTS_TAC `N + 1`; EXISTS_TAC `N:num`] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `N + 1 <= m + 1 ==> N <= m + 1`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m - 1`; `n:num`]) THEN
  SUBGOAL_THEN `m - 1 + 1 = m` SUBST_ALL_TAC THENL
   [ALL_TAC; ANTS_TAC THEN SIMP_TAC[]] THEN
  ASM_ARITH_TAC);;

let SUMMABLE_IFF_EVENTUALLY = prove
 (`!f g k. (?N. !n. N <= n /\ n IN k ==> f n = g n)
           ==> (summable k f <=> summable k g)`,
  REWRITE_TAC[summable; SERIES_CAUCHY] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `e:real` THEN
  AP_TERM_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num`
   (fun th -> EXISTS_TAC `N0 + N1:num` THEN MP_TAC th)) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[IN_INTER; IN_NUMSEG] THEN
  REPEAT STRIP_TAC THENL [ALL_TAC; CONV_TAC SYM_CONV] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let SUMMABLE_EQ_EVENTUALLY = prove
 (`!f g k. (?N. !n. N <= n /\ n IN k ==> f n = g n) /\ summable k f
           ==> summable k g`,
  MESON_TAC[SUMMABLE_IFF_EVENTUALLY]);;

let SUMMABLE_IFF_COFINITE = prove
 (`!f g s t. FINITE((s DIFF t) UNION (t DIFF s))
             ==> (summable s f <=> summable t f)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM SUMMABLE_RESTRICT] THEN
  MATCH_MP_TAC SUMMABLE_IFF_EVENTUALLY THEN
  FIRST_ASSUM(MP_TAC o ISPEC `\x:num.x` o MATCH_MP UPPER_BOUND_FINITE_SET) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN REWRITE_TAC[IN_UNIV] THEN
  DISCH_TAC THEN EXISTS_TAC `N + 1` THEN
  REWRITE_TAC[ARITH_RULE `N + 1 <= n <=> ~(n <= N)`] THEN ASM SET_TAC[]);;

let SUMMABLE_EQ_COFINITE = prove
 (`!f g s t. FINITE((s DIFF t) UNION (t DIFF s)) /\ summable s f
             ==> summable t f`,
  MESON_TAC[SUMMABLE_IFF_COFINITE]);;

let SUMMABLE_FROM_ELSEWHERE = prove
 (`!f m n. summable (from m) f ==> summable (from n) f`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUMMABLE_EQ_COFINITE) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..(m+n)` THEN
  SIMP_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_UNION; IN_DIFF; IN_FROM] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Uniform vesion of Cauchy criterion.                                       *)
(* ------------------------------------------------------------------------- *)

let SERIES_CAUCHY_UNIFORM = prove
 (`!P f:A->num->real^N k.
        (?l. !e. &0 < e
                 ==> ?N. !n x. N <= n /\ P x
                               ==> dist(vsum(k INTER (0..n)) (f x),
                                        l x) < e) <=>
        (!e. &0 < e ==> ?N. !m n x. N <= m /\ P x
                                    ==> norm(vsum(k INTER (m..n)) (f x)) < e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sums; UNIFORMLY_CONVERGENT_EQ_CAUCHY; cauchy] THEN
  ONCE_REWRITE_TAC[MESON[]
   `(!m n:num y. N <= m /\ N <= n /\ P y ==> Q m n y) <=>
    (!y. P y ==> !m n. N <= m /\ N <= n ==> Q m n y)`] THEN
  REWRITE_TAC[SEQUENCE_CAUCHY_WLOG] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  SIMP_TAC[dist; VSUM_DIFF_LEMMA; NORM_VSUM_TRIVIAL_LEMMA] THEN
  REWRITE_TAC[GE; TAUT `a ==> b \/ c <=> a /\ ~b ==> c`] THEN
  REWRITE_TAC[NOT_LT; ARITH_RULE
   `(N <= m /\ N <= n /\ m <= n) /\ m + 1 <= n <=>
    N + 1 <= m + 1 /\ m + 1 <= n`] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THENL
   [EXISTS_TAC `N + 1`; EXISTS_TAC `N:num`] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `N + 1 <= m + 1 ==> N <= m + 1`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`m - 1`; `n:num`]) THEN
  SUBGOAL_THEN `m - 1 + 1 = m` SUBST_ALL_TAC THENL
   [ALL_TAC; ANTS_TAC THEN SIMP_TAC[]] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* So trivially, terms of a convergent series go to zero.                    *)
(* ------------------------------------------------------------------------- *)

let SERIES_GOESTOZERO = prove
 (`!s x. summable s x
         ==> !e. &0 < e
                 ==> eventually (\n. n IN s ==> norm(x n) < e) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[summable; SERIES_CAUCHY] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `n:num`]) THEN
  ASM_SIMP_TAC[NUMSEG_SING; GE; SET_RULE `n IN s ==> s INTER {n} = {n}`] THEN
  REWRITE_TAC[VSUM_SING]);;

let SUMMABLE_IMP_TOZERO = prove
 (`!f:num->real^N k.
       summable k f
       ==> ((\n. if n IN k then f(n) else vec 0) --> vec 0) sequentially`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM SUMMABLE_RESTRICT] THEN
  REWRITE_TAC[summable; LIM_SEQUENTIALLY; INTER_UNIV; sums] THEN
  DISCH_THEN(X_CHOOSE_TAC `l:real^N`) THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN EXISTS_TAC `N + 1` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `n - 1` th) THEN MP_TAC(SPEC `n:num` th)) THEN
  ASM_SIMP_TAC[ARITH_RULE `N + 1 <= n ==> N <= n /\ N <= n - 1`] THEN
  ABBREV_TAC `m = n - 1` THEN
  SUBGOAL_THEN `n = SUC m` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0] THEN
  REWRITE_TAC[NORM_ARITH `dist(x,vec 0) = norm x`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NORM_0] THEN CONV_TAC NORM_ARITH);;

let SUMMABLE_IMP_BOUNDED = prove
 (`!f:num->real^N k. summable k f ==> bounded (IMAGE f k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_IMP_TOZERO) THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONVERGENT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_UNIV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[REAL_LT_IMP_LE; NORM_0]);;

let SUMMABLE_IMP_SUMS_BOUNDED = prove
 (`!f:num->real^N k.
       summable (from k) f ==> bounded { vsum(k..n) f | n IN (:num) }`,
  REWRITE_TAC[summable; sums; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONVERGENT_IMP_BOUNDED) THEN
  REWRITE_TAC[FROM_INTER_NUMSEG; SIMPLE_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Comparison test.                                                          *)
(* ------------------------------------------------------------------------- *)

let SERIES_COMPARISON = prove
 (`!f g s. (?l. ((lift o g) sums l) s) /\
           (?N. !n. n >= N /\ n IN s ==> norm(f n) <= g n)
           ==> ?l:real^N. (f sums l) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SERIES_CAUCHY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC `N1:num`)) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `N1 + N2:num` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm (vsum (s INTER (m .. n)) (lift o g))` THEN CONJ_TAC THENL
   [SIMP_TAC[GSYM LIFT_SUM; FINITE_INTER_NUMSEG; NORM_LIFT] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= abs(a)`) THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN
    REWRITE_TAC[FINITE_INTER_NUMSEG; IN_INTER; IN_NUMSEG] THEN
    ASM_MESON_TAC[ARITH_RULE `m >= N1 + N2:num /\ m <= x ==> x >= N1`];
    ASM_MESON_TAC[ARITH_RULE `m >= N1 + N2:num ==> m >= N2`]]);;

let SUMMABLE_COMPARISON = prove
 (`!f g s. summable s (lift o g) /\
           (?N. !n. n >= N /\ n IN s ==> norm(f n) <= g n)
           ==> summable s f`,
  REWRITE_TAC[summable; SERIES_COMPARISON]);;

(* ------------------------------------------------------------------------- *)
(* Uniform version of comparison test.                                       *)
(* ------------------------------------------------------------------------- *)

let SERIES_COMPARISON_UNIFORM = prove
 (`!f g P s. (?l. ((lift o g) sums l) s) /\
             (?N. !n x. N <= n /\ n IN s /\ P x ==> norm(f x n) <= g n)
             ==> ?l:A->real^N.
                    !e. &0 < e
                        ==> ?N. !n x. N <= n /\ P x
                                      ==> dist(vsum(s INTER (0..n)) (f x),
                                               l x) < e`,
  REPEAT GEN_TAC THEN SIMP_TAC[GE; SERIES_CAUCHY; SERIES_CAUCHY_UNIFORM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC `N1:num`)) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `N1 + N2:num` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `x:A`] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm (vsum (s INTER (m .. n)) (lift o g))` THEN CONJ_TAC THENL
   [SIMP_TAC[GSYM LIFT_SUM; FINITE_INTER_NUMSEG; NORM_LIFT] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= abs(a)`) THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN
    REWRITE_TAC[FINITE_INTER_NUMSEG; IN_INTER; IN_NUMSEG] THEN
    ASM_MESON_TAC[ARITH_RULE `N1 + N2:num <= m /\ m <= x ==> N1 <= x`];
    ASM_MESON_TAC[ARITH_RULE `N1 + N2:num <= m ==> N2 <= m`]]);;

(* ------------------------------------------------------------------------- *)
(* Ratio test.                                                               *)
(* ------------------------------------------------------------------------- *)

let SERIES_RATIO = prove
 (`!c a s N.
      c < &1 /\
      (!n. n >= N ==> norm(a(SUC n)) <= c * norm(a(n)))
      ==> ?l:real^N. (a sums l) s`,
  REWRITE_TAC[GE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SERIES_COMPARISON THEN
  DISJ_CASES_TAC(REAL_ARITH `c <= &0 \/ &0 < c`) THENL
   [EXISTS_TAC `\n:num. &0` THEN REWRITE_TAC[o_DEF; LIFT_NUM] THEN
    CONJ_TAC THENL [MESON_TAC[SERIES_0]; ALL_TAC] THEN
    EXISTS_TAC `N + 1` THEN REWRITE_TAC[GE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c * norm(a(n - 1):real^N)` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `N + 1 <= n ==> SUC(n - 1) = n /\ N <= n - 1`];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= --c * x ==> c * x <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    UNDISCH_TAC `c <= &0` THEN REAL_ARITH_TAC;
    ASSUME_TAC(MATCH_MP REAL_LT_IMP_LE (ASSUME `&0 < c`))] THEN
  EXISTS_TAC `\n. norm(a(N):real^N) * c pow (n - N)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `N:num` THEN
    SIMP_TAC[GE; LE_EXISTS; IMP_CONJ; ADD_SUB2; LEFT_IMP_EXISTS_THM] THEN
    SUBGOAL_THEN `!d:num. norm(a(N + d):real^N) <= norm(a N) * c pow d`
     (fun th -> MESON_TAC[th]) THEN INDUCT_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; real_pow; REAL_MUL_RID; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c * norm((a:num->real^N) (N + d))` THEN
    ASM_SIMP_TAC[LE_ADD] THEN ASM_MESON_TAC[REAL_LE_LMUL; REAL_MUL_AC]] THEN
  GEN_REWRITE_TAC I [SERIES_CAUCHY] THEN X_GEN_TAC `e:real` THEN
  SIMP_TAC[GSYM LIFT_SUM; FINITE_INTER; NORM_LIFT; FINITE_NUMSEG] THEN
  DISCH_TAC THEN SIMP_TAC[SUM_LMUL; FINITE_INTER; FINITE_NUMSEG] THEN
  ASM_CASES_TAC `(a:num->real^N) N = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; REAL_MUL_LZERO; REAL_ABS_NUM]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `((&1 - c) * e) / norm((a:num->real^N) N)`]
               REAL_ARCH_POW_INV) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_SUB_LT; NORM_POS_LT; GE] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN EXISTS_TAC `N + M:num` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs(norm((a:num->real^N) N) *
                  sum(m..n) (\i. c pow (i - N)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= abs y`) THEN
    ASM_SIMP_TAC[SUM_POS_LE; FINITE_INTER_NUMSEG; REAL_POW_LE] THEN
    MATCH_MP_TAC SUM_SUBSET THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
    REWRITE_TAC[FINITE_INTER_NUMSEG; FINITE_NUMSEG] THEN
    REWRITE_TAC[IN_INTER; IN_DIFF] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM] THEN
  DISJ_CASES_TAC(ARITH_RULE `n:num < m \/ m <= n`) THENL
   [ASM_SIMP_TAC[SUM_TRIV_NUMSEG; REAL_ABS_NUM; REAL_MUL_RZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `m = 0 + m /\ n = (n - m) + m` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `m:num <= n` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET] THEN UNDISCH_TAC `N + M:num <= m` THEN
  SIMP_TAC[LE_EXISTS] THEN DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[ARITH_RULE `(i + (N + M) + d) - N:num = (M + d) + i`] THEN
  ONCE_REWRITE_TAC[REAL_POW_ADD] THEN REWRITE_TAC[SUM_LMUL; SUM_GP] THEN
  ASM_SIMP_TAC[LT; REAL_LT_IMP_NE] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; NORM_POS_LT; REAL_ABS_MUL] THEN
  REWRITE_TAC[REAL_ABS_POW] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ABS_DIV; REAL_POW_LT; REAL_ARITH
   `&0 < c /\ c < &1 ==> &0 < abs c /\ &0 < abs(&1 - c)`; REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 < x /\ x <= &1 /\ &1 <= e ==> abs(c pow 0 - x) < e`) THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_POW_1_LE; REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[REAL_ARITH `c < &1 ==> x * abs(&1 - c) = (&1 - c) * x`] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_POW_ADD; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_ARITH
   `(((a * b) * c) * d) * e = (e * ((a * b) * c)) * d`] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_POW_LT; REAL_MUL_LID;
               REAL_ARITH `&0 < c ==> abs c = c`] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `xm < e ==> &0 <= (d - &1) * e ==> xm <= d * e`)) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_SUB_LE; GSYM REAL_POW_INV] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN
    MATCH_MP_TAC REAL_INV_1_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_MUL; REAL_LT_DIV; NORM_POS_LT]]);;

(* ------------------------------------------------------------------------- *)
(* Ostensibly weaker versions of the boundedness of partial sums.            *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_PARTIAL_SUMS = prove
 (`!f:num->real^N k.
        bounded { vsum(k..n) f | n IN (:num) }
        ==> bounded { vsum(m..n) f | m IN (:num) /\ n IN (:num) }`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bounded { vsum(0..n) f:real^N | n IN (:num) }` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
    REWRITE_TAC[bounded] THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `sum { i:num | i < k} (\i. norm(f i:real^N)) + B` THEN
    X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i:num < k` THENL
     [MATCH_MP_TAC(REAL_ARITH
       `!y. x <= y /\ y <= a /\ &0 < b ==> x <= a + b`) THEN
      EXISTS_TAC `sum (0..i) (\i. norm(f i:real^N))` THEN
      ASM_SIMP_TAC[VSUM_NORM; FINITE_NUMSEG] THEN
      MATCH_MP_TAC SUM_SUBSET THEN
      REWRITE_TAC[FINITE_NUMSEG; FINITE_NUMSEG_LT; NORM_POS_LE] THEN
      REWRITE_TAC[IN_DIFF; IN_NUMSEG; IN_ELIM_THM] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `k = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC(REAL_ARITH
       `x <= B /\ &0 <= b ==> x <= b + B`) THEN
      ASM_SIMP_TAC[SUM_POS_LE; FINITE_NUMSEG_LT; NORM_POS_LE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:num->real^N`; `0`; `k:num`; `i:num`]
      VSUM_COMBINE_L) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[NUMSEG_LT] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(x) <= a /\ norm(y) <= b ==> norm(x + y) <= a + b`) THEN
    ASM_SIMP_TAC[VSUM_NORM; FINITE_NUMSEG];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MP_TAC(MATCH_MP BOUNDED_DIFFS (W CONJ th)) THEN MP_TAC th) THEN
  REWRITE_TAC[IMP_IMP; GSYM BOUNDED_UNION] THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b ==> c <=> b ==> a ==> c`]
        BOUNDED_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; LEFT_IMP_EXISTS_THM; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `m:num`; `n:num`] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `m = 0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `n:num < m` THENL
   [DISJ2_TAC THEN REPEAT(EXISTS_TAC `vsum(0..0) (f:num->real^N)`) THEN
    ASM_SIMP_TAC[VSUM_TRIV_NUMSEG; VECTOR_SUB_REFL] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISJ2_TAC THEN MAP_EVERY EXISTS_TAC
   [`vsum(0..n) (f:num->real^N)`; `vsum(0..(m-1)) (f:num->real^N)`] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:num->real^N`; `0`; `m:num`; `n:num`]
      VSUM_COMBINE_L) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* General Dirichlet convergence test (could make this uniform on a set).    *)
(* ------------------------------------------------------------------------- *)

let SUMMABLE_BILINEAR_PARTIAL_PRE = prove
 (`!f g h:real^M->real^N->real^P l k.
        bilinear h /\
        ((\n. h (f(n + 1)) (g(n))) --> l) sequentially /\
        summable (from k) (\n. h (f(n + 1) - f(n)) (g(n)))
        ==> summable (from k) (\n. h (f n) (g(n) - g(n - 1)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[summable; sums; FROM_INTER_NUMSEG] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(fun th ->
   REWRITE_TAC[MATCH_MP BILINEAR_VSUM_PARTIAL_PRE th]) THEN
  DISCH_THEN(X_CHOOSE_TAC `l':real^P`) THEN
  EXISTS_TAC `l - (h:real^M->real^N->real^P) (f k) (g(k - 1)) - l'` THEN
  REWRITE_TAC[LIM_CASES_SEQUENTIALLY] THEN
  REPEAT(MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[LIM_CONST]));;

let SERIES_DIRICHLET_BILINEAR = prove
 (`!f g h:real^M->real^N->real^P k m p l.
        bilinear h /\
        bounded { vsum (m..n) f | n IN (:num)} /\
        summable (from p) (\n. lift(norm(g(n + 1) - g(n)))) /\
        ((\n. h (g(n + 1)) (vsum(1..n) f)) --> l) sequentially
        ==> summable (from k) (\n. h (g n) (f n))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUMMABLE_FROM_ELSEWHERE THEN
  EXISTS_TAC `1` THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP BOUNDED_PARTIAL_SUMS) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  SIMP_TAC[IN_ELIM_THM; IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[MESON[] `(!x a b. x = f a b ==> p a b) <=> (!a b. p a b)`] THEN
  X_GEN_TAC `B:real` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BILINEAR_BOUNDED_POS) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC SUMMABLE_EQ THEN
  EXISTS_TAC `\n. (h:real^M->real^N->real^P)
                  (g n) (vsum (1..n) f - vsum (1..n-1) f)` THEN
  SIMP_TAC[IN_FROM; GSYM NUMSEG_RREC] THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_NUMSEG; IN_NUMSEG;
           ARITH_RULE `1 <= n ==> ~(n <= n - 1)`] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BILINEAR_RADD; BILINEAR_RSUB] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SUMMABLE_FROM_ELSEWHERE THEN EXISTS_TAC `p:num` THEN
  MP_TAC(ISPECL [`g:num->real^M`; `\n. vsum(1..n) f:real^N`;
                 `h:real^M->real^N->real^P`; `l:real^P`; `p:num`]
         SUMMABLE_BILINEAR_PARTIAL_PRE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `summable (from p) (lift o (\n. C * B * norm(g(n + 1) - g(n):real^M)))`
  MP_TAC THENL [ASM_SIMP_TAC[o_DEF; LIFT_CMUL; SUMMABLE_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUMMABLE_COMPARISON) THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[IN_FROM; GE; LE_0] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `C * norm(g(n + 1) - g(n):real^M) * norm(vsum (1..n) f:real^N)` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL; NORM_POS_LE]);;

let SERIES_DIRICHLET = prove
 (`!f:num->real^N g N k m.
        bounded { vsum (m..n) f | n IN (:num)} /\
        (!n. N <= n ==> g(n + 1) <= g(n)) /\
        ((lift o g) --> vec 0) sequentially
        ==> summable (from k) (\n. g(n) % f(n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real^N`; `lift o (g:num->real)`;
                 `\x y:real^N. drop x % y`] SERIES_DIRICHLET_BILINEAR) THEN
  REWRITE_TAC[o_THM; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `N:num`; `vec 0:real^N`] THEN CONJ_TAC THENL
   [REWRITE_TAC[bilinear; linear; DROP_ADD; DROP_CMUL] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
  FIRST_ASSUM(MP_TAC o SPEC `1` o MATCH_MP SEQ_OFFSET) THEN
  REWRITE_TAC[o_THM] THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUMMABLE_EQ_EVENTUALLY THEN
    EXISTS_TAC `\n. lift(g(n) - g(n + 1))` THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_ARITH `b <= a ==> abs(b - a) = a - b`];
      REWRITE_TAC[summable; sums; FROM_INTER_NUMSEG; VSUM_DIFFS; LIFT_SUB] THEN
      REWRITE_TAC[LIM_CASES_SEQUENTIALLY] THEN
      EXISTS_TAC `lift(g(N:num)) - vec 0` THEN
      MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[LIM_CONST]];
    MATCH_MP_TAC LIM_NULL_VMUL_BOUNDED THEN ASM_REWRITE_TAC[o_DEF] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP BOUNDED_PARTIAL_SUMS) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
    SIMP_TAC[IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Banach fixed point theorem (not really topological...)                    *)
(* ------------------------------------------------------------------------- *)

let BANACH_FIX = prove
 (`!f s c. complete s /\ ~(s = {}) /\
           &0 <= c /\ c < &1 /\
           (IMAGE f s) SUBSET s /\
           (!x y. x IN s /\ y IN s ==> dist(f(x),f(y)) <= c * dist(x,y))
           ==> ?!x:real^N. x IN s /\ (f x = x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `dist((f:real^N->real^N) x,f y) <= c * dist(x,y)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ARITH `a <= c * a <=> &0 <= --a * (&1 - c)`] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_SUB_LT; real_div] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ARITH `&0 <= --x <=> ~(&0 < x)`] THEN
    MESON_TAC[DIST_POS_LT]] THEN
  STRIP_ASSUME_TAC(prove_recursive_functions_exist num_RECURSION
    `(z 0 = @x:real^N. x IN s) /\ (!n. z(SUC n) = f(z n))`) THEN
  SUBGOAL_THEN `!n. (z:num->real^N) n IN s` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MEMBER_NOT_EMPTY; SUBSET; IN_IMAGE];
    ALL_TAC] THEN
  UNDISCH_THEN `z 0 = @x:real^N. x IN s` (K ALL_TAC) THEN
  SUBGOAL_THEN `?x:real^N. x IN s /\ (z --> x) sequentially` MP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `e = dist(f(a:real^N),a)` THEN
    SUBGOAL_THEN `~(&0 < e)` (fun th -> ASM_MESON_TAC[th; DIST_POS_LT]) THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    SUBGOAL_THEN
     `dist(f(z N),a:real^N) < e / &2 /\ dist(f(z(N:num)),f(a)) < e / &2`
     (fun th -> ASM_MESON_TAC[th; DIST_TRIANGLE_HALF_R; REAL_LT_REFL]) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[ARITH_RULE `N <= SUC N`]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `c * dist((z:num->real^N) N,a)` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x < y /\ c * x <= &1 * x ==> c * x < y`) THEN
    ASM_SIMP_TAC[LE_REFL; REAL_LE_RMUL; DIST_POS_LE; REAL_LT_IMP_LE]] THEN
  FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [complete]) THEN
  ASM_REWRITE_TAC[CAUCHY] THEN
  SUBGOAL_THEN `!n. dist(z(n):real^N,z(SUC n)) <= c pow n * dist(z(0),z(1))`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN
    REWRITE_TAC[real_pow; ARITH; REAL_MUL_LID; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c * dist(z(n):real^N,z(SUC n))` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_LE_LMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m n:num. (&1 - c) * dist(z(m):real^N,z(m+n))
                <= c pow m * dist(z(0),z(1)) * (&1 - c pow n)`
  ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THENL
     [REWRITE_TAC[ADD_CLAUSES; DIST_REFL; REAL_MUL_RZERO] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; DIST_POS_LE; REAL_SUB_LE;
                   REAL_POW_1_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
    `(&1 - c) * (dist(z m:real^N,z(m + n)) + dist(z(m + n),z(m + SUC n)))` THEN
    ASM_SIMP_TAC[REAL_LE_LMUL; REAL_SUB_LE; REAL_LT_IMP_LE; DIST_TRIANGLE] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
      `c * x <= y ==> c * x' + y <= y' ==> c * (x + x') <= y'`)) THEN
    REWRITE_TAC[REAL_ARITH
     `q + a * b * (&1 - x) <= a * b * (&1 - y) <=> q <= a * b * (x - y)`] THEN
    REWRITE_TAC[ADD_CLAUSES; real_pow] THEN
    REWRITE_TAC[REAL_ARITH `a * b * (d - c * d) = (&1 - c) * a * d * b`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_SUB_LE; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[GSYM REAL_POW_ADD; REAL_MUL_ASSOC] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(z:num->real^N) 0 = z 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[GE; LE_0] THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `n:num`]) THEN
    REWRITE_TAC[ADD_CLAUSES; DIST_REFL; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    ASM_CASES_TAC `(z:num->real^N) 0 = z n` THEN
    ASM_REWRITE_TAC[DIST_REFL; REAL_NOT_LE] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; DIST_POS_LT; REAL_SUB_LT];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `e * (&1 - c) / dist((z:num->real^N) 0,z 1)`]
   REAL_ARCH_POW_INV) THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_SUB_LT; DIST_POS_LT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  REWRITE_TAC[real_div; GE; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; GSYM real_div; DIST_POS_LT] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_SUB_LT] THEN DISCH_TAC THEN
  REWRITE_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN X_GEN_TAC `d:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(REAL_ARITH
    `d < e ==> x <= d ==> x < e`)) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `d:num`]) THEN
  MATCH_MP_TAC(REAL_ARITH
  `(c * d) * e <= (c * d) * &1 ==> x * y <= c * d * e ==> y * x <= c * d`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; DIST_POS_LE; REAL_ARITH
   `&0 <= x ==> &1 - x <= &1`]);;

(* ------------------------------------------------------------------------- *)
(* Edelstein fixed point theorem.                                            *)
(* ------------------------------------------------------------------------- *)

let EDELSTEIN_FIX = prove
 (`!f s. compact s /\ ~(s = {}) /\ (IMAGE f s) SUBSET s /\
         (!x y. x IN s /\ y IN s /\ ~(x = y) ==> dist(f(x),f(y)) < dist(x,y))
         ==> ?!x:real^N. x IN s /\ f x = x`,
  MAP_EVERY X_GEN_TAC [`g:real^N->real^N`; `s:real^N->bool`] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[REAL_LT_REFL]] THEN
  SUBGOAL_THEN
   `!x y. x IN s /\ y IN s ==> dist((g:real^N->real^N)(x),g(y)) <= dist(x,y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real^N = y` THEN
    ASM_SIMP_TAC[DIST_REFL; REAL_LE_LT];
    ALL_TAC] THEN
  ASM_CASES_TAC `?x:real^N. x IN s /\ ~(g x = x)` THENL
   [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `y = (g:real^N->real^N) x` THEN
  SUBGOAL_THEN `(y:real^N) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_PASTECART o W CONJ) THEN
  REWRITE_TAC[compact] THEN
  (STRIP_ASSUME_TAC o prove_general_recursive_function_exists)
    `?f:num->real^N->real^N.
        (!z. f 0 z = z) /\ (!z n. f (SUC n) z = g(f n z))` THEN
  SUBGOAL_THEN `!n z. z IN s ==> (f:num->real^N->real^N) n z IN s`
  STRIP_ASSUME_TAC THENL [INDUCT_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!m n w z. m <= n /\ w IN s /\ z IN s
              ==> dist((f:num->real^N->real^N) n w,f n z) <= dist(f m w,f m z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
    MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_SIMP_TAC[REAL_LE_REFL] THEN MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC
   `\n:num. pastecart (f n (x:real^N)) (f n y:real^N)`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`l:real^(N,N)finite_sum`; `s:num->num`] THEN
  REWRITE_TAC[o_DEF; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST_ALL_TAC) THEN
  SUBGOAL_THEN
   `(\x:real^(N,N)finite_sum. fstcart x) continuous_on UNIV /\
    (\x:real^(N,N)finite_sum. sndcart x) continuous_on UNIV`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    REWRITE_TAC[ETA_AX; LINEAR_FSTCART; LINEAR_SNDCART];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY; IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th))) THEN
  REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART; IMP_IMP] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  DISCH_THEN(fun th -> CONJUNCTS_THEN2 (LABEL_TAC "A") (LABEL_TAC "B") th THEN
    MP_TAC(MATCH_MP LIM_SUB th)) THEN
  REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "AB") THEN
  SUBGOAL_THEN
   `!n. dist(a:real^N,b) <= dist((f:num->real^N->real^N) n x,f n y)`
  STRIP_ASSUME_TAC THENL
   [X_GEN_TAC `N:num` THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
    USE_THEN "AB" (MP_TAC o REWRITE_RULE[LIM_SEQUENTIALLY]) THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o MATCH_MP th)) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `M:num` THEN
    DISCH_THEN(MP_TAC o SPEC `M + N:num`) THEN REWRITE_TAC[LE_ADD] THEN
    MATCH_MP_TAC(NORM_ARITH
     `dist(fx,fy) <= dist(x,y)
      ==> ~(dist(fx - fy,a - b) < dist(a,b) - dist(x,y))`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `M + N:num` o MATCH_MP MONOTONE_BIGGER) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `b:real^N = a` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    ABBREV_TAC `e = dist(a,b) - dist((g:real^N->real^N) a,g b)` THEN
    SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_SUB_LT]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?n. dist((f:num->real^N->real^N) n x,a) < e / &2 /\
          dist(f n y,b) < e / &2`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY (fun s -> USE_THEN s (MP_TAC o SPEC `e / &2` o
        REWRITE_RULE[LIM_SEQUENTIALLY])) ["A"; "B"] THEN
      ASM_REWRITE_TAC[REAL_HALF] THEN
      DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
      EXISTS_TAC `(s:num->num) (M + N)` THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `dist(f (SUC n) x,(g:real^N->real^N) a) +
                  dist((f:num->real^N->real^N) (SUC n) y,g b) < e`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `x < e / &2 /\ y < e / &2 ==> x + y < e`) THEN
      CONJ_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `dist(x,y) < e
        ==> dist(g x,g y) <= dist(x,y) ==> dist(g x,g y) < e`)) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPEC `SUC n` (ASSUME
    `!n. dist (a:real^N,b) <=
         dist ((f:num->real^N->real^N) n x,f n y)`)) THEN
    EXPAND_TAC "e" THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `\n:num. (f:num->real^N->real^N) (SUC(s n)) x` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(g:real^N->real^N) continuous_on s` MP_TAC THENL
     [REWRITE_TAC[continuous_on] THEN ASM_MESON_TAC[REAL_LET_TRANS];
      ALL_TAC] THEN
    REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY; o_DEF] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    SUBGOAL_THEN `!n. (f:num->real^N->real^N) (SUC n) x = f n y`
     (fun th -> ASM_SIMP_TAC[th]) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Closest point of a (closed) set to a point.                               *)
(* ------------------------------------------------------------------------- *)

let closest_point = new_definition
 `closest_point s a = @x. x IN s /\ !y. y IN s ==> dist(a,x) <= dist(a,y)`;;

let CLOSEST_POINT_EXISTS = prove
 (`!s a. closed s /\ ~(s = {})
         ==> (closest_point s a) IN s /\
             !y. y IN s ==> dist(a,closest_point s a) <= dist(a,y)`,
  REWRITE_TAC[closest_point] THEN CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
  REWRITE_TAC[DISTANCE_ATTAINS_INF]);;

let CLOSEST_POINT_IN_SET = prove
 (`!s a. closed s /\ ~(s = {}) ==> (closest_point s a) IN s`,
  MESON_TAC[CLOSEST_POINT_EXISTS]);;

let CLOSEST_POINT_LE = prove
 (`!s a x. closed s /\ x IN s ==> dist(a,closest_point s a) <= dist(a,x)`,
  MESON_TAC[CLOSEST_POINT_EXISTS; MEMBER_NOT_EMPTY]);;

let CLOSEST_POINT_SELF = prove
 (`!s x:real^N. x IN s ==> closest_point s x = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[closest_point] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_SIMP_TAC[DIST_LE_0; DIST_REFL];
    STRIP_TAC THEN ASM_REWRITE_TAC[DIST_REFL; DIST_POS_LE]]);;

let CLOSEST_POINT_REFL = prove
 (`!s x:real^N. closed s /\ ~(s = {}) ==> (closest_point s x = x <=> x IN s)`,
  MESON_TAC[CLOSEST_POINT_IN_SET; CLOSEST_POINT_SELF]);;

let DIST_CLOSEST_POINT_LIPSCHITZ = prove
 (`!s x y:real^N.
        closed s /\ ~(s = {})
        ==> abs(dist(x,closest_point s x) - dist(y,closest_point s y))
            <= dist(x,y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CLOSEST_POINT_EXISTS) THEN
  DISCH_THEN(fun th ->
    CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPEC `closest_point s (y:real^N)`) (SPEC `x:real^N` th) THEN
    CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPEC `closest_point s (x:real^N)`) (SPEC `y:real^N` th)) THEN
  ASM_REWRITE_TAC[] THEN NORM_ARITH_TAC);;

let CONTINUOUS_AT_DIST_CLOSEST_POINT = prove
 (`!s x:real^N.
        closed s /\ ~(s = {})
        ==> (\x. lift(dist(x,closest_point s x))) continuous (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[continuous_at; DIST_LIFT] THEN
  ASM_MESON_TAC[DIST_CLOSEST_POINT_LIPSCHITZ; REAL_LET_TRANS]);;

let CONTINUOUS_ON_DIST_CLOSEST_POINT = prove
 (`!s t. closed s /\ ~(s = {})
         ==> (\x. lift(dist(x,closest_point s x))) continuous_on t`,
  MESON_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON;
            CONTINUOUS_AT_DIST_CLOSEST_POINT]);;

(* ------------------------------------------------------------------------- *)
(* Urysohn's lemma (for real^N, where the proof is easy using distances).    *)
(* ------------------------------------------------------------------------- *)

let URYSOHN = prove
 (`!s t a b.
        closed s /\ closed t /\ s INTER t = {}
        ==> ?f:real^N->real^M.
               f continuous_on (:real^N) /\ (!x. f(x) IN segment[a,b]) /\
               (!x. x IN s ==> f x = a) /\ (!x. x IN t ==> f x = b)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [EXISTS_TAC `(\x. b):real^N->real^M` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; CONTINUOUS_ON_CONST; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [EXISTS_TAC `(\x. a):real^N->real^M` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; CONTINUOUS_ON_CONST; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  EXISTS_TAC `\x:real^N. a + dist(x,closest_point s x) /
                             (dist(x,closest_point s x) +
                             dist(x,closest_point t x)) % (b - a:real^M)` THEN
  SIMP_TAC[CLOSEST_POINT_SELF; DIST_REFL] THEN
  REWRITE_TAC[REAL_ARITH `&0 / x = &0`; VECTOR_ADD_RID; VECTOR_MUL_LZERO] THEN
  SUBGOAL_THEN
   `!x:real^N. &0 < dist(x,closest_point s x) + dist(x,closest_point t x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
      `&0 <= x /\ &0 <= y /\ ~(x = &0 /\ y = &0) ==> &0 < x + y`) THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN
    ASM_SIMP_TAC[CLOSEST_POINT_REFL; DIST_EQ_0; DIST_POS_LE] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[real_div; GSYM VECTOR_MUL_ASSOC] THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; o_DEF] THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_DIST_CLOSEST_POINT] THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_DIST_CLOSEST_POINT];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[segment; IN_ELIM_THM] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; LEFT_OR_DISTRIB; VECTOR_ARITH
     `a + x % (b - a) = (&1 - u) % a + u % b <=> (x - u) % (b - a) = vec 0`;
     EXISTS_OR_THM] THEN
    DISJ1_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[REAL_SUB_0; UNWIND_THM1] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_ADD; DIST_POS_LE; REAL_LE_LDIV_EQ] THEN
    NORM_ARITH_TAC;
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN REWRITE_TAC[REAL_ADD_RID] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `a + x = b <=> x = &1 % (b - a)`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC REAL_DIV_REFL THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN
    ASM_SIMP_TAC[CLOSEST_POINT_REFL; DIST_EQ_0] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Tietze extension theorem, likewise just for real^N.                       *)
(* ------------------------------------------------------------------------- *)

let TIETZE_STEP = prove
 (`!f:real^N->real^1 s B.
        &0 < B /\ closed s /\
        f continuous_on s /\
        (!x. x IN s ==> norm(f x) <= B)
        ==> ?g. g continuous_on (:real^N) /\
                (!x. norm(g x) <= B / &3) /\
                (!x. x IN s ==> norm(f x - g x) <= &2 / &3 * B)`,
  REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{x:real^N | x IN s /\ f x IN {y | drop y <= --(B / &3)}}`;
                 `{x:real^N | x IN s /\ f x IN {y | drop y >= B / &3}}`;
                 `lift(--(B / &3))`; `lift(B / &3)`] URYSOHN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_INTER] THEN
      ASM_REAL_ARITH_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
    ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`lift(&1)`; `--(B / &3)`] CLOSED_HALFSPACE_LE);
      MP_TAC(ISPECL [`lift(&1)`; `B / &3`] CLOSED_HALFSPACE_GE)] THEN
    REWRITE_TAC[DOT_1; GSYM drop; LIFT_DROP; REAL_MUL_LID];
    ASM_SIMP_TAC[SEGMENT_1; IN_ELIM_THM; LIFT_DROP; IN_INTERVAL_1;
                 REAL_ARITH `&0 < B ==> --(B / &3) <= B / &3`] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^1` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[NORM_REAL; GSYM drop] THEN
    ASM_REWRITE_TAC[GSYM REAL_BOUNDS_LE] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN REWRITE_TAC[DROP_SUB; REAL_BOUNDS_LE] THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (REAL_ARITH `drop(f x) <= --(B / &3) \/ drop(f x) >= B / &3 \/
                  abs(drop(f(x:real^N))) <= B / &3`)
    THENL
     [UNDISCH_THEN
       `!x:real^N. x IN s /\ drop(f x) <= --(B / &3) ==> g x = lift(--(B / &3))`
       (MP_TAC o SPEC `x:real^N`);
      UNDISCH_THEN
       `!x:real^N. x IN s /\ drop(f x) >= B / &3 ==> g x = lift(B / &3)`
       (MP_TAC o SPEC `x:real^N`);
      MATCH_MP_TAC(REAL_ARITH
       `abs(f) <= B / &3 /\ --(B / &3) <= g /\ g <= B / &3
        ==> abs(f - g) <= &2 / &3 * B`)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_THEN `!x:real^N. x IN s ==> abs(drop(f x)) <= B`
        (MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC]);;

let TIETZE = prove
 (`!f:real^N->real^1 s B.
        &0 <= B /\
        closed s /\
        f continuous_on s /\
        (!x. x IN s ==> norm(f x) <= B)
        ==> ?g. g continuous_on (:real^N) /\
                (!x. x IN s ==> g x = f x) /\
                (!x. norm(g x) <= B)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
   `&0 <= B ==> B = &0 \/ &0 < B`)) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
   [EXISTS_TAC `\x:real^N. (vec 0:real^1)` THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_CONST; NORM_0; REAL_LE_REFL] THEN
    ASM_MESON_TAC[NORM_LE_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real^1`; `s:real^N->bool`; `B:real`]
        TIETZE_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:real^N->real^1` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?g. (g 0 = (g0:real^N->real^1)) /\
        (!n. g(SUC n) =
               @h. h continuous_on (:real^N) /\
                   (!x. norm(h x) <= &2 pow SUC n * B / &3 pow (SUC n + 1)) /\
                   (!x. x IN s ==> norm(f x - vsum(0..n) (\i. g i x) - h x)
                       <= &2 pow (SUC n + 1) * B / &3 pow (SUC n + 1)))`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[VSUM_REAL; FINITE_NUMSEG; o_DEF] THEN
    W(ACCEPT_TAC o prove_general_recursive_function_exists o snd);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (!m. m < n ==> g m continuous_on (:real^N)) /\
        g n continuous_on (:real^N) /\
        (!x. norm(g n x:real^1) <= &2 pow n * B / &3 pow (n + 1)) /\
        (!x. x IN s ==> norm(f x - vsum(0..n) (\i. g i x))
        <= &2 pow (n + 1) * B / &3 pow (n + 1))`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LT] THENL
     [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REWRITE_TAC[REAL_MUL_LID; REAL_ARITH `&2 * B / &3 = &2 / &3 * B`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[MESON[] `(!m:num. m = n \/ m < n ==> P m) <=>
                             (!m. m < n ==> P m) /\ P n`] THEN
    REWRITE_TAC[LE_0; VECTOR_ARITH `f - (g + h):real^1 = f - g - h`] THEN
    CONV_TAC SELECT_CONV THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_ARITH
     `(&2 pow (SUC n) * &2 pow 1) * B = &2 * &2 pow (SUC n) * B`] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_POW_1] THEN
    REWRITE_TAC[REAL_ARITH `a * b * inv c * inv d = (a * b / c) / d`] THEN
    REWRITE_TAC[REAL_ARITH `&2 * x / &3 = &2 / &3 * x`] THEN
    MATCH_MP_TAC TIETZE_STEP THEN
    ASM_SIMP_TAC[REAL_LT_DIV; ADD1; REAL_LT_MUL; REAL_POW_LT;
                 REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN REWRITE_TAC[LE_LT] THEN
    GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^N)` THEN ASM_SIMP_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC `(h:num->real^N->real^1) = \n x. vsum(0..n) (\i. g i x)` THEN
  SUBGOAL_THEN
   `?k:real^N->real^1.
     !e. &0 < e
         ==> ?N:num. !n x.
                 N <= n /\ x IN (:real^N) ==> dist(vsum (from 0 INTER (0..n))
                                                  (\i. g i x),k x) < e`
  MP_TAC THENL
   [REWRITE_TAC[SERIES_CAUCHY_UNIFORM]; ALL_TAC] THEN
  REWRITE_TAC[FROM_0; INTER_UNIV; IN_UNIV] THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`&2 / &3`; `e / B`] REAL_ARCH_POW_INV) THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `x:real^N`] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum(m..n) (\i. &2 pow i * B / &3 pow (i + 1))` THEN
    ASM_SIMP_TAC[VSUM_NORM_LE; FINITE_NUMSEG] THEN
    REWRITE_TAC[REAL_POW_ADD; real_div; REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_ARITH `x * B * inv y * inv(&3 pow 1) = B / &3 * x / y`;
                SUM_LMUL; GSYM REAL_POW_DIV] THEN
    REWRITE_TAC[SUM_GP] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `B / &3 * x / (&1 / &3) < e <=> x * B < e`] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < y /\ x < e ==> x - y < e`) THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&2 / &3) pow N` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^N->real^1` THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` CONTINUOUS_UNIFORM_LIMIT) THEN
    EXISTS_TAC `\n x:real^N. vsum (0..n) (\i. g i x :real^1)` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    ASM_REWRITE_TAC[IN_UNIV; IMP_IMP; RIGHT_IMP_FORALL_THM; GSYM dist] THEN
    EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(NORM_ARITH `~(&0 < norm(x - y)) ==> x = y`) THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `norm((k:real^N->real^1) x - f x) / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF; NOT_EXISTS_THM] THEN
    X_GEN_TAC `N1:num` THEN DISCH_THEN(LABEL_TAC "*") THEN
    MP_TAC(ISPECL [`&2 / &3`; `norm((k:real^N->real^1) x - f x) / &2 / B`]
        REAL_ARCH_POW_INV) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "+")) THEN
    REMOVE_THEN "*" (MP_TAC o SPECL [`N1 + N2:num`; `x:real^N`]) THEN
    REWRITE_TAC[LE_ADD] THEN MATCH_MP_TAC(NORM_ARITH
     `norm(f - s) < norm(k - f) / &2
      ==> ~(dist(s,k) < norm(k - f) / &2)`) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `B * (&2 / &3) pow N2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 pow ((N1 + N2) + 1) * B / &3 pow ((N1 + N2) + 1)` THEN
    ASM_SIMP_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x * B / y = B * x / y`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; GSYM REAL_POW_DIV] THEN
    MATCH_MP_TAC REAL_POW_MONO_INV THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC;
    X_GEN_TAC `x:real^N` THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
    EXISTS_TAC `\n. vsum(0..n) (\i. (g:num->real^N->real^1) i x)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[LIM_SEQUENTIALLY] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n) (\i. &2 pow i * B / &3 pow (i + 1))` THEN
    ASM_SIMP_TAC[VSUM_NORM_LE; FINITE_NUMSEG] THEN
    REWRITE_TAC[REAL_POW_ADD; real_div; REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_ARITH `x * B * inv y * inv(&3 pow 1) = B / &3 * x / y`;
                SUM_LMUL; GSYM REAL_POW_DIV] THEN
    REWRITE_TAC[REAL_ARITH `B / &3 * x <= B <=> B * x / &3 <= B * &1`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[SUM_GP] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    COND_CASES_TAC THENL
     [SIMP_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_POS];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `x / (&1 / &3) <= &3 <=> x <= &1`] THEN
    REWRITE_TAC[REAL_ARITH `&1 - x <= &1 <=> &0 <= x`] THEN
    MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* The same result for intervals in real^1.                                  *)
(* ------------------------------------------------------------------------- *)

let TIETZE_CLOSED_INTERVAL_1 = prove
 (`!f:real^N->real^1 s a b.
        drop a <= drop b /\
        closed s /\
        f continuous_on s /\
        (!x. x IN s ==> f x IN interval[a,b])
        ==> ?g. g continuous_on (:real^N) /\
                (!x. x IN s ==> g x = f x) /\
                (!x. g(x) IN interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. (f:real^N->real^1)(x) - inv(&2) % (a + b)`;
                 `s:real^N->bool`; `(drop(b) - drop(a)) / &2`]
        TIETZE) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_INTERVAL_1; NORM_REAL; GSYM drop] THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL; DROP_SUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^1` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x. (g:real^N->real^1)(x) + inv(&2) % (a + b)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC;
    X_GEN_TAC `x:real^N` THEN UNDISCH_TAC
     `!x. norm((g:real^N->real^1) x) <= (drop b - drop a) / &2` THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_INTERVAL_1; NORM_REAL; GSYM drop] THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL; DROP_SUB] THEN REAL_ARITH_TAC]);;

let TIETZE_OPEN_INTERVAL_1 = prove
 (`!f:real^N->real^1 s a b.
        drop a < drop b /\
        closed s /\
        f continuous_on s /\
        (!x. x IN s ==> f x IN interval(a,b))
        ==> ?g. g continuous_on (:real^N) /\
                (!x. x IN s ==> g x = f x) /\
                (!x. g(x) IN interval(a,b))`,
  REWRITE_TAC[IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^1`; `s:real^N->bool`;
                 `a:real^1`; `b:real^1`] TIETZE_CLOSED_INTERVAL_1) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[IN_INTERVAL_1; REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^1` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`;
                 `{x | (g:real^N->real^1) x IN {a,b}}`;
                 `vec 1:real^1`; `vec 0:real^1`] URYSOHN) THEN
  ASM_REWRITE_TAC[SEGMENT_1; DROP_VEC; REAL_OF_NUM_LE; ARITH] THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
      ASM_SIMP_TAC[FINITE_IMP_CLOSED; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
      ASM SET_TAC[REAL_LT_REFL]];
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(\x. &1 / &2 % (a + b) +
                    drop(h x) % (g x - &1 / &2 % (a + b))):real^N->real^1` THEN
    ASM_SIMP_TAC[DROP_CMUL; DROP_VEC; VECTOR_MUL_LID] THEN
    REWRITE_TAC[VECTOR_ARITH `a + x - a:real^N = x`] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; ETA_AX] THEN
      ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL; DROP_SUB] THEN
    REWRITE_TAC[REAL_ARITH
     `a < &1 / &2 * (a + b) + x /\ &1 / &2 * (a + b) + x < b <=>
      abs(x) < &1 * (b - a) / &2`] THEN
    ASM_CASES_TAC `(g:real^N->real^1) x IN {a,b}` THENL
     [ASM_SIMP_TAC[DROP_VEC; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC(REAL_ARITH
       `y < a /\ abs(x) * y <= &1 * y ==> abs(x) * y < a`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC(REAL_ARITH
         `a < x /\ x < b ==> abs(x - &1 / &2 * (a + b)) < (b - a) / &2`) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
        ASM_REWRITE_TAC[REAL_LT_LE; DROP_EQ] THEN ASM SET_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`)) THEN
        REAL_ARITH_TAC]]]);;

let TIETZE_UNBOUNDED_1 = prove
 (`!f:real^N->real^1 s.
        closed s /\ f continuous_on s
        ==> ?g. g continuous_on (:real^N) /\ (!x. x IN s ==> g x = f x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^1`; `vec 1:real^1`]
    HOMEOMORPHIC_OPEN_INTERVAL_UNIV) THEN
  REWRITE_TAC[INTERVAL_NE_EMPTY; VEC_COMPONENT; REAL_LT_01] THEN
  REWRITE_TAC[HOMEOMORPHIC_MINIMAL; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:real^1->real^1`; `k:real^1->real^1`] THEN
  REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(k:real^1->real^1) o (f:real^N->real^1)`;
                 `s:real^N->bool`; `vec 0:real^1`; `vec 1:real^1`]
        TIETZE_OPEN_INTERVAL_1) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[DROP_VEC; REAL_LT_01; o_THM] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^1)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(h:real^1->real^1) o (g:real^N->real^1)` THEN
    ASM_SIMP_TAC[o_THM] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
   EXISTS_TAC `interval(vec 0:real^1,vec 1)` THEN
   ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Now for general intervals in real^N by componentwise extension.           *)
(* ------------------------------------------------------------------------- *)

let TIETZE_CLOSED_INTERVAL = prove
 (`!f:real^M->real^N s a b.
        ~(interval[a,b] = {}) /\
        closed s /\
        f continuous_on s /\
        (!x. x IN s ==> f x IN interval[a,b])
        ==> ?g. g continuous_on (:real^M) /\
                (!x. x IN s ==> g x = f x) /\
                (!x. g(x) IN interval[a,b])`,
  REWRITE_TAC[INTERVAL_NE_EMPTY] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> ?g. g continuous_on (:real^M) /\
                (!x. x IN s ==> g x = lift((f:real^M->real^N)(x)$i)) /\
                (!x. g(x) IN interval[lift((a:real^N)$i),lift((b:real^N)$i)])`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TIETZE_CLOSED_INTERVAL_1 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN
    ASM_SIMP_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    SUBGOAL_THEN `(\x. lift((f:real^M->real^N) x$i)) = (\x. lift(x$i)) o f`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; CONTINUOUS_ON_COMPOSE];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:num->real^M->real^1`) THEN
  EXISTS_TAC `(\x. lambda i. drop(g i x)):real^M->real^N` THEN
  SIMP_TAC[CART_EQ; IN_INTERVAL; LAMBDA_BETA] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; LIFT_DROP; ETA_AX];
    ASM_SIMP_TAC[LIFT_DROP]]);;

let TIETZE_OPEN_INTERVAL = prove
 (`!f:real^M->real^N s a b.
        ~(interval(a,b) = {}) /\
        closed s /\
        f continuous_on s /\
        (!x. x IN s ==> f x IN interval(a,b))
        ==> ?g. g continuous_on (:real^M) /\
                (!x. x IN s ==> g x = f x) /\
                (!x. g(x) IN interval(a,b))`,
  REWRITE_TAC[INTERVAL_NE_EMPTY] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> ?g. g continuous_on (:real^M) /\
                (!x. x IN s ==> g x = lift((f:real^M->real^N)(x)$i)) /\
                (!x. g(x) IN interval(lift((a:real^N)$i),lift((b:real^N)$i)))`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TIETZE_OPEN_INTERVAL_1 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN
    ASM_SIMP_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    SUBGOAL_THEN `(\x. lift((f:real^M->real^N) x$i)) = (\x. lift(x$i)) o f`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; CONTINUOUS_ON_COMPOSE];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:num->real^M->real^1`) THEN
  EXISTS_TAC `(\x. lambda i. drop(g i x)):real^M->real^N` THEN
  SIMP_TAC[CART_EQ; IN_INTERVAL; LAMBDA_BETA] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; LIFT_DROP; ETA_AX];
    ASM_SIMP_TAC[LIFT_DROP]]);;

let TIETZE_UNBOUNDED = prove
 (`!f:real^M->real^N s.
        closed s /\ f continuous_on s
        ==> ?g. g continuous_on (:real^M) /\
                (!x. x IN s ==> g x = f x)`,
  REWRITE_TAC[INTERVAL_NE_EMPTY] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> ?g. g continuous_on (:real^M) /\
                (!x. x IN s ==> g x = lift((f:real^M->real^N)(x)$i))`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TIETZE_UNBOUNDED_1 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN
    ASM_SIMP_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    SUBGOAL_THEN `(\x. lift((f:real^M->real^N) x$i)) = (\x. lift(x$i)) o f`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; CONTINUOUS_ON_COMPOSE];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:num->real^M->real^1`) THEN
  EXISTS_TAC `(\x. lambda i. drop(g i x)):real^M->real^N` THEN
  SIMP_TAC[CART_EQ; IN_INTERVAL; LAMBDA_BETA] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; LIFT_DROP; ETA_AX];
    ASM_SIMP_TAC[LIFT_DROP]]);;
