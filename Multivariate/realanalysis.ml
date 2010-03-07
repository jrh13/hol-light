(* ========================================================================= *)
(* Some analytic concepts for R instead of R^1.                              *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

needs "Library/binomial.ml";;
needs "Multivariate/measure.ml";;
needs "Multivariate/transcendentals.ml";;

(* ------------------------------------------------------------------------- *)
(* Open-ness and closedness of a set of reals.                               *)
(* ------------------------------------------------------------------------- *)

let real_open = new_definition
  `real_open s <=>
      !x. x IN s ==> ?e. &0 < e /\ !x'. abs(x' - x) < e ==> x' IN s`;;

let real_closed = new_definition
 `real_closed s <=> real_open((:real) DIFF s)`;;

let euclideanreal = new_definition
 `euclideanreal = topology real_open`;;

let REAL_OPEN_EMPTY = prove
 (`real_open {}`,
  REWRITE_TAC[real_open; NOT_IN_EMPTY]);;

let REAL_OPEN_UNIV = prove
 (`real_open(:real)`,
  REWRITE_TAC[real_open; IN_UNIV] THEN MESON_TAC[REAL_LT_01]);;

let REAL_OPEN_INTER = prove
 (`!s t. real_open s /\ real_open t ==> real_open (s INTER t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_open; AND_FORALL_THM; IN_INTER] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `d1:real`) (X_CHOOSE_TAC `d2:real`)) THEN
  MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN
  ASM_MESON_TAC[REAL_LT_TRANS]);;

let REAL_OPEN_UNIONS = prove
 (`(!s. s IN f ==> real_open s) ==> real_open(UNIONS f)`,
  REWRITE_TAC[real_open; IN_UNIONS] THEN MESON_TAC[]);;

let REAL_OPEN_IN = prove
 (`!s. real_open s <=> open_in euclideanreal s`,
  GEN_TAC THEN REWRITE_TAC[euclideanreal] THEN CONV_TAC SYM_CONV THEN
  AP_THM_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 topology_tybij)] THEN
  REWRITE_TAC[REWRITE_RULE[IN] istopology] THEN
  REWRITE_TAC[REAL_OPEN_EMPTY; REAL_OPEN_INTER; SUBSET] THEN
  MESON_TAC[IN; REAL_OPEN_UNIONS]);;

let TOPSPACE_EUCLIDEANREAL = prove
 (`topspace euclideanreal = (:real)`,
  REWRITE_TAC[topspace; EXTENSION; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[REAL_OPEN_UNIV; IN_UNIV; REAL_OPEN_IN]);;

let TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY = prove
 (`!s. topspace (subtopology euclideanreal s) = s`,
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL; TOPSPACE_SUBTOPOLOGY; INTER_UNIV]);;

let REAL_CLOSED_IN = prove
 (`!s. real_closed s <=> closed_in euclideanreal s`,
  REWRITE_TAC[real_closed; closed_in; TOPSPACE_EUCLIDEANREAL;
              REAL_OPEN_IN; SUBSET_UNIV]);;

let REAL_OPEN_UNION = prove
 (`!s t. real_open s /\ real_open t ==> real_open(s UNION t)`,
  REWRITE_TAC[REAL_OPEN_IN; OPEN_IN_UNION]);;

let REAL_OPEN_SUBREAL_OPEN = prove
 (`!s. real_open s <=> !x. x IN s ==> ?t. real_open t /\ x IN t /\ t SUBSET s`,
  REWRITE_TAC[REAL_OPEN_IN; GSYM OPEN_IN_SUBOPEN]);;

let REAL_CLOSED_EMPTY = prove
 (`real_closed {}`,
  REWRITE_TAC[REAL_CLOSED_IN; CLOSED_IN_EMPTY]);;

let REAL_CLOSED_UNIV = prove
 (`real_closed(:real)`,
  REWRITE_TAC[REAL_CLOSED_IN; GSYM TOPSPACE_EUCLIDEANREAL; CLOSED_IN_TOPSPACE]);;

let REAL_CLOSED_UNION = prove
 (`!s t. real_closed s /\ real_closed t ==> real_closed(s UNION t)`,
  REWRITE_TAC[REAL_CLOSED_IN; CLOSED_IN_UNION]);;

let REAL_CLOSED_INTER = prove
 (`!s t. real_closed s /\ real_closed t ==> real_closed(s INTER t)`,
  REWRITE_TAC[REAL_CLOSED_IN; CLOSED_IN_INTER]);;

let REAL_CLOSED_INTERS = prove
 (`!f. (!s. s IN f ==> real_closed s) ==> real_closed(INTERS f)`,
  REWRITE_TAC[REAL_CLOSED_IN] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `f:(real->bool)->bool = {}` THEN
  ASM_SIMP_TAC[CLOSED_IN_INTERS; INTERS_0] THEN
  REWRITE_TAC[GSYM TOPSPACE_EUCLIDEANREAL; CLOSED_IN_TOPSPACE]);;

let REAL_OPEN_REAL_CLOSED = prove
 (`!s. real_open s <=> real_closed(UNIV DIFF s)`,
  SIMP_TAC[REAL_OPEN_IN; REAL_CLOSED_IN; TOPSPACE_EUCLIDEANREAL; SUBSET_UNIV;
           OPEN_IN_CLOSED_IN_EQ]);;

let REAL_CLOSED_REAL_OPEN = prove
 (`!s. real_closed s <=> real_open(UNIV DIFF s)`,
  SIMP_TAC[REAL_OPEN_IN; REAL_CLOSED_IN; TOPSPACE_EUCLIDEANREAL;
           SUBSET_UNIV; closed_in]);;

let REAL_OPEN_DIFF = prove
 (`!s t. real_open s /\ real_closed t ==> real_open(s DIFF t)`,
  REWRITE_TAC[REAL_OPEN_IN; REAL_CLOSED_IN; OPEN_IN_DIFF]);;

let REAL_CLOSED_DIFF = prove
 (`!s t. real_closed s /\ real_open t ==> real_closed(s DIFF t)`,
  REWRITE_TAC[REAL_OPEN_IN; REAL_CLOSED_IN; CLOSED_IN_DIFF]);;

let REAL_OPEN_INTERS = prove
 (`!s. FINITE s /\ (!t. t IN s ==> real_open t) ==> real_open(INTERS s)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[INTERS_INSERT; INTERS_0; REAL_OPEN_UNIV; IN_INSERT] THEN
  MESON_TAC[REAL_OPEN_INTER]);;

let REAL_CLOSED_UNIONS = prove
 (`!s. FINITE s /\ (!t. t IN s ==> real_closed t) ==> real_closed(UNIONS s)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_INSERT; UNIONS_0; REAL_CLOSED_EMPTY; IN_INSERT] THEN
  MESON_TAC[REAL_CLOSED_UNION]);;

let REAL_OPEN = prove
 (`!s. real_open s <=> open(IMAGE lift s)`,
  REWRITE_TAC[real_open; open_def; FORALL_IN_IMAGE; FORALL_LIFT; DIST_LIFT;
              LIFT_IN_IMAGE_LIFT]);;

let REAL_CLOSED = prove
 (`!s. real_closed s <=> closed(IMAGE lift s)`,
  GEN_TAC THEN REWRITE_TAC[real_closed; REAL_OPEN; CLOSED_OPEN] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF; IN_UNIV] THEN
  MESON_TAC[LIFT_DROP]);;

let REAL_CLOSED_HALFSPACE_LE = prove
 (`!a. real_closed {x | x <= a}`,
  GEN_TAC THEN SUBGOAL_THEN `closed {x | drop x <= a}` MP_TAC THENL
   [REWRITE_TAC[drop; CLOSED_HALFSPACE_COMPONENT_LE]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[REAL_CLOSED] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[LIFT_DROP]);;

let REAL_CLOSED_HALFSPACE_GE = prove
 (`!a. real_closed {x | x >= a}`,
  GEN_TAC THEN SUBGOAL_THEN `closed {x | drop x >= a}` MP_TAC THENL
   [REWRITE_TAC[drop; CLOSED_HALFSPACE_COMPONENT_GE]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[REAL_CLOSED] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[LIFT_DROP]);;

let REAL_OPEN_HALFSPACE_LT = prove
 (`!a. real_open {x | x < a}`,
  GEN_TAC THEN SUBGOAL_THEN `open {x | drop x < a}` MP_TAC THENL
   [REWRITE_TAC[drop; OPEN_HALFSPACE_COMPONENT_LT]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[REAL_OPEN] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[LIFT_DROP]);;

let REAL_OPEN_HALFSPACE_GT = prove
 (`!a. real_open {x | x > a}`,
  GEN_TAC THEN SUBGOAL_THEN `open {x | drop x > a}` MP_TAC THENL
   [REWRITE_TAC[drop; OPEN_HALFSPACE_COMPONENT_GT]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[REAL_OPEN] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Compactness of a set of reals.                                            *)
(* ------------------------------------------------------------------------- *)

let real_bounded = new_definition
 `real_bounded s <=> ?B. !x. x IN s ==> abs(x) <= B`;;

let REAL_BOUNDED = prove
 (`real_bounded s <=> bounded(IMAGE lift s)`,
  REWRITE_TAC[BOUNDED_LIFT; real_bounded]);;

let REAL_BOUNDED_POS = prove
 (`!s. real_bounded s <=> ?B. &0 < B /\ !x. x IN s ==> abs(x) <= B`,
  REWRITE_TAC[real_bounded] THEN
  MESON_TAC[REAL_ARITH `&0 < &1 + abs B /\ (x <= B ==> x <= &1 + abs B)`]);;

let REAL_BOUNDED_POS_LT = prove
 (`!s. real_bounded s <=> ?b. &0 < b /\ !x. x IN s ==> abs(x) < b`,
  REWRITE_TAC[real_bounded] THEN
  MESON_TAC[REAL_LT_IMP_LE;
            REAL_ARITH `&0 < &1 + abs(y) /\ (x <= y ==> x < &1 + abs(y))`]);;

let REAL_BOUNDED_SUBSET = prove
 (`!s t. real_bounded t /\ s SUBSET t ==> real_bounded s`,
  MESON_TAC[REAL_BOUNDED; BOUNDED_SUBSET; IMAGE_SUBSET]);;

let real_compact = new_definition
 `real_compact s <=> compact(IMAGE lift s)`;;

let REAL_COMPACT_IMP_BOUNDED = prove
 (`!s. real_compact s ==> real_bounded s`,
  REWRITE_TAC[real_compact; REAL_BOUNDED; COMPACT_IMP_BOUNDED]);;

let REAL_COMPACT_IMP_CLOSED = prove
 (`!s. real_compact s ==> real_closed s`,
  REWRITE_TAC[real_compact; REAL_CLOSED; COMPACT_IMP_CLOSED]);;

let REAL_COMPACT_EQ_BOUNDED_CLOSED = prove
 (`!s. real_compact s <=> real_bounded s /\ real_closed s`,
  REWRITE_TAC[real_compact; REAL_BOUNDED; REAL_CLOSED] THEN
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* Limits of functions with real range.                                      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("--->",(12,"right"));;

let tendsto_real = new_definition
  `(f ---> l) net <=> !e. &0 < e ==> eventually (\x. abs(f(x) - l) < e) net`;;

let TENDSTO_REAL = prove
 (`(s ---> l) = ((lift o s) --> lift l)`,
  REWRITE_TAC[FUN_EQ_THM; tendsto; tendsto_real; o_THM; DIST_LIFT]);;

let REAL_TENDSTO = prove
 (`(s --> l) = (drop o s ---> drop l)`,
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_DROP; ETA_AX]);;

let REALLIM_COMPLEX = prove
 (`(s ---> l) = ((Cx o s) --> Cx(l))`,
  REWRITE_TAC[FUN_EQ_THM; tendsto; tendsto_real; o_THM; dist;
              GSYM CX_SUB; COMPLEX_NORM_CX]);;

let REALLIM_UNIQUE = prove
 (`!net f l l'.
         ~trivial_limit net /\ (f ---> l) net /\ (f ---> l') net ==> l = l'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_UNIQUE) THEN REWRITE_TAC[LIFT_EQ]);;

let REALLIM_CONST = prove
 (`!net a. ((\x. a) ---> a) net`,
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIM_CONST]);;

let REALLIM_LMUL = prove
 (`!f l c. (f ---> l) net ==> ((\x. c * f x) ---> c * l) net`,
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_CMUL; LIM_CMUL]);;

let REALLIM_RMUL = prove
 (`!f l c. (f ---> l) net ==> ((\x. f x * c) ---> l * c) net`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REALLIM_LMUL]);;

let REALLIM_NEG = prove
 (`!net f l. (f ---> l) net ==> ((\x. --(f x)) ---> --l) net`,
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_NEG; LIM_NEG]);;

let REALLIM_NEG_EQ = prove
 (`!net f l. ((\x. --(f x)) ---> --l) net <=> (f ---> l) net`,
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_NEG; LIM_NEG_EQ]);;

let REALLIM_ADD = prove
 (`!net:(A)net f g l m.
    (f ---> l) net /\ (g ---> m) net ==> ((\x. f(x) + g(x)) ---> l + m) net`,
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_ADD; LIM_ADD]);;

let REALLIM_SUB = prove
 (`!net:(A)net f g l m.
    (f ---> l) net /\ (g ---> m) net ==> ((\x. f(x) - g(x)) ---> l - m) net`,
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_SUB; LIM_SUB]);;

let REALLIM_MUL = prove
 (`!net:(A)net f g l m.
    (f ---> l) net /\ (g ---> m) net ==> ((\x. f(x) * g(x)) ---> l * m) net`,
  REWRITE_TAC[REALLIM_COMPLEX; o_DEF; CX_MUL; LIM_COMPLEX_MUL]);;

let REALLIM_INV = prove
 (`!net f g l m.
         (f ---> l) net /\ ~(l = &0) ==> ((\x. inv(f x)) ---> inv l) net`,
  REWRITE_TAC[REALLIM_COMPLEX; o_DEF; CX_INV; LIM_COMPLEX_INV; GSYM CX_INJ]);;

let REALLIM_DIV = prove
 (`!net:(A)net f g l m.
    (f ---> l) net /\ (g ---> m) net /\ ~(m = &0)
    ==> ((\x. f(x) / g(x)) ---> l / m) net`,
  SIMP_TAC[real_div; REALLIM_MUL; REALLIM_INV]);;

let REALLIM_POW = prove
 (`!net f l n. (f ---> l) net ==> ((\x. f x pow n) ---> l pow n) net`,
  REPLICATE_TAC 3 GEN_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[real_pow; REALLIM_CONST; REALLIM_MUL]);;

let REALLIM_NULL = prove
 (`!net f l. (f ---> l) net <=> ((\x. f(x) - l) ---> &0) net`,
  REWRITE_TAC[tendsto_real; REAL_SUB_RZERO]);;

let REALLIM_NULL_ADD = prove
 (`!net:(A)net f g.
    (f ---> &0) net /\ (g ---> &0) net ==> ((\x. f(x) + g(x)) ---> &0) net`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REALLIM_ADD) THEN
  REWRITE_TAC[REAL_ADD_LID]);;

let REALLIM_NULL_LMUL = prove
 (`!net f c. (f ---> &0) net ==> ((\x. c * f x) ---> &0) net`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP REALLIM_LMUL) THEN
  REWRITE_TAC[REAL_MUL_RZERO]);;

let REALLIM_NULL_RMUL = prove
 (`!net f c. (f ---> &0) net ==> ((\x. f x * c) ---> &0) net`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP REALLIM_RMUL) THEN
  REWRITE_TAC[REAL_MUL_LZERO]);;

let REALLIM_NULL_POW = prove
 (`!net f n. (f ---> &0) net /\ ~(n = 0) ==> ((\x. f x pow n) ---> &0) net`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
   (MP_TAC o SPEC `n:num` o MATCH_MP REALLIM_POW) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[REAL_POW_ZERO]);;

let REALLIM_RE = prove
 (`!net f l. (f --> l) net ==> ((Re o f) ---> Re l) net`,
  REWRITE_TAC[REALLIM_COMPLEX] THEN
  REWRITE_TAC[tendsto; dist; o_THM; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[GSYM RE_SUB; eventually] THEN
  MESON_TAC[REAL_LET_TRANS; COMPLEX_NORM_GE_RE_IM]);;

let REALLIM_IM = prove
 (`!net f l. (f --> l) net ==> ((Im o f) ---> Im l) net`,
  REWRITE_TAC[REALLIM_COMPLEX] THEN
  REWRITE_TAC[tendsto; dist; o_THM; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[GSYM IM_SUB; eventually] THEN
  MESON_TAC[REAL_LET_TRANS; COMPLEX_NORM_GE_RE_IM]);;

let REALLIM_TRANSFORM_EVENTUALLY = prove
 (`!net f g l.
        eventually (\x. f x = g x) net /\ (f ---> l) net ==> (g ---> l) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  POP_ASSUM MP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  SIMP_TAC[o_THM]);;

let REALLIM_TRANSFORM = prove
 (`!net f g l.
        ((\x. f x - g x) ---> &0) net /\ (f ---> l) net ==> (g ---> l) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF; LIFT_NUM; LIFT_SUB; LIM_TRANSFORM]);;

let REAL_SEQ_OFFSET = prove
 (`!f l k. (f ---> l) sequentially ==> ((\i. f (i + k)) ---> l) sequentially`,
  REPEAT GEN_TAC THEN SIMP_TAC[TENDSTO_REAL; o_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SEQ_OFFSET) THEN SIMP_TAC[]);;

let REAL_SEQ_OFFSET_REV = prove
 (`!f l k. ((\i. f (i + k)) ---> l) sequentially ==> (f ---> l) sequentially`,
  SIMP_TAC[TENDSTO_REAL; o_DEF] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SEQ_OFFSET_REV THEN EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[]);;

let REALLIM_TRANSFORM_STRADDLE = prove
 (`!f g h a.
        eventually (\n. f(n) <= g(n)) net /\ (f ---> a) net /\
        eventually (\n. g(n) <= h(n)) net /\ (h ---> a) net
        ==> (g ---> a) net`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[RIGHT_AND_FORALL_THM; tendsto_real; AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  REAL_ARITH_TAC);;

let REALLIM_TRANSFORM_BOUND = prove
 (`!f g. eventually (\n. abs(f n) <= g n) net /\ (g ---> &0) net
         ==> (f ---> &0) net`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[RIGHT_AND_FORALL_THM; tendsto_real; AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  REAL_ARITH_TAC);;

let REAL_CONVERGENT_IMP_BOUNDED = prove
 (`!s l. (s ---> l) sequentially ==> real_bounded (IMAGE s (:num))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_BOUNDED; TENDSTO_REAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONVERGENT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_UNIV] THEN
  REWRITE_TAC[o_DEF; NORM_LIFT]);;

let REALLIM = prove
 (`(f ---> l) net <=>
        trivial_limit net \/
        !e. &0 < e ==> ?y. (?x. netord(net) x y) /\
                           !x. netord(net) x y ==> abs(f(x) -l) < e`,
  REWRITE_TAC[tendsto_real; eventually] THEN MESON_TAC[]);;

let REALLIM_WITHIN_LE = prove
 (`!f:real^N->real l a s.
        (f ---> l) (at a within s) <=>
           !e. &0 < e ==> ?d. &0 < d /\
                              !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) <= d
                                   ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_WITHIN_LE]);;

let REALLIM_WITHIN = prove
 (`!f:real^N->real l a s.
      (f ---> l) (at a within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) < d
                    ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_WITHIN] THEN MESON_TAC[]);;

let REALLIM_AT = prove
 (`!f l a:real^N.
      (f ---> l) (at a) <=>
              !e. &0 < e
                  ==> ?d. &0 < d /\ !x. &0 < dist(x,a) /\ dist(x,a) < d
                          ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_AT] THEN MESON_TAC[]);;

let REALLIM_AT_INFINITY = prove
 (`!f l. (f ---> l) at_infinity <=>
               !e. &0 < e ==> ?b. !x. norm(x) >= b ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_AT_INFINITY] THEN MESON_TAC[]);;

let REALLIM_SEQUENTIALLY = prove
 (`!s l. (s ---> l) sequentially <=>
          !e. &0 < e ==> ?N. !n. N <= n ==> abs(s(n) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_SEQUENTIALLY] THEN MESON_TAC[]);;

let REALLIM_EVENTUALLY = prove
 (`!net f l. eventually (\x. f x = l) net ==> (f ---> l) net`,
  REWRITE_TAC[eventually; REALLIM] THEN
  MESON_TAC[REAL_ARITH `abs(x - x) = &0`]);;

let LIM_COMPONENTWISE = prove
 (`!net f:A->real^N.
        (f --> l) net <=>
        !i. 1 <= i /\ i <= dimindex(:N) ==> ((\x. (f x)$i) ---> l$i) net`,
  ONCE_REWRITE_TAC[LIM_COMPONENTWISE_LIFT] THEN
  REWRITE_TAC[TENDSTO_REAL; o_DEF]);;

let REALLIM_LE = prove
 (`!(net:A net) f l b.
        (f ---> l) net /\
        ~trivial_limit net /\
        eventually (\x. f x <= b) net
        ==> l <= b`,
  REWRITE_TAC[FORALL_DROP; TENDSTO_REAL; LIFT_DROP] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `net:A net` LIM_DROP_LE) THEN
  EXISTS_TAC `lift o (f:A->real)` THEN
  ASM_REWRITE_TAC[o_THM; LIFT_DROP]);;

let REALLIM_GE = prove
 (`!(net:A net) f l b.
        (f ---> l) net /\
        ~trivial_limit net /\
        eventually (\x. b <= f x) net
        ==> b <= l`,
  ONCE_REWRITE_TAC[GSYM REAL_LE_NEG2] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `net:A net` REALLIM_LE) THEN
  EXISTS_TAC `\a:A. --(f a:real)` THEN
  ASM_REWRITE_TAC[REALLIM_NEG_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Real series.                                                              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("real_sums",(12,"right"));;

let real_sums = new_definition
 `(f real_sums l) s <=> ((\n. sum (s INTER (0..n)) f) ---> l) sequentially`;;

let real_infsum = new_definition
 `real_infsum s f = @l. (f real_sums l) s`;;

let real_summable = new_definition
 `real_summable s f = ?l. (f real_sums l) s`;;

let REAL_SUMS = prove
 (`(f real_sums l) = ((lift o f) sums (lift l))`,
  REWRITE_TAC[FUN_EQ_THM; sums; real_sums; TENDSTO_REAL] THEN
  SIMP_TAC[LIFT_SUM; FINITE_INTER_NUMSEG; o_DEF]);;

let REAL_SUMS_RE = prove
 (`!f l s. (f sums l) s ==> ((Re o f) real_sums (Re l)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sums; sums] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REALLIM_RE) THEN
  SIMP_TAC[o_DEF; RE_VSUM; FINITE_INTER_NUMSEG]);;

let REAL_SUMS_IM = prove
 (`!f l s. (f sums l) s ==> ((Im o f) real_sums (Im l)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sums; sums] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REALLIM_IM) THEN
  SIMP_TAC[o_DEF; IM_VSUM; FINITE_INTER_NUMSEG]);;

let REAL_SUMS_COMPLEX = prove
 (`!f l s. (f real_sums l) s <=> ((Cx o f) sums (Cx l)) s`,
  REWRITE_TAC[real_sums; sums; REALLIM_COMPLEX] THEN
  SIMP_TAC[o_DEF; VSUM_CX; FINITE_INTER; FINITE_NUMSEG]);;

let REAL_SUMMABLE = prove
 (`real_summable s f <=> summable s (lift o f)`,
  REWRITE_TAC[real_summable; summable; REAL_SUMS; GSYM EXISTS_LIFT]);;

let REAL_SUMMABLE_COMPLEX = prove
 (`real_summable s f <=> summable s (Cx o f)`,
  REWRITE_TAC[real_summable; summable; REAL_SUMS_COMPLEX] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `l:complex`) THEN EXISTS_TAC `Re l` THEN
  SUBGOAL_THEN `Cx(Re l) = l` (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM REAL] THEN MATCH_MP_TAC REAL_SERIES THEN
  MAP_EVERY EXISTS_TAC [`Cx o (f:num->real)`; `s:num->bool`] THEN
  ASM_REWRITE_TAC[o_THM; REAL_CX]);;

let REAL_SERIES_CAUCHY = prove
 (`(?l. (f real_sums l) s) <=>
   (!e. &0 < e ==> ?N. !m n. m >= N ==> abs(sum(s INTER (m..n)) f) < e)`,
  REWRITE_TAC[REAL_SUMS; SERIES_CAUCHY; GSYM EXISTS_LIFT] THEN
  SIMP_TAC[NORM_REAL; GSYM drop; DROP_VSUM; FINITE_INTER_NUMSEG] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX]);;

let REAL_SUMS_EQ = prove
 (`!f g k. (!x. x IN k ==> f x = g x) /\ (f real_sums l) k
           ==> (g real_sums l) k`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[REAL_SUMS] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUMS_EQ) THEN
  ASM_SIMP_TAC[o_THM]);;

let REAL_SUMS_SUMMABLE = prove
 (`!f l s. (f real_sums l) s ==> real_summable s f`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[]);;

let REAL_SUMS_INFSUM = prove
 (`!f s. (f real_sums (real_infsum s f)) s <=> real_summable s f`,
  REWRITE_TAC[real_infsum; real_summable] THEN MESON_TAC[]);;

let REAL_SERIES_FROM = prove
 (`!f l k. (f real_sums l) (from k) = ((\n. sum(k..n) f) ---> l) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sums] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; numseg; from; IN_ELIM_THM; IN_INTER] THEN ARITH_TAC);;

let REAL_SERIES_UNIQUE = prove
 (`!f l l' s. (f real_sums l) s /\ (f real_sums l') s ==> l = l'`,
  REWRITE_TAC[real_sums] THEN
  MESON_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; REALLIM_UNIQUE]);;

let REAL_INFSUM_UNIQUE = prove
 (`!f l s. (f real_sums l) s ==> real_infsum s f = l`,
  MESON_TAC[REAL_SERIES_UNIQUE; REAL_SUMS_INFSUM; real_summable]);;

let REAL_SERIES_FINITE = prove
 (`!f s. FINITE s ==> (f real_sums (sum s f)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[num_FINITE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[real_sums; REALLIM_SEQUENTIALLY] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `n:num` THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `s INTER (0..m) = s`
   (fun th -> ASM_REWRITE_TAC[th; REAL_SUB_REFL; REAL_ABS_NUM]) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_NUMSEG; LE_0] THEN
  ASM_MESON_TAC[LE_TRANS]);;

let REAL_SUMMABLE_IFF_EVENTUALLY = prove
 (`!f g k. (?N. !n. N <= n /\ n IN k ==> f n = g n)
           ==> (real_summable k f <=> real_summable k g)`,
  REWRITE_TAC[REAL_SUMMABLE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUMMABLE_IFF_EVENTUALLY THEN REWRITE_TAC[o_THM] THEN
  ASM_MESON_TAC[]);;

let REAL_SUMMABLE_EQ_EVENTUALLY = prove
 (`!f g k. (?N. !n. N <= n /\ n IN k ==> f n = g n) /\ real_summable k f
           ==> real_summable k g`,
  MESON_TAC[REAL_SUMMABLE_IFF_EVENTUALLY]);;

let REAL_SUMMABLE_IFF_COFINITE = prove
 (`!f g s t. FINITE((s DIFF t) UNION (t DIFF s))
             ==> (real_summable s f <=> real_summable t f)`,
  SIMP_TAC[REAL_SUMMABLE] THEN MESON_TAC[SUMMABLE_IFF_COFINITE]);;

let REAL_SUMMABLE_EQ_COFINITE = prove
 (`!f g s t. FINITE((s DIFF t) UNION (t DIFF s)) /\ real_summable s f
             ==> real_summable t f`,
  MESON_TAC[REAL_SUMMABLE_IFF_COFINITE]);;

let REAL_SUMMABLE_FROM_ELSEWHERE = prove
 (`!f m n. real_summable (from m) f ==> real_summable (from n) f`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_SUMMABLE_EQ_COFINITE) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..(m+n)` THEN
  SIMP_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_UNION; IN_DIFF; IN_FROM] THEN
  ARITH_TAC);;

let REAL_SERIES_GOESTOZERO = prove
 (`!s x. real_summable s x
         ==> !e. &0 < e
                 ==> eventually (\n. n IN s ==> abs(x n) < e) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_SUMMABLE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SERIES_GOESTOZERO) THEN
  REWRITE_TAC[o_THM; NORM_LIFT]);;

let REAL_SUMMABLE_IMP_TOZERO = prove
 (`!f:num->real k.
       real_summable k f
       ==> ((\n. if n IN k then f(n) else &0) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_SUMMABLE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_IMP_TOZERO) THEN
  REWRITE_TAC[TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF; GSYM LIFT_NUM; GSYM COND_RAND]);;

let REAL_SUMMABLE_IMP_BOUNDED = prove
 (`!f:num->real k. real_summable k f ==> real_bounded (IMAGE f k)`,
  REWRITE_TAC[REAL_BOUNDED; REAL_SUMMABLE; GSYM IMAGE_o;
              SUMMABLE_IMP_BOUNDED]);;

let REAL_SUMMABLE_IMP_REAL_SUMS_BOUNDED = prove
 (`!f:num->real k.
       real_summable (from k) f ==> real_bounded { sum(k..n) f | n IN (:num) }`,
  REWRITE_TAC[real_summable; real_sums; LEFT_IMP_EXISTS_THM] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_CONVERGENT_IMP_BOUNDED) THEN
  REWRITE_TAC[FROM_INTER_NUMSEG; SIMPLE_IMAGE]);;

let REAL_SERIES_0 = prove
 (`!s. ((\n. &0) real_sums (&0)) s`,
  REWRITE_TAC[real_sums; SUM_0; REALLIM_CONST]);;

let REAL_SERIES_ADD = prove
 (`!x x0 y y0 s.
     (x real_sums x0) s /\ (y real_sums y0) s
     ==> ((\n. x n + y n) real_sums (x0 + y0)) s`,
  SIMP_TAC[real_sums; FINITE_INTER_NUMSEG; SUM_ADD; REALLIM_ADD]);;

let REAL_SERIES_SUB = prove
 (`!x x0 y y0 s.
     (x real_sums x0) s /\ (y real_sums y0) s
     ==> ((\n. x n - y n) real_sums (x0 - y0)) s`,
  SIMP_TAC[real_sums; FINITE_INTER_NUMSEG; SUM_SUB; REALLIM_SUB]);;

let REAL_SERIES_LMUL = prove
 (`!x x0 c s. (x real_sums x0) s ==> ((\n. c * x n) real_sums (c * x0)) s`,
  SIMP_TAC[real_sums; FINITE_INTER_NUMSEG; SUM_LMUL; REALLIM_LMUL]);;

let REAL_SERIES_RMUL = prove
 (`!x x0 c s. (x real_sums x0) s ==> ((\n. x n * c) real_sums (x0 * c)) s`,
  SIMP_TAC[real_sums; FINITE_INTER_NUMSEG; SUM_RMUL; REALLIM_RMUL]);;

let REAL_SERIES_NEG = prove
 (`!x x0 s. (x real_sums x0) s ==> ((\n. --(x n)) real_sums (--x0)) s`,
  SIMP_TAC[real_sums; FINITE_INTER_NUMSEG; SUM_NEG; REALLIM_NEG]);;

let REAL_SUMS_IFF = prove
 (`!f g k. (!x. x IN k ==> f x = g x)
           ==> ((f real_sums l) k <=> (g real_sums l) k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_sums] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[IN_INTER]);;

let REAL_SUMS_EQ = prove
 (`!f g k. (!x. x IN k ==> f x = g x) /\ (f real_sums l) k
           ==> (g real_sums l) k`,
  MESON_TAC[REAL_SUMS_IFF]);;

let REAL_SERIES_FINITE_SUPPORT = prove
 (`!f s k.
     FINITE (s INTER k) /\ (!x. ~(x IN s INTER k) ==> f x = &0)
     ==> (f real_sums sum(s INTER k) f) k`,
  REWRITE_TAC[real_sums; REALLIM_SEQUENTIALLY] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPEC `\x:num. x` o MATCH_MP UPPER_BOUND_FINITE_SET) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `sum (k INTER (0..n)) (f:num->real) = sum(s INTER k) f`
   (fun th -> ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM; th]) THEN
  MATCH_MP_TAC SUM_SUPERSET THEN
  ASM_SIMP_TAC[SUBSET; IN_INTER; IN_NUMSEG; LE_0] THEN
  ASM_MESON_TAC[IN_INTER; LE_TRANS]);;

let REAL_SERIES_DIFFS = prove
 (`!f k. (f ---> &0) sequentially
         ==> ((\n. f(n) - f(n + 1)) real_sums f(k)) (from k)`,
  REWRITE_TAC[real_sums; FROM_INTER_NUMSEG; SUM_DIFFS] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. (f:num->real) k - f(n + 1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `k:num` THEN
    SIMP_TAC[];
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_SUB_RZERO] THEN
    MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
    MATCH_MP_TAC REAL_SEQ_OFFSET THEN ASM_REWRITE_TAC[]]);;

let REAL_SERIES_TRIVIAL = prove
 (`!f. (f real_sums &0) {}`,
  REWRITE_TAC[real_sums; INTER_EMPTY; SUM_CLAUSES; REALLIM_CONST]);;

let REAL_SERIES_RESTRICT = prove
 (`!f k l:real.
        ((\n. if n IN k then f(n) else &0) real_sums l) (:num) <=>
        (f real_sums l) k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sums] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; INTER_UNIV] THEN GEN_TAC THEN
  MATCH_MP_TAC(MESON[] `sum s f = sum t f /\ sum t f = sum t g
                        ==> sum s f = sum t g`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUPERSET THEN SET_TAC[];
    MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[IN_INTER]]);;

let REAL_SERIES_SUM = prove
 (`!f l k s. FINITE s /\ s SUBSET k /\ (!x. ~(x IN s) ==> f x = &0) /\
             sum s f = l ==> (f real_sums l) k`,
  REPEAT STRIP_TAC THEN EXPAND_TAC "l" THEN
  SUBGOAL_THEN `s INTER k = s:num->bool` ASSUME_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC [REAL_SERIES_FINITE_SUPPORT]]);;

(* ------------------------------------------------------------------------- *)
(* Similar combining theorems just for summability.                          *)
(* ------------------------------------------------------------------------- *)

let REAL_SUMMABLE_0 = prove
 (`!s. real_summable s (\n. &0)`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SERIES_0]);;

let REAL_SUMMABLE_ADD = prove
 (`!x y s. real_summable s x /\ real_summable s y
           ==> real_summable s (\n. x n + y n)`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SERIES_ADD]);;

let REAL_SUMMABLE_SUB = prove
 (`!x y s. real_summable s x /\ real_summable s y
           ==> real_summable s (\n. x n - y n)`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SERIES_SUB]);;

let REAL_SUMMABLE_LMUL = prove
 (`!s x c. real_summable s x ==> real_summable s (\n. c * x n)`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SERIES_LMUL]);;

let REAL_SUMMABLE_RMUL = prove
 (`!s x c. real_summable s x ==> real_summable s (\n. x n * c)`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SERIES_RMUL]);;

let REAL_SUMMABLE_NEG = prove
 (`!x s. real_summable s x ==> real_summable s (\n. --(x n))`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SERIES_NEG]);;

let REAL_SUMMABLE_IFF = prove
 (`!f g k. (!x. x IN k ==> f x = g x)
           ==> (real_summable k f <=> real_summable k g)`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SUMS_IFF]);;

let REAL_SUMMABLE_EQ = prove
 (`!f g k. (!x. x IN k ==> f x = g x) /\ real_summable k f
           ==> real_summable k g`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SUMS_EQ]);;

let REAL_SERIES_SUBSET = prove
 (`!x s t l.
        s SUBSET t /\
        ((\i. if i IN s then x i else &0) real_sums l) t
        ==> (x real_sums l) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[real_sums] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  ASM_SIMP_TAC[GSYM SUM_RESTRICT_SET; FINITE_INTER_NUMSEG] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN SET_TAC[]);;

let REAL_SUMMABLE_SUBSET = prove
 (`!x s t l.
        s SUBSET t /\
        real_summable t (\i. if i IN s then x i else &0)
        ==> real_summable s x`,
  REWRITE_TAC[real_summable] THEN MESON_TAC[REAL_SERIES_SUBSET]);;

let REAL_SUMMABLE_TRIVIAL = prove
 (`!f. real_summable {} f`,
  GEN_TAC THEN REWRITE_TAC[real_summable] THEN EXISTS_TAC `&0` THEN
  REWRITE_TAC[REAL_SERIES_TRIVIAL]);;

let REAL_SUMMABLE_RESTRICT = prove
 (`!f k l.
        real_summable (:num) (\n. if n IN k then f(n) else &0) <=>
        real_summable k f`,
  REWRITE_TAC[real_summable; REAL_SERIES_RESTRICT]);;

let REAL_SUMS_FINITE_DIFF = prove
 (`!f t s l.
        t SUBSET s /\ FINITE t /\ (f real_sums l) s
        ==> (f real_sums (l - sum t f)) (s DIFF t)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(MP_TAC o ISPEC `f:num->real` o MATCH_MP REAL_SERIES_FINITE) THEN
  ONCE_REWRITE_TAC[GSYM REAL_SERIES_RESTRICT] THEN
  REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SERIES_SUB) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:num` THEN REWRITE_TAC[IN_DIFF] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:num` o GEN_REWRITE_RULE I [SUBSET]) THEN
  MAP_EVERY ASM_CASES_TAC [`(x:num) IN s`; `(x:num) IN t`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let REAL_SUMS_FINITE_UNION = prove
 (`!f s t l.
        FINITE t /\ (f real_sums l) s
        ==> (f real_sums (l + sum (t DIFF s) f)) (s UNION t)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:num->bool` o MATCH_MP FINITE_DIFF) THEN
  DISCH_THEN(MP_TAC o ISPEC `f:num->real` o MATCH_MP REAL_SERIES_FINITE) THEN
  ONCE_REWRITE_TAC[GSYM REAL_SERIES_RESTRICT] THEN
  REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SERIES_ADD) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:num` THEN
  REWRITE_TAC[IN_DIFF; IN_UNION] THEN
  MAP_EVERY ASM_CASES_TAC [`(x:num) IN s`; `(x:num) IN t`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let REAL_SUMS_OFFSET = prove
 (`!f t s l.
        (f real_sums l) (from m) /\ m < n
        ==> (f real_sums (l - sum(m..(n-1)) f)) (from n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `from n = from m DIFF (m..(n-1))` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_FROM; IN_DIFF; IN_NUMSEG] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_SUMS_FINITE_DIFF THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    SIMP_TAC[SUBSET; IN_FROM; IN_NUMSEG]]);;

let REAL_SUMS_OFFSET_REV = prove
 (`!f t s l.
        (f real_sums l) (from m) /\ n < m
        ==> (f real_sums (l + sum(n..m-1) f)) (from n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real`; `from m`; `n..m-1`; `l:real`]
                REAL_SUMS_FINITE_UNION) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN MATCH_MP_TAC EQ_IMP THEN
  BINOP_TAC THENL [AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_FROM; IN_NUMSEG] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Convergence tests for real series.                                        *)
(* ------------------------------------------------------------------------- *)

let REAL_SERIES_CAUCHY_UNIFORM = prove
 (`!P:A->bool f k.
        (?l. !e. &0 < e
                 ==> ?N. !n x. N <= n /\ P x
                               ==> abs(sum(k INTER (0..n)) (f x) -
                                        l x) < e) <=>
        (!e. &0 < e ==> ?N. !m n x. N <= m /\ P x
                                    ==> abs(sum(k INTER (m..n)) (f x)) < e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`P:A->bool`; `\x:A n:num. lift(f x n)`; `k:num->bool`]
        SERIES_CAUCHY_UNIFORM) THEN
  SIMP_TAC[VSUM_REAL; FINITE_INTER; FINITE_NUMSEG] THEN
  REWRITE_TAC[NORM_LIFT; o_DEF; LIFT_DROP; ETA_AX] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `l:A->real`) THEN
    EXISTS_TAC `lift o (l:A->real)` THEN
    ASM_SIMP_TAC[o_THM; DIST_LIFT];
    DISCH_THEN(X_CHOOSE_TAC `l:A->real^1`) THEN
    EXISTS_TAC `drop o (l:A->real^1)` THEN
    ASM_SIMP_TAC[SUM_VSUM; FINITE_INTER; FINITE_NUMSEG] THEN
    REWRITE_TAC[o_THM; GSYM DROP_SUB; GSYM ABS_DROP] THEN
    SIMP_TAC[GSYM dist; VSUM_REAL; FINITE_INTER; FINITE_NUMSEG] THEN
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX]]);;

let REAL_SERIES_COMPARISON = prove
 (`!f g s. (?l. (g real_sums l) s) /\
           (?N. !n. n >= N /\ n IN s ==> abs(f n) <= g n)
           ==> ?l. (f real_sums l) s`,
  REWRITE_TAC[REAL_SUMS; GSYM EXISTS_LIFT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_COMPARISON THEN
  EXISTS_TAC `g:num->real` THEN
  REWRITE_TAC[NORM_LIFT; o_THM] THEN ASM_MESON_TAC[]);;

let REAL_SUMMABLE_COMPARISON = prove
 (`!f g s. real_summable s g /\
           (?N. !n. n >= N /\ n IN s ==> abs(f n) <= g n)
           ==> real_summable s f`,
  REWRITE_TAC[real_summable; REAL_SERIES_COMPARISON]);;

let REAL_SERIES_COMPARISON_UNIFORM = prove
 (`!f g P s. (?l. (g real_sums l) s) /\
             (?N. !n x. N <= n /\ n IN s /\ P x ==> abs(f x n) <= g n)
             ==> ?l:A->real.
                    !e. &0 < e
                        ==> ?N. !n x. N <= n /\ P x
                                      ==> abs(sum(s INTER (0..n)) (f x) -
                                               l x) < e`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[GE; REAL_SERIES_CAUCHY; REAL_SERIES_CAUCHY_UNIFORM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC `N1:num`)) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `N1 + N2:num` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `x:A`] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs (sum (s INTER (m .. n)) g)` THEN CONJ_TAC THENL
   [SIMP_TAC[GSYM LIFT_SUM; FINITE_INTER_NUMSEG; NORM_LIFT] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= abs(a)`) THEN
    MATCH_MP_TAC SUM_ABS_LE THEN
    REWRITE_TAC[FINITE_INTER_NUMSEG; IN_INTER; IN_NUMSEG] THEN
    ASM_MESON_TAC[ARITH_RULE `N1 + N2:num <= m /\ m <= x ==> N1 <= x`];
    ASM_MESON_TAC[ARITH_RULE `N1 + N2:num <= m ==> N2 <= m`]]);;

let REAL_SERIES_RATIO = prove
 (`!c a s N.
      c < &1 /\
      (!n. n >= N ==> abs(a(SUC n)) <= c * abs(a(n)))
      ==> ?l:real. (a real_sums l) s`,
  REWRITE_TAC[REAL_SUMS; GSYM EXISTS_LIFT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_RATIO THEN
  REWRITE_TAC[o_THM; NORM_LIFT] THEN ASM_MESON_TAC[]);;

let BOUNDED_PARTIAL_REAL_SUMS = prove
 (`!f:num->real k.
        real_bounded { sum(k..n) f | n IN (:num) }
        ==> real_bounded { sum(m..n) f | m IN (:num) /\ n IN (:num) }`,
  REWRITE_TAC[REAL_BOUNDED] THEN
  REWRITE_TAC[SET_RULE `IMAGE f {g x | P x} = {f(g x) | P x}`;
    SET_RULE `IMAGE f {g x y | P x /\ Q y} = {f(g x y) | P x /\ Q y}`] THEN
  SIMP_TAC[LIFT_SUM; FINITE_INTER; FINITE_NUMSEG] THEN
  REWRITE_TAC[BOUNDED_PARTIAL_SUMS]);;

let REAL_SERIES_DIRICHLET = prove
 (`!f:num->real g N k m.
        real_bounded { sum (m..n) f | n IN (:num)} /\
        (!n. N <= n ==> g(n + 1) <= g(n)) /\
        (g ---> &0) sequentially
        ==> real_summable (from k) (\n. g(n) * f(n))`,
  REWRITE_TAC[REAL_SUMMABLE; REAL_BOUNDED; TENDSTO_REAL] THEN
  REWRITE_TAC[LIFT_NUM; LIFT_CMUL; o_DEF] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_DIRICHLET THEN
  MAP_EVERY EXISTS_TAC [`N:num`; `m:num`] THEN
  ASM_REWRITE_TAC[o_DEF] THEN
  SIMP_TAC[VSUM_REAL; FINITE_INTER; FINITE_NUMSEG] THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
  ASM_REWRITE_TAC[SET_RULE `{lift(f x) | P x} = IMAGE lift {f x | P x}`]);;

let REAL_SERIES_ABSCONV_IMP_CONV = prove
 (`!x:num->real k. real_summable k (\n. abs(x n)) ==> real_summable k x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC `\n:num. abs(x n)` THEN ASM_REWRITE_TAC[REAL_LE_REFL]);;

let REAL_SUMS_GP = prove
 (`!x. abs(x) < &1
       ==> ((\k. x pow k) real_sums (x pow n / (&1 - x))) (from n)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `Cx x` SUMS_GP) THEN
  ASM_REWRITE_TAC[REAL_SUMS_COMPLEX; GSYM CX_SUB; GSYM CX_POW; GSYM CX_DIV;
                  o_DEF; COMPLEX_NORM_CX]);;

let REAL_SUMMABLE_GP = prove
 (`!x k. abs(x) < &1 ==> real_summable k (\n. x pow n)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`Cx x`; `k:num->bool`] SUMMABLE_GP) THEN
  ASM_REWRITE_TAC[REAL_SUMMABLE_COMPLEX] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CX; o_DEF; CX_POW]);;

let REAL_ABEL_LEMMA = prove
 (`!a M r r0.
        &0 <= r /\ r < r0 /\
        (!n. n IN k ==> abs(a n) * r0 pow n <= M)
        ==> real_summable k (\n. abs(a(n)) * r pow n)`,
  REWRITE_TAC[REAL_SUMMABLE_COMPLEX] THEN
  REWRITE_TAC[o_DEF; CX_MUL; CX_ABS] THEN REWRITE_TAC[GSYM CX_MUL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABEL_LEMMA THEN
  REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_MESON_TAC[]);;

let REAL_POWER_SERIES_CONV_IMP_ABSCONV = prove
 (`!a k w z.
        real_summable k (\n. a(n) * z pow n) /\ abs(w) < abs(z)
        ==> real_summable k (\n. abs(a(n) * w pow n))`,
  REWRITE_TAC[REAL_SUMMABLE_COMPLEX; o_DEF; CX_MUL; CX_ABS; CX_POW] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POWER_SERIES_CONV_IMP_ABSCONV THEN
  EXISTS_TAC `Cx z` THEN ASM_REWRITE_TAC[COMPLEX_NORM_CX]);;

let POWER_REAL_SERIES_CONV_IMP_ABSCONV_WEAK = prove
 (`!a k w z.
        real_summable k (\n. a(n) * z pow n) /\ abs(w) < abs(z)
        ==> real_summable k (\n. abs(a n) * w pow n)`,
  REWRITE_TAC[REAL_SUMMABLE_COMPLEX; o_DEF; CX_MUL; CX_ABS; CX_POW] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POWER_SERIES_CONV_IMP_ABSCONV_WEAK THEN
  EXISTS_TAC `Cx z` THEN ASM_REWRITE_TAC[COMPLEX_NORM_CX]);;

(* ------------------------------------------------------------------------- *)
(* Some real limits involving transcendentals.                               *)
(* ------------------------------------------------------------------------- *)

let REALLIM_1_OVER_N = prove
 (`((\n. inv(&n)) ---> &0) sequentially`,
  REWRITE_TAC[REALLIM_COMPLEX; o_DEF; CX_INV; LIM_INV_N]);;

let REALLIM_LOG_OVER_N = prove
 (`((\n. log(&n) / &n) ---> &0) sequentially`,
  REWRITE_TAC[REALLIM_COMPLEX] THEN MP_TAC LIM_LOG_OVER_N THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
  SIMP_TAC[o_DEF; CX_DIV; CX_LOG; REAL_OF_NUM_LT;
           ARITH_RULE `1 <= n ==> 0 < n`]);;

let REALLIM_1_OVER_LOG = prove
 (`((\n. inv(log(&n))) ---> &0) sequentially`,
  REWRITE_TAC[REALLIM_COMPLEX] THEN MP_TAC LIM_1_OVER_LOG THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
  REWRITE_TAC[o_DEF; complex_div; COMPLEX_MUL_LID; CX_INV] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
  SIMP_TAC[CX_LOG; REAL_OF_NUM_LT; ARITH_RULE `1 <= n ==> 0 < n`]);;

(* ------------------------------------------------------------------------- *)
(* Nets for real limit.                                                      *)
(* ------------------------------------------------------------------------- *)

let atreal = new_definition
 `atreal a = mk_net(\x y. &0 < abs(x - a) /\ abs(x - a) <= abs(y - a))`;;

let at_posinfinity = new_definition
  `at_posinfinity = mk_net(\x y:real. x >= y)`;;

let at_neginfinity = new_definition
  `at_neginfinity = mk_net(\x y:real. x <= y)`;;

let ATREAL = prove
 (`!a x y.
        netord(atreal a) x y <=> &0 < abs(x - a) /\ abs(x - a) <= abs(y - a)`,
  GEN_TAC THEN NET_PROVE_TAC[atreal] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_REFL; REAL_LE_TRANS; REAL_LET_TRANS]);;

let AT_POSINFINITY = prove
 (`!a x y. netord at_posinfinity x y <=> x >= y`,
  GEN_TAC THEN NET_PROVE_TAC[at_posinfinity] THEN
  REWRITE_TAC[real_ge; REAL_LE_REFL] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_REFL; REAL_LE_TRANS]);;

let AT_NEGINFINITY = prove
 (`!a x y. netord at_neginfinity x y <=> x <= y`,
  GEN_TAC THEN NET_PROVE_TAC[at_neginfinity] THEN
  REWRITE_TAC[real_ge; REAL_LE_REFL] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_REFL; REAL_LE_TRANS]);;

let WITHINREAL_UNIV = prove
 (`!a. atreal x within (:real) = atreal x`,
  REWRITE_TAC[within; atreal; IN_UNIV] THEN REWRITE_TAC[ETA_AX; net_tybij]);;

let TRIVIAL_LIMIT_ATREAL = prove
 (`!a. ~(trivial_limit (atreal a))`,
  X_GEN_TAC `a:real` THEN SIMP_TAC[trivial_limit; ATREAL; DE_MORGAN_THM] THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`]) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:real`; `c:real`] THEN
  ASM_CASES_TAC `b:real = c` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM DE_MORGAN_THM; GSYM NOT_EXISTS_THM] THEN
  SUBGOAL_THEN `~(b:real = a) \/ ~(c = a)` DISJ_CASES_TAC THENL
   [ASM_MESON_TAC[];
    EXISTS_TAC `(a + b) / &2` THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `(a + c) / &2` THEN ASM_REAL_ARITH_TAC]);;

let TRIVIAL_LIMIT_AT_POSINFINITY = prove
 (`~(trivial_limit at_posinfinity)`,
  REWRITE_TAC[trivial_limit; AT_POSINFINITY; DE_MORGAN_THM] THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`]) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM; real_ge; REAL_NOT_LE] THEN
  MESON_TAC[REAL_LT_TOTAL; REAL_LT_ANTISYM]);;

let TRIVIAL_LIMIT_AT_NEGINFINITY = prove
 (`~(trivial_limit at_neginfinity)`,
  REWRITE_TAC[trivial_limit; AT_NEGINFINITY; DE_MORGAN_THM] THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`]) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM; real_ge; REAL_NOT_LE] THEN
  MESON_TAC[REAL_LT_TOTAL; REAL_LT_ANTISYM]);;

let NETLIMIT_WITHINREAL = prove
 (`!a s. ~(trivial_limit (atreal a within s))
         ==> (netlimit (atreal a within s) = a)`,
  REWRITE_TAC[trivial_limit; netlimit; ATREAL; WITHIN; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x. ~(&0 < abs(x - a) /\ abs(x - a) <= abs(a - a) /\ x IN s)`
  ASSUME_TAC THENL [REAL_ARITH_TAC; ASM_MESON_TAC[]]);;

let NETLIMIT_ATREAL = prove
 (`!a. netlimit(atreal a) = a`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  MATCH_MP_TAC NETLIMIT_WITHINREAL THEN
  SIMP_TAC[TRIVIAL_LIMIT_ATREAL; WITHINREAL_UNIV]);;

let EVENTUALLY_WITHINREAL_LE = prove
 (`!s a p.
     eventually p (atreal a within s) <=>
        ?d. &0 < d /\
            !x. x IN s /\ &0 < abs(x - a) /\ abs(x - a) <= d ==> p(x)`,
  REWRITE_TAC[eventually; ATREAL; WITHIN; trivial_limit] THEN
  REWRITE_TAC[MESON[REAL_LT_01; REAL_LT_REFL] `~(!a b:real. a = b)`] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(DISJ_CASES_THEN(X_CHOOSE_THEN `b:real` MP_TAC)) THENL
     [DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
       `~(b = c) ==> &0 < abs(b - a) \/ &0 < abs(c - a)`)) THEN
      ASM_MESON_TAC[];
      MESON_TAC[REAL_LTE_TRANS]];
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `?x. x IN s /\ &0 < abs(x - a) /\ abs(x - a) <= d` THENL
     [DISJ2_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC `b:real`) THEN
      EXISTS_TAC `b:real` THEN ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL];
      DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`a + d:real`; `a:real`] THEN
      ASM_SIMP_TAC[REAL_ADD_SUB; REAL_EQ_ADD_LCANCEL_0; REAL_LT_IMP_NZ] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real` THEN
      ASM_CASES_TAC `(x:real) IN s` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC]]);;

let EVENTUALLY_WITHINREAL = prove
 (`!s a p.
     eventually p (atreal a within s) <=>
        ?d. &0 < d /\ !x. x IN s /\ &0 < abs(x - a) /\ abs(x - a) < d ==> p(x)`,
  REWRITE_TAC[EVENTUALLY_WITHINREAL_LE] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> c ==> a /\ b ==> d`] THEN
  REWRITE_TAC[APPROACHABLE_LT_LE]);;

let EVENTUALLY_ATREAL = prove
 (`!a p. eventually p (atreal a) <=>
         ?d. &0 < d /\ !x. &0 < abs(x - a) /\ abs(x - a) < d ==> p(x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[EVENTUALLY_WITHINREAL; IN_UNIV]);;

let EVENTUALLY_AT_POSINFINITY = prove
 (`!f l. eventually p at_posinfinity <=> ?b. !x. x >= b ==> p x`,
  REWRITE_TAC[eventually; TRIVIAL_LIMIT_AT_POSINFINITY; AT_POSINFINITY] THEN
  MESON_TAC[REAL_ARITH `x >= x`]);;

let EVENTUALLY_AT_NEGINFINITY = prove
 (`!f l. eventually p at_neginfinity <=> ?b. !x. x <= b ==> p x`,
  REWRITE_TAC[eventually; TRIVIAL_LIMIT_AT_NEGINFINITY; AT_NEGINFINITY] THEN
  MESON_TAC[REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Usual limit results with real domain and either vector or real range.     *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHINREAL_LE = prove
 (`!f:real->real^N l a s.
        (f --> l) (atreal a within s) <=>
           !e. &0 < e ==> ?d. &0 < d /\
                              !x. x IN s /\ &0 < abs(x - a) /\ abs(x - a) <= d
                                   ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_WITHINREAL_LE]);;

let LIM_WITHINREAL = prove
 (`!f:real->real^N l a s.
      (f --> l) (atreal a within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x. x IN s /\ &0 < abs(x - a) /\ abs(x - a) < d
                    ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_WITHINREAL] THEN MESON_TAC[]);;

let LIM_ATREAL = prove
 (`!f l:real^N a.
      (f --> l) (atreal a) <=>
              !e. &0 < e
                  ==> ?d. &0 < d /\ !x. &0 < abs(x - a) /\ abs(x - a) < d
                          ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_ATREAL] THEN MESON_TAC[]);;

let LIM_AT_POSINFINITY = prove
 (`!f l. (f --> l) at_posinfinity <=>
               !e. &0 < e ==> ?b. !x. x >= b ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_AT_POSINFINITY] THEN MESON_TAC[]);;

let LIM_AT_NEGINFINITY = prove
 (`!f l. (f --> l) at_neginfinity <=>
               !e. &0 < e ==> ?b. !x. x <= b ==> dist(f(x),l) < e`,
  REWRITE_TAC[tendsto; EVENTUALLY_AT_NEGINFINITY] THEN MESON_TAC[]);;

let REALLIM_WITHINREAL_LE = prove
 (`!f l a s.
        (f ---> l) (atreal a within s) <=>
           !e. &0 < e ==> ?d. &0 < d /\
                              !x. x IN s /\ &0 < abs(x - a) /\ abs(x - a) <= d
                                   ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_WITHINREAL_LE]);;

let REALLIM_WITHINREAL = prove
 (`!f l a s.
      (f ---> l) (atreal a within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x. x IN s /\ &0 < abs(x - a) /\ abs(x - a) < d
                    ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_WITHINREAL] THEN MESON_TAC[]);;

let REALLIM_ATREAL = prove
 (`!f l a.
      (f ---> l) (atreal a) <=>
              !e. &0 < e
                  ==> ?d. &0 < d /\ !x. &0 < abs(x - a) /\ abs(x - a) < d
                          ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_ATREAL] THEN MESON_TAC[]);;

let REALLIM_AT_POSINFINITY = prove
 (`!f l. (f ---> l) at_posinfinity <=>
               !e. &0 < e ==> ?b. !x. x >= b ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_AT_POSINFINITY] THEN MESON_TAC[]);;

let REALLIM_AT_NEGINFINITY = prove
 (`!f l. (f ---> l) at_neginfinity <=>
               !e. &0 < e ==> ?b. !x. x <= b ==> abs(f(x) - l) < e`,
  REWRITE_TAC[tendsto_real; EVENTUALLY_AT_NEGINFINITY] THEN MESON_TAC[]);;

let LIM_ATREAL_WITHINREAL = prove
 (`!f l a s. (f --> l) (atreal a) ==> (f --> l) (atreal a within s)`,
  REWRITE_TAC[LIM_ATREAL; LIM_WITHINREAL] THEN MESON_TAC[]);;

let LIM_WITHINREAL_REAL_OPEN = prove
 (`!f l a s.
     a IN s /\ real_open s
     ==> ((f --> l) (atreal a within s) <=> (f --> l) (atreal a))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[LIM_ATREAL_WITHINREAL] THEN
  REWRITE_TAC[LIM_ATREAL; LIM_WITHINREAL] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real` o GEN_REWRITE_RULE I [real_open]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[REAL_LT_TRANS]);;

let REALLIM_ATREAL_WITHINREAL = prove
 (`!f l a s. (f ---> l) (atreal a) ==> (f ---> l) (atreal a within s)`,
  REWRITE_TAC[REALLIM_ATREAL; REALLIM_WITHINREAL] THEN MESON_TAC[]);;

let REALLIM_WITHINREAL_REAL_OPEN = prove
 (`!f l a s.
     a IN s /\ real_open s
     ==> ((f ---> l) (atreal a within s) <=> (f ---> l) (atreal a))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[REALLIM_ATREAL_WITHINREAL] THEN
  REWRITE_TAC[REALLIM_ATREAL; REALLIM_WITHINREAL] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real` o GEN_REWRITE_RULE I [real_open]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[REAL_LT_TRANS]);;

let REALLIM_WITHIN_SUBSET = prove
 (`!f l a s t. (f ---> l) (at a within s) /\ t SUBSET s
               ==> (f ---> l) (at a within t)`,
  REWRITE_TAC[REALLIM_WITHIN; SUBSET] THEN MESON_TAC[]);;

let REALLIM_WITHINREAL_SUBSET = prove
 (`!f l a s t. (f ---> l) (atreal a within s) /\ t SUBSET s
               ==> (f ---> l) (atreal a within t)`,
  REWRITE_TAC[REALLIM_WITHINREAL; SUBSET] THEN MESON_TAC[]);;

let LIM_WITHINREAL_SUBSET = prove
 (`!f l a s t. (f --> l) (atreal a within s) /\ t SUBSET s
               ==> (f --> l) (atreal a within t)`,
  REWRITE_TAC[LIM_WITHINREAL; SUBSET] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Relations between limits at real and complex limit points.                *)
(* ------------------------------------------------------------------------- *)

let TRIVIAL_LIMIT_WITHINREAL_WITHIN = prove
 (`trivial_limit(atreal x within s) <=>
        trivial_limit(at (lift x) within (IMAGE lift s))`,
  REWRITE_TAC[trivial_limit; AT; WITHIN; ATREAL] THEN
  REWRITE_TAC[FORALL_LIFT; EXISTS_LIFT; LIFT_EQ; DIST_LIFT] THEN
  REWRITE_TAC[IN_IMAGE_LIFT_DROP; LIFT_DROP]);;

let TRIVIAL_LIMIT_WITHINREAL_WITHINCOMPLEX = prove
 (`trivial_limit(atreal x within s) <=>
        trivial_limit(at (Cx x) within (real INTER IMAGE Cx s))`,
  REWRITE_TAC[trivial_limit; AT; WITHIN; ATREAL] THEN
  REWRITE_TAC[SET_RULE `x IN real INTER s <=> real x /\ x IN s`] THEN
  REWRITE_TAC[TAUT `~(p /\ x /\ q) /\ ~(r /\ x /\ s) <=>
                    x ==> ~(p /\ q) /\ ~(r /\ s)`] THEN
  REWRITE_TAC[FORALL_REAL;
    MESON[IN_IMAGE; CX_INJ] `Cx x IN IMAGE Cx s <=> x IN s`] THEN
  REWRITE_TAC[dist; GSYM CX_SUB; o_THM; RE_CX; COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC(TAUT `~p /\ ~q /\ (r <=> s) ==> (p \/ r <=> q \/ s)`) THEN
  REPEAT CONJ_TAC THEN TRY EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`]) THEN CONV_TAC REAL_RING;
    DISCH_THEN(MP_TAC o SPECL [`Cx(&0)`; `Cx(&1)`]) THEN
    CONV_TAC COMPLEX_RING;
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`Cx a`; `Cx b`] THEN ASM_REWRITE_TAC[CX_INJ] THEN
    ASM_REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX];
    MAP_EVERY X_GEN_TAC [`a:complex`; `b:complex`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?d. &0 < d /\
          !z. &0 < abs(z - x) /\ abs(z - x) <= d ==> ~(z IN s)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(MESON[] `!a b. P a \/ P b ==> ?x. P x`) THEN
      MAP_EVERY EXISTS_TAC [`norm(a - Cx x)`; `norm(b - Cx x)`] THEN
      ASM_REWRITE_TAC[TAUT `a ==> ~b <=> ~(a /\ b)`] THEN
      UNDISCH_TAC `~(a:complex = b)` THEN NORM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`x + d:real`; `x - d:real`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> ~(x + d = x - d)`;
                 REAL_ARITH `&0 < d ==> abs((x + d) - x) = d`;
                 REAL_ARITH `&0 < d ==> abs(x - d - x) = d`] THEN
    ASM_MESON_TAC[]]);;

let LIM_WITHINREAL_WITHINCOMPLEX = prove
 (`(f --> a) (atreal x within s) <=>
   ((f o Re) --> a) (at(Cx x) within (real INTER IMAGE Cx s))`,
  REWRITE_TAC[LIM_WITHINREAL; LIM_WITHIN] THEN
  REWRITE_TAC[SET_RULE `x IN real INTER s <=> real x /\ x IN s`] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_REAL;
    MESON[IN_IMAGE; CX_INJ] `Cx x IN IMAGE Cx s <=> x IN s`] THEN
  REWRITE_TAC[dist; GSYM CX_SUB; o_THM; RE_CX; COMPLEX_NORM_CX]);;

let LIM_ATREAL_ATCOMPLEX = prove
 (`(f --> a) (atreal x) <=> ((f o Re) --> a) (at (Cx x) within real)`,
  REWRITE_TAC[LIM_ATREAL; LIM_WITHIN] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_REAL; IN; dist; GSYM CX_SUB; COMPLEX_NORM_CX;
              o_THM; RE_CX]);;

(* ------------------------------------------------------------------------- *)
(* Simpler theorems relating limits in real and real^1.                      *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHINREAL_WITHIN = prove
 (`(f --> a) (atreal x within s) <=>
        ((f o drop) --> a) (at (lift x) within (IMAGE lift s))`,
  REWRITE_TAC[LIM_WITHINREAL; LIM_WITHIN] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; DIST_LIFT; o_THM; LIFT_DROP]);;

let LIM_ATREAL_AT = prove
 (`(f --> a) (atreal x) <=> ((f o drop) --> a) (at (lift x))`,
  REWRITE_TAC[LIM_ATREAL; LIM_AT; FORALL_LIFT] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; DIST_LIFT; o_THM; LIFT_DROP]);;

let REALLIM_WITHINREAL_WITHIN = prove
 (`(f ---> a) (atreal x within s) <=>
        ((f o drop) ---> a) (at (lift x) within (IMAGE lift s))`,
  REWRITE_TAC[REALLIM_WITHINREAL; REALLIM_WITHIN] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; DIST_LIFT; o_THM; LIFT_DROP]);;

let REALLIM_ATREAL_AT = prove
 (`(f ---> a) (atreal x) <=> ((f o drop) ---> a) (at (lift x))`,
  REWRITE_TAC[REALLIM_ATREAL; REALLIM_AT; FORALL_LIFT] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; DIST_LIFT; o_THM; LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of a function into the reals.                                  *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("real_continuous",(12,"right"));;

let real_continuous = new_definition
  `f real_continuous net <=> (f ---> f(netlimit net)) net`;;

let REAL_CONTINUOUS_TRIVIAL_LIMIT = prove
 (`!f net. trivial_limit net ==> f real_continuous net`,
  SIMP_TAC[real_continuous; REALLIM]);;

let REAL_CONTINUOUS_WITHIN = prove
 (`!f x:real^N s.
        f real_continuous (at x within s) <=>
                (f ---> f(x)) (at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_continuous] THEN
  ASM_CASES_TAC `trivial_limit(at(x:real^N) within s)` THENL
   [ASM_REWRITE_TAC[REALLIM]; ASM_SIMP_TAC[NETLIMIT_WITHIN]]);;

let REAL_CONTINUOUS_AT = prove
 (`!f x. f real_continuous (at x) <=> (f ---> f(x)) (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_WITHIN; IN_UNIV]);;

let REAL_CONTINUOUS_WITHINREAL = prove
 (`!f x s. f real_continuous (atreal x within s) <=>
                (f ---> f(x)) (atreal x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_continuous] THEN
  ASM_CASES_TAC `trivial_limit(atreal x within s)` THENL
   [ASM_REWRITE_TAC[REALLIM]; ASM_SIMP_TAC[NETLIMIT_WITHINREAL]]);;

let REAL_CONTINUOUS_ATREAL = prove
 (`!f x. f real_continuous (atreal x) <=> (f ---> f(x)) (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; IN_UNIV]);;

let CONTINUOUS_WITHINREAL = prove
 (`!f x s. f continuous (atreal x within s) <=>
                 (f --> f(x)) (atreal x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous] THEN
  ASM_CASES_TAC `trivial_limit(atreal x within s)` THENL
   [ASM_REWRITE_TAC[LIM]; ASM_SIMP_TAC[NETLIMIT_WITHINREAL]]);;

let CONTINUOUS_ATREAL = prove
 (`!f x. f continuous (atreal x) <=> (f --> f(x)) (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[CONTINUOUS_WITHINREAL; IN_UNIV]);;

let real_continuous_within = prove
 (`f real_continuous (at x within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    (!x'. x' IN s /\ dist(x',x) < d ==> abs(f x' - f x) < e)`,
  REWRITE_TAC[REAL_CONTINUOUS_WITHIN; REALLIM_WITHIN] THEN
  REWRITE_TAC[GSYM DIST_NZ] THEN
  EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN
  ASM_MESON_TAC[REAL_ARITH `abs(x - x) = &0`]);;

let real_continuous_at = prove
 (`f real_continuous (at x) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    (!x'. dist(x',x) < d ==> abs(f x' - f x) < e)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[real_continuous_within; IN_UNIV]);;

let real_continuous_withinreal = prove
 (`f real_continuous (atreal x within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    (!x'. x' IN s /\ abs(x' - x) < d ==> abs(f x' - f x) < e)`,
  REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; REALLIM_WITHINREAL] THEN
  REWRITE_TAC[REAL_ARITH `&0 < abs(x - y) <=> ~(x = y)`] THEN
  EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN
  ASM_MESON_TAC[REAL_ARITH `abs(x - x) = &0`]);;

let real_continuous_atreal = prove
 (`f real_continuous (atreal x) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    (!x'. abs(x' - x) < d ==> abs(f x' - f x) < e)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[real_continuous_withinreal; IN_UNIV]);;

let REAL_CONTINUOUS_AT_WITHIN = prove
 (`!f s x. f real_continuous (at x)
           ==> f real_continuous (at x within s)`,
  REWRITE_TAC[real_continuous_within; real_continuous_at] THEN
  MESON_TAC[]);;

let REAL_CONTINUOUS_ATREAL_WITHINREAL = prove
 (`!f s x. f real_continuous (atreal x)
           ==> f real_continuous (atreal x within s)`,
  REWRITE_TAC[real_continuous_withinreal; real_continuous_atreal] THEN
  MESON_TAC[]);;

let REAL_CONTINUOUS_WITHINREAL_SUBSET = prove
 (`!f s t. f real_continuous (atreal x within s) /\ t SUBSET s
             ==> f real_continuous (atreal x within t)`,
  REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; REALLIM_WITHINREAL_SUBSET]);;

let REAL_CONTINUOUS_WITHIN_SUBSET = prove
 (`!f s t. f real_continuous (at x within s) /\ t SUBSET s
             ==> f real_continuous (at x within t)`,
  REWRITE_TAC[REAL_CONTINUOUS_WITHIN; REALLIM_WITHIN_SUBSET]);;

let CONTINUOUS_WITHINREAL_SUBSET = prove
 (`!f s t. f continuous (atreal x within s) /\ t SUBSET s
             ==> f continuous (atreal x within t)`,
  REWRITE_TAC[CONTINUOUS_WITHINREAL; LIM_WITHINREAL_SUBSET]);;

let continuous_withinreal = prove
 (`f continuous (atreal x within s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    (!x'. x' IN s /\ abs(x' - x) < d ==> dist(f x',f x) < e)`,
  REWRITE_TAC[CONTINUOUS_WITHINREAL; LIM_WITHINREAL] THEN
  REWRITE_TAC[REAL_ARITH `&0 < abs(x - y) <=> ~(x = y)`] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `d:real` THEN
  ASM_CASES_TAC `&0 < d` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC[DIST_REFL]);;

let continuous_atreal = prove
 (`f continuous (atreal x) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    (!x'. abs(x' - x) < d ==> dist(f x',f x) < e)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[continuous_withinreal; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic combining theorems.                                            *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_CONST = prove
 (`!net c. (\x. c) real_continuous net`,
  REWRITE_TAC[real_continuous; REALLIM_CONST]);;

let REAL_CONTINUOUS_LMUL = prove
 (`!f c net. f real_continuous net ==> (\x. c * f(x)) real_continuous net`,
  REWRITE_TAC[real_continuous; REALLIM_LMUL]);;

let REAL_CONTINUOUS_RMUL = prove
 (`!f c net. f real_continuous net ==> (\x. f(x) * c) real_continuous net`,
  REWRITE_TAC[real_continuous; REALLIM_RMUL]);;

let REAL_CONTINUOUS_NEG = prove
 (`!f net. f real_continuous net ==> (\x. --(f x)) real_continuous net`,
  REWRITE_TAC[real_continuous; REALLIM_NEG]);;

let REAL_CONTINUOUS_ADD = prove
 (`!f g net. f real_continuous net /\ g real_continuous net
           ==> (\x. f(x) + g(x)) real_continuous net`,
  REWRITE_TAC[real_continuous; REALLIM_ADD]);;

let REAL_CONTINUOUS_SUB = prove
 (`!f g net. f real_continuous net /\ g real_continuous net
           ==> (\x. f(x) - g(x)) real_continuous net`,
  REWRITE_TAC[real_continuous; REALLIM_SUB]);;

let REAL_CONTINUOUS_MUL = prove
 (`!net f g.
     f real_continuous net /\ g real_continuous net
     ==> (\x. f(x) * g(x)) real_continuous net`,
  SIMP_TAC[real_continuous; REALLIM_MUL]);;

let REAL_CONTINUOUS_INV = prove
 (`!net f.
    f real_continuous net /\ ~(f(netlimit net) = &0)
    ==> (\x. inv(f x)) real_continuous net`,
  SIMP_TAC[real_continuous; REALLIM_INV]);;

let REAL_CONTINUOUS_DIV = prove
 (`!net f g.
    f real_continuous net /\ g real_continuous net /\ ~(g(netlimit net) = &0)
    ==> (\x. f(x) / g(x)) real_continuous net`,
  SIMP_TAC[real_continuous; REALLIM_DIV]);;

let REAL_CONTINUOUS_POW = prove
 (`!net f n. f real_continuous net ==> (\x. f(x) pow n) real_continuous net`,
  SIMP_TAC[real_continuous; REALLIM_POW]);;

(* ------------------------------------------------------------------------- *)
(* Some of these without netlimit, but with many different cases.            *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_WITHIN_ID = prove
 (`!x s. (\x. x) real_continuous (atreal x within s)`,
  REWRITE_TAC[real_continuous_withinreal] THEN MESON_TAC[]);;

let REAL_CONTINUOUS_AT_ID = prove
 (`!x. (\x. x) real_continuous (atreal x)`,
  REWRITE_TAC[real_continuous_atreal] THEN MESON_TAC[]);;

let REAL_CONTINUOUS_INV_WITHIN = prove
 (`!f s a. f real_continuous (at a within s) /\ ~(f a = &0)
           ==> (\x. inv(f x)) real_continuous (at a within s)`,
  MESON_TAC[REAL_CONTINUOUS_INV; REAL_CONTINUOUS_TRIVIAL_LIMIT;
            NETLIMIT_WITHIN]);;

let REAL_CONTINUOUS_INV_AT = prove
 (`!f a. f real_continuous (at a) /\ ~(f a = &0)
         ==> (\x. inv(f x)) real_continuous (at a)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_INV_WITHIN]);;

let REAL_CONTINUOUS_INV_WITHINREAL = prove
 (`!f s a. f real_continuous (atreal a within s) /\ ~(f a = &0)
           ==> (\x. inv(f x)) real_continuous (atreal a within s)`,
  MESON_TAC[REAL_CONTINUOUS_INV; REAL_CONTINUOUS_TRIVIAL_LIMIT;
            NETLIMIT_WITHINREAL]);;

let REAL_CONTINUOUS_INV_ATREAL = prove
 (`!f a. f real_continuous (atreal a) /\ ~(f a = &0)
         ==> (\x. inv(f x)) real_continuous (atreal a)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_INV_WITHINREAL]);;

let REAL_CONTINUOUS_DIV_WITHIN = prove
 (`!f s a. f real_continuous (at a within s) /\
           g real_continuous (at a within s) /\ ~(g a = &0)
           ==> (\x. f x / g x) real_continuous (at a within s)`,
  MESON_TAC[REAL_CONTINUOUS_DIV; REAL_CONTINUOUS_TRIVIAL_LIMIT;
            NETLIMIT_WITHIN]);;

let REAL_CONTINUOUS_DIV_AT = prove
 (`!f a. f real_continuous (at a) /\
         g real_continuous (at a) /\ ~(g a = &0)
         ==> (\x. f x / g x) real_continuous (at a)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_DIV_WITHIN]);;

let REAL_CONTINUOUS_DIV_WITHINREAL = prove
 (`!f s a. f real_continuous (atreal a within s) /\
           g real_continuous (atreal a within s) /\ ~(g a = &0)
           ==> (\x. f x / g x) real_continuous (atreal a within s)`,
  MESON_TAC[REAL_CONTINUOUS_DIV; REAL_CONTINUOUS_TRIVIAL_LIMIT;
            NETLIMIT_WITHINREAL]);;

let REAL_CONTINUOUS_DIV_ATREAL = prove
 (`!f a. f real_continuous (atreal a) /\
         g real_continuous (atreal a) /\ ~(g a = &0)
         ==> (\x. f x / g x) real_continuous (atreal a)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_DIV_WITHINREAL]);;

(* ------------------------------------------------------------------------- *)
(* Composition of (real->real) o (real->real) functions.                     *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_WITHINREAL_COMPOSE = prove
 (`!f g x s. f real_continuous (atreal x within s) /\
             g real_continuous (atreal (f x) within IMAGE f s)
             ==> (g o f) real_continuous (atreal x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_continuous_withinreal; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let REAL_CONTINUOUS_ATREAL_COMPOSE = prove
 (`!f g x. f real_continuous (atreal x) /\ g real_continuous (atreal (f x))
           ==> (g o f) real_continuous (atreal x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_continuous_atreal; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Composition of (real->real) o (real^N->real) functions.                   *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_WITHIN_COMPOSE = prove
 (`!f g x s. f real_continuous (at x within s) /\
             g real_continuous (atreal (f x) within IMAGE f s)
             ==> (g o f) real_continuous (at x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_continuous_withinreal; real_continuous_within;
              o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let REAL_CONTINUOUS_AT_COMPOSE = prove
 (`!f g x. f real_continuous (at x) /\
           g real_continuous (atreal (f x) within IMAGE f (:real^N))
           ==> (g o f) real_continuous (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_WITHIN_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Composition of (real^N->real) o (real^M->real^N) functions.               *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_CONTINUOUS_WITHIN_COMPOSE = prove
 (`!f g x s. f continuous (at x within s) /\
             g real_continuous (at (f x) within IMAGE f s)
             ==> (g o f) real_continuous (at x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_continuous_within; continuous_within; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let REAL_CONTINUOUS_CONTINUOUS_AT_COMPOSE = prove
 (`!f g x. f continuous (at x) /\
           g real_continuous (at (f x) within IMAGE f (:real^N))
           ==> (g o f) real_continuous (at x)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[WITHIN_WITHIN; INTER_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_WITHIN_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Composition of (real^N->real) o (real->real^N) functions.                 *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE = prove
 (`!f g x s. f continuous (atreal x within s) /\
             g real_continuous (at (f x) within IMAGE f s)
             ==> (g o f) real_continuous (atreal x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_continuous_within; continuous_withinreal;
              real_continuous_withinreal; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let REAL_CONTINUOUS_CONTINUOUS_ATREAL_COMPOSE = prove
 (`!f g x. f continuous (atreal x) /\
           g real_continuous (at (f x) within IMAGE f (:real))
           ==> (g o f) real_continuous (atreal x)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Composition of (real->real^N) o (real->real) functions.                   *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_REAL_CONTINUOUS_WITHINREAL_COMPOSE = prove
 (`!f g x s. f real_continuous (atreal x within s) /\
             g continuous (atreal (f x) within IMAGE f s)
             ==> (g o f) continuous (atreal x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_continuous_within; continuous_withinreal;
              real_continuous_withinreal; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let CONTINUOUS_REAL_CONTINUOUS_ATREAL_COMPOSE = prove
 (`!f g x. f real_continuous (atreal x) /\
           g continuous (atreal (f x) within IMAGE f (:real))
           ==> (g o f) continuous (atreal x)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[WITHIN_WITHIN; INTER_UNIV] THEN
  REWRITE_TAC[CONTINUOUS_REAL_CONTINUOUS_WITHINREAL_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Composition of (real^M->real^N) o (real->real^M) functions.               *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHINREAL_COMPOSE = prove
 (`!f g x s. f continuous (atreal x within s) /\
             g continuous (at (f x) within IMAGE f s)
             ==> (g o f) continuous (atreal x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[continuous_within; continuous_withinreal; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let CONTINUOUS_ATREAL_COMPOSE = prove
 (`!f g x. f continuous (atreal x) /\
           g continuous (at (f x) within IMAGE f (:real))
           ==> (g o f) continuous (atreal x)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[WITHIN_WITHIN; INTER_UNIV] THEN
  REWRITE_TAC[CONTINUOUS_WITHINREAL_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Composition of (real->real^N) o (real^M->real) functions.                 *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_REAL_CONTINUOUS_WITHIN_COMPOSE = prove
 (`!f g x s. f real_continuous (at x within s) /\
             g continuous (atreal (f x) within IMAGE f s)
             ==> (g o f) continuous (at x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[continuous_within; real_continuous_within; continuous_withinreal;
              o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let CONTINUOUS_REAL_CONTINUOUS_AT_COMPOSE = prove
 (`!f g x. f real_continuous (at x) /\
           g continuous (atreal (f x) within IMAGE f (:real^M))
           ==> (g o f) continuous (at x)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[WITHIN_WITHIN; INTER_UNIV] THEN
  REWRITE_TAC[CONTINUOUS_REAL_CONTINUOUS_WITHIN_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of a real->real function on a set.                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("real_continuous_on",(12,"right"));;

let real_continuous_on = new_definition
  `f real_continuous_on s <=>
        !x. x IN s ==> !e. &0 < e
                           ==> ?d. &0 < d /\
                                   !x'. x' IN s /\ abs(x' - x) < d
                                        ==> abs(f(x') - f(x)) < e`;;

let REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN = prove
 (`!f s. f real_continuous_on s <=>
              !x. x IN s ==> f real_continuous (atreal x within s)`,
  REWRITE_TAC[real_continuous_on; real_continuous_withinreal]);;

let REAL_CONTINUOUS_ON_SUBSET = prove
 (`!f s t. f real_continuous_on s /\ t SUBSET s ==> f real_continuous_on t`,
  REWRITE_TAC[real_continuous_on; SUBSET] THEN MESON_TAC[]);;

let REAL_CONTINUOUS_ON_COMPOSE = prove
 (`!f g s. f real_continuous_on s /\ g real_continuous_on (IMAGE f s)
           ==> (g o f) real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  MESON_TAC[IN_IMAGE; REAL_CONTINUOUS_WITHINREAL_COMPOSE]);;

let REAL_CONTINUOUS_ON = prove
 (`!f s. f real_continuous_on s <=>
          (lift o f o drop) continuous_on (IMAGE lift s)`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              REAL_CONTINUOUS_WITHINREAL; CONTINUOUS_WITHIN;
              FORALL_IN_IMAGE; REALLIM_WITHINREAL_WITHIN; TENDSTO_REAL] THEN
  REWRITE_TAC[o_THM; LIFT_DROP]);;

let REAL_CONTINUOUS_ON_CONST = prove
 (`!s c. (\x. c) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REAL_CONTINUOUS_CONST]);;

let REAL_CONTINUOUS_ON_ID = prove
 (`!s. (\x. x) real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              REAL_CONTINUOUS_WITHIN_ID]);;

let REAL_CONTINUOUS_ON_LMUL = prove
 (`!f c s. f real_continuous_on s ==> (\x. c * f(x)) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REAL_CONTINUOUS_LMUL]);;

let REAL_CONTINUOUS_ON_RMUL = prove
 (`!f c s. f real_continuous_on s ==> (\x. f(x) * c) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REAL_CONTINUOUS_RMUL]);;

let REAL_CONTINUOUS_ON_NEG = prove
 (`!f s. f real_continuous_on s
         ==> (\x. --(f x)) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REAL_CONTINUOUS_NEG]);;

let REAL_CONTINUOUS_ON_ADD = prove
 (`!f g s. f real_continuous_on s /\ g real_continuous_on s
           ==> (\x. f(x) + g(x)) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REAL_CONTINUOUS_ADD]);;

let REAL_CONTINUOUS_ON_SUB = prove
 (`!f g s. f real_continuous_on s /\ g real_continuous_on s
           ==> (\x. f(x) - g(x)) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REAL_CONTINUOUS_SUB]);;

let REAL_CONTINUOUS_ON_MUL = prove
 (`!f g s. f real_continuous_on s /\ g real_continuous_on s
           ==> (\x. f(x) * g(x)) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REAL_CONTINUOUS_MUL]);;

let REAL_CONTINUOUS_ON_POW = prove
 (`!f n s. f real_continuous_on s
           ==> (\x. f(x) pow n) real_continuous_on s`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; REAL_CONTINUOUS_POW]);;

let REAL_CONTINUOUS_ON_UNION = prove
 (`!f s t.
         real_closed s /\ real_closed t /\
         f real_continuous_on s /\ f real_continuous_on t
         ==> f real_continuous_on (s UNION t)`,
  REWRITE_TAC[REAL_CLOSED; REAL_CONTINUOUS_ON; IMAGE_UNION;
              CONTINUOUS_ON_UNION]);;

let REAL_CONTINUOUS_ON_SUM = prove
 (`!t f s.
         FINITE s /\ (!a. a IN s ==> f a real_continuous_on t)
         ==> (\x. sum s (\a. f a x)) real_continuous_on t`,
  REPEAT GEN_TAC THEN SIMP_TAC[REAL_CONTINUOUS_ON; o_DEF; LIFT_SUM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_ON_VSUM) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Real version of uniform continuity.                                       *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("real_uniformly_continuous_on",(12,"right"));;

let real_uniformly_continuous_on = new_definition
  `f real_uniformly_continuous_on s <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x x'. x IN s /\ x' IN s /\ abs(x' - x) < d
                           ==> abs(f x' - f x) < e`;;

let REAL_UNIFORMLY_CONTINUOUS_ON = prove
 (`!f s. f real_uniformly_continuous_on s <=>
          (lift o f o drop) uniformly_continuous_on (IMAGE lift s)`,
  REWRITE_TAC[real_uniformly_continuous_on; uniformly_continuous_on] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_THM; DIST_LIFT; LIFT_DROP]);;

let REAL_UNIFORMLY_CONTINUOUS_IMP_REAL_CONTINUOUS = prove
 (`!f s. f real_uniformly_continuous_on s ==> f real_continuous_on s`,
  REWRITE_TAC[real_uniformly_continuous_on; real_continuous_on] THEN
  MESON_TAC[]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY = prove
 (`!f s. f real_uniformly_continuous_on s <=>
                !x y. (!n. x(n) IN s) /\ (!n. y(n) IN s) /\
                      ((\n. x(n) - y(n)) ---> &0) sequentially
                      ==> ((\n. f(x(n)) - f(y(n))) ---> &0) sequentially`,
  REWRITE_TAC[REAL_UNIFORMLY_CONTINUOUS_ON] THEN
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY; REAL_TENDSTO] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; IN_IMAGE_LIFT_DROP; DROP_SUB; DROP_VEC] THEN
  REWRITE_TAC[FORALL_LIFT_FUN; o_THM; LIFT_DROP]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_SUBSET = prove
 (`!f s t. f real_uniformly_continuous_on s /\ t SUBSET s
           ==> f real_uniformly_continuous_on t`,
  REWRITE_TAC[real_uniformly_continuous_on; SUBSET] THEN MESON_TAC[]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_COMPOSE = prove
 (`!f g s. f real_uniformly_continuous_on s /\
           g real_uniformly_continuous_on (IMAGE f s)
           ==> (g o f) real_uniformly_continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_UNIFORMLY_CONTINUOUS_ON] THEN
  SUBGOAL_THEN
   `IMAGE lift (IMAGE f s) = IMAGE (lift o f o drop) (IMAGE lift s)`
  SUBST1_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP UNIFORMLY_CONTINUOUS_ON_COMPOSE)] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_DROP]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_CONST = prove
 (`!s c. (\x. c) real_uniformly_continuous_on s`,
  REWRITE_TAC[REAL_UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY; o_DEF;
              REAL_SUB_REFL; REALLIM_CONST]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_LMUL = prove
 (`!f c s. f real_uniformly_continuous_on s
           ==> (\x. c * f(x)) real_uniformly_continuous_on s`,
  REWRITE_TAC[REAL_UNIFORMLY_CONTINUOUS_ON] THEN
  REWRITE_TAC[o_DEF; LIFT_CMUL; UNIFORMLY_CONTINUOUS_ON_CMUL]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_RMUL = prove
 (`!f c s. f real_uniformly_continuous_on s
           ==> (\x. f(x) * c) real_uniformly_continuous_on s`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_UNIFORMLY_CONTINUOUS_ON_LMUL]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_ID = prove
 (`!s. (\x. x) real_uniformly_continuous_on s`,
  REWRITE_TAC[real_uniformly_continuous_on] THEN MESON_TAC[]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_NEG = prove
 (`!f s. f real_uniformly_continuous_on s
         ==> (\x. --(f x)) real_uniformly_continuous_on s`,
  ONCE_REWRITE_TAC[REAL_ARITH `--x = -- &1 * x`] THEN
  REWRITE_TAC[REAL_UNIFORMLY_CONTINUOUS_ON_LMUL]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_ADD = prove
 (`!f g s. f real_uniformly_continuous_on s /\
           g real_uniformly_continuous_on s
           ==> (\x. f(x) + g(x)) real_uniformly_continuous_on s`,
  REWRITE_TAC[REAL_UNIFORMLY_CONTINUOUS_ON; o_DEF; LIFT_ADD] THEN
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_ADD]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_SUB = prove
 (`!f g s. f real_uniformly_continuous_on s /\
           g real_uniformly_continuous_on s
           ==> (\x. f(x) - g(x)) real_uniformly_continuous_on s`,
  REWRITE_TAC[REAL_UNIFORMLY_CONTINUOUS_ON; o_DEF; LIFT_SUB] THEN
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_SUB]);;

let REAL_UNIFORMLY_CONTINUOUS_ON_SUM = prove
 (`!t f s.
         FINITE s /\ (!a. a IN s ==> f a real_uniformly_continuous_on t)
         ==> (\x. sum s (\a. f a x)) real_uniformly_continuous_on t`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[REAL_UNIFORMLY_CONTINUOUS_ON; o_DEF; LIFT_SUM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP UNIFORMLY_CONTINUOUS_ON_VSUM) THEN
  REWRITE_TAC[]);;

let REAL_COMPACT_UNIFORMLY_CONTINUOUS = prove
 (`!f s. f real_continuous_on s /\ real_compact s
         ==> f real_uniformly_continuous_on s`,
  REWRITE_TAC[real_compact; REAL_CONTINUOUS_ON; REAL_UNIFORMLY_CONTINUOUS_ON;
              COMPACT_UNIFORMLY_CONTINUOUS]);;

let REAL_COMPACT_CONTINUOUS_IMAGE = prove
 (`!f s. f real_continuous_on s /\ real_compact s
         ==> real_compact (IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_compact; REAL_CONTINUOUS_ON] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_CONTINUOUS_IMAGE) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Continuity versus componentwise continuity.                               *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_COMPONENTWISE = prove
 (`!net f:A->real^N.
        f continuous net <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. (f x)$i) real_continuous net`,
  REWRITE_TAC[real_continuous; continuous; LIM_COMPONENTWISE]);;

let REAL_CONTINUOUS_COMPLEX_COMPONENTS_AT = prove
 (`!z. Re real_continuous (at z) /\ Im real_continuous (at z)`,
  GEN_TAC THEN MP_TAC(ISPECL
   [`at(z:complex)`; `\z:complex. z`] CONTINUOUS_COMPONENTWISE) THEN
  REWRITE_TAC[CONTINUOUS_AT_ID; DIMINDEX_2; FORALL_2] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; ETA_AX]);;

let REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN = prove
 (`!s z. Re real_continuous (at z within s) /\
         Im real_continuous (at z within s)`,
  MESON_TAC[REAL_CONTINUOUS_COMPLEX_COMPONENTS_AT;
              REAL_CONTINUOUS_AT_WITHIN]);;

let REAL_CONTINUOUS_NORM_AT = prove
 (`!z. norm real_continuous (at z)`,
  REWRITE_TAC[real_continuous_at; dist] THEN
  GEN_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN NORM_ARITH_TAC);;

let REAL_CONTINUOUS_NORM_WITHIN = prove
 (`!s z. norm real_continuous (at z within s)`,
  MESON_TAC[REAL_CONTINUOUS_NORM_AT; REAL_CONTINUOUS_AT_WITHIN]);;

(* ------------------------------------------------------------------------- *)
(* Derivative of real->real function.                                        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("has_real_derivative",(12,"right"));;
parse_as_infix ("real_differentiable",(12,"right"));;
parse_as_infix ("real_differentiable_on",(12,"right"));;

let has_real_derivative = new_definition
 `(f has_real_derivative f') net <=>
        ((\x. inv(x - netlimit net) *
              (f x - (f(netlimit net) + f' * (x - netlimit net))))
         ---> &0) net`;;

let real_differentiable = new_definition
 `f real_differentiable net <=> ?f'. (f has_real_derivative f') net`;;

let real_derivative = new_definition
 `real_derivative f x = @f'. (f has_real_derivative f') (atreal x)`;;

let higher_real_derivative = define
 `higher_real_derivative 0 f = f /\
  (!n. higher_real_derivative (SUC n) f =
                real_derivative (higher_real_derivative n f))`;;

let real_differentiable_on = new_definition
 `f real_differentiable_on s <=>
     !x. x IN s ==> ?f'. (f has_real_derivative f') (atreal x within s)`;;

(* ------------------------------------------------------------------------- *)
(* Basic limit definitions in the useful cases.                              *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_WITHINREAL = prove
 (`(f has_real_derivative f') (atreal a within s) <=>
           ((\x. (f x - f a) / (x - a)) ---> f') (atreal a within s)`,
  REWRITE_TAC[has_real_derivative] THEN
  ASM_CASES_TAC `trivial_limit(atreal a within s)` THENL
   [ASM_REWRITE_TAC[REALLIM]; ALL_TAC] THEN
  ASM_SIMP_TAC[NETLIMIT_WITHINREAL] THEN
  GEN_REWRITE_TAC RAND_CONV [REALLIM_NULL] THEN
  REWRITE_TAC[REALLIM_WITHINREAL; REAL_SUB_RZERO] THEN
  SIMP_TAC[REAL_FIELD
   `&0 < abs(x - a) ==> (fy - fa) / (x - a) - f' =
                        inv(x - a) * (fy - (fa + f' * (x - a)))`]);;

let HAS_REAL_DERIVATIVE_ATREAL = prove
 (`(f has_real_derivative f') (atreal a) <=>
           ((\x. (f x - f a) / (x - a)) ---> f') (atreal a)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_WITHINREAL]);;

(* ------------------------------------------------------------------------- *)
(* Relation to Frechet derivative.                                           *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_FRECHET_DERIVATIVE_WITHIN = prove
 (`(f has_real_derivative f') (atreal x within s) <=>
        ((lift o f o drop) has_derivative (\x. f' % x))
        (at (lift x) within (IMAGE lift s))`,
  REWRITE_TAC[has_derivative_within; HAS_REAL_DERIVATIVE_WITHINREAL] THEN
  REWRITE_TAC[o_THM; LIFT_DROP; LIM_WITHIN; REALLIM_WITHINREAL] THEN
  SIMP_TAC[LINEAR_COMPOSE_CMUL; LINEAR_ID; IMP_CONJ] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; DIST_LIFT; GSYM LIFT_SUB; LIFT_DROP;
    NORM_ARITH `dist(x,vec 0) = norm x`; GSYM LIFT_CMUL; GSYM LIFT_ADD;
    NORM_LIFT] THEN
  SIMP_TAC[REAL_FIELD
   `&0 < abs(y - x)
    ==> fy - (fx + f' * (y - x)) = (y - x) * ((fy - fx) / (y - x) - f')`] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_MUL_ASSOC; REAL_ABS_INV; REAL_ABS_ABS] THEN
  SIMP_TAC[REAL_LT_IMP_NZ; REAL_MUL_LINV; REAL_MUL_LID]);;

let HAS_REAL_FRECHET_DERIVATIVE_AT = prove
 (`(f has_real_derivative f') (atreal x) <=>
        ((lift o f o drop) has_derivative (\x. f' % x)) (at (lift x))`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV; GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN] THEN
  REWRITE_TAC[IMAGE_LIFT_UNIV]);;

let HAS_REAL_VECTOR_DERIVATIVE_WITHIN = prove
 (`(f has_real_derivative f') (atreal x within s) <=>
        ((lift o f o drop) has_vector_derivative (lift f'))
        (at (lift x) within (IMAGE lift s))`,
  REWRITE_TAC[has_vector_derivative; HAS_REAL_FRECHET_DERIVATIVE_WITHIN] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_LIFT; GSYM LIFT_CMUL] THEN
  REWRITE_TAC[LIFT_DROP; LIFT_EQ; REAL_MUL_SYM]);;

let HAS_REAL_VECTOR_DERIVATIVE_AT = prove
 (`(f has_real_derivative f') (atreal x) <=>
        ((lift o f o drop) has_vector_derivative (lift f')) (at (lift x))`,
  REWRITE_TAC[has_vector_derivative; HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_LIFT; GSYM LIFT_CMUL] THEN
  REWRITE_TAC[LIFT_DROP; LIFT_EQ; REAL_MUL_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Relation to complex derivative.                                           *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_COMPLEX_DERIVATIVE_WITHIN = prove
 (`(f has_real_derivative f') (atreal a within s) <=>
        ((Cx o f o Re) has_complex_derivative (Cx f'))
                (at (Cx a) within {z | real z /\ Re z IN s})`,
  REWRITE_TAC[HAS_REAL_DERIVATIVE_WITHINREAL; HAS_COMPLEX_DERIVATIVE_WITHIN;
              LIM_WITHIN; IN_ELIM_THM; IMP_CONJ; FORALL_REAL] THEN
  REWRITE_TAC[RE_CX; dist; GSYM CX_SUB; COMPLEX_NORM_CX; o_THM; GSYM CX_DIV;
              REALLIM_WITHINREAL] THEN
  MESON_TAC[]);;

let HAS_REAL_COMPLEX_DERIVATIVE_AT = prove
 (`(f has_real_derivative f') (atreal a) <=>
       ((Cx o f o Re) has_complex_derivative (Cx f')) (at (Cx a) within real)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE = prove
 (`!f s. f real_differentiable_on s <=>
         !x. x IN s ==> f real_differentiable (atreal x within s)`,
  REWRITE_TAC[real_differentiable_on; real_differentiable]);;

let REAL_DIFFERENTIABLE_ON_REAL_OPEN = prove
 (`!f s. real_open s
         ==> (f real_differentiable_on s <=>
              !x. x IN s ==> ?f'. (f has_real_derivative f') (atreal x))`,
  REWRITE_TAC[real_differentiable_on; HAS_REAL_DERIVATIVE_WITHINREAL;
              HAS_REAL_DERIVATIVE_ATREAL] THEN
  SIMP_TAC[REALLIM_WITHINREAL_REAL_OPEN]);;

let REAL_DIFFERENTIABLE_ON_IMP_DIFFERENTIABLE_WITHIN = prove
 (`!f s x. f real_differentiable_on s /\ x IN s
           ==> f real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE]);;

let REAL_DIFFERENTIABLE_ON_IMP_DIFFERENTIABLE_ATREAL = prove
 (`!f s x. f real_differentiable_on s /\ real_open s /\ x IN s
           ==> f real_differentiable (atreal x)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ON_REAL_OPEN; real_differentiable]);;

let HAS_COMPLEX_REAL_DERIVATIVE_WITHIN_GEN = prove
 (`!f g h s d.
        &0 < d /\ x IN s /\
        (h has_complex_derivative Cx(g))
        (at (Cx x) within {z | real z /\ Re(z) IN s}) /\
        (!y. y IN s /\ abs(y - x) < d ==>  h(Cx y) = Cx(f y))
        ==> (f has_real_derivative g) (atreal x within s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`h:complex->complex`; `d:real`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; o_THM; REAL_CX; RE_CX; dist] THEN
  X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Re w`) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o GEN_REWRITE_RULE I [REAL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM CX_SUB; COMPLEX_NORM_CX]) THEN
  ASM_REWRITE_TAC[RE_CX]);;

let HAS_COMPLEX_REAL_DERIVATIVE_AT_GEN = prove
 (`!f g h d.
        &0 < d /\
        (h has_complex_derivative Cx(g)) (at (Cx x) within real) /\
        (!y. abs(y - x) < d ==>  h(Cx y) = Cx(f y))
        ==> (f has_real_derivative g) (atreal x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_WITHIN_GEN THEN
  MAP_EVERY EXISTS_TAC [`h:complex->complex`; `d:real`] THEN
  ASM_REWRITE_TAC[IN_UNIV; ETA_AX; SET_RULE `{x | r x} = r`]);;

let HAS_COMPLEX_REAL_DERIVATIVE_WITHIN = prove
 (`!f g h s.
        x IN s /\
        (h has_complex_derivative Cx(g))
        (at (Cx x) within {z | real z /\ Re(z) IN s}) /\
        (!y. y IN s ==>  h(Cx y) = Cx(f y))
        ==> (f has_real_derivative g) (atreal x within s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_WITHIN_GEN THEN
  MAP_EVERY EXISTS_TAC [`h:complex->complex`; `&1`] THEN
  ASM_SIMP_TAC[REAL_LT_01]);;

let HAS_COMPLEX_REAL_DERIVATIVE_AT = prove
 (`!f g h.
        (h has_complex_derivative Cx(g)) (at (Cx x) within real) /\
        (!y. h(Cx y) = Cx(f y))
        ==> (f has_real_derivative g) (atreal x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_WITHIN THEN
  EXISTS_TAC `h:complex->complex` THEN
  ASM_REWRITE_TAC[IN_UNIV; ETA_AX; SET_RULE `{x | r x} = r`]);;

(* ------------------------------------------------------------------------- *)
(* Property of being an interval (equivalent to convex or connected).        *)
(* ------------------------------------------------------------------------- *)

let is_realinterval = new_definition
 `is_realinterval s <=>
        !a b c. a IN s /\ b IN s /\ a <= c /\ c <= b ==> c IN s`;;

let IS_REALINTERVAL_IS_INTERVAL = prove
 (`!s. is_realinterval s <=> is_interval(IMAGE lift s)`,
  REWRITE_TAC[IS_INTERVAL_1; is_realinterval] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[LIFT_DROP; IN_IMAGE; EXISTS_DROP; UNWIND_THM1] THEN
  REWRITE_TAC[GSYM FORALL_DROP]);;

let IS_REALINTERVAL_CONVEX = prove
 (`!s. is_realinterval s <=> convex(IMAGE lift s)`,
  REWRITE_TAC[IS_REALINTERVAL_IS_INTERVAL; IS_INTERVAL_CONVEX_1]);;

let IS_REALINTERVAL_CONNECTED = prove
 (`!s. is_realinterval s <=> connected(IMAGE lift s)`,
  REWRITE_TAC[IS_REALINTERVAL_IS_INTERVAL; IS_INTERVAL_CONNECTED_1]);;

let TRIVIAL_LIMIT_WITHIN_REALINTERVAL = prove
 (`!s x. is_realinterval s /\ x IN s
         ==> (trivial_limit(atreal x within s) <=> s = {x})`,
  REWRITE_TAC[TRIVIAL_LIMIT_WITHINREAL_WITHIN; IS_REALINTERVAL_CONVEX] THEN
  REWRITE_TAC[FORALL_DROP; GSYM IN_IMAGE_LIFT_DROP; LIFT_DROP] THEN
  SIMP_TAC[TRIVIAL_LIMIT_WITHIN_CONVEX] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE_LIFT_DROP; IN_SING] THEN
  MESON_TAC[LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Some relations with the complex numbers can also be useful.               *)
(* ------------------------------------------------------------------------- *)

let IS_REALINTERVAL_CONVEX_COMPLEX = prove
 (`!s. is_realinterval s <=> convex {z | real z /\ Re z IN s}`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM IMAGE_CX; IS_REALINTERVAL_CONVEX] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o ISPEC `Cx o drop` o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] CONVEX_LINEAR_IMAGE)) THEN
    REWRITE_TAC[GSYM IMAGE_o; GSYM o_ASSOC] THEN
    ONCE_REWRITE_TAC[IMAGE_o] THEN REWRITE_TAC[IMAGE_LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[linear; o_THM; CX_ADD; CX_MUL; DROP_ADD; DROP_CMUL;
                COMPLEX_CMUL];
    DISCH_THEN(MP_TAC o ISPEC `lift o Re` o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] CONVEX_LINEAR_IMAGE)) THEN
    REWRITE_TAC[GSYM IMAGE_o; GSYM o_ASSOC] THEN
    ONCE_REWRITE_TAC[IMAGE_o] THEN
    REWRITE_TAC[o_DEF; RE_CX; SET_RULE `IMAGE (\x. x) s = s`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[linear; o_THM; RE_CMUL;
                RE_ADD; RE_MUL_CX; LIFT_ADD; LIFT_CMUL]]);;

(* ------------------------------------------------------------------------- *)
(* The same tricks to define closed and open intervals.                      *)
(* ------------------------------------------------------------------------- *)

let open_real_interval = new_definition
  `open_real_interval(a:real,b:real) = {x:real | a < x /\ x < b}`;;

let closed_real_interval = define
  `closed_real_interval[a:real,b:real] = {x:real | a <= x /\ x <= b}`;;

make_overloadable "real_interval" `:A`;;

overload_interface("real_interval",`open_real_interval`);;
overload_interface("real_interval",`closed_real_interval`);;

let real_interval = prove
 (`real_interval(a,b) = {x | a < x /\ x < b} /\
   real_interval[a,b] = {x | a <= x /\ x <= b}`,
  REWRITE_TAC[open_real_interval; closed_real_interval]);;

let IN_REAL_INTERVAL = prove
 (`!a b x. (x IN real_interval[a,b] <=> a <= x /\ x <= b) /\
           (x IN real_interval(a,b) <=> a < x /\ x < b)`,
  REWRITE_TAC[real_interval; IN_ELIM_THM]);;

let REAL_INTERVAL_INTERVAL = prove
 (`real_interval[a,b] = IMAGE drop (interval[lift a,lift b]) /\
   real_interval(a,b) = IMAGE drop (interval(lift a,lift b))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTERVAL_1; IN_REAL_INTERVAL] THEN
  REWRITE_TAC[EXISTS_LIFT; LIFT_DROP; UNWIND_THM1]);;

let INTERVAL_REAL_INTERVAL = prove
 (`interval[a,b] = IMAGE lift (real_interval[drop a,drop b]) /\
   interval(a,b) = IMAGE lift (real_interval(drop a,drop b))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTERVAL_1; IN_REAL_INTERVAL] THEN
  REWRITE_TAC[EXISTS_DROP; LIFT_DROP; UNWIND_THM1]);;

let EMPTY_AS_REAL_INTERVAL = prove
 (`{} = real_interval[&1,&0]`,
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; LIFT_NUM; GSYM EMPTY_AS_INTERVAL] THEN
  REWRITE_TAC[IMAGE_CLAUSES]);;

let IMAGE_LIFT_REAL_INTERVAL = prove
 (`IMAGE lift (real_interval[a,b]) = interval[lift a,lift b] /\
   IMAGE lift (real_interval(a,b)) = interval(lift a,lift b)`,
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; GSYM IMAGE_o; o_DEF; LIFT_DROP] THEN
  SET_TAC[]);;

let IMAGE_DROP_INTERVAL = prove
 (`IMAGE drop (interval[a,b]) = real_interval[drop a,drop b] /\
   IMAGE drop (interval(a,b)) = real_interval(drop a,drop b)`,
  REWRITE_TAC[INTERVAL_REAL_INTERVAL; GSYM IMAGE_o; o_DEF; LIFT_DROP] THEN
  SET_TAC[]);;

let SUBSET_REAL_INTERVAL = prove
 (`!a b c d.
        (real_interval[a,b] SUBSET real_interval[c,d] <=>
                b < a \/ c <= a /\ a <= b /\ b <= d) /\
        (real_interval[a,b] SUBSET real_interval(c,d) <=>
                b < a \/ c < a /\ a <= b /\ b < d) /\
        (real_interval(a,b) SUBSET real_interval[c,d] <=>
                b <= a \/ c <= a /\ a < b /\ b <= d) /\
        (real_interval(a,b) SUBSET real_interval(c,d) <=>
                b <= a \/ c <= a /\ a < b /\ b <= d)`,
  let lemma = prove
   (`IMAGE drop s SUBSET IMAGE drop t <=> s SUBSET t`,
    SET_TAC[LIFT_DROP]) in
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; lemma; SUBSET_INTERVAL_1] THEN
  REWRITE_TAC[LIFT_DROP]);;

let REAL_INTERVAL_OPEN_SUBSET_CLOSED = prove
 (`!a b. real_interval(a,b) SUBSET real_interval[a,b]`,
  REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

let REAL_INTERVAL_EQ_EMPTY = prove
 (`(!a b. real_interval[a,b] = {} <=> b < a) /\
   (!a b. real_interval(a,b) = {} <=> b <= a)`,
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY_1; LIFT_DROP]);;

let REAL_CLOSED_REAL_INTERVAL = prove
 (`!a b. real_closed(real_interval[a,b])`,
  REWRITE_TAC[REAL_CLOSED; IMAGE_LIFT_REAL_INTERVAL; CLOSED_INTERVAL]);;

let REAL_OPEN_REAL_INTERVAL = prove
 (`!a b. real_open(real_interval(a,b))`,
  REWRITE_TAC[REAL_OPEN; IMAGE_LIFT_REAL_INTERVAL; OPEN_INTERVAL]);;

let REAL_INTERVAL_SING = prove
 (`!a. real_interval[a,a] = {a} /\ real_interval(a,a) = {}`,
  REWRITE_TAC[EXTENSION; IN_SING; NOT_IN_EMPTY; IN_REAL_INTERVAL] THEN
  REAL_ARITH_TAC);;

let REAL_COMPACT_INTERVAL = prove
 (`!a b. real_compact(real_interval[a,b])`,
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; real_compact] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_DROP; IMAGE_ID; COMPACT_INTERVAL]);;

let IS_REALINTERVAL_INTERVAL = prove
 (`!a b. is_realinterval(real_interval(a,b)) /\
         is_realinterval(real_interval[a,b])`,
  REWRITE_TAC[is_realinterval; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

let REAL_BOUNDED_REAL_INTERVAL = prove
 (`(!a b. real_bounded(real_interval[a,b])) /\
   (!a b. real_bounded(real_interval(a,b)))`,
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; REAL_BOUNDED; BOUNDED_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* Real continuity and differentiability.                                    *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_CONTINUOUS = prove
 (`f real_continuous net <=> (Cx o f) continuous net`,
  REWRITE_TAC[real_continuous; continuous; REALLIM_COMPLEX; o_THM]);;

let REAL_CONTINUOUS_CONTINUOUS1 = prove
 (`f real_continuous net <=> (lift o f) continuous net`,
  REWRITE_TAC[real_continuous; continuous; TENDSTO_REAL; o_THM]);;

let REAL_CONTINUOUS_CONTINUOUS_ATREAL = prove
 (`f real_continuous (atreal x) <=> (lift o f o drop) continuous (at(lift x))`,
  REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL_AT; CONTINUOUS_AT;
              TENDSTO_REAL; o_THM; LIFT_DROP]);;

let REAL_CONTINUOUS_CONTINUOUS_WITHINREAL = prove
 (`f real_continuous (atreal x within s) <=>
   (lift o f o drop) continuous (at(lift x) within IMAGE lift s)`,
  REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; REALLIM_WITHINREAL_WITHIN] THEN
  REWRITE_TAC[TENDSTO_REAL; CONTINUOUS_WITHIN; o_THM; LIFT_DROP]);;

let REAL_COMPLEX_CONTINUOUS_WITHINREAL = prove
 (`f real_continuous (atreal x within s) <=>
       (Cx o f o Re) continuous (at (Cx x) within (real INTER IMAGE Cx s))`,
  REWRITE_TAC[real_continuous; continuous; REALLIM_COMPLEX;
         LIM_WITHINREAL_WITHINCOMPLEX; NETLIMIT_WITHINREAL; GSYM o_ASSOC] THEN
  ASM_CASES_TAC `trivial_limit(at(Cx x) within (real INTER IMAGE Cx s))` THENL
   [ASM_REWRITE_TAC[LIM];
    ASM_SIMP_TAC[TRIVIAL_LIMIT_WITHINREAL_WITHINCOMPLEX;
        NETLIMIT_WITHIN; NETLIMIT_WITHINREAL; RE_CX; o_THM]]);;

let REAL_COMPLEX_CONTINUOUS_ATREAL = prove
 (`f real_continuous (atreal x) <=>
       (Cx o f o Re) continuous (at (Cx x) within real)`,
  REWRITE_TAC[real_continuous; continuous; REALLIM_COMPLEX;
              LIM_ATREAL_ATCOMPLEX; NETLIMIT_ATREAL; GSYM o_ASSOC] THEN
  ASM_CASES_TAC `trivial_limit(at(Cx x) within real)` THENL
   [ASM_REWRITE_TAC[LIM];
    ASM_SIMP_TAC[NETLIMIT_WITHIN; RE_CX; o_THM]]);;

let HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_WITHINREAL = prove
 (`!f f' x s. (f has_real_derivative f') (atreal x within s)
              ==> f real_continuous (atreal x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN;
              REAL_COMPLEX_CONTINUOUS_WITHINREAL] THEN
  DISCH_THEN(MP_TAC o
    MATCH_MP HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_WITHIN) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_IMAGE] THEN
  MESON_TAC[REAL; RE_CX; REAL_CX; IN]);;

let REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL = prove
 (`!f x s. f real_differentiable (atreal x within s)
           ==> f real_continuous (atreal x within s)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_WITHINREAL;
            real_differentiable]);;

let HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL = prove
 (`!f f' x. (f has_real_derivative f') (atreal x)
            ==> f real_continuous (atreal x)`,
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_AT;
              REAL_COMPLEX_CONTINUOUS_ATREAL;
              HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_WITHIN]);;

let REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL = prove
 (`!f x. f real_differentiable atreal x ==> f real_continuous atreal x`,
  MESON_TAC[HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL; real_differentiable]);;

let REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON = prove
 (`!f s. f real_differentiable_on s ==> f real_continuous_on s`,
  REWRITE_TAC[real_differentiable_on;
              REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  MESON_TAC[REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL;
            real_differentiable]);;

let REAL_CONTINUOUS_AT_COMPONENT = prove
 (`!i a. 1 <= i /\ i <= dimindex(:N)
         ==> (\x:real^N. x$i) real_continuous at a`,
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF;
              CONTINUOUS_AT_LIFT_COMPONENT]);;

let REAL_CONTINUOUS_AT_TRANSLATION = prove
 (`!a z f:real^N->real.
    f real_continuous at (a + z) <=> (\x. f(a + x)) real_continuous at z`,
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF; CONTINUOUS_AT_TRANSLATION]);;

add_translation_invariants [REAL_CONTINUOUS_AT_TRANSLATION];;

let REAL_CONTINUOUS_AT_LINEAR_IMAGE = prove
 (`!h:real^N->real^N z f:real^N->real.
        linear h /\ (!x. norm(h x) = norm x)
        ==> (f real_continuous at (h z) <=> (\x. f(h x)) real_continuous at z)`,
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF;
              CONTINUOUS_AT_LINEAR_IMAGE]);;

add_linear_invariants [REAL_CONTINUOUS_AT_LINEAR_IMAGE];;

let REAL_CONTINUOUS_AT_ARG = prove
 (`!z. ~(real z /\ &0 <= Re z) ==> Arg real_continuous (at z)`,
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS; CONTINUOUS_AT_ARG]);;

(* ------------------------------------------------------------------------- *)
(* More basics about real derivatives.                                       *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_WITHIN_SUBSET = prove
 (`!f s t x. (f has_real_derivative f') (atreal x within s) /\ t SUBSET s
             ==> (f has_real_derivative f') (atreal x within t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
   HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET) THEN ASM SET_TAC[]);;

let REAL_DIFFERENTIABLE_ON_SUBSET = prove
 (`!f s t. f real_differentiable_on s /\ t SUBSET s
           ==> f real_differentiable_on t`,
  REWRITE_TAC[real_differentiable_on] THEN
  MESON_TAC[SUBSET; HAS_REAL_DERIVATIVE_WITHIN_SUBSET]);;

let REAL_DIFFERENTIABLE_WITHIN_SUBSET = prove
 (`!f s t. f real_differentiable (atreal x within s) /\ t SUBSET s
           ==> f real_differentiable (atreal x within t)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_WITHIN_SUBSET]);;

let HAS_REAL_DERIVATIVE_ATREAL_WITHIN = prove
 (`!f f' x s. (f has_real_derivative f') (atreal x)
              ==> (f has_real_derivative f') (atreal x within s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN;
              HAS_REAL_COMPLEX_DERIVATIVE_AT] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
     HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET) THEN ASM SET_TAC[]);;

let HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN = prove
 (`!f f' a s.
         a IN s /\ real_open s
         ==> ((f has_real_derivative f') (atreal a within s) <=>
              (f has_real_derivative f') (atreal a))`,
  REPEAT GEN_TAC THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_WITHINREAL; HAS_REAL_DERIVATIVE_ATREAL;
               REALLIM_WITHINREAL_REAL_OPEN]);;

let REAL_DIFFERENTIABLE_ATREAL_WITHIN = prove
 (`!f s z. f real_differentiable (atreal z)
           ==> f real_differentiable (atreal z within s)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN]);;

let HAS_REAL_DERIVATIVE_TRANSFORM_WITHIN = prove
 (`!f f' g x s d.
       &0 < d /\ x IN s /\
       (!x'. x' IN s /\ abs(x' - x) < d ==> f x' = g x') /\
       (f has_real_derivative f') (atreal x within s)
       ==> (g has_real_derivative f') (atreal x within s)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE
    [TAUT `a /\ b /\ c /\ d ==> e <=> a /\ b /\ c ==> d ==> e`]
    HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[IN_ELIM_THM; REAL_CX; RE_CX] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
   `dist(a,b) < d ==> z <= norm(a - b) ==> z < d`)) THEN
  W(MP_TAC o PART_MATCH (rand o rand) COMPLEX_NORM_GE_RE_IM o rand o snd) THEN
  SIMP_TAC[RE_SUB; RE_CX]);;

let HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL = prove
 (`!f f' g x d.
       &0 < d /\ (!x'. abs(x' - x) < d ==> f x' = g x') /\
       (f has_real_derivative f') (atreal x)
       ==> (g has_real_derivative f') (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_TRANSFORM_WITHIN; IN_UNIV]);;

let HAS_REAL_DERIVATIVE_ZERO_CONSTANT = prove
 (`!f s.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative (&0)) (atreal x within s))
        ==> ?c. !x. x IN s ==> f(x) = c`,
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Cx o f o Re`; `{z | real z /\ Re z IN s}`]
    HAS_COMPLEX_DERIVATIVE_ZERO_CONSTANT) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; IMP_CONJ; FORALL_REAL; RE_CX; o_THM] THEN
  ASM_REWRITE_TAC[GSYM IS_REALINTERVAL_CONVEX_COMPLEX] THEN MESON_TAC[RE_CX]);;

let HAS_REAL_DERIVATIVE_ZERO_UNIQUE = prove
 (`!f s c a.
        is_realinterval s /\ a IN s /\ f a = c /\
        (!x. x IN s ==> (f has_real_derivative (&0)) (atreal x within s))
        ==> !x. x IN s ==> f(x) = c`,
  MESON_TAC[HAS_REAL_DERIVATIVE_ZERO_CONSTANT]);;

let REAL_DIFF_CHAIN_WITHIN = prove
 (`!f g f' g' x s.
        (f has_real_derivative f') (atreal x within s) /\
        (g has_real_derivative g') (atreal (f x) within (IMAGE f s))
        ==> ((g o f) has_real_derivative (g' * f'))(atreal x within s)`,
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Cx o (g o f) o Re = (Cx o g o Re) o (Cx o f o Re)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_DEF; RE_CX]; ALL_TAC] THEN
  REWRITE_TAC[CX_MUL] THEN MATCH_MP_TAC COMPLEX_DIFF_CHAIN_WITHIN THEN
  ASM_REWRITE_TAC[o_THM; RE_CX] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_ELIM_THM; o_THM; REAL_CX; RE_CX] THEN SET_TAC[]);;

let REAL_DIFF_CHAIN_ATREAL = prove
 (`!f g f' g' x.
        (f has_real_derivative f') (atreal x) /\
        (g has_real_derivative g') (atreal (f x))
        ==> ((g o f) has_real_derivative (g' * f')) (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  ASM_MESON_TAC[REAL_DIFF_CHAIN_WITHIN; SUBSET_UNIV;
                HAS_REAL_DERIVATIVE_WITHIN_SUBSET]);;

let HAS_REAL_DERIVATIVE_CHAIN = prove
 (`!P f g.
        (!x. P x ==> (g has_real_derivative g'(x)) (atreal x))
        ==> (!x s. (f has_real_derivative f') (atreal x within s) /\ P(f x)
                   ==> ((\x. g(f x)) has_real_derivative f' * g'(f x))
                       (atreal x within s)) /\
            (!x. (f has_real_derivative f') (atreal x) /\ P(f x)
                 ==> ((\x. g(f x)) has_real_derivative f' * g'(f x))
                     (atreal x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM o_DEF] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_MESON_TAC[REAL_DIFF_CHAIN_WITHIN; REAL_DIFF_CHAIN_ATREAL;
                HAS_REAL_DERIVATIVE_ATREAL_WITHIN]);;

let HAS_REAL_DERIVATIVE_CHAIN_UNIV = prove
 (`!f g. (!x. (g has_real_derivative g'(x)) (atreal x))
         ==> (!x s. (f has_real_derivative f') (atreal x within s)
                    ==> ((\x. g(f x)) has_real_derivative f' * g'(f x))
                        (atreal x within s)) /\
             (!x. (f has_real_derivative f') (atreal x)
                  ==> ((\x. g(f x)) has_real_derivative f' * g'(f x))
                      (atreal x))`,
  MP_TAC(SPEC `\x:real. T` HAS_REAL_DERIVATIVE_CHAIN) THEN SIMP_TAC[]);;

let REAL_DERIVATIVE_UNIQUE_ATREAL = prove
 (`!f z f' f''.
        (f has_real_derivative f') (atreal z) /\
        (f has_real_derivative f'') (atreal z)
        ==> f' = f''`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  DISCH_THEN(MP_TAC o C AP_THM `vec 1:real^1`) THEN
  REWRITE_TAC[VECTOR_MUL_RCANCEL; VEC_EQ; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Some handy theorems about the actual differentition function.             *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_DERIVATIVE = prove
 (`!net f f' x. (f has_real_derivative f') (atreal x)
                ==> real_derivative f x = f'`,
  REWRITE_TAC[real_derivative] THEN
  MESON_TAC[REAL_DERIVATIVE_UNIQUE_ATREAL]);;

let HAS_REAL_DERIVATIVE_DIFFERENTIABLE = prove
 (`!f x. (f has_real_derivative (real_derivative f x)) (atreal x) <=>
         f real_differentiable atreal x`,
  REWRITE_TAC[real_differentiable; real_derivative] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetical combining theorems.                                          *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_LMUL_WITHIN = prove
 (`!f f' c x s.
        (f has_real_derivative f') (atreal x within s)
        ==> ((\x. c * f(x)) has_real_derivative (c * f')) (atreal x within s)`,
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN
  REWRITE_TAC[o_DEF; CX_MUL; HAS_COMPLEX_DERIVATIVE_LMUL_WITHIN]);;

let HAS_REAL_DERIVATIVE_LMUL_ATREAL = prove
 (`!f f' c x.
        (f has_real_derivative f') (atreal x)
        ==> ((\x. c * f(x)) has_real_derivative (c * f')) (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_LMUL_WITHIN]);;

let HAS_REAL_DERIVATIVE_RMUL_WITHIN = prove
 (`!f f' c x s.
        (f has_real_derivative f') (atreal x within s)
        ==> ((\x. f(x) * c) has_real_derivative (f' * c)) (atreal x within s)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_LMUL_WITHIN]);;

let HAS_REAL_DERIVATIVE_RMUL_ATREAL = prove
 (`!f f' c x.
        (f has_real_derivative f') (atreal x)
        ==> ((\x. f(x) * c) has_real_derivative (f' * c)) (atreal x)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_LMUL_ATREAL]);;

let HAS_REAL_DERIVATIVE_CDIV_WITHIN = prove
 (`!f f' c x s.
        (f has_real_derivative f') (atreal x within s)
        ==> ((\x. f(x) / c) has_real_derivative (f' / c)) (atreal x within s)`,
  SIMP_TAC[real_div; HAS_REAL_DERIVATIVE_RMUL_WITHIN]);;

let HAS_REAL_DERIVATIVE_CDIV_ATREAL = prove
 (`!f f' c x s.
        (f has_real_derivative f') (atreal x)
        ==> ((\x. f(x) / c) has_real_derivative (f' / c)) (atreal x)`,
  SIMP_TAC[real_div; HAS_REAL_DERIVATIVE_RMUL_ATREAL]);;

let HAS_REAL_DERIVATIVE_ID = prove
 (`!net. ((\x. x) has_real_derivative &1) net`,
  REWRITE_TAC[has_real_derivative; TENDSTO_REAL;
              REAL_ARITH `x - (a + &1 * (x - a)) = &0`] THEN
  REWRITE_TAC[REAL_MUL_RZERO; LIM_CONST; o_DEF]);;

let HAS_REAL_DERIVATIVE_CONST = prove
 (`!c net. ((\x. c) has_real_derivative &0) net`,
  REWRITE_TAC[has_real_derivative; REAL_MUL_LZERO; REAL_ADD_RID; REAL_SUB_REFL;
              REAL_MUL_RZERO; REALLIM_CONST]);;

let HAS_REAL_DERIVATIVE_NEG = prove
 (`!f f' net. (f has_real_derivative f') net
            ==> ((\x. --(f(x))) has_real_derivative (--f')) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_derivative] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REALLIM_NEG) THEN
  REWRITE_TAC[REAL_NEG_0; REAL_ARITH
   `a * (--b - (--c + --d * e:real)) = --(a * (b - (c + d * e)))`]);;

let HAS_REAL_DERIVATIVE_ADD = prove
 (`!f f' g g' net.
        (f has_real_derivative f') net /\ (g has_real_derivative g') net
        ==> ((\x. f(x) + g(x)) has_real_derivative (f' + g')) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_derivative] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REALLIM_ADD) THEN
  REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; REAL_ADD_RID] THEN
  REWRITE_TAC[REAL_ARITH
   `(fx - (fa + f' * (x - a))) + (gx - (ga + g' * (x - a))):real =
    (fx + gx) - ((fa + ga) + (f' + g') * (x - a))`]);;

let HAS_REAL_DERIVATIVE_SUB = prove
 (`!f f' g g' net.
        (f has_real_derivative f') net /\ (g has_real_derivative g') net
        ==> ((\x. f(x) - g(x)) has_real_derivative (f' - g')) net`,
  SIMP_TAC[real_sub; HAS_REAL_DERIVATIVE_ADD; HAS_REAL_DERIVATIVE_NEG]);;

let HAS_REAL_DERIVATIVE_MUL_WITHIN = prove
 (`!f f' g g' x s.
        (f has_real_derivative f') (atreal x within s) /\
        (g has_real_derivative g') (atreal x within s)
        ==> ((\x. f(x) * g(x)) has_real_derivative
             (f(x) * g' + f' * g(x))) (atreal x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_MUL_WITHIN) THEN
  REWRITE_TAC[o_DEF; CX_MUL; CX_ADD; RE_CX]);;

let HAS_REAL_DERIVATIVE_MUL_ATREAL = prove
 (`!f f' g g' x.
        (f has_real_derivative f') (atreal x) /\
        (g has_real_derivative g') (atreal x)
        ==> ((\x. f(x) * g(x)) has_real_derivative
             (f(x) * g' + f' * g(x))) (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_MUL_WITHIN]);;

let HAS_REAL_DERIVATIVE_POW_WITHIN = prove
 (`!f f' x s n. (f has_real_derivative f') (atreal x within s)
                ==> ((\x. f(x) pow n) has_real_derivative
                     (&n * f(x) pow (n - 1) * f')) (atreal x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_WITHIN] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num` o
    MATCH_MP HAS_COMPLEX_DERIVATIVE_POW_WITHIN) THEN
  REWRITE_TAC[o_DEF; CX_MUL; CX_POW; RE_CX]);;

let HAS_REAL_DERIVATIVE_POW_ATREAL = prove
 (`!f f' x n. (f has_real_derivative f') (atreal x)
              ==> ((\x. f(x) pow n) has_real_derivative
                   (&n * f(x) pow (n - 1) * f')) (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_POW_WITHIN]);;

let HAS_REAL_DERIVATIVE_INV_BASIC = prove
 (`!x. ~(x = &0)
         ==> ((inv) has_real_derivative (--inv(x pow 2))) (atreal x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HAS_REAL_COMPLEX_DERIVATIVE_AT] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN THEN
  EXISTS_TAC `inv:complex->complex` THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_INV_BASIC; CX_INJ; CX_NEG; CX_INV;
               CX_POW; HAS_COMPLEX_DERIVATIVE_AT_WITHIN] THEN
  SIMP_TAC[IN; FORALL_REAL; IMP_CONJ; o_DEF; REAL_CX; RE_CX; CX_INV] THEN
  MESON_TAC[REAL_LT_01]);;

let HAS_REAL_DERIVATIVE_INV_WITHIN = prove
 (`!f f' x s. (f has_real_derivative f') (atreal x within s) /\
              ~(f x = &0)
              ==> ((\x. inv(f(x))) has_real_derivative (--f' / f(x) pow 2))
                  (atreal x within s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `~(g = &0) ==> --f / g pow 2 = --inv(g pow 2) * f`] THEN
  MATCH_MP_TAC REAL_DIFF_CHAIN_WITHIN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_INV_BASIC]);;

let HAS_REAL_DERIVATIVE_INV_ATREAL = prove
 (`!f f' x. (f has_real_derivative f') (atreal x) /\
            ~(f x = &0)
            ==> ((\x. inv(f(x))) has_real_derivative (--f' / f(x) pow 2))
                (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_INV_WITHIN]);;

let HAS_REAL_DERIVATIVE_DIV_WITHIN = prove
 (`!f f' g g' x s.
        (f has_real_derivative f') (atreal x within s) /\
        (g has_real_derivative g') (atreal x within s) /\
        ~(g(x) = &0)
        ==> ((\x. f(x) / g(x)) has_real_derivative
             (f' * g(x) - f(x) * g') / g(x) pow 2) (atreal x within s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT2 th) THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_INV_WITHIN) THEN
  UNDISCH_TAC `(f has_real_derivative f') (atreal x within s)` THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_MUL_WITHIN) THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD);;

let HAS_REAL_DERIVATIVE_DIV_ATREAL = prove
 (`!f f' g g' x.
        (f has_real_derivative f') (atreal x) /\
        (g has_real_derivative g') (atreal x) /\
        ~(g(x) = &0)
        ==> ((\x. f(x) / g(x)) has_real_derivative
             (f' * g(x) - f(x) * g') / g(x) pow 2) (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_DIV_WITHIN]);;

let HAS_REAL_DERIVATIVE_SUM = prove
 (`!f net s.
         FINITE s /\ (!a. a IN s ==> (f a has_real_derivative f' a) net)
         ==> ((\x. sum s (\a. f a x)) has_real_derivative (sum s f'))
             net`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; SUM_CLAUSES] THEN
  SIMP_TAC[HAS_REAL_DERIVATIVE_CONST; HAS_REAL_DERIVATIVE_ADD; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Same thing just for real differentiability.                               *)
(* ------------------------------------------------------------------------- *)

let REAL_DIFFERENTIABLE_CONST = prove
 (`!c net. (\z. c) real_differentiable net`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_CONST]);;

let REAL_DIFFERENTIABLE_ID = prove
 (`!net. (\z. z) real_differentiable net`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_ID]);;

let REAL_DIFFERENTIABLE_NEG = prove
 (`!f net.
        f real_differentiable net
        ==> (\z. --(f z)) real_differentiable net`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_NEG]);;

let REAL_DIFFERENTIABLE_ADD = prove
 (`!f g net.
        f real_differentiable net /\
        g real_differentiable net
        ==> (\z. f z + g z) real_differentiable net`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_ADD]);;

let REAL_DIFFERENTIABLE_SUB = prove
 (`!f g net.
        f real_differentiable net /\
        g real_differentiable net
        ==> (\z. f z - g z) real_differentiable net`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_SUB]);;

let REAL_DIFFERENTIABLE_INV_WITHIN = prove
 (`!f z s.
        f real_differentiable (atreal z within s) /\ ~(f z = &0)
        ==> (\z. inv(f z)) real_differentiable (atreal z within s)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_INV_WITHIN]);;

let REAL_DIFFERENTIABLE_MUL_WITHIN = prove
 (`!f g z s.
        f real_differentiable (atreal z within s) /\
        g real_differentiable (atreal z within s)
        ==> (\z. f z * g z) real_differentiable (atreal z within s)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_MUL_WITHIN]);;

let REAL_DIFFERENTIABLE_DIV_WITHIN = prove
 (`!f g z s.
        f real_differentiable (atreal z within s) /\
        g real_differentiable (atreal z within s) /\
        ~(g z = &0)
        ==> (\z. f z / g z) real_differentiable (atreal z within s)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_DIV_WITHIN]);;

let REAL_DIFFERENTIABLE_POW_WITHIN = prove
 (`!f n z s.
        f real_differentiable (atreal z within s)
        ==> (\z. f z pow n) real_differentiable (atreal z within s)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_POW_WITHIN]);;

let REAL_DIFFERENTIABLE_TRANSFORM_WITHIN = prove
 (`!f g x s d.
        &0 < d /\
        x IN s /\
        (!x'. x' IN s /\ abs(x' - x) < d ==> f x' = g x') /\
        f real_differentiable (atreal x within s)
        ==> g real_differentiable (atreal x within s)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_TRANSFORM_WITHIN]);;

let REAL_DIFFERENTIABLE_TRANSFORM = prove
 (`!f g s. (!x. x IN s ==> f x = g x) /\ f real_differentiable_on s
           ==> g real_differentiable_on s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[real_differentiable_on; GSYM real_differentiable] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`f:real->real`; `&1`] THEN
  ASM_SIMP_TAC[REAL_LT_01]);;

let REAL_DIFFERENTIABLE_EQ = prove
 (`!f g s. (!x. x IN s ==> f x = g x)
           ==> (f real_differentiable_on s <=> g real_differentiable_on s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_TRANSFORM]);;

let REAL_DIFFERENTIABLE_INV_ATREAL = prove
 (`!f z.
        f real_differentiable atreal z /\ ~(f z = &0)
        ==> (\z. inv(f z)) real_differentiable atreal z`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_INV_ATREAL]);;

let REAL_DIFFERENTIABLE_MUL_ATREAL = prove
 (`!f g z.
        f real_differentiable atreal z /\
        g real_differentiable atreal z
        ==> (\z. f z * g z) real_differentiable atreal z`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_MUL_ATREAL]);;

let REAL_DIFFERENTIABLE_DIV_ATREAL = prove
 (`!f g z.
        f real_differentiable atreal z /\
        g real_differentiable atreal z /\
        ~(g z = &0)
        ==> (\z. f z / g z) real_differentiable atreal z`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_DIV_ATREAL]);;

let REAL_DIFFERENTIABLE_POW_ATREAL = prove
 (`!f n z.
        f real_differentiable atreal z
        ==> (\z. f z pow n) real_differentiable atreal z`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_POW_ATREAL]);;

let REAL_DIFFERENTIABLE_TRANSFORM_ATREAL = prove
 (`!f g x d.
        &0 < d /\
        (!x'. abs(x' - x) < d ==> f x' = g x') /\
        f real_differentiable atreal x
        ==> g real_differentiable atreal x`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL]);;

let REAL_DIFFERENTIABLE_COMPOSE_WITHIN = prove
 (`!f g x s.
         f real_differentiable (atreal x within s) /\
         g real_differentiable (atreal (f x) within IMAGE f s)
         ==> (g o f) real_differentiable (atreal x within s)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[REAL_DIFF_CHAIN_WITHIN]);;

let REAL_DIFFERENTIABLE_COMPOSE_ATREAL = prove
 (`!f g x s.
         f real_differentiable (atreal x) /\
         g real_differentiable (atreal (f x))
         ==> (g o f) real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[REAL_DIFF_CHAIN_ATREAL]);;

(* ------------------------------------------------------------------------- *)
(* Same again for being holomorphic on a set.                                *)
(* ------------------------------------------------------------------------- *)

let REAL_DIFFERENTIABLE_ON_CONST = prove
 (`!c s. (\z. c) real_differentiable_on s`,
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE;
              REAL_DIFFERENTIABLE_CONST]);;

let REAL_DIFFERENTIABLE_ON_ID = prove
 (`!s. (\z. z) real_differentiable_on s`,
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE; REAL_DIFFERENTIABLE_ID]);;

let REAL_DIFFERENTIABLE_ON_COMPOSE = prove
 (`!f g s. f real_differentiable_on s /\ g real_differentiable_on (IMAGE f s)
           ==> (g o f) real_differentiable_on s`,
  SIMP_TAC[real_differentiable_on; GSYM real_differentiable;
           FORALL_IN_IMAGE] THEN
  MESON_TAC[REAL_DIFFERENTIABLE_COMPOSE_WITHIN]);;

let REAL_DIFFERENTIABLE_ON_NEG = prove
 (`!f s. f real_differentiable_on s ==> (\z. --(f z)) real_differentiable_on s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE; REAL_DIFFERENTIABLE_NEG]);;

let REAL_DIFFERENTIABLE_ON_ADD = prove
 (`!f g s.
        f real_differentiable_on s /\ g real_differentiable_on s
        ==> (\z. f z + g z) real_differentiable_on s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE; REAL_DIFFERENTIABLE_ADD]);;

let REAL_DIFFERENTIABLE_ON_SUB = prove
 (`!f g s.
        f real_differentiable_on s /\ g real_differentiable_on s
        ==> (\z. f z - g z) real_differentiable_on s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE; REAL_DIFFERENTIABLE_SUB]);;

let REAL_DIFFERENTIABLE_ON_MUL = prove
 (`!f g s.
        f real_differentiable_on s /\ g real_differentiable_on s
        ==> (\z. f z * g z) real_differentiable_on s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE;
           REAL_DIFFERENTIABLE_MUL_WITHIN]);;

let REAL_DIFFERENTIABLE_ON_INV = prove
 (`!f s. f real_differentiable_on s /\ (!z. z IN s ==> ~(f z = &0))
         ==> (\z. inv(f z)) real_differentiable_on s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE;
           REAL_DIFFERENTIABLE_INV_WITHIN]);;

let REAL_DIFFERENTIABLE_ON_DIV = prove
 (`!f g s.
        f real_differentiable_on s /\ g real_differentiable_on s /\
        (!z. z IN s ==> ~(g z = &0))
        ==> (\z. f z / g z) real_differentiable_on s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE;
           REAL_DIFFERENTIABLE_DIV_WITHIN]);;

let REAL_DIFFERENTIABLE_ON_POW = prove
 (`!f s n. f real_differentiable_on s
           ==> (\z. (f z) pow n) real_differentiable_on s`,
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE;
           REAL_DIFFERENTIABLE_POW_WITHIN]);;

let REAL_DIFFERENTIABLE_ON_SUM = prove
 (`!f s k. FINITE k /\ (!a. a IN k ==> (f a) real_differentiable_on s)
           ==> (\x. sum k (\a. f a x)) real_differentiable_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC[SUM_CLAUSES] THEN
  SIMP_TAC[REAL_DIFFERENTIABLE_ON_CONST; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_ADD THEN
  ASM_SIMP_TAC[ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Derivative (and continuity) theorems for real transcendental functions.   *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_EXP = prove
 (`!x. (exp has_real_derivative exp(x)) (atreal x)`,
  GEN_TAC THEN MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT THEN
  EXISTS_TAC `cexp` THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN;
               HAS_COMPLEX_DERIVATIVE_CEXP; CX_EXP]);;

let REAL_DIFFERENTIABLE_AT_EXP = prove
 (`!x. exp real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_EXP]);;

let REAL_DIFFERENTIABLE_WITHIN_EXP = prove
 (`!s x. exp real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_EXP]);;

let REAL_CONTINUOUS_AT_EXP = prove
 (`!x. exp real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_EXP;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_EXP = prove
 (`!s x. exp real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_EXP]);;

let REAL_CONTINUOUS_ON_EXP = prove
 (`!s. exp real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              REAL_CONTINUOUS_WITHIN_EXP]);;

let HAS_REAL_DERIVATIVE_SIN = prove
 (`!x. (sin has_real_derivative cos(x)) (atreal x)`,
  GEN_TAC THEN MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT THEN
  EXISTS_TAC `csin` THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN;
               HAS_COMPLEX_DERIVATIVE_CSIN; CX_SIN; CX_COS]);;

let REAL_DIFFERENTIABLE_AT_SIN = prove
 (`!x. sin real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_SIN]);;

let REAL_DIFFERENTIABLE_WITHIN_SIN = prove
 (`!s x. sin real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_SIN]);;

let REAL_CONTINUOUS_AT_SIN = prove
 (`!x. sin real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_SIN;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_SIN = prove
 (`!s x. sin real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_SIN]);;

let REAL_CONTINUOUS_ON_SIN = prove
 (`!s. sin real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              REAL_CONTINUOUS_WITHIN_SIN]);;

let HAS_REAL_DERIVATIVE_COS = prove
 (`!x. (cos has_real_derivative --sin(x)) (atreal x)`,
  GEN_TAC THEN MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT THEN
  EXISTS_TAC `ccos` THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN;
               HAS_COMPLEX_DERIVATIVE_CCOS; CX_SIN; CX_COS; CX_NEG]);;

let REAL_DIFFERENTIABLE_AT_COS = prove
 (`!x. cos real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_COS]);;

let REAL_DIFFERENTIABLE_WITHIN_COS = prove
 (`!s x. cos real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_COS]);;

let REAL_CONTINUOUS_AT_COS = prove
 (`!x. cos real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_COS;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_COS = prove
 (`!s x. cos real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_COS]);;

let REAL_CONTINUOUS_ON_COS = prove
 (`!s. cos real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              REAL_CONTINUOUS_WITHIN_COS]);;

let HAS_REAL_DERIVATIVE_TAN = prove
 (`!x. ~(cos x = &0)
       ==> (tan has_real_derivative inv(cos(x) pow 2)) (atreal x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT THEN
  EXISTS_TAC `ctan` THEN REWRITE_TAC[CX_INV; CX_POW; CX_COS] THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN;
               HAS_COMPLEX_DERIVATIVE_CTAN; GSYM CX_COS; CX_INJ; CX_TAN]);;

let REAL_DIFFERENTIABLE_AT_TAN = prove
 (`!x. ~(cos x = &0) ==> tan real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_TAN]);;

let REAL_DIFFERENTIABLE_WITHIN_TAN = prove
 (`!s x. ~(cos x = &0) ==> tan real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_TAN]);;

let REAL_CONTINUOUS_AT_TAN = prove
 (`!x. ~(cos x = &0) ==> tan real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_TAN;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_TAN = prove
 (`!s x. ~(cos x = &0) ==> tan real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_TAN]);;

let REAL_CONTINUOUS_ON_TAN = prove
 (`!s. (!x. x IN s ==> ~(cos x = &0)) ==> tan real_continuous_on s`,
  MESON_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
            REAL_CONTINUOUS_WITHIN_TAN]);;

let HAS_REAL_DERIVATIVE_LOG = prove
 (`!x. &0 < x ==> (log has_real_derivative inv(x)) (atreal x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT_GEN THEN
  MAP_EVERY EXISTS_TAC [`clog`; `x:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[CX_INV] THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CLOG THEN ASM_REWRITE_TAC[RE_CX];
    MATCH_MP_TAC(GSYM CX_LOG) THEN ASM_REAL_ARITH_TAC]);;

let REAL_DIFFERENTIABLE_AT_LOG = prove
 (`!x. &0 < x ==> log real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_LOG]);;

let REAL_DIFFERENTIABLE_WITHIN_LOG = prove
 (`!s x. &0 < x ==> log real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_LOG]);;

let REAL_CONTINUOUS_AT_LOG = prove
 (`!x. &0 < x ==> log real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_LOG;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_LOG = prove
 (`!s x. &0 < x ==> log real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_LOG]);;

let REAL_CONTINUOUS_ON_LOG = prove
 (`!s. (!x. x IN s ==> &0 < x) ==> log real_continuous_on s`,
  MESON_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
            REAL_CONTINUOUS_WITHIN_LOG]);;

let HAS_REAL_DERIVATIVE_SQRT = prove
 (`!x. &0 < x ==> (sqrt has_real_derivative inv(&2 * sqrt x)) (atreal x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT_GEN THEN
  MAP_EVERY EXISTS_TAC [`csqrt`; `x:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[CX_INV; CX_MUL; CX_SQRT; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CSQRT THEN
    ASM_SIMP_TAC[RE_CX];
    MATCH_MP_TAC(GSYM CX_SQRT) THEN ASM_REAL_ARITH_TAC]);;

let REAL_DIFFERENTIABLE_AT_SQRT = prove
 (`!x. &0 < x ==> sqrt real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_SQRT]);;

let REAL_DIFFERENTIABLE_WITHIN_SQRT = prove
 (`!s x. &0 < x ==> sqrt real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_SQRT]);;

let REAL_CONTINUOUS_AT_SQRT = prove
 (`!x. &0 < x ==> sqrt real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_SQRT;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_SQRT = prove
 (`!s x. &0 < x ==> sqrt real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_SQRT]);;

let HAS_REAL_DERIVATIVE_ATN = prove
 (`!x. (atn has_real_derivative inv(&1 + x pow 2)) (atreal x)`,
  GEN_TAC THEN MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT THEN
  EXISTS_TAC `catn` THEN REWRITE_TAC[CX_INV; CX_ADD; CX_ATN; CX_POW] THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN; HAS_COMPLEX_DERIVATIVE_CATN;
               IM_CX; REAL_ABS_NUM; REAL_LT_01]);;

let REAL_DIFFERENTIABLE_AT_ATN = prove
 (`!x. atn real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_ATN]);;

let REAL_DIFFERENTIABLE_WITHIN_ATN = prove
 (`!s x. atn real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_ATN]);;

let REAL_CONTINUOUS_AT_ATN = prove
 (`!x. atn real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_ATN;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_ATN = prove
 (`!s x. atn real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_ATN]);;

let REAL_CONTINUOUS_ON_ATN = prove
 (`!s. atn real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
              REAL_CONTINUOUS_WITHIN_ATN]);;

let HAS_REAL_DERIVATIVE_ASN_COS = prove
 (`!x. abs(x) < &1 ==> (asn has_real_derivative inv(cos(asn x))) (atreal x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT_GEN THEN
  MAP_EVERY EXISTS_TAC [`casn`; `&1 - abs x`] THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[CX_INV; CX_COS; CX_ASN; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CASN THEN ASM_REWRITE_TAC[RE_CX];
    MATCH_MP_TAC(GSYM CX_ASN) THEN ASM_REAL_ARITH_TAC]);;

let HAS_REAL_DERIVATIVE_ASN = prove
 (`!x. abs(x) < &1
       ==> (asn has_real_derivative inv(sqrt(&1 - x pow 2))) (atreal x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_ASN_COS) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC COS_ASN THEN ASM_REAL_ARITH_TAC);;

let REAL_DIFFERENTIABLE_AT_ASN = prove
 (`!x. abs(x) < &1 ==> asn real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_ASN]);;

let REAL_DIFFERENTIABLE_WITHIN_ASN = prove
 (`!s x. abs(x) < &1 ==> asn real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_ASN]);;

let REAL_CONTINUOUS_AT_ASN = prove
 (`!x. abs(x) < &1 ==> asn real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_ASN;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_ASN = prove
 (`!s x. abs(x) < &1 ==> asn real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_ASN]);;

let HAS_REAL_DERIVATIVE_ACS_SIN = prove
 (`!x. abs(x) < &1 ==> (acs has_real_derivative --inv(sin(acs x))) (atreal x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_REAL_DERIVATIVE_AT_GEN THEN
  MAP_EVERY EXISTS_TAC [`cacs`; `&1 - abs x`] THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[CX_INV; CX_SIN; CX_ACS; CX_NEG; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CACS THEN ASM_REWRITE_TAC[RE_CX];
    MATCH_MP_TAC(GSYM CX_ACS) THEN ASM_REAL_ARITH_TAC]);;

let HAS_REAL_DERIVATIVE_ACS = prove
 (`!x. abs(x) < &1
       ==> (acs has_real_derivative --inv(sqrt(&1 - x pow 2))) (atreal x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_ACS_SIN) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SIN_ACS THEN ASM_REAL_ARITH_TAC);;

let REAL_DIFFERENTIABLE_AT_ACS = prove
 (`!x. abs(x) < &1 ==> acs real_differentiable (atreal x)`,
  REWRITE_TAC[real_differentiable] THEN
  MESON_TAC[HAS_REAL_DERIVATIVE_ACS]);;

let REAL_DIFFERENTIABLE_WITHIN_ACS = prove
 (`!s x. abs(x) < &1 ==> acs real_differentiable (atreal x within s)`,
  MESON_TAC[REAL_DIFFERENTIABLE_ATREAL_WITHIN;
            REAL_DIFFERENTIABLE_AT_ACS]);;

let REAL_CONTINUOUS_AT_ACS = prove
 (`!x. abs(x) < &1 ==> acs real_continuous (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_ACS;
            HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]);;

let REAL_CONTINUOUS_WITHIN_ACS = prove
 (`!s x. abs(x) < &1 ==> acs real_continuous (atreal x within s)`,
  MESON_TAC[REAL_CONTINUOUS_ATREAL_WITHINREAL;
            REAL_CONTINUOUS_AT_ACS]);;

(* ------------------------------------------------------------------------- *)
(* Some somewhat sharper continuity theorems including endpoints.            *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_WITHIN_SQRT_STRONG = prove
 (`!x. sqrt real_continuous (atreal x within {t | &0 <= t})`,
  GEN_TAC THEN REWRITE_TAC[REAL_COMPLEX_CONTINUOUS_WITHINREAL] THEN
  ASM_CASES_TAC `x IN {t | &0 <= t}` THENL
   [MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`csqrt`; `&1`] THEN
    REWRITE_TAC[IMAGE_CX; IN_ELIM_THM; REAL_LT_01;
      CONTINUOUS_WITHIN_CSQRT_POSREAL;
      SET_RULE `real INTER {z | real z /\ P z} = {z | real z /\ P z}`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[REAL_CX; RE_CX; IMP_CONJ; FORALL_REAL; o_THM] THEN
    SIMP_TAC[CX_SQRT];
    MATCH_MP_TAC CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL THEN CONJ_TAC THENL
     [SUBGOAL_THEN `real INTER IMAGE Cx {t | &0 <= t} =
                    real INTER {t | Re t >= &0}`
       (fun th -> SIMP_TAC[th; CLOSED_INTER; CLOSED_REAL;
                           CLOSED_HALFSPACE_RE_GE]) THEN
     REWRITE_TAC[EXTENSION; IMAGE_CX; IN_ELIM_THM; IN_CBALL; IN_INTER] THEN
     REWRITE_TAC[real_ge; IN; CONJ_ACI];
      MATCH_MP_TAC(SET_RULE
       `(!x y. f x = f y ==> x = y) /\ ~(x IN s)
        ==> ~(f x IN t INTER IMAGE f s)`) THEN
      ASM_REWRITE_TAC[CX_INJ]]]);;

let REAL_CONTINUOUS_ON_SQRT = prove
 (`!s. (!x. x IN s ==> &0 <= x) ==> sqrt real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN
  EXISTS_TAC `{x | &0 <= x}` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; REAL_CONTINUOUS_WITHIN_SQRT_STRONG]);;

let REAL_CONTINUOUS_WITHIN_ASN_STRONG = prove
 (`!x. asn real_continuous (atreal x within {t | abs(t) <= &1})`,
  GEN_TAC THEN REWRITE_TAC[REAL_COMPLEX_CONTINUOUS_WITHINREAL] THEN
  ASM_CASES_TAC `x IN {t | abs(t) <= &1}` THENL
   [MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`casn`; `&1`] THEN
    REWRITE_TAC[IMAGE_CX; IN_ELIM_THM; CONTINUOUS_WITHIN_CASN_REAL; REAL_LT_01;
     SET_RULE `real INTER {z | real z /\ P z} = {z | real z /\ P z}`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[REAL_CX; RE_CX; IMP_CONJ; FORALL_REAL; o_THM] THEN
    SIMP_TAC[CX_ASN];
    MATCH_MP_TAC CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL THEN CONJ_TAC THENL
     [SUBGOAL_THEN `real INTER IMAGE Cx {t | abs t <= &1} =
                    real INTER cball(Cx(&0),&1)`
       (fun th -> SIMP_TAC[th; CLOSED_INTER; CLOSED_REAL; CLOSED_CBALL]) THEN
      REWRITE_TAC[EXTENSION; IMAGE_CX; IN_ELIM_THM; IN_CBALL; IN_INTER] THEN
      REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG; IN] THEN
      MESON_TAC[REAL_NORM];
      MATCH_MP_TAC(SET_RULE
       `(!x y. f x = f y ==> x = y) /\ ~(x IN s)
        ==> ~(f x IN t INTER IMAGE f s)`) THEN
      ASM_REWRITE_TAC[CX_INJ]]]);;

let REAL_CONTINUOUS_ON_ASN = prove
 (`!s. (!x. x IN s ==> abs(x) <= &1) ==> asn real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN
  EXISTS_TAC `{x | abs(x) <= &1}` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; REAL_CONTINUOUS_WITHIN_ASN_STRONG]);;

let REAL_CONTINUOUS_WITHIN_ACS_STRONG = prove
 (`!x. acs real_continuous (atreal x within {t | abs(t) <= &1})`,
  GEN_TAC THEN REWRITE_TAC[REAL_COMPLEX_CONTINUOUS_WITHINREAL] THEN
  ASM_CASES_TAC `x IN {t | abs(t) <= &1}` THENL
   [MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`cacs`; `&1`] THEN
    REWRITE_TAC[IMAGE_CX; IN_ELIM_THM; CONTINUOUS_WITHIN_CACS_REAL; REAL_LT_01;
     SET_RULE `real INTER {z | real z /\ P z} = {z | real z /\ P z}`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[REAL_CX; RE_CX; IMP_CONJ; FORALL_REAL; o_THM] THEN
    SIMP_TAC[CX_ACS];
    MATCH_MP_TAC CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL THEN CONJ_TAC THENL
     [SUBGOAL_THEN `real INTER IMAGE Cx {t | abs t <= &1} =
                    real INTER cball(Cx(&0),&1)`
       (fun th -> SIMP_TAC[th; CLOSED_INTER; CLOSED_REAL; CLOSED_CBALL]) THEN
      REWRITE_TAC[EXTENSION; IMAGE_CX; IN_ELIM_THM; IN_CBALL; IN_INTER] THEN
      REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG; IN] THEN
      MESON_TAC[REAL_NORM];
      MATCH_MP_TAC(SET_RULE
       `(!x y. f x = f y ==> x = y) /\ ~(x IN s)
        ==> ~(f x IN t INTER IMAGE f s)`) THEN
      ASM_REWRITE_TAC[CX_INJ]]]);;

let REAL_CONTINUOUS_ON_ACS = prove
 (`!s. (!x. x IN s ==> abs(x) <= &1) ==> acs real_continuous_on s`,
  REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN
  EXISTS_TAC `{x | abs(x) <= &1}` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; REAL_CONTINUOUS_WITHIN_ACS_STRONG]);;

(* ------------------------------------------------------------------------- *)
(* Differentiation conversion.                                               *)
(* ------------------------------------------------------------------------- *)

let real_differentiation_theorems = ref [];;

let add_real_differentiation_theorems =
  let ETA_THM = prove
   (`(f has_real_derivative f') net <=>
     ((\x. f x) has_real_derivative f') net`,
    REWRITE_TAC[ETA_AX]) in
  let ETA_TWEAK =
    PURE_REWRITE_RULE [IMP_CONJ] o
    GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV) [ETA_THM] o
    SPEC_ALL in
  fun l -> real_differentiation_theorems :=
              !real_differentiation_theorems @ map ETA_TWEAK l;;

add_real_differentiation_theorems
 ([HAS_REAL_DERIVATIVE_LMUL_WITHIN; HAS_REAL_DERIVATIVE_LMUL_ATREAL;
   HAS_REAL_DERIVATIVE_RMUL_WITHIN; HAS_REAL_DERIVATIVE_RMUL_ATREAL;
   HAS_REAL_DERIVATIVE_CDIV_WITHIN; HAS_REAL_DERIVATIVE_CDIV_ATREAL;
   HAS_REAL_DERIVATIVE_ID;
   HAS_REAL_DERIVATIVE_CONST;
   HAS_REAL_DERIVATIVE_NEG;
   HAS_REAL_DERIVATIVE_ADD;
   HAS_REAL_DERIVATIVE_SUB;
   HAS_REAL_DERIVATIVE_MUL_WITHIN; HAS_REAL_DERIVATIVE_MUL_ATREAL;
   HAS_REAL_DERIVATIVE_DIV_WITHIN; HAS_REAL_DERIVATIVE_DIV_ATREAL;
   HAS_REAL_DERIVATIVE_POW_WITHIN; HAS_REAL_DERIVATIVE_POW_ATREAL;
   HAS_REAL_DERIVATIVE_INV_WITHIN; HAS_REAL_DERIVATIVE_INV_ATREAL] @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN_UNIV
              HAS_REAL_DERIVATIVE_EXP))) @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN_UNIV
              HAS_REAL_DERIVATIVE_SIN))) @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN_UNIV
              HAS_REAL_DERIVATIVE_COS))) @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN
              HAS_REAL_DERIVATIVE_TAN))) @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN
              HAS_REAL_DERIVATIVE_LOG))) @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN
              HAS_REAL_DERIVATIVE_SQRT))) @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN_UNIV
              HAS_REAL_DERIVATIVE_ATN))) @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN
              HAS_REAL_DERIVATIVE_ASN))) @
  (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
    (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN
              HAS_REAL_DERIVATIVE_ACS))));;

let rec REAL_DIFF_CONV =
  let partfn tm = let l,r = dest_comb tm in mk_pair(lhand l,r)
  and is_deriv = can (term_match [] `(f has_real_derivative f') net`) in
  let rec REAL_DIFF_CONV tm =
    try tryfind (fun th -> PART_MATCH partfn th (partfn tm))
                (!real_differentiation_theorems)
    with Failure _ ->
        let ith = tryfind (fun th ->
         PART_MATCH (partfn o repeat (snd o dest_imp)) th (partfn tm))
                    (!real_differentiation_theorems) in
        REAL_DIFF_ELIM ith
  and REAL_DIFF_ELIM th =
    let tm = concl th in
    if not(is_imp tm) then th else
    let t = lhand tm in
    if not(is_deriv t) then UNDISCH th
    else REAL_DIFF_ELIM (MATCH_MP th (REAL_DIFF_CONV t)) in
  REAL_DIFF_CONV;;

(* ------------------------------------------------------------------------- *)
(* Hence a tactic.                                                           *)
(* ------------------------------------------------------------------------- *)

let REAL_DIFF_TAC =
  let pth = MESON[]
   `(f has_real_derivative f') net
    ==> f' = g'
        ==> (f has_real_derivative g') net` in
  W(fun (asl,w) -> let th = MATCH_MP pth (REAL_DIFF_CONV w) in
       MATCH_MP_TAC(repeat (GEN_REWRITE_RULE I [IMP_IMP]) (DISCH_ALL th)));;

let REAL_DIFFERENTIABLE_TAC =
  let DISCH_FIRST th = DISCH (hd(hyp th)) th in
  GEN_REWRITE_TAC I [real_differentiable] THEN
  W(fun (asl,w) ->
        let th = REAL_DIFF_CONV(snd(dest_exists w)) in
        let f' = rand(rator(concl th)) in
        EXISTS_TAC f' THEN
        (if hyp th = [] then MATCH_ACCEPT_TAC th else
         let th' = repeat (GEN_REWRITE_RULE I [IMP_IMP] o DISCH_FIRST)
                          (DISCH_FIRST th) in
         MATCH_MP_TAC th'));;

(* ------------------------------------------------------------------------- *)
(* Intermediate Value Theorem.                                               *)
(* ------------------------------------------------------------------------- *)

let REAL_IVT_INCREASING = prove
 (`!f a b y.
        a <= b /\ f real_continuous_on real_interval[a,b] /\
        f a <= y /\ y <= f b
        ==> ?x. x IN real_interval [a,b] /\ f x = y`,
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `lift a`; `lift b`; `y:real`; `1`]
        IVT_INCREASING_COMPONENT_ON_1) THEN
  ASM_REWRITE_TAC[GSYM drop; o_THM; LIFT_DROP; DIMINDEX_1; LE_REFL] THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; EXISTS_IN_IMAGE; LIFT_DROP]);;

let REAL_IVT_DECREASING = prove
 (`!f a b y.
        a <= b /\ f real_continuous_on real_interval[a,b] /\
        f b <= y /\ y <= f a
        ==> ?x. x IN real_interval [a,b] /\ f x = y`,
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `lift a`; `lift b`; `y:real`; `1`]
        IVT_DECREASING_COMPONENT_ON_1) THEN
  ASM_REWRITE_TAC[GSYM drop; o_THM; LIFT_DROP; DIMINDEX_1; LE_REFL] THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; EXISTS_IN_IMAGE; LIFT_DROP]);;

let IS_REALINTERVAL_CONTINUOUS_IMAGE = prove
 (`!s. f real_continuous_on s /\ is_realinterval s
       ==> is_realinterval(IMAGE f s)`,
  GEN_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON; IS_REALINTERVAL_CONNECTED] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONNECTED_CONTINUOUS_IMAGE) THEN
  REWRITE_TAC[IMAGE_o; REWRITE_RULE[IMAGE_o] IMAGE_LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Rolle and Mean Value Theorem.                                             *)
(* ------------------------------------------------------------------------- *)

let REAL_ROLLE = prove
 (`!f f' a b.
        a < b /\ f a = f b /\
        f real_continuous_on real_interval[a,b] /\
        (!x. x IN real_interval(a,b)
             ==> (f has_real_derivative f'(x)) (atreal x))
        ==> ?x. x IN real_interval(a,b) /\ f'(x) = &0`,
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  REWRITE_TAC[GSYM IMAGE_o; IMAGE_LIFT_DROP; has_vector_derivative] THEN
  REWRITE_TAC[LIFT_DROP] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `\x:real^1 h:real^1. f'(drop x) % h`;
                 `lift a`; `lift b`] ROLLE) THEN
  ASM_REWRITE_TAC[o_THM; LIFT_DROP] THEN ANTS_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; FORALL_LIFT; LIFT_DROP; GSYM LIFT_CMUL] THEN
    REWRITE_TAC[REAL_MUL_AC];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^1` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o C AP_THM `lift(&1)`) THEN
    REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_NUM; LIFT_EQ; REAL_MUL_RID]]);;

let REAL_MVT = prove
 (`!f f' a b.
        a < b /\
        f real_continuous_on real_interval[a,b] /\
        (!x. x IN real_interval(a,b)
             ==> (f has_real_derivative f'(x)) (atreal x))
        ==> ?x. x IN real_interval(a,b) /\ f(b) - f(a) = f'(x) * (b - a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\x:real. f(x) - (f b - f a) / (b - a) * x`;
                `(\x. f'(x) - (f b - f a) / (b - a)):real->real`;
                 `a:real`; `b:real`]
               REAL_ROLLE) THEN
  ASM_SIMP_TAC[REAL_FIELD
   `a < b ==> (fx - fba / (b - a) = &0 <=> fba = fx * (b - a))`] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_LMUL;
               REAL_CONTINUOUS_ON_ID] THEN
  CONJ_TAC THENL [UNDISCH_TAC `a < b` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
  ASM_SIMP_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_LMUL_ATREAL; HAS_REAL_DERIVATIVE_ID]);;

let REAL_MVT_SIMPLE = prove
 (`!f f' a b.
        a < b /\
        (!x. x IN real_interval[a,b]
             ==> (f has_real_derivative f'(x))
                 (atreal x within real_interval[a,b]))
        ==> ?x. x IN real_interval(a,b) /\ f(b) - f(a) = f'(x) * (b - a)`,
  MP_TAC REAL_MVT THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    ASM_MESON_TAC[real_differentiable_on; real_differentiable];
    ASM_MESON_TAC[HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN; REAL_OPEN_REAL_INTERVAL;
                  REAL_INTERVAL_OPEN_SUBSET_CLOSED;
                  HAS_REAL_DERIVATIVE_WITHIN_SUBSET; SUBSET]]);;

let REAL_MVT_VERY_SIMPLE = prove
 (`!f f' a b.
        a <= b /\
        (!x. x IN real_interval[a,b]
             ==> (f has_real_derivative f'(x))
                 (atreal x within real_interval[a,b]))
        ==> ?x. x IN real_interval[a,b] /\ f(b) - f(a) = f'(x) * (b - a)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:real = a` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO] THEN
    REWRITE_TAC[REAL_INTERVAL_SING; IN_SING; EXISTS_REFL];
    ASM_REWRITE_TAC[REAL_LE_LT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_MVT_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC[REWRITE_RULE[SUBSET] REAL_INTERVAL_OPEN_SUBSET_CLOSED]]);;

let REAL_ROLLE_SIMPLE = prove
 (`!f f' a b.
        a < b /\ f a = f b /\
        (!x. x IN real_interval[a,b]
             ==> (f has_real_derivative f'(x))
                 (atreal x within real_interval[a,b]))
        ==> ?x. x IN real_interval(a,b) /\ f'(x) = &0`,
  MP_TAC REAL_MVT_SIMPLE THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN
  REWRITE_TAC[REAL_RING `a - a = b * (c - d) <=> b = &0 \/ c = d`] THEN
  ASM_MESON_TAC[REAL_LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Continuity and differentiability of inverse functions.                    *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_ON_INVERSE = prove
 (`!f g s. f real_continuous_on s /\ real_compact s /\
           (!x. x IN s ==> g (f x) = x)
           ==> g real_continuous_on (IMAGE f s)`,
  REWRITE_TAC[REAL_CONTINUOUS_ON; real_compact] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `lift o g o drop`; `IMAGE lift s`]
          CONTINUOUS_ON_INVERSE) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP] THEN
  REWRITE_TAC[IMAGE_o; REWRITE_RULE[IMAGE_o] IMAGE_LIFT_DROP]);;

let HAS_REAL_DERIVATIVE_INVERSE_BASIC = prove
 (`!f g f' t y.
        (f has_real_derivative f') (atreal (g y)) /\
        ~(f' = &0) /\
        g real_continuous atreal y /\
        real_open t /\
        y IN t /\
        (!z. z IN t ==> f (g z) = z)
        ==> (g has_real_derivative inv(f')) (atreal y)`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT; REAL_OPEN;
              REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_INVERSE_BASIC THEN
  MAP_EVERY EXISTS_TAC
   [`lift o f o drop`; `\x:real^1. f' % x`; `IMAGE lift t`] THEN
  ASM_REWRITE_TAC[o_THM; LIFT_DROP; LIFT_IN_IMAGE_LIFT] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; LIFT_DROP; LINEAR_COMPOSE_CMUL; LINEAR_ID] THEN
  REWRITE_TAC[FUN_EQ_THM; I_THM; o_THM; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID]);;

let HAS_REAL_DERIVATIVE_INVERSE_STRONG = prove
 (`!f g f' g' s x.
         real_open s /\
         x IN s /\
         f real_continuous_on s /\
         (!x. x IN s ==> g (f x) = x) /\
         (f has_real_derivative f') (atreal x) /\
         ~(f' = &0)
         ==> (g has_real_derivative inv(f')) (atreal (f x))`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT; REAL_OPEN;
              REAL_CONTINUOUS_ON] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `lift o f o drop` HAS_DERIVATIVE_INVERSE_STRONG) THEN
  REWRITE_TAC[FORALL_LIFT; o_THM; LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`\x:real^1. f' % x`; `IMAGE lift s`] THEN
  ASM_REWRITE_TAC[o_THM; LIFT_DROP; LIFT_IN_IMAGE_LIFT] THEN
  ASM_SIMP_TAC[FUN_EQ_THM; I_THM; o_THM; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID]);;

let HAS_REAL_DERIVATIVE_INVERSE_STRONG_X = prove
 (`!f g f' g' s y.
        real_open s /\ (g y) IN s /\ f real_continuous_on s /\
        (!x. x IN s ==> (g(f(x)) = x)) /\
        (f has_real_derivative f') (atreal (g y)) /\ ~(f' = &0) /\
        f(g y) = y
        ==> (g has_real_derivative inv(f')) (atreal y)`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT; REAL_OPEN;
              REAL_CONTINUOUS_ON] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `lift o f o drop` HAS_DERIVATIVE_INVERSE_STRONG_X) THEN
  REWRITE_TAC[FORALL_LIFT; o_THM; LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`\x:real^1. f' % x`; `IMAGE lift s`] THEN
  ASM_REWRITE_TAC[o_THM; LIFT_DROP; LIFT_IN_IMAGE_LIFT] THEN
  ASM_SIMP_TAC[FUN_EQ_THM; I_THM; o_THM; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Real differentiation of sequences and series.                             *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_SEQUENCE = prove
 (`!s f f' g'.
         is_realinterval s /\
         (!n x. x IN s
                ==> (f n has_real_derivative f' n x) (atreal x within s)) /\
         (!e. &0 < e
              ==> ?N. !n x. n >= N /\ x IN s ==> abs(f' n x - g' x) <= e) /\
         (?x l. x IN s /\ ((\n. f n x) ---> l) sequentially)
         ==> ?g. !x. x IN s
                     ==> ((\n. f n x) ---> g x) sequentially /\
                         (g has_real_derivative g' x) (atreal x within s)`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN; IS_REALINTERVAL_CONVEX;
              TENDSTO_REAL] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE lift s`;
                 `\n:num. lift o f n o drop`;
                 `\n:num x:real^1 h:real^1. f' n (drop x) % h`;
                 `\x:real^1 h:real^1. g' (drop x) % h`]
         HAS_DERIVATIVE_SEQUENCE) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP] THEN ANTS_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_EXISTS_AND_THM; RIGHT_FORALL_IMP_THM;
                EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[EXISTS_LIFT; o_THM; LIFT_DROP] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB; NORM_MUL] THEN
    ASM_MESON_TAC[REAL_LE_RMUL; NORM_POS_LE];
    REWRITE_TAC[o_DEF; LIFT_DROP] THEN
    DISCH_THEN(X_CHOOSE_TAC `g:real^1->real^1`) THEN
    EXISTS_TAC `drop o g o lift` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ETA_AX]) THEN
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX]]);;

let HAS_REAL_DERIVATIVE_SERIES = prove
 (`!s f f' g' k.
         is_realinterval s /\
         (!n x. x IN s
                ==> (f n has_real_derivative f' n x) (atreal x within s)) /\
         (!e. &0 < e
              ==> ?N. !n x. n >= N /\ x IN s
                            ==> abs(sum (k INTER (0..n)) (\i. f' i x) - g' x)
                                    <= e) /\
         (?x l. x IN s /\ ((\n. f n x) real_sums l) k)
         ==> ?g. !x. x IN s
                     ==> ((\n. f n x) real_sums g x) k /\
                         (g has_real_derivative g' x) (atreal x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_sums] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SEQUENCE THEN EXISTS_TAC
   `\n:num x:real. sum(k INTER (0..n)) (\n. f' n x):real` THEN
  ASM_SIMP_TAC[ETA_AX; FINITE_INTER_NUMSEG; HAS_REAL_DERIVATIVE_SUM]);;

let REAL_DIFFERENTIABLE_BOUND = prove
 (`!f f' s B.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative f'(x)) (atreal x within s) /\
                        abs(f' x) <= B)
        ==> !x y. x IN s /\ y IN s ==> abs(f x - f y) <= B * abs(x - y)`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN; IS_REALINTERVAL_CONVEX;
              o_DEF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`lift o f o drop`; `\x h:real^1. f' (drop x) % h`;
    `IMAGE lift s`; `B:real`]
        DIFFERENTIABLE_BOUND) THEN
  ASM_SIMP_TAC[o_DEF; FORALL_IN_IMAGE; LIFT_DROP] THEN ANTS_TAC THENL
   [X_GEN_TAC `v:real` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `\h:real^1. f' (v:real) % h` ONORM) THEN
    SIMP_TAC[LINEAR_COMPOSE_CMUL; LINEAR_ID] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_LE_RMUL; NORM_POS_LE];
    SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; LIFT_DROP] THEN
    ASM_SIMP_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM LIFT_SUB; NORM_LIFT]]);;

let REAL_TAYLOR_MVT_POS = prove
 (`!f a x n.
    a < x /\
    (!i t. t IN real_interval[a,x] /\ i <= n
           ==> ((f i) has_real_derivative f (i + 1) t)
               (atreal t within real_interval[a,x]))
    ==> ?t. t IN real_interval(a,x) /\
            f 0 x =
              sum (0..n) (\i. f i a * (x - a) pow i / &(FACT i)) +
              f (n + 1) t * (x - a) pow (n + 1) / &(FACT(n + 1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?B. sum (0..n) (\i. f i a * (x - a) pow i / &(FACT i)) +
        B * (x - a) pow (n + 1) = f 0 x`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[]
     `a + (y - a) / x * x:real = y ==> ?b. a + b * x = y`) THEN
    MATCH_MP_TAC(REAL_FIELD `~(x = &0) ==> a + (y - a) / x * x = y`) THEN
    ASM_REWRITE_TAC[REAL_POW_EQ_0; REAL_SUB_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`\t. sum(0..n) (\i. f i t * (x - t) pow i / &(FACT i)) +
                     B * (x - t) pow (n + 1)`;
                `\t. (f (n + 1) t * (x - t) pow n / &(FACT n)) -
                     B * &(n + 1) * (x - t) pow n`;
                `a:real`; `x:real`]
        REAL_ROLLE_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN
      REWRITE_TAC[GSYM ADD1; real_pow; REAL_SUB_REFL; REAL_POW_ZERO;
                  REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[NOT_SUC; REAL_MUL_RZERO; REAL_DIV_1; REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_ARITH `x = (x + y) + &0 <=> y = &0`] THEN
      MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
      SIMP_TAC[ARITH; ARITH_RULE `1 <= i ==> ~(i = 0)`] THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO];
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[real_sub] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [ALL_TAC;
      REAL_DIFF_TAC THEN REWRITE_TAC[ADD_SUB] THEN CONV_TAC REAL_RING] THEN
    REWRITE_TAC[GSYM real_sub] THEN
    MATCH_MP_TAC(MESON[]
     `!g'. f' = g' /\ (f has_real_derivative g') net
           ==> (f has_real_derivative f') net`) THEN
    EXISTS_TAC
     `sum (0..n) (\i. f i t * --(&i * (x - t) pow (i - 1)) / &(FACT i) +
                                f (i + 1) t * (x - t) pow i / &(FACT i))` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_WITHIN THEN
      ASM_SIMP_TAC[ETA_AX] THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC] THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ARITH; FACT; REAL_DIV_1;
             real_pow; REAL_MUL_LZERO; REAL_NEG_0; REAL_MUL_RZERO;
             REAL_MUL_RID; REAL_ADD_LID] THEN
    ASM_CASES_TAC `n = 0` THENL
     [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; FACT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[SPECL [`f:num->real`; `1`] SUM_OFFSET_0; LE_1] THEN
    REWRITE_TAC[ADD_SUB] THEN
    REWRITE_TAC[GSYM ADD1; FACT; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD;
                GSYM REAL_OF_NUM_SUC] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_ARITH `--(n * x) * (inv n * inv y):real =
                            --(n / n) * x / y`] THEN
    REWRITE_TAC[REAL_FIELD `--((&n + &1) / (&n + &1)) * x = --x`] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL; REAL_OF_NUM_MUL; REAL_OF_NUM_SUC] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 FACT)] THEN
    REWRITE_TAC[REAL_ARITH `a * --b + c:real = c - a * b`] THEN
    REWRITE_TAC[ADD1; GSYM real_div; SUM_DIFFS_ALT; LE_0] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - 1 + 1 = n`; FACT] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
  REWRITE_TAC[REAL_EQ_ADD_LCANCEL] THEN
  REWRITE_TAC[REAL_ARITH `a * b / c:real = a / c * b`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
   `a * x / f - B * k * x = &0 ==> (B * k - a / f) * x = &0`)) THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_SUB_0] THEN
  ASM_CASES_TAC `x:real = t` THENL
   [ASM_MESON_TAC[IN_REAL_INTERVAL; REAL_LT_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM ADD1; FACT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD; ADD1] THEN
  SUBGOAL_THEN `~(&(FACT n) = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ; FACT_NZ]; CONV_TAC REAL_FIELD]);;

let REAL_TAYLOR_MVT_NEG = prove
 (`!f a x n.
    x < a /\
    (!i t. t IN real_interval[x,a] /\ i <= n
           ==> ((f i) has_real_derivative f (i + 1) t)
               (atreal t within real_interval[x,a]))
    ==> ?t. t IN real_interval(x,a) /\
            f 0 x =
              sum (0..n) (\i. f i a * (x - a) pow i / &(FACT i)) +
              f (n + 1) t * (x - a) pow (n + 1) / &(FACT(n + 1))`,
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[MESON[REAL_NEG_NEG] `(?x:real. P x) <=> (?x. P(--x))`] THEN
  MP_TAC(SPECL [`\n x. (-- &1) pow n * (f:num->real->real) n (--x)`;
                `--a:real`; `  --x:real`; `n:num`]
        REAL_TAYLOR_MVT_POS) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(x * y) * z / w:real = y * (x * z) / w`] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN
  REWRITE_TAC[REAL_ARITH `-- &1 * (--x - --a) = x - a`] THEN
  REWRITE_TAC[IN_REAL_INTERVAL; real_pow; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_ARITH `--a < t /\ t < --x <=> x < --t /\ --t < a`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LT_NEG2] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `t:real`] THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_POW_ADD; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN
  ONCE_REWRITE_TAC[REAL_ARITH `y pow 1 * x:real = x * y`] THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
    REAL_DIFF_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (--) (real_interval[--a,--x]) = real_interval[x,a]`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_REAL_INTERVAL] THEN
    REWRITE_TAC[REAL_ARITH `x:real = --y <=> --x = y`; UNWIND_THM1] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let REAL_TAYLOR = prove
 (`!f n s B.
    is_realinterval s /\
    (!i x. x IN s /\ i <= n
           ==> ((f i) has_real_derivative f (i + 1) x) (atreal x within s)) /\
    (!x. x IN s ==> abs(f (n + 1) x) <= B)
    ==> !w z. w IN s /\ z IN s
              ==> abs(f 0 z -
                      sum (0..n) (\i. f i w * (z - w) pow i / &(FACT i)))
                  <= B * abs(z - w) pow (n + 1) / &(FACT(n + 1))`,
  REPEAT STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `w = z \/ w < z \/ z < w`)
  THENL
   [ASM_SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; REAL_SUB_REFL; REAL_POW_ZERO;
                 REAL_ABS_0; ARITH; ADD_EQ_0; real_div] THEN
    REWRITE_TAC[REAL_MUL_LZERO; FACT; REAL_INV_1; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `y = &0 ==> abs(x - (x * &1 * &1 + y)) <= &0`) THEN
    MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    SIMP_TAC[ARITH; LE_1; REAL_MUL_RZERO; REAL_MUL_LZERO];
    MP_TAC(ISPECL [`f:num->real->real`; `w:real`; `z:real`; `n:num`]
                  REAL_TAYLOR_MVT_POS) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `real_interval[w,z] SUBSET s` ASSUME_TAC THENL
     [SIMP_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_MESON_TAC[is_realinterval];
      ALL_TAC];
    MP_TAC(ISPECL [`f:num->real->real`; `w:real`; `z:real`; `n:num`]
                  REAL_TAYLOR_MVT_NEG) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `real_interval[z,w] SUBSET s` ASSUME_TAC THENL
     [SIMP_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_MESON_TAC[is_realinterval];
      ALL_TAC]] THEN
 (ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `t:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `s:real->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[REAL_ADD_SUB; REAL_ABS_MUL; REAL_ABS_DIV] THEN
  REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_POW_LE; REAL_ABS_POS] THEN
  ASM_MESON_TAC[REAL_INTERVAL_OPEN_SUBSET_CLOSED; SUBSET]));;

(* ------------------------------------------------------------------------- *)
(* Comparing sums and "integrals" via real antiderivatives.                  *)
(* ------------------------------------------------------------------------- *)

let REAL_SUM_INTEGRAL_UBOUND_INCREASING = prove
 (`!f g m n.
      m <= n /\
      (!x. x IN real_interval[&m,&n + &1]
           ==> (g has_real_derivative f(x))
               (atreal x within real_interval[&m,&n + &1])) /\
      (!x y. &m <= x /\ x <= y /\ y <= &n + &1 ==> f x <= f y)
      ==> sum(m..n) (\k. f(&k)) <= g(&n + &1) - g(&m)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(m..n) (\k. g(&(k + 1)) - g(&k))` THEN CONJ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[SUM_DIFFS_ALT; REAL_OF_NUM_ADD; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real->real`; `f:real->real`; `&k`; `&(k + 1)`]
                REAL_MVT_SIMPLE) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `k < k + 1`] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ADD_SUB] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `real_interval[&m,&n + &1]` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_REAL_INTERVAL]);
      REWRITE_TAC[SUBSET] THEN GEN_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `t:real`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    REWRITE_TAC[REAL_MUL_RID] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_REAL_INTERVAL]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
    ASM_REAL_ARITH_TAC]);;

let REAL_SUM_INTEGRAL_UBOUND_DECREASING = prove
 (`!f g m n.
      m <= n /\
      (!x. x IN real_interval[&m - &1,&n]
           ==> (g has_real_derivative f(x))
               (atreal x within real_interval[&m - &1,&n])) /\
      (!x y. &m - &1 <= x /\ x <= y /\ y <= &n ==> f y <= f x)
      ==> sum(m..n) (\k. f(&k)) <= g(&n) - g(&m - &1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(m..n) (\k. g(&(k + 1) - &1) - g(&k - &1))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[SUM_DIFFS_ALT] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(x + &1) - &1 = x`] THEN
    REWRITE_TAC[REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real->real`; `f:real->real`; `&k - &1`; `&k`]
                REAL_MVT_SIMPLE) THEN
  ASM_REWRITE_TAC[REAL_ARITH `k - &1 < k`] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `real_interval[&m - &1,&n]` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_REAL_INTERVAL]);
      REWRITE_TAC[SUBSET] THEN GEN_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(a + &1) - &1 = a`] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    REWRITE_TAC[REAL_ARITH `a * (x - (x - &1)) = a`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_REAL_INTERVAL]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN
    ASM_REAL_ARITH_TAC]);;

let REAL_SUM_INTEGRAL_LBOUND_INCREASING = prove
 (`!f g m n.
      m <= n /\
      (!x. x IN real_interval[&m - &1,&n]
           ==> (g has_real_derivative f(x))
               (atreal x within real_interval[&m - &1,&n])) /\
      (!x y. &m - &1 <= x /\ x <= y /\ y <= &n ==> f x <= f y)
      ==> g(&n) - g(&m - &1) <= sum(m..n) (\k. f(&k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. --((f:real->real) z)`;
                 `\z. --((g:real->real) z)`;
                 `m:num`; `n:num`] REAL_SUM_INTEGRAL_UBOUND_DECREASING) THEN
  REWRITE_TAC[RE_NEG; RE_SUB; SUM_NEG; REAL_LE_NEG2;
              REAL_ARITH `--x - --y:real = --(x - y)`] THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_NEG]);;

let REAL_SUM_INTEGRAL_LBOUND_DECREASING = prove
 (`!f g m n.
      m <= n /\
      (!x. x IN real_interval[&m,&n + &1]
           ==> (g has_real_derivative f(x))
               (atreal x within  real_interval[&m,&n + &1])) /\
      (!x y. &m <= x /\ x <= y /\ y <= &n + &1 ==> f y <= f x)
      ==> g(&n + &1) - g(&m) <= sum(m..n) (\k. f(&k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. --((f:real->real) z)`;
                 `\z. --((g:real->real) z)`;
                 `m:num`; `n:num`] REAL_SUM_INTEGRAL_UBOUND_INCREASING) THEN
  REWRITE_TAC[RE_NEG; RE_SUB; SUM_NEG; REAL_LE_NEG2;
              REAL_ARITH `--x - --y:real = --(x - y)`] THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_NEG]);;

let REAL_SUM_INTEGRAL_BOUNDS_INCREASING = prove
 (`!f g m n.
         m <= n /\
         (!x. x IN real_interval[&m - &1,&n + &1]
              ==> (g has_real_derivative f x)
                  (atreal x within real_interval[&m - &1,&n + &1])) /\
         (!x y. &m - &1 <= x /\ x <= y /\ y <= &n + &1 ==> f x <= f y)
         ==> g(&n) - g(&m - &1) <= sum(m..n) (\k. f(&k)) /\
             sum (m..n) (\k. f(&k)) <= g(&n + &1) - g(&m)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_SUM_INTEGRAL_LBOUND_INCREASING;
    MATCH_MP_TAC REAL_SUM_INTEGRAL_UBOUND_INCREASING] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `real_interval[&m - &1,&n + &1]` THEN CONJ_TAC) THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
  TRY(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_REAL_INTERVAL])) THEN
  REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC);;

let REAL_SUM_INTEGRAL_BOUNDS_DECREASING = prove
 (`!f g m n.
      m <= n /\
      (!x. x IN real_interval[&m - &1,&n + &1]
           ==> (g has_real_derivative f(x))
               (atreal x within real_interval[&m - &1,&n + &1])) /\
      (!x y. &m - &1 <= x /\ x <= y /\ y <= &n + &1 ==> f y <= f x)
      ==> g(&n + &1) - g(&m) <= sum(m..n) (\k. f(&k)) /\
          sum(m..n) (\k. f(&k)) <= g(&n) - g(&m - &1)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_SUM_INTEGRAL_LBOUND_DECREASING;
    MATCH_MP_TAC REAL_SUM_INTEGRAL_UBOUND_DECREASING] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `real_interval[&m - &1,&n + &1]` THEN CONJ_TAC) THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
  TRY(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_REAL_INTERVAL])) THEN
  REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Relating different kinds of real limits.                                  *)
(* ------------------------------------------------------------------------- *)

let LIM_POSINFINITY_SEQUENTIALLY = prove
 (`!f l. (f --> l) at_posinfinity ==> ((\n. f(&n)) --> l) sequentially`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIM_AT_POSINFINITY; LIM_SEQUENTIALLY] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  MP_TAC(ISPEC `B:real` REAL_ARCH_SIMPLE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC);;

let REALLIM_POSINFINITY_SEQUENTIALLY = prove
 (`!f l. (f ---> l) at_posinfinity ==> ((\n. f(&n)) ---> l) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_POSINFINITY_SEQUENTIALLY) THEN
  REWRITE_TAC[o_DEF]);;

let LIM_ZERO_POSINFINITY = prove
 (`!f l. ((\x. f(&1 / x)) --> l) (atreal (&0)) ==> (f --> l) at_posinfinity`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_ATREAL; LIM_AT_POSINFINITY] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[dist; REAL_SUB_RZERO; real_ge] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&2 / d` THEN X_GEN_TAC `z:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv(z):real`) THEN
  REWRITE_TAC[real_div; REAL_MUL_LINV; REAL_INV_INV] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_ABS_INV; REAL_LT_INV_EQ] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `a <= z ==> &0 < a ==> &0 < abs z`));
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `&2 / d <= z ==> &0 < &2 / d ==> inv d < abs z`))] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH]);;

let LIM_ZERO_NEGINFINITY = prove
 (`!f l. ((\x. f(&1 / x)) --> l) (atreal (&0)) ==> (f --> l) at_neginfinity`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_ATREAL; LIM_AT_NEGINFINITY] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[dist; REAL_SUB_RZERO; real_ge] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `--(&2 / d)` THEN X_GEN_TAC `z:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv(z):real`) THEN
  REWRITE_TAC[real_div; REAL_MUL_LINV; REAL_INV_INV] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_ABS_INV; REAL_LT_INV_EQ] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `z <= --a ==> &0 < a ==> &0 < abs z`));
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `z <= --(&2 / d) ==> &0 < &2 / d ==> inv d < abs z`))] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH]);;

let REALLIM_ZERO_POSINFINITY = prove
 (`!f l. ((\x. f(&1 / x)) ---> l) (atreal (&0)) ==> (f ---> l) at_posinfinity`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF; LIM_ZERO_POSINFINITY]);;

let REALLIM_ZERO_NEGINFINITY = prove
 (`!f l. ((\x. f(&1 / x)) ---> l) (atreal (&0)) ==> (f ---> l) at_neginfinity`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF; LIM_ZERO_NEGINFINITY]);;

(* ------------------------------------------------------------------------- *)
(* Real segments (bidirectional intervals).                                  *)
(* ------------------------------------------------------------------------- *)

let closed_real_segment = define
 `closed_real_segment[a,b] = {(&1 - u) * a + u * b | &0 <= u /\ u <= &1}`;;

let open_real_segment = new_definition
 `open_real_segment(a,b) = closed_real_segment[a,b] DIFF {a,b}`;;

make_overloadable "real_segment" `:A`;;

overload_interface("real_segment",`open_real_segment`);;
overload_interface("real_segment",`closed_real_segment`);;

let real_segment = prove
 (`real_segment[a,b] = {(&1 - u) * a + u * b | &0 <= u /\ u <= &1} /\
   real_segment(a,b) = real_segment[a,b] DIFF {a,b}`,
  REWRITE_TAC[open_real_segment; closed_real_segment]);;

let REAL_SEGMENT_SEGMENT = prove
 (`(!a b. real_segment[a,b] = IMAGE drop (segment[lift a,lift b])) /\
   (!a b. real_segment(a,b) = IMAGE drop (segment(lift a,lift b)))`,
  REWRITE_TAC[segment; real_segment] THEN
  SIMP_TAC[IMAGE_DIFF_INJ; DROP_EQ; IMAGE_CLAUSES; LIFT_DROP] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; DROP_ADD; DROP_CMUL; LIFT_DROP]);;

let SEGMENT_REAL_SEGMENT = prove
 (`(!a b. segment[a,b] = IMAGE lift (real_segment[drop a,drop b])) /\
   (!a b. segment(a,b) = IMAGE lift (real_segment(drop a,drop b)))`,
  REWRITE_TAC[REAL_SEGMENT_SEGMENT; GSYM IMAGE_o] THEN
  REWRITE_TAC[o_DEF; IMAGE_ID; LIFT_DROP]);;

let REAL_SEGMENT_INTERVAL = prove
 (`(!a b. real_segment[a,b] =
          if a <= b then real_interval[a,b] else real_interval[b,a]) /\
   (!a b. real_segment(a,b) =
          if a <= b then real_interval(a,b) else real_interval(b,a))`,
  REWRITE_TAC[REAL_SEGMENT_SEGMENT; SEGMENT_1; LIFT_DROP] THEN
  REWRITE_TAC[REAL_INTERVAL_INTERVAL] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Convex real->real functions.                                              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("real_convex_on",(12,"right"));;

let real_convex_on = new_definition
  `(f:real->real) real_convex_on s <=>
        !x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
                  ==> f(u * x + v * y) <= u * f(x) + v * f(y)`;;

let REAL_CONVEX_ON = prove
 (`!f s. f real_convex_on s <=> (f o drop) convex_on (IMAGE lift s)`,
  REWRITE_TAC[real_convex_on; convex_on] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_THM; LIFT_DROP; DROP_ADD; DROP_CMUL]);;

let REAL_CONVEX_ON_SUBSET = prove
 (`!f s t. f real_convex_on t /\ s SUBSET t ==> f real_convex_on s`,
  REWRITE_TAC[REAL_CONVEX_ON] THEN
  MESON_TAC[CONVEX_ON_SUBSET; IMAGE_SUBSET]);;

let REAL_CONVEX_ADD = prove
 (`!s f g. f real_convex_on s /\ g real_convex_on s
           ==> (\x. f(x) + g(x)) real_convex_on s`,
  REWRITE_TAC[REAL_CONVEX_ON; o_DEF; CONVEX_ADD]);;

let REAL_CONVEX_LMUL = prove
 (`!s c f. &0 <= c /\ f real_convex_on s ==> (\x. c * f(x)) real_convex_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_CONVEX_ON; o_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONVEX_CMUL) THEN REWRITE_TAC[]);;

let REAL_CONVEX_RMUL = prove
 (`!s c f. &0 <= c /\ f real_convex_on s ==> (\x. f(x) * c) real_convex_on s`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_CONVEX_LMUL]);;

let REAL_CONVEX_LOWER = prove
 (`!f s x y. f real_convex_on s /\
             x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ u + v = &1
             ==> f(u * x + v * y) <= max (f(x)) (f(y))`,
  REWRITE_TAC[REAL_CONVEX_ON] THEN
  REWRITE_TAC[FORALL_DROP; GSYM IN_IMAGE_LIFT_DROP] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CONVEX_LOWER) THEN
  REWRITE_TAC[o_THM; DROP_ADD; DROP_CMUL]);;

let REAL_CONVEX_LOCAL_GLOBAL_MINIMUM = prove
 (`!f s t x.
       f real_convex_on s /\ x IN t /\ real_open t /\ t SUBSET s /\
       (!y. y IN t ==> f(x) <= f(y))
       ==> !y. y IN s ==> f(x) <= f(y)`,
  REWRITE_TAC[REAL_CONVEX_ON; REAL_OPEN] THEN
  REWRITE_TAC[FORALL_DROP; GSYM IN_IMAGE_LIFT_DROP] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(f:real->real) o drop`; `IMAGE lift s`;
                 `IMAGE lift t`; `x:real^1`] CONVEX_LOCAL_GLOBAL_MINIMUM) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; LIFT_DROP; o_THM; IMAGE_SUBSET]);;

let REAL_CONVEX_DISTANCE = prove
 (`!s a. (\x. abs(a - x)) real_convex_on s`,
  REWRITE_TAC[REAL_CONVEX_ON; o_DEF; FORALL_DROP; GSYM DROP_SUB] THEN
  REWRITE_TAC[drop; GSYM NORM_REAL; GSYM dist; CONVEX_DISTANCE]);;

let REAL_CONVEX_ON_JENSEN = prove
 (`!f s. is_realinterval s
         ==> (f real_convex_on s <=>
                !k u x.
                   (!i:num. 1 <= i /\ i <= k ==> &0 <= u(i) /\ x(i) IN s) /\
                   (sum (1..k) u = &1)
                   ==> f(sum (1..k) (\i. u(i) * x(i)))
                           <= sum (1..k) (\i. u(i) * f(x(i))))`,
  REWRITE_TAC[IS_REALINTERVAL_CONVEX; REAL_CONVEX_ON] THEN
  SIMP_TAC[CONVEX_ON_JENSEN] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[o_DEF; DROP_VSUM; FINITE_NUMSEG] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `u:num->real` THEN REWRITE_TAC[] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `x:num->real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift o (x:num->real)`) THEN
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP; IN_IMAGE_LIFT_DROP] THEN
    REWRITE_TAC[DROP_CMUL; LIFT_DROP];
    X_GEN_TAC `x:num->real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop o (x:num->real^1)`) THEN
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP; IN_IMAGE_LIFT_DROP] THEN
    ASM_REWRITE_TAC[DROP_CMUL; LIFT_DROP; GSYM IN_IMAGE_LIFT_DROP]]);;

let REAL_CONVEX_ON_CONTINUOUS = prove
 (`!f s. real_open s /\ f real_convex_on s ==> f real_continuous_on s`,
  REWRITE_TAC[REAL_CONVEX_ON; REAL_OPEN; REAL_CONTINUOUS_ON] THEN
  REWRITE_TAC[CONVEX_ON_CONTINUOUS]);;

let REAL_CONVEX_ON_LEFT_SECANT_MUL = prove
 (`!f s. f real_convex_on s <=>
          !a b x. a IN s /\ b IN s /\ x IN real_segment[a,b]
                  ==> (f x - f a) * abs(b - a) <= (f b - f a) * abs(x - a)`,
  REWRITE_TAC[REAL_CONVEX_ON; CONVEX_ON_LEFT_SECANT_MUL] THEN
  REWRITE_TAC[REAL_SEGMENT_SEGMENT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP]);;

let REAL_CONVEX_ON_RIGHT_SEQUENT_MUL = prove
 (`!f s. f real_convex_on s <=>
          !a b x. a IN s /\ b IN s /\ x IN real_segment[a,b]
                  ==> (f b - f a) * abs(b - x) <= (f b - f x) * abs(b - a)`,
  REWRITE_TAC[REAL_CONVEX_ON; CONVEX_ON_RIGHT_SECANT_MUL] THEN
  REWRITE_TAC[REAL_SEGMENT_SEGMENT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP]);;

let REAL_CONVEX_ON_LEFT_SECANT = prove
 (`!f s.
      f real_convex_on s <=>
        !a b x. a IN s /\ b IN s /\ x IN real_segment(a,b)
                ==> (f x - f a) / abs(x - a) <= (f b - f a) / abs(b - a)`,
  REWRITE_TAC[REAL_CONVEX_ON; CONVEX_ON_LEFT_SECANT] THEN
  REWRITE_TAC[REAL_SEGMENT_SEGMENT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP]);;

let REAL_CONVEX_ON_RIGHT_SEQUENT = prove
 (`!f s.
      f real_convex_on s <=>
        !a b x. a IN s /\ b IN s /\ x IN real_segment(a,b)
                ==> (f b - f a) / abs(b - a) <= (f b - f x) / abs(b - x)`,
  REWRITE_TAC[REAL_CONVEX_ON; CONVEX_ON_RIGHT_SECANT] THEN
  REWRITE_TAC[REAL_SEGMENT_SEGMENT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP]);;

let REAL_CONVEX_ON_DERIVATIVE_SECANT_IMP = prove
 (`!f f' s x y.
        f real_convex_on s /\ real_segment[x,y] SUBSET s /\
        (f has_real_derivative f') (atreal x within s)
        ==> f' * (y - x) <= f y - f x`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN;
              REAL_CONVEX_ON; REAL_SEGMENT_SEGMENT] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE_LIFT_DROP] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FORALL_DROP] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  REWRITE_TAC[GSYM IN_IMAGE_LIFT_DROP; GSYM SUBSET] THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[LIFT_DROP]
        `\x. lift(drop(f % x))`)] THEN
  REWRITE_TAC[GSYM o_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONVEX_ON_DERIVATIVE_SECANT_IMP) THEN
  REWRITE_TAC[o_THM; DROP_CMUL; DROP_SUB; LIFT_DROP]);;

let REAL_CONVEX_ON_SECANT_DERIVATIVE_IMP = prove
 (`!f f' s x y.
        f real_convex_on s /\ real_segment[x,y] SUBSET s /\
        (f has_real_derivative f') (atreal y within s)
        ==> f y - f x <= f' * (y - x)`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN;
              REAL_CONVEX_ON; REAL_SEGMENT_SEGMENT] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE_LIFT_DROP] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FORALL_DROP] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  REWRITE_TAC[GSYM IN_IMAGE_LIFT_DROP; GSYM SUBSET] THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[LIFT_DROP]
        `\x. lift(drop(f % x))`)] THEN
  REWRITE_TAC[GSYM o_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONVEX_ON_SECANT_DERIVATIVE_IMP) THEN
  REWRITE_TAC[o_THM; DROP_CMUL; DROP_SUB; LIFT_DROP]);;

let REAL_CONVEX_ON_DERIVATIVES_IMP = prove
 (`!f f'x f'y s x y.
        f real_convex_on s /\ real_segment[x,y] SUBSET s /\
        (f has_real_derivative f'x) (atreal x within s) /\
        (f has_real_derivative f'y) (atreal y within s)
        ==> f'x * (y - x) <= f'y * (y - x)`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN;
              REAL_CONVEX_ON; REAL_SEGMENT_SEGMENT] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE_LIFT_DROP] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FORALL_DROP] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  REWRITE_TAC[GSYM IN_IMAGE_LIFT_DROP; GSYM SUBSET] THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[LIFT_DROP]
        `\x. lift(drop(f % x))`)] THEN
  REWRITE_TAC[GSYM o_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONVEX_ON_DERIVATIVES_IMP) THEN
  REWRITE_TAC[o_THM; DROP_CMUL; DROP_SUB; LIFT_DROP]);;

let REAL_CONVEX_ON_DERIVATIVE_INCREASING_IMP = prove
 (`!f f'x f'y s x y.
        f real_convex_on s /\ real_interval[x,y] SUBSET s /\
        (f has_real_derivative f'x) (atreal x within s) /\
        (f has_real_derivative f'y) (atreal y within s) /\
        x < y
        ==> f'x <= f'y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `f'x:real`; `f'y:real`; `s:real->bool`;
                 `x:real`; `y:real`] REAL_CONVEX_ON_DERIVATIVES_IMP) THEN
  ASM_REWRITE_TAC[REAL_SEGMENT_INTERVAL] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_RMUL_EQ; REAL_SUB_LT]);;

let REAL_CONVEX_ON_DERIVATIVE_SECANT = prove
 (`!f f' s.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative f'(x)) (atreal x within s))
        ==> (f real_convex_on s <=>
             !x y. x IN s /\ y IN s ==> f'(x) * (y - x) <= f y - f x)`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN;
              REAL_CONVEX_ON; IS_REALINTERVAL_CONVEX] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FORALL_DROP; GSYM IN_IMAGE_LIFT_DROP; LIFT_DROP] THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[LIFT_DROP; o_DEF]
        `lift o (\x. drop(f % x))`)] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP CONVEX_ON_DERIVATIVE_SECANT) THEN
  REWRITE_TAC[DROP_CMUL; DROP_SUB; o_THM]);;

let REAL_CONVEX_ON_SECANT_DERIVATIVE = prove
 (`!f f' s.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative f'(x)) (atreal x within s))
        ==> (f real_convex_on s <=>
             !x y. x IN s /\ y IN s ==> f y - f x <= f'(y) * (y - x))`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN;
              REAL_CONVEX_ON; IS_REALINTERVAL_CONVEX] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FORALL_DROP; GSYM IN_IMAGE_LIFT_DROP; LIFT_DROP] THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[LIFT_DROP; o_DEF]
        `lift o (\x. drop(f % x))`)] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP CONVEX_ON_SECANT_DERIVATIVE) THEN
  REWRITE_TAC[DROP_CMUL; DROP_SUB; o_THM]);;

let REAL_CONVEX_ON_DERIVATIVES = prove
 (`!f f' s.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative f'(x)) (atreal x within s))
        ==> (f real_convex_on s <=>
             !x y. x IN s /\ y IN s ==> f'(x) * (y - x) <= f'(y) * (y - x))`,
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_WITHIN;
              REAL_CONVEX_ON; IS_REALINTERVAL_CONVEX] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FORALL_DROP; GSYM IN_IMAGE_LIFT_DROP; LIFT_DROP] THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[LIFT_DROP; o_DEF]
        `lift o (\x. drop(f % x))`)] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP CONVEX_ON_DERIVATIVES) THEN
  REWRITE_TAC[DROP_CMUL; DROP_SUB; o_THM]);;

let REAL_CONVEX_ON_DERIVATIVE_INCREASING = prove
 (`!f f' s x y.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative f'(x)) (atreal x within s))
        ==> (f real_convex_on s <=>
             !x y. x IN s /\ y IN s /\ x <= y ==> f'(x) <= f'(y))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_CONVEX_ON_DERIVATIVES) THEN
  EQ_TAC THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`]) THEN
    ASM_CASES_TAC `x:real = y` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_SUB_LT; REAL_LT_LE];
    DISJ_CASES_TAC(REAL_ARITH `x <= y \/ y <= x`) THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:real`; `x:real`])] THEN
    ASM_CASES_TAC `x:real = y` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_SUB_LT; REAL_LT_LE] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `a * (y - x) <= b * (y - x) <=> b * (x - y) <= a * (x - y)`] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_SUB_LT; REAL_LT_LE]]);;

let HAS_REAL_DERIVATIVE_INCREASING_IMP = prove
 (`!f f' s a b.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative f'(x)) (atreal x within s)) /\
        (!x. x IN s ==> &0 <= f'(x)) /\
        a IN s /\ b IN s /\ a <= b
        ==> f(a) <= f(b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `real_interval[a,b] SUBSET s` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [is_realinterval]) THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `a:real`; `b:real`]
    REAL_MVT_VERY_SIMPLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `s:real->bool` THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `z:real` MP_TAC) THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [GSYM REAL_SUB_LE] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC]]);;

let HAS_REAL_DERIVATIVE_INCREASING = prove
 (`!f f' s. is_realinterval s /\ ~(?a. s = {a}) /\
           (!x. x IN s ==> (f has_real_derivative f'(x)) (atreal x within s))
           ==> ((!x. x IN s ==> &0 <= f'(x)) <=>
                (!x y. x IN s /\ y IN s /\ x <= y ==> f(x) <= f(y)))`,
  REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[HAS_REAL_DERIVATIVE_INCREASING_IMP]; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `atreal x within s` REALLIM_GE) THEN
  EXISTS_TAC `\y:real. (f y - f x) / (y - x)` THEN
  ASM_SIMP_TAC[GSYM HAS_REAL_DERIVATIVE_WITHINREAL] THEN
  ASM_SIMP_TAC[TRIVIAL_LIMIT_WITHIN_REALINTERVAL] THEN
  REWRITE_TAC[EVENTUALLY_WITHINREAL] THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
  X_GEN_TAC `y:real` THEN
  REWRITE_TAC[REAL_ARITH `&0 < abs(y - x) <=> ~(y = x)`] THEN STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `~(y:real = x) ==> x < y \/ y < x`))
  THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN
    REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
    REWRITE_TAC[REAL_NEG_NEG; GSYM real_div]] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN
  ASM_SIMP_TAC[REAL_SUB_LE; REAL_LT_IMP_LE]);;

let REAL_CONVEX_ON_SECOND_DERIVATIVE = prove
 (`!f f'x f'y s x y.
        is_realinterval s /\ ~(?a. s = {a}) /\
        (!x. x IN s ==> (f has_real_derivative f'(x)) (atreal x within s)) /\
        (!x. x IN s ==> (f' has_real_derivative f''(x)) (atreal x within s))
        ==> (f real_convex_on s <=> !x. x IN s ==> &0 <= f''(x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `!x y. x IN s /\ y IN s /\ x <= y ==> (f':real->real)(x) <= f'(y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONVEX_ON_DERIVATIVE_INCREASING;
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_INCREASING] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Integrals of real->real functions; measures of real sets.                 *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_real_integral",(12,"right"));;
parse_as_infix("real_integrable_on",(12,"right"));;
parse_as_infix("absolutely_real_integrable_on",(12,"right"));;
parse_as_infix("has_real_measure",(12,"right"));;

let has_real_integral = new_definition
 `(f has_real_integral y) s <=>
        ((lift o f o drop) has_integral (lift y)) (IMAGE lift s)`;;

let real_integrable_on = new_definition
 `f real_integrable_on i <=> ?y. (f has_real_integral y) i`;;

let real_integral = new_definition
 `real_integral i f = @y. (f has_real_integral y) i`;;

let real_negligible = new_definition
 `real_negligible s <=> negligible (IMAGE lift s)`;;

let absolutely_real_integrable_on = new_definition
 `f absolutely_real_integrable_on s <=>
        f real_integrable_on s /\ (\x. abs(f x)) real_integrable_on s`;;

let has_real_measure = new_definition
 `s has_real_measure m <=> ((\x. &1) has_real_integral m) s`;;

let real_measurable = new_definition
 `real_measurable s <=> ?m. s has_real_measure m`;;

let real_measure = new_definition
 `real_measure s = @m. s has_real_measure m`;;

let HAS_REAL_INTEGRAL = prove
 (`(f has_real_integral y) (real_interval[a,b]) <=>
   ((lift o f o drop) has_integral (lift y)) (interval[lift a,lift b])`,
  REWRITE_TAC[has_real_integral; IMAGE_LIFT_REAL_INTERVAL]);;

let REAL_INTEGRABLE_INTEGRAL = prove
 (`!f i. f real_integrable_on i
         ==> (f has_real_integral (real_integral i f)) i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_integrable_on; real_integral] THEN
  CONV_TAC(RAND_CONV SELECT_CONV) THEN REWRITE_TAC[]);;

let HAS_REAL_INTEGRAL_INTEGRABLE = prove
 (`!f i s. (f has_real_integral i) s ==> f real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[]);;

let HAS_REAL_INTEGRAL_INTEGRAL = prove
 (`!f s. f real_integrable_on s <=>
         (f has_real_integral (real_integral s f)) s`,
  MESON_TAC[REAL_INTEGRABLE_INTEGRAL; HAS_REAL_INTEGRAL_INTEGRABLE]);;

let HAS_REAL_INTEGRAL_UNIQUE = prove
 (`!f i k1 k2.
        (f has_real_integral k1) i /\ (f has_real_integral k2) i ==> k1 = k2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_integral] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_UNIQUE) THEN
  REWRITE_TAC[LIFT_EQ]);;

let REAL_INTEGRAL_UNIQUE = prove
 (`!f y k.
      (f has_real_integral y) k ==> real_integral k f = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_integral] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[HAS_REAL_INTEGRAL_UNIQUE]);;

let REAL_INTEGRABLE_ON = prove
 (`f real_integrable_on s <=>
        (lift o f o drop) integrable_on (IMAGE lift s)`,
  REWRITE_TAC[real_integrable_on; has_real_integral; EXISTS_DROP;
              integrable_on; LIFT_DROP]);;

let ABSOLUTELY_REAL_INTEGRABLE_ON = prove
 (`f absolutely_real_integrable_on s <=>
        (lift o f o drop) absolutely_integrable_on (IMAGE lift s)`,
  REWRITE_TAC[absolutely_real_integrable_on; REAL_INTEGRABLE_ON;
              absolutely_integrable_on] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; NORM_LIFT]);;

let REAL_INTEGRAL = prove
 (`f real_integrable_on s
   ==> real_integral s f = drop(integral (IMAGE lift s) (lift o f o drop))`,
  REWRITE_TAC[REAL_INTEGRABLE_ON] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[has_real_integral; LIFT_DROP] THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

let HAS_REAL_INTEGRAL_IS_0 = prove
 (`!f s. (!x. x IN s ==> f(x) = &0) ==> (f has_real_integral &0) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_real_integral; LIFT_NUM] THEN
  MATCH_MP_TAC HAS_INTEGRAL_IS_0 THEN
  ASM_REWRITE_TAC[LIFT_EQ; FORALL_IN_IMAGE; o_THM; LIFT_DROP; GSYM LIFT_NUM]);;

let HAS_REAL_INTEGRAL_0 = prove
 (`!s. ((\x. &0) has_real_integral &0) s`,
  SIMP_TAC[HAS_REAL_INTEGRAL_IS_0]);;

let HAS_REAL_INTEGRAL_0_EQ = prove
 (`!i s. ((\x. &0) has_real_integral i) s <=> i = &0`,
  MESON_TAC[HAS_REAL_INTEGRAL_UNIQUE; HAS_REAL_INTEGRAL_0]);;

let HAS_REAL_INTEGRAL_LINEAR = prove
 (`!f:real->real y s h:real->real.
        (f has_real_integral y) s /\ linear(lift o h o drop)
        ==> ((h o f) has_real_integral h(y)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_integral] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_LINEAR) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;

let HAS_REAL_INTEGRAL_LMUL = prove
 (`!(f:real->real) k s c.
        (f has_real_integral k) s
        ==> ((\x. c * f(x)) has_real_integral (c * k)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_integral] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
  REWRITE_TAC[GSYM LIFT_CMUL; o_DEF]);;

let HAS_REAL_INTEGRAL_RMUL = prove
 (`!(f:real->real) k s c.
        (f has_real_integral k) s
        ==> ((\x. f(x) * c) has_real_integral (k * c)) s`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_LMUL]);;

let HAS_REAL_INTEGRAL_NEG = prove
 (`!f k s. (f has_real_integral k) s
           ==> ((\x. --(f x)) has_real_integral (--k)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_integral] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_NEG) THEN
  REWRITE_TAC[o_DEF; LIFT_NEG]);;

let HAS_REAL_INTEGRAL_ADD = prove
 (`!f:real->real g k l s.
        (f has_real_integral k) s /\ (g has_real_integral l) s
        ==> ((\x. f(x) + g(x)) has_real_integral (k + l)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_integral] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_ADD) THEN
  REWRITE_TAC[o_DEF; LIFT_ADD]);;

let HAS_REAL_INTEGRAL_SUB = prove
 (`!f:real->real g k l s.
        (f has_real_integral k) s /\ (g has_real_integral l) s
        ==> ((\x. f(x) - g(x)) has_real_integral (k - l)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_real_integral] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_SUB) THEN
  REWRITE_TAC[o_DEF; LIFT_SUB]);;

let REAL_INTEGRAL_0 = prove
 (`!s. real_integral s (\x. &0) = &0`,
  MESON_TAC[REAL_INTEGRAL_UNIQUE; HAS_REAL_INTEGRAL_0]);;

let REAL_INTEGRAL_ADD = prove
 (`!f:real->real g k l s.
        f real_integrable_on s /\ g real_integrable_on s
        ==> real_integral s (\x. f x + g x) =
            real_integral s f + real_integral s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let REAL_INTEGRAL_LMUL = prove
 (`!f:real->real c s.
        f real_integrable_on s
        ==> real_integral s (\x. c * f(x)) = c * real_integral s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let REAL_INTEGRAL_RMUL = prove
 (`!f:real->real c s.
        f real_integrable_on s
        ==> real_integral s (\x. f(x) * c) = real_integral s f * c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_RMUL THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let REAL_INTEGRAL_NEG = prove
 (`!f:real->real s.
        f real_integrable_on s
        ==> real_integral s (\x. --f(x)) = --real_integral s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_NEG THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let REAL_INTEGRAL_SUB = prove
 (`!f:real->real g k l s.
        f real_integrable_on s /\ g real_integrable_on s
        ==> real_integral s (\x. f x - g x) =
            real_integral s f - real_integral s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SUB THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let REAL_INTEGRABLE_0 = prove
 (`!s. (\x. &0) real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_0]);;

let REAL_INTEGRABLE_ADD = prove
 (`!f:real->real g k l s.
        f real_integrable_on s /\ g real_integrable_on s
        ==> (\x. f x + g x) real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_ADD]);;

let REAL_INTEGRABLE_LMUL = prove
 (`!f:real->real c s.
        f real_integrable_on s
        ==> (\x. c * f(x)) real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_LMUL]);;

let REAL_INTEGRABLE_RMUL = prove
 (`!f:real->real c s.
        f real_integrable_on s
        ==> (\x. f(x) * c) real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_RMUL]);;

let REAL_INTEGRABLE_NEG = prove
 (`!f:real->real s.
        f real_integrable_on s ==> (\x. --f(x)) real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_NEG]);;

let REAL_INTEGRABLE_SUB = prove
 (`!f:real->real g k l s.
        f real_integrable_on s /\ g real_integrable_on s
        ==> (\x. f x - g x) real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_SUB]);;

let REAL_INTEGRABLE_LINEAR = prove
 (`!f h s. f real_integrable_on s /\
           linear(lift o h o drop) ==> (h o f) real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_LINEAR]);;

let REAL_INTEGRAL_LINEAR = prove
 (`!f:real->real s h:real->real.
        f real_integrable_on s /\ linear(lift o h o drop)
        ==> real_integral s (h o f) = h(real_integral s f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_UNIQUE THEN
  MAP_EVERY EXISTS_TAC
   [`(h:real->real) o (f:real->real)`; `s:real->bool`] THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC HAS_REAL_INTEGRAL_LINEAR] THEN
  ASM_SIMP_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL; REAL_INTEGRABLE_LINEAR]);;

let HAS_REAL_INTEGRAL_SUM = prove
 (`!f:A->real->real s t.
        FINITE t /\
        (!a. a IN t ==> ((f a) has_real_integral (i a)) s)
        ==> ((\x. sum t (\a. f a x)) has_real_integral (sum t i)) s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; HAS_REAL_INTEGRAL_0; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN
  ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

let REAL_INTEGRAL_SUM = prove
 (`!f:A->real->real s t.
        FINITE t /\
        (!a. a IN t ==> (f a) real_integrable_on s)
        ==> real_integral s (\x. sum t (\a. f a x)) =
                sum t (\a. real_integral s (f a))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SUM THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let REAL_INTEGRABLE_SUM = prove
 (`!f:A->real->real s t.
        FINITE t /\
        (!a. a IN t ==> (f a) real_integrable_on s)
        ==>  (\x. sum t (\a. f a x)) real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_SUM]);;

let HAS_REAL_INTEGRAL_EQ = prove
 (`!f:real->real g k s.
        (!x. x IN s ==> (f(x) = g(x))) /\
        (f has_real_integral k) s
        ==> (g has_real_integral k) s`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_IS_0) MP_TAC) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN
   (MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_SUB) THEN
  SIMP_TAC[REAL_ARITH `x - (x - y:real) = y`; ETA_AX; REAL_SUB_RZERO]);;

let REAL_INTEGRABLE_EQ = prove
 (`!f:real->real g s.
        (!x. x IN s ==> (f(x) = g(x))) /\
        f real_integrable_on s
        ==> g real_integrable_on s`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_EQ]);;

let HAS_REAL_INTEGRAL_EQ_EQ = prove
 (`!f:real->real g k s.
        (!x. x IN s ==> (f(x) = g(x)))
        ==> ((f has_real_integral k) s <=> (g has_real_integral k) s)`,
  MESON_TAC[HAS_REAL_INTEGRAL_EQ]);;

let HAS_REAL_INTEGRAL_NULL = prove
 (`!f:real->real a b.
    b <= a ==> (f has_real_integral &0) (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[has_real_integral; REAL_INTERVAL_INTERVAL] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_DROP; LIFT_NUM] THEN
  REWRITE_TAC[SET_RULE `IMAGE (\x. x) s = s`] THEN
  MATCH_MP_TAC HAS_INTEGRAL_NULL THEN
  ASM_REWRITE_TAC[CONTENT_EQ_0_1; LIFT_DROP]);;

let HAS_REAL_INTEGRAL_NULL_EQ = prove
 (`!f a b i. b <= a
             ==> ((f has_real_integral i) (real_interval[a,b]) <=> i = &0)`,
  ASM_MESON_TAC[REAL_INTEGRAL_UNIQUE; HAS_REAL_INTEGRAL_NULL]);;

let REAL_INTEGRAL_NULL = prove
 (`!f a b. b <= a
           ==> real_integral(real_interval[a,b]) f = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_MESON_TAC[HAS_REAL_INTEGRAL_NULL]);;

let REAL_INTEGRABLE_ON_NULL = prove
 (`!f a b. b <= a
           ==> f real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_NULL]);;

let HAS_REAL_INTEGRAL_EMPTY = prove
 (`!f. (f has_real_integral &0) {}`,
  GEN_TAC THEN REWRITE_TAC[EMPTY_AS_REAL_INTERVAL] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_NULL THEN REWRITE_TAC[REAL_POS]);;

let HAS_REAL_INTEGRAL_EMPTY_EQ = prove
 (`!f i. (f has_real_integral i) {} <=> i = &0`,
  MESON_TAC[HAS_REAL_INTEGRAL_UNIQUE; HAS_REAL_INTEGRAL_EMPTY]);;

let REAL_INTEGRABLE_ON_EMPTY = prove
 (`!f. f real_integrable_on {}`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_EMPTY]);;

let REAL_INTEGRAL_EMPTY = prove
 (`!f. real_integral {} f = &0`,
  MESON_TAC[EMPTY_AS_REAL_INTERVAL; REAL_INTEGRAL_UNIQUE;
            HAS_REAL_INTEGRAL_EMPTY]);;

let HAS_REAL_INTEGRAL_REFL = prove
 (`!f a. (f has_real_integral &0) (real_interval[a,a])`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_NULL THEN
  REWRITE_TAC[REAL_LE_REFL]);;

let REAL_INTEGRABLE_ON_REFL = prove
 (`!f a. f real_integrable_on real_interval[a,a]`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_REFL]);;

let REAL_INTEGRAL_REFL = prove
 (`!f a. real_integral (real_interval[a,a]) f = &0`,
  MESON_TAC[REAL_INTEGRAL_UNIQUE; HAS_REAL_INTEGRAL_REFL]);;

let HAS_REAL_INTEGRAL_CONST = prove
 (`!a b c.
        a <= b
        ==> ((\x. c) has_real_integral (c * (b - a))) (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[has_real_integral; IMAGE_LIFT_REAL_INTERVAL] THEN
  MP_TAC(ISPECL [`lift a`; `lift b`; `lift c`] HAS_INTEGRAL_CONST) THEN
  ASM_SIMP_TAC[o_DEF; CONTENT_1; LIFT_DROP; LIFT_CMUL]);;

let HAS_REAL_INTEGRAL_BOUND = prove
 (`!f:real->real a b i B.
        &0 <= B /\ a <= b /\
        (f has_real_integral i) (real_interval[a,b]) /\
        (!x. x IN real_interval[a,b] ==> abs(f x) <= B)
        ==> abs i <= B * (b - a)`,
  REWRITE_TAC[HAS_REAL_INTEGRAL; REAL_INTERVAL_INTERVAL; GSYM NORM_LIFT] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o BINOP_CONV) [GSYM LIFT_DROP] THEN
  ASM_SIMP_TAC[GSYM CONTENT_1; LIFT_DROP] THEN
  MATCH_MP_TAC HAS_INTEGRAL_BOUND THEN
  EXISTS_TAC `lift o f o drop` THEN ASM_REWRITE_TAC[o_THM]);;

let HAS_REAL_INTEGRAL_LE = prove
 (`!f g s i j.
        (f has_real_integral i) s /\ (g has_real_integral j) s /\
        (!x. x IN s ==> f x <= g x)
        ==> i <= j`,
  REWRITE_TAC[has_real_integral] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [GSYM LIFT_DROP] THEN
  REWRITE_TAC[drop] THEN MATCH_MP_TAC
   (ISPECL [`lift o f o drop`; `lift o g o drop`; `IMAGE lift s`]
           HAS_INTEGRAL_COMPONENT_LE) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; DIMINDEX_1; LE_REFL; o_THM; LIFT_DROP;
                  GSYM drop]);;

let REAL_INTEGRAL_LE = prove
 (`!f:real->real g:real->real s.
        f real_integrable_on s /\ g real_integrable_on s /\
        (!x. x IN s ==> f x <= g x)
        ==> real_integral s f <= real_integral s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_LE THEN
  ASM_MESON_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let HAS_REAL_INTEGRAL_POS = prove
 (`!f:real->real s i.
        (f has_real_integral i) s /\
        (!x. x IN s ==> &0 <= f x)
        ==> &0 <= i`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(\x. &0):real->real`; `f:real->real`;
                 `s:real->bool`; `&0:real`;
                 `i:real`] HAS_REAL_INTEGRAL_LE) THEN
  ASM_SIMP_TAC[HAS_REAL_INTEGRAL_0]);;

let REAL_INTEGRAL_POS = prove
 (`!f:real->real s.
        f real_integrable_on s /\
        (!x. x IN s ==> &0 <= f x)
        ==> &0 <= real_integral s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_POS THEN
  ASM_MESON_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let HAS_REAL_INTEGRAL_ISNEG = prove
 (`!f:real->real s i.
        (f has_real_integral i) s /\
        (!x. x IN s ==> f x <= &0)
        ==> i <= &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `(\x. &0):real->real`;
                 `s:real->bool`; `i:real`; `&0:real`;
                ] HAS_REAL_INTEGRAL_LE) THEN
  ASM_SIMP_TAC[HAS_REAL_INTEGRAL_0]);;

let HAS_REAL_INTEGRAL_LBOUND = prove
 (`!f:real->real a b i.
        a <= b /\
        (f has_real_integral i) (real_interval[a,b]) /\
        (!x. x IN real_interval[a,b] ==> B <= f(x))
        ==> B * (b - a) <= i`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(\x. B):real->real`; `f:real->real`;
                 `real_interval[a,b]`;
                  `B * (b - a):real`;
                 `i:real`]
                HAS_REAL_INTEGRAL_LE) THEN
  ASM_SIMP_TAC[HAS_REAL_INTEGRAL_CONST]);;

let HAS_REAL_INTEGRAL_UBOUND = prove
 (`!f:real->real a b i.
        a <= b /\
        (f has_real_integral i) (real_interval[a,b]) /\
        (!x. x IN real_interval[a,b] ==> f(x) <= B)
        ==> i <= B * (b - a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `(\x. B):real->real`;
                 `real_interval[a,b]`; `i:real`;
                 `B * (b - a):real`]
                HAS_REAL_INTEGRAL_LE) THEN
  ASM_SIMP_TAC[HAS_REAL_INTEGRAL_CONST]);;

let REAL_INTEGRAL_LBOUND = prove
 (`!f:real->real a b.
        a <= b /\
        f real_integrable_on real_interval[a,b] /\
        (!x. x IN real_interval[a,b] ==> B <= f(x))
        ==> B * (b - a) <= real_integral(real_interval[a,b]) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_LBOUND THEN
  EXISTS_TAC `f:real->real` THEN
  ASM_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL]);;

let REAL_INTEGRAL_UBOUND = prove
 (`!f:real->real a b k.
        a <= b /\
        f real_integrable_on real_interval[a,b] /\
        (!x. x IN real_interval[a,b] ==> f(x) <= B)
        ==> real_integral(real_interval[a,b]) f <= B * (b - a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_UBOUND THEN
  EXISTS_TAC `f:real->real` THEN
  ASM_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL]);;

let REAL_INTEGRABLE_UNIFORM_LIMIT = prove
 (`!f a b. (!e. &0 < e
                ==> ?g. (!x. x IN real_interval[a,b] ==> abs(f x - g x) <= e) /\
                        g real_integrable_on real_interval[a,b] )
           ==> f real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[real_integrable_on; HAS_REAL_INTEGRAL; GSYM EXISTS_LIFT] THEN
  REWRITE_TAC[GSYM integrable_on] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_UNIFORM_LIMIT THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `lift o g o drop` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[o_THM; LIFT_DROP; GSYM LIFT_SUB; NORM_LIFT]);;

let HAS_REAL_INTEGRAL_NEGLIGIBLE = prove
 (`!f s t.
        real_negligible s /\ (!x. x IN (t DIFF s) ==> f x = &0)
        ==> (f has_real_integral (&0)) t`,
  REWRITE_TAC[has_real_integral; real_negligible; LIFT_NUM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_NEGLIGIBLE THEN
  EXISTS_TAC `IMAGE lift s` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[o_THM; IN_DIFF; IMP_CONJ; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[LIFT_IN_IMAGE_LIFT; LIFT_DROP] THEN ASM SET_TAC[LIFT_NUM]);;

let HAS_REAL_INTEGRAL_SPIKE = prove
 (`!f g s t y.
        real_negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x) /\
        (f has_real_integral y) t
        ==> (g has_real_integral y) t`,
  REWRITE_TAC[has_real_integral; real_negligible] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
  MAP_EVERY EXISTS_TAC [`lift o f o drop`; `IMAGE lift s`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[o_THM; IN_DIFF; IMP_CONJ; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[LIFT_IN_IMAGE_LIFT; LIFT_DROP] THEN ASM SET_TAC[LIFT_NUM]);;

let HAS_REAL_INTEGRAL_SPIKE_EQ = prove
 (`!f g s t y.
        real_negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> ((f has_real_integral y) t <=> (g has_real_integral y) t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE THENL
   [EXISTS_TAC `f:real->real`; EXISTS_TAC `g:real->real`] THEN
  EXISTS_TAC `s:real->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[REAL_ABS_SUB]);;

let REAL_INTEGRABLE_SPIKE = prove
 (`!f g s t y.
        real_negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> f real_integrable_on t ==> g real_integrable_on  t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[real_integrable_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MP_TAC(SPEC_ALL HAS_REAL_INTEGRAL_SPIKE) THEN ASM_REWRITE_TAC[]);;

let REAL_INTEGRAL_SPIKE = prove
 (`!f:real->real g s t y.
        real_negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> real_integral t f = real_integral t g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_integral] THEN
  AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE_EQ THEN
  ASM_MESON_TAC[]);;

let REAL_NEGLIGIBLE_SUBSET = prove
 (`!s:real->bool t:real->bool.
        real_negligible s /\ t SUBSET s ==> real_negligible t`,
  REWRITE_TAC[real_negligible] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `IMAGE lift s` THEN ASM_SIMP_TAC[IMAGE_SUBSET]);;

let REAL_NEGLIGIBLE_DIFF = prove
 (`!s t:real->bool. real_negligible s ==> real_negligible(s DIFF t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `s:real->bool` THEN ASM_REWRITE_TAC[SUBSET_DIFF]);;

let REAL_NEGLIGIBLE_INTER = prove
 (`!s t. real_negligible s \/ real_negligible t ==> real_negligible(s INTER t)`,
  MESON_TAC[REAL_NEGLIGIBLE_SUBSET; INTER_SUBSET]);;

let REAL_NEGLIGIBLE_UNION = prove
 (`!s t:real->bool.
       real_negligible s /\ real_negligible t ==> real_negligible (s UNION t)`,
  SIMP_TAC[NEGLIGIBLE_UNION; IMAGE_UNION; real_negligible]);;

let REAL_NEGLIGIBLE_UNION_EQ = prove
 (`!s t:real->bool.
        real_negligible (s UNION t) <=> real_negligible s /\ real_negligible t`,
  MESON_TAC[REAL_NEGLIGIBLE_UNION; SUBSET_UNION; REAL_NEGLIGIBLE_SUBSET]);;

let REAL_NEGLIGIBLE_SING = prove
 (`!a:real. real_negligible {a}`,
  REWRITE_TAC[real_negligible; NEGLIGIBLE_SING; IMAGE_CLAUSES]);;

let REAL_NEGLIGIBLE_INSERT = prove
 (`!a:real s. real_negligible(a INSERT s) <=> real_negligible s`,
  REWRITE_TAC[real_negligible; NEGLIGIBLE_INSERT; IMAGE_CLAUSES]);;

let REAL_NEGLIGIBLE_EMPTY = prove
 (`real_negligible {}`,
  REWRITE_TAC[real_negligible; NEGLIGIBLE_EMPTY; IMAGE_CLAUSES]);;

let REAL_NEGLIGIBLE_FINITE = prove
 (`!s. FINITE s ==> real_negligible s`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[REAL_NEGLIGIBLE_EMPTY; REAL_NEGLIGIBLE_INSERT]);;

let REAL_NEGLIGIBLE_UNIONS = prove
 (`!s. FINITE s /\ (!t. t IN s ==> real_negligible t)
       ==> real_negligible(UNIONS s)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; REAL_NEGLIGIBLE_EMPTY; IN_INSERT] THEN
  SIMP_TAC[REAL_NEGLIGIBLE_UNION]);;

let HAS_REAL_INTEGRAL_SPIKE_FINITE = prove
 (`!f:real->real g s t y.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x) /\
        (f has_real_integral y) t
        ==> (g has_real_integral y) t`,
  MESON_TAC[HAS_REAL_INTEGRAL_SPIKE; REAL_NEGLIGIBLE_FINITE]);;

let HAS_REAL_INTEGRAL_SPIKE_FINITE_EQ = prove
 (`!f:real->real g s a b y.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> ((f has_real_integral y) t <=> (g has_real_integral y) t)`,
  MESON_TAC[HAS_REAL_INTEGRAL_SPIKE_FINITE]);;

let REAL_INTEGRABLE_SPIKE_FINITE = prove
 (`!f:real->real g s a b y.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> f real_integrable_on t
            ==> g real_integrable_on  t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[real_integrable_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MP_TAC(SPEC_ALL HAS_REAL_INTEGRAL_SPIKE_FINITE) THEN ASM_REWRITE_TAC[]);;

let REAL_NEGLIGIBLE_FRONTIER_INTERVAL = prove
 (`!a b:real. real_negligible(real_interval[a,b] DIFF real_interval(a,b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_interval; DIFF; IN_ELIM_THM] THEN
  MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{(a:real),b}` THEN
  ASM_SIMP_TAC[REAL_NEGLIGIBLE_FINITE; FINITE_RULES] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  REAL_ARITH_TAC);;

let HAS_REAL_INTEGRAL_SPIKE_INTERIOR = prove
 (`!f:real->real g a b y.
        (!x. x IN real_interval(a,b) ==> g x = f x) /\
        (f has_real_integral y) (real_interval[a,b])
        ==> (g has_real_integral y) (real_interval[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
                           HAS_REAL_INTEGRAL_SPIKE) THEN
  EXISTS_TAC `real_interval[a:real,b] DIFF real_interval(a,b)` THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_FRONTIER_INTERVAL] THEN ASM SET_TAC[]);;

let HAS_REAL_INTEGRAL_SPIKE_INTERIOR_EQ = prove
 (`!f:real->real g a b y.
        (!x. x IN real_interval(a,b) ==> g x = f x)
        ==> ((f has_real_integral y) (real_interval[a,b]) <=>
             (g has_real_integral y) (real_interval[a,b]))`,
  MESON_TAC[HAS_REAL_INTEGRAL_SPIKE_INTERIOR]);;

let REAL_INTEGRABLE_SPIKE_INTERIOR = prove
 (`!f:real->real g a b y.
        (!x. x IN real_interval(a,b) ==> g x = f x)
        ==> f real_integrable_on (real_interval[a,b])
            ==> g real_integrable_on  (real_interval[a,b])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[real_integrable_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MP_TAC(SPEC_ALL HAS_REAL_INTEGRAL_SPIKE_INTERIOR) THEN ASM_REWRITE_TAC[]);;

let REAL_INTEGRABLE_CONTINUOUS = prove
 (`!f a b.
        f real_continuous_on real_interval[a,b]
        ==> f real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[REAL_CONTINUOUS_ON; real_integrable_on; has_real_integral;
              GSYM integrable_on; GSYM EXISTS_LIFT] THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; INTEGRABLE_CONTINUOUS]);;

let REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS = prove
 (`!f f' a b.
        a <= b /\
        (!x. x IN real_interval[a,b]
             ==> (f has_real_derivative f'(x))
                 (atreal x within real_interval[a,b]))
        ==> (f' has_real_integral (f(b) - f(a))) (real_interval[a,b])`,
  REWRITE_TAC[has_real_integral; HAS_REAL_VECTOR_DERIVATIVE_WITHIN] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; LIFT_SUB] THEN
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; FORALL_IN_IMAGE; LIFT_DROP] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o BINOP_CONV) [GSYM LIFT_DROP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;

let REAL_INTEGRABLE_SUBINTERVAL = prove
 (`!f:real->real a b c d.
        f real_integrable_on real_interval[a,b] /\
        real_interval[c,d] SUBSET real_interval[a,b]
        ==> f real_integrable_on real_interval[c,d]`,
  REWRITE_TAC[real_integrable_on; HAS_REAL_INTEGRAL] THEN
  REWRITE_TAC[EXISTS_DROP; GSYM integrable_on; LIFT_DROP] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
  MAP_EVERY EXISTS_TAC [`lift a`; `lift b`] THEN
  ASM_REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
  ASM_SIMP_TAC[IMAGE_SUBSET]);;

let HAS_REAL_INTEGRAL_COMBINE = prove
 (`!f i j a b c.
        a <= c /\ c <= b /\
        (f has_real_integral i) (real_interval[a,c]) /\
        (f has_real_integral j) (real_interval[c,b])
        ==> (f has_real_integral (i + j)) (real_interval[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_INTEGRAL; LIFT_ADD] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_COMBINE THEN
  EXISTS_TAC `lift c` THEN ASM_REWRITE_TAC[LIFT_DROP]);;

let REAL_INTEGRAL_COMBINE = prove
 (`!f i j a b c.
        a <= c /\ c <= b /\ f real_integrable_on (real_interval[a,b])
        ==> real_integral(real_interval[a,c]) f +
            real_integral(real_interval[c,b]) f =
            real_integral(real_interval[a,b]) f`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_COMBINE THEN
  EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
  MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL; REAL_LE_REFL]);;

let REAL_INTEGRABLE_COMBINE = prove
 (`!f a b c.
        a <= c /\ c <= b /\
        f real_integrable_on real_interval[a,c] /\
        f real_integrable_on real_interval[c,b]
        ==> f real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_COMBINE]);;

let REAL_INTEGRABLE_ON_LITTLE_SUBINTERVALS = prove
 (`!f:real->real a b.
        (!x. x IN real_interval[a,b]
             ==> ?d. &0 < d /\
                     !u v. x IN real_interval[u,v] /\
                           (!y. y IN real_interval[u,v]
                                ==> abs(y - x) < d /\ y IN real_interval[a,b])
                           ==> f real_integrable_on real_interval[u,v])
        ==> f real_integrable_on real_interval[a,b]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_integrable_on; HAS_REAL_INTEGRAL; EXISTS_DROP;
              GSYM integrable_on; LIFT_DROP] THEN
  DISCH_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_LITTLE_SUBINTERVALS THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM EXISTS_DROP; FORALL_LIFT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[IMAGE_LIFT_REAL_INTERVAL; LIFT_IN_IMAGE_LIFT];
    REWRITE_TAC[REAL_INTERVAL_INTERVAL; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `y:real^1` o REWRITE_RULE[SUBSET])) THEN
    ASM_SIMP_TAC[IN_BALL; FUN_IN_IMAGE; dist; NORM_REAL] THEN
    REWRITE_TAC[GSYM drop; DROP_SUB; LIFT_DROP] THEN SIMP_TAC[REAL_ABS_SUB]]);;

let REAL_INTEGRAL_HAS_REAL_DERIVATIVE = prove
 (`!f:real->real a b.
     (f real_continuous_on real_interval[a,b])
     ==> !x. x IN real_interval[a,b]
             ==> ((\u. real_integral(real_interval[a,u]) f)
                  has_real_derivative f(x))
                 (atreal x within real_interval[a,b])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRAL_HAS_VECTOR_DERIVATIVE) THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_WITHIN] THEN
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_DROP] THEN
  DISCH_TAC THEN X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
  ASM_REWRITE_TAC[SET_RULE `IMAGE (\x. x) s = s`] THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT
    `a /\ b /\ c /\ d ==> e <=> a /\ b /\ c ==> d ==> e`]
     HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN) THEN
  EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01] THEN
  X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN
  REWRITE_TAC[LIFT_DROP] THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[INTERVAL_REAL_INTERVAL; GSYM IMAGE_o; LIFT_DROP; o_DEF] THEN
  REWRITE_TAC[GSYM o_DEF; SET_RULE `IMAGE (\x. x) s = s`] THEN
  MATCH_MP_TAC REAL_INTEGRAL THEN
  MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
    REWRITE_TAC[LIFT_DROP] THEN REAL_ARITH_TAC]);;

let REAL_ANTIDERIVATIVE_CONTINUOUS = prove
 (`!f a b.
     (f real_continuous_on real_interval[a,b])
     ==> ?g. !x. x IN real_interval[a,b]
                 ==> (g has_real_derivative f(x))
                     (atreal x within real_interval[a,b])`,
  MESON_TAC[REAL_INTEGRAL_HAS_REAL_DERIVATIVE]);;

let REAL_ANTIDERIVATIVE_INTEGRAL_CONTINUOUS = prove
 (`!f a b.
     (f real_continuous_on real_interval[a,b])
     ==> ?g. !u v. u IN real_interval[a,b] /\
                   v IN real_interval[a,b] /\ u <= v
                   ==> (f has_real_integral (g(v) - g(u)))
                       (real_interval[u,v])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_ANTIDERIVATIVE_CONTINUOUS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real->real` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN
  STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `real_interval[a:real,b]` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

let HAS_REAL_INTEGRAL_AFFINITY = prove
 (`!f:real->real i a b m c.
        (f has_real_integral i) (real_interval[a,b]) /\ ~(m = &0)
        ==> ((\x. f(m * x + c)) has_real_integral (inv(abs(m)) * i))
            (IMAGE (\x. inv m * (x - c)) (real_interval[a,b]))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_INTEGRAL] THEN
  DISCH_THEN(MP_TAC o SPEC `lift c` o MATCH_MP HAS_INTEGRAL_AFFINITY) THEN
  REWRITE_TAC[DIMINDEX_1; REAL_POW_1; has_real_integral] THEN
  REWRITE_TAC[o_DEF; DROP_ADD; DROP_CMUL; LIFT_DROP; LIFT_CMUL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[INTERVAL_REAL_INTERVAL; GSYM IMAGE_o; LIFT_DROP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_DEF; LIFT_CMUL; LIFT_SUB] THEN VECTOR_ARITH_TAC);;

let REAL_INTEGRABLE_AFFINITY = prove
 (`!f a b m c.
        f real_integrable_on real_interval[a,b] /\ ~(m = &0)
        ==> (\x. f(m * x + c)) real_integrable_on
            (IMAGE (\x. inv m * (x - c)) (real_interval[a,b]))`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_AFFINITY]);;

let HAS_REAL_INTEGRAL_STRETCH = prove
 (`!f:real->real i a b m.
        (f has_real_integral i) (real_interval[a,b]) /\ ~(m = &0)
        ==> ((\x. f(m * x)) has_real_integral (inv(abs(m)) * i))
            (IMAGE (\x. inv m * x) (real_interval[a,b]))`,
  MP_TAC HAS_REAL_INTEGRAL_AFFINITY THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `&0`) THEN
  REWRITE_TAC[REAL_ADD_RID; REAL_SUB_RZERO]);;

let REAL_INTEGRABLE_STRETCH = prove
 (`!f a b m.
        f real_integrable_on real_interval[a,b] /\ ~(m = &0)
        ==> (\x. f(m * x)) real_integrable_on
            (IMAGE (\x. inv m * x) (real_interval[a,b]))`,
  REWRITE_TAC[real_integrable_on] THEN MESON_TAC[HAS_REAL_INTEGRAL_STRETCH]);;

let HAS_REAL_INTEGRAL_REFLECT_LEMMA = prove
 (`!f:real->real i a b.
     (f has_real_integral i) (real_interval[a,b])
     ==> ((\x. f(--x)) has_real_integral i) (real_interval[--b,--a])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_INTEGRAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_REFLECT_LEMMA) THEN
  REWRITE_TAC[LIFT_NEG; o_DEF; DROP_NEG]);;

let HAS_REAL_INTEGRAL_REFLECT = prove
 (`!f:real->real i a b.
     ((\x. f(--x)) has_real_integral i) (real_interval[--b,--a]) <=>
     (f has_real_integral i) (real_interval[a,b])`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_REFLECT_LEMMA) THEN
  REWRITE_TAC[REAL_NEG_NEG; ETA_AX]);;

let REAL_INTEGRABLE_REFLECT = prove
 (`!f:real->real a b.
     (\x. f(--x)) real_integrable_on (real_interval[--b,--a]) <=>
     f real_integrable_on (real_interval[a,b])`,
  REWRITE_TAC[real_integrable_on; HAS_REAL_INTEGRAL_REFLECT]);;

let REAL_INTEGRAL_REFLECT = prove
 (`!f:real->real a b.
     real_integral (real_interval[--b,--a]) (\x. f(--x)) =
     real_integral (real_interval[a,b]) f`,
  REWRITE_TAC[real_integral; HAS_REAL_INTEGRAL_REFLECT]);;

let REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR = prove
 (`!f:real->real f' a b.
        a <= b /\ f real_continuous_on real_interval[a,b] /\
        (!x. x IN real_interval(a,b)
             ==> (f has_real_derivative f'(x)) (atreal x))
        ==> (f' has_real_integral (f(b) - f(a))) (real_interval[a,b])`,
  REWRITE_TAC[has_real_integral; HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; LIFT_SUB] THEN
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; FORALL_IN_IMAGE; LIFT_DROP] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o BINOP_CONV) [GSYM LIFT_DROP] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; GSYM IMAGE_o; IMAGE_LIFT_DROP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;

let REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG = prove
 (`!f f' s a b.
        FINITE s /\
        a <= b /\ f real_continuous_on real_interval[a,b] /\
        (!x. x IN real_interval(a,b) DIFF s
             ==> (f has_real_derivative f'(x)) (atreal x))
        ==> (f' has_real_integral (f(b) - f(a))) (real_interval[a,b])`,
  REWRITE_TAC[has_real_integral; HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; LIFT_SUB] THEN
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; FORALL_IN_IMAGE; IMP_CONJ; IN_DIFF] THEN
  SUBGOAL_THEN `!x. drop x IN s <=> x IN IMAGE lift s`
    (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE s <=> FINITE(IMAGE lift s)` SUBST1_TAC THENL
   [EQ_TAC THEN SIMP_TAC[FINITE_IMAGE] THEN
    DISCH_THEN(MP_TAC o ISPEC `drop` o MATCH_MP FINITE_IMAGE) THEN
    REWRITE_TAC[GSYM IMAGE_o; IMAGE_LIFT_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP; GSYM IN_DIFF; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; GSYM IMAGE_o; IMAGE_LIFT_DROP] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o BINOP_CONV)
   [GSYM LIFT_DROP] THEN
  DISCH_THEN(MP_TAC o
    MATCH_MP FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;

let REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG = prove
 (`!f f' s a b.
        FINITE s /\
        a <= b /\ f real_continuous_on real_interval[a,b] /\
        (!x. x IN real_interval[a,b] DIFF s
             ==> (f has_real_derivative f'(x)) (atreal x))
        ==> (f' has_real_integral (f(b) - f(a))) (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG THEN
  EXISTS_TAC `s:real->bool` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
  SIMP_TAC[IN_REAL_INTERVAL; IN_DIFF] THEN REAL_ARITH_TAC);;

let REAL_INDEFINITE_INTEGRAL_CONTINUOUS = prove
 (`!f:real->real a b.
        f real_integrable_on real_interval[a,b]
        ==> (\x. real_integral (real_interval[a,x]) f)
            real_continuous_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_INTEGRABLE_ON]) THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INDEFINITE_INTEGRAL_CONTINUOUS) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_EQ) THEN
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[o_DEF] THEN
  GEN_REWRITE_TAC I [GSYM DROP_EQ] THEN
  REWRITE_TAC[INTERVAL_REAL_INTERVAL; LIFT_DROP; GSYM o_DEF] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL THEN
  MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
  REWRITE_TAC[LIFT_DROP] THEN REAL_ARITH_TAC);;

let HAS_REAL_DERIVATIVE_ZERO_UNIQUE_STRONG_INTERVAL = prove
 (`!f:real->real a b k y.
        FINITE k /\ f real_continuous_on real_interval[a,b] /\ f a = y /\
        (!x. x IN (real_interval[a,b] DIFF k)
             ==> (f has_real_derivative &0)
                 (atreal x within real_interval[a,b]))
        ==> !x. x IN real_interval[a,b] ==> f x = y`,
  REWRITE_TAC[has_real_integral; HAS_REAL_VECTOR_DERIVATIVE_WITHIN] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; LIFT_SUB] THEN
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; FORALL_IN_IMAGE; IMP_CONJ; IN_DIFF] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMP_IMP; GSYM IMAGE_o; IMAGE_LIFT_DROP] THEN
  REWRITE_TAC[GSYM IMP_CONJ; LIFT_DROP; has_vector_derivative] THEN
  REWRITE_TAC[LIFT_NUM; VECTOR_MUL_RZERO] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`lift o f o drop`; `lift a`; `lift b`; `IMAGE lift k`; `lift y`]
   HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_INTERVAL) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; o_THM; LIFT_DROP; LIFT_EQ; IN_DIFF] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[LIFT_DROP]);;

let HAS_REAL_DERIVATIVE_ZERO_UNIQUE_STRONG_CONVEX = prove
 (`!f:real->real s k c y.
      is_realinterval s /\ FINITE k /\ f real_continuous_on s /\
      c IN s /\ f c = y /\
      (!x. x IN (s DIFF k) ==> (f has_real_derivative &0) (atreal x within s))
      ==> !x. x IN s ==> f x = y`,
  REWRITE_TAC[has_real_integral; HAS_REAL_VECTOR_DERIVATIVE_WITHIN] THEN
  REWRITE_TAC[IS_REALINTERVAL_CONVEX; REAL_CONTINUOUS_ON] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; LIFT_SUB] THEN
  REWRITE_TAC[REAL_INTERVAL_INTERVAL; FORALL_IN_IMAGE; IMP_CONJ; IN_DIFF] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMP_IMP; GSYM IMAGE_o; IMAGE_LIFT_DROP] THEN
  REWRITE_TAC[GSYM IMP_CONJ; LIFT_DROP; has_vector_derivative] THEN
  REWRITE_TAC[LIFT_NUM; VECTOR_MUL_RZERO] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`lift o f o drop`; `IMAGE lift s`; `IMAGE lift k`; `lift c`; `lift y`]
   HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_CONVEX) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; o_THM; LIFT_DROP; LIFT_EQ; IN_DIFF] THEN
  ASM_REWRITE_TAC[LIFT_IN_IMAGE_LIFT; FORALL_IN_IMAGE; LIFT_DROP] THEN
  ASM_SIMP_TAC[IMP_CONJ; FORALL_IN_IMAGE; LIFT_IN_IMAGE_LIFT]);;

let HAS_REAL_INTEGRAL_RESTRICT = prove
 (`!f:real->real s t.
        s SUBSET t
        ==> (((\x. if x IN s then f x else &0) has_real_integral i) t <=>
             (f has_real_integral i) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_real_integral; o_DEF] THEN
  MP_TAC(ISPECL [`lift o f o drop`; `IMAGE lift s`; `IMAGE lift t`; `lift i`]
        HAS_INTEGRAL_RESTRICT) THEN
  ASM_SIMP_TAC[IMAGE_SUBSET; IN_IMAGE_LIFT_DROP; o_DEF] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[LIFT_NUM]);;

let HAS_REAL_INTEGRAL_RESTRICT_UNIV = prove
 (`!f:real->real s i.
        ((\x. if x IN s then f x else &0) has_real_integral i) (:real) <=>
         (f has_real_integral i) s`,
  SIMP_TAC[HAS_REAL_INTEGRAL_RESTRICT; SUBSET_UNIV]);;

let HAS_REAL_INTEGRAL_SPIKE_SET_EQ = prove
 (`!f s t y.
        real_negligible(s DIFF t UNION t DIFF s)
        ==> ((f has_real_integral y) s <=> (f has_real_integral y) t)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE_EQ THEN
  EXISTS_TAC `s DIFF t UNION t DIFF s:real->bool` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let HAS_REAL_INTEGRAL_SPIKE_SET = prove
 (`!f s t y.
        real_negligible(s DIFF t UNION t DIFF s) /\
        (f has_real_integral y) s
        ==> (f has_real_integral y) t`,
  MESON_TAC[HAS_REAL_INTEGRAL_SPIKE_SET_EQ]);;

let REAL_INTEGRABLE_SPIKE_SET = prove
 (`!f s t y.
        real_negligible(s DIFF t UNION t DIFF s)
        ==> f real_integrable_on s ==> f real_integrable_on t`,
  REWRITE_TAC[real_integrable_on] THEN
  MESON_TAC[HAS_REAL_INTEGRAL_SPIKE_SET_EQ]);;

let REAL_INTEGRABLE_SPIKE_SET_EQ = prove
 (`!f s t.
        real_negligible(s DIFF t UNION t DIFF s)
        ==> (f real_integrable_on s <=> f real_integrable_on t)`,
  MESON_TAC[REAL_INTEGRABLE_SPIKE_SET; UNION_COMM]);;

let REAL_INTEGRAL_SPIKE_SET = prove
 (`!f g s t.
        real_negligible(s DIFF t UNION t DIFF s)
        ==> real_integral s f = real_integral t f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_integral] THEN
  AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE_SET_EQ THEN
  ASM_MESON_TAC[]);;

let HAS_REAL_INTEGRAL_OPEN_INTERVAL = prove
 (`!f a b y. (f has_real_integral y) (real_interval(a,b)) <=>
             (f has_real_integral y) (real_interval[a,b])`,
  REWRITE_TAC[has_real_integral; IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[HAS_INTEGRAL_OPEN_INTERVAL]);;

let REAL_INTEGRABLE_ON_OPEN_INTERVAL = prove
 (`!f a b. f real_integrable_on real_interval(a,b) <=>
           f real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[real_integrable_on; HAS_REAL_INTEGRAL_OPEN_INTERVAL]);;

let REAL_INTEGRAL_OPEN_INTERVAL = prove
 (`!f a b. real_integral(real_interval(a,b)) f =
           real_integral(real_interval[a,b]) f`,
  REWRITE_TAC[real_integral; HAS_REAL_INTEGRAL_OPEN_INTERVAL]);;

let HAS_REAL_INTEGRAL_ON_SUPERSET = prove
 (`!f s t.
        (!x. ~(x IN s) ==> f x = &0) /\ s SUBSET t /\ (f has_real_integral i) s
        ==> (f has_real_integral i) t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ONCE_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC[]);;

let REAL_INTEGRABLE_ON_SUPERSET = prove
 (`!f s t.
        (!x. ~(x IN s) ==> f x = &0) /\ s SUBSET t /\ f real_integrable_on s
        ==> f real_integrable_on t`,
  REWRITE_TAC[real_integrable_on] THEN
  MESON_TAC[HAS_REAL_INTEGRAL_ON_SUPERSET]);;

let REAL_INTEGRAL_RESTRICT_UNIV = prove
 (`!f s. f real_integrable_on s
         ==> real_integral UNIV (\x. if x IN s then f x else &0) =
             real_integral s f`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  ASM_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL]);;

let REAL_INTEGRABLE_RESTRICT_UNIV = prove
 (`!f s. (\x. if x IN s then f x else &0) real_integrable_on (:real) <=>
         f real_integrable_on s`,
  REWRITE_TAC[real_integrable_on; HAS_REAL_INTEGRAL_RESTRICT_UNIV]);;

let REAL_NEGLIGIBLE_ON_INTERVALS = prove
 (`!s. real_negligible s <=>
         !a b:real. real_negligible(s INTER real_interval[a,b])`,
  GEN_TAC THEN REWRITE_TAC[real_negligible] THEN
  GEN_REWRITE_TAC LAND_CONV [NEGLIGIBLE_ON_INTERVALS] THEN
  REWRITE_TAC[FORALL_LIFT; GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN AP_TERM_TAC THEN SET_TAC[LIFT_DROP]);;

let HAS_REAL_INTEGRAL_SUBSET_LE = prove
 (`!f:real->real s t i j.
        s SUBSET t /\ (f has_real_integral i) s /\ (f has_real_integral j) t /\
        (!x. x IN t ==> &0 <= f x)
        ==> i <= j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_LE THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real. if x IN s then f(x) else &0`;
    `\x:real. if x IN t then f(x) else &0`; `(:real)`] THEN
  ASM_REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV; IN_UNIV] THEN
  X_GEN_TAC `x:real` THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL]) THEN
  ASM SET_TAC[]);;

let REAL_INTEGRAL_SUBSET_LE = prove
 (`!f:real->real s t.
        s SUBSET t /\ f real_integrable_on s /\ f real_integrable_on t /\
        (!x. x IN t ==> &0 <= f(x))
        ==> real_integral s f <= real_integral t f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_SUBSET_LE THEN
  ASM_MESON_TAC[REAL_INTEGRABLE_INTEGRAL]);;

let REAL_INTEGRABLE_ON_SUBINTERVAL = prove
 (`!f:real->real s a b.
        f real_integrable_on s /\ real_interval[a,b] SUBSET s
        ==> f real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
  EXISTS_TAC `IMAGE lift s` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
  ASM_SIMP_TAC[IMAGE_SUBSET]);;

let REAL_INTEGRABLE_STRADDLE = prove
 (`!f s.
        (!e. &0 < e
             ==> ?g h i j. (g has_real_integral i) s /\
                           (h has_real_integral j) s /\
                           abs(i - j) < e /\
                           !x. x IN s ==> g x <= f x /\ f x <= h x)
        ==> f real_integrable_on s`,
  REWRITE_TAC[REAL_INTEGRABLE_ON; has_real_integral] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_STRADDLE THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXISTS_DROP; FORALL_IN_IMAGE] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; GSYM DROP_SUB; LIFT_DROP; GSYM ABS_DROP] THEN
  MAP_EVERY X_GEN_TAC
   [`g:real->real`; `h:real->real`; `i:real^1`; `j:real^1`] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`lift o g o drop`; `lift o h o drop`; `i:real^1`; `j:real^1`] THEN
  ASM_REWRITE_TAC[o_THM; LIFT_DROP]);;

let HAS_REAL_INTEGRAL_UNION = prove
 (`!f i j s t.
        (f has_real_integral i) s /\ (f has_real_integral j) t /\
        real_negligible(s INTER t)
        ==> (f has_real_integral (i + j)) (s UNION t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_real_integral; real_negligible; LIFT_ADD; IMAGE_UNION] THEN
  DISCH_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_UNION THEN POP_ASSUM MP_TAC THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[LIFT_DROP]);;

let HAS_REAL_INTEGRAL_UNIONS = prove
 (`!f:real->real i t.
        FINITE t /\
        (!s. s IN t ==> (f has_real_integral (i s)) s) /\
        (!s s'. s IN t /\ s' IN t /\ ~(s = s') ==> real_negligible(s INTER s'))
        ==> (f has_real_integral (sum t i)) (UNIONS t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_real_integral; real_negligible; LIFT_ADD; IMAGE_UNIONS] THEN
  SIMP_TAC[LIFT_SUM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `\s. lift(i(IMAGE drop s))`;
                 `IMAGE (IMAGE lift) t`]
    HAS_INTEGRAL_UNIONS) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM;
               IMAGE_LIFT_DROP; GSYM IMAGE_o] THEN
  ASM_SIMP_TAC[LIFT_EQ; SET_RULE
   `(!x y. f x = f y <=> x = y)
    ==> (IMAGE f s = IMAGE f t <=> s = t) /\
        (IMAGE f s INTER IMAGE f t = IMAGE f (s INTER t))`] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [ASM SET_TAC[LIFT_DROP]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[o_DEF; GSYM IMAGE_o; IMAGE_LIFT_DROP]);;

let REAL_MONOTONE_CONVERGENCE_INCREASING = prove
 (`!f:num->real->real g s.
        (!k. (f k) real_integrable_on s) /\
        (!k x. x IN s ==> f k x <= f (SUC k) x) /\
        (!x. x IN s ==> ((\k. f k x) ---> g x) sequentially) /\
        (?B. !k. abs(real_integral s (f k)) <= B)
        ==> g real_integrable_on s /\
            ((\k. real_integral s (f k)) ---> real_integral s g) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_INTEGRABLE_ON; TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n x. lift(f (n:num) (drop x))`;
                 `lift o g o drop`;  `IMAGE lift s`]
                MONOTONE_CONVERGENCE_INCREASING) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP; o_DEF] THEN
  SUBGOAL_THEN
   `!k:num. real_integral s (f k) =
            drop(integral (IMAGE lift s) (lift o f k o drop))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[bounded] THEN EXISTS_TAC `B:real` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN
    ASM_REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; ABS_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN REWRITE_TAC[LIFT_DROP] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_INTEGRAL THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF]);;

let REAL_MONOTONE_CONVERGENCE_DECREASING = prove
 (`!f:num->real->real g s.
        (!k. (f k) real_integrable_on s) /\
        (!k x. x IN s ==> f (SUC k) x <= f k x) /\
        (!x. x IN s ==> ((\k. f k x) ---> g x) sequentially) /\
        (?B. !k. abs(real_integral s (f k)) <= B)
        ==> g real_integrable_on s /\
            ((\k. real_integral s (f k)) ---> real_integral s g) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_INTEGRABLE_ON; TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n x. lift(f (n:num) (drop x))`;
                 `lift o g o drop`;  `IMAGE lift s`]
                MONOTONE_CONVERGENCE_DECREASING) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP; o_DEF] THEN
  SUBGOAL_THEN
   `!k:num. real_integral s (f k) =
            drop(integral (IMAGE lift s) (lift o f k o drop))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[bounded] THEN EXISTS_TAC `B:real` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN
    ASM_REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; ABS_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN REWRITE_TAC[LIFT_DROP] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_INTEGRAL THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF]);;

let REAL_INTEGRAL_ABS_BOUND_INTEGRAL = prove
 (`!f:real->real g s.
        f real_integrable_on s /\ g real_integrable_on s /\
        (!x. x IN s ==> abs(f x) <= g x)
        ==> abs(real_integral s f) <= real_integral s g`,
  SIMP_TAC[REAL_INTEGRAL; GSYM ABS_DROP] THEN
  SIMP_TAC[REAL_INTEGRABLE_ON; INTEGRAL_NORM_BOUND_INTEGRAL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP; NORM_LIFT]);;

let ABSOLUTELY_REAL_INTEGRABLE_LE = prove
 (`!f:real->real s.
        f absolutely_real_integrable_on s
        ==> abs(real_integral s f) <= real_integral s (\x. abs(f x))`,
  SIMP_TAC[absolutely_real_integrable_on] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

let ABSOLUTELY_REAL_INTEGRABLE_0 = prove
 (`!s. (\x. &0) absolutely_real_integrable_on s`,
  REWRITE_TAC[absolutely_real_integrable_on; REAL_ABS_NUM;
              REAL_INTEGRABLE_0]);;

let ABSOLUTELY_REAL_INTEGRABLE_LMUL = prove
 (`!f s c. f absolutely_real_integrable_on s
           ==> (\x. c * f(x)) absolutely_real_integrable_on s`,
  SIMP_TAC[absolutely_real_integrable_on;
           REAL_INTEGRABLE_LMUL; REAL_ABS_MUL]);;

let ABSOLUTELY_REAL_INTEGRABLE_RMUL = prove
 (`!f s c. f absolutely_real_integrable_on s
           ==> (\x. f(x) * c) absolutely_real_integrable_on s`,
  SIMP_TAC[absolutely_real_integrable_on;
           REAL_INTEGRABLE_RMUL; REAL_ABS_MUL]);;

let ABSOLUTELY_REAL_INTEGRABLE_NEG = prove
 (`!f s. f absolutely_real_integrable_on s
         ==> (\x. --f(x)) absolutely_real_integrable_on s`,
  SIMP_TAC[absolutely_real_integrable_on; REAL_INTEGRABLE_NEG; REAL_ABS_NEG]);;

let ABSOLUTELY_REAL_INTEGRABLE_ABS = prove
 (`!f s. f absolutely_real_integrable_on s
         ==> (\x. abs(f x)) absolutely_real_integrable_on s`,
  SIMP_TAC[absolutely_real_integrable_on; REAL_ABS_ABS]);;

let ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL = prove
 (`!f:real->real s a b.
        f absolutely_real_integrable_on s /\ real_interval[a,b] SUBSET s
        ==> f absolutely_real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[absolutely_real_integrable_on] THEN
  MESON_TAC[REAL_INTEGRABLE_ON_SUBINTERVAL]);;

let ABSOLUTELY_REAL_INTEGRABLE_RESTRICT_UNIV = prove
 (`!f s. (\x. if x IN s then f x else &0)
              absolutely_real_integrable_on (:real) <=>
         f absolutely_real_integrable_on s`,
  REWRITE_TAC[absolutely_real_integrable_on; REAL_INTEGRABLE_RESTRICT_UNIV;
              COND_RAND; REAL_ABS_NUM]);;

let ABSOLUTELY_REAL_INTEGRABLE_ADD = prove
 (`!f:real->real g s.
        f absolutely_real_integrable_on s /\
        g absolutely_real_integrable_on s
        ==> (\x. f(x) + g(x)) absolutely_real_integrable_on s`,
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON] THEN
  SIMP_TAC[o_DEF; LIFT_ADD; ABSOLUTELY_INTEGRABLE_ADD]);;

let ABSOLUTELY_REAL_INTEGRABLE_SUB = prove
 (`!f:real->real g s.
        f absolutely_real_integrable_on s /\
        g absolutely_real_integrable_on s
        ==> (\x. f(x) - g(x)) absolutely_real_integrable_on s`,
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON] THEN
  SIMP_TAC[o_DEF; LIFT_SUB; ABSOLUTELY_INTEGRABLE_SUB]);;

let ABSOLUTELY_REAL_INTEGRABLE_LINEAR = prove
 (`!f h s.
        f absolutely_real_integrable_on s /\ linear(lift o h o drop)
        ==> (h o f) absolutely_real_integrable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_LINEAR) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;

let ABSOLUTELY_REAL_INTEGRABLE_SUM = prove
 (`!f:A->real->real s t.
        FINITE t /\
        (!a. a IN t ==> (f a) absolutely_real_integrable_on s)
        ==>  (\x. sum t (\a. f a x)) absolutely_real_integrable_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; ABSOLUTELY_REAL_INTEGRABLE_0; IN_INSERT;
           ABSOLUTELY_REAL_INTEGRABLE_ADD; ETA_AX]);;

let ABSOLUTELY_REAL_INTEGRABLE_MAX = prove
 (`!f:real->real g:real->real s.
        f absolutely_real_integrable_on s /\ g absolutely_real_integrable_on s
        ==> (\x. max (f x) (g x))
            absolutely_real_integrable_on s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `max a b = &1 / &2 * ((a + b) + abs(a - b))`] THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LMUL THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB; ABSOLUTELY_REAL_INTEGRABLE_ADD;
               ABSOLUTELY_REAL_INTEGRABLE_ABS]);;

let ABSOLUTELY_REAL_INTEGRABLE_MIN = prove
 (`!f:real->real g:real->real s.
        f absolutely_real_integrable_on s /\ g absolutely_real_integrable_on s
        ==> (\x. min (f x) (g x))
            absolutely_real_integrable_on s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `min a b = &1 / &2 * ((a + b) - abs(a - b))`] THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LMUL THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB; ABSOLUTELY_REAL_INTEGRABLE_ADD;
               ABSOLUTELY_REAL_INTEGRABLE_ABS]);;

let ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE = prove
 (`!f s. f absolutely_real_integrable_on s ==> f real_integrable_on s`,
  SIMP_TAC[absolutely_real_integrable_on]);;

let NONNEGATIVE_ABSOLUTELY_REAL_INTEGRABLE = prove
 (`!f s.
        (!x. x IN s ==> &0 <= f(x)) /\
        f real_integrable_on s
        ==> f absolutely_real_integrable_on s`,
  SIMP_TAC[absolutely_real_integrable_on] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_EQ THEN
  EXISTS_TAC `f:real->real` THEN ASM_SIMP_TAC[real_abs]);;

let ABSOLUTELY_REAL_INTEGRABLE_INTEGRABLE_BOUND = prove
 (`!f:real->real g s.
        (!x. x IN s ==> abs(f x) <= g x) /\
        f real_integrable_on s /\ g real_integrable_on s
        ==> f absolutely_real_integrable_on s`,
  REWRITE_TAC[REAL_INTEGRABLE_ON; ABSOLUTELY_REAL_INTEGRABLE_ON] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
  EXISTS_TAC `lift o g o drop` THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP; NORM_LIFT]);;

let ABSOLUTELY_REAL_INTEGRABLE_ABSOLUTELY_REAL_INTEGRABLE_BOUND = prove
 (`!f:real->real g:real->real s.
        (!x. x IN s ==> abs(f x) <= abs(g x)) /\
        f real_integrable_on s /\ g absolutely_real_integrable_on s
        ==> f absolutely_real_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_INTEGRABLE_BOUND THEN
  EXISTS_TAC `\x:real. abs(g x)` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[absolutely_real_integrable_on]) THEN
  ASM_REWRITE_TAC[]);;

let ABSOLUTELY_REAL_INTEGRABLE_INF = prove
 (`!fs s:real->bool k:A->bool.
        FINITE k /\ ~(k = {}) /\
        (!i. i IN k ==> (\x. fs x i) absolutely_real_integrable_on s)
        ==> (\x. inf (IMAGE (fs x) k)) absolutely_real_integrable_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[IMAGE_CLAUSES] THEN
  SIMP_TAC[INF_INSERT_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `k:A->bool`] THEN
  ASM_CASES_TAC `k:A->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[IN_SING; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MIN THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT]);;

let ABSOLUTELY_REAL_INTEGRABLE_SUP = prove
 (`!fs s:real->bool k:A->bool.
        FINITE k /\ ~(k = {}) /\
        (!i. i IN k ==> (\x. fs x i) absolutely_real_integrable_on s)
        ==> (\x. sup (IMAGE (fs x) k)) absolutely_real_integrable_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[IMAGE_CLAUSES] THEN
  SIMP_TAC[SUP_INSERT_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `k:A->bool`] THEN
  ASM_CASES_TAC `k:A->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[IN_SING; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MAX THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT]);;

let REAL_DOMINATED_CONVERGENCE = prove
 (`!f:num->real->real g h s.
        (!k. (f k) real_integrable_on s) /\ h real_integrable_on s /\
        (!k x. x IN s ==> abs(f k x) <= h x) /\
        (!x. x IN s ==> ((\k. f k x) ---> g x) sequentially)
        ==> g real_integrable_on s /\
            ((\k. real_integral s (f k)) ---> real_integral s g) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_INTEGRABLE_ON; TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n x. lift(f (n:num) (drop x))`;
                 `lift o g o drop`;  `lift o h o drop`; `IMAGE lift s`]
                DOMINATED_CONVERGENCE) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP; o_DEF; NORM_LIFT] THEN
  SUBGOAL_THEN
   `!k:num. real_integral s (f k) =
            drop(integral (IMAGE lift s) (lift o f k o drop))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN REWRITE_TAC[LIFT_DROP] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_INTEGRAL THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF]);;

let HAS_REAL_MEASURE_MEASURE = prove
 (`!s. real_measurable s <=> s has_real_measure (real_measure s)`,
  REWRITE_TAC[real_measure; real_measurable] THEN MESON_TAC[]);;

let HAS_REAL_MEASURE_UNIQUE = prove
 (`!s m1 m2. s has_real_measure m1 /\ s has_real_measure m2 ==> m1 = m2`,
  REWRITE_TAC[has_real_measure] THEN MESON_TAC[HAS_REAL_INTEGRAL_UNIQUE]);;

let REAL_MEASURE_UNIQUE = prove
 (`!s m. s has_real_measure m ==> real_measure s = m`,
  MESON_TAC[HAS_REAL_MEASURE_UNIQUE; HAS_REAL_MEASURE_MEASURE;
            real_measurable]);;

let HAS_REAL_MEASURE_REAL_MEASURABLE_REAL_MEASURE = prove
 (`!s m. s has_real_measure m <=> real_measurable s /\ real_measure s = m`,
  REWRITE_TAC[HAS_REAL_MEASURE_MEASURE] THEN MESON_TAC[REAL_MEASURE_UNIQUE]);;

let HAS_REAL_MEASURE_IMP_REAL_MEASURABLE = prove
 (`!s m. s has_real_measure m ==> real_measurable s`,
  REWRITE_TAC[real_measurable] THEN MESON_TAC[]);;

let HAS_REAL_MEASURE = prove
 (`!s m. s has_real_measure m <=>
              ((\x. if x IN s then &1 else &0) has_real_integral m) (:real)`,
  SIMP_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV; has_real_measure]);;

let REAL_MEASURABLE = prove
 (`!s. real_measurable s <=> (\x. &1) real_integrable_on s`,
  REWRITE_TAC[real_measurable; real_integrable_on;
              has_real_measure; EXISTS_DROP; LIFT_DROP]);;

let REAL_MEASURABLE_REAL_INTEGRABLE = prove
 (`real_measurable s <=>
    (\x. if x IN s then &1 else &0) real_integrable_on UNIV`,
  REWRITE_TAC[real_measurable; real_integrable_on; HAS_REAL_MEASURE]);;

let REAL_MEASURE_REAL_INTEGRAL = prove
 (`!s. real_measurable s ==> real_measure s = real_integral s (\x. &1)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_REWRITE_TAC[GSYM has_real_measure; GSYM HAS_REAL_MEASURE_MEASURE]);;

let REAL_MEASURE_REAL_INTEGRAL_UNIV = prove
 (`!s. real_measurable s
       ==> real_measure s =
           real_integral UNIV (\x. if x IN s then &1 else &0)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  ASM_REWRITE_TAC[GSYM HAS_REAL_MEASURE; GSYM HAS_REAL_MEASURE_MEASURE]);;

let REAL_INTEGRAL_REAL_MEASURE = prove
 (`!s. real_measurable s ==> real_integral s (\x. &1) = real_measure s`,
  SIMP_TAC[GSYM DROP_EQ; LIFT_DROP; REAL_MEASURE_REAL_INTEGRAL]);;

let REAL_INTEGRAL_REAL_MEASURE_UNIV = prove
 (`!s. real_measurable s
       ==> real_integral UNIV (\x. if x IN s then &1 else &0) =
           real_measure s`,
  SIMP_TAC[REAL_MEASURE_REAL_INTEGRAL_UNIV]);;

let HAS_REAL_MEASURE_HAS_MEASURE = prove
 (`!s m. s has_real_measure m <=> (IMAGE lift s) has_measure m`,
  REWRITE_TAC[has_real_measure; has_measure; has_real_integral] THEN
  REWRITE_TAC[o_DEF; LIFT_NUM]);;

let REAL_MEASURABLE_MEASURABLE = prove
 (`!s. real_measurable s <=> measurable(IMAGE lift s)`,
  REWRITE_TAC[real_measurable; measurable; HAS_REAL_MEASURE_HAS_MEASURE]);;

let REAL_MEASURE_MEASURE = prove
 (`!s. real_measurable s ==> real_measure s = measure(IMAGE lift s)`,
  REWRITE_TAC[real_measure; measure; HAS_REAL_MEASURE_HAS_MEASURE]);;

let HAS_REAL_MEASURE_REAL_INTERVAL = prove
 (`(!a b. real_interval[a,b] has_real_measure (max (b - a) (&0))) /\
   (!a b. real_interval(a,b) has_real_measure (max (b - a) (&0)))`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_INTERVAL;
              MEASURE_INTERVAL] THEN
  REWRITE_TAC[CONTENT_CLOSED_INTERVAL_CASES; DIMINDEX_1; FORALL_1] THEN
  REWRITE_TAC[PRODUCT_1; GSYM drop; LIFT_DROP] THEN REAL_ARITH_TAC);;

let REAL_MEASURABLE_REAL_INTERVAL = prove
 (`(!a b. real_measurable (real_interval[a,b])) /\
   (!a b. real_measurable (real_interval(a,b)))`,
  REWRITE_TAC[real_measurable] THEN
  MESON_TAC[HAS_REAL_MEASURE_REAL_INTERVAL]);;

let REAL_MEASURE_REAL_INTERVAL = prove
 (`(!a b. real_measure(real_interval[a,b]) = max (b - a) (&0)) /\
   (!a b. real_measure(real_interval(a,b)) = max (b - a) (&0))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  REWRITE_TAC[HAS_REAL_MEASURE_REAL_INTERVAL]);;

let REAL_MEASURABLE_INTER = prove
 (`!s t. real_measurable s /\ real_measurable t
         ==> real_measurable (s INTER t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_MEASURABLE_MEASURABLE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_INTER) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[LIFT_DROP]);;

let REAL_MEASURABLE_UNION = prove
 (`!s t. real_measurable s /\ real_measurable t
         ==> real_measurable (s UNION t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_MEASURABLE_MEASURABLE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_UNION) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[LIFT_DROP]);;

let HAS_REAL_MEASURE_DISJOINT_UNION = prove
 (`!s1 s2 m1 m2. s1 has_real_measure m1 /\ s2 has_real_measure m2 /\
                 DISJOINT s1 s2
                 ==> (s1 UNION s2) has_real_measure (m1 + m2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; IMAGE_UNION] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_MEASURE_DISJOINT_UNION THEN
  ASM SET_TAC[LIFT_DROP]);;

let REAL_MEASURE_DISJOINT_UNION = prove
 (`!s t. real_measurable s /\ real_measurable t /\ DISJOINT s t
         ==> real_measure(s UNION t) = real_measure s + real_measure t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_DISJOINT_UNION;
               GSYM HAS_REAL_MEASURE_MEASURE]);;

let HAS_REAL_MEASURE_POS_LE = prove
 (`!m s. s has_real_measure m ==> &0 <= m`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; HAS_MEASURE_POS_LE]);;

let REAL_MEASURE_POS_LE = prove
 (`!s. real_measurable s ==> &0 <= real_measure s`,
  REWRITE_TAC[HAS_REAL_MEASURE_MEASURE; HAS_REAL_MEASURE_POS_LE]);;

let HAS_REAL_MEASURE_SUBSET = prove
 (`!s1 s2 m1 m2.
        s1 has_real_measure m1 /\ s2 has_real_measure m2 /\ s1 SUBSET s2
        ==> m1 <= m2`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`IMAGE lift s1`; `IMAGE lift s2`]
    HAS_MEASURE_SUBSET) THEN
  ASM SET_TAC[HAS_MEASURE_SUBSET]);;

let REAL_MEASURE_SUBSET = prove
 (`!s t. real_measurable s /\ real_measurable t /\ s SUBSET t
         ==> real_measure s <= real_measure t`,
  REWRITE_TAC[HAS_REAL_MEASURE_MEASURE] THEN
  MESON_TAC[HAS_REAL_MEASURE_SUBSET]);;

let HAS_REAL_MEASURE_0 = prove
 (`!s. s has_real_measure &0 <=> real_negligible s`,
  REWRITE_TAC[real_negligible; HAS_REAL_MEASURE_HAS_MEASURE] THEN
  REWRITE_TAC[HAS_MEASURE_0]);;

let REAL_MEASURE_EQ_0 = prove
 (`!s. real_negligible s ==> real_measure s = &0`,
  MESON_TAC[REAL_MEASURE_UNIQUE; HAS_REAL_MEASURE_0]);;

let HAS_REAL_MEASURE_EMPTY = prove
 (`{} has_real_measure &0`,
  REWRITE_TAC[HAS_REAL_MEASURE_0; REAL_NEGLIGIBLE_EMPTY]);;

let REAL_MEASURE_EMPTY = prove
 (`real_measure {} = &0`,
  SIMP_TAC[REAL_MEASURE_EQ_0; REAL_NEGLIGIBLE_EMPTY]);;

let REAL_MEASURABLE_EMPTY = prove
 (`real_measurable {}`,
  REWRITE_TAC[real_measurable] THEN MESON_TAC[HAS_REAL_MEASURE_EMPTY]);;

let REAL_MEASURABLE_REAL_MEASURE_EQ_0 = prove
 (`!s. real_measurable s ==> (real_measure s = &0 <=> real_negligible s)`,
  REWRITE_TAC[HAS_REAL_MEASURE_MEASURE; GSYM HAS_REAL_MEASURE_0] THEN
  MESON_TAC[REAL_MEASURE_UNIQUE]);;

let REAL_MEASURABLE_REAL_MEASURE_POS_LT = prove
 (`!s. real_measurable s ==> (&0 < real_measure s <=> ~real_negligible s)`,
  SIMP_TAC[REAL_LT_LE; REAL_MEASURE_POS_LE;
           GSYM REAL_MEASURABLE_REAL_MEASURE_EQ_0] THEN
  REWRITE_TAC[EQ_SYM_EQ]);;

let REAL_NEGLIGIBLE_REAL_INTERVAL = prove
 (`(!a b. real_negligible(real_interval[a,b]) <=> real_interval(a,b) = {}) /\
   (!a b. real_negligible(real_interval(a,b)) <=> real_interval(a,b) = {})`,
  REWRITE_TAC[real_negligible; IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[NEGLIGIBLE_INTERVAL] THEN
  REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY; INTERVAL_EQ_EMPTY_1; LIFT_DROP]);;

let REAL_MEASURABLE_UNIONS = prove
 (`!m f. FINITE f /\ (!s. s IN f ==> real_measurable s)
         ==> real_measurable (UNIONS f)`,
  REWRITE_TAC[REAL_MEASURABLE_MEASURABLE; IMAGE_UNIONS] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_UNIONS THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE]);;

let HAS_REAL_MEASURE_DIFF_SUBSET = prove
 (`!s1 s2 m1 m2.
        s1 has_real_measure m1 /\ s2 has_real_measure m2 /\ s2 SUBSET s1
        ==> (s1 DIFF s2) has_real_measure (m1 - m2)`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[IMAGE_DIFF_INJ; LIFT_EQ] THEN
  MATCH_MP_TAC HAS_MEASURE_DIFF_SUBSET THEN
  ASM_SIMP_TAC[IMAGE_SUBSET]);;

let REAL_MEASURABLE_DIFF = prove
 (`!s t. real_measurable s /\ real_measurable t
         ==> real_measurable (s DIFF t)`,
  SIMP_TAC[REAL_MEASURABLE_MEASURABLE; IMAGE_DIFF_INJ; LIFT_EQ] THEN
  REWRITE_TAC[MEASURABLE_DIFF]);;

let REAL_MEASURE_DIFF_SUBSET = prove
 (`!s t. real_measurable s /\ real_measurable t /\ t SUBSET s
         ==> real_measure(s DIFF t) = real_measure s - real_measure t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_DIFF_SUBSET; GSYM HAS_REAL_MEASURE_MEASURE]);;

let HAS_REAL_MEASURE_UNION_REAL_NEGLIGIBLE = prove
 (`!s t m.
        s has_real_measure m /\ real_negligible t
        ==> (s UNION t) has_real_measure m`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; real_negligible; IMAGE_UNION] THEN
  REWRITE_TAC[HAS_MEASURE_UNION_NEGLIGIBLE]);;

let HAS_REAL_MEASURE_DIFF_REAL_NEGLIGIBLE = prove
 (`!s t m.
        s has_real_measure m /\ real_negligible t
        ==> (s DIFF t) has_real_measure m`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; real_negligible] THEN
  SIMP_TAC[IMAGE_DIFF_INJ; LIFT_EQ] THEN
  REWRITE_TAC[HAS_MEASURE_DIFF_NEGLIGIBLE]);;

let HAS_REAL_MEASURE_UNION_REAL_NEGLIGIBLE_EQ = prove
 (`!s t m.
     real_negligible t
     ==> ((s UNION t) has_real_measure m <=> s has_real_measure m)`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; real_negligible; IMAGE_UNION] THEN
  REWRITE_TAC[HAS_MEASURE_UNION_NEGLIGIBLE_EQ]);;

let HAS_REAL_MEASURE_DIFF_REAL_NEGLIGIBLE_EQ = prove
 (`!s t m.
     real_negligible t
     ==> ((s DIFF t) has_real_measure m <=> s has_real_measure m)`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; real_negligible] THEN
  SIMP_TAC[IMAGE_DIFF_INJ; LIFT_EQ] THEN
  REWRITE_TAC[HAS_MEASURE_DIFF_NEGLIGIBLE_EQ]);;

let HAS_REAL_MEASURE_ALMOST = prove
 (`!s s' t m. s has_real_measure m /\ real_negligible t /\
              s UNION t = s' UNION t
              ==> s' has_real_measure m`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; real_negligible; IMAGE_UNION] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_MEASURE_ALMOST THEN
  MAP_EVERY EXISTS_TAC [`IMAGE lift s`; `IMAGE lift t`] THEN ASM SET_TAC[]);;

let HAS_REAL_MEASURE_ALMOST_EQ = prove
 (`!s s' t. real_negligible t /\ s UNION t = s' UNION t
            ==> (s has_real_measure m <=> s' has_real_measure m)`,
  MESON_TAC[HAS_REAL_MEASURE_ALMOST]);;

let REAL_MEASURABLE_ALMOST = prove
 (`!s s' t. real_measurable s /\ real_negligible t /\ s UNION t = s' UNION t
            ==> real_measurable s'`,
  REWRITE_TAC[real_measurable] THEN MESON_TAC[HAS_REAL_MEASURE_ALMOST]);;

let HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNION = prove
 (`!s1 s2 m1 m2.
        s1 has_real_measure m1 /\ s2 has_real_measure m2 /\
        real_negligible(s1 INTER s2)
        ==> (s1 UNION s2) has_real_measure (m1 + m2)`,
  REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE; real_negligible; IMAGE_UNION] THEN
  SIMP_TAC[IMAGE_INTER_INJ; LIFT_EQ] THEN
  REWRITE_TAC[HAS_MEASURE_NEGLIGIBLE_UNION]);;

let REAL_MEASURE_REAL_NEGLIGIBLE_UNION = prove
 (`!s t. real_measurable s /\ real_measurable t /\ real_negligible(s INTER t)
         ==> real_measure(s UNION t) = real_measure s + real_measure t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNION;
               GSYM HAS_REAL_MEASURE_MEASURE]);;

let HAS_REAL_MEASURE_REAL_NEGLIGIBLE_SYMDIFF = prove
 (`!s t m.
        s has_real_measure m /\
        real_negligible((s DIFF t) UNION (t DIFF s))
        ==> t has_real_measure m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_MEASURE_ALMOST THEN
  MAP_EVERY EXISTS_TAC
    [`s:real->bool`; `(s DIFF t) UNION (t DIFF s):real->bool`] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let REAL_MEASURABLE_REAL_NEGLIGIBLE_SYMDIFF = prove
 (`!s t. real_measurable s /\ real_negligible((s DIFF t) UNION (t DIFF s))
         ==> real_measurable t`,
  REWRITE_TAC[real_measurable] THEN
  MESON_TAC[HAS_REAL_MEASURE_REAL_NEGLIGIBLE_SYMDIFF]);;

let REAL_MEASURE_REAL_NEGLIGIBLE_SYMDIFF = prove
 (`!s t. (real_measurable s \/ real_measurable t) /\
         real_negligible((s DIFF t) UNION (t DIFF s))
         ==> real_measure s = real_measure t`,
  MESON_TAC[HAS_REAL_MEASURE_REAL_NEGLIGIBLE_SYMDIFF; REAL_MEASURE_UNIQUE;
            UNION_COMM; HAS_REAL_MEASURE_MEASURE]);;

let HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS = prove
 (`!m f. FINITE f /\
         (!s. s IN f ==> s has_real_measure (m s)) /\
         (!s t. s IN f /\ t IN f /\ ~(s = t) ==> real_negligible(s INTER t))
         ==> (UNIONS f) has_real_measure (sum f m)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; UNIONS_0; UNIONS_INSERT; HAS_REAL_MEASURE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`s:real->bool`; `f:(real->bool)->bool`] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNION THEN
  REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[INTER_UNIONS] THEN MATCH_MP_TAC REAL_NEGLIGIBLE_UNIONS THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS = prove
 (`!m f. FINITE f /\
         (!s. s IN f ==> s has_real_measure (m s)) /\
         (!s t. s IN f /\ t IN f /\ ~(s = t) ==> real_negligible(s INTER t))
         ==> real_measure(UNIONS f) = sum f m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS]);;

let HAS_REAL_MEASURE_DISJOINT_UNIONS = prove
 (`!m f. FINITE f /\
         (!s. s IN f ==> s has_real_measure (m s)) /\
         (!s t. s IN f /\ t IN f /\ ~(s = t) ==> DISJOINT s t)
         ==> (UNIONS f) has_real_measure (sum f m)`,
  REWRITE_TAC[DISJOINT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS THEN
  ASM_SIMP_TAC[REAL_NEGLIGIBLE_EMPTY]);;

let REAL_MEASURE_DISJOINT_UNIONS = prove
 (`!m f:(real->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> s has_real_measure (m s)) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t) ==> DISJOINT s t)
        ==> real_measure(UNIONS f) = sum f m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_DISJOINT_UNIONS]);;

let HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE = prove
 (`!f:A->(real->bool) s.
        FINITE s /\
        (!x. x IN s ==> real_measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y)
               ==> real_negligible((f x) INTER (f y)))
        ==> (UNIONS (IMAGE f s)) has_real_measure
            (sum s (\x. real_measure(f x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum s (\x. real_measure(f x)) =
    sum (IMAGE (f:A->real->bool) s) real_measure`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    MATCH_MP_TAC SUM_IMAGE_NONZERO THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
    ASM_SIMP_TAC[INTER_ACI; REAL_MEASURABLE_REAL_MEASURE_EQ_0];
    MATCH_MP_TAC HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS THEN
    ASM_SIMP_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[FINITE_IMAGE; HAS_REAL_MEASURE_MEASURE]]);;

let REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE = prove
 (`!f:A->real->bool s.
        FINITE s /\
        (!x. x IN s ==> real_measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y)
               ==> real_negligible((f x) INTER (f y)))
        ==> real_measure(UNIONS (IMAGE f s)) = sum s (\x. real_measure(f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE]);;

let HAS_REAL_MEASURE_DISJOINT_UNIONS_IMAGE = prove
 (`!f:A->real->bool s.
        FINITE s /\
        (!x. x IN s ==> real_measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> (UNIONS (IMAGE f s)) has_real_measure
            (sum s (\x. real_measure(f x)))`,
  REWRITE_TAC[DISJOINT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE THEN
  ASM_SIMP_TAC[REAL_NEGLIGIBLE_EMPTY]);;

let REAL_MEASURE_DISJOINT_UNIONS_IMAGE = prove
 (`!f:A->real->bool s.
        FINITE s /\
        (!x. x IN s ==> real_measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> real_measure(UNIONS (IMAGE f s)) = sum s (\x. real_measure(f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_DISJOINT_UNIONS_IMAGE]);;

let HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE_STRONG = prove
 (`!f:A->real->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> real_measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y)
               ==> real_negligible((f x) INTER (f y)))
        ==> (UNIONS (IMAGE f s)) has_real_measure
            (sum s (\x. real_measure(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->real->bool`;
                 `{x | x IN s /\ ~((f:A->real->bool) x = {})}`]
        HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; FINITE_RESTRICT] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[NOT_IN_EMPTY];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; TAUT `a /\ ~(a /\ b) <=> a /\ ~b`] THEN
    REWRITE_TAC[REAL_MEASURE_EMPTY]]);;

let REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE_STRONG = prove
 (`!f:A->real->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> real_measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y)
               ==> real_negligible((f x) INTER (f y)))
        ==> real_measure(UNIONS (IMAGE f s)) = sum s (\x. real_measure(f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE_STRONG]);;

let HAS_REAL_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG = prove
 (`!f:A->real->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> real_measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> (UNIONS (IMAGE f s)) has_real_measure
            (sum s (\x. real_measure(f x)))`,
  REWRITE_TAC[DISJOINT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE_STRONG THEN
  ASM_SIMP_TAC[REAL_NEGLIGIBLE_EMPTY]);;

let REAL_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG = prove
 (`!f:A->real->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> real_measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> real_measure(UNIONS (IMAGE f s)) = sum s (\x. real_measure(f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG]);;

let REAL_MEASURE_UNION = prove
 (`!s t. real_measurable s /\ real_measurable t
         ==> real_measure(s UNION t) =
             real_measure(s) + real_measure(t) - real_measure(s INTER t)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE
   `s UNION t = (s INTER t) UNION (s DIFF t) UNION (t DIFF s)`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + b - c:real = c + (a - c) + (b - c)`] THEN
  MP_TAC(ISPECL [`s DIFF t:real->bool`; `t DIFF s:real->bool`]
        REAL_MEASURE_DISJOINT_UNION) THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_DIFF] THEN
  ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s INTER t:real->bool`;
                 `(s DIFF t) UNION (t DIFF s):real->bool`]
                REAL_MEASURE_DISJOINT_UNION) THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_DIFF;
               REAL_MEASURABLE_UNION; REAL_MEASURABLE_INTER] THEN
  ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN AP_TERM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[REAL_EQ_SUB_LADD] THEN MATCH_MP_TAC EQ_TRANS THENL
   [EXISTS_TAC `real_measure((s DIFF t) UNION (s INTER t):real->bool)`;
    EXISTS_TAC `real_measure((t DIFF s) UNION (s INTER t):real->bool)`] THEN
  (CONJ_TAC THENL
    [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MEASURE_DISJOINT_UNION THEN
     ASM_SIMP_TAC[REAL_MEASURABLE_DIFF; REAL_MEASURABLE_INTER];
     AP_TERM_TAC] THEN
   SET_TAC[]));;

let REAL_MEASURE_UNION_LE = prove
 (`!s t. real_measurable s /\ real_measurable t
         ==> real_measure(s UNION t) <= real_measure s + real_measure t`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_MEASURE_UNION] THEN
  REWRITE_TAC[REAL_ARITH `a + b - c <= a + b <=> &0 <= c`] THEN
  MATCH_MP_TAC REAL_MEASURE_POS_LE THEN ASM_SIMP_TAC[REAL_MEASURABLE_INTER]);;

let REAL_MEASURE_UNIONS_LE = prove
 (`!f. FINITE f /\ (!s. s IN f ==> real_measurable s)
       ==> real_measure(UNIONS f) <= sum f (\s. real_measure s)`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[UNIONS_0; UNIONS_INSERT; SUM_CLAUSES] THEN
  REWRITE_TAC[REAL_MEASURE_EMPTY; REAL_LE_REFL] THEN
  MAP_EVERY X_GEN_TAC [`s:real->bool`; `f:(real->bool)->bool`] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_measure(s) + real_measure(UNIONS f)` THEN
  ASM_SIMP_TAC[REAL_MEASURE_UNION_LE; REAL_MEASURABLE_UNIONS] THEN
  REWRITE_TAC[REAL_LE_LADD] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[]);;

let REAL_MEASURE_UNIONS_LE_IMAGE = prove
 (`!f:A->bool s:A->(real->bool).
        FINITE f /\ (!a. a IN f ==> real_measurable(s a))
        ==> real_measure(UNIONS (IMAGE s f)) <= sum f (\a. real_measure(s a))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE s (f:A->bool)) (\k:real->bool. real_measure k)` THEN
  ASM_SIMP_TAC[REAL_MEASURE_UNIONS_LE; FORALL_IN_IMAGE; FINITE_IMAGE] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SUM_IMAGE_LE THEN
  ASM_SIMP_TAC[REAL_MEASURE_POS_LE]);;

let REAL_MEASURABLE_INNER_OUTER = prove
 (`!s. real_measurable s <=>
                !e. &0 < e
                    ==> ?t u. t SUBSET s /\ s SUBSET u /\
                              real_measurable t /\ real_measurable u /\
                              abs(real_measure t - real_measure u) < e`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REPEAT(EXISTS_TAC `s:real->bool`) THEN
    ASM_REWRITE_TAC[SUBSET_REFL; REAL_SUB_REFL; REAL_ABS_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MEASURABLE_REAL_INTEGRABLE] THEN
  MATCH_MP_TAC REAL_INTEGRABLE_STRADDLE THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real->bool`; `u:real->bool`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(\x. if x IN t then &1 else &0):real->real`;
    `(\x. if x IN u then &1 else &0):real->real`;
    `real_measure(t:real->bool)`;
    `real_measure(u:real->bool)`] THEN
  ASM_REWRITE_TAC[GSYM HAS_REAL_MEASURE; GSYM HAS_REAL_MEASURE_MEASURE] THEN
  ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN
         ASM_REWRITE_TAC[DROP_VEC; REAL_POS; REAL_LE_REFL]) THEN
  ASM SET_TAC[]);;

let HAS_REAL_MEASURE_INNER_OUTER = prove
 (`!s m. s has_real_measure m <=>
                (!e. &0 < e ==> ?t. t SUBSET s /\ real_measurable t /\
                                    m - e < real_measure t) /\
                (!e. &0 < e ==> ?u. s SUBSET u /\ real_measurable u /\
                                    real_measure u < m + e)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV
      [HAS_REAL_MEASURE_REAL_MEASURABLE_REAL_MEASURE] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `s:real->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "t") (LABEL_TAC "u")) THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [REAL_MEASURABLE_INNER_OUTER] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "u" (MP_TAC o SPEC `e / &2`) THEN
    REMOVE_THEN "t" (MP_TAC o SPEC `e / &2`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[IMP_IMP; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `&0 < e /\ t <= u /\ m - e / &2 < t /\ u < m + e / &2
                          ==> abs(t - u) < e`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_MEASURE_SUBSET THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `~(&0 < x - y) /\ ~(&0 < y - x) ==> x = y`) THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [REMOVE_THEN "u" (MP_TAC o SPEC `real_measure(s:real->bool) - m`) THEN
      ASM_REWRITE_TAC[REAL_SUB_ADD2; GSYM REAL_NOT_LE];
      REMOVE_THEN "t" (MP_TAC o SPEC `m - real_measure(s:real->bool)`) THEN
      ASM_REWRITE_TAC[REAL_SUB_SUB2; GSYM REAL_NOT_LE]] THEN
    ASM_MESON_TAC[REAL_MEASURE_SUBSET]]);;

let HAS_REAL_MEASURE_INNER_OUTER_LE = prove
 (`!s:real->bool m.
        s has_real_measure m <=>
                (!e. &0 < e ==> ?t. t SUBSET s /\ real_measurable t /\
                                    m - e <= real_measure t) /\
                (!e. &0 < e ==> ?u. s SUBSET u /\ real_measurable u /\
                                    real_measure u <= m + e)`,
  REWRITE_TAC[HAS_REAL_MEASURE_INNER_OUTER] THEN
  MESON_TAC[REAL_ARITH `&0 < e /\ m - e / &2 <= t ==> m - e < t`;
            REAL_ARITH `&0 < e /\ u <= m + e / &2 ==> u < m + e`;
            REAL_ARITH `&0 < e <=> &0 < e / &2`; REAL_LT_IMP_LE]);;

let HAS_REAL_MEASURE_AFFINITY = prove
 (`!s m c y. s has_real_measure y
             ==> (IMAGE (\x. m * x + c) s) has_real_measure abs(m) * y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_MEASURE_HAS_MEASURE] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:real`; `lift c`] o MATCH_MP
    HAS_MEASURE_AFFINITY) THEN
  REWRITE_TAC[DIMINDEX_1; REAL_POW_1; GSYM IMAGE_o] THEN
  MATCH_MP_TAC EQ_IMP THEN REPEAT(AP_THM_TAC THEN AP_TERM_TAC) THEN
  SIMP_TAC[FUN_EQ_THM; FORALL_DROP; o_THM; LIFT_DROP; LIFT_ADD; LIFT_CMUL]);;

let HAS_REAL_MEASURE_SCALING = prove
 (`!s m y. s has_real_measure y
           ==> (IMAGE (\x. m * x) s) has_real_measure abs(m) * y`,
  ONCE_REWRITE_TAC[REAL_ARITH `m * x = m * x + &0`] THEN
  REWRITE_TAC[REAL_ARITH `abs m * x + &0 = abs m * x`] THEN
  REWRITE_TAC[HAS_REAL_MEASURE_AFFINITY]);;

let HAS_REAL_MEASURE_TRANSLATION = prove
 (`!s m a. s has_real_measure m ==> (IMAGE (\x. a + x) s) has_real_measure m`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + x = &1 * x + a`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_ARITH `m = abs(&1) * m`] THEN
  REWRITE_TAC[HAS_REAL_MEASURE_AFFINITY]);;

let REAL_NEGLIGIBLE_TRANSLATION = prove
 (`!s a. real_negligible s ==> real_negligible (IMAGE (\x. a + x) s)`,
  SIMP_TAC[GSYM HAS_REAL_MEASURE_0; HAS_REAL_MEASURE_TRANSLATION]);;

let HAS_REAL_MEASURE_TRANSLATION_EQ = prove
 (`!s m. (IMAGE (\x. a + x) s) has_real_measure m <=> s has_real_measure m`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  REWRITE_TAC[HAS_REAL_MEASURE_TRANSLATION] THEN
  DISCH_THEN(MP_TAC o SPEC `--a:real` o
    MATCH_MP HAS_REAL_MEASURE_TRANSLATION) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; REAL_ARITH `--a + a + b:real = b`] THEN
  SET_TAC[]);;

let REAL_NEGLIGIBLE_TRANSLATION_REV = prove
 (`!s a. real_negligible (IMAGE (\x. a + x) s) ==> real_negligible s`,
  SIMP_TAC[GSYM HAS_REAL_MEASURE_0; HAS_REAL_MEASURE_TRANSLATION_EQ]);;

let REAL_NEGLIGIBLE_TRANSLATION_EQ = prove
 (`!s a. real_negligible (IMAGE (\x. a + x) s) <=> real_negligible s`,
  SIMP_TAC[GSYM HAS_REAL_MEASURE_0; HAS_REAL_MEASURE_TRANSLATION_EQ]);;

let REAL_MEASURABLE_TRANSLATION = prove
 (`!s. real_measurable (IMAGE (\x. a + x) s) <=> real_measurable s`,
  REWRITE_TAC[real_measurable; HAS_REAL_MEASURE_TRANSLATION_EQ]);;

let REAL_MEASURE_TRANSLATION = prove
 (`!s. real_measurable s
       ==> real_measure(IMAGE (\x. a + x) s) = real_measure s`,
  REWRITE_TAC[HAS_REAL_MEASURE_MEASURE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_REWRITE_TAC[HAS_REAL_MEASURE_TRANSLATION_EQ]);;

let HAS_REAL_MEASURE_SCALING_EQ = prove
 (`!s m c. ~(c = &0)
           ==> ((IMAGE (\x. c * x) s) has_real_measure (abs(c) * m) <=>
                s has_real_measure m)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[HAS_REAL_MEASURE_SCALING] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(c:real)` o
    MATCH_MP HAS_REAL_MEASURE_SCALING) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; GSYM REAL_ABS_MUL] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GSYM REAL_ABS_MUL; REAL_MUL_LINV] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_ABS_NUM; REAL_MUL_LID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let REAL_MEASURABLE_SCALING = prove
 (`!s c. real_measurable s ==> real_measurable (IMAGE (\x. c * x) s)`,
  REWRITE_TAC[real_measurable] THEN MESON_TAC[HAS_REAL_MEASURE_SCALING]);;

let REAL_MEASURABLE_SCALING_EQ = prove
 (`!s c. ~(c = &0)
         ==> (real_measurable (IMAGE (\x. c * x) s) <=> real_measurable s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[REAL_MEASURABLE_SCALING] THEN
  DISCH_THEN(MP_TAC o SPEC `inv c:real` o MATCH_MP REAL_MEASURABLE_SCALING) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; GSYM REAL_ABS_MUL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_LID] THEN
  SET_TAC[]);;

let REAL_MEASURE_SCALING = prove
 (`!s. real_measurable s
       ==> real_measure(IMAGE (\x. c * x) s) = abs(c) * real_measure s`,
  REWRITE_TAC[HAS_REAL_MEASURE_MEASURE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_REAL_MEASURE_SCALING]);;

let HAS_REAL_MEASURE_NESTED_UNIONS = prove
 (`!s B. (!n. real_measurable(s n)) /\
         (!n. real_measure(s n) <= B) /\
         (!n. s(n) SUBSET s(SUC n))
         ==> real_measurable(UNIONS { s(n) | n IN (:num) }) /\
             ((\n. real_measure(s n))
                   ---> real_measure(UNIONS { s(n) | n IN (:num) }))
             sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL; o_DEF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[REAL_MEASURE_MEASURE] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[REAL_MEASURABLE_MEASURABLE] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`IMAGE lift o (s:num->real->bool)`; `B:real`]
        HAS_MEASURE_NESTED_UNIONS) THEN
  ASM_SIMP_TAC[o_THM; IMAGE_SUBSET] THEN
  REWRITE_TAC[SET_RULE `{IMAGE f (s n) | P n} = IMAGE (IMAGE f) {s n | P n}`;
              GSYM IMAGE_UNIONS] THEN
  SIMP_TAC[REAL_MEASURE_MEASURE; REAL_MEASURABLE_MEASURABLE]);;

let REAL_MEASURABLE_NESTED_UNIONS = prove
 (`!s B. (!n. real_measurable(s n)) /\
         (!n. real_measure(s n) <= B) /\
         (!n. s(n) SUBSET s(SUC n))
         ==> real_measurable(UNIONS { s(n) | n IN (:num) })`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_MEASURE_NESTED_UNIONS) THEN
  SIMP_TAC[]);;

let HAS_REAL_MEASURE_COUNTABLE_REAL_NEGLIGIBLE_UNIONS = prove
 (`!s:num->real->bool B.
        (!n. real_measurable(s n)) /\
        (!m n. ~(m = n) ==> real_negligible(s m INTER s n)) /\
        (!n. sum (0..n) (\k. real_measure(s k)) <= B)
        ==> real_measurable(UNIONS { s(n) | n IN (:num) }) /\
            ((\n. real_measure(s n)) real_sums
             real_measure(UNIONS { s(n) | n IN (:num) })) (from 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. UNIONS (IMAGE s (0..n)):real->bool`; `B:real`]
               HAS_REAL_MEASURE_NESTED_UNIONS) THEN
  REWRITE_TAC[real_sums; FROM_0; INTER_UNIV] THEN
  SUBGOAL_THEN
   `!n. (UNIONS (IMAGE s (0..n)):real->bool) has_real_measure
        (sum(0..n) (\k. real_measure(s k)))`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HAS_REAL_MEASURE_REAL_NEGLIGIBLE_UNIONS_IMAGE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    ASSUME_TAC(GEN `n:num` (MATCH_MP REAL_MEASURE_UNIQUE
     (SPEC `n:num` th)))) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[real_measurable]; ALL_TAC] THEN
    GEN_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[LIFT_SUM; FINITE_NUMSEG; o_DEF] THEN
  SUBGOAL_THEN
   `UNIONS {UNIONS (IMAGE s (0..n)) | n IN (:num)}:real->bool =
    UNIONS (IMAGE s (:num))`
   (fun th -> REWRITE_TAC[th] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
              REWRITE_TAC[]) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real` THEN
  REWRITE_TAC[IN_UNIONS] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; EXISTS_IN_UNIONS; IN_UNIV] THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
  REWRITE_TAC[IN_NUMSEG; LE_0] THEN MESON_TAC[LE_REFL]);;

let REAL_NEGLIGIBLE_COUNTABLE_UNIONS = prove
 (`!s:num->real->bool.
        (!n. real_negligible(s n))
        ==> real_negligible(UNIONS {s(n) | n IN (:num)})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:num->real->bool`; `&0`]
    HAS_REAL_MEASURE_COUNTABLE_REAL_NEGLIGIBLE_UNIONS) THEN
  ASM_SIMP_TAC[REAL_MEASURE_EQ_0; SUM_0; REAL_LE_REFL; LIFT_NUM] THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[HAS_REAL_MEASURE_0; real_measurable; INTER_SUBSET;
                  REAL_NEGLIGIBLE_SUBSET];
    ALL_TAC] THEN
  SIMP_TAC[GSYM REAL_MEASURABLE_REAL_MEASURE_EQ_0] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC REAL_SERIES_UNIQUE THEN REWRITE_TAC[LIFT_NUM] THEN
  MAP_EVERY EXISTS_TAC [`(\k. &0):num->real`; `from 0`] THEN
  ASM_REWRITE_TAC[REAL_SERIES_0]);;

let REAL_MEASURABLE_COUNTABLE_UNIONS_STRONG = prove
 (`!s:num->real->bool B.
        (!n. real_measurable(s n)) /\
        (!n. real_measure(UNIONS {s k | k <= n}) <= B)
        ==> real_measurable(UNIONS { s(n) | n IN (:num) })`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. UNIONS (IMAGE s (0..n)):real->bool`; `B:real`]
               REAL_MEASURABLE_NESTED_UNIONS) THEN
  SUBGOAL_THEN
   `UNIONS {UNIONS (IMAGE s (0..n)) | n IN (:num)}:real->bool =
    UNIONS (IMAGE s (:num))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real` THEN
    REWRITE_TAC[IN_UNIONS] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE; EXISTS_IN_UNIONS; IN_UNIV] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
    REWRITE_TAC[IN_NUMSEG; LE_0] THEN MESON_TAC[LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_MEASURABLE_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; FINITE_NUMSEG];
    ONCE_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
    ASM_REWRITE_TAC[IN_NUMSEG; LE_0];
    GEN_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG; LE_0] THEN ARITH_TAC]);;

let HAS_REAL_MEASURE_COUNTABLE_REAL_NEGLIGIBLE_UNIONS_BOUNDED = prove
 (`!s. (!n. real_measurable(s n)) /\
       (!m n. ~(m = n) ==> real_negligible(s m INTER s n)) /\
       real_bounded(UNIONS { s(n) | n IN (:num) })
       ==> real_measurable(UNIONS { s(n) | n IN (:num) }) /\
           ((\n. real_measure(s n)) real_sums
            real_measure(UNIONS { s(n) | n IN (:num) })) (from 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TENDSTO_REAL; o_DEF] THEN
  REWRITE_TAC[REAL_BOUNDED] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[REAL_MEASURE_MEASURE] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[REAL_MEASURABLE_MEASURABLE; real_negligible] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MP_TAC(ISPEC `IMAGE lift o (s:num->real->bool)`
        HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS_BOUNDED) THEN
  ASM_SIMP_TAC[o_THM; IMAGE_SUBSET] THEN
  REWRITE_TAC[SET_RULE `{IMAGE f (s n) | P n} = IMAGE (IMAGE f) {s n | P n}`;
              GSYM IMAGE_UNIONS] THEN
  ASM_SIMP_TAC[GSYM IMAGE_INTER_INJ; LIFT_EQ] THEN
  SIMP_TAC[REAL_SUMS; o_DEF; REAL_MEASURE_MEASURE;
           REAL_MEASURABLE_MEASURABLE]);;

let REAL_MEASURABLE_COUNTABLE_UNIONS = prove
 (`!s B. (!n. real_measurable(s n)) /\
         (!n. sum (0..n) (\k. real_measure(s k)) <= B)
         ==> real_measurable(UNIONS { s(n) | n IN (:num) })`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURABLE_COUNTABLE_UNIONS_STRONG THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..n) (\k. real_measure(s k:real->bool))` THEN
  ASM_REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (rand o rand) REAL_MEASURE_UNIONS_LE_IMAGE o
       rand o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  ONCE_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
  REWRITE_TAC[IN_NUMSEG; LE_0]);;

let REAL_MEASURABLE_COUNTABLE_UNIONS_BOUNDED = prove
 (`!s. (!n. real_measurable(s n)) /\
       real_bounded(UNIONS { s(n) | n IN (:num) })
       ==> real_measurable(UNIONS { s(n) | n IN (:num) })`,
  REWRITE_TAC[REAL_MEASURABLE_MEASURABLE; REAL_BOUNDED] THEN
  SIMP_TAC[IMAGE_INTER_INJ; LIFT_EQ; IMAGE_UNIONS] THEN
  REWRITE_TAC[SET_RULE `IMAGE f {g x | x IN s} = {f(g x) | x IN s}`] THEN
  REWRITE_TAC[MEASURABLE_COUNTABLE_UNIONS_BOUNDED]);;

let REAL_MEASURABLE_COUNTABLE_INTERS = prove
 (`!s. (!n. real_measurable(s n))
       ==> real_measurable(INTERS { s(n) | n IN (:num) })`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `INTERS { s(n):real->bool | n IN (:num) } =
                s 0 DIFF (UNIONS {s 0 DIFF s n | n IN (:num)})`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTERS; IN_DIFF; IN_UNIONS] THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_MEASURABLE_DIFF THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_MEASURABLE_COUNTABLE_UNIONS_STRONG THEN
  EXISTS_TAC `real_measure(s 0:real->bool)` THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_DIFF; LE_0] THEN
  GEN_TAC THEN MATCH_MP_TAC REAL_MEASURE_SUBSET THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; IN_ELIM_THM; IN_DIFF] THEN
    MESON_TAC[IN_DIFF]] THEN
  ONCE_REWRITE_TAC[GSYM IN_NUMSEG_0] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
               REAL_MEASURABLE_DIFF; REAL_MEASURABLE_UNIONS]);;

let REAL_NEGLIGIBLE_COUNTABLE = prove
 (`!s. COUNTABLE s ==> real_negligible s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_negligible] THEN
  MATCH_MP_TAC NEGLIGIBLE_COUNTABLE THEN ASM_SIMP_TAC[COUNTABLE_IMAGE]);;

let REAL_MEASURABLE_COMPACT = prove
 (`!s. real_compact s ==> real_measurable s`,
  REWRITE_TAC[REAL_MEASURABLE_MEASURABLE; real_compact; MEASURABLE_COMPACT]);;

let REAL_MEASURABLE_OPEN = prove
 (`!s. real_bounded s /\ real_open s ==> real_measurable s`,
  REWRITE_TAC[REAL_MEASURABLE_MEASURABLE; REAL_OPEN; REAL_BOUNDED;
              MEASURABLE_OPEN]);;

(* ------------------------------------------------------------------------- *)
(* Drop the k'th coordinate, or insert t at the k'th coordinate.             *)
(* ------------------------------------------------------------------------- *)

let dropout = new_definition
 `(dropout:num->real^N->real^M) k x =
        lambda i. if i < k then x$i else x$(i + 1)`;;

let pushin = new_definition
 `pushin k t x = lambda i. if i < k then x$i
                           else if i = k then t
                           else x$(i - 1)`;;

let DROPOUT_PUSHIN = prove
 (`!k t x.
        dimindex(:M) + 1 = dimindex(:N)
        ==> (dropout k:real^N->real^M) (pushin k t x) = x`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  ASM_SIMP_TAC[CART_EQ; dropout; pushin; LAMBDA_BETA;
               ARITH_RULE `1 <= n + 1`; ADD_SUB;
               ARITH_RULE `m <= n ==> m <= n + 1 /\ m + 1 <= n + 1`] THEN
  ARITH_TAC);;

let PUSHIN_DROPOUT = prove
 (`!k t x.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> pushin k (x$k) ((dropout k:real^N->real^M) x) = x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN(ASSUME_TAC o GSYM)) THEN
  ASM_SIMP_TAC[CART_EQ; dropout; pushin; LAMBDA_BETA;
               ARITH_RULE `i <= n + 1 ==> i - 1 <= n`] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[LT_REFL] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(i:num = k) ==> i < k \/ k < i`)) THEN
  ASM_SIMP_TAC[ARITH_RULE `i:num < k ==> ~(k < i)`] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) LAMBDA_BETA o lhand o snd) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
  ASM_SIMP_TAC[ARITH_RULE `k < i ==> ~(i - 1 < k)`] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let DROPOUT_GALOIS = prove
 (`!k t x:real^N y:real^M.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (y = dropout k x <=> (?t. x = pushin k t y))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `(x:real^N)$k` THEN ASM_SIMP_TAC[PUSHIN_DROPOUT];
    DISCH_THEN(X_CHOOSE_THEN `t:real` SUBST1_TAC) THEN
    ASM_SIMP_TAC[DROPOUT_PUSHIN]]);;

let IN_IMAGE_DROPOUT = prove
 (`!x s.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (x IN IMAGE (dropout k:real^N->real^M) s <=>
             ?t. (pushin k t x) IN s)`,
  SIMP_TAC[IN_IMAGE; DROPOUT_GALOIS] THEN MESON_TAC[]);;

let CLOSED_INTERVAL_DROPOUT = prove
 (`!k a b. dimindex(:M) + 1 = dimindex(:N) /\
           1 <= k /\ k <= dimindex(:N) /\
           a$k <= b$k
           ==> interval[dropout k a,dropout k b] =
               IMAGE (dropout k:real^N->real^M) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EXTENSION; IN_IMAGE_DROPOUT; IN_INTERVAL] THEN
  X_GEN_TAC `x:real^M` THEN
  SIMP_TAC[pushin; dropout; LAMBDA_BETA] THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `(a:real^N)$k` THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN
      COND_CASES_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[SUB_ADD]]];
    DISCH_THEN(X_CHOOSE_TAC `t:real`) THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `i + 1`) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[ADD_SUB]]]);;

let IMAGE_DROPOUT_CLOSED_INTERVAL = prove
 (`!k a b. dimindex(:M) + 1 = dimindex(:N) /\
           1 <= k /\ k <= dimindex(:N)
           ==> IMAGE (dropout k:real^N->real^M) (interval[a,b]) =
                  if a$k <= b$k then interval[dropout k a,dropout k b]
                  else {}`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CLOSED_INTERVAL_DROPOUT; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY; GSYM REAL_NOT_LE] THEN ASM_MESON_TAC[]);;

let LINEAR_DROPOUT = prove
 (`!k. dimindex(:M) < dimindex(:N)
       ==> linear(dropout k :real^N->real^M)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
   `m < n ==> !i:num. i <= m ==> i <= n /\ i + 1 <= n`)) THEN
  SIMP_TAC[linear; CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           dropout; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
               ARITH_RULE `1 <= i + 1`]);;

let DROPOUT_EQ = prove
 (`!x y k. dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N) /\
           x$k = y$k /\ (dropout k:real^N->real^M) x = dropout k y
           ==> x = y`,
  SIMP_TAC[CART_EQ; dropout; VEC_COMPONENT; LAMBDA_BETA; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `k:num`] THEN
  STRIP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(i:num = k) ==> i < k \/ k < i`))
  THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN
    ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `k < i ==> ~(i - 1 < k)`]] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let DROPOUT_0 = prove
 (`dropout k (vec 0:real^N) = vec 0`,
  SIMP_TAC[dropout; VEC_COMPONENT; CART_EQ; COND_ID; LAMBDA_BETA]);;

let DOT_DROPOUT = prove
 (`!k x y:real^N.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (dropout k x:real^M) dot (dropout k y) = x dot y - x$k * y$k`,
  REPEAT STRIP_TAC THEN SIMP_TAC[dot; dropout; LAMBDA_BETA] THEN
  REWRITE_TAC[TAUT `(if p then x else y:real) * (if p then a else b) =
                    (if p then x * a else y * b)`] THEN
  SIMP_TAC[SUM_CASES; FINITE_NUMSEG] THEN
  SUBGOAL_THEN
   `(!i. i IN 1..dimindex(:M) /\ i < k <=> i IN 1..k-1) /\
    (!i.  i IN 1..dimindex(:M) /\ ~(i < k) <=> i IN k..dimindex(:M))`
  (fun th -> REWRITE_TAC[th])
  THENL [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_ID] THEN
  REWRITE_TAC[GSYM(SPEC `1` SUM_OFFSET)] THEN
  W(MP_TAC o PART_MATCH (rhs o rand) SUM_UNION o lhs o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG; DISJOINT_NUMSEG] THEN ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`\i. (x:real^N)$i * (y:real^N)$i`;
                 `1..dimindex(:N)`;
                 `k:num`] SUM_DELETE) THEN
  ASM_REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_UNION; IN_DELETE] THEN ASM_ARITH_TAC);;

let DOT_PUSHIN = prove
 (`!k a b x y:real^M.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (pushin k a x:real^N) dot (pushin k b y) = x dot y + a * b`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(dropout k (pushin k a (x:real^M):real^N):real^M) dot
              (dropout k (pushin k b (y:real^M):real^N):real^M) +
              a * b` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[DROPOUT_PUSHIN]] THEN
  ASM_SIMP_TAC[DOT_DROPOUT] THEN
  MATCH_MP_TAC(REAL_RING
   `a':real = a /\ b' = b ==> x = x - a' * b' + a * b`) THEN
  ASM_SIMP_TAC[pushin; LAMBDA_BETA; LT_REFL]);;

let DROPOUT_ADD = prove
 (`!k x y:real^N. dropout k (x + y) = dropout k x + dropout k y`,
  SIMP_TAC[dropout; VECTOR_ADD_COMPONENT; CART_EQ; LAMBDA_BETA] THEN
  MESON_TAC[]);;

let DROPOUT_SUB = prove
 (`!k x y:real^N. dropout k (x - y) = dropout k x - dropout k y`,
  SIMP_TAC[dropout; VECTOR_SUB_COMPONENT; CART_EQ; LAMBDA_BETA] THEN
  MESON_TAC[]);;

let DROPOUT_MUL = prove
 (`!k c x:real^N. dropout k (c % x) = c % dropout k x`,
  SIMP_TAC[dropout; VECTOR_MUL_COMPONENT; CART_EQ; LAMBDA_BETA] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Take slice of set s at x$k = t and drop the k'th coordinate.              *)
(* ------------------------------------------------------------------------- *)

let slice = new_definition
 `slice k t s = IMAGE (dropout k) (s INTER {x | x$k = t})`;;

let IN_SLICE = prove
 (`!s:real^N->bool y:real^M.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (y IN slice k t s <=> pushin k t y IN s)`,
  SIMP_TAC[slice; IN_IMAGE_DROPOUT; IN_INTER; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[pushin] THEN
  ASM_SIMP_TAC[LAMBDA_BETA; LT_REFL] THEN MESON_TAC[]);;

let INTERVAL_INTER_HYPERPLANE = prove
 (`!k t a b:real^N.
        1 <= k /\ k <= dimindex(:N)
        ==> interval[a,b] INTER {x | x$k = t} =
                if a$k <= t /\ t <= b$k
                then interval[(lambda i. if i = k then t else a$i),
                              (lambda i. if i = k then t else b$i)]
                else {}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_INTERVAL; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_MESON_TAC[NOT_IN_EMPTY]] THEN
  SIMP_TAC[IN_INTERVAL; LAMBDA_BETA] THEN
  EQ_TAC THEN STRIP_TAC THENL [ASM_MESON_TAC[REAL_LE_ANTISYM]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LE_ANTISYM]] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let SLICE_INTERVAL = prove
 (`!k a b t. dimindex(:M) + 1 = dimindex(:N) /\
             1 <= k /\ k <= dimindex(:N)
             ==> slice k t (interval[a,b]) =
                 if a$k <= t /\ t <= b$k
                 then interval[(dropout k:real^N->real^M) a,dropout k b]
                 else {}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[slice; INTERVAL_INTER_HYPERPLANE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  ASM_SIMP_TAC[IMAGE_DROPOUT_CLOSED_INTERVAL; LAMBDA_BETA; REAL_LE_REFL] THEN
  MATCH_MP_TAC(MESON[]
   `a = a' /\ b = b' ==> interval[a,b] = interval[a',b']`) THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; dropout] THEN
  SUBGOAL_THEN
   `!i. i <= dimindex(:M) ==> i <= dimindex(:N) /\ i + 1 <= dimindex(:N)`
  MP_TAC THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC[LAMBDA_BETA; ARITH_RULE `1 <= i + 1`] THEN ARITH_TAC]);;

let SLICE_DIFF = prove
 (`!k a s t.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (slice k a:(real^N->bool)->(real^M->bool)) (s DIFF t) =
             (slice k a s) DIFF (slice k a t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[slice] THEN
  SIMP_TAC[SET_RULE `(s DIFF t) INTER u = (s INTER u) DIFF (t INTER u)`] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x y. x IN a /\ y IN a /\ f x = f y ==> x = y)
    ==> IMAGE f ((s INTER a) DIFF (t INTER a)) =
        IMAGE f (s INTER a) DIFF IMAGE f (t INTER a)`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[DROPOUT_EQ]);;

let SLICE_UNIV = prove
 (`!k a. dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> slice k a (:real^N) = (:real^M)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[EXTENSION; IN_UNIV; IN_IMAGE; slice; INTER_UNIV; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^M` THEN EXISTS_TAC `(pushin k a:real^M->real^N) y` THEN
  ASM_SIMP_TAC[DROPOUT_PUSHIN] THEN
  ASM_SIMP_TAC[pushin; LAMBDA_BETA; LT_REFL]);;

let SLICE_EMPTY = prove
 (`!k a. slice k a {} = {}`,
  REWRITE_TAC[slice; INTER_EMPTY; IMAGE_CLAUSES]);;

let SLICE_SUBSET = prove
 (`!s t k a. s SUBSET t ==> slice k a s SUBSET slice k a t`,
  REWRITE_TAC[slice] THEN SET_TAC[]);;

let SLICE_UNIONS = prove
 (`!s k a. slice k a (UNIONS s) = UNIONS (IMAGE (slice k a) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[slice; INTER_UNIONS; IMAGE_UNIONS] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[GSYM IMAGE_o] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; slice]);;

let SLICE_UNION = prove
 (`!k a s t.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (slice k a:(real^N->bool)->(real^M->bool)) (s UNION t) =
             (slice k a s) UNION (slice k a t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[slice; IMAGE_UNION;
        SET_RULE `(s UNION t) INTER u = (s INTER u) UNION (t INTER u)`] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[GSYM IMAGE_o] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; slice]);;

let SLICE_INTER = prove
 (`!k a s t.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (slice k a:(real^N->bool)->(real^M->bool)) (s INTER t) =
             (slice k a s) INTER (slice k a t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[slice] THEN
  MATCH_MP_TAC(SET_RULE
    `(!x y. x IN u /\ y IN u /\ f x = f y ==> x = y)
     ==> IMAGE f ((s INTER t) INTER u) =
         IMAGE f (s INTER u) INTER IMAGE f (t INTER u)`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[DROPOUT_EQ]);;

let CONVEX_SLICE = prove
 (`!k t s. dimindex(:M) < dimindex(:N) /\ convex s
           ==> convex((slice k t:(real^N->bool)->(real^M->bool)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[slice] THEN
  MATCH_MP_TAC CONVEX_LINEAR_IMAGE THEN ASM_SIMP_TAC[LINEAR_DROPOUT] THEN
  MATCH_MP_TAC CONVEX_INTER THEN ASM_REWRITE_TAC[CONVEX_STANDARD_HYPERPLANE]);;

let COMPACT_SLICE = prove
 (`!k t s. dimindex(:M) < dimindex(:N) /\ compact s
           ==> compact((slice k t:(real^N->bool)->(real^M->bool)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[slice] THEN
  MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN ASM_SIMP_TAC[LINEAR_DROPOUT] THEN
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
    MATCH_MP_TAC CLOSED_INTER THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_STANDARD_HYPERPLANE]]);;

let CLOSED_SLICE = prove
 (`!k t s. dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N) /\
           closed s
           ==> closed((slice k t:(real^N->bool)->(real^M->bool)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[slice] THEN
  SUBGOAL_THEN
   `closed(IMAGE (dropout k:real^N->real^M)
                 (IMAGE (\x. x - t % basis k)
                        (s INTER {x | x$k = t})))`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; dropout] THEN
    SUBGOAL_THEN
     `!i. i <= dimindex(:M) ==> i <= dimindex(:N) /\ i + 1 <= dimindex(:N)`
    MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; CART_EQ;
             LAMBDA_BETA; BASIS_COMPONENT; ARITH_RULE `1 <= i + 1`] THEN
    SIMP_TAC[ARITH_RULE `i:num < k ==> ~(i = k)`;
             ARITH_RULE `~(i < k) ==> ~(i + 1 = k)`] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO]] THEN
  MATCH_MP_TAC CLOSED_INJECTIVE_IMAGE_SUBSET_SUBSPACE THEN
  EXISTS_TAC `{x:real^N | x$k = &0}` THEN
  ASM_SIMP_TAC[SUBSPACE_SPECIAL_HYPERPLANE; LINEAR_DROPOUT;
               ARITH_RULE `m + 1 = n ==> m < n`] THEN
  REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[VECTOR_ARITH `x - t % b:real^N = --(t % b) + x`] THEN
    ASM_SIMP_TAC[CLOSED_TRANSLATION_EQ; CLOSED_INTER;
                 CLOSED_STANDARD_HYPERPLANE];
    MATCH_MP_TAC(SET_RULE
     `IMAGE f t SUBSET u ==> IMAGE f (s INTER t) SUBSET u`) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
                 REAL_MUL_RID; REAL_SUB_REFL];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DROPOUT_EQ THEN EXISTS_TAC `k:num` THEN
    ASM_REWRITE_TAC[DROPOUT_0; VEC_COMPONENT]]);;

let OPEN_SLICE = prove
 (`!k t s. dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N) /\
           open s
           ==> open((slice k t:(real^N->bool)->(real^M->bool)) s)`,
  REWRITE_TAC[OPEN_CLOSED] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `closed(slice k t ((:real^N) DIFF s):real^M->bool)`
  MP_TAC THENL
   [ASM_SIMP_TAC[CLOSED_SLICE];
   ASM_SIMP_TAC[SLICE_DIFF; SLICE_UNIV]]);;

let BOUNDED_SLICE = prove
 (`!k t s. dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N) /\
           bounded s
           ==> bounded((slice k t:(real^N->bool)->(real^M->bool)) s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `(slice k t:(real^N->bool)->(real^M->bool)) (interval[a,b])` THEN
  ASM_SIMP_TAC[SLICE_SUBSET] THEN ASM_SIMP_TAC[SLICE_INTERVAL] THEN
  MESON_TAC[BOUNDED_EMPTY; BOUNDED_INTERVAL]);;

let SLICE_CBALL = prove
 (`!k t x r.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (slice k t:(real^N->bool)->(real^M->bool)) (cball(x,r)) =
                if abs(t - x$k) <= r
                then cball(dropout k x,sqrt(r pow 2 - (t - x$k) pow 2))
                else {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[slice] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; NOT_IN_EMPTY; IN_CBALL] THEN
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[dist] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `~(a <= r) ==> a <= b ==> b <= r ==> F`)) THEN
    ASM_MESON_TAC[VECTOR_SUB_COMPONENT; COMPONENT_LE_NORM; NORM_SUB]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP(REAL_ARITH `abs(x) <= r ==> &0 <= r`)) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_CBALL] THEN X_GEN_TAC `y:real^M` THEN
  ASM_SIMP_TAC[DROPOUT_GALOIS; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  REWRITE_TAC[IN_CBALL; IN_INTER; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[pushin; LAMBDA_BETA; LT_REFL] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  ASM_REWRITE_TAC[dist; NORM_LE_SQUARE; GSYM pushin] THEN
  ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LE; REAL_SUB_LE; GSYM REAL_LE_SQUARE_ABS;
               REAL_ARITH `abs(x) <= r ==> abs(x) <= abs(r)`] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(x - y:real^N) dot (x - y) = x dot x + y dot y - &2 * x dot y`] THEN
  ASM_SIMP_TAC[DOT_DROPOUT; DOT_PUSHIN] THEN MATCH_MP_TAC(REAL_FIELD
     `a = t * k + b
      ==> (xx + (yy + t * t) - &2 * a <= r pow 2 <=>
           xx - k * k + yy - &2 * b <= r pow 2 - (t - k) pow 2)`) THEN
  SUBGOAL_THEN
   `y:real^M = dropout k (pushin k t y:real^N)`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC DROPOUT_PUSHIN THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[DOT_DROPOUT] THEN
    ASM_SIMP_TAC[pushin; LAMBDA_BETA; LT_REFL] THEN REAL_ARITH_TAC]);;

let SLICE_BALL = prove
 (`!k t x r.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (slice k t:(real^N->bool)->(real^M->bool)) (ball(x,r)) =
                if abs(t - x$k) < r
                then ball(dropout k x,sqrt(r pow 2 - (t - x$k) pow 2))
                else {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[slice] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; NOT_IN_EMPTY; IN_BALL] THEN
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[dist] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `~(a < r) ==> a <= b ==> b < r ==> F`)) THEN
    ASM_MESON_TAC[VECTOR_SUB_COMPONENT; COMPONENT_LE_NORM; NORM_SUB]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP(REAL_ARITH `abs(x) < r ==> &0 < r`)) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_BALL] THEN X_GEN_TAC `y:real^M` THEN
  ASM_SIMP_TAC[DROPOUT_GALOIS; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  REWRITE_TAC[IN_BALL; IN_INTER; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[pushin; LAMBDA_BETA; LT_REFL] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  ASM_REWRITE_TAC[dist; NORM_LT_SQUARE; GSYM pushin] THEN
  ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LT; REAL_SUB_LT; GSYM REAL_LT_SQUARE_ABS;
   REAL_LT_IMP_LE; REAL_ARITH `abs(x) < r ==> abs(x) < abs(r)`] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(x - y:real^N) dot (x - y) = x dot x + y dot y - &2 * x dot y`] THEN
  ASM_SIMP_TAC[DOT_DROPOUT; DOT_PUSHIN] THEN MATCH_MP_TAC(REAL_FIELD
     `a = t * k + b
      ==> (xx + (yy + t * t) - &2 * a < r pow 2 <=>
           xx - k * k + yy - &2 * b < r pow 2 - (t - k) pow 2)`) THEN
  SUBGOAL_THEN
   `y:real^M = dropout k (pushin k t y:real^N)`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC DROPOUT_PUSHIN THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[DOT_DROPOUT] THEN
    ASM_SIMP_TAC[pushin; LAMBDA_BETA; LT_REFL] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Weak but useful versions of Fubini's theorem.                             *)
(* ------------------------------------------------------------------------- *)

let FUBINI_CLOSED_INTERVAL = prove
 (`!k a b:real^N.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        a$k <= b$k
        ==> ((\t. measure (slice k t (interval[a,b]) :real^M->bool))
             has_real_integral
             (measure(interval[a,b]))) (:real)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SLICE_INTERVAL] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[MEASURE_EMPTY; MEASURE_INTERVAL] THEN
  REWRITE_TAC[GSYM IN_REAL_INTERVAL] THEN
  SIMP_TAC[HAS_REAL_INTEGRAL_RESTRICT; SUBSET_UNIV] THEN
  SUBGOAL_THEN
   `content(interval[a:real^N,b]) =
    content(interval[dropout k a:real^M,dropout k b]) * (b$k - a$k)`
  SUBST1_TAC THEN ASM_SIMP_TAC[HAS_REAL_INTEGRAL_CONST] THEN
  REWRITE_TAC[CONTENT_CLOSED_INTERVAL_CASES] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV) [COND_RAND] THEN
  GEN_REWRITE_TAC RAND_CONV [COND_RATOR] THEN
  REWRITE_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC(TAUT
   `(p <=> p') /\ x = x'
    ==> (if p then x else y) = (if p' then x' else y)`) THEN
  CONJ_TAC THENL
   [SIMP_TAC[dropout; LAMBDA_BETA] THEN EQ_TAC THEN DISCH_TAC THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i:num < k` THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN
        COND_CASES_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[SUB_ADD]]] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `1..dimindex(:N) =
                (1..(k-1)) UNION
                (k INSERT (IMAGE (\x. x + 1) (k..dimindex(:M))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_UNION; IN_INSERT; IN_IMAGE] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `1 <= k
      ==> (x = y + 1 /\ k <= y /\ y <= n <=>
           y = x - 1 /\ k + 1 <= x /\ x <= n + 1)`] THEN
    REWRITE_TAC[CONJ_ASSOC; LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `s UNION (x INSERT t) = x INSERT (s UNION t)`] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_NUMSEG; FINITE_UNION; FINITE_IMAGE] THEN
  ASM_SIMP_TAC[IN_NUMSEG; IN_UNION; IN_IMAGE; ARITH_RULE
   `1 <= k ==> ~(k <= k - 1)`] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`1`; `k - 1`; `dimindex(:M)`] NUMSEG_COMBINE_R) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) PRODUCT_UNION o lhand o snd) THEN
  SIMP_TAC[FINITE_NUMSEG; FINITE_IMAGE; IN_NUMSEG; SET_RULE
            `DISJOINT s (IMAGE f t) <=> !x. x IN t ==> ~(f x IN s)`] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) PRODUCT_UNION o rand o snd) THEN
  SIMP_TAC[FINITE_NUMSEG; FINITE_IMAGE; IN_NUMSEG; SET_RULE
            `DISJOINT s t <=> !x. ~(x IN s /\ x IN t)`] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_IMAGE; EQ_ADD_RCANCEL; SUB_ADD] THEN
  BINOP_TAC THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
  SIMP_TAC[dropout; LAMBDA_BETA; o_THM] THEN
  REPEAT STRIP_TAC THEN BINOP_TAC THEN
  (W(MP_TAC o PART_MATCH (lhs o rand) LAMBDA_BETA o rand o snd) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
   REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_ARITH_TAC));;

let MEASURABLE_OUTER_INTERVALS_BOUNDED_EXPLICIT_SPECIAL = prove
 (`!s a b e.
        2 <= dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N) /\
        measurable s /\ s SUBSET interval[a,b] /\ &0 < e
        ==> ?f:num->real^N->bool.
              (!i. (f i) SUBSET interval[a,b] /\
                   ?c d. c$k <= d$k /\ f i = interval[c,d]) /\
              (!i j. ~(i = j) ==> negligible(f i INTER f j)) /\
              s SUBSET UNIONS {f n | n IN (:num)} /\
              measurable(UNIONS {f n | n IN (:num)}) /\
              measure(UNIONS {f n | n IN (:num)}) <= measure s + e`,
  let lemma = prove
   (`UNIONS {if n IN s then f n else {} | n IN (:num)} =
     UNIONS (IMAGE f s)`,
   SIMP_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV; EXISTS_IN_IMAGE] THEN
   MESON_TAC[NOT_IN_EMPTY]) in
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MEASURABLE_OUTER_INTERVALS_BOUNDED) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `FINITE(d:(real^N->bool)->bool)` THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:num->real^N->bool`
     (fun th -> SUBST_ALL_TAC(CONJUNCT2 th) THEN ASSUME_TAC(CONJUNCT1 th))) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; FORALL_IN_IMAGE;
       RIGHT_FORALL_IMP_THM; IN_UNIV]) THEN
    EXISTS_TAC `\k. if k IN 1..CARD(d:(real^N->bool)->bool) then f k
                    else ({}:real^N->bool)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [ASM_MESON_TAC[REAL_NOT_LT; IN_NUMSEG; REAL_NOT_LE; INTERVAL_EQ_EMPTY];
        REWRITE_TAC[EMPTY_SUBSET] THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
        EXISTS_TAC `(lambda i. if i = k then &0 else &1):real^N` THEN
        EXISTS_TAC `(lambda i. if i = k then &1 else &0):real^N` THEN
        REWRITE_TAC[INTERVAL_EQ_EMPTY] THEN CONJ_TAC THENL
         [SIMP_TAC[LAMBDA_BETA; ASSUME `1 <= k`; ASSUME `k <= dimindex(:N)`;
                   REAL_POS];
          ALL_TAC] THEN
        SUBGOAL_THEN `?j. 1 <= j /\ j <= dimindex(:N) /\ ~(j = k)` MP_TAC THENL
         [MATCH_MP_TAC(MESON[] `P(k - 1) \/ P(k + 1) ==> ?i. P i`) THEN
          ASM_ARITH_TAC;
          MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[LAMBDA_BETA] THEN
          REAL_ARITH_TAC]];
      ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[lemma]] THEN
    REPEAT GEN_TAC THEN
      REPEAT(COND_CASES_TAC THEN
             ASM_REWRITE_TAC[INTER_EMPTY; NEGLIGIBLE_EMPTY]);
    MP_TAC(ISPEC `d:(real^N->bool)->bool` COUNTABLE_AS_INJECTIVE_IMAGE) THEN
    ASM_REWRITE_TAC[INFINITE] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `f:num->real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; FORALL_IN_IMAGE;
       RIGHT_FORALL_IMP_THM; IN_UNIV]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM SIMPLE_IMAGE]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_NOT_LT; IN_NUMSEG; REAL_NOT_LE; INTERVAL_EQ_EMPTY];
        ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`]] THEN
  (DISCH_TAC THEN
   SUBGOAL_THEN `negligible(interior((f:num->real^N->bool) i) INTER
                            interior(f j))`
   MP_TAC THENL [ASM_MESON_TAC[NEGLIGIBLE_EMPTY]; ALL_TAC] THEN
   REWRITE_TAC[GSYM INTERIOR_INTER] THEN
   REWRITE_TAC[GSYM HAS_MEASURE_0] THEN
   MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
     HAS_MEASURE_NEGLIGIBLE_SYMDIFF) THEN
   SIMP_TAC[INTERIOR_SUBSET; SET_RULE
      `interior(s) SUBSET s
       ==> (interior s DIFF s) UNION (s DIFF interior s) =
           s DIFF interior s`] THEN
   SUBGOAL_THEN `(?c d. (f:num->real^N->bool) i = interval[c,d]) /\
                 (?c d. (f:num->real^N->bool) j = interval[c,d])`
   STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[INTER_INTERVAL; NEGLIGIBLE_FRONTIER_INTERVAL;
                   INTERIOR_CLOSED_INTERVAL]));;

let REAL_MONOTONE_CONVERGENCE_INCREASING_AE = prove
 (`!f:num->real->real g s t.
        (!k. (f k) real_integrable_on s) /\
        (!k x. x IN s ==> f k x <= f (SUC k) x) /\
        (?t. real_negligible t /\
             !x. x IN (s DIFF t) ==> ((\k. f k x) ---> g x) sequentially) /\
        (?B. !k. abs(real_integral s (f k)) <= B)
        ==> g real_integrable_on s /\
            ((\k. real_integral s (f k)) ---> real_integral s g) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `g real_integrable_on (s DIFF t) /\
    ((\k. real_integral (s DIFF t) (f k)) ---> real_integral (s DIFF t) g)
    sequentially`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_MONOTONE_CONVERGENCE_INCREASING THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `!k:num. f k real_integrable_on s` THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      MATCH_MP_TAC REAL_INTEGRABLE_SPIKE_SET;
      ASM_SIMP_TAC[IN_DIFF];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `B:real` THEN
      UNDISCH_TAC `!k:num. abs (real_integral s (f k)) <= B` THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC REAL_INTEGRAL_SPIKE_SET];
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SPIKE_SET_EQ THEN
      MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `t:real->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      AP_THM_TAC THEN BINOP_TAC THENL
       [ABS_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_INTEGRAL_SPIKE_SET]] THEN
  MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `t:real->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let FUBINI_SIMPLE_LEMMA = prove
 (`!k s:real^N->bool e.
        &0 < e /\
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        bounded s /\ measurable s /\
        (!t. measurable(slice k t s:real^M->bool)) /\
        (\t. measure (slice k t s:real^M->bool)) real_integrable_on (:real)
        ==> real_integral(:real) (\t. measure (slice k t s :real^M->bool))
                <= measure s + e`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`; `b:real^N`; `e:real`]
        MEASURABLE_OUTER_INTERVALS_BOUNDED_EXPLICIT_SPECIAL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [SUBGOAL_THEN `1 <= dimindex(:M)` MP_TAC THENL
     [REWRITE_TAC[DIMINDEX_GE_1]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->(real^N->bool)` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t n:num. measurable((slice k t:(real^N->bool)->real^M->bool)
                                     (d n))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `n:num`] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONJUNCT2 o SPEC `n:num`) THEN
    ASM_SIMP_TAC[SLICE_INTERVAL] THEN
    MESON_TAC[MEASURABLE_EMPTY; MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `measure(UNIONS {d n | n IN (:num)}:real^N->bool)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
       [`\n t. sum(0..n)
           (\m. measure((slice k t:(real^N->bool)->real^M->bool)
                       (d m)))`;
        `\t. measure((slice k t:(real^N->bool)->real^M->bool)
                   (UNIONS {d n | n IN (:num)}))`; `(:real)`]
         REAL_MONOTONE_CONVERGENCE_INCREASING_AE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN MATCH_MP_TAC REAL_INTEGRABLE_SUM THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `j:num` THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o SPEC `j:num`) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`k:num`; `u:real^N`; `v:real^N`]
        FUBINI_CLOSED_INTERVAL) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[real_integrable_on];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
      REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC MEASURE_POS_LE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EXISTS_TAC `measure(interval[a:real^N,b])` THEN X_GEN_TAC `i:num` THEN
      W(MP_TAC o PART_MATCH (lhand o rand) REAL_INTEGRAL_SUM o
        rand o lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `?u v. u$k <= v$k /\
                            (d:num->real^N->bool) j = interval[u,v]`
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_integrable_on] THEN
        EXISTS_TAC `measure(interval[u:real^N,v])` THEN
        MATCH_MP_TAC FUBINI_CLOSED_INTERVAL THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(sum(0..i) (\m. measure(d m:real^N->bool)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
        MATCH_MP_TAC SUM_EQ_NUMSEG THEN
        X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
        SUBGOAL_THEN `?u v. u$k <= v$k /\
                            (d:num->real^N->bool) j = interval[u,v]`
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC FUBINI_CLOSED_INTERVAL THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= a ==> abs x <= a`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
        ASM_MESON_TAC[MEASURE_POS_LE; MEASURABLE_INTERVAL];
        ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (rhs o rand) MEASURE_NEGLIGIBLE_UNIONS_IMAGE o
        lhand o snd) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[FINITE_NUMSEG] THEN ASM_MESON_TAC[MEASURABLE_INTERVAL];
        ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      REWRITE_TAC[MEASURABLE_INTERVAL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_UNIONS THEN
        ASM_SIMP_TAC[FINITE_NUMSEG; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
        ASM_MESON_TAC[MEASURABLE_INTERVAL];
        REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]]] THEN
    EXISTS_TAC
     `(IMAGE (\i. (interval_lowerbound(d i):real^N)$k) (:num)) UNION
      (IMAGE (\i. (interval_upperbound(d i):real^N)$k) (:num))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_NEGLIGIBLE_COUNTABLE THEN
      SIMP_TAC[COUNTABLE_UNION; COUNTABLE_IMAGE; NUM_COUNTABLE];
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN
    REWRITE_TAC[IN_DIFF; IN_UNION; IN_IMAGE] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [IN_UNIV] THEN
    REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `\n:num. (slice k t:(real^N->bool)->real^M->bool)
                          (d n)`
       HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS_BOUNDED) THEN
    ASM_REWRITE_TAC[SLICE_UNIONS] THEN ANTS_TAC THENL
     [ALL_TAC;
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
      REWRITE_TAC[GSYM REAL_SUMS; real_sums; FROM_INTER_NUMSEG] THEN
      REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o; o_DEF]] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `(slice k t:(real^N->bool)->real^M->bool) (interval[a,b])` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[SLICE_INTERVAL] THEN
        MESON_TAC[BOUNDED_INTERVAL; BOUNDED_EMPTY];
        REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
        ASM_MESON_TAC[SLICE_SUBSET]]] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(d:num->real^N->bool) i = {}` THENL
     [ASM_REWRITE_TAC[INTER_EMPTY; NEGLIGIBLE_EMPTY; SLICE_EMPTY];
      UNDISCH_TAC `~((d:num->real^N->bool) i = {})`] THEN
    ASM_CASES_TAC `(d:num->real^N->bool) j = {}` THENL
     [ASM_REWRITE_TAC[INTER_EMPTY; NEGLIGIBLE_EMPTY; SLICE_EMPTY];
      UNDISCH_TAC `~((d:num->real^N->bool) j = {})`] THEN
    FIRST_ASSUM(fun th ->
      MAP_EVERY (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
       [SPEC `i:num` th; SPEC `j:num` th]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`w:real^N`; `x:real^N`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SLICE_INTERVAL; INTERVAL_NE_EMPTY] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    REPEAT(COND_CASES_TAC THEN
           ASM_REWRITE_TAC[INTER_EMPTY; NEGLIGIBLE_EMPTY]) THEN
    REWRITE_TAC[INTER_INTERVAL; NEGLIGIBLE_INTERVAL; INTERVAL_EQ_EMPTY] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(a /\ b ==> ~c)`] THEN
    SIMP_TAC[LAMBDA_BETA] THEN REWRITE_TAC[NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(l:num = k)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN
       (fun th -> MP_TAC(SPEC `i:num` th) THEN MP_TAC(SPEC `j:num` th))) THEN
      ASM_SIMP_TAC[INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND] THEN
      REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
     `~(l:num = k) ==> l < k \/ k < l`))
    THENL
     [EXISTS_TAC `l:num` THEN
      MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[dropout; LAMBDA_BETA]] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `l - 1` THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[dropout; LAMBDA_BETA]] THEN
    ASM_SIMP_TAC[ARITH_RULE `k < l ==> ~(l - 1 < k)`] THEN
    ASM_SIMP_TAC[SUB_ADD];
    ALL_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `real_integral (:real)
        (\t. measure ((slice k t :(real^N->bool)->real^M->bool)
                      (UNIONS {d n | n IN (:num)})))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[SLICE_SUBSET; SLICE_UNIONS] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    ONCE_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
    MATCH_MP_TAC MEASURABLE_COUNTABLE_UNIONS_BOUNDED THEN
    ASM_REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `(slice k t:(real^N->bool)->real^M->bool) (interval[a,b])` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[SLICE_INTERVAL] THEN
      MESON_TAC[BOUNDED_INTERVAL; BOUNDED_EMPTY];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      ASM_MESON_TAC[SLICE_SUBSET]];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
    EXISTS_TAC `\n. real_integral (:real)
       (\t. sum (0..n) (\m. measure((slice k t:(real^N->bool)->real^M->bool)

                         (d m))))` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MP_TAC(ISPEC `d:num->(real^N->bool)`
     HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS_BOUNDED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MEASURABLE_INTERVAL]; ALL_TAC] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `interval[a:real^N,b]` THEN
      REWRITE_TAC[BOUNDED_INTERVAL; UNIONS_SUBSET; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
    REWRITE_TAC[GSYM REAL_SUMS] THEN
    REWRITE_TAC[real_sums; FROM_INTER_NUMSEG] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) REAL_INTEGRAL_SUM o rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v. u$k <= v$k /\
                          (d:num->real^N->bool) j = interval[u,v]`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_integrable_on] THEN
      EXISTS_TAC `measure(interval[u:real^N,v])` THEN
      MATCH_MP_TAC FUBINI_CLOSED_INTERVAL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    SUBGOAL_THEN `?u v. u$k <= v$k /\
                          (d:num->real^N->bool) j = interval[u,v]`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUBINI_CLOSED_INTERVAL THEN ASM_REWRITE_TAC[]]);;

let FUBINI_SIMPLE = prove
 (`!k s:real^N->bool.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        bounded s /\
        measurable s /\
        (!t. measurable(slice k t s :real^M->bool)) /\
        (\t. measure (slice k t s :real^M->bool)) real_integrable_on (:real)
        ==> measure s =
              real_integral(:real)(\t. measure (slice k t s :real^M->bool))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[SLICE_EMPTY; MEASURE_EMPTY; REAL_INTEGRAL_0];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interval[a:real^N,b] = {})` MP_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[INTERVAL_NE_EMPTY] THEN DISCH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 < b - a) /\ ~(&0 < a - b) ==> a:real = b`) THEN
  CONJ_TAC THEN MATCH_MP_TAC(MESON[]
     `(!e. x - y = e ==> ~(&0 < e)) ==> ~(&0 < x - y)`) THEN
  X_GEN_TAC `e:real` THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `e / &2`]
      FUBINI_SIMPLE_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `interval[a:real^N,b] DIFF s`; `e / &2`]
    FUBINI_SIMPLE_LEMMA) THEN
  ASM_REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [SIMP_TAC[BOUNDED_DIFF; BOUNDED_INTERVAL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_INTERVAL]; ALL_TAC] THEN
  ASM_SIMP_TAC[SLICE_DIFF] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN MATCH_MP_TAC MEASURABLE_DIFF THEN
    ASM_SIMP_TAC[SLICE_INTERVAL] THEN
    MESON_TAC[MEASURABLE_EMPTY; MEASURABLE_INTERVAL];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `!t. measure(slice k t (interval[a:real^N,b]) DIFF
                slice k t (s:real^N->bool) :real^M->bool) =
        measure(slice k t (interval[a:real^N,b]):real^M->bool) -
        measure(slice k t s :real^M->bool)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [X_GEN_TAC `t:real` THEN MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN
    ASM_SIMP_TAC[SLICE_SUBSET] THEN
    ASM_SIMP_TAC[SLICE_INTERVAL] THEN
    MESON_TAC[MEASURABLE_EMPTY; MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `a:real^N`; `b:real^N`] FUBINI_CLOSED_INTERVAL) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN ASM_MESON_TAC[real_integrable_on];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN
  ASM_SIMP_TAC[MEASURE_DIFF_SUBSET; MEASURABLE_INTERVAL] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) REAL_INTEGRAL_SUB o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[real_integrable_on]; DISCH_THEN SUBST1_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  ASM_REAL_ARITH_TAC);;

let FUBINI_SIMPLE_ALT = prove
 (`!k s:real^N->bool.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        bounded s /\
        measurable s /\
        (!t. measurable(slice k t s :real^M->bool)) /\
        ((\t. measure (slice k t s :real^M->bool)) has_real_integral B) (:real)
        ==> measure s = B`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `real_integral (:real)
                 (\t. measure (slice k t (s:real^N->bool) :real^M->bool))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FUBINI_SIMPLE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[real_integrable_on];
    MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]]);;

let FUBINI_SIMPLE_COMPACT_STRONG = prove
 (`!k s:real^N->bool.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        compact s /\
        ((\t. measure (slice k t s :real^M->bool)) has_real_integral B) (:real)
        ==> measurable s /\ measure s = B`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MEASURABLE_COMPACT] THEN
  MATCH_MP_TAC FUBINI_SIMPLE_ALT THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; MEASURABLE_COMPACT] THEN
  GEN_TAC THEN MATCH_MP_TAC MEASURABLE_COMPACT THEN
  MATCH_MP_TAC COMPACT_SLICE THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let FUBINI_SIMPLE_COMPACT = prove
 (`!k s:real^N->bool.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        compact s /\
        ((\t. measure (slice k t s :real^M->bool)) has_real_integral B) (:real)
        ==> measure s = B`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUBINI_SIMPLE_COMPACT_STRONG) THEN SIMP_TAC[]);;

let FUBINI_SIMPLE_CONVEX_STRONG = prove
 (`!k s:real^N->bool.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        bounded s /\ convex s /\
        ((\t. measure (slice k t s :real^M->bool)) has_real_integral B) (:real)
        ==> measurable s /\ measure s = B`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MEASURABLE_CONVEX] THEN
  MATCH_MP_TAC FUBINI_SIMPLE_ALT THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MEASURABLE_CONVEX] THEN
  GEN_TAC THEN MATCH_MP_TAC MEASURABLE_CONVEX THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONVEX_SLICE; MATCH_MP_TAC BOUNDED_SLICE] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let FUBINI_SIMPLE_CONVEX = prove
 (`!k s:real^N->bool.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        bounded s /\ convex s /\
        ((\t. measure (slice k t s :real^M->bool)) has_real_integral B) (:real)
        ==> measure s = B`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUBINI_SIMPLE_CONVEX_STRONG) THEN SIMP_TAC[]);;

let FUBINI_SIMPLE_OPEN_STRONG = prove
 (`!k s:real^N->bool.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        bounded s /\ open s /\
        ((\t. measure (slice k t s :real^M->bool)) has_real_integral B) (:real)
        ==> measurable s /\ measure s = B`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MEASURABLE_OPEN] THEN
  MATCH_MP_TAC FUBINI_SIMPLE_ALT THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MEASURABLE_OPEN] THEN
  GEN_TAC THEN MATCH_MP_TAC MEASURABLE_OPEN THEN CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_SLICE; MATCH_MP_TAC OPEN_SLICE] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let FUBINI_SIMPLE_OPEN = prove
 (`!k s:real^N->bool.
        dimindex(:M) + 1 = dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N) /\
        bounded s /\ open s /\
        ((\t. measure (slice k t s :real^M->bool)) has_real_integral B) (:real)
        ==> measure s = B`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUBINI_SIMPLE_OPEN_STRONG) THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Points with scaled integer coordinates, and hence rationals, are dense.   *)
(* ------------------------------------------------------------------------- *)

let CLOSURE_DYADIC_RATIONALS = prove
 (`closure { inv(&2 pow n) % x |n,x|
             !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i) } = (:real^N)`,
  REWRITE_TAC[EXTENSION; CLOSURE_APPROACHABLE; IN_UNIV; EXISTS_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `e:real`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`inv(&2)`; `e / &(dimindex(:N))`] REAL_ARCH_POW_INV) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1;
               REAL_POW_INV; REAL_LT_RDIV_EQ] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC MONO_EXISTS THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  EXISTS_TAC `(lambda i. floor(&2 pow n * (x:real^N)$i)):real^N` THEN
  ASM_SIMP_TAC[LAMBDA_BETA; FLOOR; dist; NORM_MUL] THEN
  MATCH_MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] REAL_LET_TRANS)
   (SPEC_ALL NORM_LE_L1)) THEN
  SIMP_TAC[LAMBDA_BETA; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&(dimindex(:N)) * inv(&2 pow n)` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  SIMP_TAC[REAL_ABS_MUL; REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH;
    REAL_FIELD `~(a = &0) ==> inv a * b - x = inv a * (b - a * x)`] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  REWRITE_TAC[REAL_LE_REFL; REAL_ABS_POW; REAL_ABS_INV; REAL_ABS_NUM] THEN
  MP_TAC(SPEC `&2 pow n * (x:real^N)$k` FLOOR) THEN REAL_ARITH_TAC);;

let CLOSURE_RATIONAL_COORDINATES = prove
 (`closure { x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i) } =
   (:real^N)`,
  MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ s = UNIV ==> t = UNIV`) THEN
  EXISTS_TAC
   `closure { inv(&2 pow n) % x:real^N |n,x|
              !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i) }` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[CLOSURE_DYADIC_RATIONALS]] THEN
  MATCH_MP_TAC SUBSET_CLOSURE THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM; VECTOR_MUL_COMPONENT] THEN
  ASM_SIMP_TAC[RATIONAL_CLOSED]);;

let OPEN_SET_RATIONAL_COORDINATES = prove
 (`!s. open s /\ ~(s = {})
       ==> ?x:real^N. x IN s /\
                      !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `~(closure { x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i) } INTER
    (s:real^N->bool) = {})`
  MP_TAC THENL
   [ASM_REWRITE_TAC[CLOSURE_RATIONAL_COORDINATES; INTER_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; CLOSURE_APPROACHABLE; IN_INTER;
              IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N` o REWRITE_RULE[open_def]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let REAL_OPEN_SET_RATIONAL = prove
 (`!s. real_open s /\ ~(s = {}) ==> ?x. rational x /\ x IN s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MP_TAC(ISPEC `IMAGE lift s` OPEN_SET_RATIONAL_COORDINATES) THEN
  ASM_REWRITE_TAC[GSYM REAL_OPEN; IMAGE_EQ_EMPTY; EXISTS_IN_IMAGE] THEN
  SIMP_TAC[DIMINDEX_1; FORALL_1; GSYM drop; LIFT_DROP]);;

let REAL_OPEN_RATIONAL = prove
 (`!P. real_open {x | P x} /\ (?x. P x) ==> ?x. rational x /\ P x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `{x:real | P x}` REAL_OPEN_SET_RATIONAL) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let REAL_OPEN_SET_EXISTS_RATIONAL = prove
 (`!s. real_open s ==> ((?x. rational x /\ x IN s) <=> (?x. x IN s))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_MESON_TAC[REAL_OPEN_SET_RATIONAL; GSYM MEMBER_NOT_EMPTY]);;

let REAL_OPEN_EXISTS_RATIONAL = prove
 (`!P. real_open {x | P x} ==> ((?x. rational x /\ P x) <=> (?x. P x))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_OPEN_SET_EXISTS_RATIONAL) THEN
  REWRITE_TAC[IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* Hence a criterion for two functions to agree.                             *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_CONST_DYADIC_RATIONALS = prove
 (`!f:real^M->real^N a.
     f continuous_on (:real^M) /\
     (!x. (!i. 1 <= i /\ i <= dimindex(:M) ==> integer(x$i)) ==> f(x) = a) /\
     (!x. f(x) = a ==> f(inv(&2) % x) = a)
     ==> !x. f(x) = a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC(ISPECL
   [`f:real^M->real^N`;
    `{ inv(&2 pow n) % x:real^M |n,x|
       !i. 1 <= i /\ i <= dimindex(:M) ==> integer(x$i) }`;
    `a:real^N`] CONTINUOUS_CONSTANT_ON_CLOSURE) THEN
  ASM_REWRITE_TAC[FORALL_IN_GSPEC; CLOSURE_DYADIC_RATIONALS; IN_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[real_pow; REAL_INV_1; VECTOR_MUL_LID] THEN
  ASM_SIMP_TAC[REAL_INV_MUL; GSYM VECTOR_MUL_ASSOC]);;

let REAL_CONTINUOUS_ON_CONST_DYADIC_RATIONALS = prove
 (`!f a.
     f real_continuous_on (:real) /\
     (!x. integer(x) ==> f(x) = a) /\
     (!x. f(x) = a ==> f(x / &2) = a)
     ==> !x. f(x) = a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `lift a`]
    CONTINUOUS_ON_CONST_DYADIC_RATIONALS) THEN
  ASM_REWRITE_TAC[GSYM REAL_CONTINUOUS_ON; GSYM IMAGE_LIFT_UNIV] THEN
  ASM_SIMP_TAC[o_THM; DIMINDEX_1; FORALL_1; GSYM drop; LIFT_EQ; DROP_CMUL;
               REAL_ARITH `inv(&2) * x = x / &2`] THEN
  ASM_MESON_TAC[LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Now prove a convenient condition for linearity.                           *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ADDITIVE_IMP_LINEAR = prove
 (`!f:real^M->real^N.
        f continuous_on (:real^M) /\
        (!x y. f(x + y) = f(x) + f(y))
        ==> linear f`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) (vec 0) = vec 0` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o repeat (SPEC `vec 0:real^M`)) THEN
    REWRITE_TAC[VECTOR_ADD_LID] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[linear] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN X_GEN_TAC `x:real^M` THEN
  MP_TAC(ISPECL [`\c. norm((f:real^M->real^N)(c % x) - c % f(x))`; `&0`]
        REAL_CONTINUOUS_ON_CONST_DYADIC_RATIONALS) THEN
  REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_UNIV; WITHIN_UNIV]) THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_UNIV] THEN
    GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHINREAL_COMPOSE THEN
    SIMP_TAC[REAL_CONTINUOUS_NORM_WITHIN] THEN MATCH_MP_TAC CONTINUOUS_SUB THEN
    ASM_SIMP_TAC[REWRITE_RULE[GSYM REAL_CONTINUOUS_CONTINUOUS1]CONTINUOUS_VMUL;
                 REAL_CONTINUOUS_WITHIN_ID; CONTINUOUS_AT_WITHIN;
                 REWRITE_RULE[o_DEF] CONTINUOUS_WITHINREAL_COMPOSE];
    MATCH_MP_TAC FORALL_INTEGER THEN CONJ_TAC THENL
     [INDUCT_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO; GSYM REAL_OF_NUM_SUC] THEN
      ASM_REWRITE_TAC[VECTOR_ADD_RDISTRIB; VECTOR_MUL_LID];
      X_GEN_TAC `c:real` THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`c % x:real^M`; `--(c % x):real^M`]) THEN
      ASM_REWRITE_TAC[VECTOR_ADD_RINV; VECTOR_MUL_LNEG; IMP_IMP] THEN
      VECTOR_ARITH_TAC];
    X_GEN_TAC `c:real` THEN
    FIRST_X_ASSUM(MP_TAC o funpow 2 (SPEC `c / &2 % x:real^M`)) THEN
    REWRITE_TAC[VECTOR_ARITH `c / &2 % x + c / &2 % x:real^N = c % x`] THEN
    REWRITE_TAC[IMP_IMP] THEN VECTOR_ARITH_TAC]);;

let REAL_CONTINUOUS_ADDITIVE_IMP_LINEAR = prove
 (`!f. f real_continuous_on (:real) /\
       (!x y. f(x + y) = f(x) + f(y))
       ==> !a x. f(a * x) = a * f(x)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `lift o f o drop` CONTINUOUS_ADDITIVE_IMP_LINEAR) THEN
  ASM_REWRITE_TAC[GSYM REAL_CONTINUOUS_ON; GSYM IMAGE_LIFT_UNIV] THEN
  ASM_REWRITE_TAC[linear; GSYM FORALL_DROP; o_THM; DROP_ADD; LIFT_DROP;
                  DROP_CMUL; GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ]);;

(* ------------------------------------------------------------------------- *)
(* A variant of REAL_CONTINUOUS_ADDITIVE_IMP_LINEAR for intervals.           *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_FLOOR = prove
 (`!x. ~(integer x) ==> floor real_continuous (atreal x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_continuous_atreal] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `min (x - floor x) ((floor x + &1) - x)` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_SUB_LT; REAL_FLOOR_LT; FLOOR] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x = y ==> abs(x - y) < e`) THEN
  ASM_REWRITE_TAC[GSYM FLOOR_UNIQUE; FLOOR] THEN
  MP_TAC(ISPEC `x:real` FLOOR) THEN ASM_REAL_ARITH_TAC);;

let REAL_CONTINUOUS_FRAC = prove
 (`!x. ~(integer x) ==> frac real_continuous (atreal x)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[FRAC_FLOOR] THEN MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
  ASM_SIMP_TAC[REAL_CONTINUOUS_FLOOR; REAL_CONTINUOUS_AT_ID]);;

let REAL_CONTINUOUS_ADDITIVE_EXTEND = prove
 (`!f. f real_continuous_on real_interval[&0,&1] /\
       (!x y. &0 <= x /\ &0 <= y /\ x + y <= &1
              ==> f(x + y) = f(x) + f(y))
       ==> ?g.  g real_continuous_on (:real) /\
                (!x y. g(x + y) = g(x) + g(y)) /\
                (!x. x IN real_interval[&0,&1] ==> g x = f x)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `f(&0) = &0` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o ISPECL [`&0`; `&0`]) THEN
    REWRITE_TAC[REAL_ADD_LID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\x. f(&1) * floor(x) + f(frac x)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `f real_continuous_on real_interval[&0,&1]` THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; WITHINREAL_UNIV] THEN
    DISCH_TAC THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `integer x` THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN CONJ_TAC THEN
      ASM_SIMP_TAC[REAL_CONTINUOUS_LMUL; REAL_CONTINUOUS_FLOOR; ETA_AX] THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] REAL_CONTINUOUS_ATREAL_COMPOSE) THEN
      ASM_SIMP_TAC[REAL_CONTINUOUS_FRAC] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [IN_REAL_INTERVAL] o
                    SPEC `frac x`) THEN
      ASM_SIMP_TAC[FLOOR_FRAC; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[real_continuous_atreal; real_continuous_withinreal] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
      ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min d (min (frac x) (&1 - frac x))` THEN
      ASM_SIMP_TAC[REAL_LT_MIN; REAL_SUB_LT; FLOOR_FRAC; REAL_FRAC_POS_LT] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC[real_continuous_atreal; REAL_FRAC_ZERO; REAL_FLOOR_REFL] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE (BINDER_CONV o LAND_CONV)
       [IN_REAL_INTERVAL]) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `&1` th) THEN MP_TAC(SPEC `&0` th)) THEN
    REWRITE_TAC[REAL_LE_REFL; REAL_POS] THEN
    REWRITE_TAC[IMP_IMP; real_continuous_withinreal; AND_FORALL_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC)
                 (X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `min (&1) (min d1 d2)` THEN
    ASM_REWRITE_TAC[REAL_LT_01; REAL_LT_MIN] THEN
    X_GEN_TAC `y:real` THEN STRIP_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH `x <= y \/ y < x`) THENL
     [SUBGOAL_THEN `floor y = floor x` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM FLOOR_UNIQUE; FLOOR] THEN
        ASM_SIMP_TAC[REAL_FLOOR_REFL] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[FRAC_FLOOR; REAL_FLOOR_REFL] THEN
        REWRITE_TAC[REAL_ARITH `(a + x) - (a + &0) = x - &0`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `floor y = floor x - &1` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM FLOOR_UNIQUE; FLOOR] THEN
        ASM_SIMP_TAC[REAL_FLOOR_REFL; INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[FRAC_FLOOR; REAL_FLOOR_REFL] THEN
        REWRITE_TAC[REAL_ARITH `(f1 * (x - &1) + f) - (f1 * x + &0) =
                                f - f1`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    REPEAT GEN_TAC THEN REWRITE_TAC[REAL_FLOOR_ADD; REAL_FRAC_ADD] THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; FLOOR_FRAC; REAL_LE_ADD] THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `f1 * ((x + y) + &1) + g = (f1 * x + z) + f1 * y + h <=>
      f1 / &2 + g / &2 = z / &2 + h / &2`] THEN
    SUBGOAL_THEN
     `!t. &0 <= t /\ t <= &1 ==> f(t) / &2 = f(t / &2)`
    ASSUME_TAC THENL
     [GEN_TAC THEN FIRST_ASSUM(MP_TAC o ISPECL [`t / &2`; `t / &2`]) THEN
      REWRITE_TAC[REAL_HALF] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_REFL; FLOOR_FRAC; REAL_LT_IMP_LE;
                 REAL_ARITH `~(x + y < &1) ==> &0 <= (x + y) - &1`;
                 REAL_ARITH `x < &1 /\ y < &1 ==> (x + y) - &1 <= &1`] THEN
    MATCH_MP_TAC(MESON[]
     `f(a + b) = f a + f b /\ f(c + d) = f(c) + f(d) /\ a + b = c + d
      ==> (f:real->real)(a) + f(b) = f(c) + f(d)`) THEN
    REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY (MP_TAC o C SPEC FLOOR_FRAC) [`x:real`; `y:real`] THEN
    ASM_REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_CASES_TAC `x = &1` THEN
    ASM_REWRITE_TAC[FLOOR_NUM; FRAC_NUM; REAL_MUL_RID; REAL_ADD_RID] THEN
    STRIP_TAC THEN SUBGOAL_THEN `floor x = &0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM FLOOR_UNIQUE; INTEGER_CLOSED];
      ASM_REWRITE_TAC[FRAC_FLOOR; REAL_SUB_RZERO]] THEN
    ASM_REAL_ARITH_TAC]);;

let REAL_CONTINUOUS_ADDITIVE_IMP_LINEAR_INTERVAL = prove
 (`!f b. (f ---> &0) (atreal (&0) within {x | &0 <= x}) /\
         (!x y. &0 <= x /\ &0 <= y /\ x + y <= b ==> f(x + y) = f(x) + f(y))
         ==> !a x. &0 <= x /\ x <= b /\
                   &0 <= a * x /\ a * x <= b
                   ==> f(a * x) = a * f(x)`,
  SUBGOAL_THEN
   `!f. (f ---> &0) (atreal (&0) within {x | &0 <= x}) /\
        (!x y. &0 <= x /\ &0 <= y /\ x + y <= &1 ==> f(x + y) = f(x) + f(y))
        ==> !a x. &0 <= x /\ x <= &1 /\ &0 <= a * x /\ a * x <= &1
                  ==> f(a * x) = a * f(x)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!f. f real_continuous_on real_interval[&0,&1] /\
          (!x y. &0 <= x /\ &0 <= y /\ x + y <= &1 ==> f(x + y) = f(x) + f(y))
          ==> !a x. &0 <= x /\ x <= &1 /\ &0 <= a * x /\ a * x <= &1
                    ==> f(a * x) = a * f(x)`
    (fun th -> GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th) THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPEC `f:real->real` REAL_CONTINUOUS_ADDITIVE_EXTEND) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPEC `g:real->real` REAL_CONTINUOUS_ADDITIVE_IMP_LINEAR) THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[real_continuous_on; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_WITHINREAL]) THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
      ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
       (REAL_ARITH `y = x \/ y < x \/ x < y`) THENL
       [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM];
        SUBGOAL_THEN `(f:real->real)(y + (x - y)) = f(y) + f(x - y)`
        MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_SUB_ADD2] THEN DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC[REAL_ADD_SUB2; REAL_ABS_NEG] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN `(f:real->real)(x + (y - x)) = f(x) + f(y - x)`
        MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_SUB_ADD2] THEN DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC[REAL_ADD_SUB] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (REAL_ARITH `b < &0 \/ b = &0 \/ &0 < b`)
    THENL
     [ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_ARITH
       `a <= x /\ x <= a /\ a <= y /\ y <= a <=> x = a /\ y = a`] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `&0`]) THEN
      ASM_REWRITE_TAC[REAL_ADD_LID; REAL_LE_REFL] THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o ISPEC `(\x. f(b * x)):real->real`) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `a:real` THEN
      DISCH_THEN(fun th -> X_GEN_TAC `x:real` THEN STRIP_TAC THEN
                           MP_TAC(ISPEC `x / b:real` th)) THEN
      ASM_SIMP_TAC[REAL_FIELD `&0 < b ==> b * a * x / b = a * x`;
                   REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[REAL_ARITH `a * x / b:real = (a * x) / b`] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_ARITH `b * x + b * y <= b <=> &0 <= b * (&1 - (x + y))`;
                   REAL_LE_MUL; REAL_LT_IMP_LE; REAL_SUB_LE]] THEN
    REWRITE_TAC[REALLIM_WITHINREAL] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_WITHINREAL]) THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    REWRITE_TAC[REAL_SUB_RZERO; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d / b:real` THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < b ==> abs b * x = x * b`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; GSYM REAL_LT_RDIV_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Also, deduce that a discrete set is countable etc.                        *)
(* ------------------------------------------------------------------------- *)

let COUNTABLE_INTEGER = prove
 (`COUNTABLE integer`,
  MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC
   `IMAGE (\n. (&n:real)) (:num) UNION IMAGE (\n. --(&n)) (:num)` THEN
  SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_UNION; NUM_COUNTABLE] THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE; IN_UNIV] THEN
  REWRITE_TAC[IN; INTEGER_CASES]);;

let COUNTABLE_RATIONAL = prove
 (`COUNTABLE rational`,
  MATCH_MP_TAC COUNTABLE_SUBSET THEN
  EXISTS_TAC `IMAGE (\(x,y). x / y) (integer CROSS integer)` THEN
  SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_CROSS; COUNTABLE_INTEGER] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[rational; IN] THEN MESON_TAC[]);;

let COUNTABLE_RATIONAL_COORDINATES = prove
 (`COUNTABLE { x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i) }`,
  MATCH_MP_TAC COUNTABLE_CART THEN
  REWRITE_TAC[SET_RULE `{x | P x} = P`; COUNTABLE_RATIONAL]);;

let DISCRETE_IMP_COUNTABLE = prove
 (`!s:real^N->bool.
        (!x. x IN s ==> ?e. &0 < e /\
                            !y. y IN s /\ ~(y = x) ==> e <= norm(y - x))
        ==> COUNTABLE s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN s
        ==> ?q. (!i. 1 <= i /\ i <= dimindex(:N) ==> rational(q$i)) /\
                !y:real^N. y IN s /\ ~(y = x) ==> norm(x - q) < norm(y - q)`
  MP_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SET_RULE `x IN (:real^N)`) THEN
    REWRITE_TAC[GSYM CLOSURE_RATIONAL_COORDINATES] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^N` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN NORM_ARITH_TAC;
    POP_ASSUM(K ALL_TAC) THEN
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `q:real^N->real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`s:real^N->bool`;
      `{ x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i) }`;
      `(:num)`] CARD_LE_TRANS) THEN
    REWRITE_TAC[COUNTABLE; ge_c] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[REWRITE_RULE[COUNTABLE; ge_c] COUNTABLE_RATIONAL_COORDINATES] THEN
    REWRITE_TAC[le_c] THEN EXISTS_TAC `q:real^N->real^N` THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LT_ANTISYM]]);;

let STEINHAUS_TRIVIAL = prove
 (`!s e. ~(negligible s) /\ &0 < e
         ==> ?x y:real^N. x IN s /\ y IN s /\ ~(x = y) /\ norm(x - y) < e`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_COUNTABLE THEN
  MATCH_MP_TAC DISCRETE_IMP_COUNTABLE THEN
  ASM_MESON_TAC[REAL_NOT_LT]);;

let REAL_STEINHAUS = prove
 (`!s. real_measurable s /\ &0 < real_measure s
       ==> ?d. &0 < d /\
               real_interval(--d,d) SUBSET {x - y | x IN s /\ y IN s}`,
  GEN_TAC THEN SIMP_TAC[IMP_CONJ; REAL_MEASURE_MEASURE] THEN
  REWRITE_TAC[IMP_IMP; REAL_MEASURABLE_MEASURABLE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP STEINHAUS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  REWRITE_TAC[SUBSET; BALL_INTERVAL; IN_INTERVAL_1; IN_REAL_INTERVAL] THEN
  REWRITE_TAC[SET_RULE `{g x y | x IN IMAGE f s /\ y IN IMAGE f t} =
                        {g (f x) (f y) | x IN s /\ y IN t}`] THEN
  REWRITE_TAC[GSYM LIFT_SUB] THEN
  REWRITE_TAC[SET_RULE `{lift(f x y) | P x y} = IMAGE lift {f x y | P x y}`;
              IN_IMAGE_LIFT_DROP; GSYM FORALL_DROP] THEN
  REWRITE_TAC[DROP_SUB; DROP_VEC; LIFT_DROP; DROP_ADD] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bernstein polynomials.                                                    *)
(* ------------------------------------------------------------------------- *)

let bernstein = new_definition
 `bernstein n k x = &(binom(n,k)) * x pow k * (&1 - x) pow (n - k)`;;

let BERNSTEIN_CONV =
  GEN_REWRITE_CONV I [bernstein] THENC
  COMB2_CONV (RAND_CONV(RAND_CONV NUM_BINOM_CONV))
             (RAND_CONV(RAND_CONV NUM_SUB_CONV)) THENC
  REAL_POLY_CONV;;

(* ------------------------------------------------------------------------- *)
(* Lemmas about Bernstein polynomials.                                       *)
(* ------------------------------------------------------------------------- *)

let BERNSTEIN_POS = prove
 (`!n k x. &0 <= x /\ x <= &1 ==> &0 <= bernstein n k x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bernstein] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC);;

let SUM_BERNSTEIN = prove
 (`!n. sum (0..n) (\k. bernstein n k x) = &1`,
  REWRITE_TAC[bernstein; GSYM REAL_BINOMIAL_THEOREM] THEN
  REWRITE_TAC[REAL_SUB_ADD2; REAL_POW_ONE]);;

let BERNSTEIN_LEMMA = prove
 (`!n k x. sum(0..n) (\k. (&k - &n * x) pow 2 * bernstein n k x) =
           &n * x * (&1 - x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `!x y. sum(0..n) (\k. &(binom(n,k)) * x pow k * y pow (n - k)) =
           (x + y) pow n`
  (LABEL_TAC "0") THENL [ASM_REWRITE_TAC[REAL_BINOMIAL_THEOREM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. sum(0..n) (\k. &k * &(binom(n,k)) * x pow (k - 1) * y pow (n - k)) =
          &n * (x + y) pow (n - 1)`
  (LABEL_TAC "1") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    MAP_EVERY EXISTS_TAC
     [`\x. sum(0..n) (\k. &(binom(n,k)) * x pow k * y pow (n - k))`;
      `x:real`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG];
      ASM_REWRITE_TAC[]] THEN
    REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. sum(0..n)
        (\k. &k * &(k - 1) * &(binom(n,k)) * x pow (k - 2) * y pow (n - k)) =
          &n * &(n - 1) * (x + y) pow (n - 2)`
  (LABEL_TAC "2") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    MAP_EVERY EXISTS_TAC
     [`\x. sum(0..n) (\k. &k * &(binom(n,k)) * x pow (k - 1) * y pow (n - k))`;
      `x:real`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG];
      ASM_REWRITE_TAC[]] THEN
    REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
    REWRITE_TAC[ARITH_RULE `n - 1 - 1 = n - 2`] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `(a - b) pow 2 * x =
    a * (a - &1) * x + (&1 - &2 * b) * a * x + b * b * x`] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_BERNSTEIN] THEN
  SUBGOAL_THEN `sum(0..n) (\k. &k * bernstein n k x) = &n * x` SUBST1_TAC THENL
   [REMOVE_THEN "1" (MP_TAC o SPECL [`x:real`; `&1 - x`]) THEN
    REWRITE_TAC[REAL_SUB_ADD2; REAL_POW_ONE; bernstein; REAL_MUL_RID] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH
     `(k * b * xk * y) * x:real = k * b * (x * xk) * y`] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
    DISJ_CASES_TAC(ARITH_RULE `k = 0 \/ SUC(k - 1) = k`) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
  `sum(0..n) (\k. &k * (&k - &1) * bernstein n k x) = &n * (&n - &1) * x pow 2`
  SUBST1_TAC THENL [ALL_TAC; CONV_TAC REAL_RING] THEN
  REMOVE_THEN "2" (MP_TAC o SPECL [`x:real`; `&1 - x`]) THEN
  REWRITE_TAC[REAL_SUB_ADD2; REAL_POW_ONE; bernstein; REAL_MUL_RID] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[SUM_SING_NUMSEG; REAL_MUL_LZERO] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LE_1; REAL_MUL_ASSOC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `((((k * k1) * b) * xk) * y) * x2:real =
                            k * k1 * b * y * (x2 * xk)`] THEN
  REWRITE_TAC[GSYM REAL_POW_ADD; GSYM REAL_MUL_ASSOC] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (ARITH_RULE `k = 0 \/ k = 1 \/ 1 <= k /\ 2 + k - 2 = k`) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; SUB_REFL; REAL_SUB_REFL] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN REWRITE_TAC[REAL_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* Explicit Bernstein version of 1D Weierstrass approximation theorem        *)
(* ------------------------------------------------------------------------- *)

let BERNSTEIN_WEIERSTRASS = prove
 (`!f e.
      f real_continuous_on real_interval[&0,&1] /\ &0 < e
      ==> ?N. !n x. N <= n /\ x IN real_interval[&0,&1]
                    ==> abs(f x -
                            sum(0..n) (\k. f(&k / &n) * bernstein n k x)) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `real_bounded(IMAGE f (real_interval[&0,&1]))` MP_TAC THENL
   [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL];
    REWRITE_TAC[REAL_BOUNDED_POS; LEFT_IMP_EXISTS_THM; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `M:real` THEN STRIP_TAC] THEN
  SUBGOAL_THEN `f real_uniformly_continuous_on real_interval[&0,&1]`
  MP_TAC THENL
   [ASM_SIMP_TAC[REAL_COMPACT_UNIFORMLY_CONTINUOUS; REAL_COMPACT_INTERVAL];
    REWRITE_TAC[real_uniformly_continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF; IN_REAL_INTERVAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `!n x. 0 < n /\ &0 <= x /\ x <= &1
          ==> abs(f x - sum(0..n) (\k. f(&k / &n) * bernstein n k x))
                <= e / &2 + (&2 * M) / (d pow 2 * &n)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(sum(0..n) (\k. (f x - f(&k / &n)) * bernstein n k x))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG; SUM_LMUL] THEN
      REWRITE_TAC[SUM_BERNSTEIN; REAL_MUL_RID; REAL_LE_REFL];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH lhand SUM_ABS_NUMSEG o lhand o snd) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[BERNSTEIN_POS; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum(0..n) (\k. (e / &2 + &2 * M / d pow 2 * (x - &k / &n) pow 2) *
                     bernstein n k x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[BERNSTEIN_POS] THEN
      SUBGOAL_THEN `&0 <= &k / &n /\ &k / &n <= &1` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT] THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE; MULT_CLAUSES];
        ALL_TAC] THEN
      DISJ_CASES_TAC(REAL_ARITH
        `abs(x - &k / &n) < d \/ d <= abs(x - &k / &n)`)
      THENL
       [MATCH_MP_TAC(REAL_ARITH `x < e /\ &0 <= d ==> x <= e + d`) THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 <= &2 * x <=> &0 <= x`] THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_POW_2; REAL_LE_SQUARE;
                     REAL_LT_IMP_LE];
        MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= d ==> x <= e / &2 + d`) THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH
         `abs(x) <= M /\ abs(y) <= M /\ M * &1 <= M * b / d
          ==> abs(x - y) <= &2 * M / d * b`) THEN
        ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_POW_LT; REAL_LE_RDIV_EQ] THEN
        REWRITE_TAC[REAL_MUL_LID; GSYM REAL_LE_SQUARE_ABS] THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_ADD_RDISTRIB; SUM_ADD_NUMSEG; SUM_LMUL] THEN
      REWRITE_TAC[SUM_BERNSTEIN; REAL_MUL_RID; REAL_LE_LADD] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC; SUM_LMUL] THEN
      REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_OF_NUM_LT; ARITH; REAL_POW_LT;
                   REAL_LT_INV_EQ] THEN
      MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&n pow 2` THEN
      ASM_SIMP_TAC[GSYM SUM_LMUL; REAL_POW_LT; REAL_OF_NUM_LT; REAL_FIELD
        `&0 < n ==> n pow 2 * inv(n) = n`] THEN
      REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_MUL] THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LT; REAL_FIELD
        `&0 < n ==> n * (x - k * inv n) = n * x - k`] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `(x - y:real) pow 2 = (y - x) pow 2`] THEN
      REWRITE_TAC[BERNSTEIN_LEMMA; REAL_ARITH
        `&n * x <= &n <=> &n * x <= &n * &1 * &1`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    MP_TAC(ISPEC `(e / &4 * d pow 2) / (&2 * M)` REAL_ARCH_INV) THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH; REAL_LT_MUL] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_POW_LT; REAL_MUL_LZERO] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
    REWRITE_TAC[REAL_ARITH `(x * &2 * m) * i = (&2 * m) * (i * x)`] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:real`]) THEN ASM_SIMP_TAC[] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 < e /\ k < e / &4 ==> x <= e / &2 + k ==> x < e`) THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> y <= x ==> y < e`)) THEN
    ASM_SIMP_TAC[real_div; REAL_LE_LMUL_EQ; REAL_LT_MUL;
                 REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_MUL; REAL_POW_LT;
                 REAL_OF_NUM_LT; LE_1; REAL_OF_NUM_LE]]);;

(* ------------------------------------------------------------------------- *)
(* General Stone-Weierstrass theorem.                                        *)
(* ------------------------------------------------------------------------- *)

let STONE_WEIERSTRASS_ALT = prove
 (`!(P:(real^N->real)->bool) (s:real^N->bool).
        compact s /\
        (!c. P(\x. c)) /\
        (!f g. P(f) /\ P(g) ==> P(\x. f x + g x)) /\
        (!f g. P(f) /\ P(g) ==> P(\x. f x * g x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y)
               ==> ?f. (!x. x IN s ==> f real_continuous (at x within s)) /\
                       P(f) /\ ~(f x = f y))
        ==> !f e. (!x. x IN s ==> f real_continuous (at x within s)) /\ &0 < e
                  ==> ?g. P(g) /\ !x. x IN s ==> abs(f x - g x) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY ABBREV_TAC
   [`C = \f. !x:real^N. x IN s ==> f real_continuous at x within s`;
    `A = \f. C f /\
             !e. &0 < e
               ==> ?g. P(g) /\ !x:real^N. x IN s ==> abs(f x - g x) < e`] THEN
  SUBGOAL_THEN `!f:real^N->real. C(f) ==> A(f)` MP_TAC THENL
   [ALL_TAC; MAP_EVERY EXPAND_TAC ["A"; "C"] THEN SIMP_TAC[]] THEN
  SUBGOAL_THEN `!c:real. A(\x:real^N. c)` (LABEL_TAC "const") THENL
   [MAP_EVERY EXPAND_TAC ["A"; "C"] THEN X_GEN_TAC `c:real` THEN
    ASM_REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN X_GEN_TAC `e:real` THEN
    DISCH_TAC THEN EXISTS_TAC `(\x. c):real^N->real` THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f g:real^N->real. A(f) /\ A(g) ==> A(\x. f x + g x)`
  (LABEL_TAC "add") THENL
   [MAP_EVERY EXPAND_TAC ["A"; "C"] THEN SIMP_TAC[REAL_CONTINUOUS_ADD] THEN
    MAP_EVERY X_GEN_TAC [`f:real^N->real`; `g:real^N->real`] THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `e / &2` o CONJUNCT2)) THEN
    ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `g':real^N->real` THEN STRIP_TAC THEN
    X_GEN_TAC `f':real^N->real` THEN STRIP_TAC THEN
    EXISTS_TAC `(\x. f' x + g' x):real^N->real` THEN
    ASM_SIMP_TAC[REAL_ARITH
     `abs(f - f') < e / &2 /\ abs(g - g') < e / &2
      ==> abs((f + g) - (f' + g')) < e`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f:real^N->real. A(f) ==> C(f)` (LABEL_TAC "AC") THENL
   [EXPAND_TAC "A" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!f:real^N->real. C(f) ==> real_bounded(IMAGE f s)`
  (LABEL_TAC "bound") THENL
   [GEN_TAC THEN EXPAND_TAC "C" THEN
    REWRITE_TAC[REAL_BOUNDED; GSYM IMAGE_o] THEN
    REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1] THEN
    REWRITE_TAC[GSYM CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; COMPACT_CONTINUOUS_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f g:real^N->real. A(f) /\ A(g) ==> A(\x. f x * g x)`
  (LABEL_TAC "mul") THENL
   [MAP_EVERY X_GEN_TAC [`f:real^N->real`; `g:real^N->real`] THEN
    DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
    MAP_EVERY EXPAND_TAC ["A"; "C"] THEN SIMP_TAC[REAL_CONTINUOUS_MUL] THEN
    REWRITE_TAC[IMP_CONJ] THEN
    MAP_EVERY (DISCH_THEN o LABEL_TAC) ["cf"; "af"; "cg"; "ag"] THEN
    SUBGOAL_THEN
     `real_bounded(IMAGE (f:real^N->real) s) /\
      real_bounded(IMAGE (g:real^N->real) s)`
    MP_TAC THENL
     [ASM_SIMP_TAC[]; REWRITE_TAC[REAL_BOUNDED_POS_LT; FORALL_IN_IMAGE]] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `Bf:real` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `Bg:real` STRIP_ASSUME_TAC)) THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "ag" (MP_TAC o SPEC `e / &2 / Bf`) THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `g':real^N->real` THEN STRIP_TAC THEN
    REMOVE_THEN "af" (MP_TAC o SPEC `e / &2 / (Bg + e / &2 / Bf)`) THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; REAL_LT_ADD] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':real^N->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(\x. f'(x) * g'(x)):real^N->real` THEN
    ASM_SIMP_TAC[REAL_ARITH
     `f * g - f' * g':real = f * (g - g') + g' * (f - f')`] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `e = Bf * e / &2 / Bf +
                      (Bg + e / &2 / Bf) * e / &2 / (Bg + e / &2 / Bf)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a = e / &2 /\ b = e / &2 ==> e = a + b`) THEN
      CONJ_TAC THEN MAP_EVERY MATCH_MP_TAC [REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_ADD; REAL_HALF];
      MATCH_MP_TAC(REAL_ARITH
       `abs a < c /\ abs b < d ==> abs(a + b) < c + d`) THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!g. abs(g) < Bg /\ abs(g - g') < e ==> abs(g') < Bg + e`) THEN
      EXISTS_TAC `(g:real^N->real) x` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN s /\ y IN s /\ ~(x = y)
          ==> ?f:real^N->real. A(f) /\ ~(f x = f y)`
  (LABEL_TAC "sep") THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    MAP_EVERY EXPAND_TAC ["A"; "C"] THEN
    ASM_MESON_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f. A(f) ==> A(\x:real^N. abs(f x))` (LABEL_TAC "abs") THENL
   [SUBGOAL_THEN `!f. A(f) /\ (!x. x IN s ==> abs(f x) <= &1 / &4)
                      ==> A(\x:real^N. abs(f x))`
    ASSUME_TAC THENL
     [ALL_TAC;
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `real_bounded(IMAGE (f:real^N->real) s)` MP_TAC THENL
       [ASM_SIMP_TAC[]; REWRITE_TAC[REAL_BOUNDED_POS_LT; FORALL_IN_IMAGE]] THEN
      DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `A(\x:real^N. (&4 * B) * abs(inv(&4 * B) * f x)):bool`
      MP_TAC THENL
       [USE_THEN "mul" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_ABS_MUL] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < B ==> abs(B) = B`;
                     REAL_LT_INV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_LT_MUL;
                     REAL_OF_NUM_LT; ARITH; REAL_MUL_ASSOC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_SIMP_TAC[REAL_MUL_LID; REAL_LT_IMP_LE];
        ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 < B ==> abs(B) = B`;
                     REAL_LT_INV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
        ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_MUL_LID;
                     REAL_ARITH `&0 < B ==> ~(&4 * B = &0)`]]] THEN
    X_GEN_TAC `f:real^N->real` THEN MAP_EVERY EXPAND_TAC ["A"; "C"] THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
     [DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT1) THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT; o_DEF]
        REAL_CONTINUOUS_WITHIN_COMPOSE) THEN
      REWRITE_TAC[real_continuous_withinreal] THEN
      MESON_TAC[ARITH_RULE `abs(x - y) < d ==> abs(abs x - abs y) < d`];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(fun t -> X_GEN_TAC `e:real` THEN DISCH_TAC THEN MP_TAC t) THEN
    DISCH_THEN(MP_TAC o SPEC `min (e / &2) (&1 / &4)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_MIN; FORALL_AND_THM;
                TAUT `(a ==> b /\ c) <=> (a ==> b) /\ (a ==> c)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N->real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`\x. abs(x - &1 / &2)`; `e / &2`]
     BERNSTEIN_WEIERSTRASS) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[real_continuous_on; REAL_HALF] THEN
      MESON_TAC[ARITH_RULE
       `abs(x - y) < d ==> abs(abs(x - a) - abs(y - a)) < d`];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
    REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
    EXISTS_TAC `\x:real^N. sum(0..n) (\k. abs(&k / &n - &1 / &2) *
                                          bernstein n k (&1 / &2 + p x))` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `!m c z. P(\x:real^N.
            sum(0..m) (\k. c k * bernstein (z m) k (&1 / &2 + p x)))`
       (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN
       `!m k. P(\x:real^N. bernstein m k (&1 / &2 + p x))`
      ASSUME_TAC THENL
       [ALL_TAC; INDUCT_TAC THEN ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0]] THEN
      REPEAT GEN_TAC THEN REWRITE_TAC[bernstein] THEN
      REWRITE_TAC[REAL_ARITH `&1 - (&1 / &2 + p) = &1 / &2 + -- &1 * p`] THEN
      REPEAT(FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]) THEN
      SUBGOAL_THEN
       `!f:real^N->real k. P(f) ==> P(\x. f(x) pow k)`
       (fun th -> ASM_SIMP_TAC[th]) THEN
      GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[real_pow];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
       `!p. abs(abs(p x) - s) < e / &2 /\
            abs(f x - p x) < e / &2
            ==> abs(abs(f x) - s) < e`) THEN
      EXISTS_TAC `p:real^N->real` THEN ASM_SIMP_TAC[] THEN
      GEN_REWRITE_TAC (PAT_CONV `\x. abs(abs x - a) < e`)
        [REAL_ARITH `x = (&1 / &2 + x) - &1 / &2`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!f. abs(f) <= &1 / &4 /\ abs(f - p) < &1 / &4
            ==> &0 <= &1 / &2 + p /\ &1 / &2 + p <= &1`) THEN
      EXISTS_TAC `(f:real^N->real) x` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f:real^N->real g. A(f) /\ A(g) ==> A(\x. max (f x) (g x))`
  (LABEL_TAC "max") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ARITH
     `max a b = inv(&2) * (a + b + abs(a + -- &1 * b))`] THEN
    REPEAT(FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!f:real^N->real g. A(f) /\ A(g) ==> A(\x. min (f x) (g x))`
  (LABEL_TAC "min") THENL
   [ASM_SIMP_TAC[REAL_ARITH `min a b = -- &1 * (max(-- &1 * a) (-- &1 * b))`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. FINITE t /\ (!f. f IN t ==> A(f)) ==> A(\x:real^N. sup {f(x) | f IN t})`
  (LABEL_TAC "sup") THENL
   [REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC[FORALL_IN_INSERT; SIMPLE_IMAGE; IMAGE_CLAUSES] THEN
    ASM_SIMP_TAC[SUP_INSERT_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [`f:real^N->real`; `t:(real^N->real)->bool`] THEN
    ASM_CASES_TAC `t:(real^N->real)->bool = {}` THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. FINITE t /\ (!f. f IN t ==> A(f)) ==> A(\x:real^N. inf {f(x) | f IN t})`
  (LABEL_TAC "inf") THENL
   [REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC[FORALL_IN_INSERT; SIMPLE_IMAGE; IMAGE_CLAUSES] THEN
    ASM_SIMP_TAC[INF_INSERT_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [`f:real^N->real`; `t:(real^N->real)->bool`] THEN
    ASM_CASES_TAC `t:(real^N->real)->bool = {}` THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:real^N->real e.
      C(f) /\ &0 < e ==> ?g. A(g) /\ !x. x IN s ==> abs(f x - g x) < e`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `f:real^N->real` THEN DISCH_TAC THEN EXPAND_TAC "A" THEN
    CONJ_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`f:real^N->real`; `e / &2`]) THEN
    ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `h:real^N->real` THEN EXPAND_TAC "A" THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_MESON_TAC[REAL_ARITH
     `abs(f - h) < e / &2 /\ abs(h - g) < e / &2 ==> abs(f - g) < e`]] THEN
  MAP_EVERY X_GEN_TAC [`f:real^N->real`; `e:real`] THEN EXPAND_TAC "C" THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!x y. x IN s /\ y IN s
          ==> ?h:real^N->real. A(h) /\ h(x) = f(x) /\ h(y) = f(y)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `y:real^N = x` THENL
     [EXISTS_TAC `\z:real^N. (f:real^N->real) x` THEN ASM_SIMP_TAC[];
      SUBGOAL_THEN `?h:real^N->real. A(h) /\ ~(h x = h y)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `\z. (f y - f x) / (h y - h x) * (h:real^N->real)(z) +
                      (f x - (f y - f x) / (h y - h x) * h(x))` THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `~((h:real^N->real) x = h y)` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f2:real^N->real^N->real^N->real` THEN DISCH_TAC THEN
  ABBREV_TAC `G = \x y.
    {z | z IN s /\ (f2:real^N->real^N->real^N->real) x y z < f(z) + e}` THEN
  SUBGOAL_THEN `!x y:real^N. x IN s /\ y IN s ==> x IN G x y /\ y IN G x y`
  ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[REAL_LT_ADDR];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s ==> ?f1. A(f1) /\ f1 x = f x /\
                        !y:real^N. y IN s ==> f1 y < f y + e`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o
     GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL_SUBTOPOLOGY]) THEN
    DISCH_THEN(MP_TAC o SPEC
     `{(G:real^N->real^N->real^N->bool) x y | y IN s}`) THEN
    REWRITE_TAC[SIMPLE_IMAGE; UNIONS_IMAGE; FORALL_IN_IMAGE; ETA_AX] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      EXPAND_TAC "G" THEN REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`lift o (\z:real^N. f2 (x:real^N) (w:real^N) z - f z)`;
                     `s:real^N->bool`;
                     `{x:real^1 | x$1 < e}`] CONTINUOUS_OPEN_IN_PREIMAGE) THEN
      REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; IN_ELIM_THM] THEN
      REWRITE_TAC[GSYM drop; LIFT_DROP; o_DEF] THEN
      REWRITE_TAC[LIFT_SUB; GSYM REAL_CONTINUOUS_CONTINUOUS1;
                  REAL_ARITH `x < y + e <=> x - y < e`] THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      ONCE_REWRITE_TAC[GSYM o_DEF] THEN
      REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS1; ETA_AX] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
    REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE; UNIONS_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\z:real^N. inf {f2 (x:real^N) (y:real^N) z | y IN t}` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `x = min x x`] THEN
      REWRITE_TAC[REAL_MIN_INF; INSERT_AC] THEN AP_TERM_TAC THEN ASM SET_TAC[];
      REMOVE_THEN "inf" (MP_TAC o SPEC
       `IMAGE (\y z. (f2:real^N->real^N->real^N->real) x y z) t`) THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[SIMPLE_IMAGE; ETA_AX] THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM IMAGE_o; o_DEF];
      SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_INF_LT_FINITE; SIMPLE_IMAGE;
                   FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      UNDISCH_TAC
       `s SUBSET {y:real^N | ?z:real^N. z IN t /\ y IN G (x:real^N) z}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "G" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `f1:real^N->real^N->real` THEN DISCH_TAC] THEN
  ABBREV_TAC `H = \x:real^N. {z:real^N | z IN s /\ f z - e < f1 x z}` THEN
  SUBGOAL_THEN `!x:real^N. x IN s ==> x IN (H x)` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[REAL_ARITH `x - e < x <=> &0 < e`];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o
  GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL_SUBTOPOLOGY]) THEN
  DISCH_THEN(MP_TAC o SPEC
   `{(H:real^N->real^N->bool) x | x IN s}`) THEN
  REWRITE_TAC[SIMPLE_IMAGE; UNIONS_IMAGE; FORALL_IN_IMAGE; ETA_AX] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN EXPAND_TAC "H" THEN
    REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`lift o (\z:real^N. f z - f1 (x:real^N) z)`;
                   `s:real^N->bool`;
                   `{x:real^1 | x$1 < e}`] CONTINUOUS_OPEN_IN_PREIMAGE) THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; IN_ELIM_THM] THEN
    REWRITE_TAC[GSYM drop; LIFT_DROP; o_DEF] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
     [REAL_ARITH `x - y < z <=> x - z < y`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[LIFT_SUB; GSYM REAL_CONTINUOUS_CONTINUOUS1;
                REAL_ARITH `x < y + e <=> x - y < e`] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS1; ETA_AX] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE; UNIONS_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z:real^N. sup {f1 (x:real^N) z | x IN t}` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REMOVE_THEN "sup" (MP_TAC o SPEC `IMAGE (f1:real^N->real^N->real) t`) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[SIMPLE_IMAGE; ETA_AX] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SIMPLE_IMAGE; REAL_ARITH
   `abs(f - s) < e <=> f - e < s /\ s < f + e`] THEN
  ASM_SIMP_TAC[REAL_SUP_LT_FINITE; REAL_LT_SUP_FINITE;
               FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  UNDISCH_TAC `s SUBSET {y:real^N | ?x:real^N. x IN t /\ y IN H x}` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "H" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]);;

let STONE_WEIERSTRASS = prove
 (`!(P:(real^N->real)->bool) (s:real^N->bool).
        compact s /\
        (!f. P(f) ==> !x. x IN s ==> f real_continuous (at x within s)) /\
        (!c. P(\x. c)) /\
        (!f g. P(f) /\ P(g) ==> P(\x. f x + g x)) /\
        (!f g. P(f) /\ P(g) ==> P(\x. f x * g x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> ?f. P(f) /\ ~(f x = f y))
        ==> !f e. (!x. x IN s ==> f real_continuous (at x within s)) /\ &0 < e
                  ==> ?g. P(g) /\ !x. x IN s ==> abs(f x - g x) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC STONE_WEIERSTRASS_ALT THEN ASM_SIMP_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[]);;
