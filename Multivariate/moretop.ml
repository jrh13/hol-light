(* ========================================================================= *)
(* Additional topology theory.                                               *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2013                       *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* Injective map into R is also an open map w.r.t. the universe, and this    *)
(* is actually an implication in both directions for an interval. Compare    *)
(* the local form in INJECTIVE_INTO_1D_IMP_OPEN_MAP (not a bi-implication).  *)
(* ------------------------------------------------------------------------- *)

let INJECTIVE_EQ_1D_OPEN_MAP_UNIV = prove
 (`!f:real^1->real^1 s.
        f continuous_on s /\ is_interval s
        ==>  ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
              (!t. open t /\ t SUBSET s ==> open(IMAGE f t)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[BALL_1] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (f:real^1->real^1)
                      (segment (x - lift d,x + lift d))` THEN
    MP_TAC(ISPECL
     [`f:real^1->real^1`; `x - lift d`; `x + lift d`]
     CONTINUOUS_INJECTIVE_IMAGE_OPEN_SEGMENT_1) THEN
    REWRITE_TAC[SEGMENT_1; DROP_ADD; DROP_SUB; LIFT_DROP] THEN
    ASM_CASES_TAC `drop x - d <= drop x + d` THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM SEGMENT_1];
      ASM_REAL_ARITH_TAC] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[SUBSET; CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC[OPEN_SEGMENT_1];
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTERVAL_1] THEN
      REWRITE_TAC[DROP_ADD; DROP_SUB; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC IMAGE_SUBSET THEN
      ASM_MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET_TRANS]];
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `x:real^1`; `y:real^1`]
        CONTINUOUS_IVT_LOCAL_EXTREMUM) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT_EQ; IS_INTERVAL_CONVEX_1;
                    CONTINUOUS_ON_SUBSET];
      DISCH_THEN(X_CHOOSE_TAC `z:real^1`) THEN
      FIRST_ASSUM(MP_TAC o SPEC `segment(x:real^1,y)`) THEN
      REWRITE_TAC[OPEN_SEGMENT_1; NOT_IMP] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT; IS_INTERVAL_CONVEX_1;
                      SUBSET_TRANS; SEGMENT_OPEN_SUBSET_CLOSED];
        FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
        REWRITE_TAC[open_def; FORALL_IN_IMAGE] THEN
        DISCH_THEN(MP_TAC o SPEC `z:real^1`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `e:real`
         (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        FIRST_X_ASSUM DISJ_CASES_TAC THENL
         [DISCH_THEN(MP_TAC o SPEC `(f:real^1->real^1) z + lift(e / &2)`);
          DISCH_THEN(MP_TAC o SPEC `(f:real^1->real^1) z - lift(e / &2)`)] THEN
        ASM_REWRITE_TAC[NORM_ARITH `dist(a + b:real^N,a) = norm b`;
                        NORM_ARITH `dist(a - b:real^N,a) = norm b`; NORM_LIFT;
                        REAL_ARITH `abs(e / &2) < e <=> &0 < e`] THEN
        REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `w:real^1` (STRIP_ASSUME_TAC o GSYM)) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `w:real^1`) THEN
        ASM_SIMP_TAC[REWRITE_RULE[SUBSET] SEGMENT_OPEN_SUBSET_CLOSED] THEN
        REWRITE_TAC[DROP_ADD; DROP_SUB; LIFT_DROP] THEN
        ASM_REAL_ARITH_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* Nonsurjectivity of differentiable map from lower-dimensional sphere.      *)
(* ------------------------------------------------------------------------- *)

let NONSURJECTIVE_DIFFERENTIABLE_SPHEREMAP_LOWDIM = prove
 (`!f:real^N->real^N s t.
      subspace s /\ subspace t /\ dim s < dim t /\ s SUBSET t /\
      f differentiable_on sphere(vec 0,&1) INTER s
      ==> ~(IMAGE f (sphere(vec 0,&1) INTER s) = sphere(vec 0,&1) INTER t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `(g:real^N->real^N) =
    \x. norm(x) % (f:real^N->real^N)(inv(norm x) % x)` THEN
  SUBGOAL_THEN
   `(g:real^N->real^N) differentiable_on s DELETE (vec 0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN MATCH_MP_TAC DIFFERENTIABLE_ON_MUL THEN
    SIMP_TAC[o_DEF; DIFFERENTIABLE_ON_NORM; IN_DELETE] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC DIFFERENTIABLE_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_ON_MUL THEN
      REWRITE_TAC[DIFFERENTIABLE_ON_ID] THEN
      SUBGOAL_THEN
       `lift o (\x:real^N. inv(norm x)) =
        (lift o inv o drop) o (\x. lift(norm x))`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC DIFFERENTIABLE_ON_COMPOSE THEN
      SIMP_TAC[DIFFERENTIABLE_ON_NORM; IN_DELETE] THEN
      MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
      SIMP_TAC[FORALL_IN_IMAGE; IN_DELETE; GSYM REAL_DIFFERENTIABLE_AT] THEN
      REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_INV_ATREAL THEN
      ASM_REWRITE_TAC[REAL_DIFFERENTIABLE_ID; NORM_EQ_0];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          DIFFERENTIABLE_ON_SUBSET)) THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; IN_INTER;
                   SUBSPACE_MUL; NORM_MUL; IN_DELETE] THEN
      SIMP_TAC[REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (g:real^N->real^N) (s DELETE vec 0) = t DELETE (vec 0)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^N->real^N) (sphere (vec 0,&1) INTER s) =
                 sphere (vec 0,&1) INTER t` THEN
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE;
                IN_INTER; IN_SPHERE_0] THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[IN_IMAGE; IN_INTER; IN_SPHERE_0] THEN
    SIMP_TAC[IN_DELETE; VECTOR_MUL_EQ_0; NORM_EQ_0] THEN
    MATCH_MP_TAC(TAUT
     `(p ==> r) /\ (p ==> q ==> s) ==> p /\ q ==> r /\ s`) THEN
    CONJ_TAC THENL [ALL_TAC; DISCH_TAC] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      MP_TAC(SPEC `inv(norm x) % x:real^N` th)) THEN
    ASM_SIMP_TAC[SUBSPACE_MUL; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM;
                 REAL_MUL_LINV; NORM_EQ_0;
                 NORM_ARITH `norm x = &1 ==> ~(x:real^N = vec 0)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `norm(x:real^N) % y:real^N` THEN
    ASM_SIMP_TAC[SUBSPACE_MUL; NORM_MUL; REAL_ABS_NORM; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; NORM_EQ_0] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_EQ_0; NORM_EQ_0] THEN
    ASM_SIMP_TAC[NORM_ARITH `norm x = &1 ==> ~(x:real^N = vec 0)`] THEN
    UNDISCH_THEN `inv(norm x) % x = (f:real^N->real^N) y`
     (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; NORM_EQ_0] THEN
    REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `(:real^N)`]
        DIM_SUBSPACE_ORTHOGONAL_TO_VECTORS) THEN
  ASM_REWRITE_TAC[SUBSPACE_UNIV; DIM_UNIV; IN_UNIV; SUBSET_UNIV] THEN
  ABBREV_TAC `t' = {y:real^N | !x. x IN t ==> orthogonal x y}` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `subspace(t':real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN REWRITE_TAC[SUBSPACE_ORTHOGONAL_TO_VECTORS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?fst snd. linear fst /\ linear snd /\
              (!z. fst(z) IN t /\ snd z IN t' /\ fst z + snd z = z) /\
              (!x y:real^N. x IN t /\ y IN t'
                            ==> fst(x + y) = x /\ snd(x + y) = y)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^N->bool` ORTHOGONAL_SUBSPACE_DECOMP_EXISTS) THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `fst:real^N->real^N` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `snd:real^N->real^N` THEN
    DISCH_THEN(MP_TAC o GSYM) THEN
    ASM_SIMP_TAC[SPAN_OF_SUBSPACE; FORALL_AND_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `r /\ (r ==> p /\ q /\ s) ==> p /\ q /\ r /\ s`) THEN
    CONJ_TAC THENL
     [EXPAND_TAC "t'" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[ORTHOGONAL_SYM];
      DISCH_TAC] THEN
    MATCH_MP_TAC(TAUT `r /\ (r ==> p /\ q) ==> p /\ q /\ r`) THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      MATCH_MP_TAC ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE THEN
      MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `t':real^N->bool`] THEN
      ASM_SIMP_TAC[SPAN_OF_SUBSPACE] THEN ASM SET_TAC[];
      DISCH_TAC] THEN
    REWRITE_TAC[linear] THEN
    MATCH_MP_TAC(TAUT `(p /\ r) /\ (q /\ s) ==> (p /\ q) /\ (r /\ s)`) THEN
    REWRITE_TAC[AND_FORALL_THM] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `t':real^N->bool`] THEN
    ASM_SIMP_TAC[SPAN_OF_SUBSPACE; SUBSPACE_ADD; SUBSPACE_MUL] THEN
    (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    ASM_REWRITE_TAC[GSYM VECTOR_ADD_LDISTRIB] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `(x + y) + (x' + y'):real^N = (x + x') + (y + y')`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x:real^N. (g:real^N->real^N)(fst x) + snd x`;
    `{x + y:real^N | x IN (s DELETE vec 0) /\ y IN t'}`]
      NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE) THEN
  REWRITE_TAC[LE_REFL; NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_LOWDIM THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `t':real^N->bool`] DIM_SUMS_INTER) THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `t' + t = n ==> s < t /\ d' <= d /\ i = 0
         ==> d + i = s + t' ==> d' < n`)) THEN
    ASM_REWRITE_TAC[DIM_EQ_0] THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIM_SUBSET THEN SET_TAC[]; EXPAND_TAC "t'"] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_SING; IN_ELIM_THM] THEN
    ASM_MESON_TAC[SUBSET; ORTHOGONAL_REFL];
    MATCH_MP_TAC DIFFERENTIABLE_ON_ADD THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_ON_LINEAR] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC DIFFERENTIABLE_ON_COMPOSE THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_ON_LINEAR] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      DIFFERENTIABLE_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN ASM_SIMP_TAC[IN_DELETE];
    SUBGOAL_THEN
     `~negligible {x + y | x IN IMAGE (g:real^N->real^N) (s DELETE vec 0) /\
                           y IN t'}`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `negligible(t':real^N->bool)` MP_TAC THENL
       [MATCH_MP_TAC NEGLIGIBLE_LOWDIM THEN ASM_ARITH_TAC;
        REWRITE_TAC[TAUT `p ==> ~q <=> ~(p /\ q)`]] THEN
      REWRITE_TAC[GSYM NEGLIGIBLE_UNION_EQ] THEN
      MP_TAC NOT_NEGLIGIBLE_UNIV THEN MATCH_MP_TAC EQ_IMP THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_UNION; IN_UNIV; IN_ELIM_THM; IN_DELETE] THEN
      X_GEN_TAC `z:real^N` THEN
      REWRITE_TAC[TAUT `p \/ q <=> ~p ==> q`] THEN DISCH_TAC THEN
      EXISTS_TAC `(fst:real^N->real^N) z` THEN
      EXISTS_TAC `(snd:real^N->real^N) z` THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[VECTOR_ADD_LID];
      REWRITE_TAC[CONTRAPOS_THM] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                  FORALL_IN_IMAGE; IN_DELETE] THEN
      X_GEN_TAC `x:real^N` THEN REPEAT DISCH_TAC THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x + y:real^N` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN ASM_SIMP_TAC[] THEN ASM
      SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Map f:S^m->S^n for m < n is nullhomotopic.                                *)
(* ------------------------------------------------------------------------- *)

let INESSENTIAL_SPHEREMAP_LOWDIM_GEN = prove
 (`!f:real^M->real^N s t.
     convex s /\ bounded s /\ convex t /\ bounded t /\ aff_dim s < aff_dim t /\
     f continuous_on relative_frontier s /\
     IMAGE f (relative_frontier s) SUBSET (relative_frontier t)
     ==> ?c. homotopic_with (\z. T)
                (subtopology euclidean (relative_frontier s),
                 subtopology euclidean (relative_frontier t)) f (\x. c)`,
  let lemma1 = prove
   (`!f:real^N->real^N s t.
          subspace s /\ subspace t /\ dim s < dim t /\ s SUBSET t /\
          f continuous_on sphere(vec 0,&1) INTER s /\
          IMAGE f (sphere(vec 0,&1) INTER s) SUBSET sphere(vec 0,&1) INTER t
          ==> ?c. homotopic_with (\x. T)
                    (subtopology euclidean (sphere(vec 0,&1) INTER s),
                     subtopology euclidean (sphere(vec 0,&1) INTER t))
                     f (\x. c)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^N->real^N`; `sphere(vec 0:real^N,&1) INTER s`;
                   `&1 / &2`; `t:real^N->bool`;]
          STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION_SUBSPACE) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[COMPACT_INTER_CLOSED; COMPACT_SPHERE; CLOSED_SUBSPACE] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[SUBSET; FORALL_IN_IMAGE]] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `!x. x IN sphere(vec 0,&1) INTER s ==> ~((g:real^N->real^N) x = vec 0)`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_SPHERE_0] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_SPHERE_0]) THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INTER; IN_SPHERE_0] THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^N->real^N) differentiable_on
                  sphere(vec 0,&1) INTER s`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[DIFFERENTIABLE_ON_VECTOR_POLYNOMIAL_FUNCTION]; ALL_TAC] THEN
    ABBREV_TAC `(h:real^N->real^N) = \x. inv(norm(g x)) % g x` THEN
    SUBGOAL_THEN
     `!x. x IN sphere(vec 0,&1) INTER s
          ==> (h:real^N->real^N) x IN sphere(vec 0,&1) INTER t`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN
      ASM_SIMP_TAC[SUBSPACE_MUL; IN_INTER; IN_SPHERE_0; NORM_MUL] THEN
      REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0; GSYM IN_SPHERE_0];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(h:real^N->real^N) differentiable_on sphere(vec 0,&1) INTER s`
    ASSUME_TAC THENL
     [EXPAND_TAC "h" THEN MATCH_MP_TAC DIFFERENTIABLE_ON_MUL THEN
      ASM_SIMP_TAC[DIFFERENTIABLE_ON_VECTOR_POLYNOMIAL_FUNCTION; o_DEF] THEN
      SUBGOAL_THEN
       `(\x. lift(inv(norm((g:real^N->real^N) x)))) =
        (lift o inv o drop) o (\x. lift(norm x)) o (g:real^N->real^N)`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC DIFFERENTIABLE_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_ON_COMPOSE THEN
        ASM_SIMP_TAC[DIFFERENTIABLE_ON_VECTOR_POLYNOMIAL_FUNCTION] THEN
        MATCH_MP_TAC DIFFERENTIABLE_ON_NORM THEN
        ASM_REWRITE_TAC[SET_RULE
         `~(z IN IMAGE f s) <=> !x. x IN s ==> ~(f x = z)`];
        MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
        REWRITE_TAC[GSYM REAL_DIFFERENTIABLE_AT] THEN
        REWRITE_TAC[FORALL_IN_IMAGE; IN_SPHERE_0] THEN
        X_GEN_TAC `x:real^N` THEN
        ASM_CASES_TAC `x:real^N = vec 0` THEN
        ASM_REWRITE_TAC[NORM_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN DISCH_TAC THEN
        REWRITE_TAC[GSYM REAL_DIFFERENTIABLE_AT; o_THM] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
        MATCH_MP_TAC REAL_DIFFERENTIABLE_INV_ATREAL THEN
        ASM_SIMP_TAC[REAL_DIFFERENTIABLE_ID; NORM_EQ_0; IN_SPHERE_0]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?c. homotopic_with (\z. T)
             (subtopology euclidean (sphere(vec 0,&1) INTER s),
              subtopology euclidean (sphere(vec 0,&1) INTER t))
             (h:real^N->real^N) (\x. c)`
    MP_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOMOTOPIC_WITH_TRANS) THEN
      SUBGOAL_THEN
       `homotopic_with (\z. T)
         (subtopology euclidean (sphere(vec 0:real^N,&1) INTER s),
          subtopology euclidean (t DELETE (vec 0:real^N)))
         f g`
      MP_TAC THENL
       [MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN
        ASM_SIMP_TAC[CONTINUOUS_ON_VECTOR_POLYNOMIAL_FUNCTION] THEN
        X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[SET_RULE
          `s SUBSET t DELETE v <=> s SUBSET t /\ ~(v IN s)`] THEN
        CONJ_TAC THENL
         [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
          ASM_SIMP_TAC[SUBSPACE_IMP_CONVEX] THEN ASM SET_TAC[];
          DISCH_THEN(MP_TAC o MATCH_MP SEGMENT_BOUND) THEN
          SUBGOAL_THEN
           `(f:real^N->real^N) x IN sphere(vec 0,&1) /\
            norm(f x - g x) < &1/ &2`
          MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[IN_SPHERE_0] THEN CONV_TAC NORM_ARITH];
        DISCH_THEN(MP_TAC o
          ISPECL [`\y:real^N. inv(norm y) % y`;
                  `sphere(vec 0:real^N,&1) INTER t`] o
          MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
          HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT)) THEN
        ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
            REWRITE_TAC[o_DEF; CONTINUOUS_ON_ID] THEN
            MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
            SIMP_TAC[IN_DELETE; NORM_EQ_0] THEN
            REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM];
            REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_INTER] THEN
            ASM_SIMP_TAC[SUBSPACE_MUL; IN_SPHERE_0; NORM_MUL;
                         REAL_ABS_MUL] THEN
            SIMP_TAC[REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0]];
          MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
          RULE_ASSUM_TAC(REWRITE_RULE
           [SUBSET; IN_INTER; FORALL_IN_IMAGE; IN_SPHERE_0]) THEN
          ASM_SIMP_TAC[IN_SPHERE_0; IN_INTER;
                       REAL_INV_1; VECTOR_MUL_LID]]]] THEN
    SUBGOAL_THEN
     `?c. c IN (sphere(vec 0,&1) INTER t) DIFF
               (IMAGE (h:real^N->real^N) (sphere(vec 0,&1) INTER s))`
    MP_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `t SUBSET s /\ ~(t = s) ==> ?a. a IN s DIFF t`) THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        MATCH_MP_TAC NONSURJECTIVE_DIFFERENTIABLE_SPHEREMAP_LOWDIM] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_INTER; IN_DIFF; IN_IMAGE] THEN
      REWRITE_TAC[SET_RULE
       `~(?x. P x /\ x IN s /\ x IN t) <=>
        (!x. x IN s INTER t ==> ~(P x))`] THEN
      X_GEN_TAC `c:real^N` THEN STRIP_TAC] THEN
    EXISTS_TAC `--c:real^N` THEN
    SUBGOAL_THEN
     `homotopic_with (\z. T)
       (subtopology euclidean (sphere(vec 0:real^N,&1) INTER s),
        subtopology euclidean (t DELETE (vec 0:real^N)))
       h (\x. --c)`
    MP_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN
      ASM_SIMP_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_ON; CONTINUOUS_ON_CONST] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[SET_RULE
        `s SUBSET t DELETE v <=> s SUBSET t /\ ~(v IN s)`] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
        ASM_SIMP_TAC[SUBSPACE_IMP_CONVEX; INSERT_SUBSET; SUBSPACE_NEG] THEN
        ASM SET_TAC[];
        DISCH_TAC THEN MP_TAC(ISPECL
         [`(h:real^N->real^N) x`; `vec 0:real^N`; `--c:real^N`]
         MIDPOINT_BETWEEN) THEN
        ASM_REWRITE_TAC[BETWEEN_IN_SEGMENT; DIST_0; NORM_NEG] THEN
        SUBGOAL_THEN `((h:real^N->real^N) x) IN sphere(vec 0,&1) /\
                      (c:real^N) IN sphere(vec 0,&1)`
        MP_TAC THENL [ASM SET_TAC[]; SIMP_TAC[IN_SPHERE_0]] THEN
        STRIP_TAC THEN REWRITE_TAC[midpoint; VECTOR_ARITH
         `vec 0:real^N = inv(&2) % (x + --y) <=> x = y`] THEN
        ASM SET_TAC[]];
      DISCH_THEN(MP_TAC o
        ISPECL [`\y:real^N. inv(norm y) % y`;
                `sphere(vec 0:real^N,&1) INTER t`] o
        MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT)) THEN
      ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
          REWRITE_TAC[o_DEF; CONTINUOUS_ON_ID] THEN
          MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
          SIMP_TAC[IN_DELETE; NORM_EQ_0] THEN
          REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_INTER] THEN
          ASM_SIMP_TAC[SUBSPACE_MUL; IN_SPHERE_0; NORM_MUL; REAL_ABS_MUL] THEN
          SIMP_TAC[REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0]];
        MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
        RULE_ASSUM_TAC(REWRITE_RULE
         [SUBSET; IN_INTER; FORALL_IN_IMAGE; IN_SPHERE_0]) THEN
        ASM_SIMP_TAC[IN_SPHERE_0; IN_INTER; REAL_INV_1; VECTOR_MUL_LID;
                     NORM_NEG]]]) in
  let lemma2 = prove
   (`!s:real^M->bool u:real^N->bool.
          bounded s /\ convex s /\ subspace u /\ aff_dim s <= &(dim u)
          ==> ?t. subspace t /\ t SUBSET u /\
                  (~(s = {}) ==> aff_dim t = aff_dim s) /\
                  (relative_frontier s) homeomorphic
                  (sphere(vec 0,&1) INTER t)`,
    REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THENL
     [STRIP_TAC THEN EXISTS_TAC `{vec 0:real^N}` THEN
      ASM_REWRITE_TAC[SUBSPACE_TRIVIAL; RELATIVE_FRONTIER_EMPTY] THEN
      ASM_SIMP_TAC[HOMEOMORPHIC_EMPTY;
                   SET_RULE `s INTER {a} = {} <=> ~(a IN s)`;
                   IN_SPHERE_0; NORM_0; SING_SUBSET; SUBSPACE_0] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      FIRST_X_ASSUM(X_CHOOSE_THEN `a:real^M` MP_TAC o
          GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      GEOM_ORIGIN_TAC `a:real^M` THEN
      SIMP_TAC[AFF_DIM_DIM_0; HULL_INC; INT_OF_NUM_LE; GSYM DIM_UNIV] THEN
      REPEAT STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CHOOSE_SUBSPACE_OF_SUBSPACE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN
    ASM_SIMP_TAC[SPAN_OF_SUBSPACE; AFF_DIM_DIM_SUBSPACE; INT_OF_NUM_EQ] THEN
    STRIP_TAC THEN
    TRANS_TAC HOMEOMORPHIC_TRANS
     `relative_frontier(ball(vec 0:real^N,&1) INTER t)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
      ASM_SIMP_TAC[CONVEX_INTER; BOUNDED_INTER; BOUNDED_BALL;
                   SUBSPACE_IMP_CONVEX; CONVEX_BALL] THEN
      ONCE_REWRITE_TAC[INTER_COMM] THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBSPACE_0) THEN
      SUBGOAL_THEN `~(t INTER ball(vec 0:real^N,&1) = {})` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^N` THEN
        ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; REAL_LT_01];
        ASM_SIMP_TAC[AFF_DIM_CONVEX_INTER_OPEN; OPEN_BALL;
                     SUBSPACE_IMP_CONVEX] THEN
        ASM_SIMP_TAC[AFF_DIM_DIM_0; HULL_INC]];
      MATCH_MP_TAC(MESON[HOMEOMORPHIC_REFL] `s = t ==> s homeomorphic t`) THEN
      SIMP_TAC[GSYM FRONTIER_BALL; REAL_LT_01] THEN
      MATCH_MP_TAC RELATIVE_FRONTIER_CONVEX_INTER_AFFINE THEN
      ASM_SIMP_TAC[CONVEX_BALL; SUBSPACE_IMP_AFFINE;
                   GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `vec 0:real^N` THEN
      ASM_SIMP_TAC[CENTRE_IN_BALL; INTERIOR_OPEN; OPEN_BALL;
                   SUBSPACE_0; IN_INTER; REAL_LT_01]]) in
    ONCE_REWRITE_TAC[MESON[] `(!a b c. P a b c) <=> (!b c a. P a b c)`] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
    REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC `s:real^M->bool = {}` THENL
     [ASM_SIMP_TAC[HOMOTOPIC_WITH_EUCLIDEAN_ALT; RELATIVE_FRONTIER_EMPTY;
       PCROSS_EMPTY; NOT_IN_EMPTY; IMAGE_CLAUSES; CONTINUOUS_ON_EMPTY];
      ALL_TAC] THEN
    ASM_CASES_TAC `t:real^N->bool = {}` THEN
    ASM_SIMP_TAC[AFF_DIM_EMPTY; GSYM INT_NOT_LE; AFF_DIM_GE] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `(:real^N)`] lemma2) THEN
    ASM_REWRITE_TAC[DIM_UNIV; SUBSPACE_UNIV; AFF_DIM_LE_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP
      HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY_NULL th]) THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `t':real^N->bool`] lemma2) THEN
    ASM_SIMP_TAC[GSYM AFF_DIM_DIM_SUBSPACE] THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP
      HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY_NULL th]) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma1 THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_LT; GSYM AFF_DIM_DIM_SUBSPACE] THEN
    ASM_INT_ARITH_TAC);;

let INESSENTIAL_SPHEREMAP_LOWDIM = prove
 (`!f:real^M->real^N a r b s.
        dimindex(:M) < dimindex(:N) /\
        f continuous_on sphere(a,r) /\
        IMAGE f (sphere(a,r)) SUBSET (sphere(b,s))
        ==> ?c. homotopic_with (\z. T)
                 (subtopology euclidean (sphere(a,r)),
                  subtopology euclidean (sphere(b,s))) f (\x. c)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s <= &0` THEN
  ASM_SIMP_TAC[NULLHOMOTOPIC_INTO_CONTRACTIBLE; CONTRACTIBLE_SPHERE] THEN
  ASM_CASES_TAC `r <= &0` THEN
  ASM_SIMP_TAC[NULLHOMOTOPIC_FROM_CONTRACTIBLE; CONTRACTIBLE_SPHERE] THEN
  ASM_SIMP_TAC[GSYM FRONTIER_CBALL; INTERIOR_CBALL; BALL_EQ_EMPTY;
               CONV_RULE(RAND_CONV SYM_CONV) (SPEC_ALL
               RELATIVE_FRONTIER_NONEMPTY_INTERIOR)] THEN
  STRIP_TAC THEN MATCH_MP_TAC INESSENTIAL_SPHEREMAP_LOWDIM_GEN THEN
  ASM_REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; AFF_DIM_CBALL] THEN
  ASM_REWRITE_TAC[GSYM REAL_NOT_LE; INT_OF_NUM_LT]);;

let HOMEOMORPHIC_SPHERES_EQ,HOMOTOPY_EQUIVALENT_SPHERES_EQ =
 (CONJ_PAIR o prove)
 (`(!a:real^M b:real^N r s.
        sphere(a,r) homeomorphic sphere(b,s) <=>
        r < &0 /\ s < &0 \/ r = &0 /\ s = &0 \/
        &0 < r /\ &0 < s /\ dimindex(:M) = dimindex(:N)) /\
   (!a:real^M b:real^N r s.
        sphere(a,r) homotopy_equivalent sphere(b,s) <=>
        r < &0 /\ s < &0 \/ r = &0 /\ s = &0 \/
        &0 < r /\ &0 < s /\ dimindex(:M) = dimindex(:N))`,
  let lemma = prove
   (`!a:real^M r b:real^N s.
          dimindex(:M) < dimindex(:N) /\ &0 < r /\ &0 < s
          ==> ~(sphere(a,r) homotopy_equivalent sphere(b,s))`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o ISPEC `sphere(a:real^M,r)` o
        MATCH_MP HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY) THEN
    MATCH_MP_TAC(TAUT `~p /\ q ==> (p <=> q) ==> F`) THEN CONJ_TAC THENL
     [SUBGOAL_THEN `~(sphere(a:real^M,r) = {})` MP_TAC THENL
       [REWRITE_TAC[SPHERE_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM]] THEN
      X_GEN_TAC `c:real^M` THEN DISCH_TAC THEN
      DISCH_THEN(MP_TAC o SPECL[`\a:real^M. a`; `(\a. c):real^M->real^M`]) THEN
      SIMP_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID;
               IMAGE_ID; SUBSET_REFL] THEN
      REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~(contractible(sphere(a:real^M,r)))` MP_TAC THENL
       [REWRITE_TAC[CONTRACTIBLE_SPHERE] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[contractible] THEN MESON_TAC[]];
      MAP_EVERY X_GEN_TAC [`f:real^M->real^N`; `g:real^M->real^N`] THEN
      STRIP_TAC THEN
      MP_TAC(ISPEC `g:real^M->real^N` INESSENTIAL_SPHEREMAP_LOWDIM) THEN
      MP_TAC(ISPEC `f:real^M->real^N` INESSENTIAL_SPHEREMAP_LOWDIM) THEN
      ASM_REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN DISCH_THEN
       (MP_TAC o SPECL [`a:real^M`; `r:real`; `b:real^N`; `s:real`]) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMP_CONJ; RIGHT_IMP_FORALL_THM] THEN
      REPEAT GEN_TAC THEN REWRITE_TAC[IMP_IMP] THEN DISCH_THEN
       (fun th -> CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP
                         HOMOTOPIC_WITH_IMP_SUBSET) th THEN
                  MP_TAC th) THEN
      MATCH_MP_TAC(MESON[HOMOTOPIC_WITH_TRANS; HOMOTOPIC_WITH_SYM]
          `homotopic_with p
            (subtopology euclidean s,subtopology euclidean t) c d
            ==> homotopic_with p
                 (subtopology euclidean s,
                  subtopology euclidean t) f c /\
                homotopic_with p
                 (subtopology euclidean s,
                  subtopology euclidean t) g d
                ==> homotopic_with p
                     (subtopology euclidean s,
                      subtopology euclidean t) f g`) THEN
      REWRITE_TAC[HOMOTOPIC_CONSTANT_MAPS] THEN DISJ2_TAC THEN
      MP_TAC(ISPECL [`b:real^N`; `s:real`] PATH_CONNECTED_SPHERE) THEN
      ANTS_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
         `m < n ==> 1 <= m ==> 2 <= n`)) THEN REWRITE_TAC[DIMINDEX_GE_1];
        REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        SUBGOAL_THEN `~(sphere(a:real^M,r) = {})` MP_TAC THENL
         [REWRITE_TAC[SPHERE_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
          ASM SET_TAC[]]]]) in
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT
   `(r ==> p) /\ (q ==> r) /\ (p ==> q) ==> (r <=> q) /\ (p <=> q)`) THEN
  REWRITE_TAC[HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT] THEN
  ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[SPHERE_EMPTY; SPHERE_EQ_EMPTY;
               HOMEOMORPHIC_EMPTY; HOMOTOPY_EQUIVALENT_EMPTY]
  THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `s < &0` THEN
  ASM_SIMP_TAC[SPHERE_EMPTY; SPHERE_EQ_EMPTY;
               HOMEOMORPHIC_EMPTY; HOMOTOPY_EQUIVALENT_EMPTY]
  THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `r = &0` THEN
  ASM_SIMP_TAC[SPHERE_SING; REAL_LT_REFL; HOMEOMORPHIC_SING;
               HOMOTOPY_EQUIVALENT_SING; CONTRACTIBLE_SPHERE;
               ONCE_REWRITE_RULE[HOMOTOPY_EQUIVALENT_SYM]
                   HOMOTOPY_EQUIVALENT_SING]
  THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `s = &0` THEN
  ASM_SIMP_TAC[SPHERE_SING; REAL_LT_REFL; HOMEOMORPHIC_SING;
               HOMOTOPY_EQUIVALENT_SING; CONTRACTIBLE_SPHERE;
               ONCE_REWRITE_RULE[HOMOTOPY_EQUIVALENT_SYM]
                   HOMOTOPY_EQUIVALENT_SING]
  THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ &0 < s` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [DISCH_THEN(fun th ->
      let t = `?a:real^M b:real^N. ~(sphere(a,r) homeomorphic sphere(b,s))` in
      MP_TAC(DISCH t (GEOM_EQUAL_DIMENSION_RULE th (ASSUME t)))) THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_SPHERES] THEN MESON_TAC[];
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[ARITH_RULE `~(m:num = n) <=> m < n \/ n < m`] THEN
    STRIP_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC[HOMOTOPY_EQUIVALENT_SYM]] THEN
    ASM_SIMP_TAC[lemma]]);;

let SIMPLY_CONNECTED_SPHERE_GEN = prove
 (`!s. convex s /\ bounded s /\ &3 <= aff_dim s
       ==> simply_connected(relative_frontier s)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_CIRCLEMAP;
               PATH_CONNECTED_SPHERE_GEN;
               INT_ARITH `&3:int <= x ==> ~(x = &1)`] THEN
  SUBGOAL_THEN `sphere(vec 0:real^2,&1) = relative_frontier(cball(vec 0,&1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[RELATIVE_FRONTIER_CBALL; REAL_OF_NUM_EQ; ARITH]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INESSENTIAL_SPHEREMAP_LOWDIM_GEN THEN
  ASM_REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; AFF_DIM_CBALL] THEN
  REWRITE_TAC[DIMINDEX_2; REAL_LT_01] THEN ASM_INT_ARITH_TAC);;

let SIMPLY_CONNECTED_SPHERE = prove
 (`!a:real^N r. 3 <= dimindex(:N) ==> simply_connected(sphere(a,r))`,
  REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `r < &0 \/ r = &0 \/ &0 < r`) THEN
  ASM_SIMP_TAC[SPHERE_EMPTY; SIMPLY_CONNECTED_EMPTY] THEN
  ASM_SIMP_TAC[SPHERE_SING; CONVEX_SING; CONVEX_IMP_SIMPLY_CONNECTED] THEN
  MP_TAC(ISPEC `cball(a:real^N,r)` SIMPLY_CONNECTED_SPHERE_GEN) THEN
  ASM_SIMP_TAC[AFF_DIM_CBALL; RELATIVE_FRONTIER_CBALL; CONVEX_CBALL;
               BOUNDED_CBALL; REAL_LT_IMP_NE; INT_OF_NUM_LE]);;

let SIMPLY_CONNECTED_PUNCTURED_CONVEX = prove
 (`!s a:real^N.
        convex s /\ &3 <= aff_dim s ==> simply_connected(s DELETE a)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(a:real^N) IN relative_interior s` THENL
   [ALL_TAC;
    MATCH_MP_TAC CONTRACTIBLE_IMP_SIMPLY_CONNECTED THEN
    MATCH_MP_TAC CONTRACTIBLE_CONVEX_TWEAK_BOUNDARY_POINTS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR_CBALL]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL
   [`cball(a:real^N,e) INTER affine hull s`; `s:real^N->bool`; `a:real^N`]
        HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_CONVEX) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(MESON[HOMOTOPY_EQUIVALENT_SIMPLE_CONNECTEDNESS]
     `simply_connected s
      ==> s homotopy_equivalent t ==> simply_connected t`) THEN
    MATCH_MP_TAC SIMPLY_CONNECTED_SPHERE_GEN] THEN
  ASM_SIMP_TAC[CONVEX_INTER; AFFINE_AFFINE_HULL; AFFINE_IMP_CONVEX;
               CONVEX_CBALL; BOUNDED_INTER; BOUNDED_CBALL] THEN
  REPEAT CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhs o rand) RELATIVE_INTERIOR_CONVEX_INTER_AFFINE o
        rand o snd) THEN
    REWRITE_TAC[CONVEX_CBALL; AFFINE_AFFINE_HULL; INTERIOR_CBALL] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM; IN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_SIMP_TAC[CENTRE_IN_BALL] THEN
    ANTS_TAC THENL
     [ALL_TAC;
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[CENTRE_IN_BALL; IN_INTER]] THEN
    ASM_MESON_TAC[SUBSET; HULL_SUBSET; RELATIVE_INTERIOR_SUBSET];
    REWRITE_TAC[relative_frontier] THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (SET_RULE `s SUBSET u ==> c = s ==> c DIFF i SUBSET u`)) THEN
    REWRITE_TAC[CLOSURE_EQ] THEN MATCH_MP_TAC CLOSED_INTER THEN
    REWRITE_TAC[CLOSED_AFFINE_HULL; CLOSED_CBALL];
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    W(MP_TAC o PART_MATCH (lhs o rand)
      AFFINE_HULL_AFFINE_INTER_NONEMPTY_INTERIOR o rand o snd);
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) AFF_DIM_CONVEX_INTER_NONEMPTY_INTERIOR o
        rand o snd)] THEN
  ASM_SIMP_TAC[AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL; GSYM MEMBER_NOT_EMPTY;
               LEFT_IMP_EXISTS_THM; IN_INTER] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN
  ASM_SIMP_TAC[INTERIOR_CBALL; CENTRE_IN_BALL; HULL_INC; HULL_SUBSET;
               AFF_DIM_AFFINE_HULL]);;

let SIMPLY_CONNECTED_PUNCTURED_UNIVERSE = prove
 (`!a. 3 <= dimindex(:N) ==> simply_connected((:real^N) DELETE a)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `&1`] o
    MATCH_MP SIMPLY_CONNECTED_SPHERE) THEN
  MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC HOMOTOPY_EQUIVALENT_SIMPLE_CONNECTEDNESS THEN
  MP_TAC(ISPECL [`cball(a:real^N,&1)`; `a:real^N`]
        HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_AFFINE_HULL) THEN
  REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; RELATIVE_INTERIOR_CBALL;
              RELATIVE_FRONTIER_CBALL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[CENTRE_IN_BALL; AFFINE_HULL_NONEMPTY_INTERIOR; INTERIOR_CBALL;
           BALL_EQ_EMPTY; REAL_OF_NUM_LE; ARITH; REAL_LT_01]);;

let SIMPLY_CONNECTED_CONVEX_DIFF_FINITE = prove
 (`!s t:real^N->bool.
        convex s /\ &3 <= aff_dim s /\ FINITE t
        ==> simply_connected(s DIFF t)`,
  let lemma = prove
   (`!P. (?u v. P u /\ P v /\ ~(u = v)) /\
         (!c. P c ==> ~(s INTER {x:real^N | x$k = c} = {}))
         ==> ?u v. u IN s INTER {x | P(x$k)} /\ v IN s INTER {x | P(x$k)} /\
                   ~(u = v)`,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `u:real` th) THEN MP_TAC(SPEC `v:real` th)) THEN
    ASM SET_TAC[]) in
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN
  WF_INDUCT_TAC `CARD(t:real^N->bool)` THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s DIFF (s INTER t)`] THEN
  REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC (SET_RULE
   `s INTER t = {} \/ ?a:real^N. s INTER t = {a} \/
    ?a b. ~(a = b) /\ a IN s /\ a IN t /\ b IN s /\ b IN t`) THEN
  ASM_SIMP_TAC[CONVEX_IMP_SIMPLY_CONNECTED; SIMPLY_CONNECTED_PUNCTURED_CONVEX;
               DIFF_EMPTY; SET_RULE `s DIFF {a} = s DELETE a`] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
  REWRITE_TAC[NOT_IMP; LEFT_IMP_EXISTS_THM; NOT_FORALL_THM] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
   `~(x = y) ==> x < y \/ y < x`)) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  ONCE_REWRITE_TAC[REWRITE_RULE[IMP_CONJ_ALT] IMP_IMP] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`b:real^N`; `a:real^N`] THEN
  MATCH_MP_TAC(MESON[]
   `(!a b. R a b ==> R b a) /\ (!a b. P a b ==> R a b)
    ==> !a b. P a b \/ P b a ==> R a b`) THEN
  CONJ_TAC THENL [REWRITE_TAC[CONJ_ACI]; REPEAT STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]) THEN
  SUBGOAL_THEN
   `!s t. s DIFF t =
          {x | x IN s /\ x$k < (b:real^N)$k} DIFF
          {x | x IN t /\ x$k < b$k} UNION
          {x:real^N | x IN s /\ (a:real^N)$k < x$k} DIFF
          {x | x IN t /\ a$k < x$k}`
   (fun th -> ONCE_REWRITE_TAC[th] THEN ASSUME_TAC(GSYM th))
  THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `a < b ==> !x. a < x \/ x < b`)) THEN SET_TAC[];
    MATCH_MP_TAC SIMPLY_CONNECTED_UNION THEN ASM_REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} DIFF {x | x IN t /\ P x} =
                          (s DIFF t) INTER {x | P x}`] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT];
    REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} DIFF {x | x IN t /\ P x} =
                          (s DIFF t) INTER {x | P x}`] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    REWRITE_TAC[GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER {x | P x}`;
      FINITE_INTER; CONVEX_INTER; CONVEX_HALFSPACE_COMPONENT_LT] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_PSUBSET THEN ASM SET_TAC[REAL_LT_REFL];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `&3:int <= x ==> y = x ==> &3 <= y`)) THEN
    MATCH_MP_TAC AFF_DIM_CONVEX_INTER_OPEN THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN
    ASM SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER {x | P x}`;
      FINITE_INTER; CONVEX_INTER;
      REWRITE_RULE[real_gt] CONVEX_HALFSPACE_COMPONENT_GT] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_PSUBSET THEN ASM SET_TAC[REAL_LT_REFL];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `&3:int <= x ==> y = x ==> &3 <= y`)) THEN
    MATCH_MP_TAC AFF_DIM_CONVEX_INTER_OPEN THEN
    ASM_REWRITE_TAC[REWRITE_RULE[real_gt] OPEN_HALFSPACE_COMPONENT_GT] THEN
    ASM SET_TAC[];
    ALL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} DIFF {x | x IN t /\ P x} =
                        (s DIFF t) INTER {x | P x}`] THEN
  REWRITE_TAC[SET_RULE `(s INTER u) INTER (s INTER v) = s INTER (u INTER v)`;
              SET_RULE `(s DIFF t) INTER u = (s INTER u) DIFF t`] THEN
  REWRITE_TAC[SET_RULE `s INTER u DIFF s INTER t = s INTER u DIFF t`] THENL
   [MATCH_MP_TAC PATH_CONNECTED_CONVEX_DIFF_COUNTABLE THEN
    ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; CONVEX_INTER; COLLINEAR_AFF_DIM;
                 CONVEX_HALFSPACE_COMPONENT_LT;
                 REWRITE_RULE[real_gt] CONVEX_HALFSPACE_COMPONENT_GT] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `&3:int <= x ==> y = x ==> ~(y <= &1)`)) THEN
    MATCH_MP_TAC AFF_DIM_CONVEX_INTER_OPEN THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_LT;
                 REWRITE_RULE[real_gt] OPEN_HALFSPACE_COMPONENT_GT] THEN
    MATCH_MP_TAC(MESON[INFINITE; FINITE_EMPTY]
     `INFINITE s ==> ~(s = {})`);
    REWRITE_TAC[SET_RULE `s DIFF t = {} <=> s SUBSET t`] THEN
    MATCH_MP_TAC(MESON[FINITE_SUBSET; INFINITE]
     `INFINITE s /\ FINITE t ==> ~(s SUBSET t)`) THEN
    ASM_REWRITE_TAC[]] THEN
 (ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [CONNECTED_FINITE_IFF_SING; INFINITE; CONVEX_CONNECTED;
    CONVEX_INTER; CONVEX_HALFSPACE_COMPONENT_LT;
    REWRITE_RULE[real_gt] CONVEX_HALFSPACE_COMPONENT_GT] THEN
  MATCH_MP_TAC(SET_RULE
   `!u v. u IN s /\ v IN s /\ ~(u = v) ==> ~(s = {} \/ ?z. s = {z})`) THEN
  REWRITE_TAC[SET_RULE `{x | P x} INTER {x | Q x} = {x | Q x /\ P x}`] THEN
  MP_TAC lemma THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [EXISTS_TAC `a$k + &1 / &3 * ((b:real^N)$k - (a:real^N)$k)` THEN
    EXISTS_TAC `a$k + &2 / &3 * ((b:real^N)$k - (a:real^N)$k)` THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:real` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
    SUBGOAL_THEN `!x:real^N. x$k = basis k dot x` (fun t -> SIMP_TAC[t]) THENL
     [ASM_MESON_TAC[DOT_BASIS]; MATCH_MP_TAC CONNECTED_IVT_HYPERPLANE] THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
    ASM_SIMP_TAC[CONVEX_CONNECTED; DOT_BASIS; REAL_LT_IMP_LE]]));;

(* ------------------------------------------------------------------------- *)
(* Borsuk's odd mapping degree theorem.                                      *)
(* ------------------------------------------------------------------------- *)

let ODD_MAP_HOMOTOPY_LEMMA = prove
 (`!f:real^N->real^N s t.
        subspace s /\ subspace t /\ dim s + 1 = dim t /\ s SUBSET t /\
        f continuous_on (sphere(vec 0,&1) INTER t) /\
        IMAGE f (sphere(vec 0,&1) INTER t) SUBSET (sphere(vec 0,&1) INTER t) /\
        (!x. x IN (sphere(vec 0,&1) INTER t) ==> f(--x) = --(f x))
        ==> ?g. g continuous_on (sphere(vec 0,&1) INTER t) /\
                IMAGE g (sphere(vec 0,&1) INTER t) SUBSET
                sphere(vec 0,&1) INTER t /\
                IMAGE g (sphere(vec 0,&1) INTER s) SUBSET
                sphere(vec 0,&1) INTER s /\
                (!x. x IN (sphere(vec 0,&1) INTER t) ==> g(--x) = --(g x)) /\
                homotopic_with (\z. T)
                 (subtopology euclidean (sphere(vec 0,&1) INTER t),
                  subtopology euclidean (sphere(vec 0,&1) INTER t))
                 f g`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `sphere(vec 0:real^N,&1) INTER s = {}` THENL
   [EXISTS_TAC `f:real^N->real^N` THEN
    ASM_REWRITE_TAC[HOMOTOPIC_WITH_REFL; IMAGE_CLAUSES; SUBSET_EMPTY] THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?g. vector_polynomial_function g /\
        (!x. x IN sphere(vec 0:real^N,&1) INTER t ==> g x IN t) /\
        (!x. x IN sphere(vec 0,&1) INTER t ==> g(--x) = --(g x)) /\
        (!x. x IN sphere (vec 0,&1) INTER t ==> norm(f x - g x) < &1 / &2)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->real^N`; `sphere(vec 0:real^N,&1) INTER t`;
                 `&1 / &2`; `t:real^N->bool`;]
        STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION_SUBSPACE) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[COMPACT_INTER_CLOSED; COMPACT_SPHERE; CLOSED_SUBSPACE] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[SUBSET; FORALL_IN_IMAGE]] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\x. inv(&2) % ((g:real^N->real^N) x - g(--x))` THEN
    REWRITE_TAC[VECTOR_ARITH `--(a % (x - y)):real^N = a % (y - x)`] THEN
    REWRITE_TAC[VECTOR_NEG_NEG; IN_SPHERE_0; IN_INTER] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_SPHERE_0; IN_INTER]) THEN
    ASM_SIMP_TAC[SUBSPACE_MUL_EQ; SUBSPACE_SUB; NORM_NEG; SUBSPACE_NEG_EQ] THEN
    ASM_SIMP_TAC[VECTOR_POLYNOMIAL_FUNCTION_CMUL; VECTOR_POLYNOMIAL_FUNCTION_SUB;
                 VECTOR_POLYNOMIAL_FUNCTION_REFLECT; ETA_AX] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(NORM_ARITH
     `norm(f - g:real^N) < e /\ norm(--f - g') < e
      ==> norm(f - inv(&2) % (g - g')) < e`) THEN
    ASM_MESON_TAC[NORM_NEG; SUBSPACE_NEG; VECTOR_NEG_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN sphere(vec 0,&1) INTER t ==> ~((g:real^N->real^N) x = vec 0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_SPHERE_0] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_SPHERE_0]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INTER; IN_SPHERE_0] THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->real^N) differentiable_on
                sphere(vec 0,&1) INTER s`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[DIFFERENTIABLE_ON_VECTOR_POLYNOMIAL_FUNCTION]; ALL_TAC] THEN
  ABBREV_TAC `(h:real^N->real^N) = \x. inv(norm(g x)) % g x` THEN
  SUBGOAL_THEN
   `!x. x IN sphere(vec 0,&1) INTER t
        ==> (h:real^N->real^N) x IN sphere(vec 0,&1) INTER t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN
    ASM_SIMP_TAC[SUBSPACE_MUL; IN_INTER; IN_SPHERE_0; NORM_MUL] THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0; GSYM IN_SPHERE_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN sphere(vec 0,&1) INTER t ==> h(--x) = --((h:real^N->real^N) x)`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[NORM_NEG; VECTOR_MUL_RNEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(h:real^N->real^N) differentiable_on sphere(vec 0,&1) INTER t`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC DIFFERENTIABLE_ON_MUL THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_ON_VECTOR_POLYNOMIAL_FUNCTION; o_DEF] THEN
    SUBGOAL_THEN
     `(\x. lift(inv(norm((g:real^N->real^N) x)))) =
      (lift o inv o drop) o (\x. lift(norm x)) o (g:real^N->real^N)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFERENTIABLE_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_ON_COMPOSE THEN
      ASM_SIMP_TAC[DIFFERENTIABLE_ON_VECTOR_POLYNOMIAL_FUNCTION] THEN
      MATCH_MP_TAC DIFFERENTIABLE_ON_NORM THEN
      ASM_REWRITE_TAC[SET_RULE
       `~(z IN IMAGE f s) <=> !x. x IN s ==> ~(f x = z)`];
      MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
      REWRITE_TAC[GSYM REAL_DIFFERENTIABLE_AT] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_SPHERE_0] THEN
      X_GEN_TAC `x:real^N` THEN
      ASM_CASES_TAC `x:real^N = vec 0` THEN
      ASM_REWRITE_TAC[NORM_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM REAL_DIFFERENTIABLE_AT; o_THM] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_INV_ATREAL THEN
      ASM_SIMP_TAC[REAL_DIFFERENTIABLE_ID; NORM_EQ_0; IN_SPHERE_0]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`h:real^N->real^N`; `s:real^N->bool`; `t:real^N->bool`]
   NONSURJECTIVE_DIFFERENTIABLE_SPHEREMAP_LOWDIM) THEN
  ASM_SIMP_TAC[ARITH_RULE `s + 1 = t ==> s < t`] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      DIFFERENTIABLE_ON_SUBSET)) THEN
    ASM SET_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `~(IMAGE f s = t)
      ==> s SUBSET t /\ IMAGE f t SUBSET t
          ==> ?q. q IN t /\ ~(q IN IMAGE f s)`)) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `~((--q) IN IMAGE (h:real^N->real^N) (sphere(vec 0,&1) INTER s))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `~(q IN IMAGE f s)
      ==> (!x. n(n x) = x) /\ (!x. n x IN s <=> x IN s) /\
          (!x. x IN s ==> f(n x) = n(f x))
          ==> ~(n q IN IMAGE f s)`)) THEN
    REWRITE_TAC[VECTOR_NEG_NEG] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_SIMP_TAC[IN_INTER; IN_SPHERE_0; SUBSPACE_NEG_EQ; NORM_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?p. p IN sphere(vec 0,&1) INTER t /\
        !x:real^N. x IN s ==> orthogonal p x`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`]
        ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN) THEN
    ASM_SIMP_TAC[SPAN_OF_SUBSPACE; PSUBSET] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `~(s + 1 = s)`]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `inv(norm p) % p:real^N` THEN
    ASM_SIMP_TAC[ORTHOGONAL_MUL; IN_INTER; IN_SPHERE_0; SUBSPACE_MUL] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?k. homotopic_with (\x. T)
          (subtopology euclidean (sphere(vec 0,&1) INTER t),
           subtopology euclidean (sphere(vec 0,&1) INTER t))
          h k /\
        (!x. x IN (sphere(vec 0,&1) INTER t) ==> k(--x) = --(k x)) /\
        DISJOINT (IMAGE k (sphere(vec 0,&1) INTER s)) {p:real^N,--p}`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `p:real^N = q \/ p = --q` THENL
     [EXISTS_TAC `h:real^N->real^N` THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
      ASM_REWRITE_TAC[HOMOTOPIC_WITH_REFL; VECTOR_NEG_NEG] THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
      ASM_SIMP_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_ON] THEN ASM SET_TAC[];
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
      STRIP_TAC] THEN
    EXISTS_TAC
     `reflect_along p o reflect_along (q - p) o (h:real^N->real^N)` THEN
    REWRITE_TAC[SET_RULE
     `DISJOINT s {a,b} <=> !x. x IN s ==> ~(x = a) /\ ~(x = b)`] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; o_THM; REFLECT_ALONG_GALOIS] THEN
    REWRITE_TAC[REFLECT_ALONG_REFL; REFLECT_ALONG_NEG] THEN
    ASM_SIMP_TAC[REFLECT_ALONG_INVOLUTION] THEN CONJ_TAC THENL
     [ALL_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[IN_IMAGE; IN_INTER; IN_SPHERE_0]) THEN
      ASM_SIMP_TAC[REFLECT_ALONG_SWITCH; IN_INTER; IN_SPHERE_0] THEN
      ASM_MESON_TAC[VECTOR_NEG_NEG]] THEN
    SUBGOAL_THEN `h:real^N->real^N = reflect_along p o reflect_along p o h`
     (fun th -> GEN_REWRITE_TAC LAND_CONV [th])
    THENL [SIMP_TAC[FUN_EQ_THM; o_THM; REFLECT_ALONG_INVOLUTION]; ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
    EXISTS_TAC `sphere(vec 0:real^N,&1) INTER t` THEN CONJ_TAC THENL
     [ALL_TAC;
      SIMP_TAC[LINEAR_REFLECT_ALONG; LINEAR_CONTINUOUS_ON] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_SPHERE_0] THEN
      SIMP_TAC[NORM_REFLECT_ALONG] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[reflect_along] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_SPHERE_0]) THEN
      ASM_SIMP_TAC[SUBSPACE_MUL; SUBSPACE_SUB]] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
    EXISTS_TAC `sphere(vec 0:real^N,&1) INTER t` THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_ON] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_REFLECTIONS_ALONG THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTER])) THEN
      ASM_REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ASM_REWRITE_TAC[VECTOR_SUB_EQ]] THEN
    X_GEN_TAC `r:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_SPHERE_0] THEN
    SIMP_TAC[NORM_REFLECT_ALONG] THEN REWRITE_TAC[reflect_along] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC SUBSPACE_SUB THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSPACE_MUL THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
    ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM; SUBSPACE_ADD;
                 SUBSPACE_MUL; SUBSPACE_SUB];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
  SUBGOAL_THEN
   `?r. &0 < r /\ r < &1 /\
        !x. x IN (sphere(vec 0,&1) INTER s)
            ==> abs(p dot (k:real^N->real^N) x) < r`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real^N. abs(p dot x)`;
                   `IMAGE (k:real^N->real^N) (sphere (vec 0,&1) INTER s)`]
        CONTINUOUS_ATTAINS_SUP) THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ANTS_TAC THENL
     [SIMP_TAC[o_DEF; CONTINUOUS_ON_LIFT_DOT2; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_LIFT_ABS; CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[CLOSED_SUBSPACE; COMPACT_INTER_CLOSED; COMPACT_SPHERE] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      ASM SET_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE]] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `abs((p:real^N) dot c) < &1` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `!y. x <= y /\ y = &1 /\ ~(x = y) ==> x < &1`) THEN
      EXISTS_TAC `norm(p:real^N) * norm(c:real^N)` THEN
      REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
      SUBGOAL_THEN `c IN sphere(vec 0:real^N,&1) INTER t` ASSUME_TAC THENL
       [ASM SET_TAC[];
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_SPHERE_0])] THEN
      ASM_CASES_TAC `abs((p:real^N) dot c) = &1` THENL
       [REWRITE_TAC[NORM_CAUCHY_SCHWARZ_EQUAL];
        ASM_REWRITE_TAC[REAL_MUL_LID]] THEN
      REWRITE_TAC[COLLINEAR_3_DOT_MULTIPLES; VECTOR_SUB_RZERO] THEN
      ASM_REWRITE_TAC[GSYM NORM_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ONCE_REWRITE_TAC[DOT_SYM] THEN FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o
        MATCH_MP (REAL_ARITH `abs x = &1 ==> x = &1 \/ x = -- &1`)) THEN
      REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID] THEN ASM SET_TAC[];
      EXISTS_TAC `(&1 + abs((p:real^N) dot c)) / &2` THEN
      REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
       `abs x <= abs a /\ abs a < &1 ==> abs x < (&1 + abs a) / &2`) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `r' = (&1 + r) / &2` THEN
  SUBGOAL_THEN `&0 < r' /\ r < r' /\ r' < &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
   `i = \x. if abs(p dot x) >= r' then (x:real^N) else
            x - ((r' - max r (abs(p dot x))) / (r' - r) * (p dot x)) % p` THEN
  ABBREV_TAC `j = \x. inv(norm(i x)) % (i:real^N->real^N) x` THEN
  SUBGOAL_THEN `(i:real^N->real^N) continuous_on sphere(vec 0,&1) INTER t`
  ASSUME_TAC THENL
   [EXPAND_TAC "i" THEN REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
    REWRITE_TAC[real_ge] THEN MATCH_MP_TAC CONTINUOUS_MAP_CASES_LE THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    REPEAT CONJ_TAC THENL
     [SIMP_TAC[CONTINUOUS_MAP_REAL_CONST; CONTINUOUS_MAP_FROM_SUBTOPOLOGY];
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_ABS THEN
      MATCH_MP_TAC CONTINUOUS_MAP_DOT THEN
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      SIMP_TAC[CONTINUOUS_MAP_ID; CONTINUOUS_MAP_FROM_SUBTOPOLOGY];
      MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_SUB THEN
      SIMP_TAC[CONTINUOUS_MAP_ID; CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_MUL THEN
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN; CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN
      SIMP_TAC[CONTINUOUS_MAP_DOT; CONTINUOUS_MAP_EUCLIDEAN;
               CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_RMUL THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
      SIMP_TAC[CONTINUOUS_MAP_REAL_CONST; CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX THEN
      SIMP_TAC[CONTINUOUS_MAP_REAL_CONST; CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_ABS THEN
      MATCH_MP_TAC CONTINUOUS_MAP_DOT THEN
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      X_GEN_TAC `x:real^N` THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
      ASM_SIMP_TAC[REAL_ARITH `r < r' ==> r' - max r r' = &0`] THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO;
                  VECTOR_SUB_RZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. (i:real^N->real^N) (--x) = --(i x)` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN EXPAND_TAC "i" THEN
    REWRITE_TAC[DOT_RNEG; REAL_ABS_NEG] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_RNEG] THEN
    REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_ARITH `--x - --a:real^N = --(x - a)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN sphere(vec 0,&1) INTER t ==> ~((i:real^N->real^N) x = vec 0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXPAND_TAC "i" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[DOT_RZERO]) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_SUB_EQ]] THEN
    ASM_CASES_TAC
     `(r' - max r (abs((p:real^N) dot x))) / (r' - r) * abs(p dot x) < &1`
    THENL
     [DISCH_THEN(MP_TAC o AP_TERM `\y:real^N. y dot x`) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_SPHERE_0]) THEN
      ASM_REWRITE_TAC[GSYM NORM_POW_2; DOT_LMUL; GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC[GSYM REAL_POW_2] THEN
      ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN MATCH_MP_TAC(REAL_ARITH
       `x < &1 /\ x * y <= x * &1 ==> ~(abs(&1) * abs(&1) = x * y)`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC;
        TRANS_TAC REAL_LE_TRANS `norm(p:real^N) * norm(x:real^N)` THEN
        REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
       `~(x < &1) ==> x <= &1 * &1 ==> x = &1`)) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
        REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_SPHERE_0]) THEN
        TRANS_TAC REAL_LE_TRANS `norm(p:real^N) * norm(x:real^N)` THEN
        REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
         `x * abs y = &1 ==> x * y = &1 \/ x * y = -- &1`)) THEN
        DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
        UNDISCH_TAC `~(abs((p:real^N) dot x) >= r')` THEN
        SIMP_TAC[CONTRAPOS_THM; DOT_RMUL; GSYM NORM_POW_2] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_SPHERE_0]) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(j:real^N->real^N) continuous_on sphere(vec 0,&1) INTER t`
  ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
    ASM_REWRITE_TAC[NORM_EQ_0] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN sphere(vec 0,&1) INTER t
        ==> (j:real^N->real^N) x IN sphere(vec 0,&1) INTER t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    EXPAND_TAC "j" THEN REWRITE_TAC[IN_INTER; IN_SPHERE_0] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0] THEN MATCH_MP_TAC SUBSPACE_MUL THEN
    EXPAND_TAC "i" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_SPHERE_0]) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[SUBSPACE_SUB; SUBSPACE_MUL];
    ALL_TAC] THEN
  EXISTS_TAC `(j:real^N->real^N) o (k:real^N->real^N)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_COMPOSE; CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `IMAGE f (p INTER t) SUBSET p INTER t /\
      IMAGE f (p INTER s) SUBSET s /\ s SUBSET t
      ==> IMAGE f (p INTER t) SUBSET p INTER t /\
          IMAGE f (p INTER s) SUBSET p INTER s`) THEN
    ASM_REWRITE_TAC[IMAGE_o] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN EXPAND_TAC "j" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSPACE_MUL THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "i" THEN REWRITE_TAC[real_ge] THEN
    MP_TAC(REAL_ARITH `!x. r < r' ==> x < r ==> ~(r' <= x)`) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    ASM_SIMP_TAC[REAL_ARITH `x < r ==> max r x = r`] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_SUB_0; REAL_LT_IMP_NE] THEN
    SUBGOAL_THEN `(k:real^N->real^N) x IN t` MP_TAC THENL
     [ASM SET_TAC[]; SPEC_TAC(`(k:real^N->real^N) x`,`y:real^N`)] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
    SUBGOAL_THEN `(y:real^N) IN span (p INSERT s)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `y IN t ==> span t = t /\ p = span t ==> y IN p`)) THEN
      ASM_REWRITE_TAC[SPAN_EQ_SELF] THEN MATCH_MP_TAC DIM_EQ_SPAN THEN
      CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[DIM_INSERT]] THEN
      ASM_SIMP_TAC[SPAN_OF_SUBSPACE] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[LE_REFL] THEN
      SUBGOAL_THEN `orthogonal (p:real^N) p` MP_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[ORTHOGONAL_REFL]] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_SPHERE_0; NORM_0]) THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SPAN_BREAKDOWN_EQ; SPAN_OF_SUBSPACE] THEN
      DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
      SUBGOAL_THEN `orthogonal p (y - k % p:real^N)` MP_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[orthogonal; DOT_RSUB]] THEN
      REWRITE_TAC[DOT_RMUL; GSYM NORM_POW_2; REAL_SUB_0] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_SPHERE_0]) THEN
      ASM_SIMP_TAC[REAL_POW_2; REAL_MUL_RID]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[o_THM] THEN EXPAND_TAC "j" THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[NORM_NEG; VECTOR_MUL_RNEG];
    ALL_TAC] THEN
  TRANS_TAC HOMOTOPIC_WITH_TRANS `h:real^N->real^N` THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `homotopic_with (\z. T)
       (subtopology euclidean (sphere(vec 0:real^N,&1) INTER t),
        subtopology euclidean (t DELETE (vec 0:real^N)))
       f g`
    MP_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_VECTOR_POLYNOMIAL_FUNCTION] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[SET_RULE
        `s SUBSET t DELETE v <=> s SUBSET t /\ ~(v IN s)`] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
        ASM_SIMP_TAC[SUBSPACE_IMP_CONVEX] THEN ASM SET_TAC[];
        DISCH_THEN(MP_TAC o MATCH_MP SEGMENT_BOUND) THEN
        SUBGOAL_THEN
         `(f:real^N->real^N) x IN sphere(vec 0,&1) /\
          norm(f x - g x) < &1/ &2`
        MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_SPHERE_0] THEN CONV_TAC NORM_ARITH];
      DISCH_THEN(MP_TAC o
        ISPECL [`\y:real^N. inv(norm y) % y`;
                `sphere(vec 0:real^N,&1) INTER t`] o
        MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT)) THEN
      ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
          REWRITE_TAC[o_DEF; CONTINUOUS_ON_ID] THEN
          MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
          SIMP_TAC[IN_DELETE; NORM_EQ_0] THEN
          REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_INTER] THEN
          ASM_SIMP_TAC[SUBSPACE_MUL; IN_SPHERE_0; NORM_MUL;
                       REAL_ABS_MUL] THEN
          SIMP_TAC[REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0]];
        MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
        RULE_ASSUM_TAC(REWRITE_RULE
         [SUBSET; IN_INTER; FORALL_IN_IMAGE; IN_SPHERE_0]) THEN
        ASM_SIMP_TAC[IN_SPHERE_0; IN_INTER;
                     REAL_INV_1; VECTOR_MUL_LID]]];
    ALL_TAC] THEN
  TRANS_TAC HOMOTOPIC_WITH_TRANS `I o (k:real^N->real^N)` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[I_O_ID]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
  EXISTS_TAC `sphere(vec 0:real^N,&1) INTER t` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `homotopic_with (\z. T)
     (subtopology euclidean (sphere(vec 0:real^N,&1) INTER t),
      subtopology euclidean (t DELETE (vec 0:real^N)))
     i I`
  MP_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_ID; I_DEF] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXPAND_TAC "i" THEN REWRITE_TAC[real_ge] THEN COND_CASES_TAC THENL
     [REWRITE_TAC[SEGMENT_REFL; SING_SUBSET; IN_DELETE] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_SPHERE_0]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[NORM_0]) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET_DELETE] THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_SPHERE_0]) THEN
      ASM_SIMP_TAC[SUBSPACE_IMP_CONVEX; SUBSPACE_MUL; SUBSPACE_SUB]] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
    REWRITE_TAC[IN_SEGMENT; VECTOR_ARITH
     `vec 0:real^N = (&1 - u) % x + u % (x - p) <=> x = u % p`] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` MP_TAC) THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN DISCH_THEN(fun th ->
      MP_TAC th THEN MP_TAC(AP_TERM `norm:real^N->real` th)) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN REWRITE_TAC[NORM_MUL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_SPHERE_0]) THEN
    ASM_REWRITE_TAC[REAL_ARITH `&1 = abs x * &1 <=> x = &1 \/ x = -- &1`] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LNEG] THEN
    UNDISCH_TAC `~(r' <= abs((p:real^N) dot x))` THEN
    SIMP_TAC[CONTRAPOS_THM; DOT_RNEG] THEN
    ASM_REWRITE_TAC[GSYM NORM_POW_2] THEN ASM_ARITH_TAC;
    DISCH_THEN(MP_TAC o
      ISPECL [`\y:real^N. inv(norm y) % y`;
              `sphere(vec 0:real^N,&1) INTER t`] o
      MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
      HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT)) THEN
    ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
        REWRITE_TAC[o_DEF; CONTINUOUS_ON_ID] THEN
        MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
        SIMP_TAC[IN_DELETE; NORM_EQ_0] THEN
        REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_INTER] THEN
        ASM_SIMP_TAC[SUBSPACE_MUL; IN_SPHERE_0; NORM_MUL;
                     REAL_ABS_MUL] THEN
        SIMP_TAC[REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0]];
      GEN_REWRITE_TAC RAND_CONV [HOMOTOPIC_WITH_SYM] THEN
      MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [SUBSET; IN_INTER; FORALL_IN_IMAGE; IN_SPHERE_0]) THEN
      ASM_SIMP_TAC[IN_SPHERE_0; IN_INTER; I_DEF;
                   REAL_INV_1; VECTOR_MUL_LID]]]);;

let BORSUK_ODD_MAPPING_GEN = prove
 (`!n (f:real^N->real^N).
        f continuous_on (sphere(vec 0,&1) INTER span(IMAGE basis (1..n))) /\
        IMAGE f (sphere(vec 0,&1) INTER span(IMAGE basis (1..n))) SUBSET
        sphere(vec 0,&1) INTER span(IMAGE basis (1..n)) /\
        (!x. x IN sphere(vec 0,&1) INTER span(IMAGE basis (1..n))
             ==> f(--x) = --(f x))
        ==> (brouwer_degree1 n f == &1) (mod &2)`,
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[brouwer_degree1; ARITH] THEN
    CONV_TAC INTEGER_RULE;
    X_GEN_TAC `n:num` THEN DISCH_TAC] THEN
  X_GEN_TAC `f:real^N->real^N` THEN
  ASM_CASES_TAC `SUC n <= dimindex(:N)` THENL
   [UNDISCH_TAC `SUC n <= dimindex(:N)` THEN REWRITE_TAC[IMP_IMP];
    ASM_REWRITE_TAC[brouwer_degree1] THEN REPEAT STRIP_TAC THEN
    CONV_TAC INTEGER_RULE] THEN
  DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 1 <= n`) THENL
   [ASM_REWRITE_TAC[ARITH; NUMSEG_SING; IMAGE_CLAUSES; SPAN_SING] THEN
    SUBGOAL_THEN
     `sphere (vec 0,&1) INTER {u % basis 1 | u IN (:real)} =
      {-- &1 % basis 1:real^N,&1 % basis 1}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE
        `(!u. (u % b) IN s <=> u = c \/ u = d)
         ==> s INTER {u % b | u IN UNIV} = {c % b,d % b}`) THEN
      SIMP_TAC[IN_SPHERE_0; NORM_BASIS; LE_REFL; DIMINDEX_GE_1; NORM_MUL] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID]] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `(f:real^N->real^N)(basis 1) = basis 1 \/
      (f:real^N->real^N) (basis 1) = --basis 1`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!b. (a:int == b) (mod n) /\ (b == c) (mod n) ==> (a == c) (mod n)`)
    THENL
     [EXISTS_TAC `brouwer_degree1 1 (\x:real^N. x)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(INTEGER_RULE `a:int = b ==> (a == b) (mod n)`) THEN
        MATCH_MP_TAC BROUWER_DEGREE1_EQ THEN
        ASM_REWRITE_TAC[ARITH; NUMSEG_SING; IMAGE_CLAUSES; SPAN_SING] THEN
        REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID] THEN
        REWRITE_TAC[FORALL_IN_INSERT] THEN
        ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY];
        REWRITE_TAC[BROUWER_DEGREE1_ID] THEN CONV_TAC INTEGER_RULE];
      EXISTS_TAC `brouwer_degree1 1 (reflect_along(basis 1:real^N))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(INTEGER_RULE `a:int = b ==> (a == b) (mod n)`) THEN
        MATCH_MP_TAC BROUWER_DEGREE1_EQ THEN
        ASM_REWRITE_TAC[ARITH; NUMSEG_SING; IMAGE_CLAUSES; SPAN_SING] THEN
        REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID] THEN
        REWRITE_TAC[FORALL_IN_INSERT] THEN
        ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY; VECTOR_NEG_NEG;
                     REFLECT_BASIS_ALONG_BASIS; REFLECT_ALONG_NEG;
                     LE_REFL; DIMINDEX_GE_1];
        W(MP_TAC o PART_MATCH (lhand o rand) BROUWER_DEGREE1_REFLECT_ALONG o
          lhand o rator o snd) THEN
        SIMP_TAC[DIMINDEX_GE_1; NUMSEG_SING; LE_REFL; IMAGE_CLAUSES] THEN
        SIMP_TAC[IN_DELETE; SPAN_SUPERSET; IN_SING] THEN
        SIMP_TAC[BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[int_congruent] THEN
        EXISTS_TAC `-- &1:int` THEN CONV_TAC INT_REDUCE_CONV]];
    STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^N->real^N`;
                   `span(IMAGE basis (1..n)):real^N->bool`;
                   `span(IMAGE basis (1..SUC n)):real^N->bool`]
     ODD_MAP_HOMOTOPY_LEMMA) THEN
    ASM_REWRITE_TAC[SUBSPACE_SPAN] THEN
    SUBGOAL_THEN
     `span(IMAGE basis (1..n):real^N->bool) SUBSET
      span(IMAGE basis (1..SUC n))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SPAN_MONO THEN
      REWRITE_TAC[NUMSEG_CLAUSES; ARITH_RULE `1 <= SUC n`] THEN SET_TAC[];
      ASM_REWRITE_TAC[DIM_BASIS_IMAGE; DIM_SPAN]] THEN
    REWRITE_TAC[INTER_NUMSEG; ARITH_RULE `MAX 1 1 = 1`; CARD_NUMSEG_1] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g:real^N->real^N`) THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC;ASM SET_TAC[]] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC(INTEGER_RULE
       `(a:int == b) (mod n) ==> (b == c) (mod n) ==> (a == c) (mod n)`)] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!b. (a:int == b) (mod n) /\ (b == c) (mod n)
          ==> (a == c) (mod n)`) THEN
    EXISTS_TAC `brouwer_degree1 (SUC n) (g:real^N->real^N)` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[BROUWER_DEGREE1_HOMOTOPIC;
                    INTEGER_RULE `a:int = b ==> (a == b) (mod n)`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[brouwer_degree1; ARITH_RULE `1 <= SUC n`] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    REWRITE_TAC[SUC_SUB1] THEN
    MP_TAC(SPEC `SUC n` HOMEOMORPHIC_MAPS_NSPHERE_EUCLIDEAN_SPHERE) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[SUC_SUB1]] THEN
    MAP_EVERY ABBREV_TAC
     [`h:(num->real)->real^N =
        \x. lambda i. if 1 <= i /\ i <= SUC n then x i else &0`;
      `h':real^N->num->real =
        \x i. if 1 <= i /\ i <= SUC n then x$i else &0`] THEN
    ASM_REWRITE_TAC[homeomorphic_maps] THEN STRIP_TAC THEN
    MP_TAC(SPEC `n:num` HOMEOMORPHIC_MAPS_NSPHERE_EUCLIDEAN_SPHERE) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY ABBREV_TAC
     [`k:(num->real)->real^N =
        \x. lambda i. if 1 <= i /\ i <= n then x i else &0`;
      `k':real^N->num->real = \x i. if 1 <= i /\ i <= n then x$i else &0`] THEN
    ASM_REWRITE_TAC[homeomorphic_maps] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!x. x IN topspace(nsphere(n - 1)) ==> (h:(num->real)->real^N) x = k x`
    ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["h"; "k"] THEN REWRITE_TAC[NSPHERE; CART_EQ] THEN
      X_GEN_TAC `x:num->real` THEN ASM_SIMP_TAC[SUB_ADD; IN_NUMSEG] THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM] THEN
      STRIP_TAC THEN SIMP_TAC[LAMBDA_BETA] THEN X_GEN_TAC `i:num` THEN
      ASM_CASES_TAC `i:num <= n` THEN ASM_SIMP_TAC[COND_ID] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!y. y IN (sphere (vec 0,&1) INTER span (IMAGE basis (1..n)))
          ==> (h':real^N->num->real) y = k' y`
    ASSUME_TAC THENL
     [X_GEN_TAC `y:real^N` THEN MAP_EVERY EXPAND_TAC ["h'"; "k'"] THEN
      REWRITE_TAC[IN_INTER; IN_SPAN_IMAGE_BASIS; IN_NUMSEG] THEN
      STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
      ASM_CASES_TAC `1 <= i` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i:num <= n` THEN
      ASM_SIMP_TAC[ARITH_RULE `i <= n ==> i <= SUC n`] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rator o rand)
      BORSUK_ODD_MAPPING_DEGREE_STEP o lhand o rator o snd) THEN
    ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC(INTEGER_RULE
       `b:int = c ==> (a == b) (mod n) ==> (a == c) (mod n)`) THEN
      MATCH_MP_TAC BROUWER_DEGREE2_EQ THEN ASM_SIMP_TAC[o_THM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]) THEN
      ASM SET_TAC[]] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_MAP_COMPOSE; CONTINUOUS_MAP_EUCLIDEAN2];
      X_GEN_TAC `x:num->real` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `(h:(num->real)->real^N) (\i. --x i) = --(h x)`
      SUBST1_TAC THENL
       [EXPAND_TAC "h" THEN
        SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_NEG_COMPONENT] THEN
        MESON_TAC[REAL_NEG_0];
        RULE_ASSUM_TAC(REWRITE_RULE
         [continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]) THEN
        ASM_SIMP_TAC[ETA_AX] THEN EXPAND_TAC "h'" THEN
        REWRITE_TAC[FUN_EQ_THM; VECTOR_NEG_COMPONENT] THEN
        MESON_TAC[REAL_NEG_0]];
      MATCH_MP_TAC CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE THEN
      MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
      EXISTS_TAC `(k':real^N->num->real) o g o (k:(num->real)->real^N)` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[o_THM] THEN
        RULE_ASSUM_TAC(REWRITE_RULE
         [continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]) THEN
        ASM SET_TAC[];
        REPEAT
         (MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC
          `subtopology euclidean
           (sphere(vec 0:real^N,&1) INTER span (IMAGE basis (1..n)))` THEN
         ASM_REWRITE_TAC[]) THEN
        ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        ASM SET_TAC[]]]]);;

let BORSUK_ODD_MAPPING = prove
 (`!f:real^N->real^N.
        f continuous_on sphere(vec 0,&1) /\
        IMAGE f (sphere(vec 0,&1)) SUBSET sphere(vec 0,&1) /\
        (!x. x IN sphere(vec 0,&1) ==> f(--x) = --(f x))
        ==> (brouwer_degree f == &1) (mod &2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[brouwer_degree] THEN
  MATCH_MP_TAC BORSUK_ODD_MAPPING_GEN THEN
  REWRITE_TAC[GSYM SIMPLE_IMAGE; IN_NUMSEG; SPAN_STDBASIS; INTER_UNIV] THEN
  ASM_REWRITE_TAC[LE_REFL; SIMPLE_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Some technical lemmas about extending maps from cell complexes.           *)
(* ------------------------------------------------------------------------- *)

let EXTEND_MAP_CELL_COMPLEX_TO_SPHERE,
    EXTEND_MAP_CELL_COMPLEX_TO_SPHERE_COFINITE = (CONJ_PAIR o prove)
 (`(!f:real^M->real^N m s t.
        FINITE m /\ (!c. c IN m ==> polytope c /\ aff_dim c < aff_dim t) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2) /\
        s SUBSET UNIONS m /\ closed s /\ convex t /\ bounded t /\
        f continuous_on s /\ IMAGE f s SUBSET relative_frontier t
        ==> ?g. g continuous_on UNIONS m /\
                IMAGE g (UNIONS m) SUBSET relative_frontier t /\
                !x. x IN s ==> g x = f x) /\
   (!f:real^M->real^N m s t.
        FINITE m /\ (!c. c IN m ==> polytope c /\ aff_dim c <= aff_dim t) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2) /\
        s SUBSET UNIONS m /\ closed s /\ convex t /\ bounded t /\
        f continuous_on s /\ IMAGE f s SUBSET relative_frontier t
        ==> ?k g. FINITE k /\ DISJOINT k s /\
                  g continuous_on (UNIONS m DIFF k) /\
                  IMAGE g (UNIONS m DIFF k) SUBSET relative_frontier t /\
                  !x. x IN s ==> g x = f x)`,
  let wemma = prove
   (`!h:real^M->real^N k t f.
          (!s. s IN f ==> ?g. g continuous_on s /\
                              IMAGE g s SUBSET t /\
                              !x. x IN s INTER k ==> g x = h x) /\
          FINITE f /\ (!s. s IN f ==> closed s) /\
          (!s t. s IN f /\ t IN f /\ ~(s = t) ==> (s INTER t) SUBSET k)
          ==> ?g. g continuous_on (UNIONS f) /\
                  IMAGE g (UNIONS f) SUBSET t /\
                  !x. x IN (UNIONS f) INTER k ==> g x = h x`,
    REPLICATE_TAC 3 GEN_TAC THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r ==> s <=> q ==> p /\ r ==> s`] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC[UNIONS_0; IMAGE_CLAUSES; EMPTY_SUBSET; CONTINUOUS_ON_EMPTY;
                INTER_EMPTY; NOT_IN_EMPTY] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT] THEN
    REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; SUBSET_REFL] THEN
    MAP_EVERY X_GEN_TAC [`s:real^M->bool`; `u:(real^M->bool)->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
     (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    ASM_SIMP_TAC[UNIONS_INSERT] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(s:real^M->bool) UNION UNIONS u = UNIONS u` THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `f:real^M->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\x. if x IN s then (f:real^M->real^N) x else g x` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES THEN ASM_SIMP_TAC[CLOSED_UNIONS] THEN
    ASM SET_TAC[]) in
  let lemma = prove
   (`!h:real^M->real^N k t f.
          (!s. s IN f ==> ?g. g continuous_on s /\
                              IMAGE g s SUBSET t /\
                              !x. x IN s INTER k ==> g x = h x) /\
          FINITE f /\ (!s. s IN f ==> closed s) /\
          (!s t. s IN f /\ t IN f /\ ~(s SUBSET t) /\ ~(t SUBSET s)
                 ==> (s INTER t) SUBSET k)
          ==> ?g. g continuous_on (UNIONS f) /\
                  IMAGE g (UNIONS f) SUBSET t /\
                  !x. x IN (UNIONS f) INTER k ==> g x = h x`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP UNIONS_MAXIMAL_SETS) THEN
    MATCH_MP_TAC wemma THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN ASM SET_TAC[]) in
  let zemma = prove
   (`!f:real^M->real^N m n t.
          FINITE m /\ (!c. c IN m ==> polytope c) /\
          n SUBSET m /\ (!c. c IN m DIFF n ==> aff_dim c < aff_dim t) /\
          (!c1 c2. c1 IN m /\ c2 IN m
                   ==> (c1 INTER c2) face_of c1 /\ (c1 INTER c2) face_of c2) /\
          convex t /\ bounded t /\
          f continuous_on (UNIONS n) /\
          IMAGE f (UNIONS n) SUBSET relative_frontier t
          ==> ?g. g continuous_on (UNIONS m) /\
                  IMAGE g (UNIONS m) SUBSET relative_frontier t /\
                  (!x. x IN UNIONS n ==> g x = f x)`,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `m DIFF n:(real^M->bool)->bool = {}` THENL
     [SUBGOAL_THEN `(UNIONS m:real^M->bool) SUBSET UNIONS n` ASSUME_TAC THENL
       [ASM SET_TAC[]; EXISTS_TAC `f:real^M->real^N`] THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!i. &i <= aff_dim t
          ==> ?g. g continuous_on
                  (UNIONS
                   (n UNION {d | ?c. c IN m /\ d face_of c /\
                                      aff_dim d < &i})) /\
                  IMAGE g (UNIONS
                   (n UNION {d | ?c. c IN m /\ d face_of c /\
                                      aff_dim d < &i}))
                  SUBSET relative_frontier t /\
                  (!x. x IN UNIONS n ==> g x = (f:real^M->real^N) x)`
    MP_TAC THENL
     [ALL_TAC;
      MP_TAC(ISPEC `aff_dim(t:real^N->bool)` INT_OF_NUM_EXISTS) THEN
      MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[AFF_DIM_GE; MEMBER_NOT_EMPTY;
                      INT_ARITH `--(&1):int <= s /\ s < t ==> &0 <= t`];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `i:num`) THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[INT_LE_REFL] THEN
      SUBGOAL_THEN
       `UNIONS (n UNION {d | ?c. c IN m /\ d face_of c /\ aff_dim d < &i}) =
        UNIONS m:real^M->bool`
       (fun th -> REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [MATCH_MP_TAC UNIONS_MONO THEN REWRITE_TAC[IN_UNION] THEN
        REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
        REWRITE_TAC[FORALL_AND_THM; FORALL_IN_GSPEC] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; GEN_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[FACE_OF_IMP_SUBSET];
        MATCH_MP_TAC SUBSET_UNIONS THEN REWRITE_TAC[SUBSET; IN_UNION] THEN
        X_GEN_TAC `d:real^M->bool` THEN DISCH_TAC THEN
        ASM_CASES_TAC `(d:real^M->bool) IN n` THEN
        ASM_SIMP_TAC[IN_ELIM_THM] THEN
        EXISTS_TAC `d:real^M->bool` THEN
        ASM_SIMP_TAC[FACE_OF_REFL; POLYTOPE_IMP_CONVEX] THEN
        ASM SET_TAC[]]] THEN
    MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
     [REWRITE_TAC[INT_ARITH `d < &0 <=> (--(&1) <= d ==> d:int = --(&1))`] THEN
      REWRITE_TAC[AFF_DIM_GE; AFF_DIM_EQ_MINUS1] THEN
      SUBGOAL_THEN
       `{d:real^M->bool| ?c. c IN m /\ d face_of c /\ d = {}} = {{}}`
       (fun th -> REWRITE_TAC[th])
      THENL
       [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `d:real^M->bool` THEN
        REWRITE_TAC[IN_SING; IN_ELIM_THM] THEN
        ASM_CASES_TAC `d:real^M->bool = {}` THEN
        ASM_REWRITE_TAC[EMPTY_FACE_OF] THEN ASM SET_TAC[];
        REWRITE_TAC[UNIONS_UNION; UNIONS_1; UNION_EMPTY] THEN
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN
    REWRITE_TAC[INT_ARITH `p + &1 <= x <=> p:int < x`] THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC[INT_LT_IMP_LE] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[INT_ARITH `x:int < p + &1 <=> x <= p`] THEN
    SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
     [ASM_MESON_TAC[AFF_DIM_EMPTY; INT_ARITH `~(&p:int < --(&1))`];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(relative_frontier t:real^N->bool = {})` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
      MP_TAC(ISPEC `t:real^N->bool` AFFINE_BOUNDED_EQ_LOWDIM) THEN
      ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!d. d IN n UNION {d | ?c. c IN m /\ d face_of c /\ aff_dim d <= &p}
          ==> ?g. (g:real^M->real^N) continuous_on d /\
                  IMAGE g d SUBSET relative_frontier t /\
                  !x. x IN d INTER
                      UNIONS
                    (n UNION {d | ?c. c IN m /\ d face_of c /\ aff_dim d < &p})
                      ==> g x = h x`
    MP_TAC THENL
     [X_GEN_TAC `d:real^M->bool` THEN
      ASM_CASES_TAC `(d:real^M->bool) SUBSET UNIONS
                 (n UNION {d | ?c. c IN m /\ d face_of c /\ aff_dim d < &p})`
      THENL
       [DISCH_THEN(K ALL_TAC) THEN EXISTS_TAC `h:real^M->real^N` THEN
        REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]];
        ALL_TAC] THEN
      ASM_CASES_TAC `?a:real^M. d = {a}` THENL
       [FIRST_X_ASSUM(X_CHOOSE_THEN `a:real^M` SUBST_ALL_TAC) THEN
        DISCH_THEN(K ALL_TAC) THEN ASM_SIMP_TAC[CONTINUOUS_ON_SING; SET_RULE
         `~({a} SUBSET s) ==> ~(x IN {a} INTER s)`] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE;
                    FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
        MATCH_MP_TAC(MESON[] `(?c. P(\x. c)) ==> (?f. P f)`) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(d:real^M->bool = {})` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
       `~(s SUBSET UNIONS f) ==> ~(s IN f)`)) THEN
      REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP
       (SET_RULE `~(d IN s UNION t) /\ d IN s UNION u
                  ==> ~(d IN s) /\ d IN u DIFF t`)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
       `d IN
        {d | ?c. c IN m /\ d face_of c /\ aff_dim d <= &p} DIFF
        {d | ?c. c IN m /\ d face_of c /\ aff_dim d < &p}
        ==> ?c. c IN m /\ d face_of c /\
                (aff_dim d <= &p /\ ~(aff_dim d < &p))`)) THEN
      REWRITE_TAC[INT_ARITH `d:int <= p /\ ~(d < p) <=> d = p`] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real^M->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`h:real^M->real^N`; `relative_frontier d:real^M->bool`;
        `t:real^N->bool`] NULLHOMOTOPIC_INTO_RELATIVE_FRONTIER_EXTENSION) THEN
      ASM_REWRITE_TAC[CLOSED_RELATIVE_FRONTIER;
                      RELATIVE_FRONTIER_EQ_EMPTY] THEN
      SUBGOAL_THEN
       `relative_frontier d SUBSET
        UNIONS {e:real^M->bool | e face_of c /\ aff_dim e < &p}`
      ASSUME_TAC THENL
       [W(MP_TAC o PART_MATCH (lhs o rand) RELATIVE_FRONTIER_OF_POLYHEDRON o
          lhand o snd) THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC[POLYTOPE_IMP_POLYHEDRON; FACE_OF_POLYTOPE_POLYTOPE];
          DISCH_THEN SUBST1_TAC] THEN
        MATCH_MP_TAC SUBSET_UNIONS THEN
        ASM_SIMP_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM; facet_of] THEN
        X_GEN_TAC `f:real^M->bool` THEN REPEAT STRIP_TAC THENL
         [ASM_MESON_TAC[FACE_OF_TRANS]; INT_ARITH_TAC];
        ALL_TAC] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          ASM SET_TAC[];
          ASM_MESON_TAC[AFFINE_BOUNDED_EQ_TRIVIAL; FACE_OF_POLYTOPE_POLYTOPE;
                        POLYTOPE_IMP_BOUNDED];
          ASM SET_TAC[]];
        ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INESSENTIAL_SPHEREMAP_LOWDIM_GEN THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE; POLYTOPE_IMP_CONVEX];
          ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE; POLYTOPE_IMP_BOUNDED];
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          ASM SET_TAC[];
          ASM SET_TAC[]];
        MATCH_MP_TAC MONO_EXISTS] THEN
      X_GEN_TAC `g:real^M->real^N` THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
        ASM SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[INTER_UNIONS] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (SET_RULE `(!x. x IN s ==> P x) ==> t SUBSET s
                  ==> !x. x IN t ==> P x`)) THEN
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `e:real^M->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC FACE_OF_SUBSET_RELATIVE_FRONTIER THEN CONJ_TAC THENL
       [MATCH_MP_TAC(MESON[]
         `(d INTER e) face_of d /\ (d INTER e) face_of e
          ==> (d INTER e) face_of d`) THEN
        MATCH_MP_TAC FACE_OF_INTER_SUBFACE THEN
        EXISTS_TAC `c:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNION]) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN
        STRIP_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
        ASM_MESON_TAC[FACE_OF_REFL; SUBSET; POLYTOPE_IMP_CONVEX];
        REWRITE_TAC[SET_RULE `d INTER e = d <=> d SUBSET e`] THEN
        DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNION]) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[AFF_DIM_SUBSET; INT_NOT_LE]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] lemma)) THEN
    ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN ASM SET_TAC[]] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FINITE_UNION] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `UNIONS {{d:real^M->bool | d face_of c} | c IN m}` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_GSPEC] THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
        ASM_MESON_TAC[FINITE_POLYTOPE_FACES];
        REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
      ASM_MESON_TAC[FACE_OF_IMP_CLOSED; POLYTOPE_IMP_CLOSED;
                    POLYTOPE_IMP_CONVEX; SUBSET];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`d:real^M->bool`; `e:real^M->bool`] THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `c:real^M->bool` STRIP_ASSUME_TAC)) MP_TAC)
    THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC)) MP_TAC)
    THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[UNIONS_UNION] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s SUBSET t UNION u`) THEN
    MATCH_MP_TAC(SET_RULE `x IN s ==> x SUBSET UNIONS s`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `c:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `d INTER e face_of (d:real^M->bool) /\
                  d INTER e face_of e`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FACE_OF_INTER_SUBFACE]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FACE_OF_TRANS]; ALL_TAC] THEN
    TRANS_TAC INT_LTE_TRANS `aff_dim(d:real^M->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[POLYTOPE_IMP_CONVEX; FACE_OF_IMP_CONVEX];
      ASM SET_TAC[]]) in
  let memma = prove
   (`!h:real^M->real^N k t u f.
          (!s. s IN f ==> ?a g. ~(a IN u) /\ g continuous_on (s DELETE a) /\
                               IMAGE g (s DELETE a) SUBSET t /\
                               !x. x IN s INTER k ==> g x = h x) /\
          FINITE f /\ (!s. s IN f ==> closed s) /\
          (!s t. s IN f /\ t IN f /\ ~(s = t) ==> (s INTER t) SUBSET k)
          ==> ?c g. FINITE c /\ DISJOINT c u /\ CARD c <= CARD f /\
                    g continuous_on (UNIONS f DIFF c) /\
                    IMAGE g (UNIONS f DIFF c) SUBSET t /\
                    !x. x IN (UNIONS f DIFF c) INTER k ==> g x = h x`,
    REPLICATE_TAC 4 GEN_TAC THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r ==> s <=> q ==> p /\ r ==> s`] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC[UNIONS_0; IMAGE_CLAUSES; EMPTY_SUBSET; CONTINUOUS_ON_EMPTY;
                INTER_EMPTY; NOT_IN_EMPTY; EMPTY_DIFF] THEN
    CONJ_TAC THENL
     [MESON_TAC[DISJOINT_EMPTY; FINITE_EMPTY; CARD_CLAUSES; LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT] THEN
    REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; SUBSET_REFL] THEN
    MAP_EVERY X_GEN_TAC [`s:real^M->bool`; `u:(real^M->bool)->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
     (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    ASM_SIMP_TAC[UNIONS_INSERT] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`c:real^M->bool`; `g:real^M->real^N`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[CARD_CLAUSES] THEN
    ASM_CASES_TAC `(s:real^M->bool) UNION UNIONS u = UNIONS u` THENL
     [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[ARITH_RULE `x <= y ==> x <= SUC y`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `a:real^M`
     (X_CHOOSE_THEN `f:real^M->real^N` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `(a:real^M) INSERT c` THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; RIGHT_EXISTS_AND_THM] THEN
    REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `\x. if x IN s then (f:real^M->real^N) x else g x` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(s DIFF ((a:real^M) INSERT c)) UNION
                (UNIONS u DIFF ((a:real^M) INSERT c))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CLOSED_IN_CLOSED] THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[CLOSED_IN_CLOSED] THEN
      EXISTS_TAC `UNIONS u:real^M->bool` THEN ASM_SIMP_TAC[CLOSED_UNIONS];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET));
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET));
      ALL_TAC] THEN
    ASM SET_TAC[]) in
  let temma = prove
   (`!h:real^M->real^N k t u f.
          (!s. s IN f ==> ?a g. ~(a IN u) /\ g continuous_on (s DELETE a) /\
                                IMAGE g (s DELETE a) SUBSET t /\
                                !x. x IN s INTER k ==> g x = h x) /\
          FINITE f /\ (!s. s IN f ==> closed s) /\
          (!s t. s IN f /\ t IN f /\  ~(s SUBSET t) /\ ~(t SUBSET s)
                 ==> (s INTER t) SUBSET k)
          ==> ?c g. FINITE c /\ DISJOINT c u /\ CARD c <= CARD f /\
                    g continuous_on (UNIONS f DIFF c) /\
                    IMAGE g (UNIONS f DIFF c) SUBSET t /\
                    !x. x IN (UNIONS f DIFF c) INTER k ==> g x = h x`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`h:real^M->real^N`; `k:real^M->bool`; `t:real^N->bool`;
                   `u:real^M->bool`;
                   `{t:real^M->bool | t IN f /\
                                      (!u. u IN f ==> ~(t PSUBSET u))}`]
          memma) THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM; UNIONS_MAXIMAL_SETS] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          LE_TRANS)) THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC[] THEN SET_TAC[]) in
  let bemma = prove
   (`!f:real^M->real^N m n t.
        FINITE m /\ (!c. c IN m ==> polytope c) /\
        n SUBSET m /\ (!c. c IN m DIFF n ==> aff_dim c <= aff_dim t) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> (c1 INTER c2) face_of c1 /\ (c1 INTER c2) face_of c2) /\
        convex t /\ bounded t /\
        f continuous_on (UNIONS n) /\
        IMAGE f (UNIONS n) SUBSET relative_frontier t
        ==> ?k g. FINITE k /\ DISJOINT k (UNIONS n) /\ CARD k <= CARD m /\
                  g continuous_on (UNIONS m DIFF k) /\
                  IMAGE g (UNIONS m DIFF k) SUBSET relative_frontier t /\
                  (!x. x IN UNIONS n ==> g x = f x)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^M->real^N`;
         `n UNION {d:real^M->bool | ?c. c IN m DIFF n /\ d face_of c /\
                                        aff_dim d < aff_dim(t:real^N->bool)}`;
         `n:(real^M->bool)->bool`; `t:real^N->bool`] zemma) THEN
    ASM_REWRITE_TAC[SUBSET_UNION; SET_RULE
     `(n UNION m) DIFF n = m DIFF n`] THEN
    SIMP_TAC[IN_DIFF; IN_ELIM_THM; LEFT_IMP_EXISTS_THM;
             LEFT_AND_EXISTS_THM] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[FINITE_UNION] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `UNIONS {{d:real^M->bool | d face_of c} | c IN m}` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_GSPEC] THEN
          ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
          ASM_MESON_TAC[FINITE_POLYTOPE_FACES];
          REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]];
        REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
        ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE; SUBSET];
        REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
        ASM_MESON_TAC[FACE_OF_INTER_SUBFACE; SUBSET; FACE_OF_REFL;
                      POLYTOPE_IMP_CONVEX; FACE_OF_IMP_CONVEX]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `!d. d IN m
          ==> ?a g. ~(a IN UNIONS n) /\
                    (g:real^M->real^N) continuous_on (d DELETE a) /\
                    IMAGE g (d DELETE a) SUBSET relative_frontier t /\
                    !x. x IN d INTER
                         UNIONS
                          (n UNION {d | ?c. (c IN m /\ ~(c IN n)) /\
                                            d face_of c /\
                                            aff_dim d < aff_dim t})
                        ==> g x = h x`
    MP_TAC THENL
     [X_GEN_TAC `d:real^M->bool` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(d:real^M->bool) SUBSET
                     UNIONS(n UNION {d | ?c. (c IN m /\ ~(c IN n)) /\
                                             d face_of c /\
                                     aff_dim d < aff_dim(t:real^N->bool)})`
      THENL
       [SUBGOAL_THEN `~(UNIONS n = (:real^M))` MP_TAC THENL
         [MATCH_MP_TAC(MESON[NOT_BOUNDED_UNIV]
           `bounded s ==> ~(s = UNIV)`) THEN
          MATCH_MP_TAC BOUNDED_UNIONS THEN
          ASM_MESON_TAC[POLYTOPE_IMP_BOUNDED; SUBSET; FINITE_SUBSET];
          GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [EXTENSION]] THEN
        REWRITE_TAC[IN_UNIV; NOT_FORALL_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^M` THEN
        STRIP_TAC THEN EXISTS_TAC `h:real^M->real^N` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET;
                        SET_RULE `s SUBSET t ==> s DELETE a SUBSET t`];
          ASM SET_TAC[]];
        ALL_TAC] THEN
      ASM_CASES_TAC `(d:real^M->bool) IN n` THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISJ_CASES_THEN MP_TAC (SPEC
       `relative_interior(d:real^M->bool) = {}` EXCLUDED_MIDDLE)
      THENL
       [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY; POLYTOPE_IMP_CONVEX] THEN
        ASM SET_TAC[];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY]] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^M` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `relative_frontier d SUBSET
        UNIONS {e:real^M->bool | e face_of d /\
                                 aff_dim e < aff_dim(t:real^N->bool)}`
      ASSUME_TAC THENL
       [W(MP_TAC o PART_MATCH (lhs o rand) RELATIVE_FRONTIER_OF_POLYHEDRON o
          lhand o snd) THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC[POLYTOPE_IMP_POLYHEDRON; FACE_OF_POLYTOPE_POLYTOPE];
          DISCH_THEN SUBST1_TAC] THEN
        MATCH_MP_TAC SUBSET_UNIONS THEN
        ASM_SIMP_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM; facet_of] THEN
        ASM_SIMP_TAC[INT_ARITH `d - &1:int < t <=> d <= t`; IN_DIFF];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`d:real^M->bool`; `a:real^M`]
          RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL) THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_BOUNDED] THEN
      REWRITE_TAC[retract_of; LEFT_IMP_EXISTS_THM; retraction] THEN
      X_GEN_TAC `r:real^M->real^M` THEN STRIP_TAC THEN
      EXISTS_TAC `(h:real^M->real^N) o (r:real^M->real^M)` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN
        DISCH_THEN(X_CHOOSE_THEN `e:real^M->bool` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN
         `e INTER d face_of e /\ e INTER d face_of (d:real^M->bool)`
        MP_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP
          (REWRITE_RULE[IMP_CONJ] FACE_OF_SUBSET_RELATIVE_FRONTIER) o
          CONJUNCT2) THEN
        REWRITE_TAC[NOT_IMP; relative_frontier] THEN
        MP_TAC(ISPEC `d:real^M->bool` RELATIVE_INTERIOR_SUBSET) THEN
        ASM SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
        SIMP_TAC[HULL_SUBSET; SET_RULE
                  `s SUBSET t ==> s DELETE a SUBSET t DELETE a`];
        REWRITE_TAC[IMAGE_o] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `IMAGE h t SUBSET u ==> s SUBSET t ==> IMAGE h s SUBSET u`));
        SIMP_TAC[INTER_UNIONS; o_THM] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (SET_RULE `(!x. x IN s ==> r x = x) ==> t SUBSET s
                    ==> !x. x IN t ==> h(r x) = h x`)) THEN
        REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
        X_GEN_TAC `e:real^M->bool` THEN DISCH_TAC THEN
        MATCH_MP_TAC FACE_OF_SUBSET_RELATIVE_FRONTIER THEN
        CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        MATCH_MP_TAC(MESON[]
         `(d INTER e) face_of d /\ (d INTER e) face_of e
          ==> (d INTER e) face_of d`) THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNION]) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THENL
         [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
        MATCH_MP_TAC FACE_OF_INTER_SUBFACE THEN
        MAP_EVERY EXISTS_TAC [`d:real^M->bool`; `c:real^M->bool`] THEN
        ASM_SIMP_TAC[FACE_OF_REFL; POLYTOPE_IMP_CONVEX]] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE r (h DELETE a) SUBSET t ==> d SUBSET h /\ t SUBSET u
        ==> IMAGE r (d DELETE a) SUBSET u`)) THEN
      REWRITE_TAC[HULL_SUBSET] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] temma)) THEN
    ANTS_TAC THENL
     [ALL_TAC;
      REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]] THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CLOSED] THEN
    MAP_EVERY X_GEN_TAC [`d:real^M->bool`; `e:real^M->bool`] THEN
    STRIP_TAC THEN REWRITE_TAC[UNIONS_UNION] THEN
    ASM_CASES_TAC `(d:real^M->bool) IN n` THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `x IN s ==> x SUBSET t UNION UNIONS s`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `d:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `d INTER e:real^M->bool = d` THENL
      [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN TRANS_TAC INT_LTE_TRANS `aff_dim(d:real^M->bool)` THEN
    ASM_SIMP_TAC[IN_DIFF] THEN MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
    ASM_MESON_TAC[POLYTOPE_IMP_CONVEX]) in
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `compact(s:real^M->bool)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
      ASM_MESON_TAC[BOUNDED_SUBSET; BOUNDED_UNIONS; POLYTOPE_IMP_BOUNDED];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`;
                   `relative_frontier t:real^N->bool`]
          NEIGHBOURHOOD_EXTENSION_INTO_ANR) THEN
    ASM_SIMP_TAC[LEFT_FORALL_IMP_THM; ENR_IMP_ANR;
                 ENR_RELATIVE_FRONTIER_CONVEX] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`v:real^M->bool`; `g:real^M->real^N`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `(:real^M) DIFF v`]
          SEPARATE_COMPACT_CLOSED) THEN
    ASM_SIMP_TAC[GSYM OPEN_CLOSED; IN_DIFF; IN_UNIV] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ ~q ==> r <=> p /\ ~r ==> q`] THEN
    REWRITE_TAC[REAL_NOT_LE; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`m:(real^M->bool)->bool`; `aff_dim(t:real^N->bool) - &1`;
                   `d:real`] CELL_COMPLEX_SUBDIVISION_EXISTS) THEN
    ASM_SIMP_TAC[INT_ARITH `x:int <= t - &1 <=> x < t`] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL
     [`g:real^M->real^N`; `n:(real^M->bool)->bool`;
      `{c:real^M->bool | c IN n /\ c SUBSET v}`; `t:real^N->bool`]
     zemma) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[SUBSET_RESTRICT; IN_DIFF] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        ASM SET_TAC[];
        ASM SET_TAC[]];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^M->real^N` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^M` THEN
      DISCH_TAC THEN TRANS_TAC EQ_TRANS `(g:real^M->real^N) x` THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:real^M) IN UNIONS n` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `c:real^M->bool` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[SUBSET] THEN
      X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `x:real^M` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `diameter(c:real^M->bool)` THEN
      ASM_SIMP_TAC[dist] THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_BOUNDED]];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `compact(s:real^M->bool)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
      ASM_MESON_TAC[BOUNDED_SUBSET; BOUNDED_UNIONS; POLYTOPE_IMP_BOUNDED];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`;
                   `relative_frontier t:real^N->bool`]
          NEIGHBOURHOOD_EXTENSION_INTO_ANR) THEN
    ASM_SIMP_TAC[LEFT_FORALL_IMP_THM; ENR_IMP_ANR;
                 ENR_RELATIVE_FRONTIER_CONVEX] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`v:real^M->bool`; `g:real^M->real^N`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `(:real^M) DIFF v`]
          SEPARATE_COMPACT_CLOSED) THEN
    ASM_SIMP_TAC[GSYM OPEN_CLOSED; IN_DIFF; IN_UNIV] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ ~q ==> r <=> p /\ ~r ==> q`] THEN
    REWRITE_TAC[REAL_NOT_LE; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`m:(real^M->bool)->bool`; `aff_dim(t:real^N->bool)`;
                   `d:real`] CELL_COMPLEX_SUBDIVISION_EXISTS) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL
     [`g:real^M->real^N`; `n:(real^M->bool)->bool`;
      `{c:real^M->bool | c IN n /\ c SUBSET v}`; `t:real^N->bool`]
     bemma) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[SUBSET_RESTRICT; IN_DIFF] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        ASM SET_TAC[];
        ASM SET_TAC[]];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^M->bool` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^M->real^N` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `DISJOINT k u ==> s SUBSET u ==> DISJOINT k s`)) THEN
        REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC;
        X_GEN_TAC `x:real^M` THEN
        DISCH_TAC THEN TRANS_TAC EQ_TRANS `(g:real^M->real^N) x` THEN
        CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
      (SUBGOAL_THEN `(x:real^M) IN UNIONS n` MP_TAC THENL
        [ASM SET_TAC[]; ALL_TAC] THEN
       REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
       X_GEN_TAC `c:real^M->bool` THEN STRIP_TAC THEN
       ASM_REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[SUBSET] THEN
       X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       EXISTS_TAC `x:real^M` THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `diameter(c:real^M->bool)` THEN
       ASM_SIMP_TAC[dist] THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
       ASM_SIMP_TAC[POLYTOPE_IMP_BOUNDED])]]);;

(* ------------------------------------------------------------------------- *)
(* Special cases and corollaries involving spheres.                          *)
(* ------------------------------------------------------------------------- *)

let EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_SIMPLE = prove
 (`!f:real^M->real^N s t u.
        compact s /\ convex u /\ bounded u /\ aff_dim t <= aff_dim u /\
        s SUBSET t /\ f continuous_on s /\ IMAGE f s SUBSET relative_frontier u
        ==> ?k g. FINITE k /\ k SUBSET t /\ DISJOINT k s /\
                  g continuous_on (t DIFF k) /\
                  IMAGE g (t DIFF k) SUBSET relative_frontier u /\
                  !x. x IN s ==> g x = f x`,
  let lemma = prove
   (`!f:A->B->bool P k.
        INFINITE {x | P x} /\ FINITE k /\
        (!x y. P x /\ P y /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> ?x. P x /\ DISJOINT k (f x)`,
    REWRITE_TAC[INFINITE] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[SET_RULE `(?x. P x /\ DISJOINT k (f x)) <=>
                          ~(!x. ?y. P x ==> y IN k /\ y IN f x)`] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `g:A->B`) THEN
    MP_TAC(ISPECL [`g:A->B`; `{x:A | P x}`] FINITE_IMAGE_INJ_EQ) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; NOT_IMP] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM SET_TAC[]) in
  SUBGOAL_THEN
   `!f:real^M->real^N s t u.
        compact s /\ convex u /\ bounded u /\ aff_dim t <= aff_dim u /\
        s SUBSET t /\ f continuous_on s /\ IMAGE f s SUBSET relative_frontier u
        ==> ?k g. FINITE k /\ DISJOINT k s /\
                  g continuous_on (t DIFF k) /\
                  IMAGE g (t DIFF k) SUBSET relative_frontier u /\
                  !x. x IN s ==> g x = f x`
  MP_TAC THENL
   [ALL_TAC;
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^M->real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `k INTER t:real^M->bool` THEN
    ASM_SIMP_TAC[FINITE_INTER; INTER_SUBSET] THEN
    REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC; ASM SET_TAC[]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]] THEN
  SUBGOAL_THEN
   `!f:real^M->real^N s t u.
        compact s /\ s SUBSET t /\ affine t /\
        convex u /\ bounded u /\ aff_dim t <= aff_dim u /\
        f continuous_on s /\ IMAGE f s SUBSET relative_frontier u
        ==> ?k g. FINITE k /\ DISJOINT k s /\
                  g continuous_on (t DIFF k) /\
                  IMAGE g (t DIFF k) SUBSET relative_frontier u /\
                  !x. x IN s ==> g x = f x`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `?k g. FINITE k /\ DISJOINT k s /\
            g continuous_on (affine hull t DIFF k) /\
            IMAGE g (affine hull t DIFF k) SUBSET relative_frontier u /\
            !x. x IN s ==> g x = (f:real^M->real^N) x`
    MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[AFF_DIM_AFFINE_HULL; AFFINE_AFFINE_HULL] THEN
      TRANS_TAC SUBSET_TRANS `t:real^M->bool` THEN
      ASM_REWRITE_TAC[HULL_SUBSET];
      REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET));
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
            SUBSET_TRANS)) THEN
        MATCH_MP_TAC IMAGE_SUBSET] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s DIFF k SUBSET t DIFF k`) THEN
      REWRITE_TAC[HULL_SUBSET]]] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THENL
   [ASM_CASES_TAC `relative_frontier(u:real^N->bool) = {}` THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[RELATIVE_FRONTIER_EQ_EMPTY]) THEN
      UNDISCH_TAC `bounded(u:real^N->bool)` THEN
      ASM_SIMP_TAC[AFFINE_BOUNDED_EQ_LOWDIM] THEN DISCH_TAC THEN
      SUBGOAL_THEN `aff_dim(t:real^M->bool) <= &0` MP_TAC THENL
       [ASM_INT_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[AFF_DIM_GE; INT_ARITH
       `--(&1):int <= x ==> (x <= &0 <=> x = --(&1) \/ x = &0)`] THEN
      REWRITE_TAC[AFF_DIM_EQ_MINUS1; AFF_DIM_EQ_0] THEN
      DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC `a:real^M`)) THEN
      EXISTS_TAC `{a:real^M}` THEN
      ASM_REWRITE_TAC[DISJOINT_EMPTY; FINITE_SING; NOT_IN_EMPTY;
                      EMPTY_DIFF; DIFF_EQ_EMPTY; IMAGE_CLAUSES;
                      CONTINUOUS_ON_EMPTY; EMPTY_SUBSET];
      EXISTS_TAC `{}:real^M->bool` THEN
      FIRST_X_ASSUM(X_CHOOSE_TAC `y:real^N` o
        GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      ASM_SIMP_TAC[FINITE_EMPTY; DISJOINT_EMPTY; NOT_IN_EMPTY; DIFF_EMPTY] THEN
      EXISTS_TAC `(\x. y):real^M->real^N` THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC) THEN
  REWRITE_TAC[INSERT_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`f:real^M->real^N`;
    `{interval[--(b + vec 1):real^M,b + vec 1] INTER t}`;
    `s:real^M->bool`; `u:real^N->bool`]
   EXTEND_MAP_CELL_COMPLEX_TO_SPHERE_COFINITE) THEN
  SUBGOAL_THEN
   `interval[--b,b] SUBSET interval[--(b + vec 1):real^M,b + vec 1]`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_INTERVAL; VECTOR_ADD_COMPONENT; VECTOR_NEG_COMPONENT;
                VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FINITE_SING] THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; IMP_IMP] THEN
  REWRITE_TAC[INTER_IDEMPOT; UNIONS_1; FACE_OF_REFL_EQ; SUBSET_INTER] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[HULL_SUBSET; COMPACT_IMP_CLOSED] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
      ASM_SIMP_TAC[POLYTOPE_INTERVAL; AFFINE_IMP_POLYHEDRON];
      TRANS_TAC INT_LE_TRANS `aff_dim(t:real^M->bool)` THEN
      ASM_SIMP_TAC[AFF_DIM_SUBSET; INTER_SUBSET];
      ASM_SIMP_TAC[CONVEX_INTER; CONVEX_INTERVAL; AFFINE_IMP_CONVEX];
      ASM SET_TAC[]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `g:real^M->real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `?d:real. (&1 / &2 <= d /\ d <= &1) /\
             DISJOINT k (frontier(interval[--(b + lambda i. d):real^M,
                                             (b + lambda i. d)]))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC lemma THEN
    ASM_SIMP_TAC[INFINITE; FINITE_REAL_INTERVAL; REAL_NOT_LE] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_WLOG_LT THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[frontier] THEN MATCH_MP_TAC(SET_RULE
     `c SUBSET i' ==> DISJOINT (c DIFF i) (c' DIFF i')`) THEN
    REWRITE_TAC[INTERIOR_INTERVAL; CLOSURE_INTERVAL] THEN
    SIMP_TAC[SUBSET_INTERVAL; VECTOR_NEG_COMPONENT; VECTOR_ADD_COMPONENT;
             LAMBDA_BETA] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c:real^M = b + lambda i. d` THEN SUBGOAL_THEN
   `interval[--b:real^M,b] SUBSET interval(--c,c) /\
    interval[--b:real^M,b] SUBSET interval[--c,c] /\
    interval[--c,c] SUBSET interval[--(b + vec 1):real^M,b + vec 1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_INTERVAL] THEN EXPAND_TAC "c" THEN REPEAT CONJ_TAC THEN
    SIMP_TAC[VECTOR_NEG_COMPONENT; VECTOR_ADD_COMPONENT; LAMBDA_BETA] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
    REWRITE_TAC[VEC_COMPONENT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC
   `(g:real^M->real^N) o
    closest_point (interval[--c,c] INTER t)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CLOSEST_POINT THEN
      ASM_SIMP_TAC[CONVEX_INTER; CLOSED_INTER; CLOSED_INTERVAL; CLOSED_AFFINE;
        AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL; CONVEX_INTERVAL] THEN
      ASM SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET))];
    REWRITE_TAC[IMAGE_o] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        SUBSET_TRANS)) THEN
    MATCH_MP_TAC IMAGE_SUBSET;
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    TRANS_TAC EQ_TRANS `(g:real^M->real^N) x` THEN
    CONJ_TAC THENL [AP_TERM_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CLOSEST_POINT_SELF THEN
    ASM_SIMP_TAC[IN_INTER; HULL_INC] THEN ASM SET_TAC[]] THEN
  (REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN
   X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN CONJ_TAC THENL
    [MATCH_MP_TAC(SET_RULE
      `closest_point s x IN s /\ s SUBSET u ==> closest_point s x IN u`) THEN
     CONJ_TAC THENL [MATCH_MP_TAC CLOSEST_POINT_IN_SET; ASM SET_TAC[]] THEN
     ASM_SIMP_TAC[CLOSED_INTER; CLOSED_INTERVAL; CLOSED_AFFINE] THEN
     ASM SET_TAC[];
     ALL_TAC] THEN
   ASM_CASES_TAC `x IN interval[--c:real^M,c]` THEN
   ASM_SIMP_TAC[CLOSEST_POINT_SELF; IN_INTER] THEN
   MATCH_MP_TAC(SET_RULE
    `closest_point s x IN relative_frontier s /\
     DISJOINT k (relative_frontier s)
     ==> ~(closest_point s x IN k)`) THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC CLOSEST_POINT_IN_RELATIVE_FRONTIER THEN
     ASM_SIMP_TAC[CLOSED_INTER; CLOSED_AFFINE; CLOSED_INTERVAL] THEN
     CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_DIFF]] THEN CONJ_TAC THENL
      [ALL_TAC; ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET; IN_INTER]] THEN
     ONCE_REWRITE_TAC[INTER_COMM] THEN
     W(MP_TAC o PART_MATCH (lhs o rand)
       AFFINE_HULL_CONVEX_INTER_NONEMPTY_INTERIOR o rand o snd) THEN
     ASM_SIMP_TAC[HULL_HULL; AFFINE_AFFINE_HULL; AFFINE_IMP_CONVEX] THEN
     ASM_SIMP_TAC[HULL_P] THEN ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
     REWRITE_TAC[INTERIOR_INTERVAL] THEN ASM SET_TAC[];
     W(MP_TAC o PART_MATCH (lhs o rand) RELATIVE_FRONTIER_CONVEX_INTER_AFFINE o
       rand o snd) THEN
     ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
     REWRITE_TAC[CONVEX_INTERVAL; AFFINE_AFFINE_HULL; INTERIOR_INTERVAL] THEN
     ASM SET_TAC[]]));;

let EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_GEN = prove
 (`!f:real^M->real^N s t u p.
        compact s /\ convex u /\ bounded u /\
        affine t /\ aff_dim t <= aff_dim u /\ s SUBSET t /\
        f continuous_on s /\ IMAGE f s SUBSET relative_frontier u /\
        (!c. c IN components(t DIFF s) /\ bounded c ==> ~(c INTER p = {}))
        ==> ?k g. FINITE k /\ k SUBSET p /\ k SUBSET t /\ DISJOINT k s /\
                  g continuous_on (t DIFF k) /\
                  IMAGE g (t DIFF k) SUBSET relative_frontier u /\
                  !x. x IN s ==> g x = f x`,
  let lemma0 = prove
   (`!u t s v. closed_in (subtopology euclidean u) v /\ t SUBSET u /\
               s = v INTER t
               ==> closed_in (subtopology euclidean t) s`,
    REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_CLOSED; LEFT_AND_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]) in
  let lemma1 = prove
   (`!f:A->B->bool P k.
        INFINITE {x | P x} /\ FINITE k /\
        (!x y. P x /\ P y /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> ?x. P x /\ DISJOINT k (f x)`,
    REWRITE_TAC[INFINITE] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[SET_RULE `(?x. P x /\ DISJOINT k (f x)) <=>
                          ~(!x. ?y. P x ==> y IN k /\ y IN f x)`] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `g:A->B`) THEN
    MP_TAC(ISPECL [`g:A->B`; `{x:A | P x}`] FINITE_IMAGE_INJ_EQ) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; NOT_IMP] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM SET_TAC[]) in
  let lemma2 = prove
   (`!f:real^M->real^N s t k p u.
          FINITE k /\ affine u /\
          f continuous_on ((u:real^M->bool) DIFF k) /\
          IMAGE f ((u:real^M->bool) DIFF k) SUBSET t /\
          (!c. c IN components((u:real^M->bool) DIFF s) /\ ~(c INTER k = {})
               ==> ~(c INTER p = {})) /\
          closed_in (subtopology euclidean u) s /\ DISJOINT k s /\ k SUBSET u
          ==> ?g. g continuous_on ((u:real^M->bool) DIFF p) /\
                  IMAGE g ((u:real^M->bool) DIFF p) SUBSET t /\
                  !x. x IN s ==> g x = f x`,
    REPEAT GEN_TAC THEN ASM_CASES_TAC `k:real^M->bool = {}` THENL
     [ASM_REWRITE_TAC[DIFF_EMPTY] THEN REPEAT STRIP_TAC THEN
      EXISTS_TAC `f:real^M->real^N` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_DIFF]; ASM SET_TAC[]];
      STRIP_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
    SUBGOAL_THEN `~(((u:real^M->bool) DIFF s) INTER k = {})` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o LAND_CONV)
     [UNIONS_COMPONENTS] THEN
    REWRITE_TAC[INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `co:real^M->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `locally connected (u:real^M->bool)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[AFFINE_IMP_CONVEX; CONVEX_IMP_LOCALLY_CONNECTED];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!c. c IN components ((u:real^M->bool) DIFF s) /\ ~(c INTER k = {})
          ==> ?a g. a IN c /\ a IN p /\
                    g continuous_on (s UNION (c DELETE a)) /\
                    IMAGE g (s UNION (c DELETE a)) SUBSET t /\
                    !x. x IN s ==> g x = (f:real^M->real^N) x`
    MP_TAC THENL
     [X_GEN_TAC `c:real^M->bool` THEN STRIP_TAC THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `c:real^M->bool`) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^M` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `open_in (subtopology euclidean u) (c:real^M->bool)`
      MP_TAC THENL
       [MATCH_MP_TAC OPEN_IN_TRANS THEN
        EXISTS_TAC `u DIFF s:real^M->bool` THEN
        ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL] THEN
        MATCH_MP_TAC OPEN_IN_COMPONENTS_LOCALLY_CONNECTED THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
        EXISTS_TAC `u:real^M->bool` THEN
        ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL];
        DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th)] THEN
      REWRITE_TAC[OPEN_IN_CONTAINS_CBALL] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `a:real^M`)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `ball(a:real^M,d) INTER u SUBSET c` ASSUME_TAC THENL
       [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS;
                      SET_RULE `b SUBSET c ==> b INTER u SUBSET c INTER u`];
        ALL_TAC] THEN
      MP_TAC(ISPECL
      [`ball(a:real^M,d) INTER u`; `c:real^M->bool`;
        `s UNION c:real^M->bool`; `c INTER k:real^M->bool`]
          HOMEOMORPHISM_GROUPING_POINTS_EXISTS_GEN) THEN
      ASM_REWRITE_TAC[INTER_SUBSET; SUBSET_UNION; UNION_SUBSET] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
          EXISTS_TAC `u:real^M->bool` THEN
          ASM_SIMP_TAC[HULL_MINIMAL; HULL_SUBSET];
          MP_TAC(ISPECL [`c:real^M->bool`; `u:real^M->bool`]
             AFFINE_HULL_OPEN_IN) THEN
          ASM_SIMP_TAC[HULL_P] THEN ASM SET_TAC[];
          REWRITE_TAC[HULL_SUBSET];
          ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
          ASM_MESON_TAC[FINITE_SUBSET; INTER_SUBSET];
          MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
          EXISTS_TAC `u:real^M->bool` THEN
          ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL; INTER_COMM];
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
          EXISTS_TAC `a:real^M` THEN REWRITE_TAC[CENTRE_IN_BALL] THEN
          ASM SET_TAC[]];
        REWRITE_TAC[IN_INTER; LEFT_IMP_EXISTS_THM]] THEN
      MAP_EVERY X_GEN_TAC [`h:real^M->real^M`; `k:real^M->real^M`] THEN
      REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`cball(a:real^M,d) INTER u`; `a:real^M`]
          RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL) THEN
      MP_TAC(ISPECL [`cball(a:real^M,d)`; `u:real^M->bool`]
          RELATIVE_INTERIOR_CONVEX_INTER_AFFINE) THEN
      MP_TAC(ISPECL [`cball(a:real^M,d)`; `u:real^M->bool`]
          RELATIVE_FRONTIER_CONVEX_INTER_AFFINE) THEN
      MP_TAC(ISPECL [`u:real^M->bool`; `cball(a:real^M,d)`]
          (ONCE_REWRITE_RULE[INTER_COMM]
             AFFINE_HULL_AFFINE_INTER_NONEMPTY_INTERIOR)) THEN
      ASM_SIMP_TAC[CONVEX_CBALL; FRONTIER_CBALL; INTERIOR_CBALL] THEN
      SUBGOAL_THEN `a IN ball(a:real^M,d) INTER u` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[CENTRE_IN_BALL; IN_INTER] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      REPLICATE_TAC 3
       (ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
      ASM_SIMP_TAC[CONVEX_INTER; CONVEX_CBALL; AFFINE_IMP_CONVEX] THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[BOUNDED_SUBSET; INTER_SUBSET; BOUNDED_CBALL];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[retract_of; retraction] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^M->real^M` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC
       `(f:real^M->real^N) o (k:real^M->real^M) o
        (\x. if x IN ball(a,d) then r x else x)` THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [ALL_TAC;
        X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
        COND_CASES_TAC THENL
         [ASM SET_TAC[]; AP_TERM_TAC THEN ASM SET_TAC[]]] THEN
      ABBREV_TAC `j = \x:real^M. if x IN ball(a,d) then r x else x` THEN
      SUBGOAL_THEN
       `(j:real^M->real^M) continuous_on ((u:real^M->bool) DELETE a)`
      ASSUME_TAC THENL
       [EXPAND_TAC "j" THEN
        SUBGOAL_THEN
         `u DELETE (a:real^M) =
          (cball(a,d) DELETE a) INTER u UNION
          ((u:real^M->bool) DIFF ball(a,d))`
         (fun th -> SUBST1_TAC th THEN
                    MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
                    SUBST1_TAC(SYM th))
        THENL
         [MP_TAC(ISPECL [`a:real^M`; `d:real`] BALL_SUBSET_CBALL) THEN
          ASM SET_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[IN_DIFF; IN_INTER; IN_DELETE; CONTINUOUS_ON_ID] THEN
        REPEAT CONJ_TAC THENL
         [ALL_TAC; ALL_TAC;
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
          REWRITE_TAC[GSYM BALL_UNION_SPHERE] THEN ASM SET_TAC[]] THEN
        REWRITE_TAC[CLOSED_IN_CLOSED] THENL
         [EXISTS_TAC `cball(a:real^M,d)` THEN REWRITE_TAC[CLOSED_CBALL];
          EXISTS_TAC `(:real^M) DIFF ball(a,d)` THEN
          REWRITE_TAC[GSYM OPEN_CLOSED; OPEN_BALL]] THEN
        MP_TAC(ISPECL [`a:real^M`; `d:real`] BALL_SUBSET_CBALL) THEN
        MP_TAC(ISPECL [`a:real^M`; `d:real`] CENTRE_IN_BALL) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `IMAGE (j:real^M->real^M) (s UNION c DELETE a) SUBSET
        (s UNION c DIFF ball(a,d))`
      ASSUME_TAC THENL
       [EXPAND_TAC "j" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
        COND_CASES_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        SUBGOAL_THEN `(r:real^M->real^M) x IN sphere(a,d)` MP_TAC THENL
         [MP_TAC(ISPECL [`a:real^M`; `d:real`] CENTRE_IN_BALL) THEN
          ASM SET_TAC[];
          REWRITE_TAC[GSYM CBALL_DIFF_BALL] THEN ASM SET_TAC[]];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET))
        THENL [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC];
        ONCE_REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (SET_RULE `IMAGE f u SUBSET t
                    ==> s SUBSET u ==> IMAGE f s SUBSET t`))] THEN
      REWRITE_TAC[IMAGE_o] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `s SUBSET u ==> IMAGE f u SUBSET t ==> IMAGE f s SUBSET t`)) THEN
      REWRITE_TAC[SUBSET; IN_UNIV; IN_DIFF; FORALL_IN_IMAGE] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`a:(real^M->bool)->real^M`; `h:(real^M->bool)->real^M->real^N`] THEN
    DISCH_TAC THEN MP_TAC(ISPECL
     [`subtopology euclidean
        (s UNION UNIONS
         { c DELETE (a c) |
           c IN components ((u:real^M->bool) DIFF s) /\ ~(c INTER k = {})})`;
      `euclidean:(real^N)topology`;
      `h:(real^M->bool)->real^M->real^N`;
      `\c:real^M->bool. s UNION (c DELETE (a c))`;
      `{c | c IN components ((u:real^M->bool) DIFF s) /\ ~(c INTER k = {})}`]
     PASTING_LEMMA_EXISTS_CLOSED) THEN
    REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                SUBTOPOLOGY_SUBTOPOLOGY] THEN
    ONCE_REWRITE_TAC[TAUT`closed_in a b /\ c <=> ~(closed_in a b ==> ~c)`] THEN
    SIMP_TAC[ISPEC `euclidean` CLOSED_IN_IMP_SUBSET;
             SET_RULE `s SUBSET u ==> u INTER s = s`] THEN
    REWRITE_TAC[NOT_IMP] THEN
    SUBGOAL_THEN
     `FINITE {c | c IN components((u:real^M->bool) DIFF s) /\
                  ~(c INTER k = {})}`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`\c:real^M->bool. c INTER k`;
        `{c | c IN components ((u:real^M->bool) DIFF s) /\ ~(c INTER k = {})}`]
       FINITE_IMAGE_INJ_EQ) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
       [MESON_TAC[COMPONENTS_EQ;
                  SET_RULE
                    `s INTER k = t INTER k /\ ~(s INTER k = {})
                     ==> ~(s INTER t = {})`];
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[GSYM SIMPLE_IMAGE; IN_ELIM_THM]] THEN
      MP_TAC(ISPEC
       `{c INTER k |c| c IN components((u:real^M->bool) DIFF s) /\
                       ~(c INTER k = {})}`
        FINITE_UNIONS) THEN
      MATCH_MP_TAC(TAUT `p ==> (p <=> q /\ r) ==> q`) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        FINITE_SUBSET)) THEN
      REWRITE_TAC[UNIONS_GSPEC] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; SUBSET_UNIV] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[UNIONS_GSPEC] THEN ASM SET_TAC[];
        X_GEN_TAC `c:real^M->bool` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC lemma0 THEN
        MAP_EVERY EXISTS_TAC [`u:real^M->bool`; `s UNION c:real^M->bool`] THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC CLOSED_IN_UNION_COMPLEMENT_COMPONENT THEN
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
          MESON_TAC[IN_COMPONENTS_SUBSET;
                    SET_RULE `c SUBSET u DIFF s ==> c DELETE a SUBSET u`];
          ASM_SIMP_TAC[CLOSED_UNION_COMPLEMENT_COMPONENT; UNIONS_GSPEC] THEN
          MATCH_MP_TAC(SET_RULE
           `~(a IN t) /\ c DELETE a SUBSET t
            ==> s UNION c DELETE a = (s UNION c) INTER (s UNION t)`) THEN
          CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
          REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN
          DISCH_THEN(X_CHOOSE_THEN `c':real^M->bool` STRIP_ASSUME_TAC) THEN
          MP_TAC(ISPECL [`(u:real^M->bool) DIFF s`;
                          `c:real^M->bool`; `c':real^M->bool`]
            COMPONENTS_EQ) THEN
          ASM_CASES_TAC `c':real^M->bool = c` THENL
           [ASM_MESON_TAC[]; ALL_TAC] THEN
          ASM SET_TAC[]];
        MAP_EVERY X_GEN_TAC
         [`c1:real^M->bool`; `c2:real^M->bool`; `x:real^M`] THEN
        STRIP_TAC THEN ASM_CASES_TAC `c2:real^M->bool = c1` THEN
        ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
          `x IN u INTER (s UNION c1 DELETE a) INTER (s UNION c2 DELETE b)
           ==> (c1 INTER c2 = {}) ==> x IN s`)) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[COMPONENTS_EQ]; ASM_SIMP_TAC[]]];
      DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC)] THEN
    MP_TAC
     (ISPECL [`\x. x IN s UNION
                        UNIONS {c | c IN components((u:real^M->bool) DIFF s) /\
                                    c INTER k = {}}`;
              `f:real^M->real^N`;
              `g:real^M->real^N`;
              `s UNION
               UNIONS {c | c IN components((u:real^M->bool) DIFF s) /\
                           c INTER k = {}}`;
              `s UNION
               UNIONS { c DELETE (a c) |
                        c IN components((u:real^M->bool) DIFF s) /\
                        ~(c INTER k = {})}`]
          CONTINUOUS_ON_CASES_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC lemma0 THEN EXISTS_TAC `u:real^M->bool` THEN
        EXISTS_TAC `u DIFF
                    UNIONS {c DELETE a c |
                            c IN components ((u:real^M->bool) DIFF s) /\
                            ~(c INTER k = {})}` THEN
        REPEAT CONJ_TAC THENL
          [MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL] THEN
           MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
           X_GEN_TAC `c:real^M->bool` THEN DISCH_TAC THEN
           MATCH_MP_TAC OPEN_IN_DELETE THEN MATCH_MP_TAC OPEN_IN_TRANS THEN
           EXISTS_TAC `u DIFF s:real^M->bool` THEN
           ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL] THEN
           MATCH_MP_TAC OPEN_IN_COMPONENTS_LOCALLY_CONNECTED THEN
           ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
           EXISTS_TAC `u:real^M->bool` THEN
           ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_REFL];
           ASM_REWRITE_TAC[UNION_SUBSET] THEN
           REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
           MESON_TAC[IN_COMPONENTS_SUBSET;
                     SET_RULE `c SUBSET u DIFF s ==> c DELETE a SUBSET u /\
                                                     c SUBSET u`];
           REWRITE_TAC[SET_RULE
            `(s UNION t) UNION (s UNION u) = (s UNION t) UNION u`] THEN
           MATCH_MP_TAC(SET_RULE
            `s SUBSET u /\ t INTER s = {}
             ==> s = (u DIFF t) INTER (s UNION t)`) THEN
           CONJ_TAC THENL
            [ASM_REWRITE_TAC[UNION_SUBSET] THEN
             REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
             MESON_TAC[IN_COMPONENTS_SUBSET;
                       SET_RULE `c SUBSET u DIFF s ==> c DELETE a SUBSET u /\
                                                       c SUBSET u`];
             ALL_TAC] THEN
           REWRITE_TAC[EMPTY_UNION; SET_RULE
            `c INTER (s UNION t) = (s INTER c) UNION (c INTER t)`] THEN
           CONJ_TAC THENL
            [MATCH_MP_TAC(SET_RULE
              `t SUBSET UNIV DIFF s ==> s INTER t = {}`) THEN
             REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN GEN_TAC THEN
             DISCH_THEN(CONJUNCTS_THEN2
               (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)
               MP_TAC) THEN ASM SET_TAC[];
             REWRITE_TAC[INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
             X_GEN_TAC `c:real^M->bool` THEN STRIP_TAC THEN
             X_GEN_TAC `c':real^M->bool` THEN STRIP_TAC THEN
             MP_TAC(ISPECL [`(u:real^M->bool) DIFF s`;
                            `c:real^M->bool`; `c':real^M->bool`]
               COMPONENTS_EQ) THEN
             ASM_CASES_TAC `c':real^M->bool = c` THENL
              [ASM_MESON_TAC[]; ASM SET_TAC[]]]];
        MATCH_MP_TAC lemma0 THEN EXISTS_TAC `u:real^M->bool` THEN
        EXISTS_TAC
         `UNIONS {s UNION c |c| c IN components ((u:real^M->bool) DIFF s) /\
                                ~(c INTER k = {})}` THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC CLOSED_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
          ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
          ASM_SIMP_TAC[FINITE_IMAGE] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC CLOSED_IN_UNION_COMPLEMENT_COMPONENT THEN
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[UNION_SUBSET] THEN
          REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
          MESON_TAC[IN_COMPONENTS_SUBSET;
                    SET_RULE `c SUBSET u DIFF s ==> c DELETE a SUBSET u /\
                                                    c SUBSET u`];
          MATCH_MP_TAC(SET_RULE
           `t SUBSET u /\ u INTER s SUBSET t ==> t = u INTER (s UNION t)`) THEN
          CONJ_TAC THENL
           [REWRITE_TAC[UNIONS_GSPEC] THEN ASM SET_TAC[]; ALL_TAC] THEN
          MATCH_MP_TAC(SET_RULE
           `u INTER t SUBSET s ==> u INTER (s UNION t) SUBSET s UNION v`) THEN
          MATCH_MP_TAC(SET_RULE
          `((UNIV DIFF s) INTER t) INTER u SUBSET s
           ==> t INTER u SUBSET s`) THEN
          GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
           [INTER_UNIONS] THEN
          REWRITE_TAC[SET_RULE
           `{g x | x IN {f y | P y}} = {g(f y) | P y}`] THEN
          REWRITE_TAC[SET_RULE
           `(UNIV DIFF s) INTER (s UNION c) = c DIFF s`] THEN
          REWRITE_TAC[SET_RULE
           `t INTER u SUBSET s <=> t INTER ((UNIV DIFF s) INTER u) = {}`] THEN
          ONCE_REWRITE_TAC[INTER_UNIONS] THEN
          REWRITE_TAC[EMPTY_UNIONS; FORALL_IN_GSPEC; INTER_UNIONS] THEN
          X_GEN_TAC `c:real^M->bool` THEN STRIP_TAC THEN
          X_GEN_TAC `c':real^M->bool` THEN STRIP_TAC THEN
          MP_TAC(ISPECL [`(u:real^M->bool) DIFF s`;
               `c:real^M->bool`; `c':real^M->bool`]
            COMPONENTS_EQ) THEN
          ASM_CASES_TAC `c':real^M->bool = c` THENL
           [ASM_MESON_TAC[]; ASM SET_TAC[]]];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[UNION_SUBSET] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
        GEN_TAC THEN
        DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)
          MP_TAC) THEN ASM SET_TAC[];
        REWRITE_TAC[TAUT `p /\ ~p <=> F`] THEN X_GEN_TAC `x:real^M` THEN
        REWRITE_TAC[IN_UNION] THEN
        ASM_CASES_TAC `(x:real^M) IN s` THEN ASM_REWRITE_TAC[] THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_DELETE] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `c:real^M->bool`)
          (X_CHOOSE_TAC `c':real^M->bool`)) THEN
        MP_TAC(ISPECL [`(u:real^M->bool) DIFF s`;
                        `c:real^M->bool`; `c':real^M->bool`]
            COMPONENTS_EQ) THEN
        ASM_CASES_TAC `c':real^M->bool = c` THENL
         [ASM_MESON_TAC[]; ASM SET_TAC[]]];
      MATCH_MP_TAC(MESON[CONTINUOUS_ON_SUBSET]
       `t SUBSET s /\ P f
        ==> f continuous_on s ==> ?g. g continuous_on t /\ P g`) THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[SET_RULE
         `(s UNION t) UNION (s UNION u) = s UNION (t UNION u)`] THEN
        MATCH_MP_TAC(SET_RULE
         `(u DIFF s) DIFF p SUBSET t
          ==> u DIFF p SUBSET s UNION t`) THEN
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [UNIONS_COMPONENTS] THEN
        REWRITE_TAC[UNIONS_GSPEC] THEN ASM SET_TAC[];
        SIMP_TAC[IN_UNION]] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_UNION; IN_UNIV] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(x:real^M) IN s` THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN COND_CASES_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
        `x IN ((u:real^M->bool) DIFF s)` MP_TAC THENL
          [ASM SET_TAC[]; ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [UNIONS_COMPONENTS] THEN
      REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real^M->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
      DISCH_THEN(MP_TAC o SPEC `c:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `c:real^M->bool`]) THEN
      ASM_REWRITE_TAC[UNIONS_GSPEC] THEN ASM SET_TAC[]]) in
  let lemma3 = prove
   (`!f:real^M->real^N s t u p.
          compact s /\ convex u /\ bounded u /\
          affine t /\ aff_dim t <= aff_dim u /\ s SUBSET t /\
          f continuous_on s /\ IMAGE f s SUBSET relative_frontier u /\
          (!c. c IN components(t DIFF s) ==> ~(c INTER p = {}))
          ==> ?k g. FINITE k /\ k SUBSET p /\ k SUBSET t /\ DISJOINT k s /\
                    g continuous_on (t DIFF k) /\
                    IMAGE g (t DIFF k) SUBSET relative_frontier u /\
                    !x. x IN s ==> g x = f x`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`;
                   `t:real^M->bool`; `u:real^N->bool`]
          EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_SIMPLE) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `g:real^M->real^N`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `!x. ?y. x IN k
              ==> ?c. c IN components (t DIFF s:real^M->bool) /\
                      x IN c /\ y IN c /\ y IN p`
    MP_TAC THENL
     [X_GEN_TAC `x:real^M` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^M) IN (t DIFF s)` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [UNIONS_COMPONENTS] THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
      REWRITE_TAC[IN_UNIONS; RIGHT_EXISTS_AND_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
      REWRITE_TAC[SKOLEM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^M` (LABEL_TAC "*"))] THEN
    EXISTS_TAC `IMAGE (h:real^M->real^M) k` THEN
    MP_TAC(ISPECL
     [`g:real^M->real^N`; `s:real^M->bool`;
      `relative_frontier u:real^N->bool`; `k:real^M->bool`;
      `IMAGE (h:real^M->real^M) k`; `t:real^M->bool`] lemma2) THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; FINITE_IMAGE] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `c:real^M->bool` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
        ONCE_REWRITE_TAC[INTER_COMM] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; EXISTS_IN_IMAGE; IN_INTER] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^M` THEN
        STRIP_TAC THEN REMOVE_THEN "*" (MP_TAC o SPEC `x:real^M`) THEN
        ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC `c':real^M->bool` THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`(t:real^M->bool) DIFF s`;
                       `c:real^M->bool`; `c':real^M->bool`]
          COMPONENTS_EQ) THEN
        ASM_CASES_TAC `c':real^M->bool = c` THENL [ALL_TAC; ASM SET_TAC[]] THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
        EXISTS_TAC `(:real^M)` THEN
        ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED; SUBSET_UNIV]];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^M->real^N` THEN
      STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[SET_RULE `DISJOINT s t <=> !x. x IN s ==> ~(x IN t)`] THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET; IN_DIFF]]) in
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THENL
   [ASM_CASES_TAC `relative_frontier(u:real^N->bool) = {}` THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[RELATIVE_FRONTIER_EQ_EMPTY]) THEN
      UNDISCH_TAC `bounded(u:real^N->bool)` THEN
      ASM_SIMP_TAC[AFFINE_BOUNDED_EQ_LOWDIM] THEN DISCH_TAC THEN
      SUBGOAL_THEN `aff_dim(t:real^M->bool) <= &0` MP_TAC THENL
       [ASM_INT_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[AFF_DIM_GE; INT_ARITH
       `--(&1):int <= x ==> (x <= &0 <=> x = --(&1) \/ x = &0)`] THEN
      REWRITE_TAC[AFF_DIM_EQ_MINUS1; AFF_DIM_EQ_0] THEN
      DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC `a:real^M`)) THENL
       [EXISTS_TAC `{}:real^M->bool` THEN
        ASM_REWRITE_TAC[EMPTY_DIFF; FINITE_EMPTY; CONTINUOUS_ON_EMPTY;
                        IMAGE_CLAUSES; NOT_IN_EMPTY] THEN
        SET_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `{a:real^M}`) THEN
        ASM_REWRITE_TAC[DIFF_EMPTY; IN_COMPONENTS_SELF] THEN
        REWRITE_TAC[CONNECTED_SING; NOT_INSERT_EMPTY; BOUNDED_SING] THEN
        DISCH_TAC THEN EXISTS_TAC `{a:real^M}` THEN
        ASM_REWRITE_TAC[DIFF_EQ_EMPTY; CONTINUOUS_ON_EMPTY; NOT_IN_EMPTY;
                        FINITE_SING; IMAGE_CLAUSES; EMPTY_SUBSET] THEN
        ASM SET_TAC[]];
      EXISTS_TAC `{}:real^M->bool` THEN
      FIRST_X_ASSUM(X_CHOOSE_TAC `y:real^N` o
        GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      ASM_SIMP_TAC[FINITE_EMPTY; DISJOINT_EMPTY; NOT_IN_EMPTY; DIFF_EMPTY] THEN
      EXISTS_TAC `(\x. y):real^M->real^N` THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC) THEN
  REWRITE_TAC[INSERT_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`f:real^M->real^N`; `s:real^M->bool`;
    `t:real^M->bool`; `u:real^N->bool`;
    `p UNION (UNIONS {c | c IN components (t DIFF s) /\ ~bounded c} DIFF
              interval[--(b + vec 1):real^M,b + vec 1])`]
        lemma3) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `c:real^M->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `bounded(c:real^M->bool)` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `c:real^M->bool`) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(c SUBSET interval[--(b + vec 1):real^M,b + vec 1])`
    MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_MESON_TAC[BOUNDED_SUBSET; BOUNDED_INTERVAL];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `g:real^M->real^N`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `k INTER interval[--(b + vec 1):real^M,b + vec 1]` THEN
  ASM_SIMP_TAC[FINITE_INTER; RIGHT_EXISTS_AND_THM] THEN
  REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  SUBGOAL_THEN
   `interval[--b,b] SUBSET interval[--(b + vec 1):real^M,b + vec 1]`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_INTERVAL; VECTOR_ADD_COMPONENT; VECTOR_NEG_COMPONENT;
                VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d:real. (&1 / &2 <= d /\ d <= &1) /\
             DISJOINT k (frontier(interval[--(b + lambda i. d):real^M,
                                             (b + lambda i. d)]))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC lemma1 THEN
    ASM_SIMP_TAC[INFINITE; FINITE_REAL_INTERVAL; REAL_NOT_LE] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_WLOG_LT THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[frontier] THEN MATCH_MP_TAC(SET_RULE
     `c SUBSET i' ==> DISJOINT (c DIFF i) (c' DIFF i')`) THEN
    REWRITE_TAC[INTERIOR_INTERVAL; CLOSURE_INTERVAL] THEN
    SIMP_TAC[SUBSET_INTERVAL; VECTOR_NEG_COMPONENT; VECTOR_ADD_COMPONENT;
             LAMBDA_BETA] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c:real^M = b + lambda i. d` THEN SUBGOAL_THEN
   `interval[--b:real^M,b] SUBSET interval(--c,c) /\
    interval[--b:real^M,b] SUBSET interval[--c,c] /\
    interval[--c,c] SUBSET interval[--(b + vec 1):real^M,b + vec 1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_INTERVAL] THEN EXPAND_TAC "c" THEN REPEAT CONJ_TAC THEN
    SIMP_TAC[VECTOR_NEG_COMPONENT; VECTOR_ADD_COMPONENT; LAMBDA_BETA] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
    REWRITE_TAC[VEC_COMPONENT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC
   `(g:real^M->real^N) o
    closest_point (interval[--c,c] INTER t)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CLOSEST_POINT THEN
      ASM_SIMP_TAC[CONVEX_INTER; CLOSED_INTER; CLOSED_INTERVAL; CLOSED_AFFINE;
        AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL; CONVEX_INTERVAL] THEN
      ASM SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET))];
    REWRITE_TAC[IMAGE_o] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        SUBSET_TRANS)) THEN
    MATCH_MP_TAC IMAGE_SUBSET;
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    TRANS_TAC EQ_TRANS `(g:real^M->real^N) x` THEN
    CONJ_TAC THENL [AP_TERM_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CLOSEST_POINT_SELF THEN
    ASM_SIMP_TAC[IN_INTER; HULL_INC] THEN ASM SET_TAC[]] THEN
  (REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN
   X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN CONJ_TAC THENL
    [MATCH_MP_TAC(SET_RULE
      `closest_point s x IN s /\ s SUBSET u ==> closest_point s x IN u`) THEN
     CONJ_TAC THENL [MATCH_MP_TAC CLOSEST_POINT_IN_SET; ASM SET_TAC[]] THEN
     ASM_SIMP_TAC[CLOSED_INTER; CLOSED_INTERVAL; CLOSED_AFFINE] THEN
     ASM SET_TAC[];
     ALL_TAC] THEN
   ASM_CASES_TAC `x IN interval[--c:real^M,c]` THEN
   ASM_SIMP_TAC[CLOSEST_POINT_SELF; IN_INTER] THENL
    [ASM SET_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC(SET_RULE
    `closest_point s x IN relative_frontier s /\
     DISJOINT k (relative_frontier s)
     ==> ~(closest_point s x IN k)`) THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC CLOSEST_POINT_IN_RELATIVE_FRONTIER THEN
     ASM_SIMP_TAC[CLOSED_INTER; CLOSED_AFFINE; CLOSED_INTERVAL] THEN
     CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_DIFF]] THEN CONJ_TAC THENL
      [ALL_TAC; ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET; IN_INTER]] THEN
     ONCE_REWRITE_TAC[INTER_COMM] THEN
     W(MP_TAC o PART_MATCH (lhs o rand)
       AFFINE_HULL_CONVEX_INTER_NONEMPTY_INTERIOR o rand o snd) THEN
     ASM_SIMP_TAC[HULL_HULL; AFFINE_AFFINE_HULL; AFFINE_IMP_CONVEX] THEN
     ASM_SIMP_TAC[HULL_P] THEN ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
     REWRITE_TAC[INTERIOR_INTERVAL] THEN ASM SET_TAC[];
     W(MP_TAC o PART_MATCH (lhs o rand) RELATIVE_FRONTIER_CONVEX_INTER_AFFINE o
       rand o snd) THEN
     ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
     REWRITE_TAC[CONVEX_INTERVAL; AFFINE_AFFINE_HULL; INTERIOR_INTERVAL] THEN
     ASM SET_TAC[]]));;

let EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE = prove
 (`!f:real^M->real^N s t a r p.
        compact s /\ affine t /\ aff_dim t <= &(dimindex(:N)) /\ s SUBSET t /\
        &0 <= r /\ f continuous_on s /\ IMAGE f s SUBSET sphere(a,r) /\
        (!c. c IN components(t DIFF s) /\ bounded c ==> ~(c INTER p = {}))
        ==> ?k g. FINITE k /\ k SUBSET p /\ k SUBSET t /\ DISJOINT k s /\
                  g continuous_on (t DIFF k) /\
                  IMAGE g (t DIFF k) SUBSET sphere(a,r) /\
                  !x. x IN s ==> g x = f x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r = &0` THENL
   [ASM_SIMP_TAC[SPHERE_SING] THEN STRIP_TAC THEN
    EXISTS_TAC `{}:real^M->bool` THEN
    EXISTS_TAC `(\x. a):real^M->real^N` THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; FINITE_EMPTY] THEN ASM SET_TAC[];
    MP_TAC(ISPECL [`a:real^N`; `r:real`] RELATIVE_FRONTIER_CBALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    STRIP_TAC THEN MATCH_MP_TAC EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_GEN THEN
    ASM_REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; AFF_DIM_CBALL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let EXTEND_MAP_UNIV_TO_SPHERE_COFINITE = prove
 (`!f:real^M->real^N s a r p.
     dimindex(:M) <= dimindex(:N) /\ &0 <= r /\
     compact s /\ f continuous_on s /\ IMAGE f s SUBSET sphere(a,r) /\
     (!c. c IN components((:real^M) DIFF s) /\ bounded c
          ==> ~(c INTER p = {}))
     ==> ?k g. FINITE k /\ k SUBSET p /\ DISJOINT k s /\
               g continuous_on ((:real^M) DIFF k) /\
               IMAGE g ((:real^M) DIFF k) SUBSET sphere(a,r) /\
               !x. x IN s ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`; `(:real^M)`;
                 `a:real^N`; `r:real`; `p:real^M->bool`]
        EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE) THEN
  ASM_REWRITE_TAC[AFFINE_UNIV; SUBSET_UNIV; AFF_DIM_UNIV; INT_OF_NUM_LE]);;

let EXTEND_MAP_UNIV_TO_SPHERE_NO_BOUNDED_COMPONENT = prove
 (`!f:real^M->real^N s a r.
     dimindex(:M) <= dimindex(:N) /\ &0 <= r /\
     compact s /\ f continuous_on s /\ IMAGE f s SUBSET sphere(a,r) /\
     (!c. c IN components((:real^M) DIFF s) ==> ~bounded c)
     ==> ?g. g continuous_on (:real^M) /\
             IMAGE g (:real^M) SUBSET sphere(a,r) /\
             !x. x IN s ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`;  `a:real^N`; `r:real`;
                 `{}:real^M->bool`] EXTEND_MAP_UNIV_TO_SPHERE_COFINITE) THEN
  ASM_SIMP_TAC[IMP_CONJ; SUBSET_EMPTY; RIGHT_EXISTS_AND_THM] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
  REWRITE_TAC[UNWIND_THM2; FINITE_EMPTY; DISJOINT_EMPTY; DIFF_EMPTY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]);;

let EXTEND_MAP_SPHERE_TO_SPHERE_GEN = prove
 (`!f:real^M->real^N c s t.
        closed c /\ c SUBSET relative_frontier s /\ convex s /\ bounded s /\
        convex t /\ bounded t /\ aff_dim s <= aff_dim t /\
        f continuous_on c /\ IMAGE f c SUBSET relative_frontier t
         ==> ?g. g continuous_on (relative_frontier s) /\
                 IMAGE g (relative_frontier s) SUBSET relative_frontier t /\
                 !x. x IN c ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?p:real^M->bool. polytope p /\ aff_dim p = aff_dim(s:real^M->bool)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC CHOOSE_POLYTOPE THEN
    ASM_REWRITE_TAC[AFF_DIM_GE; AFF_DIM_LE_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `p:real^M->bool`]
        HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS) THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_BOUNDED; homeomorphic] THEN
  REWRITE_TAC[HOMEOMORPHISM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:real^M->real^M`; `k:real^M->real^M`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`(f:real^M->real^N) o (k:real^M->real^M)`;
    `{f:real^M->bool | f face_of p /\ ~(f = p)}`;
    `IMAGE (h:real^M->real^M) c`;
    `t:real^N->bool`] EXTEND_MAP_CELL_COMPLEX_TO_SPHERE) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[GSYM RELATIVE_FRONTIER_OF_POLYHEDRON_ALT;
               POLYTOPE_IMP_POLYHEDRON] THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM IMAGE_o; o_THM] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{f:real^M->bool | f face_of p}` THEN
      ASM_SIMP_TAC[FINITE_POLYTOPE_FACES] THEN SET_TAC[];
      ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE;
                    FACE_OF_AFF_DIM_LT; POLYTOPE_IMP_CONVEX; INT_LTE_TRANS];
      ASM_MESON_TAC[FACE_OF_INTER; FACE_OF_SUBSET;
                    INTER_SUBSET; FACE_OF_INTER; FACE_OF_IMP_SUBSET];
      ASM SET_TAC[];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
      ASM_REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        BOUNDED_SUBSET)) THEN
      ASM_SIMP_TAC[BOUNDED_RELATIVE_FRONTIER];
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      ASM SET_TAC[];
      REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(g:real^M->real^N) o (h:real^M->real^M)` THEN
    REWRITE_TAC[IMAGE_o; o_THM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[]]);;

let EXTEND_MAP_SPHERE_TO_SPHERE = prove
 (`!f:real^M->real^N c a r b s.
        dimindex(:M) <= dimindex(:N) /\ closed c /\ c SUBSET sphere(a,r) /\
        f continuous_on c /\ IMAGE f c SUBSET sphere(b,s) /\
        (&0 <= r /\ c = {} ==> &0 <= s)
        ==> ?g. g continuous_on sphere(a,r) /\
                IMAGE g (sphere(a,r)) SUBSET sphere(b,s) /\
                !x. x IN c ==> g x = f x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[SPHERE_EMPTY; NOT_IN_EMPTY; CONTINUOUS_ON_EMPTY;
               IMAGE_CLAUSES; EMPTY_SUBSET]
  THENL [MESON_TAC[]; ASM_REWRITE_TAC[GSYM REAL_NOT_LT]] THEN
  ASM_CASES_TAC `sphere(b:real^N,s) = {}` THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SPHERE_EQ_EMPTY]) THEN
    ASM SET_TAC[];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [SPHERE_EQ_EMPTY])] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
  ASM_CASES_TAC `r = &0` THEN
  ASM_SIMP_TAC[SPHERE_SING; CONTINUOUS_ON_SING; REAL_LE_REFL] THENL
   [ASM_CASES_TAC `c:real^M->bool = {}` THENL
     [DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC(MESON[]
       `(?c. P(\x. c)) ==> ?f. P f`) THEN ASM SET_TAC[];
      DISCH_TAC THEN EXISTS_TAC `f:real^M->real^N` THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `s = &0` THENL
   [ASM_SIMP_TAC[SPHERE_SING] THEN STRIP_TAC THEN
    EXISTS_TAC `(\x. b):real^M->real^N` THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `c:real^M->bool`;
                 `cball(a:real^M,r)`; `cball(b:real^N,s)`]
        EXTEND_MAP_SPHERE_TO_SPHERE_GEN) THEN
  ASM_REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; AFF_DIM_CBALL;
                  RELATIVE_FRONTIER_CBALL] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_OF_NUM_LE]) THEN
  ASM_REAL_ARITH_TAC);;

let EXTEND_MAP_SPHERE_TO_SPHERE_COFINITE_GEN = prove
 (`!f:real^M->real^N s t u p.
        convex t /\ bounded t /\ convex u /\ bounded u /\
        aff_dim t <= aff_dim u + &1 /\
        closed s /\ s SUBSET relative_frontier t /\
        f continuous_on s /\ IMAGE f s SUBSET relative_frontier u /\
        (!c. c IN components(relative_frontier t DIFF s) ==> ~(c INTER p = {}))
        ==> ?k g. FINITE k /\ k SUBSET p /\
                  k SUBSET relative_frontier t /\ DISJOINT k s /\
                  g continuous_on (relative_frontier t DIFF k) /\
                  IMAGE g (relative_frontier t DIFF k) SUBSET
                  relative_frontier u /\
                  !x. x IN s ==> g x = f x`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s = (relative_frontier t:real^M->bool)` THENL
   [ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`{}:real^M->bool`; `f:real^M->real^N`] THEN
    ASM_REWRITE_TAC[FINITE_EMPTY; DIFF_EMPTY] THEN SET_TAC[];
    POP_ASSUM MP_TAC] THEN
  ASM_CASES_TAC `relative_frontier t:real^M->bool = {}` THENL
   [ASM SET_TAC[]; REPEAT STRIP_TAC] THEN
  SUBGOAL_THEN
   `?c q:real^M. c IN components (relative_frontier t DIFF s) /\
                 q IN c /\ q IN relative_frontier t /\ ~(q IN s) /\ q IN p`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `(relative_frontier t:real^M->bool) DIFF s`
      UNIONS_COMPONENTS) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `s = u ==> ~(s = {}) ==> ~(u = {})`)) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[EMPTY_UNIONS]] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^M->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^M->bool`) THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM IN_DIFF] THEN
    ASM_MESON_TAC[SUBSET; IN_COMPONENTS_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?af. affine af /\ aff_dim(t:real^M->bool) = aff_dim(af:real^M->bool) + &1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^M)`; `aff_dim(t:real^M->bool) - &1`]
        CHOOSE_AFFINE_SUBSET) THEN
    REWRITE_TAC[SUBSET_UNIV; AFFINE_UNIV] THEN ANTS_TAC THENL
     [MATCH_MP_TAC(INT_ARITH
       `&0:int <= t /\ t <= n ==> --a <= t - a /\ t - &1 <= n`) THEN
      REWRITE_TAC[AFF_DIM_LE_UNIV; AFF_DIM_UNIV; AFF_DIM_POS_LE] THEN
      ASM_MESON_TAC[RELATIVE_FRONTIER_EMPTY; NOT_IN_EMPTY];
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^M->bool`; `af:real^M->bool`; `q:real^M`]
        HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN) THEN
  ASM_REWRITE_TAC[homeomorphic; homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:real^M->real^M`; `k:real^M->real^M`] THEN
  STRIP_TAC THEN MP_TAC(ISPECL
   [`(f:real^M->real^N) o (k:real^M->real^M)`;
    `IMAGE (h:real^M->real^M) s`;
    `(af:real^M->bool)`;
    `u:real^N->bool`;
    `IMAGE (h:real^M->real^M) (p INTER relative_frontier t DELETE q)`]
   EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_GEN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        ASM SET_TAC[];
        ASM_MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_SUBSET;
                      COMPACT_RELATIVE_FRONTIER_BOUNDED]];
      ASM_INT_ARITH_TAC;
      ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      ASM SET_TAC[];
      REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
      X_GEN_TAC `l:real^M->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(l:real^M->bool = {})` ASSUME_TAC THENL
       [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]; ALL_TAC] THEN
      SUBGOAL_THEN `?x:real^M. x IN l` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `l SUBSET af DIFF IMAGE (h:real^M->real^M) s`
      ASSUME_TAC THENL
       [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `connected(l:real^M->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
      SUBGOAL_THEN
       `?r. r IN components (relative_frontier t DIFF s) /\
            IMAGE (k:real^M->real^M) l SUBSET r`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[IN_COMPONENTS; LEFT_AND_EXISTS_THM] THEN
        EXISTS_TAC `connected_component (relative_frontier t DIFF s)
                                        ((k:real^M->real^M) x)` THEN
        EXISTS_TAC `(k:real^M->real^M) x` THEN REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
        ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
        CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real^M->bool`) THEN
      ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM MEMBER_NOT_EMPTY] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_INTER] THEN
      X_GEN_TAC `z:real^M` THEN STRIP_TAC THEN
      SUBGOAL_THEN `r SUBSET ((relative_frontier t:real^M->bool) DIFF s)`
      ASSUME_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `connected(r:real^M->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
      ASM_CASES_TAC `(q:real^M) IN r` THENL
       [ALL_TAC;
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
        EXISTS_TAC `(h:real^M->real^M) z` THEN REWRITE_TAC[IN_INTER] THEN
        CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        MATCH_MP_TAC(SET_RULE `!s. x IN s /\ s SUBSET t ==> x IN t`) THEN
        EXISTS_TAC `IMAGE (h:real^M->real^M) r` THEN
        ASM_SIMP_TAC[FUN_IN_IMAGE] THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
        EXISTS_TAC `af DIFF IMAGE (h:real^M->real^M) s` THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          ASM SET_TAC[];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_ELIM_THM] THEN
          X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
          CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[SET_RULE
           `~(h y IN IMAGE h s) <=> !y'. y' IN s ==> ~(h y = h y')`] THEN
          X_GEN_TAC `y':real^M` THEN DISCH_TAC THEN
          DISCH_THEN(MP_TAC o AP_TERM `k:real^M->real^M`) THEN
          MATCH_MP_TAC(MESON[]
           `k(h y) = y /\ k(h y') = y' /\ ~(y = y')
            ==> k(h y) = k(h y') ==> F`) THEN
          ASM SET_TAC[];
          ASM SET_TAC[]]] THEN
      SUBGOAL_THEN
       `?n. open_in (subtopology euclidean (relative_frontier t)) n /\
            (q:real^M) IN n /\ n INTER IMAGE (k:real^M->real^M) l = {}`
      STRIP_ASSUME_TAC THENL
       [EXISTS_TAC `relative_frontier t DIFF
                    IMAGE (k:real^M->real^M) (closure l)` THEN
        SUBGOAL_THEN `closure l SUBSET (af:real^M->bool)` ASSUME_TAC THENL
         [MATCH_MP_TAC CLOSURE_MINIMAL THEN
          ASM_SIMP_TAC[CLOSED_AFFINE] THEN ASM SET_TAC[];
          ALL_TAC] THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
          MATCH_MP_TAC CLOSED_SUBSET THEN
          CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
          MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
          ASM_REWRITE_TAC[COMPACT_CLOSURE] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          ASM SET_TAC[];
          ASM SET_TAC[];
          MP_TAC(ISPEC `l:real^M->bool` CLOSURE_SUBSET) THEN SET_TAC[]];
        ALL_TAC] THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
      SUBGOAL_THEN
       `?w. connected w /\ w SUBSET r DELETE q /\
            (k:real^M->real^M) x IN w /\ ~((n DELETE q) INTER w = {})`
      STRIP_ASSUME_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC(TAUT `F ==> p`) THEN
        SUBGOAL_THEN `IMAGE (h:real^M->real^M) w SUBSET l` MP_TAC THENL
         [ALL_TAC; ASM SET_TAC[]] THEN
        MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
        EXISTS_TAC `af DIFF IMAGE (h:real^M->real^M) s` THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          ASM SET_TAC[];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_ELIM_THM] THEN
          X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
          CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[SET_RULE
           `~(h y IN IMAGE h s) <=> !y'. y' IN s ==> ~(h y = h y')`] THEN
          X_GEN_TAC `y':real^M` THEN DISCH_TAC THEN
          DISCH_THEN(MP_TAC o AP_TERM `k:real^M->real^M`) THEN
          MATCH_MP_TAC(MESON[]
           `k(h y) = y /\ k(h y') = y' /\ ~(y = y')
            ==> k(h y) = k(h y') ==> F`) THEN
          ASM SET_TAC[];
          ASM SET_TAC[]]] THEN
      SUBGOAL_THEN `path_connected(r:real^M->bool)` MP_TAC THENL
       [W(MP_TAC o PART_MATCH (lhand o rand) PATH_CONNECTED_EQ_CONNECTED_LPC o
          snd) THEN
        ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
        MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
        EXISTS_TAC `(relative_frontier t:real^M->bool)` THEN
        ASM_SIMP_TAC[LOCALLY_PATH_CONNECTED_SPHERE_GEN] THEN
        MATCH_MP_TAC OPEN_IN_TRANS THEN
        EXISTS_TAC `(relative_frontier t:real^M->bool) DIFF s` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC OPEN_IN_COMPONENTS_LOCALLY_CONNECTED THEN
          ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
          EXISTS_TAC `(relative_frontier t:real^M->bool)` THEN
          ASM_SIMP_TAC[LOCALLY_CONNECTED_SPHERE_GEN];
          ALL_TAC] THEN
        MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
        MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[PATH_CONNECTED_ARCWISE] THEN
      DISCH_THEN(MP_TAC o SPECL [`(k:real^M->real^M) x`; `q:real^M`]) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^M` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC o
        GEN_REWRITE_RULE I [arc]) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN
       `open_in (subtopology euclidean (interval[vec 0,vec 1]))
                {x | x IN interval[vec 0,vec 1] /\
                     (g:real^1->real^M) x IN n}`
      MP_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
        EXISTS_TAC `(relative_frontier t:real^M->bool)` THEN
        ASM_REWRITE_TAC[GSYM path; GSYM path_image] THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[OPEN_IN_CONTAINS_CBALL] THEN
      REWRITE_TAC[IN_ELIM_THM; SUBSET_RESTRICT] THEN
      DISCH_THEN(MP_TAC o SPEC `vec 1:real^1`) THEN
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[pathfinish]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real`
        (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ABBREV_TAC `t' = lift(&1 - min (&1 / &2) r)` THEN
      SUBGOAL_THEN `t' IN interval[vec 0:real^1,vec 1]` ASSUME_TAC THENL
       [EXPAND_TAC "t'" THEN SIMP_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `t':real^1`) THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_CBALL; DIST_REAL;
                      DROP_VEC; GSYM drop] THEN
      ANTS_TAC THENL
       [EXPAND_TAC "t'" THEN REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
        DISCH_TAC] THEN
      EXISTS_TAC `IMAGE (g:real^1->real^M) (interval[vec 0,t'])` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[CONNECTED_INTERVAL] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        ASM_REWRITE_TAC[GSYM path; SUBSET_INTERVAL_1] THEN
        ASM_REWRITE_TAC[REAL_LE_REFL; GSYM IN_INTERVAL_1];
        REWRITE_TAC[SET_RULE
         `s SUBSET t DELETE q <=> s SUBSET t /\ !x. x IN s ==> ~(x = q)`] THEN
        CONJ_TAC THENL
         [TRANS_TAC SUBSET_TRANS
            `IMAGE (g:real^1->real^M) (interval[vec 0,vec 1])` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC IMAGE_SUBSET THEN
            ASM_REWRITE_TAC[REAL_LE_REFL; GSYM IN_INTERVAL_1;
                            SUBSET_INTERVAL_1];
            ASM_REWRITE_TAC[GSYM path_image]];
          REWRITE_TAC[FORALL_IN_IMAGE] THEN
          X_GEN_TAC `t'':real^1` THEN DISCH_TAC THEN
          FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
           [SYM th]) THEN
          REWRITE_TAC[pathfinish] THEN DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPECL [`t'':real^1`; `vec 1:real^1`]) THEN
          ASM_REWRITE_TAC[GSYM DROP_EQ] THEN
          UNDISCH_TAC `t'' IN interval[vec 0:real^1,t']` THEN
          EXPAND_TAC "t'" THEN
          REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
          ASM_REAL_ARITH_TAC];
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^1` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[pathstart]; ALL_TAC] THEN
        EXPAND_TAC "t'" THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
        ONCE_REWRITE_TAC[INTER_COMM] THEN
        REWRITE_TAC[EXISTS_IN_IMAGE; IN_INTER] THEN
        EXISTS_TAC `t':real^1` THEN CONJ_TAC THENL
         [EXPAND_TAC "t'" THEN
          REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
          ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[IN_DELETE] THEN
          FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
           [SYM th]) THEN
          REWRITE_TAC[pathfinish] THEN DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPECL [`t':real^1`; `vec 1:real^1`]) THEN
          ASM_REWRITE_TAC[GSYM DROP_EQ] THEN
          EXPAND_TAC "t'" THEN
          REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
          ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[DOT_BASIS; LE_REFL; DIMINDEX_GE_1; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`tk:real^M->bool`; `g:real^M->real^N`] THEN
  REWRITE_TAC[o_THM] THEN
  STRIP_TAC THEN EXISTS_TAC `q INSERT IMAGE (k:real^M->real^M) tk` THEN
  EXISTS_TAC `(g:real^M->real^N) o (h:real^M->real^M)` THEN
  ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; o_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `a IN t /\ s SUBSET t DELETE a ==> a INSERT s SUBSET t`) THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC SUBSET_TRANS
      `p INTER (relative_frontier t:real^M->bool) DELETE q` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (SET_RULE `t SUBSET IMAGE h s ==> IMAGE k (IMAGE h s) SUBSET s
            ==> IMAGE k t SUBSET s`)) THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> f x = x) ==> IMAGE f s SUBSET s`) THEN
    REWRITE_TAC[o_THM] THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let EXTEND_MAP_SPHERE_TO_SPHERE_COFINITE = prove
 (`!f:real^M->real^N s a d b e p.
        dimindex(:M) <= dimindex(:N) + 1 /\
        (&0 < d /\ s = {} ==> &0 <= e) /\
        closed s /\ s SUBSET sphere(a,d) /\
        f continuous_on s /\ IMAGE f s SUBSET sphere(b,e) /\
        (!c. c IN components(sphere(a,d) DIFF s) ==> ~(c INTER p = {}))
        ==> ?k g. FINITE k /\ k SUBSET p /\
                  k SUBSET sphere(a,d) /\ DISJOINT k s /\
                  g continuous_on (sphere(a,d) DIFF k) /\
                  IMAGE g (sphere(a,d) DIFF k) SUBSET sphere(b,e) /\
                  !x. x IN s ==> g x = f x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s = sphere(a:real^M,d)` THENL
   [ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`{}:real^M->bool`; `f:real^M->real^N`] THEN
    ASM_REWRITE_TAC[FINITE_EMPTY; DIFF_EMPTY] THEN SET_TAC[];
    POP_ASSUM MP_TAC] THEN
  ASM_CASES_TAC `d < &0` THENL
   [ASM_SIMP_TAC[SPHERE_EMPTY] THEN SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `d = &0` THENL
   [ASM_SIMP_TAC[SPHERE_SING] THEN
    ASM_CASES_TAC `s:real^M->bool = {}` THENL
     [ASM_REWRITE_TAC[]; ASM SET_TAC[]] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `{a:real^M}` THEN
    REWRITE_TAC[FINITE_SING; CONTINUOUS_ON_EMPTY; DIFF_EQ_EMPTY] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{a:real^M}`) THEN
    REWRITE_TAC[DIFF_EMPTY; IN_COMPONENTS_SELF; CONNECTED_SING] THEN
    REWRITE_TAC[IMAGE_CLAUSES] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `e = &0` THENL
   [ASM_SIMP_TAC[SPHERE_SING] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `{}:real^M->bool` THEN
    EXISTS_TAC `(\x. b):real^M->real^N` THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; FINITE_EMPTY] THEN ASM SET_TAC[];
    REPEAT STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= e` ASSUME_TAC THENL
   [ASM_CASES_TAC `s:real^M->bool = {}` THEN ASM_SIMP_TAC[] THEN
    MP_TAC(SYM(ISPECL [`b:real^N`; `e:real`] SPHERE_EQ_EMPTY)) THEN
    SIMP_TAC[GSYM REAL_NOT_LT] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`f:real^M->real^N`; `s:real^M->bool`; `cball(a:real^M,d)`;
    `cball(b:real^N,e)`; `p:real^M->bool`]
   EXTEND_MAP_SPHERE_TO_SPHERE_COFINITE_GEN) THEN
  ASM_REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL] THEN
  REWRITE_TAC[AFF_DIM_CBALL] THEN
  MP_TAC(ISPECL [`a:real^M`; `d:real`] RELATIVE_FRONTIER_CBALL) THEN
  MP_TAC(ISPECL [`b:real^N`; `e:real`] RELATIVE_FRONTIER_CBALL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_LE]);;

(* ------------------------------------------------------------------------- *)
(* Borsuk-style characterization of separation.                              *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_BORSUK_MAP = prove
 (`!s a:real^N.
        ~(a IN s) ==> (\x. inv(norm (x - a)) % (x - a)) continuous_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN SIMP_TAC[o_DEF] THEN CONJ_TAC THENL
    [MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV); ALL_TAC] THEN
  SIMP_TAC[CONTINUOUS_ON_LIFT_NORM_COMPOSE; CONTINUOUS_ON_SUB;
           CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
  REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]);;

let BORSUK_MAP_INTO_SPHERE = prove
 (`!s a:real^N.
        IMAGE (\x. inv(norm (x - a)) % (x - a)) s SUBSET sphere(vec 0,&1) <=>
        ~(a IN s)`,
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  REWRITE_TAC[REAL_FIELD `inv x * x = &1 <=> ~(x = &0)`] THEN
  REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN MESON_TAC[]);;

let BORSUK_MAPS_HOMOTOPIC_IN_PATH_COMPONENT = prove
 (`!s a b. path_component ((:real^N) DIFF s) a b
           ==> homotopic_with (\x. T)
                   (subtopology euclidean s,
                    subtopology euclidean (sphere(vec 0,&1)))
                   (\x. inv(norm(x - a)) % (x - a))
                   (\x. inv(norm(x - b)) % (x - b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_component; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[path; path_image; pathstart; pathfinish; SUBSET;
              FORALL_IN_IMAGE; IN_UNIV; IN_DIFF] THEN
  X_GEN_TAC `g:real^1->real^N` THEN STRIP_TAC THEN
  SIMP_TAC[HOMOTOPIC_WITH_EUCLIDEAN_ALT] THEN
  EXISTS_TAC `\z. inv(norm(sndcart z - g(fstcart z))) %
                  (sndcart z - (g:real^1->real^N)(fstcart z))` THEN
  ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_SPHERE_0;
               SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
      ASM_SIMP_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
                   NORM_EQ_0; VECTOR_SUB_EQ] THEN CONJ_TAC
      THENL [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
    REWRITE_TAC[IMAGE_FSTCART_PCROSS] THEN ASM_MESON_TAC[CONTINUOUS_ON_EMPTY];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN
    ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]]);;

let NON_EXTENSIBLE_BORSUK_MAP = prove
 (`!s c a:real^N.
        compact s /\ c IN components((:real^N) DIFF s) /\ bounded c /\ a IN c
        ==> ~(?g. g continuous_on (s UNION c) /\
                  IMAGE g (s UNION c) SUBSET sphere (vec 0,&1) /\
                  (!x. x IN s ==> g x = inv(norm(x - a)) % (x - a)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c = connected_component ((:real^N) DIFF s) a` SUBST_ALL_TAC
  THENL [ASM_MESON_TAC[IN_COMPONENTS; CONNECTED_COMPONENT_EQ]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`s UNION connected_component ((:real^N) DIFF s) a`; `a:real^N`]
      BOUNDED_SUBSET_BALL) THEN
  ASM_SIMP_TAC[BOUNDED_UNION; COMPACT_IMP_BOUNDED] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:real^N` o MATCH_MP NO_RETRACTION_CBALL) THEN
  REWRITE_TAC[retract_of; retraction] THEN
  EXISTS_TAC `\x. if x IN connected_component ((:real^N) DIFF s) a
                  then a + r % g(x)
                  else a + r % inv(norm(x - a)) % (x - a)` THEN
  REWRITE_TAC[SPHERE_SUBSET_CBALL] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `cball(a:real^N,r) =
                  (s UNION connected_component ((:real^N) DIFF s) a) UNION
                  (cball(a,r) DIFF connected_component ((:real^N) DIFF s) a)`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`a:real^N`; `r:real`] BALL_SUBSET_CBALL) THEN ASM
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNION_COMPLEMENT_COMPONENT THEN
      ASM_SIMP_TAC[IN_COMPONENTS; COMPACT_IMP_CLOSED; IN_UNIV; IN_DIFF] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC CLOSED_DIFF THEN
      ASM_SIMP_TAC[CLOSED_CBALL; OPEN_CONNECTED_COMPONENT; GSYM closed;
                   COMPACT_IMP_CLOSED];
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN SIMP_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_SIMP_TAC[CONTINUOUS_ON_CONST];
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN SIMP_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_BORSUK_MAP THEN
      ASM_SIMP_TAC[CENTRE_IN_CBALL; IN_DIFF; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV];
      REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];

      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[IN_SPHERE; NORM_ARITH `dist(a:real^N,a + x) = norm x`;
                      NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ABS_INV; REAL_ABS_NORM; VECTOR_SUB_EQ;
        REAL_FIELD `&0 < r ==> abs r = r /\ (r * x = r <=> x = &1)`;
        REAL_FIELD `inv x * x = &1 <=> ~(x = &0)`; NORM_EQ_0]
      THENL
       [ONCE_REWRITE_TAC[GSYM IN_SPHERE_0] THEN ASM SET_TAC[];
        UNDISCH_TAC `~(x IN connected_component ((:real^N) DIFF s) a)` THEN
        SIMP_TAC[CONTRAPOS_THM; IN] THEN
        ASM_REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ; IN_DIFF; IN_UNIV]];
      SIMP_TAC[IN_SPHERE; ONCE_REWRITE_RULE[NORM_SUB] dist] THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[VECTOR_ARITH `a + &1 % (x - a):real^N = x`] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `s UNION t SUBSET u ==> !x. x IN t /\ ~(x IN u) ==> wev`)) THEN
      EXISTS_TAC `x:real^N` THEN
      ASM_REWRITE_TAC[ONCE_REWRITE_RULE[NORM_SUB] dist; IN_BALL;
                      REAL_LT_REFL]]);;

let BORSUK_MAP_ESSENTIAL_BOUNDED_COMPONENT = prove
 (`!s a. compact s /\ ~(a IN s)
         ==> (bounded(connected_component ((:real^N) DIFF s) a) <=>
              ~(?c. homotopic_with (\x. T)
                      (subtopology euclidean s,
                       subtopology euclidean (sphere(vec 0:real^N,&1)))
                      (\x. inv(norm(x - a)) % (x - a)) (\x. c)))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_SIMP_TAC[DIFF_EMPTY; CONNECTED_COMPONENT_UNIV; NOT_BOUNDED_UNIV] THEN
    SIMP_TAC[HOMOTOPIC_WITH_EUCLIDEAN_ALT; NOT_IN_EMPTY; PCROSS_EMPTY;
             IMAGE_CLAUSES; CONTINUOUS_ON_EMPTY; EMPTY_SUBSET];
    ALL_TAC] THEN
  EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
    REPEAT DISCH_TAC THEN
    MP_TAC(ISPECL
     [`\x:real^N. inv(norm(x - a)) % (x - a)`; `s:real^N->bool`;
      `vec 0:real^N`; `&1`]
     NULLHOMOTOPIC_INTO_SPHERE_EXTENSION) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; NOT_IMP; CONTINUOUS_ON_BORSUK_MAP;
                 BORSUK_MAP_INTO_SPHERE] THEN
    MP_TAC(ISPECL [`s:real^N->bool`;
        `connected_component ((:real^N) DIFF s) a`;
        `a:real^N`] NON_EXTENSIBLE_BORSUK_MAP) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [IN] THEN
      REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN
      ASM_REWRITE_TAC[IN_COMPONENTS; IN_DIFF; IN_UNIV] THEN ASM_MESON_TAC[];
      REWRITE_TAC[CONTRAPOS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
       [MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; SET_TAC[]]];
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^N` o MATCH_MP BOUNDED_SUBSET_BALL o
      MATCH_MP COMPACT_IMP_BOUNDED) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?b. b IN connected_component ((:real^N) DIFF s) a /\
          ~(b IN ball(vec 0,r))`
    MP_TAC THENL
     [REWRITE_TAC[SET_RULE `(?b. b IN s /\ ~(b IN t)) <=> ~(s SUBSET t)`] THEN
      ASM_MESON_TAC[BOUNDED_SUBSET; BOUNDED_BALL];
      DISCH_THEN(X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN
     `?c. homotopic_with (\x. T)
           (subtopology euclidean (ball(vec 0:real^N,r)),
            subtopology euclidean (sphere(vec 0,&1)))
                         (\x. inv (norm (x - b)) % (x - b)) (\x. c)`
    MP_TAC THENL
     [MATCH_MP_TAC NULLHOMOTOPIC_FROM_CONTRACTIBLE THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_BORSUK_MAP; BORSUK_MAP_INTO_SPHERE;
                   CONVEX_IMP_CONTRACTIBLE; CONVEX_BALL];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N` THEN STRIP_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
    EXISTS_TAC `\x:real^N. inv(norm (x - b)) % (x - b)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC BORSUK_MAPS_HOMOTOPIC_IN_PATH_COMPONENT THEN
      ASM_SIMP_TAC[OPEN_PATH_CONNECTED_COMPONENT; GSYM closed;
                   COMPACT_IMP_CLOSED] THEN  ASM_MESON_TAC[IN];
      ASM_MESON_TAC[HOMOTOPIC_WITH_SUBSET_LEFT]]]);;

let HOMOTOPIC_BORSUK_MAPS_IN_BOUNDED_COMPONENT = prove
 (`!s a b.
        compact s /\ ~(a IN s) /\ ~(b IN s) /\
        bounded (connected_component ((:real^N) DIFF s) a) /\
        homotopic_with (\x. T)
          (subtopology euclidean s,
           subtopology euclidean (sphere(vec 0,&1)))
          (\x. inv(norm(x - a)) % (x - a))
          (\x. inv(norm(x - b)) % (x - b))
        ==> connected_component ((:real^N) DIFF s) a b`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [GSYM IN] THEN
  MP_TAC(ISPECL
   [`s:real^N->bool`; `connected_component ((:real^N) DIFF s) a`;
    `a:real^N`] NON_EXTENSIBLE_BORSUK_MAP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [IN] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN
    ASM_REWRITE_TAC[IN_COMPONENTS; IN_DIFF; IN_UNIV] THEN ASM_MESON_TAC[];
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM]] THEN
  DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC BORSUK_HOMOTOPY_EXTENSION THEN
  EXISTS_TAC `\x:real^N. inv(norm(x - b)) % (x - b)` THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED; ANR_SPHERE;
               CLOSED_SUBSET; SUBSET_UNION] THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_BORSUK_MAP; IN_UNION; BORSUK_MAP_INTO_SPHERE] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC CLOSED_UNION_COMPLEMENT_COMPONENT THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED; IN_COMPONENTS; IN_DIFF; IN_UNIV] THEN
  ASM_MESON_TAC[]);;

let BORSUK_MAPS_HOMOTOPIC_IN_CONNECTED_COMPONENT_EQ = prove
 (`!s a b. 2 <= dimindex(:N) /\ compact s /\ ~(a IN s) /\ ~(b IN s)
           ==> (homotopic_with (\x. T)
                   (subtopology euclidean s,
                    subtopology euclidean (sphere(vec 0,&1)))
                   (\x. inv(norm(x - a)) % (x - a))
                   (\x. inv(norm(x - b)) % (x - b)) <=>
                connected_component ((:real^N) DIFF s) a b)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC;
    ASM_SIMP_TAC[GSYM OPEN_PATH_CONNECTED_COMPONENT; GSYM closed;
                 COMPACT_IMP_CLOSED] THEN
    REWRITE_TAC[BORSUK_MAPS_HOMOTOPIC_IN_PATH_COMPONENT]] THEN
  ASM_CASES_TAC `bounded(connected_component ((:real^N) DIFF s) a)` THENL
   [MATCH_MP_TAC HOMOTOPIC_BORSUK_MAPS_IN_BOUNDED_COMPONENT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `bounded(connected_component ((:real^N) DIFF s) b)` THENL
   [ONCE_REWRITE_TAC[CONNECTED_COMPONENT_SYM_EQ] THEN
    MATCH_MP_TAC HOMOTOPIC_BORSUK_MAPS_IN_BOUNDED_COMPONENT THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^N) DIFF s`; `a:real^N`; `b:real^N`]
        COBOUNDED_UNIQUE_UNBOUNDED_COMPONENT) THEN
  ASM_REWRITE_TAC[CONNECTED_COMPONENT_EQ_EQ; IN_DIFF; IN_UNIV;
                  COMPL_COMPL] THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]);;

let BORSUK_SEPARATION_THEOREM_GEN = prove
 (`!s:real^N->bool.
    compact s
    ==> ((!c. c IN components((:real^N) DIFF s) ==> ~bounded c) <=>
         (!f. f continuous_on s /\ IMAGE f s SUBSET sphere(vec 0:real^N,&1)
              ==> ?c. homotopic_with (\x. T)
                       (subtopology euclidean s,
                        subtopology euclidean (sphere(vec 0,&1))) f (\x. c)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_FORALL_THM; components; EXISTS_IN_GSPEC; NOT_IMP;
                IN_UNIV; IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\x:real^N. inv(norm(x - a)) % (x - a)` THEN
    ASM_SIMP_TAC[GSYM BORSUK_MAP_ESSENTIAL_BOUNDED_COMPONENT;
                 CONTINUOUS_ON_BORSUK_MAP; BORSUK_MAP_INTO_SPHERE]] THEN
  DISCH_TAC THEN X_GEN_TAC `f:real^N->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`f:real^N->real^N`; `s:real^N->bool`; `vec 0:real^N`; `&1:real`]
        EXTEND_MAP_UNIV_TO_SPHERE_NO_BOUNDED_COMPONENT) THEN
  ASM_REWRITE_TAC[LE_REFL; REAL_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`g:real^N->real^N`; `(:real^N)`; `sphere(vec 0:real^N,&1)`]
        NULLHOMOTOPIC_FROM_CONTRACTIBLE) THEN
  ASM_REWRITE_TAC[CONTRACTIBLE_UNIV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] HOMOTOPIC_WITH_SUBSET_LEFT)) THEN
  REWRITE_TAC[SUBSET_UNIV] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        HOMOTOPIC_WITH_EQ) THEN
  ASM_SIMP_TAC[]);;

let BORSUK_SEPARATION_THEOREM = prove
 (`!s:real^N->bool.
      2 <= dimindex(:N) /\ compact s
      ==> (connected((:real^N) DIFF s) <=>
           !f. f continuous_on s /\ IMAGE f s SUBSET sphere(vec 0:real^N,&1)
               ==> ?c. homotopic_with (\x. T)
                        (subtopology euclidean s,
                         subtopology euclidean (sphere(vec 0,&1))) f (\x. c))`,
  SIMP_TAC[GSYM BORSUK_SEPARATION_THEOREM_GEN] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPEC `(:real^N) DIFF s` COMPONENTS_EQ_SING) THEN
    MP_TAC(ISPEC `(:real^N) DIFF s` COBOUNDED_IMP_UNBOUNDED) THEN
    ASM_CASES_TAC `(:real^N) DIFF s = {}` THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; COMPL_COMPL;
                 BOUNDED_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY];

    REWRITE_TAC[components; FORALL_IN_GSPEC; IN_DIFF; IN_UNIV] THEN
    DISCH_TAC THEN REWRITE_TAC[CONNECTED_EQ_CONNECTED_COMPONENT_EQ] THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COBOUNDED_UNIQUE_UNBOUNDED_COMPONENT THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED;
                 COMPL_COMPL]]);;

let HOMOTOPY_EQUIVALENT_SEPARATION = prove
 (`!s t. compact s /\ compact t /\ s homotopy_equivalent t
         ==> (connected((:real^N) DIFF s) <=> connected((:real^N) DIFF t))`,
  let special = prove
   (`!s:real^1->bool.
          bounded s /\ connected((:real^1) DIFF s) ==> s = {}`,
    REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_OPEN_INTERVAL) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; EXTENSION; NOT_IN_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IS_INTERVAL_1]) THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^1`; `b:real^1`]) THEN
    REWRITE_TAC[IN_UNIV; IN_DIFF; SUBSET; IN_INTERVAL_1] THEN
    MESON_TAC[REAL_LT_REFL; REAL_LT_IMP_LE]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= dimindex(:N)` MP_TAC THENL
   [REWRITE_TAC[DIMINDEX_GE_1];
    REWRITE_TAC[ARITH_RULE `1 <= n <=> n = 1 \/ 2 <= n`] THEN
    REWRITE_TAC[GSYM DIMINDEX_1]] THEN
  STRIP_TAC THENL
   [ASSUME_TAC(GEOM_EQUAL_DIMENSION_RULE(ASSUME `dimindex(:N) = dimindex(:1)`)
       special) THEN
    EQ_TAC THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`);
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool`)] THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN DISCH_TAC THEN
    UNDISCH_TAC `(s:real^N->bool) homotopy_equivalent (t:real^N->bool)` THEN
    ASM_REWRITE_TAC[HOMOTOPY_EQUIVALENT_EMPTY] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[CONNECTED_UNIV; DIFF_EMPTY];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BORSUK_SEPARATION_THEOREM] THEN
    MATCH_MP_TAC HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY_NULL THEN
    ASM_REWRITE_TAC[]]);;

let JORDAN_BROUWER_SEPARATION = prove
 (`!s a:real^N r.
        &0 < r /\ s homeomorphic sphere(a,r) ==> ~connected((:real^N) DIFF s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `sphere(a:real^N,r)`]
        HOMOTOPY_EQUIVALENT_SEPARATION) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_SPHERE;
                  HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT];
    DISCH_THEN SUBST1_TAC] THEN
  DISCH_TAC THEN MP_TAC(ISPECL
   [`(:real^N) DIFF sphere(a,r)`;
    `ball(a:real^N,r)`] CONNECTED_INTER_FRONTIER) THEN
  ASM_SIMP_TAC[FRONTIER_BALL; NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM CBALL_DIFF_BALL] THEN MATCH_MP_TAC(SET_RULE
     `~(b = {})
      ==> ~((UNIV DIFF (c DIFF b)) INTER b = {})`) THEN
    ASM_SIMP_TAC[BALL_EQ_EMPTY; REAL_NOT_LE];
    MATCH_MP_TAC(SET_RULE
     `~(s UNION t = UNIV) ==> ~(UNIV DIFF t DIFF s = {})`) THEN
    REWRITE_TAC[BALL_UNION_SPHERE] THEN
    MESON_TAC[BOUNDED_CBALL; NOT_BOUNDED_UNIV];
    SET_TAC[]]);;

let JORDAN_BROUWER_FRONTIER = prove
 (`!s t a:real^N r.
     2 <= dimindex(:N) /\
     s homeomorphic sphere(a,r) /\ t IN components((:real^N) DIFF s)
     ==> frontier t = s`,
  let lemma = prove
   (`!s a r. 2 <= dimindex(:N) /\ &0 < r /\ s PSUBSET sphere(a,r)
             ==> connected((:real^N) DIFF s)`,
    REWRITE_TAC[PSUBSET_ALT; SUBSET; IN_SPHERE; GSYM REAL_LE_ANTISYM] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(:real^N) DIFF s =
      {x:real^N | dist(a,x) <= r /\ ~(x IN s)} UNION
      {x:real^N | r <= dist(a,x) /\ ~(x IN s)}`
    SUBST1_TAC THENL
     [SET_TAC[REAL_LE_TOTAL]; MATCH_MP_TAC CONNECTED_UNION] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
      EXISTS_TAC `ball(a:real^N,r)` THEN
      ASM_SIMP_TAC[CONNECTED_BALL; CLOSURE_BALL; SUBSET; IN_BALL; IN_CBALL;
                   IN_ELIM_THM] THEN
      ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_NOT_LE];
      MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
      EXISTS_TAC `(:real^N) DIFF cball(a,r)` THEN
      REWRITE_TAC[CLOSURE_COMPLEMENT; SUBSET; IN_DIFF; IN_UNIV;
                  IN_BALL; IN_CBALL; IN_ELIM_THM; INTERIOR_CBALL] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_NOT_LE]] THEN
      MATCH_MP_TAC CONNECTED_OPEN_DIFF_CBALL THEN
      ASM_REWRITE_TAC[SUBSET_UNIV; CONNECTED_UNIV; OPEN_UNIV];
      ASM SET_TAC[]]) in
  MAP_EVERY X_GEN_TAC
   [`s:real^N->bool`; `c:real^N->bool`; `a:real^N`; `r:real`] THEN
  ASM_CASES_TAC `r < &0` THENL
   [ASM_SIMP_TAC[SPHERE_EMPTY; HOMEOMORPHIC_EMPTY; IMP_CONJ; DIFF_EMPTY] THEN
    SIMP_TAC[snd(EQ_IMP_RULE(SPEC_ALL COMPONENTS_EQ_SING));
             UNIV_NOT_EMPTY; CONNECTED_UNIV; IN_SING; FRONTIER_UNIV];
    ALL_TAC] THEN
  ASM_CASES_TAC `r = &0` THENL
   [ASM_SIMP_TAC[HOMEOMORPHIC_FINITE_STRONG; SPHERE_SING; FINITE_SING] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_EMPTY; GSYM HAS_SIZE; NOT_IN_EMPTY] THEN
    REWRITE_TAC[HAS_SIZE_CLAUSES; UNWIND_THM2; NOT_IN_EMPTY; IMP_CONJ] THEN
    SIMP_TAC[LEFT_IMP_EXISTS_THM; CONNECTED_PUNCTURED_UNIVERSE; IN_SING;
             snd(EQ_IMP_RULE(SPEC_ALL COMPONENTS_EQ_SING)); FRONTIER_SING;
             SET_RULE `UNIV DIFF s = {} <=> s = UNIV`; FRONTIER_COMPLEMENT;
             MESON[BOUNDED_SING; NOT_BOUNDED_UNIV] `~((:real^N) = {a})`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FRONTIER_MINIMAL_SEPARATING_CLOSED THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_COMPACTNESS) THEN
  SIMP_TAC[COMPACT_SPHERE; COMPACT_IMP_CLOSED] THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[JORDAN_BROUWER_SEPARATION]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[HOMEOMORPHISM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `IMAGE (f:real^N->real^N) t`]
        HOMOTOPY_EQUIVALENT_SEPARATION) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_SUBSET; PSUBSET];
      DISCH_TAC THEN
      SUBGOAL_THEN `t homeomorphic (IMAGE (f:real^N->real^N) t)` MP_TAC THENL
       [REWRITE_TAC[homeomorphic] THEN MAP_EVERY EXISTS_TAC
         [`f:real^N->real^N`; `g:real^N->real^N`] THEN
        ASM_REWRITE_TAC[HOMEOMORPHISM] THEN REPEAT CONJ_TAC THEN
        TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
          (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET))) THEN ASM SET_TAC[];
        ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS;
                      HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT]]];
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC lemma THEN
      MAP_EVERY EXISTS_TAC [`a:real^N`; `r:real`] THEN ASM SET_TAC[]]);;

let JORDAN_BROUWER_NONSEPARATION_STRONG = prove
 (`!s t a:real^N r.
        2 <= dimindex(:N) /\ s homeomorphic sphere(a,r) /\ t PSUBSET s
        ==> path_connected((:real^N) DIFF t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!c. c IN components((:real^N) DIFF s)
        ==> path_connected(c UNION (s DIFF t))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC
     PATH_CONNECTED_INTERMEDIATE_CLOSURE_ANR_COMPLEMENT_COMPONENT THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `c:real^N->bool`] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_COMPACTNESS) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_ANRNESS) THEN
    REWRITE_TAC[COMPACT_SPHERE; ANR_SPHERE] THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[SUBSET_UNION] THEN
    REWRITE_TAC[UNION_SUBSET; CLOSURE_SUBSET; CLOSURE_UNION_FRONTIER] THEN
    MATCH_MP_TAC(SET_RULE `f = s ==> s DIFF t SUBSET k UNION f`) THEN
    MATCH_MP_TAC JORDAN_BROUWER_FRONTIER THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `~(components((:real^N) DIFF s) = {})`
  ASSUME_TAC THENL
   [REWRITE_TAC[COMPONENTS_EQ_EMPTY; SET_RULE
     `UNIV DIFF s = {} <=> s = UNIV`] THEN
    ASM_MESON_TAC[NOT_BOUNDED_UNIV; COMPACT_EQ_BOUNDED_CLOSED;
                  HOMEOMORPHIC_COMPACTNESS; COMPACT_SPHERE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(:real^N) DIFF t =
    UNIONS {c UNION (s DIFF t) | c | c IN components((:real^N) DIFF s)}`
  SUBST1_TAC THENL
   [MP_TAC(ISPEC `(:real^N) DIFF s` UNIONS_COMPONENTS) THEN
    REWRITE_TAC[UNIONS_GSPEC] THEN ASM SET_TAC[];
    MATCH_MP_TAC PATH_CONNECTED_UNIONS THEN
    ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN
    REWRITE_TAC[INTERS_GSPEC] THEN ASM SET_TAC[]]);;

let JORDAN_BROUWER_NONSEPARATION = prove
 (`!s t a:real^N r.
        2 <= dimindex(:N) /\
        s homeomorphic sphere(a,r) /\ t PSUBSET s
        ==> connected((:real^N) DIFF t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP JORDAN_BROUWER_NONSEPARATION_STRONG) THEN
  REWRITE_TAC[PATH_CONNECTED_IMP_CONNECTED]);;

let JORDAN_BROUWER_ACCESSIBILITY = prove
 (`!s c a:real^N r x y.
        2 <= dimindex(:N) /\
        s homeomorphic sphere(a,r) /\
        c IN components((:real^N) DIFF s) /\ x IN c /\ y IN s
        ==> ?g. arc g /\  pathstart g = x /\ pathfinish g = y /\
                IMAGE g (interval[vec 0,vec 1] DELETE (vec 1)) SUBSET c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC ACCESSIBLE_FRONTIER_ANR_COMPLEMENT_COMPONENT THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_COMPACTNESS) THEN
    REWRITE_TAC[COMPACT_SPHERE];
    FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_ANRNESS) THEN
    REWRITE_TAC[ANR_SPHERE];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `x IN s ==> t = s ==> x IN t`)) THEN
    MATCH_MP_TAC JORDAN_BROUWER_FRONTIER THEN ASM_MESON_TAC[]]);;

let HOMOTOPY_EQUIVALENT_SEPARATION_SPHERE = prove
 (`!s t:real^N->bool a r.
      s SUBSET sphere(a,r) /\ t SUBSET sphere(a,r) /\
      compact s /\ compact t /\ s homotopy_equivalent t
      ==> (connected (sphere(a,r) DIFF s) <=> connected(sphere(a,r) DIFF t))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `FINITE(sphere(a:real^N,r))` THENL
   [REWRITE_TAC[CONNECTED_EQ_CARD_COMPONENTS] THEN
    SUBGOAL_THEN `FINITE(s:real^N->bool) /\ FINITE(t:real^N->bool)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPY_EQUIVALENT_CARD_EQ_COMPONENTS) THEN
    ASM_SIMP_TAC[FINITE_IMP_TOTALLY_DISCONNECTED; FINITE_DIFF; FINITE_IMAGE;
                 CARD_IMAGE_INJ; SET_RULE `{a} = {b} <=> a = b`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      CARD_EQ_IMAGE o rand o lhand o snd) THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      CARD_EQ_IMAGE o lhand o lhand o rand o snd) THEN
    SIMP_TAC[SET_RULE `{a} = {b} <=> a = b`] THEN
    GEN_REWRITE_TAC LAND_CONV [CARD_EQ_SYM] THEN
    ONCE_REWRITE_TAC[TAUT `p ==> q ==> r ==> s <=> p /\ r ==> q ==> s`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP CARD_EQ_TRANS) THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP CARD_EQ_TRANS) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[CARD_DIFF] THEN
    MATCH_MP_TAC(ARITH_RULE
     `m:num <= n /\ p <= n /\ m = p ==> n - m = n - p`) THEN
    ASM_SIMP_TAC[CARD_SUBSET] THEN MATCH_MP_TAC CARD_EQ_CARD_IMP THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [FINITE_SPHERE]) THEN
    REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LE] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `~(n = 1) ==> 1 <= n ==> 2 <= n`)) THEN
    REWRITE_TAC[DIMINDEX_GE_1] THEN DISCH_TAC] THEN
  ASM_CASES_TAC `dimindex(:N) = 2` THENL
   [ASM_SIMP_TAC[CONNECTED_COMPLEMENT_SUBSET_CIRCLE] THEN
    MATCH_MP_TAC HOMOTOPY_EQUIVALENT_CONNECTEDNESS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `s PSUBSET sphere(a:real^N,r) <=> t PSUBSET sphere(a:real^N,r)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`]
      HOMOTOPY_EQUIVALENT_SEPARATION) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL[`sphere(a:real^N,r)`; `s:real^N->bool`; `a:real^N`; `r:real`]
      JORDAN_BROUWER_NONSEPARATION) THEN
    MP_TAC(ISPECL[`sphere(a:real^N,r)`; `t:real^N->bool`; `a:real^N`; `r:real`]
      JORDAN_BROUWER_NONSEPARATION) THEN
    MP_TAC(ISPECL[`sphere(a:real^N,r)`; `a:real^N`; `r:real`]
      JORDAN_BROUWER_SEPARATION) THEN
    ASM_REWRITE_TAC[HOMEOMORPHIC_REFL] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> s PSUBSET t \/ s = t`))) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `(s PSUBSET u <=> t PSUBSET u)
    ==> s SUBSET u /\ t SUBSET u
        ==> s = u /\ t = u \/ s PSUBSET u /\ t PSUBSET u`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[DIFF_EQ_EMPTY] THEN
  SUBGOAL_THEN
  `?w z:real^N. w IN sphere(a,r) /\ z IN sphere(a,r) /\ ~(w IN s) /\ ~(z IN t)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(sphere(a:real^N,r) DELETE w) homeomorphic (:real^(N,1)finite_diff)`
  MP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_SPHERE_UNIV THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DIMINDEX_FINITE_DIFF; DIMINDEX_1] THEN ASM_ARITH_TAC;
    REWRITE_TAC[homeomorphic; LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC
   [`f:real^N->real^(N,1)finite_diff`; `g:real^(N,1)finite_diff->real^N`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(sphere(a:real^N,r) DELETE z) homeomorphic (:real^(N,1)finite_diff)`
  MP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_SPHERE_UNIV THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DIMINDEX_FINITE_DIFF; DIMINDEX_1] THEN ASM_ARITH_TAC;
    REWRITE_TAC[homeomorphic; LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC
   [`h:real^N->real^(N,1)finite_diff`; `k:real^(N,1)finite_diff->real^N`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
    [`IMAGE (f:real^N->real^(N,1)finite_diff) s`;
     `IMAGE (h:real^N->real^(N,1)finite_diff) t`]
    HOMOTOPY_EQUIVALENT_SEPARATION) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[HOMEOMORPHISM_COMPACTNESS;
        SET_RULE `s SUBSET t /\ ~(a IN s) ==> s SUBSET t DELETE a`];
      TRANS_TAC HOMOTOPY_EQUIVALENT_TRANS `s:real^N->bool` THEN CONJ_TAC THENL
       [ALL_TAC;
        TRANS_TAC HOMOTOPY_EQUIVALENT_TRANS `t:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMOTOPY_EQUIVALENT_SYM]] THEN
      MATCH_MP_TAC HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT THEN
      MATCH_MP_TAC HOMEOMORPHIC_SELF_IMAGE THEN
      ASM_MESON_TAC[SET_RULE
       `s SUBSET t /\ ~(a IN s) ==> s SUBSET t DELETE a`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIV DIFF IMAGE (f:real^N->real^(N,1)finite_diff) s =
    IMAGE f ((sphere(a,r) DELETE w) DIFF s) /\
    UNIV DIFF IMAGE (h:real^N->real^(N,1)finite_diff) t =
    IMAGE h ((sphere(a,r) DELETE z) DIFF t)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t /\
      IMAGE f s DIFF IMAGE f t = u
      ==> u = IMAGE f (s DIFF t)`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism; IN_UNIV]) THEN
    (CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]]) THEN
    MATCH_MP_TAC IMAGE_DIFF_INJ_ALT THEN
    ASM_REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE; SUBSET_DELETE] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC EQ_IMP] THEN
  BINOP_TAC THEN
  FIRST_ASSUM(fun th ->
   W(MP_TAC o PART_MATCH (lhand o rand)
   (MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] HOMEOMORPHISM_CONNECTEDNESS) th) o
   lhand o snd)) THEN
  REWRITE_TAC[SUBSET_DIFF] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SET_RULE `s DELETE a DIFF t = (s DIFF t) DELETE a`] THEN
  MATCH_MP_TAC CONNECTED_OPEN_IN_SPHERE_DELETE_EQ THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `r:real`] THEN
  ASM_SIMP_TAC[OPEN_IN_DIFF_CLOSED; COMPACT_IMP_CLOSED] THEN
  ASM_ARITH_TAC);;

let HOMEOMORPHIC_SEPARATION_SPHERE = prove
 (`!s t:real^N->bool a r.
      s SUBSET sphere(a,r) /\ t SUBSET sphere(a,r) /\ s homeomorphic t
      ==> (connected (sphere(a,r) DIFF s) <=> connected(sphere(a,r) DIFF t))`,
  SUBGOAL_THEN
   `!s t:real^N->bool a r.
      s SUBSET sphere(a,r) /\ t SUBSET sphere(a,r) /\ s homeomorphic t
      ==> connected (sphere(a,r) DIFF t)
          ==> connected(sphere(a,r) DIFF s)`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN EQ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
    ASM_REWRITE_TAC[]] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  ASM_SIMP_TAC[SEPARATION_BY_CLOSED_INTERMEDIATES_EQ;
               LOCALLY_CONNECTED_SPHERE] THEN
  SIMP_TAC[CLOSED_IN_CLOSED_EQ; CLOSED_SPHERE] THEN
  SUBGOAL_THEN
   `!c:real^N->bool. closed c /\ c SUBSET sphere(a,r) <=>
                     compact c /\ c SUBSET sphere(a,r)`
   (fun th -> REWRITE_TAC[th] THEN REWRITE_TAC[GSYM CONJ_ASSOC])
  THENL
   [MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_SUBSET; BOUNDED_SPHERE];
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC)] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `IMAGE (f:real^N->real^N) c` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[COMPACT_CONTINUOUS_IMAGE; CONTINUOUS_ON_SUBSET];
    REPLICATE_TAC 2 (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC])] THEN
  X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (g:real^N->real^N) d`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_MESON_TAC[COMPACT_CONTINUOUS_IMAGE; CONTINUOUS_ON_SUBSET];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    MATCH_MP_TAC HOMOTOPY_EQUIVALENT_SEPARATION_SPHERE THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[COMPACT_CONTINUOUS_IMAGE; CONTINUOUS_ON_SUBSET];
      MATCH_MP_TAC HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT THEN
      MATCH_MP_TAC HOMEOMORPHIC_SELF_IMAGE THEN
      MAP_EVERY EXISTS_TAC
       [`f:real^N->real^N`; `t:real^N->bool`; `s:real^N->bool`] THEN
      ASM_REWRITE_TAC[homeomorphism]]]);;

let HOMEOMORPHIC_SEPARATION = prove
 (`!s t. bounded s /\ bounded t /\ s homeomorphic t
         ==> (connected((:real^N) DIFF s) <=> connected((:real^N) DIFF t))`,
  SUBGOAL_THEN
   `!s t. bounded s /\ bounded t /\ s homeomorphic t /\
          connected((:real^N) DIFF s)
          ==> connected((:real^N) DIFF t)`
  MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[HOMEOMORPHIC_SYM]] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `dimindex(:N) = 1` THENL
   [ASM_SIMP_TAC[IMP_CONJ; BOUNDED_SEPARATION_1D] THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_SIMP_TAC[HOMEOMORPHIC_EMPTY];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `~(n = 1) ==> 1 <= n ==> 2 <= n`)) THEN
    REWRITE_TAC[DIMINDEX_GE_1] THEN REPEAT STRIP_TAC] THEN
  SUBGOAL_THEN `basis 1 IN sphere(vec 0:real^(N,1)finite_sum,&1)`
  ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_GE_1; LE_REFL];
    ABBREV_TAC `a:real^(N,1)finite_sum = basis 1` THEN
    FIRST_X_ASSUM(K ALL_TAC o SYM)] THEN
  SUBGOAL_THEN
   `(sphere(vec 0:real^(N,1)finite_sum,&1) DELETE a) homeomorphic (:real^N)`
  MP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_SPHERE_UNIV THEN
    ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; REAL_LT_01];
    REWRITE_TAC[homeomorphic; LEFT_IMP_EXISTS_THM]] THEN
  ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN
  MAP_EVERY X_GEN_TAC
   [`g:real^(N,1)finite_sum->real^N`; `f:real^N->real^(N,1)finite_sum`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`IMAGE (f:real^N->real^(N,1)finite_sum) s`;
    `IMAGE (f:real^N->real^(N,1)finite_sum) t`;
    `vec 0:real^(N,1)finite_sum`; `&1`]
   HOMEOMORPHIC_SEPARATION_SPHERE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHISM]) THEN ASM SET_TAC[];
      TRANS_TAC HOMEOMORPHIC_TRANS `s:real^N->bool` THEN CONJ_TAC THENL
       [ALL_TAC;
        TRANS_TAC HOMEOMORPHIC_TRANS `t:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM]] THEN
      MATCH_MP_TAC HOMEOMORPHIC_SELF_IMAGE THEN
      ASM_MESON_TAC[HOMEOMORPHIC_SELF_IMAGE; SUBSET_UNIV]];
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`)] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `sphere (vec 0,&1) DIFF IMAGE f s =
      a INSERT IMAGE (f:real^N->real^(N,1)finite_sum) (UNIV DIFF s)`
    SUBST1_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHISM]) THEN ASM SET_TAC[];
      W(MP_TAC o PART_MATCH (lhand o rand) CONNECTED_INSERT o snd)] THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[SUBSET_UNIV; HOMEOMORPHISM_CONNECTEDNESS];
      DISCH_THEN SUBST1_TAC] THEN
    DISJ2_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SET_RULE `s DELETE a = s DIFF {a}`]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        BOUNDED_IMAGE_IN_COMPACTIFICATION)) THEN
    REWRITE_TAC[SET_RULE `(p <=> s INTER {a} = {}) <=> (a IN s <=> ~p)`] THEN
    SIMP_TAC[COMPACT_SPHERE; CLOSED_UNIV; SUBSET_UNIV] THEN
    DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC COBOUNDED_IMP_UNBOUNDED THEN
    ASM_REWRITE_TAC[COMPL_COMPL];
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(:real^N) DIFF t =
      IMAGE (g:real^(N,1)finite_sum->real^N)
            ((sphere(vec 0,&1) DIFF IMAGE f t) DELETE a)`
    SUBST1_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism; IN_UNIV]) THEN
      ONCE_REWRITE_TAC[SET_RULE `(s DIFF t) DELETE a = s DELETE a DIFF t`] THEN
      MATCH_MP_TAC(SET_RULE
       `IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t /\
        IMAGE f s = u /\ IMAGE f t = v
        ==> u DIFF v = IMAGE f (s DIFF t)`) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHISM_SYM]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HOMEOMORPHISM_CONNECTEDNESS)) THEN
    DISCH_THEN(fun th -> W(MP_TAC o PART_MATCH (lhand o rand) th o snd)) THEN
    ANTS_TAC THENL [SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `~(a IN  IMAGE (f:real^N->real^(N,1)finite_sum) (closure t))`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `t:real^N->bool` o
         MATCH_MP (REWRITE_RULE[IMP_CONJ] HOMEOMORPHISM_CLOSURE)) THEN
      REWRITE_TAC[SUBSET_UNIV; INTER_UNIV] THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`vec 0:real^(N,1)finite_sum`; `a:real^(N,1)finite_sum`; `&1`;
      `sphere (vec 0,&1) DIFF
       IMAGE (f:real^N->real^(N,1)finite_sum) (closure t)`;
      `sphere (vec 0,&1) DIFF
       IMAGE (f:real^N->real^(N,1)finite_sum) t`]
    CONNECTED_IN_SPHERE_DELETE_INTERIOR_POINT_EQ) THEN
    ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF; SUBSET_DIFF] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
      MATCH_MP_TAC CLOSED_SUBSET THEN
      RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHISM]) THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[COMPACT_CLOSURE] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      MP_TAC(ISPEC `t:real^N->bool` CLOSURE_SUBSET) THEN SET_TAC[]]]);;

let CONNECTED_COMPLEMENT_CONTRACTIBLE = prove
 (`!s. 2 <= dimindex(:N) /\ compact s /\ contractible s
       ==> connected((:real^N) DIFF s)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[DIFF_EMPTY; CONNECTED_UNIV] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `{a:real^N}`]
        HOMOTOPY_EQUIVALENT_SEPARATION) THEN
  ASM_SIMP_TAC[HOMOTOPY_EQUIVALENT_SING; COMPACT_SING; AR_SING;
               CONNECTED_COMPLEMENT_ABSOLUTE_RETRACT]);;

let CONNECTED_COMPLEMENT_SIMPLE_PATH_IMAGE = prove
 (`!g. 3 <= dimindex(:N) /\ simple_path g
       ==> connected((:real^N) DIFF path_image g)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `arc(g:real^1->real^N)` THEN
  ASM_SIMP_TAC[ARITH_RULE `3 <= n ==> 2 <= n`; CONNECTED_ARC_COMPLEMENT] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [ARC_SIMPLE_PATH]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`path_image g:real^N->bool`;
    `relative_frontier(convex hull {vec 0:real^N,basis 1,basis 2})`]
    HOMOTOPY_EQUIVALENT_SEPARATION) THEN
  ASM_SIMP_TAC[COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH] THEN
  SIMP_TAC[COMPACT_RELATIVE_FRONTIER; COMPACT_CONVEX_HULL;
           FINITE_IMP_COMPACT; FINITE_INSERT; FINITE_EMPTY] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT THEN
    TRANS_TAC HOMEOMORPHIC_TRANS
     `relative_frontier(cball(vec 0:real^2,&1))` THEN
    CONJ_TAC THENL
     [SIMP_TAC[RELATIVE_FRONTIER_CBALL; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      ASM_SIMP_TAC[HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE; REAL_LT_01];

      MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
      REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; CONVEX_CONVEX_HULL] THEN
      REWRITE_TAC[BOUNDED_CONVEX_HULL_EQ; BOUNDED_INSERT; BOUNDED_EMPTY] THEN
      REWRITE_TAC[AFF_DIM_CBALL; REAL_LT_01] THEN CONV_TAC SYM_CONV THEN
      REWRITE_TAC[AFF_DIM_CONVEX_HULL; DIMINDEX_2] THEN
      SIMP_TAC[AFF_DIM_DIM_0; HULL_INC; IN_INSERT; INT_OF_NUM_EQ] THEN
      REWRITE_TAC[DIM_INSERT_0] THEN
      REWRITE_TAC[DIM_INSERT; SPAN_SING; DIM_SING; SPAN_EMPTY; IN_SING] THEN
      ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_2; ARITH; DIM_EMPTY;
                   ARITH_RULE `3 <= n ==> 2 <= n`] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `u:real` MP_TAC) THEN
      DISCH_THEN(MP_TAC o AP_TERM `\x:real^N. x$1`) THEN
      ASM_SIMP_TAC[BASIS_COMPONENT; VECTOR_MUL_COMPONENT; ARITH;
                   ARITH_RULE `3 <= n ==> 1 <= n /\ 2 <= n`] THEN
      REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RELATIVE_FRONTIER_OF_TRIANGLE o
    rand o rand o snd) THEN
  ASM_SIMP_TAC[COLLINEAR_LEMMA; BASIS_NONZERO; DIMINDEX_2; ARITH; DIM_EMPTY;
                 ARITH_RULE `3 <= n ==> 1 <= n /\ 2 <= n`] THEN
  ANTS_TAC THENL
   [DISCH_THEN(CHOOSE_THEN (MP_TAC o AP_TERM `\x:real^N. x$2`)) THEN
    ASM_SIMP_TAC[BASIS_COMPONENT; VECTOR_MUL_COMPONENT; ARITH;
                 ARITH_RULE `3 <= n ==> 1 <= n /\ 2 <= n`] THEN
    REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[SET_RULE `a UNION b UNION c = UNIONS {a,b,c}`] THEN
  MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED THEN
  MATCH_MP_TAC PATH_CONNECTED_OPEN_IN_DIFF_UNIONS_LOWDIM THEN
  REWRITE_TAC[CONNECTED_UNIV; AFFINE_HULL_UNIV; OPEN_IN_REFL] THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT] THEN
  REWRITE_TAC[NOT_IN_EMPTY; CLOSED_SEGMENT; AFF_DIM_SEGMENT] THEN
  REWRITE_TAC[AFF_DIM_UNIV] THEN
  REPEAT CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN
  ASM_ARITH_TAC);;

let PATH_CONNECTED_PSUPERSET_COMPLEMENT_SIMPLE_PATH_IMAGE = prove
 (`!g s:real^N->bool.
        2 <= dimindex(:N) /\ simple_path g /\
        (:real^N) DIFF path_image g PSUBSET s
        ==> path_connected s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `arc(g:real^1->real^N)` THENL
   [MATCH_MP_TAC PATH_CONNECTED_SUPERSET_COMPLEMENT_ARC_IMAGE THEN
    ASM_MESON_TAC[PSUBSET];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [ARC_SIMPLE_PATH]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  ASM_CASES_TAC `3 <= dimindex(:N)` THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC
     PATH_CONNECTED_INTERMEDIATE_CLOSURE_ANR_COMPLEMENT_COMPONENT THEN
    EXISTS_TAC `path_image g:real^N->bool` THEN
    EXISTS_TAC `(:real^N) DIFF path_image g` THEN
    ASM_SIMP_TAC[COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH] THEN
    ASM_SIMP_TAC[ANR_PATH_IMAGE_SIMPLE_PATH; IN_COMPONENTS_SELF] THEN
    ASM_SIMP_TAC[CONNECTED_COMPLEMENT_SIMPLE_PATH_IMAGE] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SET_RULE `s DIFF t = {} <=> s SUBSET t`] THEN
      ASM_MESON_TAC[SIMPLE_PATH_IMP_PATH; BOUNDED_PATH_IMAGE; BOUNDED_SUBSET;
                    NOT_BOUNDED_UNIV];
      ASM SET_TAC[];
      REWRITE_TAC[CLOSURE_COMPLEMENT] THEN
      ASM_SIMP_TAC[INTERIOR_SIMPLE_PATH_IMAGE] THEN SET_TAC[]];
    GEN_REWRITE_TAC RAND_CONV [GSYM COMPL_COMPL] THEN
    MATCH_MP_TAC JORDAN_BROUWER_NONSEPARATION_STRONG THEN
    MAP_EVERY EXISTS_TAC
     [`path_image g:real^N->bool`; `vec 0:real^N`; `&1`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    TRANS_TAC HOMEOMORPHIC_TRANS `sphere(vec 0:real^2,&1)` THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE; REAL_LT_01] THEN
    REWRITE_TAC[GSYM
     (CONV_RULE REAL_RAT_REDUCE_CONV
       (ISPECL [`x:real^N`; `&1`] RELATIVE_FRONTIER_CBALL))] THEN
    MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
    REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; AFF_DIM_CBALL] THEN
    REWRITE_TAC[REAL_LT_01; INT_OF_NUM_EQ; DIMINDEX_2] THEN ASM_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Invariance of domain and corollaries.                                     *)
(* ------------------------------------------------------------------------- *)

let INVARIANCE_OF_DOMAIN = prove
 (`!f:real^N->real^N s.
        f continuous_on s /\ open s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> open(IMAGE f s)`,
  let lemma = prove
   (`!f:real^N->real^N a r.
          f continuous_on cball(a,r) /\ &0 < r /\
          (!x y. x IN cball(a,r) /\ y IN cball(a,r) /\ f x = f y ==> x = y)
          ==> open(IMAGE f (ball(a,r)))`,
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `dimindex(:N) = 1` THENL
     [MP_TAC(ISPECL [`(:real^N)`; `(:real^1)`] ISOMETRIES_SUBSPACES) THEN
      ASM_SIMP_TAC[SUBSPACE_UNIV; DIM_UNIV; DIMINDEX_1;
                   LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`h:real^N->real^1`; `k:real^1->real^N`] THEN
      REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`(h:real^N->real^1) o f o (k:real^1->real^N)`;
                     `IMAGE (h:real^N->real^1) (cball(a,r))`]
          INJECTIVE_EQ_1D_OPEN_MAP_UNIV) THEN
      MATCH_MP_TAC(TAUT
       `p /\ q /\ r /\ (s ==> t)
        ==> (p /\ q ==> (r <=> s)) ==> t`) THEN
      REPEAT CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
        ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; GSYM IMAGE_o] THEN
        ASM_REWRITE_TAC[o_DEF; IMAGE_ID];
        REWRITE_TAC[IS_INTERVAL_CONNECTED_1] THEN
        MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
        ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; CONNECTED_CBALL];
        ASM_SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM;
                     FORALL_IN_IMAGE; o_DEF] THEN
        ASM SET_TAC[];
        DISCH_THEN(MP_TAC o SPEC `IMAGE (h:real^N->real^1) (ball(a,r))`) THEN
        ASM_SIMP_TAC[IMAGE_SUBSET; BALL_SUBSET_CBALL; GSYM IMAGE_o] THEN
        ANTS_TAC THENL
         [MP_TAC(ISPECL [`a:real^N`; `r:real`] OPEN_BALL); ALL_TAC] THEN
        MATCH_MP_TAC EQ_IMP THENL
         [CONV_TAC SYM_CONV;
          REWRITE_TAC[GSYM o_ASSOC] THEN ONCE_REWRITE_TAC[IMAGE_o] THEN
          ASM_REWRITE_TAC[o_DEF; ETA_AX]] THEN
        MATCH_MP_TAC OPEN_BIJECTIVE_LINEAR_IMAGE_EQ THEN
        ASM_MESON_TAC[]];
       FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
        `~(n = 1) ==> 1 <= n ==> 2 <= n`)) THEN
       REWRITE_TAC[DIMINDEX_GE_1] THEN DISCH_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (f:real^N->real^N) (sphere(a,r))`;
                   `a:real^N`; `r:real`]
          JORDAN_BROUWER_SEPARATION) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
      MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN EXISTS_TAC `f:real^N->real^N` THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET; SPHERE_SUBSET_CBALL;
                    COMPACT_SPHERE];
      DISCH_TAC] THEN
    MP_TAC(ISPEC `(:real^N) DIFF IMAGE f (sphere(a:real^N,r))`
      COBOUNDED_HAS_BOUNDED_COMPONENT) THEN
    ASM_REWRITE_TAC[COMPL_COMPL] THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET; SPHERE_SUBSET_CBALL;
        COMPACT_SPHERE; COMPACT_CONTINUOUS_IMAGE; COMPACT_IMP_BOUNDED];
      DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN
     `IMAGE (f:real^N->real^N) (ball(a,r)) = c`
    SUBST1_TAC THENL
     [ALL_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          OPEN_COMPONENTS)) THEN
      REWRITE_TAC[GSYM closed] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET; SPHERE_SUBSET_CBALL;
        COMPACT_SPHERE; COMPACT_CONTINUOUS_IMAGE; COMPACT_IMP_CLOSED]] THEN
    MATCH_MP_TAC(SET_RULE
     `~(c = {}) /\ (~(c INTER t = {}) ==> t SUBSET c) /\ c SUBSET t
      ==> t = c`) THEN
    REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
          COMPONENTS_MAXIMAL)) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[CONNECTED_BALL] THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; BALL_SUBSET_CBALL];
        REWRITE_TAC[GSYM CBALL_DIFF_SPHERE] THEN
        MP_TAC(ISPECL [`a:real^N`; `r:real`] SPHERE_SUBSET_CBALL) THEN
        ASM SET_TAC[]];
      FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
      FIRST_ASSUM(MP_TAC o SPEC `(:real^N) DIFF IMAGE f (cball(a:real^N,r))` o
        MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] COMPONENTS_MAXIMAL)) THEN
      SIMP_TAC[SET_RULE `UNIV DIFF t SUBSET UNIV DIFF s <=> s SUBSET t`;
               IMAGE_SUBSET; SPHERE_SUBSET_CBALL] THEN
      MATCH_MP_TAC(TAUT `p /\ ~r /\ (~q ==> s) ==> (p /\ q ==> r) ==> s`) THEN
      REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(INST_TYPE [`:N`,`:M`]
          CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT) THEN
        EXISTS_TAC `cball(a:real^N,r)` THEN
        ASM_REWRITE_TAC[CONVEX_CBALL; COMPACT_CBALL] THEN
        ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
        MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN
        EXISTS_TAC `f:real^N->real^N` THEN ASM_REWRITE_TAC[COMPACT_CBALL];
        DISCH_THEN(MP_TAC o
          MATCH_MP(REWRITE_RULE[IMP_CONJ_ALT] BOUNDED_SUBSET)) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COBOUNDED_IMP_UNBOUNDED THEN
        REWRITE_TAC[COMPL_COMPL] THEN
        ASM_MESON_TAC[COMPACT_IMP_BOUNDED; COMPACT_CONTINUOUS_IMAGE;
                      COMPACT_CBALL];
        REWRITE_TAC[GSYM CBALL_DIFF_SPHERE] THEN ASM SET_TAC[]]]) in
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  EXISTS_TAC `IMAGE (f:real^N->real^N) (ball(a,r))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC lemma THEN ASM_MESON_TAC[SUBSET; CONTINUOUS_ON_SUBSET];
    ASM_SIMP_TAC[FUN_IN_IMAGE; CENTRE_IN_BALL];
    MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS]]);;

let INVARIANCE_OF_DOMAIN_SUBSPACES = prove
 (`!f:real^M->real^N u v s.
        subspace u /\ subspace v /\ dim v <= dim u /\
        f continuous_on s /\ IMAGE f s SUBSET v /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        open_in (subtopology euclidean u) s
        ==> open_in (subtopology euclidean v) (IMAGE f s)`,
  let lemma0 = prove
   (`!f:real^M->real^M s u.
          subspace s /\ dim s = dimindex(:N) /\
          f continuous_on u /\ IMAGE f u SUBSET s /\
          (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\
          open_in (subtopology euclidean s) u
          ==> open_in (subtopology euclidean s) (IMAGE f u)`,
    REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`(:real^N)`; `s:real^M->bool`]
      HOMEOMORPHIC_SUBSPACES) THEN
    ASM_REWRITE_TAC[DIM_UNIV; SUBSPACE_UNIV] THEN
    REWRITE_TAC[homeomorphic; homeomorphism; LEFT_IMP_EXISTS_THM; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`h:real^N->real^M`; `k:real^M->real^N`] THEN
    STRIP_TAC THEN MP_TAC(ISPECL
     [`(k:real^M->real^N) o f o (h:real^N->real^M)`;
      `IMAGE (k:real^M->real^N) u`] INVARIANCE_OF_DOMAIN) THEN
    REWRITE_TAC[GSYM IMAGE_o; o_THM] THEN
    SUBGOAL_THEN
     `!t. open t <=>
          open_in (subtopology euclidean (IMAGE (k:real^M->real^N) s)) t`
     (fun th -> REWRITE_TAC[th])
    THENL [ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN]; ALL_TAC] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
        REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
        MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
        MAP_EVERY EXISTS_TAC [`h:real^N->real^M`; `s:real^M->bool`] THEN
        ASM_REWRITE_TAC[homeomorphism];
        REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
        ASM_SIMP_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `IMAGE f u =
        IMAGE (h:real^N->real^M) (IMAGE ((k o f o h) o (k:real^M->real^N)) u)`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC(SET_RULE
         `(!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THEN
        ASM_SIMP_TAC[SUBSET; o_THM] THEN ASM SET_TAC[];
        MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
        MAP_EVERY EXISTS_TAC [`k:real^M->real^N`; `(:real^N)`] THEN
        ASM_REWRITE_TAC[homeomorphism]]]) in
  let lemma1 = prove
   (`!f:real^N->real^N s u.
          subspace s /\ f continuous_on u /\ IMAGE f u SUBSET s /\
          (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\
          open_in (subtopology euclidean s) u
          ==> open_in (subtopology euclidean s) (IMAGE f u)`,
    REWRITE_TAC[INJECTIVE_ON_ALT] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    ABBREV_TAC `s' = {y:real^N | !x. x IN s ==> orthogonal x y}` THEN
    SUBGOAL_THEN `subspace(s':real^N->bool)` ASSUME_TAC THENL
      [EXPAND_TAC "s'" THEN REWRITE_TAC[SUBSPACE_ORTHOGONAL_TO_VECTORS];
       FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBSPACE_IMP_NONEMPTY)] THEN
    ABBREV_TAC `g:real^(N,N)finite_sum->real^(N,N)finite_sum =
                  \z. pastecart (f(fstcart z)) (sndcart z)` THEN
    SUBGOAL_THEN
     `g continuous_on ((u:real^N->bool) PCROSS s') /\
      IMAGE g (u PCROSS s') SUBSET (s:real^N->bool) PCROSS (s':real^N->bool) /\
      (!w z. w IN u PCROSS s' /\ z IN u PCROSS s' ==> (g w = g z <=> w = z))`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "g" THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART;
                 IMAGE_FSTCART_PCROSS] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[CONTINUOUS_ON_EMPTY];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
        SIMP_TAC[PASTECART_IN_PCROSS; SNDCART_PASTECART;
                 FSTCART_PASTECART] THEN
        ASM SET_TAC[];
        EXPAND_TAC "g" THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
        REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART;
                    SNDCART_PASTECART] THEN
        ASM_SIMP_TAC[PASTECART_INJ]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `open_in (subtopology euclidean (s PCROSS s'))
              (IMAGE (g:real^(N,N)finite_sum->real^(N,N)finite_sum)
                     (u PCROSS s'))`
    MP_TAC THENL
     [MATCH_MP_TAC lemma0 THEN
      ASM_SIMP_TAC[SUBSPACE_PCROSS; OPEN_IN_PCROSS_EQ; OPEN_IN_REFL] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[DIM_PCROSS]; ASM_MESON_TAC[]] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `(:real^N)`]
        DIM_SUBSPACE_ORTHOGONAL_TO_VECTORS) THEN
      ASM_REWRITE_TAC[SUBSET_UNIV; SUBSPACE_UNIV; IN_UNIV; DIM_UNIV] THEN
      ARITH_TAC;
      SUBGOAL_THEN
       `IMAGE (g:real^(N,N)finite_sum->real^(N,N)finite_sum) (u PCROSS s') =
        IMAGE f u PCROSS s'`
      SUBST1_TAC THENL
       [EXPAND_TAC "g" THEN
        REWRITE_TAC[EXTENSION; EXISTS_PASTECART; PASTECART_IN_PCROSS;
                    IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                    FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_INJ] THEN
        ASM SET_TAC[];
        ASM_SIMP_TAC[OPEN_IN_PCROSS_EQ; IMAGE_EQ_EMPTY] THEN
        STRIP_TAC THEN ASM_SIMP_TAC[IMAGE_CLAUSES; OPEN_IN_EMPTY]]]) in
  REWRITE_TAC[INJECTIVE_ON_ALT] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  MP_TAC(ISPECL [`u:real^M->bool`; `dim(v:real^N->bool)`]
    CHOOSE_SUBSPACE_OF_SUBSPACE) THEN ASM_SIMP_TAC[SPAN_OF_SUBSPACE] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`v:real^N->bool`; `v:real^M->bool`]
        HOMEOMORPHIC_SUBSPACES) THEN
  ASM_REWRITE_TAC[homeomorphic; homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:real^N->real^M`; `k:real^M->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (f:real^M->real^N) s =
    IMAGE (k:real^M->real^N) (IMAGE ((h:real^N->real^M) o f) s)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC(SET_RULE
     `(!x. x IN u ==> f x = g x) ==> IMAGE f u = IMAGE g u`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    ASM_SIMP_TAC[SUBSET; o_THM] THEN ASM SET_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^M`; `v:real^M->bool`] THEN
    ASM_REWRITE_TAC[homeomorphism] THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `u:real^M->bool` THEN
    ASM_REWRITE_TAC[IMAGE_o] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC lemma1 THEN
    ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[]]);;

let INVARIANCE_OF_DIMENSION_SUBSPACES = prove
 (`!f:real^M->real^N u v s.
      subspace u /\ subspace v /\
      ~(s = {}) /\ open_in (subtopology euclidean u) s /\
      f continuous_on s /\ IMAGE f s SUBSET v /\
      (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
      ==> dim u <= dim v`,
  REWRITE_TAC[GSYM NOT_LT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^M->bool`; `dim(v:real^N->bool)`]
    CHOOSE_SUBSPACE_OF_SUBSPACE) THEN
  ASM_SIMP_TAC[SPAN_OF_SUBSPACE; LE_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`v:real^N->bool`; `t:real^M->bool`]
        HOMEOMORPHIC_SUBSPACES) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[homeomorphic; homeomorphism; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:real^N->real^M`; `k:real^M->real^N`] THEN
  STRIP_TAC THEN MP_TAC(ISPECL
   [`(h:real^N->real^M) o (f:real^M->real^N)`; `u:real^M->bool`;
    `u:real^M->bool`; `s:real^M->bool`]
        INVARIANCE_OF_DOMAIN_SUBSPACES) THEN
  ASM_REWRITE_TAC[LE_LT; NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    REWRITE_TAC[o_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((h:real^N->real^M) o (f:real^M->real^N)) s SUBSET t`
  ASSUME_TAC THENL [REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `w = IMAGE ((h:real^N->real^M) o (f:real^M->real^N)) s` THEN
  DISCH_TAC THEN UNDISCH_TAC `dim(t:real^M->bool) < dim(u:real^M->bool)` THEN
  REWRITE_TAC[NOT_LT] THEN MP_TAC(ISPECL
   [`w:real^M->bool`; `u:real^M->bool`] DIM_OPEN_IN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[IMAGE_EQ_EMPTY]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_SIMP_TAC[DIM_SUBSET]);;

let INVARIANCE_OF_DOMAIN_AFFINE_SETS = prove
 (`!f:real^M->real^N u v s.
        affine u /\ affine v /\ aff_dim v <= aff_dim u /\
        f continuous_on s /\ IMAGE f s SUBSET v /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        open_in (subtopology euclidean u) s
        ==> open_in (subtopology euclidean v) (IMAGE f s)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; OPEN_IN_EMPTY; INJECTIVE_ON_ALT] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?a:real^M b:real^N. a IN s /\ a IN u /\ b IN v`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(\x. --b + x) o (f:real^M->real^N) o (\x. a + x)`;
    `IMAGE (\x:real^M. --a + x) u`; `IMAGE (\x:real^N. --b + x) v`;
    `IMAGE (\x:real^M. --a + x) s`] INVARIANCE_OF_DOMAIN_SUBSPACES) THEN
  REWRITE_TAC[IMAGE_o; INJECTIVE_ON_ALT; OPEN_IN_TRANSLATION_EQ] THEN
  SIMP_TAC[IMP_CONJ; GSYM INT_OF_NUM_LE; GSYM AFF_DIM_DIM_SUBSPACE] THEN
  ASM_REWRITE_TAC[AFF_DIM_TRANSLATION_EQ; RIGHT_FORALL_IMP_THM] THEN
  SIMP_TAC[FORALL_IN_IMAGE; o_THM; GSYM IMAGE_o; IMP_IMP; GSYM CONJ_ASSOC] THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC AFFINE_IMP_SUBSPACE THEN
      ASM_REWRITE_TAC[AFFINE_TRANSLATION_EQ] THEN REWRITE_TAC[IN_IMAGE;
        VECTOR_ARITH `vec 0:real^N = --a + x <=> x = a`] THEN
      ASM_MESON_TAC[];
      REPEAT CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
           SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]);
        REWRITE_TAC[GSYM o_ASSOC] THEN REWRITE_TAC[IMAGE_o] THEN
        MATCH_MP_TAC IMAGE_SUBSET;
        REWRITE_TAC[VECTOR_ARITH `a + x:real^N = a + y <=> x = y`]]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[VECTOR_ARITH `a + --a + x:real^N = x`; GSYM IMAGE_o; o_DEF;
               IMAGE_ID; ETA_AX]);;

let INVARIANCE_OF_DIMENSION_AFFINE_SETS = prove
 (`!f:real^M->real^N u v s.
      affine u /\ affine v /\
      ~(s = {}) /\ open_in (subtopology euclidean u) s /\
      f continuous_on s /\ IMAGE f s SUBSET v /\
      (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
      ==> aff_dim u <= aff_dim v`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; OPEN_IN_EMPTY; INJECTIVE_ON_ALT] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?a:real^M b:real^N. a IN s /\ a IN u /\ b IN v`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(\x. --b + x) o (f:real^M->real^N) o (\x. a + x)`;
    `IMAGE (\x:real^M. --a + x) u`; `IMAGE (\x:real^N. --b + x) v`;
    `IMAGE (\x:real^M. --a + x) s`] INVARIANCE_OF_DIMENSION_SUBSPACES) THEN
  REWRITE_TAC[IMAGE_o; INJECTIVE_ON_ALT; OPEN_IN_TRANSLATION_EQ] THEN
  SIMP_TAC[IMP_CONJ; GSYM INT_OF_NUM_LE; GSYM AFF_DIM_DIM_SUBSPACE] THEN
  ASM_REWRITE_TAC[AFF_DIM_TRANSLATION_EQ; RIGHT_FORALL_IMP_THM] THEN
  SIMP_TAC[FORALL_IN_IMAGE; o_THM; GSYM IMAGE_o; IMP_IMP; GSYM CONJ_ASSOC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC AFFINE_IMP_SUBSPACE THEN
    ASM_REWRITE_TAC[AFFINE_TRANSLATION_EQ] THEN REWRITE_TAC[IN_IMAGE;
      VECTOR_ARITH `vec 0:real^N = --a + x <=> x = a`] THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REPEAT CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
         SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]);
      REWRITE_TAC[GSYM o_ASSOC] THEN REWRITE_TAC[IMAGE_o] THEN
      MATCH_MP_TAC IMAGE_SUBSET;
      REWRITE_TAC[VECTOR_ARITH `a + x:real^N = a + y <=> x = y`]]] THEN
  ASM_SIMP_TAC[VECTOR_ARITH `a + --a + x:real^N = x`; GSYM IMAGE_o; o_DEF;
               IMAGE_ID; ETA_AX]);;

let INVARIANCE_OF_DIMENSION = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\ open s /\ ~(s = {}) /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> dimindex(:M) <= dimindex(:N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DIM_UNIV] THEN
  MATCH_MP_TAC INVARIANCE_OF_DIMENSION_SUBSPACES THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `s:real^M->bool`] THEN
  ASM_REWRITE_TAC[SUBSPACE_UNIV; SUBSET_UNIV; SUBTOPOLOGY_UNIV;
                  GSYM OPEN_IN]);;

let CONTINUOUS_INJECTIVE_IMAGE_SUBSPACE_DIM_LE = prove
 (`!f:real^M->real^N s t.
        subspace s /\ subspace t /\
        f continuous_on s /\ IMAGE f s SUBSET t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> dim(s) <= dim(t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INVARIANCE_OF_DIMENSION_SUBSPACES THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `s:real^M->bool`] THEN
  ASM_REWRITE_TAC[OPEN_IN_REFL] THEN ASM_SIMP_TAC[SUBSPACE_IMP_NONEMPTY]);;

let INVARIANCE_OF_DIMENSION_CONVEX_DOMAIN = prove
 (`!f:real^M->real^N s t.
        convex s /\ f continuous_on s /\ IMAGE f s SUBSET affine hull t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> aff_dim(s) <= aff_dim(t)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_GE] THEN
  MP_TAC(ISPECL
   [`f:real^M->real^N`; `affine hull s:real^M->bool`;
    `affine hull t:real^N->bool`; `relative_interior s:real^M->bool`]
        INVARIANCE_OF_DIMENSION_AFFINE_SETS) THEN
  ASM_REWRITE_TAC[AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL;
                  OPEN_IN_RELATIVE_INTERIOR] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  ASSUME_TAC(ISPEC `s:real^M->bool` RELATIVE_INTERIOR_SUBSET) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]]);;

let HOMEOMORPHIC_CONVEX_SETS = prove
 (`!s:real^M->bool t:real^N->bool.
        convex s /\ convex t /\ s homeomorphic t ==> aff_dim s = aff_dim t`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; GSYM INT_LE_ANTISYM; homeomorphism] THEN
  MAP_EVERY X_GEN_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INVARIANCE_OF_DIMENSION_CONVEX_DOMAIN THENL
   [EXISTS_TAC `f:real^M->real^N`; EXISTS_TAC `g:real^N->real^M`] THEN
  ASM_REWRITE_TAC[HULL_SUBSET] THEN ASM SET_TAC[]);;

let HOMEOMORPHIC_CONVEX_COMPACT_SETS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        convex s /\ compact s /\ convex t /\ compact t
        ==> (s homeomorphic t <=> aff_dim s = aff_dim t)`,
  MESON_TAC[HOMEOMORPHIC_CONVEX_SETS; HOMEOMORPHIC_CONVEX_COMPACT_SETS]);;

let INVARIANCE_OF_DOMAIN_GEN = prove
 (`!f:real^M->real^N s.
        dimindex(:N) <= dimindex(:M) /\ f continuous_on s /\ open s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> open(IMAGE f s)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`f:real^M->real^N`; `(:real^M)`; `(:real^N)`; `s:real^M->bool`]
   INVARIANCE_OF_DOMAIN_SUBSPACES) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; SUBSPACE_UNIV;
                  DIM_UNIV; SUBSET_UNIV]);;

let INJECTIVE_INTO_1D_IMP_OPEN_MAP_UNIV = prove
 (`!f:real^N->real^1 s t.
        f continuous_on s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        open t /\ t SUBSET s
        ==> open (IMAGE f t)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INVARIANCE_OF_DOMAIN_GEN THEN
  ASM_REWRITE_TAC[DIMINDEX_1; DIMINDEX_GE_1] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]]);;

let CONTINUOUS_ON_INVERSE_OPEN = prove
 (`!f:real^M->real^N g s.
        dimindex(:N) <= dimindex(:M) /\
        f continuous_on s /\ open s /\
        (!x. x IN s ==> g(f x) = x)
        ==> g continuous_on IMAGE f s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CONTINUOUS_OPEN_IN_PREIMAGE_EQ] THEN
  X_GEN_TAC `t:real^M->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{x | x IN IMAGE f s /\ g x IN t} = IMAGE (f:real^M->real^N) (s INTER t)`
  SUBST1_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC OPEN_OPEN_IN_TRANS] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  CONJ_TAC THEN MATCH_MP_TAC INVARIANCE_OF_DOMAIN_GEN THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTER_SUBSET]);;

let CONTINUOUS_ON_INVERSE_INTO_1D = prove
 (`!f:real^N->real^1 g s t.
        f continuous_on s /\
        (path_connected s \/
         connected s /\ (locally compact s \/ locally connected s) \/
         compact s \/
         open s) /\
        IMAGE f s = t /\ (!x. x IN s ==> g(f x) = x)
        ==> g continuous_on t`,
  REPEAT STRIP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_INVERSE_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->real^1`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC INJECTIVE_INTO_1D_IMP_OPEN_MAP THEN ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_INVERSE_INJECTIVE_PROPER_MAP THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->real^1`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONOTONE_INTO_1D_IMP_PROPER_MAP THEN
    ASM_REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `y:real^1` THEN
    SUBGOAL_THEN
     `{x | x IN s /\ (f:real^N->real^1) x = y} = {} \/
      ?a. {x | x IN s /\ (f:real^N->real^1) x = y} = {a}`
    STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[];
      ASM_REWRITE_TAC[COMPACT_EMPTY; CONNECTED_EMPTY];
      ASM_REWRITE_TAC[COMPACT_SING; CONNECTED_SING]];
    MATCH_MP_TAC CONTINUOUS_ON_INVERSE_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->real^1`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    REWRITE_TAC[open_in; SUBSET; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; X_GEN_TAC `x:real^N` THEN DISCH_TAC] THEN
    ABBREV_TAC `u = connected_component w (x:real^N)` THEN
    SUBGOAL_THEN
     `connected u /\ (x:real^N) IN u /\ u SUBSET s /\ u SUBSET w /\
      open_in (subtopology euclidean s) u`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN REPEAT CONJ_TAC THENL
       [MESON_TAC[CONNECTED_CONNECTED_COMPONENT];
        ASM_MESON_TAC[IN; CONNECTED_COMPONENT_REFL];
        ASM_MESON_TAC[CONNECTED_COMPONENT_SUBSET; SUBSET_TRANS];
        ASM_MESON_TAC[CONNECTED_COMPONENT_SUBSET];
        ASM_MESON_TAC[LOCALLY_CONNECTED_OPEN_CONNECTED_COMPONENT]];
      SUBGOAL_THEN
       `?e. &0 < e /\ !y. y IN t /\ dist(y,(f:real^N->real^1) x) < e
            ==> y IN IMAGE f u`
      ASSUME_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o
        check (free_in `w:real^N->bool`) o concl))] THEN
    SUBGOAL_THEN
     `(?e. &0 < e /\
           !y. y IN t /\ drop(f x) <= drop y /\ drop y < drop(f x) + e
               ==> y IN IMAGE f (u:real^N->bool)) /\
      (?e. &0 < e /\
           !y. y IN t /\ drop(f x) - e < drop y /\ drop y <= drop(f x)
               ==> y IN IMAGE f (u:real^N->bool))`
    MP_TAC THENL
     [ALL_TAC;
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))
       (X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
      REWRITE_TAC[IMP_IMP; AND_FORALL_THM; TAUT
       `(p ==> r) /\ (q ==> r) <=> (p \/ q ==> r)`] THEN
      DISCH_TAC THEN EXISTS_TAC `min d e:real` THEN
      ASM_REWRITE_TAC[REAL_LT_MIN; DIST_1] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
    MP_TAC(ISPECL [`f:real^N->real^1`; `s:real^N->bool`]
        MONOTONE_TOPOLOGICALLY_INTO_1D) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^1` THEN
      SUBGOAL_THEN
       `{x | x IN s /\ (f:real^N->real^1) x = y} = {} \/
        ?a. {x | x IN s /\ (f:real^N->real^1) x = y} = {a}`
      STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[];
        ASM_REWRITE_TAC[COMPACT_EMPTY; CONNECTED_EMPTY];
        ASM_REWRITE_TAC[COMPACT_SING; CONNECTED_SING]];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
     [DISCH_THEN(MP_TAC o SPEC
       `{y | y IN IMAGE (f:real^N->real^1) s /\ drop(f x) <= drop y}`);
      DISCH_THEN(MP_TAC o SPEC
       `{y | y IN IMAGE (f:real^N->real^1) s /\ drop y <= drop(f x)}`)] THEN
    (ANTS_TAC THENL
      [REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER {x | P x}`] THEN
       REWRITE_TAC[GSYM CONVEX_CONNECTED_1] THEN MATCH_MP_TAC CONVEX_INTER THEN
       REWRITE_TAC[drop; CONVEX_HALFSPACE_COMPONENT_LE;
                   REWRITE_RULE[real_ge] CONVEX_HALFSPACE_COMPONENT_GE] THEN
       REWRITE_TAC[CONVEX_CONNECTED_1] THEN
       ASM_MESON_TAC[CONNECTED_CONTINUOUS_IMAGE];
       ALL_TAC]) THEN
    REWRITE_TAC[IN_ELIM_THM; SET_RULE
     `x IN s /\ f x IN IMAGE f s /\ P x <=> x IN s /\ P x`] THEN
    REWRITE_TAC[CONNECTED_CLOSED_IN; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `{x:real^N}`) THEN
    REWRITE_TAC[CLOSED_IN_SING; IN_ELIM_THM; REAL_LE_REFL] THEN
    REWRITE_TAC[NOT_INSERT_EMPTY] THENL
     [DISCH_THEN(MP_TAC o SPEC
       `{w:real^N | w IN s DIFF u /\ drop(f x) <= drop(f w)}`);
      DISCH_THEN(MP_TAC o SPEC
       `{w:real^N | w IN s DIFF u /\ drop(f w) <= drop(f x)}`)] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (TAUT
     `~(p /\ q /\ r /\ s /\ ~t) ==> p /\ q /\ s ==> t \/ ~r`)) THEN
    (ANTS_TAC THENL
      [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
       CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
       REWRITE_TAC[SET_RULE
        `{x | x IN s DIFF u /\ P x} =
         {x | x IN s /\ P x} INTER (s DIFF u)`] THEN
       MATCH_MP_TAC CLOSED_IN_SUBTOPOLOGY_INTER_SUBSET THEN
       EXISTS_TAC `s:real^N->bool` THEN
       CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
       MATCH_MP_TAC CLOSED_IN_INTER THEN REWRITE_TAC[CLOSED_IN_REFL] THEN
       MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_REFL];
       ALL_TAC]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `{x | x IN s DIFF u /\ P x} = {} \/
      ~({x | x IN s /\ P x} SUBSET {a} UNION {x | x IN s DIFF u /\ P x})
      ==> u SUBSET s
          ==> (!x. x IN s /\ P x ==> x = a) \/
              ?x. x IN u /\ ~(x = a) /\ P x`)) THEN
    ASM_REWRITE_TAC[] THEN
    (DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
      [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN ASM SET_TAC[];
       ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `dist((f:real^N->real^1) x,f y)` THEN
    ASM_REWRITE_TAC[GSYM DIST_NZ] THEN
    (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    X_GEN_TAC `z:real^1` THEN STRIP_TAC THEN
    (SUBGOAL_THEN `is_interval(IMAGE (f:real^N->real^1) u)` MP_TAC THENL
      [REWRITE_TAC[IS_INTERVAL_CONNECTED_1] THEN
       MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
       ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
       REWRITE_TAC[IS_INTERVAL_1] THEN DISCH_THEN MATCH_MP_TAC])
    THENL
     [ALL_TAC;
      ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM]] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    ONCE_REWRITE_TAC[EXISTS_IN_IMAGE] THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `(f:real^N->real^1) y` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_NOT_LE]) THEN
    REWRITE_TAC[DIST_1] THEN ASM_REAL_ARITH_TAC;
    ASM_MESON_TAC[CONTINUOUS_ON_INVERSE];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CONTINUOUS_ON_INVERSE_OPEN THEN
    ASM_REWRITE_TAC[DIMINDEX_1; DIMINDEX_GE_1]]);;

let REAL_CONTINUOUS_ON_INVERSE = prove
 (`!f g s. f real_continuous_on s /\
           (is_realinterval s \/ real_compact s \/ real_open s) /\
           (!x. x IN s ==> g(f x) = x)
           ==> g real_continuous_on (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; real_compact; REAL_OPEN;
              IS_REALINTERVAL_IS_INTERVAL] THEN
  DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_INVERSE_INTO_1D THEN
  MAP_EVERY EXISTS_TAC [`lift o f o drop`; `IMAGE lift s`] THEN
  ASM_REWRITE_TAC[GSYM IS_INTERVAL_PATH_CONNECTED_1] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; o_DEF; LIFT_DROP; GSYM IMAGE_o] THEN
  ASM_MESON_TAC[]);;

let REAL_CONTINUOUS_ON_INVERSE_ALT = prove
 (`!f g s t. f real_continuous_on s /\
             (is_realinterval s \/ real_compact s \/ real_open s) /\
             IMAGE f s = t /\ (!x. x IN s ==> g(f x) = x)
           ==> g real_continuous_on t`,
  MESON_TAC[REAL_CONTINUOUS_ON_INVERSE]);;

let INVARIANCE_OF_DOMAIN_HOMEOMORPHISM = prove
 (`!f:real^M->real^N s.
        dimindex(:N) <= dimindex(:M) /\ f continuous_on s /\ open s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ?g. homeomorphism (s,IMAGE f s) (f,g)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^M` THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[homeomorphism] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_INVERSE_OPEN] THEN ASM SET_TAC[]);;

let INVARIANCE_OF_DOMAIN_HOMEOMORPHIC = prove
 (`!f:real^M->real^N s.
        dimindex(:N) <= dimindex(:M) /\ f continuous_on s /\ open s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> s homeomorphic (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP INVARIANCE_OF_DOMAIN_HOMEOMORPHISM) THEN
  REWRITE_TAC[homeomorphic] THEN MESON_TAC[]);;

let HOMEOMORPHIC_INTERVALS_EQ = prove
 (`(!a b:real^M c d:real^N.
        interval[a,b] homeomorphic interval[c,d] <=>
        aff_dim(interval[a,b]) = aff_dim(interval[c,d])) /\
   (!a b:real^M c d:real^N.
        interval[a,b] homeomorphic interval(c,d) <=>
        interval[a,b] = {} /\ interval(c,d) = {}) /\
   (!a b:real^M c d:real^N.
        interval(a,b) homeomorphic interval[c,d] <=>
        interval(a,b) = {} /\ interval[c,d] = {}) /\
   (!a b:real^M c d:real^N.
        interval(a,b) homeomorphic interval(c,d) <=>
        interval(a,b) = {} /\ interval(c,d) = {} \/
        ~(interval(a,b) = {}) /\ ~(interval(c,d) = {}) /\
        dimindex(:M) = dimindex(:N))`,
  SIMP_TAC[HOMEOMORPHIC_CONVEX_COMPACT_SETS_EQ; CONVEX_INTERVAL;
           COMPACT_INTERVAL] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY] THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_COMPACTNESS) THEN
    REWRITE_TAC[COMPACT_INTERVAL_EQ] THEN ASM_MESON_TAC[HOMEOMORPHIC_EMPTY];
    FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_COMPACTNESS) THEN
    REWRITE_TAC[COMPACT_INTERVAL_EQ] THEN ASM_MESON_TAC[HOMEOMORPHIC_EMPTY];
    MATCH_MP_TAC(TAUT
     `(p <=> q) /\ (~p /\ ~q ==> r) ==> p /\ q \/ ~p /\ ~q /\ r`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[HOMEOMORPHIC_EMPTY]; STRIP_TAC] THEN
    REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THEN
    MATCH_MP_TAC INVARIANCE_OF_DIMENSION THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THENL
     [ALL_TAC; GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM]] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THENL
     [EXISTS_TAC `interval(a:real^M,b)`;
      EXISTS_TAC `interval(c:real^N,d)`] THEN
    ASM_REWRITE_TAC[OPEN_INTERVAL] THEN ASM SET_TAC[];
    TRANS_TAC HOMEOMORPHIC_TRANS
     `IMAGE ((\x. lambda i. x$i):real^M->real^N)
            (interval(a,b))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INVARIANCE_OF_DOMAIN_HOMEOMORPHIC THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[LE_REFL];
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
        SIMP_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                 LAMBDA_BETA; CART_EQ];
        REWRITE_TAC[OPEN_INTERVAL];
        SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE ((\x. lambda i. x$i):real^M->real^N)
            (interval(a,b)) =
            interval((lambda i. a$i),(lambda i. b$i))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
      SIMP_TAC[IN_INTERVAL; LAMBDA_BETA] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `(lambda i. (y:real^N)$i):real^M` THEN
      SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM) THEN   SIMP_TAC[CART_EQ; LAMBDA_BETA];
      MATCH_MP_TAC HOMEOMORPHIC_OPEN_INTERVALS THEN
      GEN_REWRITE_TAC I [TAUT `(p <=> q) <=> (~p <=> ~q)`] THEN
      SIMP_TAC[INTERVAL_NE_EMPTY; LAMBDA_BETA] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o
        GEN_REWRITE_RULE I [INTERVAL_NE_EMPTY])) THEN
      ASM_MESON_TAC[]]]);;

let CONTINUOUS_IMAGE_SUBSET_INTERIOR = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\ dimindex(:N) <= dimindex(:M) /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> IMAGE f (interior s) SUBSET interior(IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN
  SIMP_TAC[IMAGE_SUBSET; INTERIOR_SUBSET] THEN
  ASM_CASES_TAC `interior s:real^M->bool = {}` THENL
   [ASM_REWRITE_TAC[INTERIOR_EMPTY; OPEN_EMPTY; IMAGE_CLAUSES];
    MATCH_MP_TAC INVARIANCE_OF_DOMAIN_GEN] THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTERIOR_SUBSET; SUBSET]);;

let HOMEOMORPHIC_INTERIORS_SAME_DIMENSION = prove
 (`!s:real^M->bool t:real^N->bool.
        dimindex(:M) = dimindex(:N) /\ s homeomorphic t
        ==> (interior s) homeomorphic (interior t)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MINIMAL]) THEN
  REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^M->real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^M` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[REWRITE_RULE[SUBSET] INTERIOR_SUBSET] THEN
  REWRITE_TAC[SET_RULE `(!x. x IN s ==> f x IN t) <=> IMAGE f s SUBSET t`] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `t = IMAGE (f:real^M->real^N) s` SUBST1_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMAGE_SUBSET_INTERIOR THEN
      ASM_MESON_TAC[LE_REFL]];
    SUBGOAL_THEN `s = IMAGE (g:real^N->real^M) t` SUBST1_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMAGE_SUBSET_INTERIOR THEN
      ASM_MESON_TAC[LE_REFL]];
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTERIOR_SUBSET];
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTERIOR_SUBSET]]);;

let HOMEOMORPHIC_INTERIORS = prove
 (`!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\ (interior s = {} <=> interior t = {})
        ==> (interior s) homeomorphic (interior t)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `interior t:real^N->bool = {}` THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_EMPTY] THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMEOMORPHIC_INTERIORS_SAME_DIMENSION THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM
   (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MINIMAL]) THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THEN
  MATCH_MP_TAC INVARIANCE_OF_DIMENSION THENL
   [MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `interior s:real^M->bool`];
    MAP_EVERY EXISTS_TAC [`g:real^N->real^M`; `interior t:real^N->bool`]] THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTERIOR_SUBSET; SUBSET]);;

let HOMEOMORPHIC_FRONTIERS_SAME_DIMENSION = prove
 (`!s:real^M->bool t:real^N->bool.
        dimindex(:M) = dimindex(:N) /\
        s homeomorphic t /\ closed s /\ closed t
        ==> (frontier s) homeomorphic (frontier t)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MINIMAL]) THEN
  REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^M->real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^M` THEN
  ASM_SIMP_TAC[REWRITE_RULE[SUBSET] FRONTIER_SUBSET_CLOSED] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[FRONTIER_SUBSET_CLOSED; CONTINUOUS_ON_SUBSET]] THEN
  ASM_SIMP_TAC[frontier; CLOSURE_CLOSED] THEN
  SUBGOAL_THEN
   `(!x:real^M. x IN interior s ==> f x IN interior t) /\
    (!y:real^N. y IN interior t ==> g y IN interior s)`
  MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[SET_RULE `(!x. x IN s ==> f x IN t) <=> IMAGE f s SUBSET t`] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `t = IMAGE (f:real^M->real^N) s` SUBST1_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMAGE_SUBSET_INTERIOR THEN
      ASM_MESON_TAC[LE_REFL]];
    SUBGOAL_THEN `s = IMAGE (g:real^N->real^M) t` SUBST1_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMAGE_SUBSET_INTERIOR THEN
      ASM_MESON_TAC[LE_REFL]]]);;

let HOMEOMORPHIC_FRONTIERS = prove
 (`!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\ closed s /\ closed t /\
        (interior s = {} <=> interior t = {})
        ==> (frontier s) homeomorphic (frontier t)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `interior t:real^N->bool = {}` THENL
   [ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; DIFF_EMPTY]; STRIP_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHIC_FRONTIERS_SAME_DIMENSION THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM
   (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MINIMAL]) THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THEN
  MATCH_MP_TAC INVARIANCE_OF_DIMENSION THENL
   [MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `interior s:real^M->bool`];
    MAP_EVERY EXISTS_TAC [`g:real^N->real^M`; `interior t:real^N->bool`]] THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTERIOR_SUBSET; SUBSET]);;

let CONTINUOUS_IMAGE_SUBSET_RELATIVE_INTERIOR = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ aff_dim t <= aff_dim s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> IMAGE f (relative_interior s) SUBSET relative_interior(IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RELATIVE_INTERIOR_MAXIMAL THEN
  SIMP_TAC[IMAGE_SUBSET; RELATIVE_INTERIOR_SUBSET] THEN
  MATCH_MP_TAC INVARIANCE_OF_DOMAIN_AFFINE_SETS THEN
  EXISTS_TAC `affine hull s:real^M->bool` THEN
  ASM_REWRITE_TAC[AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL] THEN
  REWRITE_TAC[OPEN_IN_RELATIVE_INTERIOR] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SUBSET; INT_LE_TRANS]; ALL_TAC] THEN
  ASSUME_TAC(ISPEC `s:real^M->bool` RELATIVE_INTERIOR_SUBSET) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) s` THEN
  SIMP_TAC[IMAGE_SUBSET; RELATIVE_INTERIOR_SUBSET; HULL_SUBSET]);;

let HOMEOMORPHIC_RELATIVE_INTERIORS_SAME_DIMENSION = prove
 (`!s:real^M->bool t:real^N->bool.
        aff_dim s = aff_dim t /\ s homeomorphic t
        ==> (relative_interior s) homeomorphic (relative_interior t)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MINIMAL]) THEN
  REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^M->real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^M` THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET] THEN
  REWRITE_TAC[SET_RULE `(!x. x IN s ==> f x IN t) <=> IMAGE f s SUBSET t`] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `t = IMAGE (f:real^M->real^N) s` SUBST1_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMAGE_SUBSET_RELATIVE_INTERIOR THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[INT_LE_REFL] THEN
      ASM SET_TAC[]];
    SUBGOAL_THEN `s = IMAGE (g:real^N->real^M) t` SUBST1_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMAGE_SUBSET_RELATIVE_INTERIOR THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[INT_LE_REFL] THEN
      ASM SET_TAC[]];
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; RELATIVE_INTERIOR_SUBSET];
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; RELATIVE_INTERIOR_SUBSET]]);;

let HOMEOMORPHIC_RELATIVE_INTERIORS = prove
 (`!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\
        (relative_interior s = {} <=> relative_interior t = {})
        ==> (relative_interior s) homeomorphic (relative_interior t)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `relative_interior t:real^N->bool = {}` THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_EMPTY] THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_INTERIORS_SAME_DIMENSION THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM
   (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MINIMAL]) THEN
  ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THEN
  MATCH_MP_TAC INVARIANCE_OF_DIMENSION_AFFINE_SETS THENL
   [MAP_EVERY EXISTS_TAC
     [`f:real^M->real^N`; `relative_interior s:real^M->bool`];
    MAP_EVERY EXISTS_TAC
     [`g:real^N->real^M`; `relative_interior t:real^N->bool`]] THEN
  ASM_REWRITE_TAC[OPEN_IN_RELATIVE_INTERIOR; AFFINE_AFFINE_HULL] THEN
  (REPEAT CONJ_TAC THENL
    [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; RELATIVE_INTERIOR_SUBSET];
     ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; HULL_SUBSET; SET_RULE
      `(!x. x IN s ==> f x IN t) /\ s' SUBSET s /\ t SUBSET t'
       ==> IMAGE f s' SUBSET t'`];
     ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]]));;

let HOMEOMORPHIC_RELATIVE_BOUNDARIES_SAME_DIMENSION = prove
 (`!s:real^M->bool t:real^N->bool.
        aff_dim s = aff_dim t /\ s homeomorphic t
        ==> (s DIFF relative_interior s) homeomorphic
            (t DIFF relative_interior t)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MINIMAL]) THEN
  REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^M->real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^M` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[IN_DIFF] THEN
  ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[SUBSET_DIFF; CONTINUOUS_ON_SUBSET]] THEN
  SUBGOAL_THEN
   `(!x:real^M. x IN relative_interior s ==> f x IN relative_interior t) /\
    (!y:real^N. y IN relative_interior t ==> g y IN relative_interior s)`
  MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[SET_RULE `(!x. x IN s ==> f x IN t) <=> IMAGE f s SUBSET t`] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `t = IMAGE (f:real^M->real^N) s` SUBST1_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMAGE_SUBSET_RELATIVE_INTERIOR THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[INT_LE_REFL] THEN
      ASM SET_TAC[]];
    SUBGOAL_THEN `s = IMAGE (g:real^N->real^M) t` SUBST1_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMAGE_SUBSET_RELATIVE_INTERIOR THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[INT_LE_REFL] THEN
      ASM SET_TAC[]]]);;

let HOMEOMORPHIC_RELATIVE_BOUNDARIES = prove
 (`!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\
        (relative_interior s = {} <=> relative_interior t = {})
        ==> (s DIFF relative_interior s) homeomorphic
            (t DIFF relative_interior t)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `relative_interior t:real^N->bool = {}` THEN
  ASM_SIMP_TAC[DIFF_EMPTY] THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_BOUNDARIES_SAME_DIMENSION THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM
   (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MINIMAL]) THEN
  ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THEN
  MATCH_MP_TAC INVARIANCE_OF_DIMENSION_AFFINE_SETS THENL
   [MAP_EVERY EXISTS_TAC
     [`f:real^M->real^N`; `relative_interior s:real^M->bool`];
    MAP_EVERY EXISTS_TAC
     [`g:real^N->real^M`; `relative_interior t:real^N->bool`]] THEN
  ASM_REWRITE_TAC[OPEN_IN_RELATIVE_INTERIOR; AFFINE_AFFINE_HULL] THEN
  (REPEAT CONJ_TAC THENL
    [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; RELATIVE_INTERIOR_SUBSET];
     ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; HULL_SUBSET; SET_RULE
      `(!x. x IN s ==> f x IN t) /\ s' SUBSET s /\ t SUBSET t'
       ==> IMAGE f s' SUBSET t'`];
     ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]]));;

let UNIFORMLY_CONTINUOUS_HOMEOMORPHISM_UNIV_TRIVIAL = prove
 (`!f g s:real^N->bool.
        homeomorphism (s,(:real^N)) (f,g) /\ f uniformly_continuous_on s
        ==> s = (:real^N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism; IN_UNIV] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THENL [SET_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPEC `s:real^N->bool` CLOPEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM COMPLETE_EQ_CLOSED; complete] THEN
    X_GEN_TAC `x:num->real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `cauchy ((f:real^N->real^N) o x)` MP_TAC THENL
     [ASM_MESON_TAC[UNIFORMLY_CONTINUOUS_IMP_CAUCHY_CONTINUOUS]; ALL_TAC] THEN
    REWRITE_TAC[GSYM CONVERGENT_EQ_CAUCHY] THEN
    DISCH_THEN(X_CHOOSE_TAC `l:real^N`) THEN
    EXISTS_TAC `(g:real^N->real^N) l` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `(g:real^N->real^N) o (f:real^N->real^N) o (x:num->real^N)` THEN
    REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN ASM SET_TAC[];
      MATCH_MP_TAC LIM_CONTINUOUS_FUNCTION THEN ASM_SIMP_TAC[GSYM o_DEF] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]];
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN
    ASM_REWRITE_TAC[OPEN_UNIV] THEN ASM SET_TAC[]]);;

let INVARIANCE_OF_DOMAIN_SPHERE_AFFINE_SET_GEN = prove
 (`!f:real^M->real^N u s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        bounded u /\ convex u /\ affine t /\ aff_dim t < aff_dim u /\
        open_in (subtopology euclidean (relative_frontier u)) s
        ==> open_in (subtopology euclidean t) (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `relative_frontier u:real^M->bool = {}` THEN
  ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_EMPTY; IMAGE_CLAUSES; OPEN_IN_EMPTY] THEN
  STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  SUBGOAL_THEN
   `?b c:real^M. b IN relative_frontier u /\ c IN relative_frontier u /\
                 ~(b = c)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `~(s = {} \/ ?x. s = {x}) ==> ?a b. a IN s /\ b IN s /\ ~(a = b)`) THEN
    ASM_MESON_TAC[RELATIVE_FRONTIER_NOT_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^M)`; `aff_dim(u:real^M->bool) - &1`]
        CHOOSE_AFFINE_SUBSET) THEN
  REWRITE_TAC[SUBSET_UNIV; AFFINE_UNIV] THEN ANTS_TAC THENL
   [MATCH_MP_TAC(INT_ARITH
     `&0:int <= t /\ t <= n ==> --a <= t - a /\ t - &1 <= n`) THEN
    REWRITE_TAC[AFF_DIM_LE_UNIV; AFF_DIM_UNIV; AFF_DIM_POS_LE] THEN
    ASM_MESON_TAC[RELATIVE_FRONTIER_EMPTY; NOT_IN_EMPTY];
    DISCH_THEN(X_CHOOSE_THEN `af:real^M->bool` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`u:real^M->bool`; `af:real^M->bool`]
        HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN) THEN
  ASM_REWRITE_TAC[INT_ARITH `x - a + a:int = x`] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `c:real^M` th) THEN MP_TAC(SPEC `b:real^M` th)) THEN
  ASM_REWRITE_TAC[homeomorphic; homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:real^M->real^M`; `h:real^M->real^M`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`j:real^M->real^M`; `k:real^M->real^M`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`(f:real^M->real^N) o (k:real^M->real^M)`;
    `(af:real^M->bool)`;
    `t:real^N->bool`; `IMAGE (j:real^M->real^M) (s DELETE c)`]
   INVARIANCE_OF_DOMAIN_AFFINE_SETS) THEN
  MP_TAC(ISPECL
   [`(f:real^M->real^N) o (h:real^M->real^M)`;
    `(af:real^M->bool)`;
    `t:real^N->bool`; `IMAGE (g:real^M->real^M) (s DELETE b)`]
   INVARIANCE_OF_DOMAIN_AFFINE_SETS) THEN
  ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[IMP_IMP; INT_ARITH `x:int <= y - &1 <=> x < y`] THEN
  MATCH_MP_TAC(TAUT
   `(p1 /\ p2) /\ (q1 /\ q2 ==> r) ==> (p1 ==> q1) /\ (p2 ==> q2) ==> r`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_DELETE]) THEN
    ASM_SIMP_TAC[o_THM; IN_DELETE; IMP_CONJ] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN MAP_EVERY EXISTS_TAC
     [`h:real^M->real^M`; `relative_frontier u DELETE (b:real^M)`] THEN
    ASM_SIMP_TAC[homeomorphism; DOT_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; OPEN_IN_OPEN] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    ASM SET_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_DELETE]) THEN
    ASM_SIMP_TAC[o_THM; IN_DELETE; IMP_CONJ] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN MAP_EVERY EXISTS_TAC
     [`k:real^M->real^M`; `relative_frontier u DELETE (c:real^M)`] THEN
    ASM_SIMP_TAC[homeomorphism; DOT_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; OPEN_IN_OPEN] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_UNION) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (f:real^M->real^N)
                      ((s DELETE b) UNION (s DELETE c))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IMAGE_UNION] THEN BINOP_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN ASM SET_TAC[]]);;

let INVARIANCE_OF_DOMAIN_SPHERE_AFFINE_SET = prove
 (`!f:real^M->real^N a r s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        ~(r = &0) /\ affine t /\ aff_dim t < &(dimindex(:M)) /\
        open_in (subtopology euclidean (sphere(a,r))) s
        ==> open_in (subtopology euclidean t) (IMAGE f s)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `sphere(a:real^M,r) = {}` THEN
  ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_EMPTY; OPEN_IN_EMPTY; IMAGE_CLAUSES] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPHERE_EQ_EMPTY; REAL_NOT_LT]) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `cball(a:real^M,r)`;
                 `s:real^M->bool`; `t:real^N->bool`]
        INVARIANCE_OF_DOMAIN_SPHERE_AFFINE_SET_GEN) THEN
  ASM_REWRITE_TAC[AFF_DIM_CBALL; RELATIVE_FRONTIER_CBALL;
                  BOUNDED_CBALL; CONVEX_CBALL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let NO_EMBEDDING_SPHERE_LOWDIM = prove
 (`!f:real^M->real^N a r.
        &0 < r /\
        f continuous_on sphere(a,r) /\
        (!x y. x IN sphere(a,r) /\ y IN sphere(a,r) /\ f x = f y ==> x = y)
        ==> dimindex(:M) <= dimindex(:N)`,
  REWRITE_TAC[GSYM NOT_LT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (f:real^M->real^N) (sphere(a:real^M,r))`
        COMPACT_OPEN) THEN
  ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; IMAGE_EQ_EMPTY;
               COMPACT_SPHERE; SPHERE_EQ_EMPTY;
               REAL_ARITH `&0 < r ==> ~(r < &0)`] THEN
  ONCE_REWRITE_TAC[OPEN_IN] THEN
  ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
  MATCH_MP_TAC INVARIANCE_OF_DOMAIN_SPHERE_AFFINE_SET THEN
  MAP_EVERY EXISTS_TAC [`a:real^M`; `r:real`] THEN
  ASM_REWRITE_TAC[AFFINE_UNIV; SUBSET_UNIV; AFF_DIM_UNIV;
                  OPEN_IN_REFL; INT_OF_NUM_LT] THEN
  ASM_REAL_ARITH_TAC);;

let EMPTY_INTERIOR_LOWDIM_GEN = prove
 (`!s:real^N->bool t:real^M->bool.
        dimindex(:M) < dimindex(:N) /\ s homeomorphic t ==> interior s = {}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^M)`; `(:real^N)`] ISOMETRY_SUBSET_SUBSPACE) THEN
  ASM_SIMP_TAC[SUBSPACE_UNIV; DIM_UNIV; LT_IMP_LE; IN_UNIV; SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(MESON[HOMEOMORPHIC_EMPTY]
   `!t. interior(t:real^N->bool) homeomorphic interior(s:real^N->bool) /\
        interior t = {}
        ==> interior s = {}`) THEN
  EXISTS_TAC `IMAGE (h:real^M->real^N) t` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_INTERIORS_SAME_DIMENSION THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_SYM]) THEN
    MATCH_MP_TAC EQ_IMP THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_LEFT_EQ THEN
    ASM_MESON_TAC[PRESERVES_NORM_INJECTIVE];
    MATCH_MP_TAC(SET_RULE `!t. s SUBSET t /\ t = {} ==> s = {}`) THEN
    EXISTS_TAC `interior(IMAGE (h:real^M->real^N) (:real^M))` THEN
    SIMP_TAC[SUBSET_INTERIOR; SET_RULE `IMAGE f s SUBSET IMAGE f UNIV`] THEN
    MATCH_MP_TAC EMPTY_INTERIOR_LOWDIM THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        LET_TRANS)) THEN
    REWRITE_TAC[GSYM DIM_UNIV] THEN
    MATCH_MP_TAC EQ_IMP_LE THEN MATCH_MP_TAC DIM_INJECTIVE_LINEAR_IMAGE THEN
    ASM_MESON_TAC[PRESERVES_NORM_INJECTIVE]]);;

let EMPTY_INTERIOR_LOWDIM_GEN_LE = prove
 (`!s:real^N->bool t:real^M->bool.
        dimindex(:M) <= dimindex(:N) /\
        interior t = {} /\
        s homeomorphic t
        ==> interior s = {}`,
  REWRITE_TAC[LE_LT] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[EMPTY_INTERIOR_LOWDIM_GEN];
    ASM_MESON_TAC[HOMEOMORPHIC_INTERIORS_SAME_DIMENSION;
                  HOMEOMORPHIC_EMPTY]]);;

(* ------------------------------------------------------------------------- *)
(* Dimension-based conditions for various homeomorphisms.                    *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_SUBSPACES_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t ==> (s homeomorphic t <=> dim s = dim t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[HOMEOMORPHIC_SUBSPACES]] THEN
  REWRITE_TAC[homeomorphic; HOMEOMORPHISM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_INJECTIVE_IMAGE_SUBSPACE_DIM_LE THEN
  ASM_MESON_TAC[]);;

let HOMEOMORPHIC_AFFINE_SETS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        affine s /\ affine t ==> (s homeomorphic t <=> aff_dim s = aff_dim t)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_EQ_MINUS1; HOMEOMORPHIC_EMPTY] THEN
  POP_ASSUM MP_TAC THEN
  GEN_REWRITE_TAC (funpow 3 RAND_CONV) [EQ_SYM_EQ] THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_SIMP_TAC[AFF_DIM_EMPTY; AFF_DIM_EQ_MINUS1; HOMEOMORPHIC_EMPTY] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC
   [GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM; RIGHT_IMP_FORALL_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^N`] THEN
  GEOM_ORIGIN_TAC `a:real^M` THEN GEOM_ORIGIN_TAC `b:real^N` THEN
  SIMP_TAC[AFFINE_EQ_SUBSPACE; HOMEOMORPHIC_SUBSPACES_EQ; AFF_DIM_DIM_0;
           HULL_INC; INT_OF_NUM_EQ] THEN
  MESON_TAC[]);;

let HOMEOMORPHIC_HYPERPLANES_EQ = prove
 (`!a:real^M b c:real^N d.
        ~(a = vec 0) /\ ~(c = vec 0)
        ==> ({x | a dot x = b} homeomorphic {x | c dot x = d} <=>
             dimindex(:M) = dimindex(:N))`,
  SIMP_TAC[HOMEOMORPHIC_AFFINE_SETS_EQ; AFFINE_HYPERPLANE] THEN
  SIMP_TAC[AFF_DIM_HYPERPLANE; INT_OF_NUM_EQ;
          INT_ARITH `x - &1:int = y - &1 <=> x = y`]);;

let HOMEOMORPHIC_UNIV_UNIV = prove
 (`(:real^M) homeomorphic (:real^N) <=> dimindex(:M) = dimindex(:N)`,
  SIMP_TAC[HOMEOMORPHIC_SUBSPACES_EQ; DIM_UNIV; SUBSPACE_UNIV]);;

let HOMEOMORPHIC_CBALLS_EQ = prove
 (`!a:real^M b:real^N r s.
        cball(a,r) homeomorphic cball(b,s) <=>
        r < &0 /\ s < &0 \/ r = &0 /\ s = &0 \/
        &0 < r /\ &0 < s /\ dimindex(:M) = dimindex(:N)`,
  let lemma =
    let d = `dimindex(:M) = dimindex(:N)`
    and t = `?a:real^M b:real^N. ~(cball(a,r) homeomorphic cball(b,s))` in
    DISCH d (DISCH t (GEOM_EQUAL_DIMENSION_RULE (ASSUME d) (ASSUME t))) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r < &0` THENL
   [ASM_SIMP_TAC[CBALL_EMPTY; HOMEOMORPHIC_EMPTY; CBALL_EQ_EMPTY] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `r = &0` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THENL
   [ASM_SIMP_TAC[CBALL_TRIVIAL; FINITE_SING; HOMEOMORPHIC_FINITE_STRONG] THEN
    REWRITE_TAC[FINITE_CBALL] THEN
    ASM_CASES_TAC `s < &0` THEN
    ASM_SIMP_TAC[CBALL_EMPTY; CARD_CLAUSES; FINITE_EMPTY;
                 NOT_IN_EMPTY; ARITH; REAL_LT_IMP_NE] THEN
    ASM_CASES_TAC `s = &0` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC[CBALL_TRIVIAL; CARD_CLAUSES; FINITE_EMPTY; NOT_IN_EMPTY;
                 REAL_LE_REFL; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `s <= &0` THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_FINITE_STRONG; FINITE_CBALL] THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [REWRITE_TAC[homeomorphic; HOMEOMORPHISM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
    STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THEN
    MATCH_MP_TAC INVARIANCE_OF_DIMENSION THENL
     [MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `ball(a:real^M,r)`] THEN
      MP_TAC(ISPECL [`a:real^M`; `r:real`] BALL_SUBSET_CBALL);
      MAP_EVERY EXISTS_TAC [`g:real^N->real^M`; `ball(b:real^N,s)`] THEN
      MP_TAC(ISPECL [`b:real^N`; `s:real`] BALL_SUBSET_CBALL)] THEN
    ASM_REWRITE_TAC[BALL_EQ_EMPTY; OPEN_BALL; REAL_NOT_LE] THEN
    ASM_MESON_TAC[SUBSET; CONTINUOUS_ON_SUBSET];
    DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN ASM_SIMP_TAC[HOMEOMORPHIC_CBALLS]]);;

let HOMEOMORPHIC_BALLS_EQ = prove
 (`!a:real^M b:real^N r s.
        ball(a,r) homeomorphic ball(b,s) <=>
        r <= &0 /\ s <= &0 \/
        &0 < r /\ &0 < s /\ dimindex(:M) = dimindex(:N)`,
  let lemma =
    let d = `dimindex(:M) = dimindex(:N)`
    and t = `?a:real^M b:real^N. ~(ball(a,r) homeomorphic ball(b,s))` in
    DISCH d (DISCH t (GEOM_EQUAL_DIMENSION_RULE (ASSUME d) (ASSUME t))) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r <= &0` THENL
   [ASM_SIMP_TAC[BALL_EMPTY; HOMEOMORPHIC_EMPTY; BALL_EQ_EMPTY] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s <= &0` THENL
   [ASM_SIMP_TAC[BALL_EMPTY; HOMEOMORPHIC_EMPTY; BALL_EQ_EMPTY] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [REWRITE_TAC[homeomorphic; HOMEOMORPHISM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
    STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THEN
    MATCH_MP_TAC INVARIANCE_OF_DIMENSION THENL
     [MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `ball(a:real^M,r)`];
      MAP_EVERY EXISTS_TAC [`g:real^N->real^M`; `ball(b:real^N,s)`]] THEN
    ASM_REWRITE_TAC[BALL_EQ_EMPTY; OPEN_BALL; REAL_NOT_LE] THEN
    ASM SET_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN ASM_SIMP_TAC[HOMEOMORPHIC_BALLS]]);;

let SIMPLY_CONNECTED_SPHERE_EQ = prove
 (`!a:real^N r.
        simply_connected(sphere(a,r)) <=> 3 <= dimindex(:N) \/ r <= &0`,
  let hslemma = prove
   (`!a:real^M r b:real^N s.
        dimindex(:M) = dimindex(:N)
        ==> &0 < r /\ &0 < s  ==> (sphere(a,r) homeomorphic sphere(b,s))`,
    REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th ->
      let t = `?a:real^M b:real^N. ~(sphere(a,r) homeomorphic sphere(b,s))` in
      MP_TAC(DISCH t (GEOM_EQUAL_DIMENSION_RULE th (ASSUME t)))) THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_SPHERES] THEN MESON_TAC[]) in
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[SPHERE_EMPTY; REAL_LT_IMP_LE; SIMPLY_CONNECTED_EMPTY] THEN
  ASM_CASES_TAC `r = &0` THEN
  ASM_SIMP_TAC[SPHERE_SING; REAL_LE_REFL; CONVEX_IMP_SIMPLY_CONNECTED;
               CONVEX_SING] THEN
  ASM_REWRITE_TAC[REAL_LE_LT] THEN
  EQ_TAC THEN REWRITE_TAC[SIMPLY_CONNECTED_SPHERE] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[ARITH_RULE `~(3 <= n) <=> (1 <= n ==> n = 1 \/ n = 2)`] THEN
  REWRITE_TAC[DIMINDEX_GE_1] THEN STRIP_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP SIMPLY_CONNECTED_IMP_CONNECTED) THEN
    ASM_REWRITE_TAC[CONNECTED_SPHERE_EQ; ARITH] THEN ASM_REAL_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM DIMINDEX_2]) THEN
    FIRST_ASSUM(MP_TAC o ISPECL [`a:real^N`; `r:real`; `vec 0:real^2`;
          `&1:real`] o MATCH_MP hslemma) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP HOMEOMORPHIC_SIMPLY_CONNECTED_EQ) THEN
    REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_CIRCLEMAP] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `\x:real^2. x`) THEN
    REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID; SUBSET_REFL] THEN
    REWRITE_TAC[GSYM contractible; CONTRACTIBLE_SPHERE] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let SIMPLY_CONNECTED_PUNCTURED_UNIVERSE_EQ = prove
 (`!a. simply_connected((:real^N) DELETE a) <=> 3 <= dimindex(:N)`,
  GEN_TAC THEN TRANS_TAC EQ_TRANS `simply_connected(sphere(a:real^N,&1))` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SIMPLY_CONNECTED_SPHERE_EQ]] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  MATCH_MP_TAC HOMOTOPY_EQUIVALENT_SIMPLE_CONNECTEDNESS THEN
  MP_TAC(ISPECL [`cball(a:real^N,&1)`; `a:real^N`]
        HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_AFFINE_HULL) THEN
  REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; RELATIVE_INTERIOR_CBALL;
              RELATIVE_FRONTIER_CBALL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[CENTRE_IN_BALL; AFFINE_HULL_NONEMPTY_INTERIOR; INTERIOR_CBALL;
           BALL_EQ_EMPTY; REAL_OF_NUM_LE; ARITH; REAL_LT_01]);;

let NOT_SIMPLY_CONNECTED_CIRCLE = prove
 (`!a:real^2 r. &0 < r ==> ~simply_connected(sphere(a,r))`,
  REWRITE_TAC[SIMPLY_CONNECTED_SPHERE_EQ; DIMINDEX_2; ARITH] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The exponential function as a covering map.                               *)
(* ------------------------------------------------------------------------- *)

let COVERING_SPACE_CEXP_PUNCTURED_PLANE = prove
 (`covering_space((:complex),cexp) ((:complex) DIFF {Cx(&0)})`,
  SIMP_TAC[covering_space; IN_UNIV; CONTINUOUS_ON_CEXP; IN_DIFF; IN_SING] THEN
  CONJ_TAC THENL [SET_TAC[CEXP_CLOG; CEXP_NZ]; ALL_TAC] THEN
  SIMP_TAC[OPEN_IN_OPEN_EQ; OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN
  SIMP_TAC[SUBSET_UNIV; SET_RULE `s SUBSET UNIV DIFF {a} <=> ~(a IN s)`] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  EXISTS_TAC `IMAGE cexp (ball(clog z,&1))` THEN
  REWRITE_TAC[SET_RULE `~(z IN IMAGE f s) <=> !x. x IN s ==> ~(f x = z)`] THEN
  REWRITE_TAC[CEXP_NZ] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `clog z` THEN
    ASM_SIMP_TAC[CEXP_CLOG; CENTRE_IN_BALL; REAL_LT_01];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN cball(clog z,&1) /\ y IN cball(clog z,&1) /\ cexp x = cexp y
          ==> x = y`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COMPLEX_EQ_CEXP THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(x - y:complex)` THEN
    REWRITE_TAC[GSYM IM_SUB; COMPLEX_NORM_GE_RE_IM] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2` THEN CONJ_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC NORM_ARITH;
      MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN
    REWRITE_TAC[OPEN_BALL; CONTINUOUS_ON_CEXP] THEN
    ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cball(clog z,&1)`; `cexp`;
                 `IMAGE cexp (cball(clog z,&1))`] HOMEOMORPHISM_COMPACT) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL; CONTINUOUS_ON_CEXP] THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `l:complex->complex` THEN STRIP_TAC THEN
  EXISTS_TAC `{ IMAGE (\x. x + Cx (&2 * n * pi) * ii)
                      (ball(clog z,&1))
                | integer n}` THEN
  SIMP_TAC[FORALL_IN_GSPEC; OPEN_BALL;
           ONCE_REWRITE_RULE[VECTOR_ADD_SYM] OPEN_TRANSLATION] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC; IN_IMAGE; CEXP_EQ] THEN SET_TAC[];
    REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `m:real` THEN DISCH_TAC THEN
    X_GEN_TAC `n:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `m:real = n` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_BALL; dist; SET_RULE
     `DISJOINT (IMAGE f s) (IMAGE g s) <=>
      !x y. x IN s /\ y IN s ==> ~(f x = g y)`] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC(NORM_ARITH
     `&2 <= norm(m - n)
      ==> norm(c - x) < &1 /\ norm(c - y) < &1 ==> ~(x + m = y + n)`) THEN
    REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB; COMPLEX_NORM_MUL] THEN
    REWRITE_TAC[COMPLEX_NORM_II; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_PI; REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * &1 * pi` THEN
    CONJ_TAC THENL [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    SIMP_TAC[REAL_LE_RMUL_EQ; PI_POS; REAL_POS] THEN
    MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN
    ASM_SIMP_TAC[REAL_SUB_0; INTEGER_CLOSED];
    X_GEN_TAC `n:real` THEN DISCH_TAC THEN
    EXISTS_TAC `(\x. x + Cx(&2 * n * pi) * ii) o (l:complex->complex)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_CEXP; o_THM; IMAGE_o; FORALL_IN_IMAGE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INJECTIVE_ON_ALT]) THEN
    ASM_SIMP_TAC[CEXP_ADD; CEXP_INTEGER_2PI; COMPLEX_MUL_RID;
                 REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x. e(f x) = e x) ==> IMAGE e (IMAGE f s) = IMAGE e s`) THEN
      ASM_SIMP_TAC[CEXP_ADD; CEXP_INTEGER_2PI; COMPLEX_MUL_RID];
      MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> l(e x) = x)
        ==> IMAGE t (IMAGE l (IMAGE e s)) = IMAGE t s`) THEN
      ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL];
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_ID;
               CONTINUOUS_ON_CONST] THEN
      ASM_MESON_TAC[BALL_SUBSET_CBALL; IMAGE_SUBSET;
                    CONTINUOUS_ON_SUBSET]]]);;

(* ------------------------------------------------------------------------- *)
(* Hence the Borsukian results about mappings into circle.                   *)
(* ------------------------------------------------------------------------- *)

let INESSENTIAL_EQ_CONTINUOUS_LOGARITHM = prove
 (`!f:real^N->complex s.
      (?a. homotopic_with (\h. T)
             (subtopology euclidean s,
              subtopology euclidean ((:complex) DIFF {Cx(&0)})) f (\t. a)) <=>
      (?g. g continuous_on s /\ (!x. x IN s ==> f x = cexp(g x)))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN
     (MP_TAC o CONJ COVERING_SPACE_CEXP_PUNCTURED_PLANE)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP COVERING_SPACE_LIFT_INESSENTIAL_FUNCTION) THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->complex` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?a. homotopic_with (\h. T)
              (subtopology euclidean s,
               subtopology euclidean ((:complex) DIFF {Cx(&0)}))
              (cexp o g) (\x:real^N. a)`
    MP_TAC THENL
     [MATCH_MP_TAC NULLHOMOTOPIC_THROUGH_CONTRACTIBLE THEN
      EXISTS_TAC `(:complex)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
      ASM_SIMP_TAC[STARLIKE_IMP_CONTRACTIBLE; STARLIKE_UNIV] THEN
      REWRITE_TAC[CONTINUOUS_ON_CEXP; SUBSET; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[IN_UNIV; IN_DIFF; IN_SING; CEXP_NZ];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:complex` THEN
      MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
      ASM_SIMP_TAC[o_THM]]]);;

let INESSENTIAL_IMP_CONTINUOUS_LOGARITHM_CIRCLE = prove
 (`!f:real^N->complex s.
        (?a. homotopic_with (\h. T)
              (subtopology euclidean s,
               subtopology euclidean (sphere(vec 0,&1))) f (\t. a))
        ==> ?g. g continuous_on s /\ !x. x IN s ==> f x = cexp(g x)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[sphere; GSYM INESSENTIAL_EQ_CONTINUOUS_LOGARITHM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:complex` THEN
  REWRITE_TAC[HOMOTOPIC_WITH_EUCLIDEAN] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
  SIMP_TAC[SUBSET; DIST_0; FORALL_IN_GSPEC; IN_UNIV; IN_DIFF; IN_SING] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  SIMP_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC);;

let INESSENTIAL_EQ_CONTINUOUS_LOGARITHM_CIRCLE = prove
 (`!f:real^N->complex s.
        (?a. homotopic_with (\h. T)
              (subtopology euclidean s,
               subtopology euclidean (sphere(vec 0,&1))) f (\t. a)) <=>
        (?g. (Cx o g) continuous_on s /\
             !x. x IN s ==> f x = cexp(ii * Cx(g x)))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN FIRST_ASSUM(MP_TAC o
      MATCH_MP INESSENTIAL_IMP_CONTINUOUS_LOGARITHM_CIRCLE) THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->complex` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `Im o (g:real^N->complex)` THEN CONJ_TAC THENL
     [REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_CX_IM];
      FIRST_X_ASSUM(CHOOSE_THEN (MP_TAC o CONJUNCT1 o
        MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET)) THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; NORM_CEXP] THEN
      REWRITE_TAC[EULER; o_THM; RE_MUL_II; IM_MUL_II] THEN
      SIMP_TAC[RE_CX; IM_CX; REAL_NEG_0; REAL_EXP_0]];
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?a. homotopic_with (\h. T)
            (subtopology euclidean s,
             subtopology euclidean (sphere(vec 0,&1)))
             ((cexp o (\z. ii * z)) o (Cx o g)) (\x:real^N. a)`
    MP_TAC THENL
     [MATCH_MP_TAC NULLHOMOTOPIC_THROUGH_CONTRACTIBLE THEN
      EXISTS_TAC `{z | Im z = &0}` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_COMPOSE; CONTINUOUS_ON_CEXP; CONJ_ASSOC;
                   CONTINUOUS_ON_COMPLEX_LMUL; CONTINUOUS_ON_ID] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_SPHERE_0;
                    o_THM; IM_CX] THEN
        SIMP_TAC[NORM_CEXP; RE_MUL_II; REAL_EXP_0; REAL_NEG_0];
        MATCH_MP_TAC STARLIKE_IMP_CONTRACTIBLE THEN
        MATCH_MP_TAC CONVEX_IMP_STARLIKE THEN CONJ_TAC THENL
         [REWRITE_TAC[IM_DEF; CONVEX_STANDARD_HYPERPLANE];
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
          MESON_TAC[IM_CX]]];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:complex` THEN
      MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
      ASM_SIMP_TAC[o_THM]]]);;

let HOMOTOPIC_CIRCLEMAPS_DIV,HOMOTOPIC_CIRCLEMAPS_DIV_1 = (CONJ_PAIR o prove)
 (`(!f g:real^N->real^2 s.
    homotopic_with (\x. T)
     (subtopology euclidean s,
      subtopology euclidean (sphere(vec 0,&1))) f g <=>
    f continuous_on s /\ IMAGE f s SUBSET sphere(vec 0,&1) /\
    g continuous_on s /\ IMAGE g s SUBSET sphere(vec 0,&1) /\
    ?c. homotopic_with (\x. T)
         (subtopology euclidean s,
          subtopology euclidean (sphere(vec 0,&1)))
         (\x. f x / g x) (\x. c)) /\
   (!f g:real^N->real^2 s.
    homotopic_with (\x. T)
     (subtopology euclidean s,
      subtopology euclidean (sphere(vec 0,&1))) f g <=>
    f continuous_on s /\ IMAGE f s SUBSET sphere(vec 0,&1) /\
    g continuous_on s /\ IMAGE g s SUBSET sphere(vec 0,&1) /\
    homotopic_with (\x. T)
     (subtopology euclidean s,
      subtopology euclidean (sphere(vec 0,&1)))
     (\x. f x / g x) (\x. Cx(&1)))`,
  let lemma = prove
   (`!f g h:real^N->real^2 s.
          homotopic_with (\x. T)
            (subtopology euclidean s,
             subtopology euclidean (sphere(vec 0,&1))) f g
          ==> h continuous_on s /\ (!x. x IN s ==> h(x) IN sphere(vec 0,&1))
               ==> homotopic_with (\x. T)
                    (subtopology euclidean s,
                     subtopology euclidean (sphere(vec 0,&1)))
                    (\x. f x * h x) (\x. g x * h x)`,
    REWRITE_TAC[IN_SPHERE_0] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMOTOPIC_WITH_EUCLIDEAN]) THEN
    ASM_SIMP_TAC[HOMOTOPIC_WITH_EUCLIDEAN_ALT; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; FORALL_IN_PCROSS] THEN
    X_GEN_TAC `k:real^((1,N)finite_sum)->real^2` THEN STRIP_TAC THEN
    EXISTS_TAC `\z. (k:real^(1,N)finite_sum->real^2) z * h(sndcart z)` THEN
    ASM_SIMP_TAC[COMPLEX_NORM_MUL; SNDCART_PASTECART; REAL_MUL_LID] THEN
    ASM_REWRITE_TAC[SNDCART_PASTECART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
    ASM_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; IMAGE_SNDCART_PCROSS] THEN
    ASM_REWRITE_TAC[UNIT_INTERVAL_NONEMPTY]) in
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC
   (TAUT `(q <=> r) /\ (p <=> r) ==> (p <=> q) /\ (p <=> r)`) THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`) THEN
           DISCH_TAC) THEN
    EQ_TAC THENL
     [ALL_TAC; DISCH_TAC THEN EXISTS_TAC `Cx(&1)` THEN ASM_MESON_TAC[]] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `c:complex` THEN
    DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET th) THEN
        MP_TAC th) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_TRANS) THEN
    REWRITE_TAC[HOMOTOPIC_CONSTANT_MAPS] THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`vec 0:real^2`; `&1`] PATH_CONNECTED_SPHERE) THEN
    REWRITE_TAC[DIMINDEX_2; LE_REFL; PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[IN_SPHERE_0; COMPLEX_NORM_CX; REAL_ABS_NUM]];
    EQ_TAC THEN STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP lemma) THENL
     [FIRST_ASSUM(STRIP_ASSUME_TAC o
         MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
      DISCH_THEN(MP_TAC o SPEC `\x. inv((g:real^N->complex) x)`);
      DISCH_THEN(MP_TAC o SPEC `g:real^N->complex`)] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0]) THEN
    ASM_SIMP_TAC[IN_SPHERE_0; COMPLEX_NORM_INV; REAL_INV_1] THEN
    ASM_SIMP_TAC[GSYM COMPLEX_NORM_ZERO; REAL_OF_NUM_EQ; ARITH_EQ;
                 CONTINUOUS_ON_COMPLEX_INV] THEN
    ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0; FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
     HOMOTOPIC_WITH_EQ) THEN
    ASM_SIMP_TAC[COMPLEX_DIV_RMUL; COMPLEX_MUL_LID; COMPLEX_MUL_RINV;
                 GSYM complex_div; COMPLEX_DIV_REFL;
                 GSYM COMPLEX_NORM_ZERO; REAL_OF_NUM_EQ; ARITH_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* In particular, complex logs exist on various "well-behaved" sets.         *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE = prove
 (`!f:real^N->complex s.
        f continuous_on s /\ contractible s /\
        (!x. x IN s ==> ~(f x = Cx(&0)))
        ==> ?g. g continuous_on s /\ !x. x IN s ==> f x = cexp(g x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM INESSENTIAL_EQ_CONTINUOUS_LOGARITHM] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NULLHOMOTOPIC_FROM_CONTRACTIBLE THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let CONTINUOUS_LOGARITHM_ON_SIMPLY_CONNECTED = prove
 (`!f:real^N->complex s.
        f continuous_on s /\ simply_connected s /\ locally path_connected s /\
        (!x. x IN s ==> ~(f x = Cx(&0)))
        ==> ?g. g continuous_on s /\ !x. x IN s ==> f x = cexp(g x)`,
  REPEAT STRIP_TAC THEN MP_TAC
  (ISPECL [`f:real^N->complex`; `s:real^N->bool`]
    (MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] COVERING_SPACE_LIFT)
        COVERING_SPACE_CEXP_PUNCTURED_PLANE)) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN ASM SET_TAC[]);;

let CONTINUOUS_LOGARITHM_ON_CBALL = prove
 (`!f:real^N->complex a r.
        f continuous_on cball(a,r) /\
        (!z. z IN cball(a,r) ==> ~(f z = Cx(&0)))
        ==> ?h. h continuous_on cball(a,r) /\
                !z. z IN cball(a,r) ==> f z = cexp(h z)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `cball(a:real^N,r) = {}` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_EMPTY; NOT_IN_EMPTY] THEN
  MATCH_MP_TAC CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC STARLIKE_IMP_CONTRACTIBLE THEN
  MATCH_MP_TAC CONVEX_IMP_STARLIKE THEN
  ASM_REWRITE_TAC[CONVEX_CBALL]);;

let CONTINUOUS_LOGARITHM_ON_BALL = prove
 (`!f:real^N->complex a r.
        f continuous_on ball(a,r) /\
        (!x. x IN ball(a,r) ==> ~(f x = Cx(&0)))
        ==> ?h. h continuous_on ball(a,r) /\
                !x. x IN ball(a,r) ==> f x = cexp(h x)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `ball(a:real^N,r) = {}` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_EMPTY; NOT_IN_EMPTY] THEN
  MATCH_MP_TAC CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC STARLIKE_IMP_CONTRACTIBLE THEN
  MATCH_MP_TAC CONVEX_IMP_STARLIKE THEN
  ASM_REWRITE_TAC[CONVEX_BALL]);;

let CONTINUOUS_SQRT_ON_CONTRACTIBLE = prove
 (`!f:real^N->complex s.
        f continuous_on s /\ contractible s /\
        (!x. x IN s ==> ~(f x = Cx(&0)))
        ==> ?g. g continuous_on s /\ !x. x IN s ==> f x = (g x) pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z:real^N. cexp(g z / Cx(&2))` THEN
  ASM_SIMP_TAC[GSYM CEXP_N; COMPLEX_RING `Cx(&2) * z / Cx(&2) = z`] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_CONST] THEN
  CONV_TAC COMPLEX_RING);;

let CONTINUOUS_SQRT_ON_SIMPLY_CONNECTED = prove
 (`!f:real^N->complex s.
        f continuous_on s /\ simply_connected s /\ locally path_connected s /\
        (!x. x IN s ==> ~(f x = Cx(&0)))
        ==> ?g. g continuous_on s /\ !x. x IN s ==> f x = (g x) pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_LOGARITHM_ON_SIMPLY_CONNECTED) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z:real^N. cexp(g z / Cx(&2))` THEN
  ASM_SIMP_TAC[GSYM CEXP_N; COMPLEX_RING `Cx(&2) * z / Cx(&2) = z`] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_CONST] THEN
  CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Analogously, holomorphic logarithms and square roots.                     *)
(* ------------------------------------------------------------------------- *)

let CONTRACTIBLE_IMP_HOLOMORPHIC_LOG,SIMPLY_CONNECTED_IMP_HOLOMORPHIC_LOG =
 (CONJ_PAIR o prove)
 (`(!s:complex->bool.
      contractible s
      ==> !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
              ==> ?g. g holomorphic_on s /\ !z. z IN s ==> f z = cexp(g z)) /\
   (!s:complex->bool.
      simply_connected s /\ locally path_connected s
      ==> !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
              ==> ?g. g holomorphic_on s /\ !z. z IN s ==> f z = cexp(g z))`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`f:complex->complex`; `s:complex->bool`]
        CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE);
    MP_TAC(ISPECL [`f:complex->complex`; `s:complex->bool`]
        CONTINUOUS_LOGARITHM_ON_SIMPLY_CONNECTED)] THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
 (MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:complex->complex` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `f holomorphic_on s` THEN
  REWRITE_TAC[holomorphic_on] THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `z:complex` THEN ASM_CASES_TAC `(z:complex) IN s` THEN
  ASM_REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':complex` MP_TAC) THEN
  DISCH_THEN(MP_TAC o
   ISPECL [`\x. (cexp(g x) - cexp(g z)) / (x - z)`; `&1`] o
   MATCH_MP (REWRITE_RULE [TAUT `p /\ q /\ r ==> s <=> r ==> p /\ q ==> s`]
    LIM_TRANSFORM_WITHIN)) THEN
  ASM_SIMP_TAC[REAL_LT_01] THEN
  DISCH_THEN(MP_TAC o
    SPECL [`\x:complex. if g x = g z then cexp(g z)
                        else (cexp(g x) - cexp(g z)) / (g x - g z)`;
           `cexp(g(z:complex))`] o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] LIM_COMPLEX_DIV)) THEN
  REWRITE_TAC[CEXP_NZ] THEN ANTS_TAC THENL
   [SUBGOAL_THEN
     `(\x. if g x = g z then cexp(g z)
           else (cexp(g x) - cexp(g(z:complex))) / (g x - g z)) =
      (\y. if y = g z then cexp(g z)
           else (cexp y - cexp(g z)) / (y - g z)) o g`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC LIM_COMPOSE_AT THEN
    EXISTS_TAC `(g:complex->complex) z` THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON];
      REWRITE_TAC[EVENTUALLY_TRUE];
      ONCE_REWRITE_TAC[LIM_AT_ZERO] THEN
      SIMP_TAC[COMPLEX_VEC_0; COMPLEX_ADD_SUB; COMPLEX_EQ_ADD_LCANCEL_0] THEN
      MP_TAC(SPEC `cexp(g(z:complex))` (MATCH_MP LIM_COMPLEX_LMUL
       LIM_CEXP_MINUS_1)) THEN REWRITE_TAC[COMPLEX_MUL_RID] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
      SIMP_TAC[EVENTUALLY_AT; GSYM DIST_NZ; CEXP_ADD] THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
      SIMPLE_COMPLEX_ARITH_TAC];
    DISCH_THEN(fun th ->
        EXISTS_TAC `f' / cexp(g(z:complex))` THEN MP_TAC th) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
        LIM_TRANSFORM_EVENTUALLY) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
    DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONTINUOUS_WITHIN; tendsto] THEN
    DISCH_THEN(MP_TAC o SPEC `&2 * pi`) THEN
    REWRITE_TAC[REAL_ARITH `&0 < &2 * x <=> &0 < x`; PI_POS] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `w:complex` THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
    COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_SUB_REFL; complex_div; COMPLEX_MUL_LZERO];
      ASM_CASES_TAC `w:complex = z` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~(cexp(g(w:complex)) = cexp(g z))` MP_TAC THENL
       [UNDISCH_TAC `~((g:complex->complex) w = g z)` THEN
        REWRITE_TAC[CONTRAPOS_THM] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] COMPLEX_EQ_CEXP) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
         REAL_LET_TRANS)) THEN
        REWRITE_TAC[GSYM IM_SUB; COMPLEX_NORM_GE_RE_IM];
        REPEAT(FIRST_X_ASSUM(MP_TAC o check(is_neg o concl))) THEN
        CONV_TAC COMPLEX_FIELD]]]));;

let CONTRACTIBLE_IMP_HOLOMORPHIC_SQRT,SIMPLY_CONNECTED_IMP_HOLOMORPHIC_SQRT =
 (CONJ_PAIR o prove)
 (`(!s:complex->bool.
      contractible s
      ==> !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
              ==> ?g. g holomorphic_on s /\  !z. z IN s ==> f z = g z pow 2) /\
   (!s:complex->bool.
      simply_connected s /\ locally path_connected s
      ==> !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
              ==> ?g. g holomorphic_on s /\  !z. z IN s ==> f z = g z pow 2)`,
  CONJ_TAC THEN GEN_TAC THENL
   [DISCH_THEN(ASSUME_TAC o MATCH_MP CONTRACTIBLE_IMP_HOLOMORPHIC_LOG);
    DISCH_THEN(ASSUME_TAC o
      MATCH_MP SIMPLY_CONNECTED_IMP_HOLOMORPHIC_LOG)] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `f:complex->complex`) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z:complex. cexp(g z / Cx(&2))` THEN
  ASM_SIMP_TAC[GSYM CEXP_N; COMPLEX_RING `Cx(&2) * z / Cx(&2) = z`] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
  REWRITE_TAC[HOLOMORPHIC_ON_CEXP] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_CONST] THEN
  CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Related theorems about holomorphic inverse cosines.                       *)
(* ------------------------------------------------------------------------- *)

let CONTRACTIBLE_IMP_HOLOMORPHIC_ACS = prove
 (`!f s. f holomorphic_on s /\ contractible s /\
         (!z. z IN s ==> ~(f z = Cx(&1)) /\ ~(f z = --Cx(&1)))
         ==> ?g. g holomorphic_on s /\ !z. z IN s ==> f z = ccos(g z)`,
   REPEAT STRIP_TAC THEN
   FIRST_ASSUM(MP_TAC o SPEC `\z:complex. Cx(&1) - f(z) pow 2` o
     MATCH_MP CONTRACTIBLE_IMP_HOLOMORPHIC_SQRT) THEN
   ASM_SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_POW;
                COMPLEX_RING `~(Cx(&1) - z pow 2 = Cx(&0)) <=>
                              ~(z = Cx(&1)) /\ ~(z = --Cx(&1))`] THEN
   REWRITE_TAC[COMPLEX_RING
    `Cx(&1) - w pow 2 = z pow 2 <=>
     (w + ii * z) * (w - ii * z) = Cx(&1)`] THEN
   DISCH_THEN(X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC) THEN
   FIRST_ASSUM(MP_TAC o SPEC `\z:complex. f(z) + ii * g(z)` o
       MATCH_MP CONTRACTIBLE_IMP_HOLOMORPHIC_LOG) THEN
   ASM_SIMP_TAC[HOLOMORPHIC_ON_ADD; HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_CONST;
     COMPLEX_RING `(a + b) * (a - b) = Cx(&1) ==> ~(a + b = Cx(&0))`] THEN
   DISCH_THEN(X_CHOOSE_THEN `h:complex->complex` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `\z:complex. --ii * h(z)` THEN
   ASM_SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_CONST; ccos] THEN
   X_GEN_TAC `z:complex` THEN
   DISCH_TAC THEN REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`)) THEN
   ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP (COMPLEX_FIELD
    `a * b = Cx(&1) ==> b = inv a`)) THEN
   ASM_SIMP_TAC[GSYM CEXP_NEG] THEN
   FIRST_X_ASSUM(ASSUME_TAC o SYM) THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
   ASM_REWRITE_TAC[COMPLEX_RING `ii * --ii * z = z`;
                   COMPLEX_RING `--ii * --ii * z = --z`] THEN
   CONV_TAC COMPLEX_RING);;

let CONTRACTIBLE_IMP_HOLOMORPHIC_ACS_BOUNDED = prove
 (`!f s a.
        f holomorphic_on s /\ contractible s /\ a IN s /\
        (!z. z IN s ==> ~(f z = Cx(&1)) /\ ~(f z = --Cx(&1)))
        ==> ?g. g holomorphic_on s /\ norm(g a) <= pi + norm(f a) /\
                !z. z IN s ==> f z = ccos(g z)`,
  let lemma = prove
    (`!w. ?v. ccos(v) = w /\ norm(v) <= pi + norm(w)`,
     GEN_TAC THEN EXISTS_TAC `cacs w` THEN ABBREV_TAC `v = cacs w` THEN
     MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
      [ASM_MESON_TAC[CCOS_CACS]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
     SIMP_TAC[NORM_LE_SQUARE; PI_POS_LE; NORM_POS_LE; REAL_LE_ADD] THEN
     MATCH_MP_TAC(REAL_ARITH
      `&0 <= b * c /\ a <= b pow 2 + c pow 2 ==> a <= (b + c) pow 2`) THEN
     SIMP_TAC[REAL_LE_MUL; PI_POS_LE; NORM_POS_LE] THEN
     REWRITE_TAC[COMPLEX_SQNORM; GSYM NORM_POW_2; NORM_CCOS_POW_2] THEN
     MATCH_MP_TAC REAL_LE_ADD2 THEN REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
     EXPAND_TAC "v" THEN REWRITE_TAC[REAL_ABS_PI; RE_CACS_BOUND] THEN
     MATCH_MP_TAC(REAL_ARITH
      `&0 <= c /\ x <= (d / &2) pow 2 ==> x <= c + d pow 2 / &4`) THEN
     REWRITE_TAC[REAL_LE_POW_2; GSYM REAL_LE_SQUARE_ABS; REAL_LE_ABS_SINH]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:complex->complex`; `s:complex->bool`]
        CONTRACTIBLE_IMP_HOLOMORPHIC_ACS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `(f:complex->complex) a` lemma) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ccos b = ccos(g(a:complex))` MP_TAC THENL
   [ASM_MESON_TAC[]; REWRITE_TAC[CCOS_EQ]] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real` (STRIP_ASSUME_TAC o GSYM)) THENL
   [EXISTS_TAC `\z:complex. g z + Cx(&2 * n * pi)`;
    EXISTS_TAC `\z:complex. --(g z) + Cx(&2 * n * pi)`] THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_ADD; HOLOMORPHIC_ON_NEG;
               HOLOMORPHIC_ON_CONST] THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN REWRITE_TAC[CCOS_EQ] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Extension property for inessential maps. This almost follows from         *)
(* INESSENTIAL_NEIGHBOURHOOD_EXTENSION except that here we don't need to     *)
(* assume that t is closed in s.                                             *)
(* ------------------------------------------------------------------------- *)

let INESSENTIAL_NEIGHBOURHOOD_EXTENSION_LOGARITHM = prove
 (`!f:real^N->complex s t.
        f continuous_on s /\ t SUBSET s /\
        (?g. g continuous_on t /\ !x. x IN t ==> f x = cexp(g x))
        ==> ?u. t SUBSET u /\ open_in (subtopology euclidean s) u /\
                (?g. g continuous_on u /\ !x. x IN u ==> f x = cexp(g x))`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->complex` (STRIP_ASSUME_TAC o GSYM)) THEN
  SUBGOAL_THEN
   `!x. x IN t
        ==> ?d. &0 < d /\
                (!y. y IN s /\ dist(x,y) < d
                     ==> norm(f y / f x - Cx(&1)) < &1 / &7) /\
                (!z:real^N. z IN t /\ dist(x,z) < &2 * d
                            ==> norm(h z - h x) < &1 / &5)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `(h:real^N->complex) continuous_on t` THEN
    GEN_REWRITE_TAC LAND_CONV [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[continuous_within] THEN
    DISCH_THEN(MP_TAC o SPEC `&1 / &5`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [dist] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~((f:real^N->complex) x = Cx(&0))` ASSUME_TAC THENL
     [ASM_MESON_TAC[CEXP_NZ]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\y:real^N. f y / f x) continuous (at x within s)`
    MP_TAC THENL
     [REWRITE_TAC[complex_div] THEN MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
      REWRITE_TAC[CONTINUOUS_CONST] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; SUBSET];
      REWRITE_TAC[continuous_within] THEN
      DISCH_THEN(MP_TAC o SPEC `&1 / &7`) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_SIMP_TAC[COMPLEX_DIV_REFL; dist] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC `min d (e / &2)` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; REAL_HALF] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[NORM_SUB];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:real^N->real` THEN DISCH_THEN(LABEL_TAC "*")] THEN
  ABBREV_TAC `u = \x. s INTER ball(x:real^N,d x)` THEN
  ABBREV_TAC `g = \x y. h(x:real^N) + clog(f y / f x)` THEN
  SUBGOAL_THEN
   `(!x:real^N. x IN t ==> x IN u x) /\
    (!x. x IN t ==> open_in (subtopology euclidean s) (u x))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    ASM_SIMP_TAC[IN_INTER; CENTRE_IN_BALL; OPEN_IN_OPEN_INTER; OPEN_BALL] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N y:real^N. x IN t /\ y IN u x ==> cexp(g x y) = f y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[CEXP_ADD] THEN ASM_SIMP_TAC[] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N` o el 1 o CONJUNCTS) THEN
    MP_TAC(ASSUME `y IN (u:real^N->real^N->bool) x`) THEN
    EXPAND_TAC "u" THEN REWRITE_TAC[IN_INTER; IN_BALL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (NORM_ARITH
     `norm(x - y) < &1 / &7 ==> norm(y) = &1 ==> ~(x = vec 0)`)) THEN
    SIMP_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; CEXP_CLOG; COMPLEX_VEC_0] THEN
    SIMP_TAC[COMPLEX_DIV_LMUL; COMPLEX_DIV_EQ_0; DE_MORGAN_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`subtopology euclidean (UNIONS {(u:real^N->real^N->bool) x | x IN t})`;
    `euclidean:(complex)topology`;
    `g:real^N->real^N->complex`;
    `u:real^N->real^N->bool`;
     `t:real^N->bool`]
    PASTING_LEMMA_EXISTS) THEN
  REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
              SUBTOPOLOGY_SUBTOPOLOGY] THEN
  ONCE_REWRITE_TAC[TAUT `open_in a b /\ c <=> ~(open_in a b ==> ~c)`] THEN
  SIMP_TAC[ISPEC `euclidean` OPEN_IN_IMP_SUBSET;
           SET_RULE `s SUBSET u ==> u INTER s = s`] THEN
  REWRITE_TAC[NOT_IMP] THEN
  REWRITE_TAC[SUBSET_REFL; SUBSET_UNIV;] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
        ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
        EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [REWRITE_TAC[complex_div] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_RMUL THEN
          ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTER_SUBSET];
          MATCH_MP_TAC CONTINUOUS_ON_CLOG THEN
          REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; IN_INTER] THEN
          X_GEN_TAC `y:real^N` THEN REPEAT STRIP_TAC THEN
          ONCE_REWRITE_TAC[COMPLEX_RING `z = (z - Cx(&1)) + Cx(&1)`] THEN
          REWRITE_TAC[RE_ADD; RE_CX] THEN MATCH_MP_TAC(REAL_ARITH
           `abs x < &1 ==> &0 < x + &1`) THEN
          MATCH_MP_TAC(MESON[COMPLEX_NORM_GE_RE_IM; REAL_LET_TRANS]
           `norm z < &1 ==> abs(Re z) < &1`) THEN
          MATCH_MP_TAC(REAL_ARITH `x < &1 / &7 ==> x < &1`) THEN
          REMOVE_THEN "*" (MP_TAC o SPEC `x:real^N`) THEN ASM_SIMP_TAC[] THEN
          DISCH_THEN(MP_TAC o SPEC `y:real^N` o el 1 o CONJUNCTS) THEN
          MP_TAC(ASSUME `y IN (u:real^N->real^N->bool) x`) THEN
          EXPAND_TAC "u" THEN REWRITE_TAC[IN_INTER; IN_BALL] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[]]];
      MAP_EVERY X_GEN_TAC  [`a:real^N`; `b:real^N`; `x:real^N`] THEN
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      MATCH_MP_TAC COMPLEX_EQ_CEXP THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      EXPAND_TAC "g" THEN REWRITE_TAC[IM_ADD] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&5 < a /\ abs(ha - hb) < &1 / &5 /\ abs(fa) < &2 /\ abs(fb) < &2
        ==> abs((ha + fa) - (hb + fb)) < a`) THEN
      CONJ_TAC THENL [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM IM_SUB] THEN
        MATCH_MP_TAC(MESON[COMPLEX_NORM_GE_RE_IM; REAL_LET_TRANS]
         `norm z < a ==> abs(Im z) < a`) THEN
        MP_TAC(ASSUME `x IN (u:real^N->real^N->bool) b`) THEN
        MP_TAC(ASSUME `x IN (u:real^N->real^N->bool) a`) THEN
        EXPAND_TAC "u" THEN REWRITE_TAC[IMP_IMP; IN_INTER; IN_BALL] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (TAUT
         `(p /\ q) /\ (p /\ r) ==> q /\ r`)) THEN
        DISCH_THEN(MP_TAC o MATCH_MP (NORM_ARITH
         `dist(a,x) < d /\ dist(b,x) < e
          ==> dist(a,b) < &2 * d \/ dist(a,b) < &2 * e`)) THEN
        STRIP_TAC THENL
         [REMOVE_THEN "*" (MP_TAC o SPEC `a:real^N`);
          REMOVE_THEN "*" (MP_TAC o SPEC `b:real^N`)] THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
        ASM_MESON_TAC[NORM_SUB; DIST_SYM];
        CONJ_TAC THEN TRANS_TAC REAL_LT_TRANS `pi / &2` THEN
        (CONJ_TAC THENL
          [ALL_TAC; MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC]) THEN
        MATCH_MP_TAC RE_CLOG_POS_LT_IMP THEN
        ONCE_REWRITE_TAC[COMPLEX_RING `z = (z - Cx(&1)) + Cx(&1)`] THEN
        REWRITE_TAC[RE_ADD; RE_CX] THEN MATCH_MP_TAC(REAL_ARITH
         `abs x < &1 ==> &0 < x + &1`) THEN
        MATCH_MP_TAC(MESON[COMPLEX_NORM_GE_RE_IM; REAL_LET_TRANS]
         `norm z < &1 ==> abs(Re z) < &1`) THEN
        MATCH_MP_TAC(REAL_ARITH `x < &1 / &7 ==> x < &1`) THENL
         [REMOVE_THEN "*" (MP_TAC o SPEC `a:real^N`);
          REMOVE_THEN "*" (MP_TAC o SPEC `b:real^N`)] THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^N` o el 1 o CONJUNCTS) THEN
        DISCH_THEN MATCH_MP_TAC THENL
         [MP_TAC(ASSUME `x IN (u:real^N->real^N->bool) a`);
          MP_TAC(ASSUME `x IN (u:real^N->real^N->bool) b`)] THEN
        EXPAND_TAC "u" THEN REWRITE_TAC[IN_INTER; IN_BALL] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[]]];
    DISCH_THEN(X_CHOOSE_THEN `h':real^N->complex` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `UNIONS {(u:real^N->real^N->bool) x | x IN t}` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_IN_UNIONS; FORALL_IN_GSPEC] THEN
    EXISTS_TAC `h':real^N->complex` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_IN_UNIONS; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `x:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The "borsukian" property of sets. This doesn't seem to have a standard    *)
(* name. Kuratowski uses "contractible with respect to [S^1]" while          *)
(* Whyburn uses "property b". It's closely related to unicoherence.          *)
(* ------------------------------------------------------------------------- *)

let borsukian = new_definition
 `borsukian(s:real^N->bool) <=>
        !f. f continuous_on s /\ IMAGE f s SUBSET ((:real^2) DIFF {Cx(&0)})
            ==> ?a. homotopic_with (\h. T)
                     (subtopology euclidean s,
                      subtopology euclidean ((:real^2) DIFF {Cx(&0)}))
                                   f (\x. a)`;;

let BORSUKIAN_RETRACTION_GEN = prove
 (`!s:real^M->bool t:real^N->bool h k.
        h continuous_on s /\ IMAGE h s = t /\
        k continuous_on t /\ IMAGE k t SUBSET s /\
        (!y. y IN t ==> h(k y) = y) /\
        borsukian s
        ==> borsukian t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[borsukian] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  PURE_ONCE_REWRITE_TAC[TAUT `p /\ q <=> p /\ q /\ T`] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
    COHOMOTOPICALLY_TRIVIAL_RETRACTION_NULL_GEN) THEN
  REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let RETRACT_OF_BORSUKIAN = prove
 (`!s t:real^N->bool. borsukian t /\ s retract_of t ==> borsukian s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] (REWRITE_RULE[CONJ_ASSOC]
        BORSUKIAN_RETRACTION_GEN)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->real^N` THEN
  REWRITE_TAC[RETRACTION] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `\x:real^N. x` THEN ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID]);;

let HOMEOMORPHIC_BORSUKIAN = prove
 (`!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\ borsukian s ==> borsukian t`,
  REWRITE_TAC[homeomorphic; homeomorphism] THEN
  MESON_TAC[BORSUKIAN_RETRACTION_GEN; SUBSET_REFL]);;

let HOMEOMORPHIC_BORSUKIAN_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
     s homeomorphic t ==> (borsukian s <=> borsukian t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOMEOMORPHIC_BORSUKIAN) THEN
  ASM_MESON_TAC[HOMEOMORPHIC_SYM]);;

let BORSUKIAN_TRANSLATION = prove
 (`!a:real^N s. borsukian (IMAGE (\x. a + x) s) <=> borsukian s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_BORSUKIAN_EQ THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION_SELF]);;

add_translation_invariants [BORSUKIAN_TRANSLATION];;

let BORSUKIAN_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (borsukian(IMAGE f s) <=> borsukian s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_BORSUKIAN_EQ THEN
  ASM_MESON_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF;
                HOMEOMORPHIC_REFL]);;

add_linear_invariants [BORSUKIAN_INJECTIVE_LINEAR_IMAGE];;

let HOMEOMORPHISM_BORSUKIANNESS = prove
 (`!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (borsukian(IMAGE f k) <=> borsukian k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_BORSUKIAN_EQ THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
          HOMEOMORPHISM_OF_SUBSETS)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[]);;

let HOMOTOPY_EQUIVALENT_BORSUKIANNESS = prove
 (`!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t
        ==> (borsukian s <=> borsukian t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[borsukian] THEN
  MATCH_MP_TAC HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY_NULL THEN
  ASM_REWRITE_TAC[]);;

let BORSUKIAN_ALT = prove
 (`!s:real^N->bool.
        borsukian s <=>
        !f g:real^N->real^2.
           f continuous_on s /\ IMAGE f s SUBSET ((:real^2) DIFF {Cx(&0)}) /\
           g continuous_on s /\ IMAGE g s SUBSET ((:real^2) DIFF {Cx(&0)})
           ==> homotopic_with (\h. T)
                (subtopology euclidean s,
                 subtopology euclidean ((:real^2) DIFF {Cx (&0)})) f g`,
  REWRITE_TAC[borsukian; HOMOTOPIC_TRIVIALITY] THEN
  SIMP_TAC[PATH_CONNECTED_PUNCTURED_UNIVERSE; DIMINDEX_2; LE_REFL]);;

let BORSUKIAN_CONTINUOUS_LOGARITHM = prove
 (`!s:real^N->bool.
        borsukian s <=>
        !f. f continuous_on s /\ IMAGE f s SUBSET ((:real^2) DIFF {Cx(&0)})
            ==> ?g. g continuous_on s /\ (!x. x IN s ==> f(x) = cexp(g x))`,
  REWRITE_TAC[borsukian; INESSENTIAL_EQ_CONTINUOUS_LOGARITHM]);;

let BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE = prove
 (`!s:real^N->bool.
        borsukian s <=>
           !f. f continuous_on s /\ IMAGE f s SUBSET sphere(Cx(&0),&1)
               ==> ?g. g continuous_on s /\ (!x. x IN s ==> f(x) = cexp(g x))`,
  GEN_TAC THEN REWRITE_TAC[BORSUKIAN_CONTINUOUS_LOGARITHM] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; COMPLEX_IN_SPHERE_0; SET_RULE
   `IMAGE f s SUBSET UNIV DIFF {a} <=> !z. z IN s ==> ~(f z = a)`] THEN
  EQ_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `f:real^N->complex` THEN STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `\x:real^N. f(x) / Cx(norm(f x))`) THEN
    ASM_SIMP_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NORM;
                 REAL_DIV_REFL; NORM_EQ_0; COMPLEX_NORM_ZERO] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
      ASM_REWRITE_TAC[CX_INJ; COMPLEX_NORM_ZERO; CONTINUOUS_ON_CX_LIFT] THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_NORM_COMPOSE];
      ASM_SIMP_TAC[CX_INJ; COMPLEX_NORM_ZERO; COMPLEX_FIELD
       `~(z = Cx(&0)) ==> (w / z = u <=> w = z * u)`] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->complex` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC
       `\x. clog(Cx(norm(f x:complex))) + (g:real^N->complex)(x)` THEN
      ASM_SIMP_TAC[CEXP_ADD; CEXP_CLOG; CX_INJ; COMPLEX_NORM_ZERO] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_CX_LIFT; CONTINUOUS_ON_LIFT_NORM_COMPOSE] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CLOG THEN
      ASM_SIMP_TAC[IMP_CONJ; FORALL_IN_IMAGE; RE_CX; COMPLEX_NORM_NZ]]]);;

let BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE_CX = prove
 (`!s:real^N->bool.
        borsukian s <=>
            !f. f continuous_on s /\ IMAGE f s SUBSET sphere(Cx(&0),&1)
            ==> ?g. (Cx o g) continuous_on s /\
                    (!x. x IN s ==> f x = cexp(ii * Cx(g x)))`,
  GEN_TAC THEN REWRITE_TAC[BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; COMPLEX_IN_SPHERE_0] THEN EQ_TAC THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `f:real^N->complex` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [X_GEN_TAC `g:real^N->complex` THEN STRIP_TAC THEN
    EXISTS_TAC `Im o (g:real^N->complex)` THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_CX_IM; CONTINUOUS_ON_COMPOSE; o_ASSOC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`)) THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(f:real^N->complex) x = cexp(g x)` THEN
    ASM_REWRITE_TAC[NORM_CEXP; o_DEF; REAL_EXP_EQ_1] THEN
    DISCH_TAC THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_EQ; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
    REWRITE_TAC[REAL_NEG_0];
    X_GEN_TAC `g:real^N->real` THEN STRIP_TAC THEN
    EXISTS_TAC `\x:real^N. ii * Cx(g x)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
    ASM_REWRITE_TAC[GSYM o_DEF]]);;

let BORSUKIAN_CIRCLE = prove
 (`!s:real^N->bool.
        borsukian s <=>
            !f. f continuous_on s /\ IMAGE f s SUBSET sphere(Cx(&0),&1)
                ==> ?a. homotopic_with (\h. T)
                         (subtopology euclidean s,
                          subtopology euclidean (sphere(Cx(&0),&1)))
                         f (\x. a)`,
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
  REWRITE_TAC[INESSENTIAL_EQ_CONTINUOUS_LOGARITHM_CIRCLE] THEN
  REWRITE_TAC[BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE_CX] THEN
  REWRITE_TAC[COMPLEX_VEC_0]);;

let BORSUKIAN_CIRCLE_ALT = prove
 (`!s:real^N->bool.
        borsukian s <=>
        !f g:real^N->real^2.
           f continuous_on s /\ IMAGE f s SUBSET sphere(Cx(&0),&1) /\
           g continuous_on s /\ IMAGE g s SUBSET sphere(Cx(&0),&1)
           ==> homotopic_with (\h. T)
                (subtopology euclidean s,
                 subtopology euclidean (sphere(Cx(&0),&1))) f g`,
  REWRITE_TAC[BORSUKIAN_CIRCLE; HOMOTOPIC_TRIVIALITY] THEN
  SIMP_TAC[PATH_CONNECTED_SPHERE; DIMINDEX_2; LE_REFL]);;

let CONTRACTIBLE_IMP_BORSUKIAN = prove
 (`!s:real^N->bool. contractible s ==> borsukian s`,
  SIMP_TAC[borsukian; CONTRACTIBLE_IMP_PATH_CONNECTED] THEN
  MESON_TAC[NULLHOMOTOPIC_FROM_CONTRACTIBLE]);;

let CONIC_IMP_BORSUKIAN = prove
 (`!s:real^N->bool. conic s ==> borsukian s`,
  MESON_TAC[CONIC_IMP_CONTRACTIBLE; CONTRACTIBLE_IMP_BORSUKIAN]);;

let SIMPLY_CONNECTED_IMP_BORSUKIAN = prove
 (`!s:real^N->bool.
        simply_connected s /\ locally path_connected s ==> borsukian s`,
  SIMP_TAC[BORSUKIAN_CONTINUOUS_LOGARITHM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_LOGARITHM_ON_SIMPLY_CONNECTED THEN
  ASM SET_TAC[]);;

let STARLIKE_IMP_BORSUKIAN = prove
 (`!s:real^N->bool. starlike s ==> borsukian s`,
  SIMP_TAC[CONTRACTIBLE_IMP_BORSUKIAN; STARLIKE_IMP_CONTRACTIBLE]);;

let BORSUKIAN_EMPTY = prove
 (`borsukian({}:real^N->bool)`,
  SIMP_TAC[CONTRACTIBLE_IMP_BORSUKIAN; CONTRACTIBLE_EMPTY]);;

let BORSUKIAN_UNIV = prove
 (`borsukian(:real^N)`,
  SIMP_TAC[CONTRACTIBLE_IMP_BORSUKIAN; CONTRACTIBLE_UNIV]);;

let CONVEX_IMP_BORSUKIAN = prove
 (`!s:real^N->bool. convex s ==> borsukian s`,
  MESON_TAC[STARLIKE_IMP_BORSUKIAN; CONVEX_IMP_STARLIKE; BORSUKIAN_EMPTY]);;

let BORSUKIAN_1_GEN = prove
 (`!s:real^N->bool.
        (dimindex(:N) = 1 \/ ?r:real^1->bool. s homeomorphic r)
        ==> borsukian s`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[BORSUKIAN_CIRCLE] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COHOMOTOPICALLY_TRIVIAL_1D THEN
  ASM_REWRITE_TAC[ANR_SPHERE; CONNECTED_SPHERE_EQ] THEN
  REWRITE_TAC[DIMINDEX_2; LE_REFL]);;

let BORSUKIAN_1 = prove
 (`!s:real^1->bool. borsukian s`,
  GEN_TAC THEN MATCH_MP_TAC BORSUKIAN_1_GEN THEN
  REWRITE_TAC[DIMINDEX_1]);;

let BORSUKIAN_SPHERE = prove
 (`!a:real^N r. borsukian(sphere(a,r)) <=> r <= &0 \/ ~(dimindex(:N) = 2)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[SPHERE_EMPTY; BORSUKIAN_EMPTY; REAL_LT_IMP_LE] THEN
  ASM_CASES_TAC `r = &0` THEN
  ASM_SIMP_TAC[REAL_LT_REFL; SPHERE_SING; CONVEX_IMP_BORSUKIAN; CONVEX_SING;
               GSYM REAL_NOT_LT] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `dimindex(:N) = 1` THENL
   [ASM_SIMP_TAC[ARITH; BORSUKIAN_1_GEN]; ALL_TAC] THEN
  ASM_CASES_TAC `dimindex(:N) = 2` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~borsukian(sphere(Cx(&0),&1))` MP_TAC THENL
     [REWRITE_TAC[BORSUKIAN_CIRCLE] THEN
      DISCH_THEN(MP_TAC o SPEC `\z:complex. z`) THEN
      REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID; SUBSET_REFL] THEN
      ASM_REWRITE_TAC[GSYM contractible; CONTRACTIBLE_SPHERE] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[CONTRAPOS_THM] THEN MATCH_MP_TAC
       (ONCE_REWRITE_RULE[IMP_CONJ] HOMEOMORPHIC_BORSUKIAN) THEN
      REWRITE_TAC[HOMEOMORPHIC_SPHERES_EQ] THEN
      ASM_REWRITE_TAC[DIMINDEX_2; REAL_LT_01]];
    MATCH_MP_TAC SIMPLY_CONNECTED_IMP_BORSUKIAN THEN
    ASM_SIMP_TAC[SIMPLY_CONNECTED_SPHERE] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] (GSYM dist)] THEN
    ASM_SIMP_TAC[LOCALLY_PATH_CONNECTED_SPHERE;
                 SIMPLY_CONNECTED_SPHERE_EQ] THEN
    DISJ1_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n /\ ~(n = 1) /\ ~(n = 2) ==> 3 <= n`) THEN
    ASM_REWRITE_TAC[DIMINDEX_GE_1]]);;

let BORSUKIAN_OPEN_UNION = prove
 (`!s t:real^N->bool.
        open_in (subtopology euclidean (s UNION t)) s /\
        open_in (subtopology euclidean (s UNION t)) t /\
        borsukian s /\ borsukian t /\ connected(s INTER t)
        ==> borsukian(s UNION t)`,
  REPEAT GEN_TAC THEN SIMP_TAC[BORSUKIAN_CONTINUOUS_LOGARITHM] THEN
  STRIP_TAC THEN X_GEN_TAC `f:real^N->complex` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `f:real^N->complex`)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNION]; ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->complex` STRIP_ASSUME_TAC)] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNION]; ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `h:real^N->complex` STRIP_ASSUME_TAC)] THEN
  ASM_CASES_TAC `s INTER t:real^N->bool = {}` THENL
   [EXISTS_TAC `(\x. if x IN s then g x else h x):real^N->complex` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL_OPEN THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(\x. g x - h x):real^N->complex`; `s INTER t:real^N->bool`]
   CONTINUOUS_DISCRETE_RANGE_CONSTANT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTER_SUBSET];
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      EXISTS_TAC `&2 * pi` THEN
      REWRITE_TAC[REAL_ARITH `&0 < &2 * x <=> &0 < x`; PI_POS] THEN
      X_GEN_TAC `y:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN
      ONCE_REWRITE_TAC[COMPLEX_RING
       `a - b:complex = c - d <=> a - c = b - d`] THEN
      DISCH_TAC THEN MATCH_MP_TAC COMPLEX_EQ_CEXP THEN
      REWRITE_TAC[CEXP_SUB] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
       REAL_LET_TRANS)) THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [COMPLEX_RING
       `(a - b) - (c - d):complex = (a - c) - (b - d)`] THEN
      REWRITE_TAC[GSYM IM_SUB; COMPLEX_NORM_GE_RE_IM]];

    REWRITE_TAC[IN_INTER; COMPLEX_EQ_SUB_RADD] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:complex`) THEN
    EXISTS_TAC `(\x. if x IN s then g x else a + h x):real^N->complex` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL_OPEN THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST] THEN
      ASM SET_TAC[];
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [ASM_MESON_TAC[]; REWRITE_TAC[CEXP_ADD]] THEN
      SUBGOAL_THEN `?y:real^N. y IN s /\ y IN t` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `cexp(a + h(y:real^N)) = cexp(h y)` MP_TAC THENL
       [ASM_MESON_TAC[]; REWRITE_TAC[CEXP_ADD]] THEN
      SIMP_TAC[COMPLEX_RING `a * z = z <=> a = Cx(&1) \/ z = Cx(&0)`;
               CEXP_NZ; COMPLEX_MUL_LID] THEN
      ASM SET_TAC[]]]);;

let BORSUKIAN_CLOSED_UNION = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        borsukian s /\ borsukian t /\ connected(s INTER t)
        ==> borsukian(s UNION t)`,
  REPEAT GEN_TAC THEN SIMP_TAC[BORSUKIAN_CONTINUOUS_LOGARITHM] THEN
  STRIP_TAC THEN X_GEN_TAC `f:real^N->complex` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `f:real^N->complex`)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNION]; ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->complex` STRIP_ASSUME_TAC)] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNION]; ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `h:real^N->complex` STRIP_ASSUME_TAC)] THEN
  ASM_CASES_TAC `s INTER t:real^N->bool = {}` THENL
   [EXISTS_TAC `(\x. if x IN s then g x else h x):real^N->complex` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(\x. g x - h x):real^N->complex`; `s INTER t:real^N->bool`]
   CONTINUOUS_DISCRETE_RANGE_CONSTANT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTER_SUBSET];
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      EXISTS_TAC `&2 * pi` THEN
      REWRITE_TAC[REAL_ARITH `&0 < &2 * x <=> &0 < x`; PI_POS] THEN
      X_GEN_TAC `y:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN
      ONCE_REWRITE_TAC[COMPLEX_RING
       `a - b:complex = c - d <=> a - c = b - d`] THEN
      DISCH_TAC THEN MATCH_MP_TAC COMPLEX_EQ_CEXP THEN
      REWRITE_TAC[CEXP_SUB] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
       REAL_LET_TRANS)) THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [COMPLEX_RING
       `(a - b) - (c - d):complex = (a - c) - (b - d)`] THEN
      REWRITE_TAC[GSYM IM_SUB; COMPLEX_NORM_GE_RE_IM]];

    REWRITE_TAC[IN_INTER; COMPLEX_EQ_SUB_RADD] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:complex`) THEN
    EXISTS_TAC `(\x. if x IN s then g x else a + h x):real^N->complex` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST] THEN
      ASM SET_TAC[];
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
       [ASM_MESON_TAC[]; REWRITE_TAC[CEXP_ADD]] THEN
      SUBGOAL_THEN `?y:real^N. y IN s /\ y IN t` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `cexp(a + h(y:real^N)) = cexp(h y)` MP_TAC THENL
       [ASM_MESON_TAC[]; REWRITE_TAC[CEXP_ADD]] THEN
      SIMP_TAC[COMPLEX_RING `a * z = z <=> a = Cx(&1) \/ z = Cx(&0)`;
               CEXP_NZ; COMPLEX_MUL_LID] THEN
      ASM SET_TAC[]]]);;

let BORSUKIAN_SEPARATION_COMPACT = prove
 (`!s:real^2->bool.
        compact s ==> (borsukian s <=> connected((:real^2) DIFF s))`,
  SIMP_TAC[BORSUKIAN_CIRCLE; BORSUK_SEPARATION_THEOREM; DIMINDEX_2; LE_REFL;
           COMPLEX_VEC_0]);;

let BORSUKIAN_COMPONENTWISE_EQ = prove
 (`!s:real^N->bool.
        locally connected s \/ compact s
        ==> (borsukian s <=> !c. c IN components s ==> borsukian c)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[BORSUKIAN_ALT] THEN
  MATCH_MP_TAC COHOMOTOPICALLY_TRIVIAL_ON_COMPONENTS THEN
  ASM_SIMP_TAC[OPEN_IMP_ANR; OPEN_DIFF; OPEN_UNIV; CLOSED_SING]);;

let BORSUKIAN_COMPONENTWISE = prove
 (`!s:real^N->bool.
        (locally connected s \/ compact s) /\
        (!c. c IN components s ==> borsukian c)
        ==> borsukian s`,
  MESON_TAC[BORSUKIAN_COMPONENTWISE_EQ]);;

let BORSUKIAN_MONOTONE_IMAGE_COMPACT = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\ compact s /\
        (!y. y IN t ==> connected {x | x IN s /\ f x = y}) /\
        borsukian s
        ==> borsukian t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BORSUKIAN_CONTINUOUS_LOGARITHM] THEN
  X_GEN_TAC `g:real^N->complex` THEN STRIP_TAC THEN FIRST_X_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [BORSUKIAN_CONTINUOUS_LOGARITHM]) THEN
  DISCH_THEN(MP_TAC o SPEC `(g:real^N->complex) o (f:real^M->real^N)`) THEN
  ASM_SIMP_TAC[IMAGE_o; CONTINUOUS_ON_COMPOSE; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!y. ?x. y IN t ==> x IN s /\ (f:real^M->real^N) x = y`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f':real^N->real^M` THEN STRIP_TAC THEN
  EXISTS_TAC `(h:real^M->complex) o (f':real^N->real^M)` THEN
  REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_FROM_CLOSED_GRAPH THEN
  EXISTS_TAC `IMAGE (h:real^M->complex) s` THEN
  ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; IMAGE_o] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[o_THM]] THEN
  SUBGOAL_THEN
   `{pastecart x ((h:real^M->complex) ((f':real^N->real^M) x)) | x IN t} =
    {p | ?x. x IN s /\ pastecart x p IN
                       {z | z IN s PCROSS UNIV /\
                            (sndcart z - pastecart (f(fstcart z))
                                                  (h(fstcart z))) IN {vec 0}}}`
  SUBST1_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CLOSED_COMPACT_PROJECTION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
    ASM_SIMP_TAC[CLOSED_UNIV; CLOSED_PCROSS; COMPACT_IMP_CLOSED] THEN
    REWRITE_TAC[CLOSED_SING] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[GSYM o_DEF] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; IMAGE_FSTCART_PCROSS] THEN
    ASM_REWRITE_TAC[UNIV_NOT_EMPTY]] THEN
  REWRITE_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_UNIV; IN_SING; VECTOR_SUB_EQ] THEN
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_ELIM_THM] THEN
  REWRITE_TAC[CONJ_ASSOC; PASTECART_INJ] THEN
  MAP_EVERY X_GEN_TAC [`y:real^N`; `z:complex`] THEN
  ONCE_REWRITE_TAC[TAUT `(p /\ q) /\ r <=> q /\ p /\ r`] THEN
  REWRITE_TAC[UNWIND_THM1] THEN EQ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^M` STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?a. !x. x IN {x | x IN s /\ (f:real^M->real^N) x = y}
            ==> h x - h(f' y):complex = a`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `a:complex` THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(MP_TAC o SPEC `(f':real^N->real^M) y`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[VECTOR_SUB_REFL]] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_SUB_EQ]) THEN ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_DISCRETE_RANGE_CONSTANT THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^M` THEN STRIP_TAC THEN
  EXISTS_TAC `&2 * pi` THEN
  REWRITE_TAC[REAL_ARITH `&0 < &2 * x <=> &0 < x`; PI_POS] THEN
  X_GEN_TAC `u:real^M` THEN
  REWRITE_TAC[COMPLEX_RING `a - x:complex = b - x <=> a = b`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN
  REWRITE_TAC[COMPLEX_RING `(a - x) - (b - x):complex = a - b`] THEN
  DISCH_TAC THEN MATCH_MP_TAC COMPLEX_EQ_CEXP THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN REWRITE_TAC[GSYM IM_SUB] THEN
  ASM_MESON_TAC[REAL_LET_TRANS; COMPLEX_NORM_GE_RE_IM]);;

let BORSUKIAN_OPEN_MAP_IMAGE_COMPACT = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\ compact s /\
        (!u. open_in (subtopology euclidean s) u
             ==> open_in (subtopology euclidean t) (IMAGE f u)) /\
        borsukian s
        ==> borsukian t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE_CX] THEN STRIP_TAC THEN
  X_GEN_TAC `g:real^N->complex` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^N->complex) o (f:real^M->real^N)`) THEN
  ASM_SIMP_TAC[IMAGE_o; CONTINUOUS_ON_COMPOSE; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!y. ?x. y IN t ==> x IN s /\ (f:real^M->real^N) x = y /\
                       (!x'. x' IN s /\ f x' = y ==> h x <= h x')`
  MP_TAC THENL
   [REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `{ h x:real | x IN s /\ (f:real^M->real^N) x = y}`
         COMPACT_ATTAINS_INF) THEN
    REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC; GSYM CONJ_ASSOC] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; GSYM CONTINUOUS_ON_CX_LIFT] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN SET_TAC[];
      ONCE_REWRITE_TAC[SET_RULE `x = y <=> x IN {y}`] THEN
      MATCH_MP_TAC PROPER_MAP_FROM_COMPACT THEN
      ASM_MESON_TAC[CLOSED_IN_SING; SUBSET_REFL]];
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `k:real^N->real^M` THEN DISCH_TAC THEN
  EXISTS_TAC `(h:real^M->real) o (k:real^N->real^M)` THEN
  REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[continuous_on] THEN X_GEN_TAC `y:real^N` THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Cx o (h:real^M->real)`; `s:real^M->bool`]
        COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[o_THM; DIST_CX] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`\y. {x | x IN s /\ (f:real^M->real^N) x = y}`;
    `s:real^M->bool`; `t:real^N->bool`]
    UPPER_LOWER_HEMICONTINUOUS_EXPLICIT) THEN
  ASM_SIMP_TAC[GSYM CLOSED_MAP_IFF_UPPER_HEMICONTINUOUS_PREIMAGE;
               GSYM OPEN_MAP_IFF_LOWER_HEMICONTINUOUS_PREIMAGE;
               SUBSET_REFL; SUBSET_RESTRICT] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_IMP_CLOSED_MAP]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`y:real^N`; `d:real`]) THEN
  ASM_REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC COMPACT_IMP_BOUNDED; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CLOSED_IN_COMPACT THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[SET_RULE `x IN s /\ f x = y <=> x IN s /\ f x IN {y}`] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[CLOSED_IN_SING; SUBSET_REFL];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y':real^N` THEN STRIP_TAC THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `y':real^N`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `(k:real^N->real^M) y`)
                             (MP_TAC o SPEC `(k:real^N->real^M) y'`)) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^M` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `w':real^M` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `y':real^N`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
  ASM_SIMP_TAC[] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^M`) THEN ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `w':real^M`) THEN ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`w:real^M`; `(k:real^N->real^M) y'`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`w':real^M`; `(k:real^N->real^M) y`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Unicoherence (closed).                                                    *)
(* ------------------------------------------------------------------------- *)

let unicoherent = new_definition
 `unicoherent(u:real^N->bool) <=>
  !s t. connected s /\ connected t /\ s UNION t = u /\
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t
        ==> connected (s INTER t)`;;

let HOMEOMORPHIC_UNICOHERENT = prove
 (`!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\ unicoherent s ==> unicoherent t`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
  STRIP_TAC THEN REWRITE_TAC[unicoherent] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `u INTER v = IMAGE (f:real^M->real^N)
                (IMAGE (g:real^N->real^M) u INTER IMAGE g v)`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [unicoherent]) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> r /\ (p /\ q) /\ s`] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
    CONJ_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_CLOSED_MAP THEN
    MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[homeomorphism]]);;

let HOMEOMORPHIC_UNICOHERENT_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
     s homeomorphic t ==> (unicoherent s <=> unicoherent t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HOMEOMORPHIC_UNICOHERENT) THEN
  ASM_MESON_TAC[HOMEOMORPHIC_SYM]);;

let UNICOHERENT_TRANSLATION = prove
 (`!a:real^N s. unicoherent (IMAGE (\x. a + x) s) <=> unicoherent s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_UNICOHERENT_EQ THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION_SELF]);;

add_translation_invariants [UNICOHERENT_TRANSLATION];;

let UNICOHERENT_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (unicoherent(IMAGE f s) <=> unicoherent s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_UNICOHERENT_EQ THEN
  ASM_MESON_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF;
                HOMEOMORPHIC_REFL]);;

add_linear_invariants [UNICOHERENT_INJECTIVE_LINEAR_IMAGE];;

let HOMEOMORPHISM_UNICOHERENCE = prove
 (`!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (unicoherent(IMAGE f k) <=> unicoherent k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_UNICOHERENT_EQ THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
          HOMEOMORPHISM_OF_SUBSETS)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[]);;

let BORSUKIAN_IMP_UNICOHERENT = prove
 (`!u:real^N->bool. borsukian u ==> unicoherent u`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[unicoherent] THEN
  SUBGOAL_THEN
   `!f. f continuous_on u /\ IMAGE f u SUBSET sphere(vec 0,&1)
             ==> ?a. homotopic_with (\h. T)
                      (subtopology euclidean u,
                       subtopology euclidean ((:complex) DIFF {Cx (&0)}))
                      (f:real^N->complex) (\t. a)`
  MP_TAC THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I
     [BORSUKIAN_CIRCLE]) THEN
    X_GEN_TAC `f:real^N->complex` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `f:real^N->complex`) THEN
    ASM_REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_SUBSET_RIGHT) THEN
    REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF {a} <=> ~(a IN s)`] THEN
    REWRITE_TAC[IN_SPHERE; DIST_REFL] THEN REAL_ARITH_TAC;
    POP_ASSUM(K ALL_TAC)] THEN
  REWRITE_TAC[sphere; DIST_0; INESSENTIAL_EQ_CONTINUOUS_LOGARITHM] THEN
  REPEAT STRIP_TAC THEN SIMP_TAC[CONNECTED_CLOSED_IN_EQ; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v:real^N->bool`; `w:real^N->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `closed_in (subtopology euclidean u) (v:real^N->bool) /\
    closed_in (subtopology euclidean u) (w:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_INTER; CLOSED_IN_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`v:real^N->bool`; `w:real^N->bool`; `u:real^N->bool`;
    `vec 0:real^1`; `vec 1:real^1`] URYSOHN_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->real^1` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?g:real^N->real^2.
        g continuous_on u /\ IMAGE g u SUBSET {x | norm x = &1} /\
        (!x. x IN s ==> g(x) = cexp(Cx pi * ii * Cx(drop(q x)))) /\
        (!x. x IN t ==> g(x) = inv(cexp(Cx pi * ii * Cx(drop(q x)))))`
  (DESTRUCT_TAC "@g. cont circle s t") THENL
   [EXISTS_TAC
     `\x. if (x:real^N) IN s then cexp(Cx pi * ii * Cx(drop(q x)))
          else inv(cexp(Cx pi * ii * Cx(drop(q x))))` THEN
    SUBGOAL_THEN
     `!x:real^N.
        x IN s INTER t
        ==> cexp(Cx pi * ii * Cx(drop(q x))) =
            inv(cexp(Cx pi * ii * Cx(drop (q x))))`
    ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `v UNION w:real^N->bool = s INTER t`)) THEN
      REWRITE_TAC[IN_UNION] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[DROP_VEC; COMPLEX_MUL_RZERO; CEXP_0; COMPLEX_INV_1] THEN
      REWRITE_TAC[COMPLEX_MUL_RID; EULER] THEN
      REWRITE_TAC[RE_MUL_CX; IM_MUL_CX; RE_MUL_II; IM_MUL_II] THEN
      REWRITE_TAC[RE_II; IM_II; REAL_MUL_RZERO; REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_EXP_0; COMPLEX_MUL_LID; COS_PI; SIN_PI] THEN
      REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "u" THEN MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
      ASM_REWRITE_TAC[SET_RULE
       `P /\ ~P \/ x IN t /\ x IN s <=> x IN s INTER t`] THEN
      CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_INV THEN REWRITE_TAC[CEXP_NZ]] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
      REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNION];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_INV; NORM_CEXP] THEN
      REWRITE_TAC[RE_MUL_CX; RE_MUL_II; IM_CX] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0; REAL_INV_1];
      GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
     FIRST_X_ASSUM(MP_TAC o SPEC `g:real^N->complex`) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(X_CHOOSE_THEN `h:real^N->complex` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `(?n. integer n /\
         !x:real^N. x IN s
                    ==> h(x) - Cx pi * ii * Cx (drop (q x)) =
                        Cx(&2 * n * pi) * ii) /\
    (?n. integer n /\
         !x:real^N. x IN t
                    ==> h(x) + Cx pi * ii * Cx (drop (q x)) =
                        Cx(&2 * n * pi) * ii)`
  (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `m:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))
    (X_CHOOSE_THEN `n:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))
  THENL
   [CONJ_TAC THEN MATCH_MP_TAC(MESON[]
     `(?x. x IN s) /\
      (!x. x IN s ==> ?n. P n /\ f x = k n) /\
      (?a. !x. x IN s ==> f x = a)
      ==> (?n. P n /\ !x. x IN s ==> f x = k n)`) THEN
    (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
   (CONJ_TAC THENL
     [REWRITE_TAC[COMPLEX_RING `a + b:complex = c <=> a = --b + c`;
                  COMPLEX_RING `a - b:complex = c <=> a = b + c`] THEN
      REWRITE_TAC[GSYM CEXP_EQ; CEXP_NEG] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(LABEL_TAC "*") THEN
    MATCH_MP_TAC CONTINUOUS_DISCRETE_RANGE_CONSTANT THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [(MATCH_MP_TAC CONTINUOUS_ON_ADD ORELSE
       MATCH_MP_TAC CONTINUOUS_ON_SUB) THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNION]; ALL_TAC] THEN
      REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNION];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `&2 * pi` THEN
      REWRITE_TAC[REAL_ARITH `&0 < &2 * x <=> &0 < x`; PI_POS] THEN
      X_GEN_TAC `y:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      REMOVE_THEN "*" (fun th ->
       MP_TAC(SPEC `y:real^N` th) THEN MP_TAC(SPEC `x:real^N` th)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[COMPLEX_EQ_MUL_RCANCEL; II_NZ; GSYM COMPLEX_SUB_RDISTRIB;
            COMPLEX_NORM_MUL; CX_INJ; COMPLEX_NORM_II; REAL_MUL_RID] THEN
      REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX] THEN
      REWRITE_TAC[REAL_EQ_MUL_LCANCEL; GSYM REAL_SUB_LDISTRIB] THEN
      REWRITE_TAC[GSYM REAL_SUB_RDISTRIB; REAL_ABS_MUL] THEN
      REWRITE_TAC[REAL_EQ_MUL_RCANCEL; PI_NZ; REAL_ABS_PI] THEN
      REWRITE_TAC[REAL_ABS_NUM; REAL_OF_NUM_EQ; ARITH_EQ] THEN
      DISCH_TAC THEN REWRITE_TAC[REAL_ARITH
       `&2 * p <= &2 * a * p <=> &0 <= &2 * p * (a - &1)`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PI_POS_LE; REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN
      ASM_SIMP_TAC[INTEGER_CLOSED; REAL_SUB_0]]);
      ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `p ==> q ==> F <=> ~(p /\ q)`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `(!x. x IN s ==> P x) /\ (!x. x IN t ==> Q x)
    ==> ~(v = {}) /\ ~(w = {}) /\ v UNION w SUBSET s INTER t
         ==> ~(!y z. y IN v /\ z IN w ==> ~(P y /\ Q y /\ P z /\ Q z))`)) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (COMPLEX_RING
   `y + p = n /\ y - p = m /\ z + q = n /\ z - q = m ==> q:complex = p`)) THEN
  REWRITE_TAC[DROP_VEC; COMPLEX_MUL_RZERO; COMPLEX_ENTIRE; CX_INJ] THEN
  REWRITE_TAC[PI_NZ; II_NZ; REAL_OF_NUM_EQ; ARITH_EQ]);;

let CONTRACTIBLE_IMP_UNICOHERENT = prove
 (`!u:real^N->bool. contractible u ==> unicoherent u`,
  SIMP_TAC[BORSUKIAN_IMP_UNICOHERENT; CONTRACTIBLE_IMP_BORSUKIAN]);;

let CONVEX_IMP_UNICOHERENT = prove
 (`!u:real^N->bool. convex u ==> unicoherent u`,
  SIMP_TAC[BORSUKIAN_IMP_UNICOHERENT; CONVEX_IMP_BORSUKIAN]);;

let UNICOHERENT_UNIV = prove
 (`unicoherent(:real^N)`,
  SIMP_TAC[CONVEX_IMP_UNICOHERENT; CONVEX_UNIV]);;

let UNICOHERENT_MONOTONE_IMAGE_COMPACT = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\ compact s /\
        (!y. y IN t ==> connected {x | x IN s /\ f x = y}) /\
        unicoherent s
        ==> unicoherent t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact(t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_CONTINUOUS_IMAGE]; REWRITE_TAC[unicoherent]] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
  ASM_SIMP_TAC[CLOSED_IN_CLOSED_EQ; COMPACT_IMP_CLOSED] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [unicoherent]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`{x | x IN s /\ (f:real^M->real^N) x IN u}`;
    `{x | x IN s /\ (f:real^M->real^N) x IN v}`]) THEN
  ASM_SIMP_TAC[CLOSED_IN_CLOSED_EQ; COMPACT_IMP_CLOSED; SUBSET_RESTRICT;
               CONTINUOUS_CLOSED_PREIMAGE; CONJ_ASSOC] THEN
  REWRITE_TAC[IMP_CONJ_ALT] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`; `t:real^N->bool`]
    CONNECTED_CLOSED_MONOTONE_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_IMP_CLOSED_MAP]; ALL_TAC] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o ISPEC `f:real^M->real^N` o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] CONNECTED_CONTINUOUS_IMAGE)) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN SET_TAC[];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Several common variants of unicoherence for R^n.                          *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_FRONTIER_SIMPLE = prove
 (`!s. connected(s) /\ connected((:real^N) DIFF s) ==> connected(frontier s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FRONTIER_CLOSURES] THEN
  MATCH_MP_TAC(REWRITE_RULE[unicoherent] UNICOHERENT_UNIV) THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN
  ASM_SIMP_TAC[CLOSED_CLOSURE; CONNECTED_CLOSURE] THEN
  MATCH_MP_TAC(SET_RULE
   `s SUBSET closure s /\ t SUBSET closure t /\ s UNION t = UNIV
    ==> closure s UNION closure t = UNIV`) THEN
  REWRITE_TAC[CLOSURE_SUBSET] THEN SET_TAC[]);;

let CONNECTED_FRONTIER_COMPONENT_COMPLEMENT = prove
 (`!s c:real^N->bool.
        connected s /\ c IN components((:real^N) DIFF s)
        ==> connected(frontier c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_FRONTIER_SIMPLE THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
    MATCH_MP_TAC COMPONENT_COMPLEMENT_CONNECTED THEN
    EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; CONNECTED_UNIV]]);;

let CONNECTED_FRONTIER_DISJOINT = prove
 (`!s t:real^N->bool.
     connected s /\ connected t /\ DISJOINT s t /\ frontier s SUBSET frontier t
     ==> connected(frontier s)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s = (:real^N)` THEN
  ASM_REWRITE_TAC[FRONTIER_UNIV; CONNECTED_EMPTY] THEN
  SUBGOAL_THEN `?c. c IN components((:real^N) DIFF s) /\ t SUBSET c`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC EXISTS_COMPONENT_SUPERSET THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `frontier s:real^N->bool = frontier c` SUBST1_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[CONNECTED_FRONTIER_COMPONENT_COMPLEMENT]] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[frontier; IN_DIFF] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
       MATCH_MP SUBSET_CLOSURE) THEN
      ASM_MESON_TAC[SUBSET; frontier; IN_DIFF];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
        [GSYM FRONTIER_COMPLEMENT]) THEN
      REWRITE_TAC[frontier] THEN
      MATCH_MP_TAC(SET_RULE `u SUBSET t ==> x IN s DIFF t ==> ~(x IN u)`) THEN
      MATCH_MP_TAC SUBSET_INTERIOR THEN
      ASM_MESON_TAC[IN_COMPONENTS_SUBSET]];
    GEN_REWRITE_TAC RAND_CONV [GSYM FRONTIER_COMPLEMENT] THEN
    ASM_MESON_TAC[FRONTIER_OF_COMPONENTS_SUBSET]]);;

let SEPARATION_BY_COMPONENT_CLOSED_POINTWISE = prove
 (`!s a b. closed s /\ ~connected_component ((:real^N) DIFF s) a b
           ==> ?c. c IN components s /\
                   ~connected_component((:real^N) DIFF c) a b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `(a:real^N) IN s` THENL
   [EXISTS_TAC `connected_component s (a:real^N)` THEN
    ASM_REWRITE_TAC[IN_COMPONENTS] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP CONNECTED_COMPONENT_IN) THEN
    REWRITE_TAC[IN_UNIV; IN_DIFF] THEN REWRITE_TAC[IN] THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ];
    ALL_TAC] THEN
  ASM_CASES_TAC `(b:real^N) IN s` THENL
   [EXISTS_TAC `connected_component s (b:real^N)` THEN
    ASM_REWRITE_TAC[IN_COMPONENTS] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP CONNECTED_COMPONENT_IN) THEN
    REWRITE_TAC[IN_UNIV; IN_DIFF] THEN REWRITE_TAC[IN] THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CLOSED_IRREDUCIBLE_SEPARATOR) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?c:real^N->bool. c IN components s /\ t SUBSET c` MP_TAC THENL
   [MATCH_MP_TAC EXISTS_COMPONENT_SUPERSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `~(t b) ==> s SUBSET t ==> ~(s b)`)) THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CONNECTED_COMPONENT_MONO THEN
    ASM SET_TAC[]] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`connected_component ((:real^N) DIFF t) a`;
                 `connected_component ((:real^N) DIFF t) b`]
        CONNECTED_FRONTIER_DISJOINT) THEN
  REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT; CONNECTED_COMPONENT_DISJOINT] THEN
  ASM_REWRITE_TAC[IN] THEN ONCE_REWRITE_TAC[CONNECTED_COMPONENT_SYM_EQ] THEN
  SUBGOAL_THEN
   `frontier(connected_component ((:real^N) DIFF t) a) = t /\
    frontier(connected_component ((:real^N) DIFF t) b) = t`
   (fun th -> ASM_REWRITE_TAC[th; SUBSET_REFL]) THEN
  CONJ_TAC THEN MATCH_MP_TAC FRONTIER_MINIMAL_SEPARATING_CLOSED_POINTWISE THENL
   [EXISTS_TAC `b:real^N`; EXISTS_TAC `a:real^N`] THEN
  ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[CONNECTED_COMPONENT_SYM_EQ] THEN
  ASM_SIMP_TAC[] THEN ASM SET_TAC[]);;

let SEPARATION_BY_COMPONENT_CLOSED = prove
 (`!s. closed s /\ ~connected((:real^N) DIFF s)
       ==> ?c. c IN components s /\ ~connected((:real^N) DIFF c)`,
  REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT; IN_DIFF; IN_UNIV] THEN
  MP_TAC SEPARATION_BY_COMPONENT_CLOSED_POINTWISE THEN
  MATCH_MP_TAC MONO_FORALL THEN
  MESON_TAC[REWRITE_RULE[SUBSET] IN_COMPONENTS_SUBSET]);;

let SEPARATION_BY_UNION_CLOSED_POINTWISE = prove
 (`!s t a b. closed s /\ closed t /\ DISJOINT s t /\
             connected_component ((:real^N) DIFF s) a b /\
             connected_component ((:real^N) DIFF t) a b
             ==> connected_component ((:real^N) DIFF (s UNION t)) a b`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN (fun th ->
    ASSUME_TAC th THEN MP_TAC(MATCH_MP CONNECTED_COMPONENT_IN th))) THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~ p`] THEN DISCH_THEN(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] SEPARATION_BY_COMPONENT_CLOSED_POINTWISE)) THEN
  ASM_SIMP_TAC[CLOSED_UNION; NOT_EXISTS_THM] THEN
  X_GEN_TAC `c:real^N->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(c:real^N->bool) SUBSET s \/ c SUBSET t` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_CONNECTED) THEN
    REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `t:real^N->bool`]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    UNDISCH_TAC `connected_component ((:real^N) DIFF s) a b`;
    UNDISCH_TAC `connected_component ((:real^N) DIFF t) a b`] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s b ==> t b`) THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CONNECTED_COMPONENT_MONO THEN
  ASM SET_TAC[]);;

let SEPARATION_BY_UNION_CLOSED = prove
 (`!s t:real^N->bool.
        closed s /\ closed t /\ DISJOINT s t /\
        connected((:real^N) DIFF s) /\
        connected((:real^N) DIFF t)
        ==> connected((:real^N) DIFF (s UNION t))`,
  SIMP_TAC[CONNECTED_IFF_CONNECTED_COMPONENT; IN_DIFF; IN_UNION; IN_UNIV] THEN
  MESON_TAC[SEPARATION_BY_UNION_CLOSED_POINTWISE]);;

let OPEN_UNICOHERENT_UNIV = prove
 (`!s t. open s /\ open t /\ connected s /\ connected t /\
         s UNION t = (:real^N)
         ==> connected(s INTER t)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SET_RULE
   `s INTER t = UNIV DIFF ((UNIV DIFF s) UNION (UNIV DIFF t))`] THEN
  MATCH_MP_TAC SEPARATION_BY_UNION_CLOSED THEN
  ASM_SIMP_TAC[GSYM OPEN_CLOSED; COMPL_COMPL] THEN
  ASM SET_TAC[]);;

let SEPARATION_BY_COMPONENT_OPEN = prove
 (`!s. open s /\ ~connected((:real^N) DIFF s)
       ==> ?c. c IN components s /\ ~connected((:real^N) DIFF c)`,
  let lemma = prove
   (`!s t u. closed s /\ closed t /\ s INTER t = {} /\
             connected u /\ ~(u INTER s = {}) /\ ~(u INTER t = {})
             ==> ?c. c IN components((:real^N) DIFF (s UNION t)) /\
                     ~(c INTER u = {}) /\
                     ~(frontier c INTER s = {}) /\
                     ~(frontier c INTER t = {})`,
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MESON[]
     `(?x. P x /\ Q x /\ R x) <=> ~(!x. P x /\ Q x ==> ~R x)`] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOSED]) THEN
    REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC
     [`s UNION
       UNIONS {c | c IN components((:real^N) DIFF (s UNION t)) /\
                   frontier c SUBSET s}`;
      `t UNION
        UNIONS {c | c IN components((:real^N) DIFF (s UNION t)) /\
                    frontier c SUBSET t}`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL
     [REWRITE_TAC[GSYM FRONTIER_SUBSET_EQ] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s SUBSET t UNION u`) THEN
      MATCH_MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)
          (SPEC_ALL FRONTIER_UNION_SUBSET)) THEN
      ASM_REWRITE_TAC[UNION_SUBSET; FRONTIER_SUBSET_EQ] THEN
      MATCH_MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)
          (SPEC_ALL FRONTIER_UNIONS_SUBSET_CLOSURE)) THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[UNIONS_SUBSET] THEN
      SIMP_TAC[FORALL_IN_GSPEC];
      ALL_TAC]) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `(s UNION t) UNION
                   UNIONS {c | c IN components((:real^N) DIFF (s UNION t)) /\
                   ~(c INTER u = {})}` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPEC `(:real^N) DIFF (s UNION t)` UNIONS_COMPONENTS) THEN
        SET_TAC[];
        MATCH_MP_TAC(SET_RULE
         `c SUBSET d UNION e
          ==> (s UNION t) UNION c SUBSET (s UNION d) UNION (t UNION e)`) THEN
        REWRITE_TAC[GSYM UNIONS_UNION] THEN MATCH_MP_TAC SUBSET_UNIONS THEN
        ONCE_REWRITE_TAC[SUBSET] THEN REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN
        X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`) THEN
        ASM_REWRITE_TAC[DE_MORGAN_THM] THEN
        MATCH_MP_TAC(SET_RULE
         `c SUBSET s UNION t
          ==> c INTER s = {} \/ c INTER t = {}
              ==> c SUBSET s \/ c SUBSET t`) THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP FRONTIER_OF_COMPONENTS_SUBSET) THEN
        REWRITE_TAC[FRONTIER_COMPLEMENT] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
        ASM_SIMP_TAC[FRONTIER_SUBSET_EQ; CLOSED_UNION]];
      MATCH_MP_TAC(SET_RULE
       `c UNION d SUBSET UNIV DIFF (s UNION t) /\ s INTER t = {} /\
        DISJOINT c d
        ==> (s UNION c) INTER (t UNION d) INTER u = {}`) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM UNIONS_UNION] THEN
        GEN_REWRITE_TAC RAND_CONV [UNIONS_COMPONENTS] THEN
        MATCH_MP_TAC SUBSET_UNIONS THEN SET_TAC[];
        MATCH_MP_TAC(SET_RULE
         `(!s. s IN c ==> !t. t IN c' ==> s INTER t = {})
          ==> DISJOINT (UNIONS c) (UNIONS c')`) THEN
        REWRITE_TAC[FORALL_IN_GSPEC] THEN
        MP_TAC(ISPEC `(:real^N) DIFF (s UNION t)` COMPONENTS_NONOVERLAP) THEN
        SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
        X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
        X_GEN_TAC `c':real^N->bool` THEN
        ASM_CASES_TAC `c':real^N->bool = c` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `c SUBSET s ==> s INTER t = {} /\ ~(c = {}) ==> ~(c SUBSET t)`)) THEN
        ASM_REWRITE_TAC[FRONTIER_EQ_EMPTY] THEN
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
        FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
        ASM SET_TAC[]];
      ASM SET_TAC[];
      ASM SET_TAC[]]) in
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[CONNECTED_CLOSED_SET; GSYM OPEN_CLOSED;
               LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `u:real^N->bool`; `(:real^N)`]
          lemma) THEN
  ASM_REWRITE_TAC[CONNECTED_UNIV; COMPL_COMPL] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MP_TAC(ISPEC `c:real^N->bool` CONNECTED_FRONTIER_SIMPLE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[CONNECTED_CLOSED] THEN
  MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `u:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FRONTIER_OF_COMPONENTS_SUBSET) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
  ONCE_REWRITE_TAC[GSYM FRONTIER_COMPLEMENT] THEN
  ASM_REWRITE_TAC[FRONTIER_SUBSET_EQ; GSYM OPEN_CLOSED]);;

let SEPARATION_BY_UNION_OPEN = prove
 (`!s t:real^N->bool.
        open s /\ open t /\ DISJOINT s t /\
        connected((:real^N) DIFF s) /\
        connected((:real^N) DIFF t)
        ==> connected((:real^N) DIFF (s UNION t))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SET_RULE
   `UNIV DIFF (s UNION t) = (UNIV DIFF s) INTER (UNIV DIFF t)`] THEN
  MATCH_MP_TAC(REWRITE_RULE[unicoherent] UNICOHERENT_UNIV) THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ASM SET_TAC[]);;

let CONNECTED_INTER_DISJOINT_OPEN_FRONTIERS = prove
 (`!s t:real^N->bool.
        open s /\ connected s /\ open t /\ connected t /\
        DISJOINT (frontier s) (frontier t)
        ==> connected(s INTER t)`,
  let lemma = prove
   (`~(f = {}) ==> s UNION UNIONS f = UNIONS {s UNION c | c IN f}`,
    REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]) in
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`s:real^N->bool = {}`; `t:real^N->bool = {}`] THEN
  ASM_REWRITE_TAC[INTER_EMPTY; CONNECTED_EMPTY] THEN
  MAP_EVERY ASM_CASES_TAC [`s = (:real^N)`; `t = (:real^N)`] THEN
  ASM_REWRITE_TAC[INTER_UNIV; CONNECTED_UNIV] THEN
  ASM_CASES_TAC `s INTER t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[CONNECTED_EMPTY] THEN
  MP_TAC(ISPECL
   [`s UNION UNIONS {c | c IN components((:real^N) DIFF closure t) /\
                         ~(c INTER s = {})}`;
    `t UNION UNIONS {c | c IN components((:real^N) DIFF closure s) /\
                         ~(c INTER t = {})}`]
   OPEN_UNICOHERENT_UNIV) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MESON_TAC[OPEN_COMPONENTS; closed; CLOSED_CLOSURE];
      MATCH_MP_TAC OPEN_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MESON_TAC[OPEN_COMPONENTS; closed; CLOSED_CLOSURE];
      MATCH_MP_TAC(MESON[]
       `(s = {} \/ ~(s = {}) ==> connected(u UNION UNIONS s))
        ==> connected(u UNION UNIONS s)`) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[UNION_EMPTY; UNIONS_0] THEN
      ASM_SIMP_TAC[lemma] THEN MATCH_MP_TAC CONNECTED_UNIONS THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[CONNECTED_UNION; IN_COMPONENTS_CONNECTED; UNION_COMM];
        ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ ~(s = {}) ==> ~(t = {})`) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_INTERS] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; SUBSET_UNION];
      MATCH_MP_TAC(MESON[]
       `(s = {} \/ ~(s = {}) ==> connected(u UNION UNIONS s))
        ==> connected(u UNION UNIONS s)`) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[UNION_EMPTY; UNIONS_0] THEN
      ASM_SIMP_TAC[lemma] THEN MATCH_MP_TAC CONNECTED_UNIONS THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[CONNECTED_UNION; IN_COMPONENTS_CONNECTED; UNION_COMM];
        ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ ~(s = {}) ==> ~(t = {})`) THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_INTERS] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; SUBSET_UNION];
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
      ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(x:real^N) IN t` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o MATCH_MP (SET_RULE
       `DISJOINT s t ==> !x. ~(x IN s) \/ ~(x IN t)`)) THEN
      ASM_SIMP_TAC[frontier; INTERIOR_OPEN; IN_DIFF] THEN STRIP_TAC THENL
       [SUBGOAL_THEN `x IN UNIONS(components((:real^N) DIFF closure s))`
        MP_TAC THENL
         [ASM_REWRITE_TAC[GSYM UNIONS_COMPONENTS; IN_DIFF; IN_UNIV];
          ALL_TAC] THEN
        REWRITE_TAC[IN_UNIONS] THEN
        DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
        ASM_CASES_TAC `c INTER t:real^N->bool = {}` THENL
         [ALL_TAC; ASM_MESON_TAC[]] THEN
        SUBGOAL_THEN `c INTER closure(t:real^N->bool) = {}` ASSUME_TAC THENL
         [ASM_MESON_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY; OPEN_COMPONENTS;
                        closed; CLOSED_CLOSURE];
          ALL_TAC] THEN
        SUBGOAL_THEN `x IN UNIONS(components((:real^N) DIFF closure t))`
        MP_TAC THENL
         [ASM_REWRITE_TAC[GSYM UNIONS_COMPONENTS; IN_DIFF; IN_UNIV] THEN
          ASM SET_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[IN_UNIONS] THEN
        DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool` STRIP_ASSUME_TAC) THEN
        ASM_CASES_TAC `d INTER s:real^N->bool = {}` THENL
         [ALL_TAC; ASM_MESON_TAC[]] THEN
        SUBGOAL_THEN `d INTER closure(s:real^N->bool) = {}` ASSUME_TAC THENL
         [ASM_MESON_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY; OPEN_COMPONENTS;
                        closed; CLOSED_CLOSURE];
          ALL_TAC];
        SUBGOAL_THEN `x IN UNIONS(components((:real^N) DIFF closure t))`
        MP_TAC THENL
         [ASM_REWRITE_TAC[GSYM UNIONS_COMPONENTS; IN_DIFF; IN_UNIV];
          ALL_TAC] THEN
        REWRITE_TAC[IN_UNIONS] THEN
        DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool` STRIP_ASSUME_TAC) THEN
        ASM_CASES_TAC `d INTER s:real^N->bool = {}` THENL
         [ALL_TAC; ASM_MESON_TAC[]] THEN
        SUBGOAL_THEN `d INTER closure(s:real^N->bool) = {}` ASSUME_TAC THENL
         [ASM_MESON_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY; OPEN_COMPONENTS;
                        closed; CLOSED_CLOSURE];
          ALL_TAC] THEN
        SUBGOAL_THEN `x IN UNIONS(components((:real^N) DIFF closure s))`
        MP_TAC THENL
         [ASM_REWRITE_TAC[GSYM UNIONS_COMPONENTS; IN_DIFF; IN_UNIV] THEN
          ASM SET_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[IN_UNIONS] THEN
        DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
        ASM_CASES_TAC `c INTER t:real^N->bool = {}` THENL
         [ALL_TAC; ASM_MESON_TAC[]] THEN
        SUBGOAL_THEN `c INTER closure(t:real^N->bool) = {}` ASSUME_TAC THENL
         [ASM_MESON_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY; OPEN_COMPONENTS;
                        closed; CLOSED_CLOSURE];
          ALL_TAC]] THEN
     (FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `DISJOINT s t ==> !c d. ~(c = {}) /\ c SUBSET s /\ d SUBSET t /\ c = d
                               ==> p`)) THEN
      MAP_EVERY EXISTS_TAC
       [`frontier c:real^N->bool`; `frontier d:real^N->bool`] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[FRONTIER_EQ_EMPTY; DE_MORGAN_THM] THEN
        ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; IN_COMPONENTS_SUBSET;
                      SET_RULE `s SUBSET UNIV DIFF t /\ s = UNIV ==> t = {}`;
                      CLOSURE_EQ_EMPTY];
        ASM_MESON_TAC[FRONTIER_OF_COMPONENTS_SUBSET;FRONTIER_COMPLEMENT;
                      FRONTIER_CLOSURE_SUBSET; SUBSET_TRANS];
        ASM_MESON_TAC[FRONTIER_OF_COMPONENTS_SUBSET;FRONTIER_COMPLEMENT;
                      FRONTIER_CLOSURE_SUBSET; SUBSET_TRANS];
        AP_TERM_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
        MATCH_MP_TAC COMPONENTS_MAXIMAL THENL
         [EXISTS_TAC `(:real^N) DIFF closure t`;
          EXISTS_TAC `(:real^N) DIFF closure s`] THEN
        ASM_REWRITE_TAC[] THEN
        (CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
         ASM SET_TAC[]])])];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `s INTER t' = {} /\ t INTER s' = {} /\ s' INTER t' = {}
      ==> (s UNION s') INTER (t UNION t') = s INTER t`) THEN
    REWRITE_TAC[INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC;
                UNIONS_SUBSET] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `d:real^N->bool` THENL
     [MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN
      MP_TAC(ISPECL [`(:real^N) DIFF closure s`; `d:real^N->bool`]
        IN_COMPONENTS_SUBSET) THEN
      SET_TAC[];
      MP_TAC(ISPEC `t:real^N->bool` CLOSURE_SUBSET) THEN
      MP_TAC(ISPECL [`(:real^N) DIFF closure t`; `d:real^N->bool`]
        IN_COMPONENTS_SUBSET) THEN
      SET_TAC[];
      STRIP_TAC THEN X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `DISJOINT s t
      ==> !c d. c SUBSET s /\ d SUBSET t /\ ~(c INTER d = {}) ==> F`)) THEN
    MAP_EVERY EXISTS_TAC
     [`frontier c:real^N->bool`; `frontier d:real^N->bool`] THEN
    REPEAT(CONJ_TAC THENL
     [ASM_MESON_TAC[FRONTIER_OF_COMPONENTS_SUBSET;FRONTIER_COMPLEMENT;
                      FRONTIER_CLOSURE_SUBSET; SUBSET_TRANS]; ALL_TAC]) THEN
    MATCH_MP_TAC CONNECTED_INTER_FRONTIER THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_FRONTIER_COMPONENT_COMPLEMENT THEN
      EXISTS_TAC `closure s:real^N->bool` THEN
      ASM_MESON_TAC[CONNECTED_CLOSURE];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[SET_RULE `c DIFF d = c INTER (UNIV DIFF d)`] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN CONJ_TAC THEN
    MATCH_MP_TAC CONNECTED_INTER_FRONTIER THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      ALL_TAC;
      MATCH_MP_TAC COMPONENT_COMPLEMENT_CONNECTED THEN
      EXISTS_TAC `closure t:real^N->bool` THEN
      ASM_SIMP_TAC[CONNECTED_UNIV; SUBSET_UNIV; CONNECTED_CLOSURE];
      ALL_TAC;
      ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
    MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN
    MP_TAC(ISPEC `t:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]);;

let NONSEPARATION_BY_COMPONENT_EQ = prove
 (`!s. (open s \/ closed s)
       ==> ((!c. c IN components s ==> connected((:real^N) DIFF c)) <=>
            connected((:real^N) DIFF s))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[SEPARATION_BY_COMPONENT_OPEN];
    ALL_TAC;
    ASM_MESON_TAC[SEPARATION_BY_COMPONENT_CLOSED];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPONENT_COMPLEMENT_CONNECTED THEN
  EXISTS_TAC `(:real^N) DIFF s` THEN
  ASM_REWRITE_TAC[CONNECTED_UNIV; SUBSET_UNIV;
                  COMPL_COMPL]);;

let CONNECTED_COMMON_FRONTIER_DOMAINS = prove
 (`!s t c:real^N->bool.
        open s /\ connected s /\
        open t /\ connected t /\
        ~(s = t) /\ frontier s = c /\ frontier t = c
        ==> connected c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`]
        COMMON_FRONTIER_DOMAINS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`]
    CONNECTED_FRONTIER_DISJOINT) THEN
  ASM_REWRITE_TAC[SUBSET_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The frontier of an ANR is locally connected (this is only this late       *)
(* since it's handy to use basics about unicoherence).                       *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_CONNECTED_FRONTIER_ANR = prove
 (`!s:real^N->bool.
        compact s /\ ANR s ==> locally connected (frontier s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LOCALLY_CONNECTED_IM_KLEINEN] THEN
  MAP_EVERY X_GEN_TAC [`v:real^N->bool`; `p:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_CONTAINS_CBALL]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `p:real^N`)) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `(:real^N)`]
        ANR_IMP_NEIGHBOURHOOD_RETRACT) THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; GSYM CLOSED_IN] THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of]) THEN
  REWRITE_TAC[retraction; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real^N->real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `frontier(s:real^N->bool) SUBSET s` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FRONTIER_SUBSET_EQ; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N) IN s` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. &0 < d /\ d < e /\
        {x + l:real^N | x IN s /\ l IN cball(vec 0,d)} SUBSET u /\
        !y:real^N. dist(p,y) <= d ==> dist(p,r y) <= e`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `?d. &0 < d /\ {x + l:real^N | x IN s /\ l IN cball(vec 0,d)} SUBSET u`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `s:real^N->bool = {}` THEN
      ASM_REWRITE_TAC[SET_RULE `{f x y | x IN {} /\ P y} SUBSET u`] THENL
       [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
      ASM_CASES_TAC `u = (:real^N)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THENL
       [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
      EXISTS_TAC `setdist(s,(:real^N) DIFF u) / &2` THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_HALF; SETDIST_POS_LT] THEN
        ASM_SIMP_TAC[SETDIST_EQ_0_COMPACT_CLOSED; GSYM OPEN_CLOSED] THEN
        ASM SET_TAC[];
        REWRITE_TAC[REAL_HALF; SUBSET; FORALL_IN_GSPEC] THEN DISCH_TAC THEN
        MAP_EVERY X_GEN_TAC [`x:real^N`; `l:real^N`] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[IN_CBALL_0] THEN
        DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
         `&0 < s /\ s <= e ==> ~(e <= s / &2)`) THEN
        ASM_REWRITE_TAC[] THEN
        SUBST1_TAC(NORM_ARITH `norm(l:real^N) = dist(x,x + l)`) THEN
        MATCH_MP_TAC SETDIST_LE_DIST THEN ASM SET_TAC[]];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_on]) THEN
      DISCH_THEN(MP_TAC o SPEC `p:real^N`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(MP_TAC o SPEC `e:real`)] THEN
      ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `d':real` THEN STRIP_TAC THEN
      EXISTS_TAC `min (e / &2) (min d (d' / &2))` THEN
      ASM_SIMP_TAC[REAL_LT_MIN; REAL_LE_MIN; REAL_HALF; CBALL_MIN_INTER] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[CONJ_ASSOC]] THEN
      X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      UNDISCH_TAC
       `{x + l:real^N | x IN s /\ l IN cball(vec 0,d)} SUBSET u` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[IN_ELIM_THM; IN_CBALL_0] THEN
      MAP_EVERY EXISTS_TAC [`p:real^N`; `y - p:real^N`] THEN
      ASM_REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] (GSYM dist)] THEN
      CONV_TAC VECTOR_ARITH];
    ABBREV_TAC `sd = {x + l:real^N | x IN s /\ l IN cball(vec 0,d)}`] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET interior sd` ASSUME_TAC THENL
   [TRANS_TAC SUBSET_TRANS
     `{x + l:real^N | x IN s /\ l IN ball(vec 0,d)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `vec 0 IN t /\ (!x:real^N. f x (vec 0) = x)
        ==> s SUBSET {f x y | x IN s /\ y IN t}`) THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL; VECTOR_ADD_RID];
      SIMP_TAC[INTERIOR_MAXIMAL_EQ; OPEN_SUMS; OPEN_BALL] THEN
      EXPAND_TAC "sd" THEN REWRITE_TAC[GSYM BALL_UNION_SPHERE] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET sd` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS; INTERIOR_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(sd:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "sd" THEN ASM_SIMP_TAC[COMPACT_SUMS; COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?k. &0 < k /\ k <= d /\
        (!x. ~(x IN u) ==> k <= dist(p,x)) /\
        (!c x. c IN components(cball(p,d) DIFF s) /\
               ~(p IN closure c) /\ x IN c
               ==> k <= dist(p:real^N,x))`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [open_def]) THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[REAL_NOT_LT] THEN STRIP_TAC THEN
    EXISTS_TAC
     `inf (k INSERT (d / &2) INSERT
           IMAGE (\c. setdist({p:real^N},c))
                 {c | c IN components (cball (p,d) DIFF s) /\
                      ~(closure c INTER cball (p,d / &2) = {}) /\
                      ~(p IN closure c)})` THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `p:real^N`; `d / &2`; `d:real`]
      FINITE_ANR_COMPLEMENT_COMPONENTS_CONCENTRIC) THEN
    ASM_REWRITE_TAC[REAL_ARITH `e / &2 < e <=> &0 < e`] THEN
    DISCH_TAC THEN
    ONCE_REWRITE_TAC[SET_RULE
      `{x | P x /\ Q x /\ R x} = {x | x IN {y | P y /\ Q y} /\ R x}`] THEN
    ASM_SIMP_TAC[REAL_LT_INF_FINITE; NOT_INSERT_EMPTY; FINITE_INSERT;
                 FINITE_IMAGE; FINITE_RESTRICT; REAL_INF_LE_FINITE] THEN
    REWRITE_TAC[EXISTS_IN_INSERT; FORALL_IN_INSERT] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; EXISTS_IN_GSPEC] THEN
    ASM_REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC; REAL_HALF] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `c:real^N->bool` THEN REPEAT DISCH_TAC THEN
      REWRITE_TAC[SETDIST_POS_LT; SETDIST_EQ_0_SING] THEN
      ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
      DISJ2_TAC THEN DISJ1_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[DIST_SYM];
      MAP_EVERY X_GEN_TAC [`c:real^N->bool`; `x:real^N`] THEN
      REPEAT DISCH_TAC THEN DISJ2_TAC THEN
      ASM_CASES_TAC `closure c INTER cball(p:real^N,d / &2) = {}` THENL
       [DISJ1_TAC THEN TRANS_TAC REAL_LE_TRANS `setdist({p:real^N},c)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_SETDIST THEN
          FIRST_ASSUM(ASSUME_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
          ASM_REWRITE_TAC[NOT_INSERT_EMPTY; IMP_CONJ; IN_SING] THEN
          REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
          X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o
            GEN_REWRITE_RULE I [EXTENSION]) THEN
          ASM_SIMP_TAC[IN_INTER; CLOSURE_INC; NOT_IN_EMPTY; IN_CBALL] THEN
          CONV_TAC NORM_ARITH;
          MATCH_MP_TAC SETDIST_LE_DIST THEN ASM_REWRITE_TAC[IN_SING]];
        DISJ2_TAC THEN EXISTS_TAC `c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SETDIST_LE_DIST THEN ASM_REWRITE_TAC[IN_SING]]];
    ALL_TAC] THEN
  EXISTS_TAC `frontier s INTER ball(p:real^N,k)` THEN
  SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL; IN_INTER] THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    SUBGOAL_THEN `ball(p:real^N,k) SUBSET cball(p,e)` MP_TAC THENL
     [REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN ASM_REAL_ARITH_TAC;
      ASM SET_TAC[]];
    X_GEN_TAC `q:real^N` THEN REWRITE_TAC[IN_BALL] THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `?c. c IN components(cball(p:real^N,d) DIFF s) /\ q IN closure c`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `q IN closure
       (UNIONS {c | c IN components (cball(p:real^N,d) DIFF s) /\
                    ~(closure c INTER cball(p,(k + dist (p,q)) / &2) = {})}
        UNION
        UNIONS {c | c IN components (cball(p,d) DIFF s) /\
                    closure c INTER cball(p,(k + dist (p,q)) / &2) = {}})`
    MP_TAC THENL
     [REWRITE_TAC[GSYM UNIONS_UNION; GSYM UNIONS_COMPONENTS; SET_RULE
       `{x | x IN s /\ ~P x} UNION {x | x IN s /\ P x} = s`] THEN
      MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ x IN s ==> x IN t`) THEN
      EXISTS_TAC `closure(ball(p:real^N,d) DIFF s)` THEN
      SIMP_TAC[SUBSET_CLOSURE; BALL_SUBSET_CBALL; SET_RULE
        `s SUBSET t ==> s DIFF c SUBSET t DIFF c`] THEN
      ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
      W(MP_TAC o PART_MATCH (rand o rand) OPEN_INTER_CLOSURE_SUBSET o
        rand o snd) THEN
      REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC(SET_RULE
       `x IN s ==> s SUBSET t ==> x IN t`) THEN
      ASM_REWRITE_TAC[IN_BALL; IN_INTER] THEN
      ASM_REWRITE_TAC[CLOSURE_UNION_FRONTIER; FRONTIER_COMPLEMENT;
                      IN_UNION] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[CLOSURE_UNION; IN_UNION] THEN
      MATCH_MP_TAC(TAUT `~q /\ (p ==> r) ==> p \/ q ==> r`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `!t. ~(x IN t) /\ s SUBSET t ==> ~(x IN s)`) THEN
        EXISTS_TAC `(:real^N) DIFF ball(p,(k + dist(p,q)) / &2)` THEN
        ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_BALL] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC CLOSURE_MINIMAL THEN
        REWRITE_TAC[GSYM OPEN_CLOSED; OPEN_BALL] THEN
        REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
        X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
        `d INTER cball(x:real^N,r) = {} ==> ball(x,r) SUBSET cball(x,r)
                ==> ball(x,r) INTER d = {}`)) THEN
        SIMP_TAC[BALL_SUBSET_CBALL; OPEN_INTER_CLOSURE_EQ_EMPTY;
                 OPEN_BALL] THEN
        SET_TAC[];
        MP_TAC(ISPECL
         [`s:real^N->bool`; `p:real^N`;
          `(k + dist(p:real^N,q)) / &2`; `d:real`]
          FINITE_ANR_COMPLEMENT_COMPONENTS_CONCENTRIC) THEN
        ASM_REWRITE_TAC[] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[CLOSURE_UNIONS]] THEN
        DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
        MESON_TAC[]]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`) THEN
  ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT; GSYM IN_BALL] THEN
    REWRITE_TAC[SET_RULE `~(x IN s) <=> x IN (UNIV DIFF s)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
     (REWRITE_RULE[CONJ_ASSOC] FORALL_IN_CLOSURE))) THEN
    REWRITE_TAC[CONTINUOUS_ON_ID; GSYM OPEN_CLOSED; OPEN_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `q:real^N`) THEN
    ASM_REWRITE_TAC[IN_UNIV; IN_DIFF; IN_BALL];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `(p:real^N) IN frontier c /\ (q:real^N) IN frontier c`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CLOSURE_UNION_FRONTIER]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?g. path g /\ pathstart g:real^N = p /\ pathfinish g = q /\
        (!t. t IN interval(vec 0,vec 1) ==> g t IN c)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `c:real^N->bool`]
         ACCESSIBLE_FRONTIER_ANR_INTER_COMPLEMENT_COMPONENT) THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `cball(p:real^N,d)`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th ->
        MP_TAC(SPEC `q:real^N` th) THEN
        MP_TAC(SPEC `p:real^N` th)) THEN
    ASM_REWRITE_TAC[INTERIOR_CBALL; CENTRE_IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `g1:real^1->real^N` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_BALL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g2:real^1->real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `path_component c (pathstart g1:real^N) (pathstart g2)`
    MP_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand)
        PATH_COMPONENT_EQ_CONNECTED_COMPONENT o rator o snd) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
        EXISTS_TAC `cball(p:real^N,d) DIFF s` THEN
        CONJ_TAC THENL
         [ALL_TAC;
          MATCH_MP_TAC OPEN_IN_COMPONENTS_LOCALLY_CONNECTED THEN
          ASM_REWRITE_TAC[]] THEN
        MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
        EXISTS_TAC `cball(p:real^N,d)` THEN
        ASM_SIMP_TAC[OPEN_IN_DIFF_CLOSED; COMPACT_IMP_CLOSED] THEN
        SIMP_TAC[CONVEX_IMP_LOCALLY_PATH_CONNECTED; CONVEX_CBALL;
                 CONVEX_IMP_LOCALLY_CONNECTED];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[connected_component] THEN
        EXISTS_TAC `c:real^N->bool` THEN REWRITE_TAC[SUBSET_REFL] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
        REWRITE_TAC[pathstart] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_DELETE; ENDS_IN_UNIT_INTERVAL; VEC_EQ; ARITH_EQ]];
      REWRITE_TAC[path_component] THEN
      DISCH_THEN(X_CHOOSE_THEN `g3:real^1->real^N` STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC `reversepath g1 ++ g3 ++ g2:real^1->real^N` THEN
    ASM_SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
    ASM_SIMP_TAC[PATH_REVERSEPATH; ARC_IMP_PATH] THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    STRIP_TAC THEN REWRITE_TAC[joinpaths; reversepath] THEN
    REWRITE_TAC[DROP_SUB; DROP_VEC; DROP_CMUL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path_image; SUBSET; FORALL_IN_IMAGE]) THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_DELETE; GSYM DROP_EQ; IN_INTERVAL_1; DROP_VEC;
                DROP_SUB; DROP_CMUL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image g SUBSET cball(p:real^N,d)` ASSUME_TAC THENL
   [TRANS_TAC SUBSET_TRANS `closure c:real^N->bool` THEN CONJ_TAC THENL
     [REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN
      SIMP_TAC[CLOSED_OPEN_INTERVAL_1; DROP_VEC; REAL_POS] THEN
      REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[CLOSURE_INC; pathstart; pathfinish];
      MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_CBALL] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`cball(p:real^N,e) INTER s`;
    `IMAGE (r:real^N->real^N) (path_image g)`]
   EXISTS_COMPONENT_SUPERSET) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET_INTER] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[GSYM IN_CBALL] THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE r u SUBSET s ==> t SUBSET u ==> IMAGE r t SUBSET s`));
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `p:real^N` THEN ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[CONNECTED_PATH_IMAGE] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
           (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET))] THEN
    TRANS_TAC SUBSET_TRANS `sd:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC SUBSET_TRANS `cball(p:real^N,d)` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "sd" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_CBALL] THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`p:real^N`; `y - p:real^N`] THEN
    ASM_REWRITE_TAC[DIST_0] THEN
    ASM_REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] (GSYM dist)] THEN
    CONV_TAC VECTOR_ARITH;
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC
   `h = connected_component (cball(p:real^N,e) DIFF f) (g(lift(&1 / &2)))` THEN
  MP_TAC(ISPEC `cball(p:real^N,e)` CONVEX_IMP_UNICOHERENT) THEN
  REWRITE_TAC[CONVEX_CBALL; unicoherent] THEN DISCH_THEN(MP_TAC o SPECL
   [`cball(p:real^N,e) DIFF h:real^N->bool`; `closure h:real^N->bool`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPONENT_COMPLEMENT_CONNECTED THEN
      EXISTS_TAC `f:real^N->bool` THEN REWRITE_TAC[CONNECTED_CBALL] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
        ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET_INTER];
        EXPAND_TAC "h" THEN REWRITE_TAC[components; IN_ELIM_THM] THEN
        EXISTS_TAC `g(lift(&1 / &2)):real^N` THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `lift(&1 / &2)`) THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
        SUBGOAL_THEN `cball(p:real^N,d) SUBSET cball(p,e)` MP_TAC THENL
         [ASM_REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN ASM_REAL_ARITH_TAC;
          ASM SET_TAC[]]];
      MATCH_MP_TAC CONNECTED_CLOSURE THEN EXPAND_TAC "h" THEN
      REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT];
      MATCH_MP_TAC(SET_RULE
       `h SUBSET c /\ c SUBSET b ==> (b DIFF h) UNION c = b`) THEN
      REWRITE_TAC[CLOSURE_SUBSET] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
      REWRITE_TAC[CLOSED_CBALL] THEN EXPAND_TAC "h" THEN
      TRANS_TAC SUBSET_TRANS `cball(p:real^N,e) DIFF f` THEN
      REWRITE_TAC[CONNECTED_COMPONENT_SUBSET] THEN SET_TAC[];
      MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL] THEN
      MATCH_MP_TAC OPEN_IN_TRANS THEN
      EXISTS_TAC `cball(p:real^N,e) DIFF f` THEN CONJ_TAC THENL
       [EXPAND_TAC "h" THEN
        MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENT_LOCALLY_CONNECTED THEN
        MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
        EXISTS_TAC `cball(p:real^N,e)` THEN
        SIMP_TAC[CONVEX_CBALL; CONVEX_IMP_LOCALLY_CONNECTED];
        ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
      TRANS_TAC CLOSED_IN_TRANS `cball(p:real^N,e) INTER s` THEN
      ASM_SIMP_TAC[CLOSED_IN_CLOSED_INTER; COMPACT_IMP_CLOSED] THEN
      ASM_SIMP_TAC[CLOSED_IN_COMPONENT];
      MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_CBALL] THEN
      EXPAND_TAC "h" THEN
      TRANS_TAC SUBSET_TRANS `cball(p:real^N,e) DIFF f` THEN
      REWRITE_TAC[CONNECTED_COMPONENT_SUBSET] THEN SET_TAC[]];
    ABBREV_TAC `j = (cball(p:real^N,e) DIFF h) INTER closure h` THEN
    DISCH_TAC] THEN
  EXISTS_TAC `j:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [TRANS_TAC SUBSET_TRANS `cball(p:real^N,e) INTER frontier s` THEN
    ASM_REWRITE_TAC[SUBSET_INTER] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "j" THEN REWRITE_TAC[SUBSET] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF; IN_INTER] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN f` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`cball(p:real^N,e) DIFF f`; `g(lift(&1 / &2)):real^N`]
        CLOSED_IN_CONNECTED_COMPONENT) THEN
      ASM_REWRITE_TAC[CLOSED_IN_INTER_CLOSURE] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[frontier; IN_DIFF] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC CLOSURE_INC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR_CBALL]) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `cball(p:real^N,e) INTER ball(x,r) SUBSET f` ASSUME_TAC THENL
     [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
      EXISTS_TAC `cball(p:real^N,e) INTER s` THEN
      ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTER;
                   CONVEX_BALL; CONVEX_CBALL] THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`x:real^N`; `r:real`] BALL_SUBSET_CBALL) THEN
        ASM SET_TAC[];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSURE_APPROACHABLE]) THEN
      DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
      ASM_REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] (GSYM IN_BALL)] THEN
      MP_TAC(ISPECL [`cball(p:real^N,e) DIFF f`; `g(lift(&1 / &2)):real^N`]
        CONNECTED_COMPONENT_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    SUBGOAL_THEN
     `!t. t IN closure(interval(vec 0,vec 1))
          ==> (g:real^1->real^N) t IN closure h`
    MP_TAC THENL
     [MATCH_MP_TAC FORALL_IN_CLOSURE THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
      SIMP_TAC[CLOSURE_OPEN_INTERVAL; UNIT_INTERVAL_NONEMPTY] THEN
      ASM_REWRITE_TAC[GSYM path] THEN
      REWRITE_TAC[SET_RULE
       `(!x. x IN s ==> f x IN t) <=> IMAGE f s SUBSET t`] THEN
      TRANS_TAC SUBSET_TRANS `h:real^N->bool` THEN
      REWRITE_TAC[CLOSURE_SUBSET] THEN EXPAND_TAC "h" THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[CONNECTED_INTERVAL] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        ASM_REWRITE_TAC[GSYM path; INTERVAL_OPEN_SUBSET_CLOSED];
        REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
        SUBGOAL_THEN `cball(p:real^N,d) SUBSET cball(p,e)` MP_TAC THENL
         [ASM_REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN ASM_REAL_ARITH_TAC;
          ASM SET_TAC[]]];
        SIMP_TAC[CLOSURE_OPEN_INTERVAL; UNIT_INTERVAL_NONEMPTY] THEN
        DISCH_THEN(fun th ->
          MP_TAC(SPEC `vec 1:real^1` th) THEN
          MP_TAC(SPEC `vec 0:real^1` th)) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
        ASM_REWRITE_TAC[IMP_IMP; ENDS_IN_UNIT_INTERVAL] THEN
        EXPAND_TAC "j" THEN MATCH_MP_TAC MONO_AND THEN
        SIMP_TAC[IN_INTER] THEN
        CONJ_TAC THEN DISCH_TAC THEN REWRITE_TAC[IN_DIFF] THEN
        (MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
          [REWRITE_TAC[IN_CBALL; DIST_REFL] THEN ASM_REAL_ARITH_TAC;
           DISCH_TAC]) THEN
        EXPAND_TAC "h" THEN
        MATCH_MP_TAC(MESON[CONNECTED_COMPONENT_SUBSET; SUBSET]
         `~(p IN s) ==> ~(p IN connected_component s r)`) THEN
        ASM_REWRITE_TAC[IN_DIFF] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
        MATCH_MP_TAC(SET_RULE `r x = x /\ x IN s ==> x IN IMAGE r s`) THEN
        (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
        ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE;
                      pathstart; pathfinish]]]);;

(* ------------------------------------------------------------------------- *)
(* Another interesting equivalent of an inessential mapping into C-{0}       *)
(* ------------------------------------------------------------------------- *)

let INESSENTIAL_EQ_EXTENSIBLE = prove
 (`!f s.
   closed s
   ==> ((?a. homotopic_with (\h. T)
              (subtopology euclidean s,
               subtopology euclidean ((:complex) DIFF {Cx(&0)}))
              f (\t. a)) <=>
        (?g. g continuous_on (:real^N) /\
             (!x. x IN s ==> g x = f x) /\ (!x. ~(g x = Cx(&0)))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `a:complex`) THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THENL
     [EXISTS_TAC `\x:real^N. Cx(&1)` THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; NOT_IN_EMPTY] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
    FIRST_ASSUM(MP_TAC o
      SPEC `(:real^N)` o
      MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        (REWRITE_RULE[CONJ_ASSOC] BORSUK_HOMOTOPY_EXTENSION)) o
      GEN_REWRITE_RULE I [HOMOTOPIC_WITH_SYM]) THEN
    ASM_REWRITE_TAC[GSYM CLOSED_IN; SUBTOPOLOGY_UNIV] THEN
    SIMP_TAC[OPEN_IMP_ANR; OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN
    ASM_SIMP_TAC[CLOSED_UNIV; CONTINUOUS_ON_CONST] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
    ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->complex` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[INESSENTIAL_EQ_CONTINUOUS_LOGARITHM] THEN
    MP_TAC(ISPECL [`vec 0:real^N`; `&1`] HOMEOMORPHIC_BALL_UNIV) THEN
    REWRITE_TAC[REAL_LT_01; homeomorphic; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`h:real^N->real^N`; `k:real^N->real^N`] THEN
    REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(g:real^N->complex) o (h:real^N->real^N)`;
                   `vec 0:real^N`; `&1`] CONTINUOUS_LOGARITHM_ON_BALL) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_COMPOSE; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:real^N->complex` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(j:real^N->complex) o (k:real^N->real^N)` THEN
    ASM_SIMP_TAC[o_THM] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Another simple case where sphere maps are nullhomotopic.                  *)
(* ------------------------------------------------------------------------- *)

let INESSENTIAL_SPHEREMAP_2 = prove
 (`!f:real^M->real^N a r b s.
        2 < dimindex(:M) /\ dimindex(:N) = 2 /\
        f continuous_on sphere(a,r) /\
        IMAGE f (sphere(a,r)) SUBSET (sphere(b,s))
        ==> ?c. homotopic_with (\z. T)
                  (subtopology euclidean (sphere(a,r)),
                   subtopology euclidean (sphere(b,s))) f (\x. c)`,
  let lemma = prove
   (`!f:real^N->real^2 a r.
          2 < dimindex(:N) /\
          f continuous_on sphere(a,r) /\
          IMAGE f (sphere(a,r)) SUBSET (sphere(vec 0,&1))
          ==> ?c. homotopic_with (\z. T)
                   (subtopology euclidean (sphere(a,r)),
                    subtopology euclidean (sphere(vec 0,&1)))
                   f (\x. c)`,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[INESSENTIAL_EQ_CONTINUOUS_LOGARITHM_CIRCLE] THEN
    MP_TAC(ISPECL [`f:real^N->real^2`; `sphere(a:real^N,r)`]
          CONTINUOUS_LOGARITHM_ON_SIMPLY_CONNECTED) THEN
    ASM_SIMP_TAC[SIMPLY_CONNECTED_SPHERE_EQ;
                 LOCALLY_PATH_CONNECTED_SPHERE] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `3 <= n <=> 2 < n`] THEN FIRST_X_ASSUM
       (MATCH_MP_TAC o MATCH_MP (SET_RULE
          `IMAGE f s SUBSET t ==> (!x. P x ==> ~(x IN t))
          ==> !x. x IN s ==> ~P(f x)`)) THEN
      SIMP_TAC[COMPLEX_NORM_0; IN_SPHERE_0] THEN REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `Im o (g:real^N->real^2)` THEN CONJ_TAC THENL
       [REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        ASM_REWRITE_TAC[CONTINUOUS_ON_CX_IM];
        X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
        ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
        REWRITE_TAC[o_DEF; COMPLEX_EQ; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
        REWRITE_TAC[FORALL_IN_IMAGE] THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
        ASM_SIMP_TAC[IN_SPHERE_0; NORM_CEXP; REAL_EXP_EQ_1] THEN
        REAL_ARITH_TAC]])
  and hslemma = prove
   (`!a:real^M r b:real^N s.
        dimindex(:M) = dimindex(:N) /\ &0 < r /\ &0 < s
        ==> (sphere(a,r) homeomorphic sphere(b,s))`,
    REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th ->
      let t = `?a:real^M b:real^N. ~(sphere(a,r) homeomorphic sphere(b,s))` in
      MP_TAC(DISCH t (GEOM_EQUAL_DIMENSION_RULE th (ASSUME t)))) THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_SPHERES] THEN MESON_TAC[]) in
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s <= &0` THEN
  ASM_SIMP_TAC[NULLHOMOTOPIC_INTO_CONTRACTIBLE; CONTRACTIBLE_SPHERE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  SUBGOAL_THEN
   `(sphere(b:real^N,s)) homeomorphic (sphere(vec 0:real^2,&1))`
  MP_TAC THENL
   [ASM_SIMP_TAC[hslemma; REAL_LT_01; DIMINDEX_2];
    REWRITE_TAC[homeomorphic; LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`h:real^N->real^2`; `k:real^2->real^N`] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`(h:real^N->real^2) o (f:real^M->real^N)`;
    `a:real^M`; `r:real`] lemma) THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE; ASM SET_TAC[]] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    DISCH_THEN(X_CHOOSE_THEN `c:real^2` (fun th ->
      EXISTS_TAC `(k:real^2->real^N) c` THEN MP_TAC th)) THEN
    DISCH_THEN(MP_TAC o ISPEC `k:real^2->real^N` o MATCH_MP
     (ONCE_REWRITE_RULE[IMP_CONJ] HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT)) THEN
    DISCH_THEN(MP_TAC o SPEC `sphere(b:real^N,s)`) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
    REWRITE_TAC[o_DEF] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Janiszewski's theorem.                                                    *)
(* ------------------------------------------------------------------------- *)

let JANISZEWSKI = prove
 (`!s t a b:real^2.
        compact s /\ closed t /\ connected(s INTER t) /\
        connected_component ((:real^2) DIFF s) a b /\
        connected_component ((:real^2) DIFF t) a b
        ==> connected_component ((:real^2) DIFF (s UNION t)) a b`,
  let lemma = prove
   (`!s t a b:real^2.
          compact s /\ compact t /\ connected(s INTER t) /\
          connected_component ((:real^2) DIFF s) a b /\
          connected_component ((:real^2) DIFF t) a b
          ==> connected_component ((:real^2) DIFF (s UNION t)) a b`,
    REPEAT GEN_TAC THEN
    REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN(MP_TAC o
      MATCH_MP CONNECTED_COMPONENT_IN)) THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV] THEN STRIP_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM BORSUK_MAPS_HOMOTOPIC_IN_CONNECTED_COMPONENT_EQ;
                 DIMINDEX_2; LE_REFL; COMPACT_UNION; IN_UNION] THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_CIRCLEMAPS_DIV] THEN
    REWRITE_TAC[INESSENTIAL_EQ_CONTINUOUS_LOGARITHM_CIRCLE] THEN
    ASM_SIMP_TAC[BORSUK_MAP_INTO_SPHERE; CONTINUOUS_ON_BORSUK_MAP;
                 IN_UNION] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `g:real^2->real` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `h:real^2->real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `closed_in (subtopology euclidean (s UNION t)) s /\
      closed_in (subtopology euclidean (s UNION t)) (t:real^2->bool)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[CLOSED_IN_CLOSED] THEN CONJ_TAC THENL
       [EXISTS_TAC `s:real^2->bool`; EXISTS_TAC `t:real^2->bool`] THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `s INTER t:real^2->bool = {}` THENL
     [EXISTS_TAC `(\x. if x IN s then g x else h x):real^2->real` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      REWRITE_TAC[o_DEF; COND_RAND] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
      ASM_REWRITE_TAC[GSYM o_DEF] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\x:real^2. lift(g x) - lift(h x)`; `s INTER t:real^2->bool`]
     CONTINUOUS_DISCRETE_RANGE_CONSTANT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        REWRITE_TAC[GSYM CONTINUOUS_ON_CX_LIFT] THEN
        REWRITE_TAC[GSYM o_DEF] THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTER_SUBSET];
        REWRITE_TAC[o_DEF]] THEN
      X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      EXISTS_TAC `&2 * pi` THEN
      REWRITE_TAC[REAL_ARITH `&0 < &2 * x <=> &0 < x`; PI_POS] THEN
      X_GEN_TAC `y:real^2` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN
      REWRITE_TAC[GSYM LIFT_SUB; LIFT_EQ; NORM_LIFT] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[REAL_RING `a - b:real = c - d <=> a - c = b - d`] THEN
      REWRITE_TAC[GSYM CX_INJ] THEN
      MATCH_MP_TAC(COMPLEX_RING `ii * w = ii * z ==> w = z`) THEN
      MATCH_MP_TAC COMPLEX_EQ_CEXP THEN CONJ_TAC THENL
       [REWRITE_TAC[IM_MUL_II; RE_CX] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[CX_SUB; COMPLEX_SUB_LDISTRIB; CEXP_SUB] THEN
        ASM_MESON_TAC[]];
      REWRITE_TAC[EXISTS_LIFT; GSYM LIFT_SUB; LIFT_EQ; IN_INTER] THEN
      REWRITE_TAC[REAL_EQ_SUB_RADD; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `z:real` THEN DISCH_TAC THEN
      EXISTS_TAC `(\x. if x IN s then g x else z + h x):real^2->real` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[o_DEF; COND_RAND] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
        ASM_SIMP_TAC[TAUT `~(p /\ ~p)`; CX_ADD; GSYM o_DEF] THEN
        REWRITE_TAC[o_DEF; CX_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
        ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; GSYM o_DEF];
        X_GEN_TAC `x:real^2` THEN REWRITE_TAC[] THEN
        COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[] THEN DISCH_TAC THEN
        SUBGOAL_THEN
         `?w:real^2. cexp(ii * Cx(h w)) = cexp (ii * Cx(z + h w))`
         (CHOOSE_THEN MP_TAC) THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
        REWRITE_TAC[COMPLEX_FIELD `a = b * a <=> a = Cx(&0) \/ b = Cx(&1)`;
                    CEXP_NZ]]]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?c:real^2->bool.
       compact c /\ connected c /\ a IN c /\ b IN c /\ c INTER t = {}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `path_component((:real^2) DIFF t) a b` MP_TAC THENL
     [ASM_MESON_TAC[OPEN_PATH_CONNECTED_COMPONENT; closed; COMPACT_IMP_CLOSED];
      REWRITE_TAC[path_component; SET_RULE
        `s SUBSET UNIV DIFF t <=> s INTER t = {}`]] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `path_image(g:real^1->real^2)` THEN
    ASM_SIMP_TAC[CONNECTED_PATH_IMAGE; COMPACT_PATH_IMAGE] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c UNION s:real^2->bool`; `vec 0:real^2`]
        BOUNDED_SUBSET_BALL) THEN
  ASM_SIMP_TAC[BOUNDED_UNION; COMPACT_IMP_BOUNDED; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`;
                 `(t INTER cball(vec 0,r)) UNION sphere(vec 0:real^2,r)`;
                 `a:real^2`; `b:real^2`] lemma) THEN
  ASM_SIMP_TAC[COMPACT_UNION; CLOSED_INTER_COMPACT;
               COMPACT_SPHERE; COMPACT_CBALL] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `connected(s INTER t:real^2->bool)` THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC;
      REWRITE_TAC[connected_component] THEN EXISTS_TAC `c:real^2->bool`] THEN
    MP_TAC(ISPECL [`vec 0:real^2`; `r:real`] CBALL_DIFF_SPHERE) THEN
    ASM SET_TAC[];
    REWRITE_TAC[connected_component] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `u:real^2->bool` THEN
    SIMP_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> s INTER t = {}`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL
     [`u:real^2->bool`; `cball(vec 0:real^2,r)`] CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[FRONTIER_CBALL] THEN
    MP_TAC(ISPECL [`vec 0:real^2`; `r:real`] BALL_SUBSET_CBALL) THEN
    ASM SET_TAC[]]);;

let JANISZEWSKI_GEN = prove
 (`!s t a b:real^N.
        dimindex(:N) <= 2 /\
        compact s /\ closed t /\ connected(s INTER t) /\
        connected_component ((:real^N) DIFF s) a b /\
        connected_component ((:real^N) DIFF t) a b
        ==> connected_component ((:real^N) DIFF (s UNION t)) a b`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `dimindex(:N) = 1` THENL
   [ASM_SIMP_TAC[CONNECTED_COMPONENT_1_GEN] THEN SET_TAC[];
    ASM_SIMP_TAC[ARITH_RULE `1 <= n /\ ~(n = 1) ==> (n <= 2 <=> n = 2)`;
                 DIMINDEX_GE_1] THEN
    ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[GSYM DIMINDEX_2] THEN
    DISCH_THEN(fun th ->
     MATCH_ACCEPT_TAC(GEOM_EQUAL_DIMENSION_RULE th JANISZEWSKI))]);;

let JANISZEWSKI_CONNECTED = prove
 (`!s t:real^2->bool.
       compact s /\ closed t /\ connected(s INTER t) /\
       connected ((:real^2) DIFF s) /\ connected ((:real^2) DIFF t)
       ==> connected((:real^2) DIFF (s UNION t))`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNION] THEN
  ASM_MESON_TAC[JANISZEWSKI]);;

let JANISZEWSKI_DUAL = prove
 (`!s t:real^2->bool.
        compact s /\ compact t /\ connected s /\ connected t /\
        connected((:real^2) DIFF (s UNION t))
         ==> connected(s INTER t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s UNION t:real^2->bool` BORSUKIAN_IMP_UNICOHERENT) THEN
  ASM_SIMP_TAC[BORSUKIAN_SEPARATION_COMPACT; COMPACT_UNION; unicoherent] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC CLOSED_SUBSET THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Jordan Curve theorem.                                                 *)
(* ------------------------------------------------------------------------- *)

let JORDAN_CURVE_THEOREM = prove
 (`!c:real^1->real^2.
        simple_path c /\ pathfinish c = pathstart c
        ==> ?ins out.
                 ~(ins = {}) /\ open ins /\ connected ins /\
                 ~(out = {}) /\ open out /\ connected out /\
                 bounded ins /\ ~bounded out /\
                 ins INTER out = {} /\
                 ins UNION out = (:real^2) DIFF path_image c /\
                 frontier ins = path_image c /\
                 frontier out = path_image c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `path_image(c:real^1->real^2) homeomorphic sphere(vec 0:real^2,&1)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE; REAL_LT_01];
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP SIMPLE_PATH_IMP_PATH) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP COMPACT_PATH_IMAGE) THEN
    ABBREV_TAC `s:real^2->bool = path_image c`] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        JORDAN_BROUWER_SEPARATION)) THEN
  REWRITE_TAC[REAL_LT_01] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `(:real^2) DIFF s` COBOUNDED_UNBOUNDED_COMPONENTS) THEN
  MP_TAC(ISPEC `(:real^2) DIFF s` COBOUNDED_HAS_BOUNDED_COMPONENT) THEN
  ASM_SIMP_TAC[COMPL_COMPL; COMPACT_IMP_BOUNDED;
               DIMINDEX_2; LE_REFL; IMP_IMP] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `ins:real^2->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `out:real^2->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPLICATE_TAC 5 (GEN_REWRITE_TAC I [CONJ_ASSOC]) THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; IN_COMPONENTS_CONNECTED;
                  OPEN_COMPONENTS; closed; COMPACT_IMP_CLOSED];
    STRIP_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[COMPONENTS_EQ]; DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC JORDAN_BROUWER_FRONTIER THEN
    REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN ASM_MESON_TAC[];
    STRIP_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [UNIONS_COMPONENTS] THEN
  REWRITE_TAC[GSYM UNIONS_2] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `a IN s /\ b IN s /\ (!c. c IN s /\ ~(c = a) /\ ~(c = b) ==> F)
    ==> {a,b} = s`) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `mid:real^2->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `frontier mid:real^2->bool = s` ASSUME_TAC THENL
   [MATCH_MP_TAC JORDAN_BROUWER_FRONTIER THEN
    REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(mid:real^2->bool) /\ connected mid /\ ~(mid = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; IN_COMPONENTS_CONNECTED;
                  OPEN_COMPONENTS; closed; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?a b:real^2.
        a IN s /\ b IN s  /\ ~(a = b) /\
        ?g. arc g /\ pathstart g = a /\ pathfinish g = b /\
            path_image g DIFF {a,b} SUBSET mid`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `?a b:real^2. a IN s /\ b IN s /\ ~(a = b)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!c. s SUBSET {c} ==> F) ==> ?a b. a IN s /\ b IN s /\ ~(a = b)`) THEN
      ASM_MESON_TAC[INFINITE_SIMPLE_PATH_IMAGE; INFINITE; FINITE_SING;
                    FINITE_SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`mid:real^2->bool`; `s INTER ball(a:real^2,dist(a,b))`;
      `s INTER ball(b:real^2,dist(a,b))`]
     DENSE_ACCESSIBLE_FRONTIER_POINT_PAIRS) THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL] THEN ANTS_TAC THENL
     [SUBGOAL_THEN
       `a IN ball(a:real^2,dist(a,b)) /\ b IN ball(b,dist(a,b)) /\
        ~(a IN ball(b,dist(a,b))) /\ ~(b IN ball(a,dist(a,b)))`
      MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      ASM_REWRITE_TAC[IN_BALL; DIST_REFL; GSYM DIST_NZ] THEN
      REWRITE_TAC[DIST_SYM] THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_INTER; LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC `g:real^1->real^2` THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`pathstart g:real^2`; `pathfinish g:real^2`] THEN
    ASM_SIMP_TAC[ARC_DISTINCT_ENDS] THEN EXISTS_TAC `g:real^1->real^2` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        SUBSET_TRANS)) THEN
    REWRITE_TAC[OPEN_CLOSED_INTERVAL_1; path_image; pathstart; pathfinish] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^1->real^2`; `a:real^2`; `b:real^2`]
     EXISTS_DOUBLE_ARC) THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^1->real^2`; `d:real^1->real^2`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?x:real^2 y:real^2. x IN ins /\ y IN out`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(path_image u UNION path_image g):real^2->bool`;
    `(path_image d UNION path_image g):real^2->bool`;
    `x:real^2`; `y:real^2`] JANISZEWSKI) THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
      [COMPACT_UNION; COMPACT_IMP_CLOSED; COMPACT_PATH_IMAGE;
       ARC_IMP_PATH; NOT_IMP] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `(path_image u UNION path_image g) INTER
      (path_image d UNION path_image g) = path_image(g:real^1->real^2)`
     (fun th -> ASM_SIMP_TAC[CONNECTED_ARC_IMAGE; th]) THEN
    MATCH_MP_TAC(SET_RULE
     `u INTER d SUBSET s ==> (u UNION s) INTER (d UNION s) = s`) THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE;
                  ARC_IMP_PATH];
    REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `ins UNION out UNION (s DIFF path_image u):real^2->bool` THEN
    ASM_REWRITE_TAC[IN_UNION] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `s UNION t UNION u =
                                (s UNION u) UNION (t UNION u)`] THEN
      MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
        EXISTS_TAC `ins:real^2->bool` THEN
        ASM_SIMP_TAC[UNION_SUBSET; CLOSURE_UNION_FRONTIER; SUBSET_UNION] THEN
        ASM SET_TAC[];
        MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
        EXISTS_TAC `out:real^2->bool` THEN
        ASM_SIMP_TAC[UNION_SUBSET; CLOSURE_UNION_FRONTIER; SUBSET_UNION] THEN
        ASM SET_TAC[];
        MATCH_MP_TAC(SET_RULE
         `~(u = {}) ==> ~((s UNION u) INTER (t UNION u) = {})`) THEN
        SUBGOAL_THEN `~(path_image d SUBSET {a:real^2,b})`
        MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          FINITE_SUBSET)) THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
        ASM_SIMP_TAC[INFINITE_ARC_IMAGE; GSYM INFINITE]];
      SUBGOAL_THEN `ins INTER out = {} /\ ins INTER mid = {} /\
                    (mid:real^2->bool) INTER out = {}`
      MP_TAC THENL [ASM_MESON_TAC[COMPONENTS_NONOVERLAP]; ALL_TAC] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
      ASM SET_TAC[]];
    REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `ins UNION out UNION (s DIFF path_image d):real^2->bool` THEN
    ASM_REWRITE_TAC[IN_UNION] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `s UNION t UNION u =
                                (s UNION u) UNION (t UNION u)`] THEN
      MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
        EXISTS_TAC `ins:real^2->bool` THEN
        ASM_SIMP_TAC[UNION_SUBSET; CLOSURE_UNION_FRONTIER; SUBSET_UNION] THEN
        ASM SET_TAC[];
        MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
        EXISTS_TAC `out:real^2->bool` THEN
        ASM_SIMP_TAC[UNION_SUBSET; CLOSURE_UNION_FRONTIER; SUBSET_UNION] THEN
        ASM SET_TAC[];
        MATCH_MP_TAC(SET_RULE
         `~(u = {}) ==> ~((s UNION u) INTER (t UNION u) = {})`) THEN
        SUBGOAL_THEN `~(path_image u SUBSET {a:real^2,b})`
        MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          FINITE_SUBSET)) THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
        ASM_SIMP_TAC[INFINITE_ARC_IMAGE; GSYM INFINITE]];
      SUBGOAL_THEN `ins INTER out = {} /\ ins INTER mid = {} /\
                    (mid:real^2->bool) INTER out = {}`
      MP_TAC THENL [ASM_MESON_TAC[COMPONENTS_NONOVERLAP]; ALL_TAC] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
      ASM SET_TAC[]];
    SUBGOAL_THEN `~(connected_component ((:real^2) DIFF s) x y)` MP_TAC THENL
     [REWRITE_TAC[connected_component] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`(:real^2) DIFF s`; `t:real^2->bool`]
        COMPONENTS_MAXIMAL) THEN
      DISCH_THEN(fun th ->
        MP_TAC(SPEC `ins:real^2->bool` th) THEN
        MP_TAC(SPEC `out:real^2->bool` th)) THEN ASM SET_TAC[];
      REWRITE_TAC[CONTRAPOS_THM] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s y ==> t y`) THEN
      REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CONNECTED_COMPONENT_MONO THEN
      ASM SET_TAC[]]]);;

let JORDAN_DISCONNECTED = prove
 (`!c. simple_path c /\ pathfinish c = pathstart c
       ==> ~connected((:real^2) DIFF path_image c)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[connected] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP JORDAN_CURVE_THEOREM) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let JORDAN_INSIDE_OUTSIDE = prove
 (`!c:real^1->real^2.
        simple_path c /\ pathfinish c = pathstart c
        ==> ~(inside(path_image c) = {}) /\
            open(inside(path_image c)) /\
            connected(inside(path_image c)) /\
            ~(outside(path_image c) = {}) /\
            open(outside(path_image c)) /\
            connected(outside(path_image c)) /\
            bounded(inside(path_image c)) /\
            ~bounded(outside(path_image c)) /\
            inside(path_image c) INTER outside(path_image c) = {} /\
            inside(path_image c) UNION outside(path_image c) =
            (:real^2) DIFF path_image c /\
            frontier(inside(path_image c)) = path_image c /\
            frontier(outside(path_image c)) = path_image c`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP JORDAN_CURVE_THEOREM) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`ins:real^2->bool`; `out:real^2->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `inside(path_image c) :real^2->bool = ins /\
                outside(path_image c):real^2->bool = out `
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC INSIDE_OUTSIDE_UNIQUE THEN ASM_SIMP_TAC[JORDAN_DISCONNECTED]);;

let JORDAN_COMPONENTS = prove
 (`!g. simple_path g /\ pathfinish g = pathstart g
       ==> components((:real^2) DIFF path_image g) =
           {inside(path_image g),outside(path_image g)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPONENTS_OPEN_UNIQUE THEN
  REWRITE_TAC[UNIONS_2; PAIRWISE_INSERT; NOT_IN_EMPTY; FORALL_IN_INSERT;
              IMP_CONJ; PAIRWISE_EMPTY] THEN
  MP_TAC(ISPEC `g:real^1->real^2` JORDAN_INSIDE_OUTSIDE) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `path_image g:complex->bool` INSIDE_INTER_OUTSIDE) THEN
  REPLICATE_TAC 2 STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Triple-curve or "theta-curve" theorem. Proof that there is no fourth      *)
(* component taken from Kuratowski's Topology vol 2, para 61, II.            *)
(* ------------------------------------------------------------------------- *)

let THETA_CURVE_INSIDE_CASES = prove
 (`!c1 c2 c3 a b:real^2.
        arc c1 /\ pathstart c1 = a /\ pathfinish c1 = b /\
        arc c2 /\ pathstart c2 = a /\ pathfinish c2 = b /\
        arc c3 /\ pathstart c3 = a /\ pathfinish c3 = b /\
        path_image c1 INTER path_image c2 = {a,b} /\
        path_image c2 INTER path_image c3 = {a,b} /\
        path_image c3 INTER path_image c1 = {a,b}
        ==> path_image c1 DIFF {a,b} SUBSET
            inside(path_image c2 UNION path_image c3) \/
            path_image c2 DIFF {a,b} SUBSET
            inside(path_image c3 UNION path_image c1) \/
            path_image c3 DIFF {a,b} SUBSET
            inside(path_image c1 UNION path_image c2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c3 ++ reversepath c1:real^1->real^2`
    JORDAN_INSIDE_OUTSIDE) THEN
  MP_TAC(ISPEC `c2 ++ reversepath c3:real^1->real^2`
    JORDAN_INSIDE_OUTSIDE) THEN
  MP_TAC(ISPEC `c1 ++ reversepath c2:real^1->real^2`
   JORDAN_INSIDE_OUTSIDE) THEN
  ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN;
               PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
               SIMPLE_PATH_JOIN_LOOP_EQ; ARC_REVERSEPATH_EQ;
               PATH_IMAGE_REVERSEPATH; SUBSET_REFL; PATH_IMAGE_JOIN;
               PATH_IMAGE_REVERSEPATH] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[TAUT `p \/ q <=> ~(~p /\ ~q)`] THEN
  REWRITE_TAC[SET_RULE `s SUBSET t <=> s DIFF t = {}`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN
   (MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        (REWRITE_RULE[CONJ_ASSOC] CONNECTED_INTER_FRONTIER)))) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[TAUT `p /\ ~q ==> ~r <=> p /\ r ==> q`] THEN
  PURE_ONCE_REWRITE_TAC[TAUT `~p <=> p ==> F`] THEN
  REPEAT(ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_MESON_TAC[CONNECTED_SIMPLE_PATH_ENDLESS; ARC_IMP_SIMPLE_PATH];
    DISCH_TAC]) THEN
  SUBGOAL_THEN
   `inside(path_image c1 UNION path_image c2:real^2->bool) IN
    components((:real^2) DIFF
               (path_image c1 UNION path_image c2 UNION path_image c3)) /\
    inside(path_image c2 UNION path_image c3:real^2->bool) IN
    components((:real^2) DIFF
               (path_image c1 UNION path_image c2 UNION path_image c3)) /\
    inside(path_image c3 UNION path_image c1:real^2->bool) IN
    components((:real^2) DIFF
               (path_image c1 UNION path_image c2 UNION path_image c3))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CLOPEN_IN_COMPONENTS THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [ASM_REWRITE_TAC[CLOSED_IN_INTER_CLOSURE; CLOSURE_UNION_FRONTIER];
       MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[]]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`closure(inside(path_image c1 UNION path_image c2)):real^2->bool`;
    `closure(inside(path_image c2 UNION path_image c3)):real^2->bool`]
   JANISZEWSKI_CONNECTED) THEN
  ASM_REWRITE_TAC[COMPACT_CLOSURE; CLOSED_CLOSURE; NOT_IMP] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `c2:real^1->real^2` CONNECTED_PATH_IMAGE) THEN
    ASM_SIMP_TAC[ARC_IMP_PATH] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN MATCH_MP_TAC(SET_RULE
     `i INTER (c1 UNION c2 UNION c3) = {} /\
      j INTER (c1 UNION c2 UNION c3) = {} /\
      i INTER j = {} /\ c1 INTER c3 SUBSET c2
      ==> c2 = (i UNION c1 UNION c2) INTER (j UNION c2 UNION c3)`) THEN
    REPEAT CONJ_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
      SET_TAC[];
      REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
      SET_TAC[];
      MP_TAC(ISPEC `(:real^2) DIFF
               (path_image c1 UNION path_image c2 UNION path_image c3)`
        COMPONENTS_NONOVERLAP) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
      DISCH_THEN(MP_TAC o AP_TERM `frontier:(real^2->bool)->real^2->bool`) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `c1:real^1->real^2` NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
      ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    UNDISCH_TAC
     `connected(outside(path_image c1 UNION path_image c2):real^2->bool)` THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM SET_TAC[];
    UNDISCH_TAC
     `connected(outside(path_image c2 UNION path_image c3):real^2->bool)` THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM SET_TAC[];
    (MP_TAC o ASSUME)
     `inside(path_image c3 UNION path_image c1:real^2->bool) IN
      components((:real^2) DIFF
                 (path_image c1 UNION path_image c2 UNION path_image c3))` THEN
    REWRITE_TAC[IN_COMPONENTS_MAXIMAL] THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    MATCH_MP_TAC(MESON[]
     `R s /\ ~(s = i) /\ P s /\ Q s
      ==> (!c. P c /\ Q c /\ R c /\ connected c ==> c = i)
      ==> ~connected s`) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `bounded:(real^2->bool)->bool`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COBOUNDED_IMP_UNBOUNDED THEN
      REWRITE_TAC[COMPL_COMPL] THEN
      ASM_REWRITE_TAC[BOUNDED_UNION; BOUNDED_CLOSURE_EQ];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[CLOSURE_UNION_FRONTIER; SET_RULE
     `(i UNION c1 UNION c2) UNION (j UNION c2 UNION c3) =
      (i UNION j) UNION (c1 UNION c2 UNION c3)`] THEN
    MATCH_MP_TAC(SET_RULE
     `i3 SUBSET UNIV DIFF c /\
      ~(i3 = {}) /\ i1 INTER i3 = {} /\ i2 INTER i3 = {}
      ==> ~(UNIV DIFF ((i1 UNION i2) UNION c) = {}) /\
          i3 SUBSET UNIV DIFF ((i1 UNION i2) UNION c)`) THEN
    ASM_SIMP_TAC[IN_COMPONENTS_SUBSET; IN_COMPONENTS_NONEMPTY] THEN
    MP_TAC(ISPEC `(:real^2) DIFF
                  (path_image c1 UNION path_image c2 UNION path_image c3)`
    COMPONENTS_NONOVERLAP) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN CONJ_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `frontier:(real^2->bool)->real^2->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `c2:real^1->real^2` NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
    ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH] THEN ASM SET_TAC[]]);;

let SPLIT_INSIDE_SIMPLE_CLOSED_CURVE = prove
 (`!c1 c2 c a b:real^2.
        ~(a = b) /\
        simple_path c1 /\ pathstart c1 = a /\ pathfinish c1 = b /\
        simple_path c2 /\ pathstart c2 = a /\ pathfinish c2 = b /\
        simple_path c /\ pathstart c = a /\ pathfinish c = b /\
        path_image c1 INTER path_image c2 = {a,b} /\
        path_image c1 INTER path_image c = {a,b} /\
        path_image c2 INTER path_image c = {a,b} /\
        ~(path_image c INTER inside(path_image c1 UNION path_image c2) = {})
        ==> inside(path_image c1 UNION path_image c) INTER
            inside(path_image c2 UNION path_image c) = {} /\
            inside(path_image c1 UNION path_image c) UNION
            inside(path_image c2 UNION path_image c) UNION
            (path_image c DIFF {a,b}) =
            inside(path_image c1 UNION path_image c2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (MP_TAC o C ISPEC JORDAN_INSIDE_OUTSIDE)
   [`(c1 ++ reversepath c2):real^1->real^2`;
    `(c1 ++ reversepath c):real^1->real^2`;
    `(c2 ++ reversepath c):real^1->real^2`] THEN
  ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN;
               PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
               SIMPLE_PATH_JOIN_LOOP; SIMPLE_PATH_IMP_ARC;
               PATH_IMAGE_JOIN; SIMPLE_PATH_IMP_PATH; PATH_IMAGE_REVERSEPATH;
               SIMPLE_PATH_REVERSEPATH; ARC_REVERSEPATH;
               SUBSET_REFL] THEN
  REPLICATE_TAC 3 STRIP_TAC THEN
  SUBGOAL_THEN
   `path_image(c:real^1->real^2) INTER
    outside(path_image c1 UNION path_image c2) = {}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `connected(path_image(c:real^1->real^2) DIFF
                {pathstart c,pathfinish c})`
    MP_TAC THENL [ASM_SIMP_TAC[CONNECTED_SIMPLE_PATH_ENDLESS]; ALL_TAC] THEN
    ASM_REWRITE_TAC[connected] THEN
    MAP_EVERY EXISTS_TAC
     [`inside(path_image c1 UNION path_image c2):real^2->bool`;
      `outside(path_image c1 UNION path_image c2):real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `outside(path_image c1 UNION path_image c2) SUBSET
    outside(path_image c1 UNION path_image (c:real^1->real^2)) /\
    outside(path_image c1 UNION path_image c2) SUBSET
    outside(path_image c2 UNION path_image c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ALL_TAC; GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [UNION_COMM]] THEN
    MATCH_MP_TAC OUTSIDE_UNION_OUTSIDE_UNION THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image(c1:real^1->real^2) INTER
    inside(path_image c2 UNION path_image c) = {}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `frontier(outside(path_image c1 UNION path_image c2)):real^2->bool =
      frontier(outside(path_image c2 UNION path_image c))`
    MP_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [UNION_COMM] THEN
      MATCH_MP_TAC OUTSIDE_UNION_OUTSIDE_UNION THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `connected(path_image(c1:real^1->real^2) DIFF
                  {pathstart c1,pathfinish c1})`
      MP_TAC THENL [ASM_SIMP_TAC[CONNECTED_SIMPLE_PATH_ENDLESS]; ALL_TAC] THEN
      ASM_REWRITE_TAC[connected] THEN
      MAP_EVERY EXISTS_TAC
       [`inside(path_image c2 UNION path_image c):real^2->bool`;
        `outside(path_image c2 UNION path_image c):real^2->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MP_TAC(ISPEC `c:real^1->real^2` NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image(c2:real^1->real^2) INTER
    inside(path_image c1 UNION path_image c) = {}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `frontier(outside(path_image c1 UNION path_image c2)):real^2->bool =
      frontier(outside(path_image c1 UNION path_image c))`
    MP_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OUTSIDE_UNION_OUTSIDE_UNION THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `connected(path_image(c2:real^1->real^2) DIFF
                  {pathstart c2,pathfinish c2})`
      MP_TAC THENL [ASM_SIMP_TAC[CONNECTED_SIMPLE_PATH_ENDLESS]; ALL_TAC] THEN
      ASM_REWRITE_TAC[connected] THEN
      MAP_EVERY EXISTS_TAC
       [`inside(path_image c1 UNION path_image c):real^2->bool`;
        `outside(path_image c1 UNION path_image c):real^2->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MP_TAC(ISPEC `c:real^1->real^2` NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inside(path_image c1 UNION path_image (c:real^1->real^2)) SUBSET
    inside(path_image c1 UNION path_image c2) /\
    inside(path_image c2 UNION path_image (c:real^1->real^2)) SUBSET
    inside(path_image c1 UNION path_image c2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[INSIDE_OUTSIDE] THEN
    REWRITE_TAC[SET_RULE `UNIV DIFF t SUBSET UNIV DIFF s <=> s SUBSET t`] THENL
     [ALL_TAC; GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [UNION_COMM]] THEN
    MATCH_MP_TAC(SET_RULE
     `out1 SUBSET out2 /\ c2 DIFF (c1 UNION c) SUBSET out2
      ==> (c1 UNION c2) UNION out1 SUBSET (c1 UNION c) UNION out2`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[OUTSIDE_INSIDE] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inside(path_image c1 UNION path_image c :real^2->bool) SUBSET
    outside(path_image c2 UNION path_image c) /\
    inside(path_image c2 UNION path_image c) SUBSET
    outside(path_image c1 UNION path_image c)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN CONJ_TAC THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THENL
     [SUBGOAL_THEN `?z:real^2. z IN path_image c1 /\
                               z IN outside(path_image c2 UNION path_image c)`
      (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THENL
       [REWRITE_TAC[OUTSIDE_INSIDE; IN_DIFF; IN_UNION; IN_UNIV] THEN
        MP_TAC(ISPEC `c1:real^1->real^2` NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
      REWRITE_TAC[OUTSIDE; IN_ELIM_THM; CONTRAPOS_THM] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN REWRITE_TAC[IN] THEN
      MP_TAC(ASSUME
       `open(outside(path_image c2 UNION path_image c):real^2->bool)`) THEN
      REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(ASSUME
       `frontier(inside(path_image c1 UNION path_image c):real^2->bool) =
        path_image c1 UNION path_image c`) THEN
      GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN REWRITE_TAC[frontier] THEN
      ASM_SIMP_TAC[IN_UNION; IN_DIFF; CLOSURE_APPROACHABLE; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `w:real^2` THEN STRIP_TAC THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC `w:real^2` THEN
      REWRITE_TAC[connected_component] THEN CONJ_TAC THENL
       [EXISTS_TAC
         `outside(path_image c2 UNION path_image c:real^2->bool)` THEN
        ASM_REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> s INTER t = {}`;
                        OUTSIDE_NO_OVERLAP] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
        ASM_REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] IN_BALL];
        EXISTS_TAC `inside(path_image c1 UNION path_image c:real^2->bool)` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE
         `inside(c1 UNION c) INTER (c1 UNION c) = {} /\
          c2 INTER inside(c1 UNION c) = {}
          ==> inside(c1 UNION c) SUBSET UNIV DIFF (c2 UNION c)`) THEN
        ASM_REWRITE_TAC[INSIDE_NO_OVERLAP]];
      SUBGOAL_THEN `?z:real^2. z IN path_image c2 /\
                               z IN outside(path_image c1 UNION path_image c)`
      (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THENL
       [REWRITE_TAC[OUTSIDE_INSIDE; IN_DIFF; IN_UNION; IN_UNIV] THEN
        MP_TAC(ISPEC `c2:real^1->real^2` NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
      REWRITE_TAC[OUTSIDE; IN_ELIM_THM; CONTRAPOS_THM] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN REWRITE_TAC[IN] THEN
      MP_TAC(ASSUME
       `open(outside(path_image c1 UNION path_image c):real^2->bool)`) THEN
      REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(ASSUME
       `frontier(inside(path_image c2 UNION path_image c):real^2->bool) =
        path_image c2 UNION path_image c`) THEN
      GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN REWRITE_TAC[frontier] THEN
      ASM_SIMP_TAC[IN_UNION; IN_DIFF; CLOSURE_APPROACHABLE; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `w:real^2` THEN STRIP_TAC THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC `w:real^2` THEN
      REWRITE_TAC[connected_component] THEN CONJ_TAC THENL
       [EXISTS_TAC
         `outside(path_image c1 UNION path_image c:real^2->bool)` THEN
        ASM_REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> s INTER t = {}`;
                        OUTSIDE_NO_OVERLAP] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
        ASM_REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] IN_BALL];
        EXISTS_TAC `inside(path_image c2 UNION path_image c:real^2->bool)` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE
         `inside(c2 UNION c) INTER (c2 UNION c) = {} /\
          c1 INTER inside(c2 UNION c) = {}
          ==> inside(c2 UNION c) SUBSET UNIV DIFF (c1 UNION c)`) THEN
        ASM_REWRITE_TAC[INSIDE_NO_OVERLAP]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!u. s SUBSET u /\ t INTER u = {} ==> s INTER t = {}`) THEN
    EXISTS_TAC `outside(path_image c2 UNION path_image c):real^2->bool` THEN
    ASM_REWRITE_TAC[INSIDE_INTER_OUTSIDE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `outside (path_image c1 UNION path_image c) INTER
    outside (path_image c2 UNION path_image c):real^2->bool
    SUBSET outside (path_image c1 UNION path_image c2)`
  MP_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[SET_RULE `s INTER t = u <=>
                        (UNIV DIFF s) UNION (UNIV DIFF t) = UNIV DIFF u`] THEN
    REWRITE_TAC[GSYM UNION_WITH_INSIDE] THEN ASM SET_TAC[]] THEN
  MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
  EXISTS_TAC `(:real^2) DIFF (path_image c1 UNION path_image c2)` THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[OUTSIDE_IN_COMPONENTS]; DISCH_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MP_TAC(ISPECL
   [`closure(inside(path_image c1 UNION path_image c)):real^2->bool`;
    `closure(inside(path_image c2 UNION path_image c)):real^2->bool`]
   JANISZEWSKI_CONNECTED) THEN
  ASM_REWRITE_TAC[COMPACT_CLOSURE; CLOSED_CLOSURE] THEN
  ASM_REWRITE_TAC[CLOSURE_UNION_FRONTIER;
                  COMPL_COMPL;
                  ONCE_REWRITE_RULE[UNION_COMM] UNION_WITH_INSIDE] THEN
  REWRITE_TAC[SET_RULE
   `UNIV DIFF ((UNIV DIFF s) UNION (UNIV DIFF t)) = s INTER t`] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `connected(path_image c:real^2->bool)` MP_TAC THENL
   [ASM_SIMP_TAC[CONNECTED_SIMPLE_PATH_IMAGE]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM UNION_WITH_INSIDE] THEN ASM SET_TAC[]);;
