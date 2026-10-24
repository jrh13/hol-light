(* ========================================================================= *)
(* 4CT/map_main.ml                                                           *)
(*                                                                           *)
(* The Four Colour Theorem for maps of regions in the plane modulo the       *)
(* planar-graph theorem: finite maps via ADJACENCY_GRAPH_PLANAR              *)
(* (map_grid.ml), infinite maps by compactness (COLORING_COMPACTNESS, the    *)
(* de Bruijn-Erdos theorem for n colours, from Tychonoff for a product of    *)
(* finite discrete spaces), and FOUR_COLOR_MAP_OF_PLANAR_GRAPHS under the    *)
(* hypothesis planar_graphs_four_colorable.  FOUR_COLOR_FINITE_MAP and       *)
(* MAP_COLORABLE_COMPACTNESS play the roles of four_color_finite             *)
(* (fourcolor.v) and compactness_extension (finitize.v) in Gonthier's proof, *)
(* which avoids choice by enumerating the regions through grid points.       *)
(* ========================================================================= *)

needs "4CT/map_grid.ml";;

(* ------------------------------------------------------------------------- *)
(* Finite maps (the empty region, adjacent to nothing, gets colour 0).       *)
(* ------------------------------------------------------------------------- *)

let FOUR_COLOR_FINITE_MAP = prove
 (`planar_graphs_four_colorable
   ==> !M. plane_map M /\ FINITE M ==> map_colorable 4 M`,
  REWRITE_TAC[planar_graphs_four_colorable] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`M DELETE ({}:real^2->bool)`;
    `adjacency_graph (M DELETE ({}:real^2->bool))`]) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ADJACENCY_GRAPH_PLANAR THEN
    ASM_MESON_TAC[PLANE_MAP_SUBSET; DELETE_SUBSET; FINITE_DELETE; IN_DELETE];
    REWRITE_TAC[map_colorable; adjacency_graph; IN_ELIM_THM]] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^2->bool)->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\r:real^2->bool. if r = {} then 0 else c r` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[IN_DELETE; ARITH_RULE `0 < 4`];
    MAP_EVERY X_GEN_TAC [`r1:real^2->bool`; `r2:real^2->bool`] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ADJACENT_REGIONS_NONEMPTY) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`r1:real^2->bool`; `r2:real^2->bool`] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC ADJACENT_REGIONS_SUBSET THEN
    EXISTS_TAC `M:(real^2->bool)->bool` THEN
    ASM_REWRITE_TAC[DELETE_SUBSET; IN_DELETE] THEN
    ASM_MESON_TAC[adjacent_regions]]);;

(* ------------------------------------------------------------------------- *)
(* Compactness: a relation is n-colourable when its restriction to every     *)
(* finite subset is.  The colourings form the compact product of the finite  *)
(* discrete spaces {0,..,n-1} (Tychonoff); those separating x and y form a   *)
(* closed set, and every finite family of these sets has a common point.     *)
(* ------------------------------------------------------------------------- *)

let COLORING_COMPACTNESS = prove
 (`!R:A->A->bool s n.
        (!t. FINITE t /\ t SUBSET s
             ==> ?c. (!x. x IN t ==> c x < n) /\
                     (!x y. x IN t /\ y IN t /\ R x y ==> ~(c x = c y)))
        ==> ?c. (!x. x IN s ==> c x < n) /\
                (!x y. x IN s /\ y IN s /\ R x y ==> ~(c x = c y))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  SUBGOAL_THEN `0 < n` ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `a:A` o
      REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{a:A}`) THEN
    ASM_REWRITE_TAC[FINITE_SING; SING_SUBSET; IN_SING] THEN
    MESON_TAC[ARITH_RULE `x < n ==> 0 < n`];
    ALL_TAC] THEN
  ASM_CASES_TAC `?a b:A. a IN s /\ b IN s /\ R a b` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `a:A` (X_CHOOSE_TAC `b:A`));
    EXISTS_TAC `(\x. 0):A->num` THEN ASM_MESON_TAC[]] THEN
  ABBREV_TAC
   `top = product_topology s (\x:A. discrete_topology {k | k < n})` THEN
  SUBGOAL_THEN
   `!c. c IN topspace top <=> EXTENSIONAL s c /\ !x:A. x IN s ==> c x < n`
  ASSUME_TAC THENL
   [EXPAND_TAC "top" THEN
    REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY_ALT; TOPSPACE_DISCRETE_TOPOLOGY;
                IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPEC `top:(A->num)topology` COMPACT_SPACE_FIP) THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [EXPAND_TAC "top" THEN
    REWRITE_TAC[COMPACT_SPACE_PRODUCT_TOPOLOGY;
                COMPACT_SPACE_DISCRETE_TOPOLOGY; FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE (\p. {c | c IN topspace top /\ ~(c(FST p):num = c(SND p))})
          {p | FST p IN s /\ SND p IN s /\ R (FST p) (SND p:A)}`) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `{c | c IN topspace top /\ ~(c(x:A):num = c y)} =
        {c | c IN topspace top /\
             (\c. c x,c y) c IN {(i,j) | i < n /\ j < n /\ ~(i = j)}}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; PAIR_EQ] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
        EXISTS_TAC `prod_topology (discrete_topology {k | k < n})
                                  (discrete_topology {k | k < n})` THEN
        EXPAND_TAC "top" THEN
        ASM_SIMP_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_PRODUCT_PROJECTION;
                     PROD_TOPOLOGY_DISCRETE_TOPOLOGY;
                     CLOSED_IN_DISCRETE_TOPOLOGY] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_CROSS; IN_ELIM_THM] THEN
        SIMP_TAC[]];
      X_GEN_TAC `p:A#A->bool` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC
       `IMAGE FST (p:A#A->bool) UNION IMAGE SND p`) THEN
      ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; UNION_SUBSET; SUBSET;
                   FORALL_IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:A->num` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; INTERS_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `RESTRICTION s
        (\x:A. if x IN IMAGE FST p UNION IMAGE SND p then d x else 0)` THEN
      ASM_REWRITE_TAC[RESTRICTION; EXTENSIONAL; IN_ELIM_THM] THEN
      X_GEN_TAC `q:A#A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `FST(q:A#A) IN IMAGE FST p UNION IMAGE SND p /\
                    SND q IN IMAGE FST p UNION IMAGE SND p`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[IN_UNION; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; INTERS_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `c:A->num`) THEN EXISTS_TAC `c:A->num` THEN
    ASM_MESON_TAC[]]);;

let MAP_COLORABLE_COMPACTNESS = prove
 (`!M n. (!M'. M' SUBSET M /\ FINITE M' ==> map_colorable n M')
         ==> map_colorable n M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`adjacent_regions M`; `M:(real^2->bool)->bool`; `n:num`]
    COLORING_COMPACTNESS) THEN
  REWRITE_TAC[map_colorable] THEN ANTS_TAC THENL
   [X_GEN_TAC `t:(real^2->bool)->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:(real^2->bool)->bool`) THEN
    ASM_REWRITE_TAC[map_colorable] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_MESON_TAC[ADJACENT_REGIONS_SUBSET];
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[adjacent_regions]]);;

(* ------------------------------------------------------------------------- *)
(* The theorem (modulo the planar-graph four colour theorem).                *)
(* ------------------------------------------------------------------------- *)

let FOUR_COLOR_MAP_OF_PLANAR_GRAPHS = prove
 (`planar_graphs_four_colorable ==> !M. plane_map M ==> map_colorable 4 M`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MAP_COLORABLE_COMPACTNESS THEN
  ASM_MESON_TAC[FOUR_COLOR_FINITE_MAP; PLANE_MAP_SUBSET]);;
