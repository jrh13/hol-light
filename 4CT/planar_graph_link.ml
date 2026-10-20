(* ========================================================================= *)
(* 4CT/planar_graph_link.ml                                                  *)
(*                                                                           *)
(* From the hypermap theorem to finite simple planar graphs in the sense of  *)
(* HOL Light's Autoformalization/planar_graph.ml (geometric planarity,       *)
(* planar_graph V E): FOUR_COLOR_PLANAR_GRAPH_OF_HYPERMAP derives the        *)
(* four-colourability of every planar graph from any theorem of the form of  *)
(* FOUR_COLOR_HYPERMAP.  graph_hypermap E r = mk_hypermap (graph_darts E,    *)
(* graph_reverse_dart E, graph_reverse_dart E o inverse r, r) is the dual of *)
(* the natural map of a rotation system: its faces are the vertices (the     *)
(* r-orbits of outgoing darts), its nodes the graph faces, its edges {d,     *)
(* reverse d}.  It is planar (the Euler count gives genus 0) and bridgeless  *)
(* (r preserves FST, reverse swaps it), so the hypermap theorem gives a dart *)
(* colouring constant on the r-orbits with k (reverse d) <> k d, a proper    *)
(* vertex 4-colouring of each connected component; the components are glued  *)
(* by Hilbert choice.  PLANAR_K4_NOT_3_COLORABLE checks that four colours    *)
(* are needed.                                                              *)
(* ========================================================================= *)

needs "Autoformalization/planar_graph.ml";;
prioritize_num();;
needs "4CT/coloring.ml";;

(* ------------------------------------------------------------------------- *)
(* The hypermap of a rotation system (dual orientation, see above).          *)
(* ------------------------------------------------------------------------- *)

let graph_hypermap = new_definition
 `graph_hypermap (E:(A->bool)->bool) (r:(A#A)->A#A) =
    mk_hypermap(graph_darts E, graph_reverse_dart E,
    graph_reverse_dart E o inverse r, r)`;;

let ORBIT_MAP_PERMUTATION_ORBIT = prove
 (`!f:B->B x. orbit_map f x = permutation_orbit f x`,
  REWRITE_TAC[orbit_map; permutation_orbit; EXTENSION; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let SET_OF_ORBITS_PERMUTATION_ORBITS = prove
 (`!s (f:B->B). set_of_orbits s f = permutation_orbits f s`,
  REWRITE_TAC[set_of_orbits; permutation_orbits; SIMPLE_IMAGE] THEN
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; ORBIT_MAP_PERMUTATION_ORBIT]);;

let GRAPH_HYPERMAP_PRED = prove
 (`!V (E:(A->bool)->bool) r.
     finite_simple_graph V E /\ graph_rotation E r
     ==> hypermap_pred (graph_darts E,graph_reverse_dart E,
                        graph_reverse_dart E o inverse r,r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GRAPH_ROTATION_PERMUTES) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_GRAPH_DARTS) THEN
  REWRITE_TAC[hypermap_pred; FST; SND] THEN
  ASM_REWRITE_TAC[GRAPH_REVERSE_DART_PERMUTES] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PERMUTES_COMPOSE THEN
    ASM_SIMP_TAC[GRAPH_REVERSE_DART_PERMUTES; PERMUTES_INVERSE];
    REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN X_GEN_TAC `d:A#A` THEN
    FIRST_ASSUM(fun th ->
      REWRITE_TAC[CONJUNCT2(MATCH_MP PERMUTES_INVERSES th)]) THEN
    REWRITE_TAC[GRAPH_REVERSE_DART_INVOLUTION]]);;

let GRAPH_HYPERMAP_COMPONENTS = prove
 (`!V (E:(A->bool)->bool) r.
     finite_simple_graph V E /\ graph_rotation E r
     ==> dart (graph_hypermap E r) = graph_darts E /\
         edge_map (graph_hypermap E r) = graph_reverse_dart E /\
         node_map (graph_hypermap E r) = graph_reverse_dart E o inverse r /\
         face_map (graph_hypermap E r) = r`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP GRAPH_HYPERMAP_PRED) THEN
  REWRITE_TAC[graph_hypermap] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MK_HYPERMAP_COMPONENTS) THEN SIMP_TAC[]);;

(* The faces of graph_hypermap are the sets of darts out of one vertex       *)

let GRAPH_HYPERMAP_CFACE = prove
 (`!V (E:(A->bool)->bool) r d d'.
     finite_simple_graph V E /\ graph_rotation E r /\ d IN graph_darts E
     ==> (cface (graph_hypermap E r) d d' <=>
          d' IN graph_darts E /\ FST d' = FST d)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    GRAPH_HYPERMAP_COMPONENTS) THEN
  ASM_SIMP_TAC[cface; face; ORBIT_MAP_PERMUTATION_ORBIT;
               GRAPH_ROTATION_ORBIT_OUTGOING_DARTS; IN_OUTGOING_DARTS]);;

(* ------------------------------------------------------------------------- *)
(* Bridgeless: a face keeps FST, reverse_dart swaps FST and SND (<> on       *)
(* darts).                                                                   *)
(* ------------------------------------------------------------------------- *)

let GRAPH_HYPERMAP_BRIDGELESS = prove
 (`!V (E:(A->bool)->bool) r.
     finite_simple_graph V E /\ graph_rotation E r
     ==> bridgeless (graph_hypermap E r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    GRAPH_HYPERMAP_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[bridgeless; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:A`; `v:A`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`;
                `(u:A,v:A)`; `graph_reverse_dart E (u:A,v:A)`]
    GRAPH_HYPERMAP_CFACE) THEN
  ASM_SIMP_TAC[GRAPH_REVERSE_DART_IN; REVERSE_DART_PAIR] THEN
  ASM_MESON_TAC[FINITE_SIMPLE_GRAPH_DART]);;

(* ------------------------------------------------------------------------- *)
(* Counting: darts, edges, nodes (= graph faces), faces (= vertices).        *)
(* ------------------------------------------------------------------------- *)

let ORBIT_MAP_INVOLUTION = prove
 (`!(f:B->B) x. (!y. f (f y) = y) ==> orbit_map f x = {x, f x}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[orbit_map; EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:B` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
    SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ITER] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[];
    MESON_TAC[ITER; ONE]]);;

let CARD_DART_GRAPH_HYPERMAP = prove
 (`!V (E:(A->bool)->bool) r.
     finite_simple_graph V E /\ graph_rotation E r
     ==> CARD (dart (graph_hypermap E r)) = 2 * CARD E`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    GRAPH_HYPERMAP_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`] CARD_GRAPH_DARTS) THEN
  ASM_REWRITE_TAC[]);;

let GRAPH_HYPERMAP_PLAIN = prove
 (`!V (E:(A->bool)->bool) r.
     finite_simple_graph V E /\ graph_rotation E r
     ==> plain_hypermap (graph_hypermap E r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    GRAPH_HYPERMAP_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[plain_hypermap; orbit_size; ORBIT_MAP_INVOLUTION;
               GRAPH_REVERSE_DART_INVOLUTION] THEN
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
           NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[GRAPH_REVERSE_DART_NO_FIXEDPOINT;
                ARITH_RULE `SUC(SUC 0) = 2`]);;

let NUMBER_OF_EDGES_GRAPH_HYPERMAP = prove
 (`!V (E:(A->bool)->bool) r.
     finite_simple_graph V E /\ graph_rotation E r
     ==> number_of_edges (graph_hypermap E r) = CARD E`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    GRAPH_HYPERMAP_PLAIN) THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    CARD_DART_GRAPH_HYPERMAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP PLAIN_DART_CARD) THEN
                       REWRITE_TAC[th]) THEN
  ARITH_TAC);;

let SET_OF_ORBITS_INVERSE = prove
 (`!s (f:B->B). FINITE s /\ f permutes s
                ==> set_of_orbits s (inverse f) = set_of_orbits s f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[set_of_orbits; SIMPLE_IMAGE; EXTENSION; IN_IMAGE] THEN
  ASM_MESON_TAC[ORBIT_MAP_INVERSE]);;

let GRAPH_HYPERMAP_NODE_MAP_INVERSE = prove
 (`!(E:(A->bool)->bool) r.
     graph_rotation E r
     ==> graph_reverse_dart E o inverse r =
         inverse (graph_face_successor E r)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC INVERSE_UNIQUE_o THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GRAPH_ROTATION_PERMUTES) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES) THEN
  REWRITE_TAC[graph_face_successor; FUN_EQ_THM; o_THM; I_THM] THEN
  ASM_REWRITE_TAC[GRAPH_REVERSE_DART_INVOLUTION]);;

let NUMBER_OF_NODES_GRAPH_HYPERMAP = prove
 (`!V (E:(A->bool)->bool) r.
     finite_simple_graph V E /\ graph_rotation E r
     ==> number_of_nodes (graph_hypermap E r) = CARD (graph_faces E r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    GRAPH_HYPERMAP_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_GRAPH_DARTS) THEN
  ASM_SIMP_TAC[number_of_nodes; node_set; GRAPH_HYPERMAP_NODE_MAP_INVERSE;
               SET_OF_ORBITS_INVERSE; GRAPH_FACE_SUCCESSOR_PERMUTES] THEN
  REWRITE_TAC[GRAPH_FACES_AS_PERMUTATION_ORBITS;
              SET_OF_ORBITS_PERMUTATION_ORBITS]);;

let NUMBER_OF_FACES_GRAPH_HYPERMAP = prove
 (`!V (E:(A->bool)->bool) r.
     finite_simple_graph V E /\ connected_graph V E /\
     graph_rotation E r /\ ~(E = {})
     ==> number_of_faces (graph_hypermap E r) = CARD V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    GRAPH_HYPERMAP_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[number_of_faces; face_set;
                  SET_OF_ORBITS_PERMUTATION_ORBITS] THEN
  MATCH_MP_TAC GRAPH_ROTATION_ORBIT_COUNT THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Connected graph => connected hypermap (one component).                    *)
(* ------------------------------------------------------------------------- *)

let GCOMP_ITER_FACE_MAP = prove
 (`!(H:(B)hypermap) x n. gcomp H x (ITER n (face_map H) x)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER; GCOMP_REFL] THEN
  MATCH_MP_TAC GCOMP_TRANS THEN
  EXISTS_TAC `ITER n (face_map (H:(B)hypermap)) x` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GCOMP_GLINK THEN REWRITE_TAC[glink]);;

let GRAPH_HYPERMAP_GCOMP_SAME_FST = prove
 (`!V (E:(A->bool)->bool) r d d'.
     finite_simple_graph V E /\ graph_rotation E r /\
     d IN graph_darts E /\ d' IN graph_darts E /\ FST d = FST d'
     ==> gcomp (graph_hypermap E r) d d'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`;
                `d:A#A`; `d':A#A`] GRAPH_HYPERMAP_CFACE) THEN
  ASM_REWRITE_TAC[cface; face; orbit_map; IN_ELIM_THM] THEN
  MESON_TAC[GCOMP_ITER_FACE_MAP]);;

let GRAPH_HYPERMAP_GCOMP_REVERSE = prove
 (`!V (E:(A->bool)->bool) r d.
     finite_simple_graph V E /\ graph_rotation E r
     ==> gcomp (graph_hypermap E r) d (graph_reverse_dart E d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    GRAPH_HYPERMAP_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC GCOMP_GLINK THEN
  ASM_REWRITE_TAC[glink]);;

(* graph reachability (RTC of adjacency) transfers to gcomp between darts at *)
(* the two vertices                                                          *)

let GRAPH_HYPERMAP_REACHABLE = prove
 (`!V (E:(A->bool)->bool) r.
     finite_simple_graph V E /\ graph_rotation E r
     ==> !u v. graph_reachable E u v
               ==> u = v \/
                   ?d d'. d IN graph_darts E /\ d' IN graph_darts E /\
                          FST d = u /\ FST d' = v /\
                          gcomp (graph_hypermap E r) d d'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[graph_reachable] THEN
  MATCH_MP_TAC RTC_INDUCT THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN BETA_TAC THEN DISCH_TAC THEN
    DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`(x:A,y:A)`; `(y:A,x:A)`] THEN
    ASM_REWRITE_TAC[IN_GRAPH_DARTS; FST] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[INSERT_COMM]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:A,x:A) = graph_reverse_dart E (x,y)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[GRAPH_REVERSE_DART_IN; IN_GRAPH_DARTS; REVERSE_DART_PAIR];
      MATCH_MP_TAC GRAPH_HYPERMAP_GCOMP_REVERSE THEN ASM_MESON_TAC[]];
    GEN_TAC THEN DISJ1_TAC THEN REFL_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[GCOMP_TRANS; GRAPH_HYPERMAP_GCOMP_SAME_FST]]);;

let GRAPH_HYPERMAP_CONNECTED = prove
 (`!V (E:(A->bool)->bool) r.
     finite_simple_graph V E /\ connected_graph V E /\ graph_rotation E r
     ==> connected_hypermap (graph_hypermap E r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    GRAPH_HYPERMAP_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[connected_hypermap] THEN
  MAP_EVERY X_GEN_TAC [`x:A#A`; `y:A#A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST (x:A#A) IN V /\ FST (y:A#A) IN V` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SIMPLE_GRAPH_DART; PAIR]; ALL_TAC] THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    GRAPH_HYPERMAP_REACHABLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`FST(x:A#A)`; `FST(y:A#A)`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[connected_graph]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_MESON_TAC[GCOMP_TRANS; GRAPH_HYPERMAP_GCOMP_SAME_FST]);;

let NUMBER_OF_COMPONENTS_GRAPH_HYPERMAP = prove
 (`!V (E:(A->bool)->bool) r.
     finite_simple_graph V E /\ connected_graph V E /\
     graph_rotation E r /\ ~(E = {})
     ==> number_of_components (graph_hypermap E r) = 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CONNECTED_NCOMP THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GRAPH_HYPERMAP_CONNECTED THEN EXISTS_TAC `V:A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    GRAPH_HYPERMAP_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((E:(A->bool)->bool) = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `e:A->bool`) THEN
  SUBGOAL_THEN `(e:A->bool) HAS_SIZE 2` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [finite_simple_graph]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` (X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(u:A,v:A)` THEN ASM_REWRITE_TAC[IN_GRAPH_DARTS] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Euler's formula => genus 0.                                               *)
(* ------------------------------------------------------------------------- *)

let GRAPH_HYPERMAP_PLANAR = prove
 (`!V (E:(A->bool)->bool) r.
     finite_simple_graph V E /\ connected_graph V E /\ graph_rotation E r /\
     graph_euler_formula V E r /\ ~(E = {})
     ==> planar_hypermap (graph_hypermap E r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[planar_hypermap; genus; euler_lhs; euler_rhs] THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    NUMBER_OF_COMPONENTS_GRAPH_HYPERMAP) THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    CARD_DART_GRAPH_HYPERMAP) THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    NUMBER_OF_EDGES_GRAPH_HYPERMAP) THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    NUMBER_OF_NODES_GRAPH_HYPERMAP) THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    NUMBER_OF_FACES_GRAPH_HYPERMAP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  UNDISCH_TAC `graph_euler_formula (V:A->bool) E r` THEN
  ASM_REWRITE_TAC[graph_euler_formula; graph_map_faces] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Colours as numbers below 4.                                               *)
(* ------------------------------------------------------------------------- *)

let color_num = define
 `color_num Color0 = 0 /\ color_num Color1 = 1 /\ color_num Color2 = 2 /\
  color_num Color3 = 3`;;

let COLOR_NUM_LT_4 = prove
 (`!c. color_num c < 4`,
  MATCH_MP_TAC color_INDUCT THEN REWRITE_TAC[color_num] THEN ARITH_TAC);;

let COLOR_NUM_INJ = prove
 (`!c c'. color_num c = color_num c' <=> c = c'`,
  REPEAT(MATCH_MP_TAC color_INDUCT THEN REPEAT CONJ_TAC) THEN
  REWRITE_TAC[color_num; distinctness "color"] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The connected case, parametrised by the hypermap theorem, then all        *)
(* graphs.                                                                   *)
(* ------------------------------------------------------------------------- *)

let proper_coloring = new_definition
 `proper_coloring (V:A->bool) (E:(A->bool)->bool) (c:A->num) <=>
    (!v. v IN V ==> c v < 4) /\ (!u v. {u,v} IN E ==> ~(c u = c v))`;;

(* The colouring is constant on the darts of a vertex (they form one r-orbit *)
(* = one face of graph_hypermap)                                             *)

let COLORING_GRAPH_HYPERMAP_SAME_FST = prove
 (`!V (E:(A->bool)->bool) r k d d'.
     finite_simple_graph V E /\ graph_rotation E r /\
     coloring (graph_hypermap E r) k /\
     d IN graph_darts E /\ d' IN graph_darts E /\ FST d = FST d'
     ==> k d' = k d`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CFACE_COLORING THEN
  EXISTS_TAC `graph_hypermap (E:(A->bool)->bool) r` THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    GRAPH_HYPERMAP_COMPONENTS) THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`;
                `d:A#A`; `d':A#A`] GRAPH_HYPERMAP_CFACE) THEN
  ASM_SIMP_TAC[]);;

(* A vertex gets the colour of any dart out of it                            *)

let FOUR_COLOR_CONNECTED_GRAPH_OF_HYPERMAP = prove
 (`(!H:(A#A)hypermap. planar_hypermap H /\ bridgeless H ==> four_colorable H)
   ==> !V (E:(A->bool)->bool) r.
         finite_simple_graph V E /\ connected_graph V E /\
         graph_rotation E r /\ graph_euler_formula V E r
         ==> ?c. proper_coloring V E c`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(E:(A->bool)->bool) = {}` THENL
   [EXISTS_TAC `(\v:A. 0)` THEN
    ASM_REWRITE_TAC[proper_coloring; NOT_IN_EMPTY] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `four_colorable (graph_hypermap (E:(A->bool)->bool) r)`
  MP_TAC THENL
   [ASM_MESON_TAC[GRAPH_HYPERMAP_PLANAR; GRAPH_HYPERMAP_BRIDGELESS];
    REWRITE_TAC[four_colorable; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `k:A#A->color` THEN DISCH_TAC THEN
  EXISTS_TAC `\v:A. color_num (k (@d:A#A. d IN outgoing_darts E v))` THEN
  REWRITE_TAC[proper_coloring; COLOR_NUM_LT_4; COLOR_NUM_INJ] THEN
  SUBGOAL_THEN
   `!x y:A. {x,y} IN E
            ==> k(@d:A#A. d IN outgoing_darts E x):color = k(x,y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COLORING_GRAPH_HYPERMAP_SAME_FST THEN
    MAP_EVERY EXISTS_TAC [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    THEN
    SUBGOAL_THEN `(@d:A#A. d IN outgoing_darts E x) IN outgoing_darts E x`
    MP_TAC THENL
     [CONV_TAC SELECT_CONV THEN EXISTS_TAC `(x:A,y:A)` THEN
      ASM_REWRITE_TAC[IN_OUTGOING_DARTS_PAIR];
      ASM_SIMP_TAC[IN_OUTGOING_DARTS; IN_GRAPH_DARTS]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:A`; `v:A`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `{v:A,u} IN E` ASSUME_TAC THENL
   [ASM_MESON_TAC[INSERT_COMM]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`u:A`; `v:A`] th) THEN
                          MP_TAC(SPECL [`v:A`; `u:A`] th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`V:A->bool`; `E:(A->bool)->bool`; `r:(A#A)->A#A`]
    GRAPH_HYPERMAP_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(u:A,v:A)` o CONJUNCT1 o
    GEN_REWRITE_RULE I [coloring]) THEN
  ASM_SIMP_TAC[IN_GRAPH_DARTS; GRAPH_REVERSE_DART_IN; REVERSE_DART_PAIR] THEN
  MESON_TAC[]);;

(* Each component gets the colouring chosen for it (col depends only on the  *)
(* component, a set)                                                         *)

let FOUR_COLOR_PLANAR_GRAPH_OF_HYPERMAP = prove
 (`(!H:(A#A)hypermap. planar_hypermap H /\ bridgeless H ==> four_colorable H)
   ==> !V (E:(A->bool)->bool). planar_graph V E ==> ?c. proper_coloring V E c`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PLANAR_GRAPH_EQ_EULER_ROTATIONS; euler_planar_rotation] THEN
  STRIP_TAC THEN
  ABBREV_TAC
   `col = \u:A. @c:A->num. proper_coloring (graph_component E u)
                                           (graph_component_edges E u) c` THEN
  SUBGOAL_THEN
   `!u:A. u IN V
          ==> proper_coloring (graph_component E u)
                              (graph_component_edges E u) (col u)`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:A` THEN DISCH_TAC THEN EXPAND_TAC "col" THEN
    CONV_TAC SELECT_CONV THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `r:(A#A)->A#A` STRIP_ASSUME_TAC o
      C MATCH_MP (ASSUME `(u:A) IN V`)) THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP FOUR_COLOR_CONNECTED_GRAPH_OF_HYPERMAP)
    THEN EXISTS_TAC `r:(A#A)->A#A` THEN
    ASM_MESON_TAC[GRAPH_COMPONENT_EDGES_CONNECTED];
    ALL_TAC] THEN
  EXISTS_TAC `\v:A. (col:A->A->num) v v` THEN
  REWRITE_TAC[proper_coloring] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[proper_coloring; GRAPH_COMPONENT_REFL]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:A`; `v:A`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(u:A) IN V /\ (v:A) IN V` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SIMPLE_GRAPH_DART; IN_GRAPH_DARTS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `graph_component E (v:A) = graph_component E u /\
    graph_component_edges E v = graph_component_edges E u`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[GRAPH_COMPONENT_EQ; GRAPH_COMPONENT_EDGES_EQ;
                  GRAPH_EDGE_IMP_REACHABLE; GRAPH_REACHABLE_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(col:A->A->num) v = col u` SUBST1_TAC THENL
   [EXPAND_TAC "col" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:A`) THEN
  ASM_REWRITE_TAC[proper_coloring] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  ASM_REWRITE_TAC[IN_GRAPH_COMPONENT_EDGES; INSERT_SUBSET; EMPTY_SUBSET] THEN
  ASM_MESON_TAC[GRAPH_COMPONENT_REFL; IN_GRAPH_COMPONENT;
                GRAPH_EDGE_IMP_REACHABLE]);;

(* ------------------------------------------------------------------------- *)
(* Four colours are needed: the complete graph on four vertices is planar    *)
(* but not 3-colourable (planarity by KURATOWSKI, as a subdivision of K5 or  *)
(* K3,3 has at least five vertices).                                         *)
(* ------------------------------------------------------------------------- *)

let PLANAR_K4_NOT_3_COLORABLE = prove
 (`planar_graph {0,1,2,3} (complete_graph_edges {0,1,2,3}) /\
   ~(?c. (!v. v IN {0,1,2,3} ==> c v < 3) /\
         (!u v. {u,v} IN complete_graph_edges {0,1,2,3} ==> ~(c u = c v)))`,
  CONJ_TAC THENL
   [SIMP_TAC[KURATOWSKI; FINITE_SIMPLE_COMPLETE_GRAPH; FINITE_INSERT;
             FINITE_EMPTY] THEN
    REWRITE_TAC[graph_kuratowski_obstruction] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GRAPH_SUBDIVISION_SOURCE_SUBSET) THEN
    DISCH_TAC THENL
     [SUBGOAL_THEN `CARD(W:num->bool) <= CARD {0,1,2,3}` MP_TAC;
      SUBGOAL_THEN `CARD(X UNION Y:num->bool) <= CARD {0,1,2,3}` MP_TAC] THEN
    TRY(MATCH_MP_TAC CARD_SUBSET THEN
        ASM_MESON_TAC[SUBSET_TRANS; FINITE_INSERT; FINITE_EMPTY]) THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
             NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE; DISJOINT]) THEN
    ASM_SIMP_TAC[CARD_UNION] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[NOT_EXISTS_THM; IN_COMPLETE_GRAPH_EDGES; FORALL_IN_INSERT;
                NOT_IN_EMPTY] THEN
    X_GEN_TAC `c:num->num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(fun th -> MAP_EVERY (fun (u,v) -> MP_TAC(SPECL [u;v] th))
     [`0`,`1`; `0`,`2`; `0`,`3`; `1`,`2`; `1`,`3`; `2`,`3`]) THEN
    SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT; NOT_IN_EMPTY; HAS_SIZE;
             FINITE_INSERT; FINITE_EMPTY; CARD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]);;
