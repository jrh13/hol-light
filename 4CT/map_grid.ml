(* ========================================================================= *)
(* 4CT/map_grid.ml                                                           *)
(*                                                                           *)
(* The adjacency graph of a finite plane map is planar                       *)
(* (ADJACENCY_GRAPH_PLANAR), being a minor of a grid graph.  A finite grid   *)
(* graph on num#num is straight-line planar.  The territory of a region is   *)
(* the set of lattice points within sup-norm distance h of a compact         *)
(* connected skeleton inside the region; at each adjacency, free lattice     *)
(* points of an L-shaped path inside a small ball around a border point join *)
(* the two territories.  The territories with their free points are the      *)
(* branch sets of a minor (GRAPH_BRANCH_MODEL_IMP_MINOR), and planarity is   *)
(* minor-closed (PLANAR_GRAPH_MINOR), both from planar_graph.ml.  Loads      *)
(* after map_defs.ml.                                                        *)
(* ========================================================================= *)

needs "4CT/map_defs.ml";;

(* ------------------------------------------------------------------------- *)
(* The grid graph on {0..N} x {0..N} and its straight-line drawing.          *)
(* ------------------------------------------------------------------------- *)

let grid_vertices = new_definition
 `grid_vertices (N:num) = {(i,j) | i <= N /\ j <= N}`;;

let grid_edges = new_definition
 `grid_edges (N:num) =
    {{(i,j),(SUC i,j)} | i < N /\ j <= N} UNION
    {{(i,j),(i,SUC j)} | i <= N /\ j < N}`;;

let grid_point = new_definition
 `grid_point (c:real^2) (h:real) (p:num#num) =
    c + h % vector[&(FST p); &(SND p)]`;;

let GRID_POINT_COMPONENTS = prove
 (`!c h i j. (grid_point c h (i,j))$1 = c$1 + h * &i /\
             (grid_point c h (i,j))$2 = c$2 + h * &j`,
  REWRITE_TAC[grid_point; FST; SND; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              VECTOR_2]);;

let IN_SEGMENT_GRID = prove
 (`!c h i j x.
     &0 < h
     ==> (x IN segment[grid_point c h (i,j),grid_point c h (SUC i,j)] <=>
          x$2 = c$2 + h * &j /\
          c$1 + h * &i <= x$1 /\ x$1 <= c$1 + h * &(SUC i)) /\
         (x IN segment[grid_point c h (i,j),grid_point c h (i,SUC j)] <=>
          x$1 = c$1 + h * &i /\
          c$2 + h * &j <= x$2 /\ x$2 <= c$2 + h * &(SUC j))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; GRID_POINT_COMPONENTS;
              GSYM REAL_OF_NUM_SUC] THEN
  CONJ_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`u:real`; `h:real`] REAL_LE_MUL) THEN
    MP_TAC(SPECL [`&1 - u`; `h:real`] REAL_LE_MUL) THEN
    ASM_REWRITE_TAC[REAL_SUB_LE] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REAL_ARITH_TAC;
    STRIP_TAC THEN
    EXISTS_TAC `((x:real^2)$1 - ((c:real^2)$1 + h * &i)) / h`;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`u:real`; `h:real`] REAL_LE_MUL) THEN
    MP_TAC(SPECL [`&1 - u`; `h:real`] REAL_LE_MUL) THEN
    ASM_REWRITE_TAC[REAL_SUB_LE] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REAL_ARITH_TAC;
    STRIP_TAC THEN
    EXISTS_TAC `((x:real^2)$2 - ((c:real^2)$2 + h * &j)) / h`] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_SUB_LE; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let GRID_POINT_EQ = prove
 (`!c h p q. &0 < h ==> (grid_point c h p = grid_point c h q <=> p = q)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(fun th -> MP_TAC(AP_TERM `\v:real^2. v$1` th) THEN
                         MP_TAC(AP_TERM `\v:real^2. v$2` th)) THEN
    REWRITE_TAC[GRID_POINT_COMPONENTS; REAL_EQ_ADD_LCANCEL] THEN
    ASM_SIMP_TAC[REAL_EQ_MUL_LCANCEL; REAL_LT_IMP_NZ; REAL_OF_NUM_EQ] THEN
    MESON_TAC[];
    SIMP_TAC[]]);;

let IN_GRID_VERTICES = prove
 (`!N i j. (i,j) IN grid_vertices N <=> i <= N /\ j <= N`,
  REWRITE_TAC[grid_vertices; IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

let IN_GRID_EDGES = prove
 (`!N e. e IN grid_edges N <=>
         (?i j. i < N /\ j <= N /\ e = {(i,j),(SUC i,j)}) \/
         (?i j. i <= N /\ j < N /\ e = {(i,j),(i,SUC j)})`,
  REWRITE_TAC[grid_edges; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]);;

let FINITE_GRID_VERTICES = prove
 (`!N. FINITE(grid_vertices N)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{(i:num,j:num) | i IN {m | m <= N} /\ j IN {m | m <= N}}` THEN
  SIMP_TAC[FINITE_PRODUCT; FINITE_NUMSEG_LE] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_GRID_VERTICES; IN_ELIM_THM;
              PAIR_EQ] THEN
  MESON_TAC[]);;

let FINITE_GRID_EDGES = prove
 (`!N. FINITE(grid_edges N)`,
  GEN_TAC THEN REWRITE_TAC[grid_edges; FINITE_UNION] THEN CONJ_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THENL
   [EXISTS_TAC `IMAGE (\p:num#num. {p,(SUC(FST p),SND p)}) (grid_vertices N)`;
    EXISTS_TAC
     `IMAGE (\p:num#num. {p,(FST p,SUC(SND p))}) (grid_vertices N)`] THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_GRID_VERTICES] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM; EXISTS_PAIR_THM;
              IN_GRID_VERTICES] THEN
  REWRITE_TAC[FST; SND] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN ASM_SIMP_TAC[LT_IMP_LE]);;

let FINITE_SIMPLE_GRAPH_GRID = prove
 (`!N. finite_simple_graph (grid_vertices N) (grid_edges N)`,
  GEN_TAC THEN
  REWRITE_TAC[finite_simple_graph; FINITE_GRID_VERTICES;
              FINITE_GRID_EDGES] THEN
  REWRITE_TAC[IN_GRID_EDGES] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_GRID_VERTICES] THEN
  ASM_SIMP_TAC[LT_IMP_LE; LE_SUC_LT; LE_REFL] THEN
  SIMP_TAC[HAS_SIZE; FINITE_INSERT; FINITE_EMPTY; CARD_CLAUSES; IN_INSERT;
           NOT_IN_EMPTY; PAIR_EQ; ARITH_RULE `~(SUC i = i)`] THEN ARITH_TAC);;

let GRID_INTERVAL_LEMMA = prove
 (`!h c i i' y. &0 < h /\ ~(i = i') /\
        c + h * &i <= y /\ y <= c + h * &(SUC i) /\
        c + h * &i' <= y /\ y <= c + h * &(SUC i')
        ==> ?k. y = c + h * &k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `h * &(SUC i) <= h * &i' \/ h * &(SUC i') <= h * &i`
  MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL [EXISTS_TAC `SUC i`; EXISTS_TAC `SUC i'`] THEN
  ASM_REAL_ARITH_TAC);;

let GRID_POINT_IN_GRID_EDGE = prove
 (`!N c h e q. &0 < h /\ e IN grid_edges N /\
               grid_point c h q IN straight_edge (grid_point c h) e
               ==> q IN e`,
  REWRITE_TAC[FORALL_PAIR_THM; IN_GRID_EDGES] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
  ASM_SIMP_TAC[STRAIGHT_EDGE_PAIR; IN_SEGMENT_GRID; GRID_POINT_COMPONENTS] THEN
  REWRITE_TAC[REAL_EQ_ADD_LCANCEL; REAL_LE_LADD] THEN
  ASM_SIMP_TAC[REAL_EQ_MUL_LCANCEL; REAL_LE_LMUL_EQ; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; REAL_OF_NUM_LE; IN_INSERT; NOT_IN_EMPTY;
              PAIR_EQ] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Reachability along rows, columns and L-shaped lattice paths.              *)
(* ------------------------------------------------------------------------- *)

let GRID_REACHABLE_ROW = prove
 (`!N B i i' j.
        i <= N /\ i' <= N /\ j <= N /\
        (!k. (i <= k /\ k <= i') \/ (i' <= k /\ k <= i) ==> (k,j) IN B)
        ==> graph_reachable (induced_subgraph_edges (grid_edges N) B)
                            (i,j) (i',j)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
   [MESON_TAC[GRAPH_REACHABLE_SYM]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`induced_subgraph_edges (grid_edges N) B`;
                 `\k. (i + k:num,j:num)`; `d + 1`]
                GRAPH_REACHABLE_CHAIN_FROM_FIRST) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `d:num`) THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `d < d + 1`]] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_INDUCED_SUBGRAPH_EDGES; INSERT_SUBSET; EMPTY_SUBSET;
              IN_GRID_EDGES] THEN
  REPEAT CONJ_TAC THENL
   [DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`i + k:num`; `j:num`] THEN
    REWRITE_TAC[ADD_CLAUSES; ADD1; ADD_ASSOC] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let GRID_REACHABLE_COLUMN = prove
 (`!N B j j' i.
        j <= N /\ j' <= N /\ i <= N /\
        (!l. (j <= l /\ l <= j') \/ (j' <= l /\ l <= j) ==> (i,l) IN B)
        ==> graph_reachable (induced_subgraph_edges (grid_edges N) B)
                            (i,j) (i,j')`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
   [MESON_TAC[GRAPH_REACHABLE_SYM]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`induced_subgraph_edges (grid_edges N) B`;
                 `\l. (i:num,j + l:num)`; `d + 1`]
                GRAPH_REACHABLE_CHAIN_FROM_FIRST) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `d:num`) THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `d < d + 1`]] THEN
  X_GEN_TAC `l:num` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_INDUCED_SUBGRAPH_EDGES; INSERT_SUBSET; EMPTY_SUBSET;
              IN_GRID_EDGES] THEN
  REPEAT CONJ_TAC THENL
   [DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`i:num`; `j + l:num`] THEN
    REWRITE_TAC[ADD_CLAUSES; ADD1; ADD_ASSOC] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let GRID_REACHABLE_LPATH = prove
 (`!N B i j i' j'. i <= N /\ j <= N /\ i' <= N /\ j' <= N /\
        (!k. (i <= k /\ k <= i') \/ (i' <= k /\ k <= i) ==> (k,j) IN B) /\
        (!l. (j <= l /\ l <= j') \/ (j' <= l /\ l <= j) ==> (i',l) IN B)
        ==> graph_reachable (induced_subgraph_edges (grid_edges N) B)
                            (i,j) (i',j')`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GRAPH_REACHABLE_TRANS THEN
  EXISTS_TAC `(i':num,j:num)` THEN
  ASM_SIMP_TAC[GRID_REACHABLE_ROW; GRID_REACHABLE_COLUMN]);;

(* ------------------------------------------------------------------------- *)
(* Two distinct grid segments meet only at lattice points, hence only at     *)
(* common endpoints: the grid graph is straight-line planar.                 *)
(* ------------------------------------------------------------------------- *)

let GRID_SEGMENTS_MEET_LATTICE = prove
 (`!N c h e e' x.
        &0 < h /\ e IN grid_edges N /\ e' IN grid_edges N /\ ~(e = e') /\
        x IN straight_edge (grid_point c h) e /\
        x IN straight_edge (grid_point c h) e'
        ==> ?q. x = grid_point c h q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_GRID_EDGES] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STRAIGHT_EDGE_PAIR]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_binary "IN" o concl))) THEN
  ASM_SIMP_TAC[IN_SEGMENT_GRID] THENL
   [STRIP_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&j':real = &j` MP_TAC THENL
     [ASM_MESON_TAC[REAL_EQ_ADD_LCANCEL; REAL_EQ_MUL_LCANCEL; REAL_LT_IMP_NZ];
      REWRITE_TAC[REAL_OF_NUM_EQ] THEN DISCH_THEN SUBST_ALL_TAC] THEN
    SUBGOAL_THEN `~(i:num = i')` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`h:real`; `(c:real^2)$1`; `i:num`; `i':num`; `(x:real^2)$1`]
      GRID_INTERVAL_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    EXISTS_TAC `(k:num,j:num)`;
    STRIP_TAC THEN STRIP_TAC THEN EXISTS_TAC `(i':num,j:num)`;
    STRIP_TAC THEN STRIP_TAC THEN EXISTS_TAC `(i:num,j':num)`;
    STRIP_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&i':real = &i` MP_TAC THENL
     [ASM_MESON_TAC[REAL_EQ_ADD_LCANCEL; REAL_EQ_MUL_LCANCEL; REAL_LT_IMP_NZ];
      REWRITE_TAC[REAL_OF_NUM_EQ] THEN DISCH_THEN SUBST_ALL_TAC] THEN
    SUBGOAL_THEN `~(j:num = j')` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`h:real`; `(c:real^2)$2`; `j:num`; `j':num`; `(x:real^2)$2`]
      GRID_INTERVAL_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    EXISTS_TAC `(i:num,k:num)`] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; GRID_POINT_COMPONENTS] THEN
  ASM_REWRITE_TAC[]);;

let STRAIGHT_LINE_EMBEDDING_GRID = prove
 (`!N c h. &0 < h
           ==> straight_line_embedding (grid_vertices N) (grid_edges N)
                                       (grid_point c h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[straight_line_embedding] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INJ; IN_UNIV] THEN ASM_SIMP_TAC[GRID_POINT_EQ];
    X_GEN_TAC `e:num#num->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      ASM_MESON_TAC[GRID_POINT_IN_GRID_EDGE];
      REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
       [REWRITE_TAC[straight_edge; HULL_SUBSET];
        MATCH_MP_TAC IMAGE_SUBSET THEN
        MP_TAC(SPEC `N:num` FINITE_SIMPLE_GRAPH_GRID) THEN
        REWRITE_TAC[finite_simple_graph] THEN ASM_MESON_TAC[]]];
    MAP_EVERY X_GEN_TAC [`e:num#num->bool`; `e':num#num->bool`] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^2` THEN
      STRIP_TAC THEN
      MP_TAC(SPECL [`N:num`; `c:real^2`; `h:real`; `e:num#num->bool`;
                    `e':num#num->bool`; `x:real^2`]
                   GRID_SEGMENTS_MEET_LATTICE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:num#num` SUBST_ALL_TAC) THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `q:num#num` THEN
      ASM_MESON_TAC[GRID_POINT_IN_GRID_EDGE];
      REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE; straight_edge] THEN
      MESON_TAC[HULL_SUBSET; SUBSET; IN_IMAGE; IN_INTER]]]);;

let PLANAR_GRAPH_GRID = prove
 (`!N. planar_graph (grid_vertices N) (grid_edges N)`,
  GEN_TAC THEN MATCH_MP_TAC STRAIGHT_LINE_PLANAR_IMP_PLANAR_GRAPH THEN
  REWRITE_TAC[straight_line_planar_graph; FINITE_SIMPLE_GRAPH_GRID] THEN
  EXISTS_TAC `grid_point (vec 0) (&1)` THEN
  MATCH_MP_TAC STRAIGHT_LINE_EMBEDDING_GRID THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Elementary auxiliary lemmas.                                              *)
(* ------------------------------------------------------------------------- *)

let FINITE_POSITIVE_LOWER_BOUND = prove
 (`!f:A->real s. FINITE s /\ (!x. x IN s ==> &0 < f x)
                 ==> ?d. &0 < d /\ !x. x IN s ==> d <= f x`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `inf(&1 INSERT IMAGE (f:A->real) s)` THEN
  ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_INSERT; FINITE_IMAGE; INF_FINITE;
               NOT_INSERT_EMPTY; FORALL_IN_INSERT; FORALL_IN_IMAGE;
               REAL_LT_01] THEN
  ASM_MESON_TAC[INF_FINITE; FINITE_INSERT; FINITE_IMAGE; NOT_INSERT_EMPTY;
                IN_INSERT; FUN_IN_IMAGE]);;

let GRID_COVER = prove
 (`!(c:real^2) h N (y:real^2).
        &0 < h /\
        c$1 <= y$1 /\ y$1 <= c$1 + h * &N /\
        c$2 <= y$2 /\ y$2 <= c$2 + h * &N
        ==> ?i j. i <= N /\ j <= N /\
                  abs((grid_point c h (i,j))$1 - y$1) <= h /\
                  abs((grid_point c h (i,j))$2 - y$2) <= h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `((y:real^2)$1 - (c:real^2)$1) / h` FLOOR_POS) THEN
  MP_TAC(SPEC `((y:real^2)$2 - (c:real^2)$2) / h` FLOOR_POS) THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN DISCH_THEN(X_CHOOSE_TAC `i:num`) THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN
  REWRITE_TAC[GRID_POINT_COMPONENTS] THEN
  MP_TAC(SPEC `((y:real^2)$1 - (c:real^2)$1) / h` FLOOR) THEN
  MP_TAC(SPEC `((y:real^2)$2 - (c:real^2)$2) / h` FLOOR) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ] THEN
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `&i * h <= &N * h` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_OF_NUM_LE]];
    SUBGOAL_THEN `&j * h <= &N * h` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_OF_NUM_LE]];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let IN_SUP_BOX = prove
 (`!a x:real^2 h. x IN interval[a - h % vec 1,a + h % vec 1] <=>
                  abs(a$1 - x$1) <= h /\ abs(a$2 - x$2) <= h`,
  SIMP_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
           VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT; ARITH;
           REAL_MUL_RID] THEN
  REAL_ARITH_TAC);;

let DIST_LE_COMPONENTS_2 = prove
 (`!x y:real^2. dist(x,y) <= abs(x$1 - y$1) + abs(x$2 - y$2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dist] THEN
  MP_TAC(ISPEC `x - y:real^2` NORM_LE_L1) THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2; VECTOR_SUB_COMPONENT]);;

let DIST_COMPONENT_BOUND_2 = prove
 (`!x y:real^2. abs(x$1 - y$1) <= dist(x,y) /\ abs(x$2 - y$2) <= dist(x,y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dist] THEN
  MP_TAC(ISPEC `x - y:real^2` COMPONENT_LE_NORM) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The lattice points within sup-norm distance h of a set K.                 *)
(* ------------------------------------------------------------------------- *)

let grid_near = new_definition
 `grid_near (c:real^2) (h:real) (N:num) (K:real^2->bool) =
    {g | g IN grid_vertices N /\
         ?x. x IN K /\ abs((grid_point c h g)$1 - x$1) <= h /\
                       abs((grid_point c h g)$2 - x$2) <= h}`;;

let IN_GRID_NEAR = prove
 (`!c h N K g. g IN grid_near c h N K <=>
               g IN grid_vertices N /\
               ?x. x IN K /\ abs((grid_point c h g)$1 - x$1) <= h /\
                             abs((grid_point c h g)$2 - x$2) <= h`,
  REWRITE_TAC[grid_near; IN_ELIM_THM]);;

let GRID_NEAR_SUBSET = prove
 (`!c h N K. grid_near c h N K SUBSET grid_vertices N`,
  REWRITE_TAC[SUBSET; IN_GRID_NEAR] THEN MESON_TAC[]);;

let GRID_NEAR_IN_REGION = prove
 (`!c h N K r g. &0 < h /\ (!x y. x IN K /\ dist(x,y) <= &2 * h ==> y IN r) /\
                 g IN grid_near c h N K
                 ==> grid_point c h g IN r`,
  REWRITE_TAC[IN_GRID_NEAR] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x:real^2` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`x:real^2`; `grid_point c h g`] DIST_LE_COMPONENTS_2) THEN
  ASM_REAL_ARITH_TAC);;

let GRID_NEAR_NONEMPTY = prove
 (`!(c:real^2) h N K (x:real^2).
        &0 < h /\ x IN K /\
        c$1 <= x$1 /\ x$1 <= c$1 + h * &N /\ c$2 <= x$2 /\ x$2 <= c$2 + h * &N
        ==> ?g. g IN grid_near c h N K /\
                abs((grid_point c h g)$1 - x$1) <= h /\
                abs((grid_point c h g)$2 - x$2) <= h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real^2`; `h:real`; `N:num`; `x:real^2`] GRID_COVER) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  EXISTS_TAC `(i:num,j:num)` THEN
  ASM_REWRITE_TAC[IN_GRID_NEAR; IN_GRID_VERTICES] THEN
  EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[]);;

let GRID_NEAR_DISJOINT = prove
 (`!c h N K1 K2 r1 r2.
        &0 < h /\
        (!x y. x IN K1 /\ dist(x,y) <= &2 * h ==> y IN r1) /\
        (!x y. x IN K2 /\ dist(x,y) <= &2 * h ==> y IN r2) /\
        DISJOINT r1 r2
        ==> DISJOINT (grid_near c h N K1) (grid_near c h N K2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `g:num#num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `grid_point c h g IN r1 /\ grid_point c h g IN r2` MP_TAC THENL
   [ASM_MESON_TAC[GRID_NEAR_IN_REGION]; ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The set of lattice points on the L-shaped path from p to q.               *)
(* ------------------------------------------------------------------------- *)

let grid_lpath = new_definition
 `grid_lpath (p:num#num) (q:num#num) =
    {g | SND g = SND p /\
         ((FST p <= FST g /\ FST g <= FST q) \/
         (FST q <= FST g /\ FST g <= FST p)) \/
         FST g = FST q /\
         ((SND p <= SND g /\ SND g <= SND q) \/
         (SND q <= SND g /\ SND g <= SND p))}`;;

let IN_GRID_LPATH = prove
 (`!i j i' j' k l. (k,l) IN grid_lpath (i,j) (i',j') <=>
        l = j /\ ((i <= k /\ k <= i') \/ (i' <= k /\ k <= i)) \/
        k = i' /\ ((j <= l /\ l <= j') \/ (j' <= l /\ l <= j))`,
  REWRITE_TAC[grid_lpath; IN_ELIM_THM; FST; SND]);;

let GRID_LPATH_ENDS = prove
 (`!p q. p IN grid_lpath p q /\ q IN grid_lpath p q`,
  REWRITE_TAC[FORALL_PAIR_THM; IN_GRID_LPATH] THEN ARITH_TAC);;

let GRID_LPATH_SUBSET = prove
 (`!N p q. p IN grid_vertices N /\ q IN grid_vertices N
           ==> grid_lpath p q SUBSET grid_vertices N`,
  REWRITE_TAC[FORALL_PAIR_THM; SUBSET; IN_GRID_LPATH; IN_GRID_VERTICES] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_ARITH_TAC);;

let GRID_LPATH_REACHABLE = prove
 (`!N p q g.
        p IN grid_vertices N /\ q IN grid_vertices N /\ g IN grid_lpath p q
        ==> graph_reachable
             (induced_subgraph_edges (grid_edges N) (grid_lpath p q)) p g`,
  REWRITE_TAC[FORALL_PAIR_THM; IN_GRID_VERTICES] THEN
  MAP_EVERY X_GEN_TAC
    [`N:num`; `i:num`; `j:num`; `i':num`; `j':num`; `k:num`; `l:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC GRID_REACHABLE_LPATH THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_GRID_LPATH]) THEN
  REWRITE_TAC[IN_GRID_LPATH] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY ASM_ARITH_TAC THEN
  REPEAT GEN_TAC THEN ASM_ARITH_TAC);;

let GRID_LPATH_CONNECTED = prove
 (`!N p q. p IN grid_vertices N /\ q IN grid_vertices N
           ==> connected_graph (grid_lpath p q)
                               (induced_subgraph_edges (grid_edges N)
                                                       (grid_lpath p q))`,
  REWRITE_TAC[connected_graph] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC GRAPH_REACHABLE_TRANS THEN EXISTS_TAC `p:num#num` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GRAPH_REACHABLE_SYM; ALL_TAC] THEN
  MATCH_MP_TAC GRID_LPATH_REACHABLE THEN ASM_REWRITE_TAC[]);;

let GRID_LPATH_BOX = prove
 (`!c h p q g a1 a2 d1 d2.
        &0 < h /\ g IN grid_lpath p q /\
        abs((grid_point c h p)$1 - a1) <= d1 /\
        abs((grid_point c h q)$1 - a1) <= d1 /\
        abs((grid_point c h p)$2 - a2) <= d2 /\
        abs((grid_point c h q)$2 - a2) <= d2
        ==> abs((grid_point c h g)$1 - a1) <= d1 /\
            abs((grid_point c h g)$2 - a2) <= d2`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`c:real^2`; `h:real`; `i:num`; `j:num`; `i':num`; `j':num`;
    `k:num`; `l:num`] THEN
  REWRITE_TAC[IN_GRID_LPATH; GRID_POINT_COMPONENTS] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))
  THENL
   [SUBGOAL_THEN `(h * &i <= h * &k /\ h * &k <= h * &i') \/
                  (h * &i' <= h * &k /\ h * &k <= h * &i)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_OF_NUM_LE]; ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `(h * &j <= h * &l /\ h * &l <= h * &j') \/
                  (h * &j' <= h * &l /\ h * &l <= h * &j)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_OF_NUM_LE]; ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Attaching free vertices: inside a connected vertex set S, a connected set *)
(* P meeting S can be extended by vertices Z of S outside P and Y until it   *)
(* has an edge into a target set Y SUBSET S disjoint from P.  Z is the set   *)
(* of vertices outside P reachable from P INTER S within S DIFF Y.           *)
(* ------------------------------------------------------------------------- *)

let GRAPH_ATTACH_LEMMA = prove
 (`!E S P Y:A->bool.
    connected_graph S (induced_subgraph_edges E S) /\
    connected_graph P (induced_subgraph_edges E P) /\
    ~(P INTER S = {}) /\ Y SUBSET S /\ ~(Y = {}) /\ DISJOINT P Y
    ==> ?Z u v. Z SUBSET S /\ DISJOINT Z P /\ DISJOINT Z Y /\
                connected_graph (P UNION Z)
                (induced_subgraph_edges E (P UNION Z)) /\
                u IN P UNION Z /\ v IN Y /\ {u,v} IN E`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R = induced_subgraph_edges (E:(A->bool)->bool) (S DIFF Y)` THEN
  ABBREV_TAC `A = {g:A | ?x. x IN P INTER S /\ graph_reachable R x g}` THEN
  SUBGOAL_THEN
   `!x g:A. x IN P INTER S /\ graph_reachable R x g
            ==> g IN S DIFF Y /\
                graph_reachable (induced_subgraph_edges E A) x g`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`R:(A->bool)->bool`;
      `{g:A | g IN S DIFF Y /\ graph_reachable R x g /\
              graph_reachable (induced_subgraph_edges E A) x g}`;
      `x:A`; `g:A`] GRAPH_REACHABLE_CLOSED) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; GRAPH_REACHABLE_REFL] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `graph_reachable R (x:A) b` ASSUME_TAC THENL
     [ASM_MESON_TAC[GRAPH_REACHABLE_TRANS; GRAPH_EDGE_IMP_REACHABLE];
      ALL_TAC] THEN
    UNDISCH_TAC `{a:A,b} IN R` THEN EXPAND_TAC "R" THEN
    REWRITE_TAC[IN_INDUCED_SUBGRAPH_EDGES; INSERT_SUBSET; EMPTY_SUBSET] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GRAPH_REACHABLE_TRANS THEN EXISTS_TAC `a:A` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GRAPH_EDGE_IMP_REACHABLE THEN
    ASM_REWRITE_TAC[IN_INDUCED_SUBGRAPH_EDGES; INSERT_SUBSET;
                    EMPTY_SUBSET] THEN
    EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:A->bool) SUBSET S DIFF Y` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `A DIFF (P:A->bool)` THEN
  SUBGOAL_THEN `P UNION (A DIFF P) = P UNION (A:A->bool)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:A. w IN P UNION A
          ==> ?x. x IN P /\
                  graph_reachable (induced_subgraph_edges E (P UNION A)) x w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:A` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[GRAPH_REACHABLE_REFL]; ALL_TAC] THEN
    UNDISCH_TAC `(w:A) IN A` THEN EXPAND_TAC "A" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:A` THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC GRAPH_REACHABLE_MONO THEN
    EXISTS_TAC `induced_subgraph_edges E (A:A->bool)` THEN
    ASM_SIMP_TAC[INDUCED_SUBGRAPH_EDGES_VERTEX_MONO; SUBSET_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `connected_graph (P UNION A) (induced_subgraph_edges E (P UNION A:A->bool))`
  ASSUME_TAC THENL
   [REWRITE_TAC[connected_graph] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `a:A` th) THEN MP_TAC(SPEC `b:A` th)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `graph_reachable (induced_subgraph_edges E (P UNION A)) (x:A) y`
    MP_TAC THENL
     [MATCH_MP_TAC GRAPH_REACHABLE_MONO THEN
      EXISTS_TAC `induced_subgraph_edges E (P:A->bool)` THEN
      ASM_SIMP_TAC[INDUCED_SUBGRAPH_EDGES_VERTEX_MONO; SUBSET_UNION] THEN
      ASM_MESON_TAC[connected_graph];
      ASM_MESON_TAC[GRAPH_REACHABLE_TRANS; GRAPH_REACHABLE_SYM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u v:A. u IN P UNION A /\ v IN Y /\ {u,v} IN E`
  STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`u:A`; `v:A`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(A:A->bool) SUBSET S DIFF Y` THEN SET_TAC[]] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `?x0:A y0:A. x0 IN P INTER S /\ y0 IN Y` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`induced_subgraph_edges E (S:A->bool)`;
                 `S INTER (P UNION A):A->bool`; `x0:A`; `y0:A`]
                GRAPH_REACHABLE_CLOSED) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN
    REWRITE_TAC[IN_INDUCED_SUBGRAPH_EDGES; INSERT_SUBSET; EMPTY_SUBSET;
                IN_INTER] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN
    SUBGOAL_THEN `{a:A,b} IN R` ASSUME_TAC THENL
     [EXPAND_TAC "R" THEN
      REWRITE_TAC[IN_INDUCED_SUBGRAPH_EDGES; INSERT_SUBSET; EMPTY_SUBSET;
                  IN_DIFF] THEN
      ASM_MESON_TAC[IN_UNION; SUBSET; IN_DIFF; SET_RULE
       `DISJOINT P Y /\ (a:A) IN P ==> ~(a IN Y)`];
      ALL_TAC] THEN
    UNDISCH_TAC `(a:A) IN P UNION A` THEN EXPAND_TAC "A" THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[IN_INTER; GRAPH_REACHABLE_TRANS; GRAPH_EDGE_IMP_REACHABLE;
                  GRAPH_REACHABLE_REFL];
    RULE_ASSUM_TAC(REWRITE_RULE[connected_graph]) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let CLOSED_IN_GRID_BOXES = prove
 (`!(c:real^2) h K D.
        FINITE D
        ==> closed_in (subtopology euclidean K)
             {x:real^2 | x IN K /\
                         ?g. g IN D /\ abs((grid_point c h g)$1 - x$1) <= h /\
                             abs((grid_point c h g)$2 - x$2) <= h}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x:real^2 | x IN K /\
                ?g. g IN D /\ abs((grid_point c h g)$1 - x$1) <= h /\
                    abs((grid_point c h g)$2 - x$2) <= h} =
    K INTER UNIONS
     {interval[grid_point c h g - h % vec 1,grid_point c h g + h % vec 1] |
      g IN D}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNIONS; IN_SUP_BOX] THEN
    MESON_TAC[IN_SUP_BOX];
    MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE;
                 CLOSED_INTERVAL]]);;

(* ------------------------------------------------------------------------- *)
(* The lattice points near a connected set form a connected subgraph: the    *)
(* boxes around two classes of lattice points not joined by a path would     *)
(* split K into two disjoint closed sets (two such boxes meeting at x would  *)
(* give an L-shaped path near x).                                            *)
(* ------------------------------------------------------------------------- *)

let GRID_NEAR_CONNECTED = prove
 (`!(c:real^2) h N K. &0 < h /\ connected K /\
        (!x:real^2. x IN K
                    ==> c$1 <= x$1 /\ x$1 <= c$1 + h * &N /\ c$2 <= x$2 /\
                    x$2 <= c$2 + h * &N)
        ==> connected_graph (grid_near c h N K)
                            (induced_subgraph_edges (grid_edges N)
                            (grid_near c h N K))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `B = grid_near (c:real^2) h N K` THEN
  REWRITE_TAC[connected_graph] THEN
  MAP_EVERY X_GEN_TAC [`u:num#num`; `v:num#num`] THEN STRIP_TAC THEN
  ABBREV_TAC
   `C = {g:num#num | g IN B /\
                     graph_reachable (induced_subgraph_edges (grid_edges N) B)
                                     u g}` THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `connected (K:real^2->bool)` THEN
  REWRITE_TAC[CONNECTED_CLOSED_IN] THEN
  MAP_EVERY EXISTS_TAC
   [`{x:real^2 | x IN K /\
                 ?g. g IN C /\ abs((grid_point c h g)$1 - x$1) <= h /\
                               abs((grid_point c h g)$2 - x$2) <= h}`;
    `{x:real^2 | x IN K /\
                 ?g. g IN B DIFF C /\
                     abs((grid_point c h g)$1 - x$1) <= h /\
                     abs((grid_point c h g)$2 - x$2) <= h}`] THEN
  SUBGOAL_THEN `(C:num#num->bool) SUBSET B /\ B SUBSET grid_vertices N`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN EXPAND_TAC "B" THEN
    REWRITE_TAC[GRID_NEAR_SUBSET] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_GRID_BOXES THEN
    ASM_MESON_TAC[FINITE_SUBSET; FINITE_GRID_VERTICES; SUBSET_TRANS];
    MATCH_MP_TAC CLOSED_IN_GRID_BOXES THEN
    ASM_MESON_TAC[FINITE_SUBSET; FINITE_GRID_VERTICES; SUBSET_TRANS;
                  SUBSET_DIFF];
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real^2`; `h:real`; `N:num`; `x:real^2`] GRID_COVER) THEN
    ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(i:num,j:num) IN B` ASSUME_TAC THENL
     [EXPAND_TAC "B" THEN REWRITE_TAC[IN_GRID_NEAR; IN_GRID_VERTICES] THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[IN_DIFF] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY; IN_DIFF] THEN
    X_GEN_TAC `x:real^2` THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `g:num#num` STRIP_ASSUME_TAC))
     (X_CHOOSE_THEN `g':num#num` STRIP_ASSUME_TAC o CONJUNCT2)) THEN
    SUBGOAL_THEN `grid_lpath g (g':num#num) SUBSET B` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:num#num` THEN DISCH_TAC THEN
      EXPAND_TAC "B" THEN REWRITE_TAC[IN_GRID_NEAR] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[GRID_LPATH_SUBSET; SUBSET];
        EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC GRID_LPATH_BOX THEN
        MAP_EVERY EXISTS_TAC [`g:num#num`; `g':num#num`] THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `~((g':num#num) IN C)` THEN EXPAND_TAC "C" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GRAPH_REACHABLE_TRANS THEN EXISTS_TAC `g:num#num` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC GRAPH_REACHABLE_MONO THEN
    EXISTS_TAC `induced_subgraph_edges (grid_edges N) (grid_lpath g g')` THEN
    ASM_SIMP_TAC[INDUCED_SUBGRAPH_EDGES_VERTEX_MONO] THEN
    MATCH_MP_TAC GRID_LPATH_REACHABLE THEN
    ASM_MESON_TAC[GRID_LPATH_ENDS; SUBSET];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MP_TAC(ASSUME `(u:num#num) IN B`) THEN EXPAND_TAC "B" THEN
    REWRITE_TAC[IN_GRID_NEAR] THEN STRIP_TAC THEN
    EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `u:num#num` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "C" THEN ASM_REWRITE_TAC[IN_ELIM_THM; GRAPH_REACHABLE_REFL];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MP_TAC(ASSUME `(v:num#num) IN B`) THEN EXPAND_TAC "B" THEN
    REWRITE_TAC[IN_GRID_NEAR] THEN STRIP_TAC THEN
    EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `v:num#num` THEN ASM_REWRITE_TAC[IN_DIFF] THEN
    EXPAND_TAC "C" THEN ASM_REWRITE_TAC[IN_ELIM_THM]]);;

(* ------------------------------------------------------------------------- *)
(* Analytic auxiliaries: margins of compact sets inside open sets, balls     *)
(* avoiding finitely many closures.                                          *)
(* ------------------------------------------------------------------------- *)

let COMPACT_IN_OPEN_MARGIN = prove
 (`!K r:real^N->bool.
        compact K /\ open r /\ K SUBSET r
        ==> ?d. &0 < d /\ !x y. x IN K /\ dist(x,y) <= d ==> y IN r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `(:real^N) DIFF r`]
                SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ANTS_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(y:real^N) IN r` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM_REAL_ARITH_TAC);;

let BALL_AVOIDING_CLOSURES = prove
 (`!M z:real^N.
        FINITE M /\ (!r. r IN M ==> ~(z IN closure r))
        ==> ?rho. &0 < rho /\
                  !r y. r IN M /\ dist(y,z) < rho ==> ~(y IN closure r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open ((:real^N) DIFF UNIONS (IMAGE closure M))` MP_TAC THENL
   [REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; CLOSED_CLOSURE];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o REWRITE_RULE[SUBSET]) THEN
  ASM_REWRITE_TAC[IN_BALL; IN_DIFF; IN_UNIV; IN_UNIONS; IN_IMAGE] THEN
  ASM_MESON_TAC[DIST_SYM]);;

let BOUNDED_BOX_2 = prove
 (`!s:real^2->bool.
        bounded s
        ==> ?R. &0 < R /\ !x. x IN s ==> abs(x$1) <= R /\ abs(x$2) <= R`,
  REWRITE_TAC[BOUNDED_POS] THEN MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* The adjacency graph is a finite simple graph; picking the two ends of an  *)
(* edge.                                                                     *)
(* ------------------------------------------------------------------------- *)

let FINITE_ADJACENCY_GRAPH = prove
 (`!M. FINITE M ==> FINITE(adjacency_graph M)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\p. {FST p:real^2->bool,SND p}) (M CROSS M)` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_CROSS] THEN
  REWRITE_TAC[adjacency_graph; SUBSET; IN_ELIM_THM; IN_IMAGE; IN_CROSS;
              EXISTS_PAIR_THM] THEN
  REWRITE_TAC[FST; SND; adjacent_regions] THEN MESON_TAC[]);;

let edge_other = new_definition
 `edge_other (e:A->bool) = @r. r IN e /\ ~(r = CHOICE e)`;;

let EDGE_OTHER = prove
 (`!r1 r2:A. ~(r1 = r2)
             ==> CHOICE {r1,r2} IN {r1,r2} /\ edge_other {r1,r2} IN {r1,r2} /\
                 ~(edge_other {r1,r2} = CHOICE {r1,r2})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `CHOICE {r1:A,r2} IN {r1,r2}` ASSUME_TAC THENL
   [MATCH_MP_TAC CHOICE_DEF THEN REWRITE_TAC[NOT_INSERT_EMPTY]; ALL_TAC] THEN
  ASM_REWRITE_TAC[edge_other] THEN CONV_TAC SELECT_CONV THEN
  ASM_MESON_TAC[IN_INSERT; NOT_IN_EMPTY]);;

let FINITE_SIMPLE_GRAPH_ADJACENCY = prove
 (`!M. FINITE M ==> finite_simple_graph M (adjacency_graph M)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[finite_simple_graph; FINITE_ADJACENCY_GRAPH] THEN
  REWRITE_TAC[adjacency_graph; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
    [`e:(real^2->bool)->bool`; `r1:real^2->bool`; `r2:real^2->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  SUBGOAL_THEN `~(r1:real^2->bool = r2) /\ r1 IN M /\ r2 IN M`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[adjacent_regions]; ALL_TAC] THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_INSERT; FINITE_EMPTY; CARD_CLAUSES; IN_INSERT;
               NOT_IN_EMPTY] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A compact connected skeleton inside an open connected set through a base  *)
(* point and finitely many targets: the union of paths from the base point.  *)
(* ------------------------------------------------------------------------- *)

let SKELETON_EXISTS = prove
 (`!r p:real^N Q.
        open r /\ connected r /\ p IN r /\ FINITE Q /\ Q SUBSET r
        ==> ?K. compact K /\ connected K /\ K SUBSET r /\ p IN K /\
                Q SUBSET K`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!q:real^N. q IN Q ==> ?g. path g /\ path_image g SUBSET r /\
                              pathstart g = p /\ pathfinish g = q`
  MP_TAC THENL
   [MP_TAC(ISPEC `r:real^N->bool` CONNECTED_OPEN_PATH_CONNECTED) THEN
    ASM_REWRITE_TAC[path_connected] THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `g:real^N->real^1->real^N` o
      REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])] THEN
  EXISTS_TAC `UNIONS ({p:real^N} INSERT
                      IMAGE (path_image o (g:real^N->real^1->real^N)) Q)` THEN
  ASM_SIMP_TAC[COMPACT_UNIONS; FINITE_INSERT; FINITE_IMAGE; FORALL_IN_INSERT;
               FORALL_IN_IMAGE; COMPACT_SING; o_THM; COMPACT_PATH_IMAGE;
               UNIONS_SUBSET; SING_SUBSET] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNIONS THEN
    ASM_SIMP_TAC[FORALL_IN_INSERT; FORALL_IN_IMAGE; o_THM; CONNECTED_SING;
                 CONNECTED_PATH_IMAGE] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; INTERS_INSERT; IN_INTER; IN_SING;
                INTERS_IMAGE; IN_ELIM_THM; o_THM] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE];
    REWRITE_TAC[IN_UNIONS; IN_INSERT] THEN MESON_TAC[IN_SING];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_INSERT; IN_IMAGE; o_THM] THEN
    ASM_MESON_TAC[PATHFINISH_IN_PATH_IMAGE]]);;

(* ------------------------------------------------------------------------- *)
(* Planarity transfers back along an injective relabelling of the vertices.  *)
(* ------------------------------------------------------------------------- *)

let PLANAR_GRAPH_IMAGE_INJ = prove
 (`!(d:A->B) V E. INJ d V UNIV /\ (!e. e IN E ==> e SUBSET V) /\
                  planar_graph (IMAGE d V) (IMAGE (IMAGE d) E)
                  ==> planar_graph V E`,
  REWRITE_TAC[INJ; IN_UNIV; INJECTIVE_ON_LEFT_INVERSE] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:B->A`; `IMAGE (d:A->B) V`; `IMAGE (IMAGE (d:A->B)) E`]
    PLANAR_GRAPH_IMAGE) THEN
  ASM_SIMP_TAC[INJ; IN_UNIV; FORALL_IN_IMAGE; GSYM IMAGE_o] THEN
  SUBGOAL_THEN `!s. s SUBSET V ==> IMAGE ((g:B->A) o d) s = s`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; EXTENSION; IN_IMAGE; o_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (IMAGE (g:B->A) o IMAGE d) E = IMAGE I E`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> f x = g x) ==> IMAGE f (s:(A->bool)->bool) = IMAGE g s`)
    THEN ASM_SIMP_TAC[o_THM; I_THM; GSYM IMAGE_o];
    ASM_SIMP_TAC[IMAGE_I; SUBSET_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Shrinking finitely many balls around distinct centres to disjoint ones.   *)
(* ------------------------------------------------------------------------- *)

let SHRINK_TO_DISJOINT_BALLS = prove
 (`!D (z:A->real^N) rho.
        FINITE D /\ (!e. e IN D ==> &0 < rho e) /\
        (!e e'. e IN D /\ e' IN D /\ z e = z e' ==> e = e')
        ==> ?rho'. (!e. e IN D ==> &0 < rho' e /\ rho' e <= rho e) /\
                   (!e e' y. e IN D /\ e' IN D /\ ~(e = e') /\
                             dist(y,z e) < rho' e
                             ==> ~(dist(y,z e') < rho' e'))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\p:A#A. dist(z(FST p):real^N,z(SND p))`;
                 `{p | p IN (D:A->bool) CROSS D /\ ~(FST p = SND p)}`]
        FINITE_POSITIVE_LOWER_BOUND) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_SIMP_TAC[FINITE_CROSS];
      REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; IN_CROSS; FST; SND;
                  GSYM DIST_NZ] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; IN_CROSS; FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\e:A. min (rho e) (d / &2)` THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MIN; REAL_HALF]; REAL_ARITH_TAC];
    REWRITE_TAC[REAL_LT_MIN] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`e:A`; `e':A`]) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`z (e:A):real^N`; `y:real^N`; `z (e':A):real^N`]
                  DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`y:real^N`; `z (e:A):real^N`] DIST_SYM) THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Border data for an adjacency: a non-corner common closure point and a     *)
(* ball around it avoiding the closures of all other regions; such points    *)
(* determine their edge.                                                     *)
(* ------------------------------------------------------------------------- *)

let BORDER_POINT_DETERMINES_EDGE = prove
 (`!M D (z:((real^N->bool)->bool)->real^N).
        (!e. e IN D ==> e SUBSET M /\ (!r. r IN e ==> z e IN closure r) /\
                        (!r. r IN M /\ ~(r IN e) ==> ~(z e IN closure r)))
        ==> !e e'. e IN D /\ e' IN D /\ z e = z e' ==> e = e'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION] THEN
  X_GEN_TAC `r:real^N->bool` THEN
  ASM_MESON_TAC[SUBSET]);;

let ADJACENT_BORDER_DATA = prove
 (`!M r1 r2.
        FINITE M /\ adjacent_regions M r1 r2
        ==> ?z rho. &0 < rho /\ z IN closure r1 /\ z IN closure r2 /\
                    !r y. r IN M /\ ~(r = r1) /\ ~(r = r2) /\ dist(y,z) < rho
                          ==> ~(y IN closure r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[adjacent_regions; IN_INTER] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
    [`{r | r IN M /\ ~(r = r1) /\ ~(r = r2:real^2->bool)}`; `z:real^2`]
        BALL_AVOIDING_CLOSURES) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* From territories and crossings to a connected branch-set model (pure      *)
(* graph theory): P r = the territory of region r, Z e = the free vertices   *)
(* added for the edge e, owned by CHOICE e, with an E-edge u e -- v e into   *)
(* the territory of edge_other e.                                            *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_GRAPH_INDUCED_UNIONS = prove
 (`!E:(A->bool)->bool f a.
        (!s. s IN f
             ==> a IN s /\ connected_graph s (induced_subgraph_edges E s))
        ==> connected_graph (UNIONS f) (induced_subgraph_edges E (UNIONS f))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[connected_graph; IN_UNIONS] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `s:A->bool`)
                             (X_CHOOSE_TAC `t:A->bool`)) THEN
  MATCH_MP_TAC GRAPH_REACHABLE_TRANS THEN EXISTS_TAC `a:A` THEN
  CONJ_TAC THENL [MATCH_MP_TAC GRAPH_REACHABLE_SYM; ALL_TAC] THEN
  MATCH_MP_TAC GRAPH_REACHABLE_MONO THENL
   [EXISTS_TAC `induced_subgraph_edges E (s:A->bool)`;
    EXISTS_TAC `induced_subgraph_edges E (t:A->bool)`] THEN
  ASM_MESON_TAC[connected_graph; INDUCED_SUBGRAPH_EDGES_VERTEX_MONO;
                SET_RULE `s IN f ==> s SUBSET UNIONS f`]);;

let BRANCH_MODEL_OF_TERRITORIES = prove
 (`!(V:B->bool) E (M:A->bool) D (P:A->B->bool) (Z:(A->bool)->B->bool)
    (u:(A->bool)->B) (v:(A->bool)->B).
   (!e. e IN D ==> ?r1 r2. r1 IN M /\ r2 IN M /\ ~(r1 = r2) /\ e = {r1,r2}) /\
   (!r. r IN M ==> P r SUBSET V /\ ~(P r = {}) /\
                   connected_graph (P r) (induced_subgraph_edges E (P r))) /\
   (!r r'. r IN M /\ r' IN M /\ ~(r = r') ==> DISJOINT (P r) (P r')) /\
   (!e. e IN D ==> Z e SUBSET V /\ (!r. r IN M ==> DISJOINT (Z e) (P r)) /\
                   connected_graph (P (CHOICE e) UNION Z e)
                                   (induced_subgraph_edges E
                                   (P (CHOICE e) UNION Z e)) /\
                   u e IN P (CHOICE e) UNION Z e /\ v e IN P (edge_other e) /\
                   {u e,v e} IN E) /\
   (!e e'. e IN D /\ e' IN D /\ ~(e = e') ==> DISJOINT (Z e) (Z e'))
   ==> ?d B. INJ d M UNIV /\
             graph_branch_model V E (IMAGE d M) (IMAGE (IMAGE d) D) B`,
  REPEAT GEN_TAC THEN INTRO_TAC "edges P Pdisj Z Zdisj" THEN
  SUBGOAL_THEN `!r:A. r IN M ==> CHOICE((P:A->B->bool) r) IN P r`
  ASSUME_TAC THENL [ASM_MESON_TAC[CHOICE_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!r r':A. r IN M /\ r' IN M /\ CHOICE((P:A->B->bool) r) = CHOICE(P r')
             ==> r = r'`
  MP_TAC THENL
   [ASM_MESON_TAC[SET_RULE `DISJOINT s t /\ (x:B) IN s /\ x IN t ==> F`];
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th)] THEN
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:B->A`) THEN
  SUBGOAL_THEN
   `!e:A->bool. e IN D
                ==> CHOICE e IN M /\ edge_other e IN M /\
                    ~(CHOICE e = edge_other e) /\
                    !f:A->B. IMAGE f e = {f(CHOICE e),f(edge_other e)}`
  (LABEL_TAC "ends") THENL
   [X_GEN_TAC `e:A->bool` THEN
    DISCH_THEN(fun th -> USE_THEN "edges" (MP_TAC o C MATCH_MP th)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r1:A`; `r2:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`r1:A`; `r2:A`] EDGE_OTHER) THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; IMAGE_CLAUSES] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[INSERT_COMM];
    ALL_TAC] THEN
  ABBREV_TAC
   `BR = \r:A. UNIONS ((P:A->B->bool) r INSERT
            {P r UNION (Z:(A->bool)->B->bool) e | e | e IN D /\ CHOICE e = r})`
  THEN
  SUBGOAL_THEN
   `!r x:B. x IN (BR:A->B->bool) r <=>
            x IN P r \/ ?e. e IN D /\ CHOICE e = r /\ x IN Z e`
  (LABEL_TAC "inBR") THENL
   [EXPAND_TAC "BR" THEN
    REWRITE_TAC[UNIONS_INSERT; UNIONS_GSPEC; IN_UNION; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\r:A. CHOICE((P:A->B->bool) r)`; `\x:B. (BR:A->B->bool) (g x)`] THEN
  ASM_REWRITE_TAC[INJ; IN_UNIV; graph_branch_model] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `r:A` THEN DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
      EXPAND_TAC "BR" THEN MATCH_MP_TAC CONNECTED_GRAPH_INDUCED_UNIONS THEN
      EXISTS_TAC `CHOICE((P:A->B->bool) r)` THEN
      REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_GSPEC] THEN
      ASM_SIMP_TAC[IN_UNION] THEN ASM_MESON_TAC[]];
    X_GEN_TAC `r:A` THEN DISCH_TAC THEN X_GEN_TAC `r':A` THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `~(r:A = r')` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SET_RULE `DISJOINT s t ==> ~((x:B) IN s /\ x IN t)`];
    MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:A->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "Z" (MP_TAC o C MATCH_MP (ASSUME `(e:A->bool) IN D`)) THEN
    USE_THEN "ends" (MP_TAC o C MATCH_MP (ASSUME `(e:A->bool) IN D`)) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `x = CHOICE((P:A->B->bool)(CHOICE e)) /\ y = CHOICE(P(edge_other e)) \/
      x = CHOICE(P(edge_other e)) /\ y = CHOICE((P:A->B->bool)(CHOICE e))`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `{a:B,b} = {c,d} ==> a = c /\ b = d \/ a = d /\ b = c`) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`(u:(A->bool)->B) e`; `(v:(A->bool)->B) e`];
      ASM_SIMP_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`(v:(A->bool)->B) e`; `(u:(A->bool)->B) e`] THEN
      ONCE_REWRITE_TAC[INSERT_COMM]] THEN
    ASM_MESON_TAC[IN_UNION]]);;

(* ------------------------------------------------------------------------- *)
(* The crossing at one adjacency: inside the border ball, the L-shaped       *)
(* lattice path between the two territories supplies the free vertices.      *)
(* ------------------------------------------------------------------------- *)

let GRID_CROSSING = prove
 (`!(c:real^2) h N (M:(real^2->bool)->bool) r1 r2 (z:real^2) rho
    (K:(real^2->bool)->real^2->bool) q1 q2.
     &0 < h /\ &6 * h < rho /\ r1 IN M /\ r2 IN M /\ ~(r1 = r2) /\
     (!r x y. r IN M /\ x IN K r /\ dist(x,y) <= &2 * h ==> y IN r) /\
     (!r x. r IN M /\ x IN K r
            ==> c$1 <= x$1 /\ x$1 <= c$1 + h * &N /\
                c$2 <= x$2 /\ x$2 <= c$2 + h * &N) /\
     (!r. r IN M ==> connected (K r)) /\
     (!r r'. r IN M /\ r' IN M /\ ~(r = r') ==> DISJOINT r r') /\
     (!r y. r IN M /\ ~(r = r1) /\ ~(r = r2) /\ dist(y,z) < rho
            ==> ~(y IN r)) /\
     q1 IN K r1 /\ dist(q1,z) < rho / &3 /\ q2 IN K r2 /\ dist(q2,z) < rho / &3
     ==> ?Z u v. Z SUBSET grid_vertices N /\
                 (!r. r IN M ==> DISJOINT Z (grid_near c h N (K r))) /\
                 (!w. w IN Z ==> dist(grid_point c h w,z) < rho) /\
                 connected_graph (grid_near c h N (K r1) UNION Z)
                   (induced_subgraph_edges (grid_edges N)
                   (grid_near c h N (K r1) UNION Z)) /\
                 u IN grid_near c h N (K r1) UNION Z /\
                 v IN grid_near c h N (K r2) /\
                 {u,v} IN grid_edges N`,
  REPEAT GEN_TAC THEN
  INTRO_TAC
   "hpos hrho r1M r2M neq margin box conn disj ball q1K q1z q2K q2z" THEN
  MP_TAC(SPECL [`c:real^2`; `h:real`; `N:num`;
                `(K:(real^2->bool)->real^2->bool) r1`; `q1:real^2`]
               GRID_NEAR_NONEMPTY) THEN
  MP_TAC(SPECL [`c:real^2`; `h:real`; `N:num`;
                `(K:(real^2->bool)->real^2->bool) r2`; `q2:real^2`]
               GRID_NEAR_NONEMPTY) THEN
  ASM_SIMP_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:num#num` STRIP_ASSUME_TAC) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:num#num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(g1:num#num) IN grid_vertices N /\ (g2:num#num) IN grid_vertices N`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[GRID_NEAR_SUBSET; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `S = grid_lpath g1 (g2:num#num)` THEN
  SUBGOAL_THEN `!w:num#num. w IN S ==> dist(grid_point c h w,z) < rho`
  (LABEL_TAC "inball") THENL
   [X_GEN_TAC `w:num#num` THEN DISCH_TAC THEN
    MP_TAC(SPECL
      [`c:real^2`; `h:real`; `g1:num#num`; `g2:num#num`; `w:num#num`;
       `(z:real^2)$1`; `(z:real^2)$2`; `rho / &3 + h`; `rho / &3 + h`]
      GRID_LPATH_BOX) THEN
    MP_TAC(ISPECL [`q1:real^2`; `z:real^2`] DIST_COMPONENT_BOUND_2) THEN
    MP_TAC(ISPECL [`q2:real^2`; `z:real^2`] DIST_COMPONENT_BOUND_2) THEN
    MP_TAC(ISPECL [`grid_point c h (w:num#num)`; `z:real^2`]
      DIST_LE_COMPONENTS_2) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`grid_edges N`; `S:num#num->bool`;
                 `grid_near c h N ((K:(real^2->bool)->real^2->bool) r1)`;
                 `grid_near c h N ((K:(real^2->bool)->real^2->bool) r2)
                  INTER S`]
        GRAPH_ATTACH_LEMMA) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[GRID_LPATH_CONNECTED] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC GRID_NEAR_CONNECTED THEN ASM_MESON_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      ASM_MESON_TAC[GRID_LPATH_ENDS];
      SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      ASM_MESON_TAC[GRID_LPATH_ENDS];
      MATCH_MP_TAC(SET_RULE
       `DISJOINT s t ==> DISJOINT s (t INTER u:num#num->bool)`) THEN
      MATCH_MP_TAC GRID_NEAR_DISJOINT THEN
      MAP_EVERY EXISTS_TAC [`r1:real^2->bool`; `r2:real^2->bool`] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[GRID_LPATH_SUBSET; SUBSET_TRANS];
    X_GEN_TAC `r:real^2->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `r:real^2->bool = r1` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `r:real^2->bool = r2` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`(Z:num#num->bool) SUBSET S`;
        `DISJOINT (Z:num#num->bool)
                  (grid_near c h N ((K:(real^2->bool)->real^2->bool) r2)
                   INTER S)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SET_RULE `DISJOINT s t <=> !x. x IN s ==> ~(x IN t)`] THEN
    X_GEN_TAC `w:num#num` THEN REPEAT DISCH_TAC THEN
    MP_TAC(SPECL [`c:real^2`; `h:real`; `N:num`;
                  `(K:(real^2->bool)->real^2->bool) r`; `r:real^2->bool`;
                  `w:num#num`] GRID_NEAR_IN_REGION) THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[SUBSET];
    ASM_MESON_TAC[SUBSET];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The adjacency graph of a finite plane map is planar: it is a minor of a   *)
(* fine grid graph.  For each edge e choose a border point z0 e with a ball  *)
(* meeting only the closures of the two regions of e, shrink the balls to    *)
(* disjoint ones of radius rho e, and choose points q e r of both regions    *)
(* near z0 e; a compact connected skeleton K r of each region r contains its *)
(* points q e r.  With a grid finer than the margins of the skeletons and    *)
(* the radii, the territories grid_near (K r) and the crossings of           *)
(* GRID_CROSSING give a branch-set model of the adjacency graph.             *)
(* ------------------------------------------------------------------------- *)

let ADJACENCY_GRAPH_PLANAR = prove
 (`!M. plane_map M /\ FINITE M /\ (!r. r IN M ==> ~(r = {}))
       ==> planar_graph M (adjacency_graph M)`,
  REWRITE_TAC[plane_map; pairwise] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = adjacency_graph M` THEN
  SUBGOAL_THEN `FINITE (D:((real^2->bool)->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_ADJACENCY_GRAPH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. e IN D
        ==> CHOICE e IN M /\ edge_other e IN M /\ ~(CHOICE e = edge_other e) /\
            adjacent_regions M (CHOICE e) (edge_other e) /\
            !r:real^2->bool. r IN e <=> r = CHOICE e \/ r = edge_other e`
  (LABEL_TAC "ends") THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[adjacency_graph; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`r1:real^2->bool`; `r2:real^2->bool`] THEN
    DISCH_TAC THEN FIRST_ASSUM(MP_TAC o REWRITE_RULE[adjacent_regions]) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`r1:real^2->bool`; `r2:real^2->bool`] EDGE_OTHER) THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[ADJACENT_REGIONS_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. e IN D
        ==> ?z:real^2 rho. &0 < rho /\ (!r. r IN e ==> z IN closure r) /\
                           (!r y. r IN M /\ ~(r IN e) /\ dist(y,z) < rho
                                  ==> ~(y IN closure r))`
  MP_TAC THENL
   [X_GEN_TAC `e:(real^2->bool)->bool` THEN
    DISCH_THEN(fun th -> USE_THEN "ends" (MP_TAC o C MATCH_MP th)) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`M:(real^2->bool)->bool`;
                   `CHOICE(e:(real^2->bool)->bool)`;
                   `edge_other(e:(real^2->bool)->bool)`]
                  ADJACENT_BORDER_DATA) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN MESON_TAC[];
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `z0:((real^2->bool)->bool)->real^2`
     (X_CHOOSE_THEN `rho0:((real^2->bool)->bool)->real`
       (LABEL_TAC "border")))] THEN
  MP_TAC(ISPECL [`D:((real^2->bool)->bool)->bool`;
                 `z0:((real^2->bool)->bool)->real^2`;
                 `rho0:((real^2->bool)->bool)->real`]
                SHRINK_TO_DISJOINT_BALLS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC BORDER_POINT_DETERMINES_EDGE THEN
    EXISTS_TAC `M:(real^2->bool)->bool` THEN
    X_GEN_TAC `e:(real^2->bool)->bool` THEN DISCH_TAC THEN
    REMOVE_THEN "border" (MP_TAC o C MATCH_MP
      (ASSUME `(e:(real^2->bool)->bool) IN D`)) THEN
    REMOVE_THEN "ends" (MP_TAC o C MATCH_MP
      (ASSUME `(e:(real^2->bool)->bool) IN D`)) THEN
    REWRITE_TAC[SUBSET] THEN MESON_TAC[DIST_REFL];
    DISCH_THEN(X_CHOOSE_THEN `rho:((real^2->bool)->bool)->real`
      (CONJUNCTS_THEN2 (LABEL_TAC "rhopos") (LABEL_TAC "rhodisj")))] THEN
  SUBGOAL_THEN
   `!e r:real^2->bool.
        e IN D /\ r IN e ==> ?q. q IN r /\ dist(q,z0 e) < rho e / &3`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(z0:((real^2->bool)->bool)->real^2) e IN closure r`
    MP_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[CLOSURE_APPROACHABLE]] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[REAL_ARITH `&0 < x ==> &0 < x / &3`];
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN
      `q:((real^2->bool)->bool)->(real^2->bool)->real^2` (LABEL_TAC "q"))] THEN
  SUBGOAL_THEN
   `!r:real^2->bool.
        r IN M
        ==> ?K. compact K /\ connected K /\ K SUBSET r /\ ~(K = {}) /\
                !e. e IN D /\ r IN e ==> q e r IN K`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
      C MATCH_MP (ASSUME `(r:real^2->bool) IN M`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `p:real^2`) THEN
    MP_TAC(ISPECL [`r:real^2->bool`; `p:real^2`;
       `IMAGE (\e. (q:((real^2->bool)->bool)->(real^2->bool)->real^2) e r)
              {e | e IN D /\ r IN e}`] SKELETON_EXISTS) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_RESTRICT; SUBSET; FORALL_IN_IMAGE;
                 IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `K:(real^2->bool)->real^2->bool`
      (LABEL_TAC "K"))] THEN
  SUBGOAL_THEN
   `?delta. &0 < delta /\
            !r x y. r IN M /\ x IN (K:(real^2->bool)->real^2->bool) r /\
                    dist(x,y) <= delta ==> y IN r`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!r:real^2->bool. r IN M
        ==> ?d. &0 < d /\ !x y. x IN K r /\ dist(x,y) <= d ==> y IN r`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_IN_OPEN_MARGIN THEN
      ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_TAC `d:(real^2->bool)->real` o
        REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])] THEN
    MP_TAC(ISPECL [`d:(real^2->bool)->real`; `M:(real^2->bool)->bool`]
      FINITE_POSITIVE_LOWER_BOUND) THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?rhomin. &0 < rhomin /\
             !e. e IN D ==> rhomin <= (rho:((real^2->bool)->bool)->real) e`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_POSITIVE_LOWER_BOUND THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `h = min (delta / &2) (rhomin / &7)` THEN
  SUBGOAL_THEN `&0 < h /\ &2 * h <= delta /\ &7 * h <= rhomin`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `bounded (UNIONS (IMAGE (K:(real^2->bool)->real^2->bool) M))`
  MP_TAC THENL
   [MATCH_MP_TAC BOUNDED_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC o
    MATCH_MP BOUNDED_BOX_2) THEN
  MP_TAC(SPEC `(&2 * R) / h` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  ABBREV_TAC `c:real^2 = vector[--R; --R]` THEN
  SUBGOAL_THEN
   `!r x:real^2. r IN M /\ x IN (K:(real^2->bool)->real^2->bool) r
                 ==> (c:real^2)$1 <= x$1 /\ x$1 <= c$1 + h * &N /\
                     c$2 <= x$2 /\ x$2 <= c$2 + h * &N`
  (LABEL_TAC "box") THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[VECTOR_2] THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `abs((x:real^2)$1) <= R /\ abs(x$2) <= R` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_UNIONS; IN_IMAGE] THEN
      ASM_MESON_TAC[];
      UNDISCH_TAC `(&2 * R) / h <= &N` THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. e IN D
        ==> ?Z u v.
              Z SUBSET grid_vertices N /\
              (!r. r IN M ==>
                   DISJOINT Z (grid_near c h N
                                 ((K:(real^2->bool)->real^2->bool) r))) /\
              (!w. w IN Z ==>
                   dist(grid_point c h w,
                        (z0:((real^2->bool)->bool)->real^2) e) <
                   (rho:((real^2->bool)->bool)->real) e) /\
              connected_graph (grid_near c h N (K (CHOICE e)) UNION Z)
                (induced_subgraph_edges (grid_edges N)
                   (grid_near c h N (K (CHOICE e)) UNION Z)) /\
              u IN grid_near c h N (K (CHOICE e)) UNION Z /\
              v IN grid_near c h N (K (edge_other e)) /\
              {u,v} IN grid_edges N`
  MP_TAC THENL
   [X_GEN_TAC `e:(real^2->bool)->bool` THEN DISCH_TAC THEN
    USE_THEN "ends" (MP_TAC o C MATCH_MP
      (ASSUME `(e:(real^2->bool)->bool) IN D`)) THEN
    STRIP_TAC THEN MATCH_MP_TAC GRID_CROSSING THEN
    MAP_EVERY EXISTS_TAC
     [`(q:((real^2->bool)->bool)->(real^2->bool)->real^2) e (CHOICE e)`;
      `(q:((real^2->bool)->bool)->(real^2->bool)->real^2) e (edge_other e)`]
    THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_ARITH
       `&0 < h /\ &7 * h <= m /\ m <= r ==> &6 * h < r`];
      ASM_MESON_TAC[REAL_LE_TRANS];
      ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN
      USE_THEN "border" (MP_TAC o C MATCH_MP
        (ASSUME `(e:(real^2->bool)->bool) IN D`)) THEN
      USE_THEN "rhopos" (MP_TAC o C MATCH_MP
        (ASSUME `(e:(real^2->bool)->bool) IN D`)) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET; REAL_LTE_TRANS];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `Z:((real^2->bool)->bool)->num#num->bool`
      (X_CHOOSE_THEN `u:((real^2->bool)->bool)->num#num`
        (X_CHOOSE_THEN `v:((real^2->bool)->bool)->num#num`
          (LABEL_TAC "cross"))))] THEN
  MP_TAC(ISPECL [`grid_vertices N`; `grid_edges N`; `M:(real^2->bool)->bool`;
                 `D:((real^2->bool)->bool)->bool`;
                 `\r:real^2->bool. grid_near c h N
                    ((K:(real^2->bool)->real^2->bool) r)`;
                 `Z:((real^2->bool)->bool)->num#num->bool`;
                 `u:((real^2->bool)->bool)->num#num`;
                 `v:((real^2->bool)->bool)->num#num`]
        BRANCH_MODEL_OF_TERRITORIES) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `e:(real^2->bool)->bool` THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`CHOICE(e:(real^2->bool)->bool)`;
                            `edge_other(e:(real^2->bool)->bool)`] THEN
      USE_THEN "ends" (MP_TAC o C MATCH_MP
        (ASSUME `(e:(real^2->bool)->bool) IN D`)) THEN
      SIMP_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY];
      X_GEN_TAC `r:real^2->bool` THEN DISCH_TAC THEN
      REWRITE_TAC[GRID_NEAR_SUBSET] THEN CONJ_TAC THENL
       [USE_THEN "K" (MP_TAC o C MATCH_MP
          (ASSUME `(r:real^2->bool) IN M`)) THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN STRIP_TAC THEN
        MP_TAC(SPECL [`c:real^2`; `h:real`; `N:num`;
                      `(K:(real^2->bool)->real^2->bool) r`; `x:real^2`]
                     GRID_NEAR_NONEMPTY) THEN
        ASM_MESON_TAC[];
        MATCH_MP_TAC GRID_NEAR_CONNECTED THEN ASM_MESON_TAC[]];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC GRID_NEAR_DISJOINT THEN
      MAP_EVERY EXISTS_TAC [`r:real^2->bool`; `r':real^2->bool`] THEN
      ASM_MESON_TAC[REAL_LE_TRANS];
      X_GEN_TAC `e:(real^2->bool)->bool` THEN DISCH_TAC THEN
      USE_THEN "cross" (MP_TAC o C MATCH_MP
        (ASSUME `(e:(real^2->bool)->bool) IN D`)) THEN
      SIMP_TAC[];
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[SET_RULE `DISJOINT s t <=> !x. x IN s ==> ~(x IN t)`] THEN
      X_GEN_TAC `w:num#num` THEN REPEAT STRIP_TAC THEN
      USE_THEN "rhodisj" (MP_TAC o SPECL
       [`e:(real^2->bool)->bool`; `e':(real^2->bool)->bool`;
        `grid_point c h (w:num#num)`]) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^2->bool)->num#num`
    (X_CHOOSE_THEN `B:num#num->num#num->bool` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC(ISPEC `d:(real^2->bool)->num#num` PLANAR_GRAPH_IMAGE_INJ) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "D" THEN
    ASM_MESON_TAC[FINITE_SIMPLE_GRAPH_ADJACENCY; finite_simple_graph];
    ALL_TAC] THEN
  MATCH_MP_TAC PLANAR_GRAPH_MINOR THEN
  MAP_EVERY EXISTS_TAC [`grid_vertices N`; `grid_edges N`] THEN
  REWRITE_TAC[PLANAR_GRAPH_GRID] THEN
  MATCH_MP_TAC GRAPH_BRANCH_MODEL_IMP_MINOR THEN
  EXISTS_TAC `B:num#num->num#num->bool` THEN
  ASM_REWRITE_TAC[FINITE_SIMPLE_GRAPH_GRID] THEN
  MATCH_MP_TAC FINITE_SIMPLE_GRAPH_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "D" THEN ASM_SIMP_TAC[FINITE_SIMPLE_GRAPH_ADJACENCY]);;
