(* ========================================================================= *)
(* A small unbundled interface for edge-vertex incidence.                    *)
(* ========================================================================= *)

let incidence_closed = new_definition
 `incidence_closed (edge_set:E->bool) (vertex_set:V->bool)
                   (incidence:E->V->bool) <=>
    !e v. edge_set e /\ incidence e v ==> vertex_set v`;;

let incidence_has_size = new_definition
 `incidence_has_size n (edge_set:E->bool) (incidence:E->V->bool) <=>
    !e. edge_set e ==> incidence e HAS_SIZE n`;;

let INCIDENCE_CLOSED_AND_HAS_SIZE_IMAGE = prove
 (`!n edge_set:E->bool. !vertex_set:V->bool. !incidence.
        incidence_closed edge_set vertex_set incidence /\
        incidence_has_size n edge_set incidence <=>
        IMAGE incidence edge_set SUBSET
        {s | s SUBSET vertex_set /\ s HAS_SIZE n}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
   [incidence_closed; incidence_has_size; SUBSET; FORALL_IN_IMAGE;
    IN_ELIM_THM] THEN
  SET_TAC[]);;

let INCIDENCE_RESTRICT_EDGES = prove
 (`!n edge_set:E->bool. !vertex_set:V->bool. !incidence edge_subset.
        edge_subset SUBSET edge_set /\
        incidence_closed edge_set vertex_set incidence /\
        incidence_has_size n edge_set incidence
        ==> incidence_closed edge_subset vertex_set incidence /\
            incidence_has_size n edge_subset incidence`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SUBSET; incidence_closed; incidence_has_size] THEN
  SET_TAC[]);;

let active_incidences = new_definition
 `active_incidences (edge_set:E->bool) (incidence:E->V->bool) =
    {(e,v) | edge_set e /\ incidence e v}`;;

let ACTIVE_INCIDENCES_AS_UNIONS = prove
 (`!edge_set:E->bool. !incidence:E->V->bool.
        active_incidences edge_set incidence =
        UNIONS {IMAGE (\v. (e,v)) (incidence e) | e IN edge_set}`,
  REWRITE_TAC[active_incidences] THEN SET_TAC[]);;

let FINITE_ACTIVE_INCIDENCES_CARD_LE = prove
 (`!n edge_set:E->bool. !incidence:E->V->bool.
        FINITE edge_set /\ incidence_has_size n edge_set incidence
        ==> FINITE (active_incidences edge_set incidence) /\
            CARD (active_incidences edge_set incidence) <=
            CARD edge_set * n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[incidence_has_size] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "size")) THEN
  REWRITE_TAC[ACTIVE_INCIDENCES_AS_UNIONS] THEN
  MATCH_MP_TAC FINITE_CARD_LE_UNIONS THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  X_GEN_TAC `e:E` THEN REWRITE_TAC[IN] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_CARD_LE_IMAGE THEN
  REMOVE_THEN "size" (MP_TAC o SPEC `e:E`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[HAS_SIZE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL]);;

let share_active_edge = new_definition
 `share_active_edge (edge_set:E->bool) (incidence:E->V->bool) u v <=>
    ?e. edge_set e /\ incidence e u /\ incidence e v`;;

let incidence_adjacent = new_definition
 `incidence_adjacent (edge_set:E->bool) (incidence:E->V->bool) u v <=>
    ~(u = v) /\ share_active_edge edge_set incidence u v`;;

let SHARE_ACTIVE_EDGE_SYM = prove
 (`!edge_set:E->bool. !incidence:E->V->bool. !u v.
        share_active_edge edge_set incidence u v <=>
        share_active_edge edge_set incidence v u`,
  REWRITE_TAC[share_active_edge] THEN MESON_TAC[]);;

let INCIDENCE_ADJACENT_IRREFL = prove
 (`!edge_set:E->bool. !incidence:E->V->bool. !v.
        ~incidence_adjacent edge_set incidence v v`,
  REWRITE_TAC[incidence_adjacent]);;

let INCIDENCE_ADJACENT_SYM = prove
 (`!edge_set:E->bool. !incidence:E->V->bool. !u v.
        incidence_adjacent edge_set incidence u v <=>
        incidence_adjacent edge_set incidence v u`,
  REWRITE_TAC[incidence_adjacent; SHARE_ACTIVE_EDGE_SYM] THEN MESON_TAC[]);;

let INCIDENCE_ADJACENT_IN_VERTICES = prove
 (`!edge_set:E->bool. !vertex_set:V->bool. !incidence u v.
        incidence_closed edge_set vertex_set incidence /\
        incidence_adjacent edge_set incidence u v
        ==> vertex_set u /\ vertex_set v`,
  REWRITE_TAC[incidence_closed; incidence_adjacent; share_active_edge] THEN
  MESON_TAC[]);;

let incidence_label_fiber = new_definition
 `incidence_label_fiber (labels:E->S->bool) edge_set s =
    {e | edge_set e /\ labels e s}`;;

let INCIDENCE_LABEL_FIBER_SUBSET = prove
 (`!labels:E->S->bool. !edge_set s.
        incidence_label_fiber labels edge_set s SUBSET edge_set`,
  REWRITE_TAC[incidence_label_fiber; SUBSET; IN_ELIM_THM] THEN SET_TAC[]);;

let INCIDENCE_LABEL_FIBER_PRESERVES = prove
 (`!n edge_set:E->bool. !vertex_set:V->bool. !incidence labels:E->S->bool. !s.
        incidence_closed edge_set vertex_set incidence /\
        incidence_has_size n edge_set incidence
        ==> incidence_closed (incidence_label_fiber labels edge_set s)
                             vertex_set incidence /\
            incidence_has_size n (incidence_label_fiber labels edge_set s)
                                 incidence`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC INCIDENCE_RESTRICT_EDGES THEN
  EXISTS_TAC `edge_set:E->bool` THEN
  ASM_REWRITE_TAC[INCIDENCE_LABEL_FIBER_SUBSET]);;

let FINITE_INCIDENCE_LABEL_FIBER = prove
 (`!labels:E->S->bool. !edge_set s.
        FINITE edge_set ==> FINITE (incidence_label_fiber labels edge_set s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `edge_set:E->bool` THEN
  ASM_REWRITE_TAC[INCIDENCE_LABEL_FIBER_SUBSET]);;

let triangle_free_relation = new_definition
 `triangle_free_relation (adj:V->V->bool) <=>
    !x y z. ~(adj x y /\ adj y z /\ adj z x)`;;

let independent_relation = new_definition
 `independent_relation (adj:V->V->bool) s <=>
    !x y. x IN s /\ y IN s /\ ~(x = y) ==> ~adj x y`;;

let relation_homomorphism = new_definition
 `relation_homomorphism vertex_set
       (source:A->A->bool) (target:B->B->bool) (f:A->B) <=>
    !x y. x IN vertex_set /\ y IN vertex_set /\ source x y
          ==> target (f x) (f y)`;;

let TRIANGLE_FREE_INCIDENCE_NEIGHBORHOOD = prove
 (`!core_vertices:A->bool. !core_edges:CE->bool. !core_incidence.
   !ambient_edges:AE->bool. !ambient_incidence i w.
        triangle_free_relation
          (incidence_adjacent ambient_edges ambient_incidence) /\
        relation_homomorphism core_vertices
          (incidence_adjacent core_edges core_incidence)
          (incidence_adjacent ambient_edges ambient_incidence) i
        ==> independent_relation
              (incidence_adjacent core_edges core_incidence)
              {x | x IN core_vertices /\
                   incidence_adjacent ambient_edges ambient_incidence w (i x)}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
   [triangle_free_relation; relation_homomorphism;
    independent_relation; IN_ELIM_THM] THEN
  MESON_TAC[INCIDENCE_ADJACENT_SYM]);;
