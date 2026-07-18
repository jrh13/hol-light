(* The Jordan graph predicate is exactly the closed, two-endpoint refinement. *)

needs "Library/incidence.ml";;
needs "Jordan/make.ml";;

let JORDAN_GRAPH_EQ_INCIDENCE = prove
 (`!G:(V,E)graph_t.
      graph G <=>
      incidence_closed
        (graph_edge G) (graph_vertex G) (graph_inc G) /\
      incidence_has_size 2 (graph_edge G) (graph_inc G)`,
  REWRITE_TAC[graph; INCIDENCE_CLOSED_AND_HAS_SIZE_IMAGE]);;
